import Mathlib

/-!
# Invariants of `p`-adic fields: the field and its ring of integers

This file begins the formalization of the blueprint
`numina/blueprints/padicinv/padicinv.tex` (Invariants of a finite extension of
`p`-adic fields):

* `PadicField` (blueprint `def:padic-field`): a `p`-adic field is a finite
  extension `K / ℚ_[p]`.
* `PadicField.ringOfIntegers` (`𝒪_K`): the integral closure of `ℤ_[p]` in `K`,
  together with `IsFractionRing 𝒪_K K`.
* `PadicField.instIsDiscreteValuationRing` (blueprint `prop:padic-is-dvf`):
  `𝒪_K` is a discrete valuation ring. This is the only fact left as `sorry`.

Once `𝒪_K` is a DVR it is in particular a local Dedekind domain with fraction
field `K`, so the normalized valuation `v_K : K → ℤᵐ⁰` of `def:padic-field` is
just Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation` for the maximal
ideal of `𝒪_K`; no dedicated wrapper is introduced here.
-/

noncomputable section

/-- A *`p`-adic field* is a finite extension `K / ℚ_[p]`. -/
class PadicField (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] : Prop
    extends Module.Finite ℚ_[p] K

namespace PadicField

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [PadicField p K]

/-- The canonical `ℤ_[p]`-algebra structure on a `p`-adic field, obtained by
restricting scalars along `ℤ_[p] → ℚ_[p]`. -/
instance instAlgebraPadicInt : Algebra ℤ_[p] K :=
  ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

instance instIsScalarTower : IsScalarTower ℤ_[p] ℚ_[p] K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The ring of integers `𝒪_K` of a `p`-adic field `K`: the integral closure of
`ℤ_[p]` (the integers of `ℚ_[p]`) in `K`. -/
def ringOfIntegers : Subalgebra ℤ_[p] K := integralClosure ℤ_[p] K

@[inherit_doc] scoped notation "𝒪[" K "]" => PadicField.ringOfIntegers _ K

instance : IsFractionRing (ringOfIntegers p K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] K

/-! ### Proof that `𝒪_K` is a discrete valuation ring (`prop:padic-is-dvf`)

We realize `K` as a finite extension of the valued completion
`ℚ̂ := (Rat.padicValuation p).Completion`, which is isomorphic to `ℚ_[p]`. We give
`ℚ̂` its rank-one valuation and spectral norm, show that the integral closure of the
valuation integers `𝒪[ℚ̂]` in `K` is a valuation ring (via the spectral norm), transfer
this to `𝒪_K` through the isomorphism `𝒪[ℚ̂] ≃ ℤ_[p]`, and conclude with the
local-Dedekind-domain characterization of discrete valuation rings. -/

/-- The valued completion of `ℚ` at the `p`-adic valuation; it is isomorphic to `ℚ_[p]`. -/
abbrev Qhat := (Rat.padicValuation p).Completion

/-- The value group `ℤᵐ⁰` of the `p`-adic valuation. -/
abbrev Γ : Type := WithZero (Multiplicative ℤ)

/-- The valuation on `ℚ̂` is nontrivial. -/
instance instIsNontrivial : (Valued.v : Valuation (Qhat p) (Γ)).IsNontrivial := by
  rw [Valuation.IsNontrivial_iff_exists_one_lt]
  refine ⟨(((WithVal.equiv (Rat.padicValuation p)).symm ((p : ℚ)⁻¹) :
      WithVal (Rat.padicValuation p)) : Qhat p), ?_⟩
  rw [Valued.valuedCompletion_apply, ← WithVal.val_apply_equiv, RingEquiv.apply_symm_apply,
    map_inv₀, Rat.padicValuation_self]
  rw [← WithZero.exp_zero, ← WithZero.exp_neg, WithZero.exp_lt_exp]
  norm_num

instance instRankOne : (Valued.v : Valuation (Qhat p) (Γ)).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne (Valued.v) (e := 2) (by norm_num)

/-- `ℚ̂` is a `ℚ_[p]`-algebra via the isomorphism `ℚ̂ ≃ ℚ_[p]`. -/
instance instAlgebraQhatQp : Algebra (Qhat p) ℚ_[p] :=
  (Padic.withValRingEquiv (p := p)).toRingHom.toAlgebra

/-- `K` is a `ℚ̂`-algebra (through `ℚ_[p]`). -/
instance instAlgebraQhatK : Algebra (Qhat p) K :=
  ((algebraMap ℚ_[p] K).comp (Padic.withValRingEquiv (p := p)).toRingHom).toAlgebra

instance : IsScalarTower (Qhat p) ℚ_[p] K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance instModuleFiniteQhatQp : Module.Finite (Qhat p) ℚ_[p] :=
  Module.Finite.of_surjective (Algebra.linearMap (Qhat p) ℚ_[p])
    (Padic.withValRingEquiv (p := p)).surjective

instance instAlgebraicQhatQp : Algebra.IsAlgebraic (Qhat p) ℚ_[p] :=
  Algebra.IsAlgebraic.of_finite (Qhat p) ℚ_[p]

instance instAlgebraicQhatK : Algebra.IsAlgebraic (Qhat p) K :=
  Algebra.IsAlgebraic.trans (Qhat p) ℚ_[p] K

/-- The (nontrivially) normed field structure on `ℚ̂` induced by its rank-one valuation. -/
instance instNontriviallyNormedField : NontriviallyNormedField (Qhat p) :=
  Valued.toNontriviallyNormedField (Qhat p) (Γ)

/-- If the spectral norm of `x : K` is `≤ 1`, then `x` is integral over the valuation
integers `𝒪[ℚ̂]`. -/
theorem isIntegral_of_spectralNorm_le_one {x : K} (hx : spectralNorm (Qhat p) K x ≤ 1) :
    IsIntegral (Valued.v : Valuation (Qhat p) (Γ)).integer x := by
  have : minpoly (Qhat p) x ∈
      Polynomial.lifts (Valued.v : Valuation (Qhat p) (Γ)).integer.subtype := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
    have := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp hx i
    simp only [spectralValueTerms] at this
    split_ifs at this with h
    · conv_rhs at this => rw [← Real.one_rpow (1 / (↑(minpoly (Qhat p) x).natDegree - ↑i) : ℝ)]
      rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by aesop)] at this
      simpa [Valuation.mem_integer_iff] using this
    obtain h | h := (le_of_not_gt h).eq_or_lt
    · simp [← h, minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, one_mem]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt h, zero_mem]
  obtain ⟨P, hP, _, hP'⟩ := Polynomial.lifts_and_degree_eq_and_monic this
    (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨P, hP', ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap (Qhat p),
    show (algebraMap (↥(Valued.v : Valuation (Qhat p) (Γ)).integer) (Qhat p)) =
        (Valued.v : Valuation (Qhat p) (Γ)).integer.subtype from rfl, hP, minpoly.aeval]

/-- The spectral norm is multiplicative, hence inverts. -/
theorem spectralNorm_inv (x : K) :
    spectralNorm (Qhat p) K x⁻¹ = (spectralNorm (Qhat p) K x)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [spectralNorm_zero]
  · have h := spectralAlgNorm_mul (K := Qhat p) (L := K) x x⁻¹
    rw [mul_inv_cancel₀ hx0, spectralAlgNorm_def, spectralAlgNorm_def, spectralAlgNorm_def,
      spectralNorm_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm

/-- The integral closure of `𝒪[ℚ̂]` in `K` is a valuation ring. -/
instance instValuationRing :
    ValuationRing (integralClosure (Valued.v : Valuation (Qhat p) (Γ)).integer K) := by
  refine ValuationSubring.instValuationRingSubtypeMem
    (A := ⟨(integralClosure (Valued.v : Valuation (Qhat p) (Γ)).integer K).toSubring, ?_⟩)
  intro x
  obtain hx | hx := le_total (spectralNorm (Qhat p) K x) 1
  · exact Or.inl (isIntegral_of_spectralNorm_le_one (p := p) (K := K) hx)
  · refine Or.inr (isIntegral_of_spectralNorm_le_one (p := p) (K := K) ?_)
    rw [spectralNorm_inv]
    exact inv_le_one_of_one_le₀ hx

/-- `𝒪[ℚ̂]` is a `ℤ_[p]`-algebra via the isomorphism `𝒪[ℚ̂] ≃ ℤ_[p]`. -/
instance instAlgebraZpInteger :
    Algebra ℤ_[p] ↥(Valued.v : Valuation (Qhat p) (Γ)).integer :=
  (PadicInt.withValIntegersRingEquiv (p := p)).symm.toRingHom.toAlgebra

instance instIntegerIntegral : Algebra.IsIntegral ℤ_[p]
    ↥(Valued.v : Valuation (Qhat p) (Γ)).integer := by
  have : Module.Finite ℤ_[p] ↥(Valued.v : Valuation (Qhat p) (Γ)).integer :=
    Module.Finite.of_surjective (Algebra.linearMap ℤ_[p] _)
      (PadicInt.withValIntegersRingEquiv (p := p)).symm.surjective
  exact Algebra.IsIntegral.of_finite ℤ_[p] _

instance : IsScalarTower ℤ_[p] ↥(Valued.v : Valuation (Qhat p) (Γ)).integer K := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K,
    IsScalarTower.algebraMap_apply (↥(Valued.v : Valuation (Qhat p) (Γ)).integer) (Qhat p) K,
    IsScalarTower.algebraMap_apply (Qhat p) ℚ_[p] K]
  congr 1
  have compat : ∀ y : ↥(Valued.v : Valuation (Qhat p) (Γ)).integer,
      Padic.withValRingEquiv (p := p) (y : Qhat p)
        = ((PadicInt.withValIntegersRingEquiv (p := p) y : ℤ_[p]) : ℚ_[p]) := fun y => rfl
  show algebraMap ℤ_[p] ℚ_[p] x =
    (Padic.withValRingEquiv (p := p))
      (((PadicInt.withValIntegersRingEquiv (p := p)).symm x : Qhat p))
  rw [compat, RingEquiv.apply_symm_apply]
  rfl

omit [PadicField p K] in
/-- The integral closure of `𝒪[ℚ̂]` in `K` coincides, as a subring of `K`, with that of
`ℤ_[p]` (i.e. `𝒪_K`). -/
theorem integralClosure_integer_eq :
    (integralClosure (Valued.v : Valuation (Qhat p) (Γ)).integer K).toSubring
      = (integralClosure ℤ_[p] K).toSubring := by
  ext x
  rw [Subalgebra.mem_toSubring, Subalgebra.mem_toSubring, mem_integralClosure_iff,
    mem_integralClosure_iff]
  constructor
  · intro hx
    exact isIntegral_trans (R := ℤ_[p]) x hx
  · intro hx
    exact hx.tower_top

/-- `𝒪_K` is a local ring (transferred from the valuation ring above). -/
theorem isLocalRing_integralClosure_Zp :
    IsLocalRing (integralClosure ℤ_[p] K) := by
  haveI : IsLocalRing
      ↥(integralClosure (Valued.v : Valuation (Qhat p) (Γ)).integer K).toSubring :=
    inferInstanceAs
      (IsLocalRing (integralClosure (Valued.v : Valuation (Qhat p) (Γ)).integer K))
  exact (RingEquiv.subringCongr (integralClosure_integer_eq p K)).isLocalRing

theorem isDedekind : IsDedekindDomain (integralClosure ℤ_[p] K) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI : Algebra.IsSeparable ℚ_[p] K := Algebra.IsSeparable.of_integral ℚ_[p] K
  exact IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)

omit [PadicField p K] in
theorem notField : ¬ IsField (integralClosure ℤ_[p] K) := by
  have hinj : Function.Injective (algebraMap ℤ_[p] (integralClosure ℤ_[p] K)) := by
    have hK : Function.Injective (algebraMap ℤ_[p] K) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] K, RingHom.coe_comp]
      exact (algebraMap ℚ_[p] K).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
    rw [IsScalarTower.algebraMap_eq ℤ_[p] (integralClosure ℤ_[p] K) K, RingHom.coe_comp] at hK
    exact hK.of_comp
  intro hF
  exact (IsDiscreteValuationRing.not_isField ℤ_[p])
    ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hF)

theorem isDVR : IsDiscreteValuationRing (integralClosure ℤ_[p] K) := by
  haveI := isLocalRing_integralClosure_Zp p K
  haveI := isDedekind p K
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[p] K) (notField p K)).out 2 0).mp
    (isDedekind p K)

/-- The ring of integers of a `p`-adic field is a discrete valuation ring.

This is blueprint `prop:padic-is-dvf` (a `p`-adic field is a complete DVF):
the integral closure of the complete DVR `ℤ_[p]` in a finite extension is again
a complete DVR. It is left as the next target to prove; it is the single fact on
which the normalized valuation below rests. -/
instance instIsDiscreteValuationRing :
    IsDiscreteValuationRing (ringOfIntegers p K) :=
  isDVR p K

/-- `𝒪_K` is `𝔪_K`-adically complete (the completeness half of
`prop:padic-is-dvf`): the integral closure of the complete DVR `ℤ_[p]` in a
finite extension is again complete. -/
instance instIsAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal (ringOfIntegers p K)) (ringOfIntegers p K) := by
  sorry

/-!
## Invariants of an extension `L / K` (blueprint §1.2, §1.3, §1.4)
-/

namespace Extension

variable (L : Type*) [Field L] [Algebra ℚ_[p] L] [PadicField p L]
  [Algebra K L] [Module.Finite K L] [IsScalarTower ℚ_[p] K L]

/-- `ℤ_[p]` acts on `L` through `K`, compatibly with its action through `ℚ_[p]`. -/
instance instIsScalarTowerPadicInt : IsScalarTower ℤ_[p] K L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    have hK : algebraMap ℤ_[p] K x = algebraMap ℚ_[p] K (algebraMap ℤ_[p] ℚ_[p] x) := rfl
    have hL : algebraMap ℤ_[p] L x = algebraMap ℚ_[p] L (algebraMap ℤ_[p] ℚ_[p] x) := rfl
    rw [hK, hL, IsScalarTower.algebraMap_apply ℚ_[p] K L]

/-- The inclusion `𝒪_K → 𝒪_L` of rings of integers induced by `K → L`: an
element integral over `ℤ_[p]` stays integral after embedding into `L`. -/
def ringOfIntegersMap : ringOfIntegers p K →+* ringOfIntegers p L where
  toFun x := ⟨algebraMap K L (x : K), by
    have hx : IsIntegral ℤ_[p] (x : K) := x.2
    have h2 := hx.map (IsScalarTower.toAlgHom ℤ_[p] K L)
    rwa [IsScalarTower.toAlgHom_apply] at h2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/-- The `ℤ_[p]`-algebra structure on the pair `𝒪_K → 𝒪_L`, used to form the
relative ramification index. -/
instance instAlgebraRingOfIntegers : Algebra (ringOfIntegers p K) (ringOfIntegers p L) :=
  (ringOfIntegersMap p K L).toAlgebra

/-- The *ramification index* `e(L / K)` of an extension of `p`-adic fields
(blueprint `def:ramification-index`): the ramification index of the maximal
ideal `𝔪_K` of `𝒪_K` in `𝒪_L`. Equivalently `v_L(π_K) = e`, `𝔪_K 𝒪_L = 𝔪_L ^ e`. -/
def ramificationIdx : ℕ :=
  Ideal.ramificationIdx (R := ringOfIntegers p K) (S := ringOfIntegers p L)
    (IsLocalRing.maximalIdeal (ringOfIntegers p K))
    (IsLocalRing.maximalIdeal (ringOfIntegers p L))

/-- `L / K` is *unramified* when `e = 1` (blueprint `def:tame-wild`). -/
def IsUnramified : Prop := ramificationIdx p K L = 1

/-- `L / K` is *ramified* when `e > 1` (blueprint `def:tame-wild`). -/
def IsRamified : Prop := 1 < ramificationIdx p K L

/-- `L / K` is *tamely ramified* when `p ∤ e` (blueprint `def:tame-wild`). -/
def IsTamelyRamified : Prop := ¬ (p : ℕ) ∣ ramificationIdx p K L

/-- `L / K` is *wildly ramified* when `p ∣ e` (blueprint `def:tame-wild`). -/
def IsWildlyRamified : Prop := (p : ℕ) ∣ ramificationIdx p K L

/-!
### The residue degree and the identity `e * f = [L : K]` (blueprint §1.4)
-/

-- Shared structural instances for `L / K`, used by both results below.

/-- `ℤ_[p]` acts on `L` through `𝒪_K`. -/
instance : IsScalarTower ℤ_[p] (ringOfIntegers p K) L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (ringOfIntegers p K) K L,
        ← IsScalarTower.algebraMap_apply ℤ_[p] (ringOfIntegers p K) K]
    exact IsScalarTower.algebraMap_apply ℤ_[p] K L x

/-- `𝒪_K` acts on `L` through `𝒪_L`. -/
instance : IsScalarTower (ringOfIntegers p K) (ringOfIntegers p L) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : Algebra.IsIntegral ℤ_[p] (ringOfIntegers p K) :=
  inferInstanceAs (Algebra.IsIntegral ℤ_[p] (integralClosure ℤ_[p] K))

/-- `𝒪_L` is the integral closure of `𝒪_K` in `L`: an element of `L` is integral
over `𝒪_K` iff it is integral over `ℤ_[p]`. -/
instance : IsIntegralClosure (ringOfIntegers p L) (ringOfIntegers p K) L := by
  constructor
  · exact Subtype.coe_injective
  · intro x
    refine ⟨fun hx => ⟨⟨x, isIntegral_trans (R := ℤ_[p]) x hx⟩, rfl⟩, ?_⟩
    rintro ⟨y, rfl⟩
    exact (show IsIntegral ℤ_[p] (y : L) from y.2).tower_top

instance : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L

/-- `K` has characteristic zero (it contains `ℚ_[p]`), hence `L / K` is separable.
Phrased over `𝒪_K` so that `p` is fixed by the statement. -/
instance : Module.Finite (ringOfIntegers p K) (ringOfIntegers p L) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
  exact IsIntegralClosure.finite (ringOfIntegers p K) K L (ringOfIntegers p L)

omit [PadicField p L] in
/-- `𝒪_L` is a finite free `𝒪_K`-module of rank `[L : K]`
(blueprint `lem:OL-free`, Tian Lemma 9.1.1).

The blueprint argument lifts a `k_K`-basis of `𝒪_L / π_K 𝒪_L` and uses
`π_K`-adic completeness; we instead invoke the structure theory of finitely
generated modules over the PID `𝒪_K` (the same theorem), via `𝒪_L` being the
integral closure of `𝒪_K` in `L`. -/
theorem free_finrank :
    Module.Free (ringOfIntegers p K) (ringOfIntegers p L) ∧
      Module.finrank (ringOfIntegers p K) (ringOfIntegers p L) = Module.finrank K L := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
  haveI : FaithfulSMul (ringOfIntegers p K) (ringOfIntegers p L) :=
    (faithfulSMul_iff_algebraMap_injective (ringOfIntegers p K) (ringOfIntegers p L)).2
      fun a b hab => Subtype.ext ((algebraMap K L).injective (Subtype.ext_iff.1 hab))
  haveI : Module.IsTorsionFree (ringOfIntegers p K) L :=
    .trans_faithfulSMul (ringOfIntegers p K) (ringOfIntegers p L) L
  exact ⟨IsIntegralClosure.module_free (ringOfIntegers p K) K L (ringOfIntegers p L),
         IsIntegralClosure.rank (ringOfIntegers p K) K L (ringOfIntegers p L)⟩

/-- The *residue degree* `f(L / K)` of an extension of `p`-adic fields
(blueprint `def:residue-degree`): `f = [k_L : k_K]`, realised as the inertia
degree of `𝔪_K` in `𝒪_L`. -/
def inertiaDeg : ℕ :=
  Ideal.inertiaDeg (R := ringOfIntegers p K) (S := ringOfIntegers p L)
    (IsLocalRing.maximalIdeal (ringOfIntegers p K))
    (IsLocalRing.maximalIdeal (ringOfIntegers p L))

/-- The fundamental identity `e * f = [L : K]`
(blueprint `prop:ef-eq-degree`, Tian Prop. 9.1.4).

This is `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`, the local (DVR)
case of `Ideal.sum_ramification_inertia`, specialised to the rings of integers
of the `p`-adic fields `K ⊆ L`. -/
theorem ramificationIdx_mul_inertiaDeg :
    ramificationIdx p K L * inertiaDeg p K L = Module.finrank K L := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
  have hp0 : IsLocalRing.maximalIdeal (ringOfIntegers p K) ≠ ⊥ := fun h =>
    IsDiscreteValuationRing.not_isField (ringOfIntegers p K)
      ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  simpa only [ramificationIdx, inertiaDeg] using
    Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
      (R := ringOfIntegers p K) (S := ringOfIntegers p L) (K := K) (L := L) hp0

end Extension

end PadicField
