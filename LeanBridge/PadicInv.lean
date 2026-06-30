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

`ℚ_[p]` is a complete nontrivially-normed field, so its spectral norm extends `‖·‖` to the
finite extension `K`. An element of `K` whose spectral norm is `≤ 1` is integral over `ℤ_[p]`
(its minimal polynomial has coefficients of norm `≤ 1`, i.e. in `ℤ_[p]`); hence
`𝒪_K = integralClosure ℤ_[p] K` is exactly the closed unit ball of the spectral norm, so it is
a valuation ring. Being a local Dedekind domain that is not a field, it is a DVR. -/

instance : Algebra.IsAlgebraic ℚ_[p] K := Algebra.IsAlgebraic.of_finite ℚ_[p] K

/-- If the spectral norm of `x : K` over `ℚ_[p]` is `≤ 1`, then `x` is integral over `ℤ_[p]`:
the coefficients of its minimal polynomial have norm `≤ 1`, hence lie in `ℤ_[p]`. -/
theorem isIntegral_of_spectralNorm_le_one {x : K} (hx : spectralNorm ℚ_[p] K x ≤ 1) :
    IsIntegral ℤ_[p] x := by
  have hlift : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun i ↦ ?_
    have hi := (ciSup_le_iff (spectralValueTerms_bddAbove ..)).mp hx i
    simp only [spectralValueTerms] at hi
    split_ifs at hi with h
    · conv_rhs at hi => rw [← Real.one_rpow (1 / (↑(minpoly ℚ_[p] x).natDegree - ↑i) : ℝ)]
      rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by aesop)] at hi
      exact ⟨⟨_, hi⟩, rfl⟩
    obtain h | h := (le_of_not_gt h).eq_or_lt
    · rw [← h]
      exact ⟨1, (map_one _).trans
        (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral).symm⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]
      exact ⟨0, map_zero _⟩
  obtain ⟨P, hP, _, hP'⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift
    (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  refine ⟨P, hP', ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[p], hP, minpoly.aeval]

/-- The spectral norm over `ℚ_[p]` is multiplicative, hence inverts. -/
theorem spectralNorm_inv (x : K) :
    spectralNorm ℚ_[p] K x⁻¹ = (spectralNorm ℚ_[p] K x)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [spectralNorm_zero]
  · have h := spectralAlgNorm_mul (K := ℚ_[p]) (L := K) x x⁻¹
    rw [mul_inv_cancel₀ hx0, spectralAlgNorm_def, spectralAlgNorm_def, spectralAlgNorm_def,
      spectralNorm_one] at h
    exact eq_inv_of_mul_eq_one_right h.symm

/-- `𝒪_K = integralClosure ℤ_[p] K` is the closed unit ball of the spectral norm, hence a
valuation ring: every `x : K` has `x` or `x⁻¹` of spectral norm `≤ 1`. -/
instance instValuationRing : ValuationRing (integralClosure ℤ_[p] K) := by
  refine ValuationSubring.instValuationRingSubtypeMem
    (A := ⟨(integralClosure ℤ_[p] K).toSubring, ?_⟩)
  intro x
  obtain hx | hx := le_total (spectralNorm ℚ_[p] K x) 1
  · exact Or.inl (isIntegral_of_spectralNorm_le_one (p := p) (K := K) hx)
  · refine Or.inr (isIntegral_of_spectralNorm_le_one (p := p) (K := K) ?_)
    rw [spectralNorm_inv]
    exact inv_le_one_of_one_le₀ hx

instance isDedekind : IsDedekindDomain (integralClosure ℤ_[p] K) := by
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

/-- The ring of integers of a `p`-adic field is a discrete valuation ring
(blueprint `prop:padic-is-dvf`): `𝒪_K` is a valuation ring (`instValuationRing`, hence local),
a Dedekind domain and not a field, so the DVR characterization applies. -/
instance instIsDiscreteValuationRing :
    IsDiscreteValuationRing (ringOfIntegers p K) := by
  have hD : IsDedekindDomain (integralClosure ℤ_[p] K) := inferInstance
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[p] K) (notField p K)).out 2 0).mp hD

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
