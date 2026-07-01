import Mathlib
import LeanBridge.Mono
import LeanBridge.DiscrAssoc
import LeanBridge.DiscrNormPB

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

/-- A *`p`-adic field* is a finite extension `K / ℚ_[p]`. The prime `p` is an
`outParam`: it is recovered from the field `K` (via its `ℚ_[p]`-algebra
structure), so downstream definitions such as `𝒪 K` need not carry `p`. -/
class PadicField (K : Type*) [Field K] (p : outParam ℕ) [Fact p.Prime] [Algebra ℚ_[p] K] : Prop
    extends Module.Finite ℚ_[p] K

namespace PadicField

variable (K : Type*) [Field K] {p : ℕ} [Fact p.Prime] [Algebra ℚ_[p] K] [PadicField K p]

/-- The canonical `ℤ_[p]`-algebra structure on a `p`-adic field, obtained by
restricting scalars along `ℤ_[p] → ℚ_[p]`. -/
instance instAlgebraPadicInt : Algebra ℤ_[p] K :=
  ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

instance instIsScalarTower : IsScalarTower ℤ_[p] ℚ_[p] K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_padicInt_injective (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Algebra ℚ_[p] K] : Function.Injective (algebraMap ℤ_[p] K) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] K, RingHom.coe_comp]
  exact (algebraMap ℚ_[p] K).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

omit [PadicField K p] in
theorem charZero_of_padicAlgebra (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Algebra ℚ_[p] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective

instance instIsAlgebraic : Algebra.IsAlgebraic ℚ_[p] K :=
  Algebra.IsAlgebraic.of_finite ℚ_[p] K

instance instIsSeparable : Algebra.IsSeparable ℚ_[p] K := by
  haveI : CharZero K := charZero_of_padicAlgebra p K
  exact Algebra.IsSeparable.of_integral ℚ_[p] K

instance instIsTorsionFreePadicInt : Module.IsTorsionFree ℤ_[p] K :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap_padicInt_injective p K)

/-- The ring of integers `𝒪 K` of a `p`-adic field `K`: the integral closure of
`ℤ_[p]` (the integers of `ℚ_[p]`) in `K`. The prime `p` is recovered from the
`PadicField` instance, so it is not an explicit argument. -/
def ringOfIntegers (K : Type*) [Field K] {p : ℕ} [Fact p.Prime] [Algebra ℚ_[p] K]
    [PadicField K p] : Subalgebra ℤ_[p] K := integralClosure ℤ_[p] K

@[inherit_doc] scoped notation "𝒪" => PadicField.ringOfIntegers

instance instIsIntegralClosure : IsIntegralClosure (𝒪 K) ℤ_[p] K :=
  integralClosure.isIntegralClosure ℤ_[p] K

instance : IsFractionRing (𝒪 K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] K

instance instAlgebraIsIntegralRingOfIntegers : Algebra.IsIntegral ℤ_[p] (𝒪 K) :=
  inferInstanceAs (Algebra.IsIntegral ℤ_[p] (integralClosure ℤ_[p] K))

instance instFiniteRingOfIntegers : Module.Finite ℤ_[p] (𝒪 K) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] K (𝒪 K)

instance instFreeRingOfIntegers : Module.Free ℤ_[p] (𝒪 K) :=
  IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K (𝒪 K)

/-! ### Proof that `𝒪_K` is a discrete valuation ring (`prop:padic-is-dvf`)

`ℚ_[p]` is a complete nontrivially-normed field, so its spectral norm extends `‖·‖` to the
finite extension `K`. An element of `K` whose spectral norm is `≤ 1` is integral over `ℤ_[p]`
(its minimal polynomial has coefficients of norm `≤ 1`, i.e. in `ℤ_[p]`); hence
`𝒪_K = integralClosure ℤ_[p] K` is exactly the closed unit ball of the spectral norm, so it is
a valuation ring. Being a local Dedekind domain that is not a field, it is a DVR. -/

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

instance isDedekind : IsDedekindDomain (integralClosure ℤ_[p] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)

theorem notField (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] :
    ¬ IsField (integralClosure ℤ_[p] K) := by
  have hinj : Function.Injective (algebraMap ℤ_[p] (integralClosure ℤ_[p] K)) := by
    have hK := algebraMap_padicInt_injective p K
    rw [IsScalarTower.algebraMap_eq ℤ_[p] (integralClosure ℤ_[p] K) K, RingHom.coe_comp] at hK
    exact hK.of_comp
  intro hF
  exact (IsDiscreteValuationRing.not_isField ℤ_[p])
    ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hF)

/-- The ring of integers of a `p`-adic field is a discrete valuation ring
(blueprint `prop:padic-is-dvf`): `𝒪_K` is a valuation ring (`instValuationRing`, hence local),
a Dedekind domain and not a field, so the DVR characterization applies. -/
instance instIsDiscreteValuationRing :
    IsDiscreteValuationRing (𝒪 K) := by
  have hD : IsDedekindDomain (integralClosure ℤ_[p] K) := inferInstance
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[p] K) (notField p K)).out 2 0).mp hD

private theorem isPrecomplete_of_finite_of_adicComplete
    {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [IsAdicComplete I R] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, hz⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  subst hz
  obtain ⟨m, hm⟩ : ∃ m : M,
      AdicCompletion.ofTensorProduct I M z = AdicCompletion.of I M m := by
    refine TensorProduct.induction_on z ?h0 ?htmul ?hadd
    · exact ⟨0, by simp⟩
    · intro a m
      obtain ⟨r, hr⟩ := AdicCompletion.of_surjective I R a
      refine ⟨r • m, ?_⟩
      rw [← hr]
      rw [AdicCompletion.ofTensorProduct_tmul]
      change (algebraMap R (AdicCompletion I R) r) • (AdicCompletion.of I M m) =
        (AdicCompletion.of I M) (r • m)
      exact (AdicCompletion.of I M).map_smul r m
    · intro z₁ z₂ hz₁ hz₂
      obtain ⟨m₁, hm₁⟩ := hz₁
      obtain ⟨m₂, hm₂⟩ := hz₂
      exact ⟨m₁ + m₂, by simp [hm₁, hm₂]⟩
  exact ⟨m, hm.symm⟩

private theorem isAdicComplete_of_finite_of_adicComplete
    {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [IsHausdorff I M] [IsAdicComplete I R] : IsAdicComplete I M where
  toIsHausdorff := inferInstance
  toIsPrecomplete := isPrecomplete_of_finite_of_adicComplete

private lemma isAdicComplete_of_pow
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R) {e : ℕ} (he : e ≠ 0)
    [IsAdicComplete (I ^ e) M] : IsAdicComplete I M where
  haus' x hx := by
    apply IsHausdorff.haus (show IsHausdorff (I ^ e) M from inferInstance) x
    intro n
    simpa [pow_mul] using hx (e * n)
  prec' f hf := by
    have hg : ∀ {m n : ℕ}, m ≤ n → f (e * m) ≡ f (e * n)
        [SMOD (I ^ e) ^ m • (⊤ : Submodule R M)] := by
      intro m n hmn
      simpa [pow_mul] using hf (Nat.mul_le_mul_left e hmn)
    obtain ⟨L, hL⟩ :=
      (IsPrecomplete.prec (show IsPrecomplete (I ^ e) M from inferInstance)
        (f := fun n => f (e * n))) hg
    refine ⟨L, fun n => ?_⟩
    have hnle : n ≤ e * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero he)
    exact (hf hnle).trans (SModEq.mono (by
      rw [← pow_mul]
      exact Submodule.pow_smul_top_le I M hnle) (hL n))

/-- `𝒪_K` is `𝔪_K`-adically complete (the completeness half of
`prop:padic-is-dvf`): the integral closure of the complete DVR `ℤ_[p]` in a
finite extension is again complete. -/
instance instIsAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal (𝒪 K)) (𝒪 K) := by
  let S := 𝒪 K
  have hZp : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[p]) S := by
    haveI : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[p]) S := inferInstance
    exact isAdicComplete_of_finite_of_adicComplete
  have hmap :
      IsAdicComplete ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)) S :=
    (IsAdicComplete.map_algebraMap_iff (I := IsLocalRing.maximalIdeal ℤ_[p]) (M := S)).mpr hZp
  let J : Ideal S := (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S)
  have hinj : Function.Injective (algebraMap ℤ_[p] S) := by
    have hK := algebraMap_padicInt_injective p K
    rw [IsScalarTower.algebraMap_eq ℤ_[p] S K, RingHom.coe_comp] at hK
    exact hK.of_comp
  have hmZp_bot : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := by
    intro h
    exact (IsDiscreteValuationRing.not_isField ℤ_[p])
      ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  have hJbot : J ≠ ⊥ := by
    dsimp [J]
    rw [Ideal.map_eq_bot_iff_of_injective hinj]
    exact hmZp_bot
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨e, hJe⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (R := S) hJbot hϖ
  have hJm : J = IsLocalRing.maximalIdeal S ^ e := by
    rw [hJe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have halgint : (algebraMap ℤ_[p] S).IsIntegral := by
    exact Algebra.IsIntegral.isIntegral (R := ℤ_[p]) (A := S)
  have hJtop_ne : J ≠ ⊤ := by
    dsimp [J]
    rw [Ideal.map_eq_top_iff (algebraMap ℤ_[p] S) hinj halgint]
    exact (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top
  have he : e ≠ 0 := by
    intro he0
    apply hJtop_ne
    simp [hJm, he0]
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal S ^ e) S := by
    rwa [← hJm]
  exact isAdicComplete_of_pow (M := S) (IsLocalRing.maximalIdeal S) he

-- TODO : instance : IsNonarchimedeanLocalField K

/-!
## Invariants of an extension `L / K` (blueprint §1.2, §1.3, §1.4)
-/

namespace Extension

variable (L : Type*) [Field L] [Algebra ℚ_[p] L] [PadicField L p]
  [Algebra K L] [Module.Finite K L] [IsScalarTower ℚ_[p] K L]

/-- `ℤ_[p]` acts on `L` through `K`, compatibly with its action through `ℚ_[p]`. -/
instance instIsScalarTowerPadicInt : IsScalarTower ℤ_[p] K L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    have hK : algebraMap ℤ_[p] K x = algebraMap ℚ_[p] K (algebraMap ℤ_[p] ℚ_[p] x) := rfl
    have hL : algebraMap ℤ_[p] L x = algebraMap ℚ_[p] L (algebraMap ℤ_[p] ℚ_[p] x) := rfl
    rw [hK, hL, IsScalarTower.algebraMap_apply ℚ_[p] K L]

/-- The inclusion `𝒪_K → 𝒪_L` of rings of integers induced by `K → L`: an
element integral over `ℤ_[p]` stays integral after embedding into `L`. -/
def ringOfIntegersMap : 𝒪 K →+* 𝒪 L where
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
instance instAlgebraRingOfIntegers : Algebra (𝒪 K) (𝒪 L) :=
  (ringOfIntegersMap K L).toAlgebra

/-- The *ramification index* `e(L / K)` of an extension of `p`-adic fields
(blueprint `def:ramification-index`): the ramification index of the maximal
ideal `𝔪_K` of `𝒪_K` in `𝒪_L`. Equivalently `v_L(π_K) = e`, `𝔪_K 𝒪_L = 𝔪_L ^ e`. -/
def ramificationIdx : ℕ :=
  Ideal.ramificationIdx (R := 𝒪 K) (S := 𝒪 L)
    (IsLocalRing.maximalIdeal (𝒪 K))
    (IsLocalRing.maximalIdeal (𝒪 L))

/-- `L / K` is *unramified* when `e = 1` (blueprint `def:tame-wild`). -/
def IsUnramified : Prop := ramificationIdx K L = 1

/-- `L / K` is *ramified* when `e > 1` (blueprint `def:tame-wild`). -/
def IsRamified : Prop := 1 < ramificationIdx K L

/-- `L / K` is *tamely ramified* when `p ∤ e` (blueprint `def:tame-wild`). -/
def IsTamelyRamified : Prop := ¬ (p : ℕ) ∣ ramificationIdx K L

/-- `L / K` is *wildly ramified* when `p ∣ e` (blueprint `def:tame-wild`). -/
def IsWildlyRamified : Prop := (p : ℕ) ∣ ramificationIdx K L

/-!
### The residue degree and the identity `e * f = [L : K]` (blueprint §1.4)
-/

-- Shared structural instances for `L / K`, used by both results below.

/-- `ℤ_[p]` acts on `L` through `𝒪_K`. -/
instance : IsScalarTower ℤ_[p] (𝒪 K) L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (𝒪 K) K L,
        ← IsScalarTower.algebraMap_apply ℤ_[p] (𝒪 K) K]
    exact IsScalarTower.algebraMap_apply ℤ_[p] K L x

/-- `𝒪_K` acts on `L` through `𝒪_L`. -/
instance : IsScalarTower (𝒪 K) (𝒪 L) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : Algebra.IsIntegral ℤ_[p] (𝒪 K) :=
  inferInstanceAs (Algebra.IsIntegral ℤ_[p] (integralClosure ℤ_[p] K))

/-- `𝒪_L` is the integral closure of `𝒪_K` in `L`: an element of `L` is integral
over `𝒪_K` iff it is integral over `ℤ_[p]`. -/
instance : IsIntegralClosure (𝒪 L) (𝒪 K) L := by
  constructor
  · exact Subtype.coe_injective
  · intro x
    refine ⟨fun hx => ⟨⟨x, isIntegral_trans (R := ℤ_[p]) x hx⟩, rfl⟩, ?_⟩
    rintro ⟨y, rfl⟩
    exact (show IsIntegral ℤ_[p] (y : L) from y.2).tower_top

instance : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L

theorem isSeparable_of_padicExtension (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [Algebra ℚ_[p] K]
    (L : Type*) [Field L] [Algebra K L] [Module.Finite K L] :
    Algebra.IsSeparable K L := by
  haveI : CharZero K := charZero_of_padicAlgebra p K
  exact Algebra.IsSeparable.of_integral K L

/-- `K` has characteristic zero (it contains `ℚ_[p]`), hence `L / K` is separable.
Phrased over `𝒪_K` so that `p` is fixed by the statement. -/
instance : Module.Finite (𝒪 K) (𝒪 L) := by
  haveI : Algebra.IsSeparable K L := isSeparable_of_padicExtension p K L
  exact IsIntegralClosure.finite (𝒪 K) K L (𝒪 L)

instance : FaithfulSMul (𝒪 K) (𝒪 L) :=
  (faithfulSMul_iff_algebraMap_injective (𝒪 K) (𝒪 L)).2
    fun _ _ hab => Subtype.ext ((algebraMap K L).injective (Subtype.ext_iff.1 hab))

instance : Module.IsTorsionFree (𝒪 K) L :=
  .trans_faithfulSMul (𝒪 K) (𝒪 L) L

/-- `𝒪 L` is a finite free `𝒪 K`-module of rank `[L : K]`
(blueprint `lem:OL-free`, Tian Lemma 9.1.1).

The blueprint argument lifts a `k_K`-basis of `𝒪_L / π_K 𝒪_L` and uses
`π_K`-adic completeness; we instead invoke the structure theory of finitely
generated modules over the PID `𝒪_K` (the same theorem), via `𝒪_L` being the
integral closure of `𝒪_K` in `L`. -/
theorem free_finrank :
    Module.Free (𝒪 K) (𝒪 L) ∧
      Module.finrank (𝒪 K) (𝒪 L) = Module.finrank K L := by
  haveI : Algebra.IsSeparable K L := isSeparable_of_padicExtension p K L
  exact ⟨IsIntegralClosure.module_free (𝒪 K) K L (𝒪 L),
         IsIntegralClosure.rank (𝒪 K) K L (𝒪 L)⟩

/-- The *residue degree* `f(L / K)` of an extension of `p`-adic fields
(blueprint `def:residue-degree`): `f = [k_L : k_K]`, realised as the inertia
degree of `𝔪_K` in `𝒪_L`. -/
def inertiaDeg : ℕ :=
  Ideal.inertiaDeg (R := 𝒪 K) (S := 𝒪 L)
    (IsLocalRing.maximalIdeal (𝒪 K))
    (IsLocalRing.maximalIdeal (𝒪 L))

/-- The fundamental identity `e * f = [L : K]`
(blueprint `prop:ef-eq-degree`, Tian Prop. 9.1.4).

This is `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`, the local (DVR)
case of `Ideal.sum_ramification_inertia`, specialised to the rings of integers
of the `p`-adic fields `K ⊆ L`. -/
theorem ramificationIdx_mul_inertiaDeg :
    ramificationIdx K L * inertiaDeg K L = Module.finrank K L := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have hp0 : IsLocalRing.maximalIdeal (𝒪 K) ≠ ⊥ := fun h =>
    IsDiscreteValuationRing.not_isField (𝒪 K)
      ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  simpa only [ramificationIdx, inertiaDeg] using
    Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
      (R := 𝒪 K) (S := 𝒪 L) (K := K) (L := L) hp0

/-!
### The discriminant exponent and its characterisations (blueprint §1.5, §1.6)
-/

/-- `𝒪_L` is a free `𝒪_K`-module (blueprint `lem:OL-free`), so it carries a chosen
basis used to define the discriminant. -/
instance instModuleFree : Module.Free (𝒪 K) (𝒪 L) :=
  (free_finrank K L).1

/-- The *different exponent* `δ(L / K)` (blueprint `def:different-exponent`): the
exponent of `𝔪_L` in the different ideal `𝔡_{L/K} = differentIdeal 𝒪_K 𝒪_L`, i.e.
the integer `δ` with `𝔡_{L/K} = 𝔪_L ^ δ`. -/
def differentExponent : ℕ :=
  multiplicity (IsLocalRing.maximalIdeal (𝒪 L))
    (differentIdeal (𝒪 K) (𝒪 L))

/-- The *discriminant exponent* `d(L / K) = v_K(disc(L/K))`
(blueprint `def:disc-exponent`): the exponent of `𝔪_K` in the ideal generated by
the discriminant of an `𝒪_K`-basis of `𝒪_L`. The valuation of the discriminant is
independent of the chosen basis (the determinant changes by a unit square). -/
def discriminantExponent : ℕ :=
  multiplicity (IsLocalRing.maximalIdeal (𝒪 K))
    (Ideal.span {Algebra.discr (𝒪 K)
      ⇑(Module.Free.chooseBasis (𝒪 K) (𝒪 L))})

/-! ### Reduction of the discriminant identities to a single bridge lemma

The discriminant statements below rest on the relative identity `disc(L/K) =
N_{L/K}(𝔡_{L/K})` (`relNorm_differentIdeal_eq_span_discr`). Given that identity,
`d = f · δ` and `d = 0 ↔ e = 1` are valuation-theoretic computations in the DVRs
`𝒪_K`, `𝒪_L`, using `N_{L/K}(𝔪_L) = 𝔪_K ^ f` and multiplicities. -/

attribute [local instance] FractionRing.liftAlgebra

/-- In a discrete valuation ring, `multiplicity 𝔪 (𝔪 ^ n) = n`. -/
private theorem multiplicity_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) :
    multiplicity (IsLocalRing.maximalIdeal R) ((IsLocalRing.maximalIdeal R) ^ n) = n := by
  refine multiplicity_pow_self ?_ ?_ n
  · rw [Ideal.zero_eq_bot]; exact IsDiscreteValuationRing.not_a_field R
  · exact Ideal.isUnit_iff.not.mpr (IsLocalRing.maximalIdeal.isMaximal R).ne_top

/-- In a discrete valuation ring, a nonzero ideal is `𝔪 ^ (multiplicity 𝔪 I)`. -/
private theorem eq_maximalIdeal_pow_multiplicity {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {I : Ideal R} (hI : I ≠ ⊥) :
    I = (IsLocalRing.maximalIdeal R) ^ (multiplicity (IsLocalRing.maximalIdeal R) I) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have hIn : I = (IsLocalRing.maximalIdeal R) ^ n := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  have hmult : multiplicity (IsLocalRing.maximalIdeal R) I = n := by
    rw [hIn]; exact multiplicity_maximalIdeal_pow n
  rw [hmult]; exact hIn

/-- Separability of `L / K` transported to the canonical fraction rings of `𝒪_K`,
`𝒪_L`, as required by Mathlib's relative different-ideal API. -/
theorem separable_fractionRing :
    Algebra.IsSeparable (FractionRing (𝒪 K)) (FractionRing (𝒪 L)) := by
  haveI : Algebra.IsSeparable K L := isSeparable_of_padicExtension p K L
  refine Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv (𝒪 K) K).symm.toRingEquiv
    (FractionRing.algEquiv (𝒪 L) L).symm.toRingEquiv ?_
  ext x
  have h := IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝒪 K) K)
    (FractionRing.algEquiv (𝒪 L) L) ((FractionRing.algEquiv (𝒪 K) K).symm x)
  simp only [AlgEquiv.apply_symm_apply] at h
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact (AlgEquiv.eq_symm_apply _).mpr h.symm

theorem inertiaDeg_ne_zero : inertiaDeg K L ≠ 0 :=
  (Ideal.inertiaDeg_pos (IsLocalRing.maximalIdeal (𝒪 K))
    (IsLocalRing.maximalIdeal (𝒪 L))).ne'

set_option maxHeartbeats 800000 in
/-- **Bridge lemma (A), blueprint `prop:disc-eq-f-delta` core.** The relative
"discriminant equals the norm of the different": `N_{L/K}(𝔡_{L/K}) = (disc(L/K))`
as ideals of `𝒪_K`.

Proof: monogenicity `𝒪_L = 𝒪_K[θ]` (`mono_exists_primitive`) unlocks Mathlib's
single-generator different formula `conductor_mul_differentIdeal`, giving
`𝔡_{L/K} = span {f'(θ)}` with `f = minpoly 𝒪_K θ`. Taking `relNorm`
(`Ideal.relNorm_singleton`) turns this into `span {intNorm(f'(θ))}`, and the
classical discriminant-derivative-norm identity descended from `K` to `𝒪_K`
(`intNorm_deriv_minpoly_associated_discr`) together with basis-independence of the
discriminant (`Algebra.discr_associated_of_basis`) identifies it with
`span {disc(L/K)}`. -/
theorem relNorm_differentIdeal_eq_span_discr :
    Ideal.relNorm (𝒪 K) (differentIdeal (𝒪 K) (𝒪 L)) =
      Ideal.span {Algebra.discr (𝒪 K) ⇑(Module.Free.chooseBasis (𝒪 K) (𝒪 L))} := by
  classical
  haveI : CharZero K := charZero_of_padicAlgebra p K
  haveI : Algebra.IsSeparable K L := isSeparable_of_padicExtension p K L
  haveI : Algebra.IsIntegral (𝒪 K) (𝒪 L) := Algebra.IsIntegral.of_finite _ _
  haveI : Module.IsTorsionFree (𝒪 K) (𝒪 L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective (𝒪 K) (𝒪 L))
  haveI : IsScalarTower (𝒪 K) K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- `algebraMap 𝒪_K → 𝒪_L` is local: `𝔪_K = comap 𝔪_L`.
  haveI hlh : IsLocalHom (algebraMap (𝒪 K) (𝒪 L)) := by
    have hcomap : Ideal.comap (algebraMap (𝒪 K) (𝒪 L))
        (IsLocalRing.maximalIdeal (𝒪 L)) = IsLocalRing.maximalIdeal (𝒪 K) :=
      Ideal.LiesOver.over.symm
    exact ((IsLocalRing.local_hom_TFAE (algebraMap (𝒪 K) (𝒪 L))).out 4 0).mp hcomap
  -- residue extension is separable (finite residue fields are perfect).
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField (𝒪 K))
      (IsLocalRing.ResidueField (𝒪 L)) := by
    haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
    haveI hfinK : Finite (IsLocalRing.ResidueField (𝒪 K)) := by
      haveI : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
        Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
      exact IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[p]) (S := 𝒪 K) inferInstance
    haveI : Module.Finite (IsLocalRing.ResidueField (𝒪 K))
        (IsLocalRing.ResidueField (𝒪 L)) := IsLocalRing.ResidueField.finite_of_module_finite
    haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField (𝒪 K))
        (IsLocalRing.ResidueField (𝒪 L)) := Algebra.IsAlgebraic.of_finite _ _
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- monogenicity: `𝒪_L = 𝒪_K[θ]`.
  obtain ⟨θ, hθtop⟩ : ∃ θ : 𝒪 L, Algebra.adjoin (𝒪 K) ({θ} : Set (𝒪 L)) = ⊤ :=
    Neukirch.Chapter2.Sections8to10.mono_exists_primitive
  have hθ_int : IsIntegral (𝒪 K) θ := Algebra.IsIntegral.isIntegral θ
  -- the integral power basis with generator `θ`.
  let e : ↥(Algebra.adjoin (𝒪 K) ({θ} : Set (𝒪 L))) ≃ₐ[𝒪 K] (𝒪 L) :=
    (Subalgebra.equivOfEq _ _ hθtop).trans Subalgebra.topEquiv
  let pb : PowerBasis (𝒪 K) (𝒪 L) := (Algebra.adjoin.powerBasis' hθ_int).map e
  have hpb_gen : pb.gen = θ := by
    show e (Algebra.adjoin.powerBasis' hθ_int).gen = θ
    rw [Algebra.adjoin.powerBasis'_gen]; rfl
  -- generator viewed in `L`, its `K`-integrality and minimal polynomial.
  have hθL_int : IsIntegral K (algebraMap (𝒪 L) L θ) := Algebra.IsIntegral.isIntegral _
  have hmin : minpoly K (algebraMap (𝒪 L) L θ) =
      Polynomial.map (algebraMap (𝒪 K) K) (minpoly (𝒪 K) θ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hθ_int
  -- degree bookkeeping: `deg f = [L:K]`.
  have hfdeg : (minpoly (𝒪 K) θ).natDegree = Module.finrank K L := by
    have h1 : pb.dim = (minpoly (𝒪 K) θ).natDegree := by
      show (Algebra.adjoin.powerBasis' hθ_int).dim = _
      rw [Algebra.adjoin.powerBasis'_dim]
    have h2 : Module.finrank (𝒪 K) (𝒪 L) = pb.dim := pb.finrank
    rw [← h1, ← h2]; exact (free_finrank K L).2
  have hdegK : (minpoly K (algebraMap (𝒪 L) L θ)).natDegree =
      (minpoly (𝒪 K) θ).natDegree := by
    rw [hmin, Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (𝒪 K) K)]
  -- `K⟮θ⟯ = ⊤`, the hypothesis of `conductor_mul_differentIdeal`.
  have hxK : Algebra.adjoin K {algebraMap (𝒪 L) L θ} = ⊤ := by
    have hsub : (Algebra.adjoin K {algebraMap (𝒪 L) L θ}).toSubmodule = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      show Module.finrank K ↥(Algebra.adjoin K {algebraMap (𝒪 L) L θ}) = Module.finrank K L
      rw [(Algebra.adjoin.powerBasis' hθL_int).finrank, Algebra.adjoin.powerBasis'_dim,
        hdegK, hfdeg]
    have htop : (⊤ : Subalgebra K L).toSubmodule = (⊤ : Submodule K L) := by ext x; simp
    exact Subalgebra.toSubmodule_injective (hsub.trans htop.symm)
  -- the conductor is trivial, so the different is `span {f'(θ)}`.
  have hcond : conductor (𝒪 K) θ = ⊤ := by
    rw [Ideal.eq_top_iff_one, mem_conductor_iff]
    intro b
    rw [one_mul, hθtop]
    exact Algebra.mem_top
  have hdiff : differentIdeal (𝒪 K) (𝒪 L) =
      Ideal.span {Polynomial.aeval θ (Polynomial.derivative (minpoly (𝒪 K) θ))} := by
    have h := conductor_mul_differentIdeal (𝒪 K) K L θ hxK
    rwa [hcond, Ideal.top_mul] at h
  -- discriminant = ± norm of the derivative (via the power basis), and basis independence.
  have hG2 := intNorm_deriv_minpoly_associated_discr (K := K) (L := L) pb
  rw [hpb_gen] at hG2
  have hG1 := Algebra.discr_associated_of_basis (R := 𝒪 K)
    pb.basis (Module.Free.chooseBasis (𝒪 K) (𝒪 L))
  rw [hdiff, Ideal.relNorm_singleton]
  exact Ideal.span_singleton_eq_span_singleton.mpr (hG2.trans hG1)

open IsLocalRing in
/-- `𝔪_L` is unramified over `𝒪_K` iff `e(L/K) = 1`. The forward direction is
`Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`; the converse uses separability of the
residue-field extension `k_L / k_K`, which holds because the residue fields are finite
(so perfect): `k_K` is finite as `𝒪_K` is module-finite over `ℤ_[p]` whose residue field
is `ZMod p`. -/
theorem isUnramifiedAt_maximalIdeal_iff :
    Algebra.IsUnramifiedAt (𝒪 K) (IsLocalRing.maximalIdeal (𝒪 L)) ↔ IsUnramified K L := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  haveI hfin : Finite (IsLocalRing.ResidueField (𝒪 K)) := by
    haveI : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
      Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
    exact IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[p]) (S := 𝒪 K) inferInstance
  have hp : maximalIdeal (𝒪 L) ≠ ⊥ := IsDiscreteValuationRing.not_a_field (𝒪 L)
  have hover : Ideal.under (𝒪 K) (maximalIdeal (𝒪 L)) = maximalIdeal (𝒪 K) :=
    Ideal.LiesOver.over.symm
  letI := Localization.AtPrime.algebraOfLiesOver
    (Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))) (maximalIdeal (𝒪 L))
  haveI hfinL : Finite (𝒪 L ⧸ maximalIdeal (𝒪 L)) := by
    haveI : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
      Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
    exact IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[p]) (S := 𝒪 L) inferInstance
  haveI : Algebra.IsIntegral (𝒪 K) (𝒪 L) := Algebra.IsIntegral.of_finite _ _
  haveI : Finite (𝒪 K ⧸ Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))) := by rw [hover]; exact hfin
  haveI : Finite ((Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))).ResidueField) := inferInstance
  haveI : Finite ((maximalIdeal (𝒪 L)).ResidueField) := inferInstance
  haveI : PerfectField ((Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))).ResidueField) := inferInstance
  haveI : Algebra.IsAlgebraic ((Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))).ResidueField)
      ((maximalIdeal (𝒪 L)).ResidueField) := inferInstance
  have hsep : Algebra.IsSeparable ((Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))).ResidueField)
      ((maximalIdeal (𝒪 L)).ResidueField) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [Algebra.isUnramifiedAt_iff_map_eq (𝒪 K)
      (Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))) (maximalIdeal (𝒪 L)),
    and_iff_right hsep,
    ← Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hp Ideal.map_comap_le]
  show Ideal.ramificationIdx (Ideal.under (𝒪 K) (maximalIdeal (𝒪 L)))
      (maximalIdeal (𝒪 L)) = 1 ↔ IsUnramified K L
  rw [hover]
  exact Iff.rfl

/-- The discriminant exponent equals the residue degree times the different exponent
(blueprint `prop:disc-eq-f-delta`): `d = f · δ`, since `N_{L/K}(𝔪_L) = 𝔪_K ^ f` and
the discriminant is the norm of the different (`relNorm_differentIdeal_eq_span_discr`). -/
theorem discExponent_eq_inertiaDeg_mul_differentExponent :
    discriminantExponent K L = inertiaDeg K L * differentExponent K L := by
  haveI : CharZero K := charZero_of_padicAlgebra p K
  haveI : Algebra.IsSeparable (FractionRing (𝒪 K)) (FractionRing (𝒪 L)) :=
    separable_fractionRing K L
  have hd : differentIdeal (𝒪 K) (𝒪 L) ≠ ⊥ := differentIdeal_ne_bot
  have hdpow : differentIdeal (𝒪 K) (𝒪 L) =
      (IsLocalRing.maximalIdeal (𝒪 L)) ^ (differentExponent K L) :=
    eq_maximalIdeal_pow_multiplicity hd
  have hrelmax : Ideal.relNorm (𝒪 K) (IsLocalRing.maximalIdeal (𝒪 L)) =
      (IsLocalRing.maximalIdeal (𝒪 K)) ^ (inertiaDeg K L) :=
    Ideal.relNorm_eq_pow_of_isMaximal _ _
  have key : Ideal.span {Algebra.discr (𝒪 K) ⇑(Module.Free.chooseBasis (𝒪 K) (𝒪 L))}
      = (IsLocalRing.maximalIdeal (𝒪 K)) ^ (inertiaDeg K L * differentExponent K L) := by
    rw [← relNorm_differentIdeal_eq_span_discr K L, hdpow, map_pow, hrelmax, ← pow_mul]
  show multiplicity (IsLocalRing.maximalIdeal (𝒪 K))
      (Ideal.span {Algebra.discr (𝒪 K) ⇑(Module.Free.chooseBasis (𝒪 K) (𝒪 L))}) = _
  rw [key]; exact multiplicity_maximalIdeal_pow _

open IsLocalRing in
/-- Dedekind's different theorem (blueprint `thm:dedekind-different`): the different
exponent satisfies `δ ≥ e - 1`, with equality exactly when `L / K` is tamely
ramified (`p ∤ e`).

The lower bound `e - 1 ≤ δ` is proved: `𝔪_L ^ e ∣ 𝔪_K 𝒪_L` (by definition of the
ramification index), so `Ideal.pow_sub_one_dvd_differentIdeal` gives `𝔪_L ^ (e-1) ∣ 𝔡`,
whence `e - 1 ≤ v_{𝔪_L}(𝔡) = δ`. The sharp equivalence `δ = e - 1 ↔ p ∤ e` is the
wild-ramification part of Dedekind's theorem (needs the trace/higher-ramification
computation showing `𝔪_L ^ e ∤ 𝔡` exactly in the tame case); it is not yet available
in Mathlib and is left as `sorry`. -/
theorem differentExponent_tame :
    ramificationIdx K L - 1 ≤ differentExponent K L ∧
      (differentExponent K L = ramificationIdx K L - 1 ↔ IsTamelyRamified K L) := by
  haveI : CharZero K := charZero_of_padicAlgebra p K
  haveI : Algebra.IsSeparable (FractionRing (𝒪 K)) (FractionRing (𝒪 L)) :=
    separable_fractionRing K L
  refine ⟨?_, ?_⟩
  · have hmK : maximalIdeal (𝒪 K) ≠ ⊥ := IsDiscreteValuationRing.not_a_field (𝒪 K)
    have hdvd : (maximalIdeal (𝒪 L)) ^ (ramificationIdx K L) ∣
        (maximalIdeal (𝒪 K)).map (algebraMap (𝒪 K) (𝒪 L)) :=
      Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx
    have hd : differentIdeal (𝒪 K) (𝒪 L) ≠ ⊥ := differentIdeal_ne_bot
    have hdvd' : (maximalIdeal (𝒪 L)) ^ (ramificationIdx K L - 1) ∣
        differentIdeal (𝒪 K) (𝒪 L) :=
      pow_sub_one_dvd_differentIdeal (P := maximalIdeal (𝒪 L)) (e := ramificationIdx K L)
        (hp := hmK) (hP := hdvd)
    have hfin : FiniteMultiplicity (maximalIdeal (𝒪 L)) (differentIdeal (𝒪 K) (𝒪 L)) :=
      FiniteMultiplicity.of_not_isUnit
        (Ideal.isUnit_iff.not.mpr (IsLocalRing.maximalIdeal.isMaximal (𝒪 L)).ne_top)
        (by rw [Ideal.zero_eq_bot]; exact hd)
    exact hfin.le_multiplicity_of_pow_dvd hdvd'
  · sorry

/-- The discriminant exponent vanishes exactly when `L / K` is unramified
(blueprint `thm:disc-zero-iff-unramified`): `d = 0 ↔ e = 1`. -/
theorem discExponent_eq_zero_iff_unramified :
    discriminantExponent K L = 0 ↔ IsUnramified K L := by
  haveI : CharZero K := charZero_of_padicAlgebra p K
  haveI : Algebra.IsSeparable (FractionRing (𝒪 K)) (FractionRing (𝒪 L)) :=
    separable_fractionRing K L
  have hd : differentIdeal (𝒪 K) (𝒪 L) ≠ ⊥ := differentIdeal_ne_bot
  rw [discExponent_eq_inertiaDeg_mul_differentExponent K L, Nat.mul_eq_zero,
    or_iff_right (inertiaDeg_ne_zero K L)]
  show multiplicity (IsLocalRing.maximalIdeal (𝒪 L)) (differentIdeal (𝒪 K) (𝒪 L)) = 0 ↔ _
  rw [multiplicity_eq_zero, not_dvd_differentIdeal_iff]
  exact isUnramifiedAt_maximalIdeal_iff K L

/-- Tame discriminant exponent (blueprint `cor:tame-disc`): if `L / K` is tamely
ramified then `d = f · (e - 1)`. Immediate from `d = f · δ`
(`discExponent_eq_inertiaDeg_mul_differentExponent`) and the tame equality `δ = e - 1`
(`differentExponent_tame`). -/
theorem discExponent_tame (h : IsTamelyRamified K L) :
    discriminantExponent K L = inertiaDeg K L * (ramificationIdx K L - 1) := by
  rw [discExponent_eq_inertiaDeg_mul_differentExponent K L,
    (differentExponent_tame K L).2.mpr h]

end Extension

end PadicField
