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

omit [PadicField p K] in
theorem algebraMap_padicInt_injective : Function.Injective (algebraMap ℤ_[p] K) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] K, RingHom.coe_comp]
  exact (algebraMap ℚ_[p] K).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

omit [PadicField p K] in
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

/-- The ring of integers `𝒪_K` of a `p`-adic field `K`: the integral closure of
`ℤ_[p]` (the integers of `ℚ_[p]`) in `K`. -/
def ringOfIntegers : Subalgebra ℤ_[p] K := integralClosure ℤ_[p] K

@[inherit_doc] scoped notation "𝒪[" K "]" => PadicField.ringOfIntegers _ K

instance instIsIntegralClosure : IsIntegralClosure (ringOfIntegers p K) ℤ_[p] K :=
  integralClosure.isIntegralClosure ℤ_[p] K

instance : IsFractionRing (ringOfIntegers p K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] K

instance instAlgebraIsIntegralRingOfIntegers : Algebra.IsIntegral ℤ_[p] (ringOfIntegers p K) :=
  inferInstanceAs (Algebra.IsIntegral ℤ_[p] (integralClosure ℤ_[p] K))

instance instFiniteRingOfIntegers : Module.Finite ℤ_[p] (ringOfIntegers p K) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] K (ringOfIntegers p K)

instance instFreeRingOfIntegers : Module.Free ℤ_[p] (ringOfIntegers p K) :=
  IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K (ringOfIntegers p K)

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

omit [PadicField p K] in
theorem notField : ¬ IsField (integralClosure ℤ_[p] K) := by
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
    IsDiscreteValuationRing (ringOfIntegers p K) := by
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
    IsAdicComplete (IsLocalRing.maximalIdeal (ringOfIntegers p K)) (ringOfIntegers p K) := by
  let S := ringOfIntegers p K
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

/-!
### The discriminant exponent and its characterisations (blueprint §1.5, §1.6)
-/

/-- `𝒪_L` is a free `𝒪_K`-module (blueprint `lem:OL-free`), so it carries a chosen
basis used to define the discriminant. -/
instance instModuleFree : Module.Free (ringOfIntegers p K) (ringOfIntegers p L) :=
  (free_finrank p K L).1

/-- The *different exponent* `δ(L / K)` (blueprint `def:different-exponent`): the
exponent of `𝔪_L` in the different ideal `𝔡_{L/K} = differentIdeal 𝒪_K 𝒪_L`, i.e.
the integer `δ` with `𝔡_{L/K} = 𝔪_L ^ δ`. -/
def differentExponent : ℕ :=
  multiplicity (IsLocalRing.maximalIdeal (ringOfIntegers p L))
    (differentIdeal (ringOfIntegers p K) (ringOfIntegers p L))

/-- The *discriminant exponent* `d(L / K) = v_K(disc(L/K))`
(blueprint `def:disc-exponent`): the exponent of `𝔪_K` in the ideal generated by
the discriminant of an `𝒪_K`-basis of `𝒪_L`. The valuation of the discriminant is
independent of the chosen basis (the determinant changes by a unit square). -/
def discriminantExponent : ℕ :=
  multiplicity (IsLocalRing.maximalIdeal (ringOfIntegers p K))
    (Ideal.span {Algebra.discr (ringOfIntegers p K)
      ⇑(Module.Free.chooseBasis (ringOfIntegers p K) (ringOfIntegers p L))})

/-- The discriminant exponent equals the residue degree times the different exponent
(blueprint `prop:disc-eq-f-delta`): `d = f · δ`, since `N_{L/K}(𝔪_L) = 𝔪_K ^ f` and
the discriminant is the norm of the different. -/
theorem discExponent_eq_inertiaDeg_mul_differentExponent :
    discriminantExponent p K L = inertiaDeg p K L * differentExponent p K L := by
  sorry

/-- Dedekind's different theorem (blueprint `thm:dedekind-different`): the different
exponent satisfies `δ ≥ e - 1`, with equality exactly when `L / K` is tamely
ramified (`p ∤ e`). -/
theorem differentExponent_tame :
    ramificationIdx p K L - 1 ≤ differentExponent p K L ∧
      (differentExponent p K L = ramificationIdx p K L - 1 ↔ IsTamelyRamified p K L) := by
  sorry

/-- The discriminant exponent vanishes exactly when `L / K` is unramified
(blueprint `thm:disc-zero-iff-unramified`): `d = 0 ↔ e = 1`. -/
theorem discExponent_eq_zero_iff_unramified :
    discriminantExponent p K L = 0 ↔ IsUnramified p K L := by
  sorry

/-- Tame discriminant exponent (blueprint `cor:tame-disc`): if `L / K` is tamely
ramified then `d = f · (e - 1)`. -/
theorem discExponent_tame (h : IsTamelyRamified p K L) :
    discriminantExponent p K L = inertiaDeg p K L * (ramificationIdx p K L - 1) := by
  sorry

end Extension

end PadicField
