import LeanBridge.Basic

/-!
# Ramification invariants of extensions of `p`-adic fields
-/

noncomputable section

open scoped PadicField

namespace PadicField

open RingOfIntegers

variable (K : Type*) [Field K] {p : ℕ} [Fact p.Prime] [Algebra ℚ_[p] K] [PadicField K p]

/-- The *base ramification index* `e₀ = e(K / ℚ_p)`: the
ramification index of the maximal ideal `(p) = 𝔪_{ℤ_[p]}` in `𝒪_K`. -/
def baseRamificationIndex : ℕ :=
  Ideal.ramificationIdx (R := ℤ_[p]) (S := 𝓞 K)
    (IsLocalRing.maximalIdeal ℤ_[p]) (IsLocalRing.maximalIdeal (𝓞 K))

/-!
## Invariants of an extension `L / K`
-/

namespace Extension

variable (L : Type*) [Field L] [Algebra ℚ_[p] L] [PadicField L p]
  [Algebra K L] [Module.Finite K L] [IsScalarTower ℚ_[p] K L]

/-- The *ramification index* `e(L / K)` of an extension of `p`-adic fields:
the ramification index of the maximal ideal `𝔪_K` of `𝒪_K` in `𝒪_L`.
Equivalently `v_L(π_K) = e`, `𝔪_K 𝒪_L = 𝔪_L ^ e`. -/
def ramificationIdx : ℕ :=
  Ideal.ramificationIdx (R := 𝓞 K) (S := 𝓞 L)
    (IsLocalRing.maximalIdeal (𝓞 K))
    (IsLocalRing.maximalIdeal (𝓞 L))

/-- The *absolute ramification index* `e_abs = e(L / ℚ_p)`:
the ramification index of the maximal ideal `(p) = 𝔪_{ℤ_[p]}` in `𝒪_L`. -/
def absoluteRamificationIndex : ℕ :=
  Ideal.ramificationIdx (R := ℤ_[p]) (S := 𝓞 L)
    (IsLocalRing.maximalIdeal ℤ_[p]) (IsLocalRing.maximalIdeal (𝓞 L))

/-- `L / K` is *unramified* when `e = 1`. -/
def IsUnramified : Prop := ramificationIdx K L = 1

/-- `L / K` is *ramified* when `e > 1`. -/
def IsRamified : Prop := 1 < ramificationIdx K L

/-- `L / K` is *tamely ramified* when `p ∤ e`. -/
def IsTamelyRamified : Prop := ¬ (p : ℕ) ∣ ramificationIdx K L

/-- `L / K` is *wildly ramified* when `p ∣ e`. -/
def IsWildlyRamified : Prop := (p : ℕ) ∣ ramificationIdx K L

/-- The *wild ramification exponent* `w` of `L / K`: the
exponent of `p` in `e`, i.e. `e = p ^ w · e_tame` with `p ∤ e_tame`. Concretely the
`p`-adic valuation of the ramification index. -/
def wildRamificationExponent : ℕ := padicValNat p (ramificationIdx K L)

/-- The *tame ramification index* `e_tame` of `L / K`: the
prime-to-`p` part of `e`, so that `e = p ^ w · e_tame`. -/
def tameRamificationIndex : ℕ :=
  ramificationIdx K L / p ^ wildRamificationExponent K L

/-!
### The residue degree and the identity `e * f = [L : K]` (blueprint §1.4)
-/

-- Shared structural instances for `L / K`, used by both results below.

-- instance : Algebra.IsIntegral ℤ_[p] (𝓞 K) :=
--   inferInstanceAs (Algebra.IsIntegral ℤ_[p] (integralClosure ℤ_[p] K))

/-- `𝒪_L` is the integral closure of `𝒪_K` in `L`: an element of `L` is integral
over `𝒪_K` iff it is integral over `ℤ_[p]`. -/
instance : IsIntegralClosure (𝓞 L) (𝓞 K) L := by
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

instance instIsAlgebraicFieldExtension : Algebra.IsAlgebraic K L :=
  Algebra.IsAlgebraic.of_finite K L

/-- `K` has characteristic zero (it contains `ℚ_[p]`), hence `L / K` is separable.
Phrased over `𝒪_K` so that `p` is fixed by the statement. -/
instance : Module.Finite (𝓞 K) (𝓞 L) := by
  letI : IsFractionRing (𝓞 K) K := RingOfIntegers.instIsFractionRing (K := K)
  letI : IsFractionRing (𝓞 L) L := RingOfIntegers.instIsFractionRing (K := L)
  haveI : Algebra.IsSeparable K L := isSeparable_of_padicExtension p K L
  exact IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)

instance : FaithfulSMul (𝓞 K) (𝓞 L) :=
  (faithfulSMul_iff_algebraMap_injective (𝓞 K) (𝓞 L)).2
    fun _ _ hab => Subtype.ext ((algebraMap K L).injective (Subtype.ext_iff.1 hab))

instance : Module.IsTorsionFree (𝓞 K) L :=
  .trans_faithfulSMul (𝓞 K) (𝓞 L) L

instance instAlgebraIsIntegralRingOfIntegersExtension : Algebra.IsIntegral (𝓞 K) (𝓞 L) :=
  Algebra.IsIntegral.of_finite _ _

instance instIsTorsionFreeRingOfIntegersExtension : Module.IsTorsionFree (𝓞 K) (𝓞 L) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr
    (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))

instance instIsLocalHomRingOfIntegersMap : IsLocalHom (algebraMap (𝓞 K) (𝓞 L)) := by
  have hcomap : Ideal.comap (algebraMap (𝓞 K) (𝓞 L))
      (IsLocalRing.maximalIdeal (𝓞 L)) = IsLocalRing.maximalIdeal (𝓞 K) :=
    Ideal.LiesOver.over.symm
  exact ((IsLocalRing.local_hom_TFAE (algebraMap (𝓞 K) (𝓞 L))).out 4 0).mp hcomap

instance instModuleFiniteResidueFieldRingOfIntegersExtension :
    Module.Finite (IsLocalRing.ResidueField (𝓞 K)) (IsLocalRing.ResidueField (𝓞 L)) :=
  IsLocalRing.ResidueField.finite_of_module_finite

instance instIsAlgebraicResidueFieldRingOfIntegersExtension :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField (𝓞 K)) (IsLocalRing.ResidueField (𝓞 L)) :=
  Algebra.IsAlgebraic.of_finite _ _

instance instIsSeparableResidueFieldRingOfIntegersExtension :
    Algebra.IsSeparable (IsLocalRing.ResidueField (𝓞 K)) (IsLocalRing.ResidueField (𝓞 L)) :=
  haveI : PerfectField (IsLocalRing.ResidueField (𝓞 K)) := inferInstance
  Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- Transitivity of ramification: the absolute
ramification index is the product of the relative and base ones, `e_abs = e · e₀`. -/
theorem absoluteRamificationIndex_eq :
    absoluteRamificationIndex L = ramificationIdx K L * baseRamificationIndex K := by
  have hinjKL : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)
  have hinjZL : Function.Injective (algebraMap ℤ_[p] (𝓞 L)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] (𝓞 K) (𝓞 L), RingHom.coe_comp]
    exact hinjKL.comp (FaithfulSMul.algebraMap_injective ℤ_[p] (𝓞 K))
  have hmK : IsLocalRing.maximalIdeal (𝓞 K) ≠ ⊥ := IsDiscreteValuationRing.not_a_field (𝓞 K)
  have hmZ : IsLocalRing.maximalIdeal ℤ_[p] ≠ ⊥ := IsDiscreteValuationRing.not_a_field ℤ_[p]
  have hg0 : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) (IsLocalRing.maximalIdeal (𝓞 K)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hinjKL).not.mpr hmK
  have hfg : Ideal.map (algebraMap ℤ_[p] (𝓞 L)) (IsLocalRing.maximalIdeal ℤ_[p]) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hinjZL).not.mpr hmZ
  have hg : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) (IsLocalRing.maximalIdeal (𝓞 K)) ≤
      IsLocalRing.maximalIdeal (𝓞 L) :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq Ideal.LiesOver.over)
  rw [absoluteRamificationIndex, baseRamificationIndex, ramificationIdx,
    Ideal.ramificationIdx_algebra_tower hg0 hfg hg, mul_comm]

/-- `𝓞 L` is a finite free `𝓞 K`-module of rank `[L : K]`. -/
theorem free_finrank :
    Module.Free (𝓞 K) (𝓞 L) ∧
      Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L := by
  letI : IsFractionRing (𝓞 K) K := RingOfIntegers.instIsFractionRing (K := K)
  haveI : Algebra.IsSeparable K L := isSeparable_of_padicExtension p K L
  exact ⟨IsIntegralClosure.module_free (𝓞 K) K L (𝓞 L),
         IsIntegralClosure.rank (𝓞 K) K L (𝓞 L)⟩

/-- The *residue degree* `f(L / K)` of an extension of `p`-adic fields :
  `f = [k_L : k_K]`, realised as the inertia degree of `𝔪_K` in `𝒪_L`. -/
def inertiaDeg : ℕ :=
  Ideal.inertiaDeg (R := 𝓞 K) (S := 𝓞 L)
    (IsLocalRing.maximalIdeal (𝓞 K))
    (IsLocalRing.maximalIdeal (𝓞 L))

/-- The fundamental identity `e * f = [L : K]` -/
theorem ramificationIdx_mul_inertiaDeg :
    ramificationIdx K L * inertiaDeg K L = Module.finrank K L := by
  letI : IsFractionRing (𝓞 K) K := RingOfIntegers.instIsFractionRing (K := K)
  letI : IsFractionRing (𝓞 L) L := RingOfIntegers.instIsFractionRing (K := L)
  have hp0 : IsLocalRing.maximalIdeal (𝓞 K) ≠ ⊥ := fun h =>
    IsDiscreteValuationRing.not_isField (𝓞 K)
      ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
  simpa only [ramificationIdx, inertiaDeg] using
    Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
      (R := 𝓞 K) (S := 𝓞 L) (K := K) (L := L) hp0

/-- `𝒪_L` is a free `𝒪_K`-module, so it carries a chosen
basis used to define the discriminant. -/
instance instModuleFree : Module.Free (𝓞 K) (𝓞 L) := (free_finrank K L).1



/-- In a discrete valuation ring, `multiplicity 𝔪 (𝔪 ^ n) = n`. -/
lemma multiplicity_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) :
    multiplicity (IsLocalRing.maximalIdeal R) ((IsLocalRing.maximalIdeal R) ^ n) = n := by
  refine multiplicity_pow_self ?_ ?_ n
  · rw [Ideal.zero_eq_bot]; exact IsDiscreteValuationRing.not_a_field R
  · exact Ideal.isUnit_iff.not.mpr (IsLocalRing.maximalIdeal.isMaximal R).ne_top

/-- In a discrete valuation ring, a nonzero ideal is `𝔪 ^ (multiplicity 𝔪 I)`. -/
lemma eq_maximalIdeal_pow_multiplicity {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {I : Ideal R} (hI : I ≠ ⊥) :
    I = (IsLocalRing.maximalIdeal R) ^ (multiplicity (IsLocalRing.maximalIdeal R) I) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have hIn : I = (IsLocalRing.maximalIdeal R) ^ n := by
    rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  have hmult : multiplicity (IsLocalRing.maximalIdeal R) I = n := by
    rw [hIn]; exact multiplicity_maximalIdeal_pow n
  rw [hmult]; exact hIn

omit [Module.Finite K L] in
open IsLocalRing in
/-- In this local (DVR) setting, the extension of the maximal ideal factors as a single
prime power: `𝔪_K 𝒪_L = 𝔪_L ^ e`. -/
lemma map_maximalIdeal_eq_pow_ramificationIdx :
    (maximalIdeal (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 L))
      = (maximalIdeal (𝓞 L)) ^ (ramificationIdx K L) := by
  have hP0 : maximalIdeal (𝓞 L) ≠ ⊥ := IsDiscreteValuationRing.not_a_field (𝓞 L)
  have hmK : maximalIdeal (𝓞 K) ≠ ⊥ := IsDiscreteValuationRing.not_a_field (𝓞 K)
  have hmapne : (maximalIdeal (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hmK
  have hk := eq_maximalIdeal_pow_multiplicity hmapne
  set k := multiplicity (maximalIdeal (𝓞 L))
    ((maximalIdeal (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 L))) with hk_def
  have hstrict : StrictAnti (fun n : ℕ => (maximalIdeal (𝓞 L)) ^ n) :=
    Ideal.pow_right_strictAnti (maximalIdeal (𝓞 L)) hP0
      (IsLocalRing.maximalIdeal.isMaximal (𝓞 L)).ne_top
  have hram : ramificationIdx K L = k := by
    show Ideal.ramificationIdx (R := 𝓞 K) (S := 𝓞 L)
      (maximalIdeal (𝓞 K)) (maximalIdeal (𝓞 L)) = k
    refine Ideal.ramificationIdx_spec (le_of_eq hk) ?_
    rw [hk]
    exact (hstrict (Nat.lt_succ_self k)).2
  rw [hram]; exact hk

open IsLocalRing in
/-- The ramification index of a `p`-adic extension is nonzero. -/
lemma ramificationIdx_ne_zero : NeZero (ramificationIdx K L) := by
  refine ⟨fun h => ?_⟩
  have hPe := map_maximalIdeal_eq_pow_ramificationIdx K L
  rw [h, pow_zero, Ideal.one_eq_top] at hPe
  have hle : (maximalIdeal (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 L)) ≤ maximalIdeal (𝓞 L) := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.LiesOver.over (p := maximalIdeal (𝓞 K)) (P := maximalIdeal (𝓞 L)))
  rw [hPe] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal (𝓞 L)).ne_top (top_le_iff.mp hle)

end Extension

end PadicField
