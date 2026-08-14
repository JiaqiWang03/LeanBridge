import Mathlib

/-!
# Invariants of `p`-adic fields: the field and its ring of integers

This file begins the formalization of the blueprint
`numina/blueprints/padicinv/padicinv.tex` (Invariants of a finite extension of
`p`-adic fields):

* `PadicField` : a `p`-adic field is a finite extension `K / ℚ_[p]`.
* `PadicField.ringOfIntegers` (`𝒪_K`): the integral closure of `ℤ_[p]` in `K`,
  together with `IsFractionRing 𝒪_K K`.
* `PadicField.instIsDiscreteValuationRing` : `𝒪_K` is a discrete valuation ring.
-/

noncomputable section

/-- A *`p`-adic field* is a finite extension `K / ℚ_[p]`. The prime `p` is an
`outParam`: it is recovered from the field `K` (via its `ℚ_[p]`-algebra
structure), so downstream definitions such as `𝓞 K` need not carry `p`. -/
class PadicField (K : Type*) [Field K] (p : outParam ℕ) [Fact p.Prime] [Algebra ℚ_[p] K] : Prop
    extends Module.Finite ℚ_[p] K

namespace PadicField

variable (K : Type*) [Field K] {p : ℕ} [Fact p.Prime] [Algebra ℚ_[p] K] [PadicField K p]

/-- The canonical `ℤ_[p]`-algebra structure on a `p`-adic field, obtained by
restricting scalars along `ℤ_[p] → ℚ_[p]`. -/
instance : Algebra ℤ_[p] K :=
  ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

instance : IsScalarTower ℤ_[p] ℚ_[p] K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_padicInt_injective (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Algebra ℚ_[p] K] : Function.Injective (algebraMap ℤ_[p] K) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] K, RingHom.coe_comp]
  exact (algebraMap ℚ_[p] K).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

theorem charZero_of_padicAlgebra (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]
    [Algebra ℚ_[p] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective

-- instance instIsAlgebraic : Algebra.IsAlgebraic ℚ_[p] K :=
--   Algebra.IsAlgebraic.of_finite ℚ_[p] K

instance : Algebra.IsSeparable ℚ_[p] K := by
  haveI : CharZero K := charZero_of_padicAlgebra p K
  exact Algebra.IsSeparable.of_integral ℚ_[p] K

instance : Module.IsTorsionFree ℤ_[p] K :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap_padicInt_injective p K)

/-- The ring of integers `𝓞 K` of a `p`-adic field `K`: the integral closure of
`ℤ_[p]` (the integers of `ℚ_[p]`) in `K`. The prime `p` is recovered from the
`PadicField` instance, so it is not an explicit argument. -/
def ringOfIntegers (K : Type*) [Field K] {p : ℕ} [Fact p.Prime] [Algebra ℚ_[p] K]
    [PadicField K p] : Type _ := integralClosure ℤ_[p] K
deriving CommRing, IsDomain, Nontrivial

@[inherit_doc] scoped[PadicField] notation "𝓞" => PadicField.ringOfIntegers

open scoped PadicField

namespace RingOfIntegers

instance instAlgebraPadicInt : Algebra ℤ_[p] (𝓞 K) :=
  inferInstanceAs (Algebra ℤ_[p] (integralClosure ℤ_[p] K))

instance instModulePadicInt : Module ℤ_[p] (𝓞 K ):=
  inferInstanceAs (Module ℤ_[p] (integralClosure ℤ_[p] K))

instance instAlgebraField : Algebra (𝓞 K) K :=
  inferInstanceAs (Algebra (integralClosure ℤ_[p] K) K)

/-- The canonical coercion from `𝓞 K` to `K`. -/
@[coe]
abbrev val (x : 𝓞 K) : K := algebraMap _ _ x

instance instCoeHeadField : CoeHead (𝓞 K) K := ⟨fun x => algebraMap (𝓞 K) K x⟩

@[simp]
lemma algebraMap_field_mk (x : K) (hx) :
    algebraMap (𝓞 K) K ⟨x, hx⟩ = x := rfl

omit [PadicField K p] in
@[simp]
lemma coe_mk (x : K) (hx) : ((⟨x, hx⟩ : 𝓞 K) : K) = x := rfl

@[ext]
theorem ext {x y : 𝓞 K} (h : (x : K) = (y : K)) : x = y :=
  Subtype.ext h

@[simp, norm_cast]
theorem coe_eq_coe {x y : 𝓞 K} : (x : K) = (y : K) ↔ x = y :=
  Subtype.ext_iff.symm

instance instIsScalarTowerField : IsScalarTower ℤ_[p] (𝓞 K) K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance instFaithfulSMulPadicInt : FaithfulSMul ℤ_[p] (𝓞 K) := by
  exact (faithfulSMul_iff_algebraMap_injective ℤ_[p] (𝓞 K)).mpr fun x y hxy => by
    apply algebraMap_padicInt_injective p K
    calc
      algebraMap ℤ_[p] K x = algebraMap (𝓞 K) K (algebraMap ℤ_[p] (𝓞 K) x) := by
        rw [IsScalarTower.algebraMap_apply ℤ_[p] (𝓞 K) K]
      _ = algebraMap (𝓞 K) K (algebraMap ℤ_[p] (𝓞 K) y) := by rw [hxy]
      _ = algebraMap ℤ_[p] K y := by
        rw [IsScalarTower.algebraMap_apply ℤ_[p] (𝓞 K) K]

instance instIsIntegralClosure : IsIntegralClosure (𝓞 K) ℤ_[p] K :=
  integralClosure.isIntegralClosure ℤ_[p] K

instance instIsFractionRing : IsFractionRing (𝓞 K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] K


instance instIsIntegralPadicInt: Algebra.IsIntegral ℤ_[p] (𝓞 K) :=
  inferInstanceAs (Algebra.IsIntegral ℤ_[p] (integralClosure ℤ_[p] K))

instance instCharZero: CharZero (𝓞 K) :=
  charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ_[p] (𝓞 K))

instance instPerfectFieldFractionRing: PerfectField (FractionRing (𝓞 K)) :=
  inferInstance

instance instFiniteRingOfIntegers : Module.Finite ℤ_[p] (𝓞 K) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] K (𝓞 K)

instance instFreeRingOfIntegers : Module.Free ℤ_[p] (𝓞 K) :=
  IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K (𝓞 K)

instance instAlgebraFieldExtension {L : Type*} [Ring L] [Algebra K L] : Algebra (𝓞 K) L :=
  inferInstanceAs (Algebra (integralClosure ℤ_[p] K) L)

instance instIsScalarTowerFieldAlgebra {L : Type*} [Ring L] [Algebra K L] :
    IsScalarTower (𝓞 K) K L :=
  inferInstanceAs (IsScalarTower (integralClosure ℤ_[p] K) K L)

instance instIsScalarTowerPadicIntFieldAlgebra {L : Type*} [Ring L] [Algebra K L]
    [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] K L] : IsScalarTower ℤ_[p] (𝓞 K) L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    haveI : IsScalarTower ℤ_[p] (𝓞 K) K := RingOfIntegers.instIsScalarTowerField (K := K)
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L,
      ← IsScalarTower.algebraMap_apply ℤ_[p] (𝓞 K) K,
      IsScalarTower.algebraMap_apply ℤ_[p] K L]

instance instIsTorsionFreeField : Module.IsTorsionFree (𝓞 K) K :=
  inferInstanceAs (Module.IsTorsionFree (integralClosure ℤ_[p] K) K)

instance instIsTorsionFreeAlgebra {L : Type*} [Ring L] [Algebra K L]
    [Module.IsTorsionFree K L] : Module.IsTorsionFree (𝓞 K) L :=
  Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K L

/-- If the spectral norm of `x : K` over `ℚ_[p]` is `≤ 1`, then `x` is integral over `ℤ_[p]`:
the coefficients of its minimal polynomial have norm `≤ 1`, hence lie in `ℤ_[p]`.
  A general version is exactly in FLT. -/
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

/-- Reverse of `isIntegral_of_spectralNorm_le_one`: an element integral over `ℤ_[p]` has
spectral norm `≤ 1`. Over the integrally closed `ℤ_[p]` the minimal polynomial of `x` over
`ℚ_[p]` has coefficients in `ℤ_[p]`, all of norm `≤ 1`, so the spectral value is `≤ 1`. -/
theorem spectralNorm_le_one_of_isIntegral {x : K} (hx : IsIntegral ℤ_[p] x) :
    spectralNorm ℚ_[p] K x ≤ 1 := by
  have hxalg : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  show spectralValue (minpoly ℚ_[p] x) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hxalg)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ_[p]) hx, Polynomial.coeff_map]
  simpa using PadicInt.norm_le_one ((minpoly ℤ_[p] x).coeff n)

theorem spectralNorm_le_one_iff_isIntegral {x : K} :
    spectralNorm ℚ_[p] K x ≤ 1 ↔ IsIntegral ℤ_[p] x :=
  ⟨isIntegral_of_spectralNorm_le_one K, spectralNorm_le_one_of_isIntegral K⟩

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
instance instValuationRing : ValuationRing (𝓞 K) := by
  refine ValuationSubring.instValuationRingSubtypeMem
    (A := ⟨(integralClosure ℤ_[p] K).toSubring, ?_⟩)
  intro x
  obtain hx | hx := le_total (spectralNorm ℚ_[p] K x) 1
  · exact Or.inl (isIntegral_of_spectralNorm_le_one (p := p) (K := K) hx)
  · refine Or.inr (isIntegral_of_spectralNorm_le_one (p := p) (K := K) ?_)
    rw [spectralNorm_inv]
    exact inv_le_one_of_one_le₀ hx

instance isDedekind : IsDedekindDomain (𝓞 K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)

theorem notField :
    ¬ IsField (𝓞 K) := by
  have hinj : Function.Injective (algebraMap ℤ_[p] (𝓞 K)) := by
    have hK := algebraMap_padicInt_injective p K
    rw [IsScalarTower.algebraMap_eq ℤ_[p] (𝓞 K) K, RingHom.coe_comp] at hK
    exact hK.of_comp
  intro hF
  exact (IsDiscreteValuationRing.not_isField ℤ_[p])
    ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hF)

/-- The ring of integers of a `p`-adic field is a discrete valuation ring: `𝒪_K` is a
valuation ring , a Dedekind domain and not a field, so the DVR characterization applies. -/
instance instIsDiscreteValuationRing :
    IsDiscreteValuationRing (𝓞 K) := by
  have hD : IsDedekindDomain (𝓞 K) := inferInstance
  exact ((IsDiscreteValuationRing.TFAE (𝓞 K) (notField K)).out 2 0).mp hD

lemma maximalIdeal_ne_bot : IsLocalRing.maximalIdeal (𝓞 K) ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal _) <| notField K

end RingOfIntegers

open RingOfIntegers IsNonarchimedeanLocalField ValuativeRel

def heightOneMaximalIdeal : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨IsLocalRing.maximalIdeal (𝓞 K), (IsLocalRing.maximalIdeal.isMaximal (𝓞 K)).isPrime,
    RingOfIntegers.maximalIdeal_ne_bot K⟩

def valuation : Valuation K (WithZero (Multiplicative ℤ)) :=
  letI : IsFractionRing (𝓞 K) K := RingOfIntegers.instIsFractionRing (K := K)
  IsDedekindDomain.HeightOneSpectrum.valuation K (heightOneMaximalIdeal K)

/-- The adic valuation of `𝓞 K` (with respect to its unique maximal ideal) is `≤ 1` exactly on
the ring of integers. Since `𝓞 K` is a DVR, its only height-one prime is `IsLocalRing.maximalIdeal 𝓞 K`, so the
"all valuations `≤ 1`" criterion for integrality reduces to this single valuation. -/
theorem valuation_le_one_iff_isIntegral {x : K} :
    valuation K x ≤ 1 ↔ IsIntegral ℤ_[p] x := by
  constructor
  · intro hle
    letI : IsFractionRing (𝓞 K) K := RingOfIntegers.instIsFractionRing (K := K)
    have hall : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        (IsDedekindDomain.HeightOneSpectrum.valuation K v) x ≤ 1 := by
      intro v
      have hv : v = heightOneMaximalIdeal K :=
        IsDedekindDomain.HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal inferInstance)
      rw [hv]
      exact hle
    obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x hall
    rw [← hr]
    have hr2 : IsIntegral ℤ_[p] (r : K) := r.2
    exact hr2
  · intro hint
    letI : IsFractionRing (𝓞 K) K := RingOfIntegers.instIsFractionRing (K := K)
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one (heightOneMaximalIdeal K)
      (⟨x, hint⟩ : (𝓞 K))

instance : ValuativeRel K := .ofValuation <| valuation K

instance instValuationCompatible: (valuation K).Compatible := by
  exact Valuation.Compatible.ofValuation (valuation K)

instance : ValuativeRel.IsNontrivial K := by
  letI : IsFractionRing (𝓞 K) K := RingOfIntegers.instIsFractionRing (K := K)
  rw [ValuativeRel.isNontrivial_iff_isNontrivial (valuation K)]
  exact IsDedekindDomain.HeightOneSpectrum.instIsNontrivialWithZeroMultiplicativeIntValuation K
    (heightOneMaximalIdeal K)

instance : NormedField K := spectralNorm.normedField ℚ_[p] K

instance : NontriviallyNormedField K := spectralNorm.nontriviallyNormedField ℚ_[p] K

instance : NormedAlgebra ℚ_[p] K := spectralNorm.normedAlgebra _ _

instance : ProperSpace K := FiniteDimensional.proper ℚ_[p] K

theorem Norm.isNonarchimedean : IsNonarchimedean (norm : K → ℝ) := isNonarchimedean_spectralNorm

instance : IsUltrametricDist K :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm <| Norm.isNonarchimedean K

lemma valuation_equiv_valuativeRel_valuation :
    (valuation K).IsEquiv (ValuativeRel.valuation K) :=
  (ValuativeRel.isEquiv (valuation K) (ValuativeRel.valuation K))

open scoped NNReal in
/-- The spectral-norm topology on `K` agrees with the valuative topology of the adic valuation
`valuation K`: the norm balls `{y | ‖y‖ < ε}` and the valuation balls `{z | v z < γ}` form
mutually cofinal neighborhood bases of `0`. This holds because the spectral norm and the adic
valuation of `𝓞 K` are equivalent valuations (both have `𝓞 K` as their unit ball). -/
instance : IsValuativeTopology K := by
  letI : IsFractionRing (𝓞 K) K := RingOfIntegers.instIsFractionRing (K := K)
  let w : Valuation K ℝ≥0 := NormedField.valuation (K := K)
  have hequiv : w.IsEquiv (ValuativeRel.valuation K) := by
    refine Valuation.IsEquiv.trans ?_ (valuation_equiv_valuativeRel_valuation K)
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [valuation_le_one_iff_isIntegral, ← spectralNorm_le_one_iff_isIntegral,
      NormedField.valuation_apply]
    rfl
  have hlt : ∀ x y : K,
      ‖x‖ < ‖y‖ ↔ ValuativeRel.valuation K x < ValuativeRel.valuation K y := by
    intro x y
    have hb : (‖x‖ < ‖y‖) ↔ (w x < w y) := by
      show (‖x‖ < ‖y‖) ↔ ((‖x‖₊ : ℝ≥0) < ‖y‖₊)
      rw [← NNReal.coe_lt_coe]; rfl
    rw [hb]
    exact hequiv.lt_iff_lt
  apply IsValuativeTopology.of_zero
  intro s
  rw [Metric.mem_nhds_iff]
  constructor
  · rintro ⟨ε, hε, hsub⟩
    obtain ⟨a, ha0, haε⟩ := NormedField.exists_norm_lt K hε
    have hane : a ≠ 0 := norm_pos_iff.mp ha0
    refine ⟨Units.mk0 (ValuativeRel.valuation K a) ((Valuation.ne_zero_iff _).mpr hane),
      fun z hz => hsub ?_⟩
    simp only [Units.val_mk0, Set.mem_setOf_eq] at hz
    have hzn : ‖z‖ < ‖a‖ := (hlt z a).mpr hz
    simpa only [Metric.mem_ball, dist_zero_right] using hzn.trans haε
  · rintro ⟨γ, hsub⟩
    obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective
      (K := K) (γ : ValuativeRel.ValueGroupWithZero K)
    have hane : a ≠ 0 := fun h => γ.ne_zero (by rw [← ha, h, map_zero])
    refine ⟨‖a‖, norm_pos_iff.mpr hane, fun y hy => hsub ?_⟩
    simp only [Metric.mem_ball, dist_zero_right] at hy
    have hyv : ValuativeRel.valuation K y < ValuativeRel.valuation K a := (hlt y a).mp hy
    simpa only [Set.mem_setOf_eq, ← ha] using hyv

instance : IsNonarchimedeanLocalField K where

def ringEquiv_valuation_integer : 𝓞 K ≃+* 𝒪[K] where
  toFun x := ⟨x.1, by
    rw [Valuation.mem_integer_iff, ← (valuation_equiv_valuativeRel_valuation K).le_one_iff_le_one,
      valuation_le_one_iff_isIntegral]
    exact x.2⟩
  invFun x := ⟨x.1, by
    rw [mem_integralClosure_iff, ← valuation_le_one_iff_isIntegral,
      (valuation_equiv_valuativeRel_valuation K).le_one_iff_le_one,]
    exact x.2⟩
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _:= rfl
  map_add' _ _:= rfl

open IsNonarchimedeanLocalField

namespace RingOfIntegers

instance instFiniteResidueField : Finite (IsLocalRing.ResidueField (𝓞 K)) := by
  let e := ringEquiv_valuation_integer K |>.symm
  exact Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv e).toEquiv

/-- `𝒪_K` is `𝔪_K`-adically complete : the integral closure of the complete DVR `ℤ_[p]` in a
finite extension is again complete. -/
instance instIsAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal (𝓞 K)) (𝓞 K) := by
  let e := ringEquiv_valuation_integer K |>.symm
  rw [show IsLocalRing.maximalIdeal _ = Ideal.map e 𝓂[K] by simp,
    IsAdicComplete.congr_ringEquiv _ (ringEquiv_valuation_integer K).symm]
  infer_instance

end RingOfIntegers
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
def ringOfIntegersMap : 𝓞 K →+* 𝓞 L where
  toFun x := ⟨algebraMap K L (x : K), by
    have hx : IsIntegral ℤ_[p] (x : K) := x.2
    have h2 := hx.map (IsScalarTower.toAlgHom ℤ_[p] K L)
    rwa [IsScalarTower.toAlgHom_apply] at h2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- The `ℤ_[p]`-algebra structure on the pair `𝒪_K → 𝒪_L`, used to form the
relative ramification index. -/
instance instAlgebraRingOfIntegers : Algebra (𝓞 K) (𝓞 L) :=
  (ringOfIntegersMap K L).toAlgebra

instance instIsScalarTowerRingOfIntegersField : IsScalarTower (𝓞 K) (𝓞 L) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance instIsScalarTowerPadicIntRingOfIntegers : IsScalarTower ℤ_[p] (𝓞 K) (𝓞 L) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    haveI : IsScalarTower ℤ_[p] (𝓞 K) K := RingOfIntegers.instIsScalarTowerField (K := K)
    apply RingOfIntegers.ext (K := L)
    change algebraMap ℤ_[p] L x =
      algebraMap K L (algebraMap (𝓞 K) K (algebraMap ℤ_[p] (𝓞 K) x))
    rw [← IsScalarTower.algebraMap_apply ℤ_[p] (𝓞 K) K,
      IsScalarTower.algebraMap_apply ℤ_[p] K L]

end Extension

end PadicField
