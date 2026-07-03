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
structure), so downstream definitions such as `𝒪[K]` need not carry `p`. -/
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

/-- The ring of integers `𝒪[K]` of a `p`-adic field `K`: the integral closure of
`ℤ_[p]` (the integers of `ℚ_[p]`) in `K`. The prime `p` is recovered from the
`PadicField` instance, so it is not an explicit argument. -/
def ringOfIntegers (K : Type*) [Field K] {p : ℕ} [Fact p.Prime] [Algebra ℚ_[p] K]
    [PadicField K p] : Subalgebra ℤ_[p] K := integralClosure ℤ_[p] K

namespace RingOfIntegers

@[inherit_doc] scoped notation "𝒪[" K "]" => PadicField.ringOfIntegers K

instance instIsIntegralClosure : IsIntegralClosure 𝒪[K] ℤ_[p] K :=
  integralClosure.isIntegralClosure ℤ_[p] K

instance instIsFractionRing : IsFractionRing 𝒪[K] K :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] K

instance instIsIntegralPadicInt: Algebra.IsIntegral ℤ_[p] 𝒪[K] :=
  inferInstanceAs (Algebra.IsIntegral ℤ_[p] (integralClosure ℤ_[p] K))

instance instCharZero: CharZero 𝒪[K] :=
  charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ_[p] 𝒪[K])

instance instPerfectFieldFractionRing: PerfectField (FractionRing 𝒪[K]) :=
  inferInstance

instance instFiniteRingOfIntegers : Module.Finite ℤ_[p] 𝒪[K] :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] K 𝒪[K]

instance instFreeRingOfIntegers : Module.Free ℤ_[p] 𝒪[K] :=
  IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K 𝒪[K]

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

/-- The ring of integers of a `p`-adic field is a discrete valuation ring: `𝒪_K` is a
valuation ring , a Dedekind domain and not a field, so the DVR characterization applies. -/
instance instIsDiscreteValuationRing :
    IsDiscreteValuationRing 𝒪[K] := by
  have hD : IsDedekindDomain (integralClosure ℤ_[p] K) := inferInstance
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[p] K) (notField p K)).out 2 0).mp hD

lemma maximalIdeal_ne_bot : IsLocalRing.maximalIdeal 𝒪[K] ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal _) <| notField p K

end RingOfIntegers

open RingOfIntegers

def valuation := IsDedekindDomain.HeightOneSpectrum.valuation (R := 𝒪[K]) K <|
  ⟨IsLocalRing.maximalIdeal 𝒪[K], IsLocalRing.maximalIdeal.isMaximal 𝒪[K] |>.isPrime,
    maximalIdeal_ne_bot K⟩

/-- The adic valuation of `𝒪[K]` (with respect to its unique maximal ideal) is `≤ 1` exactly on
the ring of integers. Since `𝒪[K]` is a DVR, its only height-one prime is `IsLocalRing.maximalIdeal 𝒪[K]`, so the
"all valuations `≤ 1`" criterion for integrality reduces to this single valuation. -/
theorem valuation_le_one_iff_isIntegral {x : K} :
    valuation K x ≤ 1 ↔ IsIntegral ℤ_[p] x := by
  constructor
  · intro hle
    have hall : ∀ v : IsDedekindDomain.HeightOneSpectrum 𝒪[K],
        (IsDedekindDomain.HeightOneSpectrum.valuation K v) x ≤ 1 := by
      intro v
      have hv : v = ⟨IsLocalRing.maximalIdeal 𝒪[K], (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).isPrime,
          maximalIdeal_ne_bot K⟩ :=
        IsDedekindDomain.HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal inferInstance)
      rw [hv]; exact hle
    obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x hall
    rw [← hr]
    have hr2 : IsIntegral ℤ_[p] (r : K) := r.2
    simpa using hr2
  · intro hint
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ (⟨x, hint⟩ : 𝒪[K])

instance : ValuativeRel K := .ofValuation <| valuation K

instance : ValuativeRel.IsNontrivial K := by
  haveI := Valuation.Compatible.ofValuation <| valuation K
  rw [ValuativeRel.isNontrivial_iff_isNontrivial (valuation K)]
  exact IsDedekindDomain.HeightOneSpectrum.instIsNontrivialWithZeroMultiplicativeIntValuation _ _

instance instValuationCompatible: (valuation K).Compatible :=
  Valuation.Compatible.ofValuation (valuation K)

instance : NormedField K := spectralNorm.normedField ℚ_[p] K

instance : NontriviallyNormedField K := spectralNorm.nontriviallyNormedField ℚ_[p] K

instance : NormedAlgebra ℚ_[p] K := spectralNorm.normedAlgebra _ _

instance : ProperSpace K := FiniteDimensional.proper ℚ_[p] K

theorem Norm.isNonarchimedean : IsNonarchimedean (norm : K → ℝ) := isNonarchimedean_spectralNorm

instance : IsUltrametricDist K :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm <| Norm.isNonarchimedean K

open scoped NNReal in
/-- The spectral-norm topology on `K` agrees with the valuative topology of the adic valuation
`valuation K`: the norm balls `{y | ‖y‖ < ε}` and the valuation balls `{z | v z < γ}` form
mutually cofinal neighborhood bases of `0`. This holds because the spectral norm and the adic
valuation of `𝒪[K]` are equivalent valuations (both have `𝒪[K]` as their unit ball). -/
instance : IsValuativeTopology K := by
  let w : Valuation K ℝ≥0 := NormedField.valuation (K := K)
  have hequiv : w.IsEquiv (ValuativeRel.valuation K) := by
    refine Valuation.IsEquiv.trans ?_ (ValuativeRel.isEquiv (valuation K) (ValuativeRel.valuation K))
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

end PadicField

open IsNonarchimedeanLocalField
variable (K : Type*) [Field K] {p : ℕ} [Fact p.Prime] [Algebra ℚ_[p] K] [PadicField K p]

instance instFiniteResidueFieldRingOfIntegers : Finite (IsLocalRing.ResidueField (PadicField.ringOfIntegers K)) := by
  -- exact IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation K
  -- -- haveI : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
  --   Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
  -- exact IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[p]) (S := 𝒪[K]) inferInstance

lemma isPrecomplete_of_finite_of_adicComplete
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

lemma isAdicComplete_of_finite_of_adicComplete
    {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [IsHausdorff I M] [IsAdicComplete I R] : IsAdicComplete I M where
  toIsHausdorff := inferInstance
  toIsPrecomplete := isPrecomplete_of_finite_of_adicComplete

lemma isAdicComplete_of_pow
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

/-- `𝒪_K` is `𝔪_K`-adically complete : the integral closure of the complete DVR `ℤ_[p]` in a
finite extension is again complete. -/
instance instIsAdicComplete :
    IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[K]) 𝒪[K] := by
  let S := 𝒪[K]
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
def ringOfIntegersMap : 𝒪[K] →+* 𝒪 L where
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
instance instAlgebraRingOfIntegers : Algebra 𝒪[K] (𝒪 L) :=
  (ringOfIntegersMap K L).toAlgebra

end Extension

end PadicField
