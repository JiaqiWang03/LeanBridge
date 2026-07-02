import Mathlib

namespace Neukirch.Chapter2.Sections8to10

open scoped WithZero

/-- A uniformizer `π` (`Irreducible π`) of the DVR `𝒪` generates `𝔪`. -/
theorem mono_maximalIdeal_eq_span
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪]
    {π : 𝒪} (hπ : Irreducible π) :
    IsLocalRing.maximalIdeal 𝒪 = Ideal.span {π} :=
  hπ.maximalIdeal_eq

/-- The ramification index `e`, defined DVR-directly: `𝔪K·𝒪 = (π)^e`. -/
noncomputable def mono_ramificationIdx
    (𝒪K : Type*) [CommRing 𝒪K] [IsDomain 𝒪K]
    [IsDiscreteValuationRing 𝒪K]
    (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪]
    [Algebra 𝒪K 𝒪] [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪]
    {π : 𝒪} (hπ : Irreducible π) : ℕ :=
  Classical.choose
    (IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K))
      (by
        have hmK : IsLocalRing.maximalIdeal 𝒪K ≠ ⊥ :=
          IsDiscreteValuationRing.not_a_field 𝒪K
        exact Ideal.map_ne_bot_of_ne_bot hmK)
      hπ)

/-- `𝔪K·𝒪 = 𝔪^e`. -/
theorem mono_mapMK_eq_pow
    {𝒪K : Type*} [CommRing 𝒪K] [IsDomain 𝒪K]
    [IsDiscreteValuationRing 𝒪K]
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪]
    [Algebra 𝒪K 𝒪] [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪]
    {π : 𝒪} (hπ : Irreducible π) :
    Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K) =
      (IsLocalRing.maximalIdeal 𝒪) ^ (mono_ramificationIdx 𝒪K 𝒪 hπ) := by
  have hspec :
      Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K) =
        Ideal.span {π ^ (mono_ramificationIdx 𝒪K 𝒪 hπ)} :=
    Classical.choose_spec
      (IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
        (s := Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K))
        (by
          have hmK : IsLocalRing.maximalIdeal 𝒪K ≠ ⊥ :=
            IsDiscreteValuationRing.not_a_field 𝒪K
          exact Ideal.map_ne_bot_of_ne_bot hmK)
        hπ)
  rw [hspec, mono_maximalIdeal_eq_span hπ, Ideal.span_singleton_pow]

/-! ## Ambient setup (mirrors the keystone typeclass conventions) -/

variable {𝒪K : Type*} [CommRing 𝒪K] [IsDomain 𝒪K]
    [IsDiscreteValuationRing 𝒪K]
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪]
variable [Algebra 𝒪K 𝒪] [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪]
variable [IsLocalHom (algebraMap 𝒪K 𝒪)]

omit [FaithfulSMul 𝒪K 𝒪] in
/-- The residue extension `λ/κ` is module-finite. -/
theorem mono_residueField_finite :
    Module.Finite (IsLocalRing.ResidueField 𝒪K) (IsLocalRing.ResidueField 𝒪) :=
  inferInstance

omit [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪] in
/-- **Residue bridge.**  For `g : 𝒪K[X]` and `x : 𝒪`, the residue of
`eval x (g.map (𝒪K→𝒪))` is the evaluation at `residue 𝒪 x` of `g` mapped down
the residue tower `𝒪K → κ → λ`. -/
theorem mono_residue_eval_lift (g : Polynomial 𝒪K) (x : 𝒪) :
    IsLocalRing.residue 𝒪
        (Polynomial.eval x (g.map (algebraMap 𝒪K 𝒪)))
      = Polynomial.eval (IsLocalRing.residue 𝒪 x)
          ((g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K))).map
            (algebraMap (IsLocalRing.ResidueField 𝒪K)
              (IsLocalRing.ResidueField 𝒪))) := by
  have hcomp :
      (IsLocalRing.residue 𝒪).comp (algebraMap 𝒪K 𝒪)
        = (algebraMap (IsLocalRing.ResidueField 𝒪K)
            (IsLocalRing.ResidueField 𝒪)).comp
            (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)) := by
    apply RingHom.ext
    intro a
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsLocalRing.ResidueField.algebraMap_eq 𝒪K,
      IsLocalRing.ResidueField.algebraMap_residue]
  have hmaps : (g.map (algebraMap 𝒪K 𝒪)).map (IsLocalRing.residue 𝒪)
      = (g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K))).map
          (algebraMap (IsLocalRing.ResidueField 𝒪K)
            (IsLocalRing.ResidueField 𝒪)) := by
    rw [Polynomial.map_map, Polynomial.map_map, hcomp]
  rw [← Polynomial.eval_map_apply (IsLocalRing.residue 𝒪)
      (p := g.map (algebraMap 𝒪K 𝒪)) x, hmaps]

/-- **Two-generator monogenicity.**  With `π` a uniformizer and `ξ` any lift of
a primitive element `ξ̄` of `λ/κ`, `𝒪K[ξ, π] = 𝒪`. -/
theorem mono_adjoin_two_gen
    (ξ π : 𝒪)
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤)
    (hπ : Irreducible π) :
    Algebra.adjoin 𝒪K ({ξ, π} : Set 𝒪) = ⊤ := by
  classical
  haveI : Module.Finite (IsLocalRing.ResidueField 𝒪K)
      (IsLocalRing.ResidueField 𝒪) := mono_residueField_finite
  set e := mono_ramificationIdx 𝒪K 𝒪 hπ with he
  set A : Subalgebra 𝒪K 𝒪 := Algebra.adjoin 𝒪K ({ξ, π} : Set 𝒪) with hA
  have hπA : π ∈ A := Algebra.subset_adjoin (by simp)
  have hbase : ∀ c : 𝒪, ∃ b : 𝒪, b ∈ A ∧ c - b ∈ (Ideal.span {π} : Ideal 𝒪) := by
    intro c
    have hint : IsIntegral (IsLocalRing.ResidueField 𝒪K)
        (IsLocalRing.residue 𝒪 ξ) :=
      Algebra.IsIntegral.isIntegral _
    have hAlgTop : Algebra.adjoin (IsLocalRing.ResidueField 𝒪K)
        ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
        hξ_prim, IntermediateField.top_toSubalgebra]
    have hmem : IsLocalRing.residue 𝒪 c ∈
        Algebra.adjoin (IsLocalRing.ResidueField 𝒪K)
          ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) := by
      rw [hAlgTop]; exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨p, hp⟩ := hmem
    have hsurj : Function.Surjective
        (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)) := by
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      exact IsLocalRing.residue_surjective
    obtain ⟨q, hq⟩ := Polynomial.map_surjective _ hsurj p
    refine ⟨Polynomial.aeval ξ q, ?_, ?_⟩
    · have h1 : Polynomial.aeval ξ q ∈ Algebra.adjoin 𝒪K ({ξ} : Set 𝒪) :=
        Polynomial.aeval_mem_adjoin_singleton 𝒪K ξ
      have hsub : ({ξ} : Set 𝒪) ⊆ ({ξ, π} : Set 𝒪) := by
        intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; simp
      exact (Algebra.adjoin_mono hsub) h1
    · have hbeq : IsLocalRing.residue 𝒪 (Polynomial.aeval ξ q)
          = IsLocalRing.residue 𝒪 c := by
        rw [show Polynomial.aeval ξ q
              = Polynomial.eval ξ (q.map (algebraMap 𝒪K 𝒪)) from by
                rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]]
        rw [mono_residue_eval_lift q ξ, hq, Polynomial.eval_map,
          ← Polynomial.aeval_def]
        exact hp
      rw [← mono_maximalIdeal_eq_span hπ, ← IsLocalRing.residue_eq_zero_iff,
        map_sub, hbeq]
      exact sub_self _
  have hind : ∀ n : ℕ, ∀ a : 𝒪,
      ∃ b : 𝒪, b ∈ A ∧ a - b ∈ (Ideal.span {π} ^ n : Ideal 𝒪) := by
    intro n
    induction n with
    | zero =>
      intro a
      refine ⟨0, Subalgebra.zero_mem A, ?_⟩
      simp only [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ n ih =>
      intro a
      obtain ⟨b, hbA, hab⟩ := ih a
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hab
      obtain ⟨c, hc⟩ := hab
      obtain ⟨b', hb'A, hcb'⟩ := hbase c
      rw [Ideal.mem_span_singleton] at hcb'
      obtain ⟨c', hc'⟩ := hcb'
      refine ⟨b + π ^ n * b', Subalgebra.add_mem A hbA
          (Subalgebra.mul_mem A (Subalgebra.pow_mem A hπA n) hb'A), ?_⟩
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      refine ⟨c', ?_⟩
      have hab' : a = b + π ^ n * c := by rw [← hc]; ring
      have e1 : a - (b + π ^ n * b') = π ^ n * (c - b') := by rw [hab']; ring
      rw [e1, hc']; ring
  rw [← Algebra.toSubmodule_eq_top]
  have hmap : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      = (Ideal.span {π} ^ e : Ideal 𝒪) := by
    rw [mono_mapMK_eq_pow hπ, mono_maximalIdeal_eq_span hπ]
  have hP_eq : ((IsLocalRing.maximalIdeal 𝒪K) • (⊤ : Submodule 𝒪K 𝒪))
      = ((Ideal.span {π} ^ e : Ideal 𝒪).restrictScalars 𝒪K) := by
    rw [Ideal.smul_top_eq_map, hmap]
  have hNak : (Subalgebra.toSubmodule A).map
      (Submodule.mkQ ((IsLocalRing.maximalIdeal 𝒪K)
        • (⊤ : Submodule 𝒪K 𝒪))) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, rfl⟩ :=
      Submodule.mkQ_surjective
        ((IsLocalRing.maximalIdeal 𝒪K) • (⊤ : Submodule 𝒪K 𝒪)) z
    obtain ⟨b, hbA, hab⟩ := hind e a
    refine Submodule.mem_map.mpr ⟨b, (show b ∈ A from hbA), ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hP_eq,
      Submodule.restrictScalars_mem, show b - a = -(a - b) from by ring]
    exact neg_mem hab
  exact (IsLocalRing.map_mkQ_eq_top (R := 𝒪K) (M := 𝒪)
    (N := Subalgebra.toSubmodule A)).mp hNak

omit [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪] in
/-- One Newton step: given a monic `g : 𝒪K[X]`, a uniformizer `π`, and a lift
`x₀` of a simple root `ξ̄` of `g` over `κ`, there is `x = x₀ + π·t` with the
same residue and `g(x) ∈ 𝔪²`. -/
theorem mono_newton_step
    {π : 𝒪} (hπ : Irreducible π) (g : Polynomial 𝒪K) (x₀ : 𝒪)
    (hroot : Polynomial.eval (IsLocalRing.residue 𝒪 x₀)
        ((g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K))).map
          (algebraMap (IsLocalRing.ResidueField 𝒪K)
            (IsLocalRing.ResidueField 𝒪))) = 0)
    (hderiv : Polynomial.eval (IsLocalRing.residue 𝒪 x₀)
        ((Polynomial.derivative
            (g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)))).map
          (algebraMap (IsLocalRing.ResidueField 𝒪K)
            (IsLocalRing.ResidueField 𝒪))) ≠ 0) :
    ∃ x : 𝒪, IsLocalRing.residue 𝒪 x = IsLocalRing.residue 𝒪 x₀ ∧
      Polynomial.eval x (g.map (algebraMap 𝒪K 𝒪))
        ∈ (IsLocalRing.maximalIdeal 𝒪) ^ 2 := by
  classical
  set G : Polynomial 𝒪 := g.map (algebraMap 𝒪K 𝒪) with hG
  have hGx₀_mem : Polynomial.eval x₀ G ∈ IsLocalRing.maximalIdeal 𝒪 := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    rw [hG, mono_residue_eval_lift g x₀, hroot]
  have hDeriv_unit : IsUnit (Polynomial.eval x₀ (Polynomial.derivative G)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    rw [hG, Polynomial.derivative_map,
      mono_residue_eval_lift (Polynomial.derivative g) x₀]
    rw [Polynomial.derivative_map] at hderiv
    exact hderiv
  have hmem_span : Polynomial.eval x₀ G ∈ Ideal.span ({π} : Set 𝒪) := by
    rw [← mono_maximalIdeal_eq_span hπ]; exact hGx₀_mem
  rw [Ideal.mem_span_singleton] at hmem_span
  obtain ⟨b, hb⟩ := hmem_span
  set D := Polynomial.eval x₀ (Polynomial.derivative G) with hD
  set t : 𝒪 := -(↑(hDeriv_unit.unit⁻¹) : 𝒪) * b with ht
  have hDinv : D * (↑(hDeriv_unit.unit⁻¹) : 𝒪) = 1 :=
    hDeriv_unit.mul_val_inv
  have hDt : D * t = -b := by
    have : D * t = -(D * (↑(hDeriv_unit.unit⁻¹) : 𝒪)) * b := by
      rw [ht]; ring
    rw [this, hDinv, neg_one_mul]
  refine ⟨x₀ + π * t, ?_, ?_⟩
  · rw [map_add, map_mul]
    have : IsLocalRing.residue 𝒪 π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, mono_maximalIdeal_eq_span hπ]
      exact Ideal.mem_span_singleton_self π
    rw [this, zero_mul, add_zero]
  · obtain ⟨k, hk⟩ := Polynomial.binomExpansion G x₀ (π * t)
    have hcollapse :
        Polynomial.eval x₀ G
          + Polynomial.eval x₀ (Polynomial.derivative G) * (π * t)
          + k * (π * t) ^ 2
        = π ^ 2 * (k * t ^ 2) := by
      have hDeq : Polynomial.eval x₀ (Polynomial.derivative G) = D := rfl
      rw [hb, hDeq]
      have hDtπ : D * (π * t) = π * (D * t) := by ring
      rw [hDtπ, hDt]
      ring
    rw [hk, hcollapse]
    rw [mono_maximalIdeal_eq_span hπ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact ⟨k * t ^ 2, rfl⟩

/-! ## Main theorem — single-generator monogenicity (Neukirch II.10.4) -/

/-- **Neukirch II.10.4.**  Under the standing finite-DVR-extension hypotheses
and a **separable** residue extension `λ/κ`, there is `θ : 𝒪` with
`Algebra.adjoin 𝒪K {θ} = ⊤`, i.e. `𝒪 = 𝒪K[θ]`. -/
theorem mono_exists_primitive
    [Algebra.IsSeparable
       (IsLocalRing.ResidueField 𝒪K) (IsLocalRing.ResidueField 𝒪)] :
    ∃ θ : 𝒪, Algebra.adjoin 𝒪K ({θ} : Set 𝒪) = ⊤ := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  haveI : Module.Finite (IsLocalRing.ResidueField 𝒪K)
      (IsLocalRing.ResidueField 𝒪) := mono_residueField_finite
  obtain ⟨ξbar, hξbar⟩ :=
    Field.exists_primitive_element (IsLocalRing.ResidueField 𝒪K)
      (IsLocalRing.ResidueField 𝒪)
  obtain ⟨x₀, hx₀⟩ := IsLocalRing.residue_surjective (R := 𝒪) ξbar
  set gbar : Polynomial (IsLocalRing.ResidueField 𝒪K) :=
    minpoly (IsLocalRing.ResidueField 𝒪K) ξbar with hgbar
  have hgbar_sep : gbar.Separable :=
    (Algebra.IsSeparable.isSeparable
      (IsLocalRing.ResidueField 𝒪K) ξbar)
  have hgbar_monic : gbar.Monic :=
    minpoly.monic
      (Algebra.IsIntegral.isIntegral (R := IsLocalRing.ResidueField 𝒪K) ξbar)
  have hsurj : Function.Surjective
      (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq 𝒪K]
    exact IsLocalRing.residue_surjective
  have hlifts : gbar ∈ Polynomial.lifts
      (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact hsurj (gbar.coeff n)
  obtain ⟨g, hg_map, _hg_deg, _hg_monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts hgbar_monic
  have haeval_zero : Polynomial.eval (IsLocalRing.residue 𝒪 x₀)
      ((g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K))).map
        (algebraMap (IsLocalRing.ResidueField 𝒪K)
          (IsLocalRing.ResidueField 𝒪))) = 0 := by
    rw [hg_map, hx₀, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval _ _
  have haeval_deriv : Polynomial.eval (IsLocalRing.residue 𝒪 x₀)
      ((Polynomial.derivative
          (g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)))).map
        (algebraMap (IsLocalRing.ResidueField 𝒪K)
          (IsLocalRing.ResidueField 𝒪))) ≠ 0 := by
    rw [hg_map, hx₀, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hgbar_sep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨ξ, hξ_res, hξ_sq⟩ :=
    mono_newton_step hπ g x₀ haeval_zero haeval_deriv
  have hξ_residue : IsLocalRing.residue 𝒪 ξ = ξbar := by
    rw [hξ_res, hx₀]
  set θ : 𝒪 := ξ + π with hθ
  have hθ_res : IsLocalRing.residue 𝒪 θ = ξbar := by
    rw [hθ, map_add, hξ_residue]
    have : IsLocalRing.residue 𝒪 π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, mono_maximalIdeal_eq_span hπ]
      exact Ideal.mem_span_singleton_self π
    rw [this, add_zero]
  have hθ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
      ({IsLocalRing.residue 𝒪 θ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤ := by
    rw [hθ_res]; exact hξbar
  set G : Polynomial 𝒪 := g.map (algebraMap 𝒪K 𝒪) with hGdef
  have hξsq_span : Polynomial.eval ξ G ∈ Ideal.span ({π ^ 2} : Set 𝒪) := by
    have := hξ_sq
    rw [mono_maximalIdeal_eq_span hπ, Ideal.span_singleton_pow] at this
    exact this
  rw [Ideal.mem_span_singleton] at hξsq_span
  obtain ⟨d, hd⟩ := hξsq_span
  have hDerivξ_unit :
      IsUnit (Polynomial.eval ξ (Polynomial.derivative G)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hGdef,
      Polynomial.derivative_map,
      mono_residue_eval_lift (Polynomial.derivative g) ξ, hξ_residue]
    rw [← Polynomial.derivative_map, hg_map, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    exact hgbar_sep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion G ξ π
  set D' := Polynomial.eval ξ (Polynomial.derivative G) with hD'
  set u : 𝒪 := D' + π * (d + k) with hu
  have hϖ_eq : Polynomial.eval θ G = π * u := by
    rw [hθ, hk, hd, hu]
    rw [hD']
    ring
  have hu_unit : IsUnit u := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hu, map_add, map_mul]
    have hπ_res : IsLocalRing.residue 𝒪 π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, mono_maximalIdeal_eq_span hπ]
      exact Ideal.mem_span_singleton_self π
    rw [hπ_res, zero_mul, add_zero, hD']
    rw [IsLocalRing.residue_ne_zero_iff_isUnit]
    exact hDerivξ_unit
  have hϖ_irred : Irreducible (Polynomial.eval θ G) := by
    rw [hϖ_eq, irreducible_mul_isUnit hu_unit]
    exact hπ
  have hϖ_mem : Polynomial.eval θ G ∈ Algebra.adjoin 𝒪K ({θ} : Set 𝒪) := by
    rw [hGdef,
      show Polynomial.eval θ (g.map (algebraMap 𝒪K 𝒪))
          = Polynomial.aeval θ g from by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]]
    exact Polynomial.aeval_mem_adjoin_singleton 𝒪K θ
  refine ⟨θ, ?_⟩
  rw [eq_top_iff]
  have htwo := mono_adjoin_two_gen (𝒪K := 𝒪K)
    θ (Polynomial.eval θ G) hθ_prim hϖ_irred
  rw [← htwo]
  rw [Algebra.adjoin_le_iff]
  intro y hy
  rcases hy with hy | hy
  · rw [hy]; exact Algebra.self_mem_adjoin_singleton 𝒪K θ
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]; exact hϖ_mem

end Neukirch.Chapter2.Sections8to10
