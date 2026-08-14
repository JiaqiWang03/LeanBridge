import Mathlib

namespace Monogenicity

open scoped WithZero

/-- `𝔪K·S` is a power of `𝔪`. -/
theorem mono_exists_mapMK_eq_pow
    {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R]
    {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
    {π : S} (hπ : Irreducible π) :
    ∃ e : ℕ, Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)
      = (IsLocalRing.maximalIdeal S) ^ e := by
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
    (Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field R)) hπ
  exact ⟨e, by rw [he, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

variable
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
    [IsLocalHom (algebraMap R S)]

/-- A uniformizer has zero residue. -/
lemma mono_residue_uniformizer_eq_zero {π : S} (hπ : Irreducible π) :
    IsLocalRing.residue S π = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq]
  exact Ideal.mem_span_singleton_self π

omit [FaithfulSMul R S] in
/-- The residue extension `λ/κ` is module-finite. -/
theorem mono_residueField_finite :
    Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
  inferInstance

omit [Module.Finite R S] [FaithfulSMul R S] in
/-- **Residue bridge.**  For `g : R[X]` and `x : S`, the residue of
`eval x (g.map (R→S))` is the evaluation at `residue S x` of `g` mapped down
the residue tower `R → κ → λ`. -/
theorem mono_residue_eval_lift (g : Polynomial R) (x : S) :
    IsLocalRing.residue S
        (Polynomial.eval x (g.map (algebraMap R S)))
      = Polynomial.eval (IsLocalRing.residue S x)
          ((g.map (algebraMap R (IsLocalRing.ResidueField R))).map
            (algebraMap (IsLocalRing.ResidueField R)
              (IsLocalRing.ResidueField S))) := by
  have hcomp : (IsLocalRing.residue S).comp (algebraMap R S)
        = (algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S)).comp (algebraMap R (IsLocalRing.ResidueField R)) := by
    apply RingHom.ext
    intro a
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsLocalRing.ResidueField.algebraMap_eq R,
      IsLocalRing.ResidueField.algebraMap_residue]
  have hmaps : (g.map (algebraMap R S)).map (IsLocalRing.residue S)
      = (g.map (algebraMap R (IsLocalRing.ResidueField R))).map
          (algebraMap (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField S)) := by
    rw [Polynomial.map_map, Polynomial.map_map, hcomp]
  rw [← Polynomial.eval_map_apply (IsLocalRing.residue S)
      (p := g.map (algebraMap R S)) x, hmaps]

/-- **Two-generator monogenicity.**  With `π` a uniformizer and `ξ` any lift of
a primitive element `ξ̄` of `λ/κ`, `R[ξ, π] = S`. -/
theorem mono_adjoin_two_gen
    (ξ π : S)
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField R)
       ({IsLocalRing.residue S ξ} : Set (IsLocalRing.ResidueField S)) = ⊤)
    (hπ : Irreducible π) :
    Algebra.adjoin R ({ξ, π} : Set S) = ⊤ := by
  classical
  haveI : Module.Finite (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) := mono_residueField_finite
  obtain ⟨e, hmap_pow⟩ := mono_exists_mapMK_eq_pow (R := R) (S := S) hπ
  set A : Subalgebra R S := Algebra.adjoin R ({ξ, π} : Set S) with hA
  have hπA : π ∈ A := Algebra.subset_adjoin (by simp)
  have hbase : ∀ c : S, ∃ b : S, b ∈ A ∧ c - b ∈ (Ideal.span {π} : Ideal S) := by
    intro c
    have hint : IsIntegral (IsLocalRing.ResidueField R)
        (IsLocalRing.residue S ξ) :=
      Algebra.IsIntegral.isIntegral _
    have hAlgTop : Algebra.adjoin (IsLocalRing.ResidueField R)
        ({IsLocalRing.residue S ξ} : Set (IsLocalRing.ResidueField S)) = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
        hξ_prim, IntermediateField.top_toSubalgebra]
    have hmem : IsLocalRing.residue S c ∈
        Algebra.adjoin (IsLocalRing.ResidueField R)
          ({IsLocalRing.residue S ξ} : Set (IsLocalRing.ResidueField S)) :=
      hAlgTop ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨p, hp⟩ := hmem
    have hsurj : Function.Surjective
        (algebraMap R (IsLocalRing.ResidueField R)) := by
      rw [IsLocalRing.ResidueField.algebraMap_eq]
      exact IsLocalRing.residue_surjective
    obtain ⟨q, hq⟩ := Polynomial.map_surjective _ hsurj p
    refine ⟨Polynomial.aeval ξ q, ?_, ?_⟩
    · exact Algebra.adjoin_mono (by simp) (Polynomial.aeval_mem_adjoin_singleton R ξ)
    · have hbeq : IsLocalRing.residue S (Polynomial.aeval ξ q)
          = IsLocalRing.residue S c := by
        rw [show Polynomial.aeval ξ q
              = Polynomial.eval ξ (q.map (algebraMap R S)) from by
                rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]]
        rw [mono_residue_eval_lift q ξ, hq, Polynomial.eval_map,
          ← Polynomial.aeval_def]
        exact hp
      rw [← hπ.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff,
        map_sub, hbeq]
      exact sub_self _
  have hind : ∀ n : ℕ, ∀ a : S,
      ∃ b : S, b ∈ A ∧ a - b ∈ (Ideal.span {π} ^ n : Ideal S) := by
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
  have hmap : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)
      = (Ideal.span {π} ^ e : Ideal S) := by
    rw [hmap_pow, hπ.maximalIdeal_eq]
  have hP_eq : ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R S))
      = ((Ideal.span {π} ^ e : Ideal S).restrictScalars R) := by
    rw [Ideal.smul_top_eq_map, hmap]
  have hNak : (Subalgebra.toSubmodule A).map
      (Submodule.mkQ ((IsLocalRing.maximalIdeal R)
        • (⊤ : Submodule R S))) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, rfl⟩ :=
      Submodule.mkQ_surjective
        ((IsLocalRing.maximalIdeal R) • (⊤ : Submodule R S)) z
    obtain ⟨b, hbA, hab⟩ := hind e a
    refine Submodule.mem_map.mpr ⟨b, (show b ∈ A from hbA), ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hP_eq,
      Submodule.restrictScalars_mem, show b - a = -(a - b) from by ring]
    exact neg_mem hab
  exact (IsLocalRing.map_mkQ_eq_top (R := R) (M := S)
    (N := Subalgebra.toSubmodule A)).mp hNak

omit [Module.Finite R S] [FaithfulSMul R S] in
/-- One Newton step: given a monic `g : R[X]`, a uniformizer `π`, and a lift
`x₀` of a simple root `ξ̄` of `g` over `κ`, there is `x = x₀ + π·t` with the
same residue and `g(x) ∈ 𝔪²`. -/
theorem mono_newton_step
    {π : S} (hπ : Irreducible π) (g : Polynomial R) (x₀ : S)
    (hroot : Polynomial.eval (IsLocalRing.residue S x₀)
        ((g.map (algebraMap R (IsLocalRing.ResidueField R))).map
          (algebraMap (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField S))) = 0)
    (hderiv : Polynomial.eval (IsLocalRing.residue S x₀)
        ((Polynomial.derivative
            (g.map (algebraMap R (IsLocalRing.ResidueField R)))).map
          (algebraMap (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField S))) ≠ 0) :
    ∃ x : S, IsLocalRing.residue S x = IsLocalRing.residue S x₀ ∧
      Polynomial.eval x (g.map (algebraMap R S))
        ∈ (IsLocalRing.maximalIdeal S) ^ 2 := by
  classical
  set G : Polynomial S := g.map (algebraMap R S) with hG
  have hGx₀_mem : Polynomial.eval x₀ G ∈ IsLocalRing.maximalIdeal S := by
    rw [← IsLocalRing.residue_eq_zero_iff, hG, mono_residue_eval_lift g x₀, hroot]
  have hDeriv_unit : IsUnit (Polynomial.eval x₀ (Polynomial.derivative G)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hG, Polynomial.derivative_map,
      mono_residue_eval_lift (Polynomial.derivative g) x₀]
    rwa [Polynomial.derivative_map] at hderiv
  have hmem_span : Polynomial.eval x₀ G ∈ Ideal.span ({π} : Set S) := by
    rw [← hπ.maximalIdeal_eq]; exact hGx₀_mem
  rw [Ideal.mem_span_singleton] at hmem_span
  obtain ⟨b, hb⟩ := hmem_span
  set D := Polynomial.eval x₀ (Polynomial.derivative G) with hD
  set t : S := -(↑(hDeriv_unit.unit⁻¹) : S) * b with ht
  have hDinv : D * (↑(hDeriv_unit.unit⁻¹) : S) = 1 :=
    hDeriv_unit.mul_val_inv
  have hDt : D * t = -b := by
    have : D * t = -(D * (↑(hDeriv_unit.unit⁻¹) : S)) * b := by
      rw [ht]; ring
    rw [this, hDinv, neg_one_mul]
  refine ⟨x₀ + π * t, ?_, ?_⟩
  · rw [map_add, map_mul, mono_residue_uniformizer_eq_zero hπ, zero_mul, add_zero]
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
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact ⟨k * t ^ 2, rfl⟩

/-! ## Main theorem — single-generator monogenicity (Neukirch II.10.4) -/

/-- **Neukirch II.10.4.**  Under the standing finite-DVR-extension hypotheses
and a **separable** residue extension `λ/κ`, there is `θ : S` with
`Algebra.adjoin R {θ} = ⊤`, i.e. `S = R[θ]`. -/
theorem mono_exists_primitive
    [Algebra.IsSeparable
       (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)] :
    ∃ θ : S, Algebra.adjoin R ({θ} : Set S) = ⊤ := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  haveI : Module.Finite (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S) := mono_residueField_finite
  obtain ⟨ξbar, hξbar⟩ :=
    Field.exists_primitive_element (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField S)
  obtain ⟨x₀, hx₀⟩ := IsLocalRing.residue_surjective (R := S) ξbar
  set gbar : Polynomial (IsLocalRing.ResidueField R) :=
    minpoly (IsLocalRing.ResidueField R) ξbar with hgbar
  have hgbar_sep : gbar.Separable :=
    (Algebra.IsSeparable.isSeparable
      (IsLocalRing.ResidueField R) ξbar)
  have hgbar_monic : gbar.Monic :=
    minpoly.monic
      (Algebra.IsIntegral.isIntegral (R := IsLocalRing.ResidueField R) ξbar)
  have hsurj : Function.Surjective
      (algebraMap R (IsLocalRing.ResidueField R)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq R]
    exact IsLocalRing.residue_surjective
  have hlifts : gbar ∈ Polynomial.lifts
      (algebraMap R (IsLocalRing.ResidueField R)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact hsurj (gbar.coeff n)
  obtain ⟨g, hg_map, _hg_deg, _hg_monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts hgbar_monic
  have haeval_zero : Polynomial.eval (IsLocalRing.residue S x₀)
      ((g.map (algebraMap R (IsLocalRing.ResidueField R))).map
        (algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S))) = 0 := by
    rw [hg_map, hx₀, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval _ _
  have haeval_deriv : Polynomial.eval (IsLocalRing.residue S x₀)
      ((Polynomial.derivative
          (g.map (algebraMap R (IsLocalRing.ResidueField R)))).map
        (algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField S))) ≠ 0 := by
    rw [hg_map, hx₀, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hgbar_sep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨ξ, hξ_res, hξ_sq⟩ :=
    mono_newton_step hπ g x₀ haeval_zero haeval_deriv
  have hξ_residue : IsLocalRing.residue S ξ = ξbar := by
    rw [hξ_res, hx₀]
  set θ : S := ξ + π with hθ
  have hθ_res : IsLocalRing.residue S θ = ξbar := by
    rw [hθ, map_add, hξ_residue, mono_residue_uniformizer_eq_zero hπ, add_zero]
  have hθ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField R)
      ({IsLocalRing.residue S θ} : Set (IsLocalRing.ResidueField S)) = ⊤ := by
    rw [hθ_res]; exact hξbar
  set G : Polynomial S := g.map (algebraMap R S) with hGdef
  have hξsq_span : Polynomial.eval ξ G ∈ Ideal.span ({π ^ 2} : Set S) := by
    have := hξ_sq
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow] at this
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
  set u : S := D' + π * (d + k) with hu
  have hϖ_eq : Polynomial.eval θ G = π * u := by
    rw [hθ, hk, hd, hu]
    rw [hD']
    ring
  have hu_unit : IsUnit u := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hu, map_add, map_mul,
      mono_residue_uniformizer_eq_zero hπ, zero_mul, add_zero, hD',
      IsLocalRing.residue_ne_zero_iff_isUnit]
    exact hDerivξ_unit
  have hϖ_irred : Irreducible (Polynomial.eval θ G) := by
    rw [hϖ_eq, irreducible_mul_isUnit hu_unit]
    exact hπ
  have hϖ_mem : Polynomial.eval θ G ∈ Algebra.adjoin R ({θ} : Set S) := by
    rw [hGdef,
      show Polynomial.eval θ (g.map (algebraMap R S))
          = Polynomial.aeval θ g from by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]]
    exact Polynomial.aeval_mem_adjoin_singleton R θ
  refine ⟨θ, ?_⟩
  rw [eq_top_iff]
  have htwo := mono_adjoin_two_gen (R := R)
    θ (Polynomial.eval θ G) hθ_prim hϖ_irred
  rw [← htwo]
  rw [Algebra.adjoin_le_iff]
  intro y hy
  rcases hy with hy | hy
  · rw [hy]; exact Algebra.self_mem_adjoin_singleton R θ
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]; exact hϖ_mem

end Monogenicity
