import Mathlib

/-!
# Trace over a filtration and the sharp tame different formula

This file builds the linear-algebra input for the wild-ramification part of Dedekind's
different theorem: the trace of multiplication on `𝒪_L / 𝔪_L ^ e` equals `e` times the
residue-field trace. The key general lemma is additivity of the trace along an
`f`-invariant submodule.
-/

open LinearMap Submodule Module

namespace TraceFiltration

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]

/-- **Trace is additive along an invariant submodule.** If `f` maps the subspace `p`
into itself, then `tr f = tr (f|_p) + tr (f on M ⧸ p)`. -/
theorem trace_eq_restrict_add_mapQ (f : Module.End k M) {p : Submodule k M}
    (hp : ∀ x ∈ p, f x ∈ p) :
    trace k M f = trace k p (f.restrict hp) + trace k (M ⧸ p) (p.mapQ p f hp) := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl p
  set Pp : M →ₗ[k] p := p.projectionOnto q hq with hPpdef
  set Pq : M →ₗ[k] q := q.projectionOnto p hq.symm with hPqdef
  have hid : p.subtype ∘ₗ Pp + q.subtype ∘ₗ Pq = LinearMap.id := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.id_coe, id_eq, hPpdef, hPqdef, Submodule.coe_projectionOnto_apply]
    exact projection_add_projection_eq_self hq x
  have hfcomp : f = f ∘ₗ (p.subtype ∘ₗ Pp) + f ∘ₗ (q.subtype ∘ₗ Pq) := by
    rw [← LinearMap.comp_add, hid, LinearMap.comp_id]
  conv_lhs => rw [hfcomp]
  rw [map_add]
  congr 1
  · rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
    congr 1
    ext x
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_restrict_apply,
      hPpdef, Submodule.projectionOnto_apply_of_mem_left hq (hp _ x.2)]
  · rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm',
      ← LinearMap.trace_conj' (p.mapQ p f hp) (p.quotientEquivOfIsCompl q hq)]
    congr 1

/-!
## The core trace formula `tr(μ_x on S/P^e) = e · Tr_{S/P}(x̄)`

We mirror Mathlib's `Ideal.rank_pow_quot` (which proves `[S/P^e : R/p] = e·[S/P:R/p]`)
but for the trace of multiplication by `x`, using the invariant-submodule additivity
`trace_eq_restrict_add_mapQ` in place of `rank_quotient_add_rank`, and the graded-piece
isomorphism `Ideal.quotientRangePowQuotSuccInclusionEquiv`.
-/

section CoreTrace

open Ideal

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  {p : Ideal R} {P : Ideal S} [p.IsMaximal] [P.IsPrime] [IsDedekindDomain S]
  [NeZero (Ideal.ramificationIdx p P)] [Module.Finite R S]

attribute [local instance] Ideal.Quotient.field
attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

local notation "e" => Ideal.ramificationIdx p P

/-- Multiplication by `mk x` as an `R/p`-linear endomorphism of `M i = P^i / P^e`,
built from the `(S/P^e)`-linear multiplication (so the module `↥(P^i/P^e)` keeps its
canonical `R/p`-module structure, matching `Ideal.powQuotSuccInclusion`). -/
noncomputable def mulPow (x : S) (i : ℕ) :
    Module.End (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) :=
  LinearMap.restrictScalars (R ⧸ p)
    (LinearMap.restrict (LinearMap.mulLeft (S ⧸ P ^ e) (Ideal.Quotient.mk (P ^ e) x))
      (fun _ hy => Ideal.mul_mem_left _ _ hy))

omit [p.IsMaximal] [P.IsPrime] [IsDedekindDomain S] [NeZero e] [Module.Finite R S] in
@[simp]
lemma mulPow_coe_apply (x : S) (i : ℕ)
    (y : Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) :
    (mulPow x i y : S ⧸ P ^ e) = Ideal.Quotient.mk (P ^ e) x * (y : S ⧸ P ^ e) := rfl

omit [p.IsMaximal] [P.IsPrime] [IsDedekindDomain S] [NeZero e] [Module.Finite R S] in
/-- `mulPow` commutes with the inclusion `P^(i+1)/P^e ↪ P^i/P^e`. -/
lemma mulPow_comp_inclusion (x : S) (i : ℕ) (w) :
    Ideal.powQuotSuccInclusion p P i (mulPow x (i + 1) w) =
      mulPow x i (Ideal.powQuotSuccInclusion p P i w) := by
  ext
  simp only [Ideal.powQuotSuccInclusion_apply_coe, mulPow_coe_apply]

omit [p.IsMaximal] [P.IsPrime] [IsDedekindDomain S] [NeZero e] [Module.Finite R S] in
/-- `mulPow` preserves the image `P^(i+1)/P^e ⊆ P^i/P^e`. -/
lemma mulPow_mapsTo_range (x : S) (i : ℕ) :
    ∀ z ∈ LinearMap.range (Ideal.powQuotSuccInclusion p P i),
      mulPow x i z ∈ LinearMap.range (Ideal.powQuotSuccInclusion p P i) := by
  rintro z ⟨w, rfl⟩
  exact ⟨mulPow x (i + 1) w, mulPow_comp_inclusion x i w⟩

omit [p.IsMaximal] [P.IsPrime] [IsDedekindDomain S] [NeZero e] [Module.Finite R S] in
/-- The trace of `mulPow x i` restricted to the image `range(incl) ≃ P^(i+1)/P^e` is
the trace of `mulPow x (i+1)`. -/
theorem trace_mulPow_restrict_range (x : S) (i : ℕ) :
    LinearMap.trace (R ⧸ p) ↥(LinearMap.range (Ideal.powQuotSuccInclusion p P i))
        ((mulPow x i).restrict (mulPow_mapsTo_range x i)) =
      LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1)))
        (mulPow x (i + 1)) := by
  have hconj : (mulPow x i).restrict (mulPow_mapsTo_range x i) =
      (LinearEquiv.ofInjective _ (Ideal.powQuotSuccInclusion_injective p P i)).conj
        (mulPow x (i + 1)) := by
    ext w
    obtain ⟨z, rfl⟩ := (LinearEquiv.ofInjective _
      (Ideal.powQuotSuccInclusion_injective p P i)).surjective w
    simp only [LinearMap.coe_restrict_apply, LinearEquiv.conj_apply, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.ofInjective_apply, mulPow_coe_apply, Ideal.powQuotSuccInclusion_apply_coe]
  rw [hconj, LinearMap.trace_conj']

omit [p.IsMaximal] [Module.Finite R S] in
/-- The trace of `mulPow x i` on the graded quotient `(P^i/P^e)/(P^(i+1)/P^e) ≃ S/P`
equals the residue-field trace of `x`. -/
theorem trace_mulPow_mapQ (x : S) (hP0 : P ≠ ⊥) {i : ℕ} (hi : i < e) :
    LinearMap.trace (R ⧸ p)
        (↥(Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) ⧸
          LinearMap.range (Ideal.powQuotSuccInclusion p P i))
        ((LinearMap.range (Ideal.powQuotSuccInclusion p P i)).mapQ _ (mulPow x i)
          (mulPow_mapsTo_range x i)) =
      Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) := by
  obtain ⟨a, ha_mem, ha_notMem⟩ := SetLike.exists_of_lt
    (Ideal.pow_right_strictAnti P hP0 (Ideal.IsPrime.ne_top inferInstance) (le_refl i.succ))
  set E : (S ⧸ P) ≃ₗ[R ⧸ p] _ :=
    LinearEquiv.ofBijective (Ideal.quotientToQuotientRangePowQuotSucc p P ha_mem)
      ⟨Ideal.quotientToQuotientRangePowQuotSucc_injective p P hi ha_mem ha_notMem,
       Ideal.quotientToQuotientRangePowQuotSucc_surjective p P hP0 hi ha_mem ha_notMem⟩ with hE
  set f := (LinearMap.range (Ideal.powQuotSuccInclusion p P i)).mapQ
    (LinearMap.range (Ideal.powQuotSuccInclusion p P i)) (mulPow x i)
    (mulPow_mapsTo_range x i) with hf
  have hint : f ∘ₗ E.toLinearMap
      = E.toLinearMap ∘ₗ Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P w
    simp only [hf, LinearMap.coe_comp, Function.comp_apply, hE, LinearEquiv.coe_coe,
      LinearEquiv.ofBijective_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    rw [Ideal.quotientToQuotientRangePowQuotSucc_mk, Submodule.mapQ_apply,
      show (Ideal.Quotient.mk P x) * Submodule.Quotient.mk y
        = Submodule.Quotient.mk (x * y) from rfl,
      Ideal.quotientToQuotientRangePowQuotSucc_mk]
    refine congrArg _ (Subtype.ext ?_)
    simp only [mulPow_coe_apply, ← map_mul]
    congr 1
    ring
  have hconj : E.symm.conj f = Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) := by
    refine LinearMap.ext fun z => ?_
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_symm]
    rw [show f (E z) = E (Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) z)
        from LinearMap.congr_fun hint z, LinearEquiv.symm_apply_apply]
  rw [← LinearMap.trace_conj' _ E.symm, hconj, Algebra.trace_apply]

/-- The per-step trace identity (trace analogue of `Ideal.rank_pow_quot_aux`). -/
theorem trace_mulPow_succ (x : S) (hP0 : P ≠ ⊥) {i : ℕ} (hi : i < e) :
    LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) (mulPow x i) =
      Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) +
        LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1)))
          (mulPow x (i + 1)) := by
  haveI : Module.Finite R (S ⧸ P ^ e) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R (P ^ e)).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : IsScalarTower R (R ⧸ p) (S ⧸ P ^ e) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (R ⧸ p) (S ⧸ P ^ e) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ p) (S ⧸ P ^ e)
  haveI : FiniteDimensional (R ⧸ p)
      ↥(Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) := inferInstance
  have h := trace_eq_restrict_add_mapQ (mulPow x i)
    (p := LinearMap.range (Ideal.powQuotSuccInclusion p P i)) (mulPow_mapsTo_range x i)
  rw [trace_mulPow_restrict_range x i, trace_mulPow_mapQ x hP0 hi] at h
  rw [h, add_comm]

omit [P.IsPrime] [IsDedekindDomain S] [NeZero e] in
/-- Common finiteness/tower instances for the quotient `S / P^e` as an `R/p`-module. -/
lemma instFin_aux : Module.Finite R (S ⧸ P ^ e) ∧ FiniteDimensional (R ⧸ p) (S ⧸ P ^ e) := by
  haveI : Module.Finite R (S ⧸ P ^ e) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R (P ^ e)).toLinearMap
      Ideal.Quotient.mk_surjective
  haveI : IsScalarTower R (R ⧸ p) (S ⧸ P ^ e) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨inferInstance, Module.Finite.of_restrictScalars_finite R (R ⧸ p) (S ⧸ P ^ e)⟩

/-- Telescoping the per-step identity: the trace of `mulPow x 0` on `P^0/P^e` equals
`e` times the residue trace of `x`. -/
theorem trace_mulPow_zero_eq_nsmul (x : S) (hP0 : P ≠ ⊥) :
    LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ 0)) (mulPow x 0) =
      e • Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) := by
  haveI : Module.Finite R (S ⧸ P ^ e) := instFin_aux.1
  haveI : FiniteDimensional (R ⧸ p) (S ⧸ P ^ e) := instFin_aux.2
  -- Auxiliary telescoping statement.
  have aux : ∀ i, i ≤ e →
      LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ 0)) (mulPow x 0) =
        i • Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) +
          LinearMap.trace (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) (mulPow x i) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [ih (Nat.le_of_succ_le hn), trace_mulPow_succ x hP0 (Nat.lt_of_succ_le hn),
        succ_nsmul]
      ring
  have hterm : LinearMap.trace (R ⧸ p)
      (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ e)) (mulPow x e) = 0 := by
    haveI : Subsingleton ↥(Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ e)) := by
      rw [Ideal.map_quotient_self]; infer_instance
    rw [Subsingleton.elim (mulPow x e) 0, map_zero]
  rw [aux e le_rfl, hterm, add_zero]

/-- **Core trace formula.** For the (non-reduced) quotient `S / P^e`, the trace of
multiplication by `x` equals `e` times the residue-field trace of `x`. -/
theorem algebra_trace_quot_pow_eq_nsmul (x : S) (hP0 : P ≠ ⊥) :
    Algebra.trace (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk (P ^ e) x) =
      e • Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) := by
  haveI : Module.Finite R (S ⧸ P ^ e) := instFin_aux.1
  haveI : FiniteDimensional (R ⧸ p) (S ⧸ P ^ e) := instFin_aux.2
  rw [← trace_mulPow_zero_eq_nsmul x hP0]
  set N := Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ 0) with hN
  have hNtop : N = ⊤ := by rw [hN, pow_zero, Ideal.one_eq_top, Ideal.map_top]
  have hsurj : Function.Surjective ⇑(N.subtype) := by
    rw [← LinearMap.range_eq_top, Submodule.range_subtype, hNtop]
  set ε : ↥N ≃ₗ[R ⧸ p] (S ⧸ P ^ e) :=
    LinearEquiv.ofBijective (N.subtype.restrictScalars (R ⧸ p))
      ⟨fun a b h => Subtype.ext h, hsurj⟩ with hε
  have hfwd : ∀ z : ↥N, (ε z : S ⧸ P ^ e) = (z : S ⧸ P ^ e) := fun _ => rfl
  have hcoe : ∀ w : S ⧸ P ^ e, ((ε.symm w : ↥N) : S ⧸ P ^ e) = w :=
    fun w => ε.apply_symm_apply w
  have hconj : mulPow x 0 =
      ε.symm.conj (Algebra.lmul (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk (P ^ e) x)) := by
    ext y
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_symm, mulPow_coe_apply,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hfwd, hcoe]
  rw [Algebra.trace_apply, hconj, LinearMap.trace_conj']

/-- **Bridge to the integral trace.** When `p S = P^e` (e.g. `P` is the unique prime of
`S` over `p`), the integral trace of `x` reduces mod `p` to `e` times the residue-field
trace of `x`. -/
theorem intTrace_residue_scaling
    [IsDedekindDomain R] [Module.IsTorsionFree R S]
    (x : S) (hP0 : P ≠ ⊥) (hpe : Ideal.map (algebraMap R S) p = P ^ e) :
    Ideal.Quotient.mk p (Algebra.intTrace R S x) =
      e • Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) := by
  rw [← algebra_trace_quot_pow_eq_nsmul x hP0,
    ← Algebra.trace_quotient_eq_of_isDedekindDomain (p := p) (x := x)]
  have he : RingHom.comp (algebraMap (R ⧸ p) (S ⧸ P ^ e))
        ((RingEquiv.refl (R ⧸ p)) : (R ⧸ p) →+* (R ⧸ p)) =
      RingHom.comp ((Ideal.quotEquivOfEq hpe) : (S ⧸ Ideal.map (algebraMap R S) p) →+* (S ⧸ P ^ e))
        (algebraMap (R ⧸ p) (S ⧸ Ideal.map (algebraMap R S) p)) := by
    refine RingHom.ext fun z => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [RingHom.comp_apply, RingEquiv.coe_ringHom_refl, RingHom.id_apply,
      Ideal.Quotient.algebraMap_quotient_pow_ramificationIdx,
      Ideal.Quotient.algebraMap_quotient_map_quotient,
      RingEquiv.coe_toRingHom, Ideal.quotEquivOfEq_mk]
  rw [Algebra.trace_eq_of_equiv_equiv (RingEquiv.refl (R ⧸ p)) (Ideal.quotEquivOfEq hpe) he
    (Ideal.Quotient.mk (Ideal.map (algebraMap R S) p) x)]
  simp only [RingEquiv.symm_refl, RingEquiv.coe_refl, id_eq, Ideal.quotEquivOfEq_mk]

end CoreTrace

end TraceFiltration
