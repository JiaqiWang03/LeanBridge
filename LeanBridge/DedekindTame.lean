import Mathlib

/-!
# Trace over a filtration and the sharp tame different formula

This file builds the linear-algebra input for the wild-ramification part of Dedekind's
different theorem: the trace of multiplication on `𝒪_L / 𝔪_L ^ e` equals `e` times the
residue-field trace. The key general lemma is additivity of the trace along an
`f`-invariant submodule.
-/

open LinearMap Submodule Module

namespace DedekindTame

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
  · -- p-block: `tr (f ∘ ι_p ∘ Pp) = tr (f|_p)`
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
    congr 1
    ext x
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_restrict_apply,
      hPpdef, Submodule.projectionOnto_apply_of_mem_left hq (hp _ x.2)]
  · -- q-block: `tr (f ∘ ι_q ∘ Pq) = tr (f on M ⧸ p)` via `q ≃ M ⧸ p`
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm',
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

@[simp] theorem mulPow_coe_apply (x : S) (i : ℕ)
    (y : Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) :
    (mulPow x i y : S ⧸ P ^ e) = Ideal.Quotient.mk (P ^ e) x * (y : S ⧸ P ^ e) := rfl

/-- `mulPow` commutes with the inclusion `P^(i+1)/P^e ↪ P^i/P^e`. -/
theorem mulPow_comp_inclusion (x : S) (i : ℕ) (w) :
    Ideal.powQuotSuccInclusion p P i (mulPow x (i + 1) w) =
      mulPow x i (Ideal.powQuotSuccInclusion p P i w) := by
  ext
  simp only [Ideal.powQuotSuccInclusion_apply_coe, mulPow_coe_apply]

/-- `mulPow` preserves the image `P^(i+1)/P^e ⊆ P^i/P^e`. -/
theorem mulPow_mapsTo_range (x : S) (i : ℕ) :
    ∀ z ∈ LinearMap.range (Ideal.powQuotSuccInclusion p P i),
      mulPow x i z ∈ LinearMap.range (Ideal.powQuotSuccInclusion p P i) := by
  rintro z ⟨w, rfl⟩
  exact ⟨mulPow x (i + 1) w, mulPow_comp_inclusion x i w⟩

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

set_option maxHeartbeats 1000000 in
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
  -- Intertwining `mapQ ∘ E = E ∘ (mult by x)`, using only the explicit forward map `E`.
  have hint : ((LinearMap.range (Ideal.powQuotSuccInclusion p P i)).mapQ _ (mulPow x i)
        (mulPow_mapsTo_range x i)) ∘ₗ E.toLinearMap
      = E.toLinearMap ∘ₗ Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) := by
    ext y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P y
    simp only [LinearMap.coe_comp, Function.comp_apply, hE, LinearEquiv.coe_coe,
      LinearEquiv.ofBijective_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    rw [Ideal.quotientToQuotientRangePowQuotSucc_mk, Submodule.mapQ_apply,
      show (Ideal.Quotient.mk P x) * Submodule.Quotient.mk y
        = Submodule.Quotient.mk (x * y) from rfl,
      Ideal.quotientToQuotientRangePowQuotSucc_mk]
    refine congrArg _ (Subtype.ext ?_)
    simp only [mulPow_coe_apply, ← map_mul]
    congr 1
    ring
  have hconj : E.symm.conj ((LinearMap.range (Ideal.powQuotSuccInclusion p P i)).mapQ _
        (mulPow x i) (mulPow_mapsTo_range x i))
      = Algebra.lmul (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P x) := by
    ext z
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_symm]
    rw [show ((LinearMap.range (Ideal.powQuotSuccInclusion p P i)).mapQ _ (mulPow x i)
        (mulPow_mapsTo_range x i)) (E z) = E (Algebra.lmul (R ⧸ p) (S ⧸ P)
        (Ideal.Quotient.mk P x) z) from LinearMap.congr_fun hint z,
      LinearEquiv.symm_apply_apply]
  rw [← LinearMap.trace_conj' _ E.symm, hconj, Algebra.trace_apply]

set_option maxHeartbeats 4000000 in
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

end CoreTrace

end DedekindTame
