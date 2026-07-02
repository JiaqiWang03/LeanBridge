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

end DedekindTame
