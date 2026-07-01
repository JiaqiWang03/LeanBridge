import Mathlib

/-!
# Basis-independence of the discriminant (up to associates)

Any two `R`-bases of a finite free `R`-algebra `S` have associated discriminants:
they differ by the square of the (unit) determinant of the change-of-basis matrix.
This is the ideal-theoretic content behind "the discriminant ideal is independent
of the chosen basis".
-/

/-- Two `R`-bases of `S` give associated discriminants (they differ by a unit
square, namely the square of the change-of-basis determinant). -/
theorem Algebra.discr_associated_of_basis
    {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι R S) (b' : Module.Basis κ R S) :
    Associated (Algebra.discr R ⇑b) (Algebra.discr R ⇑b') := by
  classical
  -- Step 1: reindex `b'` onto the index type `ι`.
  set e : ι ≃ κ := b.indexEquiv b' with he
  set c' : Module.Basis ι R S := b'.reindex e.symm with hc'def
  have hcoe : (⇑c' : ι → S) = ⇑b' ∘ ⇑e := by
    rw [hc'def]; ext i; simp
  have hc'discr : Algebra.discr R ⇑c' = Algebra.discr R ⇑b' := by
    rw [hcoe]
    have h := Algebra.discr_reindex R b' e.symm
    simpa using h
  -- Step 2: `b` and `c'` share the index `ι`; relate via the change-of-basis matrix.
  set P : Matrix ι ι R := b.toMatrix c' with hP
  have hvec : (⇑c' : ι → S) = Matrix.vecMul (⇑b) (P.map (algebraMap R S)) := by
    funext j
    rw [Matrix.vecMul_eq_sum, Finset.sum_apply, ← Module.Basis.sum_repr b (c' j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Matrix.map_apply, hP, Module.Basis.toMatrix_apply, smul_eq_mul,
      Algebra.smul_def]
    ring
  have hdiscr : Algebra.discr R ⇑c' = P.det ^ 2 * Algebra.discr R ⇑b := by
    rw [hvec]; exact Algebra.discr_of_matrix_vecMul (⇑b) P
  have hPunit : IsUnit P.det := by
    rw [hP, ← Module.Basis.det_apply]; exact b.isUnit_det c'
  refine ⟨(hPunit.pow 2).unit, ?_⟩
  rw [IsUnit.unit_spec, ← hc'discr, hdiscr]; ring
