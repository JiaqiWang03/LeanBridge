import Mathlib

/-!
# Basis-independence of the discriminant (up to associates)

Any two `R`-bases of a finite free `R`-algebra `S` have associated discriminants:
they differ by the square of the (unit) determinant of the change-of-basis matrix.
This is the ideal-theoretic content behind "the discriminant ideal is independent
of the chosen basis".
-/

open scoped Classical in
/-- Two `R`-bases of `S` give associated discriminants (they differ by a unit
square, namely the square of the change-of-basis determinant). -/
theorem Algebra.discr_associated_of_basis
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι R S) (b' : Module.Basis κ R S) :
    Associated (Algebra.discr R ⇑b) (Algebra.discr R ⇑b') := by
  sorry
