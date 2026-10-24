/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Basic

/-!
# Conjugation of centralizers of Lie algebra elements

For a rational point `g` of an affine group `G`, the centralizer of `Ad(g) x` is the
conjugate `g C_G(x) g⁻¹`. This file identifies their defining Hopf ideals, and hence their
closed subgroup schemes, using the actual adjoint representation on the cotangent dual.
There is no characteristic, smoothness or connectedness hypothesis. The equality retains
the equations on arbitrary coefficient algebras, including nonreduced ones.

`TauCeti.centralizerConjugationEquiv` is the resulting coordinate-algebra isomorphism.
Its direction is contravariant: from the coordinate algebra of `C_G(Ad(g) x)` to that of
`C_G(x)`. The formula on quotient classes records its compatibility with the two closed
embeddings into `G`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §1.3.
-/

public section

namespace TauCeti

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

attribute [local instance] Derivation.adjointComodule

/-- Conjugating a Lie algebra element conjugates its scheme-theoretic centralizer.
Here `basePointsRepresentation` is the actual adjoint point action on the cotangent dual. -/
theorem centralizerHopfIdeal_basePointsRepresentation
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (g : WithConv (H →ₐ[k] k)) :
    centralizerHopfIdeal H
        (Comodule.basePointsRepresentation (H := H) _ g x) =
      (centralizerHopfIdeal H x).conjugate g := by
  simp only [centralizerHopfIdeal_def]
  exact Comodule.stabilizerHopfIdeal_basePointsRepresentation x g

/-- The coordinate isomorphism induced by conjugation `C_G(x) → C_G(Ad(g) x)`.
Its pullback sends the class of `a` to the class of the pullback of `a` under conjugation by `g`.
-/
noncomputable def centralizerConjugationEquiv
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (g : WithConv (H →ₐ[k] k)) :
    (H ⧸ (centralizerHopfIdeal H
      (Comodule.basePointsRepresentation (H := H) _ g x)).toIdeal) ≃ₐc[k]
        (H ⧸ (centralizerHopfIdeal H x).toIdeal) :=
  (centralizerHopfIdeal H x).quotientConjugationEquiv _ g
    (centralizerHopfIdeal_basePointsRepresentation x g)

/-- The coordinate isomorphism agrees with ambient point conjugation on quotient classes. -/
@[simp]
theorem centralizerConjugationEquiv_mk
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (g : WithConv (H →ₐ[k] k)) (a : H) :
    centralizerConjugationEquiv x g (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk (centralizerHopfIdeal H x).toIdeal
        (HopfAlgebra.pointConjugationAlgHom g a) := by
  exact (centralizerHopfIdeal H x).quotientConjugationEquiv_mk _ g _ a

/-- The inverse coordinate isomorphism agrees with inverse ambient conjugation. -/
@[simp]
theorem centralizerConjugationEquiv_symm_mk
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (g : WithConv (H →ₐ[k] k)) (a : H) :
    (centralizerConjugationEquiv x g).symm
        (Ideal.Quotient.mk (centralizerHopfIdeal H x).toIdeal a) =
      Ideal.Quotient.mk _ ((HopfAlgebra.pointConjugationBialgEquiv g).symm a) := by
  exact (centralizerHopfIdeal H x).quotientConjugationEquiv_symm_mk _ g _ a

end TauCeti
