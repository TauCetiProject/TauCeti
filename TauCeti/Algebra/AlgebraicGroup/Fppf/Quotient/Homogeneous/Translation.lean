/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.RationalPoints

/-!
# Left translation and the rational points of homogeneous quotients

Over an algebraically closed field, the identification of rational points of fppf
homogeneous quotients with left cosets intertwines left translation by ground-ring-valued
points with Mathlib's usual left action on cosets. The comparison uses the actual sheaf
automorphism, not a separate action transported across a bijection.

The translation automorphisms are constructed in `Homogeneous.Basic` over every commutative
base ring, without normality or representability assumptions. Only translation by
ground-ring-valued points is used here, not an internal action morphism of sheaves.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, homogeneous spaces and quotient sheaves.
-/

public section

open CategoryTheory Opposite

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

/-- Over an algebraically closed field, the rational-point/coset comparison intertwines
left translation on the fppf quotient with the usual left action on cosets. -/
theorem fppfHomogeneousQuotientTranslation_hom_app_rationalPointsEquiv
    {k : Type u} [Field k] [IsAlgClosed k] (H : _root_.CommHopfAlgCat.{u} k)
    (I : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
      quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    (fppfHomogeneousQuotientTranslation H I g).hom.hom.app (op (op (CommAlgCat.of k k)))
        (fppfHomogeneousQuotientRationalPointsEquiv H I q) =
      fppfHomogeneousQuotientRationalPointsEquiv H I (g • q) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [fppfHomogeneousQuotientRationalPointsEquiv_mk,
      fppfHomogeneousQuotientTranslation_hom_app_projection,
      MulAction.Quotient.smul_mk, smul_eq_mul,
      fppfHomogeneousQuotientRationalPointsEquiv_mk, HopfAlgebra.extendPoint_self]

end

end CommHopfAlgCat
