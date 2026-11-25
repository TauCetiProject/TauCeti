/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Functor.Diagonal

/-!
# Closed diagonals of relative divisor functors

On a proper relative curve locally of finite presentation, every relative effective Cartier
divisor is finite locally free over the parameter scheme. The equality locus of two such
families therefore represents a pullback of the diagonal by a closed immersion. This applies
both to the whole divisor functor and to each fixed-degree functor.

In particular a supplied scheme representing either functor is separated over the base.
These results establish the diagonal without requiring representability of the divisor functor.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  [LocallyOfFinitePresentation f] [RelativeDimensionLE 1 f]

private theorem finiteLocallyFree_relativeEffectiveCartierSubfunctor (T : Over S)
    (D : (relativeEffectiveCartierSubfunctor f).toFunctor.obj (op T)) :
    ((relativeEffectiveCartierSubfunctor f).ι.app (op T) D).IsFiniteLocallyFreeFamily f T := by
  have hD := (mem_relativeEffectiveCartierSubfunctor_obj_iff (f := f)).mp D.property
  exact ⟨hD.isFinite, hD.flat,
    TauCeti.locallyOfFinitePresentation_subschemeι_comp_of_isEffectiveCartier
      hD.isEffectiveCartier⟩

/-- The diagonal of the relative effective Cartier divisor functor of a proper relative curve
locally of finite presentation is representable by closed immersions over the base. -/
theorem isClosedImmersion_diagonal_relativeEffectiveCartierSubfunctor :
    MorphismProperty.relative yoneda
      (MorphismProperty.inverseImage (@IsClosedImmersion : MorphismProperty Scheme.{u})
        (Over.forget S)) (diag (relativeEffectiveCartierSubfunctor f).toFunctor) := by
  exact isClosedImmersion_diagonal_of_mono_baseChangeIdealSheafFunctor f _
    (relativeEffectiveCartierSubfunctor f).ι
    (finiteLocallyFree_relativeEffectiveCartierSubfunctor f)

/-- A scheme representing the relative effective Cartier divisor functor of a proper relative
curve locally of finite presentation is separated over the base. -/
theorem isSeparated_of_representableBy_relativeEffectiveCartierSubfunctor {H : Over S}
    (e : (relativeEffectiveCartierSubfunctor f).toFunctor.RepresentableBy H) :
    IsSeparated H.hom :=
  isSeparated_of_representableBy_of_relative_diag
    (isClosedImmersion_diagonal_relativeEffectiveCartierSubfunctor f) e

/-- The diagonal of the degree-`d` relative effective Cartier divisor functor of a proper
relative curve locally of finite presentation is representable by closed immersions. -/
theorem isClosedImmersion_diagonal_relativeEffectiveCartierDegreeSubfunctor (d : ℕ) :
    MorphismProperty.relative yoneda
      (MorphismProperty.inverseImage (@IsClosedImmersion : MorphismProperty Scheme.{u})
        (Over.forget S)) (diag (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor) := by
  exact isClosedImmersion_diagonal_of_mono_baseChangeIdealSheafFunctor f _
    ((relativeEffectiveCartierDegreeSubfunctor f d).ι ≫
      (relativeEffectiveCartierSubfunctor f).ι)
    (fun T D ↦ by
      rw [NatTrans.comp_app, Subfunctor.ι_app]
      exact finiteLocallyFree_relativeEffectiveCartierSubfunctor f T D.val)

/-- A supplied scheme representing degree-`d` relative effective Cartier divisors on a proper
relative curve locally of finite presentation is separated over the base. -/
theorem isSeparated_of_representableBy_relativeEffectiveCartierDegreeSubfunctor (d : ℕ)
    {H : Over S} (e : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.RepresentableBy H) :
    IsSeparated H.hom :=
  isSeparated_of_representableBy_of_relative_diag
    (isClosedImmersion_diagonal_relativeEffectiveCartierDegreeSubfunctor f d) e

end TauCeti.AlgebraicGeometry
