/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Basic
public import TauCeti.CategoryTheory.Equivalence.EssImage

/-!
# Graded quasicoherent algebras freely generated in degree one

A graded quasicoherent algebra `A` on a scheme `X` is freely generated in degree one when it is
isomorphic, as a graded algebra, to the graded symmetric algebra `Sym F` of some quasicoherent
sheaf `F`; equivalently, when `Sym A₁ ≅ A` (`essImage_gradedSymmetricAlgebra_iff`). These algebras
form the full subcategory `FreeGradedQuasicoherentAlgebra X` of `GradedQuasicoherentAlgebra X`,
the essential image of `gradedSymmetricAlgebra X`. Their relative spectra are the linear schemes
`Spec_X Sym F` over `X` (Stacks Project, tag 01M1), whose morphisms preserve the grading.

Since the graded symmetric algebra functor is fully faithful and its degree-one component recovers
`F`, it is an equivalence
`gradedSymmetricAlgebraEquiv X : QuasicoherentSheaf X ≌ FreeGradedQuasicoherentAlgebra X`,
whose inverse is the degree-one functor and whose unit is the identification `F ≅ Sym¹ F`,
the inverse of `gradedSymmetricAlgebraDegreeOneIso`. A morphism of free graded algebras is
therefore the same as a morphism of their degree-one components.

## Main declarations

* `TauCeti.AlgebraicGeometry.FreeGradedQuasicoherentAlgebra`: graded quasicoherent algebras
  freely generated in degree one;
* `TauCeti.AlgebraicGeometry.essImage_gradedSymmetricAlgebra_iff`: a graded quasicoherent algebra
  is free in degree one exactly when it is isomorphic to the graded symmetric algebra of its
  degree-one component;
* `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraEquiv`: the equivalence between quasicoherent
  sheaves and graded quasicoherent algebras freely generated in degree one.
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry GradedQuasicoherentAlgebra

universe u

noncomputable section

variable (X : Scheme.{u})

/-- The category of graded quasicoherent algebras freely generated in degree one: the full
subcategory of `GradedQuasicoherentAlgebra X` on the algebras isomorphic to the graded symmetric
algebra `Sym F` of a quasicoherent sheaf `F`. -/
abbrev FreeGradedQuasicoherentAlgebra : Type _ :=
  (gradedSymmetricAlgebra X).EssImageSubcategory

/-- The graded symmetric algebra functor is an equivalence between quasicoherent sheaves and
graded quasicoherent algebras freely generated in degree one. Its inverse takes the degree-one
component, and its unit is the identification `F ≅ Sym¹ F`. -/
-- Exposed so that `gradedSymmetricAlgebraEquiv_unitIso` can identify the unit with an isomorphism
-- of the functors `gradedSymmetricAlgebra X ⋙ degreeOne` and `𝟭 _`, which are the composite and the
-- identity of the equivalence only by unfolding it.
@[expose]
def gradedSymmetricAlgebraEquiv : QuasicoherentSheaf X ≌ FreeGradedQuasicoherentAlgebra X :=
  (gradedSymmetricAlgebra X).equivEssImageOfCompIso (gradedSymmetricAlgebraDegreeOneIso X)

/-- The forward functor of `gradedSymmetricAlgebraEquiv` is the graded symmetric algebra,
corestricted to its essential image. -/
@[simp]
theorem gradedSymmetricAlgebraEquiv_functor :
    (gradedSymmetricAlgebraEquiv X).functor = (gradedSymmetricAlgebra X).toEssImage :=
  (rfl)

/-- The inverse functor of `gradedSymmetricAlgebraEquiv` is the degree-one functor. -/
@[simp]
theorem gradedSymmetricAlgebraEquiv_inverse :
    (gradedSymmetricAlgebraEquiv X).inverse = (gradedSymmetricAlgebra X).essImage.ι ⋙ degreeOne :=
  (rfl)

/-- The unit of `gradedSymmetricAlgebraEquiv` is the identification `F ≅ Sym¹ F`. -/
@[simp]
theorem gradedSymmetricAlgebraEquiv_unitIso :
    (gradedSymmetricAlgebraEquiv X).unitIso = (gradedSymmetricAlgebraDegreeOneIso X).symm :=
  (rfl)

variable {X}

/-- A graded quasicoherent algebra is freely generated in degree one exactly when it is isomorphic,
as a graded algebra, to the graded symmetric algebra of its degree-one component. -/
theorem essImage_gradedSymmetricAlgebra_iff (A : GradedQuasicoherentAlgebra X) :
    (gradedSymmetricAlgebra X).essImage A ↔
      Nonempty ((gradedSymmetricAlgebra X).obj (degreeOne.obj A) ≅ A) :=
  (gradedSymmetricAlgebra X).essImage_iff_nonempty_iso_of_compIso
    (gradedSymmetricAlgebraDegreeOneIso X) A

end

end AlgebraicGeometry

end TauCeti
