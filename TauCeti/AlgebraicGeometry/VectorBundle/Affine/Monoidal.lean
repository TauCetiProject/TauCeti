/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Monoidal

/-!
# Tensor compatibility of the affine vector-bundle equivalence

The equivalence between finite projective `R`-modules and finite locally free sheaves on
`Spec R` is monoidal. Its tensor and unit comparisons are the restrictions of the comparisons
of `AlgebraicGeometry.tilde.functor`, and the inverse functor of global sections carries the
compatible monoidal structure. The existing unit and counit are monoidal transformations.

We use `TauCeti.AlgebraicGeometry.tildeMonoidal` and Mathlib's
`CategoryTheory.Equivalence.inverseMonoidal`, so the tensor operations on both full
subcategories remain those of modules and sheaves, respectively.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 (b).
-/

public section

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable (R : CommRingCat.{u})

/-- The affine equivalence preserves tensor products and the tensor unit, using the canonical
comparisons of the associated-sheaf functor. -/
instance finiteProjectiveEquivFunctorMonoidal : (finiteProjectiveEquiv R).functor.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := ObjectProperty.isoMk _ (Functor.Monoidal.εIso (tilde.functor R))
      μIso M N := ObjectProperty.isoMk _ (Functor.Monoidal.μIso (tilde.functor R) M.obj N.obj)
      μIso_hom_natural_left f N := by
        apply ObjectProperty.hom_ext
        exact μ_natural_left (tilde.functor R) f.hom N.obj
      μIso_hom_natural_right M f := by
        apply ObjectProperty.hom_ext
        exact μ_natural_right (tilde.functor R) M.obj f.hom
      associativity M N P := by
        apply ObjectProperty.hom_ext
        exact Functor.LaxMonoidal.associativity (tilde.functor R) M.obj N.obj P.obj
      left_unitality M := by
        apply ObjectProperty.hom_ext
        exact Functor.LaxMonoidal.left_unitality (tilde.functor R) M.obj
      right_unitality M := by
        apply ObjectProperty.hom_ext
        exact Functor.LaxMonoidal.right_unitality (tilde.functor R) M.obj }

/-- The underlying unit comparison is that of the associated-sheaf functor. -/
@[simp]
theorem finiteProjectiveEquiv_functor_ε_hom :
    (ε (finiteProjectiveEquiv R).functor).hom = ε (tilde.functor R) :=
  (rfl)

/-- The underlying tensor comparison is that of the associated-sheaf functor. -/
@[simp]
theorem finiteProjectiveEquiv_functor_μ_hom
    (M N : (finiteProjectiveModules R).FullSubcategory) :
    (μ (finiteProjectiveEquiv R).functor M N).hom = μ (tilde.functor R) M.obj N.obj :=
  (rfl)

/-- The underlying oplax unit comparison is that of the associated-sheaf functor. -/
@[simp]
theorem finiteProjectiveEquiv_functor_η_hom :
    (η (finiteProjectiveEquiv R).functor).hom = η (tilde.functor R) :=
  (rfl)

/-- The underlying oplax tensor comparison is that of the associated-sheaf functor. -/
@[simp]
theorem finiteProjectiveEquiv_functor_δ_hom
    (M N : (finiteProjectiveModules R).FullSubcategory) :
    (δ (finiteProjectiveEquiv R).functor M N).hom = δ (tilde.functor R) M.obj N.obj :=
  (rfl)

/-- Global sections on finite locally free sheaves carries the monoidal structure inverse to
that of the associated-sheaf functor. -/
instance finiteProjectiveEquivInverseMonoidal : (finiteProjectiveEquiv R).inverse.Monoidal :=
  (finiteProjectiveEquiv R).inverseMonoidal

/-- The affine equivalence, with its canonical unit and counit, is monoidal. -/
instance finiteProjectiveEquiv_isMonoidal : (finiteProjectiveEquiv R).IsMonoidal := by
  infer_instance

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
