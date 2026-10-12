/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Torsor
public import TauCeti.CategoryTheory.Monoidal.Grp.Cokernel
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Sites.CartesianClosed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# The cokernel property of fppf quotient projections

The projection from an affine group to its fppf quotient by a closed normal subgroup is the
categorical cokernel of the subgroup inclusion. Thus every group-sheaf morphism annihilating the
subgroup descends uniquely to the quotient, even when the quotient is not representable.

This is a universal property in group objects in fppf sheaves, with arbitrary group-sheaf targets.
It does not require the source to be of finite type or smooth.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
* J. S. Milne, *Algebraic Groups* (2017), §5.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- The subgroup inclusion and quotient projection form a cokernel cofork. -/
noncomputable abbrev fppfQuotientCokernelCofork (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) :
    CokernelCofork (quotientSubgroupPointsFppfGrpInclusion H I) := by
  refine CokernelCofork.ofπ (fppfQuotientProjection H I hI) ?_
  apply Grp.hom_ext
  have hw := (isPullback_fppfQuotientTorsor H I hI).w
  have he := congrArg
    (fun f ↦ lift (1 : (pointsFppfGroupObject (quotient H I)).X ⟶
      (pointsFppfGroupObject H).X) (𝟙 _) ≫ f) hw
  -- Expose the translation action so that precomposition evaluates it at `(1,n)`.
  simp only [fppfQuotientTorsorAction_def] at he
  simp [← Category.assoc, MonObj.comp_mul] at he
  simpa [← Hom.one_def] using he.symm

/-- The projection of the cokernel cofork is the canonical fppf quotient projection. -/
@[simp]
theorem fppfQuotientCokernelCofork_π (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) :
    (fppfQuotientCokernelCofork H I hI).π = fppfQuotientProjection H I hI := by
  rfl

/-- The fppf quotient projection is the categorical cokernel of the closed normal subgroup
inclusion. In particular, homomorphisms annihilating that subgroup descend uniquely. -/
noncomputable def isColimitFppfQuotientCokernel
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    IsColimit (fppfQuotientCokernelCofork H I hI) := by
  letI : MonoidalClosed (((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) :=
    FunctorToTypes.monoidalClosed.{0, u, u + 1}
  let q := (fppfQuotientProjection H I hI).hom.hom
  letI : Sheaf.IsLocallySurjective q := isLocallySurjective_fppfQuotientProjection H I hI
  letI : Epi q := inferInstance
  letI : IsRegularEpi q := IsRegularEpiCategory.regularEpiOfEpi q
  letI : Epi (q ⊗ₘ q) := by
    rw [tensorHom_def]
    have : Epi (q ▷ (pointsFppfGroupObject H).X) := (tensorRight _).map_epi q
    have : Epi ((fppfQuotientSheaf H I hI).X ◁ q) := (tensorLeft _).map_epi q
    infer_instance
  apply Grp.isColimitCokernelCoforkOfTorsor
    (quotientSubgroupPointsFppfGrpInclusion H I) (fppfQuotientProjection H I hI)
  simpa only [fppfQuotientTorsorAction_def] using isPullback_fppfQuotientTorsor H I hI

end TauCeti.CommHopfAlgCat
