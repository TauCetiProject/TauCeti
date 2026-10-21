/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Opposite.Suspension
public import TauCeti.CategoryTheory.Exact.Stable.Shift
public import Mathlib.CategoryTheory.Triangulated.Opposite.Basic

/-!
# Integral shifts in opposite stable categories

The comparison from the stable category of an opposite Frobenius exact category to the
opposite stable category commutes coherently with integral shifts. The target uses Mathlib's
triangulated opposite shift: its shift by `n` is the opposite of the original shift by `-n`.
In particular, suspension in the opposite exact category corresponds to the original loop
functor, rather than the original suspension.

`projectiveStableOpFunctorCommShift` extends the canonical suspension-loop comparison to
all integers. Its degree-one formula retains that comparison explicitly, so it can be used
to compute the third arrow of the image of a stable conflation triangle. The forward and
inverse functors of the opposite stable equivalence also receive compatible shift structures;
their unit and counit commute with shifts. Preservation of distinguished triangles is a
separate assertion.

Install the original stable shift with `letI := hE.stableHasShift`, the source shift with
`letI := hE.op.stableHasShift`, and open `CategoryTheory.Pretriangulated.Opposite` to obtain
the target shift. Then install `letI := hE.projectiveStableOpEquivalenceFunctorCommShift`
for the forward equivalence. For the inverse, install
`letI := (E.projectiveStableOpEquivalence hE.projective_iff_injective).commShiftInverse ℤ`.
The same equivalence's `commShift_of_functor ℤ` supplies unit and counit compatibility.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* `ExactStructure.IsFrobenius.stableSuspensionCompProjectiveStableOpFunctorIso`: the canonical
  suspension-loop comparison.
* `CategoryTheory.Pretriangulated.shiftFunctorOpIso`: Mathlib's opposite shift convention.
-/

public section

namespace TauCeti.ExactStructure.IsFrobenius

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} (hE : E.IsFrobenius)

/-- The opposite stable comparison commutes with all integral shifts, for the triangulated
opposite shift on its target. The comparison in degree one is induced by the canonical
identification of opposite suspension with the original loop functor. -/
@[instance_reducible]
noncomputable def projectiveStableOpFunctorCommShift :
    letI := hE.stableHasShift
    letI := hE.op.stableHasShift
    (E.projectiveStableOpFunctor hE.projective_iff_injective).CommShift ℤ := by
  letI := hE.stableHasShift
  exact hE.op.commShiftOfIntertwiningStableSuspensionShift
    (E.projectiveStableOpFunctor hE.projective_iff_injective)
    (hE.stableSuspensionCompProjectiveStableOpFunctorIso ≪≫
      Functor.isoWhiskerLeft (E.projectiveStableOpFunctor hE.projective_iff_injective)
        (NatIso.op hE.stableShiftFunctorNegOneIso ≪≫
          (shiftFunctorOpIso E.ProjectiveStableCategory 1 (-1) (by simp)).symm))

/-- In degree one the integral comparison is the suspension-loop comparison, followed by
the identification of the original loop with shift by `-1` and the opposite shift bridge. -/
theorem projectiveStableOpFunctorCommShift_iso_one :
    letI := hE.stableHasShift
    letI := hE.op.stableHasShift
    letI := hE.projectiveStableOpFunctorCommShift
    (E.projectiveStableOpFunctor hE.projective_iff_injective).commShiftIso (1 : ℤ) =
      Functor.isoWhiskerRight hE.op.stableShiftFunctorOneIso
        (E.projectiveStableOpFunctor hE.projective_iff_injective) ≪≫
      hE.stableSuspensionCompProjectiveStableOpFunctorIso ≪≫
      Functor.isoWhiskerLeft (E.projectiveStableOpFunctor hE.projective_iff_injective)
        (NatIso.op hE.stableShiftFunctorNegOneIso ≪≫
          (shiftFunctorOpIso E.ProjectiveStableCategory 1 (-1) (by simp)).symm) := by
  let := hE.stableHasShift
  exact hE.op.commShiftOfIntertwiningStableSuspensionShift_iso_one _ _

/-- The forward functor of the opposite stable equivalence uses the shift comparison of
the opposite stable quotient functor, transported along their identifying equality. -/
@[instance_reducible]
noncomputable def projectiveStableOpEquivalenceFunctorCommShift :
    letI := hE.stableHasShift
    letI := hE.op.stableHasShift
    (E.projectiveStableOpEquivalence hE.projective_iff_injective).functor.CommShift ℤ := by
  letI := hE.stableHasShift
  letI := hE.op.stableHasShift
  letI := hE.projectiveStableOpFunctorCommShift
  exact Functor.CommShift.ofIso
    (eqToIso (E.projectiveStableOpEquivalence_functor hE.projective_iff_injective)).symm ℤ

/-- The shift comparison of the forward equivalence agrees with the quotient comparison
after the canonical identification of functors. -/
@[simp]
theorem projectiveStableOpEquivalenceFunctor_commShiftIso (n : ℤ) :
    letI := hE.stableHasShift
    letI := hE.op.stableHasShift
    letI := hE.projectiveStableOpFunctorCommShift
    letI := hE.projectiveStableOpEquivalenceFunctorCommShift
    (E.projectiveStableOpEquivalence hE.projective_iff_injective).functor.commShiftIso n =
      Functor.isoWhiskerLeft (shiftFunctor E.op.ProjectiveStableCategory n)
        (eqToIso (E.projectiveStableOpEquivalence_functor hE.projective_iff_injective)) ≪≫
      (E.projectiveStableOpFunctor hE.projective_iff_injective).commShiftIso n ≪≫
      Functor.isoWhiskerRight
        (eqToIso (E.projectiveStableOpEquivalence_functor hE.projective_iff_injective)).symm
        (shiftFunctor E.ProjectiveStableCategoryᵒᵖ n) := (rfl)

/-- The identification of the opposite stable equivalence's forward functor with the opposite
stable comparison functor respects integral shifts. -/
theorem projectiveStableOpEquivalence_functor_commShift :
    letI := hE.stableHasShift
    letI := hE.op.stableHasShift
    letI := hE.projectiveStableOpFunctorCommShift
    letI := hE.projectiveStableOpEquivalenceFunctorCommShift
    (eqToIso
      (E.projectiveStableOpEquivalence_functor hE.projective_iff_injective)).hom.CommShift ℤ := by
  let := hE.stableHasShift
  let := hE.op.stableHasShift
  let := hE.projectiveStableOpFunctorCommShift
  let := hE.projectiveStableOpEquivalenceFunctorCommShift
  have : (eqToIso
      (E.projectiveStableOpEquivalence_functor hE.projective_iff_injective)).symm.hom.CommShift ℤ :=
    Functor.CommShift.ofIso_compatibility
      (eqToIso (E.projectiveStableOpEquivalence_functor hE.projective_iff_injective)).symm ℤ
  exact NatTrans.CommShift.of_iso_inv
    (eqToIso (E.projectiveStableOpEquivalence_functor hE.projective_iff_injective)).symm ℤ

end TauCeti.ExactStructure.IsFrobenius
