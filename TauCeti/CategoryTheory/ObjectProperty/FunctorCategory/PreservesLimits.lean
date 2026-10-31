/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits

/-!
# Limits of functors preserving limits

Limits commute with limits. Hence, in the functor category `J ⥤ C`, a limit of functors which
preserve limits of shape `K` again preserves limits of shape `K`, and a limit of functors which
preserve finite limits again preserves finite limits. No exactness assumption on `C` is needed,
unlike for colimits of such functors, which Mathlib treats in
`Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits`; the proof follows the
dual argument there.

For instance, when `C` is monoidal, a binary product of objects `X` for which `tensorLeft X`
preserves finite limits (flat objects) is again flat as soon as `X ↦ tensorLeft X` preserves
binary products.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {J C : Type*} (K K' : Type*) [Category* K] [Category* K'] [Category* J] [Category* C]

/-- A limit of functors preserving limits of shape `K` preserves limits of shape `K`. -/
instance isClosedUnderLimitsOfShape_preservesLimitsOfShape [HasLimitsOfShape K' C] :
    (preservesLimitsOfShape K : ObjectProperty (J ⥤ C)).IsClosedUnderLimitsOfShape K' where
  limitsOfShape_le := by
    rintro G ⟨p⟩
    have := p.prop_diag_obj
    have : PreservesLimitsOfShape K p.diag.flip := ⟨fun {F} ↦ ⟨fun {c} hc ↦
      ⟨evaluationJointlyReflectsLimits _
        (fun k' ↦ isLimitOfPreserves (p.diag.obj k') hc)⟩⟩⟩
    have : PreservesLimitsOfShape K (lim (J := K') (C := C)) :=
      constLimAdj.rightAdjoint_preservesLimits.preservesLimitsOfShape
    -- `G` is computed pointwise as the limit of the functors `p.diag.obj k'`
    let e : G ≅ p.diag.flip ⋙ lim :=
      NatIso.ofComponents
        (fun j ↦ (isLimitOfPreserves ((evaluation _ _).obj j) p.isLimit).conePointUniqueUpToIso
          (limit.isLimit (p.diag.flip.obj j))) (fun {j₁ j₂} f ↦ by
            dsimp
            ext
            simp [IsLimit.conePointUniqueUpToIso])
    exact preservesLimitsOfShape_of_natIso e.symm

/-- A limit of functors preserving finite limits preserves finite limits. -/
instance isClosedUnderLimitsOfShape_preservesFiniteLimits [HasLimitsOfShape K' C] :
    (preservesFiniteLimits : ObjectProperty (J ⥤ C)).IsClosedUnderLimitsOfShape K' where
  limitsOfShape_le := by
    rintro G ⟨p⟩
    have := p.prop_diag_obj
    exact ⟨fun K _ _ ↦ (preservesLimitsOfShape K).prop_of_isLimit p.isLimit inferInstance⟩

end CategoryTheory.ObjectProperty
