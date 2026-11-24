/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.Translate
public import TauCeti.RepresentationTheory.Quiver.Kronecker.Injective
import TauCeti.RepresentationTheory.Quiver.Kronecker.AlmostSplit
import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Auslander–Reiten translation for the one-arrow quiver

For the quiver `1 → 2`, the translate defined by a minimal projective presentation and Matlis
duality sends the source simple `S₁` to the target simple `S₂`. This identifies the `D Tr`
construction with the left endpoint of the almost-split sequence `0 → S₂ → P₁ → S₁ → 0`.

The vertex injectives are identified as `I₁ ≅ S₁` and `I₂ ≅ P₁`. Thus among the three
indecomposables only `S₂` is non-injective, which determines the nonzero translate of `S₁`.
All statements hold over an arbitrary field.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras* (1995), IV.1.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

open Quiver.Kronecker

universe u

variable (k : Type u) [Field k] (A : Type) [Unique A]

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

/-- The `D Tr` Auslander–Reiten translate of the source simple of `1 → 2` is the target simple.
In particular it is the left endpoint of `kroneckerARSequence`. -/
theorem nonempty_iso_arTranslate_simpleRep_src_kronecker
    (hS : IsFinDim k (Quiver.Kronecker A) (simpleRep k (Quiver.Kronecker A) src)) :
    Nonempty (arTranslate k (Quiver.Kronecker A) (simpleRep k (Quiver.Kronecker A) src) hS ≅
      simpleRep k (Quiver.Kronecker A) tgt) := by
  let Q := Quiver.Kronecker A
  let S := simpleRep k Q src
  have hpS : ¬ Projective S := (isAlmostSplit_kroneckerARSequence k A).not_projective_X₃
  -- The translate of the non-projective simple `S₁` is indecomposable and non-injective.
  have hiT := (indecomposable_arTranslate_iff k Q S hS (indecomposable_of_simple S)).mpr hpS
  have hnT : ¬ Injective (arTranslate k Q S hS) := fun h ↦
    hpS ((injective_arTranslate_iff k Q S hS).mp h)
  -- Among the three indecomposables only `S₂` is non-injective.
  rcases nonempty_iso_simpleRep_src_or_simpleRep_tgt_or_indecProjRep_of_indecomposable_kronecker
    _ hiT with h | h | h
  · obtain ⟨e⟩ := h
    obtain ⟨f⟩ := nonempty_iso_indecInjRep_src_simpleRep_kronecker k A
    exact False.elim (hnT (Injective.of_iso (f ≪≫ e.symm) inferInstance))
  · exact h
  · obtain ⟨e⟩ := h
    obtain ⟨f⟩ := nonempty_iso_indecInjRep_tgt_indecProjRep_kronecker k A
    exact False.elim (hnT (Injective.of_iso (f ≪≫ e.symm) inferInstance))

end TauCeti
