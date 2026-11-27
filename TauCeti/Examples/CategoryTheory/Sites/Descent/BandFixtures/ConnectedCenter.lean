/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.ConnectedCenter

/-!
# Checks for the central sections of connected constant fixtures

* For `G = C₃` and two objects (`I = Bool`), the central sections over any object are the three
  elements of `C₃`, and evaluation at every object is surjective onto its automorphisms.
* For `G = S₃` there is only the identity central section, and evaluation is injective but not
  surjective: the automorphism of a transposition is not the evaluation of any central section.
-/

public section

namespace TauCeti.Examples.ConnectedBandFixtures

open CategoryTheory CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.ConnectedBandFixtures

variable {C : Type*} [Category* C] (U : C)

/-- **The `C₃` Check, sections.** The constant pseudofunctor with fibre
`Codiscrete Bool × B(C₃)` has exactly three central sections over every object. -/
theorem card_sections_C3 :
    Nat.card (IntrinsicBandSections
      (constant C (Codiscrete Bool × SingleObj (Multiplicative (ZMod 3)))) U) = 3 := by
  rw [← Nat.card_congr (connectedSectionsEquiv C false U).toEquiv, CommGroup.center_eq_top,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  rfl

/-- **The `C₃` Check, evaluation.** Evaluation of the central sections of the constant
pseudofunctor with fibre `Codiscrete Bool × B(C₃)` is surjective onto the automorphisms of every
object. -/
theorem eval_surjective_C3 (x : Codiscrete Bool × SingleObj (Multiplicative (ZMod 3))) :
    Function.Surjective (IntrinsicBandSections.evaluation
      (F := constant C (Codiscrete Bool × SingleObj (Multiplicative (ZMod 3)))) (𝟙 U) x) :=
  (connected_eval_surjective_iff false U x).2 CommGroup.center_eq_top

/-- The centre of `S₃` is trivial. -/
theorem center_perm_fin_three : Subgroup.center (Equiv.Perm (Fin 3)) = ⊥ := by
  refine eq_bot_iff.2 fun g hg ↦ Subgroup.mem_bot.2 ?_
  have key : ∀ g : Equiv.Perm (Fin 3), (∀ h : Equiv.Perm (Fin 3), h * g = g * h) → g = 1 := by
    decide
  exact key g (Subgroup.mem_center_iff.1 hg)

/-- **The `S₃` Check, sections.** The constant pseudofunctor with fibre
`Codiscrete Bool × B(S₃)` has only the identity central section over every object. -/
theorem card_sections_S3 :
    Nat.card (IntrinsicBandSections
      (constant C (Codiscrete Bool × SingleObj (Equiv.Perm (Fin 3)))) U) = 1 := by
  rw [← Nat.card_congr (connectedSectionsEquiv C false U).toEquiv, center_perm_fin_three,
    Subgroup.card_bot]

/-- **The `S₃` Check, evaluation.** The automorphism of an object of `Codiscrete Bool × B(S₃)`
given by the transposition `(0 1)` is not the evaluation of any central section, so evaluation is
not surjective (it is injective by `connected_eval_injective`). -/
theorem not_eval_swap_S3 (x : Codiscrete Bool × SingleObj (Equiv.Perm (Fin 3))) :
    ¬ ∃ s, IntrinsicBandSections.evaluation
      (F := constant C (Codiscrete Bool × SingleObj (Equiv.Perm (Fin 3)))) (𝟙 U) x s =
        connectedAut x (Equiv.swap 0 1) := by
  rw [connected_eval_image false U x, connectedAut_asIso_hom_snd, center_perm_fin_three]
  exact fun h ↦ (by decide : Equiv.swap (0 : Fin 3) 1 ≠ 1) (Subgroup.mem_bot.1 h)

end TauCeti.Examples.ConnectedBandFixtures
