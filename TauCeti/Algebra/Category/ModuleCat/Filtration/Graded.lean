/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Card
public import TauCeti.Algebra.Category.ModuleCat.Filtration
public import TauCeti.CategoryTheory.Filtration.Decreasing

/-!
# Graded pieces of decreasing filtrations of modules

An antitone family `F : ℤ → Submodule R M`, read at `ℤᵒᵖ`, is a decreasingly filtered module
(`CategoryTheory.FilteredObject.ofAntitone`). Its graded piece `gr^p = F^p / F^{p+1}`
(`CategoryTheory.FilteredObject.gr`, a cokernel) is the quotient module of `F p` by `F (p + 1)`,
seen inside `F p`.

## Main results

* `CategoryTheory.FilteredObject.grIsoOfAntitone`: `gr^p ≅ F p ⧸ F (p + 1)`, carrying the
  projection `F^p ⟶ gr^p` to the quotient map (`cokernel_π_grIsoOfAntitone_hom`).
* `CategoryTheory.FilteredObject.card_step_eq_card_mul_card_gr`:
  `|F p| = |F (p + 1)| · |gr^p|`.
-/

public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.FilteredObject

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  (F : ℤ → Submodule R M) (hF : Antitone F)

/-- The graded piece `gr^p = F^p / F^{p+1}` of the filtration of a module by an antitone family
`F` of submodules is the quotient of `F p` by `F (p + 1)`, seen inside `F p`. -/
noncomputable def grIsoOfAntitone (p : ℤ) :
    (gr p).obj (ofAntitone F hF) ≅
      ModuleCat.of R (F p ⧸ (F (p + 1)).comap (F p).subtype) :=
  ModuleCat.cokernelIsoRangeQuotient _ ≪≫
    (Submodule.quotEquivOfEq _ _ 
      ((congrArg LinearMap.range (hom_stepMap_ofSubmodules _ _ _)).trans
        (Submodule.range_inclusion _ _ _))).toModuleIso

/-- The projection `F^p ⟶ gr^p` onto the graded piece, followed by `grIsoOfAntitone`, is the
quotient map of `F p` by `F (p + 1)`, seen inside `F p`. -/
@[reassoc (attr := simp)]
theorem cokernel_π_grIsoOfAntitone_hom (p : ℤ) :
    cokernel.π ((ofAntitone F hF).stepMap (homOfLE (Int.le_add_one le_rfl)).op) ≫
        (grIsoOfAntitone F hF p).hom =
      ModuleCat.ofHom ((F (p + 1)).comap (F p).subtype).mkQ := by
  -- Mathlib identifies the cokernel projection with the quotient map by the range of
  -- `F^{p+1} ⟶ F^p`, which `Submodule.quotEquivOfEq` then carries to the quotient by `F (p + 1)`.
  refine (Category.assoc _ _ _).symm.trans
    ((ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom _ =≫ _).trans ?_)
  ext x
  -- On an element `x`, both sides are the class of `x`: the left side unfolds to
  -- `Submodule.quotEquivOfEq _ _ _ (Submodule.Quotient.mk x)`, the class of `x` by Mathlib's
  -- `Submodule.quotEquivOfEq_mk`, itself proved by `rfl`. Rewriting with it does not apply, as the
  -- source of the left side is the step of `ofAntitone F hF`, which is `F p` only up to unfolding.
  rfl

/-- In the filtration of a module by an antitone family `F` of submodules, the cardinality of a
step is the product of the cardinalities of the next step and of the graded piece:
`|F p| = |F (p + 1)| · |gr^p|`. -/
theorem card_step_eq_card_mul_card_gr (p : ℤ) :
    Nat.card (F p) =
      Nat.card (F (p + 1)) * Nat.card ((gr (C := ModuleCat.{v} R) p).obj (ofAntitone F hF)) := by
  rw [Submodule.card_eq_card_quotient_mul_card ((F (p + 1)).comap (F p).subtype),
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe (hF (Int.le_add_one le_rfl))).toEquiv,
    Nat.card_congr (grIsoOfAntitone F hF p).toLinearEquiv.toEquiv]

end CategoryTheory.FilteredObject
