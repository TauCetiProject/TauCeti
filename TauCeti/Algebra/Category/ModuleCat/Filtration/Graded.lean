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
(`CategoryTheory.FilteredObject.ofSubmodules`). Its graded piece `gr^p = F^p / F^{p+1}`
(`CategoryTheory.FilteredObject.gr`, a cokernel) is the quotient module of `F p` by `F (p + 1)`,
seen inside `F p`.

## Main results

* `CategoryTheory.FilteredObject.grIsoOfAntitone`: `gr^p ≅ F p ⧸ F (p + 1)`.
* `CategoryTheory.FilteredObject.card_step_eq_card_mul_card_gr`:
  `|F p| = |F (p + 1)| · |gr^p|`.
-/

public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.FilteredObject

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The linear map underlying the inclusion of steps `F_i ⟶ F_j` of `ofSubmodules F hF` along a
morphism `f : i ⟶ j` is the inclusion of `F i` in `F j`. -/
theorem hom_stepMap_ofSubmodules {I : Type*} [Category* I] (F : I → Submodule R M)
    (hF : ∀ ⦃i j⦄, (i ⟶ j) → F i ≤ F j) {i j : I} (f : i ⟶ j) :
    ((ofSubmodules F hF).stepMap f).hom = Submodule.inclusion (hF f) := by
  rw [← filtrationDiagram_map]
  rfl

variable (F : ℤ → Submodule R M) (hF : Antitone F)

/-- The decreasingly filtered module with steps `F^p = F p`, for an antitone family `F`. -/
noncomputable abbrev ofAntitone : FilteredObject (ModuleCat.{v} R) ℤᵒᵖ :=
  ofSubmodules (fun p : ℤᵒᵖ ↦ F p.unop) fun _ _ f ↦ hF (leOfHom f.unop)

/-- The graded piece `gr^p = F^p / F^{p+1}` of the filtration of a module by an antitone family
`F` of submodules is the quotient of `F p` by `F (p + 1)`, seen inside `F p`. -/
noncomputable def grIsoOfAntitone (p : ℤ) :
    (gr p).obj (ofAntitone F hF) ≅
      ModuleCat.of R (F p ⧸ (F (p + 1)).comap (F p).subtype) :=
  ModuleCat.cokernelIsoRangeQuotient _ ≪≫
    (Submodule.quotEquivOfEq _ _ 
      ((congrArg LinearMap.range (hom_stepMap_ofSubmodules _ _ _)).trans
        (Submodule.range_inclusion _ _ _))).toModuleIso

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
