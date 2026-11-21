/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.Grp.ZModuleEquivalence
public import TauCeti.Algebra.Category.ModuleCat.Products

import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Coordinate equivalences for contravariant functors to `AddCommGrpCat`

A contravariant `AddCommGrpCat`-valued functor `E : Tᵒᵖ ⥤ AddCommGrpCat` preserving `J`-indexed
products identifies `E.obj (op c.pt)`, for any colimit cofan `c` over `f : J → T`, with the
concrete product `∀ j, E.obj (op (f j))` (`CategoryTheory.Limits.IsColimit.cofanOpToPiAddEquiv`),
obtained via the equivalence `AddCommGrpCat.toIntModule` and
`CategoryTheory.Limits.IsColimit.cofanOpToPiLinearEquiv`.

## Main declarations

* `CategoryTheory.Limits.IsColimit.cofanOpToPiAddEquiv`: coordinate additive equivalence
  `E.obj (op c.pt) ≃+ ∀ j, E.obj (op (f j))`.
* `CategoryTheory.Limits.IsColimit.cofanOpToPiAddEquiv_apply`,
  `CategoryTheory.Limits.IsColimit.map_inj_cofanOpToPiAddEquiv_symm`: forward and inverse
  evaluation lemmas.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Limits.IsColimit

variable {T : Type u} [Category.{v} T]

/-- A contravariant `AddCommGrpCat`-valued functor preserving `J`-indexed products identifies its
value on any colimit cofan `c` over `f : J → T` with the concrete product
`∀ j, E.obj (op (f j))`, compatibly with the projections `E.map (c.inj j).op`. -/
def cofanOpToPiAddEquiv {J : Type w} {f : J → T} {c : Cofan f} (hc : IsColimit c)
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{max w v}) [PreservesLimitsOfShape (Discrete J) E] :
    E.obj (Opposite.op c.pt) ≃+ ∀ j, E.obj (Opposite.op (f j)) :=
  have := comp_preservesLimitsOfShape (J := Discrete J) E AddCommGrpCat.toIntModule
  (hc.cofanOpToPiLinearEquiv (E ⋙ AddCommGrpCat.toIntModule)).toAddEquiv

@[simp]
theorem cofanOpToPiAddEquiv_apply {J : Type w} {f : J → T} {c : Cofan f} (hc : IsColimit c)
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{max w v}) [PreservesLimitsOfShape (Discrete J) E]
    (x : E.obj (Opposite.op c.pt)) (j : J) :
    hc.cofanOpToPiAddEquiv E x j = E.map (c.inj j).op x :=
  have := comp_preservesLimitsOfShape (J := Discrete J) E AddCommGrpCat.toIntModule
  hc.cofanOpToPiLinearEquiv_apply (E ⋙ AddCommGrpCat.toIntModule) x j

@[simp]
theorem map_inj_cofanOpToPiAddEquiv_symm {J : Type w} {f : J → T} {c : Cofan f} (hc : IsColimit c)
    (E : Tᵒᵖ ⥤ AddCommGrpCat.{max w v}) [PreservesLimitsOfShape (Discrete J) E]
    (x : ∀ j, E.obj (Opposite.op (f j))) (j : J) :
    E.map (c.inj j).op ((hc.cofanOpToPiAddEquiv E).symm x) = x j := by
  rw [← hc.cofanOpToPiAddEquiv_apply E, AddEquiv.apply_symm_apply]

end CategoryTheory.Limits.IsColimit
