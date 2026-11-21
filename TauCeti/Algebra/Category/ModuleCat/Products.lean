/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Coordinate equivalences for contravariant functors to `ModuleCat`

A contravariant `ModuleCat R`-valued functor `F : Tᵒᵖ ⥤ ModuleCat R` preserving `J`-indexed
products identifies `F.obj (op c.pt)`, for any colimit cofan `c` over `f : J → T`, with the
concrete product `∀ j, F.obj (op (f j))` (`CategoryTheory.Limits.IsColimit.cofanOpToPiLinearEquiv`).

## Main declarations

* `CategoryTheory.Limits.IsColimit.cofanOpToPiLinearEquiv`: coordinate linear equivalence
  `F.obj (op c.pt) ≃ₗ[R] ∀ j, F.obj (op (f j))`.
* `CategoryTheory.Limits.IsColimit.cofanOpToPiLinearEquiv_apply`,
  `CategoryTheory.Limits.IsColimit.map_inj_cofanOpToPiLinearEquiv_symm`: forward and inverse
  evaluation lemmas.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uR w v u

namespace CategoryTheory.Limits.IsColimit

variable {T : Type u} [Category.{v} T]

/-- A contravariant `ModuleCat R`-valued functor preserving `J`-indexed products identifies its
value on any colimit cofan `c` over `f : J → T` with the concrete product
`∀ j, F.obj (op (f j))`, compatibly with the projections `F.map (c.inj j).op`. -/
def cofanOpToPiLinearEquiv {R : Type uR} [Ring R] {J : Type w} {f : J → T} {c : Cofan f}
    (hc : IsColimit c) (F : Tᵒᵖ ⥤ ModuleCat.{max w v} R)
    [PreservesLimitsOfShape (Discrete J) F] :
    F.obj (Opposite.op c.pt) ≃ₗ[R] ∀ j, F.obj (Opposite.op (f j)) :=
  let hFan : IsLimit (Fan.mk (F.obj (Opposite.op c.pt)) fun j ↦ F.map (c.inj j).op) :=
    (isLimitMapConeFanMkEquiv F (fun j ↦ Opposite.op (f j)) (fun j ↦ (c.inj j).op)).1
      (isLimitOfPreserves F (Cofan.IsColimit.op hc))
  let e : F.obj (Opposite.op c.pt) ≅ ModuleCat.of R (∀ j, F.obj (Opposite.op (f j))) :=
    hFan.conePointUniqueUpToIso (ModuleCat.productConeIsLimit fun j ↦ F.obj (Opposite.op (f j)))
  e.toLinearEquiv

@[simp]
theorem cofanOpToPiLinearEquiv_apply {R : Type uR} [Ring R] {J : Type w} {f : J → T} {c : Cofan f}
    (hc : IsColimit c) (F : Tᵒᵖ ⥤ ModuleCat.{max w v} R)
    [PreservesLimitsOfShape (Discrete J) F] (x : F.obj (Opposite.op c.pt)) (j : J) :
    hc.cofanOpToPiLinearEquiv F x j = F.map (c.inj j).op x :=
  congrArg (fun φ : F.obj (Opposite.op c.pt) ⟶ F.obj (Opposite.op (f j)) ↦ φ x) <|
    ((isLimitMapConeFanMkEquiv F (fun j ↦ Opposite.op (f j)) (fun j ↦ (c.inj j).op)).1
      (isLimitOfPreserves F (Cofan.IsColimit.op hc))).conePointUniqueUpToIso_hom_comp
        (ModuleCat.productConeIsLimit fun j ↦ F.obj (Opposite.op (f j))) ⟨j⟩

@[simp]
theorem map_inj_cofanOpToPiLinearEquiv_symm {R : Type uR} [Ring R] {J : Type w} {f : J → T}
    {c : Cofan f} (hc : IsColimit c) (F : Tᵒᵖ ⥤ ModuleCat.{max w v} R)
    [PreservesLimitsOfShape (Discrete J) F] (x : ∀ j, F.obj (Opposite.op (f j))) (j : J) :
    F.map (c.inj j).op ((hc.cofanOpToPiLinearEquiv F).symm x) = x j := by
  rw [← hc.cofanOpToPiLinearEquiv_apply F, LinearEquiv.apply_symm_apply]

end CategoryTheory.Limits.IsColimit
