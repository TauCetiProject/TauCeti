/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Products and coproducts in `ModuleCat`

The categorical coproduct `∐_ι M` of copies of a module `M` in `ModuleCat R` is the module
`ι →₀ M` of finitely supported families: Mathlib identifies the coproduct with the direct sum
(`ModuleCat.coprodIsoDirectSum`), and the direct sum of copies of `M` with `ι →₀ M`
(`finsuppLEquivDirectSum`). The resulting linear equivalence sends the summand inclusion of index
`i` to `Finsupp.single i`.

A contravariant `ModuleCat R`-valued functor `F : Tᵒᵖ ⥤ ModuleCat R` preserving `J`-indexed
products identifies `F.obj (op c.pt)`, for any colimit cofan `c` over `f : J → T`, with the
concrete product `∀ j, F.obj (op (f j))` (`CategoryTheory.Limits.IsColimit.cofanOpToPiLinearEquiv`).

## Main declarations

* `ModuleCat.coprodLinearEquivFinsupp`: the linear equivalence `∐_ι M ≃ₗ[R] (ι →₀ M)`.
* `ModuleCat.coprodLinearEquivFinsupp_ι_apply`, `ModuleCat.coprodLinearEquivFinsupp_symm_single`: it
  sends the summand inclusion of index `i` to `Finsupp.single i`.
* `CategoryTheory.Limits.IsColimit.cofanOpToPiLinearEquiv`: coordinate linear equivalence
  `F.obj (op c.pt) ≃ₗ[R] ∀ j, F.obj (op (f j))`.
* `CategoryTheory.Limits.IsColimit.cofanOpToPiLinearEquiv_apply`,
  `CategoryTheory.Limits.IsColimit.map_inj_cofanOpToPiLinearEquiv_symm`: forward and inverse
  evaluation lemmas.
-/

public section

noncomputable section

open CategoryTheory Limits

universe uR u v w

namespace ModuleCat

variable {R : Type u} [Ring R] (M : ModuleCat.{max v w} R) (ι : Type v)

/-- The coproduct `∐_ι M` of copies of a module `M` is the module `ι →₀ M` of finitely supported
families, the summand of index `i` going to the families supported at `i`. -/
def coprodLinearEquivFinsupp : (∐ fun _ : ι ↦ M : ModuleCat.{max v w} R) ≃ₗ[R] (ι →₀ M) :=
  open scoped Classical in
  (coprodIsoDirectSum fun _ : ι ↦ M).toLinearEquiv.trans
    (finsuppLEquivDirectSum R M ι).symm

variable {M ι}

/-- `ModuleCat.coprodLinearEquivFinsupp` sends `x` in the summand of index `i` to the family
supported at `i` with value `x`. -/
@[simp]
theorem coprodLinearEquivFinsupp_ι_apply (i : ι) (x : M) :
    coprodLinearEquivFinsupp M ι (Sigma.ι (fun _ : ι ↦ M) i x) = Finsupp.single i x := by
  classical
  rw [coprodLinearEquivFinsupp, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    ι_coprodIsoDirectSum_hom_apply, finsuppLEquivDirectSum_symm_lof]

/-- The inverse of `ModuleCat.coprodLinearEquivFinsupp` sends the family supported at `i` with
value `x` to `x` in the summand of index `i`. -/
@[simp]
theorem coprodLinearEquivFinsupp_symm_single (i : ι) (x : M) :
    (coprodLinearEquivFinsupp M ι).symm (Finsupp.single i x) = Sigma.ι (fun _ : ι ↦ M) i x := by
  rw [LinearEquiv.symm_apply_eq, coprodLinearEquivFinsupp_ι_apply]

end ModuleCat

namespace CategoryTheory.Limits.IsColimit

open Opposite

variable {T : Type u} [Category.{v} T]

/-- A contravariant `ModuleCat R`-valued functor preserving `J`-indexed products identifies its
value on any colimit cofan `c` over `f : J → T` with the concrete product
`∀ j, F.obj (op (f j))`, compatibly with the projections `F.map (c.inj j).op`. -/
def cofanOpToPiLinearEquiv {R : Type uR} [Ring R] {J : Type w} {f : J → T} {c : Cofan f}
    (hc : IsColimit c) (F : Tᵒᵖ ⥤ ModuleCat.{max w v} R)
    [PreservesLimitsOfShape (Discrete J) F] :
    F.obj (Opposite.op c.pt) ≃ₗ[R] ∀ j, F.obj (Opposite.op (f j)) :=
  let hFan : IsLimit (Fan.mk (F.obj (Opposite.op c.pt)) fun j ↦ F.map (c.inj j).op) :=
    (isLimitMapConeFanMkEquiv F (fun j ↦ Opposite.op (f j)) (fun j ↦ (c.inj j).op)).toFun
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
    ((isLimitMapConeFanMkEquiv F (fun j ↦ Opposite.op (f j)) (fun j ↦ (c.inj j).op)).toFun
      (isLimitOfPreserves F (Cofan.IsColimit.op hc))).conePointUniqueUpToIso_hom_comp
        (ModuleCat.productConeIsLimit fun j ↦ F.obj (Opposite.op (f j))) ⟨j⟩

@[simp]
theorem map_inj_cofanOpToPiLinearEquiv_symm {R : Type uR} [Ring R] {J : Type w} {f : J → T}
    {c : Cofan f} (hc : IsColimit c) (F : Tᵒᵖ ⥤ ModuleCat.{max w v} R)
    [PreservesLimitsOfShape (Discrete J) F] (x : ∀ j, F.obj (Opposite.op (f j))) (j : J) :
    F.map (c.inj j).op ((hc.cofanOpToPiLinearEquiv F).symm x) = x j := by
  rw [← hc.cofanOpToPiLinearEquiv_apply F, LinearEquiv.apply_symm_apply]

end CategoryTheory.Limits.IsColimit
