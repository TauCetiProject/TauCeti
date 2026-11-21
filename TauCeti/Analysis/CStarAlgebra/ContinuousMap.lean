/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Topology.ContinuousMap.Star
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Star

/-!
# Evaluation-kernel ideals of continuous-function C⋆-algebras

For a non-unital complex C⋆-algebra `A` and an open embedding `e : X → Y` into an `R₁` space `Y`
whose image omits a single point `y₀`, extension by zero identifies `C₀(X, A)` with the closed
two-sided kernel ideal of point evaluation at `y₀` in `C₀(Y, A)` (and in `C(Y, A)` when `Y` is
compact).

## Main declarations

* `ZeroAtInftyContinuousMap.equivKerEvalOfNotMemRangeIff`: `⋆`-algebra equivalence
  `C₀(X, A) ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀)`.
* `ZeroAtInftyContinuousMap.equivKerContinuousMapEvalOfNotMemRangeIff`: compact-codomain variant
  `C₀(X, A) ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)`.
-/

public section

open Set Topology
open scoped CStarAlgebra ZeroAtInfty

namespace ZeroAtInftyContinuousMap

section KerEval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y]
  {e : X → Y} {y₀ : Y}

/-- When an open embedding `e : X → Y` into an `R₁` space misses only a single point `y₀`,
extension by zero identifies `C₀(X, A)` with `TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀)`.
-/
noncomputable def equivKerEvalOfNotMemRangeIff (A : Type*) [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀) :
    C₀(X, A) ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀) where
  toFun f := ⟨extendByZero he f, by
    rw [TwoSidedIdeal.mem_ker, evalNonUnitalStarAlgHom_apply]
    exact extendByZero_apply_of_notMem he f ((hcompl y₀).mpr rfl)⟩
  invFun g := restrictOfEqZero he.isEmbedding (g : C₀(Y, A)) fun y hy => by
    rw [(hcompl y).mp hy]
    have hg := (TwoSidedIdeal.mem_ker (evalNonUnitalStarAlgHom ℂ A y₀)).mp g.property
    rwa [evalNonUnitalStarAlgHom_apply] at hg
  left_inv f := restrictOfEqZero_extendByZero he f
  right_inv g := Subtype.ext (extendByZero_restrictOfEqZero he (g : C₀(Y, A)) _)
  map_mul' f₁ f₂ := Subtype.ext (extendByZero_mul he f₁ f₂)
  map_add' f₁ f₂ := Subtype.ext (extendByZero_add he f₁ f₂)
  map_smul' c f := Subtype.ext (extendByZero_smul he c f)
  map_star' f := Subtype.ext (extendByZero_star he f)

@[simp]
theorem coe_equivKerEvalOfNotMemRangeIff_apply {A : Type*} [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀) (f : C₀(X, A)) :
    ((equivKerEvalOfNotMemRangeIff A he hcompl f :
      TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀)) : C₀(Y, A)) = extendByZero he f := (rfl)

@[simp]
theorem equivKerEvalOfNotMemRangeIff_symm_apply {A : Type*} [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀)
    (g : TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀)) (x : X) :
    (equivKerEvalOfNotMemRangeIff A he hcompl).symm g x = (g : C₀(Y, A)) (e x) :=
  restrictOfEqZero_apply he.isEmbedding (g : C₀(Y, A)) _ x

/-- Compact-codomain variant of `equivKerEvalOfNotMemRangeIff` landing in the kernel of
`ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀` inside `C(Y, A)`. -/
noncomputable def equivKerContinuousMapEvalOfNotMemRangeIff [CompactSpace Y]
    (A : Type*) [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀) :
    C₀(X, A) ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀) where
  toFun f := ⟨(extendByZero he f : C(Y, A)), by
    rw [TwoSidedIdeal.mem_ker, ContinuousMap.evalNonUnitalStarAlgHom_apply]
    exact extendByZero_apply_of_notMem he f ((hcompl y₀).mpr rfl)⟩
  invFun g := restrictOfEqZero he.isEmbedding
    (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty (g : C(Y, A))) fun y hy => by
      rw [(hcompl y).mp hy]
      simpa using
        (TwoSidedIdeal.mem_ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)).mp g.property
  left_inv f := restrictOfEqZero_extendByZero he f
  right_inv g := Subtype.ext <| ContinuousMap.ext fun y =>
    DFunLike.congr_fun (extendByZero_restrictOfEqZero he
      (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty (g : C(Y, A))) _) y
  map_mul' f g := Subtype.ext <| ContinuousMap.ext fun y =>
    DFunLike.congr_fun (extendByZero_mul he f g) y
  map_add' f g := Subtype.ext <| ContinuousMap.ext fun y =>
    DFunLike.congr_fun (extendByZero_add he f g) y
  map_smul' c f := Subtype.ext <| ContinuousMap.ext fun y =>
    DFunLike.congr_fun (extendByZero_smul he c f) y
  map_star' f := Subtype.ext <| ContinuousMap.ext fun y =>
    DFunLike.congr_fun (extendByZero_star he f) y

@[simp]
theorem coe_equivKerContinuousMapEvalOfNotMemRangeIff_apply [CompactSpace Y]
    {A : Type*} [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀) (f : C₀(X, A)) :
    ((equivKerContinuousMapEvalOfNotMemRangeIff A he hcompl f :
      TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)) : C(Y, A)) =
      (extendByZero he f : C(Y, A)) := (rfl)

@[simp]
theorem equivKerContinuousMapEvalOfNotMemRangeIff_symm_apply [CompactSpace Y]
    {A : Type*} [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀)
    (g : TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)) (x : X) :
    (equivKerContinuousMapEvalOfNotMemRangeIff A he hcompl).symm g x = (g : C(Y, A)) (e x) :=
  restrictOfEqZero_apply he.isEmbedding
    (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty (g : C(Y, A))) _ x

end KerEval

end ZeroAtInftyContinuousMap
