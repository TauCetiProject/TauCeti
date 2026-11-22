/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import TauCeti.Analysis.CStarAlgebra.Hom
public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Topology.ContinuousMap.Star
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Star

/-!
# Evaluation-kernel ideals of continuous-function C⋆-algebras

For a non-unital complex C⋆-algebra `A` and an open embedding `e : X → Y` into an `R₁` space `Y`
whose image omits a single point `y₀`, extension by zero identifies `C₀(X, A)` with the closed
two-sided kernel ideal of point evaluation at `y₀` in `C₀(Y, A)` (and in `C(Y, A)` when `Y` is
compact). Moreover, on any compact space `X`, point evaluation at `x : X` is surjective, so
`C(X, A) ⧸ ker (ev_x)` is `⋆`-isomorphic to `A`.

## Main declarations

* `ContinuousMap.quotientKerEvalEquiv`: `⋆`-isomorphism
  `C(X, A) ⧸ TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A x) ≃⋆ₐ[ℂ] A` for compact `X`.
* `ZeroAtInftyContinuousMap.kerContinuousMapEvalEquiv`: on a compact space `Y`, the
  `⋆`-isomorphism between evaluation kernels in `C(Y, A)` and `C₀(Y, A)` induced by
  `ContinuousMap.liftZeroAtInftyStarAlgEquiv`.
* `ZeroAtInftyContinuousMap.equivKerEvalOfNotMemRangeIff`: `⋆`-algebra equivalence
  `C₀(X, A) ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀)`.
* `ZeroAtInftyContinuousMap.equivKerContinuousMapEvalOfNotMemRangeIff`: compact-codomain variant
  `C₀(X, A) ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)`.
-/

public section

open Set Topology
open scoped CStarAlgebra ZeroAtInfty

namespace ContinuousMap

/-- For a compact space `X` and `x : X`, the `⋆`-isomorphism
`C(X, A) ⧸ TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A x) ≃⋆ₐ[ℂ] A` induced by the
surjective evaluation at `x`. -/
noncomputable def quotientKerEvalEquiv (X A : Type*) [TopologicalSpace X] [CompactSpace X]
    [NonUnitalCStarAlgebra A] (x : X) :
    C(X, A) ⧸ TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A x) ≃⋆ₐ[ℂ] A :=
  NonUnitalStarAlgHom.quotientKerEquivOfSurjective
    (φ := evalNonUnitalStarAlgHom ℂ A x)
    fun a => ⟨const X a, by simp⟩

@[simp]
theorem quotientKerEvalEquiv_mk {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : Type*) [NonUnitalCStarAlgebra A] (x : X) (f : C(X, A)) :
    quotientKerEvalEquiv X A x
        (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A x)) f) =
      f x :=
  (NonUnitalStarAlgHom.quotientKerEquivOfSurjective_mk
    (φ := evalNonUnitalStarAlgHom ℂ A x) _ f).trans
    (evalNonUnitalStarAlgHom_apply ℂ A x f)

end ContinuousMap

namespace ZeroAtInftyContinuousMap

section CompactKerEval

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]

/-- On a compact space `Y`, `ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ Y A` restricts to a
`⋆`-isomorphism between the evaluation kernels at `y₀` in `C(Y, A)` and `C₀(Y, A)`. -/
noncomputable def kerContinuousMapEvalEquiv (A : Type*) [NonUnitalCStarAlgebra A] (y₀ : Y) :
    TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀) ≃⋆ₐ[ℂ]
      TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀) where
  toFun g := ⟨ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ Y A g, by
    rw [TwoSidedIdeal.mem_ker, evalNonUnitalStarAlgHom_apply]
    have hg := (TwoSidedIdeal.mem_ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)).mp g.property
    simpa [ContinuousMap.evalNonUnitalStarAlgHom_apply] using hg⟩
  invFun g := ⟨(ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ Y A).symm g, by
    rw [TwoSidedIdeal.mem_ker, ContinuousMap.evalNonUnitalStarAlgHom_apply]
    have hg := (TwoSidedIdeal.mem_ker (evalNonUnitalStarAlgHom ℂ A y₀)).mp g.property
    simpa [evalNonUnitalStarAlgHom_apply] using hg⟩
  left_inv g := Subtype.ext ((ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ Y A).symm_apply_apply g)
  right_inv g := Subtype.ext ((ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ Y A).apply_symm_apply g)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)
  map_star' _ := Subtype.ext (map_star _ _)

@[simp]
theorem coe_kerContinuousMapEvalEquiv_apply {A : Type*} [NonUnitalCStarAlgebra A] (y₀ : Y)
    (g : TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)) :
    ((kerContinuousMapEvalEquiv A y₀ g :
      TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀)) : C₀(Y, A)) =
      ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ Y A g := (rfl)

@[simp]
theorem coe_kerContinuousMapEvalEquiv_symm_apply {A : Type*} [NonUnitalCStarAlgebra A] (y₀ : Y)
    (g : TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀)) :
    (((kerContinuousMapEvalEquiv A y₀).symm g :
      TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)) : C(Y, A)) =
      (g : C₀(Y, A)).toContinuousMap := by
  change ((ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ Y A).symm (g : C₀(Y, A))) = _
  simp

end CompactKerEval

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
    C₀(X, A) ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀) :=
  (equivKerEvalOfNotMemRangeIff A he hcompl).trans (kerContinuousMapEvalEquiv A y₀).symm

@[simp]
theorem coe_equivKerContinuousMapEvalOfNotMemRangeIff_apply [CompactSpace Y]
    {A : Type*} [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀) (f : C₀(X, A)) :
    ((equivKerContinuousMapEvalOfNotMemRangeIff A he hcompl f :
      TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)) : C(Y, A)) =
      (extendByZero he f : C(Y, A)) := by
  ext y
  simp [equivKerContinuousMapEvalOfNotMemRangeIff]

@[simp]
theorem equivKerContinuousMapEvalOfNotMemRangeIff_symm_apply [CompactSpace Y]
    {A : Type*} [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀)
    (g : TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)) (x : X) :
    (equivKerContinuousMapEvalOfNotMemRangeIff A he hcompl).symm g x = (g : C(Y, A)) (e x) := by
  simp [equivKerContinuousMapEvalOfNotMemRangeIff]

end KerEval

end ZeroAtInftyContinuousMap
