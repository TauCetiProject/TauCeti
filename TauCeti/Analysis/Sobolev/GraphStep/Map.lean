/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Sobolev.GraphStep.Basic
public import TauCeti.MeasureTheory.Function.Lp.ProdLp
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Maps and products of weak-derivative graph spaces

A weak-derivative graph space `TauCeti.WeakDerivStep mu Omega p base` consists of the pairs
`(x, Du)` of a point `x` of a space `X` and a weak derivative `Du` of the field
`base x : Lᵖ(Ω, F)`. A
continuous linear map `M : F →L[ℝ] F'` commutes with weak derivatives
(`TauCeti.HasWeakFDerivOn.compLp`): if `Du` is a weak derivative of `u`, then `M ∘ Du` is one of
`M ∘ u`. So a continuous linear map `L : X →L[ℝ] X'` that matches `M` on fields, in the sense that
`base' ∘ L = M ∘ base`, induces the continuous linear map

`(x, Du) ↦ (L x, M ∘ Du)` (`TauCeti.WeakDerivStep.mapL`)

between the graph spaces of `base` and `base'`.

The main application is to direct sums. For continuous linear maps `ι₁ : D₁ →L[ℝ] F₁` and
`ι₂ : D₂ →L[ℝ] F₂`, the graph space over `ι₁ ⊕ ι₂ : WithLp q (D₁ × D₂) →L[ℝ] WithLp q (F₁ × F₂)`
(`ContinuousLinearMap.withLpProdMap`) is the product of the graph spaces over `ι₁` and `ι₂`
(`TauCeti.WeakDerivStep.withLpProdEquiv`): a path in `Lᵖ(Ω, D₁ ⊕ D₂)` whose image under `ι₁ ⊕ ι₂`
is weakly differentiable is a pair of paths with the same property, componentwise. For a
compactly embedded common domain `D` of Hilbert spaces `H`, the graph space over `ι.compLpL` is
`Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)`, so this splits the domain of a trajectory operator `∂ₛ + A(s)` along a
direct sum of the spaces.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal

section CompLp

variable {E F F' : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F']
  [NormedSpace ℝ F'] [CompleteSpace F'] {mu : Measure E} {Omega : Opens E} {p : ℝ≥0∞}

/-- **Weak derivatives commute with continuous linear maps, for `Lᵖ` classes.** If `D` is a weak
derivative of `f` on `Ω`, then `M ∘ D` is a weak derivative of `M ∘ f`. -/
theorem HasWeakFDerivOn.compLp {f : Lp F p (mu.restrict Omega)}
    {D : Lp (E →L[ℝ] F) p (mu.restrict Omega)} (h : HasWeakFDerivOn mu Omega f D)
    (M : F →L[ℝ] F') :
    HasWeakFDerivOn mu Omega (M.compLp f) ((ContinuousLinearMap.compL ℝ E F F' M).compLp D) :=
  ((h.clm_comp M).congr_ae (M.coeFn_compLp' f).symm).congr_ae_deriv
    ((ContinuousLinearMap.compL ℝ E F F' M).coeFn_compLp' D).symm

end CompLp

namespace WeakDerivStep

variable {E F F' X X' : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
  {mu : Measure E} [IsFiniteMeasureOnCompacts mu] {Omega : Opens E}
  [IsLocallyFiniteMeasure (mu.restrict Omega)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

section Map

variable [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [AddCommGroup X'] [Module ℝ X'] [TopologicalSpace X']

/-- **The map of graph spaces induced by compatible maps.** If `L : X →L[ℝ] X'` and
`M : F →L[ℝ] F'` satisfy `base' ∘ L = M ∘ base`, the map `(x, Du) ↦ (L x, M ∘ Du)` sends the graph
space of `base` to that of `base'`: `M ∘ Du` is a weak derivative of `M ∘ base x = base' (L x)`. -/
def mapL (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (base' : X' →L[ℝ] Lp F' p (mu.restrict Omega))
    (L : X →L[ℝ] X') (M : F →L[ℝ] F')
    (h : base'.comp L = (M.compLpL p (mu.restrict Omega)).comp base) :
    WeakDerivStep mu Omega p base →L[ℝ] WeakDerivStep mu Omega p base' :=
  ContinuousLinearMap.codRestrict
    ((L.withLpProdMap 2
        ((ContinuousLinearMap.compL ℝ E F F' M).compLpL p (mu.restrict Omega))).comp
      (weakDerivStepSubmodule mu Omega p base).toSubmodule.subtypeL)
    _ fun u ↦ (mem_weakDerivStepSubmodule_iff_hasWeakFDerivOn _ _).mpr <| by
      have hu := hasWeakFDerivOn_base_prev base u
      rw [prev_coe, weakFDeriv_coe] at hu
      have hL : base' (L (WithLp.fst u.val)) = M.compLp (base (WithLp.fst u.val)) := by
        simpa using DFunLike.congr_fun h (WithLp.fst u.val)
      simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        ContinuousLinearMap.withLpProdMap_apply, WithLp.toLp_fst, WithLp.toLp_snd, hL,
        ContinuousLinearMap.compLpL_apply]
      exact hu.compLp M

variable (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (base' : X' →L[ℝ] Lp F' p (mu.restrict Omega))
  (L : X →L[ℝ] X') (M : F →L[ℝ] F')
  (h : base'.comp L = (M.compLpL p (mu.restrict Omega)).comp base)

/-- The point of `mapL base base' L M h u` is the image under `L` of the point of `u`. -/
@[simp]
theorem prev_mapL (u : WeakDerivStep mu Omega p base) :
    prev base' (mapL base base' L M h u) = L (prev base u) := by
  simp [prev_coe, mapL]

/-- The weak derivative of `mapL base base' L M h u` is that of `u` followed by `M`. -/
@[simp]
theorem weakFDeriv_mapL (u : WeakDerivStep mu Omega p base) :
    weakFDeriv base' (mapL base base' L M h u) =
      (ContinuousLinearMap.compL ℝ E F F' M).compLpL p (mu.restrict Omega) (weakFDeriv base u) := by
  simp [weakFDeriv_coe, mapL]

end Map

section Compat

variable {α D₁ D₂ F₁ F₂ : Type*} {m : MeasurableSpace α} {μ : Measure α} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [NormedAddCommGroup D₁] [NormedSpace ℝ D₁]
  [NormedAddCommGroup D₂] [NormedSpace ℝ D₂] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] (ι₁ : D₁ →L[ℝ] F₁) (ι₂ : D₂ →L[ℝ] F₂)

/-! The compatibilities of `ι₁ ⊕ ι₂` with the projections onto and inclusions of the factors, in
the form required by `TauCeti.WeakDerivStep.mapL`. -/

private theorem withLpProd_fst_compat :
    (ι₁.compLpL p μ).comp ((WithLp.fstL q ℝ D₁ D₂).compLpL p μ) =
      ((WithLp.fstL q ℝ F₁ F₂).compLpL p μ).comp ((ι₁.withLpProdMap q ι₂).compLpL p μ) := by
  rw [ContinuousLinearMap.compLpL_comp_compLpL, ContinuousLinearMap.compLpL_comp_compLpL]
  congr 1
  ext x
  simp

private theorem withLpProd_snd_compat :
    (ι₂.compLpL p μ).comp ((WithLp.sndL q ℝ D₁ D₂).compLpL p μ) =
      ((WithLp.sndL q ℝ F₁ F₂).compLpL p μ).comp ((ι₁.withLpProdMap q ι₂).compLpL p μ) := by
  rw [ContinuousLinearMap.compLpL_comp_compLpL, ContinuousLinearMap.compLpL_comp_compLpL]
  congr 1
  ext x
  simp

private theorem withLpProd_inl_compat :
    ((ι₁.withLpProdMap q ι₂).compLpL p μ).comp
        ((((WithLp.prodContinuousLinearEquiv q ℝ D₁ D₂).symm :
            D₁ × D₂ →L[ℝ] WithLp q (D₁ × D₂)).comp
              (ContinuousLinearMap.inl ℝ D₁ D₂)).compLpL p μ) =
      ((((WithLp.prodContinuousLinearEquiv q ℝ F₁ F₂).symm :
          F₁ × F₂ →L[ℝ] WithLp q (F₁ × F₂)).comp
            (ContinuousLinearMap.inl ℝ F₁ F₂)).compLpL p μ).comp
        (ι₁.compLpL p μ) := by
  rw [ContinuousLinearMap.compLpL_comp_compLpL, ContinuousLinearMap.compLpL_comp_compLpL]
  congr 1
  ext x
  simp

private theorem withLpProd_inr_compat :
    ((ι₁.withLpProdMap q ι₂).compLpL p μ).comp
        ((((WithLp.prodContinuousLinearEquiv q ℝ D₁ D₂).symm :
            D₁ × D₂ →L[ℝ] WithLp q (D₁ × D₂)).comp
              (ContinuousLinearMap.inr ℝ D₁ D₂)).compLpL p μ) =
      ((((WithLp.prodContinuousLinearEquiv q ℝ F₁ F₂).symm :
          F₁ × F₂ →L[ℝ] WithLp q (F₁ × F₂)).comp
            (ContinuousLinearMap.inr ℝ F₁ F₂)).compLpL p μ).comp
        (ι₂.compLpL p μ) := by
  rw [ContinuousLinearMap.compLpL_comp_compLpL, ContinuousLinearMap.compLpL_comp_compLpL]
  congr 1
  ext x
  simp

end Compat

section Prod

variable [FiniteDimensional ℝ E] [BorelSpace E] {D₁ D₂ F₁ F₂ : Type*} [NormedAddCommGroup D₁]
  [NormedSpace ℝ D₁] [NormedAddCommGroup D₂] [NormedSpace ℝ D₂] [NormedAddCommGroup F₁]
  [NormedSpace ℝ F₁] [CompleteSpace F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [CompleteSpace F₂] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **The graph space over a direct sum is the product of the graph spaces.** For continuous
linear maps `ι₁ : D₁ →L[ℝ] F₁` and `ι₂ : D₂ →L[ℝ] F₂`, a path `u` in `Lᵖ(Ω, WithLp q (D₁ × D₂))`
has `(ι₁ ⊕ ι₂) ∘ u` weakly differentiable exactly when its components `u₁` and `u₂` have `ι₁ ∘ u₁`
and `ι₂ ∘ u₂` weakly differentiable. This continuous linear equivalence sends `u` to `(u₁, u₂)`. -/
def withLpProdEquiv (ι₁ : D₁ →L[ℝ] F₁) (ι₂ : D₂ →L[ℝ] F₂) :
    WeakDerivStep mu Omega p ((ι₁.withLpProdMap q ι₂).compLpL p (mu.restrict Omega)) ≃L[ℝ]
      WeakDerivStep mu Omega p (ι₁.compLpL p (mu.restrict Omega)) ×
        WeakDerivStep mu Omega p (ι₂.compLpL p (mu.restrict Omega)) :=
  .ofContinuousLinearMap
    ((mapL _ _ _ _ (withLpProd_fst_compat ι₁ ι₂)).prod
      (mapL _ _ _ _ (withLpProd_snd_compat ι₁ ι₂)))
    ((mapL _ _ _ _ (withLpProd_inl_compat ι₁ ι₂)).coprod
      (mapL _ _ _ _ (withLpProd_inr_compat ι₁ ι₂)))
    (ContinuousLinearMap.ext fun w ↦ by
      have h := (Lp.withLpProdEquiv ℝ q (mu.restrict Omega)).apply_symm_apply
        (prev _ w.1, prev _ w.2)
      simp only [Lp.withLpProdEquiv_apply, Lp.withLpProdEquiv_symm_apply, map_add] at h
      refine Prod.ext (ext ?_) (ext ?_)
      · simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
          ContinuousLinearMap.coprod_apply, map_add, prev_add, prev_mapL,
          ContinuousLinearMap.id_apply, Prod.fst_add] using congrArg Prod.fst h
      · simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
          ContinuousLinearMap.coprod_apply, map_add, prev_add, prev_mapL,
          ContinuousLinearMap.id_apply, Prod.snd_add] using congrArg Prod.snd h)
    (ContinuousLinearMap.ext fun u ↦ ext <| by
      have h := (Lp.withLpProdEquiv ℝ q (mu.restrict Omega)).symm_apply_apply (prev _ u)
      simp only [Lp.withLpProdEquiv_apply, Lp.withLpProdEquiv_symm_apply] at h
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coprod_apply, prev_add, prev_mapL,
        ContinuousLinearMap.id_apply] using h)

variable (ι₁ : D₁ →L[ℝ] F₁) (ι₂ : D₂ →L[ℝ] F₂)

/-- The first component of `TauCeti.WeakDerivStep.withLpProdEquiv ι₁ ι₂ u` is the path of first
components of `u`. -/
@[simp]
theorem prev_withLpProdEquiv_fst
    (u : WeakDerivStep mu Omega p ((ι₁.withLpProdMap q ι₂).compLpL p (mu.restrict Omega))) :
    prev _ (withLpProdEquiv ι₁ ι₂ u).1 =
      (WithLp.fstL q ℝ D₁ D₂).compLpL p (mu.restrict Omega) (prev _ u) :=
  prev_mapL _ _ _ _ _ u

/-- The second component of `TauCeti.WeakDerivStep.withLpProdEquiv ι₁ ι₂ u` is the path of second
components of `u`. -/
@[simp]
theorem prev_withLpProdEquiv_snd
    (u : WeakDerivStep mu Omega p ((ι₁.withLpProdMap q ι₂).compLpL p (mu.restrict Omega))) :
    prev _ (withLpProdEquiv ι₁ ι₂ u).2 =
      (WithLp.sndL q ℝ D₁ D₂).compLpL p (mu.restrict Omega) (prev _ u) :=
  prev_mapL _ _ _ _ _ u

/-- The inverse of `TauCeti.WeakDerivStep.withLpProdEquiv ι₁ ι₂` pairs the paths of its two
arguments. -/
@[simp]
theorem prev_withLpProdEquiv_symm
    (w : WeakDerivStep mu Omega p (ι₁.compLpL p (mu.restrict Omega)) ×
      WeakDerivStep mu Omega p (ι₂.compLpL p (mu.restrict Omega))) :
    prev _ ((withLpProdEquiv (q := q) ι₁ ι₂).symm w) =
      (Lp.withLpProdEquiv ℝ q (mu.restrict Omega)).symm (prev _ w.1, prev _ w.2) := by
  simp only [withLpProdEquiv, ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofContinuousLinearMap, ContinuousLinearMap.coprod_apply, prev_add,
    prev_mapL, Lp.withLpProdEquiv_symm_apply]

/-- The weak derivative of the first component of `TauCeti.WeakDerivStep.withLpProdEquiv ι₁ ι₂ u`
is the first component of the weak derivative of `u`. -/
@[simp]
theorem weakFDeriv_withLpProdEquiv_fst
    (u : WeakDerivStep mu Omega p ((ι₁.withLpProdMap q ι₂).compLpL p (mu.restrict Omega))) :
    weakFDeriv _ (withLpProdEquiv ι₁ ι₂ u).1 =
      (ContinuousLinearMap.compL ℝ E _ _ (WithLp.fstL q ℝ F₁ F₂)).compLpL p (mu.restrict Omega)
        (weakFDeriv _ u) :=
  weakFDeriv_mapL _ _ _ _ _ u

/-- The weak derivative of the second component of `TauCeti.WeakDerivStep.withLpProdEquiv ι₁ ι₂ u`
is the second component of the weak derivative of `u`. -/
@[simp]
theorem weakFDeriv_withLpProdEquiv_snd
    (u : WeakDerivStep mu Omega p ((ι₁.withLpProdMap q ι₂).compLpL p (mu.restrict Omega))) :
    weakFDeriv _ (withLpProdEquiv ι₁ ι₂ u).2 =
      (ContinuousLinearMap.compL ℝ E _ _ (WithLp.sndL q ℝ F₁ F₂)).compLpL p (mu.restrict Omega)
        (weakFDeriv _ u) :=
  weakFDeriv_mapL _ _ _ _ _ u

end Prod

end WeakDerivStep

end TauCeti
