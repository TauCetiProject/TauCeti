/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Holder.Basic

/-!
# `Cⁿ` sections are Hölder sections

Let `V → M` be a `Cⁿ` real vector bundle over a `Cⁿ` manifold without boundary modelled on a real
normed space `E`, and let `A` be a finite bundle atlas. This file shows that for `k + 1 ≤ n`,
including smooth and analytic `n`, and `α ≤ 1` every `Cⁿ` section of `V` lies in the Hölder
space `C^{k,α}(V)` of `TauCeti.HolderSection`, and that the resulting linear map
`TauCeti.HolderSection.ofContMDiffSection` is injective. These are the smooth elements of the
Hölder scale of sections.

In chart `i` a `Cⁿ` section `s` is read as the function `A.coord i s`, which is `Cⁿ` on the open
set of points of the chart target whose preimage lies in the base set of the bundle chart
(`TauCeti.FiniteBundleAtlas.contDiffOn_coord`). This open set contains the compact set
`chart i '' closure (dom i)`, which contains `A.image i`. Near a compact set a `C^{k+1}` function
has bounded derivatives through order `k` and an `α`-Hölder `k`-th derivative for `α ≤ 1`
(`TauCeti.CkHolderSpaceOn.exists_apply_eq_of_contDiffOn_of_isCompact`), so the reading lies in
`C^{k,α}(A.image i)`. The exponent `α` cannot exceed one here: for `α > 1` the `α`-Hölder functions
on a connected open set are constant, and a smooth section need not have locally constant `k`-th
derivatives in its charts.

## Main results

* `TauCeti.FiniteBundleAtlas.memHolderSection_of_contMDiff`: for `k + 1 ≤ n` and `α ≤ 1`, a
  `Cⁿ` section has `C^{k,α}` readings.
* `TauCeti.HolderSection.ofContMDiffSection`: the linear map from `Cⁿ` sections of `V` to
  `C^{k,α}(V)`, with `TauCeti.HolderSection.toSection_ofContMDiffSection` and
  `TauCeti.HolderSection.ofContMDiffSection_injective`.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold NNReal

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V) {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) n M]
  [ContMDiffVectorBundle n F V 𝓘(ℝ, E)] {k : ℕ} {α : ℝ≥0}

/-- **`Cⁿ` sections are `C^{k,α}`.** For `k + 1 ≤ n` and `α ≤ 1`, the readings of a `Cⁿ`
section in the charts of a finite bundle atlas are `C^{k,α}` on the chart images. -/
theorem FiniteBundleAtlas.memHolderSection_of_contMDiff (hkn : k + 1 ≤ n) (hα : α ≤ 1)
    {s : ∀ x, V x}
    (hs : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) n fun x ↦ TotalSpace.mk' F x (s x)) :
    A.MemHolderSection k α s := by
  have hkn' : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hkn
  have := IsManifold.of_le (I := 𝓘(ℝ, E)) (M := M) hkn'
  have := ContMDiffVectorBundle.of_le (F := F) (E := V) (IB := 𝓘(ℝ, E)) hkn'
  refine A.memHolderSection_iff.2 fun i ↦
    CkHolderSpaceOn.exists_apply_eq_of_contDiffOn_of_isCompact
      ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet) ?_
      (A.isCompact_chart_image_closure_dom i) (A.chart_image_closure_dom_subset i)
      (A.image_subset_chart_image_closure_dom i) hα
  exact_mod_cast A.contDiffOn_coord (hs.of_le hkn') i

namespace HolderSection

/-- **`Cⁿ` sections are Hölder sections.** For `k + 1 ≤ n` and `α ≤ 1`, the linear map sending a
`Cⁿ` section of `V` to the element of `C^{k,α}(V)` whose chart components are its readings. -/
def ofContMDiffSection (hkn : k + 1 ≤ n) (hα : α ≤ 1) :
    Cₛ^n⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] HolderSection A k α where
  toFun s := ofSection s (A.memHolderSection_of_contMDiff hkn hα s.contMDiff)
  map_add' s t := ext <| by simp [ContMDiffSection.coe_add]
  map_smul' c s := ext <| by simp [ContMDiffSection.coe_smul]

/-- The underlying section of the Hölder section of a `Cⁿ` section `s` is `s`. -/
@[simp]
theorem toSection_ofContMDiffSection (hkn : k + 1 ≤ n) (hα : α ≤ 1) (s : Cₛ^n⟮𝓘(ℝ, E); F, V⟯) :
    toSection (ofContMDiffSection A hkn hα s) = s :=
  toSection_ofSection _ _

/-- The chart components of the Hölder section of a `Cⁿ` section `s` are the readings of `s`. -/
@[simp]
theorem ofContMDiffSection_apply (hkn : k + 1 ≤ n) (hα : α ≤ 1) (s : Cₛ^n⟮𝓘(ℝ, E); F, V⟯)
    (i : Fin A.n) (y : A.image i) :
    (ofContMDiffSection A hkn hα s : ∀ i : Fin A.n, CkHolderSpaceOn k α (A.image i) F) i y =
      A.coord i s y :=
  ofSection_apply _ _ i y

/-- **Injectivity.** Distinct `Cⁿ` sections have distinct Hölder sections. -/
theorem ofContMDiffSection_injective (hkn : k + 1 ≤ n) (hα : α ≤ 1) :
    Function.Injective (ofContMDiffSection A hkn hα) := fun s t h ↦
  ContMDiffSection.ext fun x ↦ by
    simpa using congrFun (congrArg toSection h) x

end HolderSection

end TauCeti
