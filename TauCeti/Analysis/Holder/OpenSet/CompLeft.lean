/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet.Closure
import TauCeti.Analysis.Holder.CompLinear

/-!
# Postcomposition with a linear map in Hölder spaces on an open set

Let `Ω` be an open set. Postcomposition with a continuous linear map `g : F →L[ℝ] G` of the values
acts boundedly from `C^{k,α}(Ω, F)` to `C^{k,α}(Ω, G)` (`TauCeti.CkHolderSpaceOn.compLeftL`), with
operator norm at most `‖g‖`: every derivative field of `g ∘ f` is `g` applied to the corresponding
derivative field of `f`. This is the open-set counterpart of `TauCeti.CkHolderSpace.compLeftL`.
Postcomposition commutes with the extension by zero near each point of `Ω`
(`TauCeti.CkHolderSpaceOn.extend_compLeftL_eventuallyEq`) and, on a convex open set, with the
extension to the closure, so it acts on boundary values as well
(`TauCeti.CkHolderSpaceOn.closureExtend_compLeftL`).

For instance, the coordinate projections of `ι → F` send an element of `C^{k,α}(Ω, ι → F)` to its
coordinates in `C^{k,α}(Ω, F)`, and the coordinate inclusions put them back. This reduces boundary
problems for maps into `ℂⁿ` with a boundary condition imposed coordinatewise to the scalar case.
-/

public section

noncomputable section

open TopologicalSpace
open scoped NNReal

namespace TauCeti.CkHolderSpaceOn

variable {k : ℕ} {α : ℝ≥0} {E F G G' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Opens E} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup G'] [NormedSpace ℝ G']

private theorem iteratedFDeriv_comp_left (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) {i : ℕ}
    (hi : i ≤ k) (x : Ω) :
    _root_.iteratedFDeriv ℝ i (g ∘ f.extend) x =
      g.compContinuousMultilinearMap (_root_.iteratedFDeriv ℝ i f.extend x) :=
  g.iteratedFDeriv_comp_left (f.contDiffOn_extend.contDiffAt (Ω.isOpen.mem_nhds x.property))
    (by exact_mod_cast hi)

private theorem holderOnWith_iteratedFDeriv_comp_left (g : F →L[ℝ] G)
    (f : CkHolderSpaceOn k α Ω F) :
    HolderOnWith (‖g‖₊ * nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F)) α
      (_root_.iteratedFDeriv ℝ k (g ∘ f.extend)) Ω :=
  g.holderOnWith_iteratedFDeriv_comp_left Ω.isOpen f.contDiffOn_extend
    f.holderOnWith_iteratedFDeriv_extend

private theorem memHolder_iteratedFDeriv_comp_left (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) :
    MemHolder α fun x : Ω ↦ _root_.iteratedFDeriv ℝ k (g ∘ f.extend) x :=
  (holderOnWith_iteratedFDeriv_comp_left g f).holderWith.memHolder

/-- Postcomposition of an element of `C^{k,α}(Ω)` with a continuous linear map. -/
private def compLeft (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) : CkHolderSpaceOn k α Ω G :=
  ofContDiffOn (g ∘ f.extend) (g.contDiff.comp_contDiffOn f.contDiffOn_extend)
    (fun i hi ↦ ⟨‖g‖ * ‖f‖, fun x ↦ by
      rw [iteratedFDeriv_comp_left g f hi x]
      exact (g.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_left (f.norm_iteratedFDeriv_extend_le hi x) (norm_nonneg g))⟩)
    (memHolder_iteratedFDeriv_comp_left g f)

private theorem compLeft_apply (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    compLeft g f x = g (f x) := by
  rw [compLeft, ofContDiffOn_apply, Function.comp_apply, extend_apply]

private theorem iteratedFDeriv_compLeft (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F)
    (i : Fin (k + 1)) (x : Ω) :
    (compLeft g f).iteratedFDeriv i x = g.compContinuousMultilinearMap (f.iteratedFDeriv i x) := by
  rw [compLeft, iteratedFDeriv_ofContDiffOn,
    iteratedFDeriv_comp_left g f (Nat.lt_succ_iff.1 i.isLt), iteratedFDeriv_extend]

/-- Postcomposition with `g` multiplies the norm by at most `‖g‖`. -/
private theorem norm_compLeft_le (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) :
    ‖compLeft g f‖ ≤ ‖g‖ * ‖f‖ := by
  have hH : HolderWith (‖g‖₊ * nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F))
      α ((compLeft g f).iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] G) := by
    have he : ((compLeft g f).iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] G) =
        (Ω : Set E).domRestrict (_root_.iteratedFDeriv ℝ k (g ∘ f.extend)) := funext fun x ↦ by
      rw [iteratedFDeriv_compLeft, ← iteratedFDeriv_extend, Set.domRestrict_apply,
        iteratedFDeriv_comp_left g f le_rfl]
      -- `↑(Fin.last k)` reduces to `k`, which `rw` cannot rewrite in the dependent type.
      rfl
    rw [he]
    exact (holderOnWith_iteratedFDeriv_comp_left g f).holderWith
  refine (norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith
    (M := fun i ↦ ‖g‖ * ‖f.iteratedFDeriv i‖) (fun i ↦ by positivity) (fun i x ↦ ?_) hH).trans_eq ?_
  · rw [iteratedFDeriv_compLeft]
    exact (g.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left ((f.iteratedFDeriv i).norm_coe_le_norm x) (norm_nonneg g))
  · rw [norm_eq f, mul_add, Finset.mul_sum, NNReal.coe_mul, coe_nnNorm]

variable (k α Ω) in
/-- Postcomposition with a continuous linear map `g` of the values, as a bounded linear operator
from `C^{k,α}(Ω, F)` to `C^{k,α}(Ω, G)`. -/
def compLeftL (g : F →L[ℝ] G) : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k α Ω G :=
  LinearMap.mkContinuous
    { toFun := compLeft g
      map_add' f₁ f₂ := ext fun x ↦ by simp [compLeft_apply, coe_add]
      map_smul' c f := ext fun x ↦ by simp [compLeft_apply, coe_smul] }
    ‖g‖ (norm_compLeft_le g)

@[simp]
theorem compLeftL_apply (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    compLeftL k α Ω g f x = g (f x) :=
  compLeft_apply g f x

/-- The derivative fields of `g ∘ f` are those of `f` followed by `g`. -/
@[simp]
theorem iteratedFDeriv_compLeftL (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F)
    (i : Fin (k + 1)) (x : Ω) :
    (compLeftL k α Ω g f).iteratedFDeriv i x =
      g.compContinuousMultilinearMap (f.iteratedFDeriv i x) :=
  iteratedFDeriv_compLeft g f i x

/-- The operator norm of postcomposition with `g` is at most `‖g‖`. -/
theorem norm_compLeftL_le (g : F →L[ℝ] G) : ‖compLeftL k α Ω g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg g) _

@[simp]
theorem compLeftL_id (f : CkHolderSpaceOn k α Ω F) : compLeftL k α Ω (.id ℝ F) f = f :=
  ext fun _ ↦ by simp

@[simp]
theorem compLeftL_zero (f : CkHolderSpaceOn k α Ω F) :
    compLeftL k α Ω (0 : F →L[ℝ] G) f = 0 :=
  ext fun _ ↦ by simp [coe_zero]

@[simp]
theorem compLeftL_compLeftL (g : F →L[ℝ] G) (g' : G →L[ℝ] G') (f : CkHolderSpaceOn k α Ω F) :
    compLeftL k α Ω g' (compLeftL k α Ω g f) = compLeftL k α Ω (g'.comp g) f :=
  ext fun _ ↦ by simp

/-- Near each point of `Ω`, the extension by zero of `g ∘ f` is `g` composed with the extension by
zero of `f`. -/
theorem extend_compLeftL_eventuallyEq (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) {x : E}
    (hx : x ∈ Ω) : (compLeftL k α Ω g f).extend =ᶠ[nhds x] g ∘ f.extend := by
  filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
  simp [extend_apply_of_mem _ hy]

/-- On a convex open set, the extension to the closure of `g ∘ f` is `g` composed with the
extension to the closure of `f`, at every point of the closure. -/
theorem closureExtend_compLeftL [CompleteSpace F] (hΩ : Convex ℝ (Ω : Set E)) (g : F →L[ℝ] G)
    (f : CkHolderSpaceOn (k + 1) α Ω F) {x : E} (hx : x ∈ closure (Ω : Set E)) :
    (compLeftL (k + 1) α Ω g f).closureExtend x = g (f.closureExtend x) :=
  (compLeftL (k + 1) α Ω g f).closureExtend_eq_of_continuousWithinAt
    (g := fun y ↦ g (f.closureExtend y)) (fun y ↦ by simp) hx
    ((g.continuous.comp_continuousOn (f.continuousOn_closureExtend hΩ) x hx).mono subset_closure)

end TauCeti.CkHolderSpaceOn
