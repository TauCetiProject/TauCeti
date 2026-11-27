/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet.Closure
import TauCeti.Analysis.Holder.CompLinear

/-!
# Postcomposition with a linear map on `C^{k,α}(Ω)`

For an open set `Ω` and a continuous linear map `g : F →L[ℝ] G`, postcomposition `f ↦ g ∘ f` maps
`C^{k,α}(Ω, F)` to `C^{k,α}(Ω, G)` with operator norm at most `‖g‖`
(`TauCeti.CkHolderSpaceOn.compLeftL`): every derivative field of `g ∘ f` is `g` applied to the
corresponding field of `f`. This is the local counterpart of `TauCeti.CkHolderSpace.compLeftL` on
the whole space. With `g` a coordinate projection or a coordinate inclusion it reduces maps into a
finite product to their components, and from order one on it commutes with the values on the
closure of a convex open set (`TauCeti.CkHolderSpaceOn.closureExtend_compLeftL`), so it preserves
boundary conditions defined by those values.

## Main declarations

* `TauCeti.CkHolderSpaceOn.compLeftL`: postcomposition with `g`, with
  `TauCeti.CkHolderSpaceOn.compLeftL_apply`, `TauCeti.CkHolderSpaceOn.iteratedFDeriv_compLeftL`
  and the bound `TauCeti.CkHolderSpaceOn.norm_compLeftL_le`.
* `TauCeti.CkHolderSpaceOn.extend_compLeftL_eventuallyEq`: near each point of `Ω`, the extension by
  zero of `g ∘ f` is `g` after that of `f`.
* `TauCeti.CkHolderSpaceOn.closureExtend_compLeftL`: the values on the closure of `g ∘ f` are `g`
  applied to those of `f`.
* `TauCeti.CkHolderSpaceOn.ext_compLeftL_proj`: an element of `C^{k,α}(Ω, ι → F)` is determined by
  its coordinates, and `TauCeti.CkHolderSpaceOn.compLeftL_proj_sum_compLeftL_single` and
  `TauCeti.CkHolderSpaceOn.sum_compLeftL_single_compLeftL_proj`: taking coordinates and putting
  them back with the coordinate inclusions are inverse.
-/

public section

noncomputable section

namespace TauCeti.CkHolderSpaceOn

open TopologicalSpace
open scoped NNReal

variable {k : ℕ} {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Opens E} {F G G' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']

private theorem iteratedFDeriv_comp_left (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) {i : ℕ}
    (hi : i ≤ k) (x : Ω) :
    _root_.iteratedFDeriv ℝ i (fun y ↦ g (f.extend y)) x =
      g.compContinuousMultilinearMap (_root_.iteratedFDeriv ℝ i f.extend x) :=
  g.iteratedFDeriv_comp_left (f.contDiffOn_extend.contDiffAt (Ω.isOpen.mem_nhds x.property))
    (by exact_mod_cast hi)

private theorem holderOnWith_iteratedFDeriv_comp_left (g : F →L[ℝ] G)
    (f : CkHolderSpaceOn k α Ω F) :
    HolderOnWith (‖g‖₊ * nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F)) α
      (_root_.iteratedFDeriv ℝ k fun y ↦ g (f.extend y)) Ω :=
  g.holderOnWith_iteratedFDeriv_comp_left Ω.isOpen f.contDiffOn_extend
    f.holderOnWith_iteratedFDeriv_extend

/-- Postcomposition of an element of `C^{k,α}(Ω)` with a continuous linear map. -/
private def compLeft (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) : CkHolderSpaceOn k α Ω G :=
  ofContDiffOn (fun y ↦ g (f.extend y)) (g.contDiff.comp_contDiffOn f.contDiffOn_extend)
    (fun i hi ↦ ⟨‖g‖ * ‖f‖, fun x ↦ by
      rw [iteratedFDeriv_comp_left g f hi x]
      exact (g.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_left (f.norm_iteratedFDeriv_extend_le hi x) (norm_nonneg g))⟩)
    ⟨_, fun x y ↦ holderOnWith_iteratedFDeriv_comp_left g f x x.property y y.property⟩

private theorem compLeft_apply (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    compLeft g f x = g (f x) := by
  unfold compLeft
  exact (ofContDiffOn_apply _ _ _ _ x).trans (by rw [extend_apply])

/-- The function `g ∘ f.extend` represents `g ∘ f` on `Ω`. -/
private theorem comp_extend_apply (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    g (f.extend x) = compLeft g f x := by
  rw [compLeft_apply, extend_apply]

/-- Postcomposition with `g` multiplies the norm by at most `‖g‖`. -/
private theorem norm_compLeft_le (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) :
    ‖compLeft g f‖ ≤ ‖g‖ * ‖f‖ := by
  have hfield (i : Fin (k + 1)) (x : Ω) :
      ‖(compLeft g f).iteratedFDeriv i x‖ ≤ ‖g‖ * ‖f.iteratedFDeriv i‖ := by
    rw [← (compLeft g f).iteratedFDeriv_eq (g := fun y ↦ g (f.extend y)) (comp_extend_apply g f),
      iteratedFDeriv_comp_left g f (Nat.lt_succ_iff.1 i.isLt) x]
    exact (g.norm_compContinuousMultilinearMap_le _).trans (mul_le_mul_of_nonneg_left
      (f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv f.extend_apply i x) (norm_nonneg g))
  have htop : HolderWith (‖g‖₊ *
      nnHolderNorm α (f.iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] F)) α
      ((compLeft g f).iteratedFDeriv (Fin.last k) : Ω → E [×k]→L[ℝ] G) := fun x y ↦ by
    rw [← (compLeft g f).iteratedFDeriv_eq (g := fun y ↦ g (f.extend y)) (comp_extend_apply g f),
      ← (compLeft g f).iteratedFDeriv_eq (g := fun y ↦ g (f.extend y)) (comp_extend_apply g f)]
    exact holderOnWith_iteratedFDeriv_comp_left g f x x.property y y.property
  refine (norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith
    (fun i ↦ by positivity) hfield htop).trans_eq ?_
  rw [norm_eq f, mul_add, Finset.mul_sum, NNReal.coe_mul, coe_nnNorm]

/-- Postcomposition with a continuous linear map `g` of the values, as a bounded linear operator
from `C^{k,α}(Ω, F)` to `C^{k,α}(Ω, G)`. -/
def compLeftL (g : F →L[ℝ] G) : CkHolderSpaceOn k α Ω F →L[ℝ] CkHolderSpaceOn k α Ω G :=
  LinearMap.mkContinuous
    { toFun := compLeft g
      map_add' f₁ f₂ := ext fun x ↦ by simp [compLeft_apply, coe_add]
      map_smul' c f := ext fun x ↦ by simp [compLeft_apply, coe_smul] }
    ‖g‖ (norm_compLeft_le g)

/-- The values of `g ∘ f` are `g` applied to the values of `f`. -/
@[simp]
theorem compLeftL_apply (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) (x : Ω) :
    compLeftL g f x = g (f x) :=
  compLeft_apply g f x

/-- The underlying function of `g ∘ f` is `g` after that of `f`. -/
theorem coe_compLeftL (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) :
    ⇑(compLeftL g f) = g ∘ f :=
  funext (compLeftL_apply g f)

/-- Near each point of `Ω`, the extension by zero of `g ∘ f` is `g` after the extension by zero of
`f`. -/
theorem extend_compLeftL_eventuallyEq (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) {x : E}
    (hx : x ∈ Ω) : (compLeftL g f).extend =ᶠ[nhds x] fun y ↦ g (f.extend y) := by
  filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
  rw [extend_apply_of_mem _ hy, compLeftL_apply, extend_apply_of_mem _ hy]

/-- The derivative fields of `g ∘ f` are those of `f` followed by `g`. -/
@[simp]
theorem iteratedFDeriv_compLeftL (g : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F)
    (i : Fin (k + 1)) (x : Ω) :
    (compLeftL g f).iteratedFDeriv i x = g.compContinuousMultilinearMap (f.iteratedFDeriv i x) := by
  rw [← (compLeftL g f).iteratedFDeriv_eq (g := fun y ↦ g (f.extend y))
      fun y ↦ (comp_extend_apply g f y).trans
        ((compLeft_apply g f y).trans (compLeftL_apply g f y).symm),
    iteratedFDeriv_comp_left g f (Nat.lt_succ_iff.1 i.isLt) x, iteratedFDeriv_extend]

/-- The operator norm of postcomposition with `g` is at most `‖g‖`. -/
theorem norm_compLeftL_le (g : F →L[ℝ] G) :
    ‖compLeftL (k := k) (α := α) (Ω := Ω) g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg g) _

/-- Postcomposition with the identity is the identity. -/
@[simp]
theorem compLeftL_id (f : CkHolderSpaceOn k α Ω F) : compLeftL (.id ℝ F) f = f :=
  ext fun _ ↦ by simp

/-- Postcomposition with the zero map is zero. -/
@[simp]
theorem compLeftL_zero (f : CkHolderSpaceOn k α Ω F) : compLeftL (0 : F →L[ℝ] G) f = 0 :=
  ext fun _ ↦ by simp [coe_zero]

/-- Postcomposition is additive in the linear map. -/
@[simp]
theorem compLeftL_add (g₁ g₂ : F →L[ℝ] G) (f : CkHolderSpaceOn k α Ω F) :
    compLeftL (g₁ + g₂) f = compLeftL g₁ f + compLeftL g₂ f :=
  ext fun _ ↦ by simp

/-- Postcomposition with a finite sum of linear maps is the sum of the postcompositions. -/
@[simp]
theorem compLeftL_sum {ι : Type*} (s : Finset ι) (g : ι → F →L[ℝ] G)
    (f : CkHolderSpaceOn k α Ω F) :
    compLeftL (∑ i ∈ s, g i) f = ∑ i ∈ s, compLeftL (g i) f :=
  ext fun _ ↦ by simp

/-- Postcomposition with `g` and then with `g'` is postcomposition with `g' ∘ g`. -/
@[simp]
theorem compLeftL_compLeftL (g : F →L[ℝ] G) (g' : G →L[ℝ] G') (f : CkHolderSpaceOn k α Ω F) :
    compLeftL g' (compLeftL g f) = compLeftL (g'.comp g) f :=
  ext fun _ ↦ by simp

/-- From order one on, on a convex open set and with complete values, the values on the closure of
`g ∘ f` are `g` applied to those of `f`. -/
theorem closureExtend_compLeftL [CompleteSpace F] (hΩ : Convex ℝ (Ω : Set E)) (g : F →L[ℝ] G)
    (f : CkHolderSpaceOn (k + 1) α Ω F) {x : E} (hx : x ∈ closure (Ω : Set E)) :
    (compLeftL g f).closureExtend x = g (f.closureExtend x) :=
  (compLeftL g f).closureExtend_eq_of_continuousWithinAt (g := fun y ↦ g (f.closureExtend y))
    (fun y ↦ by rw [compLeftL_apply, closureExtend_apply]) hx
    (g.continuous.continuousAt.comp_continuousWithinAt
      ((f.continuousOn_closureExtend hΩ x hx).mono subset_closure))

/-! ### Coordinates of maps into a product -/

section Pi

variable {ι : Type*} [Fintype ι]

/-- An element of `C^{k,α}(Ω, ι → F)` is determined by its coordinates. -/
theorem ext_compLeftL_proj {f f' : CkHolderSpaceOn k α Ω (ι → F)}
    (h : ∀ i, compLeftL (.proj (R := ℝ) (φ := fun _ : ι ↦ F) i) f =
      compLeftL (.proj (R := ℝ) (φ := fun _ : ι ↦ F) i) f') :
    f = f' :=
  ext fun x ↦ funext fun i ↦ by simpa using congrArg (· x) (h i)

variable [DecidableEq ι]

/-- The `i`-th coordinate of the element of `C^{k,α}(Ω, ι → F)` with coordinates `f j` is
`f i`. -/
theorem compLeftL_proj_sum_compLeftL_single (f : ι → CkHolderSpaceOn k α Ω F) (i : ι) :
    compLeftL (.proj (R := ℝ) (φ := fun _ : ι ↦ F) i)
      (∑ j, compLeftL (.single ℝ (fun _ ↦ F) j) (f j)) = f i :=
  ext fun x ↦ by simp [Pi.single_apply]

/-- An element of `C^{k,α}(Ω, ι → F)` is the sum of its coordinates, each put back in its
place. -/
theorem sum_compLeftL_single_compLeftL_proj (f : CkHolderSpaceOn k α Ω (ι → F)) :
    ∑ i, compLeftL (.single ℝ (fun _ ↦ F) i)
      (compLeftL (.proj (R := ℝ) (φ := fun _ : ι ↦ F) i) f) = f :=
  ext_compLeftL_proj fun i ↦ compLeftL_proj_sum_compLeftL_single _ i

end Pi

end TauCeti.CkHolderSpaceOn
