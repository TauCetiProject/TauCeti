/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.DoubleAlong.Basic
public import TauCeti.Analysis.Normed.Operator.IntrinsicStar

/-!
# Extending an operator-valued function to the double by conjugation

For a subset `A ⊆ X` and an operator-valued function `g : X → E →L[ℂ] F` between complex spaces
with a conjugation, `TauCeti.DoubleAlong.conjExtend A g` is the function on the double
`TauCeti.DoubleAlong A` which is `g` at the folded point on the first sheet and its intrinsic
conjugate `star ∘ g ∘ star` on the second sheet. Where `g` is real, at the points of `A`, the two
prescriptions agree (`conjExtend_inr`). The extension commutes with composition
(`conjExtend_comp`), turns the sheet swap into conjugation when `g` is real along `A`
(`conjExtend_swap`), and is continuous over an open set on which `g` is continuous and real along
`A` (`continuousOn_conjExtend`).

The transitions and bundle maps of the doubled bundle
(`TauCeti.FiniteRankBundleCore.doubleAlong`) are extensions of this form.
-/

public section

open Set Topology WithConv Filter

namespace TauCeti.DoubleAlong

universe u

variable {X : Type u} [TopologicalSpace X] (A : Set X)
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [StarAddMonoid E] [StarModule ℂ E]
  [ContinuousStar E] [NormedAddCommGroup F] [NormedSpace ℂ F] [StarAddMonoid F] [StarModule ℂ F]
  [ContinuousStar F] [NormedAddCommGroup G] [NormedSpace ℂ G] [StarAddMonoid G] [StarModule ℂ G]
  [ContinuousStar G]

open Classical in
/-- The extension of an operator-valued function `g` on `X` to the double along `A` by
conjugation: `g` at the folded point on the first sheet, and its intrinsic conjugate
`star ∘ g ∘ star` on the second sheet. Where `g` is real, at the points of `A`, the two
prescriptions agree (`conjExtend_inr`). -/
noncomputable def conjExtend (g : X → E →L[ℂ] F) : DoubleAlong A → E →L[ℂ] F :=
  (range (inl A)).piecewise (fun y => g (fold A y))
    fun y => (star (toConv (g (fold A y)))).ofConv

/-- On the first sheet the extension is `g` at the folded point. -/
theorem conjExtend_of_mem (g : X → E →L[ℂ] F) {y : DoubleAlong A} (hy : y ∈ range (inl A)) :
    conjExtend A g y = g (fold A y) := by
  classical
  exact piecewise_eq_of_mem _ _ _ hy

/-- Off the first sheet the extension is the conjugate of `g` at the folded point. -/
theorem conjExtend_of_notMem (g : X → E →L[ℂ] F) {y : DoubleAlong A} (hy : y ∉ range (inl A)) :
    conjExtend A g y = (star (toConv (g (fold A y)))).ofConv := by
  classical
  exact piecewise_eq_of_notMem _ _ _ hy

@[simp] theorem conjExtend_inl (g : X → E →L[ℂ] F) (x : X) : conjExtend A g (inl A x) = g x := by
  rw [conjExtend_of_mem A g (mem_range_self x), fold_inl]

/-- On the second sheet, away from `A`, the extension is the conjugate of `g`. -/
theorem conjExtend_inr_of_notMem (g : X → E →L[ℂ] F) {x : X} (hx : x ∉ A) :
    conjExtend A g (inr A x) = (star (toConv (g x))).ofConv := by
  have : inr A x ∉ range (inl A) := by
    rintro ⟨y, hy⟩
    obtain ⟨rfl, hyA⟩ := (inl_eq_inr_iff A).1 hy
    exact hx hyA
  rw [conjExtend_of_notMem A g this, fold_inr]

/-- On the second sheet the extension is the conjugate of `g`, at points where `g` is real if they
lie in `A`. -/
theorem conjExtend_inr (g : X → E →L[ℂ] F) {x : X} (hx : x ∈ A → IsSelfAdjoint (toConv (g x))) :
    conjExtend A g (inr A x) = (star (toConv (g x))).ofConv := by
  by_cases hxA : x ∈ A
  · rw [← inl_coe_eq_inr A ⟨x, hxA⟩, conjExtend_inl]
    exact congrArg ofConv (hx hxA).star_eq.symm
  · exact conjExtend_inr_of_notMem A g hxA

/-- The extension at a point depends only on the value of `g` at the folded point. -/
theorem conjExtend_congr {g g' : X → E →L[ℂ] F} {y : DoubleAlong A}
    (h : g (fold A y) = g' (fold A y)) : conjExtend A g y = conjExtend A g' y := by
  by_cases hy : y ∈ range (inl A)
  · rw [conjExtend_of_mem A g hy, conjExtend_of_mem A g' hy, h]
  · rw [conjExtend_of_notMem A g hy, conjExtend_of_notMem A g' hy, h]

/-- Pointwise, the extension of a composite is the composite of the extensions. -/
theorem conjExtend_comp (g : X → F →L[ℂ] G) (f : X → E →L[ℂ] F) (y : DoubleAlong A) :
    conjExtend A (fun x => (g x).comp (f x)) y = (conjExtend A g y).comp (conjExtend A f y) := by
  by_cases hy : y ∈ range (inl A)
  · simp only [conjExtend_of_mem A _ hy]
  · simp only [conjExtend_of_notMem A _ hy]
    exact congrArg ofConv (ContinuousLinearMap.intrinsicStar_comp' (g (fold A y)) (f (fold A y)))

/-- The extension of the constant identity is the identity. -/
@[simp] theorem conjExtend_id (y : DoubleAlong A) :
    conjExtend A (fun _ => ContinuousLinearMap.id ℂ E) y = ContinuousLinearMap.id ℂ E := by
  by_cases hy : y ∈ range (inl A)
  · simp only [conjExtend_of_mem A _ hy]
  · simp only [conjExtend_of_notMem A _ hy, ContinuousLinearMap.intrinsicStar_id, ofConv_toConv]

/-- If `g` is real at the points of `A`, its extension at the swapped point is the conjugate of its
extension. -/
theorem conjExtend_swap {g : X → E →L[ℂ] F} (hg : ∀ x ∈ A, IsSelfAdjoint (toConv (g x)))
    (y : DoubleAlong A) :
    conjExtend A g (swap A y) = (star (toConv (conjExtend A g y))).ofConv := by
  induction y using induction_on with
  | hl x => rw [swap_inl, conjExtend_inr A g (hg x), conjExtend_inl]
  | hr x => rw [swap_inr, conjExtend_inl, conjExtend_inr A g (hg x), toConv_ofConv, star_star,
      ofConv_toConv]

/-- If `g` is continuous on an open set `U` and real at the points of `A` in `U`, its extension is
continuous on the preimage of `U` under the fold. -/
theorem continuousOn_conjExtend [FiniteDimensional ℂ E] {g : X → E →L[ℂ] F} {U : Set X}
    (hU : IsOpen U) (hg : ContinuousOn g U)
    (hgA : ∀ x ∈ A ∩ U, IsSelfAdjoint (toConv (g x))) :
    ContinuousOn (conjExtend A g) (fold A ⁻¹' U) := by
  have hs : IsOpen (fold A ⁻¹' U) := hU.preimage (fold A).continuous
  -- Check continuity on each sheet of `X ⊕ X`, through the quotient map onto the double.
  rw [(isQuotientMap_quotientMap A).continuousOn_isOpen_iff hs,
    (hs.preimage (quotientMap A).continuous).continuousOn_iff]
  rintro (x | x) hx
  · rw [mem_preimage, quotientMap_inl, mem_preimage, fold_inl] at hx
    rw [← IsOpenEmbedding.inl.continuousAt_iff]
    refine (hg.continuousAt (hU.mem_nhds hx)).congr (Eventually.of_forall fun y => ?_)
    simp [quotientMap_inl]
  · rw [mem_preimage, quotientMap_inr, mem_preimage, fold_inr] at hx
    rw [← IsOpenEmbedding.inr.continuousAt_iff]
    refine (ContinuousLinearMap.continuous_intrinsicStar.continuousAt.comp
      (hg.continuousAt (hU.mem_nhds hx))).congr (mem_of_superset (hU.mem_nhds hx) fun y hy => ?_)
    simp only [Function.comp_apply, quotientMap_inr]
    exact (conjExtend_inr A g fun hyA => hgA y ⟨hyA, hy⟩).symm

end TauCeti.DoubleAlong
