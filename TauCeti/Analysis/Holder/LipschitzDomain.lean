/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet
public import TauCeti.Analysis.Sobolev.LipschitzDomain.SegmentChain
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Hölder spaces `C^{k,α}(Ω)` on a bounded Lipschitz domain

On a convex open set, the derivative fields of an element of `C^{k,α}(Ω)` below the top order are
`α`-Hölder for `α ≤ 1`, by the mean value inequality, and so `C^{k+1,α}(Ω) ⊆ C^{k,α}(Ω)`
(`TauCeti.CkHolderSpaceOn.inclusionSuccL`). On a general open set this fails across a slit. This
file proves both statements on a bounded Lipschitz domain, which need not be convex: nearby points
of such a domain are joined inside it by three segments of total length comparable to their
distance (`Set.IsLipschitzDomain.exists_segment_chain`), and the mean value inequality along them
bounds the increments of each lower derivative field at small scales. The domains of the global
Schauder theory, bounded domains with `C^{k,α}` boundary, are bounded Lipschitz domains.

## Main declarations

* `TauCeti.CkHolderSpaceOn.exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain`: there is a
  constant `C`, depending only on `Ω` and `α`, such that every derivative field through order `k`
  of every `f ∈ C^{k,α}(Ω)` is `α`-Hölder on `Ω` with constant `C ‖f‖`.
* `TauCeti.CkHolderSpaceOn.inclusionSuccLOfIsLipschitzDomain`: the inclusion
  `C^{k+1,α}(Ω) → C^{k,α}(Ω)` as a continuous linear map.

## References

* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1.
-/

public section

noncomputable section

open TopologicalSpace
open scoped NNReal

namespace TauCeti

namespace CkHolderSpaceOn

universe u v w

variable {k : ℕ} {α : ℝ≥0} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E] {Ω : Opens E} {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E' : Type w} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- On a bounded Lipschitz domain and for `α ≤ 1`, there is a constant `C`, depending only on `Ω`
and `α`, such that for every `f ∈ C^{k,α}(Ω)` and every function `g` agreeing with `f` on `Ω`,
each iterated derivative of `g` through order `k` is `α`-Hölder on `Ω` with constant `C ‖f‖`.
Compare `TauCeti.CkHolderSpaceOn.holderOnWith_iteratedFDeriv_of_le`, with constant `3 ‖f‖`, on a
convex open set. -/
theorem exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E))
    (hα : α ≤ 1) :
    ∃ C : ℝ≥0, ∀ (f : CkHolderSpaceOn k α Ω F) {g : E → F}, (∀ x : Ω, g x = f x) →
      ∀ {j : ℕ}, j ≤ k → HolderOnWith (C * ‖f‖₊) α (_root_.iteratedFDeriv ℝ j g) Ω := by
  obtain ⟨C₀, δ, hδ, hchain⟩ := hΩ.exists_segment_chain hb
  refine ⟨C₀ * δ ^ (1 - (α : ℝ)) + 2 * δ ^ (-(α : ℝ)) + 1, fun f g hg j hj ↦ ?_⟩
  have hf : (‖f‖₊ : ℝ) = ‖f‖ := coe_nnNorm f
  rcases hj.eq_or_lt with rfl | hj
  · -- The top derivative: the Hölder seminorm of the top field is at most `‖f‖`.
    refine (f.holderOnWith_iteratedFDeriv hg).mono_const ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    have hC : 0 ≤ (C₀ : ℝ) * (δ : ℝ) ^ (1 - (α : ℝ)) + 2 * (δ : ℝ) ^ (-(α : ℝ)) := by positivity
    nlinarith [f.nnHolderNorm_iteratedFDeriv_le, mul_nonneg hC (norm_nonneg f)]
  -- Below the top order: the next field bounds the derivative of this one by `‖f‖`.
  have hcd := f.contDiffOn hg
  have hdiff : ∀ x ∈ (Ω : Set E), DifferentiableAt ℝ (_root_.iteratedFDeriv ℝ j g) x :=
    fun x hx ↦ (hcd.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (by exact_mod_cast hj)
  have hder : ∀ x ∈ (Ω : Set E), ‖fderiv ℝ (_root_.iteratedFDeriv ℝ j g) x‖ ≤ ‖f‖ := by
    intro x hx
    rw [norm_fderiv_iteratedFDeriv]
    exact (f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv hg ⟨j + 1, by omega⟩
      ⟨x, hx⟩).trans (f.norm_iteratedFDeriv_le _)
  have hval : ∀ x ∈ (Ω : Set E), ‖_root_.iteratedFDeriv ℝ j g x‖ ≤ ‖f‖ := fun x hx ↦
    (f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv hg ⟨j, by omega⟩ ⟨x, hx⟩).trans
      (f.norm_iteratedFDeriv_le _)
  -- Lipschitz at scales below `δ`, by the mean value inequality along a chain of segments.
  have hnear : ∀ x ∈ (Ω : Set E), ∀ y ∈ (Ω : Set E), dist x y < δ →
      dist (_root_.iteratedFDeriv ℝ j g x) (_root_.iteratedFDeriv ℝ j g y) ≤
        ((‖f‖₊ * C₀ : ℝ≥0) : ℝ) * dist x y ^ ((1 : ℝ≥0) : ℝ) := by
    intro x hx y hy hxy
    obtain ⟨p, q, h1, h2, h3, hlen⟩ := hchain x hx y hy hxy
    rw [dist_comm, dist_eq_norm, NNReal.coe_one, Real.rpow_one, NNReal.coe_mul, hf, mul_assoc]
    exact (norm_image_sub_le_of_norm_fderiv_le_of_segment_subset hdiff hder h1 h2 h3).trans
      (mul_le_mul_of_nonneg_left hlen (norm_nonneg f))
  have hfar : ∀ x ∈ (Ω : Set E), ∀ y ∈ (Ω : Set E),
      dist (_root_.iteratedFDeriv ℝ j g x) (_root_.iteratedFDeriv ℝ j g y) ≤
        ((2 * ‖f‖₊ : ℝ≥0) : ℝ) := by
    intro x hx y hy
    rw [dist_eq_norm, NNReal.coe_mul, hf]
    push_cast
    linarith [norm_sub_le (_root_.iteratedFDeriv ℝ j g x) (_root_.iteratedFDeriv ℝ j g y),
      hval x hx, hval y hy]
  refine (HolderOnWith.of_le_of_dist_le hnear hfar hα hδ).mono_const ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [norm_nonneg f, (δ ^ (1 - (α : ℝ)) : ℝ≥0).coe_nonneg,
    (δ ^ (-(α : ℝ)) : ℝ≥0).coe_nonneg, C₀.coe_nonneg]

/-- The constant of `exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain` for the order-`k`
field of elements of `C^{k+1,α}(Ω)`, chosen once for the inclusion map. -/
private theorem exists_holderOnWith_iteratedFDeriv_succ
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E))
    (hα : α ≤ 1) :
    ∃ C : ℝ≥0, ∀ f : CkHolderSpaceOn (k + 1) α Ω F,
      HolderOnWith (C * ‖f‖₊) α (_root_.iteratedFDeriv ℝ k f.extend) Ω := by
  obtain ⟨C, hC⟩ := exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain (k := k + 1)
    (F := F) hΩ hb hα
  exact ⟨C, fun f ↦ hC f f.extend_apply k.le_succ⟩

/-- On a bounded Lipschitz domain and for `α ≤ 1`, the inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)`, as
a continuous linear map. Compare `TauCeti.CkHolderSpaceOn.inclusionSuccL`, on a convex open set,
which has operator norm at most `3`. -/
def inclusionSuccLOfIsLipschitzDomain (hΩ : (Ω : Set E).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderSpaceOn (k + 1) α Ω F →L[ℝ] CkHolderSpaceOn k α Ω F :=
  let C := (exists_holderOnWith_iteratedFDeriv_succ (k := k) (F := F) hΩ hb hα).choose
  have hC := (exists_holderOnWith_iteratedFDeriv_succ (k := k) (F := F) hΩ hb hα).choose_spec
  LinearMap.mkContinuous
    { toFun f := ofContDiffOn f.extend (f.contDiffOn_extend.of_le (by norm_cast; omega))
        (fun i hi ↦ ⟨‖f.iteratedFDeriv ⟨i, by omega⟩‖, fun x ↦
          f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv f.extend_apply ⟨i, by omega⟩ x⟩)
        (HolderWith.memHolder fun x y ↦ hC f x x.property y y.property)
      map_add' f g := by ext x; simp [extend_apply]
      map_smul' c f := by ext x; simp [extend_apply] }
    (1 + C) fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      refine (norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith
        (M := fun i ↦ ‖f.iteratedFDeriv i.castSucc‖) (fun i ↦ by positivity) (fun i x ↦ ?_)
        (K := C * ‖f‖₊) (fun x y ↦ ?_)).trans ?_
      · rw [iteratedFDeriv_ofContDiffOn]
        exact f.norm_iteratedFDeriv_apply_le_norm_iteratedFDeriv f.extend_apply i.castSucc x
      · rw [iteratedFDeriv_ofContDiffOn, iteratedFDeriv_ofContDiffOn]
        exact hC f x x.property y y.property
      · have hsum : ∑ i : Fin (k + 2), ‖f.iteratedFDeriv i‖ ≤ ‖f‖ := by
          rw [norm_eq]
          exact le_add_of_nonneg_right (NNReal.coe_nonneg _)
        rw [Fin.sum_univ_castSucc] at hsum
        push_cast
        nlinarith [norm_nonneg (f.iteratedFDeriv (Fin.last (k + 1)))]

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` on a bounded Lipschitz domain does not change
values. -/
@[simp]
theorem inclusionSuccLOfIsLipschitzDomain_apply (hΩ : (Ω : Set E).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1) (f : CkHolderSpaceOn (k + 1) α Ω F)
    (x : Ω) : inclusionSuccLOfIsLipschitzDomain hΩ hb hα f x = f x := by
  simp [inclusionSuccLOfIsLipschitzDomain, extend_apply]

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` on a bounded Lipschitz domain keeps the derivative
fields through order `k`. -/
@[simp]
theorem iteratedFDeriv_inclusionSuccLOfIsLipschitzDomain (hΩ : (Ω : Set E).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1) (f : CkHolderSpaceOn (k + 1) α Ω F)
    (i : Fin (k + 1)) (x : Ω) :
    (inclusionSuccLOfIsLipschitzDomain hΩ hb hα f).iteratedFDeriv i x =
      f.iteratedFDeriv i.castSucc x := by
  rw [inclusionSuccLOfIsLipschitzDomain, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
    AddHom.coe_mk, iteratedFDeriv_ofContDiffOn]
  exact f.iteratedFDeriv_eq f.extend_apply i.castSucc x

end CkHolderSpaceOn

end TauCeti
