/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ContinuousLog.Basic
public import Mathlib.Topology.Path
import TauCeti.Analysis.Contour.Primitive
import TauCeti.Analysis.Normed.Field.Inversion

/-!
# Continuous logarithms of a Borsuk map off a connected set

For two points `p` and `q` of the plane, the Borsuk map `z ↦ (z - p) / (z - q)` has a continuous
logarithm off any path from `p` to `q`, and more generally off the closure of a bounded connected
set that contains `p` in its closure and accumulates at `q`. The classical reason is that a closed
curve avoiding such a set winds equally often around `p` and `q`. The main statements are:

* `TauCeti.hasContinuousLogOn_sub_div_sub_compl_closure`: if `C` is bounded and preconnected,
  `q ∈ closure C \ C` and `p ∈ closure C`, then the Borsuk map has a continuous logarithm on
  `(closure C)ᶜ`;
* `Path.hasContinuousLogOn_sub_div_sub_compl_range`: the Borsuk map of the two endpoints of any
  path has a continuous logarithm off the range of that path.

These are dual to `TauCeti.hasContinuousLogOn_sub_div_sub`, which produces a logarithm on a closed
set when the two points are joined in its complement.

The proof inverts about `q`. Writing `w = (z - q)⁻¹`, the Borsuk map becomes the affine function
`w ↦ 1 + (q - p) * w`, whose only zero `(p - q)⁻¹` is the image of `p`. The image `A` of
`closure C \ {q}` under the inversion is closed by
`TauCeti.isClosed_setOf_ne_zero_and_add_inv_mem`. The image of `C` is preconnected, unbounded
by `TauCeti.not_isBounded_image_sub_inv_of_mem_closure`, and dense in `A`, so every connected
component of `A` is unbounded. Thus the complement of `A` has no holes, and the affine function
has a holomorphic logarithm there by
`TauCeti.Contour.exists_differentiableOn_eqOn_exp_comp_of_filledHull_subset`.

## References

* S. Janiszewski, *Sur les coupures du plan faites par les continus*, Prace Mat.-Fiz. **26**
  (1913).
* M. H. A. Newman, *Elements of the Topology of Plane Sets of Points*, Chapter V.
-/

public section

namespace TauCeti

open Bornology Metric Set Topology

variable {C : Set ℂ} {p q : ℂ}

/-- **The Borsuk map has a continuous logarithm off a connected set joining its two points.** Let
`C` be bounded and preconnected, with `q` in its closure but not in `C`, and with `p ≠ q` in its
closure. Then `z ↦ (z - p) / (z - q)` has a continuous logarithm on the complement of
`closure C`. -/
theorem hasContinuousLogOn_sub_div_sub_compl_closure (hCc : IsPreconnected C)
    (hCb : IsBounded C) (hqC : q ∈ closure C) (hqC' : q ∉ C) (hpC : p ∈ closure C)
    (hpq : p ≠ q) : HasContinuousLogOn (fun z => (z - p) / (z - q)) (closure C)ᶜ := by
  set A : Set ℂ := {w : ℂ | w ≠ 0 ∧ q + w⁻¹ ∈ closure C}
  have hA : IsClosed A := isClosed_setOf_ne_zero_and_add_inv_mem isClosed_closure hCb.closure q
  -- the inversion of `C` is a preconnected unbounded subset of `A`, dense in `A`
  set D : Set ℂ := (fun z => (z - q)⁻¹) '' C
  have hqz : ∀ z ∈ C, z - q ≠ 0 := fun z hz h0 => hqC' (sub_eq_zero.mp h0 ▸ hz)
  have hDA : D ⊆ A := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨inv_ne_zero (hqz z hz), by simpa using subset_closure hz⟩
  have hDc : IsPreconnected D :=
    hCc.image _ ((continuousOn_id.sub continuousOn_const).inv₀ hqz)
  have hDb : ¬ IsBounded D := not_isBounded_image_sub_inv_of_mem_closure hqC hqC'
  have hfill : filledHull Aᶜ ⊆ Aᶜ := by
    intro w hw hwA
    have hwD : w ∈ closure D := by
      have hw' : (fun z => (z - q)⁻¹) (q + w⁻¹) = w := by simp
      rw [← hw']
      refine mem_closure_image ?_ hwA.2
      exact ((continuous_id.sub continuous_const).continuousAt).inv₀ (by simpa using hwA.1)
    have hsub : insert w D ⊆ connectedComponentIn A w :=
      (hDc.subset_closure (subset_insert w D) (insert_subset hwD subset_closure)
        ).subset_connectedComponentIn (mem_insert w D) (insert_subset hwA hDA)
    rw [mem_filledHull_iff, compl_compl] at hw
    exact hDb (hw.subset ((subset_insert w D).trans hsub))
  -- after inversion the Borsuk map is affine, with its only zero in `A`
  have hzero : 0 ∉ (fun w => 1 + (q - p) * w) '' Aᶜ := by
    rintro ⟨w, hwA, hw0⟩
    have hpq' : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
    have hw : w = (p - q)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -hw0)
    exact hwA ⟨by simpa [hw] using sub_ne_zero.mpr hpq, by simpa [hw] using hpC⟩
  obtain ⟨L, hLd, hL⟩ := Contour.exists_differentiableOn_eqOn_exp_comp_of_filledHull_subset
    (g := fun w => 1 + (q - p) * w) hA.isOpen_compl hfill ((differentiable_const _).add
      ((differentiable_const _).mul differentiable_id)).differentiableOn hzero
  have hmaps : MapsTo (fun z => (z - q)⁻¹) (closure C)ᶜ Aᶜ := by
    intro z hz hzA
    exact hz (by simpa using hzA.2)
  have hzq : ∀ z ∈ (closure C)ᶜ, z - q ≠ 0 := fun z hz h0 => hz (sub_eq_zero.mp h0 ▸ hqC)
  refine hasContinuousLogOn_iff.mpr ⟨fun z => L (z - q)⁻¹,
    hLd.continuousOn.comp ((continuousOn_id.sub continuousOn_const).inv₀ hzq) hmaps,
    fun z hz => ?_⟩
  have h := hL (hmaps hz)
  simp only [Function.comp_apply] at h
  rw [h]
  field_simp [hzq z hz]
  ring

end TauCeti

namespace Path

open Set TauCeti

variable {p q : ℂ}

/-- **The Borsuk map of the endpoints of a path has a continuous logarithm off the path.** For
any path `γ` from `p` to `q`, the map `z ↦ (z - p) / (z - q)` has a continuous logarithm on the
complement of `range γ`. The path need not be injective. -/
theorem hasContinuousLogOn_sub_div_sub_compl_range (γ : Path p q) :
    HasContinuousLogOn (fun z => (z - p) / (z - q)) (range γ)ᶜ := by
  rcases eq_or_ne p q with rfl | hpq
  · refine hasContinuousLogOn_iff.mpr ⟨fun _ => 0, continuousOn_const, fun z hz => ?_⟩
    have hz : z - p ≠ 0 := sub_ne_zero.mpr fun h => hz ⟨0, by rw [γ.source, h]⟩
    simp [div_self hz]
  -- the first time `τ` at which the extended path reaches `q`
  set T : Set ℝ := Icc 0 1 ∩ γ.extend ⁻¹' {q}
  have hT : IsClosed T := isClosed_Icc.inter (isClosed_singleton.preimage γ.continuous_extend)
  have hTne : T.Nonempty := ⟨1, ⟨le_refl _ |>.trans' zero_le_one, le_rfl⟩, by simp⟩
  set τ := sInf T
  have hτ : τ ∈ T := hT.csInf_mem hTne ⟨0, fun t ht => ht.1.1⟩
  have hτ0 : 0 < τ := by
    refine lt_of_le_of_ne hτ.1.1 fun h0 => hpq ?_
    have := hτ.2
    rw [← h0, mem_preimage, Path.extend_zero, mem_singleton_iff] at this
    exact this
  set C : Set ℂ := γ.extend '' Ico 0 τ
  have hqC' : q ∉ C := by
    rintro ⟨t, ht, htq⟩
    exact not_le.mpr ht.2 (csInf_le ⟨0, fun s hs => hs.1.1⟩
      ⟨⟨ht.1, ht.2.le.trans hτ.1.2⟩, htq⟩)
  have hqC : q ∈ closure C := by
    have := hτ.2
    rw [mem_preimage, mem_singleton_iff] at this
    rw [← this]
    refine mem_closure_image γ.continuous_extend.continuousAt ?_
    rw [closure_Ico hτ0.ne]
    exact right_mem_Icc.mpr hτ0.le
  have hpC : p ∈ closure C :=
    subset_closure ⟨0, left_mem_Ico.mpr hτ0, Path.extend_zero γ⟩
  have hCrange : closure C ⊆ range γ := by
    refine closure_minimal ?_ (isCompact_range γ.continuous).isClosed
    rintro _ ⟨t, -, rfl⟩
    exact γ.extend_range ▸ mem_range_self t
  refine (hasContinuousLogOn_sub_div_sub_compl_closure
    (isPreconnected_Ico.image _ γ.continuous_extend.continuousOn)
    ((isCompact_range γ.continuous).isBounded.subset (subset_closure.trans hCrange))
    hqC hqC' hpC hpq).mono (compl_subset_compl.mpr hCrange)

end Path
