/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import TauCeti.Topology.FilledHull
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Analysis.Normed.Module.Connected

/-!
# Transport of complementary components and filled hulls under inversion

Inverting a closed set `K` in a normed division ring `𝕜` of real dimension greater than one via
`z ↦ (z - a₀)⁻¹` about a point `a₀ ∉ filledHull K` carries the punctured component of `Kᶜ`
containing `a₀` into the unbounded component of the inverted complement containing `0`
(`IsClosed.image_inv_sub_sdiff_singleton_subset_connectedComponentIn_zero`), so `0` lies outside the
filled hull of the inverted set (`IsClosed.zero_notMem_filledHull_image_inv_sub`). Consequently, any
pole set meeting `connectedComponentIn Kᶜ x` for all `x ∈ filledHull K \ K` maps (after removing
`a₀`) to a set meeting every bounded connected component of the inverted complement
(`IsClosed.image_inv_sub_inter_connectedComponentIn_nonempty`).

## Main results

* `IsClosed.image_inv_sub_sdiff_singleton_subset_connectedComponentIn_zero`: the punctured
  component of `a₀ ∉ filledHull K` in `Kᶜ` maps into the complementary component of `0` under
  inversion about `a₀`.
* `IsClosed.zero_notMem_filledHull_image_inv_sub`: `0` lies outside the filled hull of the
  inversion of a closed set `K` about a point `a₀ ∉ filledHull K`.
* `IsClosed.image_inv_sub_inter_connectedComponentIn_nonempty`: if `A` meets
  `connectedComponentIn Kᶜ x` for every `x ∈ filledHull K \ K` and `a₀ ∉ filledHull K`, then
  `(fun z ↦ (z - a₀)⁻¹) '' (A \ {a₀})` meets every bounded complementary component of
  `(fun z ↦ (z - a₀)⁻¹) '' K`.
-/

public section

open Bornology Filter Metric Set Topology

namespace TauCeti

/-- Under inversion `z ↦ (z - a₀)⁻¹` about a point `a₀` in the unbounded complementary component of
a closed set `K` in a normed division ring of real dimension greater than one, the image of
`connectedComponentIn Kᶜ a₀ \ {a₀}` lies in the component of `0` in
`((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ`. -/
theorem _root_.IsClosed.image_inv_sub_sdiff_singleton_subset_connectedComponentIn_zero {𝕜 : Type*}
    [NormedDivisionRing 𝕜] [NormedSpace ℝ 𝕜] (hrank : 1 < Module.rank ℝ 𝕜) {K : Set 𝕜} {a₀ : 𝕜}
    (hK : IsClosed K) (ha₀ : a₀ ∉ filledHull K) :
    (fun z ↦ (z - a₀)⁻¹) '' (connectedComponentIn Kᶜ a₀ \ {a₀}) ⊆
      connectedComponentIn ((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ 0 := by
  let φ : 𝕜 → 𝕜 := fun z ↦ (z - a₀)⁻¹
  set D := connectedComponentIn Kᶜ a₀
  have ha₀K : a₀ ∉ K := fun h ↦ ha₀ (subset_filledHull h)
  have h0K' : (0 : 𝕜) ∉ φ '' K := by
    rintro ⟨z, hzK, h0⟩
    exact inv_ne_zero (sub_ne_zero.mpr fun h : z = a₀ ↦ ha₀K (h ▸ hzK)) h0
  have hD_sdiff_preconn : IsPreconnected (D \ {a₀}) :=
    isPreconnected_connectedComponentIn.sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank hrank
      hK.isOpen_compl.connectedComponentIn (isClosed_singleton.preimage continuous_subtypeVal)
      ((Set.finite_singleton a₀).isDiscrete.preimage continuous_subtypeVal.continuousOn
        Subtype.val_injective)
  have hD_sdiff_unbdd : ¬ IsBounded (D \ {a₀}) := fun hbd ↦
    (mem_filledHull_iff.not.mp ha₀) <| (hbd.insert a₀).subset fun z hz ↦ by
      by_cases hza : z = a₀
      · simp [hza]
      · exact Or.inr ⟨hz, hza⟩
  exact image_inv_sub_subset_connectedComponentIn_zero hD_sdiff_preconn
    (sdiff_subset.trans (connectedComponentIn_subset Kᶜ a₀)) (fun h ↦ h.2 rfl)
    hD_sdiff_unbdd h0K'

/-- Under inversion `z ↦ (z - a₀)⁻¹` about a point `a₀` in the unbounded complementary component of
a closed set `K` in a normed division ring of real dimension greater than one, `0` lies outside the
filled hull of `(fun z ↦ (z - a₀)⁻¹) '' K`. -/
theorem _root_.IsClosed.zero_notMem_filledHull_image_inv_sub {𝕜 : Type*} [NormedDivisionRing 𝕜]
    [NormedSpace ℝ 𝕜] (hrank : 1 < Module.rank ℝ 𝕜) {K : Set 𝕜} {a₀ : 𝕜} (hK : IsClosed K)
    (ha₀ : a₀ ∉ filledHull K) :
    0 ∉ filledHull ((fun z ↦ (z - a₀)⁻¹) '' K) := by
  let φ : 𝕜 → 𝕜 := fun z ↦ (z - a₀)⁻¹
  set D := connectedComponentIn Kᶜ a₀
  have ha₀K : a₀ ∉ K := fun h ↦ ha₀ (subset_filledHull h)
  have hD_sub := hK.image_inv_sub_sdiff_singleton_subset_connectedComponentIn_zero hrank ha₀
  have ha₀_cl : a₀ ∈ closure (D \ {a₀}) := by
    have := Module.punctured_nhds_neBot ℝ 𝕜 a₀
    simpa only [Set.sdiff_eq] using (dense_compl_singleton a₀).open_subset_closure_inter
      hK.isOpen_compl.connectedComponentIn (mem_connectedComponentIn ha₀K)
  have hImg_unbdd : ¬ IsBounded (φ '' (D \ {a₀})) :=
    fun hb ↦ (isBounded_image_inv_sub_iff (U := D \ {a₀}) fun h ↦ h.2 rfl).mp hb ha₀_cl
  exact mem_filledHull_iff.not.mpr fun hbd ↦ hImg_unbdd (hbd.subset hD_sub)

/-- If `A` meets `connectedComponentIn Kᶜ x` for every `x ∈ filledHull K \ K` for a closed set `K`
in a normed division ring of real dimension greater than one and `a₀ ∉ filledHull K`, then under
the inversion `z ↦ (z - a₀)⁻¹` the set `(fun z ↦ (z - a₀)⁻¹) '' (A \ {a₀})` meets every bounded
connected component of `((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ`. -/
theorem _root_.IsClosed.image_inv_sub_inter_connectedComponentIn_nonempty {𝕜 : Type*}
    [NormedDivisionRing 𝕜] [NormedSpace ℝ 𝕜] (hrank : 1 < Module.rank ℝ 𝕜)
    {K A : Set 𝕜} {a₀ : 𝕜} (hK : IsClosed K) (ha₀ : a₀ ∉ filledHull K)
    (hA : ∀ x ∈ filledHull K \ K, (A ∩ connectedComponentIn Kᶜ x).Nonempty) :
    ∀ w ∈ filledHull ((fun z ↦ (z - a₀)⁻¹) '' K) \ ((fun z ↦ (z - a₀)⁻¹) '' K),
      ((fun z ↦ (z - a₀)⁻¹) '' (A \ {a₀}) ∩
        connectedComponentIn ((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ w).Nonempty := by
  let φ : 𝕜 → 𝕜 := fun z ↦ (z - a₀)⁻¹
  have h0_not := hK.zero_notMem_filledHull_image_inv_sub hrank ha₀
  have hD_sub := hK.image_inv_sub_sdiff_singleton_subset_connectedComponentIn_zero hrank ha₀
  have h0K' : (0 : 𝕜) ∉ φ '' K := fun h ↦ h0_not (subset_filledHull h)
  rintro w ⟨hwH, hwK'⟩
  have hw0 : w ≠ 0 := fun h ↦ h0_not (h ▸ hwH)
  set x : 𝕜 := a₀ + w⁻¹
  have hxa₀ : x ≠ a₀ := fun h ↦ inv_ne_zero hw0 (by simpa [x] using h)
  have hφx : φ x = w := by simp [φ, x]
  have hxK : x ∈ Kᶜ := fun hxK ↦ hwK' ⟨x, hxK, hφx⟩
  have hw_not_comp0 : w ∉ connectedComponentIn (φ '' K)ᶜ 0 := fun hw0c ↦
    h0_not ((mem_filledHull_iff_of_mem_connectedComponentIn hw0c).mp hwH)
  have ha₀_not_comp : a₀ ∉ connectedComponentIn Kᶜ x := fun hmem ↦
    hw_not_comp0 <| hD_sub ⟨x, ⟨(connectedComponentIn_eq hmem).symm ▸ mem_connectedComponentIn hxK,
      hxa₀⟩, hφx⟩
  have hxH : x ∈ filledHull K := by
    by_contra hx_not
    exact hw_not_comp0 <| image_inv_sub_subset_connectedComponentIn_zero
      isPreconnected_connectedComponentIn (connectedComponentIn_subset Kᶜ x) ha₀_not_comp
      (mem_filledHull_iff.not.mp hx_not) h0K' ⟨x, mem_connectedComponentIn hxK, hφx⟩
  obtain ⟨b, hbA, hbc⟩ := hA x ⟨hxH, hxK⟩
  have hba₀ : b ≠ a₀ := fun h ↦ ha₀_not_comp (h ▸ hbc)
  have hcomp := ContinuousOn.mapsTo_connectedComponentIn (f := φ)
    ((continuousOn_inv_sub_compl_singleton a₀).mono fun _ hz hza ↦ ha₀_not_comp (hza ▸ hz))
    (mem_connectedComponentIn hxK)
  rw [isPreconnected_connectedComponentIn.connectedComponentIn (mem_connectedComponentIn hxK),
    hφx] at hcomp
  exact ⟨φ b, ⟨b, ⟨hbA, hba₀⟩, rfl⟩, connectedComponentIn_mono w
    ((image_mono (connectedComponentIn_subset Kᶜ x)).trans
      (Set.image_compl_subset (inv_sub_injective a₀))) (hcomp hbc)⟩

end TauCeti
