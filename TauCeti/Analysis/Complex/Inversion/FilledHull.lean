/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledHull
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import TauCeti.Analysis.Complex.Inversion.Basic
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Geometry.Manifold.Connected
import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# Transport of complementary components and filled hulls under Möbius inversion

Inverting a closed set `K ⊆ ℂ` via `z ↦ (z - a₀)⁻¹` about a point `a₀` in the unbounded
complementary component of `K` carries the punctured unbounded component of `Kᶜ` into the
unbounded component of the inverted complement containing `0`, so `0` lies outside the filled hull
of the inverted set (`IsClosed.zero_notMem_filledHull_image_inv_sub`). Consequently, any pole set
meeting every connected component of `Kᶜ` maps (after removing `a₀`) to a set meeting every bounded
connected component of the inverted complement
(`IsClosed.image_inv_sub_inter_connectedComponentIn_nonempty`).

## Main results

* `IsClosed.zero_notMem_filledHull_image_inv_sub`: `0` lies outside the filled hull of the
  inversion of a closed set `K` about a point `a₀ ∉ filledHull K`, and the punctured unbounded
  component of `Kᶜ` maps into the complementary component of `0`.
* `IsClosed.image_inv_sub_inter_connectedComponentIn_nonempty`: if `A` meets every connected
  component of `Kᶜ` and `a₀ ∉ filledHull K`, then `(fun z ↦ (z - a₀)⁻¹) '' (A \ {a₀})` meets
  every bounded complementary component of `(fun z ↦ (z - a₀)⁻¹) '' K`.
-/

public section

open Bornology Filter Metric Set Topology

namespace TauCeti

/-- Under inversion `z ↦ (z - a₀)⁻¹` about a point `a₀` in the unbounded complementary component of
a closed set `K ⊆ ℂ`, the image of `connectedComponentIn Kᶜ a₀ \ {a₀}` lies in the unbounded
component of `((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ`, which also contains `0`; hence
`0 ∉ filledHull ((fun z ↦ (z - a₀)⁻¹) '' K)`. -/
theorem _root_.IsClosed.zero_notMem_filledHull_image_inv_sub {K : Set ℂ} {a₀ : ℂ} (hK : IsClosed K)
    (ha₀ : a₀ ∉ filledHull K) :
    0 ∉ filledHull ((fun z ↦ (z - a₀)⁻¹) '' K) ∧
      (fun z ↦ (z - a₀)⁻¹) '' (connectedComponentIn Kᶜ a₀ \ {a₀}) ⊆
        connectedComponentIn ((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ 0 := by
  let φ : ℂ → ℂ := fun z ↦ (z - a₀)⁻¹
  set D := connectedComponentIn Kᶜ a₀
  have ha₀K : a₀ ∉ K := fun h ↦ ha₀ (subset_filledHull h)
  have h0K' : (0 : ℂ) ∉ φ '' K := by
    rintro ⟨z, hzK, h0⟩
    exact inv_ne_zero (sub_ne_zero.mpr fun h : z = a₀ ↦ ha₀K (h ▸ hzK)) h0
  have hD_open : IsOpen D := hK.isOpen_compl.connectedComponentIn
  have hD_sdiff_preconn : IsPreconnected (D \ {a₀}) :=
    isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank Complex.one_lt_rank_real hD_open
      isPreconnected_connectedComponentIn isClosed_singleton (Set.finite_singleton a₀).isDiscrete
  have hImg_sub : φ '' (D \ {a₀}) ⊆ (φ '' K)ᶜ :=
    (image_mono (sdiff_subset.trans (connectedComponentIn_subset Kᶜ a₀))).trans
      (Set.image_compl_subset (inv_sub_injective a₀))
  have hD_sdiff_unbdd : ¬ IsBounded (D \ {a₀}) := fun hbd ↦
    (mem_filledHull_iff.not.mp ha₀) <| (hbd.insert a₀).subset fun z hz ↦ by
      by_cases hza : z = a₀
      · simp [hza]
      · exact Or.inr ⟨hz, hza⟩
  have h0_cl : (0 : ℂ) ∈ closure (φ '' (D \ {a₀})) := by
    rw [closure_image_inv_sub hD_sdiff_unbdd]
    exact mem_insert 0 _
  have hD_sub : φ '' (D \ {a₀}) ⊆ connectedComponentIn (φ '' K)ᶜ 0 :=
    (subset_insert 0 _).trans <|
      ((hD_sdiff_preconn.image φ
          ((continuousOn_inv_sub_compl_singleton a₀).mono fun _ hz ↦ hz.2)).subset_closure
        (subset_insert _ _) (insert_subset h0_cl subset_closure)).subset_connectedComponentIn
        (mem_insert 0 _) (insert_subset h0K' hImg_sub)
  have ha₀_cl : a₀ ∈ closure (D \ {a₀}) := mem_closure_iff_nhds.mpr fun U hU ↦ by
    obtain ⟨z, ⟨hzU, hzD⟩, hza⟩ :=
      (inferInstance : (𝓝[≠] a₀).NeBot).nonempty_of_mem <|
        Filter.inter_mem
          (nhdsWithin_le_nhds
            (Filter.inter_mem hU (hD_open.mem_nhds (mem_connectedComponentIn ha₀K))))
          self_mem_nhdsWithin
    exact ⟨z, hzU, hzD, hza⟩
  have hImg_unbdd : ¬ IsBounded (φ '' (D \ {a₀})) :=
    fun hb ↦ (isBounded_image_inv_sub_iff (U := D \ {a₀}) fun h ↦ h.2 rfl).mp hb ha₀_cl
  exact ⟨mem_filledHull_iff.not.mpr fun hbd ↦ hImg_unbdd (hbd.subset hD_sub), hD_sub⟩

/-- If `A` meets every connected component of `Kᶜ` for a closed set `K ⊆ ℂ` and `a₀ ∉ filledHull K`,
then under the Möbius inversion `z ↦ (z - a₀)⁻¹` the set `(fun z ↦ (z - a₀)⁻¹) '' (A \ {a₀})`
meets every bounded connected component of `((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ`. -/
theorem _root_.IsClosed.image_inv_sub_inter_connectedComponentIn_nonempty {K A : Set ℂ} {a₀ : ℂ}
    (hK : IsClosed K) (ha₀ : a₀ ∉ filledHull K)
    (hA : ∀ x ∈ Kᶜ, (A ∩ connectedComponentIn Kᶜ x).Nonempty) :
    ∀ w ∈ filledHull ((fun z ↦ (z - a₀)⁻¹) '' K) \ ((fun z ↦ (z - a₀)⁻¹) '' K),
      ((fun z ↦ (z - a₀)⁻¹) '' (A \ {a₀}) ∩
        connectedComponentIn ((fun z ↦ (z - a₀)⁻¹) '' K)ᶜ w).Nonempty := by
  let φ : ℂ → ℂ := fun z ↦ (z - a₀)⁻¹
  obtain ⟨h0_not, hD_sub⟩ := hK.zero_notMem_filledHull_image_inv_sub ha₀
  rintro w ⟨hwH, hwK'⟩
  have hw0 : w ≠ 0 := fun h ↦ h0_not (h ▸ hwH)
  set x : ℂ := a₀ + w⁻¹
  have hxa₀ : x ≠ a₀ := fun h ↦ inv_ne_zero hw0 (by simpa [x] using h)
  have hφx : φ x = w := by simp [φ, x]
  have hxK : x ∈ Kᶜ := fun hxK ↦ hwK' ⟨x, hxK, hφx⟩
  have ha₀_not_comp : a₀ ∉ connectedComponentIn Kᶜ x := by
    intro hmem
    have hxD : x ∈ connectedComponentIn Kᶜ a₀ :=
      (connectedComponentIn_eq hmem).symm ▸ mem_connectedComponentIn hxK
    have hw0c : w ∈ connectedComponentIn (φ '' K)ᶜ 0 := hD_sub ⟨x, ⟨hxD, hxa₀⟩, hφx⟩
    exact h0_not (mem_filledHull_iff.mpr <|
      (connectedComponentIn_eq hw0c).symm ▸ mem_filledHull_iff.mp hwH)
  obtain ⟨b, hbA, hbc⟩ := hA x hxK
  have hba₀ : b ≠ a₀ := fun h ↦ ha₀_not_comp (h ▸ hbc)
  have himg_sub : φ '' connectedComponentIn Kᶜ x ⊆ (φ '' K)ᶜ :=
    (image_mono (connectedComponentIn_subset Kᶜ x)).trans
      (Set.image_compl_subset (inv_sub_injective a₀))
  have hcomp_sub : φ '' connectedComponentIn Kᶜ x ⊆ connectedComponentIn (φ '' K)ᶜ w :=
    (isPreconnected_connectedComponentIn.image φ
      ((continuousOn_inv_sub_compl_singleton a₀).mono
        fun _ hz hza ↦ ha₀_not_comp (hza ▸ hz))).subset_connectedComponentIn
      ⟨x, mem_connectedComponentIn hxK, hφx⟩ himg_sub
  exact ⟨φ b, ⟨b, ⟨hbA, hba₀⟩, rfl⟩, hcomp_sub ⟨b, hbc, rfl⟩⟩

end TauCeti
