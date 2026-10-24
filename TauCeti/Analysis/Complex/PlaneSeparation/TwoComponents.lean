/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.PlaneSeparation.RiemannSphere

/-!
# The Jordan curve theorem in the plane

A Jordan curve `C ⊆ ℂ` has exactly two complementary components: its **inside**
`filledHull C \ C`, which is bounded, open and connected, and its **outside**
`(filledHull C)ᶜ`, which is unbounded and connected. Both have frontier `C`.

The count comes from the Riemann sphere, where the complement of a Jordan curve has exactly two
components (`TauCeti.IsJordanCurve.natCard_connectedComponents_compl_eq_two_onePoint`, from the
Jordan–Brouwer separation theorem). View `C` in `OnePoint ℂ`. A bounded component `U` of `Cᶜ`
has compact closure `U ∪ C`, so its image is open in the sphere and closed in the complement of
the curve. It is therefore a whole component there, one that misses `∞`. Two different bounded
components of `Cᶜ` would thus give, together with the component of `∞`, three components of the
complement of the curve in the sphere. So the inside is a single component. The outside is a
single component for every bounded subset of the plane
(`TauCeti.connectedComponentIn_compl_eq_compl_filledHull`).

## Main results

* `TauCeti.IsJordanCurve.filledHull_sdiff_eq_connectedComponentIn`: **the Jordan curve
  theorem**: the inside of a Jordan curve is a single component of its complement.
* `TauCeti.IsJordanCurve.isConnected_filledHull_sdiff`: the inside of a Jordan curve is
  connected.
* `TauCeti.IsJordanCurve.frontier_filledHull_sdiff`: the frontier of the inside is the curve.
* `TauCeti.IsJordanCurve.connectedComponentIn_eq_filledHull_sdiff_or_eq_compl_filledHull`:
  every complementary component is the inside or the outside.
* `TauCeti.IsJordanCurve.natCard_connectedComponents_compl_eq_two`: the complement of a Jordan
  curve has exactly two connected components.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.B, Corollary 2B.2.
* J. R. Munkres, *Topology*, §63.
-/

public section

namespace TauCeti

open Bornology Metric Set Topology
open scoped OnePoint

/-- The component of a point inside a Jordan curve `C ⊆ ℂ`, in the complement of the curve on the
Riemann sphere, lies in the image of the component of the point in `Cᶜ`. -/
private theorem IsJordanCurve.connectedComponentIn_compl_image_coe_subset {C : Set ℂ}
    (hC : IsJordanCurve C) {x : ℂ} (hx : x ∈ filledHull C \ C) :
    connectedComponentIn ((↑) '' C : Set (OnePoint ℂ))ᶜ ↑x ⊆
      (↑) '' connectedComponentIn Cᶜ x := by
  set U := connectedComponentIn Cᶜ x
  have hUo : IsOpen U := hC.isClosed.isOpen_compl.connectedComponentIn
  -- the closure of `U` is the compact set `U ∪ C`, so the image of `U` is closed off the curve
  have hcl : closure ((↑) '' U : Set (OnePoint ℂ)) ⊆ (↑) '' U ∪ (↑) '' C := by
    refine (closure_minimal (image_mono subset_closure)
      ((mem_filledHull_iff.mp hx.1).isCompact_closure.image
        OnePoint.continuous_coe).isClosed).trans ?_
    rw [← image_union, closure_eq_self_union_frontier, hC.frontier_connectedComponentIn hx.2]
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
    (OnePoint.isOpenEmbedding_coe.isOpenMap U hUo) ⟨↑x, mem_connectedComponentIn ?_,
      mem_image_of_mem _ (mem_connectedComponentIn hx.2)⟩ fun z ⟨hzU, hz⟩ => ?_
  · rintro ⟨w, hw, hwx⟩
    exact hx.2 (OnePoint.coe_injective hwx ▸ hw)
  · exact (hcl hzU).resolve_right (connectedComponentIn_subset _ _ hz)

/-- **The Jordan curve theorem.** The inside `filledHull C \ C` of a Jordan curve `C ⊆ ℂ` is a
single component of `Cᶜ`: it is the component of any of its points. -/
theorem IsJordanCurve.filledHull_sdiff_eq_connectedComponentIn {C : Set ℂ}
    (hC : IsJordanCurve C) {x : ℂ} (hx : x ∈ filledHull C \ C) :
    filledHull C \ C = connectedComponentIn Cᶜ x := by
  refine Subset.antisymm (fun y hy => ?_) fun y hy =>
    ⟨by rw [mem_filledHull_iff, ← connectedComponentIn_eq hy]; exact mem_filledHull_iff.mp hx.1,
      connectedComponentIn_subset _ _ hy⟩
  by_contra hxy
  set J : Set (OnePoint ℂ) := (↑) '' C
  have hJ : IsJordanCurve J :=
    hC.image OnePoint.continuous_coe.continuousOn OnePoint.coe_injective.injOn
  have hcard := hJ.natCard_connectedComponents_compl_eq_two_onePoint
  have : Finite (ConnectedComponents ↥Jᶜ) := Nat.finite_of_card_ne_zero (by omega)
  have hnot : ∀ {z : ℂ}, z ∉ C → (z : OnePoint ℂ) ∈ Jᶜ :=
    fun hz ⟨w, hw, hwz⟩ => hz (OnePoint.coe_injective hwz ▸ hw)
  have hinf : (∞ : OnePoint ℂ) ∈ Jᶜ := by simp [J]
  have hne : ∀ {u v : OnePoint ℂ} (hu : u ∈ Jᶜ) (hv : v ∈ Jᶜ), v ∉ connectedComponentIn Jᶜ u →
      ConnectedComponents.mk (⟨u, hu⟩ : ↥Jᶜ) ≠ .mk ⟨v, hv⟩ := by
    intro u v hu hv huv h
    rw [connectedComponentIn_eq_image hu, ConnectedComponents.coe_eq_coe.mp h] at huv
    exact huv ⟨⟨v, hv⟩, mem_connectedComponent, rfl⟩
  -- `↑x`, `↑y` and `∞` lie in three different components of `Jᶜ`
  have hxy' : (y : OnePoint ℂ) ∉ connectedComponentIn Jᶜ ↑x := fun h => by
    obtain ⟨w, hw, hwy⟩ := hC.connectedComponentIn_compl_image_coe_subset hx h
    exact hxy (OnePoint.coe_injective hwy ▸ hw)
  have hxinf : (∞ : OnePoint ℂ) ∉ connectedComponentIn Jᶜ ↑x := fun h => by
    obtain ⟨w, -, hw⟩ := hC.connectedComponentIn_compl_image_coe_subset hx h
    exact OnePoint.coe_ne_infty w hw
  have hyinf : (∞ : OnePoint ℂ) ∉ connectedComponentIn Jᶜ ↑y := fun h => by
    obtain ⟨w, -, hw⟩ := hC.connectedComponentIn_compl_image_coe_subset hy h
    exact OnePoint.coe_ne_infty w hw
  have h3 := ncard_le_ncard (subset_univ ({.mk ⟨↑x, hnot hx.2⟩, .mk ⟨↑y, hnot hy.2⟩,
    .mk ⟨∞, hinf⟩} : Set (ConnectedComponents ↥Jᶜ)))
  rw [ncard_univ, hcard, ncard_eq_three.mpr ⟨_, _, _, hne _ _ hxy', hne _ _ hxinf,
    hne _ _ hyinf, rfl⟩] at h3
  omega

/-- **The inside of a Jordan curve is connected.** -/
theorem IsJordanCurve.isConnected_filledHull_sdiff {C : Set ℂ} (hC : IsJordanCurve C) :
    IsConnected (filledHull C \ C) := by
  obtain ⟨x, hx⟩ := hC.nonempty_filledHull_sdiff
  rw [hC.filledHull_sdiff_eq_connectedComponentIn hx]
  exact isConnected_connectedComponentIn_iff.mpr hx.2

/-- **A Jordan curve bounds its inside**: the frontier of `filledHull C \ C` is `C`. -/
theorem IsJordanCurve.frontier_filledHull_sdiff {C : Set ℂ} (hC : IsJordanCurve C) :
    frontier (filledHull C \ C) = C := by
  obtain ⟨x, hx⟩ := hC.nonempty_filledHull_sdiff
  rw [hC.filledHull_sdiff_eq_connectedComponentIn hx]
  exact hC.frontier_connectedComponentIn hx.2

/-- **Every complementary component of a Jordan curve is its inside or its outside.** For
`z ∉ C`, the component of `z` in `Cᶜ` is either `filledHull C \ C` or `(filledHull C)ᶜ`. -/
theorem IsJordanCurve.connectedComponentIn_eq_filledHull_sdiff_or_eq_compl_filledHull
    {C : Set ℂ} (hC : IsJordanCurve C) {z : ℂ} (hz : z ∉ C) :
    connectedComponentIn Cᶜ z = filledHull C \ C ∨
      connectedComponentIn Cᶜ z = (filledHull C)ᶜ := by
  by_cases hzH : z ∈ filledHull C
  · exact .inl (hC.filledHull_sdiff_eq_connectedComponentIn ⟨hzH, hz⟩).symm
  · refine .inr (connectedComponentIn_compl_eq_compl_filledHull ?_ hC.isCompact.isBounded hzH)
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two

/-- **A Jordan curve in the plane has exactly two complementary components.** -/
theorem IsJordanCurve.natCard_connectedComponents_compl_eq_two {C : Set ℂ}
    (hC : IsJordanCurve C) : Nat.card (ConnectedComponents ↥Cᶜ) = 2 := by
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  -- the inside and the outside, as subsets of `Cᶜ`
  let I : Set ↥Cᶜ := (↑) ⁻¹' (filledHull C \ C)
  let O : Set ↥Cᶜ := (↑) ⁻¹' (filledHull C)ᶜ
  have hIO : Iᶜ = O := by
    ext ⟨z, hz⟩
    simp [I, O]
  have hIo : IsOpen I := hC.isClosed.isOpen_filledHull_sdiff.preimage continuous_subtype_val
  have hOo : IsOpen O :=
    hC.isClosed.isClosed_filledHull.isOpen_compl.preimage continuous_subtype_val
  have hconn : ∀ {S : Set ℂ}, IsConnected S → S ⊆ Cᶜ → IsConnected ((↑) ⁻¹' S : Set ↥Cᶜ) := by
    intro S hS hSC
    obtain ⟨z, hz⟩ := hS.nonempty
    refine ⟨⟨⟨z, hSC hz⟩, hz⟩, IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hSC]
    exact hS.isPreconnected
  let U : Fin 2 → Set ↥Cᶜ := ![I, O]
  have hI : IsClopen I := ⟨by rw [← isOpen_compl_iff, hIO]; exact hOo, hIo⟩
  have hO : IsClopen O := ⟨by rw [← isOpen_compl_iff, ← hIO, compl_compl]; exact hIo, hOo⟩
  have hdisj : Disjoint I O := hIO ▸ disjoint_compl_right
  have e := ConnectedComponents.equivOfIsClopenOfIsConnected (U := U)
    (Fin.forall_fin_two.mpr ⟨hI, hO⟩)
    (fun i j hij => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hdisj
      · exact hdisj.symm
      · exact absurd rfl hij)
    (iUnion_eq_univ_iff.mpr fun z => by
      by_cases hz : z ∈ I
      · exact ⟨0, hz⟩
      · exact ⟨1, (hIO ▸ hz : z ∈ O)⟩)
    (Fin.forall_fin_two.mpr ⟨hconn hC.isConnected_filledHull_sdiff fun z hz => hz.2,
      hconn (isConnected_compl_filledHull hrank hC.isCompact.isBounded)
        fun z hz hzC => hz (subset_filledHull hzC)⟩)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

end TauCeti
