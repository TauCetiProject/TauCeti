/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.SimplyConnected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.AlgebraicTopology.Singular.PuncturedSphereCover
import TauCeti.Topology.ConnectedComponents

/-!
# A crosscut has at most two sides

If `γ` is a crosscut of a connected open set `U ⊆ ℂ`, then `U \ range γ` has at most two
connected components. With the existence half `Path.IsCrosscut.not_isPreconnected_sdiff_range`,
this shows that a crosscut of a simply connected domain cuts it into exactly two components, its
two sides. Every point off the crosscut lies on one of the two sides, which is what the nesting
condition of a prime-end chain compares.

Simple connectivity is not needed for the upper bound: a radial segment across an annulus is a
crosscut that leaves the annulus connected.

## The argument

Move to the Riemann sphere through Mathlib's stereographic homeomorphism
`onePointEquivSphereOfFinrankEq : OnePoint ℂ ≃ₜ S²`. There the image `A` of `U` and the complement
`B` of the closed crosscut are open and path-connected: the complement of an arc in `S²` has
vanishing reduced homology (`TauCeti.isZero_reducedSingularHomologyFunctor_sphere_compl_range_cube`,
Hatcher, Proposition 2B.1(a)). The crosscut meets the complement of `U` exactly in its two
endpoints, so `A ∪ B` is the sphere with these two points removed, and `A ∩ B` is the image of
`U \ range γ`. By `TauCeti.enatCard_zerothHomotopy_inter_le_two`, which rests on the
Mayer–Vietoris sequence, `A ∩ B` has at most two path components.

## Main results

* `Path.IsCrosscut.enatCard_connectedComponents_sdiff_range_le_two` — a crosscut of a connected open
  set cuts it into at most two components.
* `Path.IsCrosscut.connectedComponentIn_eq_or_eq_of_separatesIn` — if a crosscut separates `z`
  from `w`, every point off the crosscut lies in the component of `z` or in that of `w`.
* `Path.IsCrosscut.natCard_connectedComponents_sdiff_range_eq_two` — a crosscut of a simply
  connected open set cuts it into exactly two components.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Chapter 2.
* A. Hatcher, *Algebraic Topology*, Section 2.2 and Proposition 2B.1.
-/

public section

open Metric Set Topology TauCeti CategoryTheory
open scoped unitInterval OnePoint

namespace Path

variable {x y : ℂ} {γ : Path x y} {U : Set ℂ}

/-- **A crosscut has at most two sides.** If `γ` is a crosscut of a preconnected open set
`U ⊆ ℂ`, then `U \ range γ` has at most two connected components. -/
theorem IsCrosscut.enatCard_connectedComponents_sdiff_range_le_two (hγ : IsCrosscut γ U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) :
    ENat.card (ConnectedComponents ↥(U \ range γ)) ≤ 2 := by
  -- The stereographic embedding of the plane into the unit sphere of `ℝ³`.
  let e : OnePoint ℂ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  set ι : ℂ → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := e ∘ (↑)
  have hι : IsOpenEmbedding ι := e.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
  -- The crosscut meets the complement of `U` exactly in its endpoints.
  have hγU : range γ \ U = {x, y} := by
    rw [← hγ.range_inter_frontier hUo, hUo.frontier_eq, ← inter_sdiff_assoc,
      inter_eq_left.2 hγ.range_subset_closure]
  set A := ι '' U
  set B := (ι '' range γ)ᶜ
  have hA : IsOpen A := hι.isOpenMap _ hUo
  have hB : IsOpen B :=
    ((isCompact_range γ.continuous).image hι.continuous).isClosed.isOpen_compl
  have hAc : IsPathConnected A :=
    (hUo.isConnected_iff_isPathConnected.1 ⟨closure_nonempty_iff.1
      ⟨x, frontier_subset_closure hγ.source_mem_frontier⟩, hUc⟩).image hι.continuous
  have hBc : IsPathConnected B := by
    -- The crosscut is an embedded interval `(Fin 1 → I) ≃ I`, whose complement in the sphere has
    -- vanishing reduced homology, and is therefore path-connected.
    have hev : Function.Surjective fun f : Fin 1 → I ↦ f 0 := fun t ↦ ⟨fun _ ↦ t, rfl⟩
    have hg : range (ι ∘ γ ∘ fun f : Fin 1 → I ↦ f 0) = ι '' range γ := by
      rw [range_comp, hev.range_comp]
    have hz := isZero_reducedSingularHomologyFunctor_sphere_compl_range_cube (ModuleCat.of ℚ ℚ)
      (hι.continuous.comp (γ.continuous.comp (continuous_apply (0 : Fin 1))))
      (hι.injective.comp (hγ.injective.comp fun (f g : Fin 1 → I) hfg ↦ funext fun i ↦ by
        rwa [Subsingleton.elim i 0])) 0
    rw [hg] at hz
    have : Nonempty ↥B := ⟨⟨e ∞, fun ⟨z, _, hz⟩ ↦ OnePoint.coe_ne_infty z (e.injective hz)⟩⟩
    exact isPathConnected_iff_pathConnectedSpace.2
      (pathConnectedSpace_of_isZero_reducedSingularHomologyFunctor_zero (K := ℚ) hz)
  have hAB : A ∪ B = {ι x, ι y}ᶜ := by
    rw [← image_pair, ← hγU, image_sdiff hι.injective, Set.compl_sdiff]
  have hle := enatCard_zerothHomotopy_inter_le_two (by simp) hA hB hAc hBc
    (hι.injective.ne hγ.source_ne_target) hAB
  have hABD : A ∩ B = ι '' (U \ range γ) := by
    rw [image_sdiff hι.injective, Set.sdiff_eq]
  rw [hABD] at hle
  -- Pass from path components of the image to connected components of `U \ range γ`.
  let φ := (hι.isEmbedding.homeomorphImage (U \ range γ)).symm
  have h₁ := ENat.card_le_card_of_injective (Function.injective_surjInv
    (φ.continuous.connectedComponentsMap_surjective φ.surjective))
  have h₂ := ENat.card_le_card_of_injective (Function.injective_surjInv
    (ZerothHomotopy.toConnectedComponents_surjective (X := ↥(ι '' (U \ range γ)))))
  exact h₁.trans (h₂.trans hle)

/-- **Every point off a crosscut lies on one of its two sides.** If a crosscut `γ` of a
preconnected open set `U ⊆ ℂ` separates `z` from `w`, then each point of `U \ range γ` lies in the
connected component of `z` or in that of `w`. -/
theorem IsCrosscut.connectedComponentIn_eq_or_eq_of_separatesIn (hγ : IsCrosscut γ U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) {z w v : ℂ} (hzw : γ.SeparatesIn U z w)
    (hv : v ∈ U \ range γ) :
    connectedComponentIn (U \ range γ) v = connectedComponentIn (U \ range γ) z ∨
      connectedComponentIn (U \ range γ) v = connectedComponentIn (U \ range γ) w := by
  obtain ⟨hz, hw, hzw⟩ := (separatesIn_def γ U z w).1 hzw
  by_contra! h
  -- Otherwise `v`, `z` and `w` would give three distinct components of the cut set.
  have hvz := mt (ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq hv hz).1 h.1
  have hvw := mt (ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq hv hw).1 h.2
  replace hzw := mt (ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq hz hw).1 hzw
  have hinj : Function.Injective ![ConnectedComponents.mk (⟨v, hv⟩ : ↥(U \ range γ)),
      .mk ⟨z, hz⟩, .mk ⟨w, hw⟩] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have := (ENat.card_le_card_of_injective hinj).trans
    (hγ.enatCard_connectedComponents_sdiff_range_le_two hUo hUc)
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at this
  exact absurd this (by decide)

/-- **A crosscut of a simply connected domain has exactly two sides.** If `γ` is a crosscut of a
simply connected open set `U ⊆ ℂ`, then `U \ range γ` has exactly two connected components. -/
theorem IsCrosscut.natCard_connectedComponents_sdiff_range_eq_two (hγ : IsCrosscut γ U)
    (hUo : IsOpen U) (hUs : IsSimplyConnected U) :
    Nat.card (ConnectedComponents ↥(U \ range γ)) = 2 := by
  have hle := hγ.enatCard_connectedComponents_sdiff_range_le_two hUo
    hUs.isPathConnected.isConnected.isPreconnected
  have : Finite (ConnectedComponents ↥(U \ range γ)) :=
    ENat.card_lt_top.1 (hle.trans_lt (by decide))
  -- By `Path.IsCrosscut.not_isPreconnected_sdiff_range`, there are at least two components.
  obtain ⟨z, w, hzw⟩ := hγ.exists_separatesIn hUo hUs
  obtain ⟨hz, hw, hzw⟩ := (separatesIn_def γ U z w).1 hzw
  have : Nontrivial (ConnectedComponents ↥(U \ range γ)) :=
    ⟨_, _, mt (ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq hz hw).1 hzw⟩
  have hlt := (ENat.one_lt_card_iff_nontrivial _).2 this
  rw [ENat.card_eq_coe_natCard] at hle hlt
  norm_cast at hle hlt
  omega

end Path
