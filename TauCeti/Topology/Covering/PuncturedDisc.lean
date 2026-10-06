/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CoveringMap
public import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Cyclic

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.Topology.IsLocalHomeomorph

/-!
# The finite connected covers of the punctured disc

Let `𝔻* = ball 0 1 \ {0}` be the punctured unit disc in `ℂ`. For `e ≠ 0` the power map
`z ↦ z ^ e` sends `𝔻*` onto itself, and it is a covering map with `e` sheets: the fibre over `w`
is the set of `e`-th roots of `w`. This is the local model of a branched cover near a point of
ramification index `e`.

Conversely, every connected cover of `𝔻*` with `e ≠ 0` sheets is isomorphic over `𝔻*` to this
model. The fundamental group of `𝔻*` is infinite cyclic, so a connected cover of `𝔻*` is
determined up to isomorphism by its number of sheets
(`IsCoveringMap.exists_homeomorph_comp_eq_of_card_fiber_eq`). The isomorphism can moreover be
chosen to carry any given point over `w` to any given `e`-th root of `w`; it is therefore not
unique, but only unique up to the rotations of `𝔻*` by `e`-th roots of unity.

## Main declarations

* `TauCeti.pow_mem_ball_zero_one_diff_singleton_iff`: for `e ≠ 0`, `z ^ e` lies in the punctured
  unit ball exactly when `z` does.
* `TauCeti.puncturedDiscPow`: the map `z ↦ z ^ e` from `𝔻*` to itself, for `e ≠ 0`.
* `TauCeti.puncturedDiscPow_mul`: the power maps compose, `z ^ (e * f) = (z ^ f) ^ e`.
* `TauCeti.isCoveringMap_puncturedDiscPow`: it is a covering map.
* `TauCeti.card_puncturedDiscPow_preimage_singleton`: each of its fibres has `e` points.
* `IsCoveringMap.exists_homeomorph_puncturedDiscPow_comp_eq`: **a connected cover of `𝔻*`
  with `e ≠ 0` sheets is isomorphic over `𝔻*` to `z ↦ z ^ e`**, by an isomorphism matching any
  given points of the two fibres over a point.
* `IsCoveringMap.exists_homeomorph_puncturedDiscPow_comp_eq_iff`: a connected cover of `𝔻*` is
  isomorphic over `𝔻*` to `z ↦ z ^ e` exactly when it has `e` sheets.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §5, Theorem 5.10 (a finite cover of the punctured disc with `k` sheets is `z ↦ z ^ k`).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (the classification of
  covering spaces).
-/

public section

noncomputable section

open Metric Set

namespace TauCeti

variable {e : ℕ}

/-- For `e ≠ 0`, `z ^ e` lies in the punctured unit ball exactly when `z` does. -/
theorem pow_mem_ball_zero_one_diff_singleton_iff {𝕜 : Type*} [NormedDivisionRing 𝕜] (he : e ≠ 0)
    {z : 𝕜} : z ^ e ∈ ball (0 : 𝕜) 1 \ {0} ↔ z ∈ ball (0 : 𝕜) 1 \ {0} := by
  simp [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg z) he, he]

/-- The **power map** `z ↦ z ^ e` from the punctured unit disc `ball 0 1 \ {0}` to itself, for
`e ≠ 0`. -/
def puncturedDiscPow (he : e ≠ 0) : C(↥(ball (0 : ℂ) 1 \ {0}), ↥(ball (0 : ℂ) 1 \ {0})) where
  toFun z := ⟨(z : ℂ) ^ e, (pow_mem_ball_zero_one_diff_singleton_iff he).2 z.2⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_puncturedDiscPow_apply (he : e ≠ 0) (z : ↥(ball (0 : ℂ) 1 \ {0})) :
    (puncturedDiscPow he z : ℂ) = (z : ℂ) ^ e :=
  (rfl)

/-- The first power map of the punctured disc is the identity. -/
@[simp]
theorem puncturedDiscPow_one : puncturedDiscPow one_ne_zero = ContinuousMap.id _ := by
  ext
  simp

/-- The power maps of the punctured disc compose: `z ↦ z ^ (e * f)` is `z ↦ z ^ e` after
`z ↦ z ^ f`. -/
theorem puncturedDiscPow_mul {f : ℕ} (he : e ≠ 0) (hf : f ≠ 0) :
    puncturedDiscPow (mul_ne_zero he hf) = (puncturedDiscPow he).comp (puncturedDiscPow hf) := by
  ext
  simp [pow_mul']

/-- **The power map of the punctured disc is a covering map.** It is the restriction of the
covering map `z ↦ z ^ e` of `ℂ \ {0}` to the preimage of the punctured disc, which is the punctured
disc itself. -/
theorem isCoveringMap_puncturedDiscPow (he : e ≠ 0) : IsCoveringMap (puncturedDiscPow he) := by
  have hs : (· ^ e) ⁻¹' (ball (0 : ℂ) 1 \ {0}) = ball (0 : ℂ) 1 \ {0} :=
    Set.ext fun _ => pow_mem_ball_zero_one_diff_singleton_iff he
  -- `Homeomorph.setCongr` does not move the point and `Set.restrictPreimage_mk` applies the power
  -- map, so the composite below is `puncturedDiscPow he` by definition.
  exact (((isCoveringMapOn_npow (𝕜 := ℂ) e (Nat.cast_ne_zero.2 he)).mono
    fun _ hz => hz.2).isCoveringMap_restrictPreimage).comp_homeomorph (.setCongr hs.symm)

/-- **The power map of the punctured disc has `e` sheets:** the fibre over any point `w` consists
of the `e` distinct `e`-th roots of `w`. -/
theorem card_puncturedDiscPow_preimage_singleton (he : e ≠ 0) (w : ↥(ball (0 : ℂ) 1 \ {0})) :
    Nat.card (puncturedDiscPow he ⁻¹' {w}) = e := by
  classical
  have hζ := Complex.isPrimitiveRoot_exp e he
  have himage : Subtype.val '' (puncturedDiscPow he ⁻¹' {w}) =
      (Polynomial.nthRootsFinset e (w : ℂ) : Set ℂ) := by
    ext z
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero he)]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← coe_puncturedDiscPow_apply he, Set.mem_singleton_iff.1 hz]
    · intro hz
      refine ⟨⟨z, (pow_mem_ball_zero_one_diff_singleton_iff he).1 (hz ▸ w.2)⟩, ?_, rfl⟩
      exact Set.mem_singleton_iff.2 (Subtype.ext hz)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (w : ℂ) (Nat.pos_of_ne_zero he)
  rw [← Nat.card_image_of_injective Subtype.val_injective, himage, Nat.card_coe_set_eq,
    Set.ncard_coe_finset, hζ.card_nthRootsFinset_of_pow_eq hα w.2.2]

variable {E : Type*} [TopologicalSpace E] [ConnectedSpace E] {p : E → ↥(ball (0 : ℂ) 1 \ {0})}

/-- **Every finite connected cover of the punctured disc is a power map.** Let `p : E → 𝔻*` be a
covering map from a connected space whose fibre over `w` has `e ≠ 0` points. Then `p` is
isomorphic over `𝔻*` to `z ↦ z ^ e`, by a homeomorphism `E ≃ₜ 𝔻*` carrying any given point `y₀`
over `w` to any given `e`-th root `z₀` of `w`. -/
theorem _root_.IsCoveringMap.exists_homeomorph_puncturedDiscPow_comp_eq (hp : IsCoveringMap p)
    (he : e ≠ 0) {w : ↥(ball (0 : ℂ) 1 \ {0})} (hcard : Nat.card (p ⁻¹' {w}) = e)
    (y₀ : p ⁻¹' {w}) (z₀ : puncturedDiscPow he ⁻¹' {w}) :
    ∃ h : E ≃ₜ ↥(ball (0 : ℂ) 1 \ {0}), h y₀ = z₀ ∧ puncturedDiscPow he ∘ h = p := by
  have := pathConnectedSpace_ball_diff_singleton (0 : ℂ) one_pos
  have : LocallyPathConnectedSpace ↥(ball (0 : ℂ) 1 \ {0}) :=
    (isOpen_ball.sdiff isClosed_singleton).locallyPathConnectedSpace
  have : LocallyPathConnectedSpace E := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : PathConnectedSpace E := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  have := ((convex_ball (0 : ℂ) 1).starConvex (mem_ball_self one_pos)
    ).isCyclic_fundamentalGroup_diff_singleton (r := 1 / 2) (by norm_num)
    (sphere_subset_ball (by norm_num)) w
  exact hp.exists_homeomorph_comp_eq_of_card_fiber_eq (isCoveringMap_puncturedDiscPow he) y₀ z₀
    (by rw [hcard, card_puncturedDiscPow_preimage_singleton])

/-- **The finite connected covers of the punctured disc are classified by their degree.** A
covering map `p : E → 𝔻*` from a connected space is isomorphic over `𝔻*` to `z ↦ z ^ e`, for
`e ≠ 0`, exactly when its fibre over some (equivalently, every) point `w` has `e` points. -/
theorem _root_.IsCoveringMap.exists_homeomorph_puncturedDiscPow_comp_eq_iff (hp : IsCoveringMap p)
    (he : e ≠ 0) (w : ↥(ball (0 : ℂ) 1 \ {0})) :
    (∃ h : E ≃ₜ ↥(ball (0 : ℂ) 1 \ {0}), puncturedDiscPow he ∘ h = p) ↔
      Nat.card (p ⁻¹' {w}) = e := by
  refine ⟨fun ⟨h, hcomp⟩ => ?_, fun hcard => ?_⟩
  · rw [← card_puncturedDiscPow_preimage_singleton he w]
    exact Nat.card_congr <| h.toEquiv.subtypeEquiv fun y => by simp [← hcomp]
  · have : Nonempty (p ⁻¹' {w}) := (Nat.card_pos_iff.1 (hcard ▸ Nat.pos_of_ne_zero he)).1
    have : Nonempty (puncturedDiscPow he ⁻¹' {w}) := (Nat.card_pos_iff.1
      ((card_puncturedDiscPow_preimage_singleton he w).symm ▸ Nat.pos_of_ne_zero he)).1
    exact (hp.exists_homeomorph_puncturedDiscPow_comp_eq he hcard (Classical.arbitrary _)
      (Classical.arbitrary _)).imp fun _ h => h.2

end TauCeti
