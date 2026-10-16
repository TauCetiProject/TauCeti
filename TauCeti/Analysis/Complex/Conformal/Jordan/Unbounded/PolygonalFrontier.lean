/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded

import Mathlib.Analysis.Convex.PathConnected
import TauCeti.Topology.LocallyConnected

/-!
# Inverted polygonal frontiers are locally connected

The frontier of a polygonal domain with several vertices at infinity, such as a strip, is a
finite union of closed segments and closed rays. On the Riemann sphere such a frontier can pass
through infinity several times, as the two boundary lines of a strip do, and then it is not a
Jordan curve; so local connectedness is proved here without the Jordan property. Inverting the
domain about an exterior point `q`, `z ↦ (z - q)⁻¹`, gives a bounded domain whose frontier is the
inverted frontier together with `0`, the image of infinity. Each inverted segment is an arc,
and each inverted ray, closed up by `0`, is an arc ending at `0`. A finite union of arcs is
locally connected, so the inverted frontier is locally connected.

This is the boundary hypothesis of Carathéodory's continuity theorem for the inverted domain, in
the form required by
`TauCeti.exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub`. Together
they give an unbounded simply connected domain with such a frontier an upper-half-plane Riemann map
whose inverted coordinate is continuous on the closed half-plane.

## Main statements

* `TauCeti.locallyConnectedSpace_insert_zero_image_inv_sub_union_segment_ray`: a finite union of
  closed segments and closed rays avoiding `q`, inverted about `q` and closed up by `0`, is locally
  connected.
* `TauCeti.locallyConnectedSpace_frontier_image_inv_sub_of_frontier_eq`: an unbounded open set
  whose frontier is a finite union of closed segments and closed rays has locally connected
  frontier after inversion about a point outside its closure.
* `TauCeti.continuousOn_inv_sub_lineMap`, `TauCeti.insert_zero_image_inv_sub_ray_eq`,
  `TauCeti.continuousOn_div_ray`: continuous parametrizations by `[0, 1]` of an inverted closed
  segment and of an inverted closed ray closed up by `0`.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Set

namespace TauCeti

variable {q : ℂ}

/-- The inverted affine parametrization of a closed segment avoiding `q` is continuous on
`[0, 1]`. -/
theorem continuousOn_inv_sub_lineMap {x y : ℂ} (hq : q ∉ segment ℝ x y) :
    ContinuousOn (fun s : ℝ => (AffineMap.lineMap x y s - q)⁻¹) (Icc 0 1) := by
  refine ContinuousOn.inv₀ (by fun_prop) fun s hs h => hq ?_
  rw [segment_eq_image_lineMap]
  exact ⟨s, hs, (sub_eq_zero.mp h)⟩

/-- On a closed ray `p + t * d`, `t ≥ 0`, the inverted point at parameter `t = (1 - s) / s` is
`s / (s * (p - q) + (1 - s) * d)`. -/
private theorem div_eq_inv_sub_ray {p d : ℂ} {s : ℝ} (hs : s ≠ 0) :
    (s : ℂ) / (s * (p - q) + (1 - s) * d) = (p + (((1 - s) / s : ℝ) : ℂ) * d - q)⁻¹ := by
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
  rw [← inv_div]
  congr 1
  push_cast
  field_simp
  ring

/-- Inverting a closed ray avoiding `q` about `q` and adding `0`, the image of its point at
infinity, gives the image of `[0, 1]` under `s ↦ s / (s * (p - q) + (1 - s) * d)`. -/
theorem insert_zero_image_inv_sub_ray_eq {p d : ℂ} :
    insert 0 ((fun z : ℂ => (z - q)⁻¹) '' ((fun t : ℝ => p + (t : ℂ) * d) '' Ici 0)) =
      (fun s : ℝ => (s : ℂ) / (s * (p - q) + (1 - s) * d)) '' Icc 0 1 := by
  refine Subset.antisymm (insert_subset ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩ ?_) ?_
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have ht' : (0 : ℝ) < 1 + t := by linarith [mem_Ici.mp ht]
    refine ⟨(1 + t)⁻¹, ⟨inv_nonneg.mpr ht'.le, inv_le_one_of_one_le₀ (by linarith [mem_Ici.mp ht])⟩,
      ?_⟩
    simp only
    rw [div_eq_inv_sub_ray (inv_ne_zero ht'.ne')]
    congr 4
    field_simp
    simp
  · rintro _ ⟨s, hs, rfl⟩
    rcases eq_or_lt_of_le hs.1 with rfl | hs0
    · simp
    refine mem_insert_of_mem _ ⟨_, ⟨(1 - s) / s, ?_, rfl⟩, (div_eq_inv_sub_ray hs0.ne').symm⟩
    exact div_nonneg (by linarith [hs.2]) hs0.le

/-- The parametrization `s ↦ s / (s * (p - q) + (1 - s) * d)` of an inverted closed ray avoiding
`q` is continuous on `[0, 1]`: its denominator is `d ≠ 0` at `s = 0`, and `s` times a nonzero
difference `p + t * d - q` for `s > 0`. -/
theorem continuousOn_div_ray {p d : ℂ} (hd : d ≠ 0)
    (hq : q ∉ (fun t : ℝ => p + (t : ℂ) * d) '' Ici 0) :
    ContinuousOn (fun s : ℝ => (s : ℂ) / (s * (p - q) + (1 - s) * d)) (Icc 0 1) := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs h => ?_
  rcases eq_or_lt_of_le hs.1 with rfl | hs0
  · simp [hd] at h
  refine hq ⟨(1 - s) / s, div_nonneg (by linarith [hs.2]) hs0.le, ?_⟩
  have h' := div_eq_inv_sub_ray (q := q) (p := p) (d := d) hs0.ne'
  rw [h, div_zero, eq_comm, inv_eq_zero, sub_eq_zero] at h'
  exact h'

/-- **Inverted segments and rays are locally connected.** Let `S` be the union of finitely many
closed segments `[x i, y i]` and finitely many closed rays `p k + t * d k`, `t ≥ 0`, `d k ≠ 0`, and
let `q ∉ S`. Then the inversion of `S` about `q`, together with `0`, the image of infinity, is
locally connected: it is a finite union of arcs, the inverted rays all ending at `0`. -/
theorem locallyConnectedSpace_insert_zero_image_inv_sub_union_segment_ray {ι κ : Type*}
    [Finite ι] [Finite κ] (x y : ι → ℂ) (p d : κ → ℂ) (hd : ∀ k, d k ≠ 0)
    (hq : q ∉ (⋃ i, segment ℝ (x i) (y i)) ∪ ⋃ k, (fun t : ℝ => p k + (t : ℂ) * d k) '' Ici 0) :
    LocallyConnectedSpace (insert (0 : ℂ) ((fun z : ℂ => (z - q)⁻¹) ''
      ((⋃ i, segment ℝ (x i) (y i)) ∪ ⋃ k, (fun t : ℝ => p k + (t : ℂ) * d k) '' Ici 0)) :
        Set ℂ) := by
  -- one arc for each segment, one for each ray, and the point `0` in case there is no ray
  let γ : Option (ι ⊕ κ) → ℝ → ℂ
    | none => fun _ => 0
    | some (.inl i) => fun s => (AffineMap.lineMap (x i) (y i) s - q)⁻¹
    | some (.inr k) => fun s => (s : ℂ) / (s * (p k - q) + (1 - s) * d k)
  have hγ : ∀ j, ContinuousOn (γ j) (Icc 0 1)
    | none => continuousOn_const
    | some (.inl i) => continuousOn_inv_sub_lineMap fun h =>
        hq (mem_union_left _ (mem_iUnion_of_mem i h))
    | some (.inr k) => continuousOn_div_ray (hd k) fun h =>
        hq (mem_union_right _ (mem_iUnion_of_mem k h))
  have heq : insert 0 ((fun z : ℂ => (z - q)⁻¹) ''
      ((⋃ i, segment ℝ (x i) (y i)) ∪ ⋃ k, (fun t : ℝ => p k + (t : ℂ) * d k) '' Ici 0)) =
      ⋃ j, γ j '' Icc 0 1 := by
    simp only [iUnion_option, iUnion_sum, γ, segment_eq_image_lineMap, image_image,
      ← insert_zero_image_inv_sub_ray_eq, (nonempty_Icc.mpr zero_le_one).image_const,
      image_union, image_iUnion]
    ext w
    simp only [mem_insert_iff, mem_union, mem_singleton_iff, mem_iUnion]
    -- the point `0` lies on every closed-up inverted ray, and is listed once more on its own
    constructor
    · rintro (h | h | ⟨k, h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨k, Or.inr h⟩)
    · rintro (h | h | ⟨k, h | h⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨k, h⟩)
  have := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  rw [heq]
  exact locallyConnectedSpace_iUnion_image_of_isCompact isCompact_Icc hγ

/-- **Polygonal frontiers are locally connected after inversion.** Let `U` be an unbounded open
set whose frontier is the union of finitely many closed segments `[x i, y i]` and finitely many
closed rays `p k + t * d k`, `t ≥ 0`, `d k ≠ 0`, and let `q ∉ closure U`. Then the inversion of `U`
about `q` has locally connected frontier, even when `U` has several ends at infinity. -/
theorem locallyConnectedSpace_frontier_image_inv_sub_of_frontier_eq {ι κ : Type*} [Finite ι]
    [Finite κ] {U : Set ℂ} (hUo : IsOpen U) (hq : q ∉ closure U) (hUb : ¬IsBounded U)
    {x y : ι → ℂ} {p d : κ → ℂ} (hd : ∀ k, d k ≠ 0)
    (hU : frontier U =
      (⋃ i, segment ℝ (x i) (y i)) ∪ ⋃ k, (fun t : ℝ => p k + (t : ℂ) * d k) '' Ici 0) :
    LocallyConnectedSpace (frontier ((fun z : ℂ => (z - q)⁻¹) '' U)) := by
  rw [frontier_image_inv_sub hUo hq hUb, hU]
  exact locallyConnectedSpace_insert_zero_image_inv_sub_union_segment_ray x y p d hd
    (hU ▸ fun h => hq (frontier_subset_closure h))

end TauCeti
