/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Topology.Covering.LocalPower

import Mathlib.Topology.DiscreteSubset
import TauCeti.Topology.IsLocalHomeomorph.Basic

/-!
# Branched covers of topological surfaces and their degree

A *branched cover* of topological surfaces, possibly with boundary, is a continuous surjection
`p : X → Y` with finite fibres that is a covering map off a finite set `B` of marked interior
values, carries boundary exactly onto boundary as a local homeomorphism, and is locally the power
map `w ↦ w ^ e x` in topological charts at every interior point `x`
(`TauCeti.IsLocalPowerAt`), with exponent `e x = 1` off the fibres over `B` and on the boundary.
No smooth or complex structure is involved: the charts of the power-map models are merely
homeomorphisms onto open subsets of `ℂ`. Surfaces are charted on the half-plane model
`EuclideanHalfSpace 2`, with boundary `(𝓡∂ 2).boundary`.

The exponent counts preimages: near `x`, every value near `p x` other than `p x` has exactly `e x`
preimages (`TauCeti.IsBranchedCover.exists_ncard_inter_preimage_eq`), both at interior points,
by `TauCeti.IsLocalPowerAt.exists_ncard_inter_preimage_eq`, and at boundary points, where `p` is a
local homeomorphism. So the exponents are positive and determined by `p`, independently of the
marked set (`TauCeti.IsBranchedCover.unique`).

Over a connected base, with a compact Hausdorff total space and a Hausdorff base, the fibre count
weighted by the exponents is a positive constant, the *degree*
(`TauCeti.IsBranchedCover.exists_degree`). The proof adds up the local counts over a fibre
(`IsClosedMap.eventually_ncard_preimage_eq_finsum`): the map is closed, so the preimages of a
nearby unmarked value lie close to the fibre, and there the weighted count is a raw count. This is
the degree in the topological Riemann–Hurwitz formula.

## Main definitions

* `TauCeti.IsBranchedCover p B e`: `p` is a branched cover of surfaces with marked values `B` and
  exponents `e`.

## Main results

* `TauCeti.IsBranchedCover.ne_zero`, `TauCeti.IsBranchedCover.unique`: the exponents are positive
  and determined by `p`.
* `TauCeti.IsBranchedCover.finite_preimage`: the fibres over the marked values are finite.
* `TauCeti.IsBranchedCover.sum_eq_ncard`: over an unmarked value the weighted count is the number
  of preimages.
* `TauCeti.IsBranchedCover.isLocallyConstant_sum`: the weighted fibre count is locally constant.
* `TauCeti.IsBranchedCover.exists_degree`: over a connected base it is a positive constant.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §4 (the multiplicity of a map as a local preimage count, and Theorem 4.24, the constancy of the
  weighted fibre count of a proper map).
-/

public section

open Set Topology Filter

open scoped Manifold

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
  [TopologicalSpace Y] [ChartedSpace (EuclideanHalfSpace 2) Y]

/-- A **branched cover** of topological surfaces with marked interior values `B` and exponents `e`:
a continuous surjection with finite fibres that restricts to a covering map over the complement of
`B`, satisfies `p⁻¹(∂Y) = ∂X` and is a local homeomorphism along `∂X`, and is locally the power map
`w ↦ w ^ e x`, in topological charts into `ℂ` centred at `x` and `p x`, at every interior point `x`
(`TauCeti.IsLocalPowerAt`), with `e = 1` off `p⁻¹(B)` and on the boundary.

The exponents are positive (`TauCeti.IsBranchedCover.ne_zero`) and determined by `p`
(`TauCeti.IsBranchedCover.unique`). -/
structure IsBranchedCover (p : X → Y) (B : Finset Y) (e : X → ℕ) : Prop where
  /-- A branched cover is continuous. -/
  continuous : Continuous p
  /-- A branched cover is surjective. -/
  surjective : Function.Surjective p
  /-- The fibres of a branched cover are finite. -/
  finite_fibers : ∀ y, (p ⁻¹' {y}).Finite
  /-- The marked values are interior points. -/
  branch_values_interior : (B : Set Y) ⊆ (𝓡∂ 2).interior Y
  /-- The boundary of the source is the preimage of the boundary of the target. -/
  preimage_boundary : p ⁻¹' (𝓡∂ 2).boundary Y = (𝓡∂ 2).boundary X
  /-- Off the marked values, a branched cover is a covering map. -/
  covering_off_branch : IsCoveringMap (((B : Set Y)ᶜ).restrictPreimage p)
  /-- The exponent is `1` off the fibres over the marked values. -/
  local_degree_one_off_branch : ∀ x, p x ∉ B → e x = 1
  /-- At an interior point `x`, a branched cover is locally the power map of exponent `e x`. -/
  local_power : ∀ x ∈ (𝓡∂ 2).interior X, IsLocalPowerAt p x (e x)
  /-- Along the boundary, a branched cover is a local homeomorphism. -/
  boundary_unramified : IsLocalHomeomorphOn p ((𝓡∂ 2).boundary X)
  /-- The exponent is `1` on the boundary. -/
  local_degree_one_boundary : ∀ x ∈ (𝓡∂ 2).boundary X, e x = 1

namespace IsBranchedCover

variable {p : X → Y} {B : Finset Y} {e : X → ℕ}

/-- **The exponent counts preimages.** Inside any neighbourhood `N` of `x` there is an open
neighbourhood `V` of `x` such that every value `y ≠ p x` close enough to `p x` has exactly `e x`
preimages in `V`. -/
theorem exists_ncard_inter_preimage_eq (hp : IsBranchedCover p B e) (x : X) {N : Set X}
    (hN : N ∈ 𝓝 x) :
    ∃ V ⊆ N, IsOpen V ∧ x ∈ V ∧ ∀ᶠ y in 𝓝[≠] p x, (V ∩ p ⁻¹' {y}).ncard = e x := by
  rcases (𝓡∂ 2).isInteriorPoint_or_isBoundaryPoint x with hx | hx
  · exact (hp.local_power x hx).exists_ncard_inter_preimage_eq hN
  · obtain ⟨V, hVN, hVo, hxV, hV⟩ := hp.boundary_unramified.exists_ncard_inter_preimage_eq hx hN
    rw [hp.local_degree_one_boundary x hx]
    exact ⟨V, hVN, hVo, hxV, nhdsWithin_le_nhds hV⟩

/-- The exponents of a branched cover are positive. -/
theorem ne_zero (hp : IsBranchedCover p B e) (x : X) : e x ≠ 0 := by
  rcases (𝓡∂ 2).isInteriorPoint_or_isBoundaryPoint x with hx | hx
  · exact (hp.local_power x hx).ne_zero
  · simp [hp.local_degree_one_boundary x hx]

/-- **The exponents are determined by the map**: two exponent functions exhibiting `p` as a
branched cover, possibly with different marked values, agree. -/
theorem unique {B' : Finset Y} {e' : X → ℕ} (hp : IsBranchedCover p B e)
    (hp' : IsBranchedCover p B' e') : e = e' := by
  funext x
  rcases (𝓡∂ 2).isInteriorPoint_or_isBoundaryPoint x with hx | hx
  · exact (hp.local_power x hx).unique (hp'.local_power x hx)
  · rw [hp.local_degree_one_boundary x hx, hp'.local_degree_one_boundary x hx]

/-- The points over the marked values form a finite set, a finite union of finite fibres. -/
theorem finite_preimage (hp : IsBranchedCover p B e) : (p ⁻¹' (B : Set Y)).Finite :=
  B.finite_toSet.preimage' fun y _ => hp.finite_fibers y

/-- Over an unmarked value every exponent is `1`, so the weighted fibre count is the number of
preimages. -/
theorem sum_eq_ncard (hp : IsBranchedCover p B e) {y : Y} (hy : y ∉ B) :
    ∑ x ∈ (hp.finite_fibers y).toFinset, e x = (p ⁻¹' {y}).ncard := by
  rw [ncard_eq_toFinset_card _ (hp.finite_fibers y), Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun x hx => hp.local_degree_one_off_branch x ?_
  rwa [(hp.finite_fibers y).mem_toFinset.1 hx]

/-- **The weighted fibre count is locally constant**, for a compact Hausdorff source and a
Hausdorff target: near `y`, every unmarked value other than `y` has as many preimages as the
exponents over `y` add up to. -/
theorem isLocallyConstant_sum [T2Space X] [T2Space Y] [CompactSpace X]
    (hp : IsBranchedCover p B e) :
    IsLocallyConstant fun y => ∑ x ∈ (hp.finite_fibers y).toFinset, e x := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
  have hcount := hp.continuous.isClosedMap.eventually_ncard_preimage_eq_finsum hp.finite_fibers
    fun x (hx : p x = y) _ hN => by
      rw [← hx]
      exact hp.exists_ncard_inter_preimage_eq x hN
  have hB : ∀ᶠ y' in 𝓝[≠] y, y' ∉ B :=
    nhdsNE_le_codiscrete y B.finite_toSet.compl_mem_codiscrete
  filter_upwards [eventually_nhdsWithin_iff.1 (hcount.and hB)] with y' hy'
  rcases eq_or_ne y' y with rfl | hne
  · rfl
  obtain ⟨hc, hy'B⟩ := hy' hne
  rw [hp.sum_eq_ncard hy'B, hc, finsum_mem_eq_finite_toFinset_sum _ (hp.finite_fibers y)]

/-- **The degree of a branched cover.** For a compact Hausdorff source and a connected Hausdorff
target, the fibre count weighted by the exponents is a positive constant `d`. -/
theorem exists_degree [T2Space X] [T2Space Y] [CompactSpace X] [ConnectedSpace Y]
    (hp : IsBranchedCover p B e) :
    ∃ d : ℕ, 0 < d ∧ ∀ y, ∑ x ∈ (hp.finite_fibers y).toFinset, e x = d := by
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  obtain ⟨x₀, rfl⟩ := hp.surjective y₀
  refine ⟨_, ?_, fun y => hp.isLocallyConstant_sum.apply_eq_of_preconnectedSpace y (p x₀)⟩
  exact (Nat.pos_of_ne_zero (hp.ne_zero x₀)).trans_le <| Finset.single_le_sum
    (fun _ _ => Nat.zero_le _) ((hp.finite_fibers (p x₀)).mem_toFinset.2 rfl)

end IsBranchedCover

end TauCeti
