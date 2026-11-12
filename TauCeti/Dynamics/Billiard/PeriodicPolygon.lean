/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Calculus.Deriv.PeriodicSegment
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# Periodic billiard polygons by perimeter maximization

Let `χ : ℝ → F` be a differentiable `L`-periodic curve, `L > 0`, in a real inner product space,
whose derivative vanishes nowhere. For the boundary of a convex billiard table, parametrized by
arclength, a closed billiard trajectory with `N` bounces is a closed polygon with vertices
`χ(s_k)`, `k ∈ ℤ/N`, obeying the reflection law at each vertex: the incoming and the outgoing
chords make equal angles with the tangent line. This file proves, by perimeter maximization (the
variational step of Birkhoff's argument), that such polygons exist for every `N ≥ 2`
(`TauCeti.exists_billiard_periodic_reflection`): there are
`s_k` with `χ(s_(k+1)) ≠ χ(s_k)` and

`⟪u_(k-1), χ'(s_k)⟫ = ⟪u_k, χ'(s_k)⟫` for every `k`,

where `u_k` is the unit vector from `χ(s_k)` to `χ(s_(k+1))`. Nonconsecutive vertices may
coincide, and the least period of the polygon may be a proper divisor of `N`. The rotation number
is not controlled, so this is not Birkhoff's theorem on periodic orbits of every rotation number
`p/N`: for even `N` the polygon can be a double normal traversed `N / 2` times, as for the
doubled diameter of a circle.

The polygons are the maximizers of the inscribed perimeter
`P(s) = ∑ₖ ‖χ(s_(k+1)) - χ(s_k)‖` (`TauCeti.inscribedPerimeter`). It is continuous and
`L`-periodic in each vertex parameter, so it has a global maximum
(`TauCeti.exists_isMaxOn_inscribedPerimeter`). At a maximizer no two consecutive vertices
coincide (`TauCeti.apply_add_one_ne_of_isMaxOn_inscribedPerimeter`). Indeed, if
`χ(s_(k-1)) = χ(s_k)`, maximality in the parameter `s_k` alone gives
`‖χ(t) - χ(s_(k-1))‖ + ‖χ(s_(k+1)) - χ(t)‖ ≤ ‖χ(s_(k+1)) - χ(s_(k-1))‖` for every `t`, so by the
equality case of the triangle inequality the whole curve lies in the segment between
`χ(s_(k-1))` and `χ(s_(k+1))`. A closed curve in a segment turns back at the maximum of its
coordinate along the segment, where its derivative vanishes, which is excluded. With the
consecutive vertices distinct, each term of `P` is differentiable, and Fermat's rule in the
parameter `s_k` is the reflection law (`TauCeti.inner_eq_inner_of_isMaxOn_inscribedPerimeter`).
For `N = 2` it says that the chord is orthogonal to the curve at both ends: every such curve has
a double normal (`TauCeti.exists_double_normal`).

Neither convexity of the curve nor injectivity of the parametrization is used. For the boundary
of a bounded strictly convex planar table, positively oriented and parametrized by arclength,
these polygons are closed orbits of the billiard map; for a general curve the chords of the
polygon need not stay on one side of it.

## Main results

* `TauCeti.exists_isMaxOn_inscribedPerimeter`: the inscribed perimeter has a global maximum.
* `TauCeti.apply_add_one_ne_of_isMaxOn_inscribedPerimeter`: at a maximizer, consecutive vertices
  are distinct.
* `TauCeti.inner_eq_inner_of_isMaxOn_inscribedPerimeter`: at a maximizer, the reflection law holds
  at every vertex that is distinct from its neighbours and where the curve is differentiable.
* `TauCeti.exists_billiard_periodic_reflection`: periodic billiard polygons with `N` vertices, for
  every `N ≥ 2`.
* `TauCeti.exists_double_normal`: a chord orthogonal to the curve at both of its endpoints.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (periodic billiard trajectories as critical inscribed polygons).
* G. D. Birkhoff, *Dynamical Systems*, American Mathematical Society Colloquium Publications 9,
  1927, Chapter VI (periodic billiard orbits by perimeter maximization).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 6 (Birkhoff periodic trajectories).
-/

public section

noncomputable section

open Function Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] {χ : ℝ → F} {L : ℝ} {N : ℕ} [NeZero N]

/-- The perimeter `∑ₖ ‖χ(s_(k+1)) - χ(s_k)‖` of the closed polygon inscribed in the curve `χ`
with vertices `χ(s_k)`, `k ∈ ℤ/N`. -/
def inscribedPerimeter (χ : ℝ → F) (s : ZMod N → ℝ) : ℝ :=
  ∑ k, ‖χ (s (k + 1)) - χ (s k)‖

theorem inscribedPerimeter_def (χ : ℝ → F) (s : ZMod N → ℝ) :
    inscribedPerimeter χ s = ∑ k, ‖χ (s (k + 1)) - χ (s k)‖ :=
  (rfl)

/-- The inscribed perimeter depends only on the vertices `χ(s_k)`. -/
theorem inscribedPerimeter_congr {s s' : ZMod N → ℝ} (h : ∀ k, χ (s k) = χ (s' k)) :
    inscribedPerimeter χ s = inscribedPerimeter χ s' := by
  simp only [inscribedPerimeter_def, h]

theorem continuous_inscribedPerimeter (hχ : Continuous χ) :
    Continuous (inscribedPerimeter (N := N) χ) :=
  continuous_finsetSum _ fun _ _ ↦
    ((hχ.comp (continuous_apply _)).sub (hχ.comp (continuous_apply _))).norm

/-- For at least two vertices, moving the vertex `j` to `χ(t)` changes the inscribed perimeter only
in the two sides at `χ(s_j)`. -/
theorem inscribedPerimeter_update (hN : 2 ≤ N) (s : ZMod N → ℝ) (j : ZMod N) (t : ℝ) :
    inscribedPerimeter χ (update s j t) = inscribedPerimeter χ s -
      (‖χ (s j) - χ (s (j - 1))‖ + ‖χ (s (j + 1)) - χ (s j)‖) +
      (‖χ t - χ (s (j - 1))‖ + ‖χ (s (j + 1)) - χ t‖) := by
  have : Fact (1 < N) := ⟨hN⟩
  have h1 : j - 1 ≠ j := by simp
  have h2 : j + 1 ≠ j := by simp
  -- Split off the two sides `j - 1` and `j` at the vertex `j`; the other sides do not change.
  have hsplit (r : ZMod N → ℝ) : inscribedPerimeter χ r =
      ‖χ (r (j - 1 + 1)) - χ (r (j - 1))‖ + ‖χ (r (j + 1)) - χ (r j)‖ +
        ∑ k ∈ (Finset.univ.erase j).erase (j - 1), ‖χ (r (k + 1)) - χ (r k)‖ := by
    rw [inscribedPerimeter_def, ← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨h1, Finset.mem_univ _⟩)]
    ring
  have hrest : ∑ k ∈ (Finset.univ.erase j).erase (j - 1),
      ‖χ (update s j t (k + 1)) - χ (update s j t k)‖ =
      ∑ k ∈ (Finset.univ.erase j).erase (j - 1), ‖χ (s (k + 1)) - χ (s k)‖ := by
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    obtain ⟨hk1, hk2⟩ : k ≠ j - 1 ∧ k ≠ j := by simpa using hk
    rw [update_of_ne hk2, update_of_ne fun h ↦ hk1 (eq_sub_of_add_eq h)]
  rw [hsplit, hsplit s, hrest, sub_add_cancel, update_self, update_of_ne h1, update_of_ne h2]
  ring

/-- The inscribed perimeter of a continuous periodic curve has a global maximum. -/
theorem exists_isMaxOn_inscribedPerimeter (hχ : Continuous χ) (hper : Periodic χ L)
    (hL : 0 < L) : ∃ s : ZMod N → ℝ, IsMaxOn (inscribedPerimeter χ) univ s := by
  -- Maximize over the compact box `[0, L]^N`, and reduce every parameter into `[0, L)`.
  obtain ⟨s, -, hs⟩ := (isCompact_univ_pi fun _ : ZMod N ↦ isCompact_Icc).exists_isMaxOn
    ⟨fun _ ↦ 0, fun _ _ ↦ ⟨le_rfl, hL.le⟩⟩ (continuous_inscribedPerimeter hχ).continuousOn
    (f := inscribedPerimeter χ) (s := univ.pi fun _ ↦ Icc 0 L)
  refine ⟨s, isMaxOn_iff.2 fun r _ ↦ ?_⟩
  have hr : inscribedPerimeter χ r = inscribedPerimeter χ fun k ↦ toIcoMod hL 0 (r k) :=
    inscribedPerimeter_congr fun k ↦ by simp only [toIcoMod, hper.sub_zsmul_eq]
  rw [hr]
  exact isMaxOn_iff.1 hs _ fun k _ ↦
    Ico_subset_Icc_self (by simpa using toIcoMod_mem_Ico hL 0 (r k))

section NormedSpace

variable [NormedSpace ℝ F]

/-- **Consecutive vertices of a perimeter maximizer are distinct.** For a differentiable periodic
curve with nowhere vanishing derivative in a strictly convex real normed space, and at least two
vertices, two consecutive vertices of an inscribed polygon of maximal perimeter never coincide. -/
theorem apply_add_one_ne_of_isMaxOn_inscribedPerimeter [StrictConvexSpace ℝ F]
    (hχ : Differentiable ℝ χ) (hper : Periodic χ L) (hL : 0 < L) (hχ' : ∀ t, deriv χ t ≠ 0)
    (hN : 2 ≤ N)
    {s : ZMod N → ℝ} (hs : IsMaxOn (inscribedPerimeter χ) univ s) (k : ZMod N) :
    χ (s (k + 1)) ≠ χ (s k) := by
  intro hk
  -- Moving the vertex `j = k + 1` does not increase the perimeter, so the curve lies in the
  -- segment between the neighbours `χ(s_k)` and `χ(s_(k+2))` of that vertex.
  set j := k + 1
  have hj : j - 1 = k := add_sub_cancel_right k 1
  refine (hper.exists_notMem_segment hL hχ hχ' (χ (s k)) (χ (s (j + 1)))).elim fun t ht ↦ ht ?_
  have hle := isMaxOn_iff.1 hs (update s j t) (mem_univ _)
  rw [inscribedPerimeter_update hN, hj, hk, sub_self, norm_zero, zero_add] at hle
  rw [mem_segment_iff_wbtw, ← dist_add_dist_eq_iff]
  refine le_antisymm ?_ (dist_triangle _ _ _)
  simp only [dist_eq_norm]
  linarith [norm_sub_rev (χ (s k)) (χ t), norm_sub_rev (χ t) (χ (s (j + 1))),
    norm_sub_rev (χ (s k)) (χ (s (j + 1)))]

end NormedSpace

variable [InnerProductSpace ℝ F]

/-- **The reflection law at a perimeter maximizer.** For at least two vertices, an inscribed
polygon of maximal perimeter obeys the reflection law at each vertex `χ(s_k)` that is distinct from
its two neighbours and where the curve is differentiable: the unit vectors `u_(k-1)` and `u_k`
along the incoming and the outgoing sides have the same component along the tangent vector
`χ'(s_k)`. -/
theorem inner_eq_inner_of_isMaxOn_inscribedPerimeter (hN : 2 ≤ N) {s : ZMod N → ℝ}
    (hs : IsMaxOn (inscribedPerimeter χ) univ s) {k : ZMod N} (hχ : DifferentiableAt ℝ χ (s k))
    (hk₁ : χ (s k) ≠ χ (s (k - 1))) (hk₂ : χ (s (k + 1)) ≠ χ (s k)) :
    ⟪‖χ (s k) - χ (s (k - 1))‖⁻¹ • (χ (s k) - χ (s (k - 1))), deriv χ (s k)⟫ =
      ⟪‖χ (s (k + 1)) - χ (s k)‖⁻¹ • (χ (s (k + 1)) - χ (s k)), deriv χ (s k)⟫ := by
  have h₁ : χ (s k) - χ (s (k - 1)) ≠ 0 := sub_ne_zero.2 hk₁
  have h₂ : χ (s (k + 1)) - χ (s k) ≠ 0 := sub_ne_zero.2 hk₂
  -- Moving only the vertex `k`, the perimeter is a constant plus the lengths of its two sides.
  set g : ℝ → ℝ := fun t ↦ ‖χ t - χ (s (k - 1))‖ + ‖χ (s (k + 1)) - χ t‖
  have hmax : IsLocalMax g (s k) := by
    refine IsMaxOn.isLocalMax (s := univ) (isMaxOn_iff.2 fun t _ ↦ ?_) Filter.univ_mem
    have h := isMaxOn_iff.1 hs (update s k t) (mem_univ _)
    rw [inscribedPerimeter_update hN] at h
    simp only [g]
    linarith
  -- Fermat's rule for `g` at `s k` is the reflection law.
  have hd₁ := (hasFDerivAt_norm_of_ne h₁).comp_hasDerivAt (s k)
    (hχ.hasDerivAt.sub_const (χ (s (k - 1))))
  have hd₂ := (hasFDerivAt_norm_of_ne h₂).comp_hasDerivAt (s k)
    (hχ.hasDerivAt.const_sub (χ (s (k + 1))))
  have h0 := hmax.hasDerivAt_eq_zero (hd₁.add hd₂)
  simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul] at h0
  rw [real_inner_smul_left, real_inner_smul_left]
  rw [inner_neg_right] at h0
  linarith

omit [NeZero N] in
/-- **Periodic billiard polygons by perimeter maximization.** Let `χ` be a differentiable
`L`-periodic curve, `L > 0`, in a real inner product space, with nowhere vanishing derivative. For
every `N ≥ 2` there are parameters `s_k`, `k ∈ ℤ/N`, such that consecutive vertices `χ(s_k)` and
`χ(s_(k+1))` are distinct and the reflection law holds at every vertex: with `u_k` the unit vector
from `χ(s_k)` to `χ(s_(k+1))`, `⟪u_(k-1), χ'(s_k)⟫ = ⟪u_k, χ'(s_k)⟫`. For the arclength
parametrization of the boundary of a strictly convex planar table, these are closed billiard
trajectories with `N` bounces, whose least period divides `N`. The rotation number is not
controlled: for even `N` the polygon can be a double normal traversed `N / 2` times. -/
theorem exists_billiard_periodic_reflection (hχ : Differentiable ℝ χ) (hper : Periodic χ L)
    (hL : 0 < L) (hχ' : ∀ t, deriv χ t ≠ 0) (hN : 2 ≤ N) :
    ∃ s : ZMod N → ℝ, ∀ k, χ (s (k + 1)) ≠ χ (s k) ∧
      ⟪‖χ (s k) - χ (s (k - 1))‖⁻¹ • (χ (s k) - χ (s (k - 1))), deriv χ (s k)⟫ =
        ⟪‖χ (s (k + 1)) - χ (s k)‖⁻¹ • (χ (s (k + 1)) - χ (s k)), deriv χ (s k)⟫ := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨s, hs⟩ := exists_isMaxOn_inscribedPerimeter hχ.continuous hper hL (N := N)
  have hne := apply_add_one_ne_of_isMaxOn_inscribedPerimeter hχ hper hL hχ' hN hs
  exact ⟨s, fun k ↦ ⟨hne k, inner_eq_inner_of_isMaxOn_inscribedPerimeter hN hs (hχ (s k))
    (by simpa only [sub_add_cancel] using hne (k - 1)) (hne k)⟩⟩

omit [NeZero N] in
/-- **Double normals.** A differentiable periodic curve with nowhere vanishing derivative has a
chord, between distinct points `χ(a)` and `χ(b)`, that is orthogonal to the curve at both of its
endpoints. This is the case `N = 2` of `TauCeti.exists_billiard_periodic_reflection`: a billiard
trajectory bouncing back and forth along one chord. -/
theorem exists_double_normal (hχ : Differentiable ℝ χ) (hper : Periodic χ L) (hL : 0 < L)
    (hχ' : ∀ t, deriv χ t ≠ 0) :
    ∃ a b, χ a ≠ χ b ∧ ⟪χ b - χ a, deriv χ a⟫ = 0 ∧ ⟪χ b - χ a, deriv χ b⟫ = 0 := by
  obtain ⟨s, hs⟩ := exists_billiard_periodic_reflection hχ hper hL hχ' (N := 2) le_rfl
  -- In `ℤ/2`, `k - 1 = k + 1`, so the two sides at a vertex are the same chord, reversed.
  have h (k : ZMod 2) : ⟪χ (s (k + 1)) - χ (s k), deriv χ (s k)⟫ = 0 := by
    have hk := (hs k).2
    have hk' : k - 1 = k + 1 := (by decide : ∀ k : ZMod 2, k - 1 = k + 1) k
    rw [hk', ← neg_sub (χ (s (k + 1))), norm_neg, smul_neg, inner_neg_left,
      real_inner_smul_left] at hk
    have hpos : 0 < ‖χ (s (k + 1)) - χ (s k)‖⁻¹ :=
      inv_pos.2 (norm_pos_iff.2 (sub_ne_zero.2 (hs k).1))
    nlinarith [hk, hpos]
  refine ⟨s 0, s 1, (hs 0).1.symm, by simpa using h 0, ?_⟩
  have h1 := h 1
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [h11, ← neg_sub, inner_neg_left, neg_eq_zero] at h1
  exact h1

end TauCeti
