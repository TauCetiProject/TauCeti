/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import TauCeti.Algebra.Module.ZLattice.SuccessiveMinima
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Convex.Gauge
import TauCeti.Topology.MetricSpace.DiscreteAddSubgroup

/-!
# Shortest pairs of a lattice

Let `L` be a discrete `ℤ`-submodule of a real normed space `E`. A *shortest pair* of `L`
(`ZLattice.IsShortestPair L v w`) is a shortest nonzero vector `v` of `L` together with a shortest
vector `w` of `L` off the line `ℝ ∙ v`. Shortest pairs are not unique: the sign of either vector
can be changed, and several vectors can tie for either minimum. The ties are all kept, as the set
`{p | IsShortestPair L p.1 p.2}`. When `E` is finite-dimensional this set is finite
(`ZLattice.finite_setOf_isShortestPair`) and, for a spanning lattice in dimension at least two,
nonempty (`ZLattice.exists_isShortestPair`).

The lengths of a shortest pair are the first two successive minima of `L` for the closed unit
ball, whichever of the tied pairs is chosen (`ZLattice.IsShortestPair.successiveMin_zero` and
`ZLattice.IsShortestPair.successiveMin_one`). In a strictly convex space, such as a real inner
product space, the two vectors of every shortest pair generate the lattice vectors of their plane
(`ZLattice.IsShortestPair.mem_span_of_mem_span`). For a lattice in a plane, every shortest pair is
therefore a `ℤ`-basis of the lattice (`ZLattice.IsShortestPair.span_eq`,
`ZLattice.IsShortestPair.basis`). This is the classical fact behind Lagrange's and Gauss's
reduction of binary quadratic forms: the lattice point `a • v + c • w` with `|a|, |c| ≤ 1 / 2`,
not both zero, would be shorter than `v` or shorter than `w` and off the line `ℝ ∙ v`. Strict
convexity is what makes the triangle inequality `‖a • v + c • w‖ ≤ |a| ‖v‖ + |c| ‖w‖` strict for
independent `v`, `w`. Some lattice basis attaining the first two minima exists for every norm
(`ZLattice.exists_basis_mem_smul_successiveMin`); the content here is that every shortest pair is
such a basis.

A linear map scaling all norms by the same factor `k > 0`, such as multiplication by a nonzero
complex number on `ℂ`, carries the shortest pairs of `L` exactly onto those of the image lattice
(`ZLattice.isShortestPair_map_iff`). For the lattice of parabolic translations of a cusp of a
hyperbolic `3`-manifold, a shortest pair consists of a shortest translation and a shortest
translation independent of it, and the pair does not depend on how the cusp is normalized.

## Main definitions

* `ZLattice.IsShortestPair L v w`: `v` is a shortest nonzero vector of `L` and `w` a shortest
  vector of `L` off the line `ℝ ∙ v`.
* `ZLattice.IsShortestPair.basis`: in dimension two and a strictly convex space, the `ℤ`-basis
  `v, w` of `L` given by a shortest pair.

## Main results

* `ZLattice.exists_isShortestPair` and `ZLattice.finite_setOf_isShortestPair`: in a
  finite-dimensional space, shortest pairs of a spanning lattice exist in dimension at least two,
  and a discrete lattice has finitely many.
* `ZLattice.IsShortestPair.successiveMin_zero`, `ZLattice.IsShortestPair.successiveMin_one`: the
  lengths of every shortest pair are the first two successive minima for the closed unit ball.
* `ZLattice.IsShortestPair.span_eq`: in a strictly convex plane, every shortest pair generates
  the lattice.
* `ZLattice.isShortestPair_map_iff`: shortest pairs are carried along similarities.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959, Chapter II,
  §§1–2 (lattices in the plane, reduced bases and binary quadratic forms).
* C. Adams, M. Hildebrand and J. Weeks, *Hyperbolic invariants of knots and links*, Trans. Amer.
  Math. Soc. 326 (1991), §2 (shortest parabolic translations of a cusp).
-/

public section

open Module Submodule Metric
open scoped Pointwise

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **shortest pair** of `L`: `v` is a shortest nonzero vector of `L`, and `w` is a shortest
vector of `L` among those off the line `ℝ ∙ v`. -/
structure IsShortestPair (L : Submodule ℤ E) (v w : E) : Prop where
  left_mem : v ∈ L
  left_ne_zero : v ≠ 0
  norm_left_le : ∀ x ∈ L, x ≠ 0 → ‖v‖ ≤ ‖x‖
  right_mem : w ∈ L
  right_notMem : w ∉ ℝ ∙ v
  norm_right_le : ∀ x ∈ L, x ∉ ℝ ∙ v → ‖w‖ ≤ ‖x‖

namespace IsShortestPair

variable {L : Submodule ℤ E} {v w : E}

/-- The second vector of a shortest pair is nonzero. -/
theorem right_ne_zero (h : IsShortestPair L v w) : w ≠ 0 := by
  rintro rfl
  exact h.right_notMem (zero_mem _)

/-- The two vectors of a shortest pair are linearly independent over `ℝ`. -/
theorem linearIndependent (h : IsShortestPair L v w) : LinearIndependent ℝ ![v, w] := by
  rw [LinearIndependent.pair_iff' h.left_ne_zero]
  exact fun a ha ↦ h.right_notMem (mem_span_singleton.2 ⟨a, ha⟩)

/-- The first vector of a shortest pair is no longer than the second. -/
theorem norm_left_le_norm_right (h : IsShortestPair L v w) : ‖v‖ ≤ ‖w‖ :=
  h.norm_left_le w h.right_mem h.right_ne_zero

/-- In a shortest pair, the second vector is no longer than any vector of `L` independent of the
first one. -/
theorem norm_right_le_of_linearIndependent (h : IsShortestPair L v w) {x : E} (hx : x ∈ L)
    (hvx : LinearIndependent ℝ ![v, x]) : ‖w‖ ≤ ‖x‖ :=
  h.norm_right_le x hx fun hxv ↦ by
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 hxv
    exact (LinearIndependent.pair_iff' h.left_ne_zero).1 hvx a rfl

/-- The length of a second vector does not depend on the shortest pair: two shortest pairs have
second vectors of the same length. -/
theorem norm_right_eq (h : IsShortestPair L v w) {v' w' : E} (h' : IsShortestPair L v' w') :
    ‖w‖ = ‖w'‖ := by
  -- A second vector of one pair is at most as long as either vector of the other pair that lies
  -- off its line, and at least one of them does.
  have key {v w v' w' : E} (h : IsShortestPair L v w) (h' : IsShortestPair L v' w') :
      ‖w‖ ≤ ‖w'‖ := by
    by_cases hw' : w' ∈ ℝ ∙ v
    · have hv' : v' ∉ ℝ ∙ v := fun hv' ↦ by
        obtain ⟨a, rfl⟩ := mem_span_singleton.1 hv'
        obtain ⟨b, rfl⟩ := mem_span_singleton.1 hw'
        have ha : a ≠ 0 := by
          rintro rfl
          exact h'.left_ne_zero (zero_smul ℝ v)
        exact h'.right_notMem
          (mem_span_singleton.2 ⟨b / a, by rw [smul_smul, div_mul_cancel₀ b ha]⟩)
      exact (h.norm_right_le v' h'.left_mem hv').trans h'.norm_left_le_norm_right
    · exact h.norm_right_le w' h'.right_mem hw'
  exact (key h h').antisymm (key h' h)

/-- The length of a first vector does not depend on the shortest pair. -/
theorem norm_left_eq (h : IsShortestPair L v w) {v' w' : E} (h' : IsShortestPair L v' w') :
    ‖v‖ = ‖v'‖ :=
  (h.norm_left_le v' h'.left_mem h'.left_ne_zero).antisymm
    (h'.norm_left_le v h.left_mem h.left_ne_zero)

/-- Changing the sign of the first vector of a shortest pair gives a shortest pair. -/
theorem neg_left (h : IsShortestPair L v w) : IsShortestPair L (-v) w := by
  have hline : (ℝ ∙ -v) = ℝ ∙ v := by rw [← Set.neg_singleton, span_neg]
  exact ⟨neg_mem h.left_mem, neg_ne_zero.2 h.left_ne_zero,
    fun x hx hx0 ↦ by simpa using h.norm_left_le x hx hx0, h.right_mem, hline ▸ h.right_notMem,
    fun x hx hxv ↦ h.norm_right_le x hx (hline ▸ hxv)⟩

/-- Changing the sign of the second vector of a shortest pair gives a shortest pair. -/
theorem neg_right (h : IsShortestPair L v w) : IsShortestPair L v (-w) where
  left_mem := h.left_mem
  left_ne_zero := h.left_ne_zero
  norm_left_le := h.norm_left_le
  right_mem := neg_mem h.right_mem
  right_notMem := by simpa using h.right_notMem
  norm_right_le x hx hxv := by simpa using h.norm_right_le x hx hxv

/-! ### Shortest pairs generate the lattice -/

section StrictConvex

variable [StrictConvexSpace ℝ E]

/-- In a strictly convex space, the only vector of `L` of the form `a • v + c • w` with
`|a|, |c| ≤ 1 / 2`, for a shortest pair `v, w`, is zero. -/
theorem eq_zero_of_abs_le (h : IsShortestPair L v w) {a c : ℝ} (ha : |a| ≤ 1 / 2)
    (hc : |c| ≤ 1 / 2) (hy : a • v + c • w ∈ L) : a • v + c • w = 0 := by
  by_contra hy0
  have hv := norm_pos_iff.2 h.left_ne_zero
  have hw := norm_pos_iff.2 h.right_ne_zero
  have hvw := h.norm_left_le_norm_right
  rcases eq_or_ne c 0 with rfl | hc0
  · -- Then `a • v` is a nonzero lattice vector shorter than `v`.
    simp only [zero_smul, add_zero] at hy hy0
    have := h.norm_left_le _ hy hy0
    rw [norm_smul, Real.norm_eq_abs] at this
    nlinarith
  · -- Then `a • v + c • w` lies off the line `ℝ ∙ v` and is shorter than `w`.
    have hoff : a • v + c • w ∉ ℝ ∙ v := fun hmem ↦ by
      obtain ⟨t, ht⟩ := mem_span_singleton.1 hmem
      have := (LinearIndependent.pair_iff.1 h.linearIndependent) (a - t) c (by
        rw [sub_smul, ht]
        abel)
      exact hc0 this.2
    have hle := h.norm_right_le _ hy hoff
    have hlt : ‖a • v + c • w‖ < ‖w‖ := by
      rcases eq_or_ne a 0 with rfl | ha0
      · rw [zero_smul, zero_add, norm_smul, Real.norm_eq_abs]
        nlinarith
      · -- The triangle inequality is strict, since `a • v` and `c • w` are independent.
        have hray : ¬SameRay ℝ (a • v) (c • w) := fun hray ↦ by
          obtain ⟨r₁, r₂, hr₁, _, hr⟩ := hray.exists_pos (smul_ne_zero ha0 h.left_ne_zero)
            (smul_ne_zero hc0 h.right_ne_zero)
          have := (LinearIndependent.pair_iff.1 h.linearIndependent) (r₁ * a) (-(r₂ * c)) (by
            rw [neg_smul, ← sub_eq_add_neg, mul_smul, mul_smul, hr, sub_self])
          exact mul_ne_zero hr₁.ne' ha0 this.1
        have := norm_add_lt_of_not_sameRay hray
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at this
        nlinarith [abs_nonneg a, abs_nonneg c]
    exact hlt.not_ge hle

/-- **The lattice vectors in the plane of a shortest pair are its integral combinations.** In a
strictly convex space, a vector of `L` in the real span of a shortest pair `v, w` lies in its
integral span. -/
theorem mem_span_of_mem_span (h : IsShortestPair L v w) {x : E} (hx : x ∈ L)
    (hxvw : x ∈ span ℝ {v, w}) : x ∈ span ℤ {v, w} := by
  obtain ⟨α, β, rfl⟩ := mem_span_pair.1 hxvw
  -- Subtract the nearest integral combination; the remainder has coordinates of size at most
  -- `1 / 2`, so it is zero.
  have hrem : (α - round α) • v + (β - round β) • w =
      α • v + β • w - (round α • v + round β • w) := by
    rw [sub_smul, sub_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    abel
  have hzero := h.eq_zero_of_abs_le (abs_sub_round α) (abs_sub_round β) (by
    rw [hrem]
    exact sub_mem hx (add_mem (zsmul_mem h.left_mem _) (zsmul_mem h.right_mem _)))
  rw [hrem, sub_eq_zero] at hzero
  exact mem_span_pair.2 ⟨round α, round β, hzero.symm⟩

/-- **Every shortest pair of a lattice in a plane is a basis.** In a strictly convex
two-dimensional real normed space, the two vectors of any shortest pair of `L` span `L` over
`ℤ`. -/
theorem span_eq (h : IsShortestPair L v w) (hE : finrank ℝ E = 2) : span ℤ {v, w} = L := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  have htop : span ℝ {v, w} = ⊤ := by
    rw [← Matrix.range_cons_cons_empty]
    exact h.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [hE])
  refine le_antisymm (span_le.2 ?_) fun x hx ↦ h.mem_span_of_mem_span hx (htop ▸ mem_top)
  rintro x (rfl | rfl)
  exacts [h.left_mem, h.right_mem]

/-- The `ℤ`-basis `v, w` of a lattice `L` in a strictly convex plane given by a shortest pair
`v, w` of `L`. -/
noncomputable def basis (h : IsShortestPair L v w) (hE : finrank ℝ E = 2) : Basis (Fin 2) ℤ L :=
  (Basis.span (h.linearIndependent.restrict_scalars' ℤ)).map
    (LinearEquiv.ofEq _ _ (by rw [Matrix.range_cons_cons_empty, h.span_eq hE]))

@[simp]
theorem coe_basis (h : IsShortestPair L v w) (hE : finrank ℝ E = 2) (i : Fin 2) :
    (h.basis hE i : E) = ![v, w] i := by
  simp [basis, Basis.span_apply]

end StrictConvex

end IsShortestPair

/-! ### Existence, finiteness and successive minima -/

section Minima

variable {L : Submodule ℤ E} {K : ConvexBody E}

/-- **Shortest pairs exist.** A discrete lattice spanning a real normed space of dimension at least
two has a shortest pair. -/
theorem exists_isShortestPair (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hE : 1 < finrank ℝ E) : ∃ v w, IsShortestPair L v w := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have hK0 := ConvexBody.zero_mem_interior_of_coe_eq_closedBall
    (ConvexBody.coe_closedUnitBall (E := E))
  have hgauge (x : E) : gauge (ConvexBody.closedUnitBall E : Set E) x = ‖x‖ := by
    rw [ConvexBody.coe_closedUnitBall, gauge_closedBall zero_le_one, div_one]
  -- A shortest vector off the zero subspace, then a shortest vector off its line.
  obtain ⟨v, hvL, hv0, hv⟩ := exists_mem_notMem_forall_gauge_le L hK0 (V := ⊥) (by
    intro h
    have := congrArg (fun V : Submodule ℝ E ↦ finrank ℝ V) h
    simp only [finrank_bot, finrank_top] at this
    omega)
  rw [mem_bot] at hv0
  obtain ⟨w, hwL, hwv, hw⟩ := exists_mem_notMem_forall_gauge_le L hK0 (V := ℝ ∙ v) (by
    intro h
    have := finrank_span_singleton (K := ℝ) hv0
    rw [h, finrank_top] at this
    omega)
  simp only [hgauge, mem_bot] at hv hw
  exact ⟨v, w, ⟨hvL, hv0, hv, hwL, hwv, hw⟩⟩

/-- **The ties are finite.** A discrete lattice in a finite-dimensional real normed space has
finitely many shortest pairs. -/
theorem finite_setOf_isShortestPair [FiniteDimensional ℝ E] (L : Submodule ℤ E)
    [DiscreteTopology L] :
    {p : E × E | IsShortestPair L p.1 p.2}.Finite := by
  rcases Set.eq_empty_or_nonempty {p : E × E | IsShortestPair L p.1 p.2} with hS | ⟨p, hp⟩
  · simp [hS]
  -- Both vectors of every shortest pair lie in `L` and in the ball of radius `‖p.2‖`.
  have hfin := L.toAddSubgroup.finite_inter (isBounded_closedBall (x := (0 : E)) (r := ‖p.2‖))
  refine (hfin.prod hfin).subset fun q hq ↦ ?_
  have hq : IsShortestPair L q.1 q.2 := hq
  have h₂ : ‖q.2‖ = ‖p.2‖ := hq.norm_right_eq hp
  refine ⟨⟨?_, hq.left_mem⟩, ⟨?_, hq.right_mem⟩⟩
  · rw [mem_closedBall_zero_iff, ← h₂]
    exact hq.norm_left_le_norm_right
  · rw [mem_closedBall_zero_iff, h₂]

variable {v w : E}

/-- **The first vector of a shortest pair has the length of the first successive minimum** for
the closed unit ball. -/
theorem IsShortestPair.successiveMin_zero [DiscreteTopology L] [IsZLattice ℝ L]
    (h : IsShortestPair L v w) (hK : (K : Set E) = closedBall 0 1) (hE : 0 < finrank ℝ E) :
    successiveMin L K ⟨0, hE⟩ = ‖v‖ := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos hE
  have hK0 := ConvexBody.zero_mem_interior_of_coe_eq_closedBall hK
  have hball {t : ℝ} (ht : 0 ≤ t) {x : E} : x ∈ t • (K : Set E) ↔ ‖x‖ ≤ t :=
    ConvexBody.mem_smul_iff_norm_le_of_coe_eq_closedBall hK ht
  refine le_antisymm ?_ ?_
  · exact (successiveMin_zero_le_iff L hK0 hE (norm_nonneg v)).2
      ⟨v, h.left_mem, h.left_ne_zero, (hball (norm_nonneg v)).2 le_rfl⟩
  · obtain ⟨x, hxL, hx0, hx⟩ := (successiveMin_zero_le_iff L hK0 hE
      (successiveMin_nonneg L K _)).1 le_rfl
    exact (h.norm_left_le x hxL hx0).trans
      ((hball (successiveMin_nonneg L K _)).1 hx)

/-- **The second vector of a shortest pair has the length of the second successive minimum** for
the closed unit ball. This holds for every shortest pair, whichever of the tied shortest vectors
is its first vector. -/
theorem IsShortestPair.successiveMin_one [DiscreteTopology L] [IsZLattice ℝ L]
    (h : IsShortestPair L v w) (hK : (K : Set E) = closedBall 0 1) (hE : 1 < finrank ℝ E) :
    successiveMin L K ⟨1, hE⟩ = ‖w‖ := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have hK0 := ConvexBody.zero_mem_interior_of_coe_eq_closedBall hK
  have hball {t : ℝ} (ht : 0 ≤ t) {x : E} : x ∈ t • (K : Set E) ↔ ‖x‖ ≤ t :=
    ConvexBody.mem_smul_iff_norm_le_of_coe_eq_closedBall hK ht
  have hw := norm_nonneg w
  refine le_antisymm ?_ ?_
  · -- The independent vectors `v` and `w` both have length at most `‖w‖`.
    refine successiveMin_le hw h.linearIndependent (fun j ↦ ?_) fun j ↦ ?_
    · fin_cases j
      exacts [h.left_mem, h.right_mem]
    · rw [hball hw]
      fin_cases j
      exacts [h.norm_left_le_norm_right, le_rfl]
  · -- Of two independent lattice vectors attaining the minimum, one lies off the line `ℝ ∙ v`.
    have hlam := successiveMin_nonneg L K ⟨1, hE⟩
    obtain ⟨u, hu, huLK⟩ := (successiveMin_le_iff L hK0 hlam).1 le_rfl
    have hu' : LinearIndependent ℝ ![u 0, u 1] := by
      convert hu using 1
      ext j
      fin_cases j <;> rfl
    have hoff : ∃ j, u j ∉ ℝ ∙ v := by
      by_contra! hon
      obtain ⟨a, ha⟩ := mem_span_singleton.1 (hon 0)
      obtain ⟨b, hb⟩ := mem_span_singleton.1 (hon 1)
      have hab := (LinearIndependent.pair_iff.1 hu') b (-a) (by
        rw [← ha, ← hb, smul_smul, smul_smul, ← add_smul, show b * a + -a * b = 0 by ring,
          zero_smul])
      exact hu.ne_zero 1 (by rw [← hb, hab.1, zero_smul])
    obtain ⟨j, hj⟩ := hoff
    exact (h.norm_right_le _ (huLK j).1 hj).trans ((hball hlam).1 (huLK j).2)

end Minima

/-! ### Transport along similarities -/

section Map

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Shortest pairs are carried along similarities.** If the linear map `f` multiplies every norm
by the same factor `k > 0`, then `f v, f w` is a shortest pair of the image lattice `f(L)` exactly
when `v, w` is a shortest pair of `L`. -/
theorem isShortestPair_map_iff {L : Submodule ℤ E} {v w : E} {f : E →ₗ[ℝ] F} {k : ℝ}
    (hk : 0 < k) (hf : ∀ x, ‖f x‖ = k * ‖x‖) :
    IsShortestPair (L.map (f.restrictScalars ℤ)) (f v) (f w) ↔ IsShortestPair L v w := by
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx ↦ ?_
    have := hf x
    rw [hx, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left hk.ne')
  have hL (x : E) : f x ∈ L.map (f.restrictScalars ℤ) ↔ x ∈ L := by
    rw [← SetLike.mem_coe, Submodule.map_coe, LinearMap.coe_restrictScalars, hinj.mem_set_image,
      SetLike.mem_coe]
  have hline (x : E) : f x ∈ ℝ ∙ f v ↔ x ∈ ℝ ∙ v := by
    simp only [mem_span_singleton, ← map_smul, hinj.eq_iff]
  have hnorm (x y : E) : ‖f x‖ ≤ ‖f y‖ ↔ ‖x‖ ≤ ‖y‖ := by
    rw [hf, hf, mul_le_mul_iff_right₀ hk]
  -- Every vector of the image lattice is the image of a vector of `L`.
  have hall {P : F → Prop} : (∀ y ∈ L.map (f.restrictScalars ℤ), P y) ↔ ∀ x ∈ L, P (f x) :=
    ⟨fun H x hx ↦ H _ ((hL x).2 hx), fun H y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      exact H x hx⟩
  constructor
  · intro h
    refine ⟨(hL v).1 h.left_mem, fun hv ↦ h.left_ne_zero (by rw [hv, map_zero]),
      fun x hx hx0 ↦ (hnorm v x).1 (h.norm_left_le _ ((hL x).2 hx) ?_), (hL w).1 h.right_mem,
      fun hw ↦ h.right_notMem ((hline w).2 hw),
      fun x hx hxv ↦ (hnorm w x).1 (h.norm_right_le _ ((hL x).2 hx) ((hline x).not.2 hxv))⟩
    rwa [Ne, ← map_zero f, hinj.eq_iff]
  · intro h
    refine ⟨(hL v).2 h.left_mem, by rw [Ne, ← map_zero f, hinj.eq_iff]; exact h.left_ne_zero,
      hall.2 fun x hx hx0 ↦ (hnorm v x).2 (h.norm_left_le x hx ?_), (hL w).2 h.right_mem,
      fun hw ↦ h.right_notMem ((hline w).1 hw),
      hall.2 fun x hx hxv ↦ (hnorm w x).2 (h.norm_right_le x hx ((hline x).not.1 hxv))⟩
    rintro rfl
    exact hx0 (map_zero f)

end Map

end ZLattice
