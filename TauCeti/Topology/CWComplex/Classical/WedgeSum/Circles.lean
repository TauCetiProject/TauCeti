/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.Topology.WedgeSum
import TauCeti.Topology.CWComplex.Classical.Skeleton.Basic
import TauCeti.Topology.MetricSpace.Pseudo.Pi
import TauCeti.Topology.Separation.InvFunOn

/-!
# The CW structure on a wedge of circles

The wedge of circles `WedgeSum fun _ : S => (1 : Circle)` indexed by a type `S` is a
one-dimensional CW complex with one `0`-cell, the wedge point, and one `1`-cell for each `s : S`
(`TauCeti.WedgeSum.circleCWComplex`, an instance). There is no finiteness hypothesis on `S`. The
characteristic map `TauCeti.WedgeSum.circleCellMap s` of the `s`-th `1`-cell wraps the interval
`[-1, 1]` once around the `s`-th circle, sending `t` to `exp (i (π t + π))`, so that both end
points go to the wedge point `1`.

The wedge of circles is the `1`-skeleton of the presentation complex of a group presentation, and
the standard model of a classifying space of a free group. With this structure, and since the
wedge sum of Hausdorff spaces is Hausdorff, the theory of classical CW complexes (cellular
approximation, spaces of CW type and Whitehead's theorem) applies to it.

The weak topology of the CW structure is the quotient topology of the wedge sum: a set is closed
as soon as its trace on every circle is closed (`TauCeti.WedgeSum.isClosed_iff`). The inverse of a
characteristic map is continuous on its open cell because the closed interval is compact
(`ContinuousOn.continuousOn_invFunOn_image_of_isCompact`).

## Main definitions

* `TauCeti.WedgeSum.circleCellMap s`: the characteristic map of the `s`-th circle.
* `TauCeti.WedgeSum.circleCWComplex`: the CW structure on the wedge of circles.
* `TauCeti.WedgeSum.circleCellOneEquiv`: its `1`-cells are indexed by `S`.

## Main results

* `TauCeti.WedgeSum.map_one_circleCWComplex`: the characteristic map of the `1`-cell indexed by
  `s` (through `circleCellOneEquiv`) is `circleCellMap s`.
* `TauCeti.WedgeSum.closedCell_one_circleCWComplex`,
  `TauCeti.WedgeSum.openCell_one_circleCWComplex`: the closed `1`-cell indexed by `s` is the
  `s`-th circle, and the open `1`-cell is that circle without the wedge point.
* `TauCeti.WedgeSum.cellFrontier_one_circleCWComplex`: the frontier of every `1`-cell is the
  wedge point.
* `TauCeti.WedgeSum.map_zero_circleCWComplex`: the `0`-cell is the wedge point.
* `TauCeti.WedgeSum.isEmpty_cell_circleCWComplex`: there are no cells of dimension at least `2`.
* `TauCeti.WedgeSum.skeletonLT_one_circleCWComplex`: the `0`-skeleton is the wedge point.
* The structure is finite dimensional, and finite when `S` is finite (instances).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, the cell structure of graphs, and Section 1.2, Example 1.21 for wedges of circles.
-/

public section

noncomputable section

open Metric Real Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

namespace WedgeSum

variable {S : Type u}

/-- The map wrapping `[-1, 1]` once around the circle, starting and ending at `1`. -/
private def circleWrap (x : Fin 1 → ℝ) : Circle :=
  Circle.exp (π * x 0 + π)

private lemma continuous_circleWrap : Continuous circleWrap :=
  Circle.exp.continuous.comp (by fun_prop)

/-- A point of the open interval is not sent to `1`. -/
private lemma circleWrap_ne_one {x : Fin 1 → ℝ} (hx : x ∈ ball 0 1) : circleWrap x ≠ 1 := by
  replace hx : -1 < x 0 ∧ x 0 < 1 := by simpa [Real.ball_eq_Ioo] using Pi.mem_ball_unique.1 hx
  intro h
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 h
  have h0 : (0 : ℝ) < n := by nlinarith [pi_pos]
  have h1 : (n : ℝ) < 1 := by nlinarith [pi_pos]
  exact (Int.cast_pos.1 h0).not_ge (Int.lt_add_one_iff.1 (by exact_mod_cast h1))

/-- Both end points of the interval are sent to `1`. -/
private lemma circleWrap_of_mem_sphere {x : Fin 1 → ℝ} (hx : x ∈ sphere 0 1) :
    circleWrap x = 1 := by
  replace hx : |x 0| = 1 := by simpa [Real.dist_eq] using Pi.mem_sphere_unique.1 hx
  rcases abs_eq (zero_le_one' ℝ) |>.1 hx with h | h
  · rw [circleWrap, h, mul_one, ← two_mul, Circle.exp_two_pi]
  · rw [circleWrap, h, mul_neg_one, neg_add_cancel, Circle.exp_zero]

private lemma injOn_circleWrap : InjOn circleWrap (ball 0 1) := by
  intro x hx y hy h
  have hmem {z : Fin 1 → ℝ} (hz : z ∈ ball 0 1) : π * z 0 + π ∈ Ico 0 (2 * π) := by
    replace hz : -1 < z 0 ∧ z 0 < 1 := by simpa [Real.ball_eq_Ioo] using Pi.mem_ball_unique.1 hz
    exact ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩
  have hxy := Circle.exp_injOn_Ico (by rw [sub_zero]) (hmem hx) (hmem hy) h
  funext i
  rw [Subsingleton.elim i 0]
  exact mul_left_cancel₀ pi_pos.ne' (add_right_cancel hxy)

/-- Every point of the circle is the image of a point of the closed interval. -/
private lemma image_circleWrap_closedBall : circleWrap '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  obtain ⟨r, ⟨hr0, hr1⟩, rfl⟩ : z ∈ Circle.exp '' Icc 0 (0 + 2 * π) := by
    rw [Circle.periodic_exp.image_Icc two_pi_pos, Circle.exp_surjective.range_eq]
    exact mem_univ z
  refine ⟨fun _ ↦ r / π - 1, ?_, ?_⟩
  · have hx : -1 ≤ r / π - 1 ∧ r / π - 1 ≤ 1 :=
      ⟨by linarith [div_nonneg hr0 pi_pos.le],
        by linarith [(div_le_iff₀ pi_pos).2 (by linarith : r ≤ 2 * π)]⟩
    exact Pi.mem_closedBall_unique.2 (by simpa [Real.closedBall_eq_Icc] using hx)
  · simp [circleWrap, mul_sub, mul_div_cancel₀ r pi_pos.ne']

variable (S) in
/-- The characteristic map of the `1`-cell of the wedge of circles indexed by `s : S`: it wraps
the interval `[-1, 1]` once around the `s`-th circle, sending `t` to `exp (i (π t + π))`, and is a
bijection from the open interval `(-1, 1)` onto the `s`-th circle without the wedge point. -/
def circleCellMap (s : S) : PartialEquiv (Fin 1 → ℝ) (WedgeSum fun _ : S ↦ (1 : Circle)) :=
  InjOn.toPartialEquiv (fun x ↦ incl (fun _ : S ↦ (1 : Circle)) s (circleWrap x)) (ball 0 1)
    fun _ hx _ hy h ↦ injOn_circleWrap hx hy
      ((incl_inj (x := fun _ : S ↦ (1 : Circle))).1 h)

@[simp]
theorem circleCellMap_apply (s : S) (x : Fin 1 → ℝ) :
    circleCellMap S s x = incl (fun _ : S ↦ (1 : Circle)) s (Circle.exp (π * x 0 + π)) :=
  (rfl)

@[simp]
theorem circleCellMap_source (s : S) : (circleCellMap S s).source = ball 0 1 :=
  (rfl)

/-- The inverse of `circleCellMap S s` is the inverse of the wrapping map on the open interval. -/
theorem coe_circleCellMap_symm (s : S) :
    ⇑(circleCellMap S s).symm = Function.invFunOn (circleCellMap S s) (ball 0 1) :=
  (rfl)

private lemma coe_circleCellMap (s : S) :
    ⇑(circleCellMap S s) = incl (fun _ : S ↦ (1 : Circle)) s ∘ circleWrap :=
  (rfl)

theorem continuous_circleCellMap (s : S) : Continuous (circleCellMap S s) :=
  (incl (fun _ : S ↦ (1 : Circle)) s).continuous.comp continuous_circleWrap

/-- The closed `1`-cell of `s` is the `s`-th circle. -/
theorem image_circleCellMap_closedBall (s : S) :
    circleCellMap S s '' closedBall 0 1 = range (incl (fun _ : S ↦ (1 : Circle)) s) := by
  rw [coe_circleCellMap, image_comp, image_circleWrap_closedBall, image_univ]

/-- The open `1`-cell of `s` is the `s`-th circle without the wedge point. -/
theorem image_circleCellMap_ball (s : S) :
    circleCellMap S s '' ball 0 1 =
      range (incl (fun _ : S ↦ (1 : Circle)) s) \ {base (fun _ : S ↦ (1 : Circle))} := by
  refine subset_antisymm ?_ fun y ⟨⟨z, hz⟩, hy⟩ ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨_, rfl⟩, fun h ↦ circleWrap_ne_one hx
      ((incl_eq_base_iff (x := fun _ : S ↦ (1 : Circle))).1 h)⟩
  subst hz
  obtain ⟨x, hx, rfl⟩ : z ∈ circleWrap '' closedBall 0 1 := by
    rw [image_circleWrap_closedBall]
    exact mem_univ z
  refine ⟨x, ?_, rfl⟩
  rcases (mem_closedBall_iff_norm.1 hx).lt_or_eq with h | h
  · exact mem_ball_iff_norm.2 h
  · refine (hy ?_).elim
    rw [mem_singleton_iff, incl_eq_base_iff]
    exact circleWrap_of_mem_sphere (mem_sphere_iff_norm.2 h)

/-- The target of `circleCellMap S s`, the image of the open interval, is the `s`-th circle
without the wedge point. -/
@[simp]
theorem circleCellMap_target (s : S) :
    (circleCellMap S s).target =
      range (incl (fun _ : S ↦ (1 : Circle)) s) \ {base (fun _ : S ↦ (1 : Circle))} :=
  image_circleCellMap_ball s

/-- The boundary of the `1`-cell of `s` is the wedge point. -/
theorem circleCellMap_of_mem_sphere (s : S) {x : Fin 1 → ℝ} (hx : x ∈ sphere 0 1) :
    circleCellMap S s x = base (fun _ : S ↦ (1 : Circle)) := by
  rw [coe_circleCellMap, Function.comp_apply, circleWrap_of_mem_sphere hx, incl_apply_self]

/-- The wedge point lies in no open `1`-cell. -/
private lemma base_notMem_image_circleCellMap_ball (s : S) :
    base (fun _ : S ↦ (1 : Circle)) ∉ circleCellMap S s '' ball 0 1 := by
  rw [image_circleCellMap_ball]
  exact fun h ↦ h.2 rfl

/-- The open `1`-cells of two different circles are disjoint. -/
private lemma disjoint_image_circleCellMap_ball {s t : S} (hst : s ≠ t) :
    Disjoint (circleCellMap S s '' ball 0 1) (circleCellMap S t '' ball 0 1) := by
  rw [image_circleCellMap_ball, image_circleCellMap_ball, disjoint_left]
  rintro _ ⟨⟨y, rfl⟩, hy⟩ ⟨⟨z, hz⟩, -⟩
  rcases incl_eq_incl_iff.1 hz with ⟨-, rfl⟩ | h
  · exact hy (by simp)
  · exact hst (Sigma.mk.inj h).1.symm

/-- The inverse of the characteristic map of a `1`-cell is continuous on the open cell. -/
private lemma continuousOn_circleCellMap_symm (s : S) :
    ContinuousOn (circleCellMap S s).symm (circleCellMap S s).target := by
  rw [coe_circleCellMap_symm, circleCellMap_target, ← image_circleCellMap_ball]
  refine (continuous_circleCellMap s).continuousOn.continuousOn_invFunOn_image_of_isCompact
    (isCompact_closedBall 0 1) ball_subset_closedBall
    (fun _ hx _ hy h ↦ (circleCellMap S s).injOn hx hy h) ?_
  rw [image_circleCellMap_ball, disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨-, hy⟩
  rw [closedBall_sdiff_ball] at hx
  exact hy (circleCellMap_of_mem_sphere s hx)

/-- The cells of the wedge of circles: one `0`-cell, one `1`-cell for each circle, and no cells
of higher dimension. -/
private def CircleCell (S : Type u) : ℕ → Type u
  | 0 => PUnit
  | 1 => S
  | _ + 2 => PEmpty

/-- The characteristic maps of the wedge of circles. -/
private def circleCellMaps (S : Type u) :
    (n : ℕ) → CircleCell S n → PartialEquiv (Fin n → ℝ) (WedgeSum fun _ : S ↦ (1 : Circle))
  | 0, _ => .single 0 (base (fun _ : S ↦ (1 : Circle)))
  | 1, s => circleCellMap S s
  | _ + 2, i => PEmpty.elim i

/-- The open cells of the wedge of circles are pairwise disjoint. -/
private lemma pairwiseDisjoint_circleCellMaps :
    (univ : Set (Σ n, CircleCell S n)).PairwiseDisjoint
      fun i ↦ circleCellMaps S i.1 i.2 '' ball 0 1 := by
  rintro ⟨m, i⟩ - ⟨n, j⟩ - hne
  match m, i, n, j with
  | 0, ⟨⟩, 0, ⟨⟩ => exact absurd rfl hne
  | 0, ⟨⟩, 1, t =>
    refine disjoint_left.2 ?_
    rintro _ ⟨x, -, rfl⟩
    exact base_notMem_image_circleCellMap_ball (S := S) t
  | 1, s, 0, ⟨⟩ =>
    refine disjoint_right.2 ?_
    rintro _ ⟨x, -, rfl⟩
    exact base_notMem_image_circleCellMap_ball (S := S) s
  | 1, s, 1, t =>
    exact disjoint_image_circleCellMap_ball (S := S) fun h ↦ hne (Sigma.ext rfl (heq_of_eq h))
  | _ + 2, i, _, _ | _, _, _ + 2, i => exact PEmpty.elim i

/-- The boundary of every cell of the wedge of circles lies in the `0`-cell. -/
private lemma mapsTo_circleCellMaps (n : ℕ) (i : CircleCell S n) :
    ∃ I : Π m, Finset (CircleCell S m), MapsTo (circleCellMaps S n i) (sphere 0 1)
      (⋃ (m < n) (j ∈ I m), circleCellMaps S m j '' closedBall 0 1) := by
  match n, i with
  | 0, _ =>
    exact ⟨fun _ ↦ ∅, fun x hx ↦ ((sphere_eq_empty_of_subsingleton one_ne_zero).subset hx).elim⟩
  | 1, s =>
    refine ⟨fun m ↦ match m with | 0 => {⟨⟩} | _ + 1 => ∅, fun x hx ↦ ?_⟩
    refine mem_iUnion₂.2 ⟨0, zero_lt_one, mem_iUnion₂.2 ⟨⟨⟩, Finset.mem_singleton_self _, ?_⟩⟩
    exact ⟨0, by simp, (circleCellMap_of_mem_sphere (S := S) s hx).symm⟩
  | _ + 2, i => exact PEmpty.elim i

/-- **The CW structure on a wedge of circles.** The wedge of circles indexed by `S` has one
`0`-cell, the wedge point, and one `1`-cell for each `s : S`, with characteristic map
`TauCeti.WedgeSum.circleCellMap s` (`TauCeti.WedgeSum.map_one_circleCWComplex`). -/
@[instance_reducible]
def circleCWComplex : CWComplex (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) where
  cell := CircleCell S
  map := circleCellMaps S
  source_eq
    | 0, _ => by ext x; simp [circleCellMaps, Subsingleton.elim x 0]
    | 1, _ => rfl
    | _ + 2, i => PEmpty.elim i
  continuousOn
    | 0, _ => continuousOn_const
    | 1, s => (continuous_circleCellMap s).continuousOn
    | _ + 2, i => PEmpty.elim i
  continuousOn_symm
    | 0, _ => continuousOn_const
    | 1, s => continuousOn_circleCellMap_symm s
    | _ + 2, i => PEmpty.elim i
  pairwiseDisjoint' := pairwiseDisjoint_circleCellMaps
  mapsTo' := mapsTo_circleCellMaps
  closed' A _ hA := isClosed_iff.2 fun s ↦ by
    simpa [circleCellMaps, image_circleCellMap_closedBall, preimage_inter_range] using
      (hA 1 s).preimage (incl _ s).continuous
  union' := by
    refine eq_univ_of_forall fun y ↦ ?_
    induction y using WedgeSum.ind with
    | base => exact mem_iUnion₂.2 ⟨0, ⟨⟩, 0, by simp, rfl⟩
    | incl s z =>
      obtain ⟨x, hx, hxz⟩ : incl _ s z ∈ circleCellMap S s '' closedBall 0 1 := by
        rw [image_circleCellMap_closedBall]
        exact mem_range_self z
      exact mem_iUnion₂.2 ⟨1, s, x, hx, hxz⟩

attribute [instance] circleCWComplex

/-- The `1`-cells of the wedge of circles indexed by `S` are indexed by `S`. -/
def circleCellOneEquiv : cell (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) 1 ≃ S :=
  Equiv.refl S

/-- The characteristic map of the `1`-cell `i` is `TauCeti.WedgeSum.circleCellMap` of the
corresponding index `circleCellOneEquiv i`. -/
@[simp]
theorem map_one_circleCWComplex (i : cell (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) 1) :
    map (C := (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle)))) 1 i =
      circleCellMap S (circleCellOneEquiv i) :=
  (rfl)

/-- The closed `1`-cell `i` is the circle indexed by `circleCellOneEquiv i`. -/
@[simp]
theorem closedCell_one_circleCWComplex
    (i : cell (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) 1) :
    closedCell (C := (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle)))) 1 i =
      range (incl (fun _ : S ↦ (1 : Circle)) (circleCellOneEquiv i)) :=
  image_circleCellMap_closedBall (circleCellOneEquiv i)

/-- The open `1`-cell `i` is the circle indexed by `circleCellOneEquiv i` without the wedge
point. -/
@[simp]
theorem openCell_one_circleCWComplex
    (i : cell (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) 1) :
    openCell (C := (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle)))) 1 i =
      range (incl (fun _ : S ↦ (1 : Circle)) (circleCellOneEquiv i)) \
        {base (fun _ : S ↦ (1 : Circle))} :=
  image_circleCellMap_ball (circleCellOneEquiv i)

/-- The frontier of every `1`-cell is the wedge point: each `1`-cell is a loop. -/
@[simp]
theorem cellFrontier_one_circleCWComplex
    (i : cell (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) 1) :
    cellFrontier (C := (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle)))) 1 i =
      {base (fun _ : S ↦ (1 : Circle))} := by
  have h1 : (fun _ ↦ 1 : Fin 1 → ℝ) ∈ sphere 0 1 :=
    Pi.mem_sphere_unique.2 (by simp)
  refine subset_antisymm
    (image_subset_iff.2 fun x hx ↦ circleCellMap_of_mem_sphere (circleCellOneEquiv i) hx)
    (singleton_subset_iff.2 ⟨_, h1, circleCellMap_of_mem_sphere (circleCellOneEquiv i) h1⟩)

/-- The wedge of circles has a single `0`-cell. -/
instance : Unique (cell (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) 0) :=
  inferInstanceAs (Unique PUnit)

/-- The `0`-cell of the wedge of circles is the wedge point. -/
@[simp]
theorem map_zero_circleCWComplex (i : cell (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) 0)
    (x : Fin 0 → ℝ) :
    map (C := (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle)))) 0 i x =
      base (fun _ : S ↦ (1 : Circle)) :=
  (rfl)

/-- The wedge of circles has no cells of dimension at least `2`. -/
theorem isEmpty_cell_circleCWComplex {n : ℕ} (hn : 2 ≤ n) :
    IsEmpty (cell (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) n) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact inferInstanceAs (IsEmpty PEmpty.{u + 1})

/-- The wedge of circles is a finite dimensional CW complex. -/
instance : RelCWComplex.FiniteDimensional (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) where
  eventually_isEmpty_cell := Filter.eventually_atTop.2 ⟨2, fun _ ↦ isEmpty_cell_circleCWComplex⟩

/-- A wedge of finitely many circles is a finite CW complex. -/
instance [Finite S] : RelCWComplex.Finite (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) where
  finite_cell
    | 0 => inferInstanceAs (Finite PUnit)
    | 1 => inferInstanceAs (Finite S)
    | _ + 2 => inferInstanceAs (Finite PEmpty)

/-- The `0`-skeleton of the wedge of circles, `skeletonLT _ 1`, is the wedge point. -/
theorem skeletonLT_one_circleCWComplex :
    (skeletonLT (univ : Set (WedgeSum fun _ : S ↦ (1 : Circle))) 1 :
      Set (WedgeSum fun _ : S ↦ (1 : Circle))) = {base (fun _ : S ↦ (1 : Circle))} := by
  simp [skeletonLT_one_eq_insert]

end WedgeSum

end TauCeti
