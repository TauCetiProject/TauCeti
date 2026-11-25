/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered

/-!
# Order units and the order-unit norm

Let `E` be a real ordered vector space. An element `e : E` is an *order unit* when every vector
`a` lies in some order interval `-r • e ≤ a ≤ r • e`, and the order unit is *Archimedean* when
`a ≤ ε • e` for every `ε > 0` forces `a ≤ 0`. The *order-unit norm* of `a` is

```text
‖a‖ = inf {r ≥ 0 : -r • e ≤ a ≤ r • e},
```

the Minkowski gauge of the order interval `[-e, e]`. Kadison's representation of an Archimedean
order-unit space as a space of continuous affine functions on its state space, and the metric
geometry of states built on it by Rieffel, start from this norm.

The first part of the file constructs it. For any order unit the gauge of `[-e, e]` is a real
seminorm, `TauCeti.orderUnitSeminorm`, with `‖e‖ = 1` as soon as `e ≠ 0`; for an Archimedean
order unit it is a norm, and its closed balls are exactly the order intervals:

```text
‖a‖ ≤ r ↔ -r • e ≤ a ≤ r • e    (0 ≤ r).
```

The second part takes the opposite point of view, needed to state theorems about spaces that
already carry a norm, such as `C(K, ℝ)`: `TauCeti.IsOrderUnitNorm e` records that a given norm
satisfies `‖e‖ = 1` and the interval formula above. The constructed norm satisfies it
(`TauCeti.IsArchimedeanOrderUnit.isOrderUnitNorm`), and conversely the interval formula forces
`e` to be an Archimedean order unit (`TauCeti.IsOrderUnitNorm.isArchimedeanOrderUnit`). For
such a norm the positive cone is closed, `e` is an interior point of it, and the order is
recovered from the norm and `e`: `0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖`. A unital linear order embedding
between two such spaces is isometric. The predicate is stable under restriction to a subspace
containing `e` and under finite nonempty products with the coordinatewise order and the supremum
norm, and `ℝ` and `C(K, ℝ)` for nonempty compact `K`, with `e = 1`, satisfy it. The self-adjoint
part of a unital C⋆-algebra is treated in `TauCeti.Analysis.CStarAlgebra.OrderUnit`.

## Main definitions

* `TauCeti.IsOrderUnit e`: every vector lies in an order interval `[-r • e, r • e]`, `r > 0`.
* `TauCeti.IsArchimedeanOrderUnit e`: an order unit with the Archimedean property.
* `TauCeti.orderUnitSeminorm`: the gauge of `[-e, e]`, as a `Seminorm ℝ E`.
* `TauCeti.IsArchimedeanOrderUnit.normedAddCommGroup`,
  `TauCeti.IsArchimedeanOrderUnit.normedSpace`: the normed space structure of the order-unit
  norm.
* `TauCeti.IsOrderUnitNorm e`: a given norm is the order-unit norm of `e`.

## Main results

* `TauCeti.IsArchimedeanOrderUnit.orderUnitSeminorm_le_iff`: the interval formula.
* `TauCeti.IsArchimedeanOrderUnit.orderUnitSeminorm_eq_zero_iff`: definiteness.
* `TauCeti.IsOrderUnit.orderUnitSeminorm_self`: `‖e‖ = 1` for `e ≠ 0`.
* `TauCeti.IsArchimedeanOrderUnit.isOrderUnitNorm`: the constructed norm is an order-unit norm.
* `TauCeti.IsOrderUnitNorm.isArchimedeanOrderUnit`: the interval formula excludes
  non-Archimedean cones.
* `TauCeti.IsOrderUnitNorm.norm_eq_orderUnitSeminorm`: an order-unit norm is the order-unit
  seminorm of its unit.
* `TauCeti.IsOrderUnitNorm.nonneg_iff_norm_smul_sub_le`: recovery of the order from the norm.
* `TauCeti.IsOrderUnitNorm.norm_map`: unital linear order embeddings are isometric.
* `TauCeti.IsOrderUnitNorm.isClosed_nonneg`, `TauCeti.IsOrderUnitNorm.orderClosedTopology`,
  `TauCeti.IsOrderUnitNorm.mem_interior_Ici_zero`: the positive cone is closed and has `e` as an
  interior point.
* `TauCeti.IsOrderUnitNorm.submodule`, `TauCeti.IsOrderUnitNorm.prod`,
  `TauCeti.IsOrderUnitNorm.pi`, `TauCeti.isOrderUnitNorm_real_one`,
  `TauCeti.isOrderUnitNorm_continuousMap_one`: subspaces, finite nonempty products and
  examples.

## References

* R. V. Kadison, *A representation theory for commutative topological algebra*, Mem. Amer.
  Math. Soc. 7 (1951).
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, §1.
-/

public section

open Set Metric
open scoped Pointwise

namespace TauCeti

section OrderedModule

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]

/-- An element `e` of a real ordered vector space is an *order unit* when every vector lies in
some order interval `[-r • e, r • e]` with `r > 0`. -/
structure IsOrderUnit (e : E) : Prop where
  exists_neg_smul_le_le_smul (a : E) : ∃ r : ℝ, 0 < r ∧ -(r • e) ≤ a ∧ a ≤ r • e

/-- An order unit `e` is *Archimedean* when `a ≤ ε • e` for every `ε > 0` forces `a ≤ 0`. -/
structure IsArchimedeanOrderUnit (e : E) : Prop extends IsOrderUnit e where
  le_zero_of_forall_le_smul {a : E} : (∀ ε : ℝ, 0 < ε → a ≤ ε • e) → a ≤ 0

variable [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e a b : E} {r : ℝ}

/-- An order interval `[-e, e]` of a real ordered vector space is balanced. -/
theorem balanced_Icc_neg (e : E) : Balanced ℝ (Icc (-e) e) :=
  (balanced_iff_neg_mem (convex_Icc _ _)).2 fun _ hx => ⟨neg_le_neg hx.2, neg_le.1 hx.1⟩

omit [IsOrderedAddMonoid E] in
/-- For `r > 0`, the dilation `r • [-e, e]` of an order interval is the order interval
`[-r • e, r • e]`. -/
theorem mem_smul_Icc_neg_iff (hr : 0 < r) :
    a ∈ r • Icc (-e) e ↔ -(r • e) ≤ a ∧ a ≤ r • e := by
  rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne', mem_Icc, le_inv_smul_iff_of_pos hr,
    inv_smul_le_iff_of_pos hr, smul_neg]

namespace IsOrderUnit

/-- An order unit is nonnegative. -/
theorem nonneg (he : IsOrderUnit e) : 0 ≤ e := by
  obtain ⟨r, hr, h₁, h₂⟩ := he.exists_neg_smul_le_le_smul 0
  have h : 0 ≤ (r + r) • e := by
    rw [add_smul]
    exact neg_le_iff_add_nonneg.1 (h₁.trans h₂)
  have := smul_nonneg (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ r + r)) h
  rwa [inv_smul_smul₀ (by positivity)] at this

/-- The order interval `[-e, e]` of an order unit is absorbent. -/
theorem absorbent_Icc_neg (he : IsOrderUnit e) : Absorbent ℝ (Icc (-e) e) := by
  refine absorbent_iff_forall_absorbs_singleton.2 fun a => ?_
  obtain ⟨r, hr, h⟩ := he.exists_neg_smul_le_le_smul a
  exact .of_norm ⟨‖r‖, fun c hc => singleton_subset_iff.2 <|
    (balanced_Icc_neg e).smul_mono hc ((mem_smul_Icc_neg_iff hr).2 h)⟩

/-- The order interval `[-e, e]` of an order unit contains `0`. -/
theorem zero_mem_Icc_neg (he : IsOrderUnit e) : (0 : E) ∈ Icc (-e) e :=
  ⟨neg_nonpos.2 he.nonneg, he.nonneg⟩

end IsOrderUnit

/-- The *order-unit seminorm* of an order unit `e`: the gauge `inf {r > 0 : -r • e ≤ a ≤ r • e}`
of the order interval `[-e, e]`. It is a norm when `e` is Archimedean
(`TauCeti.IsArchimedeanOrderUnit.orderUnitSeminorm_eq_zero_iff`). -/
noncomputable def orderUnitSeminorm (he : IsOrderUnit e) : Seminorm ℝ E :=
  gaugeSeminorm (balanced_Icc_neg e) (convex_Icc _ _) he.absorbent_Icc_neg

/-- The order-unit seminorm is the gauge of the order interval `[-e, e]`. -/
theorem orderUnitSeminorm_apply (he : IsOrderUnit e) (a : E) :
    orderUnitSeminorm he a = gauge (Icc (-e) e) a :=
  (rfl)

/-- The order-unit seminorm of `a` is at most `r ≥ 0` exactly when `a` lies in every order
interval `[-s • e, s • e]` with `s > r`. -/
theorem IsOrderUnit.orderUnitSeminorm_le_iff_forall_lt (he : IsOrderUnit e) (hr : 0 ≤ r) :
    orderUnitSeminorm he a ≤ r ↔ ∀ s, r < s → -(s • e) ≤ a ∧ a ≤ s • e := by
  have := congrArg (a ∈ ·) <|
    setOfPred_gauge_le_eq (convex_Icc _ _) he.zero_mem_Icc_neg he.absorbent_Icc_neg hr
  simp only [mem_ofPred_eq, mem_iInter, eq_iff_iff] at this
  rw [orderUnitSeminorm_apply, this]
  exact forall₂_congr fun s hs => mem_smul_Icc_neg_iff (hr.trans_lt hs)

/-- A vector in the order interval `[-r • e, r • e]` has order-unit seminorm at most `r`. -/
theorem IsOrderUnit.orderUnitSeminorm_le (he : IsOrderUnit e) (hr : 0 ≤ r)
    (h₁ : -(r • e) ≤ a) (h₂ : a ≤ r • e) : orderUnitSeminorm he a ≤ r :=
  (he.orderUnitSeminorm_le_iff_forall_lt hr).2 fun _s hs =>
    ⟨(neg_le_neg (smul_le_smul_of_nonneg_right hs.le he.nonneg)).trans h₁,
      h₂.trans (smul_le_smul_of_nonneg_right hs.le he.nonneg)⟩

/-- A nonzero order unit has order-unit seminorm one. -/
theorem IsOrderUnit.orderUnitSeminorm_self (he : IsOrderUnit e) (he₀ : e ≠ 0) :
    orderUnitSeminorm he e = 1 := by
  refine le_antisymm (he.orderUnitSeminorm_le zero_le_one ?_ ?_) (not_lt.1 fun hlt => he₀ ?_)
  · simpa using neg_le_self he.nonneg
  · simp
  · set n := orderUnitSeminorm he e
    have hs : n < (n + 1) / 2 := by linarith
    have hle := ((he.orderUnitSeminorm_le_iff_forall_lt (apply_nonneg _ e)).1 le_rfl _ hs).2
    have hpos : (0 : ℝ) < 1 - (n + 1) / 2 := by linarith
    have : (1 - (n + 1) / 2) • e ≤ (1 - (n + 1) / 2) • (0 : E) := by
      rwa [sub_smul, one_smul, smul_zero, sub_nonpos]
    exact le_antisymm ((smul_le_smul_iff_of_pos_left hpos).1 this) he.nonneg

namespace IsArchimedeanOrderUnit

omit [PosSMulMono ℝ E] in
/-- For an Archimedean order unit, a vector below every `s • e` with `s > r` is below `r • e`. -/
theorem le_smul_of_forall_lt (he : IsArchimedeanOrderUnit e) (h : ∀ s, r < s → a ≤ s • e) :
    a ≤ r • e :=
  sub_nonpos.1 <| he.le_zero_of_forall_le_smul fun ε hε => by
    rw [sub_le_iff_le_add, ← add_smul]
    exact h _ (lt_add_of_pos_left r hε)

/-- The interval formula: for an Archimedean order unit, the order-unit seminorm of `a` is at
most `r ≥ 0` exactly when `-r • e ≤ a ≤ r • e`. -/
theorem orderUnitSeminorm_le_iff (he : IsArchimedeanOrderUnit e) (hr : 0 ≤ r) :
    orderUnitSeminorm he.toIsOrderUnit a ≤ r ↔ -(r • e) ≤ a ∧ a ≤ r • e := by
  refine ⟨fun h => ?_, fun h => he.orderUnitSeminorm_le hr h.1 h.2⟩
  rw [he.orderUnitSeminorm_le_iff_forall_lt hr] at h
  exact ⟨neg_le.1 <| he.le_smul_of_forall_lt fun s hs => neg_le.1 (h s hs).1,
    he.le_smul_of_forall_lt fun s hs => (h s hs).2⟩

/-- The order-unit seminorm of an Archimedean order unit is definite. -/
theorem orderUnitSeminorm_eq_zero_iff (he : IsArchimedeanOrderUnit e) :
    orderUnitSeminorm he.toIsOrderUnit a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ map_zero _⟩
  obtain ⟨h₁, h₂⟩ := (he.orderUnitSeminorm_le_iff le_rfl).1 h.le
  simp only [zero_smul, neg_zero] at h₁ h₂
  exact le_antisymm h₂ h₁

/-- The normed group structure given by the order-unit norm of an Archimedean order unit. It is
not an instance, since the order unit `e` is not determined by `E`. -/
noncomputable abbrev normedAddCommGroup (he : IsArchimedeanOrderUnit e) : NormedAddCommGroup E :=
  letI : Norm E := ⟨orderUnitSeminorm he.toIsOrderUnit⟩
  NormedAddCommGroup.ofCore (𝕜 := ℝ)
    { norm_nonneg := apply_nonneg _
      norm_smul := map_smul_eq_mul _
      norm_triangle := map_add_le_add _
      norm_eq_zero_iff := fun _ => he.orderUnitSeminorm_eq_zero_iff }

/-- The real normed space structure given by the order-unit norm of an Archimedean order unit,
compatible with `TauCeti.IsArchimedeanOrderUnit.normedAddCommGroup`. -/
noncomputable abbrev normedSpace (he : IsArchimedeanOrderUnit e) :
    letI := he.normedAddCommGroup
    NormedSpace ℝ E :=
  letI := he.normedAddCommGroup
  { norm_smul_le := fun c a => (map_smul_eq_mul (orderUnitSeminorm he.toIsOrderUnit) c a).le }

/-- The norm of `TauCeti.IsArchimedeanOrderUnit.normedAddCommGroup` is the order-unit seminorm. -/
theorem norm_eq_orderUnitSeminorm (he : IsArchimedeanOrderUnit e) (a : E) :
    letI := he.normedAddCommGroup
    ‖a‖ = orderUnitSeminorm he.toIsOrderUnit a :=
  (rfl)

end IsArchimedeanOrderUnit

end OrderedModule

section Norm

variable {E : Type*} [Norm E] [AddCommGroup E] [Module ℝ E] [PartialOrder E]

/-- A norm on a real ordered vector space is the *order-unit norm* of `e` when `‖e‖ = 1` and the
closed balls about `0` are the order intervals: `‖a‖ ≤ r ↔ -r • e ≤ a ≤ r • e` for `r ≥ 0`. This
is the hypothesis under which theorems about order-unit spaces carrying a given norm, such as
`C(K, ℝ)` or the self-adjoint part of a unital C⋆-algebra, are stated. -/
structure IsOrderUnitNorm (e : E) : Prop where
  norm_eq_one : ‖e‖ = 1
  norm_le_iff {a : E} {r : ℝ} (hr : 0 ≤ r) : ‖a‖ ≤ r ↔ -(r • e) ≤ a ∧ a ≤ r • e

end Norm

/-- The order-unit norm constructed from a nonzero Archimedean order unit `e` is an order-unit
norm for `e`. -/
theorem IsArchimedeanOrderUnit.isOrderUnitNorm {E : Type*} [AddCommGroup E] [Module ℝ E]
    [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] {e : E}
    (he : IsArchimedeanOrderUnit e) (he₀ : e ≠ 0) :
    letI : Norm E := he.normedAddCommGroup.toNorm
    IsOrderUnitNorm e :=
  letI : Norm E := he.normedAddCommGroup.toNorm
  ⟨(he.norm_eq_orderUnitSeminorm e).trans (he.orderUnitSeminorm_self he₀), fun {a} _ hr =>
    (iff_of_eq (congrArg (· ≤ _) (he.norm_eq_orderUnitSeminorm a))).trans
      (he.orderUnitSeminorm_le_iff hr)⟩

namespace IsOrderUnitNorm

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E] {e a b : E}
  {r : ℝ}

/-- Every vector `a` is bounded below by `-‖a‖ • e`. -/
theorem neg_norm_smul_le (h : IsOrderUnitNorm e) (a : E) : -(‖a‖ • e) ≤ a :=
  ((h.norm_le_iff (norm_nonneg a)).1 le_rfl).1

/-- Every vector `a` is bounded above by `‖a‖ • e`. -/
theorem le_norm_smul (h : IsOrderUnitNorm e) (a : E) : a ≤ ‖a‖ • e :=
  ((h.norm_le_iff (norm_nonneg a)).1 le_rfl).2

/-- The closed balls about `0` of an order-unit norm are the order intervals. -/
theorem closedBall_zero_eq_Icc (h : IsOrderUnitNorm e) (hr : 0 ≤ r) :
    closedBall (0 : E) r = Icc (-(r • e)) (r • e) := by
  ext a
  rw [mem_closedBall_zero_iff, h.norm_le_iff hr, mem_Icc]

/-- An order unit for an order-unit norm is nonzero. -/
theorem ne_zero (h : IsOrderUnitNorm e) : e ≠ 0 := by
  rintro rfl
  simpa using h.norm_eq_one

/-- The unit of an order-unit norm is an order unit. -/
theorem isOrderUnit (h : IsOrderUnitNorm e) : IsOrderUnit e :=
  ⟨fun a => ⟨‖a‖ + 1, by positivity, (h.norm_le_iff (by positivity)).1 (by linarith)⟩⟩

/-- Nonnegative multiples of the unit of an order-unit norm are nonnegative. -/
theorem smul_nonneg (h : IsOrderUnitNorm e) (hr : 0 ≤ r) : 0 ≤ r • e :=
  ((h.norm_le_iff hr).1 (by rwa [norm_zero])).2

/-- The unit of an order-unit norm is nonnegative. -/
theorem nonneg (h : IsOrderUnitNorm e) : 0 ≤ e := by
  simpa using h.smul_nonneg zero_le_one

variable [IsOrderedAddMonoid E]

/-- Multiples of the unit of an order-unit norm are monotone in the scalar. -/
theorem monotone_smul_right (h : IsOrderUnitNorm e) : Monotone fun r : ℝ => r • e := fun r s hrs =>
  sub_nonneg.1 <| by
    rw [← sub_smul]
    exact h.smul_nonneg (sub_nonneg.2 hrs)

/-- The open unit ball about the unit of an order-unit norm consists of nonnegative vectors. -/
theorem ball_subset_Ici_zero (h : IsOrderUnitNorm e) : ball e 1 ⊆ Ici 0 := fun a ha => by
  have := ((h.norm_le_iff zero_le_one).1 (mem_ball_iff_norm.1 ha).le).1
  rwa [one_smul, neg_le_sub_iff_le_add, le_add_iff_nonneg_left] at this

/-- The unit of an order-unit norm is an interior point of the positive cone. -/
theorem mem_interior_Ici_zero (h : IsOrderUnitNorm e) : e ∈ interior (Ici 0) :=
  mem_interior.2 ⟨ball e 1, h.ball_subset_Ici_zero, isOpen_ball, mem_ball_self one_pos⟩

/-- The interval formula excludes non-Archimedean cones: the unit of an order-unit norm is an
Archimedean order unit. -/
theorem isArchimedeanOrderUnit (h : IsOrderUnitNorm e) : IsArchimedeanOrderUnit e where
  toIsOrderUnit := h.isOrderUnit
  le_zero_of_forall_le_smul {a} ha := by
    -- `a ≤ ε • e` for every `ε > 0` gives `‖‖a‖ • e + a‖ ≤ ‖a‖`, which forces `a ≤ 0`.
    have h₀ : 0 ≤ ‖a‖ • e + a := neg_le_iff_add_nonneg'.1 (h.neg_norm_smul_le a)
    have hb : ‖‖a‖ • e + a‖ ≤ ‖a‖ := by
      refine le_of_forall_pos_le_add fun ε hε => (h.norm_le_iff (by positivity)).2 ⟨?_, ?_⟩
      · exact (neg_nonpos.2 (h.smul_nonneg (by positivity))).trans h₀
      · rw [add_smul]
        gcongr
        exact ha ε hε
    simpa using ((h.norm_le_iff (norm_nonneg a)).1 hb).2

/-- An order-unit norm is the order-unit seminorm of its unit. -/
theorem norm_eq_orderUnitSeminorm [PosSMulMono ℝ E] (h : IsOrderUnitNorm e) (a : E) :
    ‖a‖ = orderUnitSeminorm h.isOrderUnit a := by
  have key (r : ℝ) (hr : 0 ≤ r) : ‖a‖ ≤ r ↔ orderUnitSeminorm h.isOrderUnit a ≤ r := by
    rw [h.norm_le_iff hr, h.isArchimedeanOrderUnit.orderUnitSeminorm_le_iff hr]
  exact le_antisymm ((key _ (apply_nonneg _ a)).2 le_rfl) ((key _ (norm_nonneg a)).1 le_rfl)

/-- An order-unit norm is monotone on the positive cone. -/
theorem norm_le_norm_of_le_of_nonneg (h : IsOrderUnitNorm e) (hab : a ≤ b) (ha : 0 ≤ a) :
    ‖a‖ ≤ ‖b‖ :=
  (h.norm_le_iff (norm_nonneg b)).2
    ⟨(neg_nonpos.2 (h.smul_nonneg (norm_nonneg b))).trans ha,
      hab.trans (h.le_norm_smul b)⟩

/-- The order is recovered from an order-unit norm and its unit: `a` is nonnegative exactly when
`‖‖a‖ • e - a‖ ≤ ‖a‖`. -/
theorem nonneg_iff_norm_smul_sub_le (h : IsOrderUnitNorm e) : 0 ≤ a ↔ ‖‖a‖ • e - a‖ ≤ ‖a‖ := by
  rw [h.norm_le_iff (norm_nonneg a), neg_le_sub_iff_le_add, sub_le_self_iff]
  exact ⟨fun ha => ⟨(h.le_norm_smul a).trans
    (le_add_of_nonneg_left (h.smul_nonneg (norm_nonneg a))), ha⟩, And.right⟩

/-- The positive cone of an order-unit norm is closed. -/
theorem isClosed_nonneg (h : IsOrderUnitNorm e) : IsClosed {a : E | 0 ≤ a} := by
  refine isClosed_of_closure_subset fun a ha => ?_
  rw [mem_ofPred_eq, ← neg_nonpos]
  refine h.isArchimedeanOrderUnit.le_zero_of_forall_le_smul fun ε hε => ?_
  obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.1 ha ε hε
  calc -a ≤ b + -a := le_add_of_nonneg_left hb
    _ = b - a := (sub_eq_add_neg b a).symm
    _ ≤ ‖b - a‖ • e := h.le_norm_smul _
    _ ≤ ε • e := h.monotone_smul_right (by rw [← dist_eq_norm']; exact hab.le)

/-- An order-unit norm makes `E` an ordered topological group: the order relation is closed. -/
theorem orderClosedTopology (h : IsOrderUnitNorm e) : OrderClosedTopology E :=
  ⟨isClosed_le_of_isClosed_nonneg h.isClosed_nonneg⟩

end IsOrderUnitNorm

/-- The absolute value on `ℝ` is the order-unit norm of `1`. -/
theorem isOrderUnitNorm_real_one : IsOrderUnitNorm (1 : ℝ) where
  norm_eq_one := norm_one
  norm_le_iff _ := by simp [Real.norm_eq_abs, abs_le]

/-- For a nonempty compact space `K`, the supremum norm on `C(K, ℝ)` is the order-unit norm of
the constant function `1`. -/
theorem isOrderUnitNorm_continuousMap_one {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [Nonempty K] : IsOrderUnitNorm (1 : C(K, ℝ)) where
  norm_eq_one := norm_one
  norm_le_iff hr := by
    simp [ContinuousMap.norm_le _ hr, ContinuousMap.le_def, Real.norm_eq_abs, abs_le, forall_and]

namespace IsOrderUnitNorm

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E] {e : E}

/-- An order-unit norm restricts to an order-unit norm on every subspace containing the unit. -/
theorem submodule (h : IsOrderUnitNorm e) (p : Submodule ℝ E) (hp : e ∈ p) :
    IsOrderUnitNorm (⟨e, hp⟩ : p) where
  norm_eq_one := h.norm_eq_one
  norm_le_iff {a} _ hr := by
    rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe]
    exact h.norm_le_iff hr

/-- A linear order embedding between spaces with order-unit norms which maps unit to unit is
isometric. -/
theorem norm_map {F : Type*} [SeminormedAddCommGroup F] [Module ℝ F] [PartialOrder F] {f : F}
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : E →ₗ[ℝ] F) (hTe : T e = f)
    (hT : ∀ a b, T a ≤ T b ↔ a ≤ b) (a : E) : ‖T a‖ = ‖a‖ := by
  have key (r : ℝ) (hr : 0 ≤ r) : ‖T a‖ ≤ r ↔ ‖a‖ ≤ r := by
    rw [hf.norm_le_iff hr, he.norm_le_iff hr, ← hTe, ← map_smul, ← map_neg, hT, hT]
  exact le_antisymm ((key _ (norm_nonneg a)).2 le_rfl) ((key _ (norm_nonneg _)).1 le_rfl)

/-- The product of two order-unit norms, with the coordinatewise order and the maximum norm, is
the order-unit norm of the pair of units. -/
theorem prod {F : Type*} [SeminormedAddCommGroup F] [Module ℝ F] [PartialOrder F] {f : F}
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) : IsOrderUnitNorm (e, f) where
  norm_eq_one := by rw [Prod.norm_mk, he.norm_eq_one, hf.norm_eq_one, max_self]
  norm_le_iff hr := by
    rw [norm_prod_le_iff, he.norm_le_iff hr, hf.norm_le_iff hr]
    simp only [Prod.le_def, Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd]
    tauto

/-- A finite nonempty product of order-unit norms, with the coordinatewise order and the
supremum norm, is the order-unit norm of the family of units. -/
theorem pi {ι : Type*} [Fintype ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, PartialOrder (E i)]
    {e : ∀ i, E i} (h : ∀ i, IsOrderUnitNorm (e i)) : IsOrderUnitNorm e where
  norm_eq_one := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (h i).norm_eq_one.le) ?_
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (h i).norm_eq_one ▸ norm_le_pi_norm e i
  norm_le_iff hr := by
    simp only [pi_norm_le_iff_of_nonneg hr, (h _).norm_le_iff hr, Pi.le_def, Pi.neg_apply,
      Pi.smul_apply, forall_and]

end IsOrderUnitNorm

end TauCeti
