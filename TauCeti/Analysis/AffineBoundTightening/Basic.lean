/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Filter.Extr
public import Mathlib.Order.Interval.Basic

/-!
# Joint variable-and-row interval endpoints and affine image arithmetic

This file defines the joint coordinate space `Fin n ⊕ Fin m` for `n` variables and `m` affine rows,
raw lower-and-upper endpoint pairs `Raw n m` (allowing inverted pairs where the lower bound exceeds
the upper bound), and the public interval state `State n m = Interval (Coord n m → ℝ)` with one
global empty state `⊥` distinct from the unique nonempty zero-coordinate box when `n = m = 0`.

It develops the characteristic API for:
* `TauCeti.AffineBoundTightening.pack`: packing raw endpoint pairs to `State n m`, sending ordered
  pairs to their `NonemptyInterval` and invalid pairs to `⊥`;
* `TauCeti.AffineBoundTightening.Within`: reverse-lower / forward-upper endpoint containment,
  defined uniformly on valid and invalid raw pairs;
* `TauCeti.AffineBoundTightening.width`: total joint coordinate width, its monotonicity under
  `Within`, and equality from containment plus equal width;
* `TauCeti.AffineBoundTightening.zLo`, `TauCeti.AffineBoundTightening.zHi`,
  `TauCeti.AffineBoundTightening.imageLo`, `TauCeti.AffineBoundTightening.imageHi`,
  `TauCeti.AffineBoundTightening.restLo`, `TauCeti.AffineBoundTightening.restHi`: signed
  coefficient-product bounds, row affine image endpoints, and single-variable omitted sums,
  together with their exact attained extrema over ordered variable boxes.

## References

* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *Feasibility-Based Bounds Tightening via Fixed
  Points*, COCOA 2010, LNCS 6508, pp. 65–76, §4 (9)–(10).
-/

public section

open scoped BigOperators
open Set

namespace TauCeti.AffineBoundTightening

/-- Joint variable and row coordinates, with variables on the left and rows on the right. -/
abbrev Coord (n m : ℕ) := Fin n ⊕ Fin m

/-- Real lower and upper endpoints, including pairs whose lower endpoint exceeds the upper. -/
abbrev Raw (n m : ℕ) := (Coord n m → ℝ) × (Coord n m → ℝ)

/-- A nonempty joint closed interval or one global empty state. -/
abbrev State (n m : ℕ) := Interval (Coord n m → ℝ)

noncomputable section

variable {n m : ℕ}

/-! ### Endpoint containment -/

/-- Endpoint containment: `q` lies within `r` when `r.1 ≤ q.1` and `q.2 ≤ r.2`, including for
invalid endpoint pairs. -/
def Within (q r : Raw n m) : Prop := r.1 ≤ q.1 ∧ q.2 ≤ r.2

/-- Endpoint containment restated as reverse lower and forward upper pointwise inequalities. -/
theorem within_iff {q r : Raw n m} : Within q r ↔ r.1 ≤ q.1 ∧ q.2 ≤ r.2 :=
  Iff.rfl

/-- Lower-endpoint inequality extracted from `Within`. -/
theorem Within.fst_le {q r : Raw n m} (h : Within q r) : r.1 ≤ q.1 :=
  h.1

/-- Upper-endpoint inequality extracted from `Within`. -/
theorem Within.le_snd {q r : Raw n m} (h : Within q r) : q.2 ≤ r.2 :=
  h.2

/-- Endpoint containment is reflexive. -/
@[refl]
theorem Within.refl (q : Raw n m) : Within q q :=
  ⟨le_rfl, le_rfl⟩

/-- Reflexivity of endpoint containment with implicit argument. -/
theorem Within.rfl {q : Raw n m} : Within q q :=
  Within.refl q

/-- Endpoint containment is transitive. -/
theorem Within.trans {q r s : Raw n m} (hqr : Within q r) (hrs : Within r s) : Within q s :=
  ⟨hrs.1.trans hqr.1, hqr.2.trans hrs.2⟩

/-- Endpoint containment is antisymmetric. -/
theorem Within.antisymm {q r : Raw n m} (hqr : Within q r) (hrq : Within r q) : q = r :=
  Prod.ext (le_antisymm hrq.1 hqr.1) (le_antisymm hqr.2 hrq.2)

/-- Orderedness propagates outward along endpoint containment. -/
theorem Within.le_of_le {q r : Raw n m} (h : Within q r) (hq : q.1 ≤ q.2) : r.1 ≤ r.2 :=
  h.1.trans (hq.trans h.2)

/-- Endpoint containment implies inclusion of the corresponding closed boxes. -/
theorem Within.Icc_subset {q r : Raw n m} (h : Within q r) : Icc q.1 q.2 ⊆ Icc r.1 r.2 :=
  Icc_subset_Icc h.1 h.2

/-- For an ordered raw tuple, closed-box inclusion is equivalent to endpoint containment. -/
theorem Icc_subset_Icc_iff_within {q r : Raw n m} (hq : q.1 ≤ q.2) :
    Icc q.1 q.2 ⊆ Icc r.1 r.2 ↔ Within q r :=
  Icc_subset_Icc_iff hq

/-! ### Packing raw endpoints to public intervals -/

/-- Convert ordered endpoints to a nonempty interval and invalid endpoints to global bottom. -/
def pack (q : Raw n m) : State n m :=
  if h : q.1 ≤ q.2 then (⟨q, h⟩ : NonemptyInterval _) else ⊥

/-- Packing an ordered raw tuple produces the corresponding nonempty interval. -/
theorem pack_of_le {q : Raw n m} (h : q.1 ≤ q.2) :
    pack q = (⟨q, h⟩ : NonemptyInterval (Coord n m → ℝ)) := by
  simp [pack, h]

/-- Packing an invalid raw tuple produces the global empty state `⊥`. -/
theorem pack_of_not_le {q : Raw n m} (h : ¬ q.1 ≤ q.2) : pack q = ⊥ := by
  simp [pack, h]

/-- A raw tuple packs to `⊥` exactly when its lower endpoint is not below its upper endpoint. -/
@[simp]
theorem pack_eq_bot_iff {q : Raw n m} : pack q = ⊥ ↔ ¬ q.1 ≤ q.2 := by
  by_cases h : q.1 ≤ q.2
  · rw [pack_of_le h]
    exact iff_of_false WithBot.coe_ne_bot (not_not.mpr h)
  · simp [pack_of_not_le h, h]

/-- A raw tuple packs to a nonbottom state exactly when its endpoints are ordered. -/
theorem pack_ne_bot_iff {q : Raw n m} : pack q ≠ ⊥ ↔ q.1 ≤ q.2 := by
  simp [pack_eq_bot_iff]

/-- As a subset of `Coord n m → ℝ`, `pack q` is always `Set.Icc q.1 q.2`. -/
@[simp]
theorem coe_pack (q : Raw n m) : (pack q : Set (Coord n m → ℝ)) = Icc q.1 q.2 := by
  by_cases h : q.1 ≤ q.2
  · rw [pack_of_le h]
    rfl
  · rw [pack_of_not_le h, Interval.coe_bot, Icc_eq_empty h]

/-- Membership in `pack q` coincides with membership in `Set.Icc q.1 q.2`. -/
@[simp]
theorem mem_pack_iff {q : Raw n m} {x : Coord n m → ℝ} : x ∈ pack q ↔ x ∈ Icc q.1 q.2 := by
  rw [← SetLike.mem_coe, coe_pack]

/-- Packing a singleton endpoint pair yields `Interval.pure`. -/
@[simp]
theorem pack_pure (x : Coord n m → ℝ) : pack (x, x) = Interval.pure x := by
  rw [pack_of_le le_rfl]
  rfl

/-- Packing the underlying endpoints of a `NonemptyInterval` recovers it as a public state. -/
@[simp]
theorem pack_toProd (s : NonemptyInterval (Coord n m → ℝ)) : pack s.toProd = (s : State n m) := by
  rw [pack_of_le s.fst_le_snd]

/-- `pack q` equals a nonempty interval `s` if and only if `q = s.toProd`. -/
theorem pack_eq_coe_iff {q : Raw n m} {s : NonemptyInterval (Coord n m → ℝ)} :
    pack q = (s : State n m) ↔ q = s.toProd := by
  constructor
  · intro h
    have hq : q.1 ≤ q.2 := pack_ne_bot_iff.mp (h ▸ WithBot.coe_ne_bot)
    rw [pack_of_le hq, Interval.coe_inj] at h
    exact congrArg NonemptyInterval.toProd h
  · rintro rfl
    exact pack_toProd s

/-- On ordered raw tuples, `pack` is injective. -/
theorem pack_eq_pack_iff {q r : Raw n m} (hq : q.1 ≤ q.2) : pack q = pack r ↔ q = r := by
  rw [pack_of_le hq, eq_comm, pack_eq_coe_iff, eq_comm]

/-- Every nonbottom public state is the packed form of an ordered raw tuple. -/
theorem exists_raw_of_ne_bot {s : State n m} (hs : s ≠ ⊥) :
    ∃ q : Raw n m, q.1 ≤ q.2 ∧ pack q = s := by
  cases s using Interval.recBotCoe with
  | bot => exact absurd rfl hs
  | coe s => exact ⟨s.toProd, s.fst_le_snd, pack_toProd s⟩

/-- Packing is monotone from `Within` to the interval order on `State n m`. -/
theorem Within.pack_le {q r : Raw n m} (h : Within q r) : pack q ≤ pack r := by
  rw [← Interval.coe_subset_coe, coe_pack, coe_pack]
  exact h.Icc_subset

/-- For an ordered raw tuple, the public interval order agrees with endpoint containment. -/
theorem pack_le_pack_iff {q r : Raw n m} (hq : q.1 ≤ q.2) : pack q ≤ pack r ↔ Within q r := by
  rw [← Interval.coe_subset_coe, coe_pack, coe_pack]
  exact Icc_subset_Icc_iff_within hq

/-! ### Total coordinate width -/

/-- The sum of all variable and row endpoint widths. -/
def width (q : Raw n m) : ℝ := ∑ c, (q.2 c - q.1 c)

/-- Definitional unfolding of `width`. -/
theorem width_def (q : Raw n m) : width q = ∑ c, (q.2 c - q.1 c) :=
  (rfl)

/-- Decomposition of total width into variable width plus row width. -/
theorem width_eq_sum_add_sum (q : Raw n m) :
    width q =
      (∑ j : Fin n, (q.2 (.inl j) - q.1 (.inl j))) +
        ∑ i : Fin m, (q.2 (.inr i) - q.1 (.inr i)) :=
  Fintype.sum_sum_type _

/-- Every singleton raw tuple has width zero. -/
@[simp]
theorem width_pure (x : Coord n m → ℝ) : width (x, x) = 0 := by
  simp [width_def]

/-- An ordered raw tuple has nonnegative width. -/
theorem width_nonneg {q : Raw n m} (hq : q.1 ≤ q.2) : 0 ≤ width q :=
  Finset.sum_nonneg fun c _ => sub_nonneg.mpr (hq c)

/-- An ordered raw tuple has width zero if and only if its lower and upper endpoints coincide. -/
theorem width_eq_zero_iff {q : Raw n m} (hq : q.1 ≤ q.2) : width q = 0 ↔ q.1 = q.2 := by
  rw [width_def, Finset.sum_eq_zero_iff_of_nonneg fun c _ => sub_nonneg.mpr (hq c)]
  simp only [Finset.mem_univ, true_implies, sub_eq_zero, funext_iff]
  exact forall_congr' fun _ => eq_comm

/-- Endpoint containment implies monotonicity of total width. -/
theorem Within.width_le {q r : Raw n m} (h : Within q r) : width q ≤ width r :=
  Finset.sum_le_sum fun c _ => sub_le_sub (h.2 c) (h.1 c)

/-- Endpoint containment together with equal total width forces equality of raw tuples. -/
theorem eq_of_within_of_width_eq {q r : Raw n m} (h : Within q r) (hw : width q = width r) :
    q = r := by
  have hcoord : ∀ c ∈ (Finset.univ : Finset (Coord n m)),
      q.2 c - q.1 c = r.2 c - r.1 c :=
    (Finset.sum_eq_sum_iff_of_le fun c _ => sub_le_sub (h.2 c) (h.1 c)).mp hw
  refine Prod.ext (funext fun c => ?_) (funext fun c => ?_) <;>
    · have := hcoord c (Finset.mem_univ c)
      have := h.1 c
      have := h.2 c
      grind

/-- Strict endpoint containment gives strictly smaller total width. -/
theorem Within.width_lt_of_ne {q r : Raw n m} (h : Within q r) (hne : q ≠ r) :
    width q < width r :=
  lt_of_le_of_ne h.width_le fun hw => hne (eq_of_within_of_width_eq h hw)

/-! ### Signed coefficient products, row images, and omitted sums -/

/-- Lower endpoint of a signed coefficient product, with zero coefficients contributing zero. -/
def zLo (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) : ℝ :=
  if 0 ≤ A i j then A i j * q.1 (.inl j) else A i j * q.2 (.inl j)

/-- Upper endpoint of a signed coefficient product, with zero coefficients contributing zero. -/
def zHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) : ℝ :=
  if 0 ≤ A i j then A i j * q.2 (.inl j) else A i j * q.1 (.inl j)

/-- Sum of signed product lower endpoints for one affine row. -/
def imageLo (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) : ℝ :=
  ∑ j, zLo A q i j

/-- Sum of signed product upper endpoints for one affine row. -/
def imageHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) : ℝ :=
  ∑ j, zHi A q i j

/-- Row lower sum omitting one variable coordinate. -/
def restLo (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.erase j, zLo A q i k

/-- Row upper sum omitting one variable coordinate. -/
def restHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.erase j, zHi A q i k

/-- Signed lower product for a nonnegative coefficient. -/
theorem zLo_of_nonneg {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : 0 ≤ A i j) : zLo A q i j = A i j * q.1 (.inl j) := by
  simp [zLo, h]

/-- Signed lower product for a nonpositive coefficient (including zero). -/
theorem zLo_of_nonpos {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j ≤ 0) : zLo A q i j = A i j * q.2 (.inl j) := by
  unfold zLo
  split_ifs with h0
  · have hz : A i j = 0 := le_antisymm h h0
    simp [hz]
  · rfl

/-- A zero coefficient gives signed lower product zero. -/
theorem zLo_of_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j = 0) : zLo A q i j = 0 := by
  rw [zLo_of_nonneg h.ge, h, zero_mul]

/-- Signed upper product for a nonnegative coefficient. -/
theorem zHi_of_nonneg {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : 0 ≤ A i j) : zHi A q i j = A i j * q.2 (.inl j) := by
  simp [zHi, h]

/-- Signed upper product for a nonpositive coefficient (including zero). -/
theorem zHi_of_nonpos {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j ≤ 0) : zHi A q i j = A i j * q.1 (.inl j) := by
  unfold zHi
  split_ifs with h0
  · have hz : A i j = 0 := le_antisymm h h0
    simp [hz]
  · rfl

/-- A zero coefficient gives signed upper product zero. -/
theorem zHi_of_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j = 0) : zHi A q i j = 0 := by
  rw [zHi_of_nonneg h.ge, h, zero_mul]

/-- The zero matrix has zero signed lower products. -/
@[simp]
theorem zLo_zero (q : Raw n m) (i : Fin m) (j : Fin n) :
    zLo (0 : Matrix (Fin m) (Fin n) ℝ) q i j = 0 :=
  zLo_of_zero rfl

/-- The zero matrix has zero signed upper products. -/
@[simp]
theorem zHi_zero (q : Raw n m) (i : Fin m) (j : Fin n) :
    zHi (0 : Matrix (Fin m) (Fin n) ℝ) q i j = 0 :=
  zHi_of_zero rfl

/-- On a singleton tuple, the signed lower product is the ordinary product. -/
@[simp]
theorem zLo_pure (A : Matrix (Fin m) (Fin n) ℝ) (x : Coord n m → ℝ) (i : Fin m) (j : Fin n) :
    zLo A (x, x) i j = A i j * x (.inl j) := by
  unfold zLo
  split_ifs <;> rfl

/-- On a singleton tuple, the signed upper product is the ordinary product. -/
@[simp]
theorem zHi_pure (A : Matrix (Fin m) (Fin n) ℝ) (x : Coord n m → ℝ) (i : Fin m) (j : Fin n) :
    zHi A (x, x) i j = A i j * x (.inl j) := by
  unfold zHi
  split_ifs <;> rfl

/-- Signed product endpoints are ordered whenever the variable coordinate is ordered. -/
theorem zLo_le_zHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (hq : q.1 (.inl j) ≤ q.2 (.inl j)) : zLo A q i j ≤ zHi A q i j := by
  by_cases h : 0 ≤ A i j
  · rw [zLo_of_nonneg h, zHi_of_nonneg h]
    exact mul_le_mul_of_nonneg_left hq h
  · rw [zLo_of_nonpos (le_of_not_ge h), zHi_of_nonpos (le_of_not_ge h)]
    exact mul_le_mul_of_nonpos_left hq (le_of_not_ge h)

/-- Lower enclosure of `A i j * x` by `zLo`. -/
theorem zLo_le_mul {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n} {x : ℝ}
    (hx : x ∈ Icc (q.1 (.inl j)) (q.2 (.inl j))) : zLo A q i j ≤ A i j * x := by
  by_cases h : 0 ≤ A i j
  · rw [zLo_of_nonneg h]
    exact mul_le_mul_of_nonneg_left hx.1 h
  · rw [zLo_of_nonpos (le_of_not_ge h)]
    exact mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge h)

/-- Upper enclosure of `A i j * x` by `zHi`. -/
theorem mul_le_zHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n} {x : ℝ}
    (hx : x ∈ Icc (q.1 (.inl j)) (q.2 (.inl j))) : A i j * x ≤ zHi A q i j := by
  by_cases h : 0 ≤ A i j
  · rw [zHi_of_nonneg h]
    exact mul_le_mul_of_nonneg_left hx.2 h
  · rw [zHi_of_nonpos (le_of_not_ge h)]
    exact mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge h)

/-- Exact attainment of `zLo` as the minimum of `t ↦ A i j * t` on the ordered variable interval. -/
theorem exists_isMinOn_mul_eq_zLo {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    {j : Fin n} (hq : q.1 (.inl j) ≤ q.2 (.inl j)) :
    ∃ x ∈ Icc (q.1 (.inl j)) (q.2 (.inl j)),
      A i j * x = zLo A q i j ∧
      IsMinOn (fun t => A i j * t) (Icc (q.1 (.inl j)) (q.2 (.inl j))) x := by
  let x : ℝ := if 0 ≤ A i j then q.1 (.inl j) else q.2 (.inl j)
  have hval : A i j * x = zLo A q i j := by
    by_cases h : 0 ≤ A i j
    · simp [x, zLo_of_nonneg h, h]
    · simp [x, zLo_of_nonpos (le_of_not_ge h), h]
  refine ⟨x, ?_, hval, fun t ht => by
    simpa [hval] using zLo_le_mul (A := A) (q := q) (i := i) (j := j) ht⟩
  dsimp only [x]
  split_ifs <;> exact ⟨by grind, by grind⟩

/-- Exact attainment of `zHi` as the maximum of `t ↦ A i j * t` on the ordered variable interval. -/
theorem exists_isMaxOn_mul_eq_zHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    {j : Fin n} (hq : q.1 (.inl j) ≤ q.2 (.inl j)) :
    ∃ x ∈ Icc (q.1 (.inl j)) (q.2 (.inl j)),
      A i j * x = zHi A q i j ∧
      IsMaxOn (fun t => A i j * t) (Icc (q.1 (.inl j)) (q.2 (.inl j))) x := by
  let x : ℝ := if 0 ≤ A i j then q.2 (.inl j) else q.1 (.inl j)
  have hval : A i j * x = zHi A q i j := by
    by_cases h : 0 ≤ A i j
    · simp [x, zHi_of_nonneg h, h]
    · simp [x, zHi_of_nonpos (le_of_not_ge h), h]
  refine ⟨x, ?_, hval, fun t ht => by
    simpa [hval] using mul_le_zHi (A := A) (q := q) (i := i) (j := j) ht⟩
  dsimp only [x]
  split_ifs <;> exact ⟨by grind, by grind⟩

/-- Signed lower products increase under endpoint containment. -/
theorem Within.zLo_le {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} (h : Within q r)
    (i : Fin m) (j : Fin n) : zLo A r i j ≤ zLo A q i j := by
  by_cases ha : 0 ≤ A i j
  · rw [zLo_of_nonneg ha, zLo_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (h.1 (.inl j)) ha
  · rw [zLo_of_nonpos (le_of_not_ge ha), zLo_of_nonpos (le_of_not_ge ha)]
    exact mul_le_mul_of_nonpos_left (h.2 (.inl j)) (le_of_not_ge ha)

/-- Signed upper products decrease under endpoint containment. -/
theorem Within.zHi_le {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} (h : Within q r)
    (i : Fin m) (j : Fin n) : zHi A q i j ≤ zHi A r i j := by
  by_cases ha : 0 ≤ A i j
  · rw [zHi_of_nonneg ha, zHi_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (h.2 (.inl j)) ha
  · rw [zHi_of_nonpos (le_of_not_ge ha), zHi_of_nonpos (le_of_not_ge ha)]
    exact mul_le_mul_of_nonpos_left (h.1 (.inl j)) (le_of_not_ge ha)

/-- Definitional unfolding of `imageLo`. -/
theorem imageLo_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    imageLo A q i = ∑ j, zLo A q i j :=
  (rfl)

/-- Definitional unfolding of `imageHi`. -/
theorem imageHi_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    imageHi A q i = ∑ j, zHi A q i j :=
  (rfl)

/-- Definitional unfolding of `restLo`. -/
theorem restLo_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    restLo A q i j = ∑ k ∈ Finset.univ.erase j, zLo A q i k :=
  (rfl)

/-- Definitional unfolding of `restHi`. -/
theorem restHi_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    restHi A q i j = ∑ k ∈ Finset.univ.erase j, zHi A q i k :=
  (rfl)

/-- Decomposition of a row lower image into one signed product plus its omitted sum. -/
theorem imageLo_eq_zLo_add_restLo (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m)
    (j : Fin n) : imageLo A q i = zLo A q i j + restLo A q i j :=
  (Finset.add_sum_erase Finset.univ (fun k => zLo A q i k) (Finset.mem_univ j)).symm

/-- Decomposition of a row upper image into one signed product plus its omitted sum. -/
theorem imageHi_eq_zHi_add_restHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m)
    (j : Fin n) : imageHi A q i = zHi A q i j + restHi A q i j :=
  (Finset.add_sum_erase Finset.univ (fun k => zHi A q i k) (Finset.mem_univ j)).symm

/-- A zero matrix entry leaves the row lower image equal to its omitted sum. -/
theorem imageLo_eq_restLo_of_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    {j : Fin n} (h : A i j = 0) : imageLo A q i = restLo A q i j := by
  rw [imageLo_eq_zLo_add_restLo A q i j, zLo_of_zero h, zero_add]

/-- A zero matrix entry leaves the row upper image equal to its omitted sum. -/
theorem imageHi_eq_restHi_of_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    {j : Fin n} (h : A i j = 0) : imageHi A q i = restHi A q i j := by
  rw [imageHi_eq_zHi_add_restHi A q i j, zHi_of_zero h, zero_add]

/-- A zero row has lower affine image zero. -/
theorem imageLo_eq_zero_of_row_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    (h : ∀ j, A i j = 0) : imageLo A q i = 0 := by
  rw [imageLo_def]
  exact Finset.sum_eq_zero fun j _ => zLo_of_zero (h j)

/-- A zero row has upper affine image zero. -/
theorem imageHi_eq_zero_of_row_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    (h : ∀ j, A i j = 0) : imageHi A q i = 0 := by
  rw [imageHi_def]
  exact Finset.sum_eq_zero fun j _ => zHi_of_zero (h j)

/-- The zero matrix has zero lower affine images. -/
@[simp]
theorem imageLo_zero (q : Raw n m) (i : Fin m) :
    imageLo (0 : Matrix (Fin m) (Fin n) ℝ) q i = 0 :=
  imageLo_eq_zero_of_row_zero fun _ => rfl

/-- The zero matrix has zero upper affine images. -/
@[simp]
theorem imageHi_zero (q : Raw n m) (i : Fin m) :
    imageHi (0 : Matrix (Fin m) (Fin n) ℝ) q i = 0 :=
  imageHi_eq_zero_of_row_zero fun _ => rfl

/-- The zero matrix has zero omitted lower sums. -/
@[simp]
theorem restLo_zero (q : Raw n m) (i : Fin m) (j : Fin n) :
    restLo (0 : Matrix (Fin m) (Fin n) ℝ) q i j = 0 := by
  simp [restLo_def]

/-- The zero matrix has zero omitted upper sums. -/
@[simp]
theorem restHi_zero (q : Raw n m) (i : Fin m) (j : Fin n) :
    restHi (0 : Matrix (Fin m) (Fin n) ℝ) q i j = 0 := by
  simp [restHi_def]

/-- On a singleton tuple, the lower row image equals the matrix-vector product. -/
@[simp]
theorem imageLo_pure (A : Matrix (Fin m) (Fin n) ℝ) (x : Coord n m → ℝ) (i : Fin m) :
    imageLo A (x, x) i = A.mulVec (fun j => x (.inl j)) i := by
  simp [imageLo_def, Matrix.mulVec, dotProduct]

/-- On a singleton tuple, the upper row image equals the matrix-vector product. -/
@[simp]
theorem imageHi_pure (A : Matrix (Fin m) (Fin n) ℝ) (x : Coord n m → ℝ) (i : Fin m) :
    imageHi A (x, x) i = A.mulVec (fun j => x (.inl j)) i := by
  simp [imageHi_def, Matrix.mulVec, dotProduct]

/-- With at most one variable, every omitted lower sum is zero. -/
theorem restLo_eq_zero_of_subsingleton [Subsingleton (Fin n)] (A : Matrix (Fin m) (Fin n) ℝ)
    (q : Raw n m) (i : Fin m) (j : Fin n) : restLo A q i j = 0 := by
  rw [restLo_def]
  exact Finset.sum_eq_zero fun k hk => absurd (Subsingleton.elim k j) (Finset.ne_of_mem_erase hk)

/-- With at most one variable, every omitted upper sum is zero. -/
theorem restHi_eq_zero_of_subsingleton [Subsingleton (Fin n)] (A : Matrix (Fin m) (Fin n) ℝ)
    (q : Raw n m) (i : Fin m) (j : Fin n) : restHi A q i j = 0 := by
  rw [restHi_def]
  exact Finset.sum_eq_zero fun k hk => absurd (Subsingleton.elim k j) (Finset.ne_of_mem_erase hk)

/-- Row image endpoints are ordered whenever the variable endpoints are ordered. -/
theorem imageLo_le_imageHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    (hq : ∀ j, q.1 (.inl j) ≤ q.2 (.inl j)) : imageLo A q i ≤ imageHi A q i :=
  Finset.sum_le_sum fun j _ => zLo_le_zHi (hq j)

/-- Omitted sums are ordered whenever the remaining variable endpoints are ordered. -/
theorem restLo_le_restHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (hq : ∀ k, k ≠ j → q.1 (.inl k) ≤ q.2 (.inl k)) : restLo A q i j ≤ restHi A q i j :=
  Finset.sum_le_sum fun k hk => zLo_le_zHi (hq k (Finset.ne_of_mem_erase hk))

/-- Lower enclosure of `A.mulVec x i` by `imageLo`. -/
theorem imageLo_le_mulVec {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    {x : Fin n → ℝ} (hx : ∀ j, x j ∈ Icc (q.1 (.inl j)) (q.2 (.inl j))) :
    imageLo A q i ≤ A.mulVec x i := by
  rw [imageLo_def, Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => zLo_le_mul (hx j)

/-- Upper enclosure of `A.mulVec x i` by `imageHi`. -/
theorem mulVec_le_imageHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    {x : Fin n → ℝ} (hx : ∀ j, x j ∈ Icc (q.1 (.inl j)) (q.2 (.inl j))) :
    A.mulVec x i ≤ imageHi A q i := by
  rw [imageHi_def, Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_zHi (hx j)

/-- Lower enclosure of the omitted row sum by `restLo`. -/
theorem restLo_le_sum_erase {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    {x : Fin n → ℝ} (hx : ∀ k, k ≠ j → x k ∈ Icc (q.1 (.inl k)) (q.2 (.inl k))) :
    restLo A q i j ≤ ∑ k ∈ Finset.univ.erase j, A i k * x k :=
  Finset.sum_le_sum fun k hk => zLo_le_mul (hx k (Finset.ne_of_mem_erase hk))

/-- Upper enclosure of the omitted row sum by `restHi`. -/
theorem sum_erase_le_restHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    {x : Fin n → ℝ} (hx : ∀ k, k ≠ j → x k ∈ Icc (q.1 (.inl k)) (q.2 (.inl k))) :
    ∑ k ∈ Finset.univ.erase j, A i k * x k ≤ restHi A q i j :=
  Finset.sum_le_sum fun k hk => mul_le_zHi (hx k (Finset.ne_of_mem_erase hk))

/-- Exact attainment of `imageLo` as the minimum of `v ↦ A.mulVec v i` on an ordered variable
box. -/
theorem exists_isMinOn_mulVec_eq_imageLo {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    (hq : ∀ j, q.1 (.inl j) ≤ q.2 (.inl j)) :
    ∃ x ∈ Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j)),
      A.mulVec x i = imageLo A q i ∧
      IsMinOn (fun v => A.mulVec v i)
        (Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j))) x := by
  let x : Fin n → ℝ := fun j => if 0 ≤ A i j then q.1 (.inl j) else q.2 (.inl j)
  have hxmem : x ∈ Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j)) := by
    refine ⟨fun j => ?_, fun j => ?_⟩ <;> dsimp [x] <;> split_ifs <;> grind
  have hval : A.mulVec x i = imageLo A q i := by
    rw [imageLo_def, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 0 ≤ A i j
    · simp [x, zLo_of_nonneg h, h]
    · simp [x, zLo_of_nonpos (le_of_not_ge h), h]
  refine ⟨x, hxmem, hval, fun v hv => ?_⟩
  simpa [hval] using imageLo_le_mulVec (A := A) (q := q) (i := i) fun j => ⟨hv.1 j, hv.2 j⟩

/-- Exact attainment of `imageHi` as the maximum of `v ↦ A.mulVec v i` on an ordered variable
box. -/
theorem exists_isMaxOn_mulVec_eq_imageHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    (hq : ∀ j, q.1 (.inl j) ≤ q.2 (.inl j)) :
    ∃ x ∈ Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j)),
      A.mulVec x i = imageHi A q i ∧
      IsMaxOn (fun v => A.mulVec v i)
        (Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j))) x := by
  let x : Fin n → ℝ := fun j => if 0 ≤ A i j then q.2 (.inl j) else q.1 (.inl j)
  have hxmem : x ∈ Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j)) := by
    refine ⟨fun j => ?_, fun j => ?_⟩ <;> dsimp [x] <;> split_ifs <;> grind
  have hval : A.mulVec x i = imageHi A q i := by
    rw [imageHi_def, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 0 ≤ A i j
    · simp [x, zHi_of_nonneg h, h]
    · simp [x, zHi_of_nonpos (le_of_not_ge h), h]
  refine ⟨x, hxmem, hval, fun v hv => ?_⟩
  simpa [hval] using mulVec_le_imageHi (A := A) (q := q) (i := i) fun j => ⟨hv.1 j, hv.2 j⟩

/-- Row lower images increase under endpoint containment. -/
theorem Within.imageLo_le {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} (h : Within q r)
    (i : Fin m) : imageLo A r i ≤ imageLo A q i :=
  Finset.sum_le_sum fun j _ => h.zLo_le i j

/-- Row upper images decrease under endpoint containment. -/
theorem Within.imageHi_le {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} (h : Within q r)
    (i : Fin m) : imageHi A q i ≤ imageHi A r i :=
  Finset.sum_le_sum fun j _ => h.zHi_le i j

/-- Omitted lower sums increase under endpoint containment. -/
theorem Within.restLo_le {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} (h : Within q r)
    (i : Fin m) (j : Fin n) : restLo A r i j ≤ restLo A q i j :=
  Finset.sum_le_sum fun k _ => h.zLo_le i k

/-- Omitted upper sums decrease under endpoint containment. -/
theorem Within.restHi_le {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} (h : Within q r)
    (i : Fin m) (j : Fin n) : restHi A q i j ≤ restHi A r i j :=
  Finset.sum_le_sum fun k _ => h.zHi_le i k

end

end TauCeti.AffineBoundTightening
