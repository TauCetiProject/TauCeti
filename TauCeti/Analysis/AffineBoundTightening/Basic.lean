/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Interval.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

/-!
# Joint variable-and-row intervals and signed affine arithmetic

This file introduces the joint variable-and-row endpoint model and signed affine interval
arithmetic for finite-real simultaneous affine bound tightening.

Variables are indexed by `Fin n` and affine rows by `Fin m`, allowing either dimension to be zero.
Raw endpoint tuples `Raw n m` store finite lower and upper vectors on `Coord n m := Fin n ⊕ Fin m`,
including unordered (invalid) pairs; `pack` maps ordered pairs to Mathlib's
`Interval (Coord n m → ℝ)` and unordered pairs to global `⊥`, keeping `⊥` distinct from the unique
nonempty zero-coordinate box when `n = m = 0`.

## Main definitions

* `TauCeti.AffineBoundTightening.Coord`, `TauCeti.AffineBoundTightening.Raw`,
  `TauCeti.AffineBoundTightening.State`, `TauCeti.AffineBoundTightening.pack`: joint coordinates,
  raw lower/upper endpoint pairs, public intervals with one global bottom, and packing.
* `TauCeti.AffineBoundTightening.Within`, `TauCeti.AffineBoundTightening.width`: raw endpoint
  containment (valid also for unordered pairs) and total variable-plus-row width.
* `TauCeti.AffineBoundTightening.zLo`, `TauCeti.AffineBoundTightening.zHi`,
  `TauCeti.AffineBoundTightening.imageLo`, `TauCeti.AffineBoundTightening.imageHi`,
  `TauCeti.AffineBoundTightening.restLo`, `TauCeti.AffineBoundTightening.restHi`: signed product
  endpoints, affine row image endpoints, and omitted row sums.

## Main results

* `TauCeti.AffineBoundTightening.pack_le_pack_iff`: for an ordered raw tuple `q`, public interval
  inclusion `pack q ≤ pack r` agrees with raw endpoint containment `Within q r`.
* `TauCeti.AffineBoundTightening.eq_of_within_of_width_eq`: containment together with equal total
  width forces equality of raw endpoint tuples.
* `TauCeti.AffineBoundTightening.isLeast_image_mulVec_Icc`,
  `TauCeti.AffineBoundTightening.isGreatest_image_mulVec_Icc`: `imageLo` and `imageHi` are the
  exact attained extrema of each affine row over an ordered variable box.

## References

* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *Feasibility-Based Bounds Tightening via Fixed
  Points*, COCOA 2010, LNCS 6508, §4, pp. 71–73, equations (9)–(10).
-/

public section

open scoped BigOperators
open Set

namespace TauCeti.AffineBoundTightening

/-! ### Joint endpoints and public intervals -/

/-- Joint variable and row coordinates, with variables on the left and rows on the right. -/
abbrev Coord (n m : ℕ) := Fin n ⊕ Fin m

/-- Real lower and upper endpoints, including pairs whose lower endpoint exceeds the upper. -/
abbrev Raw (n m : ℕ) := (Coord n m → ℝ) × (Coord n m → ℝ)

/-- A nonempty joint closed interval or one global empty state. -/
abbrev State (n m : ℕ) := Interval (Coord n m → ℝ)

variable {n m : ℕ}

/-- Extensionality for raw endpoint tuples split into variable and row coordinates. -/
theorem raw_ext {q r : Raw n m}
    (hxL : ∀ j, q.1 (.inl j) = r.1 (.inl j))
    (hxU : ∀ j, q.2 (.inl j) = r.2 (.inl j))
    (hbL : ∀ i, q.1 (.inr i) = r.1 (.inr i))
    (hbU : ∀ i, q.2 (.inr i) = r.2 (.inr i)) : q = r := by
  refine Prod.ext (funext fun c => ?_) (funext fun c => ?_)
  · cases c with
    | inl j => exact hxL j
    | inr i => exact hbL i
  · cases c with
    | inl j => exact hxU j
    | inr i => exact hbU i

/-- Convert ordered endpoints to a nonempty interval and unordered endpoints to global bottom. -/
noncomputable def pack (q : Raw n m) : State n m :=
  if h : q.1 ≤ q.2 then (⟨q, h⟩ : NonemptyInterval _) else ⊥

theorem pack_of_le {q : Raw n m} (hq : q.1 ≤ q.2) :
    pack q = (⟨q, hq⟩ : NonemptyInterval (Coord n m → ℝ)) := by
  simp [pack, hq]

theorem pack_of_not_le {q : Raw n m} (hq : ¬ q.1 ≤ q.2) : pack q = ⊥ := by
  simp [pack, hq]

@[simp]
theorem coe_pack (q : Raw n m) : (pack q : Set (Coord n m → ℝ)) = Icc q.1 q.2 := by
  by_cases hq : q.1 ≤ q.2
  · rw [pack_of_le hq, Interval.coe_coe, NonemptyInterval.coe_def]
  · rw [pack_of_not_le hq, Interval.coe_bot, Icc_eq_empty hq]

@[simp]
theorem mem_pack (q : Raw n m) (y : Coord n m → ℝ) : y ∈ pack q ↔ y ∈ Icc q.1 q.2 := by
  rw [← SetLike.mem_coe, coe_pack]

@[simp]
theorem pack_eq_bot_iff (q : Raw n m) : pack q = ⊥ ↔ ¬ q.1 ≤ q.2 := by
  by_cases hq : q.1 ≤ q.2
  · rw [pack_of_le hq]
    exact iff_of_false WithBot.coe_ne_bot (not_not.mpr hq)
  · rw [pack_of_not_le hq]
    exact iff_of_true rfl hq

@[simp]
theorem pack_singleton (y : Coord n m → ℝ) : pack (y, y) = Interval.pure y := by
  rw [pack_of_le le_rfl]
  rfl

@[simp]
theorem pack_toProd (s : NonemptyInterval (Coord n m → ℝ)) : pack s.toProd = s := by
  rw [pack_of_le s.fst_le_snd]

theorem exists_pack_eq_of_ne_bot {s : State n m} (hs : s ≠ ⊥) :
    ∃ q : Raw n m, q.1 ≤ q.2 ∧ pack q = s := by
  lift s to NonemptyInterval (Coord n m → ℝ) using hs
  exact ⟨s.toProd, s.fst_le_snd, pack_toProd s⟩

theorem pack_inj_of_le {q r : Raw n m} (hq : q.1 ≤ q.2) (hr : r.1 ≤ r.2) :
    pack q = pack r ↔ q = r := by
  rw [pack_of_le hq, pack_of_le hr, Interval.coe_inj, ← NonemptyInterval.toProd_injective.eq_iff]

/-! ### Endpoint containment and total width -/

/-- Endpoint containment: reverse lower and forward upper inequalities, also for unordered pairs. -/
def Within (q r : Raw n m) : Prop := r.1 ≤ q.1 ∧ q.2 ≤ r.2

theorem within_def {q r : Raw n m} : Within q r ↔ r.1 ≤ q.1 ∧ q.2 ≤ r.2 :=
  Iff.rfl

theorem Within.le_fst {q r : Raw n m} (h : Within q r) : r.1 ≤ q.1 := h.1

theorem Within.snd_le {q r : Raw n m} (h : Within q r) : q.2 ≤ r.2 := h.2

@[refl, simp]
theorem Within.refl (q : Raw n m) : Within q q := ⟨le_rfl, le_rfl⟩

theorem Within.trans {q r s : Raw n m} (hqr : Within q r) (hrs : Within r s) : Within q s :=
  ⟨hrs.1.trans hqr.1, hqr.2.trans hrs.2⟩

theorem Within.antisymm {q r : Raw n m} (hqr : Within q r) (hrq : Within r q) : q = r :=
  Prod.ext (le_antisymm hrq.1 hqr.1) (le_antisymm hqr.2 hrq.2)

theorem Within.fst_le_snd {q r : Raw n m} (h : Within q r) (hq : q.1 ≤ q.2) : r.1 ≤ r.2 :=
  h.1.trans (hq.trans h.2)

theorem Within.not_le_of_not_le {q r : Raw n m} (h : Within q r) (hr : ¬ r.1 ≤ r.2) :
    ¬ q.1 ≤ q.2 :=
  fun hq => hr (h.fst_le_snd hq)

theorem Within.Icc_subset {q r : Raw n m} (h : Within q r) : Icc q.1 q.2 ⊆ Icc r.1 r.2 :=
  Icc_subset_Icc h.1 h.2

theorem Icc_subset_Icc_iff_within {q r : Raw n m} (hq : q.1 ≤ q.2) :
    Icc q.1 q.2 ⊆ Icc r.1 r.2 ↔ Within q r :=
  Icc_subset_Icc_iff hq

theorem pack_le_pack_of_within {q r : Raw n m} (h : Within q r) : pack q ≤ pack r := by
  rw [← Interval.coe_subset_coe, coe_pack, coe_pack]
  exact h.Icc_subset

/-- For an ordered raw tuple `q`, public interval inclusion `pack q ≤ pack r` agrees with raw
endpoint containment `Within q r`. -/
theorem pack_le_pack_iff {q r : Raw n m} (hq : q.1 ≤ q.2) : pack q ≤ pack r ↔ Within q r := by
  rw [← Interval.coe_subset_coe, coe_pack, coe_pack, Icc_subset_Icc_iff_within hq]

/-- The sum of all variable and row endpoint widths. -/
def width (q : Raw n m) : ℝ := ∑ c, (q.2 c - q.1 c)

theorem width_def (q : Raw n m) : width q = ∑ c, (q.2 c - q.1 c) := (rfl)

theorem width_eq_sum_var_add_row (q : Raw n m) :
    width q = (∑ j : Fin n, (q.2 (.inl j) - q.1 (.inl j))) +
      ∑ i : Fin m, (q.2 (.inr i) - q.1 (.inr i)) :=
  Fintype.sum_sum_type fun c => q.2 c - q.1 c

theorem width_nonneg {q : Raw n m} (hq : q.1 ≤ q.2) : 0 ≤ width q :=
  Finset.sum_nonneg fun c _ => sub_nonneg.mpr (hq c)

@[simp]
theorem width_singleton (y : Coord n m → ℝ) : width (y, y) = 0 := by
  simp [width_def]

/-- An ordered raw tuple has zero total width iff its lower and upper endpoints coincide. -/
theorem width_eq_zero_iff {q : Raw n m} (hq : q.1 ≤ q.2) : width q = 0 ↔ q.1 = q.2 := by
  rw [width_def, Finset.sum_eq_zero_iff_of_nonneg fun c _ => sub_nonneg.mpr (hq c)]
  constructor
  · intro h
    funext c
    linarith [h c (Finset.mem_univ c)]
  · intro h c _
    simp [h]

theorem width_le_of_within {q r : Raw n m} (h : Within q r) : width q ≤ width r :=
  Finset.sum_le_sum fun c _ => sub_le_sub (h.2 c) (h.1 c)

/-- Endpoint containment together with equal total width forces equality of raw endpoint tuples. -/
theorem eq_of_within_of_width_eq {q r : Raw n m} (h : Within q r) (hw : width q = width r) :
    q = r := by
  have hterm : ∀ c ∈ (Finset.univ : Finset (Coord n m)),
      q.2 c - q.1 c = r.2 c - r.1 c :=
    (Finset.sum_eq_sum_iff_of_le fun c _ => sub_le_sub (h.2 c) (h.1 c)).mp hw
  refine Prod.ext (funext fun c => ?_) (funext fun c => ?_)
  · linarith [h.1 c, h.2 c, hterm c (Finset.mem_univ c)]
  · linarith [h.1 c, h.2 c, hterm c (Finset.mem_univ c)]

theorem width_lt_of_within_of_ne {q r : Raw n m} (h : Within q r) (hne : q ≠ r) :
    width q < width r :=
  lt_of_le_of_ne (width_le_of_within h) fun hw => hne (eq_of_within_of_width_eq h hw)

/-! ### Signed products, row images, and omitted sums -/

/-- Lower endpoint of a signed coefficient product, with zero coefficients contributing zero. -/
noncomputable def zLo (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) : ℝ :=
  if 0 ≤ A i j then A i j * q.1 (.inl j) else A i j * q.2 (.inl j)

/-- Upper endpoint of a signed coefficient product, with zero coefficients contributing zero. -/
noncomputable def zHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) : ℝ :=
  if 0 ≤ A i j then A i j * q.2 (.inl j) else A i j * q.1 (.inl j)

/-- Sum of signed product lower endpoints for one affine row. -/
noncomputable def imageLo (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) : ℝ :=
  ∑ j, zLo A q i j

/-- Sum of signed product upper endpoints for one affine row. -/
noncomputable def imageHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) : ℝ :=
  ∑ j, zHi A q i j

/-- Row lower sum omitting one variable coordinate. -/
noncomputable def restLo (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.erase j, zLo A q i k

/-- Row upper sum omitting one variable coordinate. -/
noncomputable def restHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.erase j, zHi A q i k

theorem zLo_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    zLo A q i j = if 0 ≤ A i j then A i j * q.1 (.inl j) else A i j * q.2 (.inl j) := (rfl)

theorem zHi_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    zHi A q i j = if 0 ≤ A i j then A i j * q.2 (.inl j) else A i j * q.1 (.inl j) := (rfl)

theorem imageLo_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    imageLo A q i = ∑ j, zLo A q i j := (rfl)

theorem imageHi_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    imageHi A q i = ∑ j, zHi A q i j := (rfl)

theorem restLo_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    restLo A q i j = ∑ k ∈ Finset.univ.erase j, zLo A q i k := (rfl)

theorem restHi_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    restHi A q i j = ∑ k ∈ Finset.univ.erase j, zHi A q i k := (rfl)

theorem zLo_of_nonneg {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : 0 ≤ A i j) : zLo A q i j = A i j * q.1 (.inl j) := by
  simp [zLo_def, h]

theorem zLo_of_nonpos {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j ≤ 0) : zLo A q i j = A i j * q.2 (.inl j) := by
  rcases h.lt_or_eq with hlt | heq
  · simp [zLo_def, not_le.mpr hlt]
  · simp [zLo_def, heq]

theorem zLo_of_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j = 0) : zLo A q i j = 0 := by
  simp [zLo_def, h]

theorem zHi_of_nonneg {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : 0 ≤ A i j) : zHi A q i j = A i j * q.2 (.inl j) := by
  simp [zHi_def, h]

theorem zHi_of_nonpos {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j ≤ 0) : zHi A q i j = A i j * q.1 (.inl j) := by
  rcases h.lt_or_eq with hlt | heq
  · simp [zHi_def, not_le.mpr hlt]
  · simp [zHi_def, heq]

theorem zHi_of_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j = 0) : zHi A q i j = 0 := by
  simp [zHi_def, h]

@[simp]
theorem zLo_zero (q : Raw n m) (i : Fin m) (j : Fin n) :
    zLo (0 : Matrix (Fin m) (Fin n) ℝ) q i j = 0 :=
  zLo_of_eq_zero rfl

@[simp]
theorem zHi_zero (q : Raw n m) (i : Fin m) (j : Fin n) :
    zHi (0 : Matrix (Fin m) (Fin n) ℝ) q i j = 0 :=
  zHi_of_eq_zero rfl

@[simp]
theorem imageLo_zero (q : Raw n m) (i : Fin m) :
    imageLo (0 : Matrix (Fin m) (Fin n) ℝ) q i = 0 := by
  simp [imageLo_def]

@[simp]
theorem imageHi_zero (q : Raw n m) (i : Fin m) :
    imageHi (0 : Matrix (Fin m) (Fin n) ℝ) q i = 0 := by
  simp [imageHi_def]

@[simp]
theorem restLo_zero (q : Raw n m) (i : Fin m) (j : Fin n) :
    restLo (0 : Matrix (Fin m) (Fin n) ℝ) q i j = 0 := by
  simp [restLo_def]

@[simp]
theorem restHi_zero (q : Raw n m) (i : Fin m) (j : Fin n) :
    restHi (0 : Matrix (Fin m) (Fin n) ℝ) q i j = 0 := by
  simp [restHi_def]

@[simp]
theorem zLo_singleton (A : Matrix (Fin m) (Fin n) ℝ) (y : Coord n m → ℝ) (i : Fin m) (j : Fin n) :
    zLo A (y, y) i j = A i j * y (.inl j) := by
  simp [zLo_def]

@[simp]
theorem zHi_singleton (A : Matrix (Fin m) (Fin n) ℝ) (y : Coord n m → ℝ) (i : Fin m) (j : Fin n) :
    zHi A (y, y) i j = A i j * y (.inl j) := by
  simp [zHi_def]

@[simp]
theorem imageLo_singleton (A : Matrix (Fin m) (Fin n) ℝ) (y : Coord n m → ℝ) (i : Fin m) :
    imageLo A (y, y) i = A.mulVec (fun j => y (.inl j)) i := by
  simp [imageLo_def, Matrix.mulVec, dotProduct]

@[simp]
theorem imageHi_singleton (A : Matrix (Fin m) (Fin n) ℝ) (y : Coord n m → ℝ) (i : Fin m) :
    imageHi A (y, y) i = A.mulVec (fun j => y (.inl j)) i := by
  simp [imageHi_def, Matrix.mulVec, dotProduct]

theorem zLo_congr_var {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m} {j : Fin n}
    (hL : q.1 (.inl j) = r.1 (.inl j)) (hU : q.2 (.inl j) = r.2 (.inl j)) :
    zLo A q i j = zLo A r i j := by
  simp only [zLo_def, hL, hU]

theorem zHi_congr_var {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m} {j : Fin n}
    (hL : q.1 (.inl j) = r.1 (.inl j)) (hU : q.2 (.inl j) = r.2 (.inl j)) :
    zHi A q i j = zHi A r i j := by
  simp only [zHi_def, hL, hU]

theorem imageLo_congr_var {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m}
    (hL : ∀ j, q.1 (.inl j) = r.1 (.inl j)) (hU : ∀ j, q.2 (.inl j) = r.2 (.inl j)) :
    imageLo A q i = imageLo A r i :=
  Finset.sum_congr rfl fun j _ => zLo_congr_var (hL j) (hU j)

theorem imageHi_congr_var {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m}
    (hL : ∀ j, q.1 (.inl j) = r.1 (.inl j)) (hU : ∀ j, q.2 (.inl j) = r.2 (.inl j)) :
    imageHi A q i = imageHi A r i :=
  Finset.sum_congr rfl fun j _ => zHi_congr_var (hL j) (hU j)

theorem restLo_congr_var {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m} {j : Fin n}
    (hL : ∀ k ≠ j, q.1 (.inl k) = r.1 (.inl k)) (hU : ∀ k ≠ j, q.2 (.inl k) = r.2 (.inl k)) :
    restLo A q i j = restLo A r i j :=
  Finset.sum_congr rfl fun k hk =>
    zLo_congr_var (hL k (Finset.ne_of_mem_erase hk)) (hU k (Finset.ne_of_mem_erase hk))

theorem restHi_congr_var {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m} {j : Fin n}
    (hL : ∀ k ≠ j, q.1 (.inl k) = r.1 (.inl k)) (hU : ∀ k ≠ j, q.2 (.inl k) = r.2 (.inl k)) :
    restHi A q i j = restHi A r i j :=
  Finset.sum_congr rfl fun k hk =>
    zHi_congr_var (hL k (Finset.ne_of_mem_erase hk)) (hU k (Finset.ne_of_mem_erase hk))

theorem imageLo_eq_zero_of_row_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    (h : ∀ j, A i j = 0) : imageLo A q i = 0 :=
  Finset.sum_eq_zero fun j _ => zLo_of_eq_zero (h j)

theorem imageHi_eq_zero_of_row_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    (h : ∀ j, A i j = 0) : imageHi A q i = 0 :=
  Finset.sum_eq_zero fun j _ => zHi_of_eq_zero (h j)

theorem zLo_le_zHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : q.1 (.inl j) ≤ q.2 (.inl j)) : zLo A q i j ≤ zHi A q i j := by
  by_cases ha : 0 ≤ A i j
  · rw [zLo_of_nonneg ha, zHi_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left h ha
  · have hneg : A i j ≤ 0 := (not_le.mp ha).le
    rw [zLo_of_nonpos hneg, zHi_of_nonpos hneg]
    exact mul_le_mul_of_nonpos_left h hneg

theorem zLo_le_mul {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n} {t : ℝ}
    (ht : t ∈ Icc (q.1 (.inl j)) (q.2 (.inl j))) : zLo A q i j ≤ A i j * t := by
  by_cases ha : 0 ≤ A i j
  · rw [zLo_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left ht.1 ha
  · have hneg : A i j ≤ 0 := (not_le.mp ha).le
    rw [zLo_of_nonpos hneg]
    exact mul_le_mul_of_nonpos_left ht.2 hneg

theorem mul_le_zHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n} {t : ℝ}
    (ht : t ∈ Icc (q.1 (.inl j)) (q.2 (.inl j))) : A i j * t ≤ zHi A q i j := by
  by_cases ha : 0 ≤ A i j
  · rw [zHi_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left ht.2 ha
  · have hneg : A i j ≤ 0 := (not_le.mp ha).le
    rw [zHi_of_nonpos hneg]
    exact mul_le_mul_of_nonpos_left ht.1 hneg

/-- `zLo A q i j` is the exact attained minimum of `t ↦ A i j * t` on
`[q.1 (.inl j), q.2 (.inl j)]`. -/
theorem isLeast_image_mul_Icc {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : q.1 (.inl j) ≤ q.2 (.inl j)) :
    IsLeast ((fun t => A i j * t) '' Icc (q.1 (.inl j)) (q.2 (.inl j))) (zLo A q i j) := by
  refine ⟨⟨if 0 ≤ A i j then q.1 (.inl j) else q.2 (.inl j), ?_, ?_⟩, ?_⟩
  · split_ifs
    · exact left_mem_Icc.mpr h
    · exact right_mem_Icc.mpr h
  · split_ifs with ha
    · rw [zLo_of_nonneg ha]
    · rw [zLo_of_nonpos (not_le.mp ha).le]
  · rintro _ ⟨t, ht, rfl⟩
    exact zLo_le_mul ht

/-- `zHi A q i j` is the exact attained maximum of `t ↦ A i j * t` on
`[q.1 (.inl j), q.2 (.inl j)]`. -/
theorem isGreatest_image_mul_Icc {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    {j : Fin n} (h : q.1 (.inl j) ≤ q.2 (.inl j)) :
    IsGreatest ((fun t => A i j * t) '' Icc (q.1 (.inl j)) (q.2 (.inl j))) (zHi A q i j) := by
  refine ⟨⟨if 0 ≤ A i j then q.2 (.inl j) else q.1 (.inl j), ?_, ?_⟩, ?_⟩
  · split_ifs
    · exact right_mem_Icc.mpr h
    · exact left_mem_Icc.mpr h
  · split_ifs with ha
    · rw [zHi_of_nonneg ha]
    · rw [zHi_of_nonpos (not_le.mp ha).le]
  · rintro _ ⟨t, ht, rfl⟩
    exact mul_le_zHi ht

theorem imageLo_le_imageHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    (h : ∀ j, q.1 (.inl j) ≤ q.2 (.inl j)) : imageLo A q i ≤ imageHi A q i :=
  Finset.sum_le_sum fun j _ => zLo_le_zHi (h j)

theorem imageLo_le_mulVec {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {x : Fin n → ℝ}
    (hx : x ∈ Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j))) :
    imageLo A q i ≤ A.mulVec x i := by
  simp only [imageLo_def, Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => zLo_le_mul ⟨hx.1 j, hx.2 j⟩

theorem mulVec_le_imageHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {x : Fin n → ℝ}
    (hx : x ∈ Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j))) :
    A.mulVec x i ≤ imageHi A q i := by
  simp only [imageHi_def, Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_zHi ⟨hx.1 j, hx.2 j⟩

/-- `imageLo A q i` is the exact attained minimum of row `i` over the variable box of `q`. -/
theorem isLeast_image_mulVec_Icc {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    (h : ∀ j, q.1 (.inl j) ≤ q.2 (.inl j)) :
    IsLeast ((fun x => A.mulVec x i) '' Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j)))
      (imageLo A q i) := by
  refine ⟨⟨fun j => if 0 ≤ A i j then q.1 (.inl j) else q.2 (.inl j), ?_, ?_⟩, ?_⟩
  · refine ⟨fun j => ?_, fun j => ?_⟩ <;> dsimp only <;> split_ifs <;>
      first | exact le_rfl | exact h j
  · simp only [Matrix.mulVec, dotProduct, imageLo_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with ha
    · rw [zLo_of_nonneg ha]
    · rw [zLo_of_nonpos (not_le.mp ha).le]
  · rintro _ ⟨x, hx, rfl⟩
    exact imageLo_le_mulVec hx

/-- `imageHi A q i` is the exact attained maximum of row `i` over the variable box of `q`. -/
theorem isGreatest_image_mulVec_Icc {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    (h : ∀ j, q.1 (.inl j) ≤ q.2 (.inl j)) :
    IsGreatest ((fun x => A.mulVec x i) '' Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j)))
      (imageHi A q i) := by
  refine ⟨⟨fun j => if 0 ≤ A i j then q.2 (.inl j) else q.1 (.inl j), ?_, ?_⟩, ?_⟩
  · refine ⟨fun j => ?_, fun j => ?_⟩ <;> dsimp only <;> split_ifs <;>
      first | exact le_rfl | exact h j
  · simp only [Matrix.mulVec, dotProduct, imageHi_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with ha
    · rw [zHi_of_nonneg ha]
    · rw [zHi_of_nonpos (not_le.mp ha).le]
  · rintro _ ⟨x, hx, rfl⟩
    exact mulVec_le_imageHi hx

theorem zLo_add_restLo (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    zLo A q i j + restLo A q i j = imageLo A q i :=
  Finset.add_sum_erase Finset.univ (fun k => zLo A q i k) (Finset.mem_univ j)

theorem zHi_add_restHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    zHi A q i j + restHi A q i j = imageHi A q i :=
  Finset.add_sum_erase Finset.univ (fun k => zHi A q i k) (Finset.mem_univ j)

theorem restLo_eq_imageLo_of_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m}
    {i : Fin m} {j : Fin n} (h : A i j = 0) : restLo A q i j = imageLo A q i := by
  have hsum := zLo_add_restLo A q i j
  rwa [zLo_of_eq_zero h, zero_add] at hsum

theorem restHi_eq_imageHi_of_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m}
    {i : Fin m} {j : Fin n} (h : A i j = 0) : restHi A q i j = imageHi A q i := by
  have hsum := zHi_add_restHi A q i j
  rwa [zHi_of_eq_zero h, zero_add] at hsum

theorem restLo_le_restHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : ∀ k ≠ j, q.1 (.inl k) ≤ q.2 (.inl k)) : restLo A q i j ≤ restHi A q i j :=
  Finset.sum_le_sum fun k hk => zLo_le_zHi (h k (Finset.ne_of_mem_erase hk))

theorem restLo_le_sum_erase {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    {x : Fin n → ℝ} (hx : ∀ k ≠ j, x k ∈ Icc (q.1 (.inl k)) (q.2 (.inl k))) :
    restLo A q i j ≤ ∑ k ∈ Finset.univ.erase j, A i k * x k :=
  Finset.sum_le_sum fun k hk => zLo_le_mul (hx k (Finset.ne_of_mem_erase hk))

theorem sum_erase_le_restHi {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    {x : Fin n → ℝ} (hx : ∀ k ≠ j, x k ∈ Icc (q.1 (.inl k)) (q.2 (.inl k))) :
    ∑ k ∈ Finset.univ.erase j, A i k * x k ≤ restHi A q i j :=
  Finset.sum_le_sum fun k hk => mul_le_zHi (hx k (Finset.ne_of_mem_erase hk))

theorem zLo_le_zLo_of_within {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m} {j : Fin n}
    (h : Within q r) : zLo A r i j ≤ zLo A q i j := by
  by_cases ha : 0 ≤ A i j
  · rw [zLo_of_nonneg ha, zLo_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (h.1 (.inl j)) ha
  · have hneg : A i j ≤ 0 := (not_le.mp ha).le
    rw [zLo_of_nonpos hneg, zLo_of_nonpos hneg]
    exact mul_le_mul_of_nonpos_left (h.2 (.inl j)) hneg

theorem zHi_le_zHi_of_within {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m} {j : Fin n}
    (h : Within q r) : zHi A q i j ≤ zHi A r i j := by
  by_cases ha : 0 ≤ A i j
  · rw [zHi_of_nonneg ha, zHi_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (h.2 (.inl j)) ha
  · have hneg : A i j ≤ 0 := (not_le.mp ha).le
    rw [zHi_of_nonpos hneg, zHi_of_nonpos hneg]
    exact mul_le_mul_of_nonpos_left (h.1 (.inl j)) hneg

theorem imageLo_le_imageLo_of_within {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m}
    (h : Within q r) : imageLo A r i ≤ imageLo A q i :=
  Finset.sum_le_sum fun _ _ => zLo_le_zLo_of_within h

theorem imageHi_le_imageHi_of_within {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m}
    (h : Within q r) : imageHi A q i ≤ imageHi A r i :=
  Finset.sum_le_sum fun _ _ => zHi_le_zHi_of_within h

theorem restLo_le_restLo_of_within {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m}
    {j : Fin n} (h : Within q r) : restLo A r i j ≤ restLo A q i j :=
  Finset.sum_le_sum fun _ _ => zLo_le_zLo_of_within h

theorem restHi_le_restHi_of_within {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} {i : Fin m}
    {j : Fin n} (h : Within q r) : restHi A q i j ≤ restHi A r i j :=
  Finset.sum_le_sum fun _ _ => zHi_le_zHi_of_within h

end TauCeti.AffineBoundTightening
