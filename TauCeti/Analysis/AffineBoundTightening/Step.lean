/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Logic.Function.Defs
public import Mathlib.Topology.Algebra.Ring.Real
public import TauCeti.Analysis.AffineBoundTightening.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

/-!
# Simultaneous affine bound-tightening operator and iteration

This file defines the simultaneous affine bound-tightening operator on joint variable-and-row
boxes, establishes its order-theoretic and topological properties, and connects its raw and public
iterations.

Given a coefficient matrix `A : Matrix (Fin m) (Fin n) ℝ` and initial endpoints `q₀ : Raw n m`,
one step `step A q₀ q := down A (up A (clip q q₀))` clips to `q₀`, tightens each row interval
against its exact affine image, and simultaneously tightens each variable interval against all
row-inversion bounds computed from the same incoming state. Raw formulas remain well-defined on
unordered tuples, while `publicStep` and `publicRun` operate on `State n m` with global `⊥`
absorbing.

## Main definitions

* `TauCeti.AffineBoundTightening.clip`, `TauCeti.AffineBoundTightening.inverseLo`,
  `TauCeti.AffineBoundTightening.inverseHi`, `TauCeti.AffineBoundTightening.up`,
  `TauCeti.AffineBoundTightening.down`, `TauCeti.AffineBoundTightening.step`: simultaneous
  clipping, upward row tightening, downward row inversion, and combined step.
* `TauCeti.AffineBoundTightening.publicStep`, `TauCeti.AffineBoundTightening.rawRun`,
  `TauCeti.AffineBoundTightening.publicRun`: absorbing public step and raw/public iterates.
* `TauCeti.AffineBoundTightening.graph`: joint graph embedding `x ↦ (x, A.mulVec x)`.

## Main results

* `TauCeti.AffineBoundTightening.step_within_self`,
  `TauCeti.AffineBoundTightening.step_within_init`,
  `TauCeti.AffineBoundTightening.step_mono`,
  `TauCeti.AffineBoundTightening.continuous_step`: contraction, monotonicity for `Within`,
  invalidity persistence, and product-topology continuity of `step A q₀`.
* `TauCeti.AffineBoundTightening.isFixedPt_step_iff_bounds`: coordinate-inequality
  characterization of fixed raw tuples.
* `TauCeti.AffineBoundTightening.publicRun_eq_pack_rawRun`: every public iterate equals the packed
  raw iterate.
* `TauCeti.AffineBoundTightening.graph_survives`: every initially enclosed affine graph point
  belongs to every public iterate.
* `TauCeti.AffineBoundTightening.within_rawRun_of_isFixedPt`: every fixed tuple of `step A q₀`
  lies within every raw iterate.

## References

* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *Feasibility-Based Bounds Tightening via Fixed
  Points*, COCOA 2010, LNCS 6508, §2 and §4, pp. 67–72, equations (9)–(11).
-/

public section

open scoped BigOperators
open Function Set

namespace TauCeti.AffineBoundTightening

variable {n m : ℕ}

/-! ### Clipping and the maps `up`, `down`, and `step` -/

/-- Intersect raw endpoints with their initial variable and row bounds. -/
def clip (q q₀ : Raw n m) : Raw n m :=
  (fun c => max (q.1 c) (q₀.1 c), fun c => min (q.2 c) (q₀.2 c))

@[simp]
theorem clip_fst (q q₀ : Raw n m) (c : Coord n m) : (clip q q₀).1 c = max (q.1 c) (q₀.1 c) := (rfl)

@[simp]
theorem clip_snd (q q₀ : Raw n m) (c : Coord n m) : (clip q q₀).2 c = min (q.2 c) (q₀.2 c) := (rfl)

theorem clip_within_left (q q₀ : Raw n m) : Within (clip q q₀) q :=
  within_def.mpr ⟨fun _ => le_max_left _ _, fun _ => min_le_left _ _⟩

theorem clip_within_right (q q₀ : Raw n m) : Within (clip q q₀) q₀ :=
  within_def.mpr ⟨fun _ => le_max_right _ _, fun _ => min_le_right _ _⟩

theorem within_clip_iff {r q q₀ : Raw n m} :
    Within r (clip q q₀) ↔ Within r q ∧ Within r q₀ := by
  simp only [within_def, Pi.le_def, clip_fst, clip_snd, max_le_iff, le_min_iff]
  grind

theorem clip_eq_self_of_within {q q₀ : Raw n m} (h : Within q q₀) : clip q q₀ = q :=
  (clip_within_left q q₀).antisymm (within_clip_iff.mpr ⟨Within.refl q, h⟩)

@[simp]
theorem clip_self (q : Raw n m) : clip q q = q :=
  clip_eq_self_of_within (Within.refl q)

@[simp]
theorem Icc_clip (q q₀ : Raw n m) :
    Icc (clip q q₀).1 (clip q q₀).2 = Icc q.1 q.2 ∩ Icc q₀.1 q₀.2 := by
  ext y
  simp only [mem_Icc, mem_inter_iff, Pi.le_def, clip_fst, clip_snd, max_le_iff, le_min_iff]
  grind

theorem pack_clip [DecidableLE (Coord n m → ℝ)] (q q₀ : Raw n m) :
    pack (clip q q₀) = pack q ⊓ pack q₀ := by
  apply SetLike.coe_injective
  rw [Interval.coe_inf, coe_pack, coe_pack, coe_pack, Icc_clip]

theorem clip_mono {q₁ q₂ r₁ r₂ : Raw n m} (hq : Within q₁ q₂) (hr : Within r₁ r₂) :
    Within (clip q₁ r₁) (clip q₂ r₂) :=
  within_def.mpr
    ⟨fun c => max_le_max (hq.le_fst c) (hr.le_fst c),
     fun c => min_le_min (hq.snd_le c) (hr.snd_le c)⟩

/-- Lower inverse-row candidate; the zero coefficient branch keeps the incoming endpoint. -/
noncomputable def inverseLo (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m)
    (i : Fin m) (j : Fin n) : ℝ :=
  if 0 < A i j then (q.1 (.inr i) - restHi A q i j) / A i j
  else if A i j < 0 then (q.2 (.inr i) - restLo A q i j) / A i j
  else q.1 (.inl j)

/-- Upper inverse-row candidate; the zero coefficient branch keeps the incoming endpoint. -/
noncomputable def inverseHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m)
    (i : Fin m) (j : Fin n) : ℝ :=
  if 0 < A i j then (q.2 (.inr i) - restLo A q i j) / A i j
  else if A i j < 0 then (q.1 (.inr i) - restHi A q i j) / A i j
  else q.2 (.inl j)

theorem inverseLo_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    inverseLo A q i j =
      if 0 < A i j then (q.1 (.inr i) - restHi A q i j) / A i j
      else if A i j < 0 then (q.2 (.inr i) - restLo A q i j) / A i j
      else q.1 (.inl j) := (rfl)

theorem inverseHi_def (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    inverseHi A q i j =
      if 0 < A i j then (q.2 (.inr i) - restLo A q i j) / A i j
      else if A i j < 0 then (q.1 (.inr i) - restHi A q i j) / A i j
      else q.2 (.inl j) := (rfl)

theorem inverseLo_of_pos {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : 0 < A i j) : inverseLo A q i j = (q.1 (.inr i) - restHi A q i j) / A i j := by
  simp [inverseLo_def, h]

theorem inverseLo_of_neg {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j < 0) : inverseLo A q i j = (q.2 (.inr i) - restLo A q i j) / A i j := by
  simp [inverseLo_def, h, not_lt.mpr h.le]

theorem inverseLo_of_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j = 0) : inverseLo A q i j = q.1 (.inl j) := by
  simp [inverseLo_def, h]

theorem inverseHi_of_pos {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : 0 < A i j) : inverseHi A q i j = (q.2 (.inr i) - restLo A q i j) / A i j := by
  simp [inverseHi_def, h]

theorem inverseHi_of_neg {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j < 0) : inverseHi A q i j = (q.1 (.inr i) - restHi A q i j) / A i j := by
  simp [inverseHi_def, h, not_lt.mpr h.le]

theorem inverseHi_of_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j = 0) : inverseHi A q i j = q.2 (.inl j) := by
  simp [inverseHi_def, h]

@[simp]
theorem inverseLo_zero (q : Raw n m) (i : Fin m) (j : Fin n) :
    inverseLo (0 : Matrix (Fin m) (Fin n) ℝ) q i j = q.1 (.inl j) :=
  inverseLo_of_eq_zero rfl

@[simp]
theorem inverseHi_zero (q : Raw n m) (i : Fin m) (j : Fin n) :
    inverseHi (0 : Matrix (Fin m) (Fin n) ℝ) q i j = q.2 (.inl j) :=
  inverseHi_of_eq_zero rfl

theorem inverseLo_le_inverseLo_of_within {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m}
    {i : Fin m} {j : Fin n} (h : Within q r) : inverseLo A r i j ≤ inverseLo A q i j := by
  rcases lt_trichotomy (A i j) 0 with hneg | hzero | hpos
  · rw [inverseLo_of_neg hneg, inverseLo_of_neg hneg]
    exact div_le_div_of_nonpos_of_le hneg.le
      (sub_le_sub (h.snd_le (.inr i)) (restLo_le_restLo_of_within h))
  · rw [inverseLo_of_eq_zero hzero, inverseLo_of_eq_zero hzero]
    exact h.le_fst (.inl j)
  · rw [inverseLo_of_pos hpos, inverseLo_of_pos hpos]
    exact div_le_div_of_nonneg_right
      (sub_le_sub (h.le_fst (.inr i)) (restHi_le_restHi_of_within h)) hpos.le

theorem inverseHi_le_inverseHi_of_within {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m}
    {i : Fin m} {j : Fin n} (h : Within q r) : inverseHi A q i j ≤ inverseHi A r i j := by
  rcases lt_trichotomy (A i j) 0 with hneg | hzero | hpos
  · rw [inverseHi_of_neg hneg, inverseHi_of_neg hneg]
    exact div_le_div_of_nonpos_of_le hneg.le
      (sub_le_sub (h.le_fst (.inr i)) (restHi_le_restHi_of_within h))
  · rw [inverseHi_of_eq_zero hzero, inverseHi_of_eq_zero hzero]
    exact h.snd_le (.inl j)
  · rw [inverseHi_of_pos hpos, inverseHi_of_pos hpos]
    exact div_le_div_of_nonneg_right
      (sub_le_sub (h.snd_le (.inr i)) (restLo_le_restLo_of_within h)) hpos.le

/-- Keep variable endpoints and intersect each row with its affine image. -/
noncomputable def up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) : Raw n m :=
  (Sum.elim (fun j => q.1 (.inl j)) (fun i => max (q.1 (.inr i)) (imageLo A q i)),
   Sum.elim (fun j => q.2 (.inl j)) (fun i => min (q.2 (.inr i)) (imageHi A q i)))

@[simp]
theorem up_fst_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n) :
    (up A q).1 (.inl j) = q.1 (.inl j) := (rfl)

@[simp]
theorem up_snd_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n) :
    (up A q).2 (.inl j) = q.2 (.inl j) := (rfl)

@[simp]
theorem up_fst_inr (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    (up A q).1 (.inr i) = max (q.1 (.inr i)) (imageLo A q i) := (rfl)

@[simp]
theorem up_snd_inr (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    (up A q).2 (.inr i) = min (q.2 (.inr i)) (imageHi A q i) := (rfl)

@[simp]
theorem zLo_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    zLo A (up A q) i j = zLo A q i j :=
  zLo_congr_var (up_fst_inl A q j) (up_snd_inl A q j)

@[simp]
theorem zHi_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    zHi A (up A q) i j = zHi A q i j :=
  zHi_congr_var (up_fst_inl A q j) (up_snd_inl A q j)

@[simp]
theorem imageLo_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    imageLo A (up A q) i = imageLo A q i :=
  imageLo_congr_var (up_fst_inl A q) (up_snd_inl A q)

@[simp]
theorem imageHi_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    imageHi A (up A q) i = imageHi A q i :=
  imageHi_congr_var (up_fst_inl A q) (up_snd_inl A q)

@[simp]
theorem restLo_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    restLo A (up A q) i j = restLo A q i j :=
  restLo_congr_var (fun k _ => up_fst_inl A q k) (fun k _ => up_snd_inl A q k)

@[simp]
theorem restHi_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    restHi A (up A q) i j = restHi A q i j :=
  restHi_congr_var (fun k _ => up_fst_inl A q k) (fun k _ => up_snd_inl A q k)

theorem up_within (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) : Within (up A q) q := by
  refine within_def.mpr ⟨fun c => ?_, fun c => ?_⟩ <;> cases c <;> simp

theorem up_mono (A : Matrix (Fin m) (Fin n) ℝ) {q r : Raw n m} (h : Within q r) :
    Within (up A q) (up A r) := by
  refine within_def.mpr ⟨fun c => ?_, fun c => ?_⟩
  · cases c with
    | inl j => exact h.le_fst (.inl j)
    | inr i => exact max_le_max (h.le_fst (.inr i)) (imageLo_le_imageLo_of_within h)
  · cases c with
    | inl j => exact h.snd_le (.inl j)
    | inr i => exact min_le_min (h.snd_le (.inr i)) (imageHi_le_imageHi_of_within h)

theorem up_eq_self_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} :
    up A q = q ↔ ∀ i, imageLo A q i ≤ q.1 (.inr i) ∧ q.2 (.inr i) ≤ imageHi A q i := by
  constructor
  · intro h i
    have hL : max (q.1 (.inr i)) (imageLo A q i) = q.1 (.inr i) := by
      rw [← up_fst_inr A q i, h]
    have hU : min (q.2 (.inr i)) (imageHi A q i) = q.2 (.inr i) := by
      rw [← up_snd_inr A q i, h]
    exact ⟨max_eq_left_iff.mp hL, min_eq_left_iff.mp hU⟩
  · intro h
    refine raw_ext (up_fst_inl A q) (up_snd_inl A q) (fun i => ?_) (fun i => ?_)
    · simp [max_eq_left (h i).1]
    · simp [min_eq_left (h i).2]

theorem mem_Icc_up_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {y : Coord n m → ℝ} :
    y ∈ Icc (up A q).1 (up A q).2 ↔
      y ∈ Icc q.1 q.2 ∧ ∀ i, imageLo A q i ≤ y (.inr i) ∧ y (.inr i) ≤ imageHi A q i := by
  simp only [mem_Icc, Pi.le_def, Sum.forall, up_fst_inl, up_snd_inl, up_fst_inr, up_snd_inr,
    max_le_iff, le_min_iff]
  grind

/-- Keep row endpoints and intersect variables with all inverse candidates from the same state. -/
noncomputable def down (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) : Raw n m :=
  (Sum.elim (fun j => Finset.univ.fold max (q.1 (.inl j)) (fun i => inverseLo A q i j))
     (fun i => q.1 (.inr i)),
   Sum.elim (fun j => Finset.univ.fold min (q.2 (.inl j)) (fun i => inverseHi A q i j))
     (fun i => q.2 (.inr i)))

@[simp]
theorem down_fst_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n) :
    (down A q).1 (.inl j) = Finset.univ.fold max (q.1 (.inl j)) (fun i => inverseLo A q i j) :=
  (rfl)

@[simp]
theorem down_snd_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n) :
    (down A q).2 (.inl j) = Finset.univ.fold min (q.2 (.inl j)) (fun i => inverseHi A q i j) :=
  (rfl)

@[simp]
theorem down_fst_inr (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    (down A q).1 (.inr i) = q.1 (.inr i) := (rfl)

@[simp]
theorem down_snd_inr (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    (down A q).2 (.inr i) = q.2 (.inr i) := (rfl)

theorem down_fst_inl_le_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {j : Fin n} {t : ℝ} :
    (down A q).1 (.inl j) ≤ t ↔ q.1 (.inl j) ≤ t ∧ ∀ i, inverseLo A q i j ≤ t := by
  simp [down_fst_inl, Finset.fold_max_le]

theorem le_down_fst_inl_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {j : Fin n} {t : ℝ} :
    t ≤ (down A q).1 (.inl j) ↔ t ≤ q.1 (.inl j) ∨ ∃ i, t ≤ inverseLo A q i j := by
  simp [down_fst_inl, Finset.le_fold_max]

theorem le_down_snd_inl_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {j : Fin n} {t : ℝ} :
    t ≤ (down A q).2 (.inl j) ↔ t ≤ q.2 (.inl j) ∧ ∀ i, t ≤ inverseHi A q i j := by
  simp [down_snd_inl, Finset.le_fold_min]

theorem down_snd_inl_le_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {j : Fin n} {t : ℝ} :
    (down A q).2 (.inl j) ≤ t ↔ q.2 (.inl j) ≤ t ∨ ∃ i, inverseHi A q i j ≤ t := by
  simp [down_snd_inl, Finset.fold_min_le]

theorem le_down_fst_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n) :
    q.1 (.inl j) ≤ (down A q).1 (.inl j) :=
  le_down_fst_inl_iff.mpr (Or.inl le_rfl)

theorem inverseLo_le_down_fst_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m)
    (i : Fin m) (j : Fin n) : inverseLo A q i j ≤ (down A q).1 (.inl j) :=
  le_down_fst_inl_iff.mpr (Or.inr ⟨i, le_rfl⟩)

theorem down_snd_inl_le (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n) :
    (down A q).2 (.inl j) ≤ q.2 (.inl j) :=
  down_snd_inl_le_iff.mpr (Or.inl le_rfl)

theorem down_snd_inl_le_inverseHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m)
    (i : Fin m) (j : Fin n) : (down A q).2 (.inl j) ≤ inverseHi A q i j :=
  down_snd_inl_le_iff.mpr (Or.inr ⟨i, le_rfl⟩)

theorem down_within (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) : Within (down A q) q := by
  refine within_def.mpr ⟨fun c => ?_, fun c => ?_⟩
  · cases c with
    | inl j => exact le_down_fst_inl A q j
    | inr i => exact le_rfl
  · cases c with
    | inl j => exact down_snd_inl_le A q j
    | inr i => exact le_rfl

theorem down_mono (A : Matrix (Fin m) (Fin n) ℝ) {q r : Raw n m} (h : Within q r) :
    Within (down A q) (down A r) := by
  refine within_def.mpr ⟨fun c => ?_, fun c => ?_⟩
  · cases c with
    | inl j =>
        exact down_fst_inl_le_iff.mpr
          ⟨(h.le_fst (.inl j)).trans (le_down_fst_inl A q j),
           fun i =>
            (inverseLo_le_inverseLo_of_within h).trans (inverseLo_le_down_fst_inl A q i j)⟩
    | inr i => exact h.le_fst (.inr i)
  · cases c with
    | inl j =>
        exact le_down_snd_inl_iff.mpr
          ⟨(down_snd_inl_le A q j).trans (h.snd_le (.inl j)),
           fun i =>
            (down_snd_inl_le_inverseHi A q i j).trans (inverseHi_le_inverseHi_of_within h)⟩
    | inr i => exact h.snd_le (.inr i)

theorem down_eq_self_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} :
    down A q = q ↔ ∀ i j, inverseLo A q i j ≤ q.1 (.inl j) ∧ q.2 (.inl j) ≤ inverseHi A q i j := by
  constructor
  · intro h i j
    have hL : (down A q).1 (.inl j) ≤ q.1 (.inl j) := by rw [h]
    have hU : q.2 (.inl j) ≤ (down A q).2 (.inl j) := by rw [h]
    exact ⟨(down_fst_inl_le_iff.mp hL).2 i, (le_down_snd_inl_iff.mp hU).2 i⟩
  · intro h
    refine raw_ext (fun j => ?_) (fun j => ?_) (down_fst_inr A q) (down_snd_inr A q)
    · exact le_antisymm
        (down_fst_inl_le_iff.mpr ⟨le_rfl, fun i => (h i j).1⟩) (le_down_fst_inl A q j)
    · exact le_antisymm
        (down_snd_inl_le A q j) (le_down_snd_inl_iff.mpr ⟨le_rfl, fun i => (h i j).2⟩)

theorem mem_Icc_down_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {y : Coord n m → ℝ} :
    y ∈ Icc (down A q).1 (down A q).2 ↔
      y ∈ Icc q.1 q.2 ∧
        ∀ i j, inverseLo A q i j ≤ y (.inl j) ∧ y (.inl j) ≤ inverseHi A q i j := by
  simp only [mem_Icc, Pi.le_def, Sum.forall, down_fst_inl_le_iff, le_down_snd_inl_iff,
    down_fst_inr, down_snd_inr]
  grind

/-- One simultaneous affine tightening step: clipping, upward images, then downward inverses. -/
noncomputable def step (A : Matrix (Fin m) (Fin n) ℝ) (q₀ q : Raw n m) : Raw n m :=
  down A (up A (clip q q₀))

theorem step_def (A : Matrix (Fin m) (Fin n) ℝ) (q₀ q : Raw n m) :
    step A q₀ q = down A (up A (clip q q₀)) := (rfl)

@[simp]
theorem up_eq_self_of_zero_rows (A : Matrix (Fin 0) (Fin n) ℝ) (q : Raw n 0) : up A q = q :=
  up_eq_self_iff.mpr fun i => Fin.elim0 i

@[simp]
theorem down_eq_self_of_zero_rows (A : Matrix (Fin 0) (Fin n) ℝ) (q : Raw n 0) : down A q = q :=
  down_eq_self_iff.mpr fun i => Fin.elim0 i

@[simp]
theorem step_eq_clip_of_zero_rows (A : Matrix (Fin 0) (Fin n) ℝ) (q₀ q : Raw n 0) :
    step A q₀ q = clip q q₀ := by
  rw [step_def, up_eq_self_of_zero_rows, down_eq_self_of_zero_rows]

/-! ### Contraction, monotonicity, fixed points, and continuity -/

/-- One simultaneous step contracts any raw tuple into itself. -/
theorem step_within_self (A : Matrix (Fin m) (Fin n) ℝ) (q₀ q : Raw n m) :
    Within (step A q₀ q) q :=
  ((down_within A _).trans (up_within A _)).trans (clip_within_left q q₀)

/-- One simultaneous step contracts any raw tuple into the initial tuple `q₀`. -/
theorem step_within_init (A : Matrix (Fin m) (Fin n) ℝ) (q₀ q : Raw n m) :
    Within (step A q₀ q) q₀ :=
  ((down_within A _).trans (up_within A _)).trans (clip_within_right q q₀)

/-- The simultaneous tightening step is monotone with respect to raw endpoint containment. -/
theorem step_mono (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) {q r : Raw n m} (h : Within q r) :
    Within (step A q₀ q) (step A q₀ r) :=
  down_mono A (up_mono A (clip_mono h (Within.refl q₀)))

/-- An unordered raw tuple remains unordered after one simultaneous tightening step. -/
theorem not_le_step_of_not_le (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) {q : Raw n m}
    (hq : ¬ q.1 ≤ q.2) : ¬ (step A q₀ q).1 ≤ (step A q₀ q).2 :=
  (step_within_self A q₀ q).not_le_of_not_le hq

/-- A raw tuple is fixed by `step A q₀` iff it lies within `q₀` and is fixed by `up` and `down`. -/
theorem isFixedPt_step_iff {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m} :
    IsFixedPt (step A q₀) q ↔ Within q q₀ ∧ up A q = q ∧ down A q = q := by
  constructor
  · intro h
    have hq₀ : Within q q₀ := by
      have hstep := step_within_init A q₀ q
      rwa [h.eq] at hstep
    have hclip : clip q q₀ = q := clip_eq_self_of_within hq₀
    have hdu : down A (up A q) = q := by
      simpa [step_def, hclip] using h.eq
    have hup : up A q = q := by
      apply (up_within A q).antisymm
      have hdown := down_within A (up A q)
      rwa [hdu] at hdown
    refine ⟨hq₀, hup, ?_⟩
    rwa [hup] at hdu
  · rintro ⟨hq₀, hup, hdown⟩
    simp [IsFixedPt, step_def, clip_eq_self_of_within hq₀, hup, hdown]

/-- Explicit coordinate-inequality characterization of fixed tuples of `step A q₀`. -/
theorem isFixedPt_step_iff_bounds {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m} :
    IsFixedPt (step A q₀) q ↔
      Within q q₀ ∧
      (∀ i, imageLo A q i ≤ q.1 (.inr i) ∧ q.2 (.inr i) ≤ imageHi A q i) ∧
      (∀ i j, inverseLo A q i j ≤ q.1 (.inl j) ∧ q.2 (.inl j) ≤ inverseHi A q i j) := by
  rw [isFixedPt_step_iff, up_eq_self_iff, down_eq_self_iff]

theorem continuous_zLo (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous fun q : Raw n m => zLo A q i j := by
  by_cases ha : 0 ≤ A i j
  · simp_rw [zLo_of_nonneg ha]
    exact continuous_const.mul ((continuous_apply (Sum.inl j)).comp continuous_fst)
  · simp_rw [zLo_of_nonpos (not_le.mp ha).le]
    exact continuous_const.mul ((continuous_apply (Sum.inl j)).comp continuous_snd)

theorem continuous_zHi (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous fun q : Raw n m => zHi A q i j := by
  by_cases ha : 0 ≤ A i j
  · simp_rw [zHi_of_nonneg ha]
    exact continuous_const.mul ((continuous_apply (Sum.inl j)).comp continuous_snd)
  · simp_rw [zHi_of_nonpos (not_le.mp ha).le]
    exact continuous_const.mul ((continuous_apply (Sum.inl j)).comp continuous_fst)

theorem continuous_imageLo (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Continuous fun q : Raw n m => imageLo A q i := by
  simp_rw [imageLo_def]
  exact continuous_finsetSum _ fun j _ => continuous_zLo A i j

theorem continuous_imageHi (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Continuous fun q : Raw n m => imageHi A q i := by
  simp_rw [imageHi_def]
  exact continuous_finsetSum _ fun j _ => continuous_zHi A i j

theorem continuous_restLo (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous fun q : Raw n m => restLo A q i j := by
  simp_rw [restLo_def]
  exact continuous_finsetSum _ fun k _ => continuous_zLo A i k

theorem continuous_restHi (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous fun q : Raw n m => restHi A q i j := by
  simp_rw [restHi_def]
  exact continuous_finsetSum _ fun k _ => continuous_zHi A i k

theorem continuous_clip : Continuous fun p : Raw n m × Raw n m => clip p.1 p.2 := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun c =>
      ((continuous_apply c).comp (continuous_fst.comp continuous_fst)).max
        ((continuous_apply c).comp (continuous_fst.comp continuous_snd))
  · exact continuous_pi fun c =>
      ((continuous_apply c).comp (continuous_snd.comp continuous_fst)).min
        ((continuous_apply c).comp (continuous_snd.comp continuous_snd))

theorem continuous_inverseLo (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous fun q : Raw n m => inverseLo A q i j := by
  rcases lt_trichotomy (A i j) 0 with hneg | hzero | hpos
  · simp_rw [inverseLo_of_neg hneg]
    exact (((continuous_apply (Sum.inr i)).comp continuous_snd).sub
      (continuous_restLo A i j)).div_const (A i j)
  · simp_rw [inverseLo_of_eq_zero hzero]
    exact (continuous_apply (Sum.inl j)).comp continuous_fst
  · simp_rw [inverseLo_of_pos hpos]
    exact (((continuous_apply (Sum.inr i)).comp continuous_fst).sub
      (continuous_restHi A i j)).div_const (A i j)

theorem continuous_inverseHi (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous fun q : Raw n m => inverseHi A q i j := by
  rcases lt_trichotomy (A i j) 0 with hneg | hzero | hpos
  · simp_rw [inverseHi_of_neg hneg]
    exact (((continuous_apply (Sum.inr i)).comp continuous_fst).sub
      (continuous_restHi A i j)).div_const (A i j)
  · simp_rw [inverseHi_of_eq_zero hzero]
    exact (continuous_apply (Sum.inl j)).comp continuous_snd
  · simp_rw [inverseHi_of_pos hpos]
    exact (((continuous_apply (Sum.inr i)).comp continuous_snd).sub
      (continuous_restLo A i j)).div_const (A i j)

theorem continuous_up (A : Matrix (Fin m) (Fin n) ℝ) : Continuous (up A) := by
  refine Continuous.prodMk (continuous_pi fun c => ?_) (continuous_pi fun c => ?_)
  · cases c with
    | inl j => exact (continuous_apply (Sum.inl j)).comp continuous_fst
    | inr i =>
        exact ((continuous_apply (Sum.inr i)).comp continuous_fst).max (continuous_imageLo A i)
  · cases c with
    | inl j => exact (continuous_apply (Sum.inl j)).comp continuous_snd
    | inr i =>
        exact ((continuous_apply (Sum.inr i)).comp continuous_snd).min (continuous_imageHi A i)

theorem continuous_down (A : Matrix (Fin m) (Fin n) ℝ) : Continuous (down A) := by
  refine Continuous.prodMk (continuous_pi fun c => ?_) (continuous_pi fun c => ?_)
  · cases c with
    | inl j =>
        suffices ∀ s : Finset (Fin m),
            Continuous fun q : Raw n m => s.fold max (q.1 (.inl j)) (fun i => inverseLo A q i j)
          from this Finset.univ
        intro s
        induction s using Finset.induction with
        | empty =>
            simp only [Finset.fold_empty]
            exact (continuous_apply (Sum.inl j)).comp continuous_fst
        | @insert i s hi ih =>
            simp_rw [Finset.fold_insert hi]
            exact (continuous_inverseLo A i j).max ih
    | inr i => exact (continuous_apply (Sum.inr i)).comp continuous_fst
  · cases c with
    | inl j =>
        suffices ∀ s : Finset (Fin m),
            Continuous fun q : Raw n m => s.fold min (q.2 (.inl j)) (fun i => inverseHi A q i j)
          from this Finset.univ
        intro s
        induction s using Finset.induction with
        | empty =>
            simp only [Finset.fold_empty]
            exact (continuous_apply (Sum.inl j)).comp continuous_snd
        | @insert i s hi ih =>
            simp_rw [Finset.fold_insert hi]
            exact (continuous_inverseHi A i j).min ih
    | inr i => exact (continuous_apply (Sum.inr i)).comp continuous_snd

/-- For fixed `A` and `q₀`, `step A q₀` is continuous in the finite product topology on
`Raw n m`. -/
theorem continuous_step (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    Continuous (step A q₀) :=
  (continuous_down A).comp
    ((continuous_up A).comp (continuous_clip.comp (continuous_id.prodMk continuous_const)))

/-! ### Raw and public iterates -/

/-- Apply the raw step to nonempty intervals and keep global bottom absorbing. -/
noncomputable def publicStep (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    State n m → State n m :=
  Interval.recBotCoe ⊥ (fun q => pack (step A q₀ (q.fst, q.snd)))

/-- Actual raw iteration from the initial endpoints. -/
noncomputable def rawRun (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) : Raw n m :=
  (step A q₀)^[k] q₀

/-- Actual public iteration from the packed initial endpoints. -/
noncomputable def publicRun (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) : State n m :=
  (publicStep A q₀)^[k] (pack q₀)

theorem rawRun_def (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    rawRun A q₀ k = (step A q₀)^[k] q₀ := (rfl)

theorem publicRun_def (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    publicRun A q₀ k = (publicStep A q₀)^[k] (pack q₀) := (rfl)

@[simp]
theorem publicStep_bot (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    publicStep A q₀ ⊥ = ⊥ := (rfl)

@[simp]
theorem publicStep_coe (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m)
    (s : NonemptyInterval (Coord n m → ℝ)) :
    publicStep A q₀ s = pack (step A q₀ s.toProd) := (rfl)

@[simp]
theorem publicStep_pack (A : Matrix (Fin m) (Fin n) ℝ) (q₀ q : Raw n m) :
    publicStep A q₀ (pack q) = pack (step A q₀ q) := by
  by_cases hq : q.1 ≤ q.2
  · rw [pack_of_le hq, publicStep_coe]
  · rw [pack_of_not_le hq, publicStep_bot, pack_of_not_le (not_le_step_of_not_le A q₀ hq)]

@[simp]
theorem rawRun_zero (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    rawRun A q₀ 0 = q₀ := (rfl)

@[simp]
theorem rawRun_succ (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    rawRun A q₀ (k + 1) = step A q₀ (rawRun A q₀ k) :=
  Function.iterate_succ_apply' (step A q₀) k q₀

@[simp]
theorem publicRun_zero (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    publicRun A q₀ 0 = pack q₀ := (rfl)

@[simp]
theorem publicRun_succ (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    publicRun A q₀ (k + 1) = publicStep A q₀ (publicRun A q₀ k) :=
  Function.iterate_succ_apply' (publicStep A q₀) k (pack q₀)

/-- Every public iterate equals the packed raw iterate. -/
theorem publicRun_eq_pack_rawRun (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    publicRun A q₀ k = pack (rawRun A q₀ k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [publicRun_succ, ih, publicStep_pack, rawRun_succ]

theorem coe_publicRun (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    (publicRun A q₀ k : Set (Coord n m → ℝ)) = Icc (rawRun A q₀ k).1 (rawRun A q₀ k).2 := by
  rw [publicRun_eq_pack_rawRun, coe_pack]

theorem publicRun_eq_bot_iff (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    publicRun A q₀ k = ⊥ ↔ ¬ (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2 := by
  rw [publicRun_eq_pack_rawRun, pack_eq_bot_iff]

/-- Nonemptiness of the `k`-th public iterate is equivalent to ordering of the `k`-th raw tuple. -/
theorem publicRun_nonempty_iff (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    (publicRun A q₀ k : Set (Coord n m → ℝ)).Nonempty ↔
      (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2 := by
  rw [coe_publicRun, nonempty_Icc]

theorem rawRun_within_of_le (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) {k l : ℕ} (hkl : k ≤ l) :
    Within (rawRun A q₀ l) (rawRun A q₀ k) := by
  induction l, hkl using Nat.le_induction with
  | base => exact Within.refl _
  | succ j _ ih =>
      rw [rawRun_succ]
      exact (step_within_self A q₀ _).trans ih

theorem rawRun_within_init (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    Within (rawRun A q₀ k) q₀ :=
  rawRun_within_of_le A q₀ (Nat.zero_le k)

theorem monotone_rawRun_fst (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (c : Coord n m) :
    Monotone fun k => (rawRun A q₀ k).1 c :=
  fun _ _ hkl => (rawRun_within_of_le A q₀ hkl).le_fst c

theorem antitone_rawRun_snd (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (c : Coord n m) :
    Antitone fun k => (rawRun A q₀ k).2 c :=
  fun _ _ hkl => (rawRun_within_of_le A q₀ hkl).snd_le c

theorem antitone_publicRun (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    Antitone (publicRun A q₀) := by
  intro k l hkl
  rw [publicRun_eq_pack_rawRun, publicRun_eq_pack_rawRun]
  exact pack_le_pack_of_within (rawRun_within_of_le A q₀ hkl)

theorem publicRun_eq_bot_of_le (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) {k l : ℕ}
    (hkl : k ≤ l) (hk : publicRun A q₀ k = ⊥) : publicRun A q₀ l = ⊥ :=
  le_bot_iff.mp ((antitone_publicRun A q₀ hkl).trans hk.le)

theorem rawRun_eq_of_isFixedPt {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    (hq₀ : IsFixedPt (step A q₀) q₀) (k : ℕ) : rawRun A q₀ k = q₀ :=
  Function.iterate_fixed hq₀ k

theorem publicRun_eq_of_isFixedPt {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    (hq₀ : IsFixedPt (step A q₀) q₀) (k : ℕ) : publicRun A q₀ k = pack q₀ := by
  rw [publicRun_eq_pack_rawRun, rawRun_eq_of_isFixedPt hq₀]

/-! ### Graph points survive every iterate -/

/-- The joint point consisting of the original variables and their affine row values. -/
def graph (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Coord n m → ℝ :=
  Sum.elim x (A.mulVec x)

@[simp]
theorem graph_inl (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (j : Fin n) :
    graph A x (.inl j) = x j := (rfl)

@[simp]
theorem graph_inr (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m) :
    graph A x (.inr i) = A.mulVec x i := (rfl)

theorem graph_injective (A : Matrix (Fin m) (Fin n) ℝ) : Injective (graph A) := by
  intro x y h
  funext j
  simpa using congrFun h (.inl j)

theorem graph_mem_Icc_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {x : Fin n → ℝ} :
    graph A x ∈ Icc q.1 q.2 ↔
      (∀ j, q.1 (.inl j) ≤ x j ∧ x j ≤ q.2 (.inl j)) ∧
      (∀ i, q.1 (.inr i) ≤ A.mulVec x i ∧ A.mulVec x i ≤ q.2 (.inr i)) := by
  simp only [mem_Icc, Pi.le_def, Sum.forall, graph_inl, graph_inr]
  grind

theorem graph_mem_Icc_up {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {x : Fin n → ℝ}
    (hx : graph A x ∈ Icc q.1 q.2) : graph A x ∈ Icc (up A q).1 (up A q).2 := by
  have hxvar : x ∈ Icc (fun j => q.1 (.inl j)) (fun j => q.2 (.inl j)) :=
    ⟨fun j => hx.1 (.inl j), fun j => hx.2 (.inl j)⟩
  exact mem_Icc_up_iff.mpr ⟨hx, fun i => ⟨imageLo_le_mulVec hxvar, mulVec_le_imageHi hxvar⟩⟩

theorem inverseLo_le_of_graph_mem {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {x : Fin n → ℝ}
    (hx : graph A x ∈ Icc q.1 q.2) (i : Fin m) (j : Fin n) : inverseLo A q i j ≤ x j := by
  have hvar : ∀ k ≠ j, x k ∈ Icc (q.1 (.inl k)) (q.2 (.inl k)) :=
    fun k _ => ⟨hx.1 (.inl k), hx.2 (.inl k)⟩
  have hrowL : q.1 (.inr i) ≤ A.mulVec x i := hx.1 (.inr i)
  have hrowU : A.mulVec x i ≤ q.2 (.inr i) := hx.2 (.inr i)
  have hsum : A i j * x j + ∑ k ∈ Finset.univ.erase j, A i k * x k = A.mulVec x i := by
    simp [Matrix.mulVec, dotProduct]
  rcases lt_trichotomy (A i j) 0 with hneg | hzero | hpos
  · rw [inverseLo_of_neg hneg, div_le_iff_of_neg hneg]
    have hrest := restLo_le_sum_erase (A := A) (i := i) hvar
    linarith
  · rw [inverseLo_of_eq_zero hzero]
    exact hx.1 (.inl j)
  · rw [inverseLo_of_pos hpos, div_le_iff₀ hpos]
    have hrest := sum_erase_le_restHi (A := A) (i := i) hvar
    linarith

theorem le_inverseHi_of_graph_mem {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {x : Fin n → ℝ}
    (hx : graph A x ∈ Icc q.1 q.2) (i : Fin m) (j : Fin n) : x j ≤ inverseHi A q i j := by
  have hvar : ∀ k ≠ j, x k ∈ Icc (q.1 (.inl k)) (q.2 (.inl k)) :=
    fun k _ => ⟨hx.1 (.inl k), hx.2 (.inl k)⟩
  have hrowL : q.1 (.inr i) ≤ A.mulVec x i := hx.1 (.inr i)
  have hrowU : A.mulVec x i ≤ q.2 (.inr i) := hx.2 (.inr i)
  have hsum : A i j * x j + ∑ k ∈ Finset.univ.erase j, A i k * x k = A.mulVec x i := by
    simp [Matrix.mulVec, dotProduct]
  rcases lt_trichotomy (A i j) 0 with hneg | hzero | hpos
  · rw [inverseHi_of_neg hneg, le_div_iff_of_neg hneg]
    have hrest := sum_erase_le_restHi (A := A) (i := i) hvar
    linarith
  · rw [inverseHi_of_eq_zero hzero]
    exact hx.2 (.inl j)
  · rw [inverseHi_of_pos hpos, le_div_iff₀ hpos]
    have hrest := restLo_le_sum_erase (A := A) (i := i) hvar
    linarith

theorem graph_mem_Icc_down {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {x : Fin n → ℝ}
    (hx : graph A x ∈ Icc q.1 q.2) : graph A x ∈ Icc (down A q).1 (down A q).2 :=
  mem_Icc_down_iff.mpr
    ⟨hx, fun i j => ⟨inverseLo_le_of_graph_mem hx i j, le_inverseHi_of_graph_mem hx i j⟩⟩

theorem graph_mem_Icc_step {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m} {x : Fin n → ℝ}
    (hx : graph A x ∈ Icc q.1 q.2) (hx₀ : graph A x ∈ Icc q₀.1 q₀.2) :
    graph A x ∈ Icc (step A q₀ q).1 (step A q₀ q).2 := by
  have hclip : graph A x ∈ Icc (clip q q₀).1 (clip q q₀).2 := by
    rw [Icc_clip]
    exact ⟨hx, hx₀⟩
  exact graph_mem_Icc_down (graph_mem_Icc_up hclip)

theorem graph_mem_Icc_rawRun {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m} {x : Fin n → ℝ}
    (hx : graph A x ∈ Icc q₀.1 q₀.2) (k : ℕ) :
    graph A x ∈ Icc (rawRun A q₀ k).1 (rawRun A q₀ k).2 := by
  induction k with
  | zero => exact hx
  | succ k ih =>
      rw [rawRun_succ]
      exact graph_mem_Icc_step ih hx

/-- An initially enclosed affine graph point belongs to every public iterate. -/
theorem graph_survives (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m)
    (x : Fin n → ℝ) (hx : graph A x ∈ Icc q₀.1 q₀.2) (k : ℕ) :
    graph A x ∈ (publicRun A q₀ k : Set (Coord n m → ℝ)) := by
  rw [coe_publicRun]
  exact graph_mem_Icc_rawRun hx k

theorem publicRun_nonempty_of_graph_mem {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    {x : Fin n → ℝ} (hx : graph A x ∈ Icc q₀.1 q₀.2) (k : ℕ) :
    (publicRun A q₀ k : Set (Coord n m → ℝ)).Nonempty :=
  ⟨graph A x, graph_survives A q₀ x hx k⟩

theorem rawRun_le_of_graph_mem {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    {x : Fin n → ℝ} (hx : graph A x ∈ Icc q₀.1 q₀.2) (k : ℕ) :
    (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2 :=
  (publicRun_nonempty_iff A q₀ k).mp (publicRun_nonempty_of_graph_mem hx k)

/-! ### Fixed tuples lie in every iterate -/

theorem within_init_of_isFixedPt {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hq : IsFixedPt (step A q₀) q) : Within q q₀ := by
  have h := step_within_init A q₀ q
  rwa [hq.eq] at h

/-- Every fixed tuple of `step A q₀` lies within every raw iterate. -/
theorem within_rawRun_of_isFixedPt {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hq : IsFixedPt (step A q₀) q) (k : ℕ) : Within q (rawRun A q₀ k) := by
  induction k with
  | zero => exact within_init_of_isFixedPt hq
  | succ k ih =>
      rw [rawRun_succ]
      have hmono := step_mono A q₀ ih
      rwa [hq.eq] at hmono

theorem rawRun_fst_le_of_isFixedPt {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hq : IsFixedPt (step A q₀) q) (k : ℕ) (c : Coord n m) :
    (rawRun A q₀ k).1 c ≤ q.1 c :=
  (within_rawRun_of_isFixedPt hq k).le_fst c

theorem le_rawRun_snd_of_isFixedPt {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hq : IsFixedPt (step A q₀) q) (k : ℕ) (c : Coord n m) :
    q.2 c ≤ (rawRun A q₀ k).2 c :=
  (within_rawRun_of_isFixedPt hq k).snd_le c

theorem pack_le_publicRun_of_isFixedPt {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hq : IsFixedPt (step A q₀) q) (k : ℕ) : pack q ≤ publicRun A q₀ k := by
  rw [publicRun_eq_pack_rawRun]
  exact pack_le_pack_of_within (within_rawRun_of_isFixedPt hq k)

/-- An ordered fixed tuple of `step A q₀` forces every public iterate to be nonempty. -/
theorem publicRun_nonempty_of_isFixedPt {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hq : IsFixedPt (step A q₀) q) (hord : q.1 ≤ q.2) (k : ℕ) :
    (publicRun A q₀ k : Set (Coord n m → ℝ)).Nonempty :=
  (publicRun_nonempty_iff A q₀ k).mpr ((within_rawRun_of_isFixedPt hq k).fst_le_snd hord)

end TauCeti.AffineBoundTightening
