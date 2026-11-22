/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Topology.Algebra.Ring.Real
public import TauCeti.Analysis.AffineBoundTightening.Basic

/-!
# Simultaneous affine bound-tightening operator and iteration

This file defines the finite-real simultaneous affine bound-tightening operator on joint
variable-and-row endpoint boxes `Raw n m` and its lifted public operator on `State n m` with an
absorbing global empty state `⊥`.

One raw step `step A q₀ q = down A (up A (clip q q₀))` intersects `q` with the initial bounds `q₀`,
updates row intervals from the signed affine images of the variables (`up`), and simultaneously
updates every variable interval from all row inverse intervals evaluated at the same incoming state
(`down`), using a zero coefficient branch that imposes no inverse restriction.

## Main definitions

* `TauCeti.AffineBoundTightening.clip`, `TauCeti.AffineBoundTightening.inverseLo`,
  `TauCeti.AffineBoundTightening.inverseHi`, `TauCeti.AffineBoundTightening.up`,
  `TauCeti.AffineBoundTightening.down`, `TauCeti.AffineBoundTightening.step`: components of one
  simultaneous raw tightening step.
* `TauCeti.AffineBoundTightening.publicStep`, `TauCeti.AffineBoundTightening.rawRun`,
  `TauCeti.AffineBoundTightening.publicRun`: public step with absorbing `⊥` and raw/public
  iterations from `q₀`.
* `TauCeti.AffineBoundTightening.graph`: embedding `x ↦ (x, A.mulVec x)` of a point into joint
  variable-and-row coordinates.

## Main results

* `TauCeti.AffineBoundTightening.step_within_self`,
  `TauCeti.AffineBoundTightening.step_within_initial`,
  `TauCeti.AffineBoundTightening.Within.step`,
  `TauCeti.AffineBoundTightening.continuous_step`: contraction, monotonicity under `Within`, and
  continuity in the finite product topology for fixed `A` and `q₀`.
* `TauCeti.AffineBoundTightening.publicRun_eq_pack_rawRun`: exact commutation between raw and
  public iterates at every step `k`.
* `TauCeti.AffineBoundTightening.graph_survives`: every affine graph point initially enclosed by
  `q₀` belongs to every public iterate `publicRun A q₀ k`.
* `TauCeti.AffineBoundTightening.within_rawRun_of_isFixedPt_step`: every raw fixed tuple of
  `step A q₀` lies within `q₀` and within every raw iterate `rawRun A q₀ k`.

## References

* P. Belotti, S. Cafieri, J. Lee, and L. Liberti, *Feasibility-Based Bounds Tightening via Fixed
  Points*, COCOA 2010, LNCS 6508, pp. 65–76, §2 p. 67, Lemma 2.1 p. 70, and §4 (9)–(11) pp. 71–72.
-/

public section

open scoped BigOperators
open Set

namespace TauCeti.AffineBoundTightening

noncomputable section

variable {n m : ℕ}

/-! ### Clipping -/

/-- Intersect raw endpoints with their initial variable and row bounds. -/
def clip (q q₀ : Raw n m) : Raw n m :=
  (fun c => max (q.1 c) (q₀.1 c), fun c => min (q.2 c) (q₀.2 c))

/-- Lower endpoint of a clipped raw tuple. -/
@[simp]
theorem clip_fst (q q₀ : Raw n m) (c : Coord n m) :
    (clip q q₀).1 c = max (q.1 c) (q₀.1 c) :=
  (rfl)

/-- Upper endpoint of a clipped raw tuple. -/
@[simp]
theorem clip_snd (q q₀ : Raw n m) (c : Coord n m) :
    (clip q q₀).2 c = min (q.2 c) (q₀.2 c) :=
  (rfl)

/-- Membership in the closed box of `clip q q₀` is membership in both closed boxes. -/
theorem mem_Icc_clip_iff {q q₀ : Raw n m} {x : Coord n m → ℝ} :
    x ∈ Icc (clip q q₀).1 (clip q q₀).2 ↔ x ∈ Icc q.1 q.2 ∧ x ∈ Icc q₀.1 q₀.2 := by
  have h : Icc (clip q q₀).1 (clip q q₀).2 = Icc q.1 q.2 ∩ Icc q₀.1 q₀.2 :=
    (Icc_inter_Icc (a₁ := q.1) (b₁ := q.2) (a₂ := q₀.1) (b₂ := q₀.2)).symm
  rw [h, mem_inter_iff]

/-- Packing a clipped raw tuple gives the lattice meet of the packed intervals. -/
theorem pack_clip (q q₀ : Raw n m) : pack (clip q q₀) = pack q ⊓ pack q₀ := by
  apply SetLike.coe_injective
  rw [Interval.coe_inf, coe_pack, coe_pack, coe_pack]
  exact (Icc_inter_Icc (a₁ := q.1) (b₁ := q.2) (a₂ := q₀.1) (b₂ := q₀.2)).symm

/-- Clipping contracts into its first argument. -/
theorem clip_within_left (q q₀ : Raw n m) : Within (clip q q₀) q :=
  within_iff.mpr ⟨fun _ => le_max_left _ _, fun _ => min_le_left _ _⟩

/-- Clipping contracts into its second argument. -/
theorem clip_within_right (q q₀ : Raw n m) : Within (clip q q₀) q₀ :=
  within_iff.mpr ⟨fun _ => le_max_right _ _, fun _ => min_le_right _ _⟩

/-- Clipping `q` against `q₀` leaves `q` unchanged if and only if `Within q q₀`. -/
theorem clip_eq_left_iff {q q₀ : Raw n m} : clip q q₀ = q ↔ Within q q₀ := by
  constructor
  · intro h
    exact h ▸ clip_within_right q q₀
  · intro h
    exact Prod.ext (funext fun c => max_eq_left (h.fst_le c))
      (funext fun c => min_eq_left (h.le_snd c))

/-- Clipping a raw tuple against itself leaves it unchanged. -/
@[simp]
theorem clip_self (q : Raw n m) : clip q q = q :=
  clip_eq_left_iff.mpr Within.rfl

/-- Clipping is monotone in both arguments with respect to `Within`. -/
theorem Within.clip {q₁ q₂ r₁ r₂ : Raw n m} (h₁ : Within q₁ r₁) (h₂ : Within q₂ r₂) :
    Within (clip q₁ q₂) (clip r₁ r₂) :=
  within_iff.mpr
    ⟨fun c => max_le_max (h₁.fst_le c) (h₂.fst_le c),
     fun c => min_le_min (h₁.le_snd c) (h₂.le_snd c)⟩

/-! ### Inverse candidates and the simultaneous maps `up`, `down`, `step` -/

/-- Lower inverse-row candidate; the zero coefficient branch keeps the incoming endpoint. -/
def inverseLo (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) : ℝ :=
  if 0 < A i j then (q.1 (.inr i) - restHi A q i j) / A i j
  else if A i j < 0 then (q.2 (.inr i) - restLo A q i j) / A i j
  else q.1 (.inl j)

/-- Upper inverse-row candidate; the zero coefficient branch keeps the incoming endpoint. -/
def inverseHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) : ℝ :=
  if 0 < A i j then (q.2 (.inr i) - restLo A q i j) / A i j
  else if A i j < 0 then (q.1 (.inr i) - restHi A q i j) / A i j
  else q.2 (.inl j)

/-- Keep variable endpoints and intersect each row with its signed affine image. -/
def up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) : Raw n m :=
  (Sum.elim (fun j => q.1 (.inl j)) (fun i => max (q.1 (.inr i)) (imageLo A q i)),
   Sum.elim (fun j => q.2 (.inl j)) (fun i => min (q.2 (.inr i)) (imageHi A q i)))

/-- Keep row endpoints and intersect each variable with all inverse candidates computed from the
same incoming tuple. -/
def down (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) : Raw n m :=
  (Sum.elim (fun j => Finset.univ.fold max (q.1 (.inl j)) (fun i => inverseLo A q i j))
     (fun i => q.1 (.inr i)),
   Sum.elim (fun j => Finset.univ.fold min (q.2 (.inl j)) (fun i => inverseHi A q i j))
     (fun i => q.2 (.inr i)))

/-- One simultaneous affine tightening step: clipping, upward images, then downward inverses. -/
def step (A : Matrix (Fin m) (Fin n) ℝ) (q₀ q : Raw n m) : Raw n m :=
  down A (up A (clip q q₀))

/-- Lower inverse candidate in the positive-coefficient branch. -/
theorem inverseLo_of_pos {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : 0 < A i j) : inverseLo A q i j = (q.1 (.inr i) - restHi A q i j) / A i j := by
  simp [inverseLo, h]

/-- Lower inverse candidate in the negative-coefficient branch. -/
theorem inverseLo_of_neg {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j < 0) : inverseLo A q i j = (q.2 (.inr i) - restLo A q i j) / A i j := by
  simp [inverseLo, h, not_lt_of_gt h]

/-- A zero coefficient imposes no lower inverse restriction. -/
theorem inverseLo_of_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j = 0) : inverseLo A q i j = q.1 (.inl j) := by
  simp [inverseLo, h]

/-- Upper inverse candidate in the positive-coefficient branch. -/
theorem inverseHi_of_pos {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : 0 < A i j) : inverseHi A q i j = (q.2 (.inr i) - restLo A q i j) / A i j := by
  simp [inverseHi, h]

/-- Upper inverse candidate in the negative-coefficient branch. -/
theorem inverseHi_of_neg {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j < 0) : inverseHi A q i j = (q.1 (.inr i) - restHi A q i j) / A i j := by
  simp [inverseHi, h, not_lt_of_gt h]

/-- A zero coefficient imposes no upper inverse restriction. -/
theorem inverseHi_of_zero {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m} {j : Fin n}
    (h : A i j = 0) : inverseHi A q i j = q.2 (.inl j) := by
  simp [inverseHi, h]

/-- A variable lower endpoint dominates its lower inverse candidate exactly when it dominates the
positive-coefficient and negative-coefficient formulas, each imposed only in its own sign branch. -/
theorem inverseLo_le_fst_inl_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    {j : Fin n} :
    inverseLo A q i j ≤ q.1 (.inl j) ↔
      (0 < A i j → (q.1 (.inr i) - restHi A q i j) / A i j ≤ q.1 (.inl j)) ∧
      (A i j < 0 → (q.2 (.inr i) - restLo A q i j) / A i j ≤ q.1 (.inl j)) := by
  rcases lt_trichotomy (A i j) 0 with ha | ha | ha
  · simp [inverseLo_of_neg ha, ha, not_lt_of_gt ha]
  · simp [inverseLo_of_zero ha, ha]
  · simp [inverseLo_of_pos ha, ha, not_lt_of_gt ha]

/-- A variable upper endpoint lies below its upper inverse candidate exactly when it lies below the
positive-coefficient and negative-coefficient formulas, each imposed only in its own sign branch. -/
theorem snd_inl_le_inverseHi_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {i : Fin m}
    {j : Fin n} :
    q.2 (.inl j) ≤ inverseHi A q i j ↔
      (0 < A i j → q.2 (.inl j) ≤ (q.2 (.inr i) - restLo A q i j) / A i j) ∧
      (A i j < 0 → q.2 (.inl j) ≤ (q.1 (.inr i) - restHi A q i j) / A i j) := by
  rcases lt_trichotomy (A i j) 0 with ha | ha | ha
  · simp [inverseHi_of_neg ha, ha, not_lt_of_gt ha]
  · simp [inverseHi_of_zero ha, ha]
  · simp [inverseHi_of_pos ha, ha, not_lt_of_gt ha]

/-- Lower inverse candidates increase under endpoint containment. -/
theorem Within.inverseLo_le {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} (h : Within q r)
    (i : Fin m) (j : Fin n) : inverseLo A r i j ≤ inverseLo A q i j := by
  rcases lt_trichotomy (A i j) 0 with ha | ha | ha
  · rw [inverseLo_of_neg ha, inverseLo_of_neg ha]
    exact div_le_div_of_nonpos_of_le ha.le (sub_le_sub (h.le_snd (.inr i)) (h.restLo_le i j))
  · rw [inverseLo_of_zero ha, inverseLo_of_zero ha]
    exact h.fst_le (.inl j)
  · rw [inverseLo_of_pos ha, inverseLo_of_pos ha]
    exact div_le_div_of_nonneg_right (sub_le_sub (h.fst_le (.inr i)) (h.restHi_le i j)) ha.le

/-- Upper inverse candidates decrease under endpoint containment. -/
theorem Within.inverseHi_le {A : Matrix (Fin m) (Fin n) ℝ} {q r : Raw n m} (h : Within q r)
    (i : Fin m) (j : Fin n) : inverseHi A q i j ≤ inverseHi A r i j := by
  rcases lt_trichotomy (A i j) 0 with ha | ha | ha
  · rw [inverseHi_of_neg ha, inverseHi_of_neg ha]
    exact div_le_div_of_nonpos_of_le ha.le (sub_le_sub (h.fst_le (.inr i)) (h.restHi_le i j))
  · rw [inverseHi_of_zero ha, inverseHi_of_zero ha]
    exact h.le_snd (.inl j)
  · rw [inverseHi_of_pos ha, inverseHi_of_pos ha]
    exact div_le_div_of_nonneg_right (sub_le_sub (h.le_snd (.inr i)) (h.restLo_le i j)) ha.le

/-- `up` leaves variable lower endpoints unchanged. -/
@[simp]
theorem up_fst_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n) :
    (up A q).1 (.inl j) = q.1 (.inl j) :=
  (rfl)

/-- `up` leaves variable upper endpoints unchanged. -/
@[simp]
theorem up_snd_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n) :
    (up A q).2 (.inl j) = q.2 (.inl j) :=
  (rfl)

/-- Row lower endpoint after `up`. -/
@[simp]
theorem up_fst_inr (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    (up A q).1 (.inr i) = max (q.1 (.inr i)) (imageLo A q i) :=
  (rfl)

/-- Row upper endpoint after `up`. -/
@[simp]
theorem up_snd_inr (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    (up A q).2 (.inr i) = min (q.2 (.inr i)) (imageHi A q i) :=
  (rfl)

/-- `up` preserves signed lower products because it leaves variable bounds unchanged. -/
@[simp]
theorem zLo_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    zLo A (up A q) i j = zLo A q i j := by
  by_cases h : 0 ≤ A i j
  · rw [zLo_of_nonneg h, zLo_of_nonneg h, up_fst_inl]
  · rw [zLo_of_nonpos (le_of_not_ge h), zLo_of_nonpos (le_of_not_ge h), up_snd_inl]

/-- `up` preserves signed upper products because it leaves variable bounds unchanged. -/
@[simp]
theorem zHi_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    zHi A (up A q) i j = zHi A q i j := by
  by_cases h : 0 ≤ A i j
  · rw [zHi_of_nonneg h, zHi_of_nonneg h, up_snd_inl]
  · rw [zHi_of_nonpos (le_of_not_ge h), zHi_of_nonpos (le_of_not_ge h), up_fst_inl]

/-- `up` preserves lower row images. -/
@[simp]
theorem imageLo_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    imageLo A (up A q) i = imageLo A q i := by
  simp [imageLo_def]

/-- `up` preserves upper row images. -/
@[simp]
theorem imageHi_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    imageHi A (up A q) i = imageHi A q i := by
  simp [imageHi_def]

/-- `up` preserves omitted lower sums. -/
@[simp]
theorem restLo_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    restLo A (up A q) i j = restLo A q i j := by
  simp [restLo_def]

/-- `up` preserves omitted upper sums. -/
@[simp]
theorem restHi_up (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) (j : Fin n) :
    restHi A (up A q) i j = restHi A q i j := by
  simp [restHi_def]

/-- `up` contracts into its input tuple. -/
theorem up_within (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) : Within (up A q) q := by
  refine within_iff.mpr ⟨fun c => ?_, fun c => ?_⟩ <;> cases c with
  | inl j => exact le_rfl
  | inr i => first | exact le_max_left _ _ | exact min_le_left _ _

/-- `up` is monotone with respect to `Within`. -/
theorem Within.up {q r : Raw n m} (h : Within q r) (A : Matrix (Fin m) (Fin n) ℝ) :
    Within (up A q) (up A r) := by
  refine within_iff.mpr ⟨fun c => ?_, fun c => ?_⟩ <;> cases c with
  | inl j => first | exact h.fst_le (.inl j) | exact h.le_snd (.inl j)
  | inr i =>
    first
    | exact max_le_max (h.fst_le (.inr i)) (h.imageLo_le i)
    | exact min_le_min (h.le_snd (.inr i)) (h.imageHi_le i)

/-- `up A q = q` if and only if each row interval already lies inside its affine image. -/
theorem up_eq_self_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} :
    up A q = q ↔ ∀ i, imageLo A q i ≤ q.1 (.inr i) ∧ q.2 (.inr i) ≤ imageHi A q i := by
  constructor
  · intro h i
    have h1 : max (q.1 (.inr i)) (imageLo A q i) = q.1 (.inr i) :=
      congrFun (congrArg Prod.fst h) (.inr i)
    have h2 : min (q.2 (.inr i)) (imageHi A q i) = q.2 (.inr i) :=
      congrFun (congrArg Prod.snd h) (.inr i)
    exact ⟨max_eq_left_iff.mp h1, min_eq_left_iff.mp h2⟩
  · intro h
    refine Prod.ext (funext fun c => ?_) (funext fun c => ?_) <;> cases c with
    | inl j => rfl
    | inr i =>
      first
      | exact max_eq_left (h i).1
      | exact min_eq_left (h i).2

/-- Membership in the closed box of `up A q`. -/
theorem mem_Icc_up_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {x : Coord n m → ℝ} :
    x ∈ Icc (up A q).1 (up A q).2 ↔
      x ∈ Icc q.1 q.2 ∧ ∀ i, x (.inr i) ∈ Icc (imageLo A q i) (imageHi A q i) := by
  constructor
  · intro hx
    refine ⟨(up_within A q).Icc_subset hx, fun i => ⟨?_, ?_⟩⟩
    · exact (le_max_right _ _).trans (hx.1 (.inr i))
    · exact (hx.2 (.inr i)).trans (min_le_right _ _)
  · rintro ⟨hx, himg⟩
    refine ⟨fun c => ?_, fun c => ?_⟩ <;> cases c with
    | inl j => first | exact hx.1 (.inl j) | exact hx.2 (.inl j)
    | inr i =>
      first
      | exact max_le (hx.1 (.inr i)) (himg i).1
      | exact le_min (hx.2 (.inr i)) (himg i).2

/-- Variable lower endpoint after `down`. -/
@[simp]
theorem down_fst_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n) :
    (down A q).1 (.inl j) =
      Finset.univ.fold max (q.1 (.inl j)) (fun i => inverseLo A q i j) :=
  (rfl)

/-- Variable upper endpoint after `down`. -/
@[simp]
theorem down_snd_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (j : Fin n) :
    (down A q).2 (.inl j) =
      Finset.univ.fold min (q.2 (.inl j)) (fun i => inverseHi A q i j) :=
  (rfl)

/-- `down` leaves row lower endpoints unchanged. -/
@[simp]
theorem down_fst_inr (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    (down A q).1 (.inr i) = q.1 (.inr i) :=
  (rfl)

/-- `down` leaves row upper endpoints unchanged. -/
@[simp]
theorem down_snd_inr (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m) :
    (down A q).2 (.inr i) = q.2 (.inr i) :=
  (rfl)

/-- Characterization of upper bounds on a variable lower endpoint after `down`. -/
theorem down_fst_inl_le_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {j : Fin n} {t : ℝ} :
    (down A q).1 (.inl j) ≤ t ↔ q.1 (.inl j) ≤ t ∧ ∀ i, inverseLo A q i j ≤ t := by
  simp [Finset.fold_max_le]

/-- Characterization of lower bounds on a variable upper endpoint after `down`. -/
theorem le_down_snd_inl_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {j : Fin n} {t : ℝ} :
    t ≤ (down A q).2 (.inl j) ↔ t ≤ q.2 (.inl j) ∧ ∀ i, t ≤ inverseHi A q i j := by
  simp [Finset.le_fold_min]

/-- Every row's lower inverse candidate lies below the updated variable lower endpoint. -/
theorem inverseLo_le_down_fst_inl (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m)
    (j : Fin n) : inverseLo A q i j ≤ (down A q).1 (.inl j) := by
  rw [down_fst_inl, Finset.le_fold_max]
  exact Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩

/-- The updated variable upper endpoint lies below every row's upper inverse candidate. -/
theorem down_snd_inl_le_inverseHi (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) (i : Fin m)
    (j : Fin n) : (down A q).2 (.inl j) ≤ inverseHi A q i j := by
  rw [down_snd_inl, Finset.fold_min_le]
  exact Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩

/-- `down` contracts into its input tuple. -/
theorem down_within (A : Matrix (Fin m) (Fin n) ℝ) (q : Raw n m) : Within (down A q) q := by
  refine within_iff.mpr ⟨fun c => ?_, fun c => ?_⟩ <;> cases c with
  | inl j =>
    first
    | exact (down_fst_inl_le_iff.mp le_rfl).1
    | exact (le_down_snd_inl_iff.mp le_rfl).1
  | inr i => exact le_rfl

/-- `down` is monotone with respect to `Within`. -/
theorem Within.down {q r : Raw n m} (h : Within q r) (A : Matrix (Fin m) (Fin n) ℝ) :
    Within (down A q) (down A r) := by
  refine within_iff.mpr ⟨fun c => ?_, fun c => ?_⟩ <;> cases c with
  | inl j =>
    first
    | exact down_fst_inl_le_iff.mpr
        ⟨(h.fst_le (.inl j)).trans ((down_within A q).fst_le (.inl j)),
          fun i => (h.inverseLo_le i j).trans (inverseLo_le_down_fst_inl A q i j)⟩
    | exact le_down_snd_inl_iff.mpr
        ⟨((down_within A q).le_snd (.inl j)).trans (h.le_snd (.inl j)),
          fun i => (down_snd_inl_le_inverseHi A q i j).trans (h.inverseHi_le i j)⟩
  | inr i => first | exact h.fst_le (.inr i) | exact h.le_snd (.inr i)

/-- `down A q = q` if and only if each variable interval already respects every row inverse
candidate. -/
theorem down_eq_self_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} :
    down A q = q ↔ ∀ i j, inverseLo A q i j ≤ q.1 (.inl j) ∧ q.2 (.inl j) ≤ inverseHi A q i j := by
  constructor
  · intro h i j
    have h1 : (down A q).1 (.inl j) ≤ q.1 (.inl j) := by rw [h]
    have h2 : q.2 (.inl j) ≤ (down A q).2 (.inl j) := by rw [h]
    exact ⟨(down_fst_inl_le_iff.mp h1).2 i, (le_down_snd_inl_iff.mp h2).2 i⟩
  · intro h
    refine (down_within A q).antisymm (within_iff.mpr ⟨fun c => ?_, fun c => ?_⟩) <;> cases c with
    | inl j =>
      first
      | exact down_fst_inl_le_iff.mpr ⟨le_rfl, fun i => (h i j).1⟩
      | exact le_down_snd_inl_iff.mpr ⟨le_rfl, fun i => (h i j).2⟩
    | inr i => exact le_rfl

/-- Membership in the closed box of `down A q`. -/
theorem mem_Icc_down_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {x : Coord n m → ℝ} :
    x ∈ Icc (down A q).1 (down A q).2 ↔
      x ∈ Icc q.1 q.2 ∧ ∀ i j, x (.inl j) ∈ Icc (inverseLo A q i j) (inverseHi A q i j) := by
  constructor
  · intro hx
    refine ⟨(down_within A q).Icc_subset hx, fun i j => ⟨?_, ?_⟩⟩
    · exact (inverseLo_le_down_fst_inl A q i j).trans (hx.1 (.inl j))
    · exact (hx.2 (.inl j)).trans (down_snd_inl_le_inverseHi A q i j)
  · rintro ⟨hx, hinv⟩
    refine ⟨fun c => ?_, fun c => ?_⟩ <;> cases c with
    | inl j =>
      first
      | exact down_fst_inl_le_iff.mpr ⟨hx.1 (.inl j), fun i => (hinv i j).1⟩
      | exact le_down_snd_inl_iff.mpr ⟨hx.2 (.inl j), fun i => (hinv i j).2⟩
    | inr i => first | exact hx.1 (.inr i) | exact hx.2 (.inr i)

/-- With zero rows, `up` is the identity. -/
@[simp]
theorem up_zero_rows (A : Matrix (Fin 0) (Fin n) ℝ) (q : Raw n 0) : up A q = q :=
  up_eq_self_iff.mpr fun i => Fin.elim0 i

/-- With zero rows, `down` is the identity. -/
@[simp]
theorem down_zero_rows (A : Matrix (Fin 0) (Fin n) ℝ) (q : Raw n 0) : down A q = q :=
  down_eq_self_iff.mpr fun i => Fin.elim0 i

/-- Definitional unfolding of `step`. -/
theorem step_def (A : Matrix (Fin m) (Fin n) ℝ) (q₀ q : Raw n m) :
    step A q₀ q = down A (up A (clip q q₀)) :=
  (rfl)

/-- With zero rows, `step` reduces to clipping against the initial bounds. -/
@[simp]
theorem step_zero_rows (A : Matrix (Fin 0) (Fin n) ℝ) (q₀ q : Raw n 0) :
    step A q₀ q = clip q q₀ := by
  simp [step_def]

/-- With zero rows, a raw tuple is fixed by `step` if and only if it lies within `q₀`. -/
theorem isFixedPt_step_zero_rows_iff (A : Matrix (Fin 0) (Fin n) ℝ) (q₀ q : Raw n 0) :
    Function.IsFixedPt (step A q₀) q ↔ Within q q₀ := by
  rw [Function.IsFixedPt, step_zero_rows, clip_eq_left_iff]

/-! ### Contraction, monotonicity, invalidity persistence, and continuity of `step` -/

/-- One tightening step contracts into its incoming tuple. -/
theorem step_within_self (A : Matrix (Fin m) (Fin n) ℝ) (q₀ q : Raw n m) :
    Within (step A q₀ q) q :=
  (down_within A _).trans ((up_within A _).trans (clip_within_left q q₀))

/-- One tightening step contracts into the initial tuple `q₀`. -/
theorem step_within_initial (A : Matrix (Fin m) (Fin n) ℝ) (q₀ q : Raw n m) :
    Within (step A q₀ q) q₀ :=
  (down_within A _).trans ((up_within A _).trans (clip_within_right q q₀))

/-- `step A q₀` is monotone with respect to endpoint containment `Within`. -/
theorem Within.step {q r : Raw n m} (h : Within q r) (A : Matrix (Fin m) (Fin n) ℝ)
    (q₀ : Raw n m) : Within (step A q₀ q) (step A q₀ r) :=
  ((h.clip Within.rfl).up A).down A

/-- Once a raw tuple is invalid, one application of `step` remains invalid. -/
theorem not_le_step_of_not_le {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (h : ¬ q.1 ≤ q.2) : ¬ (step A q₀ q).1 ≤ (step A q₀ q).2 :=
  fun hs => h ((step_within_self A q₀ q).le_of_le hs)

/-- Characterization of raw fixed points of `step A q₀` in terms of initial containment, row-image
bounds, and inverse-row bounds. -/
theorem isFixedPt_step_iff {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m} :
    Function.IsFixedPt (step A q₀) q ↔
      Within q q₀ ∧
      (∀ i, imageLo A q i ≤ q.1 (.inr i) ∧ q.2 (.inr i) ≤ imageHi A q i) ∧
      (∀ i j, inverseLo A q i j ≤ q.1 (.inl j) ∧ q.2 (.inl j) ≤ inverseHi A q i j) := by
  constructor
  · intro hfix
    have hq₀ : Within q q₀ := hfix ▸ step_within_initial A q₀ q
    have hclip : clip q q₀ = q := clip_eq_left_iff.mpr hq₀
    have hdu : down A (up A q) = q := by
      simpa [Function.IsFixedPt, step_def, hclip] using hfix
    have hqup : Within q (up A q) := by
      simpa [hdu] using down_within A (up A q)
    have hup : up A q = q := (up_within A q).antisymm hqup
    have hdown : down A q = q := by
      simpa [hup] using hdu
    exact ⟨hq₀, up_eq_self_iff.mp hup, down_eq_self_iff.mp hdown⟩
  · rintro ⟨hq₀, hup, hdown⟩
    rw [Function.IsFixedPt, step_def, clip_eq_left_iff.mpr hq₀, up_eq_self_iff.mpr hup,
      down_eq_self_iff.mpr hdown]

/-- Continuity of `zLo` in the raw tuple for fixed `A`, `i`, `j`. -/
theorem continuous_zLo (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous (fun q : Raw n m => zLo A q i j) := by
  by_cases h : 0 ≤ A i j
  · simp only [zLo_of_nonneg h]
    exact continuous_const.mul ((continuous_apply (Sum.inl j : Coord n m)).comp continuous_fst)
  · simp only [zLo_of_nonpos (le_of_not_ge h)]
    exact continuous_const.mul ((continuous_apply (Sum.inl j : Coord n m)).comp continuous_snd)

/-- Continuity of `zHi` in the raw tuple for fixed `A`, `i`, `j`. -/
theorem continuous_zHi (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous (fun q : Raw n m => zHi A q i j) := by
  by_cases h : 0 ≤ A i j
  · simp only [zHi_of_nonneg h]
    exact continuous_const.mul ((continuous_apply (Sum.inl j : Coord n m)).comp continuous_snd)
  · simp only [zHi_of_nonpos (le_of_not_ge h)]
    exact continuous_const.mul ((continuous_apply (Sum.inl j : Coord n m)).comp continuous_fst)

/-- Continuity of `imageLo` in the raw tuple for fixed `A`, `i`. -/
theorem continuous_imageLo (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Continuous (fun q : Raw n m => imageLo A q i) := by
  simp only [imageLo_def]
  exact continuous_finsetSum _ fun j _ => continuous_zLo A i j

/-- Continuity of `imageHi` in the raw tuple for fixed `A`, `i`. -/
theorem continuous_imageHi (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Continuous (fun q : Raw n m => imageHi A q i) := by
  simp only [imageHi_def]
  exact continuous_finsetSum _ fun j _ => continuous_zHi A i j

/-- Continuity of `restLo` in the raw tuple for fixed `A`, `i`, `j`. -/
theorem continuous_restLo (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous (fun q : Raw n m => restLo A q i j) := by
  simp only [restLo_def]
  exact continuous_finsetSum _ fun k _ => continuous_zLo A i k

/-- Continuity of `restHi` in the raw tuple for fixed `A`, `i`, `j`. -/
theorem continuous_restHi (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous (fun q : Raw n m => restHi A q i j) := by
  simp only [restHi_def]
  exact continuous_finsetSum _ fun k _ => continuous_zHi A i k

/-- Joint continuity of `clip` in both raw tuples in the finite product topology. -/
theorem continuous_clip : Continuous (fun p : Raw n m × Raw n m => clip p.1 p.2) := by
  refine Continuous.prodMk (continuous_pi fun c => ?_) (continuous_pi fun c => ?_)
  · exact ((continuous_apply c).comp (continuous_fst.comp continuous_fst)).max
      ((continuous_apply c).comp (continuous_fst.comp continuous_snd))
  · exact ((continuous_apply c).comp (continuous_snd.comp continuous_fst)).min
      ((continuous_apply c).comp (continuous_snd.comp continuous_snd))

/-- Continuity of `inverseLo` in the raw tuple for fixed `A`, `i`, `j`, including the zero
branch. -/
theorem continuous_inverseLo (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous (fun q : Raw n m => inverseLo A q i j) := by
  rcases lt_trichotomy (A i j) 0 with ha | ha | ha
  · simp only [inverseLo_of_neg ha]
    exact (((continuous_apply (Sum.inr i : Coord n m)).comp continuous_snd).sub
      (continuous_restLo A i j)).div_const (A i j)
  · simp only [inverseLo_of_zero ha]
    exact (continuous_apply (Sum.inl j : Coord n m)).comp continuous_fst
  · simp only [inverseLo_of_pos ha]
    exact (((continuous_apply (Sum.inr i : Coord n m)).comp continuous_fst).sub
      (continuous_restHi A i j)).div_const (A i j)

/-- Continuity of `inverseHi` in the raw tuple for fixed `A`, `i`, `j`, including the zero
branch. -/
theorem continuous_inverseHi (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (j : Fin n) :
    Continuous (fun q : Raw n m => inverseHi A q i j) := by
  rcases lt_trichotomy (A i j) 0 with ha | ha | ha
  · simp only [inverseHi_of_neg ha]
    exact (((continuous_apply (Sum.inr i : Coord n m)).comp continuous_fst).sub
      (continuous_restHi A i j)).div_const (A i j)
  · simp only [inverseHi_of_zero ha]
    exact (continuous_apply (Sum.inl j : Coord n m)).comp continuous_snd
  · simp only [inverseHi_of_pos ha]
    exact (((continuous_apply (Sum.inr i : Coord n m)).comp continuous_snd).sub
      (continuous_restLo A i j)).div_const (A i j)

/-- Continuity of `up A` in the finite product topology on `Raw n m`. -/
theorem continuous_up (A : Matrix (Fin m) (Fin n) ℝ) : Continuous (up A) := by
  refine Continuous.prodMk (continuous_pi fun c => ?_) (continuous_pi fun c => ?_) <;>
    cases c with
    | inl j =>
      first
      | exact (continuous_apply (Sum.inl j : Coord n m)).comp continuous_fst
      | exact (continuous_apply (Sum.inl j : Coord n m)).comp continuous_snd
    | inr i =>
      first
      | exact ((continuous_apply (Sum.inr i : Coord n m)).comp continuous_fst).max
          (continuous_imageLo A i)
      | exact ((continuous_apply (Sum.inr i : Coord n m)).comp continuous_snd).min
          (continuous_imageHi A i)

/-- Continuity of `down A` in the finite product topology on `Raw n m`. -/
theorem continuous_down (A : Matrix (Fin m) (Fin n) ℝ) : Continuous (down A) := by
  have hmax (s : Finset (Fin m)) (j : Fin n) :
      Continuous fun q : Raw n m =>
        s.fold max (q.1 (.inl j)) (fun i => inverseLo A q i j) := by
    induction s using Finset.induction_on with
    | empty => exact (continuous_apply (Sum.inl j : Coord n m)).comp continuous_fst
    | insert i s hi ih =>
      simpa only [Finset.fold_insert hi] using (continuous_inverseLo A i j).max ih
  have hmin (s : Finset (Fin m)) (j : Fin n) :
      Continuous fun q : Raw n m =>
        s.fold min (q.2 (.inl j)) (fun i => inverseHi A q i j) := by
    induction s using Finset.induction_on with
    | empty => exact (continuous_apply (Sum.inl j : Coord n m)).comp continuous_snd
    | insert i s hi ih =>
      simpa only [Finset.fold_insert hi] using (continuous_inverseHi A i j).min ih
  refine Continuous.prodMk (continuous_pi fun c => ?_) (continuous_pi fun c => ?_) <;>
    cases c with
    | inl j => first | exact hmax Finset.univ j | exact hmin Finset.univ j
    | inr i =>
      first
      | exact (continuous_apply (Sum.inr i : Coord n m)).comp continuous_fst
      | exact (continuous_apply (Sum.inr i : Coord n m)).comp continuous_snd

/-- Continuity of one simultaneous tightening step `step A q₀` in the finite product topology. -/
theorem continuous_step (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    Continuous (step A q₀) :=
  (continuous_down A).comp
    ((continuous_up A).comp (continuous_clip.comp (continuous_id.prodMk continuous_const)))

/-! ### Raw and public iterates -/

/-- Apply the raw step to nonempty intervals and keep global bottom absorbing. -/
def publicStep (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) : State n m → State n m :=
  Interval.recBotCoe ⊥ (fun q => pack (step A q₀ (q.fst, q.snd)))

/-- Actual raw iteration from the initial endpoints. -/
def rawRun (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) : Raw n m :=
  (step A q₀)^[k] q₀

/-- Actual public iteration from the packed initial endpoints. -/
def publicRun (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) : State n m :=
  (publicStep A q₀)^[k] (pack q₀)

/-- Global bottom is absorbing under `publicStep`. -/
@[simp]
theorem publicStep_bot (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    publicStep A q₀ ⊥ = ⊥ :=
  (rfl)

/-- Action of `publicStep` on a nonempty interval. -/
@[simp]
theorem publicStep_coe (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m)
    (s : NonemptyInterval (Coord n m → ℝ)) :
    publicStep A q₀ (s : State n m) = pack (step A q₀ s.toProd) :=
  (rfl)

/-- `pack` intertwines `step` and `publicStep` on all raw tuples, valid or invalid. -/
@[simp]
theorem publicStep_pack (A : Matrix (Fin m) (Fin n) ℝ) (q₀ q : Raw n m) :
    publicStep A q₀ (pack q) = pack (step A q₀ q) := by
  by_cases h : q.1 ≤ q.2
  · rw [pack_of_le h, publicStep_coe]
  · rw [pack_of_not_le h, publicStep_bot, pack_of_not_le (not_le_step_of_not_le h)]

/-- Definitional unfolding of `rawRun`. -/
theorem rawRun_def (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    rawRun A q₀ k = (step A q₀)^[k] q₀ :=
  (rfl)

/-- The zeroth raw iterate is `q₀`. -/
@[simp]
theorem rawRun_zero (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    rawRun A q₀ 0 = q₀ :=
  (rfl)

/-- Successor identity for `rawRun`. -/
@[simp]
theorem rawRun_succ (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    rawRun A q₀ (k + 1) = step A q₀ (rawRun A q₀ k) :=
  Function.iterate_succ_apply' (step A q₀) k q₀

/-- Definitional unfolding of `publicRun`. -/
theorem publicRun_def (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    publicRun A q₀ k = (publicStep A q₀)^[k] (pack q₀) :=
  (rfl)

/-- The zeroth public iterate is `pack q₀`. -/
@[simp]
theorem publicRun_zero (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    publicRun A q₀ 0 = pack q₀ :=
  (rfl)

/-- Successor identity for `publicRun`. -/
@[simp]
theorem publicRun_succ (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    publicRun A q₀ (k + 1) = publicStep A q₀ (publicRun A q₀ k) :=
  Function.iterate_succ_apply' (publicStep A q₀) k (pack q₀)

/-- Every public iterate is the packed form of the corresponding raw iterate. -/
theorem publicRun_eq_pack_rawRun (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    publicRun A q₀ k = pack (rawRun A q₀ k) :=
  (Function.Semiconj.iterate_right (fun q => (publicStep_pack A q₀ q).symm) k q₀).symm

/-- Later raw iterates lie within earlier raw iterates. -/
theorem rawRun_within_of_le (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) {j k : ℕ}
    (hjk : j ≤ k) : Within (rawRun A q₀ k) (rawRun A q₀ j) := by
  induction k, hjk using Nat.le_induction with
  | base => exact Within.rfl
  | succ k _ ih =>
    rw [rawRun_succ]
    exact (step_within_self A q₀ (rawRun A q₀ k)).trans ih

/-- Every raw iterate lies within the initial tuple `q₀`. -/
theorem rawRun_within_initial (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    Within (rawRun A q₀ k) q₀ :=
  rawRun_within_of_le A q₀ (Nat.zero_le k)

/-- Lower endpoints of `rawRun` form a monotone sequence. -/
theorem monotone_rawRun_fst (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    Monotone (fun k => (rawRun A q₀ k).1) :=
  fun _ _ hjk => (rawRun_within_of_le A q₀ hjk).fst_le

/-- Upper endpoints of `rawRun` form an antitone sequence. -/
theorem antitone_rawRun_snd (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    Antitone (fun k => (rawRun A q₀ k).2) :=
  fun _ _ hjk => (rawRun_within_of_le A q₀ hjk).le_snd

/-- Public iterates form an antitone sequence in `State n m`. -/
theorem antitone_publicRun (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) :
    Antitone (publicRun A q₀) := by
  intro j k hjk
  rw [publicRun_eq_pack_rawRun, publicRun_eq_pack_rawRun]
  exact (rawRun_within_of_le A q₀ hjk).pack_le

/-- Once a public iterate reaches `⊥`, all later public iterates remain `⊥`. -/
theorem publicRun_eq_bot_of_le {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m} {j k : ℕ}
    (hjk : j ≤ k) (hj : publicRun A q₀ j = ⊥) : publicRun A q₀ k = ⊥ :=
  le_bot_iff.mp (hj ▸ antitone_publicRun A q₀ hjk)

/-- A public iterate is nonbottom if and only if the raw iterate has ordered endpoints. -/
theorem publicRun_ne_bot_iff (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    publicRun A q₀ k ≠ ⊥ ↔ (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2 := by
  rw [publicRun_eq_pack_rawRun, pack_ne_bot_iff]

/-- A public iterate has a Cartesian member if and only if the raw iterate has ordered
endpoints. -/
theorem coe_publicRun_nonempty_iff (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (k : ℕ) :
    (publicRun A q₀ k : Set (Coord n m → ℝ)).Nonempty ↔
      (rawRun A q₀ k).1 ≤ (rawRun A q₀ k).2 := by
  rw [publicRun_eq_pack_rawRun, coe_pack, nonempty_Icc]

/-! ### Graph points survive every iterate -/

/-- The joint point consisting of the original variables and their affine row values. -/
def graph (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Coord n m → ℝ :=
  Sum.elim x (A.mulVec x)

/-- Variable-coordinate projection of `graph A x`. -/
@[simp]
theorem graph_inl (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (j : Fin n) :
    graph A x (.inl j) = x j :=
  (rfl)

/-- Row-coordinate projection of `graph A x`. -/
@[simp]
theorem graph_inr (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m) :
    graph A x (.inr i) = A.mulVec x i :=
  (rfl)

/-- The graph map `x ↦ (x, A.mulVec x)` is injective. -/
theorem graph_injective (A : Matrix (Fin m) (Fin n) ℝ) : Function.Injective (graph A) :=
  fun _ _ h => funext fun j => congrFun h (.inl j)

/-- Characterization of box membership for a graph point. -/
theorem mem_Icc_graph_iff {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {x : Fin n → ℝ} :
    graph A x ∈ Icc q.1 q.2 ↔
      (∀ j, x j ∈ Icc (q.1 (.inl j)) (q.2 (.inl j))) ∧
      (∀ i, A.mulVec x i ∈ Icc (q.1 (.inr i)) (q.2 (.inr i))) := by
  constructor
  · intro hx
    exact ⟨fun j => ⟨hx.1 (.inl j), hx.2 (.inl j)⟩, fun i => ⟨hx.1 (.inr i), hx.2 (.inr i)⟩⟩
  · rintro ⟨hx, hb⟩
    refine ⟨fun c => ?_, fun c => ?_⟩ <;> cases c with
    | inl j => first | exact (hx j).1 | exact (hx j).2
    | inr i => first | exact (hb i).1 | exact (hb i).2

/-- A graph point enclosed by a raw box remains enclosed after `up`. -/
theorem graph_mem_Icc_up {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {x : Fin n → ℝ}
    (hx : graph A x ∈ Icc q.1 q.2) : graph A x ∈ Icc (up A q).1 (up A q).2 := by
  have hxvar : ∀ j, x j ∈ Icc (q.1 (.inl j)) (q.2 (.inl j)) := (mem_Icc_graph_iff.mp hx).1
  exact mem_Icc_up_iff.mpr ⟨hx, fun i => ⟨imageLo_le_mulVec hxvar, mulVec_le_imageHi hxvar⟩⟩

/-- A graph point enclosed by a raw box remains enclosed after `down`. -/
theorem graph_mem_Icc_down {A : Matrix (Fin m) (Fin n) ℝ} {q : Raw n m} {x : Fin n → ℝ}
    (hx : graph A x ∈ Icc q.1 q.2) : graph A x ∈ Icc (down A q).1 (down A q).2 := by
  obtain ⟨hxvar, hxrow⟩ := mem_Icc_graph_iff.mp hx
  refine mem_Icc_down_iff.mpr ⟨hx, fun i j => ?_⟩
  have hsplit : A.mulVec x i = A i j * x j + ∑ k ∈ Finset.univ.erase j, A i k * x k := by
    rw [Matrix.mulVec, dotProduct, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
  have hlo : restLo A q i j ≤ ∑ k ∈ Finset.univ.erase j, A i k * x k :=
    restLo_le_sum_erase fun k _ => hxvar k
  have hhi : ∑ k ∈ Finset.univ.erase j, A i k * x k ≤ restHi A q i j :=
    sum_erase_le_restHi fun k _ => hxvar k
  have hrow1 : q.1 (.inr i) ≤ A i j * x j + ∑ k ∈ Finset.univ.erase j, A i k * x k :=
    hsplit ▸ (hxrow i).1
  have hrow2 : A i j * x j + ∑ k ∈ Finset.univ.erase j, A i k * x k ≤ q.2 (.inr i) :=
    hsplit ▸ (hxrow i).2
  simp only [graph_inl]
  rcases lt_trichotomy (A i j) 0 with ha | ha | ha
  · rw [inverseLo_of_neg ha, inverseHi_of_neg ha]
    refine ⟨(div_le_iff_of_neg ha).mpr ?_, (le_div_iff_of_neg ha).mpr ?_⟩ <;>
      · rw [mul_comm]; grind
  · rw [inverseLo_of_zero ha, inverseHi_of_zero ha]
    exact hxvar j
  · rw [inverseLo_of_pos ha, inverseHi_of_pos ha]
    refine ⟨(div_le_iff₀ ha).mpr ?_, (le_div_iff₀ ha).mpr ?_⟩ <;>
      · rw [mul_comm]; grind

/-- A graph point enclosed by both `q` and `q₀` remains enclosed after one `step`. -/
theorem graph_mem_Icc_step {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m} {x : Fin n → ℝ}
    (hxq : graph A x ∈ Icc q.1 q.2) (hx₀ : graph A x ∈ Icc q₀.1 q₀.2) :
    graph A x ∈ Icc (step A q₀ q).1 (step A q₀ q).2 :=
  graph_mem_Icc_down (graph_mem_Icc_up (mem_Icc_clip_iff.mpr ⟨hxq, hx₀⟩))

/-- An initially enclosed affine graph point belongs to every raw iterate's closed box. -/
theorem graph_mem_Icc_rawRun (A : Matrix (Fin m) (Fin n) ℝ) (q₀ : Raw n m) (x : Fin n → ℝ)
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
  rw [publicRun_eq_pack_rawRun, coe_pack]
  exact graph_mem_Icc_rawRun A q₀ x hx k

/-- The singleton box at an initially enclosed graph point is fixed by `step A q₀`. -/
theorem isFixedPt_step_graph {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m} {x : Fin n → ℝ}
    (hx : graph A x ∈ Icc q₀.1 q₀.2) :
    Function.IsFixedPt (step A q₀) (graph A x, graph A x) := by
  have hmem := graph_mem_Icc_step (q := (graph A x, graph A x)) ⟨le_rfl, le_rfl⟩ hx
  have hw := step_within_self A q₀ (graph A x, graph A x)
  exact Prod.ext (le_antisymm hmem.1 hw.fst_le) (le_antisymm hw.le_snd hmem.2)

/-- Supplying an initially enclosed graph point witnesses nonemptiness of every public iterate. -/
theorem coe_publicRun_nonempty_of_graph {A : Matrix (Fin m) (Fin n) ℝ} {q₀ : Raw n m}
    {x : Fin n → ℝ} (hx : graph A x ∈ Icc q₀.1 q₀.2) (k : ℕ) :
    (publicRun A q₀ k : Set (Coord n m → ℝ)).Nonempty :=
  ⟨graph A x, graph_survives A q₀ x hx k⟩

/-! ### Fixed tuples lie in every iterate -/

/-- Every raw fixed tuple of `step A q₀` lies within the initial tuple `q₀`. -/
theorem within_initial_of_isFixedPt_step {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hq : Function.IsFixedPt (step A q₀) q) : Within q q₀ :=
  hq ▸ step_within_initial A q₀ q

/-- Every raw fixed tuple of `step A q₀` lies within every raw iterate `rawRun A q₀ k`. -/
theorem within_rawRun_of_isFixedPt_step {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hq : Function.IsFixedPt (step A q₀) q) (k : ℕ) : Within q (rawRun A q₀ k) := by
  induction k with
  | zero => exact within_initial_of_isFixedPt_step hq
  | succ k ih =>
    rw [rawRun_succ]
    exact hq ▸ ih.step A q₀

/-- Every packed raw fixed tuple of `step A q₀` lies below every public iterate. -/
theorem pack_le_publicRun_of_isFixedPt_step {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hq : Function.IsFixedPt (step A q₀) q) (k : ℕ) : pack q ≤ publicRun A q₀ k := by
  rw [publicRun_eq_pack_rawRun]
  exact (within_rawRun_of_isFixedPt_step hq k).pack_le

/-- An ordered raw fixed tuple of `step A q₀` witnesses nonemptiness of every public iterate. -/
theorem coe_publicRun_nonempty_of_isFixedPt_step {A : Matrix (Fin m) (Fin n) ℝ} {q₀ q : Raw n m}
    (hord : q.1 ≤ q.2) (hq : Function.IsFixedPt (step A q₀) q) (k : ℕ) :
    (publicRun A q₀ k : Set (Coord n m → ℝ)).Nonempty :=
  (coe_publicRun_nonempty_iff A q₀ k).mpr
    ((within_rawRun_of_isFixedPt_step hq k).le_of_le hord)

end

end TauCeti.AffineBoundTightening
