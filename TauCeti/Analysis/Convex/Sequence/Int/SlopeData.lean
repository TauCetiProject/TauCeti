/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Int.Basic
public import TauCeti.Analysis.Convex.Sequence.SlopeData.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Order.Interval.Set.OrdConnectedLinear

/-!
# Integer-anchored slope presentations

A convex height sequence on `ℤ` whose finite domain is bounded below can be described
by its first point and its nondecreasing unit slopes. `IntFiniteSlopeData` describes a
nonempty finite interval; `IntInfiniteSlopeData` describes a half-line. The initial
abscissa may be negative. A finite presentation of length zero is a singleton, and
neither presentation represents the empty polygon or a domain unbounded below.

Heights are obtained by extending the cumulative-sum construction of
`FiniteSlopeData` and `InfiniteSlopeData` by infinity and translating its anchor. Over
the reals they are convex.
Extraction from a convex sequence with the specified domain and reconstruction are
inverse operations; `exists_heights_eq_iff` characterises the possible domains. These
presentations therefore describe the geometry independently
of any coefficient sequence producing it.
-/

public section

namespace TauCeti

variable {Γ Γ' : Type*} [Preorder Γ] [Preorder Γ']

/-- A finite polygon with integer initial abscissa and nondecreasing unit slopes.
Length zero describes just its anchor, with no edges. -/
structure IntFiniteSlopeData (Γ : Type*) [Preorder Γ] where
  /-- The first integer with finite height. -/
  start : ℤ
  /-- The height at the first point. -/
  initialHeight : Γ
  /-- The number of unit edges. -/
  length : ℕ
  /-- The slopes of the unit edges, from left to right. -/
  slope : Fin length → Γ
  /-- Slopes are nondecreasing. -/
  monotone : Monotone slope

namespace IntFiniteSlopeData

/-- Read the relative slope data at the natural-number anchor zero. -/
def toFiniteSlopeData (d : IntFiniteSlopeData Γ) : FiniteSlopeData Γ where
  start := 0
  initialHeight := d.initialHeight
  length := d.length
  slope := d.slope
  monotone := d.monotone

@[simp]
theorem toFiniteSlopeData_start (d : IntFiniteSlopeData Γ) :
    d.toFiniteSlopeData.start = 0 := (rfl)
@[simp]
theorem toFiniteSlopeData_initialHeight (d : IntFiniteSlopeData Γ) :
    d.toFiniteSlopeData.initialHeight = d.initialHeight := (rfl)
@[simp]
theorem toFiniteSlopeData_length (d : IntFiniteSlopeData Γ) :
    d.toFiniteSlopeData.length = d.length := (rfl)
@[simp]
theorem toFiniteSlopeData_slope (d : IntFiniteSlopeData Γ) (i : Fin d.toFiniteSlopeData.length) :
    d.toFiniteSlopeData.slope i = d.slope (i.cast d.toFiniteSlopeData_length) := (rfl)

/-- The integer anchor together with the relative natural-indexed data determines a presentation. -/
@[ext]
theorem ext {d e : IntFiniteSlopeData Γ} (hs : d.start = e.start)
    (hd : d.toFiniteSlopeData = e.toFiniteSlopeData) : d = e := by
  cases d
  cases e
  cases hs
  cases hd
  rfl

/-- Translate the integer anchor, preserving the initial height and all relative slopes. -/
def translate (d : IntFiniteSlopeData Γ) (k : ℤ) : IntFiniteSlopeData Γ :=
  { d with start := d.start + k }

@[simp]
theorem translate_start (d : IntFiniteSlopeData Γ) (k : ℤ) :
    (d.translate k).start = d.start + k := (rfl)

@[simp]
theorem translate_initialHeight (d : IntFiniteSlopeData Γ) (k : ℤ) :
    (d.translate k).initialHeight = d.initialHeight := (rfl)
@[simp]
theorem translate_length (d : IntFiniteSlopeData Γ) (k : ℤ) :
    (d.translate k).length = d.length := (rfl)
@[simp]
theorem translate_slope (d : IntFiniteSlopeData Γ) (k : ℤ)
    (i : Fin (d.translate k).length) :
    (d.translate k).slope i = d.slope (i.cast (d.translate_length k)) := (rfl)

/-- Anchor translation preserves the relative natural-indexed data. -/
@[simp]
theorem toFiniteSlopeData_translate (d : IntFiniteSlopeData Γ) (k : ℤ) :
    (d.translate k).toFiniteSlopeData = d.toFiniteSlopeData := (rfl)

section AddCommMonoid

variable [AddCommMonoid Γ] [AddCommMonoid Γ'] (d : IntFiniteSlopeData Γ)

/-- Cumulative-sum heights on the finite domain, extended by infinity outside it. -/
noncomputable def heights (n : ℤ) : WithTop Γ :=
  Function.extend ((↑) : ℕ → ℤ) d.toFiniteSlopeData.heights ⊤ (n - d.start)

/-- The defining extension-and-translation formula for the represented heights. -/
theorem heights_def (n : ℤ) : d.heights n =
    Function.extend ((↑) : ℕ → ℤ) d.toFiniteSlopeData.heights ⊤ (n - d.start) := (rfl)

/-- Translating the anchor translates the represented integer heights. -/
@[simp]
theorem heights_translate (k n : ℤ) : (d.translate k).heights n = d.heights (n - k) := by
  simp only [heights_def, translate_start, toFiniteSlopeData_translate, sub_add_eq_sub_sub,
    sub_right_comm]

/-- At an offset from the anchor, the heights agree with the natural-indexed construction. -/
@[simp]
theorem heights_start_add (n : ℕ) : d.heights (d.start + n) = d.toFiniteSlopeData.heights n := by
  simp only [heights, add_sub_cancel_left, Nat.cast_injective.extend_apply]

/-- The heights are infinite strictly before the anchor. -/
theorem heights_eq_top_of_lt {n : ℤ} (hn : n < d.start) : d.heights n = ⊤ :=
  Function.extend_natCast_of_neg _ _ (sub_neg.mpr hn)

/-- The finite domain is exactly the interval from `start` to `start + length`. -/
theorem heights_ne_top_iff {n : ℤ} :
    d.heights n ≠ ⊤ ↔ d.start ≤ n ∧ n ≤ d.start + d.length := by
  refine Function.extend_natCast_sub_induction d.toFiniteSlopeData.heights ⊤ d.start n
    (P := fun n y => y ≠ ⊤ ↔ d.start ≤ n ∧ n ≤ d.start + d.length) ?_ ?_
  · intro n hn
    simp [not_le.mpr hn]
  · intro k
    rw [FiniteSlopeData.heights_ne_top_iff]
    simp only [toFiniteSlopeData_start, toFiniteSlopeData_length, zero_add]
    omega

/-- The finite domain of the represented integer heights. -/
theorem setOf_heights_ne_top :
    {n | d.heights n ≠ ⊤} = Set.Icc d.start (d.start + d.length) :=
  Set.ext fun _ => d.heights_ne_top_iff

/-- The represented heights are infinite precisely outside the finite domain. -/
@[simp]
theorem heights_eq_top_iff {n : ℤ} :
    d.heights n = ⊤ ↔ n < d.start ∨ d.start + d.length < n := by
  rw [← not_iff_not, ← ne_eq, heights_ne_top_iff]
  omega

/-- The height at the anchor is the initial height. -/
@[simp]
theorem heights_start : d.heights d.start = (d.initialHeight : WithTop Γ) := by
  calc d.heights d.start = d.toFiniteSlopeData.heights d.toFiniteSlopeData.start := by
         simpa using d.heights_start_add 0
       _ = (d.initialHeight : WithTop Γ) := d.toFiniteSlopeData.heights_start

/-- Transport the heights and slopes along an order-preserving additive map. -/
def map (f : Γ →+o Γ') : IntFiniteSlopeData Γ' where
  start := d.start
  initialHeight := f d.initialHeight
  length := d.length
  slope i := f (d.slope i)
  monotone := f.monotone'.comp d.monotone

@[simp]
theorem map_start (f : Γ →+o Γ') : (d.map f).start = d.start := (rfl)
@[simp]
theorem map_initialHeight (f : Γ →+o Γ') :
    (d.map f).initialHeight = f d.initialHeight := (rfl)
@[simp]
theorem map_length (f : Γ →+o Γ') : (d.map f).length = d.length := (rfl)
@[simp]
theorem map_slope (f : Γ →+o Γ') (i : Fin (d.map f).length) :
    (d.map f).slope i = f (d.slope (i.cast (d.map_length f))) := (rfl)

/-- Reading relative data commutes with an additive order-preserving map. -/
@[simp]
theorem toFiniteSlopeData_map (f : Γ →+o Γ') :
    (d.map f).toFiniteSlopeData = d.toFiniteSlopeData.map f := by
  refine FiniteSlopeData.ext_of_slope (by simp) (by simp) (by simp) ?_
  intro i
  simp

/-- Transporting the values commutes with constructing the represented heights. -/
@[simp]
theorem heights_map (f : Γ →+o Γ') (n : ℤ) :
    (d.map f).heights n = WithTop.map f (d.heights n) := by
  refine Function.extend_natCast_sub_induction d.toFiniteSlopeData.heights ⊤ d.start n
    (P := fun n y => (d.map f).heights n = WithTop.map f y) ?_ ?_
  · intro n hn
    rw [heights_eq_top_of_lt _ (by simpa using hn), WithTop.map_top]
  · intro k
    rw [← map_start d f, heights_start_add, toFiniteSlopeData_map,
      FiniteSlopeData.heights_map]

end AddCommMonoid

/-- Integer-anchored finite slope data is determined by its represented heights. -/
theorem heights_injective [AddCancelCommMonoid Γ] :
    Function.Injective (heights : IntFiniteSlopeData Γ → ℤ → WithTop Γ) := by
  intro d e hde
  have hdom (n : ℤ) := (d.heights_ne_top_iff (n := n)).symm.trans
    ((congrArg (fun h : ℤ → WithTop Γ => h n ≠ ⊤) hde).to_iff.trans e.heights_ne_top_iff)
  have hs : d.start = e.start := by
    have := (hdom d.start).mp ⟨le_rfl, by omega⟩
    have := (hdom e.start).mpr ⟨le_rfl, by omega⟩
    omega
  refine ext hs (FiniteSlopeData.heights_injective (funext fun n => ?_))
  rw [← heights_start_add, ← heights_start_add, ← hs, hde]

/-- Every finite unit edge has exactly the slope stored in the presentation. -/
theorem sub_heights_start_add (d : IntFiniteSlopeData ℝ) (i : Fin d.length) :
    (d.heights (d.start + i + 1)).untop₀ - (d.heights (d.start + i)).untop₀ = d.slope i := by
  have hi := d.toFiniteSlopeData.unitSlope_heights (i.cast d.toFiniteSlopeData_length.symm)
  rw [unitSlope_def] at hi
  simpa only [toFiniteSlopeData_start, zero_add, toFiniteSlopeData_slope,
    Fin.val_cast, Fin.cast_cast,
    Fin.cast_eq_self, ← heights_start_add, Nat.cast_add, Nat.cast_one, ← add_assoc] using hi

/-- The integer-anchored heights are convex. -/
theorem isIntConvexSeq_heights (d : IntFiniteSlopeData ℝ) : IsIntConvexSeq d.heights := by
  -- Extend the zero-anchored heights, then translate the index by the negative anchor.
  exact (isIntConvexSeq_extend_iff.mpr
    d.toFiniteSlopeData.isConvexSeq_heights).comp_add_right (-d.start)

/-- Extract finite slopes from a convex integer-indexed sequence on `[l,l+k]`. -/
noncomputable def ofIsIntConvexSeq {h : ℤ → WithTop ℝ} (hh : IsIntConvexSeq h)
    {l : ℤ} {k : ℕ}
    (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n ∧ n ≤ l + k) : IntFiniteSlopeData ℝ :=
  let d := FiniteSlopeData.ofIsConvexSeq (hh.isConvexSeq l)
    (l := 0) (k := k) (fun n => by simpa using hdom (l + n))
  { start := l
    initialHeight := d.initialHeight
    length := d.length
    slope := d.slope
    monotone := d.monotone }

variable {h : ℤ → WithTop ℝ} (hh : IsIntConvexSeq h) {l : ℤ} {k : ℕ}
  (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n ∧ n ≤ l + k)

@[simp]
theorem ofIsIntConvexSeq_start : (ofIsIntConvexSeq hh hdom).start = l := (rfl)
@[simp]
theorem ofIsIntConvexSeq_initialHeight :
    (ofIsIntConvexSeq hh hdom).initialHeight = (h l).untop₀ := by
  simp [ofIsIntConvexSeq]
@[simp]
theorem ofIsIntConvexSeq_length : (ofIsIntConvexSeq hh hdom).length = k := by
  simp [ofIsIntConvexSeq]

/-- The extracted slopes are the real differences on successive finite integer heights. -/
@[simp]
theorem ofIsIntConvexSeq_slope (i : Fin (ofIsIntConvexSeq hh hdom).length) :
    (ofIsIntConvexSeq hh hdom).slope i =
      (h (l + i + 1)).untop₀ - (h (l + i)).untop₀ := by
  -- Expose the finite index so the slope accessor can identify its dependent domain.
  rcases i with ⟨i, hi⟩
  dsimp only [ofIsIntConvexSeq]
  rw [FiniteSlopeData.ofIsConvexSeq_slope, unitSlope_def]
  simp [add_assoc]

private theorem toFiniteSlopeData_ofIsIntConvexSeq :
    (ofIsIntConvexSeq hh hdom).toFiniteSlopeData =
      FiniteSlopeData.ofIsConvexSeq (hh.isConvexSeq l)
        (l := 0) (k := k) (fun n => by simpa using hdom (l + n)) := by
  -- The extraction constructor copies the natural data. Its initial height and slopes,
  -- including the reindexed Fin arguments, therefore agree by unfolding the constructors.
  refine FiniteSlopeData.ext_of_slope (by simp) (by rfl) (by rfl) ?_
  intro i
  rfl

/-- Reconstructing extracted finite slope data recovers all integer heights. -/
@[simp]
theorem heights_ofIsIntConvexSeq : (ofIsIntConvexSeq hh hdom).heights = h := by
  funext n
  refine Function.extend_natCast_sub_induction
    (ofIsIntConvexSeq hh hdom).toFiniteSlopeData.heights ⊤ l n
    (P := fun n y => y = h n) ?_ ?_
  · intro n hn
    exact (not_ne_iff.mp ((hdom n).not.mpr (by omega))).symm
  · intro i
    simp only [toFiniteSlopeData_ofIsIntConvexSeq,
      FiniteSlopeData.heights_ofIsConvexSeq]

/-- Extracting the slopes of reconstructed heights recovers the finite presentation. -/
@[simp]
theorem ofIsIntConvexSeq_heights (d : IntFiniteSlopeData ℝ) :
    ofIsIntConvexSeq d.isIntConvexSeq_heights (fun _ => d.heights_ne_top_iff) = d :=
  heights_injective (heights_ofIsIntConvexSeq _ _)

end IntFiniteSlopeData

/-- A polygon with integer initial abscissa and a half-line as its finite domain,
represented by a nondecreasing sequence of unit slopes. -/
structure IntInfiniteSlopeData (Γ : Type*) [Preorder Γ] where
  /-- The first integer with finite height. -/
  start : ℤ
  /-- The height at the first point. -/
  initialHeight : Γ
  /-- The slopes of the unit edges, from left to right. -/
  slope : ℕ → Γ
  /-- Slopes are nondecreasing. -/
  monotone : Monotone slope

namespace IntInfiniteSlopeData

/-- Read the relative slope data at the natural-number anchor zero. -/
def toInfiniteSlopeData (d : IntInfiniteSlopeData Γ) : InfiniteSlopeData Γ where
  start := 0
  initialHeight := d.initialHeight
  slope := d.slope
  monotone := d.monotone

@[simp]
theorem toInfiniteSlopeData_start (d : IntInfiniteSlopeData Γ) :
    d.toInfiniteSlopeData.start = 0 := (rfl)
@[simp]
theorem toInfiniteSlopeData_initialHeight (d : IntInfiniteSlopeData Γ) :
    d.toInfiniteSlopeData.initialHeight = d.initialHeight := (rfl)
@[simp]
theorem toInfiniteSlopeData_slope (d : IntInfiniteSlopeData Γ) (i : ℕ) :
    d.toInfiniteSlopeData.slope i = d.slope i := (rfl)

/-- The integer anchor together with the relative natural-indexed data determines a presentation. -/
@[ext]
theorem ext {d e : IntInfiniteSlopeData Γ} (hs : d.start = e.start)
    (hd : d.toInfiniteSlopeData = e.toInfiniteSlopeData) : d = e := by
  cases d
  cases e
  cases hs
  cases hd
  rfl

/-- Translate the integer anchor, preserving the initial height and all relative slopes. -/
def translate (d : IntInfiniteSlopeData Γ) (k : ℤ) : IntInfiniteSlopeData Γ :=
  { d with start := d.start + k }

@[simp]
theorem translate_start (d : IntInfiniteSlopeData Γ) (k : ℤ) :
    (d.translate k).start = d.start + k := (rfl)

@[simp]
theorem translate_initialHeight (d : IntInfiniteSlopeData Γ) (k : ℤ) :
    (d.translate k).initialHeight = d.initialHeight := (rfl)
@[simp]
theorem translate_slope (d : IntInfiniteSlopeData Γ) (k : ℤ) (i : ℕ) :
    (d.translate k).slope i = d.slope i := (rfl)

/-- Anchor translation preserves the relative natural-indexed data. -/
@[simp]
theorem toInfiniteSlopeData_translate (d : IntInfiniteSlopeData Γ) (k : ℤ) :
    (d.translate k).toInfiniteSlopeData = d.toInfiniteSlopeData := (rfl)

section AddCommMonoid

variable [AddCommMonoid Γ] [AddCommMonoid Γ'] (d : IntInfiniteSlopeData Γ)

/-- Cumulative-sum heights on the finite domain, extended by infinity outside it. -/
noncomputable def heights (n : ℤ) : WithTop Γ :=
  Function.extend ((↑) : ℕ → ℤ) d.toInfiniteSlopeData.heights ⊤ (n - d.start)

/-- The defining extension-and-translation formula for the represented heights. -/
theorem heights_def (n : ℤ) : d.heights n =
    Function.extend ((↑) : ℕ → ℤ) d.toInfiniteSlopeData.heights ⊤ (n - d.start) := (rfl)

/-- Translating the anchor translates the represented integer heights. -/
@[simp]
theorem heights_translate (k n : ℤ) : (d.translate k).heights n = d.heights (n - k) := by
  simp only [heights_def, translate_start, toInfiniteSlopeData_translate, sub_add_eq_sub_sub,
    sub_right_comm]

/-- At an offset from the anchor, the heights agree with the natural-indexed construction. -/
@[simp]
theorem heights_start_add (n : ℕ) : d.heights (d.start + n) = d.toInfiniteSlopeData.heights n := by
  simp only [heights, add_sub_cancel_left, Nat.cast_injective.extend_apply]

/-- The heights are infinite strictly before the anchor. -/
theorem heights_eq_top_of_lt {n : ℤ} (hn : n < d.start) : d.heights n = ⊤ :=
  Function.extend_natCast_of_neg _ _ (sub_neg.mpr hn)

/-- The finite domain is exactly the half-line starting at the anchor. -/
theorem heights_ne_top_iff {n : ℤ} :
    d.heights n ≠ ⊤ ↔ d.start ≤ n := by
  refine Function.extend_natCast_sub_induction d.toInfiniteSlopeData.heights ⊤ d.start n
    (P := fun n y => y ≠ ⊤ ↔ d.start ≤ n) ?_ ?_
  · intro n hn
    simp [not_le.mpr hn]
  · intro k
    rw [InfiniteSlopeData.heights_ne_top_iff]
    simp

/-- The finite domain of the represented integer heights. -/
theorem setOf_heights_ne_top :
    {n | d.heights n ≠ ⊤} = Set.Ici d.start :=
  Set.ext fun _ => d.heights_ne_top_iff

/-- The represented heights are infinite precisely outside the finite domain. -/
@[simp]
theorem heights_eq_top_iff {n : ℤ} :
    d.heights n = ⊤ ↔ n < d.start := by
  rw [← not_iff_not, ← ne_eq, heights_ne_top_iff]
  omega

/-- The height at the anchor is the initial height. -/
@[simp]
theorem heights_start : d.heights d.start = (d.initialHeight : WithTop Γ) := by
  calc d.heights d.start = d.toInfiniteSlopeData.heights d.toInfiniteSlopeData.start := by
         simpa using d.heights_start_add 0
       _ = (d.initialHeight : WithTop Γ) := d.toInfiniteSlopeData.heights_start

/-- Transport the heights and slopes along an order-preserving additive map. -/
def map (f : Γ →+o Γ') : IntInfiniteSlopeData Γ' where
  start := d.start
  initialHeight := f d.initialHeight
  slope i := f (d.slope i)
  monotone := f.monotone'.comp d.monotone

@[simp]
theorem map_start (f : Γ →+o Γ') : (d.map f).start = d.start := (rfl)
@[simp]
theorem map_initialHeight (f : Γ →+o Γ') :
    (d.map f).initialHeight = f d.initialHeight := (rfl)
@[simp]
theorem map_slope (f : Γ →+o Γ') (i : ℕ) :
    (d.map f).slope i = f (d.slope i) := (rfl)

/-- Reading relative data commutes with an additive order-preserving map. -/
@[simp]
theorem toInfiniteSlopeData_map (f : Γ →+o Γ') :
    (d.map f).toInfiniteSlopeData = d.toInfiniteSlopeData.map f := by
  ext <;> simp

/-- Transporting the values commutes with constructing the represented heights. -/
@[simp]
theorem heights_map (f : Γ →+o Γ') (n : ℤ) :
    (d.map f).heights n = WithTop.map f (d.heights n) := by
  refine Function.extend_natCast_sub_induction d.toInfiniteSlopeData.heights ⊤ d.start n
    (P := fun n y => (d.map f).heights n = WithTop.map f y) ?_ ?_
  · intro n hn
    rw [heights_eq_top_of_lt _ (by simpa using hn), WithTop.map_top]
  · intro k
    rw [← map_start d f, heights_start_add, toInfiniteSlopeData_map,
      InfiniteSlopeData.heights_map]

end AddCommMonoid

/-- Integer-anchored infinite slope data is determined by its represented heights. -/
theorem heights_injective [AddCancelCommMonoid Γ] :
    Function.Injective (heights : IntInfiniteSlopeData Γ → ℤ → WithTop Γ) := by
  intro d e hde
  have hdom (n : ℤ) := (d.heights_ne_top_iff (n := n)).symm.trans
    ((congrArg (fun h : ℤ → WithTop Γ => h n ≠ ⊤) hde).to_iff.trans e.heights_ne_top_iff)
  have hs : d.start = e.start := by
    have := (hdom d.start).mp le_rfl
    have := (hdom e.start).mpr le_rfl
    omega
  refine ext hs (InfiniteSlopeData.heights_injective (funext fun n => ?_))
  rw [← heights_start_add, ← heights_start_add, ← hs, hde]

/-- Every unit edge has exactly the slope stored in the presentation. -/
theorem sub_heights_start_add (d : IntInfiniteSlopeData ℝ) (i : ℕ) :
    (d.heights (d.start + i + 1)).untop₀ - (d.heights (d.start + i)).untop₀ = d.slope i := by
  have hi := d.toInfiniteSlopeData.unitSlope_heights i
  rw [unitSlope_def] at hi
  simpa only [toInfiniteSlopeData_start, zero_add, toInfiniteSlopeData_slope, ← heights_start_add,
    Nat.cast_add, Nat.cast_one, ← add_assoc] using hi

/-- The integer-anchored heights are convex. -/
theorem isIntConvexSeq_heights (d : IntInfiniteSlopeData ℝ) : IsIntConvexSeq d.heights := by
  -- Extend the zero-anchored heights, then translate the index by the negative anchor.
  exact (isIntConvexSeq_extend_iff.mpr
    d.toInfiniteSlopeData.isConvexSeq_heights).comp_add_right (-d.start)

/-- Extract unit slopes from a convex integer-indexed sequence on `[l,∞)`. -/
noncomputable def ofIsIntConvexSeq {h : ℤ → WithTop ℝ} (hh : IsIntConvexSeq h) {l : ℤ}
    (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n) : IntInfiniteSlopeData ℝ :=
  let d := InfiniteSlopeData.ofIsConvexSeq (hh.isConvexSeq l)
    (l := 0) (fun n => by simpa using hdom (l + n))
  { start := l
    initialHeight := d.initialHeight
    slope := d.slope
    monotone := d.monotone }

variable {h : ℤ → WithTop ℝ} (hh : IsIntConvexSeq h) {l : ℤ}
  (hdom : ∀ n, h n ≠ ⊤ ↔ l ≤ n)

@[simp]
theorem ofIsIntConvexSeq_start : (ofIsIntConvexSeq hh hdom).start = l := (rfl)
@[simp]
theorem ofIsIntConvexSeq_initialHeight :
    (ofIsIntConvexSeq hh hdom).initialHeight = (h l).untop₀ := by
  simp [ofIsIntConvexSeq]

/-- The extracted slopes are the real differences on successive finite integer heights. -/
@[simp]
theorem ofIsIntConvexSeq_slope (i : ℕ) :
    (ofIsIntConvexSeq hh hdom).slope i =
      (h (l + i + 1)).untop₀ - (h (l + i)).untop₀ := by
  simp [ofIsIntConvexSeq, InfiniteSlopeData.ofIsConvexSeq_slope, unitSlope_def, add_assoc]

private theorem toInfiniteSlopeData_ofIsIntConvexSeq :
    (ofIsIntConvexSeq hh hdom).toInfiniteSlopeData =
      InfiniteSlopeData.ofIsConvexSeq (hh.isConvexSeq l)
        (l := 0) (fun n => by simpa using hdom (l + n)) := by
  ext <;> simp [toInfiniteSlopeData, ofIsIntConvexSeq]

/-- Reconstructing extracted infinite slope data recovers all integer heights. -/
@[simp]
theorem heights_ofIsIntConvexSeq : (ofIsIntConvexSeq hh hdom).heights = h := by
  funext n
  refine Function.extend_natCast_sub_induction
    (ofIsIntConvexSeq hh hdom).toInfiniteSlopeData.heights ⊤ l n
    (P := fun n y => y = h n) ?_ ?_
  · intro n hn
    exact (not_ne_iff.mp ((hdom n).not.mpr (by omega))).symm
  · intro i
    simp only [toInfiniteSlopeData_ofIsIntConvexSeq,
      InfiniteSlopeData.heights_ofIsConvexSeq]

/-- Extracting the slopes of reconstructed heights recovers the infinite presentation. -/
@[simp]
theorem ofIsIntConvexSeq_heights (d : IntInfiniteSlopeData ℝ) :
    ofIsIntConvexSeq d.isIntConvexSeq_heights (fun _ => d.heights_ne_top_iff) = d :=
  heights_injective (heights_ofIsIntConvexSeq _ _)

end IntInfiniteSlopeData

namespace IntFiniteSlopeData

/-- A real integer-indexed sequence has a finite slope presentation exactly when it is
convex with nonempty finite domain. -/
theorem exists_heights_eq_iff {h : ℤ → WithTop ℝ} :
    (∃ d : IntFiniteSlopeData ℝ, d.heights = h) ↔
      IsIntConvexSeq h ∧ {n | h n ≠ ⊤}.Nonempty ∧ {n | h n ≠ ⊤}.Finite := by
  constructor
  · rintro ⟨d, rfl⟩
    rw [d.setOf_heights_ne_top]
    exact ⟨d.isIntConvexSeq_heights, Set.nonempty_Icc.mpr (by omega), Set.finite_Icc _ _⟩
  · rintro ⟨hh, hne, hfin⟩
    have hset := (hne.ordConnected_iff_of_bdd hfin.bddBelow hfin.bddAbove).mp hh.ordConnected
    obtain ⟨n, hn⟩ := hne
    obtain ⟨hlo, hhi⟩ := Set.ext_iff.mp hset n |>.mp hn
    have hlen : sInf {n | h n ≠ ⊤} +
        (((sSup {n | h n ≠ ⊤} - sInf {n | h n ≠ ⊤}).toNat : ℕ) : ℤ) =
          sSup {n | h n ≠ ⊤} := by omega
    have hdom (n : ℤ) : h n ≠ ⊤ ↔
        sInf {n | h n ≠ ⊤} ≤ n ∧ n ≤ sInf {n | h n ≠ ⊤} +
        (((sSup {n | h n ≠ ⊤} - sInf {n | h n ≠ ⊤}).toNat : ℕ) : ℤ) := by
      rw [hlen]
      exact Set.ext_iff.mp hset n
    exact ⟨ofIsIntConvexSeq hh hdom, heights_ofIsIntConvexSeq hh hdom⟩

/-- A represented finite polygon is fixed by the integer lower convex envelope. -/
@[simp]
theorem intLowerConvexEnvelope_heights (d : IntFiniteSlopeData ℝ) :
    intLowerConvexEnvelope d.heights = d.heights :=
  d.isIntConvexSeq_heights.intLowerConvexEnvelope_eq

end IntFiniteSlopeData

namespace IntInfiniteSlopeData

/-- A real integer-indexed sequence has an infinite one-sided slope presentation exactly
when it is convex and its finite domain is infinite and bounded below. -/
theorem exists_heights_eq_iff {h : ℤ → WithTop ℝ} :
    (∃ d : IntInfiniteSlopeData ℝ, d.heights = h) ↔
      IsIntConvexSeq h ∧ {n | h n ≠ ⊤}.Infinite ∧ BddBelow {n | h n ≠ ⊤} := by
  constructor
  · rintro ⟨d, rfl⟩
    rw [d.setOf_heights_ne_top]
    exact ⟨d.isIntConvexSeq_heights, Set.Ici_infinite _, bddBelow_Ici⟩
  · rintro ⟨hh, hinf, hbdd⟩
    have hfirst := Int.csInf_mem hinf.nonempty hbdd
    have hunbounded : ¬BddAbove {n | h n ≠ ⊤} :=
      fun hb => hinf (hbdd.finite_of_bddAbove hb)
    have hdom (n : ℤ) : h n ≠ ⊤ ↔ sInf {n | h n ≠ ⊤} ≤ n := by
      refine ⟨fun hn => csInf_le hbdd hn, fun hn => ?_⟩
      obtain ⟨m, hm, hnm⟩ := not_bddAbove_iff.mp hunbounded n
      exact hh.ordConnected.out hfirst hm ⟨hn, hnm.le⟩
    exact ⟨ofIsIntConvexSeq hh hdom, heights_ofIsIntConvexSeq hh hdom⟩

/-- A represented half-line polygon is fixed by the integer lower convex envelope. -/
@[simp]
theorem intLowerConvexEnvelope_heights (d : IntInfiniteSlopeData ℝ) :
    intLowerConvexEnvelope d.heights = d.heights :=
  d.isIntConvexSeq_heights.intLowerConvexEnvelope_eq

end IntInfiniteSlopeData

namespace FiniteSlopeData

/-- Preserve a natural-anchored presentation while viewing its anchor as an integer. -/
def toInt (d : FiniteSlopeData Γ) : IntFiniteSlopeData Γ where
  start := d.start
  initialHeight := d.initialHeight
  length := d.length
  slope := d.slope
  monotone := d.monotone

@[simp]
theorem toInt_start (d : FiniteSlopeData Γ) : d.toInt.start = (d.start : ℤ) := (rfl)
@[simp]
theorem toInt_initialHeight (d : FiniteSlopeData Γ) :
    d.toInt.initialHeight = d.initialHeight := (rfl)
@[simp]
theorem toInt_length (d : FiniteSlopeData Γ) : d.toInt.length = d.length := (rfl)
@[simp]
theorem toInt_slope (d : FiniteSlopeData Γ) (i : Fin d.toInt.length) :
    d.toInt.slope i = d.slope (i.cast d.toInt_length) := (rfl)

/-- Reading relative data after casting the anchor resets the natural anchor to zero. -/
@[simp]
theorem toFiniteSlopeData_toInt (d : FiniteSlopeData Γ) :
    d.toInt.toFiniteSlopeData = { d with start := 0 } := (rfl)

/-- Casting the anchor commutes with an additive order-preserving map. -/
@[simp]
theorem toInt_map [AddCommMonoid Γ] [AddCommMonoid Γ'] (d : FiniteSlopeData Γ)
    (f : Γ →+o Γ') : (d.map f).toInt = d.toInt.map f := by
  refine IntFiniteSlopeData.ext (by simp) ?_
  simp only [IntFiniteSlopeData.toFiniteSlopeData_map, toFiniteSlopeData_toInt]
  refine ext_of_slope (by simp) (by simp) (by simp) ?_
  intro i
  simp

/-- Casting the anchor extends the original natural-indexed heights by infinity. -/
theorem heights_toInt [AddCommMonoid Γ] (d : FiniteSlopeData Γ) :
    d.toInt.heights = Function.extend ((↑) : ℕ → ℤ) d.heights ⊤ := by
  have htail : d.toInt.toFiniteSlopeData.heights = fun k => d.heights (d.start + k) := by
    funext k
    simp [toFiniteSlopeData_toInt, FiniteSlopeData.heights_def]
  funext n
  rw [IntFiniteSlopeData.heights_def, toInt_start, htail]
  exact Function.extend_natCast_sub_natCast d.heights ⊤ d.start
    (fun k hk => d.heights_eq_top_iff.mpr (Or.inl hk)) n

end FiniteSlopeData

namespace InfiniteSlopeData

/-- Preserve a natural-anchored presentation while viewing its anchor as an integer. -/
def toInt (d : InfiniteSlopeData Γ) : IntInfiniteSlopeData Γ where
  start := d.start
  initialHeight := d.initialHeight
  slope := d.slope
  monotone := d.monotone

@[simp]
theorem toInt_start (d : InfiniteSlopeData Γ) : d.toInt.start = (d.start : ℤ) := (rfl)
@[simp]
theorem toInt_initialHeight (d : InfiniteSlopeData Γ) :
    d.toInt.initialHeight = d.initialHeight := (rfl)
@[simp]
theorem toInt_slope (d : InfiniteSlopeData Γ) (i : ℕ) :
    d.toInt.slope i = d.slope i := (rfl)

/-- Reading relative data after casting the anchor resets the natural anchor to zero. -/
@[simp]
theorem toInfiniteSlopeData_toInt (d : InfiniteSlopeData Γ) :
    d.toInt.toInfiniteSlopeData = { d with start := 0 } := (rfl)

/-- Casting the anchor commutes with an additive order-preserving map. -/
@[simp]
theorem toInt_map [AddCommMonoid Γ] [AddCommMonoid Γ'] (d : InfiniteSlopeData Γ)
    (f : Γ →+o Γ') : (d.map f).toInt = d.toInt.map f := by
  refine IntInfiniteSlopeData.ext (by simp) ?_
  simp only [IntInfiniteSlopeData.toInfiniteSlopeData_map, toInfiniteSlopeData_toInt]
  ext <;> simp

/-- Casting the anchor extends the original natural-indexed heights by infinity. -/
theorem heights_toInt [AddCommMonoid Γ] (d : InfiniteSlopeData Γ) :
    d.toInt.heights = Function.extend ((↑) : ℕ → ℤ) d.heights ⊤ := by
  have htail : d.toInt.toInfiniteSlopeData.heights = fun k => d.heights (d.start + k) := by
    funext k
    simp [toInfiniteSlopeData_toInt, InfiniteSlopeData.heights_def]
  funext n
  rw [IntInfiniteSlopeData.heights_def, toInt_start, htail]
  exact Function.extend_natCast_sub_natCast d.heights ⊤ d.start
    (fun k hk => d.heights_eq_top_iff.mpr hk) n

end InfiniteSlopeData

end TauCeti
