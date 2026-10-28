/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Bounds.Image
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import TauCeti.Analysis.Convex.Sequence.Basic

/-!
# Lower convex envelopes of height sequences

Suprema of convex height sequences are convex, so every height sequence `a` with a
real affine lower bound has a greatest convex minorant, its lower convex envelope.
Newton polygons are the lower convex envelopes of coefficient valuations; this file
contains the construction-independent geometry, with no coefficient data.

The predicate `IsLowerConvexEnvelope a h` says that `h` is convex, lies below `a`, and
dominates every convex minorant of `a`. It determines `h` uniquely, and it is satisfied
by some `h` exactly when `a` is admissible. The total function `lowerConvexEnvelope a`
is the pointwise supremum of the convex minorants when `a` is admissible, and the
all-infinite sequence otherwise. That fallback is not an envelope of the inadmissible
input: geometric conclusions about `lowerConvexEnvelope a` assume `IsAdmissible a`.

## Main results

* `IsConvexSeq.of_isLUB`: a least upper bound of a family of convex height sequences
  is convex; `IsConvexSeq.sup` and `IsConvexSeq.iSup` are the binary and
  indexed cases.
* `isLowerConvexEnvelope_lowerConvexEnvelope`: an admissible sequence has
  `lowerConvexEnvelope a` as its lower convex envelope.
* `exists_isLowerConvexEnvelope_iff`: a lower convex envelope exists exactly for
  admissible sequences.
* `le_lowerConvexEnvelope_iff`: a convex sequence lies below the envelope of `a` exactly
  when it lies below `a`.
* `lowerConvexEnvelope_mono` and `lowerConvexEnvelope_idem`: the envelope is monotone
  on admissible inputs and idempotent.
* `lowerConvexEnvelope_ne_top_iff`: the finite domain of an admissible envelope is the
  integer convex hull of the finite indices of the sequence.
* `lowerConvexEnvelope_eq_of_forall_lt` and `lowerConvexEnvelope_eq_of_forall_gt`: the
  envelope passes through the first point and, when there is one, the last point.
* `lowerConvexEnvelope_add_affine`: adding a real affine function to the sequence adds it
  to the envelope; `lowerConvexEnvelope_const_add` allows an infinite constant, and
  `lowerConvexEnvelope_add_nsmul` states the shear by a finite slope.
* `lowerConvexEnvelope_shift`: shifting the sequence to the right, with infinite heights
  at the vacated indices, shifts the envelope in the same way.
* `lowerConvexEnvelope_reflect`: reflecting points that are infinite beyond `N` in the index
  `N` reflects their envelope in the same way.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

namespace TauCeti

/-! ### Suprema of convex height sequences -/

namespace IsConvexSeq

/-- A least upper bound of a family of convex height sequences is convex. The empty
family has no least upper bound, since height sequences have no least element. -/
theorem of_isLUB {S : Set (ℕ → WithTop ℝ)} {h : ℕ → WithTop ℝ}
    (hS : ∀ g ∈ S, IsConvexSeq g) (hh : IsLUB S h) : IsConvexSeq h := by
  have hp := isLUB_pi.mp hh
  have hle : ∀ g ∈ S, g ≤ h := fun g hg => hh.1 hg
  refine isConvexSeq_iff_two_mul_le.mpr ⟨⟨fun i hi k hk j hj => ?_⟩, fun n hn hn₂ => ?_⟩
  · -- Every member of the family is bounded at `j` by its larger outer height.
    have hbound : h j ≤ max (h i) (h k) := by
      refine (hp j).2 ?_
      rintro _ ⟨g, hg, rfl⟩
      exact ((hS g hg).le_max hj.1 hj.2).trans (max_le_max (hle g hg i) (hle g hg k))
    exact ne_top_of_le_ne_top (max_ne_top hi hk) hbound
  · -- Every member satisfies the second-difference bound by the outer heights of `h`.
    set x := (h n).untop₀
    set z := (h (n + 2)).untop₀
    have hbound : h (n + 1) ≤ (((x + z) / 2 : ℝ) : WithTop ℝ) := by
      refine (hp (n + 1)).2 ?_
      rintro _ ⟨g, hg, rfl⟩
      have hgn : g n ≠ ⊤ := ne_top_of_le_ne_top hn (hle g hg n)
      have hgn₂ : g (n + 2) ≠ ⊤ := ne_top_of_le_ne_top hn₂ (hle g hg (n + 2))
      have hgn₁ : g (n + 1) ≠ ⊤ :=
        (hS g hg).ne_top_of_le_of_le hgn hgn₂ (by omega) (by omega)
      have hmid := (isConvexSeq_iff_two_mul_le.mp (hS g hg)).2 n hgn hgn₂
      have hx := WithTop.untop₀_le_untop₀ hn (hle g hg n)
      have hz := WithTop.untop₀_le_untop₀ hn₂ (hle g hg (n + 2))
      rw [Function.eval_apply, ← WithTop.coe_untop₀_of_ne_top hgn₁, WithTop.coe_le_coe]
      linarith
    have hn₁ : h (n + 1) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hbound
    rw [← WithTop.coe_untop₀_of_ne_top hn₁, WithTop.coe_le_coe] at hbound
    linarith

/-- The pointwise maximum of two convex height sequences is convex. -/
theorem sup {g h : ℕ → WithTop ℝ} (hg : IsConvexSeq g) (hh : IsConvexSeq h) :
    IsConvexSeq (g ⊔ h) :=
  of_isLUB (by simp [hg, hh]) isLUB_pair

/-- The pointwise supremum of a nonempty family of convex height sequences is convex. -/
theorem iSup {ι : Sort*} [Nonempty ι] {g : ι → ℕ → WithTop ℝ}
    (hg : ∀ i, IsConvexSeq (g i)) : IsConvexSeq fun n => ⨆ i, g i n := by
  refine of_isLUB (Set.forall_mem_range.mpr hg) (isLUB_pi.mpr fun n => ?_)
  rw [← Set.range_comp]
  exact WithTop.isLUB_sSup' (Set.range_nonempty _)

end IsConvexSeq

/-! ### Lower convex envelopes -/

/-- `h` is the lower convex envelope of `a`: it is a convex minorant of `a` that
dominates every convex minorant of `a`. -/
structure IsLowerConvexEnvelope (a h : ℕ → WithTop ℝ) : Prop where
  /-- The envelope is convex. -/
  isConvexSeq : IsConvexSeq h
  /-- The envelope lies below the point heights. -/
  le : h ≤ a
  /-- The envelope dominates every convex minorant. -/
  greatest : ∀ ⦃g : ℕ → WithTop ℝ⦄, IsConvexSeq g → g ≤ a → g ≤ h

/-- Being the lower convex envelope means being the greatest convex minorant. -/
theorem isLowerConvexEnvelope_iff_isGreatest {a h : ℕ → WithTop ℝ} :
    IsLowerConvexEnvelope a h ↔ IsGreatest {g | IsConvexSeq g ∧ g ≤ a} h :=
  ⟨fun hh => ⟨⟨hh.isConvexSeq, hh.le⟩, fun _ hg => hh.greatest hg.1 hg.2⟩,
    fun hh => ⟨hh.1.1, hh.1.2, fun _ hg hga => hh.2 ⟨hg, hga⟩⟩⟩

namespace IsLowerConvexEnvelope

variable {a h g : ℕ → WithTop ℝ}

/-- The lower convex envelope is unique. -/
theorem unique (hh : IsLowerConvexEnvelope a h) (hg : IsLowerConvexEnvelope a g) :
    h = g :=
  (isLowerConvexEnvelope_iff_isGreatest.mp hh).unique
    (isLowerConvexEnvelope_iff_isGreatest.mp hg)

/-- A sequence with a lower convex envelope is admissible. -/
theorem isAdmissible (hh : IsLowerConvexEnvelope a h) : IsAdmissible a :=
  exists_convexSeq_le_iff.mp ⟨h, hh.isConvexSeq, hh.le⟩

/-- A convex sequence is its own lower convex envelope. -/
theorem of_isConvexSeq (hh : IsConvexSeq h) : IsLowerConvexEnvelope h h :=
  ⟨hh, le_rfl, fun _ _ hgh => hgh⟩

end IsLowerConvexEnvelope

open scoped Classical in
/-- The lower convex envelope of a height sequence, as a total function. For an admissible
sequence it is the pointwise supremum of all convex minorants. For an inadmissible
sequence it is the all-infinite fallback, which is not an envelope of that sequence. -/
noncomputable def lowerConvexEnvelope (a : ℕ → WithTop ℝ) : ℕ → WithTop ℝ :=
  if IsAdmissible a then fun n => ⨆ g : {g : ℕ → WithTop ℝ // IsConvexSeq g ∧ g ≤ a}, g.1 n
  else ⊤

variable {a b h : ℕ → WithTop ℝ}

/-- For an admissible sequence, each envelope height is the least upper bound of the
heights of the convex minorants there. -/
theorem isLUB_lowerConvexEnvelope (ha : IsAdmissible a) (n : ℕ) :
    IsLUB ((fun g : ℕ → WithTop ℝ => g n) '' {g | IsConvexSeq g ∧ g ≤ a})
      (lowerConvexEnvelope a n) := by
  obtain ⟨g₀, hg₀⟩ := exists_convexSeq_le_iff.mpr ha
  have : Nonempty {g : ℕ → WithTop ℝ // IsConvexSeq g ∧ g ≤ a} := ⟨⟨g₀, hg₀⟩⟩
  rw [lowerConvexEnvelope, ite_eq_left ha, Set.image_eq_range]
  exact WithTop.isLUB_sSup' (Set.range_nonempty _)

/-- The envelope of an inadmissible sequence is the all-infinite fallback. -/
theorem lowerConvexEnvelope_of_not_isAdmissible (ha : ¬IsAdmissible a) :
    lowerConvexEnvelope a = ⊤ := by
  rw [lowerConvexEnvelope, ite_eq_right ha]

/-- An admissible sequence has `lowerConvexEnvelope a` as its lower convex envelope. -/
theorem isLowerConvexEnvelope_lowerConvexEnvelope (ha : IsAdmissible a) :
    IsLowerConvexEnvelope a (lowerConvexEnvelope a) := by
  have hlub : IsLUB {g : ℕ → WithTop ℝ | IsConvexSeq g ∧ g ≤ a} (lowerConvexEnvelope a) :=
    isLUB_pi.mpr (isLUB_lowerConvexEnvelope ha)
  exact ⟨IsConvexSeq.of_isLUB (S := {g | IsConvexSeq g ∧ g ≤ a}) (fun g hg => hg.1) hlub,
    hlub.2 fun g hg => hg.2,
    fun g hg hga => hlub.1 ⟨hg, hga⟩⟩

/-- A lower convex envelope exists exactly for admissible sequences. -/
theorem exists_isLowerConvexEnvelope_iff :
    (∃ h, IsLowerConvexEnvelope a h) ↔ IsAdmissible a :=
  ⟨fun ⟨_, hh⟩ => hh.isAdmissible, fun ha => ⟨_, isLowerConvexEnvelope_lowerConvexEnvelope ha⟩⟩

/-- Any lower convex envelope of `a` is the total function `lowerConvexEnvelope a`. -/
theorem IsLowerConvexEnvelope.eq_lowerConvexEnvelope (hh : IsLowerConvexEnvelope a h) :
    h = lowerConvexEnvelope a :=
  hh.unique (isLowerConvexEnvelope_lowerConvexEnvelope hh.isAdmissible)

/-- For an admissible sequence, being its lower convex envelope is equality with
`lowerConvexEnvelope a`. -/
theorem isLowerConvexEnvelope_iff_eq (ha : IsAdmissible a) :
    IsLowerConvexEnvelope a h ↔ h = lowerConvexEnvelope a :=
  ⟨IsLowerConvexEnvelope.eq_lowerConvexEnvelope,
    fun hh => hh ▸ isLowerConvexEnvelope_lowerConvexEnvelope ha⟩

/-- The total envelope is convex, including the all-infinite fallback. -/
theorem isConvexSeq_lowerConvexEnvelope (a : ℕ → WithTop ℝ) :
    IsConvexSeq (lowerConvexEnvelope a) := by
  by_cases ha : IsAdmissible a
  · exact (isLowerConvexEnvelope_lowerConvexEnvelope ha).isConvexSeq
  · rw [lowerConvexEnvelope_of_not_isAdmissible ha]
    exact isConvexSeq_top

/-- The envelope of an admissible sequence lies below it. -/
theorem lowerConvexEnvelope_le (ha : IsAdmissible a) : lowerConvexEnvelope a ≤ a :=
  (isLowerConvexEnvelope_lowerConvexEnvelope ha).le

/-- A convex minorant lies below the envelope. Admissibility is automatic. -/
theorem le_lowerConvexEnvelope (hh : IsConvexSeq h) (hha : h ≤ a) :
    h ≤ lowerConvexEnvelope a :=
  (isLowerConvexEnvelope_lowerConvexEnvelope (hh.isAdmissible.mono hha)).greatest hh hha

/-- For an admissible sequence `a`, a convex sequence lies below the envelope of `a`
exactly when it lies below `a`. -/
theorem le_lowerConvexEnvelope_iff (ha : IsAdmissible a) (hh : IsConvexSeq h) :
    h ≤ lowerConvexEnvelope a ↔ h ≤ a :=
  ⟨fun hle => hle.trans (lowerConvexEnvelope_le ha), le_lowerConvexEnvelope hh⟩

/-- A convex sequence is its own lower convex envelope. -/
theorem IsConvexSeq.lowerConvexEnvelope_eq (hh : IsConvexSeq h) :
    lowerConvexEnvelope h = h :=
  ((IsLowerConvexEnvelope.of_isConvexSeq hh).eq_lowerConvexEnvelope).symm

/-- The envelope of the empty point set is the empty polygon. -/
@[simp]
theorem lowerConvexEnvelope_top : lowerConvexEnvelope (⊤ : ℕ → WithTop ℝ) = ⊤ :=
  isConvexSeq_top.lowerConvexEnvelope_eq

/-- Taking the lower convex envelope is idempotent. -/
@[simp]
theorem lowerConvexEnvelope_idem (a : ℕ → WithTop ℝ) :
    lowerConvexEnvelope (lowerConvexEnvelope a) = lowerConvexEnvelope a :=
  (isConvexSeq_lowerConvexEnvelope a).lowerConvexEnvelope_eq

/-- The envelope is monotone on admissible inputs: a lower admissible bound `b ≤ a`, not
necessarily convex, has envelope below that of `a`. -/
theorem lowerConvexEnvelope_mono (hb : IsAdmissible b) (hba : b ≤ a) :
    lowerConvexEnvelope b ≤ lowerConvexEnvelope a :=
  le_lowerConvexEnvelope (isConvexSeq_lowerConvexEnvelope b)
    ((lowerConvexEnvelope_le hb).trans hba)

/-! ### Finite domain and endpoints -/

/-- If `a` is infinite off an order-connected set `s`, the envelope is infinite off `s`
as well. -/
private theorem lowerConvexEnvelope_eq_top_of_notMem {s : Set ℕ} (hs : s.OrdConnected)
    (hoff : ∀ k ∉ s, a k = ⊤) {n : ℕ} (hn : n ∉ s) : lowerConvexEnvelope a n = ⊤ := by
  by_cases ha : IsAdmissible a
  · obtain ⟨c, m, hcm⟩ := isAdmissible_iff.mp ha
    classical
    have hg := le_lowerConvexEnvelope (a := a) (isConvexSeq_affine_ite hs c m) fun k => ?_
    · simpa [hn] using hg n
    by_cases hk : k ∈ s
    · simpa [hk] using hcm k
    · simp [hk, hoff k hk]
  · simp [lowerConvexEnvelope_of_not_isAdmissible ha]

/-- The envelope is infinite at `n` if every point at or before `n` is infinite. -/
theorem lowerConvexEnvelope_eq_top_of_forall_le {n : ℕ} (hn : ∀ i ≤ n, a i = ⊤) :
    lowerConvexEnvelope a n = ⊤ :=
  lowerConvexEnvelope_eq_top_of_notMem Set.ordConnected_Ioi
    (fun k hk => hn k (not_lt.mp hk)) (lt_irrefl n)

/-- The envelope is infinite at `n` if every point at or after `n` is infinite. -/
theorem lowerConvexEnvelope_eq_top_of_forall_ge {n : ℕ} (hn : ∀ k, n ≤ k → a k = ⊤) :
    lowerConvexEnvelope a n = ⊤ :=
  lowerConvexEnvelope_eq_top_of_notMem Set.ordConnected_Iio
    (fun k hk => hn k (not_lt.mp hk)) (lt_irrefl n)

/-- For an admissible sequence, the finite domain of the envelope is the integer convex
hull of the finite domain of the sequence. -/
theorem lowerConvexEnvelope_ne_top_iff (ha : IsAdmissible a) {n : ℕ} :
    lowerConvexEnvelope a n ≠ ⊤ ↔ ∃ i ≤ n, ∃ k, n ≤ k ∧ a i ≠ ⊤ ∧ a k ≠ ⊤ := by
  constructor
  · intro hn
    by_contra hcon
    push Not at hcon
    by_cases hi : ∃ i ≤ n, a i ≠ ⊤
    · obtain ⟨i, hin, hi⟩ := hi
      exact hn (lowerConvexEnvelope_eq_top_of_forall_ge fun k hk => hcon i hin k hk hi)
    · push Not at hi
      exact hn (lowerConvexEnvelope_eq_top_of_forall_le hi)
  · rintro ⟨i, hin, k, hnk, hi, hk⟩
    have hle := lowerConvexEnvelope_le ha
    exact (isConvexSeq_lowerConvexEnvelope a).ne_top_of_le_of_le
      (ne_top_of_le_ne_top hi (hle i)) (ne_top_of_le_ne_top hk (hle k)) hin hnk

/-- If an affine line through `(p, a p)` lies below `a` on an order-connected set `s`
containing `p`, and `a` is infinite off `s`, then the envelope agrees with `a` at `p`. -/
private theorem lowerConvexEnvelope_eq_of_affine_le {s : Set ℕ} (hs : s.OrdConnected)
    {p : ℕ} (hps : p ∈ s) (hoff : ∀ n ∉ s, a n = ⊤) {c m : ℝ}
    (hline : ∀ n ∈ s, ((c + m * n : ℝ) : WithTop ℝ) ≤ a n)
    (hp : a p = ((c + m * p : ℝ) : WithTop ℝ)) : lowerConvexEnvelope a p = a p := by
  classical
  have hga : (fun n => if n ∈ s then ((c + m * n : ℝ) : WithTop ℝ) else ⊤) ≤ a := by
    intro n
    by_cases hn : n ∈ s
    · simpa [hn] using hline n hn
    · simp [hn, hoff n hn]
  have hcv := isConvexSeq_affine_ite hs c m
  refine le_antisymm (lowerConvexEnvelope_le (hcv.isAdmissible.mono hga) p) ?_
  simpa [hps, hp] using le_lowerConvexEnvelope hcv hga p

/-- An admissible envelope passes through the first point of the sequence: if every point
before `p` is infinite, the envelope agrees with the sequence at `p`. -/
theorem lowerConvexEnvelope_eq_of_forall_lt (ha : IsAdmissible a) {p : ℕ}
    (hp : ∀ n < p, a n = ⊤) : lowerConvexEnvelope a p = a p := by
  by_cases hap : a p = ⊤
  · rw [hap]
    exact lowerConvexEnvelope_eq_top_of_forall_le fun i hi =>
      (eq_or_lt_of_le hi).elim (fun h => h ▸ hap) (hp i)
  obtain ⟨c, m, hcm⟩ := isAdmissible_iff.mp ha
  set y := (a p).untop₀
  have hy : a p = y := (WithTop.coe_untop₀_of_ne_top hap).symm
  have hδ : c + m * p ≤ y := by
    have := hcm p
    rwa [hy, WithTop.coe_le_coe] at this
  -- Steepen the affine minorant downwards so that it passes through `(p, y)`.
  set m' := m + (c + m * p - y)
  refine lowerConvexEnvelope_eq_of_affine_le (Set.ordConnected_Ici (a := p))
    (Set.mem_Ici.mpr le_rfl) (fun n hn => hp n (not_le.mp hn)) (c := y - m' * p) (m := m')
    (fun k hk => ?_)
    (by rw [hy, sub_add_cancel])
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hk) with rfl | hpk
  · rw [hy, WithTop.coe_le_coe]
    linarith
  · refine le_trans ?_ (hcm k)
    rw [WithTop.coe_le_coe]
    have hk' : (p : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hpk
    nlinarith

/-- The envelope passes through the last point of the sequence, when there is one: if
every point after `p` is infinite, the envelope agrees with the sequence at `p`. Such a
sequence has only finitely many finite points, so it is automatically admissible. -/
theorem lowerConvexEnvelope_eq_of_forall_gt {p : ℕ}
    (hp : ∀ n, p < n → a n = ⊤) : lowerConvexEnvelope a p = a p := by
  by_cases hap : a p = ⊤
  · rw [hap]
    exact lowerConvexEnvelope_eq_top_of_forall_ge fun k hk =>
      (eq_or_lt_of_le hk).elim (fun h => h ▸ hap) (hp k)
  obtain ⟨c, m, hcm⟩ := isAdmissible_iff.mp (isAdmissible_of_forall_gt hp)
  set y := (a p).untop₀
  have hy : a p = y := (WithTop.coe_untop₀_of_ne_top hap).symm
  have hδ : c + m * p ≤ y := by
    have := hcm p
    rwa [hy, WithTop.coe_le_coe] at this
  -- Steepen the affine minorant upwards so that it passes through `(p, y)`.
  set m' := m + (y - (c + m * p))
  refine lowerConvexEnvelope_eq_of_affine_le (Set.ordConnected_Iic (a := p))
    (Set.mem_Iic.mpr le_rfl) (fun n hn => hp n (not_le.mp hn)) (c := y - m' * p) (m := m')
    (fun k hk => ?_)
    (by rw [hy, sub_add_cancel])
  rcases eq_or_lt_of_le (Set.mem_Iic.mp hk) with rfl | hkp
  · rw [hy, WithTop.coe_le_coe]
    linarith
  · refine le_trans ?_ (hcm k)
    rw [WithTop.coe_le_coe]
    have hk' : (k : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt hkp
    nlinarith

/-! ### Affine covariance -/

/-- Adding a real affine function to the points adds it to their lower convex envelope. -/
theorem IsLowerConvexEnvelope.add_affine (hh : IsLowerConvexEnvelope a h) (c m : ℝ) :
    IsLowerConvexEnvelope (fun n => a n + ((c + m * n : ℝ) : WithTop ℝ))
      (fun n => h n + ((c + m * n : ℝ) : WithTop ℝ)) := by
  refine ⟨hh.isConvexSeq.add_affine c m, fun n => add_le_add_left (hh.le n) _,
    fun g hg hga n => ?_⟩
  -- Subtract the affine function from `g` to obtain a convex minorant of `a`.
  have hg' : (fun n => g n + ((-c + -m * n : ℝ) : WithTop ℝ)) ≤ a := fun k =>
    (add_le_add_left (hga k) _).trans_eq ((a k).add_affine_add_neg_affine c m k)
  have hle := add_le_add_left (hh.greatest (hg.add_affine (-c) (-m)) hg' n)
    ((c + m * n : ℝ) : WithTop ℝ)
  have hcancel :
      g n + ((-c + -m * n : ℝ) : WithTop ℝ) + ((c + m * n : ℝ) : WithTop ℝ) = g n := by
    simpa only [neg_neg] using (g n).add_affine_add_neg_affine (-c) (-m) n
  rwa [hcancel] at hle

/-- Adding a real affine function to a sequence adds it to the envelope. This holds for
inadmissible sequences too, where both sides are the all-infinite fallback. With `m = 0`
it is a height translation; with `c = 0` it is a shear. -/
theorem lowerConvexEnvelope_add_affine (a : ℕ → WithTop ℝ) (c m : ℝ) :
    lowerConvexEnvelope (fun n => a n + ((c + m * n : ℝ) : WithTop ℝ)) =
      fun n => lowerConvexEnvelope a n + ((c + m * n : ℝ) : WithTop ℝ) := by
  by_cases ha : IsAdmissible a
  · exact ((isLowerConvexEnvelope_lowerConvexEnvelope ha).add_affine c m
      |>.eq_lowerConvexEnvelope).symm
  · rw [lowerConvexEnvelope_of_not_isAdmissible ha, lowerConvexEnvelope_of_not_isAdmissible
      (by simpa using ha)]
    funext n
    simp

/-- Adding a constant height, possibly infinite, to a sequence adds it to the envelope. An
infinite constant gives the empty polygon on both sides. -/
theorem lowerConvexEnvelope_const_add (t : WithTop ℝ) (a : ℕ → WithTop ℝ) :
    lowerConvexEnvelope (fun n => t + a n) = fun n => t + lowerConvexEnvelope a n := by
  induction t with
  | top =>
    simp only [top_add]
    exact lowerConvexEnvelope_top
  | coe r =>
    simpa [add_comm] using lowerConvexEnvelope_add_affine a r 0

/-- Adding the shear `n ↦ n • t` of a finite slope `t` to a sequence adds it to the envelope.
The finiteness hypothesis is needed: `n • ⊤` is `0` at `n = 0` and `⊤` elsewhere, which is
not affine. -/
theorem lowerConvexEnvelope_add_nsmul (a : ℕ → WithTop ℝ) {t : WithTop ℝ} (ht : t ≠ ⊤) :
    lowerConvexEnvelope (fun n => a n + n • t) = fun n => lowerConvexEnvelope a n + n • t := by
  lift t to ℝ using ht with m
  have key (n : ℕ) : n • (m : WithTop ℝ) = ((0 + m * n : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_nsmul, nsmul_eq_mul, zero_add, mul_comm]
  simp only [key]
  exact lowerConvexEnvelope_add_affine a 0 m

/-! ### Translation of indices -/

/-- Shifting the points `k` places to the right, with infinite heights at the first `k`
indices, shifts their lower convex envelope in the same way. -/
theorem IsLowerConvexEnvelope.shift (hh : IsLowerConvexEnvelope a h) (k : ℕ) :
    IsLowerConvexEnvelope (fun n => if k ≤ n then a (n - k) else ⊤)
      (fun n => if k ≤ n then h (n - k) else ⊤) := by
  refine ⟨hh.isConvexSeq.shift k, fun n => ?_, fun g hg hga n => ?_⟩
  · dsimp only
    split_ifs
    exacts [hh.le _, le_rfl]
  · -- Dropping the first `k` heights of `g` gives a convex minorant of `a`.
    have hle := hh.greatest (hg.comp_add_right k) fun m => by simpa using hga (m + k)
    dsimp only
    split_ifs with hkn
    · simpa [Nat.sub_add_cancel hkn] using hle (n - k)
    · exact le_top

/-- Shifting a sequence `k` places to the right, with infinite heights at the first `k`
indices, shifts its lower convex envelope in the same way. This holds for inadmissible
sequences too, where both sides are the all-infinite fallback. -/
theorem lowerConvexEnvelope_shift (a : ℕ → WithTop ℝ) (k : ℕ) :
    lowerConvexEnvelope (fun n => if k ≤ n then a (n - k) else ⊤) =
      fun n => if k ≤ n then lowerConvexEnvelope a (n - k) else ⊤ := by
  by_cases ha : IsAdmissible a
  · exact ((isLowerConvexEnvelope_lowerConvexEnvelope ha).shift k
      |>.eq_lowerConvexEnvelope).symm
  · rw [lowerConvexEnvelope_of_not_isAdmissible ha, lowerConvexEnvelope_of_not_isAdmissible
      (by rwa [isAdmissible_shift_iff])]
    funext n
    simp


/-! ### Reflection of indices -/

/-- Reflecting points in `N`, when they are infinite beyond `N`, reflects their lower convex
envelope in the same way. The hypothesis is needed, since reflection discards the points beyond
`N`, which may affect the envelope on `[0, N]`. -/
theorem IsLowerConvexEnvelope.reflect (hh : IsLowerConvexEnvelope a h) {N : ℕ}
    (ha : ∀ n, N < n → a n = ⊤) :
    IsLowerConvexEnvelope (fun n => if n ≤ N then a (N - n) else ⊤)
      (fun n => if n ≤ N then h (N - n) else ⊤) := by
  refine ⟨hh.isConvexSeq.reflect N, fun n => ?_, fun g hg hga n => ?_⟩
  · dsimp only
    split_ifs
    exacts [hh.le _, le_rfl]
  · -- Reflecting `g` back gives a convex minorant of `a`.
    have hle := hh.greatest (hg.reflect N) fun m => by
      dsimp only
      split_ifs with hm
      · simpa [Nat.sub_sub_self hm] using hga (N - m)
      · simp [ha m (by omega)]
    dsimp only
    split_ifs with hn
    · simpa [Nat.sub_sub_self hn] using hle (N - n)
    · exact le_top

/-- Reflecting points in `N`, when they are infinite beyond `N`, reflects their lower convex
envelope in the same way. -/
theorem lowerConvexEnvelope_reflect {N : ℕ} (ha : ∀ n, N < n → a n = ⊤) :
    lowerConvexEnvelope (fun n => if n ≤ N then a (N - n) else ⊤) =
      fun n => if n ≤ N then lowerConvexEnvelope a (N - n) else ⊤ :=
  ((isLowerConvexEnvelope_lowerConvexEnvelope (isAdmissible_of_forall_gt ha)).reflect ha
    |>.eq_lowerConvexEnvelope).symm

end TauCeti
