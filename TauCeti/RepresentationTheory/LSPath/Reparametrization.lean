/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.PLPath
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Algebra.GroupWithZero.Units.Basic
import TauCeti.Algebra.Order.Group.MinMax

/-!
# Parametrized piecewise-linear paths and reparametrization

`TauCeti.PLPath 𝕜 V` models piecewise-linear paths up to reparametrization by reduced segment
lists. This file compares that model with parametrized paths, that is with functions `𝕜 → V`.

A *timed presentation* is a list of pairs `(d, v)` of a positive duration `d` and a segment `v`.
Its parametrized path `TauCeti.PLPath.evalTimed p` starts at `0` at time `0` and runs along the
segments in order, along `v` at constant velocity `d⁻¹ • v` during a time interval of length `d`;
it is constant before time `0` and after the total duration `TauCeti.PLPath.duration p`. A timed
presentation `φ` in `𝕜` with nonnegative segments presents a nondecreasing piecewise-linear map
from `[0, duration φ]` onto `[0, s]`, where `s` is the sum of its segments. So `p` is a
*reparametrization* of `q` (`TauCeti.PLPath.IsReparam p q`) when
`evalTimed p = evalTimed q ∘ evalTimed φ` for such a `φ` running from `[0, duration p]` onto
`[0, duration q]`; for presentations of duration `1` these are Littelmann's nondecreasing
surjective piecewise-linear reparametrizations of `[0, 1]`.

The main result is that the segment-list model is faithful: two timed presentations of positive
duration present the same `TauCeti.PLPath` exactly when they are reparametrizations of a common
timed presentation, which may be chosen of any prescribed positive duration. All constructions
use only the field operations of `𝕜`, so over `ℚ` every subdivision time and every
reparametrization stays rational.

## Main definitions

* `TauCeti.PLPath.duration`, `TauCeti.PLPath.IsTimed`: the total duration of a list of
  `(duration, segment)` pairs, and the condition that every duration is positive.
* `TauCeti.PLPath.evalTimed`: the parametrized path of a timed presentation.
* `TauCeti.PLPath.timedComp`: a timed presentation of the composite of two parametrized paths.
* `TauCeti.PLPath.IsReparam`: one timed presentation is a reparametrization of another.

## Main results

* `TauCeti.PLPath.evalTimed_duration`: the parametrized path ends at the endpoint of the path it
  presents.
* `TauCeti.PLPath.evalTimed_append`: the parametrized path of a concatenation runs through the
  first presentation and then, shifted by its duration, through the second.
* `TauCeti.PLPath.monotone_evalTimed`, `TauCeti.PLPath.exists_evalTimed_eq`: a timed presentation
  in `𝕜` with nonnegative segments is nondecreasing, and maps `[0, duration φ]` onto
  `[0, s]`, where `s` is the sum of its segments.
* `TauCeti.PLPath.evalTimed_timedComp`: `timedComp` presents the composite.
* `TauCeti.PLPath.ofSegments_map_snd_eq_of_evalTimed_eq`: two timed presentations with the same
  parametrized path present the same `TauCeti.PLPath`.
* `TauCeti.PLPath.IsReparam.trans`, `TauCeti.PLPath.IsReparam.ofSegments_map_snd_eq`:
  reparametrization is transitive and does not change the presented `TauCeti.PLPath`.
* `TauCeti.PLPath.IsReparam.append`: reparametrization is compatible with concatenation.
* `TauCeti.PLPath.ofSegments_map_snd_eq_iff_exists_isReparam`: two timed presentations of positive
  duration present the same `TauCeti.PLPath` exactly when they are reparametrizations of a common
  timed presentation.

## References

* P. Littelmann, *A Littlewood-Richardson rule for symmetrizable Kac-Moody algebras*, Invent.
  Math. 116 (1994), §1.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §1.
-/

public section

namespace TauCeti

universe u v

namespace PLPath

variable {𝕜 : Type u} {V : Type v}

/-! ### Timed presentations and their parametrized paths -/

section Duration

variable [AddMonoid 𝕜]

/-- The total duration of a list of `(duration, segment)` pairs. -/
def duration (p : List (𝕜 × V)) : 𝕜 :=
  (p.map Prod.fst).sum

theorem duration_def (p : List (𝕜 × V)) : duration p = (p.map Prod.fst).sum :=
  (rfl)

@[simp]
theorem duration_nil : duration ([] : List (𝕜 × V)) = 0 :=
  (rfl)

@[simp]
theorem duration_cons (x : 𝕜 × V) (p : List (𝕜 × V)) :
    duration (x :: p) = x.1 + duration p :=
  List.sum_cons

@[simp]
theorem duration_append (p q : List (𝕜 × V)) : duration (p ++ q) = duration p + duration q := by
  rw [duration_def, duration_def, duration_def, List.map_append, List.sum_append]

end Duration

section IsTimed

variable [Zero 𝕜] [LT 𝕜] {p : List (𝕜 × V)}

/-- A list of `(duration, segment)` pairs is a *timed presentation* when every duration is
positive. -/
def IsTimed (p : List (𝕜 × V)) : Prop :=
  ∀ x ∈ p, 0 < x.1

/-- The characterization of timed presentations, for use outside this file. -/
theorem isTimed_iff : IsTimed p ↔ ∀ x ∈ p, 0 < x.1 :=
  Iff.rfl

@[simp]
theorem isTimed_nil : IsTimed ([] : List (𝕜 × V)) :=
  fun _ h ↦ absurd h List.not_mem_nil

@[simp]
theorem isTimed_cons {x : 𝕜 × V} : IsTimed (x :: p) ↔ 0 < x.1 ∧ IsTimed p :=
  List.forall_mem_cons

end IsTimed

theorem IsTimed.nonneg [Zero 𝕜] [Preorder 𝕜] {p : List (𝕜 × V)} (hp : IsTimed p) :
    ∀ x ∈ p, 0 ≤ x.1 :=
  fun x hx ↦ (hp x hx).le

/-- A timed presentation with nonnegative segments has nonnegative durations and segments. -/
theorem IsTimed.and_nonneg {W : Type*} [Zero 𝕜] [Preorder 𝕜] [Zero W] [LE W]
    {p : List (𝕜 × W)} (hp : IsTimed p) (hp' : ∀ x ∈ p, 0 ≤ x.2) : ∀ x ∈ p, 0 ≤ x.1 ∧ 0 ≤ x.2 :=
  fun x hx ↦ ⟨(hp x hx).le, hp' x hx⟩

section Eval

variable [Field 𝕜] [LinearOrder 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The parametrized path of a list of `(duration, segment)` pairs. At time `t` the first pair
`(d, v)` contributes `(max 0 (min t d) / d) • v`, and the remaining pairs are run from time `d` on.
For a timed presentation (`TauCeti.PLPath.IsTimed p`, every duration positive) this starts at `0`
at time `0` and runs along each segment `v` in turn at constant velocity, during a time interval of
length the duration `d` of `v`. -/
def evalTimed : List (𝕜 × V) → 𝕜 → V
  | [], _ => 0
  | (d, v) :: p, t => (max 0 (min t d) / d) • v + evalTimed p (t - d)

@[simp]
theorem evalTimed_nil (t : 𝕜) : evalTimed ([] : List (𝕜 × V)) t = 0 :=
  (rfl)

@[simp]
theorem evalTimed_cons (d : 𝕜) (v : V) (p : List (𝕜 × V)) (t : 𝕜) :
    evalTimed ((d, v) :: p) t = (max 0 (min t d) / d) • v + evalTimed p (t - d) :=
  (rfl)

/-- The parametrized path of a concatenation runs through the first presentation and then, from
its total duration on, through the second. -/
theorem evalTimed_append (p q : List (𝕜 × V)) (t : 𝕜) :
    evalTimed (p ++ q) t = evalTimed p t + evalTimed q (t - duration p) := by
  induction p generalizing t with
  | nil => simp
  | cons x p ih =>
    obtain ⟨d, v⟩ := x
    rw [List.cons_append, evalTimed_cons, evalTimed_cons, ih, duration_cons, sub_sub, add_assoc]

/-- Stationary segments do not move the parametrized path. -/
theorem evalTimed_eq_zero_of_forall {p : List (𝕜 × V)} (h : ∀ x ∈ p, x.2 = 0) (t : 𝕜) :
    evalTimed p t = 0 := by
  induction p generalizing t with
  | nil => rfl
  | cons x p ih =>
    obtain ⟨d, v⟩ := x
    simp only [List.forall_mem_cons] at h
    rw [evalTimed_cons, h.1, smul_zero, zero_add, ih h.2]

end Eval

section DurationOrder

variable [AddCommMonoid 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] {p : List (𝕜 × V)}

theorem duration_nonneg (hp : ∀ x ∈ p, 0 ≤ x.1) : 0 ≤ duration p :=
  List.sum_nonneg (by simpa using fun d v h ↦ hp (d, v) h)

theorem IsTimed.duration_pos (hp : IsTimed p) (hne : p ≠ []) : 0 < duration p :=
  List.sum_pos _ (List.forall_mem_map.2 hp) (by simpa using hne)

/-- A timed presentation of nonpositive duration is empty. -/
theorem IsTimed.eq_nil_of_duration_nonpos (hp : IsTimed p) (h : duration p ≤ 0) : p = [] := by
  by_contra hne
  exact (hp.duration_pos hne).not_ge h

end DurationOrder

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {p q r : List (𝕜 × V)} {d e t : 𝕜}

variable [AddCommGroup V] [Module 𝕜 V] {v w : V}

omit [IsStrictOrderedRing 𝕜] in
/-- Up to time `0`, the first segment has not been started. -/
theorem evalTimed_cons_of_nonpos (ht : t ≤ 0) :
    evalTimed ((d, v) :: p) t = evalTimed p (t - d) := by
  rw [evalTimed_cons, max_eq_left ((min_le_left t d).trans ht), zero_div, zero_smul, zero_add]

omit [IsStrictOrderedRing 𝕜] in
/-- From time `d` on, the first segment, of duration `d`, has been run entirely. -/
theorem evalTimed_cons_of_le (hd : 0 < d) (ht : d ≤ t) :
    evalTimed ((d, v) :: p) t = v + evalTimed p (t - d) := by
  rw [evalTimed_cons, min_eq_right ht, max_eq_right hd.le, div_self hd.ne', one_smul]

/-- The parametrized path is `0` up to time `0`. -/
theorem evalTimed_of_nonpos (hp : ∀ x ∈ p, 0 ≤ x.1) (ht : t ≤ 0) : evalTimed p t = 0 := by
  induction p generalizing t with
  | nil => rfl
  | cons x p ih =>
    obtain ⟨d, v⟩ := x
    simp only [List.forall_mem_cons] at hp
    rw [evalTimed_cons_of_nonpos ht, ih hp.2 (by linarith [hp.1])]

@[simp]
theorem evalTimed_zero (hp : ∀ x ∈ p, 0 ≤ x.1) : evalTimed p 0 = 0 :=
  evalTimed_of_nonpos hp le_rfl

/-- The parametrized path is constant at the sum of the segments after the total duration. -/
theorem evalTimed_of_duration_le (hp : IsTimed p) (ht : duration p ≤ t) :
    evalTimed p t = (p.map Prod.snd).sum := by
  induction p generalizing t with
  | nil => rfl
  | cons x p ih =>
    obtain ⟨d, v⟩ := x
    rw [isTimed_cons] at hp
    have hdur := duration_nonneg hp.2.nonneg
    simp only [duration_cons] at ht
    rw [evalTimed_cons_of_le hp.1 (by linarith), ih hp.2 (by linarith), List.map_cons,
      List.sum_cons]

/-- The parametrized path of a timed presentation ends, at its total duration, at the endpoint of
the path it presents. -/
theorem evalTimed_duration (hp : IsTimed p) :
    evalTimed p (duration p) = (ofSegments 𝕜 (p.map Prod.snd)).endpoint := by
  rw [evalTimed_of_duration_le hp le_rfl, endpoint_ofSegments]

/-- After the first segment, the parametrized path of the remaining segments is that of the whole
presentation, shifted back by the first duration and translated back by the first segment. -/
theorem evalTimed_eq_evalTimed_cons_add_sub (hd : 0 < d) {s : 𝕜} (hs : 0 ≤ s) :
    evalTimed p s = evalTimed ((d, v) :: p) (s + d) - v := by
  rw [evalTimed_cons_of_le hd (by linarith), add_sub_cancel_right, add_sub_cancel_left]

/-! ### Subdividing a segment -/

/-- Subdividing a segment of duration `D = d₁ + d₂` into its pieces of durations `d₁` and `d₂`
does not change the parametrized path. The durations `d₁` and `d₂` may vanish. -/
theorem evalTimed_cons_eq_evalTimed_cons_cons {d₁ d₂ D : 𝕜} {v₁ v₂ : V} (h₁ : 0 ≤ d₁)
    (h₂ : 0 ≤ d₂) (hD : d₁ + d₂ = D) (hv₁ : v₁ = (d₁ / D) • v) (hv₂ : v₂ = (d₂ / D) • v)
    (p : List (𝕜 × V)) (t : 𝕜) :
    evalTimed ((D, v) :: p) t = evalTimed ((d₁, v₁) :: (d₂, v₂) :: p) t := by
  subst hD hv₁ hv₂
  have hcancel (s d : 𝕜) : max 0 (min s d) / d * (d / (d₁ + d₂)) = max 0 (min s d) / (d₁ + d₂) :=
    div_mul_div_cancel_of_imp fun hd ↦ by simp [hd]
  simp only [evalTimed_cons, smul_smul, hcancel, max_zero_min_add h₁ h₂, sub_sub]
  module

/-- Subdividing a segment `w` of duration `e` at the time `d`, for `0 ≤ d ≤ e`, into its pieces
`(d / e) • w` of duration `d` and `((e - d) / e) • w` of duration `e - d` does not change the
parametrized path. -/
theorem evalTimed_cons_eq_evalTimed_cons_cons_sub (hd : 0 ≤ d) (hde : d ≤ e) (w : V)
    (p : List (𝕜 × V)) (t : 𝕜) :
    evalTimed ((e, w) :: p) t = evalTimed ((d, (d / e) • w) :: (e - d, ((e - d) / e) • w) :: p) t :=
  evalTimed_cons_eq_evalTimed_cons_cons hd (sub_nonneg.2 hde) (add_sub_cancel d e) rfl rfl p t

/-! ### Timed presentations in `𝕜` -/

/-- A timed presentation in `𝕜` with nonnegative segments has a nonnegative parametrized path. -/
theorem evalTimed_nonneg {φ : List (𝕜 × 𝕜)} (hφ : ∀ x ∈ φ, 0 ≤ x.1 ∧ 0 ≤ x.2) (t : 𝕜) :
    0 ≤ evalTimed φ t := by
  induction φ generalizing t with
  | nil => exact le_rfl
  | cons x φ ih =>
    obtain ⟨d, a⟩ := x
    simp only [List.forall_mem_cons] at hφ
    rw [evalTimed_cons, smul_eq_mul]
    exact add_nonneg (mul_nonneg (div_nonneg (le_max_left _ _) hφ.1.1) hφ.1.2) (ih hφ.2 _)

/-- A timed presentation in `𝕜` with nonnegative segments has a nondecreasing parametrized
path. -/
theorem monotone_evalTimed {φ : List (𝕜 × 𝕜)} (hφ : ∀ x ∈ φ, 0 ≤ x.1 ∧ 0 ≤ x.2) :
    Monotone (evalTimed φ) := by
  induction φ with
  | nil => exact monotone_const
  | cons x φ ih =>
    obtain ⟨d, a⟩ := x
    simp only [List.forall_mem_cons] at hφ
    intro s t hst
    simp only [evalTimed_cons, smul_eq_mul]
    gcongr
    · exact hφ.1.2
    · exact hφ.1.1
    · exact ih hφ.2 (by linarith)

/-- A timed presentation `φ` in `𝕜` with nonnegative segments maps `[0, duration φ]` onto
`[0, s]`, where `s` is the sum of its segments. -/
theorem exists_evalTimed_eq {φ : List (𝕜 × 𝕜)} (hφ : IsTimed φ) (hφ' : ∀ x ∈ φ, 0 ≤ x.2)
    {u : 𝕜} (hu₀ : 0 ≤ u) (hu : u ≤ (φ.map Prod.snd).sum) :
    ∃ t, 0 ≤ t ∧ t ≤ duration φ ∧ evalTimed φ t = u := by
  induction φ generalizing u with
  | nil => exact ⟨0, le_rfl, le_rfl, by simpa using (hu.antisymm hu₀).symm⟩
  | cons x φ ih =>
    obtain ⟨d, a⟩ := x
    obtain ⟨hd, hφ⟩ := isTimed_cons.1 hφ
    obtain ⟨ha, hφ'⟩ := List.forall_mem_cons.1 hφ'
    dsimp only at hd ha
    simp only [List.map_cons, List.sum_cons] at hu
    have hdur := duration_nonneg hφ.nonneg
    rcases le_or_gt u a with hua | hau
    · rcases ha.lt_or_eq with ha | ha
      · have hle : u * d / a ≤ d := by
          rw [div_le_iff₀ ha]
          nlinarith
        have hnn : 0 ≤ u * d / a := div_nonneg (mul_nonneg hu₀ hd.le) ha.le
        refine ⟨u * d / a, hnn, by simp only [duration_cons]; linarith, ?_⟩
        rw [evalTimed_cons, min_eq_left hle, max_eq_right hnn,
          evalTimed_of_nonpos hφ.nonneg (by linarith), add_zero, smul_eq_mul]
        field_simp
      · refine ⟨0, le_rfl, by simp only [duration_cons]; linarith, ?_⟩
        rw [evalTimed_zero (isTimed_cons.2 ⟨(hd : 0 < (d, a).1), hφ⟩).nonneg]
        linarith
    · obtain ⟨t, ht₀, ht, htu⟩ := ih hφ hφ' (u := u - a) (by linarith) (by linarith)
      refine ⟨t + d, by linarith, by simp only [duration_cons]; linarith, ?_⟩
      rw [evalTimed_cons_of_le hd (by linarith), add_sub_cancel_right, htu, add_sub_cancel]

/-! ### Composing with a reparametrization -/

/-- Prepending a segment `v`, run during time `d` on the source side and during time `d'` on the
target side, to a factorization `evalTimed p = evalTimed q ∘ evalTimed φ` gives a factorization
through the timing `(d, d') :: φ`. A zero target duration `d'` requires a stationary segment. -/
theorem evalTimed_cons_comp {d' : 𝕜} {φ : List (𝕜 × 𝕜)} (hd : 0 < d) (hd' : 0 ≤ d')
    (hv : d' = 0 → v = 0) (hφ : ∀ x ∈ φ, 0 ≤ x.1 ∧ 0 ≤ x.2) (hq : ∀ x ∈ q, 0 ≤ x.1)
    (h : ∀ t, evalTimed p t = evalTimed q (evalTimed φ t)) (t : 𝕜) :
    evalTimed ((d, v) :: p) t = evalTimed ((d', v) :: q) (evalTimed ((d, d') :: φ) t) := by
  have hφ₁ : ∀ x ∈ φ, 0 ≤ x.1 := fun x hx ↦ (hφ x hx).1
  rcases le_total t d with htd | hdt
  · -- Before time `d`, both sides run along `v`, and the rest of the path has not started.
    rw [evalTimed_cons, evalTimed_cons, evalTimed_cons, h, smul_eq_mul]
    set c := max 0 (min t d) / d
    have h₀ : 0 ≤ c := div_nonneg (le_max_left _ _) hd.le
    have h₁ : c ≤ 1 := div_le_one_of_le₀ (max_le hd.le (min_le_right _ _)) hd.le
    rw [evalTimed_of_nonpos hφ₁ (by linarith), add_zero, evalTimed_zero hq,
      evalTimed_of_nonpos hq (by nlinarith), min_eq_left (by nlinarith),
      max_eq_right (mul_nonneg h₀ hd')]
    rcases eq_or_ne d' 0 with rfl | hd'0
    · simp [hv rfl]
    · rw [mul_div_cancel_right₀ _ hd'0]
  · -- After time `d`, both sides have run along all of `v`.
    have hs := evalTimed_nonneg hφ (t - d)
    rw [evalTimed_cons_of_le hd hdt, evalTimed_cons_of_le hd hdt, h]
    rcases hd'.lt_or_eq with hd'0 | rfl
    · rw [evalTimed_cons_of_le hd'0 (by linarith), add_sub_cancel_left]
    · simp [hv rfl]

/-! ### Reparametrization -/

/-- `p` is a *reparametrization* of `q`: there is a timed presentation `φ` in `𝕜` with
nonnegative segments, of duration `duration p` and with segments summing to `duration q`, such
that `evalTimed p = evalTimed q ∘ evalTimed φ`. By `TauCeti.PLPath.monotone_evalTimed` and
`TauCeti.PLPath.exists_evalTimed_eq`, `evalTimed φ` is a nondecreasing piecewise-linear map from
`[0, duration p]` onto `[0, duration q]`; outside `[0, duration p]` both sides of the
factorization are constant. -/
def IsReparam (p q : List (𝕜 × V)) : Prop :=
  ∃ φ : List (𝕜 × 𝕜), IsTimed φ ∧ (∀ x ∈ φ, 0 ≤ x.2) ∧ duration φ = duration p ∧
    (φ.map Prod.snd).sum = duration q ∧ ∀ t, evalTimed p t = evalTimed q (evalTimed φ t)

omit [IsStrictOrderedRing 𝕜] in
/-- The characterization of reparametrizations by their timings, for use outside this file. -/
theorem isReparam_iff : IsReparam p q ↔
    ∃ φ : List (𝕜 × 𝕜), IsTimed φ ∧ (∀ x ∈ φ, 0 ≤ x.2) ∧ duration φ = duration p ∧
      (φ.map Prod.snd).sum = duration q ∧ ∀ t, evalTimed p t = evalTimed q (evalTimed φ t) :=
  Iff.rfl

/-- Two timed presentations with the same segments are reparametrizations of each other. -/
theorem isReparam_of_map_snd_eq (hp : IsTimed p) (hq : IsTimed q)
    (h : p.map Prod.snd = q.map Prod.snd) : IsReparam p q := by
  induction p generalizing q with
  | nil =>
    obtain rfl : q = [] := List.map_eq_nil_iff.1 h.symm
    exact ⟨[], isTimed_nil, by simp, rfl, rfl, fun _ ↦ rfl⟩
  | cons x p ih =>
    obtain ⟨d, v⟩ := x
    obtain ⟨⟨e, w⟩, q, rfl⟩ := List.exists_cons_of_ne_nil (show q ≠ [] by rintro rfl; simp at h)
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨hd, hp⟩ := isTimed_cons.1 hp
    obtain ⟨he, hq⟩ := isTimed_cons.1 hq
    obtain ⟨φ, hφ, hφ', hφp, hφq, hφe⟩ := ih hp hq h
    refine ⟨(d, e) :: φ, isTimed_cons.2 ⟨hd, hφ⟩, List.forall_mem_cons.2 ⟨he.le, hφ'⟩,
      by simp [hφp], by simp [hφq], ?_⟩
    · exact evalTimed_cons_comp hd he.le (fun h ↦ absurd h he.ne')
        (hφ.and_nonneg hφ') hq.nonneg hφe

/-- A timed presentation is a reparametrization of itself, through the identity timing. -/
theorem IsReparam.refl (hp : IsTimed p) : IsReparam p p :=
  isReparam_of_map_snd_eq hp hp rfl

/-- Prepending the same segment, run during the same time, preserves reparametrization. -/
theorem IsReparam.cons (h : IsReparam p q) (hd : 0 < d) (hq : ∀ x ∈ q, 0 ≤ x.1) (v : V) :
    IsReparam ((d, v) :: p) ((d, v) :: q) := by
  obtain ⟨φ, hφ, hφ', hφp, hφq, hφe⟩ := h
  refine ⟨(d, d) :: φ, isTimed_cons.2 ⟨hd, hφ⟩, List.forall_mem_cons.2 ⟨hd.le, hφ'⟩,
    by simp [hφp], by simp [hφq], ?_⟩
  exact evalTimed_cons_comp hd hd.le (fun h ↦ absurd h hd.ne')
    (hφ.and_nonneg hφ') hq hφe

/-- Concatenating reparametrizations is a reparametrization: the timings concatenate. -/
theorem IsReparam.append {p₁ p₂ q₁ q₂ : List (𝕜 × V)} (h₁ : IsReparam p₁ q₁)
    (h₂ : IsReparam p₂ q₂) (hq₁ : IsTimed q₁) (hq₂ : ∀ x ∈ q₂, 0 ≤ x.1) :
    IsReparam (p₁ ++ p₂) (q₁ ++ q₂) := by
  obtain ⟨φ₁, hφ₁, hφ₁', hφ₁p, hφ₁q, hφ₁e⟩ := h₁
  obtain ⟨φ₂, hφ₂, hφ₂', hφ₂p, hφ₂q, hφ₂e⟩ := h₂
  refine ⟨φ₁ ++ φ₂, fun x hx ↦ (List.mem_append.1 hx).elim (hφ₁ x) (hφ₂ x),
    fun x hx ↦ (List.mem_append.1 hx).elim (hφ₁' x) (hφ₂' x), by simp [hφ₁p, hφ₂p],
    by simp [hφ₁q, hφ₂q], fun t ↦ ?_⟩
  rw [evalTimed_append, evalTimed_append, evalTimed_append, hφ₁e, hφ₂e, hφ₁p]
  rcases le_total t (duration p₁) with ht | ht
  · -- Up to the end of `p₁`, the timing stays within `q₁`, and `p₂` has not started.
    have hs : evalTimed φ₁ t ≤ duration q₁ := by
      rw [← hφ₁q, ← evalTimed_of_duration_le hφ₁ le_rfl]
      exact monotone_evalTimed (hφ₁.and_nonneg hφ₁') (ht.trans hφ₁p.ge)
    rw [evalTimed_of_nonpos hφ₂.nonneg (sub_nonpos.2 ht), evalTimed_zero hq₂, add_zero,
      add_zero, evalTimed_of_nonpos hq₂ (sub_nonpos.2 hs), add_zero]
  · -- After the end of `p₁`, the timing has run through all of `q₁`.
    have hs := evalTimed_nonneg (hφ₂.and_nonneg hφ₂') (t - duration p₁)
    rw [evalTimed_of_duration_le hφ₁ (hφ₁p.trans_le ht), hφ₁q, add_sub_cancel_left,
      evalTimed_of_duration_le hq₁ le_rfl, evalTimed_of_duration_le hq₁ (le_add_of_nonneg_right hs)]

/-- Merging two adjacent segments pointing in the same direction, run during the sum of their
durations, is a reparametrization. -/
theorem isReparam_cons_cons_add (hd : 0 < d) (he : 0 < e) (hvw : SameRay 𝕜 v w)
    (hr : IsTimed r) : IsReparam ((d, v) :: (e, w) :: r) ((d + e, v + w) :: r) := by
  obtain ⟨a, b, ha, hb, hab, hva, hwb⟩ := hvw.exists_eq_smul_add
  have hde : 0 < d + e := add_pos hd he
  have hsplit (t : 𝕜) : evalTimed ((d + e, v + w) :: r) t =
      evalTimed ((a * (d + e), v) :: (b * (d + e), w) :: r) t :=
    evalTimed_cons_eq_evalTimed_cons_cons (mul_nonneg ha hde.le) (mul_nonneg hb hde.le)
      (by rw [← add_mul, hab, one_mul]) (by rwa [mul_div_cancel_right₀ _ hde.ne'])
      (by rwa [mul_div_cancel_right₀ _ hde.ne']) r t
  obtain ⟨ψ, hψ, hψ', hψr, hψr', hψe⟩ := IsReparam.refl hr
  refine ⟨(d, a * (d + e)) :: (e, b * (d + e)) :: ψ,
    isTimed_cons.2 ⟨hd, isTimed_cons.2 ⟨he, hψ⟩⟩,
    List.forall_mem_cons.2
      ⟨mul_nonneg ha hde.le, List.forall_mem_cons.2 ⟨mul_nonneg hb hde.le, hψ'⟩⟩,
    ?_, ?_, ?_⟩
  · simp [hψr]
  · simp only [List.map_cons, List.sum_cons, duration_cons, hψr']
    linear_combination (d + e) * hab
  · intro t
    rw [hsplit]
    have hψ₂ : ∀ x ∈ ψ, 0 ≤ x.1 ∧ 0 ≤ x.2 := hψ.and_nonneg hψ'
    refine evalTimed_cons_comp hd (mul_nonneg ha hde.le)
      (fun h ↦ by rw [hva, (mul_eq_zero.1 h).resolve_right hde.ne', zero_smul])
      (List.forall_mem_cons.2 ⟨⟨he.le, mul_nonneg hb hde.le⟩, hψ₂⟩)
      (List.forall_mem_cons.2 ⟨mul_nonneg hb hde.le, hr.nonneg⟩)
      (evalTimed_cons_comp he (mul_nonneg hb hde.le)
        (fun h ↦ by rw [hwb, (mul_eq_zero.1 h).resolve_right hde.ne', zero_smul]) hψ₂ hr.nonneg
        hψe) t

/-! ### Composites of parametrized paths -/

/-- A list of `(duration, segment)` pairs presenting the composite `evalTimed q ∘ evalTimed φ` of
the parametrized path of `q` with a timing `φ` in `𝕜`, when `q` and `φ` are timed presentations
and every segment of `φ` is nonnegative (see `TauCeti.PLPath.evalTimed_timedComp`). It runs
through the pieces of `φ` in turn: a piece of `φ` that ends before the current segment `(e, w)` of
`q` does is run along the corresponding part of `w`, and a piece of `φ` that ends after it is
subdivided at the end of that segment. -/
def timedComp : List (𝕜 × V) → List (𝕜 × 𝕜) → List (𝕜 × V)
  | _, [] => []
  | [], φ => φ.map fun x ↦ (x.1, 0)
  | (e, w) :: q, (d, a) :: φ =>
    if a < e then (d, (a / e) • w) :: timedComp ((e - a, ((e - a) / e) • w) :: q) φ
    else if a = e then (d, w) :: timedComp q φ
    else (d * e / a, w) :: timedComp q ((d - d * e / a, a - e) :: φ)
termination_by q φ => q.length + φ.length

/-- `TauCeti.PLPath.timedComp q φ` presents the composite `evalTimed q ∘ evalTimed φ`. -/
theorem evalTimed_timedComp {φ : List (𝕜 × 𝕜)} (hq : IsTimed q) (hφ : IsTimed φ)
    (hφ' : ∀ x ∈ φ, 0 ≤ x.2) (t : 𝕜) :
    evalTimed (timedComp q φ) t = evalTimed q (evalTimed φ t) := by
  induction q, φ using timedComp.induct generalizing t with
  | case1 q => rw [timedComp.eq_1, evalTimed_nil, evalTimed_nil, evalTimed_zero hq.nonneg]
  | case2 φ hφ₀ =>
    rw [timedComp.eq_2 _ hφ₀, evalTimed_nil]
    exact evalTimed_eq_zero_of_forall (List.forall_mem_map.2 fun _ _ ↦ rfl) t
  | case3 e w q d a φ hae ih =>
    obtain ⟨he, hq⟩ := isTimed_cons.1 hq
    obtain ⟨hd, hφ⟩ := isTimed_cons.1 hφ
    obtain ⟨ha, hφ'⟩ := List.forall_mem_cons.1 hφ'
    dsimp only at he hd ha
    have hq₂ : IsTimed ((e - a, ((e - a) / e) • w) :: q) := isTimed_cons.2 ⟨sub_pos.2 hae, hq⟩
    simp only [timedComp.eq_3, hae, ↓reduceIte]
    rw [evalTimed_cons_eq_evalTimed_cons_cons_sub ha hae.le w q]
    exact evalTimed_cons_comp hd ha (fun h ↦ by rw [h, zero_div, zero_smul])
      (hφ.and_nonneg hφ') hq₂.nonneg (ih hq₂ hφ hφ') t
  | case4 w q d a φ _ ih =>
    obtain ⟨ha, hq⟩ := isTimed_cons.1 hq
    obtain ⟨hd, hφ⟩ := isTimed_cons.1 hφ
    obtain ⟨-, hφ'⟩ := List.forall_mem_cons.1 hφ'
    simp only [timedComp.eq_3, lt_self_iff_false, ↓reduceIte]
    exact evalTimed_cons_comp hd ha.le (fun h ↦ absurd h ha.ne')
      (hφ.and_nonneg hφ') hq.nonneg (ih hq hφ hφ') t
  | case5 e w q d a φ hae hae' ih =>
    obtain ⟨he, hq⟩ := isTimed_cons.1 hq
    obtain ⟨hd, hφ⟩ := isTimed_cons.1 hφ
    obtain ⟨-, hφ'⟩ := List.forall_mem_cons.1 hφ'
    dsimp only at he hd
    have hea := (not_lt.1 hae).lt_of_ne' hae'
    have hpos : 0 < d * e / a := div_pos (mul_pos hd he) (he.trans hea)
    have hlt := mul_div_lt_self hd (he.trans hea) hea
    have ha : a ≠ 0 := (he.trans hea).ne'
    have hφ₂ : IsTimed ((d - d * e / a, a - e) :: φ) := isTimed_cons.2 ⟨sub_pos.2 hlt, hφ⟩
    have hφ₂' : ∀ x ∈ (d - d * e / a, a - e) :: φ, 0 ≤ x.2 :=
      List.forall_mem_cons.2 ⟨(sub_pos.2 hea).le, hφ'⟩
    simp only [timedComp.eq_3, hae, hae', ↓reduceIte]
    rw [evalTimed_cons_eq_evalTimed_cons_cons (D := d) (v := a) (v₁ := e) (v₂ := a - e)
      (d₁ := d * e / a) (d₂ := d - d * e / a) hpos.le (sub_pos.2 hlt).le
      (add_sub_cancel _ d) (by rw [smul_eq_mul]; field_simp) (by rw [smul_eq_mul]; field_simp) φ]
    exact evalTimed_cons_comp hpos he.le (fun h ↦ absurd h he.ne')
      (hφ₂.and_nonneg hφ₂') hq.nonneg (ih hq hφ₂ hφ₂') t

theorem isTimed_timedComp {φ : List (𝕜 × 𝕜)} (hq : IsTimed q) (hφ : IsTimed φ) :
    IsTimed (timedComp q φ) := by
  induction q, φ using timedComp.induct with
  | case1 q => simp [timedComp.eq_1]
  | case2 φ hφ₀ =>
    rw [timedComp.eq_2 _ hφ₀]
    exact List.forall_mem_map.2 hφ
  | case3 e w q d a φ hae ih =>
    obtain ⟨hd, hφ⟩ := isTimed_cons.1 hφ
    simp only [timedComp.eq_3, hae, ↓reduceIte]
    exact isTimed_cons.2 ⟨hd, ih (isTimed_cons.2 ⟨sub_pos.2 hae, (isTimed_cons.1 hq).2⟩) hφ⟩
  | case4 w q d a φ _ ih =>
    simp only [timedComp.eq_3, lt_self_iff_false, ↓reduceIte]
    exact isTimed_cons.2 ⟨(isTimed_cons.1 hφ).1, ih (isTimed_cons.1 hq).2 (isTimed_cons.1 hφ).2⟩
  | case5 e w q d a φ hae hae' ih =>
    obtain ⟨he, hq⟩ := isTimed_cons.1 hq
    obtain ⟨hd, hφ⟩ := isTimed_cons.1 hφ
    dsimp only at he hd
    have hea := (not_lt.1 hae).lt_of_ne' hae'
    have hpos : 0 < d * e / a := div_pos (mul_pos hd he) (he.trans hea)
    have hlt := mul_div_lt_self hd (he.trans hea) hea
    simp only [timedComp.eq_3, hae, hae', ↓reduceIte]
    exact isTimed_cons.2 ⟨hpos, ih hq (isTimed_cons.2 ⟨sub_pos.2 hlt, hφ⟩)⟩

@[simp]
theorem duration_timedComp (q : List (𝕜 × V)) (φ : List (𝕜 × 𝕜)) :
    duration (timedComp q φ) = duration φ := by
  induction q, φ using timedComp.induct with
  | case1 q => simp [timedComp.eq_1]
  | case2 φ hφ₀ => simp [timedComp.eq_2 _ hφ₀, duration, Function.comp_def]
  | case3 e w q d a φ hae ih => simp [timedComp.eq_3, hae, ih]
  | case4 w q d a φ _ ih => simp [timedComp.eq_3, ih]
  | case5 e w q d a φ hae hae' ih =>
    simp only [timedComp.eq_3, hae, hae', ↓reduceIte, duration_cons, ih]
    ring

/-- Composing a timed presentation in `𝕜` with nonnegative segments with a timing gives
nonnegative segments again. -/
theorem timedComp_snd_nonneg {q : List (𝕜 × 𝕜)} {φ : List (𝕜 × 𝕜)} (hq : IsTimed q)
    (hq' : ∀ x ∈ q, 0 ≤ x.2) (hφ' : ∀ x ∈ φ, 0 ≤ x.2) : ∀ x ∈ timedComp q φ, 0 ≤ x.2 := by
  induction q, φ using timedComp.induct with
  | case1 q => simp [timedComp.eq_1]
  | case2 φ hφ₀ =>
    rw [timedComp.eq_2 _ hφ₀]
    exact List.forall_mem_map.2 fun _ _ ↦ le_rfl
  | case3 e w q d a φ hae ih =>
    obtain ⟨he, hq⟩ := isTimed_cons.1 hq
    obtain ⟨hw, hq'⟩ := List.forall_mem_cons.1 hq'
    obtain ⟨ha, hφ'⟩ := List.forall_mem_cons.1 hφ'
    dsimp only at he hw ha
    simp only [timedComp.eq_3, hae, ↓reduceIte]
    refine List.forall_mem_cons.2 ⟨mul_nonneg (div_nonneg ha he.le) hw, ih ?_ ?_ hφ'⟩
    · exact isTimed_cons.2 ⟨sub_pos.2 hae, hq⟩
    · exact List.forall_mem_cons.2 ⟨mul_nonneg (div_nonneg (sub_pos.2 hae).le he.le) hw, hq'⟩
  | case4 w q d a φ _ ih =>
    simp only [timedComp.eq_3, lt_self_iff_false, ↓reduceIte]
    exact List.forall_mem_cons.2 ⟨(List.forall_mem_cons.1 hq').1,
      ih (isTimed_cons.1 hq).2 (List.forall_mem_cons.1 hq').2 (List.forall_mem_cons.1 hφ').2⟩
  | case5 e w q d a φ hae hae' ih =>
    simp only [timedComp.eq_3, hae, hae', ↓reduceIte]
    exact List.forall_mem_cons.2 ⟨(List.forall_mem_cons.1 hq').1,
      ih (isTimed_cons.1 hq).2 (List.forall_mem_cons.1 hq').2
        (List.forall_mem_cons.2 ⟨sub_nonneg.2 (not_lt.1 hae), (List.forall_mem_cons.1 hφ').2⟩)⟩

/-- When the timing `φ` runs through all of `q`, the composite `TauCeti.PLPath.timedComp q φ`
presents the same `TauCeti.PLPath` as `q`. -/
theorem ofSegments_map_snd_timedComp {φ : List (𝕜 × 𝕜)} (hq : IsTimed q) (hφ' : ∀ x ∈ φ, 0 ≤ x.2)
    (h : duration q ≤ (φ.map Prod.snd).sum) :
    ofSegments 𝕜 ((timedComp q φ).map Prod.snd) = ofSegments 𝕜 (q.map Prod.snd) := by
  induction q, φ using timedComp.induct with
  | case1 q => simp [timedComp.eq_1, hq.eq_nil_of_duration_nonpos (by simpa using h)]
  | case2 φ hφ₀ =>
    rw [timedComp.eq_2 _ hφ₀, List.map_nil, ofSegments_nil, ofSegments_eq_one_iff, List.map_map]
    exact List.forall_mem_map.2 fun _ _ ↦ rfl
  | case3 e w q d a φ hae ih =>
    obtain ⟨he, hq⟩ := isTimed_cons.1 hq
    obtain ⟨ha, hφ'⟩ := List.forall_mem_cons.1 hφ'
    dsimp only at he ha
    simp only [duration_cons, List.map_cons, List.sum_cons] at h
    simp only [timedComp.eq_3, hae, ↓reduceIte]
    rw [List.map_cons, ofSegments_cons,
      ih (isTimed_cons.2 ⟨sub_pos.2 hae, hq⟩) hφ' (by simp only [duration_cons]; linarith),
      ← ofSegments_cons, List.map_cons, List.map_cons,
      ofSegments_div_smul_cons_sub_div_smul_cons ha hae.le he]
  | case4 w q d a φ _ ih =>
    simp only [duration_cons, List.map_cons, List.sum_cons] at h
    simp only [timedComp.eq_3, lt_self_iff_false, ↓reduceIte]
    rw [List.map_cons, List.map_cons,
      ofSegments_cons, ofSegments_cons,
      ih (isTimed_cons.1 hq).2 (List.forall_mem_cons.1 hφ').2 (by linarith)]
  | case5 e w q d a φ hae hae' ih =>
    simp only [duration_cons, List.map_cons, List.sum_cons] at h
    simp only [timedComp.eq_3, hae, hae', ↓reduceIte]
    rw [List.map_cons, List.map_cons, ofSegments_cons,
      ofSegments_cons, ih (isTimed_cons.1 hq).2
        (List.forall_mem_cons.2 ⟨sub_nonneg.2 (not_lt.1 hae), (List.forall_mem_cons.1 hφ').2⟩)
        (by simp only [List.map_cons, List.sum_cons]; linarith)]

/-! ### The parametrized path determines the presented path -/

/-- Two timed presentations with the same parametrized path whose first segments have the same
duration have the same first segment, and the same parametrized path after it. -/
private theorem eq_and_evalTimed_eq_of_evalTimed_cons_eq (hd : 0 < d) (hp : IsTimed p)
    (hq : IsTimed q) (h : ∀ t, evalTimed ((d, v) :: p) t = evalTimed ((d, w) :: q) t) :
    v = w ∧ ∀ t, evalTimed p t = evalTimed q t := by
  have hp₀ := evalTimed_eq_evalTimed_cons_add_sub (p := p) (v := v) hd le_rfl
  have hq₀ := evalTimed_eq_evalTimed_cons_add_sub (p := q) (v := w) hd le_rfl
  rw [evalTimed_zero hp.nonneg, h, eq_comm, sub_eq_zero] at hp₀
  rw [evalTimed_zero hq.nonneg, eq_comm, sub_eq_zero] at hq₀
  obtain rfl : v = w := hp₀.symm.trans hq₀
  refine ⟨rfl, fun t ↦ ?_⟩
  rcases le_total t 0 with ht | ht
  · rw [evalTimed_of_nonpos hp.nonneg ht, evalTimed_of_nonpos hq.nonneg ht]
  · rw [evalTimed_eq_evalTimed_cons_add_sub (p := p) (v := v) hd ht,
      evalTimed_eq_evalTimed_cons_add_sub (p := q) (v := v) hd ht, h]

/-- Two timed presentations with the same parametrized path present the same
`TauCeti.PLPath`: the presented `TauCeti.PLPath` depends only on the parametrized path. -/
theorem ofSegments_map_snd_eq_of_evalTimed_eq (hp : IsTimed p) (hq : IsTimed q)
    (h : ∀ t, evalTimed p t = evalTimed q t) :
    ofSegments 𝕜 (p.map Prod.snd) = ofSegments 𝕜 (q.map Prod.snd) := by
  induction hn : p.length + q.length using Nat.strong_induction_on generalizing p q with
  | _ n ih =>
  -- First segments of the same duration: compare the remaining segments by induction.
  have same : ∀ {d : 𝕜} {v w : V} {p q : List (𝕜 × V)}, 0 < d → IsTimed p → IsTimed q →
      p.length + q.length < n →
      (∀ t, evalTimed ((d, v) :: p) t = evalTimed ((d, w) :: q) t) →
      ofSegments 𝕜 (v :: p.map Prod.snd) = ofSegments 𝕜 (w :: q.map Prod.snd) := by
    intro d v w p q hd hp hq hlt h
    obtain ⟨rfl, h'⟩ := eq_and_evalTimed_eq_of_evalTimed_cons_eq hd hp hq h
    rw [ofSegments_cons, ofSegments_cons, ih _ hlt hp hq h' rfl]
  -- A shorter first segment of `p`: subdivide the first segment of `q` at its duration.
  have shorter : ∀ {d e : 𝕜} {v w : V} {p q : List (𝕜 × V)}, 0 < d → d < e → IsTimed p →
      IsTimed q → p.length + q.length + 2 = n →
      (∀ t, evalTimed ((d, v) :: p) t = evalTimed ((e, w) :: q) t) →
      ofSegments 𝕜 (v :: p.map Prod.snd) = ofSegments 𝕜 (w :: q.map Prod.snd) := by
    intro d e v w p q hd hde hp hq hn h
    have he : 0 < e := hd.trans hde
    rw [same hd hp (isTimed_cons.2 ⟨sub_pos.2 hde, hq⟩) (by simp only [List.length_cons]; omega)
      fun t ↦ (h t).trans (evalTimed_cons_eq_evalTimed_cons_cons_sub hd.le hde.le w q t),
      List.map_cons, ofSegments_div_smul_cons_sub_div_smul_cons hd.le hde.le he]
  -- An empty presentation has the parametrized path of a single stationary segment.
  have nil_left : ∀ {e : 𝕜} {w : V} {q : List (𝕜 × V)}, 0 < e → IsTimed q →
      q.length + 1 = n → (∀ t, evalTimed ((e, w) :: q) t = 0) →
      ofSegments 𝕜 (w :: q.map Prod.snd) = 1 := by
    intro e w q he hq hn h
    rw [← same (p := []) (v := 0) he isTimed_nil hq (by simp only [List.length_nil]; omega)
      fun t ↦ by simp [evalTimed_cons, h]]
    simp
  match p, q, hp, hq, h with
  | [], [], _, _, _ => rfl
  | [], (e, w) :: q, _, hq, h =>
    obtain ⟨he, hq⟩ := isTimed_cons.1 hq
    simpa using (nil_left he hq (by simpa using hn) fun t ↦ (h t).symm).symm
  | (d, v) :: p, [], hp, _, h =>
    obtain ⟨hd, hp⟩ := isTimed_cons.1 hp
    simpa using nil_left hd hp (by simpa using hn) h
  | (d, v) :: p, (e, w) :: q, hp, hq, h =>
    obtain ⟨hd, hp'⟩ := isTimed_cons.1 hp
    obtain ⟨he, hq'⟩ := isTimed_cons.1 hq
    simp only [List.length_cons] at hn
    simp only [List.map_cons]
    rcases lt_trichotomy d e with hde | rfl | hde
    · exact shorter hd hde hp' hq' (by omega) h
    · exact same hd hp' hq' (by omega) h
    · exact (shorter he hde hq' hp' (by omega) fun t ↦ (h t).symm).symm

/-! ### Reparametrizations present the same path -/

/-- Reparametrization is transitive: the timings compose by `TauCeti.PLPath.timedComp`. -/
theorem IsReparam.trans (hpq : IsReparam p q) (hqr : IsReparam q r) : IsReparam p r := by
  obtain ⟨φ, hφ, hφ', hφp, hφq, hφe⟩ := hpq
  obtain ⟨ψ, hψ, hψ', hψq, hψr, hψe⟩ := hqr
  refine ⟨timedComp ψ φ, isTimed_timedComp hψ hφ, timedComp_snd_nonneg hψ hψ' hφ',
    by rw [duration_timedComp, hφp], ?_,
    fun t ↦ by rw [hφe, hψe, evalTimed_timedComp hψ hφ hφ']⟩
  rw [← endpoint_ofSegments (𝕜 := 𝕜), ofSegments_map_snd_timedComp hψ hφ' (by rw [hψq, hφq]),
    endpoint_ofSegments, hψr]

/-- A reparametrization presents the same `TauCeti.PLPath`. -/
theorem IsReparam.ofSegments_map_snd_eq (h : IsReparam p q) (hp : IsTimed p) (hq : IsTimed q) :
    ofSegments 𝕜 (p.map Prod.snd) = ofSegments 𝕜 (q.map Prod.snd) := by
  obtain ⟨φ, hφ, hφ', -, hφq, hφe⟩ := h
  rw [ofSegments_map_snd_eq_of_evalTimed_eq hp (isTimed_timedComp hq hφ)
    fun t ↦ by rw [hφe, evalTimed_timedComp hq hφ hφ'], ofSegments_map_snd_timedComp hq hφ' hφq.ge]

/-- Every timed presentation is a reparametrization of a timed presentation of its normal
form. -/
theorem exists_isReparam_map_snd_eq_normalize (hp : IsTimed p) :
    ∃ r, IsTimed r ∧ r.map Prod.snd = normalize 𝕜 (p.map Prod.snd) ∧ IsReparam p r := by
  induction p with
  | nil => exact ⟨[], isTimed_nil, normalize_nil.symm, IsReparam.refl isTimed_nil⟩
  | cons x p ih =>
    obtain ⟨d, v⟩ := x
    obtain ⟨hd, hp⟩ := isTimed_cons.1 hp
    obtain ⟨r, hr, hrs, hpr⟩ := ih hp
    have h₁ : IsReparam ((d, v) :: p) ((d, v) :: r) := hpr.cons hd hr.nonneg v
    rw [List.map_cons, normalize_cons, ← hrs]
    rcases r with _ | ⟨⟨e, w⟩, r⟩
    · rcases eq_or_ne v 0 with rfl | hv
      · refine ⟨[], isTimed_nil, by simp, h₁.trans ⟨[(d, 0)], by simpa using hd, by simp,
          by simp, by simp, fun t ↦ by simp [evalTimed_cons]⟩⟩
      · exact ⟨[(d, v)], by simpa using hd, by simp [consMerge_nil_of_ne_zero hv], h₁⟩
    · obtain ⟨he, hr⟩ := isTimed_cons.1 hr
      by_cases hvw : SameRay 𝕜 v w
      · exact ⟨(d + e, v + w) :: r, isTimed_cons.2 ⟨add_pos hd he, hr⟩,
          by simp [consMerge_cons_of_sameRay hvw], h₁.trans (isReparam_cons_cons_add hd he hvw hr)⟩
      · exact ⟨(d, v) :: (e, w) :: r, isTimed_cons.2 ⟨hd, isTimed_cons.2 ⟨he, hr⟩⟩,
          by simp [consMerge_cons_of_not_sameRay hvw], h₁⟩

omit [IsStrictOrderedRing 𝕜] in
/-- A timed presentation of positive duration whose parametrized path is a reparametrization of
the constant path is a reparametrization of the constant path of any duration `T`. -/
private theorem IsReparam.singleton_zero_of_nil (h : IsReparam p ([] : List (𝕜 × V)))
    (hp : 0 < duration p) {T : 𝕜} (hT : 0 ≤ T) : IsReparam p [(T, (0 : V))] := by
  obtain ⟨φ, -, -, -, -, hφe⟩ := h
  exact ⟨[(duration p, T)], by simpa using hp, by simpa using hT, by simp, by simp,
    fun t ↦ by simp [hφe, evalTimed_cons]⟩

/-- **Faithfulness of the segment-list model.** Two timed presentations of positive duration
present the same `TauCeti.PLPath` exactly when they are both reparametrizations of a common timed
presentation, which can be chosen of any prescribed positive duration `T`. For `T = 1` and
presentations of duration `1`, these are nondecreasing surjective piecewise-linear
reparametrizations of `[0, 1]`. -/
theorem ofSegments_map_snd_eq_iff_exists_isReparam (hp : IsTimed p) (hq : IsTimed q)
    (hp₀ : 0 < duration p) (hq₀ : 0 < duration q) {T : 𝕜} (hT : 0 < T) :
    ofSegments 𝕜 (p.map Prod.snd) = ofSegments 𝕜 (q.map Prod.snd) ↔
      ∃ r, IsTimed r ∧ duration r = T ∧ IsReparam p r ∧ IsReparam q r := by
  refine ⟨fun h ↦ ?_, fun ⟨r, hr, _, hpr, hqr⟩ ↦
    (hpr.ofSegments_map_snd_eq hp hr).trans (hqr.ofSegments_map_snd_eq hq hr).symm⟩
  obtain ⟨rp, hrp, hrps, hprp⟩ := exists_isReparam_map_snd_eq_normalize hp
  obtain ⟨rq, hrq, hrqs, hqrq⟩ := exists_isReparam_map_snd_eq_normalize hq
  rw [PLPath.ext_iff, segments_ofSegments, segments_ofSegments] at h
  rw [← h] at hrqs
  set l := normalize 𝕜 (p.map Prod.snd)
  rcases eq_or_ne l [] with hl | hl
  · -- The constant path: both are reparametrizations of a single stationary segment.
    rw [hl, List.map_eq_nil_iff] at hrps hrqs
    subst hrps hrqs
    exact ⟨[(T, 0)], by simpa using hT, by simp, hprp.singleton_zero_of_nil hp₀ hT.le,
      hqrq.singleton_zero_of_nil hq₀ hT.le⟩
  · -- Otherwise, run the segments of the normal form during equal times.
    have hlen : (0 : 𝕜) < l.length := Nat.cast_pos.2 (List.length_pos_iff.2 hl)
    have hr : IsTimed (l.map fun v ↦ (T / l.length, v)) :=
      List.forall_mem_map.2 fun _ _ ↦ div_pos hT hlen
    have hrs : (l.map fun v ↦ (T / l.length, v)).map Prod.snd = l := by simp
    refine ⟨l.map fun v ↦ (T / l.length, v), hr, ?_,
      hprp.trans (isReparam_of_map_snd_eq hrp hr (hrps.trans hrs.symm)),
      hqrq.trans (isReparam_of_map_snd_eq hrq hr (hrqs.trans hrs.symm))⟩
    simp [duration, Function.comp_def, mul_div_cancel₀ _ hlen.ne']

end PLPath

end TauCeti
