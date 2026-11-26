/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import TauCeti.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Real.Sqrt
import TauCeti.Algebra.Order.Archimedean.Basic

/-!
# Rational enclosures of real and complex numbers

A certified numerical computation never treats an approximate value as exact. Every real number
`t` it uses comes with a closed rational interval `[l, u]` satisfying `l ≤ t ≤ u`, and every
complex number `z` with a rational box: a pair of closed rational intervals containing `Re z` and
`Im z`. Every check made on the rational data of such an enclosure (its width, its precision,
membership of a rational, a bound for the square of the modulus) is then a comparison of rational
numbers; only the proof that the interval or box contains the enclosed number is a statement about
that number itself. This is how
explicit bounds for linear forms in logarithms and the lattice reductions built on them are
turned into rigorous statements about real and complex numbers.

The intervals are Mathlib's `NonemptyInterval ℚ`, and the width of an interval is its
`NonemptyInterval.length`.

Overlapping enclosures do not certify equality: the interval `[1, 2]` encloses both `1` and `2`.
An enclosure of width zero, on the other hand, determines the enclosed number
(`TauCeti.RealEnclosure.eq_of_length_eq_zero`, `TauCeti.ComplexEnclosure.eq_of_width_eq_zero`).

## Main definitions

* `TauCeti.RealEnclosure t`: a rational interval containing the real number `t`.
* `TauCeti.RealEnclosure.HasPrecision E n`: the interval of `E` has width at most `2⁻ⁿ`.
* `TauCeti.RealEnclosure.bisect`, `TauCeti.RealEnclosure.refine`: the half of the interval that
  contains the enclosed number, and the enclosure obtained by bisecting `n` times.
* `TauCeti.ComplexEnclosure z`: real enclosures of the real and imaginary parts of `z`.
* `TauCeti.ComplexEnclosure.box`, `TauCeti.ComplexEnclosure.width`,
  `TauCeti.ComplexEnclosure.HasPrecision`, `TauCeti.ComplexEnclosure.normSqBound`: the rational
  box of a complex enclosure, its coordinatewise error bound (bounding the errors of the real and
  imaginary parts separately), its absolute precision and a rational upper bound for `|z|²`.
* `TauCeti.ComplexEnclosure.refine`: both intervals refined `n` times.

## Main results

* `TauCeti.RealEnclosure.abs_sub_le_length`: every real `u` between the endpoints satisfies
  `|t - u| ≤ width`; `TauCeti.RealEnclosure.abs_sub_ratCast_le_length` is the case of a rational
  `q` in the interval.
* `TauCeti.RealEnclosure.ofRat`, `TauCeti.RealEnclosure.ofLE`: the degenerate enclosure `[q, q]`
  of a rational `q`, and the enlargement of an enclosure to a larger interval.
* `TauCeti.ComplexEnclosure.max_abs_sub_le_width`: every point `w` of the box satisfies
  `max (|Re z - Re w|, |Im z - Im w|) ≤ width`; at absolute precision `n` the bound is `2⁻ⁿ`
  (`TauCeti.ComplexEnclosure.HasPrecision.max_abs_sub_le`).
* `TauCeti.ComplexEnclosure.ratCast_add_ratCast_mul_I_mem_box_iff`: a point `a + b i` with
  rational coordinates lies in the box exactly when `a` and `b` lie in the rational intervals;
  `TauCeti.ComplexEnclosure.zero_notMem_box_iff` is the case of the point `0`.
* `TauCeti.ComplexEnclosure.normSq_le_normSqBound`:
  `|z|² ≤ max (l_R², u_R²) + max (l_I², u_I²)`.
* `TauCeti.ComplexEnclosure.hasPrecision_ofReal_iff`: a real enclosure viewed as a complex one
  keeps its absolute precision.
* `NonemptyInterval.reProdIm_Icc_ratCast_subset`: nested rational rectangles span nested complex
  rectangles.
* `TauCeti.RealEnclosure.bisect_interval_of_le`, `TauCeti.RealEnclosure.bisect_interval_of_lt`:
  the half kept by a bisection.
* `TauCeti.RealEnclosure.length_refine`, `TauCeti.RealEnclosure.refine_interval_antitone`: the
  refinements of an enclosure are nested and the one at level `n` has `2⁻ⁿ` times its width;
  `TauCeti.RealEnclosure.HasPrecision.refine`: each bisection gains one bit of absolute precision,
  and `TauCeti.RealEnclosure.exists_hasPrecision_refine`: every precision is reached. The same
  holds for complex enclosures (`TauCeti.ComplexEnclosure.width_refine`,
  `TauCeti.ComplexEnclosure.refine_box_antitone`).

## References

* B. M. M. de Weger, *Algorithms for Diophantine equations*, CWI Tract 65, 1989, §2.5, printed
  pp. 33–34.
* J. R. Doyle, D. Krumm, *Computing algebraic numbers of bounded height*, arXiv:1111.4963, §4
  (before §4.1).
-/

public section

open Complex in
/-- Nested rational rectangles span nested rectangles of `ℂ`. -/
theorem NonemptyInterval.reProdIm_Icc_ratCast_subset {R R' J J' : NonemptyInterval ℚ}
    (hR : R' ≤ R) (hJ : J' ≤ J) :
    Set.Icc (R'.fst : ℝ) R'.snd ×ℂ Set.Icc (J'.fst : ℝ) J'.snd ⊆
      Set.Icc (R.fst : ℝ) R.snd ×ℂ Set.Icc (J.fst : ℝ) J.snd :=
  reProdIm_subset_iff.mpr <| Set.prod_mono (Icc_ratCast_subset_Icc_ratCast hR)
    (Icc_ratCast_subset_Icc_ratCast hJ)

namespace TauCeti

/-- A *real enclosure* of `t : ℝ`: a closed nonempty rational interval `[l, u]` with
`l ≤ t ≤ u` in `ℝ`. Its error bound is the width `u - l` of the interval, which is
`NonemptyInterval.length`. -/
@[ext]
structure RealEnclosure (t : ℝ) where
  /-- The enclosing closed rational interval. -/
  interval : NonemptyInterval ℚ
  /-- The lower endpoint of the interval is at most `t`. -/
  fst_le : (interval.fst : ℝ) ≤ t
  /-- The upper endpoint of the interval is at least `t`. -/
  le_snd : t ≤ (interval.snd : ℝ)

namespace RealEnclosure

variable {t : ℝ}

/-- The enclosed real number lies in the real interval spanned by the rational endpoints. -/
theorem mem_Icc (E : RealEnclosure t) : t ∈ Set.Icc (E.interval.fst : ℝ) E.interval.snd :=
  ⟨E.fst_le, E.le_snd⟩

/-- A rational number lies in the real interval spanned by the rational endpoints exactly when
it lies in the rational interval. -/
theorem ratCast_mem_Icc_iff (E : RealEnclosure t) {q : ℚ} :
    (q : ℝ) ∈ Set.Icc (E.interval.fst : ℝ) E.interval.snd ↔ q ∈ E.interval := by
  rw [← Set.mem_preimage, Rat.preimage_cast_Icc, Set.mem_Icc, NonemptyInterval.mem_def]

/-- Every real number `u` between the endpoints of the interval approximates the enclosed number
up to the width of the interval. -/
theorem abs_sub_le_length (E : RealEnclosure t) {u : ℝ}
    (hu : u ∈ Set.Icc (E.interval.fst : ℝ) E.interval.snd) : |t - u| ≤ E.interval.length := by
  rw [NonemptyInterval.length, Rat.cast_sub]
  exact abs_sub_le_of_le_of_le E.fst_le E.le_snd hu.1 hu.2

/-- Every rational number `q` of the interval approximates the enclosed number up to the width
of the interval. -/
theorem abs_sub_ratCast_le_length (E : RealEnclosure t) {q : ℚ} (hq : q ∈ E.interval) :
    |t - q| ≤ E.interval.length :=
  E.abs_sub_le_length (E.ratCast_mem_Icc_iff.mpr hq)

/-- The enclosed number is within the width of the interval of its lower endpoint. -/
theorem abs_sub_fst_le_length (E : RealEnclosure t) :
    |t - E.interval.fst| ≤ E.interval.length :=
  E.abs_sub_ratCast_le_length ⟨le_rfl, E.interval.fst_le_snd⟩

/-- An enclosure of width zero determines the enclosed number: it is the common endpoint. -/
theorem eq_of_length_eq_zero (E : RealEnclosure t) (h : E.interval.length = 0) :
    t = E.interval.fst := by
  have := E.abs_sub_fst_le_length
  rw [h, Rat.cast_zero] at this
  exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

/-- The singleton interval `[q, q]` certifies that the enclosed number is `q`. -/
theorem eq_of_interval_eq_pure (E : RealEnclosure t) {q : ℚ}
    (h : E.interval = NonemptyInterval.pure q) : t = q := by
  have := E.eq_of_length_eq_zero (by rw [h, NonemptyInterval.length_pure])
  rw [this, h]
  simp

/-- The degenerate enclosure `[q, q]` of a rational number `q`. -/
def ofRat (q : ℚ) : RealEnclosure q where
  interval := NonemptyInterval.pure q
  fst_le := le_rfl
  le_snd := le_rfl

@[simp]
theorem ofRat_interval (q : ℚ) : (ofRat q).interval = NonemptyInterval.pure q :=
  (rfl)

/-- An interval containing the interval of an enclosure of `t` again encloses `t`. -/
def ofLE (E : RealEnclosure t) (J : NonemptyInterval ℚ) (h : E.interval ≤ J) :
    RealEnclosure t where
  interval := J
  fst_le := le_trans (by exact_mod_cast (NonemptyInterval.le_def.mp h).1) E.fst_le
  le_snd := le_trans E.le_snd (by exact_mod_cast (NonemptyInterval.le_def.mp h).2)

@[simp]
theorem ofLE_interval (E : RealEnclosure t) (J : NonemptyInterval ℚ) (h : E.interval ≤ J) :
    (E.ofLE J h).interval = J :=
  (rfl)

/-- A real enclosure has *absolute precision* `n` when its width is at most `2⁻ⁿ`. -/
def HasPrecision (E : RealEnclosure t) (n : ℕ) : Prop :=
  E.interval.length ≤ ((2 : ℚ) ^ n)⁻¹

theorem hasPrecision_iff (E : RealEnclosure t) (n : ℕ) :
    E.HasPrecision n ↔ E.interval.length ≤ ((2 : ℚ) ^ n)⁻¹ :=
  Iff.rfl

instance (E : RealEnclosure t) (n : ℕ) : Decidable (E.HasPrecision n) :=
  decidable_of_iff _ (E.hasPrecision_iff n).symm

/-- Absolute precision `n` implies every smaller absolute precision. -/
theorem HasPrecision.mono {E : RealEnclosure t} {m n : ℕ} (h : E.HasPrecision n)
    (hmn : m ≤ n) : E.HasPrecision m :=
  h.trans (inv_anti₀ (by positivity) (pow_le_pow_right₀ one_le_two hmn))

/-- At absolute precision `n`, every real number between the endpoints of the interval
approximates the enclosed number up to `2⁻ⁿ`. -/
theorem HasPrecision.abs_sub_le {E : RealEnclosure t} {n : ℕ} (h : E.HasPrecision n) {u : ℝ}
    (hu : u ∈ Set.Icc (E.interval.fst : ℝ) E.interval.snd) : |t - u| ≤ ((2 : ℝ) ^ n)⁻¹ :=
  (E.abs_sub_le_length hu).trans <| by
    simpa using (Rat.cast_le (K := ℝ)).mpr ((E.hasPrecision_iff n).mp h)

/-- At absolute precision `n`, every rational number of the interval approximates the enclosed
number up to `2⁻ⁿ`. -/
theorem HasPrecision.abs_sub_ratCast_le {E : RealEnclosure t} {n : ℕ} (h : E.HasPrecision n)
    {q : ℚ} (hq : q ∈ E.interval) : |t - q| ≤ ((2 : ℝ) ^ n)⁻¹ :=
  h.abs_sub_le (E.ratCast_mem_Icc_iff.mpr hq)

/-- The degenerate enclosure of a rational number has every absolute precision. -/
@[simp]
theorem hasPrecision_ofRat (q : ℚ) (n : ℕ) : (ofRat q).HasPrecision n := by
  rw [hasPrecision_iff, ofRat_interval, NonemptyInterval.length_pure]
  positivity

/-- The half of the interval `[l, u]` of `E` that contains `t`: the lower half
`[l, (l + u) / 2]` when `t ≤ (l + u) / 2`, and the upper half `[(l + u) / 2, u]` otherwise. -/
noncomputable def bisect (E : RealEnclosure t) : RealEnclosure t :=
  if h : t ≤ ((E.interval.fst + E.interval.snd) / 2 : ℚ) then
    { interval := E.interval.lowerHalf
      fst_le := by rw [NonemptyInterval.lowerHalf_fst]; exact E.fst_le
      le_snd := by rwa [NonemptyInterval.lowerHalf_snd] }
  else
    { interval := E.interval.upperHalf
      fst_le := by rw [NonemptyInterval.upperHalf_fst]; exact (not_le.mp h).le
      le_snd := by rw [NonemptyInterval.upperHalf_snd]; exact E.le_snd }

/-- When `t` lies in the lower half of the interval `[l, u]`, bisection keeps `[l, (l + u) / 2]`. -/
theorem bisect_interval_of_le (E : RealEnclosure t)
    (h : t ≤ ((E.interval.fst + E.interval.snd) / 2 : ℚ)) :
    E.bisect.interval = E.interval.lowerHalf := by
  rw [bisect, dite_eq_left h]

/-- When `t` lies strictly above the midpoint of the interval `[l, u]`, bisection keeps
`[(l + u) / 2, u]`. -/
theorem bisect_interval_of_lt (E : RealEnclosure t)
    (h : ((E.interval.fst + E.interval.snd) / 2 : ℚ) < t) :
    E.bisect.interval = E.interval.upperHalf := by
  rw [bisect, dite_eq_right (not_le.mpr h)]

/-- Bisection shrinks the interval. -/
theorem bisect_interval_le (E : RealEnclosure t) : E.bisect.interval ≤ E.interval := by
  rcases le_or_gt t ((E.interval.fst + E.interval.snd) / 2 : ℚ) with h | h
  · exact (E.bisect_interval_of_le h).trans_le E.interval.lowerHalf_le
  · exact (E.bisect_interval_of_lt h).trans_le E.interval.upperHalf_le

/-- Bisection halves the width. -/
@[simp]
theorem length_bisect (E : RealEnclosure t) :
    E.bisect.interval.length = E.interval.length / 2 := by
  rcases le_or_gt t ((E.interval.fst + E.interval.snd) / 2 : ℚ) with h | h
  · rw [bisect_interval_of_le E h, NonemptyInterval.length_lowerHalf]
  · rw [bisect_interval_of_lt E h, NonemptyInterval.length_upperHalf]

/-- The refinement of `E` at level `n`: the enclosure of `t` obtained by bisecting `n` times,
keeping each time the half that contains `t`. Its intervals are nested
(`TauCeti.RealEnclosure.refine_interval_antitone`) and the `n`-th has width `2⁻ⁿ` times the width
of `E` (`TauCeti.RealEnclosure.length_refine`). -/
noncomputable def refine (E : RealEnclosure t) : ℕ → RealEnclosure t
  | 0 => E
  | n + 1 => (E.refine n).bisect

@[simp]
theorem refine_zero (E : RealEnclosure t) : E.refine 0 = E :=
  (rfl)

@[simp]
theorem refine_succ (E : RealEnclosure t) (n : ℕ) : E.refine (n + 1) = (E.refine n).bisect :=
  (rfl)

/-- The intervals of the refinements of an enclosure are nested. -/
theorem refine_interval_antitone (E : RealEnclosure t) :
    Antitone fun n => (E.refine n).interval :=
  antitone_nat_of_succ_le fun n => (E.refine n).bisect_interval_le

/-- Every refinement of an enclosure lies in its interval. -/
theorem refine_interval_le (E : RealEnclosure t) (n : ℕ) : (E.refine n).interval ≤ E.interval :=
  E.refine_interval_antitone n.zero_le

/-- The refinement at level `n` has width `2⁻ⁿ` times the width of the enclosure. -/
@[simp]
theorem length_refine (E : RealEnclosure t) (n : ℕ) :
    (E.refine n).interval.length = E.interval.length / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [refine_succ, length_bisect, ih, pow_succ, div_div]

/-- An enclosure of width zero is its own refinement at every level; in particular the singleton
`[q, q]` stays a singleton. -/
theorem refine_interval_of_length_eq_zero (E : RealEnclosure t) (h : E.interval.length = 0)
    (n : ℕ) : (E.refine n).interval = E.interval := by
  have hle := NonemptyInterval.le_def.mp (E.refine_interval_le n)
  rw [NonemptyInterval.length, sub_eq_zero] at h
  have := (E.refine n).interval.fst_le_snd
  exact NonemptyInterval.ext (Prod.ext (by linarith) (by linarith))

/-- Each bisection gains one bit of absolute precision. -/
theorem HasPrecision.refine {E : RealEnclosure t} {k : ℕ} (h : E.HasPrecision k) (n : ℕ) :
    (E.refine n).HasPrecision (k + n) := by
  rw [hasPrecision_iff, length_refine]
  calc E.interval.length / 2 ^ n ≤ ((2 : ℚ) ^ k)⁻¹ / 2 ^ n := by gcongr; exact h
    _ = ((2 : ℚ) ^ (k + n))⁻¹ := by ring

/-- Every enclosure has refinements of every absolute precision. -/
theorem exists_hasPrecision_refine (E : RealEnclosure t) (n : ℕ) :
    ∃ m, (E.refine m).HasPrecision n := by
  simpa only [hasPrecision_iff, length_refine] using
    (exists_div_pow_lt E.interval.length one_lt_two (by positivity : (0 : ℚ) < (2 ^ n)⁻¹)).imp
      fun _ => le_of_lt

end RealEnclosure

/-- A *complex enclosure* of `z : ℂ`: a rational box, that is, real enclosures of the real part
and of the imaginary part of `z`. -/
@[ext]
structure ComplexEnclosure (z : ℂ) where
  /-- The enclosure of the real part. -/
  re : RealEnclosure z.re
  /-- The enclosure of the imaginary part. -/
  im : RealEnclosure z.im

namespace ComplexEnclosure

open Complex

variable {z : ℂ}

/-- The rational box `{w : Re w ∈ R, Im w ∈ I}` of a complex enclosure `(R, I)`. -/
def box (E : ComplexEnclosure z) : Set ℂ :=
  Set.Icc (E.re.interval.fst : ℝ) E.re.interval.snd ×ℂ
    Set.Icc (E.im.interval.fst : ℝ) E.im.interval.snd

/-- Combined with `Complex.mem_reProdIm`, this characterizes membership in the box by the endpoint
bounds on the real and imaginary parts. -/
theorem box_def (E : ComplexEnclosure z) :
    E.box = Set.Icc (E.re.interval.fst : ℝ) E.re.interval.snd ×ℂ
      Set.Icc (E.im.interval.fst : ℝ) E.im.interval.snd :=
  (rfl)

/-- The enclosed complex number lies in the box of the enclosure. -/
theorem self_mem_box (E : ComplexEnclosure z) : z ∈ E.box :=
  mem_reProdIm.mpr ⟨E.re.mem_Icc, E.im.mem_Icc⟩

/-- A point `a + b i` with rational coordinates lies in the box exactly when `a` lies in the real
interval and `b` in the imaginary interval of the enclosure. -/
theorem ratCast_add_ratCast_mul_I_mem_box_iff (E : ComplexEnclosure z) (a b : ℚ) :
    (a + b * I : ℂ) ∈ E.box ↔ a ∈ E.re.interval ∧ b ∈ E.im.interval := by
  rw [box_def, mem_reProdIm, ← E.re.ratCast_mem_Icc_iff, ← E.im.ratCast_mem_Icc_iff]
  simp

/-- The point `0` lies outside the box exactly when `0` lies outside the real or the imaginary
interval of the enclosure. -/
theorem zero_notMem_box_iff (E : ComplexEnclosure z) :
    (0 : ℂ) ∉ E.box ↔ (0 : ℚ) ∉ E.re.interval ∨ (0 : ℚ) ∉ E.im.interval := by
  rw [← not_and_or, ← E.ratCast_add_ratCast_mul_I_mem_box_iff]
  simp

/-- The coordinatewise error bound of a complex enclosure: the larger of the widths of its two
intervals. It bounds the errors of the real and of the imaginary part separately, not the modulus
of the error. -/
def width (E : ComplexEnclosure z) : ℚ :=
  max E.re.interval.length E.im.interval.length

theorem width_def (E : ComplexEnclosure z) :
    E.width = max E.re.interval.length E.im.interval.length :=
  (rfl)

theorem width_nonneg (E : ComplexEnclosure z) : 0 ≤ E.width :=
  le_max_of_le_left E.re.interval.length_nonneg

/-- Every point `w` of the box approximates the enclosed number coordinatewise up to the width:
the errors of the real and of the imaginary part are both at most `E.width`. -/
theorem max_abs_sub_le_width (E : ComplexEnclosure z) {w : ℂ} (hw : w ∈ E.box) :
    max |z.re - w.re| |z.im - w.im| ≤ E.width := by
  rw [box_def, mem_reProdIm] at hw
  rw [width_def, Rat.cast_max]
  exact max_le_max (E.re.abs_sub_le_length hw.1) (E.im.abs_sub_le_length hw.2)

/-- A complex enclosure of width zero determines the enclosed number. -/
theorem eq_of_width_eq_zero (E : ComplexEnclosure z) (h : E.width = 0) :
    z = E.re.interval.fst + E.im.interval.fst * I := by
  have hre := E.re.eq_of_length_eq_zero
    (le_antisymm (h ▸ le_max_left _ _) E.re.interval.length_nonneg)
  have him := E.im.eq_of_length_eq_zero
    (le_antisymm (h ▸ le_max_right _ _) E.im.interval.length_nonneg)
  simpa [hre, him] using (re_add_im z).symm

/-- A complex enclosure has *absolute precision* `n` when both of its intervals have width at
most `2⁻ⁿ`. -/
def HasPrecision (E : ComplexEnclosure z) (n : ℕ) : Prop :=
  E.re.HasPrecision n ∧ E.im.HasPrecision n

theorem hasPrecision_iff (E : ComplexEnclosure z) (n : ℕ) :
    E.HasPrecision n ↔ E.re.HasPrecision n ∧ E.im.HasPrecision n :=
  Iff.rfl

/-- Absolute precision `n` of a complex enclosure means that its coordinatewise error bound is at
most `2⁻ⁿ`. -/
theorem hasPrecision_iff_width_le (E : ComplexEnclosure z) (n : ℕ) :
    E.HasPrecision n ↔ E.width ≤ ((2 : ℚ) ^ n)⁻¹ := by
  rw [hasPrecision_iff, width_def, max_le_iff, RealEnclosure.hasPrecision_iff,
    RealEnclosure.hasPrecision_iff]

instance (E : ComplexEnclosure z) (n : ℕ) : Decidable (E.HasPrecision n) :=
  decidable_of_iff _ (E.hasPrecision_iff_width_le n).symm

/-- Absolute precision `n` implies every smaller absolute precision. -/
theorem HasPrecision.mono {E : ComplexEnclosure z} {m n : ℕ} (h : E.HasPrecision n)
    (hmn : m ≤ n) : E.HasPrecision m :=
  ⟨h.1.mono hmn, h.2.mono hmn⟩

/-- At absolute precision `n`, every point `w` of the box approximates the enclosed number
coordinatewise up to `2⁻ⁿ`. -/
theorem HasPrecision.max_abs_sub_le {E : ComplexEnclosure z} {n : ℕ} (h : E.HasPrecision n)
    {w : ℂ} (hw : w ∈ E.box) : max |z.re - w.re| |z.im - w.im| ≤ ((2 : ℝ) ^ n)⁻¹ := by
  rw [box_def, mem_reProdIm] at hw
  exact max_le (h.1.abs_sub_le hw.1) (h.2.abs_sub_le hw.2)

/-- The refinement of a complex enclosure at level `n`: both of its intervals refined at level
`n`. -/
noncomputable def refine (E : ComplexEnclosure z) (n : ℕ) : ComplexEnclosure z :=
  ⟨E.re.refine n, E.im.refine n⟩

@[simp]
theorem refine_re (E : ComplexEnclosure z) (n : ℕ) : (E.refine n).re = E.re.refine n :=
  (rfl)

@[simp]
theorem refine_im (E : ComplexEnclosure z) (n : ℕ) : (E.refine n).im = E.im.refine n :=
  (rfl)

@[simp]
theorem refine_zero (E : ComplexEnclosure z) : E.refine 0 = E :=
  ComplexEnclosure.ext (by simp) (by simp)

/-- The boxes of the refinements of a complex enclosure are nested. -/
theorem refine_box_antitone (E : ComplexEnclosure z) : Antitone fun n => (E.refine n).box :=
  fun m n hmn => by
    simp only [box_def]
    exact NonemptyInterval.reProdIm_Icc_ratCast_subset (E.re.refine_interval_antitone hmn)
      (E.im.refine_interval_antitone hmn)

/-- The refinement at level `n` has width `2⁻ⁿ` times the width of the enclosure. -/
@[simp]
theorem width_refine (E : ComplexEnclosure z) (n : ℕ) :
    (E.refine n).width = E.width / 2 ^ n := by
  simp [width_def, max_div_div_right]

/-- Each bisection gains one bit of absolute precision. -/
theorem HasPrecision.refine {E : ComplexEnclosure z} {k : ℕ} (h : E.HasPrecision k) (n : ℕ) :
    (E.refine n).HasPrecision (k + n) :=
  ⟨h.1.refine n, h.2.refine n⟩

/-- Every complex enclosure has refinements of every absolute precision. -/
theorem exists_hasPrecision_refine (E : ComplexEnclosure z) (n : ℕ) :
    ∃ m, (E.refine m).HasPrecision n := by
  simpa only [hasPrecision_iff_width_le, width_refine] using
    (exists_div_pow_lt E.width one_lt_two (by positivity : (0 : ℚ) < (2 ^ n)⁻¹)).imp
      fun _ => le_of_lt

/-- The rational upper bound `max (l_R², u_R²) + max (l_I², u_I²)` for `|z|²` read off from a
complex enclosure `([l_R, u_R], [l_I, u_I])`. -/
def normSqBound (E : ComplexEnclosure z) : ℚ :=
  max (E.re.interval.fst ^ 2) (E.re.interval.snd ^ 2) +
    max (E.im.interval.fst ^ 2) (E.im.interval.snd ^ 2)

theorem normSqBound_def (E : ComplexEnclosure z) :
    E.normSqBound = max (E.re.interval.fst ^ 2) (E.re.interval.snd ^ 2) +
      max (E.im.interval.fst ^ 2) (E.im.interval.snd ^ 2) :=
  (rfl)

/-- The square of the modulus of the enclosed number is bounded by the rational number
`max (l_R², u_R²) + max (l_I², u_I²)`. -/
theorem normSq_le_normSqBound (E : ComplexEnclosure z) : normSq z ≤ E.normSqBound := by
  rw [normSq_apply, normSqBound_def]
  push_cast
  -- A real number between `l` and `u` has square at most `max (l², u²)`.
  have key {l u x : ℝ} (hl : l ≤ x) (hu : x ≤ u) : x ^ 2 ≤ max (l ^ 2) (u ^ 2) := by
    rw [← sq_abs x, ← sq_abs l, ← sq_abs u, ← max_pow_of_nonneg (abs_nonneg l) (abs_nonneg u)]
    exact pow_le_pow_left₀ (abs_nonneg x) (abs_le_max_abs_abs hl hu) 2
  have hre := key E.re.fst_le E.re.le_snd
  have him := key E.im.fst_le E.im.le_snd
  nlinarith

/-- A real enclosure of `t` is a complex enclosure of `t`, with imaginary interval `[0, 0]`. -/
def ofReal {t : ℝ} (E : RealEnclosure t) : ComplexEnclosure t where
  re := ⟨E.interval, by simpa using E.fst_le, by simpa using E.le_snd⟩
  im := ⟨NonemptyInterval.pure 0, by simp, by simp⟩

@[simp]
theorem ofReal_re_interval {t : ℝ} (E : RealEnclosure t) :
    (ofReal E).re.interval = E.interval :=
  (rfl)

@[simp]
theorem ofReal_im_interval {t : ℝ} (E : RealEnclosure t) :
    (ofReal E).im.interval = NonemptyInterval.pure 0 :=
  (rfl)

/-- Passing a real enclosure to a complex one does not change its absolute precision. -/
@[simp]
theorem hasPrecision_ofReal_iff {t : ℝ} (E : RealEnclosure t) (n : ℕ) :
    (ofReal E).HasPrecision n ↔ E.HasPrecision n := by
  simp [hasPrecision_iff, RealEnclosure.hasPrecision_iff]

/-- A complex enclosure whose imaginary interval is `[0, 0]` encloses a real number: `z` is the
real number `Re z`, which is enclosed by the real interval of the enclosure. -/
theorem re_eq_self_of_im_interval_eq_pure_zero (E : ComplexEnclosure z)
    (h : E.im.interval = NonemptyInterval.pure 0) : (z.re : ℂ) = z := by
  have him := E.im.eq_of_interval_eq_pure h
  simpa [him] using re_add_im z

end ComplexEnclosure

/-! ### Examples

The following checks illustrate the conventions: a zero-width box at `i` does not contain the
point with the coordinates swapped, the decimal interval `[141/100, 142/100]` encloses `√2` with
absolute precision `6` but not `7`, and a common enclosure of two numbers does not prove that they
are equal. -/

example : ComplexEnclosure Complex.I where
  re := ⟨NonemptyInterval.pure 0, by simp, by simp⟩
  im := ⟨NonemptyInterval.pure 1, by simp, by simp⟩

example (E : ComplexEnclosure Complex.I) (h : E.re.interval = NonemptyInterval.pure 0)
    (h' : E.im.interval = NonemptyInterval.pure 1) : (1 : ℂ) ∉ E.box ∧ (0 : ℂ) ∉ E.box := by
  simp [ComplexEnclosure.box_def, Complex.mem_reProdIm, h, h']

/-- The decimal enclosure `[141/100, 142/100]` of `√2`. -/
private def sqrtTwoEnclosure : RealEnclosure (Real.sqrt 2) where
  interval := ⟨(141 / 100, 142 / 100), by norm_num⟩
  fst_le := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  le_snd := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num

example : sqrtTwoEnclosure.HasPrecision 6 ∧ ¬ sqrtTwoEnclosure.HasPrecision 7 := by
  simp only [RealEnclosure.hasPrecision_iff, sqrtTwoEnclosure, NonemptyInterval.length]
  norm_num

-- The interval `[1, 2]` encloses both `1` and `2`.
example : ∃ (E : RealEnclosure 1) (F : RealEnclosure 2), E.interval = F.interval :=
  ⟨⟨⟨(1, 2), by norm_num⟩, by norm_num, by norm_num⟩,
    ⟨⟨(1, 2), by norm_num⟩, by norm_num, by norm_num⟩, rfl⟩

end TauCeti
