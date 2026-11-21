/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.BinaryQuadraticForm.Reduction
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.SumIntegralComparisons
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mertens' count of positive definite binary quadratic forms

Summed over `0 < D < X`, the number of `SL(2, ℤ)`-classes of positive definite integral binary
quadratic forms `a x² + b x y + c y²` of discriminant `b² - 4 a c = -D` is
`(π / 18) X^{3/2} + O(X log X)` (Mertens, 1874). Every class is counted once, whether or not the
form is primitive, and without the stabiliser weights `1/2` and `1/3` of the Hurwitz class number.
The constant is `1/6` times the hyperbolic area `π / 3` of `SL(2, ℤ) \ ℍ`.

Each class contains exactly one reduced form
(`TauCeti.BinaryQuadraticForm.nat_card_orbitRel_quotient_posDef`), so the count is that of the
integer triples `(a, b, c)` with `|b| ≤ a ≤ c`, `4 a c - b² < X` and the boundary condition of
`TauCeti.IsReducedForm`. Dropping the boundary condition adds the triples with `b = -a`, or with
`b < 0` and `c = a`, which number `O(X log X)`. The remaining triples are counted by slicing:
for fixed `a` and `b` the `c` range over an interval of length `max ((X + b²) / (4 a) - a) 0` up
to one; the sum of these lengths over `|b| ≤ a` is twice their integral over `b ∈ [0, a]` up to
`X / (2 a)`; substituting `b = 2 a u` turns this into `∫₀^{1/2} max (X - 4 (1 - u²) a²) 0 du`;
and, for each `u`, the sum of `max (X - 4 (1 - u²) a²) 0` over `a ≥ 1` is the integral over
`a ≥ 0`, namely `X^{3/2} / (3 √(1 - u²))`, up to `X`. Finally
`∫₀^{1/2} (1 - u²)^{-1/2} du = arcsin (1/2) = π / 6`.

## Main results

* `TauCeti.BinaryQuadraticForm.abs_sum_card_reducedForms_sub_le`: the reduced forms of
  discriminant `-D`, over `0 < D < X`, number `(π / 18) X^{3/2}` up to `48 X log X`, for `X ≥ 2`.
* `TauCeti.BinaryQuadraticForm.abs_finsum_card_orbitRel_quotient_posDef_sub_le`: the same for the
  `SL(2, ℤ)`-classes of positive definite forms of discriminant `-D`.

## References

* F. Mertens, *Über einige asymptotische Gesetze der Zahlentheorie*, J. Reine Angew. Math. **77**
  (1874), 289–338.
* M. Bhargava and A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. **181** (2015), 191–242,
  Theorem 1.4(a).
-/

public section

open Finset MulAction Real intervalIntegral
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

/-! ### The volume computation -/

/-- `∫₀^R max (X - k a²) 0 da = (2/3) X √(X / k)` once `R` passes the zero `√(X / k)`. -/
private theorem integral_max_sub_mul_sq {X k R : ℝ} (hX : 0 ≤ X) (hk : 0 < k)
    (hR : √(X / k) ≤ R) :
    ∫ a in (0 : ℝ)..R, max (X - k * a ^ 2) 0 = 2 / 3 * X * √(X / k) := by
  set r := √(X / k) with hr
  have hr0 : 0 ≤ r := sqrt_nonneg _
  have hkr : k * r ^ 2 = X := by
    rw [hr, sq_sqrt (div_nonneg hX hk.le)]
    field_simp
  have hcont : Continuous fun a : ℝ ↦ max (X - k * a ^ 2) 0 := by fun_prop
  rw [← integral_add_adjacent_intervals (b := r) (hcont.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _)]
  have h1 : ∫ a in (0 : ℝ)..r, max (X - k * a ^ 2) 0 = ∫ a in (0 : ℝ)..r, (X - k * a ^ 2) := by
    refine integral_congr fun a ha ↦ ?_
    rw [Set.uIcc_of_le hr0] at ha
    have : a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha.1 ha.2 2
    exact max_eq_left (by nlinarith)
  have h2 : ∫ a in r..R, max (X - k * a ^ 2) 0 = ∫ _ in r..R, (0 : ℝ) := by
    refine integral_congr fun a ha ↦ ?_
    rw [Set.uIcc_of_le hR] at ha
    have : r ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hr0 ha.1 2
    exact max_eq_right (by nlinarith)
  rw [h1, h2, integral_zero, add_zero, integral_sub intervalIntegrable_const
    ((continuous_pow 2).intervalIntegrable _ _ |>.const_mul k), integral_const, integral_const_mul,
    integral_pow]
  simp only [sub_zero, smul_eq_mul]
  linear_combination (-r / 3) * hkr

/-- The sum `∑_{a=1}^n max (X - k a²) 0` of an antitone function differs from its integral over
`[0, n]` by at most `X`. -/
private theorem abs_sum_max_sub_mul_sq_sub_integral_le {X k : ℝ} (hX : 0 ≤ X) (hk : 0 ≤ k)
    (n : ℕ) :
    |∑ i ∈ range n, max (X - k * ((i + 1 : ℕ) : ℝ) ^ 2) 0 -
      ∫ a in (0 : ℝ)..n, max (X - k * a ^ 2) 0| ≤ X := by
  have hanti : AntitoneOn (fun a : ℝ ↦ max (X - k * a ^ 2) 0) (Set.Icc 0 (0 + n)) :=
    fun x hx y _ hxy ↦ by
      have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.1 hxy 2
      dsimp only
      gcongr
  have h := hanti.abs_sum_range_sub_integral_le
  simp only [zero_add] at h
  exact h.trans (by simp [hX])

/-- `∫₀^{1/2} (1 - u²)^{-1/2} du = π / 6`. -/
private theorem integral_one_div_sqrt_one_sub_sq_zero_half :
    ∫ u in (0 : ℝ)..1 / 2, 1 / √(1 - u ^ 2) = π / 6 := by
  rw [integral_one_div_sqrt_one_sub_sq, arcsin_zero, sub_zero, ← sin_pi_div_six,
    arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])]

/-! ### Summing over the middle coefficient -/

/-- For `a = n ≥ 1`, the sum over `|b| ≤ a` of `max ((X + b²) / (4 a) - a) 0`, the real length of
the range of `c`, is twice the integral over `[0, a]` up to an error of at most `X / (2 a)`. -/
private theorem abs_sum_Icc_sub_two_mul_integral_le {X : ℝ} (hX : 0 ≤ X) {n : ℕ} (hn : 0 < n) :
    |∑ b ∈ Icc (-(n : ℤ)) n, max ((X + (b : ℝ) ^ 2) / (4 * n) - n) 0 -
      2 * ∫ t in (0 : ℝ)..n, max ((X + t ^ 2) / (4 * n) - n) 0| ≤ X / (2 * n) := by
  set g : ℝ → ℝ := fun t ↦ max ((X + t ^ 2) / (4 * n) - n) 0 with hg
  have hmono : MonotoneOn g (Set.Icc 0 (0 + n)) := fun x hx y _ hxy ↦ by
    have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.1 hxy 2
    simp only [hg]
    gcongr
  have h := hmono.abs_sum_range_sub_integral_le
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at h
  -- `g` is even, so the sum over `[-n, n]` is `g 0` plus twice the sum over `[1, n]`
  have hsum : ∑ b ∈ Icc (-(n : ℤ)) n, g b = g 0 + 2 * ∑ i ∈ range n, g ((i : ℝ) + 1) := by
    have h := sum_Icc_eq_add_sum_range (fun b : ℤ ↦ g b) n n
    have heven : ∀ j : ℕ, g ((-(j : ℤ) : ℤ) : ℝ) = g j := fun j ↦ by simp [hg]
    simp only [heven, sum_range_succ', Int.cast_natCast, Nat.cast_add, Nat.cast_one,
      Int.cast_zero, Nat.cast_zero] at h
    linarith
  have hg0 : 0 ≤ g 0 := le_max_right _ _
  have hgn : g n ≤ X / (4 * n) := by
    refine max_le ?_ (by positivity)
    rw [div_sub' (by positivity)]
    gcongr
    nlinarith
  have key : |∑ b ∈ Icc (-(n : ℤ)) n, g b - 2 * ∫ t in (0 : ℝ)..n, g t| ≤ X / (2 * n) := by
    rw [hsum, abs_le]
    rw [abs_le] at h
    have : X / (2 * n) = 2 * (X / (4 * n)) := by field_simp; ring
    constructor <;> linarith
  simpa only [hg] using key

/-! ### The forms in a box -/

section Box

variable (X : ℝ)

/-- The integral forms `⟨a, b, c⟩` with `1 ≤ a ≤ ⌈√X⌉₊`, `|b| ≤ a ≤ c` and `4 a c - b² < X`, listed
by `a = i + 1`, then `b`, then `c`. -/
private noncomputable def boxForms : Finset (BinaryQuadraticForm ℤ) :=
  (range ⌈√X⌉₊).biUnion fun i ↦ (Icc (-((i + 1 : ℕ) : ℤ)) (i + 1 : ℕ)).biUnion fun b ↦
    (Ico ((i + 1 : ℕ) : ℤ) ⌈(X + (b : ℝ) ^ 2) / (4 * (i + 1 : ℕ))⌉).image
      fun c ↦ ⟨(i + 1 : ℕ), b, c⟩

/-- A form lies in `boxForms X` exactly when `0 < a`, `|b| ≤ a ≤ c` and `4 a c - b² < X`: the
bound `a ≤ ⌈√X⌉₊` follows from `3 a² ≤ 4 a c - b²`. -/
private theorem mem_boxForms {f : BinaryQuadraticForm ℤ} :
    f ∈ boxForms X ↔
      0 < f.a ∧ |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ ((4 * f.a * f.c - f.b ^ 2 : ℤ) : ℝ) < X := by
  simp only [boxForms, mem_biUnion, mem_range, mem_Icc, mem_Ico, mem_image]
  constructor
  · rintro ⟨i, -, b, ⟨hb₁, hb₂⟩, c, ⟨hc₁, hc₂⟩, rfl⟩
    dsimp only
    have hc := Int.lt_ceil.1 hc₂
    rw [lt_div_iff₀ (by positivity)] at hc
    refine ⟨by omega, abs_le.2 ⟨hb₁, hb₂⟩, hc₁, ?_⟩
    push_cast at hc ⊢
    linarith
  · obtain ⟨a, b, c⟩ := f
    dsimp only
    rintro ⟨ha, hb, hac, hX⟩
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, a = ((i + 1 : ℕ) : ℤ) := ⟨(a - 1).toNat, by omega⟩
    have hbb : b ^ 2 ≤ ((i + 1 : ℕ) : ℤ) ^ 2 := sq_le_sq' (abs_le.1 hb).1 (abs_le.1 hb).2
    have h3 : 3 * ((i + 1 : ℕ) : ℤ) ^ 2 ≤ 4 * ((i + 1 : ℕ) : ℤ) * c - b ^ 2 := by nlinarith
    have h3' : 3 * ((i + 1 : ℕ) : ℝ) ^ 2 < X := by
      exact_mod_cast (Int.cast_le.2 h3).trans_lt hX
    have hlt : ((i + 1 : ℕ) : ℝ) < √X := (lt_sqrt (by positivity)).2 (by nlinarith)
    have hA : i + 1 < ⌈√X⌉₊ := by exact_mod_cast hlt.trans_le (Nat.le_ceil _)
    refine ⟨i, by omega, b, abs_le.1 hb, c, ⟨hac, Int.lt_ceil.2 ?_⟩, rfl⟩
    rw [lt_div_iff₀ (by positivity)]
    push_cast at hX ⊢
    linarith

/-- The forms of `boxForms X` satisfying `q`, counted column by column. -/
private theorem card_filter_boxForms (q : BinaryQuadraticForm ℤ → Prop) [DecidablePred q] :
    #((boxForms X).filter q) = ∑ i ∈ range ⌈√X⌉₊, ∑ b ∈ Icc (-((i + 1 : ℕ) : ℤ)) (i + 1 : ℕ),
      #((Ico ((i + 1 : ℕ) : ℤ) ⌈(X + (b : ℝ) ^ 2) / (4 * (i + 1 : ℕ))⌉).filter
        fun c ↦ q ⟨(i + 1 : ℕ), b, c⟩) := by
  rw [boxForms, filter_biUnion, card_biUnion]
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [filter_biUnion, card_biUnion]
    · refine sum_congr rfl fun b _ ↦ ?_
      rw [filter_image, card_image_of_injective _ fun c c' h ↦ by simpa using h]
    · intro b _ b' _ hbb'
      refine disjoint_filter_filter (disjoint_left.2 fun f hf hf' ↦ hbb' ?_)
      simp only [mem_image] at hf hf'
      obtain ⟨c, -, rfl⟩ := hf
      obtain ⟨c', -, h⟩ := hf'
      simp only [BinaryQuadraticForm.mk.injEq] at h
      exact h.2.1.symm
  · intro i _ j _ hij
    refine disjoint_filter_filter (disjoint_left.2 fun f hf hf' ↦ hij ?_)
    simp only [mem_biUnion, mem_image] at hf hf'
    obtain ⟨b, -, c, -, rfl⟩ := hf
    obtain ⟨b', -, c', -, h⟩ := hf'
    simp only [BinaryQuadraticForm.mk.injEq] at h
    omega

/-- The reduced forms of discriminant `-D`, over the `D < X`, are the reduced forms of
`boxForms X`. -/
private theorem sum_card_reducedForms_eq_card_filter_boxForms :
    ∑ D ∈ range ⌈X⌉₊, #(reducedForms D) = #((boxForms X).filter IsReducedForm) := by
  have hD0 {D : ℕ} {f : BinaryQuadraticForm ℤ} (hf : f ∈ reducedForms D) : D ≠ 0 := by
    rintro rfl
    simp at hf
  rw [← card_biUnion fun D _ D' _ h ↦ disjoint_left.2 fun f hf hf' ↦ h ?_]
  · congr 1
    ext ⟨a, b, c⟩
    simp only [mem_biUnion, mem_range, mem_filter, mem_boxForms]
    constructor
    · rintro ⟨D, hD, hf⟩
      obtain ⟨hd, hr⟩ := (mem_reducedForms (hD0 hf)).1 hf
      simp only [BinaryQuadraticForm.discrim_def, discrim] at hd
      refine ⟨⟨a_pos_of_mem_reducedForms hf, hr.1, hr.2.1, ?_⟩, hr⟩
      rw [show 4 * a * c - b ^ 2 = D by linear_combination -hd]
      exact_mod_cast Nat.lt_ceil.1 hD
    · rintro ⟨⟨ha, hb, hac, hX⟩, hr⟩
      have hbb : b ^ 2 ≤ a ^ 2 := sq_le_sq' (abs_le.1 hb).1 (abs_le.1 hb).2
      have hpos : 0 < 4 * a * c - b ^ 2 := by nlinarith
      refine ⟨(4 * a * c - b ^ 2).toNat, Nat.lt_ceil.2 ?_, (mem_reducedForms (by omega)).2
        ⟨?_, hr⟩⟩
      · rwa [← Int.cast_natCast, Int.toNat_of_nonneg hpos.le]
      · simp only [BinaryQuadraticForm.discrim_def, discrim]
        omega
  · have h := (mem_reducedForms (hD0 hf)).1 hf
    have h' := (mem_reducedForms (hD0 hf')).1 hf'
    exact_mod_cast neg_inj.1 (h.1.symm.trans h'.1)

/-- In a column `a`, `|b| ≤ a`, the forms `⟨a, b, c⟩` with `a ≤ c` that are not reduced are those
with `b = -a`, and the form with `c = a` if `b < 0`. -/
private theorem card_filter_not_isReducedForm_le {a b : ℤ} (hb : |b| ≤ a) (y : ℝ) :
    #((Ico a ⌈y⌉).filter fun c ↦ ¬ IsReducedForm ⟨a, b, c⟩) ≤
      (if b = -a then #(Ico a ⌈y⌉) else 0) + 1 := by
  calc #((Ico a ⌈y⌉).filter fun c ↦ ¬ IsReducedForm ⟨a, b, c⟩)
      ≤ #((if b = -a then Ico a ⌈y⌉ else ∅) ∪ {a}) := card_le_card fun c hc ↦ ?_
    _ ≤ _ := (card_union_le _ _).trans (by split_ifs <;> simp)
  obtain ⟨hc, hn⟩ := mem_filter.1 hc
  rw [mem_union, mem_singleton]
  split_ifs with h
  · exact Or.inl hc
  refine Or.inr (by_contra fun hca ↦ hn ⟨hb, (mem_Ico.1 hc).1, fun h' ↦ ?_⟩)
  rcases h' with h' | h'
  · simp only at h' ⊢
    rcases abs_cases b with h₁ | h₁ <;> omega
  · exact absurd h'.symm hca

/-- In the column `a = n`, at most `#[n, y(-n)) + 2 n + 1` forms `⟨n, b, c⟩`, `|b| ≤ n ≤ c < y(b)`,
are not reduced. -/
private theorem sum_card_filter_not_isReducedForm_le (n : ℕ) (y : ℤ → ℝ) :
    ∑ b ∈ Icc (-(n : ℤ)) n, #((Ico (n : ℤ) ⌈y b⌉).filter fun c ↦ ¬ IsReducedForm ⟨n, b, c⟩) ≤
      #(Ico (n : ℤ) ⌈y (-n)⌉) + (2 * n + 1) :=
  calc _ ≤ ∑ b ∈ Icc (-(n : ℤ)) n, ((if b = -n then #(Ico (n : ℤ) ⌈y b⌉) else 0) + 1) :=
        sum_le_sum fun b hb ↦ card_filter_not_isReducedForm_le (abs_le.2 (mem_Icc.1 hb)) _
    _ = _ := by
      have hmem : -(n : ℤ) ∈ Icc (-(n : ℤ)) n := by simp
      rw [sum_add_distrib, sum_ite_eq', sum_const, Int.card_Icc, smul_eq_mul, mul_one]
      simp only [hmem, reduceIte]
      congr 1
      omega

/-- The reduced forms of `boxForms X` fall short of all its forms by at most
`∑_{1 ≤ a ≤ ⌈√X⌉₊} (X / (4 a) + 2 a + 2)`. -/
private theorem card_boxForms_sub_card_filter_isReducedForm_le (hX : 0 ≤ X) :
    (#(boxForms X) : ℝ) - #((boxForms X).filter IsReducedForm) ≤
      ∑ i ∈ range ⌈√X⌉₊, (X / (4 * (i + 1 : ℕ)) + 1 + (2 * (i + 1 : ℕ) + 1)) := by
  rw [← card_filter_add_card_filter_not IsReducedForm, Nat.cast_add, add_sub_cancel_left,
    card_filter_boxForms, Nat.cast_sum]
  refine sum_le_sum fun i _ ↦ ?_
  set n := i + 1
  have hn : (0 : ℝ) < n := by positivity
  refine (Nat.cast_le.2 (sum_card_filter_not_isReducedForm_le n
    fun b ↦ (X + (b : ℝ) ^ 2) / (4 * n))).trans ?_
  push_cast
  gcongr
  -- the column `b = -n` has at most `(X + n²) / (4 n) - n + 1 ≤ X / (4 n) + 1` entries
  have h := (abs_le.1 (abs_card_Ico_ceil_sub_le n ((X + (-(n : ℝ)) ^ 2) / (4 * n)))).2
  have hmax : max ((X + (-(n : ℝ)) ^ 2) / (4 * n) - n) 0 ≤ X / (4 * n) := by
    refine max_le ?_ (by positivity)
    have : (X + (-(n : ℝ)) ^ 2) / (4 * n) - n = X / (4 * n) - 3 * n / 4 := by
      field_simp
      ring
    linarith
  push_cast at h
  linarith

/-- The number of forms in `boxForms X` is `∑_{a, |b| ≤ a} max ((X + b²) / (4 a) - a) 0`, the
lengths of the ranges `[a, (X + b²) / (4 a))` of `c`, up to one for each pair `(a, b)`, so up to
`∑_{1 ≤ a ≤ ⌈√X⌉₊} (2 a + 1)`. -/
private theorem abs_card_boxForms_sub_le :
    |(#(boxForms X) : ℝ) - ∑ i ∈ range ⌈√X⌉₊, ∑ b ∈ Icc (-((i + 1 : ℕ) : ℤ)) (i + 1 : ℕ),
      max ((X + (b : ℝ) ^ 2) / (4 * (i + 1 : ℕ)) - (i + 1 : ℕ)) 0| ≤
        ∑ i ∈ range ⌈√X⌉₊, (2 * (i + 1 : ℕ) + 1 : ℝ) := by
  have h := card_filter_boxForms X fun _ ↦ True
  simp only [filter_true] at h
  rw [h, Nat.cast_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
  rw [Nat.cast_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun b _ ↦ ?_).trans_eq (b := ∑ _ ∈
    Icc (-((i + 1 : ℕ) : ℤ)) (i + 1 : ℕ), (1 : ℝ)) ?_)
  · simpa using abs_card_Ico_ceil_sub_le ((i + 1 : ℕ) : ℤ) ((X + (b : ℝ) ^ 2) / (4 * (i + 1 : ℕ)))
  · rw [sum_const, Int.card_Icc, nsmul_one]
    norm_cast
    omega

/-- Substituting `t = 2 a u`: twice the integral over `[0, a]` of the length of the range of `c` is
`∫₀^{1/2} max (X - 4 (1 - u²) a²) 0 du`. -/
private theorem two_mul_integral_eq {a : ℝ} (ha : 0 < a) :
    2 * ∫ t in (0 : ℝ)..a, max ((X + t ^ 2) / (4 * a) - a) 0 =
      ∫ u in (0 : ℝ)..1 / 2, max (X - 4 * (1 - u ^ 2) * a ^ 2) 0 := by
  have h := integral_comp_mul_left (fun t ↦ max ((X + t ^ 2) / (4 * a) - a) 0) (a := 0)
    (b := 1 / 2) (c := 2 * a) (by positivity)
  rw [mul_zero, show 2 * a * (1 / 2) = a by ring, smul_eq_mul] at h
  have hc : ∀ u : ℝ, max (X - 4 * (1 - u ^ 2) * a ^ 2) 0 =
      4 * a * max ((X + (2 * a * u) ^ 2) / (4 * a) - a) 0 := fun u ↦ by
    rw [mul_max_of_nonneg _ _ (by positivity), mul_zero]
    congr 1
    field_simp
    ring
  simp_rw [hc]
  rw [intervalIntegral.integral_const_mul, h]
  field_simp
  ring

/-- Summing the columns `a ≤ ⌈√X⌉₊` under the integral: for each `u ∈ [0, 1/2]` the sum over `a` is
`∫₀^∞ max (X - 4 (1 - u²) a²) 0 da = X^{3/2} / (3 √(1 - u²))` up to `X`, and
`∫₀^{1/2} (1 - u²)^{-1/2} du = π / 6`. -/
private theorem abs_integral_sum_sub_le (hX : 0 ≤ X) :
    |(∫ u in (0 : ℝ)..1 / 2, ∑ i ∈ range ⌈√X⌉₊,
      max (X - 4 * (1 - u ^ 2) * ((i + 1 : ℕ) : ℝ) ^ 2) 0) - π / 18 * (X * √X)| ≤ X / 2 := by
  have hG : ∫ u in (0 : ℝ)..1 / 2, X * √X / 3 * (1 / √(1 - u ^ 2)) = π / 18 * (X * √X) := by
    rw [intervalIntegral.integral_const_mul, integral_one_div_sqrt_one_sub_sq_zero_half]
    ring
  rw [← hG, ← integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (integrable_one_div_sqrt_one_sub_sq.intervalIntegrable.const_mul _)]
  rw [← Real.norm_eq_abs]
  refine le_of_le_of_eq (norm_integral_le_of_norm_le_const (C := X) fun u hu ↦ ?_)
    (by rw [sub_zero, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring)
  rw [Set.uIoc_of_le (by norm_num)] at hu
  have hu1 : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have hk : 0 < 4 * (1 - u ^ 2) := by positivity
  have hsum := abs_sum_max_sub_mul_sq_sub_integral_le hX hk.le ⌈√X⌉₊
  have hR : √(X / (4 * (1 - u ^ 2))) ≤ ⌈√X⌉₊ :=
    (sqrt_le_sqrt (div_le_self hX (by nlinarith [hu.1, hu.2]))).trans (Nat.le_ceil _)
  rw [integral_max_sub_mul_sq hX hk hR] at hsum
  have hsqrt : √(X / (4 * (1 - u ^ 2))) = √X / (2 * √(1 - u ^ 2)) := by
    rw [sqrt_div' _ hk.le, sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      sqrt_sq (by norm_num)]
  have hval : 2 / 3 * X * (√X / (2 * √(1 - u ^ 2))) = X * √X / 3 * (1 / √(1 - u ^ 2)) := by
    field_simp
  rw [hsqrt, hval] at hsum
  rwa [Real.norm_eq_abs]

end Box

/-! ### The count -/

/-- The accumulated errors are `O(X log X)`: at most `48 X log X` for `X ≥ 2`. -/
private theorem error_le {X : ℝ} (hX : 2 ≤ X) :
    ∑ i ∈ range ⌈√X⌉₊, (X / (4 * (i + 1 : ℕ)) + 1 + (2 * (i + 1 : ℕ) + 1)) +
      ∑ i ∈ range ⌈√X⌉₊, (2 * (i + 1 : ℕ) + 1 : ℝ) + ∑ i ∈ range ⌈√X⌉₊, X / (2 * (i + 1 : ℕ)) +
        X / 2 ≤ 48 * X * log X := by
  set A := ⌈√X⌉₊
  have hX0 : 0 < X := by linarith
  have hsX : 1 ≤ √X := one_le_sqrt.2 (by linarith)
  have hA : (A : ℝ) ≤ 2 * √X := (Nat.ceil_lt_add_one (sqrt_nonneg X)).le.trans (by linarith)
  have hA1 : 1 ≤ A := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hA2 : (A : ℝ) * A ≤ 4 * X := by nlinarith [sq_sqrt hX0.le, Nat.cast_nonneg (α := ℝ) A]
  -- the harmonic sum: `∑_{a ≤ A} 1 / a ≤ 1 + log A ≤ 1 + log 2 + (log X) / 2`
  have hH : ∑ i ∈ range A, ((i + 1 : ℕ) : ℝ)⁻¹ ≤ 1 + log 2 + log X / 2 := by
    have h := harmonic_le_one_add_log A
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    refine h.trans ?_
    have := log_le_log (by exact_mod_cast hA1) hA
    rw [log_mul (by norm_num) (by positivity), log_sqrt hX0.le] at this
    linarith
  -- the other terms: `∑_{a ≤ A} (4 a + 3) ≤ 7 A²`
  have hlin : ∑ i ∈ range A, (4 * ((i + 1 : ℕ) : ℝ) + 3) ≤ 7 * (A * A) := by
    refine (sum_le_card_nsmul (range A) _ (7 * (A : ℝ)) fun i hi ↦ ?_).trans_eq
      (by rw [card_range, nsmul_eq_mul]; ring)
    have : ((i + 1 : ℕ) : ℝ) ≤ A := by exact_mod_cast mem_range.1 hi
    have : (1 : ℝ) ≤ A := by exact_mod_cast hA1
    linarith
  have hsum : ∑ i ∈ range A, (X / (4 * (i + 1 : ℕ)) + 1 + (2 * (i + 1 : ℕ) + 1)) +
      ∑ i ∈ range A, (2 * (i + 1 : ℕ) + 1 : ℝ) + ∑ i ∈ range A, X / (2 * (i + 1 : ℕ)) =
      3 * X / 4 * ∑ i ∈ range A, ((i + 1 : ℕ) : ℝ)⁻¹ +
        ∑ i ∈ range A, (4 * ((i + 1 : ℕ) : ℝ) + 3) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    field_simp
    ring
  have hlog : 2 / 3 ≤ log X :=
    (by linarith [log_two_gt_d9] : (2 / 3 : ℝ) ≤ log 2).trans (log_le_log (by norm_num) hX)
  have hlog2 : log 2 ≤ 1 := by linarith [log_two_lt_d9]
  rw [hsum]
  have : 3 * X / 4 * ∑ i ∈ range A, ((i + 1 : ℕ) : ℝ)⁻¹ ≤ 3 * X / 4 * (2 + log X / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hlog hX0.le]

/-- **Mertens' count of reduced forms**: the reduced positive definite integral binary quadratic
forms `a x² + b x y + c y²` of discriminant `-D`, over the `0 < D < X`, number
`(π / 18) X^{3/2} + O(X log X)`; explicitly, the error is at most `48 X log X` for `X ≥ 2`. -/
theorem abs_sum_card_reducedForms_sub_le {X : ℝ} (hX : 2 ≤ X) :
    |((∑ D ∈ range ⌈X⌉₊, #(reducedForms D) : ℕ) : ℝ) - π / 18 * X ^ (3 / 2 : ℝ)| ≤
      48 * X * log X := by
  have hX0 : 0 ≤ X := by linarith
  have h1 := card_boxForms_sub_card_filter_isReducedForm_le X hX0
  have h1' : (#((boxForms X).filter IsReducedForm) : ℝ) ≤ #(boxForms X) := by
    exact_mod_cast card_filter_le _ _
  have h2 := abs_card_boxForms_sub_le X
  -- comparing each column sum over `b` with an integral, then substituting
  have h3 : |∑ i ∈ range ⌈√X⌉₊, ∑ b ∈ Icc (-((i + 1 : ℕ) : ℤ)) (i + 1 : ℕ),
      max ((X + (b : ℝ) ^ 2) / (4 * (i + 1 : ℕ)) - (i + 1 : ℕ)) 0 -
      ∫ u in (0 : ℝ)..1 / 2, ∑ i ∈ range ⌈√X⌉₊,
        max (X - 4 * (1 - u ^ 2) * ((i + 1 : ℕ) : ℝ) ^ 2) 0| ≤
      ∑ i ∈ range ⌈√X⌉₊, X / (2 * (i + 1 : ℕ)) := by
    rw [integral_finsetSum fun i _ ↦ Continuous.intervalIntegrable (by fun_prop) _ _,
      ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
    rw [← two_mul_integral_eq X (by positivity)]
    exact abs_sum_Icc_sub_two_mul_integral_le hX0 i.succ_pos
  have h4 := abs_integral_sum_sub_le X hX0
  have hpow : X ^ (3 / 2 : ℝ) = X * √X := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add (by linarith), rpow_one,
      sqrt_eq_rpow]
  have h5 := error_le hX
  rw [sum_card_reducedForms_eq_card_filter_boxForms, hpow]
  rw [abs_le] at h2 h3 h4 ⊢
  constructor <;> linarith

/-- **Mertens' count of classes of positive definite forms**: the number of `SL(2, ℤ)`-classes of
positive definite integral binary quadratic forms of discriminant `-D`, summed over the `0 < D < X`,
is `(π / 18) X^{3/2} + O(X log X)`; explicitly, the error is at most `48 X log X` for `X ≥ 2`.
Every class is counted once, primitive or not, and with no stabiliser weight. -/
theorem abs_finsum_card_orbitRel_quotient_posDef_sub_le {X : ℝ} (hX : 2 ≤ X) :
    |(∑ᶠ D : ℕ+, if (D : ℝ) < X then
        (Nat.card (orbitRel.Quotient SL(2, ℤ) (posDef (D : ℕ))) : ℝ) else 0) -
      π / 18 * X ^ (3 / 2 : ℝ)| ≤ 48 * X * log X := by
  convert abs_sum_card_reducedForms_sub_le hX using 3
  rw [finsum_eq_sum_of_support_subset (s := (range ⌈X⌉₊).preimage PNat.val
    PNat.coe_injective.injOn) _ fun D hD ↦ ?_]
  · rw [Nat.cast_sum, ← sum_preimage PNat.val _ PNat.coe_injective.injOn _ fun n _ hn ↦ ?_]
    · refine sum_congr rfl fun D hD ↦ ?_
      rw [mem_preimage, mem_range, Nat.lt_ceil] at hD
      simp only [hD, reduceIte, nat_card_orbitRel_quotient_posDef]
    · obtain rfl : n = 0 := by_contra fun h ↦ hn ⟨⟨n, Nat.pos_of_ne_zero h⟩, rfl⟩
      simp
  · rw [Function.mem_support, ne_eq, ite_eq_right_iff, not_imp] at hD
    simpa using Nat.lt_ceil.2 hD.1

end TauCeti.BinaryQuadraticForm
