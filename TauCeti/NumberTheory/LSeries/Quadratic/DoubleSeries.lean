/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Reciprocity
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.OddTwist
import TauCeti.NumberTheory.LSeries.RiemannZeta.Basic

/-!
# The quadratic double Dirichlet series

For complex Dirichlet characters `ψ`, `ψ'` of level eight, the quadratic double Dirichlet series is

`Z(s, w; ψ, ψ') = ζ₂(2s + 2w - 1) ∑_d ψ'(d) L₂(s, χ_d ψ) d⁻ʷ`,

where `ζ₂(u) = (1 - 2⁻ᵘ) ζ(u)` is the Riemann zeta function with its Euler factor at `2` removed,
`d` runs over the positive odd integers, and `L₂(s, χ_d ψ) = ∑_n (d / n) ψ(n) n⁻ˢ` is the series
over positive odd `n` of the Jacobi symbol `(d / n)` twisted by `ψ`. No square factor of `d` is
removed, so `(d / n)` vanishes whenever `gcd(d, n) > 1`. Since `ψ` and `ψ'` vanish at even
integers, the sums over odd `n` and `d` are written as ordinary Dirichlet series (`LSeries`) with
the coefficients `n ↦ (d / n) ψ(n)` and `d ↦ ψ'(d) L₂(s, χ_d ψ)`. For odd `d`, the inner series is
the `L`-function of the imprimitive twist `DirichletCharacter.oddQuadraticTwist ψ d` by
`DirichletCharacter.LFunction_oddQuadraticTwist_eq_LSeries`.

The sixteen series, one for each pair `(ψ, ψ')`, are the objects of Blomer's study of the
quadratic double Dirichlet series; their meromorphic continuation to `ℂ²` rests on two functional
equations, under `(s, w) ↦ (w, s)` and under `(s, w) ↦ (1 - s, s + w - 1/2)`. This file proves
the analytic facts on the tube `1 < re s`, `1 < re w` from which that continuation starts: there
the double series converges absolutely as a sum over pairs `(d, n)`, `Z` is holomorphic in
`(s, w)` jointly and bounded on each closed subtube, and the first functional equation holds in
the form

`Z(s, w; ψ, ψ') = ∑_(ρ, ρ') A (ψ, ψ') (ρ, ρ') Z(w, s; ρ, ρ')`,

with the quadratic reciprocity matrix `A = TauCeti.quadraticReciprocityMatrix`: quadratic
reciprocity interchanges the roles of `n` and `d` in the absolutely convergent double sum.

## Main definitions and results

* `DirichletCharacter.quadraticDoubleSeries ψ ψ' (s, w)`: the series `Z(s, w; ψ, ψ')`.
* `DirichletCharacter.hasSum_quadraticDoubleSeriesTerm`: on the tube, the outer Dirichlet series
  is the absolutely convergent sum over pairs `(d, n)` of `ψ'(d) d⁻ʷ (d / n) ψ(n) n⁻ˢ`.
* `DirichletCharacter.norm_quadraticDoubleSeries_le`: `‖Z(s, w)‖ ≤ 2 (Re ζ(σ))³` on
  `σ ≤ re s`, `σ ≤ re w`, for `1 < σ`.
* `DirichletCharacter.differentiableOn_quadraticDoubleSeries`: `Z` is holomorphic on the tube.
* `DirichletCharacter.quadraticDoubleSeries_eq_sum`: the functional equation under
  `(s, w) ↦ (w, s)` on the tube.

## References

V. Blomer, *Subconvexity for a double Dirichlet series*, Compositio Mathematica 147 (2011),
355–374, Introduction, (1), and §3, (29)–(35).
-/

public section

open Complex LSeries Filter Finset TauCeti

namespace DirichletCharacter

/-- The **quadratic double Dirichlet series** of the characters `ψ`, `ψ'` of level eight at
`p = (s, w)`:
`Z(s, w; ψ, ψ') = ζ₂(2s + 2w - 1) ∑_d ψ'(d) L₂(s, χ_d ψ) d⁻ʷ`, with
`ζ₂(u) = (1 - 2⁻ᵘ) ζ(u)` and `L₂(s, χ_d ψ) = ∑_n (d / n) ψ(n) n⁻ˢ` (Jacobi symbol). Both
characters vanish at even integers, so `d` and `n` effectively run over the positive odd integers;
the square factors of `d` are kept. This is the value of the series where it converges, in
particular on `1 < re s`, `1 < re w`; it is not an analytic continuation. -/
noncomputable def quadraticDoubleSeries (ψ ψ' : DirichletCharacter ℂ 8) (p : ℂ × ℂ) : ℂ :=
  (1 - 2 ^ (-(2 * p.1 + 2 * p.2 - 1))) * riemannZeta (2 * p.1 + 2 * p.2 - 1) *
    LSeries (fun d ↦ ψ' d * LSeries (fun n ↦ (jacobiSym d n : ℂ) * ψ n) p.1) p.2

theorem quadraticDoubleSeries_def (ψ ψ' : DirichletCharacter ℂ 8) (p : ℂ × ℂ) :
    quadraticDoubleSeries ψ ψ' p =
      (1 - 2 ^ (-(2 * p.1 + 2 * p.2 - 1))) * riemannZeta (2 * p.1 + 2 * p.2 - 1) *
        LSeries (fun d ↦ ψ' d * LSeries (fun n ↦ (jacobiSym d n : ℂ) * ψ n) p.1) p.2 :=
  (rfl)

/-- The term of the quadratic double Dirichlet series at the pair `x = (d, n)`: it is
`ψ'(d) d⁻ʷ (d / n) ψ(n) n⁻ˢ` for positive `d` and `n`, and zero if `d = 0` or `n = 0`. -/
noncomputable def quadraticDoubleSeriesTerm (ψ ψ' : DirichletCharacter ℂ 8) (p : ℂ × ℂ)
    (x : ℕ × ℕ) : ℂ :=
  term (fun d ↦ ψ' d) p.2 x.1 * term (fun n ↦ (jacobiSym x.1 n : ℂ) * ψ n) p.1 x.2

theorem quadraticDoubleSeriesTerm_def (ψ ψ' : DirichletCharacter ℂ 8) (p : ℂ × ℂ)
    (x : ℕ × ℕ) : quadraticDoubleSeriesTerm ψ ψ' p x =
      term (fun d ↦ ψ' d) p.2 x.1 * term (fun n ↦ (jacobiSym x.1 n : ℂ) * ψ n) p.1 x.2 :=
  (rfl)

/-- The term at a pair of positive integers. -/
theorem quadraticDoubleSeriesTerm_of_ne_zero (ψ ψ' : DirichletCharacter ℂ 8) (p : ℂ × ℂ)
    {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    quadraticDoubleSeriesTerm ψ ψ' p (d, n) =
      ψ' d / (d : ℂ) ^ p.2 * ((jacobiSym d n : ℂ) * ψ n / (n : ℂ) ^ p.1) := by
  rw [quadraticDoubleSeriesTerm_def, term_of_ne_zero hd, term_of_ne_zero hn]

/-- The term vanishes unless both entries of the pair are odd. -/
theorem quadraticDoubleSeriesTerm_eq_zero_of_not_odd (ψ ψ' : DirichletCharacter ℂ 8)
    (p : ℂ × ℂ) {x : ℕ × ℕ} (hx : ¬ (_root_.Odd x.1 ∧ _root_.Odd x.2)) :
    quadraticDoubleSeriesTerm ψ ψ' p x = 0 := by
  obtain ⟨d, n⟩ := x
  rw [not_and_or, Nat.not_odd_iff_even, Nat.not_odd_iff_even] at hx
  rw [quadraticDoubleSeriesTerm_def]
  rcases hx with h | h
  · rw [term_def, ψ'.apply_eq_zero_of_even (by decide) h.natCast]
    simp
  · rw [term_def (fun n ↦ (jacobiSym d n : ℂ) * ψ n), ψ.apply_eq_zero_of_even (by decide) h.natCast]
    simp

/-- On `σ ≤ re s`, `σ ≤ re w`, the term at `(d, n)` is bounded by `d^(-σ) n^(-σ)`, written with
the terms of the Riemann zeta series at `σ`. -/
private theorem norm_quadraticDoubleSeriesTerm_le (ψ ψ' : DirichletCharacter ℂ 8) {σ : ℝ}
    {p : ℂ × ℂ} (hs : σ ≤ p.1.re) (hw : σ ≤ p.2.re) (x : ℕ × ℕ) :
    ‖quadraticDoubleSeriesTerm ψ ψ' p x‖ ≤ ‖term 1 σ x.1‖ * ‖term 1 σ x.2‖ := by
  rw [quadraticDoubleSeriesTerm_def, norm_mul]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _)
  · refine (norm_term_le_of_re_le_re _ (by simpa using hw) _).trans (norm_term_le _ ?_)
    simpa using ψ'.norm_le_one _
  · refine (norm_term_le_of_re_le_re _ (by simpa using hs) _).trans (norm_term_le _ ?_)
    simpa using norm_jacobiSym_mul_le_one ψ _ _

/-- For `1 < σ`, the products of terms of the Riemann zeta series at `σ` are summable over pairs.
-/
private theorem summable_norm_term_one_mul_norm_term_one {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : ℕ × ℕ ↦ ‖term 1 σ x.1‖ * ‖term 1 σ x.2‖ := by
  have h : Summable fun n ↦ ‖term 1 (σ : ℂ) n‖ :=
    (LSeriesSummable_one_iff.mpr (by simpa using hσ)).norm
  exact h.mul_of_nonneg h (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)

/-- On the tube `1 < re s`, `1 < re w`, the terms are absolutely summable over pairs `(d, n)`. -/
theorem summable_norm_quadraticDoubleSeriesTerm (ψ ψ' : DirichletCharacter ℂ 8) {p : ℂ × ℂ}
    (hs : 1 < p.1.re) (hw : 1 < p.2.re) :
    Summable fun x ↦ ‖quadraticDoubleSeriesTerm ψ ψ' p x‖ :=
  (summable_norm_term_one_mul_norm_term_one (lt_min hs hw)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
    (norm_quadraticDoubleSeriesTerm_le ψ ψ' (min_le_left _ _) (min_le_right _ _))

/-- For `1 < re s`, the inner series `L₂(s, χ_d ψ)` converges absolutely, for every `d`. -/
private theorem LSeriesSummable_jacobiSym_mul (ψ : DirichletCharacter ℂ 8) (d : ℤ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (fun n ↦ (jacobiSym d n : ℂ) * ψ n) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ norm_jacobiSym_mul_le_one ψ d n) hs

/-- **The quadratic double Dirichlet series as a sum over pairs.** On the tube `1 < re s`,
`1 < re w`, the outer Dirichlet series `∑_d ψ'(d) L₂(s, χ_d ψ) d⁻ʷ` is the sum over pairs `(d, n)`
of `ψ'(d) d⁻ʷ (d / n) ψ(n) n⁻ˢ`. -/
theorem hasSum_quadraticDoubleSeriesTerm (ψ ψ' : DirichletCharacter ℂ 8) {p : ℂ × ℂ}
    (hs : 1 < p.1.re) (hw : 1 < p.2.re) :
    HasSum (quadraticDoubleSeriesTerm ψ ψ' p)
      (LSeries (fun d ↦ ψ' d * LSeries (fun n ↦ (jacobiSym d n : ℂ) * ψ n) p.1) p.2) := by
  have hsum := (summable_norm_quadraticDoubleSeriesTerm ψ ψ' hs hw).of_norm
  -- Summing first over `n` gives the terms of the outer Dirichlet series.
  have hfib (d : ℕ) : HasSum (fun n ↦ quadraticDoubleSeriesTerm ψ ψ' p (d, n))
      (term (fun d ↦ ψ' d * LSeries (fun n ↦ (jacobiSym d n : ℂ) * ψ n) p.1) p.2 d) := by
    rcases eq_or_ne d 0 with rfl | hd
    · simp [quadraticDoubleSeriesTerm_def]
    · have h := ((LSeriesSummable_jacobiSym_mul ψ d hs).LSeriesHasSum).mul_left
        (term (fun d ↦ ψ' d) p.2 d)
      rw [term_of_ne_zero hd, mul_div_right_comm]
      simpa [quadraticDoubleSeriesTerm_def, term_of_ne_zero hd] using h
  have hL := hsum.hasSum.prod_fiberwise hfib
  rw [LSeries, hL.tsum_eq]
  exact hsum.hasSum

/-- On the tube `1 < re s`, `1 < re w`, the quadratic double Dirichlet series is `ζ₂(2s + 2w - 1)`
times the absolutely convergent sum over pairs `(d, n)` of `ψ'(d) d⁻ʷ (d / n) ψ(n) n⁻ˢ`. -/
theorem quadraticDoubleSeries_eq_mul_tsum (ψ ψ' : DirichletCharacter ℂ 8) {p : ℂ × ℂ}
    (hs : 1 < p.1.re) (hw : 1 < p.2.re) :
    quadraticDoubleSeries ψ ψ' p =
      (1 - 2 ^ (-(2 * p.1 + 2 * p.2 - 1))) * riemannZeta (2 * p.1 + 2 * p.2 - 1) *
        ∑' x, quadraticDoubleSeriesTerm ψ ψ' p x := by
  rw [quadraticDoubleSeries_def, (hasSum_quadraticDoubleSeriesTerm ψ ψ' hs hw).tsum_eq]

/-- **A uniform bound on closed subtubes.** If `1 < σ`, `σ ≤ re s` and `σ ≤ re w`, then
`‖Z(s, w; ψ, ψ')‖ ≤ 2 (Re ζ(σ))³`. -/
theorem norm_quadraticDoubleSeries_le (ψ ψ' : DirichletCharacter ℂ 8) {σ : ℝ} (hσ : 1 < σ)
    {p : ℂ × ℂ} (hs : σ ≤ p.1.re) (hw : σ ≤ p.2.re) :
    ‖quadraticDoubleSeries ψ ψ' p‖ ≤ 2 * (riemannZeta σ).re ^ 3 := by
  have hu : σ ≤ (2 * p.1 + 2 * p.2 - 1).re := by
    simp
    linarith
  -- The three factors: `1 - 2 ^ (-u)`, `ζ(u)` and the sum over pairs.
  have h₁ : ‖1 - (2 : ℂ) ^ (-(2 * p.1 + 2 * p.2 - 1))‖ ≤ 2 := by
    have h2 : ‖(2 : ℂ) ^ (-(2 * p.1 + 2 * p.2 - 1))‖ ≤ 1 := by
      have := norm_natCast_cpow_of_pos two_pos (-(2 * p.1 + 2 * p.2 - 1))
      rw [Nat.cast_ofNat] at this
      rw [this]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by rw [neg_re]; linarith)
    linarith [norm_sub_le (1 : ℂ) ((2 : ℂ) ^ (-(2 * p.1 + 2 * p.2 - 1))), norm_one (α := ℂ)]
  have h₂ : ‖riemannZeta (2 * p.1 + 2 * p.2 - 1)‖ ≤ (riemannZeta σ).re :=
    (norm_riemannZeta_le (by linarith)).trans
      (strictAntiOn_riemannZeta_re.antitoneOn hσ (hσ.trans_le hu) hu)
  have h₃ : ‖∑' x, quadraticDoubleSeriesTerm ψ ψ' p x‖ ≤ (riemannZeta σ).re ^ 2 := by
    rw [sq]
    exact tsum_of_norm_bounded ((hasSum_norm_term_one_riemannZeta_re hσ).mul
      (hasSum_norm_term_one_riemannZeta_re hσ)
      (summable_norm_term_one_mul_norm_term_one hσ)) (norm_quadraticDoubleSeriesTerm_le ψ ψ' hs hw)
  rw [quadraticDoubleSeries_eq_mul_tsum ψ ψ' (hσ.trans_le hs) (hσ.trans_le hw), norm_mul, norm_mul,
    pow_succ', ← mul_assoc]
  have hζ := (one_lt_riemannZeta_re hσ).le
  gcongr

/-- Each term of the double series is an entire function of `(s, w)`. -/
private theorem differentiable_quadraticDoubleSeriesTerm (ψ ψ' : DirichletCharacter ℂ 8)
    (x : ℕ × ℕ) : Differentiable ℂ fun p ↦ quadraticDoubleSeriesTerm ψ ψ' p x := fun p ↦ by
  have h₁ : DifferentiableAt ℂ (fun p : ℂ × ℂ ↦ term (fun d ↦ ψ' d) p.2 x.1) p :=
    (hasDerivAt_term (fun d ↦ ψ' d) x.1 p.2).differentiableAt.comp p differentiableAt_snd
  have h₂ : DifferentiableAt ℂ
      (fun p : ℂ × ℂ ↦ term (fun n ↦ (jacobiSym x.1 n : ℂ) * ψ n) p.1 x.2) p :=
    (hasDerivAt_term (fun n ↦ (jacobiSym x.1 n : ℂ) * ψ n) x.2 p.1).differentiableAt.comp p
      differentiableAt_fst
  simpa only [quadraticDoubleSeriesTerm_def] using h₁.fun_mul h₂

/-- On each tube `σ < re s`, `σ < re w` with `1 < σ`, the sum over pairs is holomorphic, as a
uniform limit of finite sums of entire functions. -/
private theorem differentiableOn_tsum_quadraticDoubleSeriesTerm (ψ ψ' : DirichletCharacter ℂ 8)
    {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ (fun p ↦ ∑' x, quadraticDoubleSeriesTerm ψ ψ' p x)
      {p : ℂ × ℂ | σ < p.1.re ∧ σ < p.2.re} := by
  have hunif := tendstoUniformlyOn_tsum (summable_norm_term_one_mul_norm_term_one hσ)
    (f := fun x p ↦ quadraticDoubleSeriesTerm ψ ψ' p x)
    (s := {p : ℂ × ℂ | σ < p.1.re ∧ σ < p.2.re})
    fun x p hp ↦ norm_quadraticDoubleSeriesTerm_le ψ ψ' hp.1.le hp.2.le x
  refine hunif.differentiableOn (Eventually.of_forall fun t ↦ ?_)
    ((isOpen_re_gt σ).prod (isOpen_re_gt σ))
  exact (Differentiable.fun_sum fun x _ ↦
    differentiable_quadraticDoubleSeriesTerm ψ ψ' x).differentiableOn

/-- **Holomorphy on the tube.** The quadratic double Dirichlet series is jointly holomorphic in
`(s, w)` on `1 < re s`, `1 < re w`. -/
theorem differentiableOn_quadraticDoubleSeries (ψ ψ' : DirichletCharacter ℂ 8) :
    DifferentiableOn ℂ (quadraticDoubleSeries ψ ψ') {p : ℂ × ℂ | 1 < p.1.re ∧ 1 < p.2.re} := by
  intro p₀ hp₀
  -- Work on a smaller tube `σ < re s`, `σ < re w` around `p₀`, with `1 < σ`.
  set σ := (1 + min p₀.1.re p₀.2.re) / 2
  have hm : 1 < min p₀.1.re p₀.2.re := lt_min hp₀.1 hp₀.2
  have hσ : 1 < σ := by simp only [σ]; linarith
  have hσm : σ < min p₀.1.re p₀.2.re := by simp only [σ]; linarith
  set U := {p : ℂ × ℂ | σ < p.1.re ∧ σ < p.2.re}
  have hU : IsOpen U := (isOpen_re_gt σ).prod (isOpen_re_gt σ)
  have hp₀U : p₀ ∈ U := ⟨hσm.trans_le (min_le_left _ _), hσm.trans_le (min_le_right _ _)⟩
  have hUt (p : ℂ × ℂ) (hp : p ∈ U) : 1 < p.1.re ∧ 1 < p.2.re := ⟨hσ.trans hp.1, hσ.trans hp.2⟩
  -- The factor `ζ₂(2s + 2w - 1)` is holomorphic there, since `re (2s + 2w - 1) > 3`.
  have hζ : DifferentiableOn ℂ (fun p : ℂ × ℂ ↦
      (1 - 2 ^ (-(2 * p.1 + 2 * p.2 - 1))) * riemannZeta (2 * p.1 + 2 * p.2 - 1)) U := by
    intro p hp
    have hu : DifferentiableAt ℂ (fun p : ℂ × ℂ ↦ 2 * p.1 + 2 * p.2 - 1) p := by fun_prop
    have hne : 2 * p.1 + 2 * p.2 - 1 ≠ 1 := fun h ↦ by
      have := congrArg re h
      simp at this
      linarith [hUt p hp]
    exact (((differentiableAt_const _).sub (hu.neg.const_cpow (Or.inl two_ne_zero))).mul
      ((differentiableAt_riemannZeta hne).comp p hu)).differentiableWithinAt
  have hd := (hζ.mul (differentiableOn_tsum_quadraticDoubleSeriesTerm ψ ψ' hσ)).congr
    fun p hp ↦ quadraticDoubleSeries_eq_mul_tsum ψ ψ' (hUt p hp).1 (hUt p hp).2
  exact (hd.differentiableAt (hU.mem_nhds hp₀U)).differentiableWithinAt

/-- The reciprocity law for the terms of the double series: the term of `(ψ, ψ')` at `(d, n)` and
`(s, w)` is the combination, with the row `(ψ, ψ')` of the quadratic reciprocity matrix, of the
terms of `(ρ, ρ')` at `(n, d)` and `(w, s)`. -/
theorem quadraticDoubleSeriesTerm_eq_sum (ψ ψ' : DirichletCharacter ℂ 8) (p : ℂ × ℂ)
    (d n : ℕ) :
    quadraticDoubleSeriesTerm ψ ψ' p (d, n) =
      ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8,
        quadraticReciprocityMatrix (ψ, ψ') q * quadraticDoubleSeriesTerm q.1 q.2 p.swap (n, d) := by
  by_cases hodd : _root_.Odd d ∧ _root_.Odd n
  · have hd : d ≠ 0 := hodd.1.pos.ne'
    have hn : n ≠ 0 := hodd.2.pos.ne'
    simp_rw [quadraticDoubleSeriesTerm_of_ne_zero _ _ _ hd hn,
      quadraticDoubleSeriesTerm_of_ne_zero _ _ _ hn hd, Prod.fst_swap, Prod.snd_swap]
    -- Both sides are `(d ^ w * n ^ s)⁻¹` times the two sides of the reciprocity law.
    have h := congrArg (· / ((d : ℂ) ^ p.2 * (n : ℂ) ^ p.1))
      (apply_mul_apply_mul_jacobiSym_eq_sum hodd.2 hodd.1 ψ ψ')
    simp only [sum_div] at h
    convert h using 1
    · ring
    · exact sum_congr rfl fun q _ ↦ by ring
  · rw [quadraticDoubleSeriesTerm_eq_zero_of_not_odd ψ ψ' p hodd]
    refine (sum_eq_zero fun q _ ↦ ?_).symm
    rw [quadraticDoubleSeriesTerm_eq_zero_of_not_odd q.1 q.2 p.swap (by tauto), mul_zero]

/-- **The functional equation under `(s, w) ↦ (w, s)`, on the tube.** For `1 < re s` and
`1 < re w`, `Z(s, w; ψ, ψ') = ∑_(ρ, ρ') A (ψ, ψ') (ρ, ρ') Z(w, s; ρ, ρ')`, where `A` is the
quadratic reciprocity matrix. -/
theorem quadraticDoubleSeries_eq_sum
    (ψ ψ' : DirichletCharacter ℂ 8) {p : ℂ × ℂ} (hs : 1 < p.1.re) (hw : 1 < p.2.re) :
    quadraticDoubleSeries ψ ψ' p =
      ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8,
        quadraticReciprocityMatrix (ψ, ψ') q * quadraticDoubleSeries q.1 q.2 p.swap := by
  have hsum (q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8) :
      Summable (quadraticDoubleSeriesTerm q.1 q.2 p.swap) :=
    (summable_norm_quadraticDoubleSeriesTerm q.1 q.2 hw hs).of_norm
  -- Interchange the roles of `d` and `n` in each of the sixteen double sums.
  have htsum : ∑' x, quadraticDoubleSeriesTerm ψ ψ' p x =
      ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8, quadraticReciprocityMatrix (ψ, ψ') q *
        ∑' x, quadraticDoubleSeriesTerm q.1 q.2 p.swap x := calc
    _ = ∑' x : ℕ × ℕ, ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8,
          quadraticReciprocityMatrix (ψ, ψ') q *
            quadraticDoubleSeriesTerm q.1 q.2 p.swap (Equiv.prodComm ℕ ℕ x) :=
      tsum_congr fun x ↦ quadraticDoubleSeriesTerm_eq_sum ψ ψ' p x.1 x.2
    _ = ∑ q : DirichletCharacter ℂ 8 × DirichletCharacter ℂ 8, ∑' x : ℕ × ℕ,
          quadraticReciprocityMatrix (ψ, ψ') q *
            quadraticDoubleSeriesTerm q.1 q.2 p.swap (Equiv.prodComm ℕ ℕ x) :=
      Summable.tsum_finsetSum fun q _ ↦
        ((Equiv.prodComm ℕ ℕ).summable_iff.mpr (hsum q)).mul_left _
    _ = _ := sum_congr rfl fun q _ ↦ by
      rw [tsum_mul_left, (Equiv.prodComm ℕ ℕ).tsum_eq (quadraticDoubleSeriesTerm q.1 q.2 p.swap)]
  have hζ : 2 * p.swap.1 + 2 * p.swap.2 - 1 = 2 * p.1 + 2 * p.2 - 1 := by
    rw [Prod.fst_swap, Prod.snd_swap]
    ring
  simp_rw [quadraticDoubleSeries_eq_mul_tsum ψ ψ' hs hw,
    quadraticDoubleSeries_eq_mul_tsum _ _ (p := p.swap) hw hs, hζ, htsum, mul_sum]
  exact sum_congr rfl fun q _ ↦ by ring

/-! The coefficient of the outer series at `d = 1` is `L₂(s, ψ)`. -/

example (ψ : DirichletCharacter ℂ 8) (s : ℂ) :
    LSeries (fun n ↦ (jacobiSym (1 : ℕ) n : ℂ) * ψ n) s = LSeries (fun n ↦ ψ n) s := by
  simp [jacobiSym.one_left]

end DirichletCharacter
