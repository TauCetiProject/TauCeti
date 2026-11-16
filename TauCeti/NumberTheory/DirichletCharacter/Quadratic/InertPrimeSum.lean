/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.MulChar.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LegendreSymbol.Basic
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.Chebyshev.PrimeTail
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.FundamentalDiscriminant
import TauCeti.NumberTheory.NumberField.Quadratic.EmbeddingBound
import TauCeti.RingTheory.Polynomial.Resultant.Multiplicity

/-!
# Inert-prime sum bound via the determinant method

For a quadratic Dirichlet character `χ` of level `q ≠ 0` (with values in any commutative ring where
`2 ≠ 0`), Mertens' first theorem bounds `∑_{p ≤ x} log p / p` by `log x + O(1)`. This file proves
that the inert primes — those with `χ(p) = -1` — carry at most three quarters of the Mertens mass
once `x ≥ q ^ 18`:
`∑_{p ≤ x, χ(p) = -1} log p / p ≤ (3 / 4) log x + K`,
with an absolute constant `K` independent of `R`, `q`, `χ`, and `x`.

The proof runs unconditionally for the Jacobi symbol `jacobiSym d p = -1` of any integer `d` with
`|d| ^ 18 ≤ x` (`TauCeti.sum_primesLE_jacobiSym_eq_neg_one_log_div_le`), and transfers to
quadratic characters (`DirichletCharacter.sum_primesLE_eq_neg_one_log_div_le` and
`DirichletCharacter.sum_primesLE_pow_eq_neg_one_log_div_le`) via the squarefree Kronecker
realization of primitive quadratic characters
(`DirichletCharacter.IsPrimitive.exists_squarefree_apply_eq_jacobiSym`).

For a squarefree radicand `d ≠ 1` and `x ≥ max 36 (|d| ^ 18)`, set `R = ⌊x⌋₊`, `S = ⌊R / 18⌋`,
and let `N` be minimal with `R ^ 2 ≤ N ^ 3`. On the `N ^ 2` quadratic grid points
`(x + yω, x - yω)` in `ℤ[√d]` (`0 ≤ x, y < N`), form the `R S` vectors `v_{r, s}` whose
`(x, y, j)`-entry (`0 ≤ j < N`) is `∂_z^j (z ^ r z' ^ s)` evaluated at `(x + yω, x - yω)`.
Embedding each `a + bω ∈ ℤ[√d]` into `ℝ²` via `(a, √|d| b)` produces an integer Gram matrix
`G_ℤ` (unified for both signs of `d`) whose determinant satisfies three bounds:

1. **Positivity (`det G_ℤ > 0`).** Any real linear dependence among the rows yields a nonzero
   bivariate polynomial `F : ℂ[X][X]` of degrees `< R` and `< S` vanishing to order `N` in `z` at
   all `N ^ 2` points `(x + y√d, x - y√d)`. A linear change of variables reduces the zero count of
   any factor to `MvPolynomial.schwartz_zippel_totalDegree`, so
   `Polynomial.mul_card_le_of_forall_iterate_derivative_eval_eq_zero` gives
   `N ^ 3 ≤ N R + N S + 2 R S`, contradicting the parameter choice.
2. **Archimedean upper bound.** Hadamard's inequality (`Matrix.log_det_gram_le`) and the quadratic
   embedding bound (`QuadraticAlgebra.norm_embedding_algebraMap_le`) bound `log (det G_ℤ)` by
   `R S (3 log N + 2 N log R) + R S (R + S) log (2 N √|d|)`.
3. **`p`-adic lower bound.** At every odd prime `p ≤ R` with `(d / p) = -1`, Frobenius in
   `QuadraticAlgebra (ZMod p) d 0` gives `(x + yω) ^ p ≡ x - yω (mod p)`. A unitriangular integer
   change of basis replaces `z ^ r z' ^ s` with `z ^ (r - p h) (z ^ p - z') ^ h z' ^ s` for
   `h = min (r / p) (S - 1 - s)`, whose `z`-derivatives are all divisible by `p ^ h`, yielding
   `p ^ (2 ∑ h) ∣ det G_ℤ`.

Comparing the `p`-adic and archimedean bounds and dividing by `R ^ 2 S` gives main coefficient
`(1 + 1 / 18) (2 / 3 + 1 / 36) = 475 / 648 < 3 / 4`, while the error terms are bounded by
Chebyshev's `θ(R) ≤ (log 4) R` and `TauCeti.sum_log_div_sq_le_of_prime`.

## Main results

* `TauCeti.sum_primesLE_jacobiSym_eq_neg_one_log_div_le`:
  `∑_{p ≤ x, jacobiSym d p = -1} log p / p ≤ (3 / 4) log x + K` for all `d : ℤ` and `x ≥ 1` with
  `|d| ^ 18 ≤ x`.
* `DirichletCharacter.sum_primesLE_eq_neg_one_log_div_le`:
  `∑_{p ≤ x, χ(p) = -1} log p / p ≤ (3 / 4) log x + K` for every quadratic character `χ` of level
  `q ≠ 0` (into any commutative ring with `2 ≠ 0`) and `x ≥ q ^ 18`.
* `DirichletCharacter.sum_primesLE_pow_eq_neg_one_log_div_le`:
  the power-cutoff corollary at `x = q ^ C` for every `C ≥ 18`.

## References

* B. Green, *On Landau–Siegel zeros*, Hexagon 2610.00311, 2026, Theorem 1.1 and §§2–6 (the Gram
  determinant method for inert primes; the parameter choice `N ≈ R ^ (2 / 3)` here yields the
  constant `3 / 4` cleanly without `rpow`).
* OpenAI, *Uniform exclusion of Landau–Siegel zeros*, October 2026.
-/

public section

open scoped Polynomial Matrix QuadraticAlgebra

namespace TauCeti

/-! ### Quadratic grid injectivity and Schwartz–Zippel bound -/

section GridSchwartzZippel

/-- A squarefree integer `d ≠ 1` is not a square in `ℚ`. -/
private theorem not_isSquare_ratCast_of_squarefree {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    ¬ IsSquare (d : ℚ) := by
  rintro ⟨q, hq⟩
  have hrat : ((d * (q.den : ℤ) ^ 2 : ℤ) : ℚ) = ((q.num ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [hq, ← sq, ← mul_pow, Rat.mul_den_eq_num]
  have hint : d * (q.den : ℤ) ^ 2 = q.num ^ 2 := Int.cast_injective hrat
  have hdvd : q.den ∣ q.num.natAbs := by
    have hsq : (q.den : ℤ) ^ 2 ∣ q.num ^ 2 := ⟨d, by linarith⟩
    have hnat : q.den ^ 2 ∣ q.num.natAbs ^ 2 := by
      rw [← Int.natCast_dvd_natCast]; simpa [sq_abs] using hsq
    exact (Nat.pow_dvd_pow_iff two_ne_zero).mp hnat
  have hden1 : q.den = 1 := (Nat.gcd_eq_left hdvd).symm.trans q.reduced.symm.gcd_eq_one
  have hdsq : d = q.num * q.num := by rw [hden1] at hint; simpa [sq] using hint
  have hu : IsUnit q.num := hd q.num ⟨1, by linarith⟩
  rcases Int.isUnit_iff.mp hu with h | h <;> exact hd1 (by rw [h] at hdsq; simpa using hdsq)

/-- For squarefree `d ≠ 1`, the conjugate coordinate `(x, y) ↦ x - y √d` is injective on `ℕ × ℕ`. -/
private theorem quadGrid_snd_injective {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    Function.Injective fun xy : ℕ × ℕ ↦
      (xy.1 : ℂ) - (xy.2 : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ) := by
  intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  have hinj := (QuadraticAlgebra.algHom_injective_iff
    (QuadraticAlgebra.negSqrtEmbedding (d : ℚ))).mpr (not_isSquare_ratCast_of_squarefree hd hd1)
  have heq : QuadraticAlgebra.negSqrtEmbedding (d : ℚ) ⟨(x₁ : ℚ), (y₁ : ℚ)⟩ =
      QuadraticAlgebra.negSqrtEmbedding (d : ℚ) ⟨(x₂ : ℚ), (y₂ : ℚ)⟩ := by
    simpa [QuadraticAlgebra.negSqrtEmbedding_apply] using h
  have hqa := QuadraticAlgebra.ext_iff.mp (hinj heq)
  exact Prod.ext (Nat.cast_injective hqa.1) (Nat.cast_injective hqa.2)

/-- Linear change of variables `z ↦ X₀ + s X₁`, `z' ↦ X₀ - s X₁` from `ℂ[X][X]` to
`MvPolynomial (Fin 2) ℂ`. -/
private noncomputable def toMvQuad (s : ℂ) : ℂ[X][X] →+* MvPolynomial (Fin 2) ℂ :=
  Polynomial.eval₂RingHom
    (Polynomial.aeval (MvPolynomial.X 0 - MvPolynomial.C s * MvPolynomial.X 1)).toRingHom
    (MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1)

private theorem eval_toMvQuad (s x y : ℂ) (g : ℂ[X][X]) :
    MvPolynomial.eval ![x, y] (toMvQuad s g) =
      (g.map (Polynomial.evalRingHom (x - y * s))).eval (x + y * s) := by
  let lhs : ℂ[X][X] →+* ℂ := (MvPolynomial.eval ![x, y]).comp (toMvQuad s)
  let rhs : ℂ[X][X] →+* ℂ :=
    (Polynomial.evalRingHom (x + y * s)).comp
      (Polynomial.mapRingHom (Polynomial.evalRingHom (x - y * s)))
  change lhs g = rhs g
  have hcomp : lhs = rhs := by
    refine Polynomial.ringHom_ext' ?_ (by simp [lhs, rhs, toMvQuad, mul_comm])
    exact Polynomial.ringHom_ext (fun c ↦ by simp [lhs, rhs, toMvQuad])
      (by simp [lhs, rhs, toMvQuad, mul_comm])
  exact congrArg (fun f ↦ f g) hcomp

private theorem toMvQuad_ne_zero {s : ℂ} (hs : s ≠ 0) {g : ℂ[X][X]} (hg : g ≠ 0) :
    toMvQuad s g ≠ 0 := by
  intro h0
  have hspec (v : ℂ) : g.map (Polynomial.evalRingHom v) = 0 := by
    refine Polynomial.funext fun u ↦ ?_
    let x : ℂ := (u + v) / 2
    let y : ℂ := (u - v) / (2 * s)
    have h1 : x + y * s = u := by simp only [x, y]; field_simp; ring
    have h2 : x - y * s = v := by simp only [x, y]; field_simp; ring
    have hev := eval_toMvQuad s x y g
    rw [h0, map_zero, h1, h2] at hev
    simpa using hev.symm
  have hcoeff (k : ℕ) : g.coeff k = 0 := by
    refine Polynomial.funext fun v ↦ ?_
    simpa [Polynomial.coeff_map] using congrArg (fun p : ℂ[X] ↦ p.coeff k) (hspec v)
  apply hg
  ext k j
  simp [hcoeff k]

private theorem totalDegree_toMvQuad_le (s : ℂ) (g : ℂ[X][X]) :
    (toMvQuad s g).totalDegree ≤
      g.natDegree + g.support.sup fun k ↦ (g.coeff k).natDegree := by
  have hlin (ε : ℂ) : (MvPolynomial.X 0 + MvPolynomial.C ε * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_add _ _).trans
      (max_le (by simp [MvPolynomial.totalDegree_X]) ?_)
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (by simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X])
  have hlin_sub : (MvPolynomial.X 0 - MvPolynomial.C s * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℂ).totalDegree ≤ 1 := by
    simpa [sub_eq_add_neg, MvPolynomial.C_neg] using hlin (-s)
  have hinner (p : ℂ[X]) :
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 2) -
          MvPolynomial.C s * MvPolynomial.X (1 : Fin 2)) p).totalDegree ≤ p.natDegree := by
    rw [Polynomial.aeval_eq_sum_range]
    refine MvPolynomial.totalDegree_finsetSum_le fun j hj ↦ ?_
    have hj' : j ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact (MvPolynomial.totalDegree_pow _ _).trans
      ((Nat.mul_le_mul_left j hlin_sub).trans (by simpa using hj'))
  rw [toMvQuad, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
  refine MvPolynomial.totalDegree_finsetSum_le fun k hk ↦ ?_
  have hk' : k ≤ g.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hcoeff : (g.coeff k).natDegree ≤ g.support.sup fun j ↦ (g.coeff j).natDegree := by
    by_cases hmem : k ∈ g.support
    · exact Finset.le_sup (f := fun j ↦ (g.coeff j).natDegree) hmem
    · rw [Polynomial.notMem_support_iff.mp hmem, Polynomial.natDegree_zero]; exact Nat.zero_le _
  have hpow : ((MvPolynomial.X (0 : Fin 2) +
      MvPolynomial.C s * MvPolynomial.X (1 : Fin 2)) ^ k).totalDegree ≤ g.natDegree :=
    (MvPolynomial.totalDegree_pow _ _).trans
      ((Nat.mul_le_mul_left k (hlin s)).trans (by simpa using hk'))
  exact (Nat.add_le_add ((hinner _).trans hcoeff) hpow).trans (by omega)

/-- Schwartz–Zippel zero-count bound on the `N × N` quadratic grid `(x + y s, x - y s)`. -/
private theorem card_filter_quadGrid_eval_eq_zero_le {s : ℂ} (hs : s ≠ 0) (N : ℕ)
    {g : ℂ[X][X]} (hg : g ≠ 0) :
    (Finset.univ.filter fun xy : Fin N × Fin N ↦
        (g.map (Polynomial.evalRingHom ((xy.1 : ℂ) - (xy.2 : ℂ) * s))).eval
          ((xy.1 : ℂ) + (xy.2 : ℂ) * s) = 0).card ≤
      N * (g.natDegree + g.support.sup fun k ↦ (g.coeff k).natDegree) := by
  classical
  rcases eq_or_ne N 0 with rfl | hN0
  · simp
  let S : Finset ℂ := (Finset.range N).image Nat.cast
  have hScard : S.card = N := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  let emb : Fin N × Fin N ↪ (Fin 2 → ℂ) :=
    ⟨fun xy ↦ ![(xy.1 : ℂ), (xy.2 : ℂ)], fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h ↦ by
      have h0 : (x₁ : ℂ) = (x₂ : ℂ) := by simpa using congrFun h 0
      have h1 : (y₁ : ℂ) = (y₂ : ℂ) := by simpa using congrFun h 1
      exact Prod.ext (Fin.ext (Nat.cast_injective h0)) (Fin.ext (Nat.cast_injective h1))⟩
  have hsub : (Finset.univ.filter fun xy : Fin N × Fin N ↦
      (g.map (Polynomial.evalRingHom ((xy.1 : ℂ) - (xy.2 : ℂ) * s))).eval
        ((xy.1 : ℂ) + (xy.2 : ℂ) * s) = 0).map emb ⊆
      (Fintype.piFinset fun _ : Fin 2 ↦ S).filter
        (fun f ↦ MvPolynomial.eval f (toMvQuad s g) = 0) := by
    intro f hf
    obtain ⟨xy, hxy, rfl⟩ := Finset.mem_map.mp hf
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦ ?_, ?_⟩
    · fin_cases i
      · exact Finset.mem_image.mpr ⟨xy.1.1, Finset.mem_range.mpr xy.1.2, rfl⟩
      · exact Finset.mem_image.mpr ⟨xy.2.1, Finset.mem_range.mpr xy.2.2, rfl⟩
    · rw [show emb xy = ![(xy.1 : ℂ), (xy.2 : ℂ)] from rfl, eval_toMvQuad]
      exact (Finset.mem_filter.mp hxy).2
  have hcard_le := (Finset.card_map emb).symm.le.trans (Finset.card_le_card hsub)
  have hsz := MvPolynomial.schwartz_zippel_totalDegree (toMvQuad_ne_zero hs hg) S
  rw [hScard] at hsz
  have hNpos : (0 : NNRat) < (N : NNRat) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
  have hmul : (((Fintype.piFinset fun _ : Fin 2 ↦ S).filter
      (fun f ↦ MvPolynomial.eval f (toMvQuad s g) = 0)).card : NNRat) ≤
      (N : NNRat) * ((toMvQuad s g).totalDegree : NNRat) := by
    rw [div_le_div_iff₀ (pow_pos hNpos 2) hNpos, sq] at hsz
    exact le_of_mul_le_mul_right (by simpa [mul_assoc, mul_left_comm, mul_comm] using hsz) hNpos
  have hnat : ((Fintype.piFinset fun _ : Fin 2 ↦ S).filter
      (fun f ↦ MvPolynomial.eval f (toMvQuad s g) = 0)).card ≤
      N * (toMvQuad s g).totalDegree := by exact_mod_cast hmul
  exact hcard_le.trans (hnat.trans (Nat.mul_le_mul_left N (totalDegree_toMvQuad_le s g)))

end GridSchwartzZippel

/-! ### Grid vectors, integer Gram matrix, linear independence, and Hadamard bound -/

section GramMatrix

/-- The grid point `x + yω` in `QuadraticAlgebra ℤ d 0`. -/
private def zPt (d : ℤ) (x y : ℕ) : QuadraticAlgebra ℤ d 0 := ⟨x, y⟩

/-- The conjugate grid point `x - yω` in `QuadraticAlgebra ℤ d 0`. -/
private def zConj (d : ℤ) (x y : ℕ) : QuadraticAlgebra ℤ d 0 := ⟨x, -(y : ℤ)⟩

/-- Canonical inclusion `QuadraticAlgebra ℤ d 0 →+* QuadraticAlgebra ℚ d 0`. -/
private noncomputable def toRatQA (d : ℤ) :
    QuadraticAlgebra ℤ d 0 →+* QuadraticAlgebra ℚ (d : ℚ) 0 :=
  algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ (d : ℚ) ((0 : ℤ) : ℚ))

/-- Row `(r, s)` evaluated at `(x, y, j)`: the `j`-th `z`-derivative of `z ^ r z' ^ s` at
`(x + yω, x - yω)` in `QuadraticAlgebra ℤ d 0`. -/
private def gridVec (d : ℤ) (R S N : ℕ) (rs : Fin R × Fin S)
    (xyj : Fin N × Fin N × Fin N) : QuadraticAlgebra ℤ d 0 :=
  (rs.1.1.descFactorial xyj.2.2.1 : ℤ) •
    (zPt d xyj.1.1 xyj.2.1.1 ^ (rs.1.1 - xyj.2.2.1) * zConj d xyj.1.1 xyj.2.1.1 ^ rs.2.1)

/-- Embedding `gridVec` into `EuclideanSpace ℝ ((Fin N × Fin N × Fin N) × Fin 2)` via
`a + bω ↦ (a, √|d| b)`. -/
private noncomputable def realGridVec (d : ℤ) (R S N : ℕ) (rs : Fin R × Fin S) :
    EuclideanSpace ℝ ((Fin N × Fin N × Fin N) × Fin 2) :=
  WithLp.toLp 2 fun k ↦
    if k.2 = 0 then ((gridVec d R S N rs k.1).re : ℝ)
    else Real.sqrt |(d : ℝ)| * ((gridVec d R S N rs k.1).im : ℝ)

/-- The integer Gram matrix of `realGridVec d R S N`. -/
private def intGram (d : ℤ) (R S N : ℕ) : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ :=
  Matrix.of fun u v ↦
    ∑ k : Fin N × Fin N × Fin N,
      ((gridVec d R S N u k).re * (gridVec d R S N v k).re +
        |d| * (gridVec d R S N u k).im * (gridVec d R S N v k).im)

private theorem intGram_map_eq_gram (d : ℤ) (R S N : ℕ) :
    (intGram d R S N).map (Int.castRingHom ℝ) = Matrix.gram ℝ (realGridVec d R S N) := by
  ext u v
  simp only [Matrix.map_apply, Int.coe_castRingHom, intGram, Matrix.of_apply, Int.cast_sum,
    Int.cast_add, Int.cast_mul, Int.cast_abs, Matrix.gram_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type (f := fun p : (Fin N × Fin N × Fin N) × Fin 2 ↦ _)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Fin.sum_univ_two, realGridVec, Fin.isValue, ↓reduceIte, one_ne_zero]
  have hsq : Real.sqrt |(d : ℝ)| * Real.sqrt |(d : ℝ)| = |(d : ℝ)| :=
    Real.mul_self_sqrt (abs_nonneg _)
  linear_combination -((gridVec d R S N u k).im : ℝ) * ((gridVec d R S N v k).im : ℝ) * hsq

private theorem det_intGram_cast (d : ℤ) (R S N : ℕ) :
    ((intGram d R S N).det : ℝ) = (Matrix.gram ℝ (realGridVec d R S N)).det := by
  rw [← intGram_map_eq_gram]
  exact RingHom.map_det (Int.castRingHom ℝ) (intGram d R S N)

private theorem sqrtEmbedding_toRatQA (d : ℤ) (α : QuadraticAlgebra ℤ d 0) :
    QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d α) =
      (α.re : ℂ) + (α.im : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ) := by
  rw [QuadraticAlgebra.sqrtEmbedding_apply]
  change (((α.re : ℚ) : ℂ) + ((α.im : ℚ) : ℂ) * _) = _
  simp

private theorem negSqrtEmbedding_toRatQA (d : ℤ) (α : QuadraticAlgebra ℤ d 0) :
    QuadraticAlgebra.negSqrtEmbedding (d : ℚ) (toRatQA d α) =
      (α.re : ℂ) - (α.im : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ) := by
  rw [QuadraticAlgebra.negSqrtEmbedding_apply]
  change (((α.re : ℚ) : ℂ) - ((α.im : ℚ) : ℂ) * _) = _
  simp

private theorem sqrtEmbedding_gridVec (d : ℤ) (R S N : ℕ) (rs : Fin R × Fin S)
    (xyj : Fin N × Fin N × Fin N) :
    QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d (gridVec d R S N rs xyj)) =
      (rs.1.1.descFactorial xyj.2.2.1 : ℂ) *
        ((xyj.1.1 : ℂ) + (xyj.2.1.1 : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ)) ^
          (rs.1.1 - xyj.2.2.1) *
        ((xyj.1.1 : ℂ) - (xyj.2.1.1 : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ)) ^ rs.2.1 := by
  have hz : QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d (zPt d xyj.1.1 xyj.2.1.1)) =
      (xyj.1.1 : ℂ) + (xyj.2.1.1 : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ) := by
    simp [sqrtEmbedding_toRatQA, zPt]
  have hc : QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d (zConj d xyj.1.1 xyj.2.1.1)) =
      (xyj.1.1 : ℂ) - (xyj.2.1.1 : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ) := by
    simp [sqrtEmbedding_toRatQA, zConj, sub_eq_add_neg]
  simp only [gridVec, zsmul_eq_mul, map_mul, map_pow, Int.cast_natCast, map_natCast, hz, hc]
  ring

/-- The bivariate polynomial `∑_{r, s} f(r, s) z' ^ s z ^ r` in `ℂ[X][X]` attached to `f`. -/
private noncomputable def gridPoly {R S : ℕ} (f : Fin R × Fin S → ℝ) : ℂ[X][X] :=
  ∑ rs : Fin R × Fin S,
    Polynomial.C (Polynomial.C (f rs : ℂ) * Polynomial.X ^ rs.2.1) * Polynomial.X ^ rs.1.1

private theorem gridPoly_coeff {R S : ℕ} (f : Fin R × Fin S → ℝ) (k : ℕ) :
    (gridPoly f).coeff k = ∑ rs : Fin R × Fin S,
      if k = rs.1.1 then Polynomial.C (f rs : ℂ) * Polynomial.X ^ rs.2.1 else 0 := by
  rw [gridPoly, ← Polynomial.lcoeff_apply, map_sum]
  refine Finset.sum_congr rfl fun rs _ ↦ ?_
  rw [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]

private theorem gridPoly_ne_zero_and_deg_le {R S : ℕ} {f : Fin R × Fin S → ℝ}
    (hfne : ¬ ∀ rs, f rs = 0) :
    gridPoly f ≠ 0 ∧ (gridPoly f).natDegree ≤ R ∧
      ((gridPoly f).support.sup fun k ↦ ((gridPoly f).coeff k).natDegree) ≤ S := by
  have hcoeff (r s' : ℕ) (hr : r < R) (hs' : s' < S) :
      ((gridPoly f).coeff r).coeff s' = (f (⟨r, hr⟩, ⟨s', hs'⟩) : ℂ) := by
    rw [gridPoly_coeff]
    have h2 : (∑ rs : Fin R × Fin S,
        if r = rs.1.1 then Polynomial.C (f rs : ℂ) * Polynomial.X ^ rs.2.1 else 0).coeff s' =
        ∑ rs : Fin R × Fin S,
          (if r = rs.1.1 then Polynomial.C (f rs : ℂ) * Polynomial.X ^ rs.2.1 else 0).coeff s' :=
      map_sum (Polynomial.lcoeff ℂ s') _ Finset.univ
    rw [h2, Finset.sum_eq_single (⟨r, hr⟩, ⟨s', hs'⟩)]
    · simp
    · intro rs _ hne
      by_cases hr' : r = rs.1.1
      · have hs'' : rs.2.1 ≠ s' := fun h ↦ hne (Prod.ext (Fin.ext hr'.symm) (Fin.ext h))
        simp [hr', hs''.symm]
      · simp [hr']
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨?_, ?_, ?_⟩
  · intro h0; apply hfne; intro ⟨r, s'⟩
    have h := hcoeff r.1 s'.1 r.2 s'.2
    rw [h0, Polynomial.coeff_zero, Polynomial.coeff_zero] at h
    exact Complex.ofReal_eq_zero.mp h.symm
  · refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun rs _ ↦ ?_)
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans rs.1.2.le
  · refine Finset.sup_le fun k _ ↦ ?_
    rw [gridPoly_coeff]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun rs _ ↦ ?_)
    dsimp only [Function.comp_apply]
    split_ifs
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans rs.2.2.le
    · simp

private theorem gridPoly_iterate_derivative_eval_eq (d : ℤ) {R S N : ℕ} (f : Fin R × Fin S → ℝ)
    (xy : Fin N × Fin N) (j : Fin N) :
    ((Polynomial.derivative^[j.1] (gridPoly f)).map
      (Polynomial.evalRingHom
        ((xy.1.1 : ℂ) - (xy.2.1 : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ)))).eval
        ((xy.1.1 : ℂ) + (xy.2.1 : ℂ) * QuadraticAlgebra.sqrtRadicand (d : ℚ)) =
      ∑ rs : Fin R × Fin S, (f rs : ℂ) *
        QuadraticAlgebra.sqrtEmbedding (d : ℚ)
          (toRatQA d (gridVec d R S N rs (xy.1, xy.2, j))) := by
  set s := QuadraticAlgebra.sqrtRadicand (d : ℚ)
  rw [gridPoly, Polynomial.iterate_derivative_sum, Polynomial.map_sum]
  change (Polynomial.evalRingHom ((xy.1.1 : ℂ) + (xy.2.1 : ℂ) * s)) (∑ rs, _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun rs _ ↦ ?_
  simp only [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_C_mul,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_natCast, sqrtEmbedding_gridVec, s]
  ring

/-- A real linear relation on `realGridVec` forces the complex `sqrtEmbedding` combination to vanish
at every grid triple `(x, y, j)`. -/
private theorem sum_sqrtEmbedding_gridVec_eq_zero {d : ℤ} (hd0 : d ≠ 0) {R S N : ℕ}
    {f : Fin R × Fin S → ℝ} (hf : ∑ rs, f rs • realGridVec d R S N rs = 0)
    (k : Fin N × Fin N × Fin N) :
    ∑ rs : Fin R × Fin S, (f rs : ℂ) *
      QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d (gridVec d R S N rs k)) = 0 := by
  have hre : ∑ rs : Fin R × Fin S, f rs * ((gridVec d R S N rs k).re : ℝ) = 0 := by
    simpa [realGridVec] using congrFun (congrArg WithLp.ofLp hf) (k, 0)
  have him : ∑ rs : Fin R × Fin S, f rs * ((gridVec d R S N rs k).im : ℝ) = 0 := by
    have h1 := congrFun (congrArg WithLp.ofLp hf) (k, 1)
    have hsq0 : Real.sqrt |(d : ℝ)| ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr hd0))
    have hmul : Real.sqrt |(d : ℝ)| *
        ∑ rs : Fin R × Fin S, f rs * ((gridVec d R S N rs k).im : ℝ) = 0 := by
      rw [Finset.mul_sum]; simpa [realGridVec, mul_left_comm, mul_comm, mul_assoc] using h1
    exact (mul_eq_zero.mp hmul).resolve_left hsq0
  simp_rw [sqrtEmbedding_toRatQA, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul]
  have hreC : (∑ rs : Fin R × Fin S, (f rs : ℂ) * ((gridVec d R S N rs k).re : ℂ)) = 0 := by
    exact_mod_cast hre
  have himC : (∑ rs : Fin R × Fin S, (f rs : ℂ) * ((gridVec d R S N rs k).im : ℂ)) = 0 := by
    exact_mod_cast him
  rw [hreC, himC, zero_mul, add_zero]

private theorem linearIndependent_realGridVec {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {R S N : ℕ} (hparam : N * R + N * S + 2 * R * S < N ^ 3) :
    LinearIndependent ℝ (realGridVec d R S N) := by
  classical
  set s := QuadraticAlgebra.sqrtRadicand (d : ℚ)
  have hs0 : s ≠ 0 :=
    QuadraticAlgebra.sqrtRadicand_eq_zero_iff.not.mpr (Int.cast_ne_zero.mpr hd.ne_zero)
  rw [Fintype.linearIndependent_iff]
  intro f hf
  by_contra hfne
  obtain ⟨hFne, hFdeg, hFpdeg⟩ := gridPoly_ne_zero_and_deg_le hfne
  have hvan : ∀ xy : Fin N × Fin N, ∀ j < N,
      ((Polynomial.derivative^[j] (gridPoly f)).map
        (Polynomial.evalRingHom ((xy.1.1 : ℂ) - (xy.2.1 : ℂ) * s))).eval
          ((xy.1.1 : ℂ) + (xy.2.1 : ℂ) * s) = 0 := fun xy j hj ↦ by
    rw [gridPoly_iterate_derivative_eval_eq d f xy ⟨j, hj⟩]
    exact sum_sqrtEmbedding_gridVec_eq_zero hd.ne_zero hf (xy.1, xy.2, ⟨j, hj⟩)
  have hmul := Polynomial.mul_card_le_of_forall_iterate_derivative_eval_eq_zero
    (P := fun xy : Fin N × Fin N ↦
      ((xy.1.1 : ℂ) + (xy.2.1 : ℂ) * s, (xy.1.1 : ℂ) - (xy.2.1 : ℂ) * s))
    (fun ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h ↦ by
      have hxy := quadGrid_snd_injective hd hd1 (a₁ := (x₁.1, y₁.1)) (a₂ := (x₂.1, y₂.1)) h
      exact Prod.ext (Fin.ext (congrArg Prod.fst hxy)) (Fin.ext (congrArg Prod.snd hxy)))
    (fun g hg ↦ card_filter_quadGrid_eval_eq_zero_le hs0 N hg) hFne hvan
  have hcard : N * Fintype.card (Fin N × Fin N) = N ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_fin]; ring
  rw [hcard] at hmul
  have h1 : N * (gridPoly f).natDegree ≤ N * R := Nat.mul_le_mul_left N hFdeg
  have h2 : N * ((gridPoly f).support.sup fun k ↦ ((gridPoly f).coeff k).natDegree) ≤ N * S :=
    Nat.mul_le_mul_left N hFpdeg
  have h3 : 2 * (gridPoly f).natDegree *
      ((gridPoly f).support.sup fun k ↦ ((gridPoly f).coeff k).natDegree) ≤ 2 * R * S :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hFdeg) hFpdeg
  omega

/-- Unified identity `a² + |d| b² = (‖σ₊ α‖² + ‖σ₋ α‖²) / 2` for both signs of `d`. -/
private theorem re_sq_add_abs_mul_im_sq (d : ℤ) (α : QuadraticAlgebra ℤ d 0) :
    (α.re : ℝ) ^ 2 + |(d : ℝ)| * (α.im : ℝ) ^ 2 =
      (‖QuadraticAlgebra.sqrtEmbedding (d : ℚ) (toRatQA d α)‖ ^ 2 +
        ‖QuadraticAlgebra.negSqrtEmbedding (d : ℚ) (toRatQA d α)‖ ^ 2) / 2 := by
  rw [sqrtEmbedding_toRatQA, negSqrtEmbedding_toRatQA]
  rcases le_total 0 d with hd | hd
  · have hdq : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
    have hdr : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    rw [QuadraticAlgebra.sqrtRadicand_of_nonneg hdq, abs_of_nonneg hdr]
    simp only [Rat.cast_intCast, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith [Real.sq_sqrt hdr]
  · have hdq : (d : ℚ) ≤ 0 := by exact_mod_cast hd
    have hdr : (d : ℝ) ≤ 0 := by exact_mod_cast hd
    rw [QuadraticAlgebra.sqrtRadicand_of_nonpos hdq, abs_of_nonpos hdr]
    simp only [Rat.cast_intCast, ← Complex.ofReal_intCast, ← mul_assoc, ← Complex.ofReal_mul,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.sq_sqrt (neg_nonneg.mpr hdr)]

/-- Complex-embedding norm bound for each entry of `gridVec`. -/
private theorem norm_embedding_gridVec_le {d : ℤ} (hd0 : d ≠ 0) {R S N : ℕ} (hR : 1 ≤ R)
    (hN : 1 ≤ N) (σ : QuadraticAlgebra ℚ (d : ℚ) 0 →ₐ[ℚ] ℂ) (rs : Fin R × Fin S)
    (k : Fin N × Fin N × Fin N) :
    ‖σ (toRatQA d (gridVec d R S N rs k))‖ ≤
      (R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ (rs.1.1 + rs.2.1) := by
  have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast Int.one_le_abs hd0
  have hsqd1 : 1 ≤ Real.sqrt |(d : ℝ)| := by simpa using Real.sqrt_le_sqrt hd1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM1 : 1 ≤ 2 * (N : ℝ) * Real.sqrt |(d : ℝ)| := by nlinarith
  have hx : (k.1.1 : ℝ) ≤ N := by exact_mod_cast k.1.2.le
  have hy : (k.2.1.1 : ℝ) ≤ N := by exact_mod_cast k.2.1.2.le
  have hpt1 : ‖σ (toRatQA d (zPt d k.1.1 k.2.1.1))‖ ≤ 2 * (N : ℝ) * Real.sqrt |(d : ℝ)| := by
    refine (QuadraticAlgebra.norm_embedding_algebraMap_le σ (zPt d k.1.1 k.2.1.1)).trans ?_
    simp only [zPt, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
    nlinarith
  have hpt2 : ‖σ (toRatQA d (zConj d k.1.1 k.2.1.1))‖ ≤ 2 * (N : ℝ) * Real.sqrt |(d : ℝ)| := by
    refine (QuadraticAlgebra.norm_embedding_algebraMap_le σ (zConj d k.1.1 k.2.1.1)).trans ?_
    simp only [zConj, Int.cast_natCast, Int.cast_neg, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
    nlinarith
  simp only [gridVec, zsmul_eq_mul, map_mul, map_pow, Int.cast_natCast, map_natCast, norm_mul,
    norm_pow, Complex.norm_natCast]
  have hdesc : (rs.1.1.descFactorial k.2.2.1 : ℝ) ≤ (R : ℝ) ^ N := by
    exact_mod_cast (Nat.descFactorial_le_pow rs.1.1 k.2.2.1).trans
      ((Nat.pow_le_pow_left rs.1.2.le _).trans (Nat.pow_le_pow_right hR k.2.2.2.le))
  have hpow1 : ‖σ (toRatQA d (zPt d k.1.1 k.2.1.1))‖ ^ (rs.1.1 - k.2.2.1) ≤
      (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ rs.1.1 :=
    (pow_le_pow_left₀ (norm_nonneg _) hpt1 _).trans (pow_le_pow_right₀ hM1 (Nat.sub_le _ _))
  have hpow2 : ‖σ (toRatQA d (zConj d k.1.1 k.2.1.1))‖ ^ rs.2.1 ≤
      (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ rs.2.1 :=
    pow_le_pow_left₀ (norm_nonneg _) hpt2 _
  rw [pow_add]
  exact mul_le_mul hdesc (mul_le_mul hpow1 hpow2 (by positivity) (by positivity))
    (by positivity) (by positivity)

/-- Row-norm bound for `realGridVec d R S N rs`. -/
private theorem norm_sq_realGridVec_le {d : ℤ} (hd0 : d ≠ 0) {R S N : ℕ} (hR : 1 ≤ R) (hN : 1 ≤ N)
    (rs : Fin R × Fin S) :
    ‖realGridVec d R S N rs‖ ^ 2 ≤
      (N : ℝ) ^ 3 *
        ((R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ (rs.1.1 + rs.2.1)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  calc ∑ k : Fin N × Fin N × Fin N, ∑ j : Fin 2, realGridVec d R S N rs (k, j) ^ 2
      = ∑ k : Fin N × Fin N × Fin N,
          ((gridVec d R S N rs k).re ^ 2 + |(d : ℝ)| * (gridVec d R S N rs k).im ^ 2) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        simp only [Fin.sum_univ_two, realGridVec, Fin.isValue, ↓reduceIte, one_ne_zero, mul_pow,
          Real.sq_sqrt (abs_nonneg _)]
    _ ≤ ∑ _k : Fin N × Fin N × Fin N,
          ((R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ (rs.1.1 + rs.2.1)) ^ 2 := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        rw [re_sq_add_abs_mul_im_sq]
        have hsq1 := pow_le_pow_left₀ (norm_nonneg _)
          (norm_embedding_gridVec_le hd0 hR hN (QuadraticAlgebra.sqrtEmbedding (d : ℚ)) rs k) 2
        have hsq2 := pow_le_pow_left₀ (norm_nonneg _)
          (norm_embedding_gridVec_le hd0 hR hN (QuadraticAlgebra.negSqrtEmbedding (d : ℚ)) rs k) 2
        linarith
    _ = (N : ℝ) ^ 3 *
          ((R : ℝ) ^ N * (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ^ (rs.1.1 + rs.2.1)) ^ 2 := by
        simp [pow_succ, mul_assoc]

/-- Exact sum `∑ i : Fin m, (i : ℝ) = m (m - 1) / 2`. -/
private theorem sum_fin_val_eq (m : ℕ) :
    ∑ i : Fin m, (i.1 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (i : ℝ))]
  rcases eq_or_ne m 0 with rfl | hm0
  · simp
  · have h2 : 2 * ∑ i ∈ Finset.range m, i = m * (m - 1) := by
      rw [Finset.sum_range_id]
      exact Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd
    have h2R : (2 : ℝ) * ∑ i ∈ Finset.range m, (i : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
      have := congrArg (Nat.cast (R := ℝ)) h2
      push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hm0)] at this
      exact this
    linarith

private theorem sum_fin_prod_add_le (R S : ℕ) :
    ∑ rs : Fin R × Fin S, 2 * ((rs.1.1 : ℝ) + rs.2.1) ≤ (R : ℝ) * S * ((R : ℝ) + S) := by
  rw [Fintype.sum_prod_type]
  have hexp : ∑ r : Fin R, ∑ s : Fin S, 2 * ((r.1 : ℝ) + s.1) =
      2 * (S : ℝ) * (∑ r : Fin R, (r.1 : ℝ)) + 2 * (R : ℝ) * (∑ s : Fin S, (s.1 : ℝ)) := by
    calc ∑ r : Fin R, ∑ s : Fin S, 2 * ((r.1 : ℝ) + s.1)
        = ∑ r : Fin R, (2 * (S : ℝ) * (r.1 : ℝ) + 2 * ∑ s : Fin S, (s.1 : ℝ)) := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          simp_rw [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
          ring
      _ = 2 * (S : ℝ) * (∑ r : Fin R, (r.1 : ℝ)) + 2 * (R : ℝ) * (∑ s : Fin S, (s.1 : ℝ)) := by
          simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
          ring
  rw [hexp, sum_fin_val_eq R, sum_fin_val_eq S]
  nlinarith [Nat.cast_nonneg (α := ℝ) R, Nat.cast_nonneg (α := ℝ) S]

/-- Archimedean upper bound on `log (det (intGram d R S N))` via Hadamard's inequality. -/
private theorem log_det_intGram_le {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) {R S N : ℕ}
    (hR : 1 ≤ R) (hN : 1 ≤ N) (hparam : N * R + N * S + 2 * R * S < N ^ 3) :
    0 < (intGram d R S N).det ∧
      Real.log ((intGram d R S N).det : ℝ) ≤
        (R : ℝ) * S * (3 * Real.log N + 2 * N * Real.log R) +
          (R : ℝ) * S * ((R : ℝ) + S) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
  have hli := linearIndependent_realGridVec hd hd1 hparam
  have hposR : 0 < ((intGram d R S N).det : ℝ) := by
    rw [det_intGram_cast]; exact Matrix.det_gram_pos_iff.mpr hli
  refine ⟨by exact_mod_cast hposR, ?_⟩
  rw [det_intGram_cast]
  refine (Matrix.log_det_gram_le hli).trans ?_
  have hd0 : d ≠ 0 := hd.ne_zero
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hMpos : 0 < 2 * (N : ℝ) * Real.sqrt |(d : ℝ)| :=
    mul_pos (mul_pos two_pos hNpos) (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr hd0)))
  have hrow (rs : Fin R × Fin S) :
      2 * Real.log ‖realGridVec d R S N rs‖ ≤
        3 * Real.log N + 2 * N * Real.log R +
          2 * ((rs.1.1 : ℝ) + rs.2.1) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
    have hne : ‖realGridVec d R S N rs‖ ≠ 0 := norm_ne_zero_iff.mpr (hli.ne_zero rs)
    rw [show 2 * Real.log ‖realGridVec d R S N rs‖ = Real.log (‖realGridVec d R S N rs‖ ^ 2) by
      simp [Real.log_pow]]
    refine (Real.log_le_log (sq_pos_of_ne_zero hne) (norm_sq_realGridVec_le hd0 hR hN rs)).trans ?_
    rw [Real.log_mul (pow_ne_zero 3 hNpos.ne') (pow_ne_zero 2 (mul_ne_zero (pow_ne_zero N hRpos.ne')
      (pow_ne_zero _ hMpos.ne'))), Real.log_pow, Real.log_pow,
      Real.log_mul (pow_ne_zero N hRpos.ne') (pow_ne_zero _ hMpos.ne'), Real.log_pow, Real.log_pow]
    push_cast; linarith
  have hlogM : 0 ≤ Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
    apply Real.log_nonneg
    have hsq1 : 1 ≤ Real.sqrt |(d : ℝ)| := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ |(d : ℝ)| by exact_mod_cast Int.one_le_abs hd0)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  calc ∑ rs : Fin R × Fin S, 2 * Real.log ‖realGridVec d R S N rs‖
      ≤ ∑ rs : Fin R × Fin S, (3 * Real.log N + 2 * N * Real.log R +
          2 * ((rs.1.1 : ℝ) + rs.2.1) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|)) :=
        Finset.sum_le_sum fun rs _ ↦ hrow rs
    _ = (R : ℝ) * S * (3 * Real.log N + 2 * N * Real.log R) +
          (∑ rs : Fin R × Fin S, 2 * ((rs.1.1 : ℝ) + rs.2.1)) *
            Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Finset.sum_mul]
    _ ≤ (R : ℝ) * S * (3 * Real.log N + 2 * N * Real.log R) +
          (R : ℝ) * S * ((R : ℝ) + S) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
        gcongr; exact sum_fin_prod_add_le R S

end GramMatrix

/-! ### Frobenius congruence and `p`-adic divisibility of the Gram determinant -/

section PadicDivisibility

private theorem qa_re_sum {ι : Type*} {d : ℤ} (s : Finset ι)
    (f : ι → QuadraticAlgebra ℤ d 0) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum (AddMonoidHom.mk' QuadraticAlgebra.re QuadraticAlgebra.re_add) f s

private theorem qa_im_sum {ι : Type*} {d : ℤ} (s : Finset ι)
    (f : ι → QuadraticAlgebra ℤ d 0) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im :=
  map_sum (AddMonoidHom.mk' QuadraticAlgebra.im QuadraticAlgebra.im_add) f s

/-- Reduction modulo `p` from `QuadraticAlgebra ℤ d 0` to `QuadraticAlgebra (ZMod p) d 0`. -/
private def modPRingHom (d : ℤ) (p : ℕ) :
    QuadraticAlgebra ℤ d 0 →+* QuadraticAlgebra (ZMod p) (d : ZMod p) 0 where
  toFun α := ⟨(α.re : ZMod p), (α.im : ZMod p)⟩
  map_one' := by ext <;> simp
  map_mul' α β := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' α β := by ext <;> simp

private theorem dvd_quadraticAlgebra_iff {d : ℤ} {n : ℤ} {α : QuadraticAlgebra ℤ d 0} :
    (n : QuadraticAlgebra ℤ d 0) ∣ α ↔ n ∣ α.re ∧ n ∣ α.im := by
  constructor
  · rintro ⟨β, rfl⟩
    exact ⟨⟨β.re, by simp [QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]⟩,
      ⟨β.im, by simp [QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨⟨a, b⟩, QuadraticAlgebra.ext ?_ ?_⟩
    · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
        Int.cast_id, zero_mul, mul_zero, add_zero, ha]
    · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
        Int.cast_id, zero_mul, mul_zero, add_zero, hb]

private theorem modPRingHom_eq_zero_iff {d : ℤ} {p : ℕ} {α : QuadraticAlgebra ℤ d 0} :
    modPRingHom d p α = 0 ↔ ((p : ℤ) : QuadraticAlgebra ℤ d 0) ∣ α := by
  rw [QuadraticAlgebra.ext_iff, dvd_quadraticAlgebra_iff]
  simp [modPRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- For an odd prime `p` with `jacobiSym d p = -1`, Frobenius sends `x + yω` to `x - yω` modulo `p`
in `QuadraticAlgebra ℤ d 0`. -/
private theorem frobenius_dvd_zPt_pow_sub_zConj {d : ℤ} {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hinert : jacobiSym d p = -1) (x y : ℕ) :
    ((p : ℤ) : QuadraticAlgebra ℤ d 0) ∣ zPt d x y ^ p - zConj d x y := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← modPRingHom_eq_zero_iff, map_sub, map_pow, sub_eq_zero]
  have : CharP (QuadraticAlgebra (ZMod p) (d : ZMod p) 0) p := ⟨fun n ↦ by
    rw [QuadraticAlgebra.ext_iff]
    simp [QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, ZMod.natCast_eq_zero_iff]⟩
  have h1 : modPRingHom d p (zPt d x y) =
      (x : QuadraticAlgebra (ZMod p) (d : ZMod p) 0) +
        (y : QuadraticAlgebra (ZMod p) (d : ZMod p) 0) * QuadraticAlgebra.omega := by
    refine QuadraticAlgebra.ext ?_ ?_
    · simp [modPRingHom, zPt, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]
    · simp [modPRingHom, zPt, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]
  have h2 : modPRingHom d p (zConj d x y) =
      (x : QuadraticAlgebra (ZMod p) (d : ZMod p) 0) -
        (y : QuadraticAlgebra (ZMod p) (d : ZMod p) 0) * QuadraticAlgebra.omega := by
    refine QuadraticAlgebra.ext ?_ ?_
    · simp [modPRingHom, zConj, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]
    · simp [modPRingHom, zConj, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega]
  rw [h1, h2, add_pow_char, mul_pow]
  have hcast (n : ℕ) : (n : QuadraticAlgebra (ZMod p) (d : ZMod p) 0) ^ p = n := by
    change (algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) (d : ZMod p) 0) (n : ZMod p)) ^ p =
      algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) (d : ZMod p) 0) (n : ZMod p)
    rw [← map_pow, ZMod.pow_card]
  have hωsq : (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod p) (d : ZMod p) 0) ^ 2 =
      algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) (d : ZMod p) 0) (d : ZMod p) := by
    rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]; simp
  have hp_eq : p = 2 * (p / 2) + 1 := by obtain ⟨k, rfl⟩ := hodd; omega
  have hleg : ((d : ZMod p) ^ (p / 2)) = -1 := by
    have := legendreSym.eq_pow p d
    rw [jacobiSym.legendreSym.to_jacobiSym, hinert, Int.cast_neg, Int.cast_one] at this
    exact this.symm
  have hωp : (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod p) (d : ZMod p) 0) ^ p =
      -QuadraticAlgebra.omega := by
    rw [show (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod p) (d : ZMod p) 0) ^ p =
          (QuadraticAlgebra.omega : QuadraticAlgebra (ZMod p) (d : ZMod p) 0) ^ (2 * (p / 2) + 1)
        from congrArg ((QuadraticAlgebra.omega : QuadraticAlgebra (ZMod p) (d : ZMod p) 0) ^ ·)
          hp_eq,
      pow_succ, pow_mul, hωsq, ← map_pow, hleg, map_neg, map_one, neg_one_mul]
  rw [hcast x, hcast y, hωp, mul_neg, sub_eq_add_neg]

/-- If `(p : A) ∣ z₀ ^ p - z₁`, then `(p : A) ^ h` divides every `k`-th derivative of
`(X ^ p - C z₁) ^ h` evaluated at `z₀`. -/
private theorem pow_dvd_eval_iterate_derivative_pow {A : Type*} [CommRing A] {p : ℕ} {z₀ z₁ : A}
    (hcong : (p : A) ∣ z₀ ^ p - z₁) (h k : ℕ) :
    (p : A) ^ h ∣
      (Polynomial.derivative^[k] ((Polynomial.X ^ p - Polynomial.C z₁) ^ h)).eval z₀ := by
  have hdvd_desc : ∀ m : ℕ, p ∣ p.descFactorial (m + 1) := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [Nat.descFactorial_succ]; exact dvd_mul_of_dvd_right ih _
  have hbase (m : ℕ) :
      (p : A) ∣ (Polynomial.derivative^[m] (Polynomial.X ^ p - Polynomial.C z₁)).eval z₀ := by
    cases m with
    | zero => simpa using hcong
    | succ m =>
      have hderiv : Polynomial.derivative^[m + 1] (Polynomial.X ^ p - Polynomial.C z₁) =
          Polynomial.C (p.descFactorial (m + 1) : A) * Polynomial.X ^ (p - (m + 1)) := by
        rw [Polynomial.iterate_derivative_sub, Polynomial.iterate_derivative_X_pow_eq_C_mul,
          Function.iterate_succ_apply, Polynomial.derivative_C, Polynomial.iterate_derivative_zero,
          sub_zero]
      rw [hderiv, Polynomial.eval_mul, Polynomial.eval_C]
      obtain ⟨c, hc⟩ := hdvd_desc m
      exact dvd_mul_of_dvd_left ⟨(c : A), by rw [hc, Nat.cast_mul]⟩ _
  induction h generalizing k with
  | zero => simp
  | succ h ih =>
    rw [pow_succ (Polynomial.X ^ p - Polynomial.C z₁), Polynomial.iterate_derivative_mul]
    change (p : A) ^ (h + 1) ∣ (Polynomial.evalRingHom z₀) (∑ i ∈ Finset.range (k + 1), _)
    rw [map_sum]
    refine Finset.dvd_sum fun i _ ↦ ?_
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_smul, Polynomial.eval_mul, nsmul_eq_mul]
    refine dvd_mul_of_dvd_right ?_ _
    rw [pow_succ]
    exact mul_dvd_mul (ih (k - i)) (hbase i)

/-- Divisibility of the `j`-th derivative of `X ^ (r - p * h) * (X ^ p - C z₁) ^ h * C (z₁ ^ s)`
evaluated at `z₀`. -/
private theorem pow_dvd_eval_iterate_derivative_basis {A : Type*} [CommRing A] {p : ℕ} {z₀ z₁ : A}
    (hcong : (p : A) ∣ z₀ ^ p - z₁) (r s h j : ℕ) :
    (p : A) ^ h ∣ (Polynomial.derivative^[j]
      (Polynomial.X ^ (r - p * h) * (Polynomial.X ^ p - Polynomial.C z₁) ^ h *
        Polynomial.C (z₁ ^ s))).eval z₀ := by
  rw [mul_assoc, Polynomial.iterate_derivative_mul]
  change (p : A) ^ h ∣ (Polynomial.evalRingHom z₀) (∑ i ∈ Finset.range (j + 1), _)
  rw [map_sum]
  refine Finset.dvd_sum fun i _ ↦ ?_
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_smul, Polynomial.eval_mul, nsmul_eq_mul,
    mul_comm _ (Polynomial.C (z₁ ^ s)), Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul]
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right
    (pow_dvd_eval_iterate_derivative_pow hcong h i) _) _) _

/-- Binomial expansion of
`(derivative^[j] (X ^ (r - p * h) * (X ^ p - C z₁) ^ h * C (z₁ ^ s))).eval z₀`. -/
private theorem eval_iterate_derivative_basis_eq {A : Type*} [CommRing A] {p r s h j : ℕ}
    (hph : p * h ≤ r) (z₀ z₁ : A) :
    (Polynomial.derivative^[j]
      (Polynomial.X ^ (r - p * h) * (Polynomial.X ^ p - Polynomial.C z₁) ^ h *
        Polynomial.C (z₁ ^ s))).eval z₀ =
      ∑ t ∈ Finset.range (h + 1),
        ((-1 : ℤ) ^ t * (h.choose t : ℤ)) •
          (((r - p * t).descFactorial j : ℤ) • (z₀ ^ (r - p * t - j) * z₁ ^ (s + t))) := by
  have hexp : Polynomial.X ^ (r - p * h) * (Polynomial.X ^ p - Polynomial.C z₁) ^ h *
      Polynomial.C (z₁ ^ s) =
      ∑ t ∈ Finset.range (h + 1),
        Polynomial.C (((-1 : A) ^ t * (h.choose t : A)) * z₁ ^ (s + t)) *
          Polynomial.X ^ (r - p * t) := by
    rw [sub_eq_add_neg, add_comm, add_pow, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have hth : t ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    have hpowX : (Polynomial.X : A[X]) ^ (r - p * h) * (Polynomial.X ^ p) ^ (h - t) =
        Polynomial.X ^ (r - p * t) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      have : p * t ≤ p * h := Nat.mul_le_mul_left p hth
      have : p * (h - t) = p * h - p * t := Nat.mul_sub_left_distrib p h t
      omega
    have hneg : (-Polynomial.C z₁) ^ t = Polynomial.C ((-1 : A) ^ t * z₁ ^ t) := by
      rw [← map_neg, ← map_pow, neg_eq_neg_one_mul, mul_pow]
    rw [hneg, pow_add, ← hpowX]
    simp only [map_mul, map_pow, map_neg, map_one, Polynomial.C_eq_natCast]
    ring
  rw [hexp, Polynomial.iterate_derivative_sum]
  change (Polynomial.evalRingHom z₀) (∑ t ∈ Finset.range (h + 1), _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Polynomial.coe_evalRingHom, Polynomial.iterate_derivative_C_mul,
    Polynomial.iterate_derivative_X_pow_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    zsmul_eq_mul, zsmul_eq_mul]
  push_cast; ring

/-- The local divisibility exponent `h(r, s) = min (r / p) (S - 1 - s)` for row `(r, s)`. -/
private def padicExp {R : ℕ} (S p : ℕ) (rs : Fin R × Fin S) : ℕ :=
  min (rs.1.1 / p) (S - 1 - rs.2.1)

/-- The unitriangular integer row-transformation matrix for an odd inert prime `p`. -/
private def unitriMat (R S p : ℕ) : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ :=
  Matrix.of fun u v ↦
    if u.2.1 ≤ v.2.1 ∧ v.2.1 ≤ u.2.1 + padicExp S p u ∧
        v.1.1 + p * (v.2.1 - u.2.1) = u.1.1 then
      (-1 : ℤ) ^ (v.2.1 - u.2.1) * ((padicExp S p u).choose (v.2.1 - u.2.1) : ℤ)
    else 0

private theorem det_unitriMat (R S p : ℕ) : (unitriMat R S p).det = 1 := by
  let e : (Fin R × Fin S) ≃ Lex (Fin S × Fin R) :=
    (Equiv.prodComm (Fin R) (Fin S)).trans toLex
  rw [← Matrix.det_reindex_self e (unitriMat R S p)]
  have htri : ((unitriMat R S p).reindex e e).BlockTriangular id := by
    intro a b hab
    change (unitriMat R S p) (e.symm a) (e.symm b) = 0
    simp only [unitriMat, Matrix.of_apply, ite_eq_right_iff]
    intro ⟨h1, _, h3⟩
    have hlt' : (ofLex b).1 < (ofLex a).1 ∨
        ((ofLex b).1 = (ofLex a).1 ∧ (ofLex b).2 < (ofLex a).2) := Prod.Lex.lt_iff.mp hab
    have he1 : (e.symm a).1 = (ofLex a).2 := rfl
    have he2 : (e.symm a).2 = (ofLex a).1 := rfl
    have hb1 : (e.symm b).1 = (ofLex b).2 := rfl
    have hb2 : (e.symm b).2 = (ofLex b).1 := rfl
    rw [he2, hb2] at h1; rw [he1, he2, hb1, hb2] at h3
    rcases hlt' with hs | ⟨hs, hr⟩
    · exact absurd h1 (not_le.mpr hs)
    · rw [hs, Nat.sub_self, mul_zero, add_zero] at h3; exact absurd h3 (ne_of_lt hr)
  rw [Matrix.det_of_isUpperTriangular htri]
  exact Finset.prod_eq_one fun a _ ↦ by simp [unitriMat]

/-- Reindexing each transformed row into the binomial derivative combination. -/
private theorem transformed_row_eq_binomial {d : ℤ} {R S N p : ℕ} (u : Fin R × Fin S)
    (k : Fin N × Fin N × Fin N) :
    ∑ v : Fin R × Fin S, unitriMat R S p u v • gridVec d R S N v k =
      ∑ t ∈ Finset.range (padicExp S p u + 1),
        ((-1 : ℤ) ^ t * ((padicExp S p u).choose t : ℤ)) •
          (((u.1.1 - p * t).descFactorial k.2.2.1 : ℤ) •
            (zPt d k.1.1 k.2.1.1 ^ (u.1.1 - p * t - k.2.2.1) *
              zConj d k.1.1 k.2.1.1 ^ (u.2.1 + t))) := by
  have hph : p * padicExp S p u ≤ u.1.1 :=
    (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le u.1.1 p)
  have hsh : u.2.1 + padicExp S p u < S := by
    have hle : padicExp S p u ≤ S - 1 - u.2.1 := min_le_right _ _
    omega
  let P (v : Fin R × Fin S) : Prop :=
    u.2.1 ≤ v.2.1 ∧ v.2.1 ≤ u.2.1 + padicExp S p u ∧ v.1.1 + p * (v.2.1 - u.2.1) = u.1.1
  have hfilt : ∑ v : Fin R × Fin S, unitriMat R S p u v • gridVec d R S N v k =
      ∑ v ∈ Finset.univ.filter P, unitriMat R S p u v • gridVec d R S N v k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    split_ifs with hv
    · rfl
    · simp only [unitriMat, Matrix.of_apply, show ¬ (u.2.1 ≤ v.2.1 ∧
        v.2.1 ≤ u.2.1 + padicExp S p u ∧ v.1.1 + p * (v.2.1 - u.2.1) = u.1.1) from hv,
        ↓reduceIte, zero_smul]
  rw [hfilt]
  let f (t : ℕ) : Fin R × Fin S :=
    if ht : t ≤ padicExp S p u then
      (⟨u.1.1 - p * t, lt_of_le_of_lt (Nat.sub_le _ _) u.1.2⟩, ⟨u.2.1 + t, by omega⟩)
    else u
  have hth {t : ℕ} (ht : t ∈ Finset.range (padicExp S p u + 1)) : t ≤ padicExp S p u :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  have hpt {t : ℕ} (ht : t ≤ padicExp S p u) : p * t ≤ u.1.1 :=
    (Nat.mul_le_mul_left p ht).trans hph
  symm
  refine Finset.sum_nbij' f (fun v ↦ v.2.1 - u.2.1) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩ <;>
      simp only [f, hth ht, ↓reduceDIte]
    · exact Nat.le_add_right _ _
    · exact Nat.add_le_add_left (hth ht) _
    · rw [Nat.add_sub_cancel_left]; exact Nat.sub_add_cancel (hpt (hth ht))
  · exact fun v hv ↦ Finset.mem_range.mpr (by have ⟨_, h2, _⟩ := (Finset.mem_filter.mp hv).2; omega)
  · exact fun t ht ↦ by simp [f, hth ht]
  · intro v hv
    have ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp hv).2
    ext <;> simp only [f, show v.2.1 - u.2.1 ≤ padicExp S p u by omega, ↓reduceDIte] <;> omega
  · intro t ht
    have hcond : u.2.1 ≤ u.2.1 + t ∧ u.2.1 + t ≤ u.2.1 + padicExp S p u ∧
        u.1.1 - p * t + p * t = u.1.1 :=
      ⟨Nat.le_add_right _ _, Nat.add_le_add_left (hth ht) _, Nat.sub_add_cancel (hpt (hth ht))⟩
    simp only [unitriMat, Matrix.of_apply, f, hth ht, ↓reduceDIte, Nat.add_sub_cancel_left, hcond,
      and_self, ↓reduceIte, gridVec]

/-- Each transformed row is divisible by `p ^ (padicExp S p u)` in `QuadraticAlgebra ℤ d 0`. -/
private theorem pow_padicExp_dvd_transformed_row {d : ℤ} {R S N p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hinert : jacobiSym d p = -1) (u : Fin R × Fin S)
    (k : Fin N × Fin N × Fin N) :
    ((p : ℤ) : QuadraticAlgebra ℤ d 0) ^ padicExp S p u ∣
      ∑ v : Fin R × Fin S, unitriMat R S p u v • gridVec d R S N v k := by
  have hph : p * padicExp S p u ≤ u.1.1 :=
    (Nat.mul_le_mul_left p (min_le_left _ _)).trans (Nat.mul_div_le u.1.1 p)
  rw [transformed_row_eq_binomial, ← eval_iterate_derivative_basis_eq hph]
  have hcong := frobenius_dvd_zPt_pow_sub_zConj hp hodd hinert k.1.1 k.2.1.1
  have hdvd :=
    pow_dvd_eval_iterate_derivative_basis (p := p) hcong u.1.1 u.2.1 (padicExp S p u) k.2.2.1
  simpa only [Int.cast_natCast] using hdvd

/-- Entry formula for the conjugated Gram matrix `U * intGram d R S N * Uᵀ`. -/
private theorem transformed_gram_entry {d : ℤ} {R S N : ℕ}
    (U : Matrix (Fin R × Fin S) (Fin R × Fin S) ℤ) (u v : Fin R × Fin S) :
    (U * intGram d R S N * Uᵀ) u v =
      ∑ k : Fin N × Fin N × Fin N,
        ((∑ a, U u a • gridVec d R S N a k).re * (∑ b, U v b • gridVec d R S N b k).re +
          |d| * (∑ a, U u a • gridVec d R S N a k).im * (∑ b, U v b • gridVec d R S N b k).im) := by
  have hre (u' : Fin R × Fin S) (k : Fin N × Fin N × Fin N) :
      (∑ a, U u' a • gridVec d R S N a k).re = ∑ a, U u' a * (gridVec d R S N a k).re := by
    simp [qa_re_sum]
  have him (u' : Fin R × Fin S) (k : Fin N × Fin N × Fin N) :
      (∑ a, U u' a • gridVec d R S N a k).im = ∑ a, U u' a * (gridVec d R S N a k).im := by
    simp [qa_im_sum]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, intGram, Matrix.of_apply,
    Finset.sum_mul, Finset.mul_sum, hre, him]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.sum_comm] <;>
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- **`p`-adic divisibility of the Gram determinant.** For every odd prime `p` with
`jacobiSym d p = -1`, `p ^ (2 ∑_{r, s} min (r / p) (S - 1 - s))` divides `(intGram d R S N).det`. -/
private theorem pow_two_mul_sum_padicExp_dvd_det_intGram {d : ℤ} {R S N p : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hinert : jacobiSym d p = -1) :
    (p : ℤ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u) ∣ (intGram d R S N).det := by
  let U := unitriMat R S p
  let Gw := U * intGram d R S N * Uᵀ
  have hdet : Gw.det = (intGram d R S N).det := by
    simp [Gw, Matrix.det_mul, Matrix.det_transpose, U, det_unitriMat]
  rw [← hdet]
  have hGw_dvd (u v : Fin R × Fin S) :
      (p : ℤ) ^ (padicExp S p u + padicExp S p v) ∣ Gw u v := by
    change (p : ℤ) ^ _ ∣ (U * intGram d R S N * Uᵀ) u v
    rw [transformed_gram_entry U u v]
    refine Finset.dvd_sum fun k _ ↦ ?_
    have hu := dvd_quadraticAlgebra_iff.mp (by
      simpa only [← Int.cast_pow] using pow_padicExp_dvd_transformed_row hp hodd hinert u k)
    have hv := dvd_quadraticAlgebra_iff.mp (by
      simpa only [← Int.cast_pow] using pow_padicExp_dvd_transformed_row hp hodd hinert v k)
    rw [pow_add]
    refine dvd_add (mul_dvd_mul hu.1 hv.1) ?_
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right (mul_dvd_mul hu.2 hv.2) |d|
  rw [Matrix.det_apply]
  refine Finset.dvd_sum fun σ _ ↦ ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine dvd_mul_of_dvd_right ?_ _
  have hprod_pow : (p : ℤ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u) =
      ∏ u : Fin R × Fin S, (p : ℤ) ^ (padicExp S p (σ u) + padicExp S p u) := by
    simp_rw [pow_add, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Equiv.sum_comp σ (padicExp S p), ← pow_add, two_mul]
  rw [hprod_pow]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun u _ ↦ hGw_dvd (σ u) u

/-- Lower bound on `log (det (intGram d R S N))` from all odd inert primes in a finite set `P'`. -/
private theorem sum_padicExp_log_le_log_det_intGram {d : ℤ} {R S N : ℕ}
    (hdet : 0 < (intGram d R S N).det) {P' : Finset ℕ}
    (hP' : ∀ p ∈ P', p.Prime ∧ Odd p ∧ jacobiSym d p = -1) :
    ∑ p ∈ P', (2 * (∑ u : Fin R × Fin S, padicExp S p u : ℝ)) * Real.log p ≤
      Real.log ((intGram d R S N).det : ℝ) := by
  have hdvd : ∏ p ∈ P', (p : ℤ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u) ∣
      (intGram d R S N).det := by
    refine Finset.prod_dvd_of_coprime ?_ fun p hp ↦ ?_
    · intro p hp q hq hne
      have hcop : Nat.Coprime p q := (Nat.coprime_primes (hP' p hp).1 (hP' q hq).1).mpr hne
      exact (Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcop)).pow
    · exact pow_two_mul_sum_padicExp_dvd_det_intGram (hP' p hp).1 (hP' p hp).2.1 (hP' p hp).2.2
  have hleR : (∏ p ∈ P', (p : ℝ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u)) ≤
      ((intGram d R S N).det : ℝ) := by exact_mod_cast Int.le_of_dvd hdet hdvd
  have hpos : 0 < ∏ p ∈ P', (p : ℝ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u) :=
    Finset.prod_pos fun p hp ↦ pow_pos (Nat.cast_pos.mpr (hP' p hp).1.pos) _
  calc ∑ p ∈ P', (2 * (∑ u : Fin R × Fin S, padicExp S p u : ℝ)) * Real.log p
      = ∑ p ∈ P', Real.log ((p : ℝ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u)) := by
        refine Finset.sum_congr rfl fun p _ ↦ ?_; rw [Real.log_pow]; push_cast; rfl
    _ = Real.log (∏ p ∈ P', (p : ℝ) ^ (2 * ∑ u : Fin R × Fin S, padicExp S p u)) := by
        rw [Real.log_prod fun p hp ↦ pow_ne_zero _ (Nat.cast_ne_zero.mpr (hP' p hp).1.ne_zero)]
    _ ≤ Real.log ((intGram d R S N).det : ℝ) := Real.log_le_log hpos hleR

end PadicDivisibility

/-! ### Elementary parameter estimates and assembly for squarefree `d ≠ 1` -/

section Assembly

/-- Elementary lower bound `∑_{s < S} min k (S - 1 - s) ≥ S k - k²`. -/
private theorem sum_min_sub_ge (S k : ℕ) :
    (S : ℝ) * k - (k : ℝ) ^ 2 ≤ ∑ s : Fin S, ((min k (S - 1 - s.1) : ℕ) : ℝ) := by
  rcases le_or_gt S k with hSk | hkS
  · have hnonpos : (S : ℝ) * k - (k : ℝ) ^ 2 ≤ 0 := by
      have : (S : ℝ) ≤ k := by exact_mod_cast hSk
      nlinarith
    exact hnonpos.trans (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  · let T : Finset (Fin S) := Finset.univ.filter fun s : Fin S ↦ s.1 < S - k
    have hcard : T.card = S - k := by
      have heq : T = (Finset.range (S - k)).attach.map
          ⟨fun x ↦ ⟨x.1, (Finset.mem_range.mp x.2).trans_le (Nat.sub_le S k)⟩,
            fun x y h ↦ Subtype.ext (by simpa using congrArg Fin.val h)⟩ := by
        ext s
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Finset.mem_attach, true_and]
        exact ⟨fun hs ↦ ⟨⟨s.1, Finset.mem_range.mpr hs⟩, rfl⟩,
          fun ⟨⟨x, hx⟩, h⟩ ↦ h ▸ Finset.mem_range.mp hx⟩
      rw [heq, Finset.card_map, Finset.card_attach, Finset.card_range]
    have hsumT : ∑ s ∈ T, ((min k (S - 1 - s.1) : ℕ) : ℝ) = ((S - k : ℕ) : ℝ) * k := by
      have hconst : ∀ s ∈ T, min k (S - 1 - s.1) = k := fun s hs ↦
        min_eq_left (by have := (Finset.mem_filter.mp hs).2; omega)
      calc ∑ s ∈ T, ((min k (S - 1 - s.1) : ℕ) : ℝ)
          = ∑ _s ∈ T, (k : ℝ) := Finset.sum_congr rfl fun s hs ↦ by rw [hconst s hs]
        _ = ((S - k : ℕ) : ℝ) * k := by simp [hcard]
    have hsub : ((S - k : ℕ) : ℝ) * k = (S : ℝ) * k - (k : ℝ) ^ 2 := by
      rw [Nat.cast_sub hkS.le]; ring
    rw [← hsub, ← hsumT]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ ↦ Nat.cast_nonneg _

/-- Lower bound on `2 ∑_{r, s} padicExp S p (r, s)` in terms of `R`, `S`, and `p`. -/
private theorem two_mul_sum_padicExp_ge (R S p : ℕ) (hp : 0 < p) :
    (R : ℝ) ^ 2 * S / p - (R : ℝ) * S / p - 2 * R * S - 2 * (R : ℝ) ^ 3 / (p : ℝ) ^ 2 ≤
      2 * (∑ u : Fin R × Fin S, (padicExp S p u : ℝ)) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hrow (r : Fin R) :
      (S : ℝ) * ((r.1 : ℝ) / p - 1) - ((r.1 : ℝ) / p) ^ 2 ≤
        ∑ s : Fin S, (padicExp S p (r, s) : ℝ) := by
    refine le_trans ?_ (sum_min_sub_ge S (r.1 / p))
    have hdiv_le : ((r.1 / p : ℕ) : ℝ) ≤ (r.1 : ℝ) / p := Nat.cast_div_le
    have hdiv_ge : (r.1 : ℝ) / p - 1 ≤ ((r.1 / p : ℕ) : ℝ) := by
      have hlt : r.1 < p * (r.1 / p + 1) := by
        have := Nat.div_add_mod r.1 p; have := Nat.mod_lt r.1 hp; nlinarith
      have hltR : (r.1 : ℝ) < p * (((r.1 / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt
      rw [sub_le_iff_le_add, div_le_iff₀ hpR]; linarith
    have hsq : (((r.1 / p : ℕ) : ℝ) ^ 2) ≤ ((r.1 : ℝ) / p) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv_le 2
    nlinarith [Nat.cast_nonneg (α := ℝ) S]
  have hsum_r2 : ∑ r : Fin R, (r.1 : ℝ) ^ 2 ≤ (R : ℝ) ^ 3 := by
    calc ∑ r : Fin R, (r.1 : ℝ) ^ 2
        ≤ ∑ _r : Fin R, (R : ℝ) ^ 2 := Finset.sum_le_sum fun r _ ↦
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast r.2.le) 2
      _ = (R : ℝ) ^ 3 := by simp [pow_succ, mul_assoc]
  have htot := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) ↦ hrow r
  have hprod : ∑ u : Fin R × Fin S, (padicExp S p u : ℝ) =
      ∑ r : Fin R, ∑ s : Fin S, (padicExp S p (r, s) : ℝ) := Fintype.sum_prod_type _
  rw [← hprod] at htot
  have hsimp : ∑ r : Fin R, ((S : ℝ) * ((r.1 : ℝ) / p - 1) - ((r.1 : ℝ) / p) ^ 2) =
      (S : ℝ) / p * (∑ r : Fin R, (r.1 : ℝ)) - R * S -
        (1 / (p : ℝ) ^ 2) * ∑ r : Fin R, (r.1 : ℝ) ^ 2 := by
    simp_rw [mul_sub, mul_one, div_pow, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  rw [hsimp, sum_fin_val_eq R] at htot
  have hmul2 : (1 / (p : ℝ) ^ 2) * ∑ r : Fin R, (r.1 : ℝ) ^ 2 ≤ (R : ℝ) ^ 3 / (p : ℝ) ^ 2 := by
    rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hsum_r2 (sq_nonneg _)
  have hmain : (S : ℝ) / p * ((R : ℝ) * ((R : ℝ) - 1) / 2) =
      ((R : ℝ) ^ 2 * S / p - (R : ℝ) * S / p) / 2 := by ring
  linarith [show 2 * (R : ℝ) * S = 2 * ((R : ℝ) * S) by ring,
    show 2 * (R : ℝ) ^ 3 / (p : ℝ) ^ 2 = 2 * ((R : ℝ) ^ 3 / (p : ℝ) ^ 2) by ring]

/-- Parameter bounds for `R ≥ 36`, `S = R / 18`, and the minimal `N` with `R ^ 2 ≤ N ^ 3`. -/
private theorem exists_grid_params {R : ℕ} (hR : 36 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ N ≤ R ∧ R ^ 2 ≤ N ^ 3 ∧ N ^ 3 ≤ 8 * R ^ 2 ∧
      N * R + N * (R / 18) + 2 * R * (R / 18) < N ^ 3 := by
  have hex : ∃ n : ℕ, R ^ 2 ≤ n ^ 3 := ⟨R, by nlinarith⟩
  classical
  let N := Nat.find hex
  have hRN : R ^ 2 ≤ N ^ 3 := Nat.find_spec hex
  have hNR : N ≤ R := Nat.find_min' hex (by nlinarith)
  have hN2 : 2 ≤ N := by
    by_contra h
    have hpow1 : N ^ 3 ≤ 1 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    nlinarith
  have hprev : (N - 1) ^ 3 < R ^ 2 := Nat.lt_of_not_ge (Nat.find_min hex (by omega))
  have hN8 : N ^ 3 ≤ 8 * R ^ 2 := by
    have h3 : N ^ 3 ≤ (2 * (N - 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h4 : (2 * (N - 1)) ^ 3 = 8 * (N - 1) ^ 3 := by ring
    omega
  have h9R : 9 * R < 4 * N ^ 2 := by
    refine lt_of_pow_lt_pow_left₀ 3 (Nat.zero_le _) ?_
    have h729 : 729 * R ^ 3 < 64 * R * R ^ 3 :=
      Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega) 3)
    calc (9 * R) ^ 3 = 729 * R ^ 3 := by ring
      _ < 64 * R * R ^ 3 := h729
      _ = 64 * (R ^ 2) ^ 2 := by ring
      _ ≤ 64 * (N ^ 3) ^ 2 := Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hRN 2)
      _ = (4 * N ^ 2) ^ 3 := by ring
  have hS : 18 * (R / 18) ≤ R := Nat.mul_div_le R 18
  have hparam : N * R + N * (R / 18) + 2 * R * (R / 18) < N ^ 3 := by
    have h9 : 9 * (N * R + N * (R / 18) + 2 * R * (R / 18)) < 9 * N ^ 3 := by
      have h1 : N * (R / 18) ≤ N * R := Nat.mul_le_mul_left N (Nat.div_le_self R 18)
      have h3 : R * (18 * (R / 18)) ≤ R ^ 2 := by nlinarith
      have h4 : 18 * (N * R) < 8 * N ^ 3 := by nlinarith
      nlinarith
    omega
  exact ⟨N, hN2, hNR, hRN, hN8, hparam⟩

/-- Elementary bound `(3 log N + 2 N log R) / R ≤ 2 log 8 + 9` when `2 ≤ N ≤ R` and
`N ^ 3 ≤ 8 R ^ 2`. -/
private theorem archimedean_error_le {R N : ℕ} (hN2 : 2 ≤ N) (hNR : N ≤ R)
    (hN8 : N ^ 3 ≤ 8 * R ^ 2) :
    (3 * Real.log N + 2 * N * Real.log R) / R ≤ 2 * Real.log 8 + 9 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hlogN : Real.log N ≤ R := (Real.log_le_sub_one_of_pos hNpos).trans (by
    have : (N : ℝ) ≤ R := by exact_mod_cast hNR
    linarith)
  have h1 : 3 * Real.log N / R ≤ 3 := by rw [div_le_iff₀ hRpos]; linarith
  have hcube : (R : ℝ) ≤ 8 * ((R : ℝ) / N) ^ 3 := by
    have h8 : (N : ℝ) ^ 3 ≤ 8 * (R : ℝ) ^ 2 := by exact_mod_cast hN8
    rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hNpos 3)]; nlinarith
  have hlogR : Real.log R ≤ Real.log 8 + 3 * ((R : ℝ) / N) := by
    have hqpos : 0 < (R : ℝ) / N := div_pos hRpos hNpos
    refine (Real.log_le_log hRpos hcube).trans ?_
    rw [Real.log_mul (by norm_num) (pow_ne_zero 3 hqpos.ne'), Real.log_pow]
    have hlogq : Real.log ((R : ℝ) / N) ≤ (R : ℝ) / N :=
      (Real.log_le_sub_one_of_pos hqpos).trans (by linarith)
    linarith
  have h2 : 2 * N * Real.log R / R ≤ 2 * Real.log 8 + 6 := by
    have hNR' : (N : ℝ) / R ≤ 1 := (div_le_one hRpos).mpr (by exact_mod_cast hNR)
    have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    calc 2 * (N : ℝ) * Real.log R / R
        = 2 * ((N : ℝ) / R) * Real.log R := by ring
      _ ≤ 2 * ((N : ℝ) / R) * (Real.log 8 + 3 * ((R : ℝ) / N)) := by gcongr
      _ = 2 * ((N : ℝ) / R) * Real.log 8 + 6 := by field_simp; ring
      _ ≤ 2 * 1 * Real.log 8 + 6 := by nlinarith
      _ = 2 * Real.log 8 + 6 := by ring
  rw [add_div]; linarith

/-- Splitting off `p = 2` from a filtered `Nat.primesLE` sum costs at most `log 2 / 2`. -/
private theorem sum_filter_primesLE_le_add_odd {N : ℕ} {P : ℕ → Prop} [DecidablePred P] :
    ∑ p ∈ (Nat.primesLE N).filter P, Real.log p / p ≤
      Real.log 2 / 2 + ∑ p ∈ (Nat.primesLE N).filter (fun p ↦ P p ∧ Odd p), Real.log p / p := by
  rw [← Finset.sum_filter_add_sum_filter_not ((Nat.primesLE N).filter P) Odd, add_comm]
  refine add_le_add ?_ ?_
  · have hsub : ((Nat.primesLE N).filter P).filter (fun p ↦ ¬ Odd p) ⊆ {2} := by
      intro p hp
      have hpr := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
      have hnot : ¬ Odd p := (Finset.mem_filter.mp hp).2
      exact Finset.mem_singleton.mpr (by by_contra hne; exact hnot (hpr.odd_of_ne_two hne))
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦ ?_).trans (by simp)
    rw [Finset.mem_singleton.mp hp]; positivity
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun p hp _ ↦ ?_
    · rw [Finset.mem_filter, Finset.mem_filter] at hp
      exact Finset.mem_filter.mpr ⟨hp.1.1, hp.1.2, hp.2⟩
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast
        (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).one_lt.le)) (Nat.cast_nonneg _)

/-- Comparing the `p`-adic lower bound and the Hadamard upper bound on `log (det (intGram d R S N))`
and dividing by `R ^ 2 * S`. -/
private theorem inert_sum_master_bound {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) {R S N : ℕ}
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hN : 1 ≤ N) (hparam : N * R + N * S + 2 * R * S < N ^ 3)
    {P' : Finset ℕ} (hP' : ∀ p ∈ P', p.Prime ∧ Odd p ∧ jacobiSym d p = -1) :
    ∑ p ∈ P', Real.log p / p ≤
      (1 + (S : ℝ) / R) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) +
        (3 * Real.log N + 2 * N * Real.log R) / R +
        (∑ p ∈ P', Real.log p / p) / R + 2 * (∑ p ∈ P', Real.log p) / R +
        2 * (R : ℝ) / S * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) := by
  obtain ⟨hdet_pos, hdet_ub⟩ := log_det_intGram_le hd hd1 hR hN hparam
  have hlb := sum_padicExp_log_le_log_det_intGram hdet_pos hP'
  have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hSpos : (0 : ℝ) < S := Nat.cast_pos.mpr (by omega)
  have hR2S : (0 : ℝ) < (R : ℝ) ^ 2 * S := mul_pos (sq_pos_of_pos hRpos) hSpos
  have hlb2 : (R : ℝ) ^ 2 * S * (∑ p ∈ P', Real.log p / p) -
      (R : ℝ) * S * (∑ p ∈ P', Real.log p / p) - 2 * R * S * (∑ p ∈ P', Real.log p) -
      2 * (R : ℝ) ^ 3 * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) ≤
      Real.log ((intGram d R S N).det : ℝ) := by
    refine le_trans ?_ hlb
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    have hp_pr := (hP' p hp).1
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_pr.one_lt.le)
    have hmul := mul_le_mul_of_nonneg_right (two_mul_sum_padicExp_ge R S p hp_pr.pos) hlogp
    linarith [show ((R : ℝ) ^ 2 * S / p - (R : ℝ) * S / p - 2 * R * S -
        2 * (R : ℝ) ^ 3 / (p : ℝ) ^ 2) * Real.log p =
        (R : ℝ) ^ 2 * S * (Real.log p / p) - (R : ℝ) * S * (Real.log p / p) -
        2 * R * S * Real.log p - 2 * (R : ℝ) ^ 3 * (Real.log p / (p : ℝ) ^ 2) by ring]
  have hmul_div := (div_le_div_iff_of_pos_right hR2S).mpr (hlb2.trans hdet_ub)
  have heqL : ((R : ℝ) ^ 2 * S * (∑ p ∈ P', Real.log p / p) -
      (R : ℝ) * S * (∑ p ∈ P', Real.log p / p) - 2 * R * S * (∑ p ∈ P', Real.log p) -
      2 * (R : ℝ) ^ 3 * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2)) / ((R : ℝ) ^ 2 * S) =
      (∑ p ∈ P', Real.log p / p) - (∑ p ∈ P', Real.log p / p) / R -
      2 * (∑ p ∈ P', Real.log p) / R -
      2 * (R : ℝ) / S * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) := by field_simp
  have heqR : ((R : ℝ) * S * (3 * Real.log N + 2 * N * Real.log R) +
      (R : ℝ) * S * ((R : ℝ) + S) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|)) /
      ((R : ℝ) ^ 2 * S) =
      (3 * Real.log N + 2 * N * Real.log R) / R +
      (1 + (S : ℝ) / R) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by field_simp
  rw [heqL, heqR] at hmul_div; linarith

/-- Main-term estimate `(1 + S / R) log (2 N √|d|) ≤ (3 / 4) log x + (19 / 9) log 2`. -/
private theorem inert_sum_main_term_le {d : ℤ} (hd0 : d ≠ 0) {R S N : ℕ} {x : ℝ} (hR : 1 ≤ R)
    (hN : 1 ≤ N) (hRx : (R : ℝ) ≤ x) (hS_le : (S : ℝ) ≤ (R : ℝ) / 18) (hN8 : N ^ 3 ≤ 8 * R ^ 2)
    (hdx : (|d| : ℝ) ^ (18 : ℕ) ≤ x) :
    (1 + (S : ℝ) / R) * Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ≤
      3 / 4 * Real.log x + 19 / 9 * Real.log 2 := by
  have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hdpos : (0 : ℝ) < |(d : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hd0)
  have hlogR_le : Real.log R ≤ Real.log x := Real.log_le_log hRpos hRx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (le_trans (by exact_mod_cast hR) hRx)
  have hlogN_le : Real.log N ≤ Real.log 2 + 2 / 3 * Real.log x := by
    have hlog := Real.log_le_log (pow_pos hNpos 3) (by exact_mod_cast hN8 : (N : ℝ) ^ 3 ≤ 8 * R ^ 2)
    rw [Real.log_pow, Real.log_mul (by norm_num) (pow_ne_zero 2 hRpos.ne'), Real.log_pow,
      show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow] at hlog
    push_cast at hlog; linarith
  have hlogd_le : Real.log |(d : ℝ)| ≤ 1 / 18 * Real.log x := by
    have hlog := Real.log_le_log (pow_pos hdpos 18) hdx
    rw [Real.log_pow] at hlog; push_cast at hlog; linarith
  have hM_le : Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) ≤
      2 * Real.log 2 + 25 / 36 * Real.log x := by
    rw [Real.log_mul (mul_ne_zero two_ne_zero hNpos.ne') (Real.sqrt_pos.mpr hdpos).ne',
      Real.log_mul two_ne_zero hNpos.ne', Real.log_sqrt hdpos.le]
    linarith
  have hSR : 1 + (S : ℝ) / R ≤ 19 / 18 := by
    have : (S : ℝ) / R ≤ 1 / 18 := (div_le_iff₀ hRpos).mpr (by linarith); linarith
  have hlogM_nn : 0 ≤ Real.log (2 * (N : ℝ) * Real.sqrt |(d : ℝ)|) := by
    apply Real.log_nonneg
    have hsq1 : 1 ≤ Real.sqrt |(d : ℝ)| := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ |(d : ℝ)| by exact_mod_cast Int.one_le_abs hd0)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have h1 := mul_le_mul hSR hM_le hlogM_nn (by norm_num : (0 : ℝ) ≤ 19 / 18)
  linarith

/-- Prime-sum error estimates for `P' ⊆ Nat.primesLE R` when `1 ≤ S` and `R ≤ 27 * S`. -/
private theorem inert_sum_prime_errors_le {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hRS : (R : ℝ) ≤ 27 * S) {P' : Finset ℕ} (hP'sub : P' ⊆ Nat.primesLE R) :
    (∑ p ∈ P', Real.log p / p) / R + 2 * (∑ p ∈ P', Real.log p) / R +
        2 * (R : ℝ) / S * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) ≤
      1 + 56 * Real.log 4 := by
  have hRpos : (0 : ℝ) < R := Nat.cast_pos.mpr (by omega)
  have hSpos : (0 : ℝ) < S := Nat.cast_pos.mpr (by omega)
  have hpr : ∀ p ∈ P', p.Prime := fun p hp ↦ Nat.prime_of_mem_primesLE (hP'sub hp)
  have hterm3 : (∑ p ∈ P', Real.log p / p) / R ≤ 1 := by
    rw [div_le_one hRpos]
    have hsub : P' ⊆ Finset.Icc 1 R := fun p hp ↦
      Finset.mem_Icc.mpr ⟨(hpr p hp).one_lt.le, Nat.le_of_mem_primesLE (hP'sub hp)⟩
    calc ∑ p ∈ P', Real.log p / p
        ≤ ∑ _p ∈ P', (1 : ℝ) := Finset.sum_le_sum fun p hp ↦ by
          have hppos : (0 : ℝ) < p := Nat.cast_pos.mpr (hpr p hp).pos
          rw [div_le_one hppos]; exact (Real.log_le_sub_one_of_pos hppos).trans (by linarith)
      _ = (P'.card : ℝ) := by simp
      _ ≤ ((Finset.Icc 1 R).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = R := by simp
  have hterm4 : 2 * (∑ p ∈ P', Real.log p) / R ≤ 2 * Real.log 4 := by
    have htheta : ∑ p ∈ P', Real.log p ≤ Chebyshev.theta R := by
      rw [Chebyshev.theta_eq_sum_Icc, ← Nat.primesLE_eq_filter_Icc_zero, Nat.floor_natCast]
      exact Finset.sum_le_sum_of_subset_of_nonneg hP'sub fun p hp _ ↦
        Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le)
    have hle := htheta.trans (Chebyshev.theta_le_log4_mul_x hRpos.le)
    rw [div_le_iff₀ hRpos]; linarith
  have hterm5 : 2 * (R : ℝ) / S * (∑ p ∈ P', Real.log p / (p : ℝ) ^ 2) ≤ 54 * Real.log 4 := by
    have htail := TauCeti.sum_log_div_sq_le_of_prime (y := 2) zero_lt_two hpr
      (fun p hp ↦ by exact_mod_cast (hpr p hp).two_le)
    have hRS' : 2 * (R : ℝ) / S ≤ 54 := by rw [div_le_iff₀ hSpos]; linarith
    have hsum_nn : 0 ≤ ∑ p ∈ P', Real.log p / (p : ℝ) ^ 2 :=
      Finset.sum_nonneg fun p hp ↦
        div_nonneg (Real.log_nonneg (by exact_mod_cast (hpr p hp).one_lt.le)) (sq_nonneg _)
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  linarith

/-- The explicit universal constant used in the inert-prime sum bound. -/
private noncomputable def inertConst : ℝ :=
  Real.log 36 + 57 * Real.log 4 + 2 * Real.log 8 + 3 * Real.log 2 + 14

private theorem inertConst_nonneg : 0 ≤ inertConst := by
  have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have : 0 ≤ Real.log 36 := Real.log_nonneg (by norm_num)
  rw [inertConst]; linarith

/-- Inert-prime sum bound for squarefree `d ≠ 1` and `x ≥ max 36 (|d| ^ 18)`. -/
private theorem sum_primesLE_jacobiSym_le_of_squarefree_large {d : ℤ} (hd : Squarefree d)
    (hd1 : d ≠ 1) {x : ℝ} (hx36 : 36 ≤ x) (hdx : (|d| : ℝ) ^ (18 : ℕ) ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1 ∧ Odd p), Real.log p / p ≤
      3 / 4 * Real.log x + (56 * Real.log 4 + 2 * Real.log 8 + 19 / 9 * Real.log 2 + 10) := by
  set R := ⌊x⌋₊
  have hR36 : 36 ≤ R := Nat.le_floor hx36
  set S := R / 18
  have hS_le : (S : ℝ) ≤ (R : ℝ) / 18 := Nat.cast_div_le
  have hR_le_S : (R : ℝ) ≤ 27 * (S : ℝ) := by exact_mod_cast (show R ≤ 27 * S by omega)
  obtain ⟨N, hN2, hNR, _, hN8, hparam⟩ := exists_grid_params hR36
  set P' := (Nat.primesLE R).filter (fun p ↦ jacobiSym d p = -1 ∧ Odd p)
  have hP'_prop : ∀ p ∈ P', p.Prime ∧ Odd p ∧ jacobiSym d p = -1 := fun p hp ↦ by
    obtain ⟨hm, hj, ho⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.prime_of_mem_primesLE hm, ho, hj⟩
  have hmaster := inert_sum_master_bound hd hd1 (by omega) (by omega) (by omega) hparam hP'_prop
  have hmain := inert_sum_main_term_le hd.ne_zero (by omega) (by omega) (Nat.floor_le (by linarith))
    hS_le hN8 hdx
  have harch := archimedean_error_le hN2 hNR hN8
  have herr :=
    inert_sum_prime_errors_le (P' := P') (by omega) (by omega) hR_le_S (Finset.filter_subset _ _)
  linarith

/-- Inert-prime sum bound for squarefree `d ≠ 1` and all `x ≥ 1` with `|d| ^ 18 ≤ x`. -/
private theorem sum_primesLE_jacobiSym_le_of_squarefree {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) (hdx : (|d| : ℝ) ^ (18 : ℕ) ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1), Real.log p / p ≤
      3 / 4 * Real.log x + inertConst := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hlog36 : 0 ≤ Real.log 36 := Real.log_nonneg (by norm_num)
  rcases lt_or_ge x 36 with hlt | hge
  · have hsub : ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1), Real.log p / p ≤
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p hp _ ↦
        div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le))
          (Nat.cast_nonneg _)
    have hmert := hsub.trans (Chebyshev.sum_primesLE_log_div_le hx)
    have hlogx_le : Real.log x ≤ Real.log 36 := Real.log_le_log (by linarith) hlt.le
    rw [inertConst]; linarith
  · have hsplit := sum_filter_primesLE_le_add_odd (N := ⌊x⌋₊) (P := fun p ↦ jacobiSym d p = -1)
    have hlarge := sum_primesLE_jacobiSym_le_of_squarefree_large hd hd1 hge hdx
    rw [inertConst]; linarith

end Assembly

/-! ### Public inert-prime sum bounds -/

/-- **Inert-prime sum bound for Jacobi symbols.** There is an absolute constant `K` such that for
every integer `d` and every real `x ≥ 1` with `|d| ^ 18 ≤ x`,
`∑_{p ≤ x, jacobiSym d p = -1} log p / p ≤ (3 / 4) log x + K`. -/
theorem sum_primesLE_jacobiSym_eq_neg_one_log_div_le :
    ∃ K : ℝ, ∀ (d : ℤ) (x : ℝ), 1 ≤ x → (|d| : ℝ) ^ (18 : ℕ) ≤ x →
      ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1), Real.log p / p ≤
        3 / 4 * Real.log x + K := by
  refine ⟨inertConst, fun d x hx hdx ↦ ?_⟩
  have hK_nn : 0 ≤ inertConst := inertConst_nonneg
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx
  rcases eq_or_ne d 0 with rfl | hd0
  · have hempty : (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym 0 p = -1) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun p hp ↦ by
        rw [jacobiSym.zero_left (Nat.prime_of_mem_primesLE hp).one_lt]; norm_num
    rw [hempty, Finset.sum_empty]; linarith
  · obtain ⟨m, d₀, hmd, hsf_d₀⟩ := _root_.exists_sq_mul_squarefree d
    have hm0 : m ≠ 0 := fun h ↦ hd0 (by rw [← hmd, h]; simp)
    have hd₀_abs : |d₀| ≤ |d| := by
      have hm1 : (1 : ℤ) ≤ m ^ 2 := by
        have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0; nlinarith [sq_abs m]
      rw [← hmd, abs_mul, abs_of_nonneg (sq_nonneg m)]; nlinarith [abs_nonneg d₀]
    have hd₀_x : (|d₀| : ℝ) ^ (18 : ℕ) ≤ x :=
      (pow_le_pow_left₀ (abs_nonneg _) (by exact_mod_cast hd₀_abs) 18).trans hdx
    have hsub : (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1) ⊆
        (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d₀ p = -1) := by
      intro p hp
      obtain ⟨hpm, hj⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_filter.mpr ⟨hpm, ?_⟩
      rw [← hmd, jacobiSym.mul_left, sq, jacobiSym.mul_left] at hj
      rcases jacobiSym.trichotomy m p with h0 | h1 | hn1
      · simp [h0] at hj
      · simpa [h1] using hj
      · simpa [hn1] using hj
    have hle_d₀ : ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d p = -1), Real.log p / p ≤
        ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym d₀ p = -1), Real.log p / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦
        div_nonneg (Real.log_nonneg (by exact_mod_cast
          (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).one_lt.le)) (Nat.cast_nonneg _)
    rcases eq_or_ne d₀ 1 with rfl | hd₀1
    · have hempty : (Nat.primesLE ⌊x⌋₊).filter (fun p ↦ jacobiSym 1 p = -1) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun p _ ↦ by rw [jacobiSym.one_left]; norm_num
      rw [hempty, Finset.sum_empty] at hle_d₀; linarith
    · exact hle_d₀.trans (sum_primesLE_jacobiSym_le_of_squarefree hsf_d₀ hd₀1 hx hd₀_x)

end TauCeti

namespace DirichletCharacter

private theorem neg_one_ne_zero_of_two {R : Type*} [CommRing R] [NeZero (2 : R)] :
    (-1 : R) ≠ 0 := fun h ↦ by
  have h1 : (1 : R) = 0 := by simpa using congrArg Neg.neg h
  exact NeZero.ne (2 : R) (by rw [← one_add_one_eq_two, h1, add_zero])

private theorem neg_one_ne_one_of_two {R : Type*} [CommRing R] [NeZero (2 : R)] :
    (-1 : R) ≠ 1 := fun h ↦
  NeZero.ne (2 : R) (by rw [← one_add_one_eq_two]; linear_combination -h)

private theorem primitiveCharacter_apply_eq_neg_one {R : Type*} [CommRing R] [NeZero (2 : R)]
    {q : ℕ} [NeZero q] (χ : DirichletCharacter R q) {p : ℕ} (hp : χ (p : ZMod q) = -1) :
    χ.primitiveCharacter (p : ZMod χ.conductor) = -1 := by
  have hu : IsUnit (p : ZMod q) := by
    by_contra hnu; exact neg_one_ne_zero_of_two (hp.symm.trans (MulChar.map_nonunit χ hnu))
  have hcop : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((ZMod.isUnit_iff_coprime p q).mp hu)
  simpa only [Int.cast_natCast, hp] using χ.primitiveCharacter_apply_of_isCoprime hcop

private theorem filter_primesLE_odd_subset_jacobiSym {R : Type*} [CommRing R] [NeZero (2 : R)]
    [DecidableEq R] {q : ℕ} [NeZero q] {χ : DirichletCharacter R q} {d : ℤ} {N : ℕ}
    (hd_val : ∀ n : ℕ, _root_.Odd n →
      χ.primitiveCharacter (n : ZMod χ.conductor) = (jacobiSym d n : R)) :
    (Nat.primesLE N).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1 ∧ _root_.Odd p) ⊆
      (Nat.primesLE N).filter (fun p ↦ jacobiSym d p = -1) := by
  intro p hp
  obtain ⟨hpm, hχp, hodd⟩ := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr ⟨hpm, ?_⟩
  have hv : (jacobiSym d p : R) = -1 :=
    (hd_val p hodd).symm.trans (primitiveCharacter_apply_eq_neg_one χ hχp)
  rcases jacobiSym.trichotomy d p with h0 | h1 | hn1
  · exact absurd (by simpa [h0] using hv.symm) neg_one_ne_zero_of_two
  · exact absurd (by simpa [h1] using hv.symm) neg_one_ne_one_of_two
  · exact hn1

/-- **Inert-prime sum bound for quadratic Dirichlet characters.** There is an absolute constant `K`
such that for every commutative ring `R` with `2 ≠ 0`, every level `q ≠ 0`, every quadratic
Dirichlet character `χ : DirichletCharacter R q`, and every real `x ≥ q ^ 18`,
`∑_{p ≤ x, χ(p) = -1} log p / p ≤ (3 / 4) log x + K`. -/
theorem sum_primesLE_eq_neg_one_log_div_le :
    ∃ K : ℝ, ∀ {R : Type*} [CommRing R] [NeZero (2 : R)] [DecidableEq R]
      {q : ℕ} [NeZero q] (χ : DirichletCharacter R q), χ.IsQuadratic →
      ∀ x : ℝ, (q : ℝ) ^ (18 : ℕ) ≤ x →
        ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1), Real.log p / p ≤
          3 / 4 * Real.log x + K := by
  obtain ⟨K, hK⟩ := TauCeti.sum_primesLE_jacobiSym_eq_neg_one_log_div_le
  refine ⟨max K 0 + Real.log 2 / 2, fun {R} _ _ _ {q} _ χ hquad x hx ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hx1 : 1 ≤ x := (one_le_pow₀ hq1).trans hx
  have hlogx_nn : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog2_nn : 0 ≤ Real.log 2 / 2 := div_nonneg (Real.log_nonneg (by norm_num)) zero_le_two
  let ψ := χ.primitiveCharacter
  have : NeZero χ.conductor := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne q) χ.conductor_dvd_level⟩
  by_cases hψ1 : ψ = 1
  · have hempty : (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun p _ hp ↦ ?_
      have hv := primitiveCharacter_apply_eq_neg_one χ hp
      rw [show χ.primitiveCharacter = 1 from hψ1] at hv
      have hu : IsUnit (p : ZMod χ.conductor) := by
        by_contra hnu
        exact neg_one_ne_zero_of_two
          (hv.symm.trans (MulChar.map_nonunit (1 : DirichletCharacter R _) hnu))
      exact neg_one_ne_one_of_two (hv.symm.trans (MulChar.one_apply hu))
    rw [hempty, Finset.sum_empty]; linarith [le_max_right K 0]
  · obtain ⟨d, _, _, hd_le, hd_val⟩ :=
      (DirichletCharacter.primitiveCharacter_isPrimitive χ).exists_squarefree_apply_eq_jacobiSym
        hquad.primitiveCharacter hψ1
    have hcond_le : χ.conductor ≤ q :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    have hdx : (|d| : ℝ) ^ (18 : ℕ) ≤ x := by
      have hdq : (|d| : ℝ) ≤ q := by exact_mod_cast hd_le.trans (by exact_mod_cast hcond_le)
      exact (pow_le_pow_left₀ (abs_nonneg _) hdq 18).trans hx
    have hodd_le := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ ↦ Real.log p / p)
      (filter_primesLE_odd_subset_jacobiSym (N := ⌊x⌋₊) hd_val) fun p hp _ ↦ div_nonneg
        (Real.log_nonneg (by exact_mod_cast
          (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).one_lt.le)) (Nat.cast_nonneg _)
    have hsplit := TauCeti.sum_filter_primesLE_le_add_odd (N := ⌊x⌋₊)
      (P := fun p : ℕ ↦ χ (p : ZMod q) = -1)
    linarith [hK d x hx1 hdx, le_max_left K 0]

/-- **Inert-prime sum bound at power cutoffs `q ^ C`.** For every commutative ring `R` with `2 ≠ 0`,
every level `q ≠ 0`, every quadratic Dirichlet character `χ : DirichletCharacter R q`, and every
integer `C ≥ 18`, `∑_{p ≤ q ^ C, χ(p) = -1} log p / p ≤ (3 / 4) log (q ^ C) + K`. -/
theorem sum_primesLE_pow_eq_neg_one_log_div_le :
    ∃ K : ℝ, ∀ {R : Type*} [CommRing R] [NeZero (2 : R)] [DecidableEq R]
      {q : ℕ} [NeZero q] (χ : DirichletCharacter R q), χ.IsQuadratic →
      ∀ C : ℕ, 18 ≤ C →
        ∑ p ∈ (Nat.primesLE (q ^ C)).filter (fun p : ℕ ↦ χ (p : ZMod q) = -1), Real.log p / p ≤
          3 / 4 * Real.log ((q : ℝ) ^ C) + K := by
  obtain ⟨K, hK⟩ := sum_primesLE_eq_neg_one_log_div_le
  refine ⟨K, fun {R} _ _ _ {q} _ χ hquad C hC ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℝ) ^ (18 : ℕ) ≤ (q : ℝ) ^ C := pow_le_pow_right₀ hq1 hC
  have hfl : ⌊(q : ℝ) ^ C⌋₊ = q ^ C := by rw [← Nat.cast_pow, Nat.floor_natCast]
  simpa only [hfl] using hK χ hquad ((q : ℝ) ^ C) hpow

end DirichletCharacter
