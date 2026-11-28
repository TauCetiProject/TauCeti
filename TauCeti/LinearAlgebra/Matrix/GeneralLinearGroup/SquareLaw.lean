/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.MatchedFunctions
public import TauCeti.LinearAlgebra.Matrix.Trace.Fourier
public import TauCeti.Logic.Equiv.Sum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.LinearAlgebra.Matrix.Determinant.GaussSum

/-!
# The finite square law

Let `R` be a finite commutative ring, `χ` a multiplicative character of `R` and
`σ : b ⊕ a ≃ n` a splitting of an index type. Functions `L` of `a × n` matrices and `L'` of
`n × b` matrices satisfy the *square law* with constant `c` (`MulChar.SquareLaw`) if
`L (h x) = χ (det h) * L x` for `h ∈ GL_a(R)`, `L' (y h) = χ (det h) * L' y` for `h ∈ GL_b(R)`,
and `∑ y, Ψ y * L' y = c * ∑ x, Φ x * L x` for all pairs `(Φ, Ψ)` matched for `χ` along `σ`
(`MulChar.AreMatched`). The two routes around a commuting square of theta lifts, paired with
a form and a functional, satisfy such a law, with the matrices recording the finite data of the
lifts at the ramified places.

Testing the law against the matched block functions of an indicator gives its value at the block
points: `#GL_b(R) * L' (1; -z) = c * #GL_a(R) * L (z 1)` for every `a × b` matrix `z`
(`MulChar.SquareLaw.card_mul_apply_eq`). For the splitting `a ⊕ (n ⊕ b) ≃ n ⊕ (a ⊕ b)`
(`Equiv.sumLeftComm`) this becomes a relation between data on `n × a` matrices and data on
`(n ⊕ b) × (a ⊕ b)` matrices: summed against a function `p` of `n × a` matrices,
`#GL_a(R) * ∑ y, p y * L' (y; 1; 0) = c * #GL_{n ⊕ b}(R) * ∑ x, next(p) x * L (1 x)`
(`MulChar.SquareLaw.card_mul_sum_eq_mul_card_mul_sum_nextDatum`), where the next datum
`next(p)` (`TauCeti.nextDatum`) is `p (-η) / #M_{n×b}(R)` at the block matrix `(η s; 0 1)` and
`0` elsewhere, `(y; 1; 0)` stacks `y` over the inclusion of `a` in `a ⊕ b`, and `(1 x)` places
the inclusion of `n` in `n ⊕ b` left of `x`. Iterating `next` builds the finite data of the
descents along a chain of lifts.

For complex values, a primitive additive character `ψ` and a primitive `χ`, the same relation
holds between Fourier transforms for the trace pairing (`AddChar.traceFourier`) when
`n = u`, `a = u ⊕ v` and `b = v`: for a function `p` of `a × n` matrices,
`∑ y, F(conj p) y * L' (y; 1; 0) = γ * c * ∑ x, F(conj next(p)) x * L (1 x)`, with the next datum
formed with `n` and `a` exchanged and a constant `γ` with `‖γ‖ ^ 2 * #R ^ (#v * (#v + 2 #u)) = 1`
(`AddChar.IsPrimitive.exists_sum_traceFourier_mul_eq_of_squareLaw`). Here `1 / γ` is
`#M_{u×v}(R)` times the determinant Gauss sum `∑ t, χ (det t) * ψ (Tr t)` over `v × v` matrices:
averaging over the block `s` of the next datum kills, by orthogonality, the matrices `x` with a
nonzero block below `a`, and the sum over the last diagonal block of `x` is the Gauss sum, by
`AddChar.IsPrimitive.exists_traceFourier_eq_mul_inv_det`.

## Main definitions

* `MulChar.SquareLaw χ σ c L L'`: `L` and `L'` satisfy the square law with constant `c`.
* `TauCeti.nextDatum b p`: the next datum of a function `p` of `n × a` matrices.

## Main results

* `MulChar.SquareLaw.card_mul_apply_eq`: the square law at the block points.
* `TauCeti.nextDatum_apply`, `TauCeti.nextDatum_eq_zero`: the next datum on and off the matrices
  with lower blocks `0` and `1`; `TauCeti.nextDatum_zero`, `TauCeti.nextDatum_add`,
  `TauCeti.nextDatum_smul`: it is linear in the datum.
* `TauCeti.sum_nextDatum_mul`: pairing a next datum with a function.
* `MulChar.SquareLaw.card_mul_sum_eq_mul_card_mul_sum_nextDatum`: the square law for the
  splitting `a ⊕ (n ⊕ b) ≃ n ⊕ (a ⊕ b)`, against a datum and its next datum.
* `AddChar.IsPrimitive.exists_sum_traceFourier_mul_eq_of_squareLaw`: its Fourier form, for
  primitive characters.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/New/Determinant/Chain/SquareLaw.lean` (declarations `New.Exchange.SquareLaw`,
  `New.Exchange.SquareLaw.sum_eq_nextDatum`,
  `New.Exchange.SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum`); Apache 2.0, Copyright 2026
  Anthropic, PBC. The statements follow the route of these declarations; the proofs here are
  written from it.
-/

public section

open Matrix

namespace MulChar

variable {R Λ a b n : Type*} [CommRing R] [Fintype R] [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq a] [DecidableEq b] [DecidableEq n]

/-- Functions `L` of `a × n` matrices and `L'` of `n × b` matrices satisfy the *square law* for
the character `χ` along the splitting `σ : b ⊕ a ≃ n`, with constant `c`, if `L` transforms by
`χ ∘ det` under `GL_a(R)` acting on the left, `L'` transforms by `χ ∘ det` under `GL_b(R)` acting
on the right, and `∑ y, Ψ y * L' y = c * ∑ x, Φ x * L x` for every pair `(Φ, Ψ)` matched for `χ`
along `σ`. -/
structure SquareLaw [CommSemiring Λ] (χ : MulChar R Λ) (σ : b ⊕ a ≃ n) (c : Λ)
    (L : Matrix a n R → Λ) (L' : Matrix n b R → Λ) : Prop where
  /-- `L` transforms by `χ ∘ det` under `GL_a(R)` acting on the left. -/
  apply_mul_left (h : GL a R) (x : Matrix a n R) :
    L ((h : Matrix a a R) * x) = χ (h : Matrix a a R).det * L x
  /-- `L'` transforms by `χ ∘ det` under `GL_b(R)` acting on the right. -/
  apply_mul_right (h : GL b R) (y : Matrix n b R) :
    L' (y * (h : Matrix b b R)) = χ (h : Matrix b b R).det * L' y
  /-- The pairings of matched functions with `L'` and `L` differ by the factor `c`. -/
  sum_mul_eq (Φ : Matrix a n R → Λ) (Ψ : Matrix n b R → Λ) (h : χ.AreMatched σ Φ Ψ) :
    ∑ y, Ψ y * L' y = c * ∑ x, Φ x * L x

/-- **The square law at the block points.** If `L` and `L'` satisfy the square law with constant
`c`, then `#GL_b(R) * L' (1; -z) = c * #GL_a(R) * L (z 1)` for every `a × b` matrix `z`, where
`(1; -z)` has the identity on the rows `b` and `-z` on the rows `a`, and `(z 1)` has `z` on the
columns `b` and the identity on the columns `a`. -/
theorem SquareLaw.card_mul_apply_eq [CommSemiring Λ] {χ : MulChar R Λ} {σ : b ⊕ a ≃ n} {c : Λ}
    {L : Matrix a n R → Λ} {L' : Matrix n b R → Λ} (hL : χ.SquareLaw σ c L L')
    (z : Matrix a b R) :
    Nat.card (GL b R) * L' ((fromRows 1 (-z)).submatrix σ.symm id) =
      c * Nat.card (GL a R) * L ((fromCols z 1).submatrix id σ.symm) := by
  classical
  have h := hL.sum_mul_eq _ _
    (areMatched_rowBlockFun_colBlockFun χ (fun w ↦ if w = z then 1 else 0) σ)
  rw [sum_colBlockFun_mul χ _ hL.apply_mul_right, sum_rowBlockFun_mul χ _ hL.apply_mul_left] at h
  simpa [mul_assoc] using h

end MulChar

namespace TauCeti

section NextDatum

variable {R Λ a n : Type*} [CommRing R] [Semifield Λ] (b : Type*) [DecidableEq b]

open scoped Classical in
/-- The next datum of a function `p` of `n × a` matrices: the function of `(n ⊕ b) × (a ⊕ b)`
matrices that is `p (-η) / #M_{n×b}(R)` at the block matrix `(η s; 0 1)`, for all `η` and `s`, and
`0` elsewhere. -/
noncomputable def nextDatum (p : Matrix n a R → Λ) (x : Matrix (n ⊕ b) (a ⊕ b) R) : Λ :=
  if x.toBlocks₂₁ = 0 ∧ x.toBlocks₂₂ = 1 then p (-x.toBlocks₁₁) / Nat.card (Matrix n b R) else 0

variable {b}

/-- The next datum at a matrix `x` with lower blocks `0` and `1` is `p (-x₁₁) / #M_{n×b}(R)`, where
`x₁₁` is the upper left block of `x`. -/
theorem nextDatum_apply (p : Matrix n a R → Λ) {x : Matrix (n ⊕ b) (a ⊕ b) R}
    (h₂₁ : x.toBlocks₂₁ = 0) (h₂₂ : x.toBlocks₂₂ = 1) :
    nextDatum b p x = p (-x.toBlocks₁₁) / Nat.card (Matrix n b R) := by
  simp [nextDatum, h₂₁, h₂₂]

/-- The next datum at a block matrix `(η s; 0 1)` is `p (-η) / #M_{n×b}(R)`. -/
@[simp]
theorem nextDatum_fromBlocks (p : Matrix n a R → Λ) (η : Matrix n a R) (s : Matrix n b R) :
    nextDatum b p (fromBlocks η s 0 1) = p (-η) / Nat.card (Matrix n b R) := by
  rw [nextDatum_apply] <;> simp

/-- The next datum vanishes off the block matrices `(η s; 0 1)`. -/
@[simp]
theorem nextDatum_eq_zero (p : Matrix n a R → Λ) {x : Matrix (n ⊕ b) (a ⊕ b) R}
    (hx : ¬(x.toBlocks₂₁ = 0 ∧ x.toBlocks₂₂ = 1)) : nextDatum b p x = 0 := by
  rw [nextDatum, ite_eq_right hx]

/-- The next datum of the zero function is zero. -/
@[simp]
theorem nextDatum_zero : nextDatum b (0 : Matrix n a R → Λ) = 0 := by
  funext x
  by_cases hx : x.toBlocks₂₁ = 0 ∧ x.toBlocks₂₂ = 1
  · simp [nextDatum_apply _ hx.1 hx.2]
  · simp [nextDatum_eq_zero _ hx]

/-- The next datum of a sum is the sum of the next data. -/
@[simp]
theorem nextDatum_add (p q : Matrix n a R → Λ) :
    nextDatum b (p + q) = nextDatum b p + nextDatum b q := by
  funext x
  by_cases hx : x.toBlocks₂₁ = 0 ∧ x.toBlocks₂₂ = 1
  · simp [nextDatum_apply _ hx.1 hx.2, add_div]
  · simp [nextDatum_eq_zero _ hx]

/-- The next datum of a scalar multiple is the scalar multiple of the next datum. -/
@[simp]
theorem nextDatum_smul (c : Λ) (p : Matrix n a R → Λ) :
    nextDatum b (c • p) = c • nextDatum b p := by
  funext x
  by_cases hx : x.toBlocks₂₁ = 0 ∧ x.toBlocks₂₂ = 1
  · simp [nextDatum_apply _ hx.1 hx.2, mul_div_assoc]
  · simp [nextDatum_eq_zero _ hx]

/-- Pairing the next datum of `p` with a function `g` is averaging `p (-η) * g (η s; 0 1)` over the
blocks `s`, summed over `η`. -/
theorem sum_nextDatum_mul [Fintype R] [Fintype a] [Fintype b] [Fintype n] [DecidableEq a]
    [DecidableEq n] (p : Matrix n a R → Λ) (g : Matrix (n ⊕ b) (a ⊕ b) R → Λ) :
    ∑ x, nextDatum b p x * g x =
      (∑ η, ∑ s, p (-η) * g (fromBlocks η s 0 1)) / Nat.card (Matrix n b R) := by
  classical
  rw [Matrix.sum_fromBlocks, Finset.sum_div]
  refine Finset.sum_congr rfl fun η _ ↦ ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Finset.sum_eq_single 0 (fun C _ hC ↦ ?_) (by simp), Finset.sum_eq_single 1
    (fun D _ hD ↦ ?_) (by simp), nextDatum_fromBlocks, div_mul_eq_mul_div]
  · rw [nextDatum_eq_zero p (by simpa using hD), zero_mul]
  · exact Finset.sum_eq_zero fun D _ ↦ by rw [nextDatum_eq_zero p (by simp [hC]), zero_mul]

/-- Conjugating the next datum is taking the next datum of the conjugate function. -/
@[simp]
theorem star_nextDatum [StarRing Λ] (p : Matrix n a R → Λ) :
    star (nextDatum b p) = nextDatum b (star p) := by
  funext x
  by_cases hx : x.toBlocks₂₁ = 0 ∧ x.toBlocks₂₂ = 1
  · simp [nextDatum, hx]
  · simp [nextDatum_eq_zero _ hx]

end NextDatum

end TauCeti

namespace MulChar

variable {R Λ a b n : Type*} [CommRing R] [Fintype R] [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq a] [DecidableEq b] [DecidableEq n]

omit [Fintype R] [Fintype a] [DecidableEq a] in
/-- A function `L` of `(n ⊕ b) × (n ⊕ (a ⊕ b))` matrices that transforms by `χ ∘ det` under
`GL_{n ⊕ b}(R)` acting on the left satisfies
`L (1 A (B + s D); 0 0 (g D)) = χ (det g) * L (1 A B; 0 0 D)` for invertible `g`. -/
private theorem apply_fromCols_fromBlocks_mul [CommMonoidWithZero Λ] {χ : MulChar R Λ}
    {L : Matrix (n ⊕ b) (n ⊕ (a ⊕ b)) R → Λ}
    (hL : ∀ (h : GL (n ⊕ b) R) (x : Matrix (n ⊕ b) (n ⊕ (a ⊕ b)) R),
      L ((h : Matrix (n ⊕ b) (n ⊕ b) R) * x) = χ (h : Matrix (n ⊕ b) (n ⊕ b) R).det * L x)
    (A : Matrix n a R) (B s : Matrix n b R) (g : GL b R) (D : Matrix b b R) :
    L (fromCols (fromRows 1 0) (fromBlocks A (B + s * D) 0 ((g : Matrix b b R) * D))) =
      χ (g : Matrix b b R).det * L (fromCols (fromRows 1 0) (fromBlocks A B 0 D)) := by
  have hdet : IsUnit (fromBlocks (1 : Matrix n n R) s 0 (g : Matrix b b R)).det := by
    simp [det_fromBlocks_zero₂₁]
  have h := hL (GeneralLinearGroup.mk'' _ hdet) (fromCols (fromRows 1 0) (fromBlocks A B 0 D))
  rw [GeneralLinearGroup.val_mk'', det_fromBlocks_zero₂₁, det_one, one_mul, mul_fromCols,
    fromBlocks_mul_fromRows, fromBlocks_multiply] at h
  simpa using h

omit [Fintype R] [Fintype a] [DecidableEq a] in
/-- A function of `(n ⊕ b) × (n ⊕ (a ⊕ b))` matrices that transforms by `χ ∘ det` under
`GL_{n ⊕ b}(R)` acting on the left takes the same value at `(1 η s; 0 0 1)` for all `s`. -/
private theorem apply_fromCols_fromBlocks_eq [CommMonoidWithZero Λ] {χ : MulChar R Λ}
    {L : Matrix (n ⊕ b) (n ⊕ (a ⊕ b)) R → Λ}
    (hL : ∀ (h : GL (n ⊕ b) R) (x : Matrix (n ⊕ b) (n ⊕ (a ⊕ b)) R),
      L ((h : Matrix (n ⊕ b) (n ⊕ b) R) * x) = χ (h : Matrix (n ⊕ b) (n ⊕ b) R).det * L x)
    (η : Matrix n a R) (s : Matrix n b R) :
    L (fromCols (fromRows 1 0) (fromBlocks η s 0 1)) =
      L (fromCols (fromRows 1 0) (fromBlocks η 0 0 1)) := by
  simpa using apply_fromCols_fromBlocks_mul hL η 0 s 1 1

/-- The square law along `a ⊕ (n ⊕ b) ≃ n ⊕ (a ⊕ b)` at the block points `(-y; 0)`. -/
private theorem SquareLaw.card_mul_apply_fromRows_eq [CommSemiring Λ] {χ : MulChar R Λ} {c : Λ}
    {L : Matrix (n ⊕ b) (n ⊕ (a ⊕ b)) R → Λ} {L' : Matrix (n ⊕ (a ⊕ b)) a R → Λ}
    (hL : χ.SquareLaw (Equiv.sumLeftComm a n b) c L L') (y : Matrix n a R) :
    Nat.card (GL a R) * L' (fromRows y (fromRows 1 0)) =
      c * Nat.card (GL (n ⊕ b) R) * L (fromCols (fromRows 1 0) (fromBlocks (-y) 0 0 1)) := by
  convert hL.card_mul_apply_eq (fromRows (-y) 0) using 3
  · ext (i | i | i) j <;> simp
  · ext (i | i) (j | j | j) <;> simp [Matrix.one_apply]

/-- **The finite square law against the next datum.** If `L` and `L'` satisfy the square law with
constant `c` along the splitting `a ⊕ (n ⊕ b) ≃ n ⊕ (a ⊕ b)`, then for every function `p` of
`n × a` matrices,
`#GL_a(R) * ∑ y, p y * L' (y; 1; 0) = c * #GL_{n ⊕ b}(R) * ∑ x, next(p) x * L (1 x)`,
where `(y; 1; 0)` stacks `y` over the inclusion of `a` in `a ⊕ b` and `(1 x)` places the inclusion
of `n` in `n ⊕ b` left of `x`. -/
theorem SquareLaw.card_mul_sum_eq_mul_card_mul_sum_nextDatum [Semifield Λ]
    {χ : MulChar R Λ} {c : Λ} {L : Matrix (n ⊕ b) (n ⊕ (a ⊕ b)) R → Λ}
    {L' : Matrix (n ⊕ (a ⊕ b)) a R → Λ} (hL : χ.SquareLaw (Equiv.sumLeftComm a n b) c L L')
    (p : Matrix n a R → Λ) :
    Nat.card (GL a R) * ∑ y, p y * L' (fromRows y (fromRows 1 0)) =
      c * Nat.card (GL (n ⊕ b) R) *
        ∑ x, TauCeti.nextDatum b p x * L (fromCols (fromRows 1 0) x) := by
  by_cases hM : (Nat.card (Matrix n b R) : Λ) = 0
  · -- Then `#GL_{n ⊕ b}(R)` vanishes in `Λ` as well, and both sides are `0`.
    obtain ⟨k, hk⟩ := natCard_matrix_dvd_natCard_GL (m := n) (k := b) (R := R)
    have hGL : (Nat.card (GL (n ⊕ b) R) : Λ) = 0 := by rw [hk, Nat.cast_mul, hM, zero_mul]
    rw [hGL, mul_zero, zero_mul, Finset.mul_sum]
    exact Finset.sum_eq_zero fun y _ ↦ by
      rw [mul_left_comm, hL.card_mul_apply_fromRows_eq, hGL, mul_zero, zero_mul, mul_zero]
  rw [TauCeti.sum_nextDatum_mul]
  simp_rw [apply_fromCols_fromBlocks_eq hL.apply_mul_left, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hM,
    ← Equiv.sum_comp (Equiv.neg (Matrix n a R)), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [mul_left_comm, hL.card_mul_apply_fromRows_eq, Equiv.neg_apply, neg_neg, mul_left_comm]

/-! ### The Fourier form of the square law -/

/-- The pairing of `L (1 x)` with the Fourier transform of the conjugate of a next datum. -/
private theorem sum_traceFourier_star_nextDatum_mul {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive)
    {χ : MulChar R ℂ} {γ : ℂ}
    (hγ : ∀ f : Matrix b b R → ℂ, (∀ (g : GL b R) (D : Matrix b b R),
      f ((g : Matrix b b R) * D) = χ (g : Matrix b b R).det * f D) →
        ψ.traceFourier f 1 = γ * f 1)
    {L : Matrix (n ⊕ b) (n ⊕ (a ⊕ b)) R → ℂ}
    (hL : ∀ (h : GL (n ⊕ b) R) (x : Matrix (n ⊕ b) (n ⊕ (a ⊕ b)) R),
      L ((h : Matrix (n ⊕ b) (n ⊕ b) R) * x) = χ (h : Matrix (n ⊕ b) (n ⊕ b) R).det * L x)
    (p : Matrix a n R → ℂ) :
    ∑ x, ψ.traceFourier (star (TauCeti.nextDatum b p)) x * L (fromCols (fromRows 1 0) x) =
      Nat.card (Matrix n b R) * γ *
        ∑ A, ψ.traceFourier (star p) (-A) * L (fromCols (fromRows 1 0) (fromBlocks A 0 0 1)) := by
  have hM : (Nat.card (Matrix a b R) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- The sum over the lower right block is a determinant Gauss sum.
  have hD (A : Matrix n a R) (B : Matrix n b R) :
      ∑ D, L (fromCols (fromRows 1 0) (fromBlocks A B 0 D)) * ψ D.trace =
        γ * L (fromCols (fromRows 1 0) (fromBlocks A 0 0 1)) := by
    have h := hγ (fun D ↦ L (fromCols (fromRows 1 0) (fromBlocks A B 0 D)))
      (fun g D ↦ by simpa using apply_fromCols_fromBlocks_mul hL A B 0 g D)
    simpa [AddChar.traceFourier_apply, apply_fromCols_fromBlocks_eq hL] using h
  calc _ = (∑ η, ∑ s, star p (-η) *
          ψ.traceFourier (fun x ↦ L (fromCols (fromRows 1 0) x)) (fromBlocks η s 0 1)) /
            Nat.card (Matrix a b R) := by
        rw [TauCeti.star_nextDatum, AddChar.sum_traceFourier_mul, TauCeti.sum_nextDatum_mul]
    _ = ∑ η, star p (-η) * (Nat.card (Matrix n b R) * γ *
          ∑ A, ψ (η * A).trace * L (fromCols (fromRows 1 0) (fromBlocks A 0 0 1))) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun η _ ↦ ?_
        rw [← Finset.mul_sum, hψ.sum_traceFourier_fromBlocks, mul_div_assoc,
          mul_div_cancel_left₀ _ hM]
        congr 1
        have hA (A : Matrix n a R) : ∑ B, ∑ D, L (fromCols (fromRows 1 0) (fromBlocks A B 0 D)) *
            (ψ (η * A).trace * ψ D.trace) = Nat.card (Matrix n b R) * γ *
              (ψ (η * A).trace * L (fromCols (fromRows 1 0) (fromBlocks A 0 0 1))) := by
          simp_rw [mul_left_comm _ (ψ (η * A).trace), ← Finset.mul_sum, hD, Finset.sum_const,
            Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
          ring
        rw [Finset.sum_congr rfl fun A _ ↦ hA A, ← Finset.mul_sum]
    _ = _ := by
        rw [← Equiv.sum_comp (Equiv.neg (Matrix a n R)), Finset.mul_sum]
        simp_rw [AddChar.traceFourier_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun A _ ↦ Finset.sum_congr rfl fun η _ ↦ ?_
        simp only [Equiv.neg_apply, neg_neg, Pi.star_apply, Matrix.neg_mul, trace_neg,
          trace_mul_comm η A]
        ring

end MulChar

namespace AddChar

open MulChar

variable {R : Type*} [CommRing R] [Fintype R]

/-- **The Fourier form of the finite square law.** Let `ψ` be a primitive additive character of
`R` and `χ` a primitive multiplicative character (for every `e ≠ 0` some `1 + c₀ e` is a unit
with `χ (1 + c₀ e) ≠ 1`), and take the shapes `n = u`, `a = u ⊕ v`, `b = v`. There is `γ` with
`‖γ‖ ^ 2 * #R ^ (#v * (#v + 2 #u)) = 1` such that, whenever `L` and `L'` satisfy the square law
with constant `c` along `a ⊕ (n ⊕ b) ≃ n ⊕ (a ⊕ b)`, for every function `p` of `a × n` matrices
`∑ y, F(conj p) y * L' (y; 1; 0) = γ * c * ∑ x, F(conj next(p)) x * L (1 x)`, where `F` is the
Fourier transform for the trace pairing (`AddChar.traceFourier`), `conj` the complex conjugate, and
the next datum `next(p)` is formed with the roles of `n` and `a` exchanged. -/
theorem IsPrimitive.exists_sum_traceFourier_mul_eq_of_squareLaw {u v : Type*} [Fintype u]
    [Fintype v] [DecidableEq u] [DecidableEq v] {ψ : AddChar R ℂ} (hψ : ψ.IsPrimitive)
    {χ : MulChar R ℂ} (hχ : ∀ e : R, e ≠ 0 → ∃ c₀ : R, IsUnit (1 + c₀ * e) ∧ χ (1 + c₀ * e) ≠ 1) :
    ∃ γ : ℂ, ‖γ‖ ^ 2 * (Nat.card R : ℝ) ^ (Nat.card v * (Nat.card v + 2 * Nat.card u)) = 1 ∧
      ∀ (c : ℂ) (L : Matrix (u ⊕ v) (u ⊕ ((u ⊕ v) ⊕ v)) R → ℂ)
        (L' : Matrix (u ⊕ ((u ⊕ v) ⊕ v)) (u ⊕ v) R → ℂ),
        χ.SquareLaw (Equiv.sumLeftComm (u ⊕ v) u v) c L L' →
        ∀ p : Matrix (u ⊕ v) u R → ℂ,
          ∑ y, ψ.traceFourier (star p) y * L' (fromRows y (fromRows 1 0)) =
            γ * c * ∑ x, ψ.traceFourier (star (TauCeti.nextDatum v p)) x *
              L (fromCols (fromRows 1 0) x) := by
  obtain ⟨γv, hγv, hF⟩ := hψ.exists_traceFourier_eq_mul_inv_det (n := v) hχ
  have hR : (Nat.card R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hM : (Nat.card (Matrix u v R) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcard : (Nat.card (Matrix u v R) : ℝ) ^ 2 * ‖γv‖ ^ 2 =
      (Nat.card R : ℝ) ^ (Nat.card v * (Nat.card v + 2 * Nat.card u)) := by
    rw [hγv, ← Nat.card_eq_fintype_card, card_matrix, card_matrix]
    push_cast
    rw [← pow_mul, ← pow_add]
    ring_nf
  have hγv0 : γv ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_pow two_ne_zero, mul_zero] at hcard
    exact pow_ne_zero _ hR hcard.symm
  refine ⟨(Nat.card (Matrix u v R) * γv)⁻¹, ?_, fun c L L' hL p ↦ ?_⟩
  · rw [norm_inv, norm_mul, Complex.norm_natCast, inv_pow, mul_pow, hcard,
      inv_mul_cancel₀ (pow_ne_zero _ hR)]
  have hγ (f : Matrix v v R → ℂ) (hf : ∀ (g : GL v R) (D : Matrix v v R),
      f ((g : Matrix v v R) * D) = χ (g : Matrix v v R).det * f D) :
      ψ.traceFourier f 1 = γv * f 1 := by
    rw [hF f hf 1, det_one, map_one, mul_one]
  have hGL : (Nat.card (GL (u ⊕ v) R) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hpt (y : Matrix u (u ⊕ v) R) : L' (fromRows y (fromRows 1 0)) =
      c * L (fromCols (fromRows 1 0) (fromBlocks (-y) 0 0 1)) := by
    have h := hL.card_mul_apply_fromRows_eq y
    rw [mul_comm c, mul_assoc] at h
    exact mul_left_cancel₀ hGL h
  rw [sum_traceFourier_star_nextDatum_mul hψ hγ hL.apply_mul_left,
    ← Equiv.sum_comp (Equiv.neg (Matrix u (u ⊕ v) R))]
  simp_rw [hpt, Equiv.neg_apply, neg_neg]
  have hk : (Nat.card (Matrix u v R) * γv)⁻¹ * c * Nat.card (Matrix u v R) * γv = c := by
    field_simp
  rw [← mul_assoc, ← mul_assoc, hk, Finset.mul_sum]
  exact Finset.sum_congr rfl fun A _ ↦ by ring

end AddChar
