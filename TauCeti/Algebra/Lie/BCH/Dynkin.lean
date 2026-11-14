/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.NatAntidiagonal
public import TauCeti.Algebra.Lie.Free.Grading
import TauCeti.Algebra.Lie.Subalgebra.LieSpan
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# The degreewise Dynkin Lie polynomials

`TauCeti.BCH.dynkinTerm K n x y` is the homogeneous term of degree `n` in Dynkin's
Baker--Campbell--Hausdorff formula over a characteristic-zero field `K`. Nonempty
exponent blocks `x^r y^s` are concatenated into one word, then interpreted as a
right-nested Lie bracket. The coefficients
include the logarithm factor, the inverse total degree and the factorials of every
exponent. All sums defining a term are finite.

`TauCeti.BCH.dynkinPolynomial` specializes these terms to the two generators of the
free Lie algebra over `K`. No convergence assertion is part of this construction.
These coefficients support formal completions and numerical evaluation of the series.
The finite definitions also make sense in positive characteristic using total inversion
(`0⁻¹ = 0`); their interpretation as BCH coefficients is asserted only in characteristic zero.

## References

* Michael Müger, *Notes on the theorem of Baker--Campbell--Hausdorff--Dynkin*
  (April 22, 2020), Theorem 1.3, formula (1.4), and Corollary 6.9.
  <https://www.math.ru.nl/~mueger/PDF/BCHD.pdf>
-/

public section

open Finset

noncomputable section

namespace TauCeti.BCH

variable (K : Type*) [Field K]
variable {L M : Type*} [LieRing L] [LieAlgebra K L] [LieRing M] [LieAlgebra K M]

/-- The right-nested bracket of a word in `x` and `y`, with empty word equal to zero. -/
def dynkinWordBracket (x y : L) (w : List Bool) : L :=
  match w.getLast? with
  | none => 0
  | some b => rightNormedBracket (fun a => if a then y else x) b w.dropLast

omit [LieAlgebra K L] in
/-- The bracket of the empty word is zero. -/
@[simp]
theorem dynkinWordBracket_nil (x y : L) : dynkinWordBracket x y [] = 0 := by
  simp [dynkinWordBracket]

omit [LieAlgebra K L] in
/-- The bracket of a singleton is its letter: false selects `x`, true selects `y`. -/
@[simp]
theorem dynkinWordBracket_singleton (x y : L) (b : Bool) :
    dynkinWordBracket x y [b] = if b then y else x := by
  simp [dynkinWordBracket]

omit [LieAlgebra K L] in
/-- Prepending a letter to a nonempty word gives one outer bracket. -/
@[simp]
theorem dynkinWordBracket_cons_cons (x y : L) (b c : Bool) (w : List Bool) :
    dynkinWordBracket x y (b :: c :: w) = ⁅if b then y else x, dynkinWordBracket x y (c :: w)⁆ := by
  simp only [dynkinWordBracket, List.getLast?_cons_cons, List.dropLast_cons_cons]
  cases (c :: w).getLast? <;> simp

-- The recursion enumerates k nonempty exponent blocks of total degree n. The
-- function argument retains the word until all exponent blocks have been chosen.
/-- Sum a function over `k` nonempty exponent blocks of total length `n`, weighted by
the inverse product of all exponent factorials. The blocks are concatenated before evaluation. -/
def dynkinBlockSum (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V] :
    ℕ → ℕ → (List Bool → V) → V
  | 0, n, f => if n = 0 then f [] else 0
  | k + 1, n, f =>
    ∑ p ∈ antidiagonal n, if p.1 = 0 then 0 else
      ∑ q ∈ antidiagonal p.1,
        ((q.1.factorial * q.2.factorial : ℕ) : K)⁻¹ •
          dynkinBlockSum K k p.2 (fun w =>
            f (List.replicate q.1 false ++ List.replicate q.2 true ++ w))

/-- Zero exponent blocks contribute just the empty word in total degree zero. -/
@[simp]
theorem dynkinBlockSum_zero {V : Type*} [AddCommGroup V] [Module K V]
    (n : ℕ) (f : List Bool → V) :
    dynkinBlockSum K 0 n f = if n = 0 then f [] else 0 := by
  rw [dynkinBlockSum]

/-- The finite exponent-block sum is obtained by choosing the first nonempty block. -/
theorem dynkinBlockSum_succ {V : Type*} [AddCommGroup V] [Module K V]
    (k n : ℕ) (f : List Bool → V) :
    dynkinBlockSum K (k + 1) n f =
      ∑ p ∈ antidiagonal n, if p.1 = 0 then 0 else
        ∑ q ∈ antidiagonal p.1,
          ((q.1.factorial * q.2.factorial : ℕ) : K)⁻¹ •
            dynkinBlockSum K k p.2 (fun w =>
              f (List.replicate q.1 false ++ List.replicate q.2 true ++ w)) := by
  rw [dynkinBlockSum]

/-- The degree-`n` Dynkin term is
`Σ_k (-1)^(k-1)/(k n) Σ [x^r₁ y^s₁ ⋯ x^rₖ y^sₖ] / Π_i rᵢ! sᵢ!`,
where every block has `rᵢ + sᵢ > 0` and the total exponent sum is `n`.
The concatenated word is right-nested, with its final letter innermost and a
singleton interpreted as its letter. This is Müger's formula (1.4). -/
def dynkinTerm (n : ℕ) (x y : L) : L :=
  ∑ k ∈ range (n + 1),
    ((((-1 : ℤ) ^ (k - 1) * (k * n : ℕ) : ℤ) : K))⁻¹ •
      dynkinBlockSum K k n (dynkinWordBracket x y)

/-- The finite exponent-block formula characterizing the degree-`n` Dynkin term. -/
theorem dynkinTerm_def (n : ℕ) (x y : L) :
    dynkinTerm K n x y = ∑ k ∈ range (n + 1),
      ((-1 : K) ^ (k - 1) / (k * n : ℕ)) •
        dynkinBlockSum K k n (dynkinWordBracket x y) := by
  simp [dynkinTerm, div_eq_mul_inv, ← inv_pow, mul_comm]

/-- The universal homogeneous Dynkin polynomial in the free Lie algebra on two generators. -/
def dynkinPolynomial (n : ℕ) : FreeLieAlgebra K Bool :=
  dynkinTerm K n (FreeLieAlgebra.of K false) (FreeLieAlgebra.of K true)

/-- The universal Dynkin polynomial is the Dynkin term on the two free generators. -/
theorem dynkinPolynomial_def (n : ℕ) :
    dynkinPolynomial K n =
      dynkinTerm K n (FreeLieAlgebra.of K false) (FreeLieAlgebra.of K true) := by
  rw [dynkinPolynomial]

omit [LieAlgebra K L] [LieAlgebra K M] in
/-- Lie homomorphisms commute with the word bracket. -/
@[simp]
theorem _root_.LieHom.map_dynkinWordBracket {R : Type*} [CommRing R]
    [LieAlgebra R L] [LieAlgebra R M] (f : L →ₗ⁅R⁆ M) (x y : L) (w : List Bool) :
    f (dynkinWordBracket x y w) = dynkinWordBracket (f x) (f y) w := by
  induction w with
  | nil => simp [dynkinWordBracket]
  | cons b w ih =>
    cases w with
    | nil => cases b <;> simp [dynkinWordBracket]
    | cons c w => cases b <;> simp [dynkinWordBracket_cons_cons, f.map_lie, ih]

variable {K} in
/-- Additive maps commute with the weighted exponent-block sum. -/
@[simp]
theorem _root_.map_dynkinBlockSum {V W F : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FunLike F V W] [AddMonoidHomClass F V W]
    (g : F) (k n : ℕ) (f : List Bool → V) :
    g (dynkinBlockSum K k n f) = dynkinBlockSum K k n (fun w => g (f w)) := by
  induction k generalizing n f with
  | zero => by_cases hn : n = 0 <;> simp [dynkinBlockSum_zero, hn]
  | succ k ih =>
    simp only [dynkinBlockSum_succ, map_sum, map_inv_natCast_smul g K K,
      apply_ite, map_zero, ih]

/-- The weighted exponent-block sum does not depend on the coefficient field. -/
theorem dynkinBlockSum_eq_dynkinBlockSum (K' : Type*) [Field K'] {V : Type*}
    [AddCommGroup V] [Module K V] [Module K' V] (k n : ℕ) (f : List Bool → V) :
    dynkinBlockSum K k n f = dynkinBlockSum K' k n f := by
  induction k generalizing n f with
  | zero => simp only [dynkinBlockSum_zero]
  | succ k ih =>
    simp only [dynkinBlockSum_succ, ih, inv_natCast_smul_eq K K']

variable {K} in
/-- Lie homomorphisms over any scalar ring commute with each degreewise Dynkin term. -/
@[simp]
theorem _root_.LieHom.map_dynkinTerm {R : Type*} [CommRing R]
    [LieAlgebra R L] [LieAlgebra R M] (f : L →ₗ⁅R⁆ M) (n : ℕ) (x y : L) :
    f (dynkinTerm K n x y) = dynkinTerm K n (f x) (f y) := by
  simp only [dynkinTerm, map_sum,
    map_inv_intCast_smul f K K, map_dynkinBlockSum, LieHom.map_dynkinWordBracket]

/-- The homogeneous Dynkin terms do not depend on the coefficient field. -/
theorem dynkinTerm_eq_dynkinTerm (K' : Type*) [Field K'] [LieAlgebra K' L]
    (n : ℕ) (x y : L) : dynkinTerm K n x y = dynkinTerm K' n x y := by
  simp only [dynkinTerm,
    dynkinBlockSum_eq_dynkinBlockSum K K', inv_intCast_smul_eq K K']

variable {K} in
/-- Any Lie homomorphism evaluates the universal polynomial at the images of its generators. -/
@[simp]
theorem _root_.LieHom.map_dynkinPolynomial (f : FreeLieAlgebra K Bool →ₗ⁅K⁆ L) (n : ℕ) :
    f (dynkinPolynomial K n) =
      dynkinTerm K n (f (FreeLieAlgebra.of K false)) (f (FreeLieAlgebra.of K true)) := by
  rw [dynkinPolynomial_def, LieHom.map_dynkinTerm]

/-- Evaluating the universal Dynkin polynomial gives the corresponding Dynkin term. -/
theorem lift_dynkinPolynomial (n : ℕ) (g : Bool → L) :
    FreeLieAlgebra.lift K g (dynkinPolynomial K n) =
      dynkinTerm K n (g false) (g true) := by
  simp

/-- The Dynkin series has zero constant term. -/
@[simp]
theorem dynkinTerm_zero (x y : L) : dynkinTerm K 0 x y = 0 := by
  simp [dynkinTerm]

/-- The degree-one term of the Dynkin series is the sum of the inputs. -/
@[simp]
theorem dynkinTerm_one (x y : L) : dynkinTerm K 1 x y = x + y := by
  norm_num [dynkinTerm, dynkinBlockSum, Finset.Nat.antidiagonal_succ, dynkinWordBracket,
    List.replicate_succ, Finset.sum_range_succ]
  module

/-- The universal Dynkin polynomial has zero constant term. -/
@[simp]
theorem dynkinPolynomial_zero : dynkinPolynomial K 0 = 0 := by
  simp [dynkinPolynomial_def]

/-- The linear universal Dynkin polynomial is the sum of the free generators. -/
@[simp]
theorem dynkinPolynomial_one :
    dynkinPolynomial K 1 = FreeLieAlgebra.of K false + FreeLieAlgebra.of K true := by
  simp [dynkinPolynomial_def]

/-- The degree-two term of the Dynkin series is one half of the bracket. -/
theorem dynkinTerm_two (x y : L) :
    dynkinTerm K 2 x y = (1 / 2 : K) • ⁅x, y⁆ := by
  norm_num [dynkinTerm, dynkinBlockSum, Finset.Nat.antidiagonal_succ, dynkinWordBracket,
    List.replicate_succ, Finset.sum_range_succ]
  rw [← lie_skew y x]
  module

/-- The degree-three term is one twelfth of the sum of the two double brackets. -/
theorem dynkinTerm_three (x y : L) :
    dynkinTerm K 3 x y = (1 / 12 : K) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆) := by
  norm_num [dynkinTerm, dynkinBlockSum, Finset.Nat.antidiagonal_succ, dynkinWordBracket,
    List.replicate_succ, Finset.sum_range_succ]
  simp only [← lie_skew y x, lie_neg]
  have h6 : (6 : K) = 3 * 2 := by norm_num
  have h12 : (12 : K) = 3 * 2 * 2 := by norm_num
  match_scalars
  -- Total inversion includes characteristics two and three, where small denominators vanish.
  all_goals
    by_cases h2 : (2 : K) = 0
    · simp [h2, h12]
    · by_cases h3 : (3 : K) = 0
      · simp [h3, h12]
      · have hn6 : (6 : K) ≠ 0 := by rw [h6]; exact mul_ne_zero h3 h2
        have hn12 : (12 : K) ≠ 0 := by
          rw [h12]
          exact mul_ne_zero (mul_ne_zero h3 h2) h2
        field_simp [h2, h3, hn6, hn12]; ring

/-- The block sum lies in a submodule containing every word value of its prescribed length. -/
theorem dynkinBlockSum_mem {V : Type*} [AddCommGroup V] [Module K V]
    (P : Submodule K V) (k n : ℕ) (f : List Bool → V)
    (hf : ∀ w, w.length = n → f w ∈ P) : dynkinBlockSum K k n f ∈ P := by
  induction k generalizing n f with
  | zero =>
    by_cases hn : n = 0
    · subst n
      simpa [dynkinBlockSum] using hf [] rfl
    · simp [dynkinBlockSum, hn]
  | succ k ih =>
    rw [dynkinBlockSum]
    apply P.sum_mem
    intro p hp
    split_ifs with hp0
    · exact P.zero_mem
    apply P.sum_mem
    intro q hq
    apply P.smul_mem
    apply ih
    intro w hw
    apply hf
    simp only [List.length_append, List.length_replicate, hw]
    have hp' := mem_antidiagonal.mp hp
    have hq' := mem_antidiagonal.mp hq
    omega

/-- The block sum vanishes if all word values of its prescribed length vanish. -/
theorem dynkinBlockSum_eq_zero_of_forall {V : Type*} [AddCommGroup V] [Module K V]
    (k n : ℕ) (f : List Bool → V) (hf : ∀ w, w.length = n → f w = 0) :
    dynkinBlockSum K k n f = 0 := by
  simpa only [Submodule.mem_bot] using dynkinBlockSum_mem K (⊥ : Submodule K V) k n f (by
    intro w hw
    simpa only [Submodule.mem_bot] using hf w hw)

/-- The block sum of the zero word function vanishes in every degree. -/
@[simp]
theorem dynkinBlockSum_const_zero {V : Type*} [AddCommGroup V] [Module K V] (k n : ℕ) :
    dynkinBlockSum K k n (fun _ => (0 : V)) = 0 :=
  dynkinBlockSum_eq_zero_of_forall K k n _ (fun _ _ => rfl)

/-- The weighted block sum respects subtraction of word functions. -/
theorem dynkinBlockSum_sub {V : Type*} [AddCommGroup V] [Module K V]
    (k n : ℕ) (f g : List Bool → V) :
    dynkinBlockSum K k n (fun w => f w - g w) =
      dynkinBlockSum K k n f - dynkinBlockSum K k n g := by
  induction k generalizing n f g with
  | zero => by_cases hn : n = 0 <;> simp [dynkinBlockSum, hn]
  | succ k ih =>
    simp only [dynkinBlockSum, ih, smul_sub]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp only [sub_self, Finset.sum_sub_distrib]

/-- The weighted block sum respects negation of word functions. -/
@[simp]
theorem dynkinBlockSum_neg {V : Type*} [AddCommGroup V] [Module K V]
    (k n : ℕ) (f : List Bool → V) :
    dynkinBlockSum K k n (fun w => -f w) = -dynkinBlockSum K k n f := by
  simpa only [zero_sub, dynkinBlockSum_const_zero] using
    dynkinBlockSum_sub K k n (fun _ => 0) f

/-- The weighted block sum respects addition of word functions. -/
@[simp]
theorem dynkinBlockSum_add {V : Type*} [AddCommGroup V] [Module K V]
    (k n : ℕ) (f g : List Bool → V) :
    dynkinBlockSum K k n (fun w => f w + g w) =
      dynkinBlockSum K k n f + dynkinBlockSum K k n g := by
  simpa only [sub_neg_eq_add, dynkinBlockSum_neg] using
    dynkinBlockSum_sub K k n f (fun w => -g w)

/-- The block sum depends only on word values at its prescribed length. -/
theorem dynkinBlockSum_congr {V : Type*} [AddCommGroup V] [Module K V]
    (k n : ℕ) (f g : List Bool → V) (hfg : ∀ w, w.length = n → f w = g w) :
    dynkinBlockSum K k n f = dynkinBlockSum K k n g := by
  have h := dynkinBlockSum_eq_zero_of_forall K k n (fun w => f w - g w) (by
    intro w hw
    rw [hfg w hw, sub_self])
  rw [dynkinBlockSum_sub] at h
  exact sub_eq_zero.mp h

omit [LieAlgebra K L] in
/-- Scaling the letters scales a word bracket by the corresponding power of the scalar. -/
theorem dynkinWordBracket_smul {R : Type*} [CommRing R] [LieAlgebra R L]
    (t : R) (x y : L) (w : List Bool) :
    dynkinWordBracket (t • x) (t • y) w = t ^ w.length • dynkinWordBracket x y w := by
  induction w with
  | nil => simp [dynkinWordBracket]
  | cons b w ih =>
    cases w with
    | nil => cases b <;> simp [dynkinWordBracket]
    | cons c w =>
      rw [dynkinWordBracket_cons_cons, dynkinWordBracket_cons_cons, ih]
      have hb : (if b then t • y else t • x) = t • (if b then y else x) := by
        cases b <;> rfl
      rw [hb, smul_lie, lie_smul, smul_smul]
      simp only [List.length_cons, pow_succ]
      congr 1
      ring

/-- The weighted block sum respects scalar multiplication of word functions. -/
theorem dynkinBlockSum_smul {V R : Type*} [AddCommGroup V] [Module K V]
    [DistribSMul R V] (t : R) (k n : ℕ) (f : List Bool → V) :
    dynkinBlockSum K k n (fun w => t • f w) = t • dynkinBlockSum K k n f := by
  exact (map_dynkinBlockSum (K := K) (DistribSMul.toAddMonoidHom V t) k n f).symm

/-- Simultaneously scaling the inputs scales the degree-`n` Dynkin term by the `n`th power. -/
theorem dynkinTerm_smul {R : Type*} [CommRing R] [LieAlgebra R L]
    (n : ℕ) (t : R) (x y : L) :
    dynkinTerm K n (t • x) (t • y) = t ^ n • dynkinTerm K n x y := by
  unfold dynkinTerm
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h := dynkinBlockSum_congr K k n (dynkinWordBracket (t • x) (t • y))
    (fun w => t ^ n • dynkinWordBracket x y w) (by
      intro w hw
      rw [dynkinWordBracket_smul, hw])
  rw [h, dynkinBlockSum_smul]
  exact inv_intCast_smul_comm K _ _ _

omit [LieAlgebra K L] in
/-- A word bracket of length other than one vanishes when the two letters bracket to zero. -/
theorem dynkinWordBracket_eq_zero_of_lie_eq_zero (x y : L) (hxy : ⁅x, y⁆ = 0) (w : List Bool)
    (hw : w.length ≠ 1) : dynkinWordBracket x y w = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases w with
    | nil => simp at hw
    | cons c w =>
      cases w with
      | nil =>
        have hyx : ⁅y, x⁆ = 0 := by rw [← lie_skew y x, hxy, neg_zero]
        cases b <;> cases c <;> simp [dynkinWordBracket, hxy, hyx]
      | cons d w =>
        have hz := ih (by simp)
        rw [dynkinWordBracket_cons_cons, hz, lie_zero]

/-- If the two inputs bracket to zero, only the degree-one Dynkin term can be nonzero. -/
theorem dynkinTerm_of_lie_eq_zero (n : ℕ) (x y : L) (hxy : ⁅x, y⁆ = 0) :
    dynkinTerm K n x y = if n = 1 then x + y else 0 := by
  by_cases hn : n = 1
  · subst n
    simp
  rw [ite_eq_right hn, dynkinTerm]
  apply Finset.sum_eq_zero
  intro k _
  have h := dynkinBlockSum_eq_zero_of_forall K k n (dynkinWordBracket x y) (by
    intro w hw
    exact dynkinWordBracket_eq_zero_of_lie_eq_zero x y hxy w (by omega))
  rw [h, smul_zero]

/-- On the left coordinate axis, the only nonzero Dynkin term has degree one. -/
@[simp]
theorem dynkinTerm_zero_left (n : ℕ) (y : L) :
    dynkinTerm K n 0 y = if n = 1 then y else 0 := by
  simpa using dynkinTerm_of_lie_eq_zero K n 0 y (zero_lie y)

/-- On the right coordinate axis, the only nonzero Dynkin term has degree one. -/
@[simp]
theorem dynkinTerm_zero_right (n : ℕ) (x : L) :
    dynkinTerm K n x 0 = if n = 1 then x else 0 := by
  simpa using dynkinTerm_of_lie_eq_zero K n x 0 (lie_zero x)

private theorem dynkinWordBracket_mem_homogeneousSubmodule (w : List Bool) :
    dynkinWordBracket (FreeLieAlgebra.of K false) (FreeLieAlgebra.of K true) w ∈
      FreeLieAlgebra.homogeneousSubmodule K Bool w.length := by
  have hg (b : Bool) : _root_.FreeLieAlgebra.of K b ∈
      FreeLieAlgebra.homogeneousSubmodule K Bool 1 := by
    simpa only [FreeLieAlgebra.word_of, FreeMagma.length] using
      FreeLieAlgebra.word_mem_homogeneousSubmodule K (FreeMagma.of b)
  induction w with
  | nil => exact Submodule.zero_mem _
  | cons b w ih =>
    cases w with
    | nil =>
      cases b
      · simpa [dynkinWordBracket] using hg false
      · simpa [dynkinWordBracket] using hg true
    | cons c w =>
      rw [dynkinWordBracket_cons_cons]
      have hb : (if b then _root_.FreeLieAlgebra.of K true else
          _root_.FreeLieAlgebra.of K false) ∈
          FreeLieAlgebra.homogeneousSubmodule K Bool 1 := by
        cases b <;> exact hg _
      simpa only [List.length_cons, vadd_eq_add, Nat.add_comm 1] using
        SetLike.GradedBracket.bracket_mem hb ih

/-- The universal Dynkin polynomial of degree `n` lies in the word-length piece of degree `n`. -/
theorem dynkinPolynomial_mem_homogeneousSubmodule (n : ℕ) :
    dynkinPolynomial K n ∈ FreeLieAlgebra.homogeneousSubmodule K Bool n := by
  unfold dynkinPolynomial dynkinTerm
  apply Submodule.sum_mem
  intro k _
  apply Submodule.smul_mem
  apply dynkinBlockSum_mem
  intro w hw
  simpa only [hw] using dynkinWordBracket_mem_homogeneousSubmodule K w

/-- The degreewise Dynkin series, with each coefficient in its homogeneous free Lie piece. -/
def dynkinSeries : (n : ℕ) → FreeLieAlgebra.homogeneousSubmodule K Bool n :=
  fun n => ⟨dynkinPolynomial K n, dynkinPolynomial_mem_homogeneousSubmodule K n⟩

/-- Each coefficient of the degreewise Dynkin series is the universal Dynkin polynomial. -/
@[simp]
theorem coe_dynkinSeries (n : ℕ) : (dynkinSeries K n : FreeLieAlgebra K Bool) =
    dynkinPolynomial K n := by simp [dynkinSeries]

/-- The homogeneous free-Lie series has zero constant coefficient. -/
@[simp]
theorem dynkinSeries_zero : dynkinSeries K 0 = 0 := by
  ext
  simp

end TauCeti.BCH
