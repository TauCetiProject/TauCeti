/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.CriticalValues
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FieldSimp
import TauCeti.Data.Rat.AbcTriple

/-!
# Belyi polynomials and the three-point step of Belyi's theorem

For natural numbers `m` and `n`, the Belyi polynomial

  `B_{m,n} = ((m + n) ^ (m + n) / (m ^ m * n ^ n)) * X ^ m * (1 - X) ^ n`

sends `0` and `1` to `0` (for `m` and `n` positive) and `m / (m + n)` to `1`, and its
derivative is a multiple of `X ^ (m - 1) * (1 - X) ^ (n - 1) * (m - (m + n) * X)`. So its
critical points lie in `{0, 1, m / (m + n)}` and its critical values lie in `{0, 1}`. The
containment of critical points is strict when `m = 1` or `n = 1`: `B_{1,1} = 4 X (1 - X)` has
the single critical point `1 / 2`.

Composing an affine normalization over `ℚ` with a Belyi polynomial sends three chosen rational
points into `{0, 1}` without creating critical values outside `{0, 1}`. Inducting on the size of
the set gives polynomial Belyification over `ℚ`: every finite set of rational numbers is carried
into `{0, 1}` by a nonconstant polynomial with rational coefficients whose critical values, in
every field of characteristic zero, lie in `{0, 1}`. Being a polynomial, it also fixes `∞`.
This is the step of Belyi's theorem that follows the reduction of algebraic branch values to
rational ones.

## Main declarations

* `TauCeti.belyiPolynomial`: the Belyi polynomial `B_{m,n}` over a field; `B_{1,1}` is
  `4 X (1 - X)` (`TauCeti.belyiPolynomial_one_one`).
* `TauCeti.X_mul_one_sub_X_mul_derivative_belyiPolynomial`: the derivative of `B_{m,n}`,
  multiplied by `X (1 - X)`.
* `TauCeti.rootSet_derivative_belyiPolynomial_subset`: the critical points of `B_{m,n}` lie in
  `{0, 1, m / (m + n)}`.
* `TauCeti.criticalValues_belyiPolynomial_subset`: the critical values of `B_{m,n}` lie in
  `{0, 1}`.
* `TauCeti.exists_polynomial_eval_mem_criticalValues_subset`: polynomial Belyification of a
  finite set of rational numbers.

## References

* G. V. Belyi, *On Galois extensions of a maximal cyclotomic field*, Izv. Akad. Nauk SSSR
  Ser. Mat. 43 (1979), 267–276.
* Bernhard Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004),
  253–265, Lemma 3.6.
* Ernesto Girondo and Gabino González-Diez, *Introduction to Compact Riemann Surfaces and
  Dessins d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University
  Press, 2012, §3.1.
-/

public section

open Polynomial

namespace TauCeti

universe u

section Field

variable (K : Type*) [Field K]

/-- The Belyi polynomial `B_{m,n} = ((m + n) ^ (m + n) / (m ^ m * n ^ n)) * X ^ m * (1 - X) ^ n`.
In characteristic zero its normalizing constant makes its value at `m / (m + n)` equal to `1`
(`TauCeti.eval_div_belyiPolynomial`). -/
noncomputable def belyiPolynomial (m n : ℕ) : K[X] :=
  C (((m : K) + n) ^ (m + n) / ((m : K) ^ m * (n : K) ^ n)) * X ^ m * (1 - X) ^ n

variable {K}

/-- The Belyi polynomial is preserved by every ring homomorphism of fields. -/
@[simp]
theorem map_belyiPolynomial {L : Type*} [Field L] (f : K →+* L) (m n : ℕ) :
    (belyiPolynomial K m n).map f = belyiPolynomial L m n := by
  simp [belyiPolynomial, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub]

/-- The Belyi polynomial `B_{1,1}` is `4 X (1 - X)`. -/
theorem belyiPolynomial_one_one : belyiPolynomial K 1 1 = C 4 * X * (1 - X) := by
  norm_num [belyiPolynomial]

/-- The value of the Belyi polynomial at a point `x`. -/
theorem eval_belyiPolynomial (m n : ℕ) (x : K) :
    (belyiPolynomial K m n).eval x =
      ((m : K) + n) ^ (m + n) / ((m : K) ^ m * (n : K) ^ n) * x ^ m * (1 - x) ^ n := by
  simp [belyiPolynomial]

/-- For `m ≠ 0`, the Belyi polynomial vanishes at `0`. -/
@[simp]
theorem eval_zero_belyiPolynomial {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    (belyiPolynomial K m n).eval 0 = 0 := by
  simp [eval_belyiPolynomial, hm]

/-- For `n ≠ 0`, the Belyi polynomial vanishes at `1`. -/
@[simp]
theorem eval_one_belyiPolynomial (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (belyiPolynomial K m n).eval 1 = 0 := by
  simp [eval_belyiPolynomial, hn]

/-- The derivative of the Belyi polynomial: `X (1 - X) B′_{m,n} = B_{m,n} (m - (m + n) X)`.
Multiplying by `X (1 - X)` avoids the exponents `m - 1` and `n - 1`. -/
theorem X_mul_one_sub_X_mul_derivative_belyiPolynomial (m n : ℕ) :
    X * (1 - X) * derivative (belyiPolynomial K m n) =
      belyiPolynomial K m n * (C (m : K) - C ((m : K) + n) * X) := by
  rw [belyiPolynomial]
  generalize ((m : K) + n) ^ (m + n) / ((m : K) ^ m * (n : K) ^ n) = c
  -- Split off `m = 0` and `n = 0` so that the exponents `m - 1` and `n - 1` simplify.
  rcases m with _ | m <;> rcases n with _ | n <;>
    simp only [derivative_mul, derivative_pow, derivative_C, derivative_sub, derivative_one,
      derivative_X, Nat.add_sub_cancel, map_add, map_natCast] <;> ring

variable [CharZero K]

/-- In characteristic zero, the normalizing constant `(m + n) ^ (m + n) / (m ^ m * n ^ n)` of the
Belyi polynomial is nonzero. -/
theorem belyiConstant_ne_zero (m n : ℕ) :
    ((m : K) + n) ^ (m + n) / ((m : K) ^ m * (n : K) ^ n) ≠ 0 := by
  -- `a ^ a` is nonzero for every natural number `a`, including `0 ^ 0 = 1`.
  refine div_ne_zero ?_ (mul_ne_zero ?_ ?_) <;> exact_mod_cast Nat.pow_self_pos.ne'

/-- In characteristic zero, the Belyi polynomial takes the value `1` at `m / (m + n)`. -/
@[simp]
theorem eval_div_belyiPolynomial (m n : ℕ) :
    (belyiPolynomial K m n).eval ((m : K) / (m + n)) = 1 := by
  rcases eq_or_ne (m + n) 0 with h | h
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp h
    simp [eval_belyiPolynomial]
  have hmn : (m : K) + n ≠ 0 := by exact_mod_cast h
  have hsub : 1 - (m : K) / (m + n) = n / (m + n) := by
    field_simp
    ring
  have hc := belyiConstant_ne_zero (K := K) m n
  rw [div_ne_zero_iff, mul_ne_zero_iff] at hc
  obtain ⟨-, hm, hn⟩ := hc
  rw [eval_belyiPolynomial, hsub, div_pow, div_pow, pow_add]
  field_simp

/-- In characteristic zero, the Belyi polynomial `B_{m,n}` has degree `m + n`. -/
theorem natDegree_belyiPolynomial (m n : ℕ) : (belyiPolynomial K m n).natDegree = m + n := by
  have hc := belyiConstant_ne_zero (K := K) m n
  have h1 : (1 - X : K[X]).natDegree = 1 := by
    rw [← neg_sub, natDegree_neg, ← C_1, natDegree_X_sub_C]
  rw [belyiPolynomial, mul_assoc, natDegree_C_mul hc, natDegree_mul (pow_ne_zero _ X_ne_zero)
    (pow_ne_zero _ (fun h ↦ by simp [h] at h1)), natDegree_X_pow, natDegree_pow, h1, mul_one]

/-- The critical points of the Belyi polynomial lie in `{0, 1, m / (m + n)}`. The containment is
strict when `m = 1` or `n = 1`. -/
theorem rootSet_derivative_belyiPolynomial_subset (L : Type*) [Field L] [Algebra K L]
    (m n : ℕ) :
    (derivative (belyiPolynomial K m n)).rootSet L ⊆ {0, 1, (m : L) / (m + n)} := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  intro x hx
  rw [← rootSet_map L (T := L), ← derivative_map, map_belyiPolynomial, mem_rootSet] at hx
  obtain ⟨hne, hx⟩ := hx
  rw [coe_aeval_eq_eval] at hx
  -- Evaluate `X (1 - X) B′ = B (m - (m + n) X)` at the critical point `x`.
  have key := congr_arg (eval x) (X_mul_one_sub_X_mul_derivative_belyiPolynomial (K := L) m n)
  simp only [eval_mul, eval_sub, eval_X, eval_one, eval_C, hx, mul_zero] at key
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra! h
  obtain ⟨h0, h1, hr⟩ := h
  rcases mul_eq_zero.mp key.symm with h | h
  · rw [eval_belyiPolynomial] at h
    exact mul_ne_zero (mul_ne_zero (belyiConstant_ne_zero m n) (pow_ne_zero _ h0))
      (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h1))) h
  rcases eq_or_ne ((m : L) + n) 0 with hmn | hmn
  · obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := Nat.add_eq_zero_iff.mp (by exact_mod_cast hmn)
    simp [belyiPolynomial] at hne
  exact hr (by field_simp; linear_combination -h)

/-- The critical values of the Belyi polynomial lie in `{0, 1}`. -/
theorem criticalValues_belyiPolynomial_subset (L : Type*) [Field L] [Algebra K L] (m n : ℕ) :
    (belyiPolynomial K m n).criticalValues L ⊆ {0, 1} := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_criticalValues.mp hy
  rw [← eval_map_algebraMap, map_belyiPolynomial, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases rootSet_derivative_belyiPolynomial_subset L m n hx with rfl | rfl | rfl
  · rcases eq_or_ne m 0 with rfl | hm
    · simpa using Or.inr (eval_div_belyiPolynomial (K := L) 0 n)
    · exact Or.inl (eval_zero_belyiPolynomial hm n)
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [eval_belyiPolynomial]
    · exact Or.inl (eval_one_belyiPolynomial m hn)
  · exact Or.inr (eval_div_belyiPolynomial m n)

end Field

section Rat

/-- If `p` and `q` over `ℚ` have their critical values in `{0, 1}`, in every field of
characteristic zero, and `p` sends `0` and `1` into `{0, 1}`, then `p ∘ q` has its critical
values in `{0, 1}` as well. -/
private theorem criticalValues_comp_subset_zero_one {p q : ℚ[X]}
    (hp : ∀ (L : Type u) [Field L] [Algebra ℚ L], p.criticalValues L ⊆ {0, 1})
    (hq : ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1})
    (hp0 : p.eval 0 ∈ ({0, 1} : Set ℚ)) (hp1 : p.eval 1 ∈ ({0, 1} : Set ℚ))
    (L : Type u) [Field L] [Algebra ℚ L] :
    (p.comp q).criticalValues L ⊆ {0, 1} := by
  -- A value of `p` at `0` or `1` of `L` is the image of a rational value in `{0, 1}`.
  have hmap : ∀ y : ℚ, p.eval y ∈ ({0, 1} : Set ℚ) →
      aeval (algebraMap ℚ L y) p ∈ ({0, 1} : Set L) := by
    intro y h
    rw [aeval_algebraMap_apply_eq_algebraMap_eval]
    rcases h with h | h <;> simp_all
  refine (criticalValues_comp_subset p q).trans (Set.union_subset ?_ (hp L))
  rintro _ ⟨y, hy, rfl⟩
  rcases hq L hy with rfl | rfl
  · simpa using hmap 0 hp0
  · simpa using hmap 1 hp1

/-- **The three-point step.** For a set `S` of at least three rational numbers, an affine
normalization followed by a Belyi polynomial sends the least and the greatest element of `S`
to `0` and a third one to `1`. The resulting nonconstant polynomial has critical values in
`{0, 1}`, and the image of `S` is smaller than `S` and contains `0` and `1`. -/
private theorem exists_card_image_lt (S : Finset ℚ) (hS : 2 < S.card) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧
      (∀ (L : Type u) [Field L] [Algebra ℚ L], f.criticalValues L ⊆ {0, 1}) ∧
      (S.image fun s ↦ f.eval s).card < S.card ∧ (0 : ℚ) ∈ S.image (fun s ↦ f.eval s) ∧
      (1 : ℚ) ∈ S.image (fun s ↦ f.eval s) := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set a := S.min' hne
  set b := S.max' hne
  obtain ⟨c, hcS, hca, hcb⟩ : ∃ c ∈ S, c ≠ a ∧ c ≠ b := by
    have : 0 < ((S.erase a).erase b).card := by
      have h₁ := Finset.pred_card_le_card_erase (s := S) (a := a)
      have h₂ := Finset.pred_card_le_card_erase (s := S.erase a) (a := b)
      omega
    obtain ⟨c, hc⟩ := Finset.card_pos.mp this
    simp only [Finset.mem_erase] at hc
    exact ⟨c, hc.2.2, hc.2.1, hc.1⟩
  have hac : a < c := lt_of_le_of_ne (S.min'_le c hcS) hca.symm
  have hcb' : c < b := lt_of_le_of_ne (S.le_max' c hcS) hcb
  have hab : a ≠ b := (hac.trans hcb').ne
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  -- The affine normalization sending `a` to `0` and `b` to `1`.
  set A := C (b - a)⁻¹ * (X - C a)
  have hA : A.natDegree = 1 := by rw [natDegree_C_mul (inv_ne_zero hba), natDegree_X_sub_C]
  obtain ⟨m, n, hm, hn, hr⟩ := Rat.exists_eq_div_add_of_pos_of_lt_one
    (div_pos (sub_pos.mpr hac) (sub_pos.mpr (hac.trans hcb')))
    ((div_lt_one (sub_pos.mpr (hac.trans hcb'))).mpr (by linarith))
  set f := (belyiPolynomial ℚ m n).comp A
  have hfx : ∀ x, f.eval x = (belyiPolynomial ℚ m n).eval ((x - a) / (b - a)) := fun x ↦ by
    simp [f, A, div_eq_inv_mul]
  have hfa : f.eval a = 0 := by simp [hfx, eval_zero_belyiPolynomial hm]
  have hfb : f.eval b = 0 := by simp [hfx, div_self hba, eval_one_belyiPolynomial m hn]
  have hfc : f.eval c = 1 := by rw [hfx, hr, eval_div_belyiPolynomial]
  refine ⟨f, ?_, fun L _ _ ↦ ?_, ?_, hfa ▸ Finset.mem_image_of_mem _ (S.min'_mem hne),
    hfc ▸ Finset.mem_image_of_mem _ hcS⟩
  · rw [natDegree_comp, natDegree_belyiPolynomial, hA]
    omega
  · -- The affine normalization has no critical values.
    refine (criticalValues_comp_subset _ _).trans (Set.union_subset ?_
      (criticalValues_belyiPolynomial_subset L m n))
    simp [criticalValues_eq_empty_of_natDegree_le_one hA.le]
  · -- The image is smaller since the distinct points `a` and `b` have the same image.
    exact lt_of_le_of_ne Finset.card_image_le fun h ↦
      hab (Finset.card_image_iff.mp h (S.min'_mem hne) (S.max'_mem hne) (hfa.trans hfb.symm))

/-- **Polynomial Belyification over `ℚ`.** Every finite set `S` of rational numbers is carried
into `{0, 1}` by a nonconstant polynomial `q` with rational coefficients whose critical values,
in every field of characteristic zero, lie in `{0, 1}`. -/
theorem exists_polynomial_eval_mem_criticalValues_subset (S : Finset ℚ) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, q.eval s ∈ ({0, 1} : Set ℚ)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1} := by
  -- It suffices to treat sets containing `0` and `1`.
  suffices h : ∀ T : Finset ℚ, 0 ∈ T → 1 ∈ T → ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ T, q.eval s ∈ ({0, 1} : Set ℚ)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1} by
    obtain ⟨q, hq, hqS, hqcrit⟩ := h (insert 0 (insert 1 S)) (by simp) (by simp)
    exact ⟨q, hq, fun s hs ↦ hqS s (by simp [hs]), hqcrit⟩
  intro S hS0 hS1
  induction hS : S.card using Nat.strong_induction_on generalizing S with
  | _ k ih =>
  subst hS
  by_cases h3 : S.card ≤ 2
  · -- A set of at most two elements containing `0` and `1` is `{0, 1}`, fixed by `X`.
    have hS : S = {0, 1} := (Finset.eq_of_subset_of_card_le (by simp [Finset.insert_subset_iff,
      hS0, hS1]) (h3.trans (Finset.card_pair zero_ne_one).ge)).symm
    exact ⟨X, by simp, fun s hs ↦ by simpa [hS] using hs, fun L _ _ ↦ by simp⟩
  -- Apply the three-point step and recurse on the smaller image, which contains `0` and `1`.
  obtain ⟨f, hf, hfcrit, hT, h0, h1⟩ := exists_card_image_lt S (by omega)
  obtain ⟨q, hq, hqT, hqcrit⟩ := ih _ hT _ h0 h1 rfl
  refine ⟨q.comp f, ?_, fun s hs ↦ ?_,
    criticalValues_comp_subset_zero_one hqcrit hfcrit (hqT 0 h0) (hqT 1 h1)⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hq hf
  · rw [eval_comp]
    exact hqT _ (Finset.mem_image_of_mem _ hs)

end Rat

end TauCeti
