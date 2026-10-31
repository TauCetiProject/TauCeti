/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Basic
public import TauCeti.NumberTheory.HurwitzClassNumber
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.QuadraticDiscriminant
import TauCeti.NumberTheory.BinaryQuadraticForm.OfMatrix
import TauCeti.NumberTheory.BinaryQuadraticForm.Reflection
import TauCeti.NumberTheory.Divisors

/-!
# The elliptic trace fibres of Popa–Zagier's explicit element

Let `TauCeti.PopaZagier.weight M` be twelve times the coefficient of the integral matrix `M` in
Popa and Zagier's explicit Hecke element, their eq. (15). If `t² - 4 n = -D < 0`, then

`∑_{tr M = t, det M = n} weight M = -12 H(D)`,

the sum running over all integral matrices of trace `t` and determinant `n`, where `H` is the
Hurwitz class number `TauCeti.hurwitzClassNumber`. In Popa and Zagier's normalisation: the
coefficients of their element sum to `-H(4 n - t²)` over every elliptic trace fibre. The trace of
a matrix on the binary forms of degree `w` only depends on its trace and determinant
(`TauCeti.trace_binaryFormRep_eq_dickson_eval`), so this identity is the input that evaluates the
contribution of the elliptic matrices to the trace of the element on binary forms, the
class-number terms `P_{w+2}(t, n) H(4 n - t²)` of the Eichler–Selberg trace formula.

## Main results

* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_add_two`: for `n > 0`, the weights of the
  matrices of trace `t + 2` and determinant `n + t + 1` have the same sum as those of trace `t`
  and determinant `n`.
* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_eq_neg_twelve_mul_hurwitzClassNumber`: the
  weights of the matrices of trace `t` and determinant `n` sum to `-12 H(D)` when
  `t² - 4 n = -D < 0`.

## Proof

The translation `M ↦ M + 1` maps the matrices of trace `t` and determinant `n` bijectively to
those of trace `t + 2` and determinant `n + t + 1`. It fixes the form
`Q_M = c x² + (d - a) x y - b y²` of `M = (a b; c d)`, hence the discriminant `t² - 4 n`, and it
fixes the first line of each of the four sums of eq. (15). So it changes the weight of `M` only
where one of the second-line inequalities `c < a`, `b < d ≤ 0`, `a ≤ 0` and `d ≤ 0` changes, that is
at the matrices with `a = c`, `b = d`, `d = 0` or `a = 0`. For `n > 0` these are parametrised by the
factorisations `n = u v` into positive integers, and their changes cancel under `(u, v) ↦ (v, u)`.
This gives the first result; the sum over the matrices of trace `t` and determinant `n` therefore
depends only on `D = 4 n - t²`.

For `t ≤ -D` only the sums `T₃` and `T₄` contribute, with all their second-line inequalities
automatic. Through `M ↦ Q_M` their matrices are the forms `⟨a', b', c'⟩` of discriminant `-D` with
`0 ≤ -b' ≤ a' ≤ c'`, respectively `0 ≤ -b' ≤ c' ≤ a'`. Each of the two families is, with its
weights, six times the weighted count of the reduced forms of discriminant `-D` that defines
`H(D)`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1 and §4, eq. (15).
-/

public section

open Matrix

namespace TauCeti

namespace PopaZagier

/-! ### Translation by the identity -/

variable {t n : ℤ}

/-- The change of `T₁` under `M ↦ M + 1`, supported on the matrices with `a = c`. -/
private def corr₁ (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  if 0 ≤ M 1 0 ∧ M 1 0 = M 0 0 then chainWeight₃ (M 0 0 - M 1 1) (-M 0 1) (M 1 0) else 0

/-- The gain of `T₂` under `M ↦ M + 1`, supported on the matrices with `b = d < 0`. -/
private def corr₂ (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  if M 0 1 = M 1 1 ∧ M 1 1 ≤ -1 then chainWeight₃ (-M 0 1) (M 0 0 - M 1 1) (M 1 0) else 0

/-- The losses of `T₂` and `T₄` under `M ↦ M + 1`, supported on the matrices with `d = 0`. -/
private def corr₃ (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  if M 1 1 = 0 ∧ M 0 1 < 0 then
    chainWeight₃ (-M 0 1) (M 0 0 - M 1 1) (M 1 0) + chainWeight₄ 0 (M 0 0 - M 1 1) (-M 0 1) (M 1 0)
  else 0

/-- The loss of `T₃` under `M ↦ M + 1`, supported on the matrices with `a = 0`. -/
private def corr₄ (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  if M 0 0 = 0 ∧ 0 < M 1 0 then chainWeight₄ 0 (M 0 0 - M 1 1) (M 1 0) (-M 0 1) else 0

/-- The change of the four sums of eq. (15) under `(a b; c d) ↦ (a + 1, b; c, d + 1)`: the
first lines only involve `a - d`, `b` and `c`, so only the second lines change. -/
private theorem weight_add_one_add_one (a b c d : ℤ) :
    weight₁ (a + 1) b c (d + 1) - weight₂ (a + 1) b c (d + 1) - weight₃ (a + 1) b c (d + 1) -
      weight₄ (a + 1) b c (d + 1) =
    weight₁ a b c d - weight₂ a b c d - weight₃ a b c d - weight₄ a b c d +
      ((if 0 ≤ c ∧ c = a then chainWeight₃ (a - d) (-b) c else 0) -
        (if b = d ∧ d ≤ -1 then chainWeight₃ (-b) (a - d) c else 0) +
        (if d = 0 ∧ b < 0 then
          chainWeight₃ (-b) (a - d) c + chainWeight₄ 0 (a - d) (-b) c else 0) +
        (if a = 0 ∧ 0 < c then chainWeight₄ 0 (a - d) c (-b) else 0)) := by
  simp only [weight₁, weight₂, weight₃, weight₄, add_sub_add_right_eq_sub]
  generalize chainWeight₃ (a - d) (-b) c = X
  generalize chainWeight₃ (-b) (a - d) c = Y
  generalize chainWeight₄ 0 (a - d) c (-b) = Z
  generalize chainWeight₄ 0 (a - d) (-b) c = W
  have h₁ : (if 0 ≤ c ∧ c < a + 1 then X else 0) =
      (if 0 ≤ c ∧ c < a then X else 0) + (if 0 ≤ c ∧ c = a then X else 0) := by
    split_ifs <;> omega
  have h₂ : (if b < d + 1 ∧ d + 1 ≤ 0 then Y else 0) = (if b < d ∧ d ≤ 0 then Y else 0) +
      (if b = d ∧ d ≤ -1 then Y else 0) - (if d = 0 ∧ b < 0 then Y else 0) := by
    split_ifs <;> omega
  have h₃ : (if a + 1 ≤ 0 ∧ 0 < c then Z else 0) =
      (if a ≤ 0 ∧ 0 < c then Z else 0) - (if a = 0 ∧ 0 < c then Z else 0) := by
    split_ifs <;> omega
  have h₄ : (if d + 1 ≤ 0 ∧ 0 < -b then W else 0) =
      (if d ≤ 0 ∧ 0 < -b then W else 0) - (if d = 0 ∧ b < 0 then W else 0) := by
    split_ifs <;> omega
  have h₅ : (if d = 0 ∧ b < 0 then Y + W else 0) =
      (if d = 0 ∧ b < 0 then Y else 0) + (if d = 0 ∧ b < 0 then W else 0) := by
    split_ifs <;> omega
  rw [h₁, h₂, h₃, h₄, h₅]
  ring

/-- `weight (M + 1) - weight M` is the sum of the four corrections. -/
private theorem weight_add_one (M : Matrix (Fin 2) (Fin 2) ℤ) :
    weight (M + 1) = weight M + (corr₁ M - corr₂ M + corr₃ M + corr₄ M) := by
  simpa [weight, corr₁, corr₂, corr₃, corr₄, Matrix.add_apply, Matrix.one_apply] using
    weight_add_one_add_one (M 0 0) (M 0 1) (M 1 0) (M 1 1)

/-! ### Factorisations of `n` -/

/-- A function on matrices of trace `t` and determinant `n` supported on the image of a family
`φ` injective on the factorisations of `n` sums to its sum along `φ`. -/
private theorem finsum_eq_sum_divisorsAntidiagonal (g : Matrix (Fin 2) (Fin 2) ℤ → ℤ)
    (φ : ℕ × ℕ → Matrix (Fin 2) (Fin 2) ℤ)
    (hφ : ∀ p ∈ n.toNat.divisorsAntidiagonal, φ p ∈ traceDetFiber (Fin 2) t n)
    (hinj : Set.InjOn φ n.toNat.divisorsAntidiagonal)
    (hsupp : ∀ M ∈ traceDetFiber (Fin 2) t n, g M ≠ 0 →
      ∃ p ∈ n.toNat.divisorsAntidiagonal, φ p = M) :
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ g M.1).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, g M.1 = ∑ p ∈ n.toNat.divisorsAntidiagonal, g (φ p) := by
  classical
  set s : Finset (traceDetFiber (Fin 2) t n) :=
    n.toNat.divisorsAntidiagonal.attach.image fun p ↦ ⟨φ p.1, hφ p.1 p.2⟩ with hs
  have hsub : (Function.support fun M : traceDetFiber (Fin 2) t n ↦ g M.1) ⊆ s := by
    intro M hM
    obtain ⟨p, hp, hpM⟩ := hsupp M.1 M.2 hM
    exact Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, Subtype.ext hpM⟩
  refine ⟨s.finite_toSet.subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsub, hs, Finset.sum_image fun p _ q _ h ↦
    Subtype.ext (hinj p.2 q.2 (congrArg Subtype.val h))]
  exact Finset.sum_attach _ fun p ↦ g (φ p)

/-- The matrices with `a = c` are `(u, t - u - v; u, t - u)` for `n = u v`. -/
private theorem finsum_corr₁ (hn : 0 < n) :
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₁ M.1).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₁ M.1 = ∑ p ∈ n.toNat.divisorsAntidiagonal,
        chainWeight₃ (2 * p.1 - t) (p.1 + p.2 - t) p.1 := by
  obtain ⟨hfin, hsum⟩ := finsum_eq_sum_divisorsAntidiagonal (t := t) (n := n) corr₁
    (fun p ↦ !![(p.1 : ℤ), t - p.1 - p.2; p.1, t - p.1])
    (fun p hp ↦ mem_traceDetFiber_fin_two.mpr ⟨by simp, by
      obtain ⟨-, -, h⟩ := Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat hp
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
      linear_combination h⟩)
    (Set.LeftInvOn.injOn (f₁' := fun M ↦ ((M 0 0).toNat, (M 1 1 - M 0 1).toNat))
      fun _ _ ↦ by simp)
    (fun M hM h ↦ by
      obtain ⟨ht, hdet⟩ := mem_traceDetFiber_fin_two.mp hM
      unfold corr₁ at h
      split_ifs at h with hg
      · obtain ⟨hc, hca⟩ := hg
        have hdet' : M 0 0 * (M 1 1 - M 0 1) = n := by rw [← hdet, hca]; ring
        obtain ⟨hu, hv⟩ : 0 < M 0 0 ∧ 0 < M 1 1 - M 0 1 := by
          rcases pos_and_pos_or_neg_and_neg_of_mul_pos (hdet' ▸ hn) with h' | h'
          · exact h'
          · omega
        refine ⟨_, Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat hu hv hdet',
          Eq.trans ?_ (eta_fin_two M).symm⟩
        simp only [Int.toNat_of_nonneg hu.le, Int.toNat_of_nonneg hv.le,
          EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and]
        omega
      · exact absurd rfl h)
  refine ⟨hfin, hsum.trans (Finset.sum_congr rfl fun p hp ↦ ?_)⟩
  obtain ⟨h1, -, -⟩ := Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat hp
  simp only [corr₁, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one,
    h1.le, true_and, ite_true]
  ring_nf

/-- The matrices with `b = d < 0` are `(t + u, -u; t + u + v, -u)` for `n = u v`. -/
private theorem finsum_corr₂ (hn : 0 < n) :
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₂ M.1).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₂ M.1 = ∑ p ∈ n.toNat.divisorsAntidiagonal,
        chainWeight₃ p.1 (t + 2 * p.1) (t + p.1 + p.2) := by
  obtain ⟨hfin, hsum⟩ := finsum_eq_sum_divisorsAntidiagonal (t := t) (n := n) corr₂
    (fun p ↦ !![t + p.1, -(p.1 : ℤ); t + p.1 + p.2, -(p.1 : ℤ)])
    (fun p hp ↦ mem_traceDetFiber_fin_two.mpr ⟨by simp, by
      obtain ⟨-, -, h⟩ := Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat hp
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
      linear_combination h⟩)
    (Set.LeftInvOn.injOn (f₁' := fun M ↦ ((-M 1 1).toNat, (M 1 0 - M 0 0).toNat))
      fun _ _ ↦ by simp)
    (fun M hM h ↦ by
      obtain ⟨ht, hdet⟩ := mem_traceDetFiber_fin_two.mp hM
      unfold corr₂ at h
      split_ifs at h with hg
      · obtain ⟨hbd, hd⟩ := hg
        have hdet' : -M 1 1 * (M 1 0 - M 0 0) = n := by rw [← hdet, hbd]; ring
        have hu : 0 < -M 1 1 := by omega
        have hv : 0 < M 1 0 - M 0 0 := pos_of_mul_pos_right (hdet' ▸ hn) hu.le
        refine ⟨_, Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat hu hv hdet',
          Eq.trans ?_ (eta_fin_two M).symm⟩
        simp only [Int.toNat_of_nonneg hu.le, Int.toNat_of_nonneg hv.le,
          EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true]
        omega
      · exact absurd rfl h)
  refine ⟨hfin, hsum.trans (Finset.sum_congr rfl fun p hp ↦ ?_)⟩
  obtain ⟨h1, -, -⟩ := Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat hp
  have : -(p.1 : ℤ) ≤ -1 := by omega
  simp only [corr₂, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, this,
    and_self, ite_true]
  ring_nf

/-- The matrices with `d = 0` are `(t, -v; u, 0)` for `n = u v`. -/
private theorem finsum_corr₃ (hn : 0 < n) :
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₃ M.1).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₃ M.1 = ∑ p ∈ n.toNat.divisorsAntidiagonal,
        (chainWeight₃ p.2 t p.1 + chainWeight₄ 0 t p.2 p.1) := by
  obtain ⟨hfin, hsum⟩ := finsum_eq_sum_divisorsAntidiagonal (t := t) (n := n) corr₃
    (fun p ↦ !![t, -(p.2 : ℤ); p.1, 0])
    (fun p hp ↦ mem_traceDetFiber_fin_two.mpr ⟨by simp, by
      obtain ⟨-, -, h⟩ := Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat hp
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
      linear_combination h⟩)
    (Set.LeftInvOn.injOn (f₁' := fun M ↦ ((M 1 0).toNat, (-M 0 1).toNat)) fun _ _ ↦ by simp)
    (fun M hM h ↦ by
      obtain ⟨ht, hdet⟩ := mem_traceDetFiber_fin_two.mp hM
      unfold corr₃ at h
      split_ifs at h with hg
      · obtain ⟨hd, hb⟩ := hg
        have hdet' : M 1 0 * -M 0 1 = n := by rw [← hdet, hd]; ring
        have hv : 0 < -M 0 1 := by omega
        have hu : 0 < M 1 0 := pos_of_mul_pos_left (hdet' ▸ hn) hv.le
        refine ⟨_, Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat hu hv hdet',
          Eq.trans ?_ (eta_fin_two M).symm⟩
        simp only [Int.toNat_of_nonneg hu.le, Int.toNat_of_nonneg hv.le,
          EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and]
        omega
      · exact absurd rfl h)
  refine ⟨hfin, hsum.trans (Finset.sum_congr rfl fun p hp ↦ ?_)⟩
  obtain ⟨-, h2, -⟩ := Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat hp
  have : -(p.2 : ℤ) < 0 := by omega
  simp only [corr₃, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, this,
    and_self, ite_true, neg_neg, sub_zero]

/-- The matrices with `a = 0` are `(0, -v; u, t)` for `n = u v`. -/
private theorem finsum_corr₄ (hn : 0 < n) :
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₄ M.1).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₄ M.1 = ∑ p ∈ n.toNat.divisorsAntidiagonal,
        chainWeight₄ 0 (-t) p.1 p.2 := by
  obtain ⟨hfin, hsum⟩ := finsum_eq_sum_divisorsAntidiagonal (t := t) (n := n) corr₄
    (fun p ↦ !![0, -(p.2 : ℤ); p.1, t])
    (fun p hp ↦ mem_traceDetFiber_fin_two.mpr ⟨by simp, by
      obtain ⟨-, -, h⟩ := Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat hp
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
      linear_combination h⟩)
    (Set.LeftInvOn.injOn (f₁' := fun M ↦ ((M 1 0).toNat, (-M 0 1).toNat)) fun _ _ ↦ by simp)
    (fun M hM h ↦ by
      obtain ⟨ht, hdet⟩ := mem_traceDetFiber_fin_two.mp hM
      unfold corr₄ at h
      split_ifs at h with hg
      · obtain ⟨ha, hc⟩ := hg
        have hdet' : M 1 0 * -M 0 1 = n := by rw [← hdet, ha]; ring
        have hv : 0 < -M 0 1 := pos_of_mul_pos_right (hdet' ▸ hn) hc.le
        refine ⟨_, Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat hc hv hdet',
          Eq.trans ?_ (eta_fin_two M).symm⟩
        simp only [Int.toNat_of_nonneg hc.le, Int.toNat_of_nonneg hv.le,
          EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and]
        omega
      · exact absurd rfl h)
  refine ⟨hfin, hsum.trans (Finset.sum_congr rfl fun p hp ↦ ?_)⟩
  obtain ⟨h1, -, -⟩ := Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat hp
  simp only [corr₄, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, h1,
    and_self, ite_true, neg_neg, zero_sub]

/-- The total change of the weights under `M ↦ M + 1` at the factorisation `n = u v`, collecting
`corr₁`, ..., `corr₄`. -/
private def pairTerm (u v t : ℤ) : ℤ :=
  chainWeight₃ (2 * u - t) (u + v - t) u - chainWeight₃ u (t + 2 * u) (t + u + v) +
    chainWeight₃ v t u + chainWeight₄ 0 (-t) u v + chainWeight₄ 0 t v u

/-- The changes at `(u, v)` and at `(v, u)` cancel. -/
private theorem pairTerm_add_pairTerm (u v t : ℤ) (hu : 0 < u) (hv : 0 < v) :
    pairTerm u v t + pairTerm v u t = 0 := by
  wlog huv : u ≤ v generalizing u v
  · rw [add_comm]
    exact this v u hv hu (by omega)
  unfold pairTerm chainWeight₃ chainWeight₄
  have : t < -v ∨ t = -v ∨ (-v < t ∧ t < -u) ∨ t = -u ∨ (-u < t ∧ t < 0) ∨ t = 0 ∨
      (0 < t ∧ t < u) ∨ t = u ∨ (u < t ∧ t < v) ∨ t = v ∨ v < t := by omega
  rcases huv.lt_or_eq with h | rfl <;>
  rcases this with h | h | h | h | h | h | h | h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, and_true] <;> omega

/-- The changes cancel in total, by `(u, v) ↦ (v, u)`. -/
private theorem sum_pairTerm (n t : ℤ) :
    ∑ p ∈ n.toNat.divisorsAntidiagonal, pairTerm p.1 p.2 t = 0 := by
  have hswap : ∑ p ∈ n.toNat.divisorsAntidiagonal, pairTerm p.1 p.2 t =
      ∑ p ∈ n.toNat.divisorsAntidiagonal, pairTerm p.2 p.1 t := by
    conv_rhs => rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
    rfl
  have hsum : ∑ p ∈ n.toNat.divisorsAntidiagonal, (pairTerm p.1 p.2 t + pairTerm p.2 p.1 t) = 0 :=
    Finset.sum_eq_zero fun p hp ↦ by
      obtain ⟨h1, h2, -⟩ := Int.pos_pos_mul_eq_of_mem_divisorsAntidiagonal_toNat hp
      exact pairTerm_add_pairTerm _ _ t h1 h2
  rw [Finset.sum_add_distrib, ← hswap] at hsum
  omega

/-- **Translation by the identity.** For `n > 0`, the weights of the matrices of trace `t + 2`
and determinant `n + t + 1` have the same sum as those of trace `t` and determinant `n`.

The translation `M ↦ M + 1` is a bijection between these matrices, it fixes the discriminant
`t² - 4 n`, and its effect on the weights cancels in total. -/
theorem finsum_weight_traceDetFiber_add_two (hn : 0 < n) :
    ∑ᶠ M : traceDetFiber (Fin 2) (t + 2) (n + t + 1), weight M.1 =
      ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 := by
  obtain ⟨h₁, e₁⟩ := finsum_corr₁ (t := t) hn
  obtain ⟨h₂, e₂⟩ := finsum_corr₂ (t := t) hn
  obtain ⟨h₃, e₃⟩ := finsum_corr₃ (t := t) hn
  obtain ⟨h₄, e₄⟩ := finsum_corr₄ (t := t) hn
  have h₁₂ := (h₁.union h₂).subset (Function.support_sub _ _)
  have h₁₂₃ := (h₁₂.union h₃).subset (Function.support_add _ _)
  have h₁₂₃₄ := (h₁₂₃.union h₄).subset (Function.support_add _ _)
  -- the fibre `(t + 2, n + t + 1)` is the translate of `(t, n)` by the scalar `1`
  have ht : t + 2 = t + 2 * 1 := by ring
  have hn' : n + t + 1 = n + 1 * t + 1 ^ 2 := by ring
  rw [ht, hn', ← finsum_comp_equiv (traceDetFiberAddScalarEquiv t n 1)]
  simp only [traceDetFiberAddScalarEquiv_apply_coe, map_one, weight_add_one]
  rw [finsum_add_distrib (finite_support_weight_traceDetFiber t n) h₁₂₃₄,
    finsum_add_distrib h₁₂₃ h₄, finsum_add_distrib h₁₂ h₃, finsum_sub_distrib h₁ h₂, e₁, e₂, e₃,
    e₄, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [add_eq_left]
  refine (Finset.sum_congr rfl fun p _ ↦ ?_).trans (sum_pairTerm n t)
  unfold pairTerm
  ring_nf

/-! ### Very negative trace -/

open BinaryQuadraticForm in
/-- For `t ≤ -D`, only `T₃` and `T₄` contribute to the weight of a matrix of trace `t` and
determinant `n`, without their second-line conditions; in terms of `Q_M = ⟨a', b', c'⟩` their
first lines are `0 ≤ -b' ≤ a' ≤ c'` and `0 ≤ -b' ≤ c' ≤ a'`. -/
private theorem weight_eq_of_le {M : Matrix (Fin 2) (Fin 2) ℤ} {D : ℤ} (hD : 0 < D)
    (hM : M ∈ traceDetFiber (Fin 2) t n) (h : t ^ 2 - 4 * n = -D) (ht : t ≤ -D) :
    weight M = -(chainWeight₄ 0 (-(ofMatrix M).b) (ofMatrix M).a (ofMatrix M).c +
      chainWeight₄ 0 (-(ofMatrix M).b) (ofMatrix M).c (ofMatrix M).a) := by
  obtain ⟨htr, hdet⟩ := mem_traceDetFiber_fin_two.mp hM
  rw [weight]
  simp only [ofMatrix_a, ofMatrix_b, ofMatrix_c, neg_sub]
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  -- the discriminant of `Q_M` is `(a - d)² + 4 b c = -D`
  have hdisc : (a - d) ^ 2 + 4 * b * c = -D := by rw [← h, ← htr, ← hdet]; ring
  have h₁ : weight₁ a b c d = 0 := by
    unfold weight₁
    split_ifs with hg
    · by_contra hne
      have := le_of_chainWeight₃_ne_zero hne
      omega
    · rfl
  have h₂ : weight₂ a b c d = 0 := by
    unfold weight₂
    split_ifs with hg
    · by_contra hne
      obtain ⟨hx, hy⟩ := le_of_chainWeight₃_ne_zero hne
      -- with `x = -b`, `y = a - d` and `z = c`, `t > y - 2 x ≥ -D`
      rcases le_or_gt (2 * -b) (a - d) with hyx | hyx
      · omega
      · have hzy : 0 ≤ c - (a - d) := by omega
        have hx₀ : 0 ≤ -b := by omega
        have hy₁ : 0 ≤ a - d - 1 := by omega
        have hxy : 0 ≤ 4 * -b - (a - d) := by omega
        nlinarith [mul_nonneg hzy hx₀, mul_nonneg hy₁ hxy]
    · rfl
  have h₃ : weight₃ a b c d = chainWeight₄ 0 (a - d) c (-b) := by
    unfold weight₃
    split_ifs with hg
    · rfl
    · by_contra hne
      obtain ⟨h0, hy, hz⟩ := le_of_chainWeight₄_ne_zero (Ne.symm hne)
      have hc : 0 < c := by
        rcases hy.lt_or_eq with hy | hy
        · omega
        · nlinarith
      -- `3 c² ≤ D`, so `a - d ≤ c ≤ D ≤ -t`
      have : 3 * c ^ 2 ≤ D := by nlinarith [mul_le_mul_of_nonneg_left hz hc.le]
      have : c ≤ D := by nlinarith
      omega
  have h₄ : weight₄ a b c d = chainWeight₄ 0 (a - d) (-b) c := by
    unfold weight₄
    split_ifs with hg
    · rfl
    · by_contra hne
      obtain ⟨h0, hy, hz⟩ := le_of_chainWeight₄_ne_zero (Ne.symm hne)
      have hb : 0 < -b := by
        rcases hy.lt_or_eq with hy | hy
        · omega
        · nlinarith
      omega
  rw [h₁, h₂, h₃, h₄]
  ring

/-! ### Reduced forms -/

/-- Six times `reducedFormWeight f`. -/
private def sixWeight (f : BinaryQuadraticForm ℤ) : ℤ :=
  if f.b = 0 ∧ f.a = f.c then 3 else if f.a = f.b ∧ f.b = f.c then 2 else 6

/-- `sixWeight f` is six times `reducedFormWeight f`. -/
private theorem six_mul_reducedFormWeight (f : BinaryQuadraticForm ℤ) :
    6 * reducedFormWeight f = sixWeight f := by
  unfold reducedFormWeight sixWeight
  split_ifs <;> norm_num

/-- The involution `⟨a, b, c⟩ ↦ ⟨a, -b, c⟩` on the reduced forms with `0 < |b| < a < c`. -/
private def negMiddle (f : BinaryQuadraticForm ℤ) : BinaryQuadraticForm ℤ :=
  if 0 < |f.b| ∧ |f.b| < f.a ∧ f.a < f.c then ⟨f.a, -f.b, f.c⟩ else f

/-- On a reduced form `⟨a, b, c⟩` of discriminant `-D`, `chainWeight₄ 0 b a c - sixWeight` is `6`
if `0 < b < a < c`, `-6` if `0 < -b < a < c`, and `0` otherwise. -/
private theorem chainWeight₄_sub_sixWeight {D : ℕ} [NeZero D] {f : BinaryQuadraticForm ℤ}
    (hf : f ∈ reducedForms D) :
    chainWeight₄ 0 f.b f.a f.c - sixWeight f =
      (if 0 < f.b ∧ f.b < f.a ∧ f.a < f.c then 6 else 0) -
        (if 0 < -f.b ∧ -f.b < f.a ∧ f.a < f.c then 6 else 0) := by
  have ha := a_pos_of_mem_reducedForms hf
  obtain ⟨-, h1, h2, h3⟩ := (mem_reducedForms (NeZero.ne D)).mp hf
  unfold chainWeight₄ sixWeight
  rcases abs_cases f.b with ⟨hb, hb'⟩ | ⟨hb, hb'⟩ <;> rw [hb] at h1 h3 <;>
  rcases lt_trichotomy f.b 0 with h | h | h <;>
  rcases lt_trichotomy f.b f.a with h' | h' | h' <;>
  rcases lt_trichotomy (-f.b) f.a with h₀ | h₀ | h₀ <;>
  rcases h2.lt_or_eq with h'' | h'' <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right] <;> omega

/-- The forms `⟨a, b, c⟩` with `0 ≤ b ≤ a ≤ c` of discriminant `-D`, counted with
`chainWeight₄ 0 b a c`, are six times the weighted reduced forms: `⟨a, b, c⟩` with `0 < b < a < c`
stands for the two reduced forms `⟨a, ±b, c⟩`. -/
private theorem sum_reducedForms_chainWeight₄ (D : ℕ) [NeZero D] :
    ∑ f ∈ reducedForms D, chainWeight₄ 0 f.b f.a f.c = ∑ f ∈ reducedForms D, sixWeight f := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_involution (fun f _ ↦ negMiddle f) (fun f hf ↦ ?_) (fun f hf hne ↦ ?_)
    (fun f hf ↦ ?_) (fun f hf ↦ ?_)
  · unfold negMiddle
    split_ifs with hs
    · rw [chainWeight₄_sub_sixWeight hf,
        chainWeight₄_sub_sixWeight (mk_neg_mem_reducedForms hf hs.2.1 hs.2.2)]
      dsimp only
      rcases abs_cases f.b with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rw [hb] at hs <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right, neg_neg] <;> omega
    · rw [chainWeight₄_sub_sixWeight hf, ite_eq_right fun h ↦ hs (by rw [abs_of_pos h.1]; exact h),
        ite_eq_right fun h ↦ hs (by rw [abs_of_neg (by omega)]; exact h)]
      rfl
  · unfold negMiddle
    split_ifs with hs
    · intro h
      have := congrArg BinaryQuadraticForm.b h
      dsimp only at this
      have := abs_pos.mp hs.1
      omega
    · rw [chainWeight₄_sub_sixWeight hf, ite_eq_right fun h ↦ hs (by rw [abs_of_pos h.1]; exact h),
        ite_eq_right fun h ↦ hs (by rw [abs_of_neg (by omega)]; exact h)] at hne
      exact absurd rfl hne
  · unfold negMiddle
    split_ifs with hs
    · exact mk_neg_mem_reducedForms hf hs.2.1 hs.2.2
    · exact hf
  · unfold negMiddle
    split_ifs with hs hs'
    · ext <;> simp
    · simp only [abs_neg] at hs'
      exact absurd hs hs'
    · rfl

/-- The weighted count `sum_reducedForms_chainWeight₄` over all forms of discriminant `-D`. -/
private theorem finsum_chainWeight₄_forms (D : ℕ) [NeZero D] :
    (Function.support fun f : {f : BinaryQuadraticForm ℤ // f.discrim = -(D : ℤ)} ↦
      chainWeight₄ 0 f.1.b f.1.a f.1.c).Finite ∧
    ∑ᶠ f : {f : BinaryQuadraticForm ℤ // f.discrim = -(D : ℤ)}, chainWeight₄ 0 f.1.b f.1.a f.1.c =
      ∑ f ∈ reducedForms D, sixWeight f := by
  classical
  have hsub : (Function.support fun f : {f : BinaryQuadraticForm ℤ // f.discrim = -(D : ℤ)} ↦
      chainWeight₄ 0 f.1.b f.1.a f.1.c) ⊆
      ((reducedForms D).subtype fun f ↦ f.discrim = -(D : ℤ) : Set _) := by
    intro f hf
    obtain ⟨h0, h1, h2⟩ := le_of_chainWeight₄_ne_zero hf
    rw [Finset.mem_coe, Finset.mem_subtype]
    refine (mem_reducedForms (NeZero.ne D)).mpr ⟨f.2, ?_⟩
    rw [isReducedForm_iff, abs_of_nonneg h0]
    exact ⟨h1, h2, fun _ ↦ h0⟩
  refine ⟨Finset.finite_toSet _ |>.subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsub]
  exact (Finset.sum_subtype_of_mem (fun g : BinaryQuadraticForm ℤ ↦ chainWeight₄ 0 g.b g.a g.c)
    fun g hg ↦ ((mem_reducedForms (NeZero.ne D)).mp hg).1).trans (sum_reducedForms_chainWeight₄ D)

/-- The matrices of trace `t` and determinant `n` and the forms of discriminant `t² - 4 n`. -/
private def formEquiv {D : ℕ} (h : t ^ 2 - 4 * n = -D) :
    traceDetFiber (Fin 2) t n ≃ {f : BinaryQuadraticForm ℤ // f.discrim = -(D : ℤ)} :=
  (Equiv.subtypeEquivRight fun _ ↦ mem_traceDetFiber).trans
    ((BinaryQuadraticForm.ofMatrixEquiv t n).trans (Equiv.subtypeEquivRight fun _ ↦ by rw [h]))

/-- `formEquiv h` sends a matrix `M` to its form `Q_M`. -/
private theorem coe_formEquiv {D : ℕ} (h : t ^ 2 - 4 * n = -D) (M : traceDetFiber (Fin 2) t n) :
    (formEquiv h M : BinaryQuadraticForm ℤ) = BinaryQuadraticForm.ofMatrix M.1 := by
  simp [formEquiv]

open BinaryQuadraticForm in
/-- For `t ≤ -D`, the weights of the matrices of trace `t` and determinant `n` sum to `-12 H(D)`,
in the form `-2 ∑ sixWeight`. -/
private theorem finsum_weight_of_le {D : ℕ} [NeZero D] (h : t ^ 2 - 4 * n = -D)
    (ht : t ≤ -D) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 =
      -(2 * ∑ f ∈ reducedForms D, sixWeight f) := by
  obtain ⟨hfin, hsum⟩ := finsum_chainWeight₄_forms D
  set g : {f : BinaryQuadraticForm ℤ // f.discrim = -(D : ℤ)} → ℤ :=
    fun f ↦ chainWeight₄ 0 f.1.b f.1.a f.1.c
  -- `⟨a, b, c⟩ ↦ ⟨a, -b, c⟩` and `⟨a, b, c⟩ ↦ S • ⟨a, b, c⟩ = ⟨c, -b, a⟩` on the forms of
  -- discriminant `-D`
  let e₁ : {f : BinaryQuadraticForm ℤ // f.discrim = -(D : ℤ)} ≃
      {f : BinaryQuadraticForm ℤ // f.discrim = -(D : ℤ)} :=
    { toFun f := ⟨f.1.reflected, by rw [discrim_reflected, f.2]⟩
      invFun f := ⟨f.1.reflected, by rw [discrim_reflected, f.2]⟩
      left_inv f := Subtype.ext f.1.reflected_reflected
      right_inv f := Subtype.ext f.1.reflected_reflected }
  let e₂ : {f : BinaryQuadraticForm ℤ // f.discrim = -(D : ℤ)} ≃
      {f : BinaryQuadraticForm ℤ // f.discrim = -(D : ℤ)} :=
    (MulAction.toPerm (α := SpecialLinearGroup (Fin 2) ℤ) ModularGroup.S).subtypeEquiv
      fun f ↦ by rw [MulAction.toPerm_apply, discrim_smul]
  have hfin₁ : (Function.support (g ∘ e₁)).Finite := hfin.preimage e₁.injective.injOn
  have hfin₂ : (Function.support (g ∘ e₂)).Finite := hfin.preimage e₂.injective.injOn
  have hD : (0 : ℤ) < D := by exact_mod_cast NeZero.pos D
  calc ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1
      = ∑ᶠ M : traceDetFiber (Fin 2) t n,
          -((g ∘ e₁) (formEquiv h M) + (g ∘ e₂) (formEquiv h M)) :=
        finsum_congr fun M ↦ by
          rw [weight_eq_of_le hD M.2 h ht]
          simp only [Function.comp_apply, g, e₁, e₂, Equiv.coe_fn_mk, Equiv.subtypeEquiv_apply,
            MulAction.toPerm_apply, coe_formEquiv, reflected_a, reflected_b, reflected_c, S_smul]
    _ = ∑ᶠ f, -((g ∘ e₁) f + (g ∘ e₂) f) :=
        finsum_comp_equiv (formEquiv h) (f := fun f ↦ -((g ∘ e₁) f +
          (g ∘ e₂) f))
    _ = -(∑ᶠ f, g (e₁ f) + ∑ᶠ f, g (e₂ f)) := by
        rw [finsum_neg_distrib, finsum_add_distrib hfin₁ hfin₂]
        rfl
    _ = -(2 * ∑ f ∈ reducedForms D, sixWeight f) := by
        rw [finsum_comp_equiv, finsum_comp_equiv, hsum, two_mul]

/-! ### The elliptic fibres -/

/-- **The elliptic trace fibres of Popa–Zagier's element.** If `t² - 4 n = -D < 0`, then the
weights of the integral matrices of trace `t` and determinant `n` sum to `-12 H(D)`: the
coefficients of Popa and Zagier's explicit element, a twelfth of the weights, sum to
`-H(4 n - t²)` over the matrices of trace `t` and determinant `n`.

The hypothesis `D ≠ 0` is needed: for `t = 2 a` and `n = a²` with `a > 0` the weights sum to
`2`, the weight of the scalar matrix `a • 1`, while `-12 H(0) = 1`. -/
theorem finsum_weight_traceDetFiber_eq_neg_twelve_mul_hurwitzClassNumber {D : ℕ} [NeZero D]
    (h : t ^ 2 - 4 * n = -D) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, (weight M.1 : ℚ) = -12 * hurwitzClassNumber D := by
  -- descend from `t` to a trace `≤ -D` in steps of `2`, keeping `t² - 4 n = -D`
  have key (k : ℕ) : ∀ t n : ℤ, t ^ 2 - 4 * n = -D → t ≤ 2 * k - D →
      ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.1 =
        -(2 * ∑ f ∈ reducedForms D, sixWeight f) := by
    induction k with
    | zero => exact fun t n h ht ↦ finsum_weight_of_le h (by simpa using ht)
    | succ k ih =>
      intro t n h ht
      by_cases ht' : t ≤ -D
      · exact finsum_weight_of_le h ht'
      have hD : (0 : ℤ) < D := by exact_mod_cast NeZero.pos D
      have hpos : 0 < n - t + 1 := by nlinarith [sq_nonneg (t - 2)]
      have hstep := finsum_weight_traceDetFiber_add_two (t := t - 2) hpos
      have hn' : n - t + 1 + (t - 2) + 1 = n := by ring
      rw [sub_add_cancel, hn'] at hstep
      rw [hstep]
      exact ih (t - 2) (n - t + 1) (by linear_combination h) (by push_cast at ht ⊢; omega)
  have hcast := map_finsum (Int.castAddHom ℚ) (finite_support_weight_traceDetFiber t n)
  simp only [Int.coe_castAddHom] at hcast
  rw [← hcast, key (t + D).toNat t n h (by omega), hurwitzClassNumber_of_ne_zero (NeZero.ne D),
    Finset.mul_sum]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  rw [← six_mul_reducedFormWeight]
  ring

end PopaZagier

end TauCeti
