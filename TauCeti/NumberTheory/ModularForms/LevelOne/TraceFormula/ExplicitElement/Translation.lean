/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.ExplicitElement.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.NumberTheory.Divisors

/-!
# Translation of the trace fibres of Popa–Zagier's explicit element

Let `TauCeti.PopaZagier.weight M` be twelve times the coefficient of the integral matrix `M` in
Popa and Zagier's explicit Hecke element, their eq. (15). For `n ≠ 0`, translation by the identity
matrix `M ↦ M + 1` preserves the sum of `weight M` over the trace–determinant fibre `(t, n)`:

`∑_{tr M = t + 2, det M = n + t + 1} weight M = ∑_{tr M = t, det M = n} weight M`.

This module proves the translation identity and its three shared non-elliptic consequences:
vanishing for nonpositive trace, reduction of positive-trace fibres to the range `0 < n' < t'`,
and evaluation of the fibres in that range.

## Main results

* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_add_two`: for `n ≠ 0`, the weights of the
  matrices of trace `t + 2` and determinant `n + t + 1` have the same sum as those of trace `t`
  and determinant `n`.
* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_eq_zero_of_trace_nonpos`: the weights of the
  matrices of trace `t ≤ 0` and determinant `n` sum to zero when `t² - 4 n ≥ 0`.
* `TauCeti.PopaZagier.exists_finsum_weight_traceDetFiber_eq`: for `t > 0`, `n > 0`, and
  `t² - 4 n ≥ 0`, the fibre sum equals that of a fibre `(t', n')` of the same discriminant with
  `0 < n' < t'`.
* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_of_det_lt_trace`: for `0 < n < t`, the weights
  sum to `2` if `(t, n) = (2, 1)`, to `12 (n - 1)` if `t = n + 1` with `n > 1`, and to `0`
  otherwise.

## Proof

The translation `M ↦ M + 1` maps the matrices of trace `t` and determinant `n` bijectively to
those of trace `t + 2` and determinant `n + t + 1`. It fixes the form
`Q_M = c x² + (d - a) x y - b y²` of `M = (a b; c d)`, hence the discriminant `t² - 4 n`, and it
fixes the first line of each of the four sums of eq. (15). So it changes the weight of `M` only
where one of the second-line inequalities `c < a`, `b < d ≤ 0`, `a ≤ 0` and `d ≤ 0` changes, that is
at the matrices with `a = c`, `b = d`, `d = 0` or `a = 0`. For `n > 0` these are parametrised by the
factorisations `n = u v` into positive integers, and their changes cancel under `(u, v) ↦ (v, u)`;
for `n < 0` all four corrections vanish. This gives `finsum_weight_traceDetFiber_add_two`.

If `t ≤ 0` and `t² - 4 n ≥ 0`, translating upwards decreases `n` until `n ≤ 0`, where every weight
vanishes because every matrix of nonzero weight has positive determinant. If `t > 0`, `n > 0` and
`t² - 4 n ≥ 0`, translating downwards decreases `t` while `t ≤ n` until reaching a fibre with
`0 < n' < t'`, that is, with an eigenvalue in `(0, 1]`. On such a fibre only the sum `T₁`
contributes, and only through the matrices `(1 b; 0 n')` with `0 ≤ b < n'`, which occur exactly
when `t' = n' + 1`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §4, eq. (15).
-/

public section

open Matrix

namespace TauCeti.PopaZagier

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
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ g M.val).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, g M.val = ∑ p ∈ n.toNat.divisorsAntidiagonal, g (φ p) := by
  classical
  set s : Finset (traceDetFiber (Fin 2) t n) :=
    n.toNat.divisorsAntidiagonal.attach.image fun p ↦ ⟨φ p.val, hφ p.val p.property⟩ with hs
  have hsub : (Function.support fun M : traceDetFiber (Fin 2) t n ↦ g M.val) ⊆ s := by
    intro M hM
    obtain ⟨p, hp, hpM⟩ := hsupp M.val M.property hM
    exact Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, Subtype.ext hpM⟩
  refine ⟨s.finite_toSet.subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsub, hs, Finset.sum_image fun p _ q _ h ↦
    Subtype.ext (hinj p.property q.property (congrArg Subtype.val h))]
  exact Finset.sum_attach _ fun p ↦ g (φ p)

/-- The matrices with `a = c` are `(u, t - u - v; u, t - u)` for `n = u v`. -/
private theorem finsum_corr₁ (hn : n ≠ 0) :
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₁ M.val).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₁ M.val = ∑ p ∈ n.toNat.divisorsAntidiagonal,
        chainWeight₃ (2 * p.1 - t) (p.1 + p.2 - t) p.1 := by
  obtain ⟨hfin, hsum⟩ := finsum_eq_sum_divisorsAntidiagonal (t := t) (n := n) corr₁
    (fun p ↦ !![(p.1 : ℤ), t - p.1 - p.2; p.1, t - p.1])
    (fun p hp ↦ mem_traceDetFiber_fin_two.mpr ⟨by simp, by
      obtain ⟨-, -, h⟩ := Int.mem_divisorsAntidiagonal_toNat.mp hp
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
        have hw := le_of_chainWeight₃_ne_zero h
        obtain ⟨hu, hv⟩ : 0 < M 0 0 ∧ 0 < M 1 1 - M 0 1 := by
          have := mul_ne_zero_iff.mp (hdet'.trans_ne hn)
          omega
        refine ⟨_, Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat hu hv hdet',
          Eq.trans ?_ (eta_fin_two M).symm⟩
        simp only [Int.toNat_of_nonneg hu.le, Int.toNat_of_nonneg hv.le,
          EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and]
        omega
      · exact absurd rfl h)
  refine ⟨hfin, hsum.trans (Finset.sum_congr rfl fun p hp ↦ ?_)⟩
  obtain ⟨h1, -, -⟩ := Int.mem_divisorsAntidiagonal_toNat.mp hp
  simp only [corr₁, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one,
    h1.le, true_and, ite_true]
  ring_nf

/-- The matrices with `b = d < 0` are `(t + u, -u; t + u + v, -u)` for `n = u v`. -/
private theorem finsum_corr₂ :
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₂ M.val).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₂ M.val = ∑ p ∈ n.toNat.divisorsAntidiagonal,
        chainWeight₃ p.1 (t + 2 * p.1) (t + p.1 + p.2) := by
  obtain ⟨hfin, hsum⟩ := finsum_eq_sum_divisorsAntidiagonal (t := t) (n := n) corr₂
    (fun p ↦ !![t + p.1, -(p.1 : ℤ); t + p.1 + p.2, -(p.1 : ℤ)])
    (fun p hp ↦ mem_traceDetFiber_fin_two.mpr ⟨by simp, by
      obtain ⟨-, -, h⟩ := Int.mem_divisorsAntidiagonal_toNat.mp hp
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
        have hv : 0 < M 1 0 - M 0 0 := by have := le_of_chainWeight₃_ne_zero h; omega
        refine ⟨_, Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat hu hv hdet',
          Eq.trans ?_ (eta_fin_two M).symm⟩
        simp only [Int.toNat_of_nonneg hu.le, Int.toNat_of_nonneg hv.le,
          EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true]
        omega
      · exact absurd rfl h)
  refine ⟨hfin, hsum.trans (Finset.sum_congr rfl fun p hp ↦ ?_)⟩
  obtain ⟨h1, -, -⟩ := Int.mem_divisorsAntidiagonal_toNat.mp hp
  have : -(p.1 : ℤ) ≤ -1 := by omega
  simp only [corr₂, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, this,
    and_self, ite_true]
  ring_nf

/-- The matrices with `d = 0` are `(t, -v; u, 0)` for `n = u v`. -/
private theorem finsum_corr₃ :
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₃ M.val).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₃ M.val = ∑ p ∈ n.toNat.divisorsAntidiagonal,
        (chainWeight₃ p.2 t p.1 + chainWeight₄ 0 t p.2 p.1) := by
  obtain ⟨hfin, hsum⟩ := finsum_eq_sum_divisorsAntidiagonal (t := t) (n := n) corr₃
    (fun p ↦ !![t, -(p.2 : ℤ); p.1, 0])
    (fun p hp ↦ mem_traceDetFiber_fin_two.mpr ⟨by simp, by
      obtain ⟨-, -, h⟩ := Int.mem_divisorsAntidiagonal_toNat.mp hp
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
        have hu : 0 < M 1 0 := by
          by_cases h₃ : chainWeight₃ (-M 0 1) (M 0 0 - M 1 1) (M 1 0) = 0
          · have := le_of_chainWeight₄_ne_zero (by rwa [h₃, zero_add] at h)
            omega
          · have := le_of_chainWeight₃_ne_zero h₃
            omega
        refine ⟨_, Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat hu hv hdet',
          Eq.trans ?_ (eta_fin_two M).symm⟩
        simp only [Int.toNat_of_nonneg hu.le, Int.toNat_of_nonneg hv.le,
          EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and]
        omega
      · exact absurd rfl h)
  refine ⟨hfin, hsum.trans (Finset.sum_congr rfl fun p hp ↦ ?_)⟩
  obtain ⟨-, h2, -⟩ := Int.mem_divisorsAntidiagonal_toNat.mp hp
  have : -(p.2 : ℤ) < 0 := by omega
  simp only [corr₃, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, this,
    and_self, ite_true, neg_neg, sub_zero]

/-- The matrices with `a = 0` are `(0, -v; u, t)` for `n = u v`. -/
private theorem finsum_corr₄ :
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₄ M.val).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₄ M.val = ∑ p ∈ n.toNat.divisorsAntidiagonal,
        chainWeight₄ 0 (-t) p.1 p.2 := by
  obtain ⟨hfin, hsum⟩ := finsum_eq_sum_divisorsAntidiagonal (t := t) (n := n) corr₄
    (fun p ↦ !![0, -(p.2 : ℤ); p.1, t])
    (fun p hp ↦ mem_traceDetFiber_fin_two.mpr ⟨by simp, by
      obtain ⟨-, -, h⟩ := Int.mem_divisorsAntidiagonal_toNat.mp hp
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one]
      linear_combination h⟩)
    (Set.LeftInvOn.injOn (f₁' := fun M ↦ ((M 1 0).toNat, (-M 0 1).toNat)) fun _ _ ↦ by simp)
    (fun M hM h ↦ by
      obtain ⟨ht, hdet⟩ := mem_traceDetFiber_fin_two.mp hM
      unfold corr₄ at h
      split_ifs at h with hg
      · obtain ⟨ha, hc⟩ := hg
        have hdet' : M 1 0 * -M 0 1 = n := by rw [← hdet, ha]; ring
        have hv : 0 < -M 0 1 := by have := le_of_chainWeight₄_ne_zero h; omega
        refine ⟨_, Int.prodMk_toNat_mem_divisorsAntidiagonal_toNat hc hv hdet',
          Eq.trans ?_ (eta_fin_two M).symm⟩
        simp only [Int.toNat_of_nonneg hc.le, Int.toNat_of_nonneg hv.le,
          EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, true_and]
        omega
      · exact absurd rfl h)
  refine ⟨hfin, hsum.trans (Finset.sum_congr rfl fun p hp ↦ ?_)⟩
  obtain ⟨h1, -, -⟩ := Int.mem_divisorsAntidiagonal_toNat.mp hp
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
      obtain ⟨h1, h2, -⟩ := Int.mem_divisorsAntidiagonal_toNat.mp hp
      exact pairTerm_add_pairTerm _ _ t h1 h2
  rw [Finset.sum_add_distrib, ← hswap] at hsum
  omega

/-- **Translation by the identity.** For `n ≠ 0`, the weights of the matrices of trace `t + 2`
and determinant `n + t + 1` have the same sum as those of trace `t` and determinant `n`.

The translation `M ↦ M + 1` is a bijection between these matrices, it fixes the discriminant
`t² - 4 n`, and its effect on the weights cancels in total. -/
theorem finsum_weight_traceDetFiber_add_two (hn : n ≠ 0) :
    ∑ᶠ M : traceDetFiber (Fin 2) (t + 2) (n + t + 1), weight M.val =
      ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val := by
  obtain ⟨h₁, e₁⟩ := finsum_corr₁ (t := t) hn
  obtain ⟨h₂, e₂⟩ := finsum_corr₂ (t := t) (n := n)
  obtain ⟨h₃, e₃⟩ := finsum_corr₃ (t := t) (n := n)
  obtain ⟨h₄, e₄⟩ := finsum_corr₄ (t := t) (n := n)
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

/-! ### Non-elliptic reduction and base fibres -/

/-- **Nonpositive trace.** If `t ≤ 0` and `t² - 4 n ≥ 0`, then the weights of the matrices of
trace `t` and determinant `n` sum to zero. -/
theorem finsum_weight_traceDetFiber_eq_zero_of_trace_nonpos (ht : t ≤ 0) (hD : 4 * n ≤ t ^ 2) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val = 0 := by
  induction hk : n.toNat using Nat.strong_induction_on generalizing t n with
  | _ k ih =>
  rcases le_or_gt n 0 with hn | hn
  · exact finsum_weight_traceDetFiber_eq_zero_of_det_nonpos hn
  -- translate upwards to the fibre `(t + 2, n + t + 1)`, of smaller determinant
  rw [← finsum_weight_traceDetFiber_add_two hn.ne']
  have ht₂ : t ≤ -2 := by nlinarith
  exact ih _ (by omega) (by omega) (by nlinarith) rfl

/-- **Positive-trace reduction.** At positive trace and determinant with nonnegative discriminant,
the sum of the weights over a fibre equals the sum over a fibre with the same discriminant and
`0 < n' < t'` (an eigenvalue in `(0, 1]`). -/
theorem exists_finsum_weight_traceDetFiber_eq (ht : 0 < t) (hn : 0 < n) (hD : 4 * n ≤ t ^ 2) :
    ∃ t' n' : ℤ, t' ^ 2 - 4 * n' = t ^ 2 - 4 * n ∧ 0 < n' ∧ n' < t' ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val =
        ∑ᶠ M : traceDetFiber (Fin 2) t' n', weight M.val := by
  -- translate downwards while the determinant stays positive
  induction hk : t.toNat using Nat.strong_induction_on generalizing t n with
  | _ k ih =>
    rcases lt_or_ge n t with h | h
    · exact ⟨t, n, rfl, hn, h, rfl⟩
    have hn' : 0 < n - t + 1 := by omega
    -- `t ≤ n` and `4 n ≤ t²` force `4 ≤ t`
    have ht' : 0 < t - 2 := by nlinarith
    have hstep := finsum_weight_traceDetFiber_add_two (t := t - 2) hn'.ne'
    rw [show t - 2 + 2 = t by ring, show n - t + 1 + (t - 2) + 1 = n by ring] at hstep
    obtain ⟨t', n', hD', hn'', h', e⟩ :=
      ih _ (by omega) ht' hn' (by nlinarith) rfl
    exact ⟨t', n', by linear_combination hD', hn'', h', hstep.trans e⟩

/-- At nonnegative discriminant, no matrix has nonzero weight in `T₃` or `T₄`: their first lines
force a negative discriminant `(a - d)² + 4 b c`. -/
private theorem weight₃_eq_zero_and_weight₄_eq_zero {a b c d : ℤ}
    (hD : 0 ≤ (a - d) ^ 2 + 4 * b * c) : weight₃ a b c d = 0 ∧ weight₄ a b c d = 0 := by
  constructor
  · unfold weight₃
    split_ifs with h
    · by_contra hw
      obtain ⟨h₁, h₂, h₃⟩ := le_of_chainWeight₄_ne_zero hw
      nlinarith [mul_nonneg h₁ (by omega : (0 : ℤ) ≤ c - (a - d)),
        mul_nonneg h.2.le (by omega : (0 : ℤ) ≤ c - (a - d)),
        mul_nonneg h.2.le (by omega : (0 : ℤ) ≤ -b - c), sq_pos_of_pos h.2]
    · rfl
  · unfold weight₄
    split_ifs with h
    · by_contra hw
      obtain ⟨h₁, h₂, h₃⟩ := le_of_chainWeight₄_ne_zero hw
      nlinarith [sq_pos_of_pos h.2]
    · rfl

/-- If `n < t`, no matrix of trace `t` and determinant `n` has nonzero weight in `T₂`. -/
private theorem weight₂_eq_zero {a b c d : ℤ} (h : a * d - b * c < a + d) :
    weight₂ a b c d = 0 := by
  unfold weight₂
  split_ifs with hbd
  · by_contra hw
    obtain ⟨h₁, h₂⟩ := le_of_chainWeight₃_ne_zero hw
    -- `-b c ≥ (1 - d) c ≥ (1 - d) (a - d)` forces `n - t + 1 ≥ (d - 1)² > 0`
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -b - (1 - d)) (by omega : (0 : ℤ) ≤ c),
      mul_nonneg (by omega : (0 : ℤ) ≤ 1 - d) (by omega : (0 : ℤ) ≤ c - (a - d))]
  · rfl

/-- If `n < t`, a matrix of trace `t` and determinant `n` with nonzero weight in `T₁` is
`(1 b; 0 n)`, and then `t = n + 1`. -/
private theorem eq_of_weight₁_ne_zero {a b c d : ℤ}
    (h : a * d - b * c < a + d) (hw : weight₁ a b c d ≠ 0) :
    c = 0 ∧ a = 1 ∧ d = a * d - b * c ∧ a + d = a * d - b * c + 1 := by
  unfold weight₁ at hw
  split_ifs at hw with hca
  · obtain ⟨h₁, h₂⟩ := le_of_chainWeight₃_ne_zero hw
    obtain ⟨hc, hca⟩ := hca
    rcases hc.lt_or_eq with hc | rfl
    · -- `c > 0` is impossible
      exfalso
      rcases le_or_gt 0 b with hb | hb
      · -- here `n ≥ a² - a + d`, so `(a - 1)² ≤ 0` with `a ≥ 2`
        nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ d - a - b) hc.le,
          mul_nonneg (by omega : (0 : ℤ) ≤ d - a) (by omega : (0 : ℤ) ≤ a - 1 - c)]
      · -- here `-b c = (a - 1) (1 - d) + (n - t + 1) > 0` forces `d ≤ 0`, so `a ≤ c`
        have hd : d ≤ 0 := by
          by_contra! hd
          nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ a - 1) (by omega : (0 : ℤ) ≤ d - 1),
            mul_pos (by omega : (0 : ℤ) < -b) hc]
        omega
    · -- `c = 0`: the diagonal entries are positive with `(a - 1) (d - 1) = n - t + 1 ≤ 0`
      simp only [mul_zero, sub_zero] at h
      have h0 : (a - 1) * (d - 1) = 0 := by
        nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ a - 1) (by omega : (0 : ℤ) ≤ d - 1)]
      obtain rfl : a = 1 := by rcases mul_eq_zero.mp h0 with h0 | h0 <;> omega
      exact ⟨rfl, rfl, by ring, by ring⟩
  · exact absurd rfl hw

/-- If `n < t`, the matrices of trace `t` and determinant `n` of nonzero weight are the
matrices `(1 b; 0 n)`, and they only occur if `t = n + 1`. -/
private theorem eq_of_weight_ne_zero (ht : n < t)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M ∈ traceDetFiber (Fin 2) t n) (hw : weight M ≠ 0) :
    t = n + 1 ∧ M = !![1, M 0 1; 0, n] := by
  have hn : 0 < n := by
    have := det_pos_of_weight_ne_zero hw
    rwa [(mem_traceDetFiber.mp hM).2] at this
  obtain ⟨htr, hdet⟩ := mem_traceDetFiber_fin_two.mp hM
  have hD : 0 ≤ (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 := by
    have : (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0 = t ^ 2 - 4 * n := by
      rw [← htr, ← hdet]
      ring
    nlinarith [sq_nonneg (n - 1)]
  obtain ⟨h₃, h₄⟩ := weight₃_eq_zero_and_weight₄_eq_zero hD
  have h' : M 0 0 * M 1 1 - M 0 1 * M 1 0 < M 0 0 + M 1 1 := by rw [hdet, htr]; exact ht
  unfold weight at hw
  rw [weight₂_eq_zero h', h₃, h₄, sub_zero, sub_zero, sub_zero] at hw
  obtain ⟨hc, ha, hd, ht'⟩ := eq_of_weight₁_ne_zero h' hw
  rw [hdet] at hd ht'
  refine ⟨htr ▸ ht', ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hc, hd]

/-- **Fibres with `0 < n < t`.** For `0 < n < t`, the weights of the matrices of trace `t` and
determinant `n` sum to `2` if `(t, n) = (2, 1)`, to `12 (n - 1)` if `t = n + 1` with `n > 1`, and
to `0` otherwise. -/
theorem finsum_weight_traceDetFiber_of_det_lt_trace (hn : 0 < n) (ht : n < t) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val =
      if t = n + 1 then (if n = 1 then 2 else 12 * (n - 1)) else 0 := by
  classical
  by_cases htn : t = n + 1
  · rw [ite_eq_left htn]
    subst htn
    let φ (b : ℤ) : traceDetFiber (Fin 2) (n + 1) n :=
      ⟨!![1, b; 0, n], mem_traceDetFiber_fin_two.mpr ⟨by simp [add_comm], by simp⟩⟩
    have hφ : Function.Injective φ := fun b b' hb ↦ by
      simpa [φ] using congrFun (congrFun (congrArg Subtype.val hb) 0) 1
    have hsub : (Function.support fun M : traceDetFiber (Fin 2) (n + 1) n ↦ weight M.val) ⊆
        (Finset.Ico 0 n).image φ := by
      intro M hM
      obtain ⟨-, hM'⟩ := eq_of_weight_ne_zero ht M.property hM
      have hw : weight !![1, M.val 0 1; 0, n] ≠ 0 := hM' ▸ hM
      rw [weight_upperTriangular 1 (M.val 0 1) n one_pos] at hw
      have hb : 0 ≤ M.val 0 1 ∧ M.val 0 1 < n := by split_ifs at hw <;> omega
      exact Finset.mem_image.mpr ⟨M.val 0 1, Finset.mem_Ico.mpr hb, Subtype.ext hM'.symm⟩
    rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_image fun b _ b' _ hb ↦ hφ hb]
    simp only [φ, sum_Ico_weight_upperTriangular 1 n one_pos]
    split_ifs <;> omega
  · rw [ite_eq_right htn]
    refine finsum_eq_zero_of_forall_eq_zero fun M ↦ ?_
    by_contra hw
    exact htn (eq_of_weight_ne_zero ht M.property hw).1

end TauCeti.PopaZagier
