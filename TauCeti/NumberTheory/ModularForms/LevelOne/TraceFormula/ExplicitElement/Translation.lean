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
Popa and Zagier's explicit Hecke element, their eq. (15). For `n > 0`, translation by the identity
matrix `M ↦ M + 1` preserves the sum of `weight M` over the trace–determinant fibre `(t, n)`:

`∑_{tr M = t + 2, det M = n + t + 1} weight M = ∑_{tr M = t, det M = n} weight M`.

This module proves the translation identity and its two non-elliptic consequences: vanishing for
nonpositive trace and reduction of positive-trace fibres to the range `n' + 1 ≤ t'`.

## Main results

* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_add_two`: for `n > 0`, the weights of the
  matrices of trace `t + 2` and determinant `n + t + 1` have the same sum as those of trace `t`
  and determinant `n`.
* `TauCeti.PopaZagier.finsum_weight_traceDetFiber_eq_zero_of_trace_nonpos`: the weights of the
  matrices of trace `t ≤ 0` and determinant `n` sum to zero when `t² - 4 n ≥ 0`.
* `TauCeti.PopaZagier.exists_finsum_weight_traceDetFiber_eq`: for `t > 0`, `n > 0`, and
  `t² - 4 n ≥ 0`, the fibre sum equals that of a fibre `(t', n')` of the same discriminant with
  `0 < n'` and `n' + 1 ≤ t'`.

## Proof

The translation `M ↦ M + 1` maps the matrices of trace `t` and determinant `n` bijectively to
those of trace `t + 2` and determinant `n + t + 1`. It fixes the form
`Q_M = c x² + (d - a) x y - b y²` of `M = (a b; c d)`, hence the discriminant `t² - 4 n`, and it
fixes the first line of each of the four sums of eq. (15). So it changes the weight of `M` only
where one of the second-line inequalities `c < a`, `b < d ≤ 0`, `a ≤ 0` and `d ≤ 0` changes, that is
at the matrices with `a = c`, `b = d`, `d = 0` or `a = 0`. For `n > 0` these are parametrised by the
factorisations `n = u v` into positive integers, and their changes cancel under `(u, v) ↦ (v, u)`.
This gives `finsum_weight_traceDetFiber_add_two`.

If `t ≤ 0` and `t² - 4 n ≥ 0`, translating upwards decreases `n` until `n ≤ 0`, where every weight
vanishes because every matrix of nonzero weight has positive determinant. If `t > 0`, `n > 0` and
`t² - 4 n ≥ 0`, translating downwards decreases `t` while `t < n + 1` until reaching a fibre with
`0 < n'` and `n' + 1 ≤ t'`.

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
private theorem finsum_corr₁ (hn : 0 < n) :
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₁ M.val).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₁ M.val = ∑ p ∈ n.toNat.divisorsAntidiagonal,
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
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₂ M.val).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₂ M.val = ∑ p ∈ n.toNat.divisorsAntidiagonal,
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
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₃ M.val).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₃ M.val = ∑ p ∈ n.toNat.divisorsAntidiagonal,
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
    (Function.support fun M : traceDetFiber (Fin 2) t n ↦ corr₄ M.val).Finite ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, corr₄ M.val = ∑ p ∈ n.toNat.divisorsAntidiagonal,
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
    ∑ᶠ M : traceDetFiber (Fin 2) (t + 2) (n + t + 1), weight M.val =
      ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val := by
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

/-- **Nonpositive trace.** If `t ≤ 0` and `t² - 4 n ≥ 0`, then the weights of the matrices of
trace `t` and determinant `n` sum to zero. -/
theorem finsum_weight_traceDetFiber_eq_zero_of_trace_nonpos (ht : t ≤ 0) (hD : 4 * n ≤ t ^ 2) :
    ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val = 0 := by
  induction hk : n.toNat using Nat.strong_induction_on generalizing t n with
  | _ k ih =>
  rcases le_or_gt n 0 with hn | hn
  · exact finsum_weight_traceDetFiber_eq_zero_of_det_nonpos hn
  -- translate upwards to the fibre `(t + 2, n + t + 1)`, of smaller determinant
  rw [← finsum_weight_traceDetFiber_add_two hn]
  have ht₂ : t ≤ -2 := by nlinarith
  exact ih _ (by omega) (by omega) (by nlinarith) rfl

/-- **Positive-trace reduction.** At positive trace and determinant with nonnegative discriminant,
the sum of the weights over a fibre equals the sum over a fibre with the same discriminant and an
eigenvalue in `(0, 1]`. -/
theorem exists_finsum_weight_traceDetFiber_eq (ht : 0 < t) (hn : 0 < n) (hD : 4 * n ≤ t ^ 2) :
    ∃ t' n' : ℤ, t' ^ 2 - 4 * n' = t ^ 2 - 4 * n ∧ 0 < n' ∧ n' + 1 ≤ t' ∧
      ∑ᶠ M : traceDetFiber (Fin 2) t n, weight M.val =
        ∑ᶠ M : traceDetFiber (Fin 2) t' n', weight M.val := by
  -- translate downwards while the determinant stays positive
  induction hk : t.toNat using Nat.strong_induction_on generalizing t n with
  | _ k ih =>
    rcases le_or_gt (n + 1) t with h | h
    · exact ⟨t, n, rfl, hn, h, rfl⟩
    have hn' : 0 < n - t + 1 := by omega
    -- `t ≤ n` and `4 n ≤ t²` force `4 ≤ t`
    have ht' : 0 < t - 2 := by nlinarith
    have hstep := finsum_weight_traceDetFiber_add_two (t := t - 2) hn'
    rw [show t - 2 + 2 = t by ring, show n - t + 1 + (t - 2) + 1 = n by ring] at hstep
    obtain ⟨t', n', hD', hn'', h', e⟩ :=
      ih _ (by omega) ht' hn' (by nlinarith) rfl
    exact ⟨t', n', by linear_combination hD', hn'', h', hstep.trans e⟩

end TauCeti.PopaZagier
