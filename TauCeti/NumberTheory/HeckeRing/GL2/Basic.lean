/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.NumberTheory.HeckeRing.GLn.CoprimeMul
public import TauCeti.NumberTheory.HeckeRing.GLn.ScalarMul

import Mathlib.Data.Finset.NatDivisors

/-!
# The `GL₂` Hecke operators `T(a, d)` and `T(m)`

The specialization of the `GL_n` Hecke ring to `n = 2`: the basis operators `T(a, d)` for
divisor pairs `a ∣ d`, the scalar operators `T(c, c)`, and Shimura's summed operator
`T(m) = ∑_{a ∣ m} T(a, m / a)`.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GL2/Basic.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main definitions

* `HeckeRing.GL2.heckeTDiag`: `T(a, d)`, zero unless `0 < a`, `0 < d`, `a ∣ d`.
* `HeckeRing.GL2.heckeTScalar`: the scalar operator `T(c, c)`.
* `HeckeRing.GL2.heckeT`: Shimura's `T(m) = ∑_{a ∣ m} T(a, m / a)`.

## Main results

* `HeckeRing.GL2.heckeTDiag_one_one`: `T(1, 1) = 1`.
* `HeckeRing.GL2.heckeT_one`: `T(1) = 1`.
* `HeckeRing.GL2.heckeT_prime`: `T(p) = T(1, p)` for prime `p`.
* `HeckeRing.GL2.heckeTDiag_mul_of_coprime`: `T(a,da) · T(b,db) = T(ab, da·db)` for
  coprime determinants.
* `HeckeRing.GL2.heckeT_mul_coprime`: `T(m) · T(n) = T(mn)` for coprime `m`, `n`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Theorem 3.24.
-/

public section

open Matrix HeckeRing DoubleCoset Finset HeckeRing.GLn

namespace HeckeRing.GL2

/-- `T(a, d)`: the diagonal Hecke basis element of the pair `(a, d)`, zero unless
`0 < a`, `0 < d` and `a ∣ d`. -/
noncomputable def heckeTDiag (a d : ℕ) : IntegralHeckeRing 2 :=
  if 0 < a ∧ 0 < d ∧ a ∣ d then diagElem ![a, d] else 0

/-- Defining equation for the sealed `heckeTDiag`. -/
lemma heckeTDiag_def (a d : ℕ) :
    heckeTDiag a d = if 0 < a ∧ 0 < d ∧ a ∣ d then diagElem ![a, d] else 0 := (rfl)

/-- `T(a, d)` is the diagonal Hecke element when the divisor-pair conditions hold. -/
lemma heckeTDiag_of_pos {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (h : a ∣ d) :
    heckeTDiag a d = diagElem ![a, d] :=
  if_pos ⟨ha, hd, h⟩

/-- `T(a, d)` is zero when the divisor-pair conditions fail. -/
lemma heckeTDiag_eq_zero {a d : ℕ} (h : ¬(0 < a ∧ 0 < d ∧ a ∣ d)) : heckeTDiag a d = 0 :=
  if_neg h

/-- `T(c, c)`: the scalar Hecke operator. -/
noncomputable def heckeTScalar (c : ℕ) : IntegralHeckeRing 2 :=
  heckeTDiag c c

/-- The defining equation of `heckeTScalar`. -/
lemma heckeTScalar_def (c : ℕ) : heckeTScalar c = heckeTDiag c c := (rfl)

/-- The scalar operator of a positive `c` is the constant diagonal element. -/
lemma heckeTScalar_of_pos {c : ℕ} (hc : 0 < c) :
    heckeTScalar c = diagElem (fun _ : Fin 2 ↦ c) := by
  rw [heckeTScalar, heckeTDiag_of_pos hc hc dvd_rfl]
  exact congrArg diagElem (funext fun i ↦ by fin_cases i <;> rfl)

/-- `T(1, 1)` is the identity. -/
@[simp] lemma heckeTDiag_one_one : heckeTDiag 1 1 = 1 := by
  rw [heckeTDiag_of_pos one_pos one_pos dvd_rfl,
    show ![1, 1] = (fun _ : Fin 2 ↦ 1) from funext fun i ↦ by fin_cases i <;> rfl]
  exact diagElem_one

/-- Shimura's summed Hecke operator: `T(m) = ∑_{a ∣ m} T(a, m / a)`. -/
noncomputable def heckeT (m : ℕ+) : IntegralHeckeRing 2 :=
  ∑ a ∈ (m : ℕ).divisors, heckeTDiag a ((m : ℕ) / a)

/-- The defining equation of `heckeT`. -/
lemma heckeT_def (m : ℕ+) :
    heckeT m = ∑ a ∈ (m : ℕ).divisors, heckeTDiag a ((m : ℕ) / a) := (rfl)

/-- `T(1) = 1`: the only divisor pair of `1` is `(1,1)`. -/
@[simp] lemma heckeT_one : heckeT 1 = 1 := by
  rw [heckeT_def]
  simp only [PNat.one_coe, Nat.divisors_one, Finset.sum_singleton, Nat.div_self one_pos]
  exact heckeTDiag_one_one

/-- For a prime `p`, the summed operator collapses: `T(p) = T(1, p)`. -/
lemma heckeT_prime (p : ℕ) (hp : p.Prime) : heckeT ⟨p, hp.pos⟩ = heckeTDiag 1 p := by
  -- `heckeT` is sealed (`public section`, no `@[expose]`), so `rw`/`simp` cannot unfold it;
  -- `change` states the defeq divisor-pair sum directly
  change ∑ a ∈ p.divisors, heckeTDiag a (p / a) = _
  rw [hp.sum_divisors, Nat.div_self hp.pos, Nat.div_one,
    heckeTDiag_eq_zero (fun ⟨_, _, hdvd⟩ ↦ hp.ne_one (Nat.dvd_one.mp hdvd)), zero_add]

section Structural

variable (p : ℕ)

/-- Powers of the scalar operator: `T(p,p) ^ i = T(pⁱ,...,pⁱ)`. -/
lemma heckeTScalar_pow (hp : 0 < p) (i : ℕ) :
    heckeTScalar p ^ i = diagElem (fun _ : Fin 2 ↦ p ^ i) := by
  induction i with
  | zero =>
    rw [pow_zero]
    exact ((congrArg diagElem (funext fun _ ↦ by simp)).trans diagElem_one).symm
  | succ i ih =>
    rw [pow_succ', ih, heckeTScalar_of_pos hp,
      diagElem_const_mul 2 p hp (fun _ ↦ p ^ i) (fun _ ↦ pow_pos hp i)]
    exact congrArg diagElem (funext fun _ ↦ by simp [Pi.mul_apply, pow_succ, mul_comm])

/-- Expansion of `T(pᵏ)`: only the divisor pairs `(pⁱ, p^(k-i))` with `i ≤ k - i`
contribute. -/
lemma heckeT_ppow_expansion (hp : p.Prime) (k : ℕ) :
    heckeT ⟨p ^ k, pow_pos hp.pos k⟩ =
      ∑ i ∈ Finset.range (k / 2 + 1), heckeTDiag (p ^ i) (p ^ (k - i)) := by
  -- `heckeT` is sealed (`public section`, no `@[expose]`), so `rw`/`simp` cannot unfold it;
  -- `change` states the defeq divisor-pair sum directly
  change ∑ a ∈ (p ^ k).divisors, heckeTDiag a (p ^ k / a) = _
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_congr rfl
    (g := fun j ↦ heckeTDiag (p ^ j) (p ^ (k - j))) fun j hj ↦ by
      rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos]]
  refine (Finset.sum_subset (Finset.range_mono (by omega)) fun j hj hnj ↦ ?_).symm
  simp only [Finset.mem_range] at hj hnj
  exact heckeTDiag_eq_zero fun ⟨_, _, hdvd⟩ ↦ absurd (Nat.le_of_dvd (pow_pos hp.pos _) hdvd)
    (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (by omega)))

/-- **Coprime multiplicativity** (Shimura, Proposition 3.16 in the `GL₂` notation):
`T(a, da) · T(b, db) = T(ab, da·db)` when the determinants `a·da` and `b·db` are coprime. -/
lemma heckeTDiag_mul_of_coprime (a b da db : ℕ) (hda : 0 < da)
    (hdb : 0 < db) (hdva : a ∣ da) (hdvb : b ∣ db)
    (hcop : Nat.Coprime (a * da) (b * db)) :
    heckeTDiag a da * heckeTDiag b db = heckeTDiag (a * b) (da * db) := by
  -- positivity of the left entries is forced: a divisor of a positive number is positive
  have ha : 0 < a := Nat.pos_of_dvd_of_pos hdva hda
  have hb : 0 < b := Nat.pos_of_dvd_of_pos hdvb hdb
  rw [heckeTDiag_of_pos ha hda hdva, heckeTDiag_of_pos hb hdb hdvb,
    heckeTDiag_of_pos (Nat.mul_pos ha hb) (Nat.mul_pos hda hdb) (Nat.mul_dvd_mul hdva hdvb)]
  have hprod : diagElem ((![a, da] : Fin 2 → ℕ) * ![b, db]) =
      diagElem (![a * b, da * db] : Fin 2 → ℕ) :=
    congrArg diagElem (funext fun i ↦ by fin_cases i <;> simp [Pi.mul_apply])
  rw [← hprod]
  exact diagElem_mul_of_coprime 2 ![a, da] ![b, db]
    (fun i ↦ by fin_cases i <;> simp [ha, hda])
    (fun i ↦ by fin_cases i <;> simp [hb, hdb])
    (by simpa [Fin.prod_univ_two] using hcop)

open scoped Pointwise in
/-- **Shimura, Theorem 3.24(3a)** — coprime multiplicativity: `T(m) · T(n) = T(mn)` when
`m` and `n` are coprime. -/
theorem heckeT_mul_coprime (m n : ℕ+) (hcop : Nat.Coprime (m : ℕ) (n : ℕ)) :
    heckeT m * heckeT n = heckeT (m * n) := by
  simp only [heckeT_def, PNat.mul_coe]
  -- `Finset` pointwise multiplication is by definition the image of the product set,
  -- so the divisor-set product can be reindexed as a sum over pairs
  rw [Finset.sum_mul_sum, Nat.divisors_mul,
    show ((m : ℕ).divisors * (n : ℕ).divisors) =
      ((m : ℕ).divisors ×ˢ (n : ℕ).divisors).image (fun q ↦ q.1 * q.2) from rfl,
    Finset.sum_image hcop.mul_injOn_divisors, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  obtain ⟨a, b⟩ := q
  simp only [Finset.mem_product, Nat.mem_divisors] at hq
  have ha_pos : 0 < a := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hq
  have hb_pos : 0 < b := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hq
  rw [(Nat.div_mul_div_comm hq.1.1 hq.2.1).symm]
  by_cases hca : a ∣ (m : ℕ) / a
  · by_cases hcb : b ∣ (n : ℕ) / b
    · refine heckeTDiag_mul_of_coprime a b _ _
        (Nat.div_pos (Nat.le_of_dvd (by omega) hq.1.1) ha_pos)
        (Nat.div_pos (Nat.le_of_dvd (by omega) hq.2.1) hb_pos) hca hcb ?_
      rwa [Nat.mul_div_cancel' hq.1.1, Nat.mul_div_cancel' hq.2.1]
    · rw [show heckeTDiag b ((n : ℕ) / b) = 0 from
        heckeTDiag_eq_zero (by push Not; intro _ _; exact hcb), mul_zero]
      symm
      refine heckeTDiag_eq_zero ?_
      push Not
      intro _ _ hdvd
      exact absurd (((hcop.symm.coprime_dvd_left hq.2.1).coprime_dvd_right
        (Nat.div_dvd_of_dvd hq.1.1)).dvd_of_dvd_mul_left
        (dvd_trans (dvd_mul_left b a) hdvd)) hcb
  · rw [show heckeTDiag a ((m : ℕ) / a) = 0 from
      heckeTDiag_eq_zero (by push Not; intro _ _; exact hca), zero_mul]
    symm
    refine heckeTDiag_eq_zero ?_
    push Not
    intro _ _ hdvd
    exact absurd (((hcop.coprime_dvd_left hq.1.1).coprime_dvd_right
      (Nat.div_dvd_of_dvd hq.2.1)).dvd_of_dvd_mul_right
      (dvd_trans (dvd_mul_right a b) hdvd)) hca

end Structural

end HeckeRing.GL2
