/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.LeftSlice

/-!
# Slice Markov rules and block multiplicativity for countable atomic models

Exhaustion by finite alphabets lifts `tailIncl` scaling
(`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_tailIncl`) and separated-block multiplicativity
(`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_castAdd_mul_natAdd`) to countable atomic models.
When the weights sum to `1` and either the left slice
`(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑' (a < b), p a` or the right slice
`(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑' (c > b), p c` equals `q * z` for every
letter `b`, `countableAtomicTrace` satisfies the corresponding Markov rule and agrees with the
Ocneanu trace on every finite stage
(`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_eq_ocneanuTrace_of_leftSlice`,
`TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_eq_ocneanuTrace_of_rightSlice`).

## Main results

* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_tailIncl`: scaling under adding a first strand.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_castAdd_mul_natAdd`: separated-block
  multiplicativity.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_T_zero_mul_tailIncl` and
  `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_eq_ocneanuTrace_of_leftSlice`: countable
  first-site Markov rule and Ocneanu identification.
* `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_strandIncl_mul_T_last` and
  `TauCeti.TypeAHeckeAlgebra.countableAtomicTrace_eq_ocneanuTrace_of_rightSlice`: countable
  last-site Markov rule and Ocneanu identification.
-/

public section

open Filter Finsupp
open scoped Topology

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [NormedCommRing R] [CompleteSpace R] {ι : Type*} [LinearOrder ι]
  (pos : ι → Prop) [DecidablePred pos] (q : Rˣ)

/-- Adding an uncrossed first strand multiplies `countableAtomicTrace` by `∑' a, p a`. -/
@[simp]
theorem countableAtomicTrace_tailIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖) {n : ℕ}
    (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (n + 1) (tailIncl q n x) =
      countableAtomicTrace pos q p hp n x * ∑' a, p a :=
  tendsto_nhds_unique (tendsto_atomicTrace_finset pos q p hp (n + 1) (tailIncl q n x)) <|
    ((tendsto_atomicTrace_finset pos q p hp n x).mul hp.of_norm.hasSum).congr fun s ↦ by
      rw [← Finset.sum_attach s p, ← Finset.univ_eq_attach, ← atomicTrace_tailIncl]

/-- **Block multiplicativity of `countableAtomicTrace`** on disjoint consecutive strand blocks. -/
theorem countableAtomicTrace_castAdd_mul_natAdd (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {m n : ℕ} (x : TypeAHeckeAlgebra R q m) (y : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp (m + n) (castAdd R q m n x * natAdd R q m n y) =
      countableAtomicTrace pos q p hp m x * countableAtomicTrace pos q p hp n y :=
  tendsto_nhds_unique
    (tendsto_atomicTrace_finset pos q p hp (m + n) (castAdd R q m n x * natAdd R q m n y)) <|
    ((tendsto_atomicTrace_finset pos q p hp m x).mul
      (tendsto_atomicTrace_finset pos q p hp n y)).congr fun s ↦
        (atomicTrace_castAdd_mul_natAdd (fun a : s ↦ pos a) q (fun a : s ↦ p a) x y).symm

private theorem countableAtomicTrace_eq_mul_of_slice (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R} {n : ℕ} {x : TypeAHeckeAlgebra R q (n + 1)} {y : TypeAHeckeAlgebra R q (n + 2)}
    (e : (Fin (n + 1) → ι) × ι ≃ (Fin (n + 2) → ι)) (b : (Fin (n + 1) → ι) → ι)
    (P : ι → ι → Prop) [∀ u, DecidablePred (P u)] (hP : ∀ u, ¬ P u u)
    (hprod : ∀ w a, ∏ i, p (e (w, a) i) = p a * ∏ i, p (w i))
    (hdiag : ∀ w a, signedChecked pos q y (single (e (w, a)) 1) (e (w, a)) =
      ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
        (if a = b w then (if pos (b w) then (q : R) ^ 2 else -1)
          else if P (b w) a then (q : R) ^ 2 - 1 else 0))
    (hz : ∀ u, (if pos u then (q : R) ^ 2 else -1) * p u +
      ((q : R) ^ 2 - 1) * (∑' a, if P u a then p a else 0) = q * z) :
    countableAtomicTrace pos q p hp (n + 2) y = z * countableAtomicTrace pos q p hp (n + 1) x := by
  classical
  rw [countableAtomicTrace_apply,
    (e.tsum_eq _).symm.trans (Summable.tsum_prod (e.summable_iff.mpr
      (summable_norm_signedChecked_mul_prod pos q hp (n + 2) y).of_norm)),
    countableAtomicTrace_apply,
    ← (summable_norm_signedChecked_mul_prod pos q hp (n + 1) x).of_norm.tsum_mul_left]
  congr 1 with w
  set u := b w
  have h₁ : Summable fun a ↦ if a = u then (if pos u then (q : R) ^ 2 else -1) * p u else 0 :=
    summable_of_ne_finset_zero (s := {u}) fun _ ha ↦ by simp [Finset.notMem_singleton.mp ha]
  have h_ite : Summable fun a ↦ ‖if P u a then p a else 0‖ :=
    hp.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun _ ↦ by split_ifs <;> simp
  have h₂ := h_ite.of_norm.mul_left ((q : R) ^ 2 - 1)
  have hdecomp (a : ι) :
      signedChecked pos q y (single (e (w, a)) 1) (e (w, a)) * ∏ i, p (e (w, a) i) =
        (((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) *
          ((if a = u then (if pos u then (q : R) ^ 2 else -1) * p u else 0) +
            ((q : R) ^ 2 - 1) * (if P u a then p a else 0)) := by
    rw [hdiag w a, hprod w a]
    split_ifs <;> simp_all [u] <;> ring
  rw [funext hdecomp, (h₁.add h₂).tsum_mul_left, h₁.tsum_add h₂, tsum_ite_eq,
    h_ite.of_norm.tsum_mul_left, hz u]
  linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * Units.inv_mul q

/-- **Countable first-site (left-slice) Markov rule** for `countableAtomicTrace`. -/
theorem countableAtomicTrace_T_zero_mul_tailIncl (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' a, if a < b then p a else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q (n + 1)) :
    countableAtomicTrace pos q p hp (n + 2) (T q (0 : Fin (n + 1)) * tailIncl q (n + 1) x) =
      z * countableAtomicTrace pos q p hp (n + 1) x := by
  rw [countableAtomicTrace_mul_comm]
  exact countableAtomicTrace_eq_mul_of_slice pos q p hp
    ((Equiv.prodComm (Fin (n + 1) → ι) ι).trans (Fin.consEquiv fun _ : Fin (n + 2) ↦ ι))
    (· 0) (fun u a ↦ a < u) lt_irrefl
    (fun w a ↦ by simp [Fin.prod_univ_succ (n := n + 1)])
    (fun w a ↦ signedChecked_tailIncl_mul_T_zero_single_cons_apply pos q x a w) hz

/-- **Countable atomic trace with scalar left slice is the Ocneanu trace.** -/
theorem countableAtomicTrace_eq_ocneanuTrace_of_leftSlice (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) {z : R} (hp1 : ∑' a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' a, if a < b then p a else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace z).eq_toInfinite_of_T_zero_mul_tailIncl
    (countableAtomicTrace pos q p hp) (by simp [hp1])
    (fun _ ↦ countableAtomicTrace_mul_comm pos q p hp)
    (fun _ _ ↦ countableAtomicTrace_castAdd_mul_natAdd pos q p hp)
    (fun _ ↦ countableAtomicTrace_T_zero_mul_tailIncl pos q p hp hz) n x

/-- **Countable last-site (right-slice) Markov rule** for `countableAtomicTrace`. -/
theorem countableAtomicTrace_strandIncl_mul_T_last (p : ι → R) (hp : Summable fun a ↦ ‖p a‖)
    {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' c, if b < c then p c else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q (n + 1)) :
    countableAtomicTrace pos q p hp (n + 2)
        (strandIncl R q (n + 1) x * T q (Fin.last n)) =
      z * countableAtomicTrace pos q p hp (n + 1) x := by
  refine countableAtomicTrace_eq_mul_of_slice pos q p hp
    ((Equiv.prodComm (Fin (n + 1) → ι) ι).trans (Fin.snocEquiv fun _ : Fin (n + 2) ↦ ι))
    (· (Fin.last n)) (· < ·) lt_irrefl
    (fun w c ↦ by simp [Fin.prod_univ_castSucc (n := n + 1), mul_comm]) (fun w c ↦ ?_) hz
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Fin.snocEquiv_apply,
    signedChecked_strandIncl_mul_T_last_single_snoc_apply]
  congr 1
  by_cases h : c = w (Fin.last n) <;> simp [h, eq_comm]

/-- **Countable atomic trace with scalar right slice is the Ocneanu trace.** -/
theorem countableAtomicTrace_eq_ocneanuTrace_of_rightSlice (p : ι → R)
    (hp : Summable fun a ↦ ‖p a‖) {z : R} (hp1 : ∑' a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * (∑' c, if b < c then p c else 0) = q * z)
    {n : ℕ} (x : TypeAHeckeAlgebra R q n) :
    countableAtomicTrace pos q p hp n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  eq_ocneanuTrace_toInfinite (countableAtomicTrace pos q p hp) (by simp)
    (fun _ _ ↦ by rw [countableAtomicTrace_strandIncl, hp1, mul_one])
    (fun _ ↦ countableAtomicTrace_mul_comm pos q p hp)
    (fun _ ↦ countableAtomicTrace_strandIncl_mul_T_last pos q p hp hz) n x

end TauCeti.TypeAHeckeAlgebra
