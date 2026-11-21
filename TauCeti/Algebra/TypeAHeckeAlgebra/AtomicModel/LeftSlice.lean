/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Block
public import TauCeti.Algebra.TypeAHeckeAlgebra.Tail
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination

/-!
# First-site Markov rules and left-slice geometric atomic models

For an atomic model `TauCeti.TypeAHeckeAlgebra.atomicTrace pos q p n` on an ordered alphabet `ι`,
the shifted-tail inclusion `TauCeti.TypeAHeckeAlgebra.tailIncl` fixes the prepended first letter and
acts on the remaining strands (`TauCeti.TypeAHeckeAlgebra.signedChecked_tailIncl_mapDomain_cons`).
Consequently `atomicTrace` scales by `∑ a, p a` under `tailIncl`
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_tailIncl`), and multiplying by `T 0` tests the *left slice*
`(if pos b then q ^ 2 else -1) * p b + (q ^ 2 - 1) * ∑ (a < b), p a`.

When the weights sum to `1` and every left slice equals `q * z`, `atomicTrace` satisfies the
first-site Markov rule (`TauCeti.TypeAHeckeAlgebra.atomicTrace_T_zero_mul_tailIncl`) and
restricts `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z`
(`TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_ocneanuTrace_of_leftSlice`). Decreasing positive
geometric weights (`TauCeti.TypeAHeckeAlgebra.atomicTrace_geometric_leftSlice_eq`) and increasing
negative geometric weights (`TauCeti.TypeAHeckeAlgebra.atomicTrace_negGeometric_eq`) realize both
halves `a_(±(r + 1))(Q)` of Wenzl's discrete series.

## Main results

* `TauCeti.TypeAHeckeAlgebra.signedChecked_tailIncl_mapDomain_cons`,
  `TauCeti.TypeAHeckeAlgebra.signedChecked_tailIncl_single_cons_apply_cons`, and
  `TauCeti.TypeAHeckeAlgebra.signedChecked_tailIncl_mul_T_zero_single_cons_apply`: action and
  first-crossing diagonal entries of `tailIncl`.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_tailIncl` and
  `TauCeti.TypeAHeckeAlgebra.atomicTrace_T_zero_mul_tailIncl`: first-site scaling and Markov rule.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_eq_ocneanuTrace_of_leftSlice`: Ocneanu identification from
  a scalar left slice.
* `TauCeti.TypeAHeckeAlgebra.atomicTrace_geometric_leftSlice_eq` and
  `TauCeti.TypeAHeckeAlgebra.atomicTrace_negGeometric_eq`: finite positive and negative geometric
  realizations in first-site order.

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
-/

public section

open Function Finsupp

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) {n : ℕ}

/-- `tailIncl` fixes the prepended first letter and acts on the remaining `n` letters. -/
@[simp]
theorem signedChecked_tailIncl_mapDomain_cons (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    signedChecked pos q (tailIncl q n x) (mapDomain (fun w ↦ Fin.cons a w) v) =
      mapDomain (fun w ↦ Fin.cons a w) (signedChecked pos q x v) := by
  set L := lmapDomain R R (fun w : Fin n → ι ↦ (Fin.cons a w : Fin (n + 1) → ι))
  suffices h : (signedChecked pos q (tailIncl q n x)).comp L = L.comp (signedChecked pos q x) by
    simpa [L] using LinearMap.congr_fun h v
  refine signedChecked_comp_eq_of_forall_T pos q _ L (fun i ↦ ?_) x
  have hj : BraidGroup.strand (⟨i + 1, by omega⟩ : Fin (n + 1 - 1)) =
      (BraidGroup.strand i).succ := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (⟨i + 1, by omega⟩ : Fin (n + 1 - 1)) =
      (BraidGroup.strandSucc i).succ := Fin.ext (by simp)
  rw [tailIncl_T, signedChecked_T, signedChecked_T, LinearMap.smul_comp, LinearMap.comp_smul,
    hj, hk, signedCheckedR_comp_lmapDomain_cons]

/-- `tailIncl` acts block-diagonally on words grouped by their first letter. -/
theorem signedChecked_tailIncl_single_cons_apply_cons (x : TypeAHeckeAlgebra R q n)
    (w u : Fin n → ι) (a d : ι) :
    signedChecked pos q (tailIncl q n x) (single (Fin.cons a w) 1) (Fin.cons d u) =
      if a = d then signedChecked pos q x (single w 1) u else 0 := by
  have h := signedChecked_tailIncl_mapDomain_cons pos q x a (single w 1)
  rw [mapDomain_single] at h; rw [h]
  split_ifs with had
  · subst d; exact mapDomain_apply_of_injective (@Fin.cons_right_injective _ (fun _ ↦ ι) a) _ _
  · apply mapDomain_of_notMem_range; rintro ⟨_, hv⟩
    exact had (by simpa using congrArg (fun z : Fin (n + 1) → ι ↦ z 0) hv)

/-- Diagonal entry of `tailIncl x * T 0` at `Fin.cons a w`. -/
theorem signedChecked_tailIncl_mul_T_zero_single_cons_apply
    (x : TypeAHeckeAlgebra R q (n + 1)) (a : ι) (w : Fin (n + 1) → ι) :
    signedChecked pos q (tailIncl q (n + 1) x * T q (0 : Fin (n + 1)))
        (single (Fin.cons a w) 1) (Fin.cons a w) =
      ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
        (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
          else if a < w 0 then (q : R) ^ 2 - 1 else 0) := by
  have hj : BraidGroup.strand (n := n + 2) (0 : Fin (n + 1)) = 0 := Fin.ext (by simp)
  have hk : BraidGroup.strandSucc (n := n + 2) (0 : Fin (n + 1)) = (0 : Fin (n + 1)).succ :=
    Fin.ext (by simp)
  have hswap : Fin.cons a w ∘ Equiv.swap (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ =
      Fin.cons (w 0) (update w 0 a) := by
    rw [Equiv.comp_swap_eq_update, update_comm (Fin.succ_ne_zero _)]; simp
  simp only [map_mul, mul_apply_eq_comp, signedChecked_T, hj, hk, LinearMap.smul_apply,
    signedCheckedR_single_one, Fin.cons_zero, Fin.cons_succ, hswap]
  rcases lt_trichotomy a (w 0) with h | rfl | h
  · simp only [h.ne, h.ne', h, ↓reduceIte, map_sub, map_smul, Finsupp.smul_apply,
      Finsupp.sub_apply, smul_eq_mul, signedChecked_tailIncl_single_cons_apply_cons]; ring
  · simp only [↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
      signedChecked_tailIncl_single_cons_apply_cons]; ring
  · simp only [h.ne, h.ne', h.not_gt, ↓reduceIte, map_neg, map_smul, Finsupp.smul_apply,
      Finsupp.neg_apply, smul_eq_mul, signedChecked_tailIncl_single_cons_apply_cons]; ring

/-- Adding an uncrossed first strand multiplies the atomic trace by the total weight. -/
@[simp]
theorem atomicTrace_tailIncl [Fintype ι] (p : ι → R) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p (n + 1) (tailIncl q n x) = atomicTrace pos q p n x * ∑ a, p a := by
  rw [← strandCycleConj_strandIncl, strandCycleConj_apply, mul_assoc, atomicTrace_mul_comm,
    mul_assoc, Units.inv_mul, mul_one, atomicTrace_strandIncl]

private theorem sum_leftSlice [Fintype ι] (p : ι → R) (b : ι) :
    (∑ a, (if a = b then (if pos b then (q : R) ^ 2 else -1)
      else if a < b then (q : R) ^ 2 - 1 else 0) * p a) =
      (if pos b then (q : R) ^ 2 else -1) * p b + ((q : R) ^ 2 - 1) * ∑ a with a < b, p a := by
  classical
  have h (a : ι) : (if a = b then (if pos b then (q : R) ^ 2 else -1)
      else if a < b then (q : R) ^ 2 - 1 else 0) * p a =
      (if a = b then (if pos b then (q : R) ^ 2 else -1) * p b else 0) +
        (if a < b then ((q : R) ^ 2 - 1) * p a else 0) := by
    split_ifs <;> simp_all
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]

/-- **First-site (left-slice) Markov rule** for `atomicTrace`. -/
theorem atomicTrace_T_zero_mul_tailIncl [Fintype ι] (p : ι → R) {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ a with a < b, p a = q * z)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    atomicTrace pos q p (n + 2) (T q (0 : Fin (n + 1)) * tailIncl q (n + 1) x) =
      z * atomicTrace pos q p (n + 1) x := by
  rw [atomicTrace_mul_comm, atomicTrace_eq_sum,
    ← (Fin.consEquiv (fun _ : Fin (n + 2) ↦ ι)).sum_comp]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    signedChecked_tailIncl_mul_T_zero_single_cons_apply]
  simp_rw [Fin.prod_univ_succ (n := n + 1), Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_comm, atomicTrace_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hfactor : (∑ a, ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w *
      (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
        else if a < w 0 then (q : R) ^ 2 - 1 else 0) * (p a * ∏ i, p (w i))) =
      ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w * (∏ i, p (w i)) *
        ∑ a, (if a = w 0 then (if pos (w 0) then (q : R) ^ 2 else -1)
          else if a < w 0 then (q : R) ^ 2 - 1 else 0) * p a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hfactor, sum_leftSlice, hz]
  linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * Units.inv_mul q

/-- **The atomic trace with scalar left slice is the Ocneanu trace.** -/
theorem atomicTrace_eq_ocneanuTrace_of_leftSlice [Fintype ι] (p : ι → R) {z : R}
    (hp : ∑ a, p a = 1)
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ a with a < b, p a = q * z)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace z).eq_toInfinite_of_T_zero_mul_tailIncl
    (atomicTrace pos q p) (by simp) (by simp [hp]) (fun _ ↦ atomicTrace_mul_comm pos q p)
    (fun _ _ ↦ atomicTrace_castAdd_mul_natAdd pos q p)
    (fun _ ↦ atomicTrace_T_zero_mul_tailIncl pos q p hz) n x

/-- **Positive discrete geometric model in first-site R-order** (`z = c * q ^ (2 * r + 1)`). -/
theorem atomicTrace_geometric_leftSlice_eq {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace (fun _ : Fin (r + 1) ↦ True) q (fun a ↦ c * ((q : R) ^ 2) ^ (r - (a : ℕ))) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * (q : R) ^ (2 * r + 1))
        (toInfinite R q n x) := by
  refine atomicTrace_eq_ocneanuTrace_of_leftSlice _ q _ ?_ (fun b ↦ ?_) x
  · rw [← Finset.mul_sum, ← hc]; congr 1
    exact (Fintype.sum_equiv Fin.revPerm _ (fun a : Fin (r + 1) ↦ ((q : R) ^ 2) ^ (a : ℕ))
      fun a ↦ by simp only [Fin.revPerm_apply, Fin.val_rev]; congr 1; omega).trans
      (Fin.sum_univ_eq_sum_range (fun a ↦ ((q : R) ^ 2) ^ a) (r + 1))
  · have hI : ∑ a : Fin (r + 1) with a < b, c * ((q : R) ^ 2) ^ (r - (a : ℕ)) =
        c * ∑ k ∈ Finset.Ico ((r - (b : ℕ)) + 1) (r + 1), ((q : R) ^ 2) ^ k := by
      rw [← Finset.mul_sum]; congr 1
      refine Finset.sum_bij' (fun a _ ↦ r - (a : ℕ))
        (fun k hk ↦ ⟨r - k, by rw [Finset.mem_Ico] at hk; omega⟩)
        (fun a ha ↦ by simp only [Finset.mem_filter, Fin.lt_def, Finset.mem_Ico] at ha ⊢; omega)
        (fun k hk ↦ by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def,
          Finset.mem_Ico] at hk ⊢; omega)
        (fun a _ ↦ Fin.ext (by dsimp; omega))
        (fun k hk ↦ by rw [Finset.mem_Ico] at hk; dsimp; omega)
        (fun _ _ ↦ rfl)
    have hle : r - (b : ℕ) + 1 ≤ r + 1 := by omega
    have hg := geom_sum_Ico_mul ((q : R) ^ 2) hle
    rw [pow_succ' ((q : R) ^ 2) (r - (b : ℕ))] at hg
    have hpow : (q : R) * (q : R) ^ (2 * r + 1) = ((q : R) ^ 2) ^ (r + 1) := by ring
    simp only [↓reduceIte, hI]; linear_combination c * hg - c * hpow

/-- **Negative discrete geometric model in first-site R-order** (`z = -(c * q⁻¹)`). -/
theorem atomicTrace_negGeometric_eq {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1)
    (x : TypeAHeckeAlgebra R q n) :
    atomicTrace (fun _ : Fin (r + 1) ↦ False) q (fun a ↦ c * ((q : R) ^ 2) ^ (a : ℕ)) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (-(c * ↑q⁻¹)) (toInfinite R q n x) := by
  refine atomicTrace_eq_ocneanuTrace_of_leftSlice _ q _ ?_ (fun b ↦ ?_) x
  · rw [← Finset.mul_sum, ← hc, Fin.sum_univ_eq_sum_range (fun a ↦ ((q : R) ^ 2) ^ a)]
  · have hI : ∑ a : Fin (r + 1) with a < b, c * ((q : R) ^ 2) ^ (a : ℕ) =
        c * ∑ a ∈ Finset.range (b : ℕ), ((q : R) ^ 2) ^ a := by
      rw [← Finset.mul_sum, Finset.sum_filter]; congr 1; simp_rw [Fin.lt_def]
      rw [Fin.sum_univ_eq_sum_range
        (fun a ↦ if a < (b : ℕ) then ((q : R) ^ 2) ^ a else 0) (r + 1), ← Finset.sum_filter]
      congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega
    simp only [↓reduceIte, hI]
    linear_combination c * geom_sum_mul ((q : R) ^ 2) (b : ℕ) + c * Units.mul_inv q

end TauCeti.TypeAHeckeAlgebra
