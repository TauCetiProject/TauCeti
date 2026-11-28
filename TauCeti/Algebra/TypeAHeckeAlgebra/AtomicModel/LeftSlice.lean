/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Block.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Tail
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.TypeAHeckeAlgebra.Cocenter.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# First-site Markov rules and left-slice geometric atomic models

For an atomic model `TauCeti.TypeAHeckeAlgebra.atomicTrace pos q p n`, `tailIncl` fixes the first
letter (`signedChecked_tailIncl_mapDomain_cons`) and scales the trace by `∑ a, p a`
(`atomicTrace_tailIncl`). Multiplying by `T 0` tests the left slice, so scalar left slices yield
first-site Markov rules (`atomicTrace_T_zero_mul_tailIncl`,
`atomicTrace_eq_ocneanuTrace_of_leftSlice`) and realize Wenzl's discrete series
(`atomicTrace_geometric_leftSlice_eq`, `atomicTrace_negGeometric_eq`). Cf. Wenzl (1988, §3),
Neretin (arXiv:2101.02133, §§1.6–1.7, §3.1).
-/

public section

open Function Finsupp

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  (q : Rˣ) {n : ℕ}

/-- `tailIncl` fixes the prepended first letter and acts on the remaining `n` letters. -/
@[simp] theorem signedChecked_tailIncl_mapDomain_cons (x : TypeAHeckeAlgebra R q n) (a : ι)
    (v : (Fin n → ι) →₀ R) :
    signedChecked pos q (tailIncl q n x) (mapDomain (fun w ↦ Fin.cons a w) v) =
      mapDomain (fun w ↦ Fin.cons a w) (signedChecked pos q x v) := by
  set L := lmapDomain R R (fun w : Fin n → ι ↦ (Fin.cons a w : Fin (n + 1) → ι))
  suffices h : (signedChecked pos q (tailIncl q n x)).comp L = L.comp (signedChecked pos q x) by
    simpa [L] using LinearMap.congr_fun h v
  refine signedChecked_comp_eq_of_forall_T pos q _ L (fun i ↦ ?_) x
  rw [tailIncl_T, signedChecked_T, signedChecked_T, LinearMap.smul_comp, LinearMap.comp_smul,
    show BraidGroup.strand (⟨i + 1, by omega⟩ : Fin (n + 1 - 1)) = (BraidGroup.strand i).succ from
      Fin.ext (by simp), show BraidGroup.strandSucc (⟨i + 1, by omega⟩ : Fin (n + 1 - 1)) =
        (BraidGroup.strandSucc i).succ from Fin.ext (by simp), signedCheckedR_comp_lmapDomain_cons]

/-- `tailIncl` acts block-diagonally on words grouped by their first letter. -/
theorem signedChecked_tailIncl_single_cons_apply_cons (x : TypeAHeckeAlgebra R q n)
    (w u : Fin n → ι) (a d : ι) :
    signedChecked pos q (tailIncl q n x) (single (Fin.cons a w) 1) (Fin.cons d u) =
      if a = d then signedChecked pos q x (single w 1) u else 0 := by
  rw [← mapDomain_single (a := w) (b := (1 : R)), signedChecked_tailIncl_mapDomain_cons]
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
  simp only [map_mul, mul_apply_eq_comp, signedChecked_T, hj, hk, LinearMap.smul_apply,
    signedCheckedR_single_one, Fin.cons_zero, Fin.cons_succ, Fin.cons_comp_swap_zero]
  rcases lt_trichotomy a (w 0) with h | rfl | h
  · simp only [h.ne, h.ne', h, ↓reduceIte, map_sub, map_smul, Finsupp.smul_apply,
      Finsupp.sub_apply, smul_eq_mul, signedChecked_tailIncl_single_cons_apply_cons]; ring
  · simp only [↓reduceIte, map_smul, Finsupp.smul_apply, smul_eq_mul,
      signedChecked_tailIncl_single_cons_apply_cons]; split_ifs <;> ring
  · simp only [h.ne, h.ne', h.not_gt, ↓reduceIte, map_neg, map_smul, Finsupp.smul_apply,
      Finsupp.neg_apply, smul_eq_mul, signedChecked_tailIncl_single_cons_apply_cons]; ring

/-- Adding an uncrossed first strand multiplies the atomic trace by the total weight. -/
@[simp] theorem atomicTrace_tailIncl [Fintype ι] (p : ι → R) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p (n + 1) (tailIncl q n x) = atomicTrace pos q p n x * ∑ a, p a := by
  rw [← strandCycleConj_strandIncl, strandCycleConj_apply, mul_assoc, atomicTrace_mul_comm,
    mul_assoc, Units.inv_mul, mul_one, atomicTrace_strandIncl]

private theorem sum_leftSlice [Fintype ι] (p : ι → R) (b : ι) :
    (∑ a, (if a = b then (if pos b then (q : R) ^ 2 else -1)
      else if a < b then (q : R) ^ 2 - 1 else 0) * p a) =
      (if pos b then (q : R) ^ 2 else -1) * p b + ((q : R) ^ 2 - 1) * ∑ a with a < b, p a := by
  classical
  trans ∑ a, ((if a = b then (if pos b then (q : R) ^ 2 else -1) * p b else 0) +
    if a < b then ((q : R) ^ 2 - 1) * p a else 0)
  · exact Finset.sum_congr rfl fun a _ ↦ by split_ifs <;> simp_all
  · simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter]

/-- **First-site (left-slice) Markov rule** for `atomicTrace`. -/
theorem atomicTrace_T_zero_mul_tailIncl [Fintype ι] (p : ι → R) {z : R}
    (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ a with a < b, p a = q * z)
    (x : TypeAHeckeAlgebra R q (n + 1)) :
    atomicTrace pos q p (n + 2) (T q (0 : Fin (n + 1)) * tailIncl q (n + 1) x) =
      z * atomicTrace pos q p (n + 1) x := by
  rw [atomicTrace_mul_comm, atomicTrace_eq_sum, ← (Fin.consEquiv fun _ ↦ ι).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fin.prod_univ_succ (n := n + 1),
    signedChecked_tailIncl_mul_T_zero_single_cons_apply, Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_comm, atomicTrace_eq_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ ↦ ?_
  trans ((q⁻¹ : Rˣ) : R) * signedChecked pos q x (single w 1) w * (∏ i, p (w i)) * (q * z)
  · rw [← hz (w 0), ← sum_leftSlice, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  · linear_combination (z * signedChecked pos q x (single w 1) w * ∏ i, p (w i)) * Units.inv_mul q

/-- **The atomic trace with scalar left slice is the Ocneanu trace.** -/
theorem atomicTrace_eq_ocneanuTrace_of_leftSlice [Fintype ι] (p : ι → R) {z : R}
    (hp : ∑ a, p a = 1) (hz : ∀ b, (if pos b then (q : R) ^ 2 else -1) * p b +
      ((q : R) ^ 2 - 1) * ∑ a with a < b, p a = q * z) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace pos q p n x = InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z (toInfinite R q n x) :=
  (InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace z).eq_toInfinite_of_T_zero_mul_tailIncl
    (atomicTrace pos q p) (by simp [hp]) (fun _ ↦ atomicTrace_mul_comm pos q p)
    (fun _ _ ↦ atomicTrace_castAdd_mul_natAdd pos q p)
    (fun _ ↦ atomicTrace_T_zero_mul_tailIncl pos q p hz) n x

/-- **Positive discrete geometric model in first-site R-order** (`z = c * q ^ (2 * r + 1)`). -/
theorem atomicTrace_geometric_leftSlice_eq {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace (fun _ : Fin (r + 1) ↦ True) q (fun a ↦ c * ((q : R) ^ 2) ^ (r - (a : ℕ))) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (c * (q : R) ^ (2 * r + 1))
        (toInfinite R q n x) := by
  refine atomicTrace_eq_ocneanuTrace_of_leftSlice _ q _ ?_ (fun b ↦ ?_) x
  · rw [← Finset.mul_sum, ← hc, ← Fin.sum_univ_eq_sum_range (fun a ↦ ((q : R) ^ 2) ^ a)]
    exact congrArg (c * ·) (Fintype.sum_equiv Fin.revPerm _ _ fun a ↦ by simp)
  · have hI : ∑ a : Fin (r + 1) with a < b, c * ((q : R) ^ 2) ^ (r - (a : ℕ)) =
        c * ∑ k ∈ Finset.Ico ((r - (b : ℕ)) + 1) (r + 1), ((q : R) ^ 2) ^ k := by
      rw [← Finset.mul_sum, Finset.sum_filter]; congr 1
      refine (Fintype.sum_equiv Fin.revPerm _ (fun a ↦ if r - (b : ℕ) < a then
          ((q : R) ^ 2) ^ (a : ℕ) else 0) fun a ↦ by
        simp only [Fin.revPerm_apply, Fin.val_rev, Fin.lt_def]
        split_ifs <;> congr 1 <;> omega).trans ?_
      rw [Fin.sum_univ_eq_sum_range (fun a ↦ if r - (b : ℕ) < a then ((q : R) ^ 2) ^ a else 0),
        ← Finset.sum_filter]; congr 1; ext k; simp; omega
    have hg := geom_sum_Ico_mul ((q : R) ^ 2) (by omega : r - (b : ℕ) + 1 ≤ r + 1)
    rw [pow_succ' ((q : R) ^ 2) (r - (b : ℕ)), show ((q : R) ^ 2) ^ (r + 1) =
      (q : R) * (q : R) ^ (2 * r + 1) by ring] at hg
    simp only [↓reduceIte, hI]; linear_combination c * hg

/-- **Negative discrete geometric model in first-site R-order** (`z = -(c * q⁻¹)`). -/
theorem atomicTrace_negGeometric_eq {r : ℕ} {c : R}
    (hc : c * ∑ a ∈ Finset.range (r + 1), ((q : R) ^ 2) ^ a = 1) (x : TypeAHeckeAlgebra R q n) :
    atomicTrace (fun _ : Fin (r + 1) ↦ False) q (fun a ↦ c * ((q : R) ^ 2) ^ (a : ℕ)) n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace R q (-(c * ↑q⁻¹)) (toInfinite R q n x) := by
  refine atomicTrace_eq_ocneanuTrace_of_leftSlice _ q _ ?_ (fun b ↦ ?_) x
  · rw [← Finset.mul_sum, ← hc, Fin.sum_univ_eq_sum_range (fun a ↦ ((q : R) ^ 2) ^ a)]
  · have hI : ∑ a : Fin (r + 1) with a < b, c * ((q : R) ^ 2) ^ (a : ℕ) =
        c * ∑ a ∈ Finset.range (b : ℕ), ((q : R) ^ 2) ^ a := by
      rw [← Finset.mul_sum, Finset.sum_filter]; simp only [Fin.lt_def]
      rw [Fin.sum_univ_eq_sum_range (fun a ↦ if a < (b : ℕ) then ((q : R) ^ 2) ^ a else 0),
        ← Finset.sum_filter]
      exact congrArg (c * ·) (Finset.sum_congr (by ext a; simp; omega) fun _ _ ↦ rfl)
    simp only [↓reduceIte, hI]
    linear_combination c * geom_sum_mul ((q : R) ^ 2) b + c * Units.mul_inv q

end TauCeti.TypeAHeckeAlgebra
