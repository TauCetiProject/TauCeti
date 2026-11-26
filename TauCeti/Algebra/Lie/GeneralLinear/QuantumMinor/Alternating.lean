/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.LinearCombination

/-!
# Column alternation of quantum minors

The matrix-unit Lie relations give an exchange identity for the two factors at consecutive
spectral parameters. Pairing the Leibniz terms that swap the two selected rows makes the
quantum minor alternating in its column tuple as well as in its row tuple. In particular,
a repeated column kills the minor, without an assumption on the characteristic.

See A. Molev, M. Nazarov and G. Olshanski, *Yangians and classical Lie algebras*, §2,
and L. Alpöge's `Formalism.REAL.QSkewRow` for the column alternation identity.
-/

public section

namespace Matrix

open Equiv Equiv.Perm

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A]

/-- A family of elements with the commutator relations of the general linear matrix units. -/
def HasMatrixUnitLieRelations (E : Matrix ι ι A) : Prop :=
  ∀ a b c d, ⁅E a b, E c d⁆ = (if b = c then E a d else 0) - (if d = a then E c b else 0)

/-- The entrywise characterization of a matrix-unit family. -/
theorem hasMatrixUnitLieRelations_iff (E : Matrix ι ι A) : E.HasMatrixUnitLieRelations ↔
    ∀ a b c d, ⁅E a b, E c d⁆ = (if b = c then E a d else 0) - (if d = a then E c b else 0) :=
  (Iff.rfl)

-- Only used to compare the two positions in a Leibniz product.
private def shifted (E : Matrix ι ι A) (s : K) (a b : ι) : A :=
  (if a = b then algebraMap K A s else 0) + E a b

private theorem shifted_pair (E : Matrix ι ι A) (hE : E.HasMatrixUnitLieRelations)
    (s : K) (a b c d : ι) :
    shifted E s a c * shifted E (s - 1) b d -
      shifted E s b c * shifted E (s - 1) a d =
    shifted E (s - 1) b d * shifted E s a c -
      shifted E (s - 1) b c * shifted E s a d := by
  have hcentral (u : K) (i j : ι) (x : A) : ⁅(if i = j then algebraMap K A u else 0), x⁆ = 0 := by
    split <;> simp [Commute.lie_eq (Algebra.commutes u x)]
  have hcentral' (u : K) (i j : ι) (x : A) : ⁅x, (if i = j then algebraMap K A u else 0)⁆ = 0 := by
    rw [← lie_skew, hcentral, neg_zero]
  have hcomm : ⁅shifted E s a c, shifted E (s - 1) b d⁆ = ⁅E a c, E b d⁆ := by
    simp only [shifted, add_lie, lie_add, hcentral, hcentral', zero_add]
  have hstep i j : shifted E (s - 1) i j = shifted E s i j - (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · simp [shifted, hij]
      abel
    · simp [shifted, hij]
  have hcross : shifted E s b c * shifted E (s - 1) a d -
      shifted E (s - 1) b c * shifted E s a d = ⁅E a c, E b d⁆ := by
    rw [hstep b c, hstep a d, (hasMatrixUnitLieRelations_iff E).mp hE]
    simp only [mul_sub, sub_mul]
    by_cases hbc : b = c <;> by_cases had : d = a <;>
      simp [hbc, had, eq_comm (a := a) (b := d), eq_comm (a := c) (b := b), shifted]
  rw [Ring.lie_def] at hcomm
  rw [← hcross] at hcomm
  linear_combination (norm := abel) hcomm

private theorem quantumMinor_comp_swap_right (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) {n : ℕ} (a b : Fin (n + 1) → ι) (i : Fin n) :
    E.quantumMinor u a (b ∘ swap i.castSucc i.succ) = -E.quantumMinor u a b := by
  simp only [quantumMinor_eq_columnDet]
  rw [← neg_one_smul ℤ]
  apply columnDet_eq_zsmul_of_adjacent _ _ _ (i := i.castSucc) (j := i.succ) (by simp)
  · intro r k hi hj
    simp [of_apply, Function.comp_apply, swap_apply_of_ne_of_ne hi hj]
  · intro r s _
    let v := u - (i.val : K)
    have hs := shifted_pair E hE v (a r) (a s) (b i.castSucc) (b i.succ)
    have ht := shifted_pair E hE v (a r) (a s) (b i.succ) (b i.castSucc)
    have ht' := ht.trans ((neg_sub _ _).symm.trans (congrArg Neg.neg hs.symm))
    simpa only [v, shifted, of_apply, Function.comp_apply, swap_apply_left, swap_apply_right,
      Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub,
      neg_one_smul] using ht'

/-- Permuting the columns of a quantum minor multiplies it by the sign of the permutation. -/
@[simp] theorem quantumMinor_comp_perm_right (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) {n : ℕ} (a b : Fin n → ι) (e : Perm (Fin n)) :
    E.quantumMinor u a (b ∘ e) = sign e • E.quantumMinor u a b := by
  cases n with
  | zero => rw [Subsingleton.elim e 1]; simp
  | succ n =>
    induction (mclosure_swap_castSucc_succ n).ge (Submonoid.mem_top e) using
      Submonoid.closure_induction_left generalizing b with
    | one => simp
    | mul_left x hx y _ ih =>
      obtain ⟨i, rfl⟩ := hx
      rw [Perm.coe_mul, ← Function.comp_assoc, ih,
        quantumMinor_comp_swap_right E hE u a b i, sign_mul,
        sign_swap i.castSucc_lt_succ.ne]
      simp [Units.smul_def]

private theorem quantumMinor_eq_zero_of_adjacent_eq (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) {n : ℕ} (a b : Fin (n + 1) → ι) (i : Fin n)
    (h : b i.castSucc = b i.succ) : E.quantumMinor u a b = 0 := by
  rw [quantumMinor_eq_columnDet]
  refine (columnDet_eq_zsmul_of_adjacent _ _ 0 (i := i.castSucc) (j := i.succ) (by simp)
    (fun _ _ _ _ ↦ rfl) ?_).trans (zero_smul _ _)
  intro r s _
  simpa only [shifted, h, of_apply, Fin.val_succ, Fin.val_castSucc,
    Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub, zero_smul, sub_self] using
    shifted_pair E hE (u - (i.val : K)) (a r) (a s) (b i.succ) (b i.succ)

/-- A quantum minor with a repeated column index vanishes. -/
theorem quantumMinor_eq_zero_of_not_injective_right (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) {n : ℕ} (a b : Fin n → ι)
    (h : ¬ Function.Injective b) : E.quantumMinor u a b = 0 := by
  obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp h
  have hn : 2 ≤ n := by omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hn)
    (Fin.cases i fun _ ↦ j) (Fin.castLE_injective hn) (by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · exact (hne hxy).elim
      · exact (hne hxy.symm).elim
      · rfl)
  have h₀ : e 0 = i := he 0
  have h₁ : e 1 = j := he 1
  have hzero := quantumMinor_eq_zero_of_adjacent_eq E hE u a (b ∘ e) 0
    (by simpa [Function.comp_apply, h₀, h₁] using heq)
  rw [quantumMinor_comp_perm_right E hE] at hzero
  simpa [smul_smul] using congrArg (fun x : A ↦ (sign e)⁻¹ • x) hzero

end Matrix
