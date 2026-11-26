/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import TauCeti.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.NoncommRing

/-!
# Alternating traces of matrix products

The alternating trace is the unnormalized alternation of the trace of an ordered matrix
product. It is invariant under the simultaneous infinitesimal conjugation action on its
arguments.
-/

public section

noncomputable section

namespace Matrix

variable (R ι A : Type*) [CommSemiring R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]

/-- The unnormalized alternating trace of an ordered matrix product. -/
def alternatingTrace (n : ℕ) : Matrix ι ι A [⋀^Fin n]→ₗ[R] A :=
  ((traceLinearMap ι R A).compMultilinearMap
    (MultilinearMap.mkPiAlgebraFin R n (Matrix ι ι A))).alternatization

/-- The characteristic permutation formula has no factorial normalization. -/
theorem alternatingTrace_apply (n : ℕ) (v : Fin n → Matrix ι ι A) :
    alternatingTrace R ι A n v = ∑ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • trace (List.ofFn fun i ↦ v (σ i)).prod := by
  simp [alternatingTrace, MultilinearMap.alternatization_apply]

/-- The trace of an ordered product is invariant under the simultaneous infinitesimal
conjugation action on all its arguments. -/
private theorem sum_trace_prod_update_lie (n : ℕ) (Y : Matrix ι ι A)
    (v : Fin n → Matrix ι ι A) :
    ∑ i, trace (List.ofFn (Function.update v i ⁅Y, v i⁆)).prod = 0 := by
  have h := TauCeti.map_prod_ofFn_of_leibniz (fun X : Matrix ι ι A ↦ ⁅Y, X⁆)
    (fun X Z ↦ by simp only [Ring.lie_def]; noncomm_ring) v
  calc
    (∑ i, trace (List.ofFn (Function.update v i ⁅Y, v i⁆)).prod) =
        (traceAddMonoidHom ι A)
          (∑ i, (List.ofFn (Function.update v i ⁅Y, v i⁆)).prod) := by rw [map_sum]; rfl
    _ = trace ⁅Y, (List.ofFn v).prod⁆ := congrArg trace h.symm
    _ = 0 := by rw [Ring.lie_def, trace_sub, trace_mul_comm, sub_self]

/-- Alternation preserves the infinitesimal conjugation invariance of the trace. -/
theorem alternatingTrace_sum_update_lie (n : ℕ) (Y : Matrix ι ι A)
    (v : Fin n → Matrix ι ι A) :
    ∑ i, alternatingTrace R ι A n (Function.update v i ⁅Y, v i⁆) = 0 := by
  simp only [alternatingTrace_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro σ _
  rw [← Finset.smul_sum]
  suffices ∑ i, trace
      (List.ofFn fun j ↦ Function.update v i ⁅Y, v i⁆ (σ j)).prod = 0 by rw [this, smul_zero]
  have hupdate (i : Fin n) :
      (fun j ↦ Function.update v (σ i) ⁅Y, v (σ i)⁆ (σ j)) =
        Function.update (fun j ↦ v (σ j)) i ⁅Y, v (σ i)⁆ := by
    ext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne, σ.injective.ne_iff]
  rw [← Equiv.sum_comp σ]
  simp only [hupdate]
  exact sum_trace_prod_update_lie ι A n Y (fun j ↦ v (σ j))

/-- Conjugate transposition reverses an ordered product, contributing the sign of reversal
to its alternating trace. -/
theorem alternatingTrace_star [StarRing A] (n : ℕ) (v : Fin n → Matrix ι ι A) :
    star (alternatingTrace R ι A n v) = Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) •
      alternatingTrace R ι A n (fun i ↦ (v i)ᴴ) := by
  have hreverse (w : Fin n → Matrix ι ι A) :
      (List.ofFn w).reverse = List.ofFn (fun i ↦ w (Fin.revPerm i)) := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp [List.getElem_reverse, Fin.rev, Nat.sub_sub, Nat.add_comm]
  have hstar (u : ℤˣ) : star u = u := Units.ext (by simp)
  simp only [alternatingTrace_apply, star_sum, star_smul, hstar,
    ← trace_conjTranspose, conjTranspose_list_prod, List.map_ofFn, hreverse]
  rw [Finset.smul_sum]
  rw [← Equiv.sum_comp (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n)))]
  apply Finset.sum_congr rfl
  intro σ _
  simp [Equiv.Perm.sign_mul, smul_smul, Equiv.Perm.mul_apply, mul_comm]

end Matrix
