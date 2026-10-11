/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import TauCeti.LinearAlgebra.IntegralLattice.Examples
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Integral isometries of the hyperbolic plane

The hyperbolic plane `U` has Gram matrix `!![0, 1; 1, 0]`. Every integral isometry
is the identity, simultaneous negation, coordinate exchange, or their composite.
Consequently its full integral isometry group has four elements, although its
rational isometry group is infinite.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §1.
-/

public section
namespace TauCeti.IntegralLattice

/-- Exchange of the two isotropic basis vectors of the hyperbolic plane. -/
def hyperbolicPlaneSwap : Isometry hyperbolicPlane hyperbolicPlane where
  toIsometryEquiv :=
    { toLinearEquiv :=
        { toFun := fun x ↦ ![x 1, x 0]
          invFun := fun x ↦ ![x 1, x 0]
          left_inv := by intro x; ext i; fin_cases i <;> rfl
          right_inv := by intro x; ext i; fin_cases i <;> rfl
          map_add' := by intro x y; ext i; fin_cases i <;> rfl
          map_smul' := by intro a x; ext i; fin_cases i <;> rfl }
      map_app' := by intro x y; simp [hyperbolicPlane_form_apply, add_comm] }
  map_carrier := by
    ext x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_hyperbolicPlane_carrier_iff] at hy ⊢
      intro i
      fin_cases i
      · exact hy 1
      · exact hy 0
    · intro hx
      refine ⟨![x 1, x 0], ?_, ?_⟩
      · rw [mem_hyperbolicPlane_carrier_iff] at hx ⊢
        intro i
        fin_cases i
        · exact hx 1
        · exact hx 0
      · ext i
        fin_cases i <;> rfl

/-- The swap reverses the two rational coordinates. -/
@[simp] theorem hyperbolicPlaneSwap_apply (x : Fin 2 → ℚ) :
    hyperbolicPlaneSwap x = ![x 1, x 0] := (rfl)

private theorem isometry_eq_of_basis_images
    {e f : Isometry hyperbolicPlane hyperbolicPlane}
    (h0 : e ![1, 0] = f ![1, 0]) (h1 : e ![0, 1] = f ![0, 1]) : e = f := by
  apply Isometry.ext
  intro x
  have hx : x = x 0 • (![1, 0] : Fin 2 → ℚ) + x 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp
  rw [hx]
  simp only [map_add, map_smul, h0, h1]

/-- The full integral isometry group of the hyperbolic plane consists of the identity,
negation, coordinate exchange, and their composite. -/
theorem hyperbolicPlane_isometry_eq (e : Isometry hyperbolicPlane hyperbolicPlane) :
    e = 1 ∨ e = Isometry.neg hyperbolicPlane ∨ e = hyperbolicPlaneSwap ∨
      e = Isometry.neg hyperbolicPlane * hyperbolicPlaneSwap := by
  have hx : ∀ i, ∃ n : ℤ, (n : ℚ) = e (![1, 0] : Fin 2 → ℚ) i :=
    (mem_hyperbolicPlane_carrier_iff _).mp
      ((e.apply_mem_carrier_iff _).mpr (by simp [Fin.forall_fin_two]))
  have hy : ∀ i, ∃ n : ℤ, (n : ℚ) = e (![0, 1] : Fin 2 → ℚ) i :=
    (mem_hyperbolicPlane_carrier_iff _).mp
      ((e.apply_mem_carrier_iff _).mpr (by simp [Fin.forall_fin_two]))
  have hxx : e ![1, 0] 0 * e ![1, 0] 1 = 0 := by
    have h := e.map_app ![1, 0] ![1, 0]
    simp only [hyperbolicPlane_form_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_zero, zero_mul, add_zero] at h
    linarith
  have hyy : e ![0, 1] 0 * e ![0, 1] 1 = 0 := by
    have h := e.map_app ![0, 1] ![0, 1]
    simp only [hyperbolicPlane_form_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_zero, zero_mul, add_zero] at h
    linarith
  have hxy : e ![1, 0] 0 * e ![0, 1] 1 + e ![1, 0] 1 * e ![0, 1] 0 = 1 := by
    have h := e.map_app ![1, 0] ![0, 1]
    norm_num only [hyperbolicPlane_form_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact h
  rcases mul_eq_zero.mp hxx with hx0 | hx1
  · have hprod : e ![1, 0] 1 * e ![0, 1] 0 = 1 := by simpa [hx0] using hxy
    obtain ⟨n, hn⟩ := hx 1
    obtain ⟨m, hm⟩ := hy 0
    have hnm : n * m = 1 := by
      exact_mod_cast (show (n : ℚ) * (m : ℚ) = 1 from by rw [hn, hm]; exact hprod)
    have hpair : (e ![1, 0] 1 = 1 ∧ e ![0, 1] 0 = 1) ∨
        (e ![1, 0] 1 = -1 ∧ e ![0, 1] 0 = -1) := by
      rw [← hn, ← hm]
      exact_mod_cast Int.eq_one_or_neg_one_of_mul_eq_one' hnm
    rcases hpair with ⟨h, hy0⟩ | ⟨h, hy0⟩
    · have hy1 : e ![0, 1] 1 = 0 := by simpa [hy0] using hyy
      right; right; left
      apply isometry_eq_of_basis_images <;> ext i <;> fin_cases i <;>
        simp [hx0, h, hy0, hy1]
    · have hy1 : e ![0, 1] 1 = 0 := by simpa [hy0] using hyy
      right; right; right
      apply isometry_eq_of_basis_images <;> ext i <;> fin_cases i <;>
        simp [hx0, h, hy0, hy1]
  · have hprod : e ![1, 0] 0 * e ![0, 1] 1 = 1 := by simpa [hx1] using hxy
    obtain ⟨n, hn⟩ := hx 0
    obtain ⟨m, hm⟩ := hy 1
    have hnm : n * m = 1 := by
      exact_mod_cast (show (n : ℚ) * (m : ℚ) = 1 from by rw [hn, hm]; exact hprod)
    have hpair : (e ![1, 0] 0 = 1 ∧ e ![0, 1] 1 = 1) ∨
        (e ![1, 0] 0 = -1 ∧ e ![0, 1] 1 = -1) := by
      rw [← hn, ← hm]
      exact_mod_cast Int.eq_one_or_neg_one_of_mul_eq_one' hnm
    rcases hpair with ⟨h, hy1⟩ | ⟨h, hy1⟩
    · have hy0 : e ![0, 1] 0 = 0 := by simpa [hy1] using hyy
      left
      apply isometry_eq_of_basis_images <;> ext i <;> fin_cases i <;>
        simp [hx1, h, hy0, hy1]
    · have hy0 : e ![0, 1] 0 = 0 := by simpa [hy1] using hyy
      right; left
      apply isometry_eq_of_basis_images <;> ext i <;> fin_cases i <;>
        simp [hx1, h, hy0, hy1]

/-- The full integral isometry group of the hyperbolic plane has four elements. -/
theorem card_isometry_hyperbolicPlane :
    Nat.card (Isometry hyperbolicPlane hyperbolicPlane) = 4 := by
  let f : Fin 4 → Isometry hyperbolicPlane hyperbolicPlane :=
    ![1, Isometry.neg hyperbolicPlane, hyperbolicPlaneSwap,
      Isometry.neg hyperbolicPlane * hyperbolicPlaneSwap]
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl |
        (have h := congrArg (fun e : Isometry hyperbolicPlane hyperbolicPlane ↦
           (e ![1, 0] 0, e ![1, 0] 1)) hij
         norm_num [f] at h)
    · intro e
      rcases hyperbolicPlane_isometry_eq e with h | h | h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
      · exact ⟨3, h.symm⟩
  simpa using (Nat.card_eq_of_bijective f hf).symm

end TauCeti.IntegralLattice
