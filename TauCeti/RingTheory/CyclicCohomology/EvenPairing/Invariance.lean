/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.RingTheory.CyclicCohomology.EvenPairing.Basic
import Mathlib.Algebra.Polynomial.Derivative
import TauCeti.Algebra.Group.Idempotent
import TauCeti.Algebra.Polynomial.Eval.AlgebraMap
import TauCeti.LinearAlgebra.Multilinear.Polynomial

/-!
# Homotopy and conjugation invariance of the even pairing

Let `φ` be a cyclic cocycle of even degree on an algebra `A`. This file shows that the value
`φ(e, …, e)` on an idempotent `e`, and hence Connes' even pairing `⟨[e], [φ]⟩`, is unchanged by
moving `e` along a polynomial path of idempotents and by conjugating `e` by an invertible element.
These are the invariances needed before the even pairing can descend from idempotents to `K₀`.

The argument has three steps.

* **Infinitesimal invariance.** If `e` is idempotent and `y` is tangent to the idempotents at `e`,
  that is `e y + y e = y`, then `φ(e, …, y, …, e) = 0` in every slot. Indeed `y = x e - e x` for
  `x = y e - e y`, and evaluating `bφ = 0` on `(x, e, …, e)` gives
  `φ(x e, e, …, e) = φ(e x, e, …, e)` in even degree; cyclicity moves the distinguished entry to
  any slot. This is `TauCeti.apply_update_const_eq_zero_of_isIdempotentElem`, proved in
  `TauCeti.RingTheory.CyclicCohomology.Cochain`.
* **Polynomial homotopy invariance.** For an idempotent `e(X)` with coefficients in `A`, the
  derivative of `t ↦ φ(e(t), …, e(t))` is a sum of such infinitesimal terms, because
  `e′ = e e′ + e′ e`. By the zero-derivative principle of
  `MultilinearMap.apply_eval_algebraMap_eq_of_linearDeriv_eq_zero`, it is constant.
* **Conjugation invariance.** For `N² = 0` the path `t ↦ (1 + tN) e (1 - tN)` joins `e` to
  `(1 + N) e (1 - N)`. In `2 × 2` matrices, conjugating the corner `e ⊕ 0` by
  `!![0, u; -u⁻¹, 0]`, a product of three such unipotents, gives the corner `0 ⊕ u⁻¹ e u`; matrix
  extension `φ#Tr` recovers `φ` on either corner.

Applied to the algebra `Matrix ι ι A`, the conjugation statements cover conjugation of idempotent
matrices by invertible matrices.

## Main results

* `TauCeti.apply_const_eval_algebraMap_eq`: invariance of `φ(e, …, e)` along polynomial paths of
  idempotents.
* `TauCeti.apply_const_units_conj`: invariance of `φ(e, …, e)` under conjugation by a unit.
* `TauCeti.cyclicCohomology.evenPairing_eval_algebraMap_eq` and
  `TauCeti.cyclicCohomology.evenPairing_units_conj`: the corresponding invariances of the even
  pairing.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §3.
* J.-L. Loday, *Cyclic Homology*, §8.3.
-/

public section

noncomputable section

namespace TauCeti

open Polynomial

section Homotopy

variable {R A M : Type*} [Field R] [CharZero R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M]

/-- **Polynomial homotopy invariance.** Let `φ` be a cyclic cocycle of even degree and `e` an
idempotent polynomial with coefficients in `A`. Then `φ(e(t), …, e(t))` does not depend on the
scalar `t`. -/
theorem apply_const_eval_algebraMap_eq {n : ℕ} (hn : Even n)
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n)
    (hbφ : hochschildCoboundary R A M n φ = 0) {e : A[X]} (he : IsIdempotentElem e) (s t : R) :
    φ (fun _ ↦ e.eval (algebraMap R A s)) = φ (fun _ ↦ e.eval (algebraMap R A t)) := by
  refine φ.apply_eval_algebraMap_eq_of_linearDeriv_eq_zero (fun _ ↦ e) (fun r ↦ ?_) s t
  -- Differentiating `e = e * e` shows that `e′` is tangent to the idempotents at `e`.
  have hd : derivative e = derivative e * e + e * derivative e := by
    conv_lhs => rw [← he.eq]
    exact derivative_mul
  rw [MultilinearMap.linearDeriv_apply]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  -- Evaluation at the central element `algebraMap R A r` is a ring homomorphism.
  simp only [← evalAlgebraMapRingHom_apply A r]
  refine apply_update_const_eq_zero_of_isIdempotentElem hn hφ hbφ (he.map _) ?_ k
  rw [← map_mul, ← map_mul, ← map_add, add_comm, ← hd]

/-- Conjugating an idempotent by a square-zero unipotent `1 + N` preserves the value of an
even-degree cyclic cocycle on constant tuples. -/
private theorem apply_const_one_add_mul_mul_one_sub_eq {n : ℕ} (hn : Even n)
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n)
    (hbφ : hochschildCoboundary R A M n φ = 0) {e N : A} (he : IsIdempotentElem e)
    (hN : N * N = 0) :
    IsIdempotentElem ((1 + N) * e * (1 - N)) ∧
      φ (fun _ ↦ (1 + N) * e * (1 - N)) = φ (fun _ ↦ e) := by
  refine ⟨he.mul_mul_of_mul_eq_one (by simp [sub_mul, mul_add, hN]), ?_⟩
  -- The polynomial path `t ↦ (1 + tN) e (1 - tN)` of idempotents joins `e` to `(1 + N) e (1 - N)`.
  have hX : C N * X * (C N * X) = (0 : A[X]) := by
    rw [(commute_X (C N)).mul_mul_mul_comm, ← C_mul, hN, C_0, zero_mul]
  have hP : IsIdempotentElem ((1 + C N * X) * C e * (1 - C N * X)) :=
    (he.map C).mul_mul_of_mul_eq_one (by simp [sub_mul, mul_add, hX])
  have h := apply_const_eval_algebraMap_eq hn hφ hbφ hP 1 0
  rw [← evalAlgebraMapRingHom_apply A, ← evalAlgebraMapRingHom_apply A] at h
  simp only [map_mul, map_add, map_sub, map_one] at h
  simpa only [evalAlgebraMapRingHom_apply, eval_C, eval_X, map_one, map_zero, mul_one, one_mul,
    mul_zero, add_zero, sub_zero] using h

/-- Conjugating an idempotent `e` to `u⁻¹ e u` by a unit `u` preserves the value of an
even-degree cyclic cocycle on constant tuples. -/
private theorem apply_const_units_conj' {n : ℕ} (hn : Even n)
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n)
    (hbφ : hochschildCoboundary R A M n φ = 0) (u : Aˣ) {e : A} (he : IsIdempotentElem e) :
    φ (fun _ ↦ ↑u⁻¹ * e * ↑u) = φ (fun _ ↦ e) := by
  -- Pass to `2 × 2` matrices, where conjugation by `!![0, u; -u⁻¹, 0]`, a product of three
  -- square-zero unipotents, moves the corner `e ⊕ 0` to the corner `0 ⊕ u⁻¹ e u`.
  let ψ := matrixCochainExtension (Fin 2) n φ
  have hψ : ψ ∈ cyclicCochains R (Matrix (Fin 2) (Fin 2) A) M n :=
    matrixCochainExtension_mem_cyclicCochains (Fin 2) n ⟨φ, hφ⟩
  have hbψ : hochschildCoboundary R (Matrix (Fin 2) (Fin 2) A) M n ψ = 0 := by
    rw [← matrixCochainExtension_hochschildCoboundary, hbφ, map_zero]
  have hsq (i j : Fin 2) (hij : i ≠ j) (x : A) : Matrix.single i j x * Matrix.single i j x = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _
  have hE₀ : IsIdempotentElem (Matrix.single (0 : Fin 2) (0 : Fin 2) e) := by
    rw [IsIdempotentElem, Matrix.single_mul_single_same, he.eq]
  obtain ⟨hE₁, h₁⟩ := apply_const_one_add_mul_mul_one_sub_eq hn hψ hbψ hE₀
    (hsq 0 1 zero_ne_one (u : A))
  obtain ⟨hE₂, h₂⟩ := apply_const_one_add_mul_mul_one_sub_eq hn hψ hbψ hE₁
    (hsq 1 0 one_ne_zero (-(↑u⁻¹ : A)))
  obtain ⟨-, h₃⟩ := apply_const_one_add_mul_mul_one_sub_eq hn hψ hbψ hE₂
    (hsq 0 1 zero_ne_one (u : A))
  have hconj : (1 + Matrix.single (0 : Fin 2) (1 : Fin 2) (u : A)) *
      ((1 + Matrix.single (1 : Fin 2) (0 : Fin 2) (-(↑u⁻¹ : A))) *
      ((1 + Matrix.single (0 : Fin 2) (1 : Fin 2) (u : A)) *
        Matrix.single (0 : Fin 2) (0 : Fin 2) e *
          (1 - Matrix.single (0 : Fin 2) (1 : Fin 2) (u : A))) *
      (1 - Matrix.single (1 : Fin 2) (0 : Fin 2) (-(↑u⁻¹ : A)))) *
        (1 - Matrix.single (0 : Fin 2) (1 : Fin 2) (u : A)) =
      Matrix.single (1 : Fin 2) (1 : Fin 2) (↑u⁻¹ * e * ↑u) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply, mul_add, add_mul, sub_mul,
        mul_sub, mul_assoc]
  rw [← matrixCochainExtension_single (Fin 2) (1 : Fin 2) n φ,
    ← matrixCochainExtension_single (Fin 2) (0 : Fin 2) n φ, ← hconj]
  exact h₃.trans (h₂.trans h₁)

/-- **Conjugation invariance.** Conjugating an idempotent `e` by a unit `u` preserves the value
`φ(e, …, e)` of a cyclic cocycle `φ` of even degree. -/
theorem apply_const_units_conj {n : ℕ} (hn : Even n)
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n)
    (hbφ : hochschildCoboundary R A M n φ = 0) (u : Aˣ) {e : A} (he : IsIdempotentElem e) :
    φ (fun _ ↦ ↑u * e * ↑u⁻¹) = φ (fun _ ↦ e) := by
  simpa only [inv_inv] using apply_const_units_conj' hn hφ hbφ u⁻¹ he

namespace cyclicCohomology

/-- **Polynomial homotopy invariance of the even pairing.** For an idempotent polynomial `e` with
coefficients in `A`, the even pairing with `e(t)` does not depend on the scalar `t`. -/
theorem evenPairing_eval_algebraMap_eq {e : A[X]} (he : IsIdempotentElem e) (s t : R)
    (hs : IsIdempotentElem (e.eval (algebraMap R A s)))
    (ht : IsIdempotentElem (e.eval (algebraMap R A t))) (m : ℕ) :
    evenPairing (R := R) (M := M) (e.eval (algebraMap R A s)) hs m =
      evenPairing (e.eval (algebraMap R A t)) ht m := by
  ext φ
  have hb := (mem_cyclicCocycles_iff R A M).1 φ.2
  simp only [LinearMap.coe_comp, Function.comp_apply, evenPairing_mk]
  rw [apply_const_eval_algebraMap_eq (even_two_mul m) φ.1.2 hb he s t]

/-- **Conjugation invariance of the even pairing.** Conjugating an idempotent by a unit does not
change its even pairing with cyclic cohomology. -/
theorem evenPairing_units_conj (u : Aˣ) {e : A} (he : IsIdempotentElem e)
    (hue : IsIdempotentElem (↑u * e * ↑u⁻¹)) (m : ℕ) :
    evenPairing (R := R) (M := M) (↑u * e * ↑u⁻¹) hue m = evenPairing e he m := by
  ext φ
  have hb := (mem_cyclicCocycles_iff R A M).1 φ.2
  simp only [LinearMap.coe_comp, Function.comp_apply, evenPairing_mk]
  rw [apply_const_units_conj (even_two_mul m) φ.1.2 hb u he]

end cyclicCohomology

end Homotopy

end TauCeti
