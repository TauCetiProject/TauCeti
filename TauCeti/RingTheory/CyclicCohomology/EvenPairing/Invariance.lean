/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import TauCeti.RingTheory.CyclicCohomology.EvenPairing.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.GeomSum
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
  any slot.
* **Polynomial homotopy invariance.** For an idempotent `e(X)` with coefficients in `A`, the
  derivative of `t ↦ φ(e(t), …, e(t))` is a sum of such infinitesimal terms, because
  `e′ = e e′ + e′ e`. By the zero-derivative principle of
  `MultilinearMap.apply_eval_algebraMap_eq_of_sum_update_derivative_eq_zero`, it is constant.
* **Conjugation invariance.** For `N² = 0` the path `t ↦ (1 + tN) e (1 - tN)` joins `e` to
  `(1 + N) e (1 - N)`. In `2 × 2` matrices, conjugating the corner `e ⊕ 0` by
  `!![0, u; -u⁻¹, 0]`, a product of three such unipotents, gives the corner `0 ⊕ u⁻¹ e u`; matrix
  extension `φ#Tr` recovers `φ` on either corner.

Applied to the algebra `Matrix ι ι A`, the conjugation statements cover conjugation of idempotent
matrices by invertible matrices.

## Main results

* `TauCeti.apply_update_const_eq_zero_of_isIdempotentElem`: an even-degree cyclic cocycle vanishes
  on `(e, …, y, …, e)` when `y` is tangent to the idempotents at `e`.
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

section Rotation

variable {R A M : Type*} [Semiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- In even degree, a cyclic cochain takes the same value when the single distinguished entry of
an otherwise constant tuple moves to the first slot. -/
private theorem apply_update_const_eq_apply_update_const_zero {n : ℕ} (hn : Even n)
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n)
    (e z : A) (k : Fin (n + 1)) :
    φ (Function.update (fun _ ↦ e) k z) = φ (Function.update (fun _ ↦ e) 0 z) := by
  induction k using Fin.induction with
  | zero => rfl
  | succ k ih =>
    have h := mem_cyclicCochains_iff.1 hφ (Function.update (fun _ ↦ e) k.castSucc z)
    rw [Function.update_comp_equiv, Equiv.symm_symm, hn.neg_one_pow, one_smul] at h
    rw [← ih, ← h]
    congr 2
    exact Fin.ext (by simp)

end Rotation

section Infinitesimal

variable {R A M : Type*} [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- **Infinitesimal invariance of the even pairing.** Let `φ` be a cyclic cocycle of even degree
and `e` an idempotent. If `y` is tangent to the idempotents at `e`, that is `e y + y e = y`, then
`φ` vanishes on the tuple `(e, …, e)` with one entry replaced by `y`. -/
theorem apply_update_const_eq_zero_of_isIdempotentElem {n : ℕ} (hn : Even n)
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n)
    (hbφ : hochschildCoboundary R A M n φ = 0) {e y : A} (he : IsIdempotentElem e)
    (hy : e * y + y * e = y) (k : Fin (n + 1)) :
    φ (Function.update (fun _ ↦ e) k y) = 0 := by
  rw [apply_update_const_eq_apply_update_const_zero hn hφ]
  -- Tangency forces `e y e = 0`, so `y = x e - e x` for `x = y e - e y`.
  have hey : e * y * e = 0 := by
    have h : e * y * e + e * y * e = e * y * e := by
      calc e * y * e + e * y * e = e * (e * y + y * e) * e := by
            rw [mul_add, add_mul, ← mul_assoc e e y, he.eq, ← mul_assoc e y e,
              mul_assoc (e * y) e e, he.eq]
        _ = e * y * e := by rw [hy]
    simpa using h
  set x := y * e - e * y
  have hxy : x * e - e * x = y := by
    simp only [x, sub_mul, mul_sub, mul_assoc, he.eq]
    rw [← mul_assoc e y e, hey, ← mul_assoc, he.eq, sub_zero, zero_sub, sub_neg_eq_add, add_comm,
      hy]
  -- Evaluate `bφ = 0` on `(x, e, …, e)`: the middle faces cancel in even degree.
  have hb := congrArg (fun ψ ↦ ψ (Fin.cons x fun _ ↦ e)) hbφ
  simp only [hochschildCoboundary_apply_eq_sum_contractNth_add, Fin.sum_univ_succ] at hb
  have h0 : Fin.contractNth (0 : Fin (n + 1)).castSucc (· * ·)
      (Fin.cons x fun _ ↦ e : Fin (n + 2) → A) = Function.update (fun _ ↦ e) 0 (x * e) := by
    funext k
    cases k using Fin.cases <;> simp [Fin.contractNth]
  have hj (j : Fin n) : Fin.contractNth j.succ.castSucc (· * ·)
      (Fin.cons x fun _ ↦ e : Fin (n + 2) → A) = Function.update (fun _ ↦ e) 0 x := by
    funext k
    cases k using Fin.cases <;> simp [Fin.contractNth, he.eq]
  have hl : (Fin.cons ((Fin.cons x fun _ ↦ e : Fin (n + 2) → A) (Fin.last (n + 1)) *
      (Fin.cons x fun _ ↦ e : Fin (n + 2) → A) 0)
      fun k : Fin n ↦ (Fin.cons x fun _ ↦ e : Fin (n + 2) → A) k.castSucc.succ) =
      Function.update (fun _ ↦ e) 0 (e * x) := by
    funext k
    cases k using Fin.cases <;> simp
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, h0, hj, hl, zero_apply] at hb
  rw [← Finset.sum_smul, Fin.sum_univ_eq_sum_range (fun i ↦ (-1 : ℤ) ^ (i + 1)) n] at hb
  simp only [pow_succ, mul_neg_one, Finset.sum_neg_distrib, neg_one_geom_sum, hn, ↓reduceIte,
    neg_zero, zero_smul, add_zero, (hn.add_one).neg_one_pow, neg_one_smul] at hb
  rwa [← hxy, φ.map_update_sub, sub_eq_add_neg]

end Infinitesimal

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
  refine φ.apply_eval_algebraMap_eq_of_sum_update_derivative_eq_zero (fun _ ↦ e) (fun r ↦ ?_) s t
  -- Evaluation at the central element `algebraMap R A r` is a ring homomorphism.
  let ev : A[X] →+* A :=
    eval₂RingHom' (RingHom.id A) (algebraMap R A r) fun a ↦ Algebra.commute_algebraMap_right r a
  have hev (q : A[X]) : ev q = q.eval (algebraMap R A r) := eval₂_id
  -- Differentiating `e = e * e` shows that `e′` is tangent to the idempotents at `e`.
  have hd : derivative e = derivative e * e + e * derivative e := by
    conv_lhs => rw [← he.eq]
    exact derivative_mul
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  refine apply_update_const_eq_zero_of_isIdempotentElem hn hφ hbφ (e := ev e) (he.map ev) ?_ k
  rw [← hev, ← map_mul, ← map_mul, ← map_add, add_comm, ← hd]

/-- Conjugating an idempotent by a square-zero unipotent `1 + N`, whose inverse is `1 - N`, gives an
idempotent. -/
private theorem isIdempotentElem_one_add_mul_mul_one_sub {B : Type*} [Ring B] {E N : B}
    (hE : IsIdempotentElem E) (hN : N * N = 0) : IsIdempotentElem ((1 + N) * E * (1 - N)) := by
  have hinv : (1 - N) * (1 + N) = 1 := by
    rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, hN, add_zero, add_sub_cancel_right]
  rw [IsIdempotentElem]
  calc (1 + N) * E * (1 - N) * ((1 + N) * E * (1 - N))
      = (1 + N) * E * ((1 - N) * (1 + N)) * E * (1 - N) := by simp only [mul_assoc]
    _ = (1 + N) * E * (1 - N) := by rw [hinv, mul_one, mul_assoc _ E E, hE.eq]

/-- Conjugating an idempotent by a square-zero unipotent `1 + N` preserves the value of an
even-degree cyclic cocycle on constant tuples. -/
private theorem apply_const_one_add_mul_mul_one_sub_eq {n : ℕ} (hn : Even n)
    {φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M} (hφ : φ ∈ cyclicCochains R A M n)
    (hbφ : hochschildCoboundary R A M n φ = 0) {e N : A} (he : IsIdempotentElem e)
    (hN : N * N = 0) :
    IsIdempotentElem ((1 + N) * e * (1 - N)) ∧
      φ (fun _ ↦ (1 + N) * e * (1 - N)) = φ (fun _ ↦ e) := by
  refine ⟨isIdempotentElem_one_add_mul_mul_one_sub he hN, ?_⟩
  -- The polynomial path `t ↦ (1 + tN) e (1 - tN)` of idempotents joins `e` to `(1 + N) e (1 - N)`.
  have hX : C N * X * (C N * X) = (0 : A[X]) := by
    rw [mul_assoc, ← mul_assoc X, (commute_X (C N)).eq, ← mul_assoc, ← mul_assoc, ← C_mul, hN,
      C_0, zero_mul, zero_mul]
  have hP : IsIdempotentElem ((1 + C N * X) * C e * (1 - C N * X)) := by
    refine isIdempotentElem_one_add_mul_mul_one_sub ?_ hX
    rw [IsIdempotentElem, ← C_mul, he.eq]
  have h := apply_const_eval_algebraMap_eq hn hφ hbφ hP 1 0
  let ev (r : R) : A[X] →+* A :=
    eval₂RingHom' (RingHom.id A) (algebraMap R A r) fun a ↦ Algebra.commute_algebraMap_right r a
  have hev (r : R) (q : A[X]) : q.eval (algebraMap R A r) = ev r q := eval₂_id.symm
  rw [hev, hev] at h
  simpa only [map_mul, map_add, map_sub, map_one, ev, eval₂RingHom'_apply, eval₂_C, eval₂_X,
    RingHom.id_apply, map_zero, mul_zero, mul_one, one_mul, add_zero, sub_zero] using h

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
