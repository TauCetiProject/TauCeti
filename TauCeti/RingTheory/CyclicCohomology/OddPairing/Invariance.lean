/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Eval.AlgebraMap
public import TauCeti.LinearAlgebra.Multilinear.Polynomial
public import TauCeti.RingTheory.CyclicCohomology.OddPairing.Basic

import TauCeti.Data.Fin.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Homotopy invariance and multiplicativity of the odd pairing

Let `φ` be a cyclic cocycle of odd degree `2m + 1` on a unital algebra `A`, and for an invertible
`u` write `f(u) = φ(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)` for the value entering Connes' odd pairing
`⟨[u], [φ]⟩`. This file shows that `f` is unchanged along polynomial paths of invertibles, that it
vanishes on square-zero unipotents `1 + N`, and that it is multiplicative,
`f(uv) = f(u) + f(v)`. Consequently the odd pairing is a homomorphism from the group of
invertibles, invariant under conjugation and vanishing on elementary matrices: these are the
relations through which it descends to algebraic `K₁ = GL_∞(A) / E_∞(A)`.

The argument has three steps.

* **Infinitesimal invariance.** Write `x = u⁻¹ - 1` and `y = u - 1`, which are quasi-inverse in
  both orders. A tangent vector `(x', y')` to this relation satisfies
  `y' + x' + x'y + xy' = 0`. Evaluating `bφ = 0` on `(z, x, y, …, x, y)` and telescoping the
  inner faces, which split because adjacent entries are quasi-inverse, gives
  `φ(z + zx, y, x, …, y) = φ(x, y, …, x, z + yz)`. For `z = x' + x'y` the two entries are `x'` and
  `-y'`, and cyclicity then shows that the derivative `∑ₖ φ(…, x' or y' in slot k, …)` vanishes
  (`TauCeti.linearDeriv_eq_zero_of_add_add_mul_eq_zero`).
* **Polynomial homotopy invariance.** For an invertible polynomial `u(X)` with coefficients in
  `A`, the zero-derivative principle
  `MultilinearMap.apply_eval_algebraMap_eq_of_linearDeriv_eq_zero` shows that `f(u(t))` does not
  depend on the scalar `t`. The path `t ↦ u(1 + tN)` for `N² = 0` then shows `f(u(1 + N)) = f(u)`.
* **Multiplicativity.** In `2 × 2` matrices over `A`, the block diagonal matrix `v ⊕ v⁻¹` is a
  product of six square-zero unipotents, so `(uv) ⊕ 1 = (u ⊕ v)(v ⊕ v⁻¹)` has the same value of
  the matrix extension `φ#Tr` as `u ⊕ v`. Matrix extension is additive on diagonal matrices, so
  `f(uv) = f(u) + f(v)`.

## Main results

* `TauCeti.linearDeriv_eq_zero_of_add_add_mul_eq_zero`: infinitesimal invariance of an odd-degree
  cyclic cocycle on alternating quasi-inverse tuples.
* `TauCeti.apply_units_eval_algebraMap_eq`: invariance along polynomial paths of invertibles.
* `TauCeti.apply_units_mul`: multiplicativity, `f(uv) = f(u) + f(v)`.
* `TauCeti.cyclicCohomology.oddPairing_map_evalAlgebraMapRingHom_eq`: polynomial homotopy
  invariance of the odd pairing.
* `TauCeti.cyclicCohomology.oddPairing_mul`, `TauCeti.cyclicCohomology.oddPairing_inv` and
  `TauCeti.cyclicCohomology.oddPairing_conj`: the odd pairing is a homomorphism on invertibles
  and is invariant under conjugation.
* `TauCeti.cyclicCohomology.oddPairing_eq_zero_of_val_eq_one_add` and
  `TauCeti.cyclicCohomology.oddPairing_eq_zero_of_val_eq_one_add_single`: the odd pairing
  vanishes on square-zero unipotents, in particular on elementary matrices.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §3.
* J.-L. Loday, *Cyclic Homology*, §8.3.
-/

public section

noncomputable section

namespace TauCeti

open Polynomial

section Infinitesimal

variable {R A M : Type*} [CommRing R] [NonUnitalRing A] [Module R A] [AddCommGroup M]
  [Module R M] {m : ℕ} {φ : MultilinearMap R (fun _ : Fin (2 * m + 2) ↦ A) M}

/-- Rotating an alternating tuple of even length swaps its two entries. -/
private theorem alternating_comp_finRotate_symm {α : Type*} (x y : α) :
    (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) ∘ (finRotate (2 * m + 2)).symm =
      fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then y else x := by
  funext k
  cases k using Fin.cases with
  | zero =>
    have h : (finRotate (2 * m + 2)).symm 0 = Fin.last (2 * m + 1) :=
      (Equiv.symm_apply_eq _).2 finRotate_last.symm
    simp [h]
  | succ k =>
    have h : (finRotate (2 * m + 2)).symm k.succ = k.castSucc :=
      (Equiv.symm_apply_eq _).2 (Fin.finRotate_castSucc k).symm
    by_cases hk : Even (k : ℕ) <;> simp [h, hk, Nat.even_add_one]

/-- A cyclic cochain of odd degree changes sign when the distinguished entry of an alternating
tuple moves one slot to the right and the two alternating entries are swapped. -/
private theorem apply_update_alternating_finRotate (hφ : φ ∈ cyclicCochains R A M (2 * m + 1))
    (x y v : A) (k : Fin (2 * m + 2)) :
    φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then y else x)
        (finRotate (2 * m + 2) k) v) =
      -φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) k v) := by
  have h := mem_cyclicCochains_iff.1 hφ
    (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) k v)
  rwa [Function.update_comp_equiv, Equiv.symm_symm, alternating_comp_finRotate_symm,
    (odd_two_mul_add_one m).neg_one_pow, neg_one_smul] at h

/-- On an alternating tuple, the value of a cyclic cochain of odd degree with one distinguished
entry depends only on the parity of the slot of that entry. -/
private theorem apply_update_alternating_eq (hφ : φ ∈ cyclicCochains R A M (2 * m + 1)) (v : A)
    (k : Fin (2 * m + 2)) (x y : A) :
    φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) k v) =
      if Even (k : ℕ) then
        φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) 0 v)
      else φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) 1 v) := by
  induction k using Fin.induction generalizing x y with
  | zero => simp
  | succ k ih =>
    have h₁ := apply_update_alternating_finRotate hφ y x v k.castSucc
    have h₀ := apply_update_alternating_finRotate hφ x y v 0
    have h₀' := apply_update_alternating_finRotate hφ y x v 0
    rw [Fin.finRotate_castSucc] at h₁
    simp only [finRotate_apply, zero_add] at h₀ h₀'
    rw [h₁, ih y x]
    by_cases hk : Even (k : ℕ)
    · simp [hk, Nat.even_add_one, h₀']
    · simp [hk, Nat.even_add_one, h₀]

/-- Moving the last entry of a tuple to the front changes the sign of a cyclic cochain of odd
degree. -/
private theorem apply_cons_init (hφ : φ ∈ cyclicCochains R A M (2 * m + 1))
    (a : Fin (2 * m + 2) → A) (w : A) :
    φ (Fin.cons (α := fun _ ↦ A) w (Fin.init a)) = -φ (Function.update a (Fin.last _) w) := by
  have h := mem_cyclicCochains_iff.1 hφ (Function.update a (Fin.last _) w)
  rw [(odd_two_mul_add_one m).neg_one_pow, neg_one_smul] at h
  rw [← h]
  congr 1
  funext k
  cases k using Fin.cases with
  | zero =>
    have h0 : (finRotate (2 * m + 2)).symm 0 = Fin.last (2 * m + 1) :=
      (Equiv.symm_apply_eq _).2 finRotate_last.symm
    simp [h0]
  | succ k =>
    have hk : (finRotate (2 * m + 2)).symm k.succ = k.castSucc :=
      (Equiv.symm_apply_eq _).2 (Fin.finRotate_castSucc k).symm
    simp [hk, Fin.init]

/-- The inner face of `(z, a₀, …, aₙ₊₁)` multiplying two quasi-inverse entries `aᵢ`, `aᵢ₊₁` splits
into the values on the tuples deleting `aᵢ₊₁` or `aᵢ`. -/
private theorem apply_contractNth_succ_cons {n : ℕ}
    (ψ : MultilinearMap R (fun _ : Fin (n + 2) ↦ A) M) (z : A) (a : Fin (n + 2) → A)
    (i : Fin (n + 1)) (h : a i.succ + a i.castSucc + a i.castSucc * a i.succ = 0) :
    ψ (Fin.contractNth i.succ.castSucc (· * ·) (Fin.cons z a : Fin (n + 3) → A)) =
      -(ψ (Fin.cons z (Fin.removeNth i.succ a)) + ψ (Fin.cons z (Fin.removeNth i.castSucc a))) := by
  have hc : Fin.contractNth i.succ.castSucc (· * ·) (Fin.cons z a : Fin (n + 3) → A) =
      Fin.cons z (Fin.contractNth i.castSucc (· * ·) a) := by
    funext k
    cases k using Fin.cases <;> simp [Fin.contractNth]
  rw [hc, Fin.contractNth_castSucc_eq_update_removeNth_succ, Fin.cons_update,
    ψ.map_update_mul_of_add_add_mul_eq_zero _ _ h, ← Fin.cons_update, ← Fin.cons_update,
    Fin.update_removeNth_succ_eq_removeNth_castSucc,
    Function.update_eq_self_iff.2 (by simp [Fin.removeNth_apply])]

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Evaluating `bφ = 0` on `(z, x, y, …, x, y)` for quasi-inverse `x` and `y`: the inner faces
telescope, leaving `φ(z + zx, y, x, …, y) = φ(x, z + yz, x, …, y)`. -/
private theorem apply_update_alternating_zero_eq_apply_update_alternating_one
    (hφ : φ ∈ cyclicCochains R A M (2 * m + 1))
    (hbφ : hochschildCoboundary R A M (2 * m + 1) φ = 0) {x y : A} (hxy : y + x + x * y = 0)
    (hyx : x + y + y * x = 0) (z : A) :
    φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) 0
        (z + z * x)) =
      φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) 1
        (z + y * z)) := by
  set a : Fin (2 * m + 2) → A := fun k ↦ if Even (k : ℕ) then x else y
  -- Adjacent entries of `a` are quasi-inverse.
  have hadj (i : Fin (2 * m + 1)) : a i.succ + a i.castSucc + a i.castSucc * a i.succ = 0 := by
    by_cases hi : Even (i : ℕ) <;> simp [a, hi, Nat.even_add_one, hxy, hyx]
  have hb := congrArg (fun ψ ↦ ψ (Fin.cons z a)) hbφ
  simp only [zero_apply] at hb
  rw [hochschildCoboundary_apply_eq_sum_contractNth_add, Fin.sum_univ_succ] at hb
  -- The first face multiplies `z` into the first entry.
  have h0 : Fin.contractNth (0 : Fin (2 * m + 2)).castSucc (· * ·)
      (Fin.cons z a : Fin (2 * m + 3) → A) = Function.update a 0 (z * x) := by
    funext k
    cases k using Fin.cases <;> simp [Fin.contractNth, a]
  -- The inner faces telescope.
  set g : Fin (2 * m + 2) → M := fun j ↦ (-1 : ℤ) ^ (j : ℕ) • φ (Fin.cons z (Fin.removeNth j a))
    with hg
  have hinner (i : Fin (2 * m + 1)) :
      (-1 : ℤ) ^ ((i.succ : Fin (2 * m + 2)) : ℕ) •
        φ (Fin.contractNth i.succ.castSucc (· * ·) (Fin.cons z a : Fin (2 * m + 3) → A)) =
        g i.castSucc - g i.succ := by
    rw [apply_contractNth_succ_cons φ z a i (hadj i)]
    simp only [hg, Fin.val_succ, Fin.val_castSucc, pow_succ, mul_neg_one, neg_smul, smul_neg,
      smul_add]
    abel
  have htel : ∑ i : Fin (2 * m + 1), (g i.castSucc - g i.succ) = g 0 - g (Fin.last _) := by
    have hs := Fin.sum_univ_succ g
    rw [Fin.sum_univ_castSucc] at hs
    rw [Finset.sum_sub_distrib]
    linear_combination (norm := abel) hs
  have hg0 : g 0 = φ (Function.update a 0 z) := by
    simp only [hg, Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero]
    congr 1
    conv_rhs => rw [← Fin.cons_self_tail a]
    rw [Fin.update_cons_zero]
  have hglast : g (Fin.last _) = φ (Function.update a (Fin.last _) z) := by
    simp only [hg, Fin.val_last, Fin.removeNth_last, apply_cons_init hφ,
      (odd_two_mul_add_one m).neg_one_pow, neg_one_smul, neg_neg]
  -- The last face multiplies the last entry `y` into `z`.
  have hl : (Fin.cons ((Fin.cons z a : Fin (2 * m + 3) → A) (Fin.last (2 * m + 2)) *
      (Fin.cons z a : Fin (2 * m + 3) → A) 0)
      fun k : Fin (2 * m + 1) ↦ (Fin.cons z a : Fin (2 * m + 3) → A) k.castSucc.succ) =
      Fin.cons (α := fun _ ↦ A) (y * z) (Fin.init a) := by
    have hlast : (Fin.cons z a : Fin (2 * m + 3) → A) (Fin.last (2 * m + 2)) = y := by
      rw [← Fin.succ_last, Fin.cons_succ]
      simp [a]
    -- The remaining entries are those of `Fin.init a`, by definition.
    rw [hlast]
    rfl
  simp only [Fin.val_zero, pow_zero, one_smul, h0, hinner, htel, hg0, hglast, hl,
    apply_cons_init hφ, (show Even (2 * m + 1 + 1) from ⟨m + 1, by ring⟩).neg_one_pow,
    one_smul] at hb
  -- The last slot has odd index, so it may be replaced by slot `1`.
  have hlast := apply_update_alternating_eq hφ (z + y * z) (Fin.last _) x y
  simp only [Fin.val_last, Nat.not_even_iff_odd.2 (odd_two_mul_add_one m), ↓reduceIte]
    at hlast
  rw [← hlast, φ.map_update_add, φ.map_update_add, ← sub_eq_zero, ← hb]
  abel

/-- **Infinitesimal invariance on alternating quasi-inverse tuples.** Let `φ` be a cyclic
cocycle of odd degree `2m + 1`, and let `x` and `y` be quasi-inverse in both orders. If `(x', y')`
is tangent to this relation, `y' + x' + x'y + xy' = 0`, then the derivative of `φ` at
`(x, y, …, x, y)` in the direction `(x', y', …, x', y')` vanishes. -/
theorem linearDeriv_eq_zero_of_add_add_mul_eq_zero (hφ : φ ∈ cyclicCochains R A M (2 * m + 1))
    (hbφ : hochschildCoboundary R A M (2 * m + 1) φ = 0) {x y x' y' : A}
    (hxy : y + x + x * y = 0) (hyx : x + y + y * x = 0) (h' : y' + x' + x' * y + x * y' = 0) :
    φ.linearDeriv (fun k ↦ if Even (k : ℕ) then x else y)
      (fun k ↦ if Even (k : ℕ) then x' else y') = 0 := by
  -- With `z = x' + x'y`, the two entries of the telescoped identity are `x'` and `-y'`.
  set z := x' + x' * y
  have hzx : z + z * x = x' := by
    have h := congrArg (x' * ·) hyx
    simp only [mul_add, mul_zero] at h
    rw [← sub_eq_zero, ← h]
    simp only [z, add_mul, mul_assoc]
    abel
  have hzy : z + y * z = -y' := by
    have hz : z = -y' - x * y' := by
      rw [← sub_eq_zero, ← h']
      simp only [z]
      abel
    have h := congrArg (· * y') hyx
    simp only [add_mul, zero_mul] at h
    rw [hz, ← sub_eq_zero, ← neg_eq_zero, ← h]
    simp only [mul_sub, mul_neg, mul_assoc]
    abel
  have hpair : φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) 1 y') =
      -φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) 0 x') := by
    have h := apply_update_alternating_zero_eq_apply_update_alternating_one hφ hbφ hxy hyx z
    rw [hzx, hzy, φ.map_update_neg] at h
    rw [h, neg_neg]
  rw [MultilinearMap.linearDeriv_apply]
  have hterm (k : Fin (2 * m + 2)) :
      φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) k
        (if Even (k : ℕ) then x' else y')) =
        (-1 : ℤ) ^ (k : ℕ) •
          φ (Function.update (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then x else y) 0 x') := by
    rw [apply_update_alternating_eq hφ]
    by_cases hk : Even (k : ℕ)
    · simp [hk, hk.neg_one_pow]
    · simp [hk, (Nat.not_even_iff_odd.1 hk).neg_one_pow, hpair]
  simp only [hterm, ← Finset.sum_smul]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (-1 : ℤ) ^ i) (2 * m + 2), neg_one_geom_sum]
  simp [show Even (2 * m + 2) from ⟨m + 1, by ring⟩]

end Infinitesimal

section Homotopy

variable {R A M : Type*} [Field R] [CharZero R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M] {m : ℕ} {φ : MultilinearMap R (fun _ : Fin (2 * m + 2) ↦ A) M}

/-- **Polynomial homotopy invariance.** Let `φ` be a cyclic cocycle of odd degree `2m + 1` and
`u` an invertible polynomial with coefficients in `A`. Then
`φ(u(t)⁻¹ - 1, u(t) - 1, …, u(t)⁻¹ - 1, u(t) - 1)` does not depend on the scalar `t`. -/
theorem apply_units_eval_algebraMap_eq (hφ : φ ∈ cyclicCochains R A M (2 * m + 1))
    (hbφ : hochschildCoboundary R A M (2 * m + 1) φ = 0) (u : (A[X])ˣ) (s t : R) :
    φ (fun k ↦ if Even (k : ℕ) then (↑u⁻¹ : A[X]).eval (algebraMap R A s) - 1
      else (↑u : A[X]).eval (algebraMap R A s) - 1) =
      φ (fun k ↦ if Even (k : ℕ) then (↑u⁻¹ : A[X]).eval (algebraMap R A t) - 1
        else (↑u : A[X]).eval (algebraMap R A t) - 1) := by
  set p : Fin (2 * m + 2) → A[X] := fun k ↦ if Even (k : ℕ) then ↑u⁻¹ - 1 else ↑u - 1
  have hp (r : R) : (fun k ↦ (p k).eval (algebraMap R A r)) = fun k : Fin (2 * m + 2) ↦
      if Even (k : ℕ) then (↑u⁻¹ : A[X]).eval (algebraMap R A r) - 1
      else (↑u : A[X]).eval (algebraMap R A r) - 1 := by
    funext k
    by_cases hk : Even (k : ℕ) <;> simp [p, hk]
  rw [← hp, ← hp]
  refine φ.apply_eval_algebraMap_eq_of_linearDeriv_eq_zero p (fun r ↦ ?_) s t
  have hd (k : Fin (2 * m + 2)) : (p k).derivative.eval (algebraMap R A r) =
      if Even (k : ℕ) then (derivative ↑u⁻¹ : A[X]).eval (algebraMap R A r)
      else (derivative ↑u : A[X]).eval (algebraMap R A r) := by
    by_cases hk : Even (k : ℕ) <;> simp [p, hk]
  rw [hp, funext hd]
  -- Evaluation at the central element `algebraMap R A r` is a ring homomorphism.
  simp only [← evalAlgebraMapRingHom_apply A r]
  set ev := evalAlgebraMapRingHom A r
  have hinv : ev ↑u⁻¹ * ev ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hinv' : ev ↑u * ev ↑u⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  -- Differentiating `u⁻¹ u = 1` gives the tangent relation.
  have hder : ev (derivative ↑u⁻¹) * ev ↑u + ev ↑u⁻¹ * ev (derivative ↑u) = 0 := by
    rw [← map_mul, ← map_mul, ← map_add, ← derivative_mul, Units.inv_mul, derivative_one,
      map_zero]
  refine linearDeriv_eq_zero_of_add_add_mul_eq_zero hφ hbφ ?_ ?_ ?_
  · simp only [sub_mul, mul_sub, hinv, mul_one, one_mul]
    abel
  · simp only [sub_mul, mul_sub, hinv', mul_one, one_mul]
    abel
  · rw [← hder]
    simp only [sub_mul, mul_sub, mul_one, one_mul]
    abel

/-- Multiplying an invertible on the right by a square-zero unipotent `1 + N` does not change the
value of an odd-degree cyclic cocycle on its alternating tuple. -/
private theorem apply_units_mul_eq_of_val_eq_one_add
    (hφ : φ ∈ cyclicCochains R A M (2 * m + 1))
    (hbφ : hochschildCoboundary R A M (2 * m + 1) φ = 0) (u e : Aˣ) {N : A}
    (he : (e : A) = 1 + N) (hN : N * N = 0) :
    φ (fun k ↦ if Even (k : ℕ) then ↑(u * e)⁻¹ - 1 else ↑(u * e) - 1) =
      φ (fun k ↦ if Even (k : ℕ) then ↑u⁻¹ - 1 else ↑u - 1) := by
  have he' : ((e⁻¹ : Aˣ) : A) = 1 - N :=
    Units.inv_eq_of_mul_eq_one_right (by rw [he]; simp [add_mul, mul_sub, hN])
  -- The polynomial path `t ↦ u (1 + tN)` of invertibles joins `u` to `u (1 + N)`.
  have hX : C N * X * (C N * X) = (0 : A[X]) := by
    rw [(commute_X (C N)).mul_mul_mul_comm, ← C_mul, hN, C_0, zero_mul]
  have h₁ : (1 + C N * X) * (1 - C N * X) = (1 : A[X]) := by
    rw [add_mul, one_mul, mul_sub, mul_one, hX, sub_zero, sub_add_cancel]
  have h₂ : (1 - C N * X) * (1 + C N * X) = (1 : A[X]) := by
    rw [sub_mul, one_mul, mul_add, mul_one, hX, add_zero, add_sub_cancel_right]
  let U : (A[X])ˣ :=
    { val := C ↑u * (1 + C N * X)
      inv := (1 - C N * X) * C ↑u⁻¹
      val_inv := by
        rw [mul_assoc, ← mul_assoc (1 + C N * X), h₁, one_mul, ← C_mul, Units.mul_inv, C_1]
      inv_val := by
        rw [mul_assoc, ← mul_assoc (C _) (C _), ← C_mul, Units.inv_mul, C_1, one_mul, h₂] }
  have h := apply_units_eval_algebraMap_eq hφ hbφ U 1 0
  simp only [← evalAlgebraMapRingHom_apply A] at h
  simp only [U, Units.inv_mk, map_mul, map_add, map_sub, map_one, evalAlgebraMapRingHom_apply,
    eval_C, eval_X, map_zero, mul_zero, add_zero, sub_zero, mul_one, one_mul] at h
  simpa only [mul_inv_rev, Units.val_mul, he, he'] using h

/-- **Multiplicativity.** For a cyclic cocycle `φ` of odd degree `2m + 1`, the value
`f(u) = φ(u⁻¹ - 1, u - 1, …, u⁻¹ - 1, u - 1)` satisfies `f(uv) = f(u) + f(v)`. -/
theorem apply_units_mul (hφ : φ ∈ cyclicCochains R A M (2 * m + 1))
    (hbφ : hochschildCoboundary R A M (2 * m + 1) φ = 0) (u v : Aˣ) :
    φ (fun k ↦ if Even (k : ℕ) then ↑(u * v)⁻¹ - 1 else ↑(u * v) - 1) =
      φ (fun k ↦ if Even (k : ℕ) then ↑u⁻¹ - 1 else ↑u - 1) +
        φ (fun k ↦ if Even (k : ℕ) then ↑v⁻¹ - 1 else ↑v - 1) := by
  -- Pass to `2 × 2` matrices, where the matrix extension `ψ = φ#Tr` is again a cyclic cocycle.
  let ψ := matrixCochainExtension (Fin 2) (2 * m + 1) φ
  have hψ : ψ ∈ cyclicCochains R (Matrix (Fin 2) (Fin 2) A) M (2 * m + 1) :=
    matrixCochainExtension_mem_cyclicCochains (Fin 2) (2 * m + 1) ⟨φ, hφ⟩
  have hbψ : hochschildCoboundary R (Matrix (Fin 2) (Fin 2) A) M (2 * m + 1) ψ = 0 := by
    rw [← matrixCochainExtension_hochschildCoboundary, hbφ, map_zero]
  -- The block diagonal invertible `a ⊕ b`.
  let diag (a b : Aˣ) : (Matrix (Fin 2) (Fin 2) A)ˣ :=
    { val := !![(a : A), 0; 0, b]
      inv := !![(↑a⁻¹ : A), 0; 0, ↑b⁻¹]
      val_inv := by simp [Matrix.one_fin_two]
      inv_val := by simp [Matrix.one_fin_two] }
  -- On block diagonal invertibles, the value of `ψ` is the sum of the values of `φ`.
  have hdiag (a b : Aˣ) :
      ψ (fun k ↦ if Even (k : ℕ) then ↑(diag a b)⁻¹ - 1 else ↑(diag a b) - 1) =
        φ (fun k ↦ if Even (k : ℕ) then ↑a⁻¹ - 1 else ↑a - 1) +
          φ (fun k ↦ if Even (k : ℕ) then ↑b⁻¹ - 1 else ↑b - 1) := by
    have h : (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ)
        then (↑(diag a b)⁻¹ : Matrix (Fin 2) (Fin 2) A) - 1 else ↑(diag a b) - 1) =
        fun k : Fin (2 * m + 2) ↦ Matrix.diagonal ![if Even (k : ℕ) then (↑a⁻¹ : A) - 1
          else ↑a - 1, if Even (k : ℕ) then (↑b⁻¹ : A) - 1 else ↑b - 1] := by
      funext k
      ext i j
      fin_cases i <;> fin_cases j <;> split_ifs <;> simp [diag]
    rw [h, matrixCochainExtension_diagonal, Fin.sum_univ_two]
    rfl
  -- The square-zero unipotents `1 + N` with `N` strictly upper or lower triangular.
  let upper (c : A) : (Matrix (Fin 2) (Fin 2) A)ˣ :=
    { val := !![1, c; 0, 1]
      inv := !![1, -c; 0, 1]
      val_inv := by simp [Matrix.one_fin_two]
      inv_val := by simp [Matrix.one_fin_two] }
  let lower (c : A) : (Matrix (Fin 2) (Fin 2) A)ˣ :=
    { val := !![1, 0; c, 1]
      inv := !![1, 0; -c, 1]
      val_inv := by simp [Matrix.one_fin_two]
      inv_val := by simp [Matrix.one_fin_two] }
  have hupper (w : (Matrix (Fin 2) (Fin 2) A)ˣ) (c : A) :
      ψ (fun k ↦ if Even (k : ℕ) then ↑(w * upper c)⁻¹ - 1 else ↑(w * upper c) - 1) =
        ψ (fun k ↦ if Even (k : ℕ) then ↑w⁻¹ - 1 else ↑w - 1) :=
    apply_units_mul_eq_of_val_eq_one_add hψ hbψ w (upper c) (N := !![0, c; 0, 0])
      (by simp [upper, Matrix.one_fin_two]) (by ext i j; fin_cases i <;> fin_cases j <;> simp)
  have hlower (w : (Matrix (Fin 2) (Fin 2) A)ˣ) (c : A) :
      ψ (fun k ↦ if Even (k : ℕ) then ↑(w * lower c)⁻¹ - 1 else ↑(w * lower c) - 1) =
        ψ (fun k ↦ if Even (k : ℕ) then ↑w⁻¹ - 1 else ↑w - 1) :=
    apply_units_mul_eq_of_val_eq_one_add hψ hbψ w (lower c) (N := !![0, 0; c, 0])
      (by simp [lower, Matrix.one_fin_two]) (by ext i j; fin_cases i <;> fin_cases j <;> simp)
  -- `(uv) ⊕ 1 = (u ⊕ v) (v ⊕ v⁻¹)`, where `v ⊕ v⁻¹` is a product of six unipotents.
  have hfac : diag (u * v) 1 = diag u v * upper ↑v * lower (-↑v⁻¹) * upper ↑v * upper (-1) *
      lower 1 * upper (-1) := by
    ext : 1
    simp [diag, upper, lower, mul_assoc]
  have h := hdiag (u * v) 1
  rw [hfac, hupper, hlower, hupper, hupper, hlower, hupper, hdiag] at h
  have h₁ : φ (fun k : Fin (2 * m + 2) ↦ if Even (k : ℕ) then ↑(1 : Aˣ)⁻¹ - 1 else ↑(1 : Aˣ) - 1) =
      0 := by
    simp [← Pi.zero_def]
  rwa [h₁, add_zero, eq_comm] at h

end Homotopy

namespace cyclicCohomology

variable {A M : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]

/-- **Polynomial homotopy invariance of the odd pairing.** For an invertible polynomial `u` with
coefficients in `A`, the odd pairing with `u(t)` does not depend on the scalar `t`. -/
theorem oddPairing_map_evalAlgebraMapRingHom_eq (u : (A[X])ˣ) (s t : ℂ) (m : ℕ) :
    oddPairing (M := M) (Units.map (evalAlgebraMapRingHom A s : A[X] →* A) u) m =
      oddPairing (Units.map (evalAlgebraMapRingHom A t : A[X] →* A) u) m := by
  ext φ
  have hb := (mem_cyclicCocycles_iff ℂ A M).1 φ.2
  simp only [LinearMap.coe_comp, Function.comp_apply, oddPairing_mk, Units.coe_map,
    Units.coe_map_inv, MonoidHom.coe_ofClass, evalAlgebraMapRingHom_apply]
  rw [apply_units_eval_algebraMap_eq φ.1.2 hb u s t]

/-- **Multiplicativity of the odd pairing**: `⟨[uv], [φ]⟩ = ⟨[u], [φ]⟩ + ⟨[v], [φ]⟩`. -/
@[simp]
theorem oddPairing_mul (u v : Aˣ) (m : ℕ) :
    oddPairing (M := M) (u * v) m = oddPairing u m + oddPairing v m := by
  ext φ
  have hb := (mem_cyclicCocycles_iff ℂ A M).1 φ.2
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply, oddPairing_mk,
    apply_units_mul φ.1.2 hb u v, smul_add]

/-- The odd pairing of the inverse is the negative of the odd pairing. -/
@[simp]
theorem oddPairing_inv (u : Aˣ) (m : ℕ) :
    oddPairing (M := M) u⁻¹ m = -oddPairing u m := by
  have h := oddPairing_mul (M := M) u u⁻¹ m
  rw [mul_inv_cancel, oddPairing_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- **Conjugation invariance of the odd pairing.** Conjugating an invertible by another invertible
does not change its odd pairing with cyclic cohomology. -/
theorem oddPairing_conj (g u : Aˣ) (m : ℕ) :
    oddPairing (M := M) (g * u * g⁻¹) m = oddPairing u m := by
  rw [oddPairing_mul, oddPairing_mul, oddPairing_inv]
  abel

/-- The odd pairing vanishes on a square-zero unipotent `1 + N`. -/
theorem oddPairing_eq_zero_of_val_eq_one_add (e : Aˣ) {N : A} (he : (e : A) = 1 + N)
    (hN : N * N = 0) (m : ℕ) : oddPairing (M := M) e m = 0 := by
  ext φ
  have hb := (mem_cyclicCocycles_iff ℂ A M).1 φ.2
  have h := apply_units_mul_eq_of_val_eq_one_add φ.1.2 hb 1 e he hN
  rw [one_mul] at h
  simp only [LinearMap.coe_comp, Function.comp_apply, oddPairing_mk, h, LinearMap.zero_apply]
  simp [← Pi.zero_def]

/-- **Vanishing of the odd pairing on elementary matrices**: the odd pairing of an invertible
matrix `1 + c Eᵢⱼ` with `i ≠ j` vanishes. -/
theorem oddPairing_eq_zero_of_val_eq_one_add_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : (Matrix ι ι A)ˣ) {i j : ι} (hij : i ≠ j) {c : A}
    (he : (e : Matrix ι ι A) = 1 + Matrix.single i j c) (m : ℕ) :
    oddPairing (M := M) e m = 0 :=
  oddPairing_eq_zero_of_val_eq_one_add e he (Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _)
    m

end cyclicCohomology


end TauCeti
