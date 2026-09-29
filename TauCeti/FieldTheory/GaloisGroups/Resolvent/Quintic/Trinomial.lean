/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Homogeneous
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quintic.Orbit

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The resolvent sextic of a quintic trinomial

For a quintic `X⁵ + aX + b` over any commutative ring, the specialization of Dummit's `F₂₀`
resolvent specification is

`X⁶ + 8aX⁵ + 40a²X⁴ + 160a³X³ + 400a⁴X² + (512a⁵ - 3125b⁴)X + (256a⁶ - 9375ab⁴)`.

This is formula (2′) of Dummit's *Solving solvable quintics*. Here it is a theorem about the
orbit-product definition of `TauCeti.resolventSextic`, not a definition: it checks the
specification, the symmetric descent and the Vieta substitution against the source. Its
instances give the resolvent sextics of the trinomials used as worked examples, such as
`X⁵ - 5X - 12`, whose sextic has the integral root `40`.

The proof does not expand the orbit product. Dummit's invariant is homogeneous of degree four,
so the coefficient of `X ^ k` in its integral orbit product is weighted homogeneous of weight
`4 (6 - k)` when the variable standing for `eᵢ₊₁` has weight `i + 1`. At `X⁵ + aX + b` the
elementary symmetric polynomials `e₁, e₂, e₃` vanish and `e₄ = a`, `e₅ = -b`, so only the
monomials `e₄ⁱ e₅ʲ` with `4i + 5j = 4 (6 - k)` survive. This leaves eight integral constants,
independent of `a` and `b`. They are read off from two quintics whose roots are explicit complex
numbers: `X⁵ - X`, whose sextic is `(X - 2)⁴ (X² + 16)`, fixes the six constants in front of
powers of `a`, and the two real orbit values `190 ± 12√31` at the roots of
`X⁵ - 41X + 120 = (X + 3)(X² - 4X + 5)(X² + X + 8)` fix the two constants in front of `b⁴`.

## Main results

* `TauCeti.quinticF20Spec_specialize_X_pow_five_add_C_mul_X_add_C`: Dummit's formula for the
  specialization at `X⁵ + aX + b` over any commutative ring.
* `TauCeti.resolventSextic_X_pow_five_add_C_mul_X_add_C`: the resolvent sextic of the integral
  quintic `X⁵ + aX + b`.
* `TauCeti.resolventSextic_X_pow_five_sub_five_mul_X_sub_twelve` and
  `TauCeti.isRoot_resolventSextic_X_pow_five_sub_five_mul_X_sub_twelve`: the resolvent sextic of
  `X⁵ - 5X - 12`, and its root `40`.

## References

* D. S. Dummit, *Solving solvable quintics*, Mathematics of Computation **57** (1991), 387–401,
  equations (2) and (2′).
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- At a quintic `X⁵ + aX + b` the Vieta substitution kills the slots of `e₁`, `e₂`, `e₃` and
sends those of `e₄` and `e₅` to `a` and `-b`. -/
private theorem vietaHom_X_pow_five_add_C_mul_X_add_C (a b : R) :
    vietaHom 5 (X ^ 5 + C a * X + C b) =
      MvPolynomial.eval₂Hom (Int.castRingHom R) ![0, 0, 0, a, -b] := by
  refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i => ?_
  rw [vietaHom_X, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  fin_cases i <;> simp [coeff_X, coeff_C, coeff_X_pow] <;> ring

/-- A weighted homogeneous polynomial of weight `w` for the weights `i + 1`, specialized at
`X⁵ + aX + b`: only the monomials in the last two slots survive, and their exponents solve
`4 i + 5 j = w`. -/
private theorem vietaHom_X_pow_five_add_C_mul_X_add_C_apply (a b : R)
    {P : MvPolynomial (Fin 5) ℤ} {w : ℕ}
    (hP : P.IsWeightedHomogeneous (fun i : Fin 5 => (i : ℕ) + 1) w) (S : Finset (ℕ × ℕ))
    (hS : ∀ i j, 4 * i + 5 * j = w → (i, j) ∈ S) :
    vietaHom 5 (X ^ 5 + C a * X + C b) P =
      ∑ ij ∈ S, (P.coeff (Finsupp.single 3 ij.1 + Finsupp.single 4 ij.2) : R) *
        a ^ ij.1 * (-b) ^ ij.2 := by
  classical
  let v : Fin 5 → R := ![0, 0, 0, a, -b]
  let F : (Fin 5 →₀ ℕ) → R := fun d => (Int.castRingHom R) (P.coeff d) * ∏ i, v i ^ d i
  let g : ℕ × ℕ → (Fin 5 →₀ ℕ) := fun ij => Finsupp.single 3 ij.1 + Finsupp.single 4 ij.2
  have hg : Function.Injective g := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h3 := DFunLike.congr_fun h 3
    have h4 := DFunLike.congr_fun h 4
    simp only [g, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at h3 h4
    simp only [Prod.mk.injEq]
    exact ⟨by simpa using h3, by simpa using h4⟩
  have hFg (ij : ℕ × ℕ) : F (g ij) = (P.coeff (g ij) : R) * a ^ ij.1 * (-b) ^ ij.2 := by
    simp [F, g, v, Fin.prod_univ_five, mul_assoc]
  -- Outside the image of `S`, a monomial of the support meets one of the three vanishing slots.
  have hzero (d : Fin 5 →₀ ℕ) (hd : d ∈ P.support) (hdS : d ∉ S.image g) : F d = 0 := by
    by_cases h012 : d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 0
    · refine absurd (Finset.mem_image.mpr ⟨(d 3, d 4), hS _ _ ?_, ?_⟩) hdS
      · have hw := hP (MvPolynomial.mem_support_iff.mp hd)
        simp only [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_five, smul_eq_mul,
          zero_mul, implies_true] at hw
        simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at hw
        omega
      · ext i
        fin_cases i <;> simp [g, h012]
    · have : ∏ i, v i ^ d i = 0 := by
        simp only [Fin.prod_univ_five, v]
        rcases not_and_or.mp h012 with h | h
        · simp [zero_pow h]
        · rcases not_and_or.mp h with h | h
          · simp [zero_pow h]
          · simp [zero_pow h]
      simp [F, this]
  rw [vietaHom_X_pow_five_add_C_mul_X_add_C, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  calc ∑ d ∈ P.support, F d = ∑ d ∈ P.support ∪ S.image g, F d :=
        Finset.sum_subset Finset.subset_union_left fun d _ hd => by
          simp [F, MvPolynomial.notMem_support_iff.mp hd]
    _ = ∑ d ∈ S.image g, F d :=
        (Finset.sum_subset Finset.subset_union_right fun d hd hdS =>
          hzero d ((Finset.mem_union.mp hd).resolve_right hdS) hdS).symm
    _ = _ := by
        rw [Finset.sum_image hg.injOn]
        exact Finset.sum_congr rfl fun ij _ => hFg ij

/-- The integral constant of the orbit product of `quinticF20Spec` in front of `e₄ⁱ e₅ʲ` in the
coefficient of `X ^ k`. -/
private noncomputable def c (k i j : ℕ) : ℤ :=
  (quinticF20Spec.orbitProduct.coeff k).coeff (Finsupp.single 3 i + Finsupp.single 4 j)

/-- The shape of the resolvent sextic of `X⁵ + aX + b` forced by the grading, with eight
undetermined integral constants. -/
private theorem specialize_X_pow_five_add_C_mul_X_add_C_eq (a b : R) :
    quinticF20Spec.specialize R (X ^ 5 + C a * X + C b) =
      X ^ 6 + C (c 5 1 0 * a) * X ^ 5 + C (c 4 2 0 * a ^ 2) * X ^ 4 +
        C (c 3 3 0 * a ^ 3) * X ^ 3 + C (c 2 4 0 * a ^ 4) * X ^ 2 +
        C (c 1 5 0 * a ^ 5 + c 1 0 4 * b ^ 4) * X + C (c 0 6 0 * a ^ 6 + c 0 1 4 * a * b ^ 4) := by
  have hw (k : ℕ) := quinticF20Spec.isWeightedHomogeneous_orbitProduct_coeff
    (quinticF20Spec_Φ ▸ isHomogeneous_quinticF20Invariant) k
  simp only [quinticF20Spec_H, index_referenceSubgroup_five_two] at hw
  ext k
  rw [ResolventSpec.specialize_def, coeff_map]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  match k with
  | 0 =>
    rw [vietaHom_X_pow_five_add_C_mul_X_add_C_apply a b (hw 0) {(6, 0), (1, 4)}
      (fun i j h => by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega)]
    simp [c]
    ring
  | 1 =>
    rw [vietaHom_X_pow_five_add_C_mul_X_add_C_apply a b (hw 1) {(5, 0), (0, 4)}
      (fun i j h => by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]; omega)]
    simp [c]
    ring
  | 2 =>
    rw [vietaHom_X_pow_five_add_C_mul_X_add_C_apply a b (hw 2) {(4, 0)}
      (fun i j h => by simp only [Finset.mem_singleton, Prod.mk.injEq]; omega)]
    simp [c]
  | 3 =>
    rw [vietaHom_X_pow_five_add_C_mul_X_add_C_apply a b (hw 3) {(3, 0)}
      (fun i j h => by simp only [Finset.mem_singleton, Prod.mk.injEq]; omega)]
    simp [c]
  | 4 =>
    rw [vietaHom_X_pow_five_add_C_mul_X_add_C_apply a b (hw 4) {(2, 0)}
      (fun i j h => by simp only [Finset.mem_singleton, Prod.mk.injEq]; omega)]
    simp [c]
  | 5 =>
    rw [vietaHom_X_pow_five_add_C_mul_X_add_C_apply a b (hw 5) {(1, 0)}
      (fun i j h => by simp only [Finset.mem_singleton, Prod.mk.injEq]; omega)]
    simp [c]
  | 6 =>
    have h6 : quinticF20Spec.orbitProduct.coeff 6 = 1 := by
      have hm := quinticF20Spec.monic_orbitProduct
      rwa [Monic, leadingCoeff, ResolventSpec.natDegree_orbitProduct, quinticF20Spec_H,
        index_referenceSubgroup_five_two] at hm
    simp [h6]
  | k + 7 =>
    have hk : quinticF20Spec.orbitProduct.coeff (k + 7) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [ResolventSpec.natDegree_orbitProduct, quinticF20Spec_H,
        index_referenceSubgroup_five_two]
      omega
    simp [hk]

/-- The value of a renaming of Dummit's invariant, written out. -/
private theorem eval₂_rename_quinticF20Invariant (x : Fin 5 → R) (σ : Equiv.Perm (Fin 5)) :
    MvPolynomial.eval₂ (Int.castRingHom R) x (MvPolynomial.rename ⇑σ quinticF20Invariant) =
      x (σ 0) ^ 2 * (x (σ 1) * x (σ 4) + x (σ 2) * x (σ 3)) +
        x (σ 1) ^ 2 * (x (σ 2) * x (σ 0) + x (σ 3) * x (σ 4)) +
        x (σ 2) ^ 2 * (x (σ 3) * x (σ 1) + x (σ 4) * x (σ 0)) +
        x (σ 3) ^ 2 * (x (σ 4) * x (σ 2) + x (σ 0) * x (σ 1)) +
        x (σ 4) ^ 2 * (x (σ 0) * x (σ 3) + x (σ 1) * x (σ 2)) := by
  rw [rename_quinticF20Invariant]
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X, Fin.sum_univ_five]
  simp only [Fin.isValue, Fin.reduceAdd, Fin.reduceSub]

/-- The roots `0, 1, -1, i, -i` of `X⁵ - X`. -/
private noncomputable def x₁ : Fin 5 → ℂ := ![0, 1, -1, Complex.I, -Complex.I]

/-- `C i` squares to `-1` in `ℂ[X]`. -/
private theorem C_I_sq : (C Complex.I : ℂ[X]) ^ 2 = -1 := by
  rw [← C_pow, Complex.I_sq, C_neg, C_1]

private theorem prod_x₁ : (X ^ 5 + C (-1) * X + C 0 : ℂ[X]) = ∏ i, (X - C (x₁ i)) := by
  simp only [Fin.prod_univ_five, x₁]
  simp
  linear_combination (X ^ 3 - X) * C_I_sq

open Equiv in
/-- At `X⁵ - X` the six orbit values are `2`, four times, and `± 4i`. -/
private theorem specialize_X_pow_five_sub_X :
    quinticF20Spec.specialize ℂ (X ^ 5 + C (-1) * X + C 0) = (X - 2) ^ 4 * (X ^ 2 + 16) := by
  rw [ResolventSpec.specialize_def, map_vietaHom_eq_galResolvent quinticF20Spec.orbitProduct_esymm
    prod_x₁, quinticF20Spec_Φ, ← MvPolynomial.map_universalResolvent_eq_galResolvent,
    universalResolvent_quinticF20Invariant, Polynomial.map_prod,
    prod_quinticF20OrbitRepresentatives]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, MvPolynomial.coe_eval₂Hom,
    eval₂_rename_quinticF20Invariant]
  simp [x₁, swap_apply_def]
  linear_combination (-16 * (X - 2) ^ 4) * C_I_sq

/-- A root of `X⁵ + aX + b` given by an orbit value: the shape of the sextic evaluated there. -/
private theorem eval_eq_zero_of_eq_prod {a b : R} {x : Fin 5 → R}
    (hf : X ^ 5 + C a * X + C b = ∏ i, (X - C (x i))) {σ : Equiv.Perm (Fin 5)} {v : R}
    (hv : MvPolynomial.eval₂ (Int.castRingHom R) x
      (MvPolynomial.rename ⇑σ quinticF20Invariant) = v) :
    v ^ 6 + c 5 1 0 * a * v ^ 5 + c 4 2 0 * a ^ 2 * v ^ 4 + c 3 3 0 * a ^ 3 * v ^ 3 +
      c 2 4 0 * a ^ 4 * v ^ 2 + (c 1 5 0 * a ^ 5 + c 1 0 4 * b ^ 4) * v +
      (c 0 6 0 * a ^ 6 + c 0 1 4 * a * b ^ 4) = 0 := by
  have h := quinticF20Spec.isRoot_specialize_eval₂_rename hf σ
  rw [quinticF20Spec_Φ, hv, specialize_X_pow_five_add_C_mul_X_add_C_eq] at h
  simpa using h

/-- `√31`, as a complex number. -/
private noncomputable def sqrt31 : ℂ := (Real.sqrt 31 : ℂ)

private theorem sqrt31_sq : sqrt31 ^ 2 = 31 := by
  rw [sqrt31, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The roots `-3, 2 ± i, (-1 ± i√31) / 2` of
`X⁵ - 41X + 120 = (X + 3)(X² - 4X + 5)(X² + X + 8)`. -/
private noncomputable def x₂ : Fin 5 → ℂ :=
  ![-3, 2 + Complex.I, 2 - Complex.I, (-1 + Complex.I * sqrt31) / 2,
    (-1 - Complex.I * sqrt31) / 2]

private theorem prod_x₂ : (X ^ 5 + C (-41) * X + C 120 : ℂ[X]) = ∏ i, (X - C (x₂ i)) := by
  have key (u w : ℂ) : (X - C u) * (X - C w) = X ^ 2 - C (u + w) * X + C (u * w) := by
    rw [C_add, C_mul]
    ring
  have h12 : x₂ 1 + x₂ 2 = 4 ∧ x₂ 1 * x₂ 2 = 5 := by
    simp only [x₂]
    constructor
    · simp
      ring
    · simp
      linear_combination (-1 : ℂ) * Complex.I_sq
  have h34 : x₂ 3 + x₂ 4 = -1 ∧ x₂ 3 * x₂ 4 = 8 := by
    simp only [x₂]
    constructor
    · simp
      ring
    · simp
      linear_combination (-(1 : ℂ) / 4 * sqrt31 ^ 2) * Complex.I_sq + (1 / 4 : ℂ) * sqrt31_sq
  rw [Fin.prod_univ_five, mul_assoc (_ * _), mul_assoc (X - C (x₂ 0)), key, key, h12.1, h12.2,
    h34.1, h34.2]
  simp [x₂, C_ofNat]
  ring

private theorem eval₂_rename_x₂_swap_two_four :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) x₂
      (MvPolynomial.rename ⇑(Equiv.swap (2 : Fin 5) 4) quinticF20Invariant) =
        190 - 12 * sqrt31 := by
  rw [eval₂_rename_quinticF20Invariant]
  simp [x₂, Equiv.swap_apply_def]
  linear_combination (Complex.I ^ 2 * sqrt31 ^ 3 / 4 - Complex.I ^ 2 * sqrt31 - sqrt31 ^ 3 / 4 -
    19 * sqrt31 ^ 2 / 4 + 79 * sqrt31 / 4 - 4) * Complex.I_sq + (sqrt31 / 4 + 19 / 4) * sqrt31_sq

private theorem eval₂_rename_x₂_swap_two_three_mul_swap_three_four :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) x₂
      (MvPolynomial.rename ⇑(Equiv.swap 2 3 * Equiv.swap 3 4 : Equiv.Perm (Fin 5))
        quinticF20Invariant) =
        190 + 12 * sqrt31 := by
  rw [eval₂_rename_quinticF20Invariant]
  simp [x₂, Equiv.swap_apply_def]
  linear_combination (-Complex.I ^ 2 * sqrt31 ^ 3 / 4 + Complex.I ^ 2 * sqrt31 + sqrt31 ^ 3 / 4 -
    19 * sqrt31 ^ 2 / 4 - 79 * sqrt31 / 4 - 4) * Complex.I_sq + (19 / 4 - sqrt31 / 4) * sqrt31_sq

/-- **The eight constants.** At `X⁵ - X` the full sextic `(X - 2)⁴ (X² + 16)` fixes the six
constants in front of powers of `a`; at `X⁵ - 41X + 120` the two real orbit values `190 ± 12√31`
fix the two constants in front of `b⁴`. -/
private theorem c_values : c 5 1 0 = 8 ∧ c 4 2 0 = 40 ∧ c 3 3 0 = 160 ∧ c 2 4 0 = 400 ∧
    c 1 5 0 = 512 ∧ c 1 0 4 = -3125 ∧ c 0 6 0 = 256 ∧ c 0 1 4 = -9375 := by
  have hP1 (t : ℂ) := congrArg (eval t) specialize_X_pow_five_sub_X
  simp only [specialize_X_pow_five_add_C_mul_X_add_C_eq, eval_add, eval_mul, eval_pow, eval_C,
    eval_X, eval_sub, eval_ofNat] at hP1
  have hm := eval_eq_zero_of_eq_prod prod_x₂ eval₂_rename_x₂_swap_two_four
  have hp := eval_eq_zero_of_eq_prod prod_x₂ eval₂_rename_x₂_swap_two_three_mul_swap_three_four
  generalize c 5 1 0 = A1, c 4 2 0 = A2, c 3 3 0 = A3, c 2 4 0 = A4, c 1 5 0 = A5,
    c 1 0 4 = B5, c 0 6 0 = A6, c 0 1 4 = B6 at hP1 hm hp ⊢
  -- Each integral equation is proved by casting it to `ℂ`, where `hP1`, `hm` and `hp` live.
  -- Six values of `(X - 2)⁴ (X² + 16)` pin down the six constants in front of powers of `a`.
  have E₁ : -A1 + A2 - A3 + A4 - A5 + A6 = 16 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination hP1 1
  have E₂ : A1 + A2 + A3 + A4 + A5 + A6 = 1376 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination hP1 (-1)
  have E₃ : -32 * A1 + 16 * A2 - 8 * A3 + 4 * A4 - 2 * A5 + A6 = -64 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination hP1 2
  have E₄ : 32 * A1 + 16 * A2 + 8 * A3 + 4 * A4 + 2 * A5 + A6 = 5056 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination hP1 (-2)
  have E₅ : -243 * A1 + 81 * A2 - 27 * A3 + 9 * A4 - 3 * A5 + A6 = -704 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination hP1 3
  have E₆ : 243 * A1 + 81 * A2 + 27 * A3 + 9 * A4 + 3 * A5 + A6 = 14896 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination hP1 (-3)
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ :
      A1 = 8 ∧ A2 = 40 ∧ A3 = 160 ∧ A4 = 400 ∧ A5 = 512 ∧ A6 = 256 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  push_cast at hm hp
  -- The difference and the sum of the equations at `190 ± 12√31` isolate `B5`, then `B6`.
  obtain rfl : B5 = -3125 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination (sqrt31 / 154275840000) * (hp - hm) - ((B5 : ℂ) / 31 +
      203 * sqrt31 ^ 4 / 77500 + 54229 * sqrt31 ^ 2 / 38750 + 3125 / 31) * sqrt31_sq
  push_cast at hm hp
  obtain rfl : B6 = -9375 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination (hp + hm) / (-17003520000) - (-9 * sqrt31 ^ 4 / 25625 -
      75401 * sqrt31 ^ 2 / 102500 - 13551881 / 102500) * sqrt31_sq
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Dummit's formula for the resolvent of a quintic trinomial.** Over every commutative ring,
the specialization of the quintic `F₂₀` specification at `X⁵ + aX + b` is
`X⁶ + 8aX⁵ + 40a²X⁴ + 160a³X³ + 400a⁴X² + (512a⁵ - 3125b⁴)X + (256a⁶ - 9375ab⁴)`. -/
theorem quinticF20Spec_specialize_X_pow_five_add_C_mul_X_add_C (a b : R) :
    quinticF20Spec.specialize R (X ^ 5 + C a * X + C b) =
      X ^ 6 + C (8 * a) * X ^ 5 + C (40 * a ^ 2) * X ^ 4 + C (160 * a ^ 3) * X ^ 3 +
        C (400 * a ^ 4) * X ^ 2 + C (512 * a ^ 5 - 3125 * b ^ 4) * X +
        C (256 * a ^ 6 - 9375 * a * b ^ 4) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := c_values
  rw [specialize_X_pow_five_add_C_mul_X_add_C_eq, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  push_cast
  ring_nf

/-- **Dummit's formula (2′) for the resolvent sextic** of the integral quintic `X⁵ + aX + b`. -/
theorem resolventSextic_X_pow_five_add_C_mul_X_add_C (a b : ℤ) :
    resolventSextic (X ^ 5 + C a * X + C b) =
      X ^ 6 + C (8 * a) * X ^ 5 + C (40 * a ^ 2) * X ^ 4 + C (160 * a ^ 3) * X ^ 3 +
        C (400 * a ^ 4) * X ^ 2 + C (512 * a ^ 5 - 3125 * b ^ 4) * X +
        C (256 * a ^ 6 - 9375 * a * b ^ 4) := by
  rw [resolventSextic_def, quinticF20Spec_specialize_X_pow_five_add_C_mul_X_add_C]

/-- The resolvent sextic of `X⁵ - 5X - 12`, from Dummit's formula for a quintic trinomial. -/
theorem resolventSextic_X_pow_five_sub_five_mul_X_sub_twelve :
    resolventSextic (X ^ 5 - 5 * X - 12) =
      X ^ 6 - 40 * X ^ 5 + 1000 * X ^ 4 - 20000 * X ^ 3 + 250000 * X ^ 2 - 66400000 * X +
        976000000 := by
  have hf : (X ^ 5 - 5 * X - 12 : ℤ[X]) = X ^ 5 + C (-5) * X + C (-12) := by
    simp only [map_neg, C_ofNat]
    ring
  rw [hf, resolventSextic_X_pow_five_add_C_mul_X_add_C]
  norm_num [C_ofNat]
  ring

/-- The resolvent sextic of `X⁵ - 5X - 12` has the integral root `40`. -/
theorem isRoot_resolventSextic_X_pow_five_sub_five_mul_X_sub_twelve :
    (resolventSextic (X ^ 5 - 5 * X - 12)).IsRoot 40 := by
  rw [resolventSextic_X_pow_five_sub_five_mul_X_sub_twelve]
  norm_num [IsRoot]

end TauCeti
