/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.QuantumGroups.HalfAlgebra.SkewDerivative

import TauCeti.Algebra.FreeAlgebra
import TauCeti.Algebra.Star.Free

/-!
# The bilinear form on the free algebra and its radical

Let `T = R⟨θᵢ : i ∈ I⟩` and `χ : I → I → R` be as in
`TauCeti.QuantumGroups.HalfAlgebra.SkewDerivative`. Lusztig's bilinear form on `T` is the
bilinear form `B` determined by `B(1, z) = ε(z)`, the constant term of `z`, and

`B(θᵢ y, z) = B(y, Lᵢ z)`,

so that `B(θᵢ₁ ⋯ θᵢₙ, z) = ε(Lᵢₙ ⋯ Lᵢ₁ z)`. It has `B(θᵢ, θⱼ) = δᵢⱼ`, and when `χ` is symmetric it
is symmetric and also satisfies `B(y θᵢ, z) = B(y, Rᵢ z)`. Lusztig normalizes the generators
differently, with `B(θᵢ, θᵢ) = (1 - vᵢ⁻²)⁻¹`. The positive part `f` of the quantized enveloping
algebra attached to a Cartan datum is the quotient of `T` by the radical `J` of `B`, for
`χ(αᵢ, αⱼ) = q^(dᵢ aᵢⱼ)`.

This file constructs `B` and proves the properties of `J` that make `f = T / J` an algebra with
skew derivatives, a torus action and word reversal: `J` is a left ideal stable under the skew
derivatives `Rᵢ` and every diagonal scaling, and when `χ` is symmetric it is also a right ideal
stable under the skew derivatives `Lᵢ` and word reversal. For symmetric `χ` over a commutative
ring, it also proves that the common kernel of the `Lᵢ` modulo `J` consists of the scalars modulo
`J`, the basic tool for showing that an element of `f` vanishes.

## Main definitions

* `TauCeti.freePairing χ`: the bilinear form `B` on the free algebra.
* `TauCeti.halfRadical χ`: its (left) radical `J`.

## Main results

* `TauCeti.freePairing_ι_mul_left`, `TauCeti.freePairing_mul_ι_left`: `B(θᵢ y, z) = B(y, Lᵢ z)` and
  `B(y θᵢ, z) = B(y, Rᵢ z)`, the second when `χ i j = χ j i` for all `j`.
* `TauCeti.eq_freePairing_iff`: `B` is the unique bilinear form with `B(1, z) = ε(z)` and
  `B(θᵢ y, z) = B(y, Lᵢ z)`.
* `TauCeti.freePairing_ι_ι`: the generators are orthonormal.
* `TauCeti.freePairing_freeRemove_left`: `B(Lᵢ x, y) = B(x, θᵢ y)` when `χ i j = χ j i` for all
  `j`.
* `TauCeti.isSymm_freePairing`: `B` is symmetric when `χ` is.
* `TauCeti.freePairing_freeHalfScale_left`: every diagonal scaling is self-adjoint for `B`.
* `TauCeti.freePairing_star_star`: `B` is invariant under word reversal when `χ` is symmetric.
* `TauCeti.freePairing_ι_pow_ι_pow`: in rank one,
  `B(θᵢⁿ, θᵢⁿ) = ∏_(k < n) (1 + χ i i + ⋯ + χ i iᵏ)`.
* `TauCeti.mul_mem_halfRadical_left`, `TauCeti.mul_mem_halfRadical_right`: `J` is a left
  ideal, and a two-sided ideal when `χ` is symmetric.
* `TauCeti.freeRemove_mem_halfRadical`, `TauCeti.freeRemoveRight_mem_halfRadical`,
  `TauCeti.freeHalfScale_mem_halfRadical`, `TauCeti.star_mem_halfRadical_iff`: stability of `J`,
  under `Lᵢ` and word reversal only for symmetric `χ`.
* `TauCeti.forall_freeRemove_mem_halfRadical_iff`: for symmetric `χ` over a commutative ring, all
  `Lᵢ x` lie in `J` exactly when `x` is congruent modulo `J` to its constant term.

## Implementation notes

The form is defined through the algebra map `θᵢ ↦ Lᵢ` from `T` to the opposite of the
endomorphism algebra of `T`, followed by the constant term, so linearity in both arguments and the
recursion `B(θᵢ y, z) = B(y, Lᵢ z)` hold by construction. Symmetry is then proved from the
adjunction `B(Lᵢ x, y) = B(x, θᵢ y)`, by induction on words.

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §1.2.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, American
  Mathematical Society, 1996, Chapter 6.
-/

public section

noncomputable section

namespace TauCeti

open FreeAlgebra

section CommSemiring

variable {R I : Type*} [CommSemiring R] [DecidableEq I] (χ : I → I → R)

/-- The algebra map `θᵢ ↦ Lᵢ` into the opposite of the endomorphism algebra: a word
`θᵢ₁ ⋯ θᵢₙ` acts by `Lᵢₙ ∘ ⋯ ∘ Lᵢ₁`. -/
private def removeAction : FreeAlgebra R I →ₐ[R] (Module.End R (FreeAlgebra R I))ᵐᵒᵖ :=
  lift R fun i => MulOpposite.op (freeRemove χ i).toLinearMap

/-- Lusztig's bilinear form on the free algebra on the simple generators: the bilinear form with
`B(1, z) = ε(z)` and `B(θᵢ y, z) = B(y, Lᵢ z)`, where `ε` is the constant term and `Lᵢ` the left
skew derivative `TauCeti.freeRemove χ i`. -/
def freePairing : LinearMap.BilinForm R (FreeAlgebra R I) :=
  LinearMap.compRight R (algebraMapInv : FreeAlgebra R I →ₐ[R] R).toLinearMap ∘ₗ
    (MulOpposite.opLinearEquiv R).symm.toLinearMap ∘ₗ (removeAction χ).toLinearMap

private theorem freePairing_apply (x z : FreeAlgebra R I) :
    freePairing χ x z = algebraMapInv ((removeAction χ x).unop z) :=
  (rfl)

/-- The recursion of the form in the first argument, for an arbitrary left factor. -/
private theorem freePairing_mul_left (x y z : FreeAlgebra R I) :
    freePairing χ (x * y) z = freePairing χ y ((removeAction χ x).unop z) := by
  simp [freePairing_apply]

@[simp]
theorem freePairing_one_left (z : FreeAlgebra R I) : freePairing χ 1 z = algebraMapInv z := by
  simp [freePairing_apply]

@[simp]
theorem freePairing_algebraMap_left (r : R) (z : FreeAlgebra R I) :
    freePairing χ (algebraMap R (FreeAlgebra R I) r) z = r * algebraMapInv z := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- **The defining recursion of the form**: `B(θᵢ y, z) = B(y, Lᵢ z)`. -/
@[simp]
theorem freePairing_ι_mul_left (i : I) (y z : FreeAlgebra R I) :
    freePairing χ (ι R i * y) z = freePairing χ y (freeRemove χ i z) := by
  simp [freePairing_mul_left, removeAction]

@[simp]
theorem freePairing_ι_left (i : I) (z : FreeAlgebra R I) :
    freePairing χ (ι R i) z = algebraMapInv (freeRemove χ i z) := by
  simpa using freePairing_ι_mul_left χ i 1 z

@[simp]
theorem freePairing_one_right (x : FreeAlgebra R I) : freePairing χ x 1 = algebraMapInv x := by
  induction x using FreeAlgebra.induction_ι_mul with
  | one => simp
  | smul r a ha => simp [ha]
  | add a b ha hb => simp [ha, hb]
  | ι_mul i a _ => simp

/-- **Uniqueness of the form**: `freePairing χ` is the only bilinear form `B` with
`B(1, z) = ε(z)` and `B(θᵢ y, z) = B(y, Lᵢ z)`. -/
theorem eq_freePairing_iff {B : LinearMap.BilinForm R (FreeAlgebra R I)} :
    B = freePairing χ ↔
      (∀ z, B 1 z = algebraMapInv z) ∧ ∀ i y z, B (ι R i * y) z = B y (freeRemove χ i z) := by
  refine ⟨by rintro rfl; simp, fun ⟨one, ι_mul⟩ => LinearMap.ext₂ fun x z => ?_⟩
  induction x using FreeAlgebra.induction_ι_mul generalizing z with
  | one => simp [one]
  | smul r a ha => simp [ha]
  | add a b ha hb => simp [ha, hb]
  | ι_mul i a ha => simp [ι_mul, ha]

/-- The simple generators are orthonormal: `B(θᵢ, θⱼ) = δᵢⱼ`. -/
theorem freePairing_ι_ι (i j : I) :
    freePairing χ (ι R i) (ι R j) = if i = j then 1 else 0 := by
  simp only [freePairing_ι_left, freeRemove_ι]
  split_ifs <;> simp

/-- **Adjunction of the left skew derivative and left multiplication**:
`B(Lᵢ x, y) = B(x, θᵢ y)`, when `χ i j = χ j i` for every `j`. -/
theorem freePairing_freeRemove_left {i : I} (hχ : ∀ j, χ i j = χ j i) (x y : FreeAlgebra R I) :
    freePairing χ (freeRemove χ i x) y = freePairing χ x (ι R i * y) := by
  induction x using FreeAlgebra.induction_ι_mul generalizing y with
  | one => simp
  | smul r a ha => simp [ha]
  | add a b ha hb => simp [ha, hb]
  | ι_mul j a ha =>
    simp [freeRemove_ι_mul, ← ha, hχ j, apply_ite, ite_apply, eq_comm (a := j)]

/-- The operator by which a word acts in `removeAction` commutes with `Rᵢ` when `χ` is symmetric
at `i`. -/
private theorem removeAction_freeRemoveRight {i : I} (hχ : ∀ j, χ i j = χ j i)
    (x z : FreeAlgebra R I) :
    (removeAction χ x).unop (freeRemoveRight χ i z) =
      freeRemoveRight χ i ((removeAction χ x).unop z) := by
  induction x using FreeAlgebra.induction generalizing z with
  | grade0 r => simp
  | grade1 j => simp [removeAction, freeRemove_freeRemoveRight χ (hχ j).symm]
  | mul a b ha hb => simp [ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- **The recursion of the form on the right**: `B(y θᵢ, z) = B(y, Rᵢ z)`, when `χ i j = χ j i`
for every `j`. -/
theorem freePairing_mul_ι_left {i : I} (hχ : ∀ j, χ i j = χ j i) (y z : FreeAlgebra R I) :
    freePairing χ (y * ι R i) z = freePairing χ y (freeRemoveRight χ i z) := by
  rw [freePairing_mul_left, freePairing_ι_left, freePairing_apply,
    removeAction_freeRemoveRight χ hχ, algebraMapInv_freeRemoveRight]

/-- **The form is symmetric** when `χ` is. -/
theorem isSymm_freePairing (hχ : ∀ i j, χ i j = χ j i) : (freePairing χ).IsSymm := by
  refine ⟨fun x z => ?_⟩
  induction x using FreeAlgebra.induction_ι_mul generalizing z with
  | one => simp
  | smul r a ha => simp [ha]
  | add a b ha hb => simp [ha, hb]
  | ι_mul i a ha => rw [freePairing_ι_mul_left, ha, freePairing_freeRemove_left χ (hχ i)]

/-- Every diagonal scaling is self-adjoint for the form: `B(c · x, z) = B(x, c · z)`. Both sides
vanish unless `x` and `z` have the same multidegree `β`, where they are multiplied by `c^β`. -/
theorem freePairing_freeHalfScale_left (c : I → R) (x z : FreeAlgebra R I) :
    freePairing χ (freeHalfScale c x) z = freePairing χ x (freeHalfScale c z) := by
  induction x using FreeAlgebra.induction_ι_mul generalizing z with
  | one => simp
  | smul r a ha => simp [ha]
  | add a b ha hb => simp [ha, hb]
  | ι_mul i a ha =>
    simp [ha, freeRemove_freeHalfScale]

/-- **Adjunction of the right skew derivative and right multiplication**:
`B(Rᵢ x, y) = B(x, y θᵢ)`. -/
theorem freePairing_freeRemoveRight_left (i : I) (x y : FreeAlgebra R I) :
    freePairing χ (freeRemoveRight χ i x) y = freePairing χ x (y * ι R i) := by
  induction x using FreeAlgebra.induction_ι_mul generalizing y with
  | one => simp
  | smul r a ha => simp [ha]
  | add a b ha hb => simp [ha, hb]
  | ι_mul j a ha =>
    rcases eq_or_ne i j with rfl | h
    · simp [freeRemoveRight_mul, SigmaDerivation.leibniz, ha, freePairing_freeHalfScale_left,
        add_comm]
    · simp [freeRemoveRight_mul, SigmaDerivation.leibniz, ha, h, h.symm]

/-- The form is invariant under word reversal, when `χ` is symmetric. -/
theorem freePairing_star_star (hχ : ∀ i j, χ i j = χ j i) (x z : FreeAlgebra R I) :
    freePairing χ (star x) (star z) = freePairing χ x z := by
  induction x using FreeAlgebra.induction_ι_mul generalizing z with
  | one => simp
  | smul r a ha => simp [ha]
  | add a b ha hb => simp [ha, hb]
  | ι_mul i a ha =>
    rw [star_mul, star_ι, freePairing_mul_ι_left χ (hχ i), freeRemoveRight_eq_star, star_star,
      ha, freePairing_ι_mul_left]

/-- In rank one, `B(θᵢⁿ, θᵢⁿ) = ∏_(k < n) (1 + χ i i + ⋯ + χ i iᵏ)`. For `χ i i = q²` this is
`q^(n(n-1)/2) [n]_q!`, so the powers of `θᵢ` are not in the radical at a generic parameter. -/
theorem freePairing_ι_pow_ι_pow (i : I) (n : ℕ) :
    freePairing χ (ι R i ^ n) (ι R i ^ n) =
      ∏ k ∈ Finset.range n, ∑ m ∈ Finset.range (k + 1), χ i i ^ m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', freePairing_ι_mul_left, ← pow_succ', freeRemove_ι_pow_succ]
    simp [ih, Finset.prod_range_succ, mul_comm]

/-! ### The radical -/

/-- The radical `J` of the form: the elements `x` with `B(x, z) = 0` for every `z`. When `χ` is
symmetric it is a two-sided ideal, and the positive part of the quantum group is the quotient of
the free algebra by it. -/
def halfRadical : Submodule R (FreeAlgebra R I) :=
  LinearMap.ker (freePairing χ)

variable {χ}

theorem mem_halfRadical {x : FreeAlgebra R I} :
    x ∈ halfRadical χ ↔ ∀ z, freePairing χ x z = 0 := by
  simp [halfRadical, LinearMap.ext_iff]

/-- For symmetric `χ`, the left radical of the form is also its right radical. -/
theorem mem_halfRadical_iff_right (hχ : ∀ i j, χ i j = χ j i) {x : FreeAlgebra R I} :
    x ∈ halfRadical χ ↔ ∀ z, freePairing χ z x = 0 := by
  simp [mem_halfRadical, (isSymm_freePairing χ hχ).eq _ x]

/-- The radical is a left ideal. -/
theorem mul_mem_halfRadical_left (x : FreeAlgebra R I) {y : FreeAlgebra R I}
    (hy : y ∈ halfRadical χ) : x * y ∈ halfRadical χ := by
  rw [mem_halfRadical] at hy ⊢
  intro z
  rw [freePairing_mul_left, hy]

/-- The radical is a right ideal, when `χ` is symmetric. -/
theorem mul_mem_halfRadical_right (hχ : ∀ i j, χ i j = χ j i) {x : FreeAlgebra R I}
    (hx : x ∈ halfRadical χ) (y : FreeAlgebra R I) : x * y ∈ halfRadical χ := by
  induction y using FreeAlgebra.induction_ι_mul generalizing x with
  | one => simpa using hx
  | smul r a ha => simpa using Submodule.smul_mem _ r (ha hx)
  | add a b ha hb => simpa [mul_add] using add_mem (ha hx) (hb hx)
  | ι_mul i a ha =>
    rw [← mul_assoc]
    refine ha ?_
    rw [mem_halfRadical] at hx ⊢
    intro z
    rw [freePairing_mul_ι_left χ (hχ i), hx]

/-- The radical is stable under the left skew derivative `Lᵢ`, when `χ i j = χ j i` for every
`j`. -/
theorem freeRemove_mem_halfRadical {i : I} (hχ : ∀ j, χ i j = χ j i) {x : FreeAlgebra R I}
    (hx : x ∈ halfRadical χ) : freeRemove χ i x ∈ halfRadical χ := by
  rw [mem_halfRadical] at hx ⊢
  intro z
  rw [freePairing_freeRemove_left χ hχ, hx]

/-- The radical is stable under the right skew derivative `Rᵢ`. -/
theorem freeRemoveRight_mem_halfRadical {i : I} {x : FreeAlgebra R I} (hx : x ∈ halfRadical χ) :
    freeRemoveRight χ i x ∈ halfRadical χ := by
  rw [mem_halfRadical] at hx ⊢
  intro z
  rw [freePairing_freeRemoveRight_left, hx]

/-- The radical is stable under every diagonal scaling, so the torus acts on the quotient. -/
theorem freeHalfScale_mem_halfRadical (c : I → R) {x : FreeAlgebra R I}
    (hx : x ∈ halfRadical χ) : freeHalfScale c x ∈ halfRadical χ := by
  rw [mem_halfRadical] at hx ⊢
  intro z
  rw [freePairing_freeHalfScale_left, hx]

/-- The radical is stable under word reversal, when `χ` is symmetric. -/
theorem star_mem_halfRadical_iff (hχ : ∀ i j, χ i j = χ j i) {x : FreeAlgebra R I} :
    star x ∈ halfRadical χ ↔ x ∈ halfRadical χ := by
  simp only [mem_halfRadical]
  refine ⟨fun h z => ?_, fun h z => ?_⟩
  · rw [← freePairing_star_star χ hχ, h]
  · rw [← star_star z, freePairing_star_star χ hχ, h]

end CommSemiring

section CommRing

variable {R I : Type*} [CommRing R] [DecidableEq I] {χ : I → I → R}

/-- **Modulo the radical, the common kernel of the left skew derivatives is the scalars**: for
symmetric `χ`, every `Lᵢ x` lies in `J` exactly when `x` is congruent modulo `J` to its constant
term. -/
theorem forall_freeRemove_mem_halfRadical_iff (hχ : ∀ i j, χ i j = χ j i)
    {x : FreeAlgebra R I} :
    (∀ i, freeRemove χ i x ∈ halfRadical χ) ↔
      x - algebraMap R (FreeAlgebra R I) (algebraMapInv x) ∈ halfRadical χ := by
  refine ⟨fun h => (mem_halfRadical_iff_right hχ).2 fun z => ?_, fun h i => ?_⟩
  · -- Pair against words: `B(1, ·)` is the constant term, and `B(θᵢ a, ·) = B(a, Lᵢ ·)`.
    induction z using FreeAlgebra.induction_ι_mul with
    | one => simp
    | smul r a ha => simp [ha]
    | add a b ha hb => simp [ha, hb]
    | ι_mul i a _ =>
      rw [freePairing_ι_mul_left, map_sub, freeRemove_algebraMap, sub_zero]
      exact (mem_halfRadical_iff_right hχ).1 (h i) a
  · simpa using freeRemove_mem_halfRadical (hχ i) h

end CommRing

end TauCeti
