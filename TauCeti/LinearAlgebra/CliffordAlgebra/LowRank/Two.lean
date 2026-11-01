/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
-- Public: `ιInv` appears in the coordinate formula for the character.
public import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
import Mathlib.Tactic.LinearCombination

/-!
# Clifford algebras in dimension two

The odd component of a two-dimensional Clifford algebra consists entirely of vector generators.
Indeed, the generator image lies in the odd component, and both spaces have dimension two: the
generator is injective, while the odd component has dimension `2 ^ (2 - 1)`.

This is a general grading fact, independent of the Lipschitz and Spin groups. Multiplying by a
fixed vector `a` of invertible norm exchanges the two components, so every even element is a
product `ι a * ι w` of `a` with another vector.

For the sum of two squares on `R²`, write `J = ι e₀ * ι e₁`, so that `J * J = -1`. Every even
element of a two-dimensional Clifford algebra over a field is `ι e₀ * ι w = w₀ + w₁ J`, so the even
Clifford algebra is `K[J]`. Over any commutative ring `R` containing a square root `i` of `-1`,
the even Clifford algebra has the character `u + v J ↦ u + i v`, built with `even.lift`.

## Main definitions

* `CliffordAlgebra.evenWeightedSumSquaresOneAlgHom`: the character `u + v J ↦ u + i v` of the
  even Clifford algebra of the sum of two squares.

## Main results

* `CliffordAlgebra.range_ι_eq_evenOdd_one_of_finrank_eq_two`: every odd Clifford element in
  dimension two is a vector generator.
* `CliffordAlgebra.mem_even_iff_exists_ι_mul_ι_of_finrank_eq_two`: every even Clifford element in
  dimension two is a product `ι a * ι w`, for any fixed `a` of invertible norm.
* `CliffordAlgebra.evenWeightedSumSquaresOneAlgHom_ι` and
  `CliffordAlgebra.evenWeightedSumSquaresOneAlgHom_apply`: the character on a product of two
  generators, and in coordinates.
-/

public section

open Module

namespace CliffordAlgebra

universe u v

section FieldDimension

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [Invertible (2 : K)]

/-- In dimension two, every odd Clifford element is a vector generator. -/
theorem range_ι_eq_evenOdd_one_of_finrank_eq_two (Q : QuadraticForm K V)
    (hV : finrank K V = 2) : LinearMap.range (ι Q) = evenOdd Q 1 := by
  let _ : FiniteDimensional K V :=
    FiniteDimensional.of_finrank_pos (by rw [hV]; decide)
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; decide)
  apply Submodule.eq_of_le_of_finrank_eq (range_ι_le_evenOdd_one Q)
  rw [LinearMap.finrank_range_of_inj (ι_injective Q), finrank_evenOdd Q, hV]
  norm_num

/-- In dimension two, the even Clifford elements are exactly the products `ι a * ι w`, for any
fixed vector `a` of invertible norm. -/
theorem mem_even_iff_exists_ι_mul_ι_of_finrank_eq_two (Q : QuadraticForm K V)
    (hV : finrank K V = 2) (a : V) [Invertible (Q a)] {x : CliffordAlgebra Q} :
    x ∈ even Q ↔ ∃ w, x = ι Q a * ι Q w := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hx' : x ∈ evenOdd Q 0 := by rwa [← even_toSubmodule, Subalgebra.mem_toSubmodule]
    have hodd : ι Q a * x ∈ evenOdd Q 1 :=
      add_zero (1 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mem_evenOdd_one Q a) hx'
    rw [← range_ι_eq_evenOdd_one_of_finrank_eq_two Q hV] at hodd
    obtain ⟨w, hw⟩ := hodd
    refine ⟨⅟(Q a) • w, ?_⟩
    rw [map_smul, mul_smul_comm, hw, ← mul_assoc, ι_sq_scalar, ← Algebra.smul_def, smul_smul,
      invOf_mul_self, one_smul]
  · rintro ⟨w, rfl⟩
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
    exact ι_mul_ι_mem_evenOdd_zero Q a w

end FieldDimension

/-! ### The sum of two squares when `-1` is a square -/

section SumTwoSquares

open QuadraticMap

section CommRing

variable {R : Type u} [CommRing R] (i : R) (hi : i * i = -1)

/-- The bilinear map `(x, y) ↦ (x₀ - i x₁) (y₀ + i y₁)` on `R²`, which sends a pair of vectors to
the value of the character `evenWeightedSumSquaresOneAlgHom` on their Clifford product. -/
private def evenWeightedSumSquaresOneHom :
    EvenHom (weightedSumSquares R ![(1 : R), 1]) R where
  bilin := LinearMap.mk₂ R (fun x y ↦ x 0 * y 0 + x 1 * y 1 + i * (x 0 * y 1 - x 1 * y 0))
    (fun _ _ _ ↦ by simp only [Pi.add_apply]; ring)
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [Pi.add_apply]; ring)
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring)
  contract m := by
    simp only [LinearMap.mk₂_apply, weightedSumSquares_fin_two_apply, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring
  contract_mid a b c := by
    simp only [LinearMap.mk₂_apply, weightedSumSquares_fin_two_apply, one_mul, smul_eq_mul]
    linear_combination (a 0 * b 1 - a 1 * b 0) * (b 0 * c 1 - b 1 * c 0) * hi

/-- **The character of the even Clifford algebra of the sum of two squares** attached to a square
root `i` of `-1`. Writing `J = ι e₀ * ι e₁`, so that `J * J = -1`, every even element over a field
is `u + v J`, and the character sends it to `u + i v`. -/
noncomputable def evenWeightedSumSquaresOneAlgHom :
    even (weightedSumSquares R ![(1 : R), 1]) →ₐ[R] R :=
  even.lift _ (evenWeightedSumSquaresOneHom i hi)

/-- The character on a product of two generators: `ι x * ι y ↦ (x₀ - i x₁) (y₀ + i y₁)`. -/
@[simp]
theorem evenWeightedSumSquaresOneAlgHom_ι (x y : Fin 2 → R) :
    evenWeightedSumSquaresOneAlgHom i hi ((even.ι _).bilin x y) =
      x 0 * y 0 + x 1 * y 1 + i * (x 0 * y 1 - x 1 * y 0) :=
  even.lift_ι _ _ x y

end CommRing

variable {K : Type u} [Field K] [Invertible (2 : K)] (i : K) (hi : i * i = -1)

/-- The character `evenWeightedSumSquaresOneAlgHom` in coordinates: an even element `x` is
`ι e₀ * ι w` for the vector `w = ιInv (ι e₀ * x)`, and is sent to `w₀ + i w₁`. -/
theorem evenWeightedSumSquaresOneAlgHom_apply (x : even (weightedSumSquares K ![(1 : K), 1])) :
    evenWeightedSumSquaresOneAlgHom i hi x =
      ιInv (weightedSumSquares K ![(1 : K), 1])
          (ι _ ![1, 0] * (x : CliffordAlgebra (weightedSumSquares K ![(1 : K), 1]))) 0 +
        i * ιInv (weightedSumSquares K ![(1 : K), 1])
          (ι _ ![1, 0] * (x : CliffordAlgebra (weightedSumSquares K ![(1 : K), 1]))) 1 := by
  let _ : Invertible (weightedSumSquares K ![(1 : K), 1] ![1, 0]) :=
    invertibleOfNonzero (by simp)
  obtain ⟨w, hw⟩ := (mem_even_iff_exists_ι_mul_ι_of_finrank_eq_two _ (Module.finrank_fin_fun K)
    ![1, 0]).1 x.2
  have hx : x = (even.ι _).bilin ![1, 0] w := Subtype.ext (by simp [hw, even.ι])
  rw [hw, ← mul_assoc, ι_sq_scalar, hx, evenWeightedSumSquaresOneAlgHom_ι]
  simp

end SumTwoSquares

end CliffordAlgebra
