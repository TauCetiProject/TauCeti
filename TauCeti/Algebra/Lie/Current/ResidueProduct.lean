/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Field
public import TauCeti.Algebra.Vertex.ResidueProduct

/-!
# Singular products of affine current fields

For a smooth representation of a residue central extension, the zeroth residue
product of `Jˣ` and `Jʸ` is `J⁅x,y⁆`. The first is the constant field
`-a Φ(x,y) id`, and all higher nonnegative products vanish. Thus the singular
operator product coefficients are themselves native fields, with no formal
power-series multiplication or analytic convergence assumption.

Here `a` is the central scalar and `Φ` follows Mathlib's positive-residue
convention. The usual affine form is `κ = -Φ`, so the first product is
`a κ(x,y) id`. The results include central value zero and arbitrary commutative
coefficient rings.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.5.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.4.
-/

public section

noncomputable section

open scoped VertexOperator
open VertexOperator Finset

namespace TauCeti.CurrentAlgebra

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M]
  (Φ : LinearMap.BilinForm R L) (a : R)
  {σ : currentAlgebra R L →ₗ[R] Module.End R M} (hσ : IsSmooth σ)
  (hσc : ∀ u v, σ u * σ v - σ v * σ u =
    σ ⁅u, v⁆ + algebraMap R (Module.End R M) (a * residuePairing R L Φ u v))

include hσc

/-- The zeroth residue product of current fields is the field of the Lie bracket. -/
theorem nonnegResidueProduct_currentField_zero (x y : L) :
    nonnegResidueProduct 0 (currentField σ hσ x) (currentField σ hσ y) =
      currentField σ hσ ⁅x, y⁆ := by
  apply ext_ncoeff
  intro m
  simp only [ncoeff_nonnegResidueProduct, Nat.antidiagonal_zero, sum_singleton,
    Nat.choose_zero_right, pow_zero, one_smul, Nat.cast_zero, add_zero]
  rw [ncoeff_currentField_mul_sub_mul Φ a hσ hσc]
  split_ifs with hm <;> simp_all

/-- The first residue product is the constant scalar field `-a Φ(x,y) id`.
Its only possibly nonzero normalized coefficient has index `-1`. -/
theorem ncoeff_nonnegResidueProduct_currentField_one (x y : L) (m : ℤ) :
    (nonnegResidueProduct 1 (currentField σ hσ x) (currentField σ hσ y))[[m]] =
      if m = -1 then algebraMap R (Module.End R M) (-a * Φ x y) else 0 := by
  simp only [ncoeff_nonnegResidueProduct, Nat.sum_antidiagonal_succ,
    Nat.antidiagonal_zero, sum_singleton,
    Nat.cast_zero, Nat.cast_one, Nat.reduceAdd,
    ncoeff_currentField_mul_sub_mul Φ a hσ hσc]
  have hm : (0 : ℤ) + (m + 1) = 1 + (m + 0) := by omega
  rw [hm]
  by_cases h : m = -1
  · subst m
    simp
  · have h' : (1 : ℤ) + m ≠ 0 := by omega
    simp [h, h']

/-- All nonnegative current products of index at least two vanish. -/
theorem nonnegResidueProduct_currentField_eq_zero (x y : L) {n : ℕ} (hn : 2 ≤ n) :
    nonnegResidueProduct n (currentField σ hσ x) (currentField σ hσ y) = 0 :=
  (isLocalOfOrder_currentField Φ a hσ hσc x y).nonnegResidueProduct_eq_zero hn

end TauCeti.CurrentAlgebra
