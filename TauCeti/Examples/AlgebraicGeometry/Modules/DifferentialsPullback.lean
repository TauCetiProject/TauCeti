/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Checks for the comparison map of differentials

The comparison map `c_f : f^* Ω_{Y/R} → Ω_{X/R}` of a morphism `f : X → Y` over `Spec R` is, on
affine charts `Spec B → Spec A`, Mathlib's `KaehlerDifferential.mapBaseChange R A B :
B ⊗[A] Ω[A⁄R] → Ω[B⁄R]`, `b ⊗ da ↦ b · d(f^* a)` (Tau Ceti's
`cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv`). These examples test
`mapBaseChange` on a cusp, the identity and a closed point.

* **The cusp.** For `t ↦ (t², t³)`, that is `k[x, y] → k[t]`, `x ↦ t²`, `y ↦ t³`, the map sends
  `dx` to `2t dt` and `dy` to `3t² dt`, with the coefficients `2` and `3` read in `k`. In
  characteristic two it sends `dx` to `0` and `dy` to `t² dt`.
* **The identity.** For the identity of `k[x]`, `dx ↦ dx`, and `dx ≠ 0`, so the zero map, which is
  also linear, is excluded.
* **A closed point.** For a closed point `x ↦ a`, `k[x] → k`, the map
  `k ⊗[k[x]] Ω[k[x]⁄k] → Ω[k⁄k] = 0` is surjective but not injective: `1 ⊗ dx ≠ 0`.
-/

public section

open Polynomial KaehlerDifferential TensorProduct

namespace TauCeti.Examples.DifferentialsPullback

variable (k : Type) [Field k]

section Cusp

-- `k[t]` is a `k[x, y]`-algebra through the cusp `x ↦ t²`, `y ↦ t³`.
variable [Algebra (MvPolynomial (Fin 2) k) k[X]] [IsScalarTower k (MvPolynomial (Fin 2) k) k[X]]
  (hf : ∀ a, algebraMap (MvPolynomial (Fin 2) k) k[X] a = MvPolynomial.aeval ![X ^ 2, X ^ 3] a)

include hf

/-- The comparison map of the cusp sends `dx` and `dy` to `n tⁿ⁻¹ dt`, for `n = 2` and `n = 3`
respectively. -/
theorem mapBaseChange_cusp_X (i : Fin 2) :
    mapBaseChange k (MvPolynomial (Fin 2) k) k[X]
      (1 ⊗ₜ D k (MvPolynomial (Fin 2) k) (MvPolynomial.X i)) =
      (((![2, 3] i : ℕ) : k[X]) * X ^ (![2, 3] i - 1)) • D k k[X] X := by
  have hX : ![X ^ 2, X ^ 3] i = (X : k[X]) ^ ![2, 3] i := by fin_cases i <;> rfl
  simp [mapBaseChange_tmul, hf, hX, Derivation.leibniz_pow, mul_smul, Nat.cast_smul_eq_nsmul]

/-- **Check.** The cusp sends `dx` to `2t dt`. -/
example : mapBaseChange k (MvPolynomial (Fin 2) k) k[X]
    (1 ⊗ₜ D k (MvPolynomial (Fin 2) k) (MvPolynomial.X 0)) = (2 * X : k[X]) • D k k[X] X := by
  norm_num [mapBaseChange_cusp_X k hf]

/-- **Check.** The cusp sends `dy` to `3t² dt`. -/
example : mapBaseChange k (MvPolynomial (Fin 2) k) k[X]
    (1 ⊗ₜ D k (MvPolynomial (Fin 2) k) (MvPolynomial.X 1)) = (3 * X ^ 2 : k[X]) • D k k[X] X := by
  norm_num [mapBaseChange_cusp_X k hf]

/-- **Check.** In characteristic two the cusp sends `dx` to `0`. -/
example [CharP k 2] : mapBaseChange k (MvPolynomial (Fin 2) k) k[X]
    (1 ⊗ₜ D k (MvPolynomial (Fin 2) k) (MvPolynomial.X 0)) = 0 := by
  simp [mapBaseChange_cusp_X k hf, CharTwo.two_eq_zero]

/-- **Check.** In characteristic two the cusp sends `dy` to `t² dt`. -/
example [CharP k 2] : mapBaseChange k (MvPolynomial (Fin 2) k) k[X]
    (1 ⊗ₜ D k (MvPolynomial (Fin 2) k) (MvPolynomial.X 1)) = (X ^ 2 : k[X]) • D k k[X] X := by
  have h3 : (3 : k[X]) = 2 + 1 := by norm_num
  simp only [CharTwo.two_eq_zero, zero_add] at h3
  simp [mapBaseChange_cusp_X k hf, h3]

end Cusp

/-- **Check.** For the identity of `k[x]`, the comparison map sends `dx` to `dx`. -/
example : mapBaseChange k k[X] k[X] (1 ⊗ₜ D k k[X] X) = D k k[X] X := by
  simp [mapBaseChange_tmul]

/-- **Check.** `dx ≠ 0` in `Ω[k[x]⁄k]`, so the zero map is not the comparison map of the
identity. -/
example : D k k[X] X ≠ 0 := fun h ↦ by
  simpa using congr_arg (polynomialEquiv k) h

section ClosedPoint

-- `k` is a `k[x]`-algebra through a closed point `x ↦ a`. `Ω[k⁄k] = 0` is the instance
-- `Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`, since `k` is unramified over `k`.
variable [Algebra k[X] k] [IsScalarTower k k[X] k]

/-- **Check.** For a closed point `k[x] → k`, the comparison map
`k ⊗[k[x]] Ω[k[x]⁄k] → Ω[k⁄k] = 0` is surjective. -/
example : Function.Surjective (mapBaseChange k k[X] k) :=
  fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

/-- **Check.** For a closed point `k[x] → k`, the comparison map is not injective: `1 ⊗ dx ≠ 0`
in `k ⊗[k[x]] Ω[k[x]⁄k]`, which is `k`, while `Ω[k⁄k] = 0`. -/
example : ¬ Function.Injective (mapBaseChange k k[X] k) := by
  intro h
  -- `k ⊗[k[x]] Ω[k[x]⁄k] ≃ k ⊗[k[x]] k[x] ≃ k` sends `1 ⊗ dx` to `1`.
  let φ := (TensorProduct.rid k[X] k).toLinearMap ∘ₗ (polynomialEquiv k).toLinearMap.lTensor k
  have hφ : φ (1 ⊗ₜ D k k[X] X) = 1 := by simp [φ]
  have h0 : (1 : k) ⊗ₜ[k[X]] D k k[X] X = 0 := h (Subsingleton.elim _ _)
  rw [h0, map_zero] at hφ
  exact zero_ne_one hφ

end ClosedPoint

end TauCeti.Examples.DifferentialsPullback
