/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Checks for the comparison map of differentials

The comparison map `c_f : f^* Ω_{Y/R} → Ω_{X/R}` of a morphism `f : X → Y` over `Spec R` is, on
affine charts `Spec B → Spec A`, Mathlib's `KaehlerDifferential.mapBaseChange R A B :
B ⊗[A] Ω[A⁄R] → Ω[B⁄R]`, `b ⊗ da ↦ b · d(f^* a)` (Tau Ceti's
`cotangentMap_app_pullbackRelativeDifferentialsSectionsEquiv`). These are the ring forms of the
Checks of NashBlowups §0.1.

* **The cusp.** For `t ↦ (t², t³)`, that is `k[x, y] → k[t]`, `x ↦ t²`, `y ↦ t³`, the map sends
  `dx` to `2t dt` and `dy` to `3t² dt`. In characteristic two it sends `dx` to `0` and `dy` to
  `t² dt`, so it is not the formal derivative over `ℤ`.
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

/-- The cusp `t ↦ (t², t³)` as the algebra map `k[x, y] → k[t]`. -/
noncomputable abbrev cusp : MvPolynomial (Fin 2) k →ₐ[k] k[X] :=
  MvPolynomial.aeval ![X ^ 2, X ^ 3]

-- `k[t]` is a `k[x, y]`-algebra through the cusp.
variable [Algebra (MvPolynomial (Fin 2) k) k[X]] [IsScalarTower k (MvPolynomial (Fin 2) k) k[X]]
  (hf : ∀ a, algebraMap (MvPolynomial (Fin 2) k) k[X] a = cusp k a)

include hf

/-- The comparison map of the cusp on `da`: `d(f^* a)`. -/
theorem mapBaseChange_cusp (a : MvPolynomial (Fin 2) k) :
    mapBaseChange k (MvPolynomial (Fin 2) k) k[X] (1 ⊗ₜ D k (MvPolynomial (Fin 2) k) a) =
      D k k[X] (cusp k a) := by
  rw [mapBaseChange_tmul, one_smul, map_D, hf]

/-- **Check.** The cusp sends `dx` to `2t dt`. -/
example : mapBaseChange k (MvPolynomial (Fin 2) k) k[X]
    (1 ⊗ₜ D k (MvPolynomial (Fin 2) k) (MvPolynomial.X 0)) = (2 * X : k[X]) • D k k[X] X := by
  rw [mapBaseChange_cusp k hf, MvPolynomial.aeval_X]
  simp only [Matrix.cons_val_zero]
  rw [Derivation.leibniz_pow, mul_smul, ← ofNat_smul_eq_nsmul (R := k[X])]
  norm_num

/-- **Check.** The cusp sends `dy` to `3t² dt`. -/
example : mapBaseChange k (MvPolynomial (Fin 2) k) k[X]
    (1 ⊗ₜ D k (MvPolynomial (Fin 2) k) (MvPolynomial.X 1)) = (3 * X ^ 2 : k[X]) • D k k[X] X := by
  rw [mapBaseChange_cusp k hf, MvPolynomial.aeval_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Derivation.leibniz_pow, mul_smul, ← ofNat_smul_eq_nsmul (R := k[X])]

/-- **Check.** In characteristic two the cusp sends `dx` to `0`. -/
example [CharP k 2] : mapBaseChange k (MvPolynomial (Fin 2) k) k[X]
    (1 ⊗ₜ D k (MvPolynomial (Fin 2) k) (MvPolynomial.X 0)) = 0 := by
  rw [mapBaseChange_cusp k hf, MvPolynomial.aeval_X]
  simp only [Matrix.cons_val_zero]
  rw [Derivation.leibniz_pow, ← ofNat_smul_eq_nsmul (R := k), CharTwo.two_eq_zero, zero_smul]

/-- **Check.** In characteristic two the cusp sends `dy` to `t² dt`. -/
example [CharP k 2] : mapBaseChange k (MvPolynomial (Fin 2) k) k[X]
    (1 ⊗ₜ D k (MvPolynomial (Fin 2) k) (MvPolynomial.X 1)) = (X ^ 2 : k[X]) • D k k[X] X := by
  rw [mapBaseChange_cusp k hf, MvPolynomial.aeval_X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Derivation.leibniz_pow, ← ofNat_smul_eq_nsmul (R := k),
    show (3 : k) = 1 by rw [show (3 : k) = 2 + 1 by norm_num, CharTwo.two_eq_zero, zero_add],
    one_smul]

end Cusp

/-- **Check.** For the identity of `k[x]`, the comparison map sends `dx` to `dx`. -/
example : mapBaseChange k k[X] k[X] (1 ⊗ₜ D k k[X] X) = D k k[X] X := by
  rw [mapBaseChange_tmul, one_smul, map_D, Algebra.algebraMap_self, RingHom.id_apply]

/-- **Check.** `dx ≠ 0` in `Ω[k[x]⁄k]`, so the zero map is not the comparison map of the
identity. -/
example : D k k[X] X ≠ 0 := fun h ↦ by
  simpa using congr_arg (polynomialEquiv k) h

section ClosedPoint

-- `k` is a `k[x]`-algebra through a closed point `x ↦ a`.
variable [Algebra k[X] k] [IsScalarTower k k[X] k]

/-- **Check.** For a closed point `k[x] → k`, the comparison map
`k ⊗[k[x]] Ω[k[x]⁄k] → Ω[k⁄k] = 0` is surjective. -/
example : Function.Surjective (mapBaseChange k k[X] k) := by
  have : Subsingleton Ω[k⁄k] := subsingleton_of_surjective k k Function.surjective_id
  exact fun y ↦ ⟨0, Subsingleton.elim _ _⟩

/-- **Check.** For a closed point `k[x] → k`, the comparison map is not injective: `1 ⊗ dx ≠ 0`
in `k ⊗[k[x]] Ω[k[x]⁄k]`, which is `k`, while `Ω[k⁄k] = 0`. -/
example : ¬ Function.Injective (mapBaseChange k k[X] k) := by
  have : Subsingleton Ω[k⁄k] := subsingleton_of_surjective k k Function.surjective_id
  intro h
  -- `k ⊗[k[x]] Ω[k[x]⁄k] ≃ k ⊗[k[x]] k[x] ≃ k` sends `1 ⊗ dx` to `1`.
  let φ := (TensorProduct.rid k[X] k).toLinearMap ∘ₗ (polynomialEquiv k).toLinearMap.lTensor k
  have hφ : φ (1 ⊗ₜ D k k[X] X) = 1 := by simp [φ]
  have h0 : (1 : k) ⊗ₜ[k[X]] D k k[X] X = 0 := h (Subsingleton.elim _ _)
  rw [h0, map_zero] at hφ
  exact zero_ne_one hφ

end ClosedPoint

end TauCeti.Examples.DifferentialsPullback
