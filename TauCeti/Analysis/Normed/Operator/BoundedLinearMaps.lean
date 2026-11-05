/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Bounded bilinear maps and bounded scalar actions over a normed ring

Over a seminormed commutative ring `R`, which need not be a field, an `R`-bilinear map `β` with
`‖β x y‖ ≤ C * ‖x‖ * ‖y‖` is jointly continuous (`LinearMap.continuous₂_of_bound`), and so is a
scalar action with `‖r • m‖ ≤ C * ‖r‖ * ‖m‖` (`TauCeti.continuousSMul_of_norm_smul_le`). For an
`R`-algebra `S`, such a bound on the action makes the structure map bounded
(`TauCeti.exists_norm_algebraMap_le_of_norm_smul_le`).
-/

public section

open scoped NNReal

variable {R : Type*} [SeminormedCommRing R]

/-- An `R`-bilinear map bounded by `C * ‖x‖ * ‖y‖` is jointly continuous. -/
theorem LinearMap.continuous₂_of_bound {X Y Z : Type*} [SeminormedAddCommGroup X]
    [Module R X] [SeminormedAddCommGroup Y] [Module R Y] [SeminormedAddCommGroup Z] [Module R Z]
    (β : X →ₗ[R] Y →ₗ[R] Z) (C : ℝ) (hβ : ∀ x y, ‖β x y‖ ≤ C * ‖x‖ * ‖y‖) :
    Continuous fun p : X × Y ↦ β p.1 p.2 :=
  IsBoundedBilinearMap.continuous (𝕜 := R)
    { add_left := fun x₁ x₂ y ↦ by simp
      smul_left := fun c x y ↦ by simp
      add_right := fun x y₁ y₂ ↦ by simp
      smul_right := fun c x y ↦ by simp
      bound := ⟨max C 1, by positivity, fun x y ↦
        (hβ x y).trans (by gcongr; exact le_max_left _ _)⟩ }

/-- A scalar action bounded by `C * ‖r‖ * ‖m‖` is continuous. -/
theorem TauCeti.continuousSMul_of_norm_smul_le {M : Type*} [SeminormedAddCommGroup M]
    [Module R M]
    (h : ∃ C : ℝ≥0, ∀ (r : R) (m : M), ‖r • m‖ ≤ C * ‖r‖ * ‖m‖) : ContinuousSMul R M :=
  h.elim fun C hC ↦ ⟨(LinearMap.lsmul R M).continuous₂_of_bound C hC⟩

/-- If the action of `R` on an `R`-algebra `S` is bounded, `‖r • s‖ ≤ C * ‖r‖ * ‖s‖`, then so is
the structure map: `‖algebraMap R S r‖ ≤ C * ‖1‖ * ‖r‖`. -/
theorem TauCeti.exists_norm_algebraMap_le_of_norm_smul_le {S : Type*} [SeminormedRing S]
    [Algebra R S] (h : ∃ C : ℝ≥0, ∀ (r : R) (s : S), ‖r • s‖ ≤ C * ‖r‖ * ‖s‖) :
    ∃ C : ℝ≥0, ∀ r : R, ‖algebraMap R S r‖ ≤ C * ‖r‖ :=
  h.elim fun C hC ↦ ⟨C * ‖(1 : S)‖₊, fun r ↦ by
    simpa [Algebra.algebraMap_eq_smul_one, mul_right_comm] using hC r 1⟩

end
