/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Loop
public import TauCeti.Algebra.Lie.HahnModule
public import TauCeti.RingTheory.HahnSeries.Addition

/-!
# Polynomial loops as Hahn series

The polynomial loop algebra `loopAlgebra R Γ L = R[Γ] ⊗[R] L` of a Lie algebra `L` over a
commutative ring `R` embeds into the Lie algebra `HahnModule Γ R L` of `L`-valued Hahn series,
sending `t ^ a ⊗ x` to the monomial `x t ^ a`. For `Γ = ℤ` this is the inclusion of the polynomial
loop algebra `L[t, t⁻¹]` into the formal loop algebra `L((t))`.

## Main definitions and results

* `LieAlgebra.LoopAlgebra.toHahnModule`: the embedding, as a morphism of Lie algebras over `R`.
* `LieAlgebra.LoopAlgebra.coeff_toHahnModule`: its coefficients are those of
  `LieAlgebra.LoopAlgebra.toFinsupp`.
* `LieAlgebra.LoopAlgebra.toHahnModule_single_tmul`: `t ^ a ⊗ x` goes to the monomial `x t ^ a`.
* `LieAlgebra.LoopAlgebra.toHahnModule_injective`: the embedding is injective.
-/

public section

noncomputable section

open HahnModule

namespace LieAlgebra.LoopAlgebra

variable (R Γ L : Type*) [CommRing R] [AddCommMonoid Γ] [PartialOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [LieRing L] [LieAlgebra R L]

/-- The embedding of polynomial loops into `L`-valued Hahn series, sending `t ^ a ⊗ x` to the
monomial `x t ^ a`. -/
def toHahnModule : loopAlgebra R Γ L →ₗ⁅R⁆ HahnModule Γ R L where
  toFun p := of R (HahnSeries.ofFinsuppLinearMap R (toFinsupp R Γ L p))
  map_add' p q := by
    ext a
    simp
  map_smul' r p := by
    ext a
    simp
  map_lie' {p q} := by
    obtain ⟨f, rfl⟩ := (toFinsupp R Γ L).symm.surjective p
    obtain ⟨g, rfl⟩ := (toFinsupp R Γ L).symm.surjective q
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ =>
      simp only [map_add, add_lie, of_add, LinearEquiv.apply_symm_apply] at h₁ h₂ ⊢
      rw [h₁, h₂]
    | single a x =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g₁ g₂ h₁ h₂ =>
        simp only [map_add, lie_add, of_add, LinearEquiv.apply_symm_apply] at h₁ h₂ ⊢
        rw [h₁, h₂]
      | single b y =>
        simp only [toFinsupp_symm_single, ExtendScalars.bracket_tmul,
          AddMonoidAlgebra.single_mul_single, mul_one, toFinsupp_single_tmul,
          HahnSeries.ofFinsuppLinearMap_single, single_lie_single]

variable {R Γ L}

/-- The coefficients of the image of a polynomial loop are its coefficients. -/
@[simp]
theorem coeff_toHahnModule (p : loopAlgebra R Γ L) (a : Γ) :
    ((of R).symm (toHahnModule R Γ L p)).coeff a = toFinsupp R Γ L p a := by
  simp [toHahnModule]

/-- The loop `t ^ a ⊗ x` is sent to the monomial `x t ^ a`. -/
@[simp]
theorem toHahnModule_single_tmul (a : Γ) (x : L) :
    toHahnModule R Γ L (AddMonoidAlgebra.single a 1 ⊗ₜ[R] x) = of R (HahnSeries.single a x) := by
  simp [toHahnModule]

/-- Distinct polynomial loops have distinct images in the Hahn series. -/
theorem toHahnModule_injective : Function.Injective (toHahnModule R Γ L) := fun p q h ↦
  (toFinsupp R Γ L).injective <| Finsupp.ext fun a ↦ by
    rw [← coeff_toHahnModule, ← coeff_toHahnModule, h]

end LieAlgebra.LoopAlgebra
