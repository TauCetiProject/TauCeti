/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import TauCeti.Algebra.Lie.Loop.HahnModule
public import TauCeti.RingTheory.LaurentSeries.ModuleDerivative
-- Proof-only: the loop residue pairing on modes.
import TauCeti.Algebra.Lie.Loop.Cocycle

/-!
# The derivative and residue pairing of formal loops

For a Lie algebra `L` over a commutative ring `R`, the formal loop algebra `L((t))` is
`HahnModule ℤ R L` with the coefficient convolution bracket. Its derivative `D`, the derivative
`HahnModule.derivative R` of `L`-valued Laurent series, is a Lie derivation:
`D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆`.

For a bilinear form `Φ` on `L`, the residue pairing `(x, y) ↦ Res Φ(x, D y) dt` restricts along the
embedding `LieAlgebra.LoopAlgebra.toHahnModule` of polynomial loops to Mathlib's residue pairing
`LieAlgebra.LoopAlgebra.residuePairing` on `loopAlgebra R ℤ L`. In particular a mode `x t⁻ⁿ` pairs
with a mode `y tⁿ` to `n Φ(x, y)`.

## Main definitions and results

* `HahnModule.derivative_lie`: the Leibniz rule `D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆`.
* `HahnModule.lieDerivation R L`: the derivative of formal loops as a Lie derivation.
* `LieAlgebra.LoopAlgebra.residuePairing_toHahnModule`: the residue pairing of formal loops
  restricts to Mathlib's residue pairing of polynomial loops.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3.
-/

public section

noncomputable section

open HahnSeries

namespace HahnModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **The Leibniz rule** `D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆` for the bracket of formal loops: the
bracket is the coefficientwise extension of the bracket of `L`. -/
theorem derivative_lie (x y : HahnModule ℤ R L) :
    derivative R ⁅x, y⁆ = ⁅derivative R x, y⁆ + ⁅x, derivative R y⁆ :=
  (of R).symm.injective <| by
    rw [of_symm_derivative, of_symm_add, of_symm_lie, of_symm_lie, of_symm_lie]
    exact derivative_convolutionAddMonoidHom _ x y

variable (R L) in
/-- The derivative of formal loops `L((t))` as a Lie derivation. -/
def lieDerivation : LieDerivation R (HahnModule ℤ R L) (HahnModule ℤ R L) where
  toLinearMap := derivative R
  leibniz' x y := by
    rw [derivative_lie, ← lie_skew (derivative R x) y, sub_eq_add_neg, add_comm]

/-- The Lie derivation of formal loops evaluates as the derivative. -/
@[simp]
theorem lieDerivation_apply (x : HahnModule ℤ R L) :
    lieDerivation R L x = derivative R x :=
  (rfl)

end HahnModule

namespace LieAlgebra.LoopAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The residue pairing `(x, y) ↦ Res Φ(x, D y) dt` of formal loops restricts along the embedding
of polynomial loops to Mathlib's residue pairing of polynomial loops. -/
theorem residuePairing_toHahnModule (Φ : LinearMap.BilinForm R L) (p q : loopAlgebra R ℤ L) :
    HahnModule.residuePairing R Φ (toHahnModule R ℤ L p) (toHahnModule R ℤ L q) =
      residuePairing R ℤ L Φ p q := by
  obtain ⟨f, rfl⟩ := (toFinsupp R ℤ L).symm.surjective p
  obtain ⟨g, rfl⟩ := (toFinsupp R ℤ L).symm.surjective q
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | single m x =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single n y =>
      rw [toFinsupp_symm_single, toFinsupp_symm_single, toHahnModule_single_tmul,
        toHahnModule_single_tmul, HahnModule.residuePairing_single_single,
        TauCeti.LieAlgebra.LoopAlgebra.residuePairing_single_tmul]

end LieAlgebra.LoopAlgebra
