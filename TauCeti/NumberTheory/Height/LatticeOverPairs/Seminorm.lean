/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import TauCeti.NumberTheory.Height.LatticeOverPairs.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Conjugated seminorms of a twisted lattice

Applying a complex field automorphism to the coordinates of the distinguished lift and
then measuring in the rational Gram matrix gives a seminorm over `ℚ`, not in general over
`ℂ`. This makes rational rescaling of the lifts valid at every conjugate without assuming
that the field automorphism commutes with complex conjugation or is an isometry.

The squared norm is the one used for rational normalization in
`New.Data.span_short_integralRamified_eq_top` in `New/Reduction/ShortAndEnough.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public noncomputable section

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace TauCeti.TwistedLattice

variable {T C V : Type*} [One T] [Fintype C] [AddCommGroup V] [Module ℚ V] [Module ℂ V]
variable {S : T → Type*} [∀ t, NormedAddCommGroup (S t)] [∀ t, InnerProductSpace ℂ (S t)]

/-- The seminorm of the distinguished lift after applying `σ` to its coordinates. The scalar
field is `ℚ` because every complex field automorphism fixes the rational scalars. -/
def seminormAt (L : TwistedLattice S C V) (σ : ℂ ≃+* ℂ) : Seminorm ℚ V :=
  let G := L.gram.map (algebraMap ℚ ℂ)
  letI : SeminormedAddCommGroup (C → ℂ) := G.toSeminormedAddCommGroup L.posDef_gram.posSemidef
  letI : InnerProductSpace ℂ (C → ℂ) := G.toInnerProductSpace L.posDef_gram.posSemidef
  let f := (L.coord ∘ₗ L.lift 1).restrictScalars ℚ
  ((normSeminorm ℂ (C → ℂ)).restrictScalars ℚ).comp
    (LinearMap.pi fun i ↦ σ.toRatAlgEquiv.toLinearMap ∘ₗ (LinearMap.proj i ∘ₗ f))

/-- The conjugated seminorm is the square root of the conjugated squared norm. -/
theorem seminormAt_apply (L : TwistedLattice S C V) (σ : ℂ ≃+* ℂ) (x : V) :
    L.seminormAt σ x = Real.sqrt (L.normSqAt σ x) := by
  rw [seminormAt, normSqAt_def]
  simp only [Seminorm.comp_apply, Seminorm.coe_restrictScalars, coe_normSeminorm]
  rw [dotProduct_comm]
  -- The matrix-induced norm is defined as the square root of the real part of its pairing.
  rfl

/-- Squaring the conjugated seminorm recovers the Gram expression of the twisted lattice. -/
@[simp] theorem seminormAt_sq (L : TwistedLattice S C V) (σ : ℂ ≃+* ℂ) (x : V) :
    L.seminormAt σ x ^ 2 = L.normSqAt σ x := by
  rw [L.seminormAt_apply, Real.sq_sqrt (L.normSqAt_nonneg σ x)]

/-- At the identity embedding, the seminorm measures the usual norm of the distinguished lift. -/
@[simp] theorem seminormAt_refl (L : TwistedLattice S C V) (x : V) :
    L.seminormAt (RingEquiv.refl ℂ) x = ‖L.lift 1 x‖ := by
  rw [L.seminormAt_apply, L.normSqAt_refl, Real.sqrt_sq (norm_nonneg _)]

/-- Conjugating the coordinates does not change which vectors have zero seminorm: those killed
by the distinguished lift. -/
@[simp] theorem seminormAt_eq_zero_iff (L : TwistedLattice S C V) (σ : ℂ ≃+* ℂ) (x : V) :
    L.seminormAt σ x = 0 ↔ L.lift 1 x = 0 := by
  constructor
  · intro h
    have hsq : L.normSqAt σ x = 0 := by rw [← L.seminormAt_sq, h, zero_pow (by decide)]
    have hσ : (fun i ↦ σ (L.coord (L.lift 1 x) i)) = 0 := by
      by_contra hne
      have hpos : 0 < L.normSqAt σ x := by
        rw [L.normSqAt_def]
        exact L.posDef_gram.re_dotProduct_pos hne
      exact hpos.ne' hsq
    have hcoord : L.coord (L.lift 1 x) = 0 := funext fun i ↦ σ.injective (by
      simpa using congrFun hσ i)
    have hinner := L.inner_eq_dotProduct (L.lift 1 x) (L.lift 1 x)
    simpa [hcoord] using hinner
  · intro hx
    simp [L.seminormAt_apply, L.normSqAt_def, hx, ← Pi.zero_def]

omit [Module ℚ V] in
/-- A rational multiple changes the squared norm by the square of the rational norm, at every
complex field automorphism. -/
theorem normSqAt_rat_smul (L : TwistedLattice S C V) (σ : ℂ ≃+* ℂ) (c : ℚ) (x : V) :
    L.normSqAt σ ((c : ℂ) • x) = ‖c‖ ^ 2 * L.normSqAt σ x := by
  let : Module ℚ V := Module.restrictScalars ℚ ℂ V
  rw [Rat.cast_smul_eq_qsmul, ← L.seminormAt_sq σ (c • x), map_smul_eq_mul, mul_pow,
    L.seminormAt_sq]

end TauCeti.TwistedLattice
