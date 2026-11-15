/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.CarrierDilation

/-!
# Localizing a dilated lattice carrier

Multiplication by a nonzero integer commutes with localization of the integral carrier. In the
completed rational space, the embedded localization of the dilated carrier is exactly the
corresponding multiple of the embedded localization of the original carrier. The completed
rational form is unchanged; on the integral localizations the forms differ by the square of
the multiplier under the canonical carrier equivalence.
-/

public section

open Module TensorProduct
open scoped Pointwise

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) (p : ℕ) [Fact p.Prime]

/-- The localized carrier equivalence induced by multiplication by a nonzero integer. -/
noncomputable def localCarrierDilationEquiv (n : ℤ) (hn : n ≠ 0) :
    L.LocalCarrier p ≃ₗ[ℤ_[p]] (L.carrierDilation n hn).LocalCarrier p :=
  LinearEquiv.baseChange ℤ ℤ_[p] _ _ (L.carrierDilationEquiv n hn)

/-- The local integral pairing scales by the square of the carrier dilation. -/
theorem localIntegralForm_carrierDilationEquiv (n : ℤ) (hn : n ≠ 0)
    (x y : L.LocalCarrier p) :
    (L.carrierDilation n hn).localIntegralForm p
        (L.localCarrierDilationEquiv p n hn x)
        (L.localCarrierDilationEquiv p n hn y) =
      (n : ℤ_[p]) ^ 2 * L.localIntegralForm p x y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂, mul_add]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂, mul_add]
    | tmul b y =>
      simp only [localCarrierDilationEquiv, LinearEquiv.baseChange_tmul,
        localIntegralForm_tmul,
        integralForm_carrierDilationEquiv, Int.cast_mul, Int.cast_pow]
      ring

/-- Localizing the dilated carrier and then embedding it in the completed space is the same as
embedding the original localization and multiplying by the dilating integer. -/
theorem localizationToCompletion_carrierDilation (n : ℤ) (hn : n ≠ 0)
    (x : L.LocalCarrier p) :
    (L.carrierDilation n hn).localizationToCompletion p
        (L.localCarrierDilationEquiv p n hn x) =
      (n : ℤ_[p]) • L.localizationToCompletion p x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul a x =>
    simp only [localCarrierDilationEquiv, LinearEquiv.baseChange_tmul,
      localizationToCompletion_tmul,
      coe_carrierDilationEquiv_apply]
    simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]

/-- The embedded localization of `nL` is `n` times the embedded localization of `L`. -/
theorem range_localizationToCompletion_carrierDilation (n : ℤ) (hn : n ≠ 0) :
    LinearMap.range ((L.carrierDilation n hn).localizationToCompletion p) =
      (n : ℤ_[p]) • LinearMap.range (L.localizationToCompletion p) := by
  ext v
  simp only [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨L.localizationToCompletion p ((L.localCarrierDilationEquiv p n hn).symm x),
      ⟨_, rfl⟩, ?_⟩
    simpa using (L.localizationToCompletion_carrierDilation p n hn
      ((L.localCarrierDilationEquiv p n hn).symm x)).symm
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨L.localCarrierDilationEquiv p n hn x,
      L.localizationToCompletion_carrierDilation p n hn x⟩

end TauCeti.IntegralLattice
