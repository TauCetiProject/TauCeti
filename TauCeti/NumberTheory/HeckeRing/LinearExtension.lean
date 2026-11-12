/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Opposite
public import TauCeti.NumberTheory.HeckeRing.Multiplication

/-!
# Multiplicativity of a linear extension is a basis-level condition

A `Z`-linear map out of the Hecke ring is determined by its values on the basis elements
`single Z D 1`, one for each double coset. The same is true of its *multiplicativity*:
`F (x * y) = F x * F y` for all `x` and `y` follows from the special case where both arguments
are basis elements, and likewise for the reversed identity `F (x * y) = F y * F x`.

## The reversed identity

The Hecke ring acts on modular forms through the slash, which is a *right* action, while
`Module.End` multiplies by composition; that is what motivates recording the reversed order
alongside the plain one, so a consumer whose basis identity comes out reversed — as
`HeckeRing.GL2.twistedHeckeSlashRingCharLinearMap_mul_single_single` does — need not route
through `MulOpposite` itself. Both live in the `LinearMap` namespace, so a consumer writes
`F.map_mul_of_basis`.

## Main results

* `HeckeCosetModule.map_mul_of_structureConstants`: linear maps on `HeckeCosetModule` acting on
  basis elements via `HeckeCoset.map` intertwine `HeckeCosetModule.mul` whenever they preserve
  `structureConstants` on chosen representatives.
* `LinearMap.map_mul_of_basis`: a linear map that is multiplicative on basis elements is
  multiplicative.
* `LinearMap.map_mul_reverse_of_basis`: the same with the factors on the right-hand side in
  the opposite order.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1 (the Hecke ring as a free module on the double cosets).
-/

public section

namespace HeckeCosetModule

section Basis

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G} [IsHeckeTriple Δ H H]
variable {Z : Type*} [Semiring Z] {A : Type*} [NonUnitalNonAssocSemiring A] [Module Z A]
  [IsScalarTower Z A A] [SMulCommClass Z A A]

/-- The product of two basis elements is the product of the two *unit* basis elements, scaled by
the two coefficients. This is `single_mul_single` with the structure constants eliminated between
the general and the unit case, which is the form the reductions below consume. -/
private lemma single_mul_single_eq_smul_smul (D₁ D₂ : HeckeCoset Δ H H) (a b : Z) :
    single Z D₁ a * single Z D₂ b = a • b • (single Z D₁ 1 * single Z D₂ 1) := by
  rw [single_mul_single, single_mul_single, one_smul, one_smul]

end Basis

section BimoduleMap

variable {G : Type*} [Group G] {Δ₁ Δ₂ : Submonoid G} {H₁ H₂ H₃ H₁' H₂' H₃' : Subgroup G}
  (R : Type*) [Semiring R]

/-- `R`-linear maps between Hecke coset modules that send basis elements along `HeckeCoset.map`
intertwine the bimodule convolution product `HeckeCosetModule.mul` whenever they map
`structureConstants` at chosen representatives to `structureConstants` at the mapped
representatives. -/
theorem map_mul_of_structureConstants
    [IsHeckeTriple Δ₁ H₁ H₂] [IsHeckeTriple Δ₁ H₂ H₃]
    [IsHeckeTriple Δ₂ H₁' H₂'] [IsHeckeTriple Δ₂ H₂' H₃']
    (hΔ : Δ₁ ≤ Δ₂) (h₁ : H₁ ≤ H₁') (h₂ : H₂ ≤ H₂') (h₃ : H₃ ≤ H₃')
    (L₁₂ : HeckeCosetModule Δ₁ H₁ H₂ R →ₗ[R] HeckeCosetModule Δ₂ H₁' H₂' R)
    (L₂₃ : HeckeCosetModule Δ₁ H₂ H₃ R →ₗ[R] HeckeCosetModule Δ₂ H₂' H₃' R)
    (L₁₃ : HeckeCosetModule Δ₁ H₁ H₃ R →ₗ[R] HeckeCosetModule Δ₂ H₁' H₃' R)
    (hL₁₂ : ∀ D a, L₁₂ (single R D a) = single R (D.map hΔ h₁ h₂) a)
    (hL₂₃ : ∀ D b, L₂₃ (single R D b) = single R (D.map hΔ h₂ h₃) b)
    (hSC : ∀ (D₁ : HeckeCoset Δ₁ H₁ H₂) (D₂ : HeckeCoset Δ₁ H₂ H₃),
      L₁₃ (structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep) =
        structureConstants R H₁' H₂' H₃' (D₁.map hΔ h₁ h₂).rep (D₂.map hΔ h₂ h₃).rep)
    (f : HeckeCosetModule Δ₁ H₁ H₂ R) (g : HeckeCosetModule Δ₁ H₂ H₃ R) :
    L₁₃ (mul R f g) = mul R (L₁₂ f) (L₂₃ g) := by
  induction f using HeckeCosetModule.induction_linear with
  | h0 => simp [zero_mul]
  | hadd _ _ ih₁ ih₂ => simp only [add_mul, map_add, ih₁, ih₂]
  | hsingle D₁ a =>
    induction g using HeckeCosetModule.induction_linear with
    | h0 => simp [mul_zero]
    | hadd _ _ ih₁ ih₂ => simp only [mul_add, map_add, ih₁, ih₂]
    | hsingle D₂ b =>
      rw [mul_single_single, map_smul, map_smul, hSC D₁ D₂, hL₁₂, hL₂₃, mul_single_single]

end BimoduleMap

end HeckeCosetModule

namespace LinearMap

open scoped HeckeCosetModule

variable {G : Type*} [Group G] {Δ : Submonoid G} {H : Subgroup G} [IsHeckeTriple Δ H H]
variable {Z : Type*} [Semiring Z] {A : Type*} [NonUnitalNonAssocSemiring A] [Module Z A]
  [IsScalarTower Z A A] [SMulCommClass Z A A]

/-- **Multiplicativity is a basis-level condition.** A `Z`-linear map out of the Hecke ring that
is multiplicative on the basis elements `HeckeCosetModule.single Z D 1` is multiplicative. -/
theorem map_mul_of_basis (F : 𝕋 Δ H Z →ₗ[Z] A)
    (h : ∀ D₁ D₂ : HeckeCoset Δ H H,
      F (HeckeCosetModule.single Z D₁ 1 * HeckeCosetModule.single Z D₂ 1) =
        F (HeckeCosetModule.single Z D₁ 1) * F (HeckeCosetModule.single Z D₂ 1))
    (x y : 𝕋 Δ H Z) : F (x * y) = F x * F y := by
  -- Both sides are biadditive in `(x, y)`, so `induction_linear` in each argument reduces to a
  -- pair of basis elements; there `single_mul_single_eq_smul_smul` releases the two coefficients
  -- and linearity of `F` puts them back.
  induction x using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd x₁ x₂ h₁ h₂ => rw [_root_.add_mul, map_add, map_add, h₁, h₂, _root_.add_mul]
  | hsingle D₁ a =>
    induction y using HeckeCosetModule.induction_linear with
    | h0 => simp
    | hadd y₁ y₂ h₁ h₂ => rw [_root_.mul_add, map_add, map_add, h₁, h₂, _root_.mul_add]
    | hsingle D₂ b =>
      rw [HeckeCosetModule.single_mul_single_eq_smul_smul, map_smul, map_smul, h,
        ← HeckeCosetModule.smul_single_one Z D₁ a, ← HeckeCosetModule.smul_single_one Z D₂ b,
        map_smul, map_smul, smul_mul_assoc, mul_smul_comm]

/-- **Anti-multiplicativity is a basis-level condition.** A `Z`-linear map out of the Hecke ring
that sends a product of basis elements to the product of their images *in the opposite order* does
so on all of the ring.

This is the order a right action produces, so it is the shape a slash-derived extension arrives
in. -/
theorem map_mul_reverse_of_basis (F : 𝕋 Δ H Z →ₗ[Z] A)
    (h : ∀ D₁ D₂ : HeckeCoset Δ H H,
      F (HeckeCosetModule.single Z D₁ 1 * HeckeCosetModule.single Z D₂ 1) =
        F (HeckeCosetModule.single Z D₂ 1) * F (HeckeCosetModule.single Z D₁ 1))
    (x y : 𝕋 Δ H Z) : F (x * y) = F y * F x :=
  -- `op` turns the reversed hypothesis into the plain one over `Aᵐᵒᵖ`, so this is
  -- `map_mul_of_basis` for `op ∘ F`, read back through `unop`.
  congrArg MulOpposite.unop <|
    map_mul_of_basis ((MulOpposite.opLinearEquiv Z).toLinearMap.comp F)
      (fun D₁ D₂ ↦ by simpa [MulOpposite.op_mul] using congrArg MulOpposite.op (h D₁ D₂)) x y

end LinearMap

end
