/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.Algebra.Lie.Sl2.Spectrum

/-!
# Rotation speeds in finite-dimensional representations of `so(3)`

Let `a₀, a₁, a₂` be elements of a real Lie algebra satisfying the cyclic relations
`⁅a₀, a₁⁆ = a₂`, `⁅a₁, a₂⁆ = a₀`, `⁅a₂, a₀⁆ = a₁` of the standard basis of `so(3) ≅ 𝔰𝔲(2)`
(`TauCeti.soThreeLieHom`). In a finite-dimensional real representation `M`, the generator `a₂`
of the rotations about the third axis can only rotate a plane at a half-integer speed: if
`⁅a₂, u⁆ = c w` and `⁅a₂, w⁆ = -c u` with `u ≠ 0`, then `2 c` is an integer
(`TauCeti.exists_int_two_mul_eq_of_lie_eq_smul`). For `so(3)` acting on `ℝ³` the speeds are the
integers `0, 1`, and for `𝔰𝔲(2) ≅ so(3)` acting on `ℂ² = ℝ⁴` they are `± 1/2`.

The reason is that the complexification of `so(3)` is `𝔰𝔩₂(ℂ)`. In a complex Lie algebra the
elements

`h = 2 i a₂`, `e = i a₀ - a₁`, `f = i a₀ + a₁`

form an `𝔰𝔩₂` triple as soon as `a₂ ≠ 0` (`TauCeti.isSl2Triple_two_mul_I_smul`). On
`ℂ ⊗ M`, the vector `1 ⊗ u + i ⊗ w` is an eigenvector of `h` with eigenvalue `2 c`, and the
eigenvalues of the Cartan element of an `𝔰𝔩₂` triple in a finite-dimensional module are integers
(`TauCeti.exists_int_of_lie_h_eq_smul`).

Applied to the adjoint representation of a compact Lie algebra, this is the integrality of the
Cartan integers of its real roots.

## Main results

* `TauCeti.isSl2Triple_two_mul_I_smul`: the complexified `so(3)` triple is an `𝔰𝔩₂` triple.
* `TauCeti.exists_int_two_mul_eq_of_lie_eq_smul`: the rotation speeds of `a₂` in a
  finite-dimensional real representation are half-integers.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter II, §5 (the representations of `SU(2)` and `SO(3)`)
  and Chapter V, §2.
-/

public section

open Complex TensorProduct

namespace TauCeti

/-- **The complexification of `so(3)` is `𝔰𝔩₂(ℂ)`.** If `a₀, a₁, a₂` in a complex Lie algebra
satisfy the cyclic relations `⁅a₀, a₁⁆ = a₂`, `⁅a₁, a₂⁆ = a₀`, `⁅a₂, a₀⁆ = a₁` of `so(3)` and
`a₂ ≠ 0`, then `(2 i a₂, i a₀ - a₁, i a₀ + a₁)` is an `𝔰𝔩₂` triple. -/
theorem isSl2Triple_two_mul_I_smul {L : Type*} [LieRing L] [LieAlgebra ℂ L] {a : Fin 3 → L}
    (h₀ : ⁅a 0, a 1⁆ = a 2) (h₁ : ⁅a 1, a 2⁆ = a 0) (h₂ : ⁅a 2, a 0⁆ = a 1) (ha : a 2 ≠ 0) :
    IsSl2Triple ((2 * I) • a 2) (I • a 0 - a 1) (I • a 0 + a 1) where
  h_ne_zero := smul_ne_zero (by simp) ha
  lie_e_f := by
    have h₀' : ⁅a 1, a 0⁆ = -a 2 := by rw [← lie_skew, h₀]
    simp only [sub_lie, lie_add, smul_lie, lie_smul, lie_self, h₀, h₀', smul_zero]
    module
  lie_h_e_nsmul := by
    have h₁' : ⁅a 2, a 1⁆ = -a 0 := by rw [← lie_skew, h₁]
    simp only [lie_sub, smul_lie, lie_smul, h₂, h₁', smul_smul]
    match_scalars
    · linear_combination 2 * I_sq
    · ring
  lie_h_f_nsmul := by
    have h₁' : ⁅a 2, a 1⁆ = -a 0 := by rw [← lie_skew, h₁]
    simp only [lie_add, smul_lie, lie_smul, h₂, h₁', smul_smul]
    match_scalars
    · linear_combination 2 * I_sq
    · ring

/-- **Rotation speeds in representations of `so(3)` are half-integers.** Let `a₀, a₁, a₂` in a real
Lie algebra `L` satisfy the cyclic relations `⁅a₀, a₁⁆ = a₂`, `⁅a₁, a₂⁆ = a₀`, `⁅a₂, a₀⁆ = a₁` of
`so(3)`, and let `M` be a finite-dimensional `L`-module. If `a₂` rotates a pair `u ≠ 0, w` at speed
`c`, `⁅a₂, u⁆ = c w` and `⁅a₂, w⁆ = -c u`, then `2 c` is an integer. -/
theorem exists_int_two_mul_eq_of_lie_eq_smul {L M : Type*} [LieRing L] [LieAlgebra ℝ L]
    [AddCommGroup M] [Module ℝ M] [LieRingModule L M] [LieModule ℝ L M] [Module.Finite ℝ M]
    {a : Fin 3 → L} (h₀ : ⁅a 0, a 1⁆ = a 2) (h₁ : ⁅a 1, a 2⁆ = a 0) (h₂ : ⁅a 2, a 0⁆ = a 1)
    {u w : M} {c : ℝ} (hu : ⁅a 2, u⁆ = c • w) (hw : ⁅a 2, w⁆ = -(c • u)) (hu0 : u ≠ 0) :
    ∃ n : ℤ, 2 * c = n := by
  -- Pass to the complexifications `ℂ ⊗ L` and `ℂ ⊗ M`.
  let A : Fin 3 → ℂ ⊗[ℝ] L := fun i ↦ (1 : ℂ) ⊗ₜ a i
  have hA (i j : Fin 3) : ⁅A i, A j⁆ = (1 : ℂ) ⊗ₜ ⁅a i, a j⁆ := by
    simp [A, LieAlgebra.ExtendScalars.bracket_tmul]
  let U : ℂ ⊗[ℝ] M := (1 : ℂ) ⊗ₜ u
  let W : ℂ ⊗[ℝ] M := (1 : ℂ) ⊗ₜ w
  let T := LieModule.toEnd ℂ (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] M)
  have hU : T (A 2) U = (c : ℂ) • W := by
    simp [T, A, U, W, hu, tmul_smul, ← algebraMap_smul ℂ c]
  have hW : T (A 2) W = -((c : ℂ) • U) := by
    simp [T, A, U, W, hw, tmul_neg, tmul_smul, ← algebraMap_smul ℂ c]
  -- The vector `1 ⊗ u + i ⊗ w` is an eigenvector of `h = 2 i a₂` with eigenvalue `2 c`.
  have hlie : T ((2 * I) • A 2) (U + I • W) = ((2 * c : ℝ) : ℂ) • (U + I • W) := by
    simp only [map_smul, map_add, LinearMap.smul_apply, hU, hW, smul_add, smul_neg, smul_smul]
    match_scalars
    · ring
    · linear_combination (-2 * (c : ℂ)) * I_sq
  -- It is nonzero, since its real part is `u`.
  have hm0 : U + I • W ≠ 0 := by
    intro h
    have := congrArg (TensorProduct.lift ((LinearMap.lsmul ℝ M).comp reLm)) h
    simp [U, W, smul_tmul', hu0] at this
  by_cases hh : (2 * I) • A 2 = 0
  · -- If `a₂` acts by zero on the complexification, the speed `c` vanishes.
    refine ⟨0, ?_⟩
    rw [hh, map_zero, LinearMap.zero_apply] at hlie
    have := (smul_eq_zero.mp hlie.symm).resolve_right hm0
    exact_mod_cast this
  · have hA2 : A 2 ≠ 0 := fun h ↦ hh (by rw [h, smul_zero])
    rw [LieModule.toEnd_apply_apply] at hlie
    obtain ⟨n, hn⟩ := exists_int_of_lie_h_eq_smul
      (isSl2Triple_two_mul_I_smul (by rw [hA, h₀]) (by rw [hA, h₁]) (by rw [hA, h₂]) hA2) hlie hm0
    exact ⟨n, by exact_mod_cast hn⟩

end TauCeti
