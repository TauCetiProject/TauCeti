/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Symmetric complex-linear interpolation

For a symmetric bilinear form preserved by a complex structure `J`, a self-adjoint
endomorphism commuting with `J` can send a nonisotropic vector `z` to `ξ` precisely when
`ξ` is orthogonal to `J z`. The construction uses rank-one maps and does not require
finite dimension or positive definiteness.

This is the pointwise linear algebra used in the localized transversality argument of
Floer--Hofer--Salamon, *Transversality in elliptic Morse theory for the symplectic action*,
Duke Math. J. 80 (1995), 251--292. The orthogonality condition is essential.
-/

public section

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  (J : TauCeti.AlmostComplexStructure V) {g : LinearMap.BilinForm ℝ V}

/-- A self-adjoint complex-linear map sends every vector to the orthogonal complement
of its complex rotation. -/
theorem bilinForm_apply_complex_rotation_eq_zero (hg : g.IsSymm)
    (hgJ : ∀ v w, g (J v) (J w) = g v w) {S : V →ₗ[ℝ] V}
    (hS : LinearMap.IsAdjointPair g g S S) (hSJ : IsComplexLinearMap J J S) (z : V) :
    g (S z) (J z) = 0 := by
  have hskew := J.bilinForm_apply_left_eq_neg_apply_right hgJ (S z) z
  have hcomm := (isComplexLinearMap_iff_apply J J S).mp hSJ z
  have hsym := hS z (J z)
  have hswap := hg.eq (S (J z)) z
  rw [hcomm] at hsym hswap
  linarith

/-- At a nonisotropic vector, orthogonality to its complex rotation is sufficient for
interpolation by a self-adjoint complex-linear endomorphism. -/
theorem exists_isAdjointPair_isComplexLinearMap_apply_eq (hg : g.IsSymm)
    (hgJ : ∀ v w, g (J v) (J w) = g v w) {z ξ : V} (hz : g z z ≠ 0)
    (hξ : g ξ (J z) = 0) :
    ∃ S : V →ₗ[ℝ] V, LinearMap.IsAdjointPair g g S S ∧
      IsComplexLinearMap J J S ∧ S z = ξ := by
  let K : V → V → V →ₗ[ℝ] V := fun v w ↦
    (g w).smulRight v + (g (J w)).smulRight (J v)
  have hK (v w x : V) : K v w x = g w x • v + g (J w) x • J v := by
    simp [K]
  have hKJ (v w : V) : IsComplexLinearMap J J (K v w) := by
    rw [isComplexLinearMap_iff_apply]
    intro x
    have hskew := J.bilinForm_apply_left_eq_neg_apply_right hgJ w x
    simp only [hK, hgJ, J.toLinearMap.map_add, J.toLinearMap.map_smul,
      J.apply_apply, smul_neg]
    rw [hskew]
    module
  have hKad (v w : V) : LinearMap.IsAdjointPair g g (K v w) (K w v) := by
    intro x y
    simp only [hK, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [hg.eq w x, hg.eq (J w) x]
    ring
  let c := (g z z)⁻¹
  let S := c • (K ξ z + K z ξ) - (g ξ z * c ^ 2) • K z z
  refine ⟨S, ?_, ?_, ?_⟩
  · have hsum : LinearMap.IsAdjointPair g g (K ξ z + K z ξ) (K ξ z + K z ξ) := by
      simpa only [add_comm] using (hKad ξ z).add (hKad z ξ)
    exact (hsum.smul c).sub ((hKad z z).smul (g ξ z * c ^ 2))
  · exact ((hKJ ξ z).add (hKJ z ξ)).smul c |>.sub ((hKJ z z).smul _)
  · have hzz := J.bilinForm_apply_apply_self_eq_zero hg hgJ z
    have hJzz : g (J z) z = 0 := by rw [hg.eq, hzz]
    have hJξz : g (J ξ) z = 0 := by
      rw [J.bilinForm_apply_left_eq_neg_apply_right hgJ, hξ, neg_zero]
    have hc : c * g z z = 1 := inv_mul_cancel₀ hz
    simp only [S, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
      hK, hJzz, hJξz, zero_smul, add_zero]
    rw [smul_add, smul_smul, hc, one_smul, smul_smul]
    have heq : c * g ξ z = g ξ z * c ^ 2 * g z z := by
      dsimp [c]
      field_simp
    rw [heq]
    module

/-- Characterization of the possible value at a nonisotropic vector of a self-adjoint
endomorphism commuting with the complex structure. -/
@[simp]
theorem exists_isAdjointPair_isComplexLinearMap_apply_eq_iff (hg : g.IsSymm)
    (hgJ : ∀ v w, g (J v) (J w) = g v w) {z ξ : V} (hz : g z z ≠ 0) :
    (∃ S : V →ₗ[ℝ] V, LinearMap.IsAdjointPair g g S S ∧
      IsComplexLinearMap J J S ∧ S z = ξ) ↔ g ξ (J z) = 0 := by
  constructor
  · rintro ⟨S, hS, hSJ, rfl⟩
    exact J.bilinForm_apply_complex_rotation_eq_zero hg hgJ hS hSJ z
  · exact J.exists_isAdjointPair_isComplexLinearMap_apply_eq hg hgJ hz

end TauCeti.AlmostComplexStructure
