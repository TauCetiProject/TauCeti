/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import TauCeti.Geometry.Symplectic.Hamiltonian.Localized

/-!
# Localized coefficient directions for the Floer operator

At a fixed domain point, compactly supported smooth variations of the `ds` component of the
Hamiltonian perturbation realize every vector in the target of the Floer operator. The
perturbation is supported in any specified neighborhood of the domain/target point. In
particular, it can be confined to a compact core, leaving the cylindrical end data unchanged.

The realization is an exact affine identity for the nonlinear operator, not only a formal
linearization: adding `r δK_s` changes its value by `r v`. Consequently its parameter derivative
is `v`. There is no immersion or nonconstancy hypothesis on the map. This distinguishes
Hamiltonian variations from variations of the almost complex structure, which multiply the
perturbed derivative of the map.

These are coordinate-level range statements. They do not assert surjectivity of a Sobolev
operator, unique continuation, or regularity of any moduli space.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on Hamiltonian variations in the universal inhomogeneous Cauchy–Riemann operator.
-/

public section

open Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The Floer operator is affine in a differentiable Hamiltonian variation of its `ds`
component. Neither the map nor the endomorphism field needs to be differentiable for this
pointwise identity. -/
theorem floerOperator_add_const_mul_left (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt δK : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ)
    (hKs : DifferentiableAt ℝ (Ks z) (u z))
    (hδK : DifferentiableAt ℝ (δK z) (u z)) (r : ℝ) :
    ω.floerOperator J (fun w y ↦ Ks w y + r * δK w y) Kt u z =
      ω.floerOperator J Ks Kt u z - r • ω.hamiltonianVectorField (δK z) (u z) := by
  have hX := ω.hamiltonianVectorField_const_mul_add_const_mul hKs hδK 1 r
  simp only [one_mul, one_smul] at hX
  simp only [floerOperator_def, hX]
  abel

/-- A smooth Hamiltonian variation supported in any neighborhood of `(z, u z)` realizes any
prescribed direction of the Floer operator. The formula holds for every real parameter, and
also when `u` is constant. Only the original `ds` Hamiltonian must be differentiable at the
point in question. -/
theorem exists_contDiff_floerOperator_add_const_mul_left (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) (v : V)
    (hKs : DifferentiableAt ℝ (Ks z) (u z))
    {U : Set ((ℝ × ℝ) × V)} (hU : U ∈ 𝓝 (z, u z)) :
    ∃ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry δK) ∧
      HasCompactSupport (Function.uncurry δK) ∧ tsupport (Function.uncurry δK) ⊆ U ∧
      δK z (u z) = 0 ∧ ∀ r : ℝ,
        ω.floerOperator J (fun w y ↦ Ks w y + r * δK w y) Kt u z =
          ω.floerOperator J Ks Kt u z + r • v := by
  obtain ⟨δK, hs, hc, hsub, hzero, hX⟩ :=
    ω.exists_contDiff_hamiltonianVectorField_eq z (u z) (-v) hU
  refine ⟨δK, hs, hc, hsub, hzero, fun r ↦ ?_⟩
  have hd : DifferentiableAt ℝ (δK z) (u z) :=
    (hs.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) (u z)
  rw [ω.floerOperator_add_const_mul_left J Ks Kt δK u z hKs hd, hX, smul_neg,
    sub_neg_eq_add]

/-- Localized smooth Hamiltonian variations give actual parameter derivatives of the Floer
operator in every prescribed direction, even along constant maps. The derivative is the same
at every parameter value. -/
theorem exists_contDiff_hasDerivAt_floerOperator (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) (v : V)
    (hKs : DifferentiableAt ℝ (Ks z) (u z))
    {U : Set ((ℝ × ℝ) × V)} (hU : U ∈ 𝓝 (z, u z)) :
    ∃ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry δK) ∧
      HasCompactSupport (Function.uncurry δK) ∧ tsupport (Function.uncurry δK) ⊆ U ∧
      ∀ r : ℝ, HasDerivAt
        (fun t : ℝ ↦ ω.floerOperator J (fun w y ↦ Ks w y + t * δK w y) Kt u z) v r := by
  obtain ⟨δK, hs, hc, hsub, -, h⟩ :=
    ω.exists_contDiff_floerOperator_add_const_mul_left J Ks Kt u z v hKs hU
  refine ⟨δK, hs, hc, hsub, fun r ↦ ?_⟩
  simp_rw [h]
  simpa using ((hasDerivAt_id r).smul_const v).const_add (ω.floerOperator J Ks Kt u z)

end TauCeti.SymplecticForm
