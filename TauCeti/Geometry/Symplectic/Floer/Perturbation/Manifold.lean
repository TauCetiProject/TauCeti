/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.CovariantLinearization
public import TauCeti.Geometry.Symplectic.Hamiltonian.Localized.Detection

/-!
# Hamiltonian coefficient directions of the intrinsic Floer operator

For a map into a manifold, varying the two Hamiltonian coefficients of the Floer operator
has derivative `-X_δKs - J X_δKt`, in the actual tangent fiber at the image point. In fact,
the dependence on the real coefficient is affine. Compactly supported smooth variations
of the first coefficient realize every vector at a chosen domain point, while leaving
prescribed data outside any chosen domain/target neighborhood unchanged.

A continuous covector field along a map which annihilates all these coefficient derivatives
vanishes. This follows from the intrinsic Hamiltonian detection theorem
`SmoothTwoForm.IsNondegenerate.exists_contMDiff_integral_apply_hamiltonianVectorField_pos`.
It applies to constant as well as nonconstant maps: there is no injectivity hypothesis.
The covector is continuous as a section of the cotangent bundle, not just as a function
under a set-theoretic identification of tangent fibers.

The domain here is a coordinate plane, and the target is an actual manifold. Neither a
connection nor closedness of the nondegenerate two-form is needed for coefficient variation.
These statements are not Sobolev surjectivity, unique continuation, or moduli regularity
results. The integral detection theorem assumes continuity on the whole coordinate domain;
its test Hamiltonians can be confined to an arbitrarily small neighborhood in a compact core.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  Section 8.1 (Hamiltonian variations in the universal inhomogeneous curve operator).
-/

public noncomputable section

open Set Topology Manifold MeasureTheory MeasureTheory.Measure

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  (ω : SmoothTwoForm I M)
  (J : ℝ × ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x)
  (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M)

/-- Simultaneous Hamiltonian coefficient variation of the intrinsic Floer operator is affine.
The endomorphism field and the map need not be differentiable. -/
theorem floerOperator_add_smul (δKs δKt : ℝ × ℝ → M → ℝ) (z : ℝ × ℝ)
    (hKs : MDifferentiableAt I 𝓘(ℝ) (Ks z) (u z))
    (hKt : MDifferentiableAt I 𝓘(ℝ) (Kt z) (u z))
    (hδKs : MDifferentiableAt I 𝓘(ℝ) (δKs z) (u z))
    (hδKt : MDifferentiableAt I 𝓘(ℝ) (δKt z) (u z)) (r : ℝ) :
    ω.floerOperator J (fun w ↦ Ks w + r • δKs w) (fun w ↦ Kt w + r • δKt w) u z =
      ω.floerOperator J Ks Kt u z -
        r • (ω.hamiltonianVectorField (δKs z) (u z) +
          J z (u z) (ω.hamiltonianVectorField (δKt z) (u z))) := by
  rw [floerOperator_def, floerOperator_def,
    hamiltonianVectorField_add_smul hKs hδKs,
    hamiltonianVectorField_add_smul hKt hδKt]
  simp only [map_sub, map_add, map_smul, smul_add]
  abel

/-- Varying only the first Hamiltonian coefficient changes the operator by `-r X_δK`.
There is no differentiability requirement on the unchanged second coefficient. -/
theorem floerOperator_add_smul_left (δK : ℝ × ℝ → M → ℝ) (z : ℝ × ℝ)
    (hKs : MDifferentiableAt I 𝓘(ℝ) (Ks z) (u z))
    (hδK : MDifferentiableAt I 𝓘(ℝ) (δK z) (u z)) (r : ℝ) :
    ω.floerOperator J (fun w ↦ Ks w + r • δK w) Kt u z =
      ω.floerOperator J Ks Kt u z - r • ω.hamiltonianVectorField (δK z) (u z) := by
  rw [floerOperator_def, floerOperator_def, hamiltonianVectorField_add_smul hKs hδK]
  abel

/-- The derivative in a real coefficient of a variation of the first Hamiltonian is its
negative Hamiltonian vector. The tangent fiber is read in its model normed space. -/
theorem hasDerivAt_floerOperator_add_smul_left (δK : ℝ × ℝ → M → ℝ) (z : ℝ × ℝ)
    (hKs : MDifferentiableAt I 𝓘(ℝ) (Ks z) (u z))
    (hδK : MDifferentiableAt I 𝓘(ℝ) (δK z) (u z)) (r : ℝ) :
    HasDerivAt (fun a : ℝ ↦ (ω.floerOperator J (fun w ↦ Ks w + a • δK w) Kt u z : E))
      (-ω.hamiltonianVectorField (δK z) (u z) : E) r := by
  simp only [floerOperator_def]
  exact ((ω.hasDerivAt_hamiltonianVectorField_add_smul hKs hδK r).const_sub (F := E)
    (TauCeti.Manifold.curveVelocity I (fun s ↦ u (s, z.2)) z.1 : E)).add_const (F := E) _

variable [FiniteDimensional ℝ E] [T2Space M]

/-- A smooth variation supported in any neighborhood of the domain/target point realizes
any prescribed affine direction of the intrinsic Floer operator. Only invertibility of the
two-form at that target point is needed, and the Hamiltonian variation vanishes there. -/
theorem exists_contMDiff_floerOperator_add_smul_left (z : ℝ × ℝ)
    (hω : (ω.flat (u z)).IsInvertible) (v : TangentSpace I (u z))
    (hKs : MDifferentiableAt I 𝓘(ℝ) (Ks z) (u z))
    {U : Set ((ℝ × ℝ) × M)} (hU : U ∈ 𝓝 (z, u z)) :
    ∃ δK : ℝ × ℝ → M → ℝ,
      ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (⊤ : ℕ∞) (Function.uncurry δK) ∧
      HasCompactSupport (Function.uncurry δK) ∧ tsupport (Function.uncurry δK) ⊆ U ∧
      δK z (u z) = 0 ∧ ∀ r : ℝ,
        ω.floerOperator J (fun w ↦ Ks w + r • δK w) Kt u z =
          ω.floerOperator J Ks Kt u z + r • v := by
  obtain ⟨δK, hs, hc, hU', hzero, hX⟩ :=
    exists_contMDiff_hamiltonianVectorField_eq (J := 𝓘(ℝ, ℝ × ℝ)) z (u z) hω (-v) hU
  refine ⟨δK, hs, hc, hU', hzero, fun r ↦ ?_⟩
  have hd : MDifferentiableAt I 𝓘(ℝ) (δK z) (u z) :=
    (hs.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)
  rw [ω.floerOperator_add_smul_left J Ks Kt u δK z hKs hd, hX, smul_neg, sub_neg_eq_add]

variable {ω J Ks Kt u}
  {η : ∀ z, TangentSpace I (u z) →L[ℝ] ℝ}
  {μ : Measure (ℝ × ℝ)} [IsFiniteMeasureOnCompacts μ] [IsOpenPosMeasure μ]

/-- A nonzero continuous covector along a map pairs positively with the parameter derivative
of a localized smooth Hamiltonian variation of the intrinsic Floer operator. The test pairing
is integrable, and no differentiability or nonconstancy of the map is assumed. -/
theorem IsNondegenerate.exists_contMDiff_integral_apply_deriv_floerOperator_pos
    (hω : ω.IsNondegenerate)
    (hη : Continuous (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)))
    (hKs : ∀ z, MDifferentiableAt I 𝓘(ℝ) (Ks z) (u z))
    {z : ℝ × ℝ} (hz : η z ≠ 0) {U : Set ((ℝ × ℝ) × M)} (hU : U ∈ 𝓝 (z, u z)) :
    ∃ δK : ℝ × ℝ → M → ℝ,
      ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (⊤ : ℕ∞) (Function.uncurry δK) ∧
      HasCompactSupport (Function.uncurry δK) ∧ tsupport (Function.uncurry δK) ⊆ U ∧
      Integrable (fun w ↦ η w (deriv (fun a : ℝ ↦
        (ω.floerOperator J (fun p ↦ Ks p + a • δK p) Kt u w : E)) 0)) μ ∧
      0 < ∫ w, η w (deriv (fun a : ℝ ↦
        (ω.floerOperator J (fun p ↦ Ks p + a • δK p) Kt u w : E)) 0) ∂μ := by
  obtain ⟨K, hs, hc, hKU, hi, hp⟩ :=
    hω.exists_contMDiff_integral_apply_hamiltonianVectorField_pos
      (J := 𝓘(ℝ, ℝ × ℝ)) (μ := μ) hη hz hU
  have hd (w : ℝ × ℝ) : deriv (fun a : ℝ ↦
      (ω.floerOperator J (fun p ↦ Ks p + a • (-K) p) Kt u w : E)) 0 =
        (ω.hamiltonianVectorField (K w) (u w) : E) := by
    have hK : MDifferentiableAt I 𝓘(ℝ) ((-K) w) (u w) :=
      ((hs.neg).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by simp)
    have heq := HasDerivAt.deriv (F := E)
      (ω.hasDerivAt_floerOperator_add_smul_left J Ks Kt u (-K) w (hKs w) hK 0)
    simp only [Pi.neg_apply, hamiltonianVectorField_neg, neg_neg] at heq
    exact heq
  refine ⟨-K, hs.neg, hc.neg, ?_, ?_, ?_⟩
  · have hneg : Function.uncurry (-K) = -Function.uncurry K := rfl
    simpa only [hneg, tsupport_neg] using hKU
  · simpa only [hd] using hi
  · simpa only [hd] using hp

/-- A continuous covector annihilating all integrable localized Hamiltonian coefficient
derivatives of the intrinsic Floer operator vanishes at the chosen point. The test class
includes integrability, so totalized integrals of nonintegrable pairings are not used. -/
theorem IsNondegenerate.eq_zero_of_forall_integral_apply_deriv_floerOperator_eq_zero
    (hω : ω.IsNondegenerate)
    (hη : Continuous (fun z ↦ (⟨u z, η z⟩ : CotangentBundle I M)))
    (hKs : ∀ z, MDifferentiableAt I 𝓘(ℝ) (Ks z) (u z))
    {z : ℝ × ℝ} {U : Set ((ℝ × ℝ) × M)} (hU : U ∈ 𝓝 (z, u z))
    (h : ∀ δK : ℝ × ℝ → M → ℝ,
      ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (⊤ : ℕ∞) (Function.uncurry δK) →
      HasCompactSupport (Function.uncurry δK) → tsupport (Function.uncurry δK) ⊆ U →
      Integrable (fun w ↦ η w (deriv (fun a : ℝ ↦
        (ω.floerOperator J (fun p ↦ Ks p + a • δK p) Kt u w : E)) 0)) μ →
      ∫ w, η w (deriv (fun a : ℝ ↦
        (ω.floerOperator J (fun p ↦ Ks p + a • δK p) Kt u w : E)) 0) ∂μ = 0) :
    η z = 0 := by
  by_contra hz
  obtain ⟨δK, hs, hc, hKU, hi, hp⟩ :=
    hω.exists_contMDiff_integral_apply_deriv_floerOperator_pos
      (J := J) (Kt := Kt) (μ := μ) hη hKs hz hU
  exact (ne_of_gt hp) (h δK hs hc hKU hi)

end TauCeti.SmoothTwoForm
