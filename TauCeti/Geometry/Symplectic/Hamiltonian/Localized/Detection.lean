/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Localized.Manifold
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Detecting covectors by localized Hamiltonian variations

A nonzero continuous covector field along a continuous map into a manifold pairs positively
with some smooth, compactly supported, parameter-dependent Hamiltonian vector field. The
Hamiltonian can be supported in any neighborhood of the chosen parameter/target point.
Consequently, a continuous covector annihilating all these variations vanishes there.

Both the parameter and target may be manifolds. Covector continuity is continuity into the
cotangent bundle, not continuity of its components in an arbitrary tangent identification.
No injectivity or nonconstancy of the map is required: localization in the parameter separates
points with identical target images. The two-form need only be nondegenerate, not closed.
These results supply the Hamiltonian-direction detection argument for inhomogeneous curve
operators; they do not assert Fredholmness, unique continuation, or universal regularity.

The proof combines the intrinsic first-jet realization
`SmoothTwoForm.exists_contMDiff_hamiltonianVectorField_eq` with a nonnegative parameter bump.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on localized Hamiltonian variations in the universal Cauchy–Riemann operator.
-/

public noncomputable section

open Set Topology Manifold MeasureTheory MeasureTheory.Measure Bundle
open scoped ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M Q G P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [TopologicalSpace G] {J : ModelWithCorners ℝ Q G}
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold J ∞ P] [T2Space P]
  {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
  {u : P → M}
  {η : ∀ p, TangentSpace I (u p) →L[ℝ] ℝ}
  (hη : Continuous (fun p ↦ (⟨u p, η p⟩ : CotangentBundle I M)))

include hσ hη

omit [T2Space M] [FiniteDimensional ℝ Q] [T2Space P] [IsManifold J ∞ P] in
/-- A continuous covector along a continuous map pairs continuously with the Hamiltonian
vector field of a jointly `C¹` family. -/
theorem IsNondegenerate.continuous_apply_hamiltonianVectorField [IsManifold J 1 P]
    {K : P → M → ℝ} (hK : ContMDiff (J.prod I) 𝓘(ℝ) 1 (Function.uncurry K)) :
    Continuous (fun p ↦ η p (σ.hamiltonianVectorField (K p) (u p))) := by
  have hu : Continuous u :=
    (FiberBundle.continuous_proj (E →L[ℝ] ℝ) _).comp hη
  have hX := (hσ.contMDiff_hamiltonianVectorField_uncurry (n := 0) (by simp)
    (hK.of_le (by simp))).continuous.comp (continuous_id.prodMk hu)
  have h := Continuous.clm_bundle_apply (E₂ := Bundle.Trivial M ℝ) hη hX
  exact continuous_snd.comp ((Bundle.Trivial.homeomorphProd M ℝ).continuous.comp h)

variable [MeasurableSpace P] [BorelSpace P] {μ : Measure P}
  [IsFiniteMeasureOnCompacts μ] [IsOpenPosMeasure μ]

omit [T2Space M] in
/-- Cut off a Hamiltonian in the parameter near a point where its covector pairing is positive.
The cutoff preserves the joint support constraint and makes the pairing integrable and
nonnegative everywhere. -/
private theorem exists_cutoff_integral_pos {K : P → M → ℝ}
    (hK : ContMDiff (J.prod I) 𝓘(ℝ) ∞ (Function.uncurry K))
    (hKc : HasCompactSupport (Function.uncurry K)) {U : Set (P × M)}
    (hKU : tsupport (Function.uncurry K) ⊆ U) {p : P}
    (hp : 0 < η p (σ.hamiltonianVectorField (K p) (u p))) :
    ∃ L : P → M → ℝ, ContMDiff (J.prod I) 𝓘(ℝ) ∞ (Function.uncurry L) ∧
      HasCompactSupport (Function.uncurry L) ∧ tsupport (Function.uncurry L) ⊆ U ∧
      Integrable (fun q ↦ η q (σ.hamiltonianVectorField (L q) (u q))) μ ∧
      0 < ∫ q, η q (σ.hamiltonianVectorField (L q) (u q)) ∂μ := by
  let f : P → ℝ := fun q ↦ η q (σ.hamiltonianVectorField (K q) (u q))
  have hf : Continuous f :=
    hσ.continuous_apply_hamiltonianVectorField hη (hK.of_le (by simp))
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := J) p).mem_iff.1
    (hf.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp))
  let L : P → M → ℝ := fun q ↦ b q • K q
  have heq (q : P) : η q (σ.hamiltonianVectorField (L q) (u q)) = b q * f q := by
    simp [L, f, hamiltonianVectorField_const_smul]
  have hbc : HasCompactSupport (fun q ↦ b q * f q) := b.hasCompactSupport.mul_right
  have hcont : Continuous (fun q ↦ b q * f q) := b.contMDiff.continuous.mul hf
  have hnonneg (q : P) : 0 ≤ b q * f q := by
    by_cases hq : q ∈ tsupport b
    · exact mul_nonneg b.nonneg (le_of_lt (hb hq))
    · simp [image_eq_zero_of_notMem_tsupport hq]
  have hbp : b p * f p ≠ 0 := by simpa using ne_of_gt hp
  refine ⟨L, (b.contMDiff.comp contMDiff_fst).smul hK, hKc.smul_left,
    (tsupport_smul_subset_right (fun z : P × M ↦ b z.1)
      (Function.uncurry K)).trans hKU, ?_, ?_⟩
  · simpa only [heq] using hcont.integrable_of_hasCompactSupport hbc
  · simpa only [heq] using
      hcont.integral_pos_of_hasCompactSupport_nonneg_ne_zero hbc hnonneg hbp

/-- A nonzero continuous covector along a map into a nondegenerate manifold is detected by a
smooth Hamiltonian variation supported in any neighborhood of the parameter/target point.
Its pairing is integrable and has strictly positive integral. This applies equally to constant
maps and to nonconstant maps. -/
theorem IsNondegenerate.exists_contMDiff_integral_apply_hamiltonianVectorField_pos
    {p : P} (hp : η p ≠ 0) {U : Set (P × M)} (hU : U ∈ 𝓝 (p, u p)) :
    ∃ K : P → M → ℝ, ContMDiff (J.prod I) 𝓘(ℝ) ∞ (Function.uncurry K) ∧
      HasCompactSupport (Function.uncurry K) ∧ tsupport (Function.uncurry K) ⊆ U ∧
      Integrable (fun q ↦ η q (σ.hamiltonianVectorField (K q) (u q))) μ ∧
      0 < ∫ q, η q (σ.hamiltonianVectorField (K q) (u q)) ∂μ := by
  have hv : ∃ v, η p v ≠ 0 := by
    by_contra! h
    exact hp (ContinuousLinearMap.ext h)
  obtain ⟨v, hv⟩ := hv
  obtain ⟨K, hK, hKc, hKU, -, hKv⟩ :=
    exists_contMDiff_hamiltonianVectorField_eq (J := J) p (u p)
      (hσ.isInvertible_flat _) ((η p v) • v) hU
  apply exists_cutoff_integral_pos hσ hη hK hKc hKU
  rw [hKv, map_smul, smul_eq_mul]
  exact mul_self_pos.mpr hv

/-- A continuous covector annihilating all smooth Hamiltonian variations in a neighborhood of
one parameter/target point vanishes at that parameter. Integrability is included explicitly
in the test class, so the hypothesis does not use totalized integrals of nonintegrable tests. -/
theorem IsNondegenerate.eq_zero_of_integral_apply_hamiltonianVectorField_eq_zero
    {p : P} {U : Set (P × M)} (hU : U ∈ 𝓝 (p, u p))
    (h : ∀ K : P → M → ℝ,
      ContMDiff (J.prod I) 𝓘(ℝ) ∞ (Function.uncurry K) →
      HasCompactSupport (Function.uncurry K) → tsupport (Function.uncurry K) ⊆ U →
      Integrable (fun q ↦ η q (σ.hamiltonianVectorField (K q) (u q))) μ →
      ∫ q, η q (σ.hamiltonianVectorField (K q) (u q)) ∂μ = 0) :
    η p = 0 := by
  by_contra hp
  obtain ⟨K, hK, hKc, hKU, hKi, hKpos⟩ :=
    hσ.exists_contMDiff_integral_apply_hamiltonianVectorField_pos (J := J) (μ := μ) hη hp hU
  exact (ne_of_gt hKpos) (h K hK hKc hKU hKi)

end TauCeti.SmoothTwoForm
