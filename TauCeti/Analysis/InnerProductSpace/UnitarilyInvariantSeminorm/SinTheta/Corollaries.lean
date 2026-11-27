/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius.Basic
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Davis–Kahan `sin Θ` bounds for concrete norms

The Davis–Kahan bounds for an arbitrary unitarily invariant seminorm specialize to the
operator norm, the Frobenius norm and every Ky Fan norm, with constant `1` under
interval/exterior spectral separation.

For a single trial vector `x` and a real number `m`, the residual bound in the operator norm
reads `δ ‖P_{Uᗮ} x‖ ≤ ‖A x - m x‖`: it is the residual bound with the one-dimensional trial
space `𝕜`, the map `X = (t ↦ t x)` and `M = m`. For `U` the line through a unit eigenvector `u`
it reads `δ ‖x - ⟪u, x⟫ u‖ ≤ ‖A x - m x‖`.

The Frobenius and Ky Fan bounds include both the residual form, for a trial map `X`, and the
perturbation form, for invariant subspaces of two self-adjoint operators. The reverse
interval/exterior orientation is also available for these two norms. The operator-norm
perturbation bound controls the directed sine map `Submodule.sinThetaMap`.

These specialize the general bounds in `UnitarilyInvariantSeminorm.SinTheta.Basic`.

## Main results

* `Submodule.mul_norm_sinThetaMap_le_norm_sub_of_pointIntervalExteriorGap`:
  the operator-norm perturbation bound for the directed sine map.
* `LinearMap.IsSymmetric.mul_norm_starProjection_orthogonal_le_norm_apply_sub_smul`:
  the residual bound for a single trial vector, `δ ‖P_{Uᗮ} x‖ ≤ ‖A x - m x‖`.
* `LinearMap.IsSymmetric.mul_norm_sub_inner_smul_le_norm_apply_sub_smul`: the same bound at a
  unit eigenvector `u`, `δ ‖x - ⟪u, x⟫ u‖ ≤ ‖A x - m x‖`.

The following declarations are in the `TauCeti.UnitarilyInvariantSeminorm` namespace.

* `mul_frobenius_starProjection_comp_le_frobenius_sylvester_apply`:
  the Frobenius residual bound.
* `mul_frobenius_starProjection_comp_starProjection_le_frobenius_sub`:
  the Frobenius perturbation bound, also available with the interval and exterior swapped.
* `mul_kyFan_starProjection_comp_le_kyFan_sylvester_apply`:
  the residual bound for any Ky Fan index.
* `mul_kyFan_starProjection_comp_starProjection_le_kyFan_sub`:
  the perturbation bound for any Ky Fan index, also available with the spectral roles swapped.

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.3.
-/

public section

open Module
open scoped InnerProductSpace

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {a b δ : ℝ}

/-- **Frobenius residual `sin Θ` bound.** Under interval/exterior spectral
separation, `δ ‖P_{Uᗮ} X‖_F ≤ ‖A X - X M‖_F` for any trial map `X`. -/
theorem mul_frobenius_starProjection_comp_le_frobenius_sylvester_apply
    {A : E →L[𝕜] E} {M : F →L[𝕜] F} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hM : (M : F →ₗ[𝕜] F).IsSymmetric) {U : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U)
    (h : End.PointIntervalExteriorGap (M : F →ₗ[𝕜] F) ⊤ (A : E →ₗ[𝕜] E) Uᗮ a b δ)
    (X : F →L[𝕜] E) :
    δ * frobenius 𝕜 F E (Uᗮ.starProjection ∘L X) ≤
      frobenius 𝕜 F E (A.sylvester M X) :=
  (frobenius 𝕜 F E).mul_map_starProjection_comp_le_map_sylvester_apply hA hM hU h X

/-- **Frobenius perturbation `sin Θ` bound.** For invariant subspaces
`U` and `V`, interval/exterior separation implies
`δ ‖P_{Vᗮ} P_U‖_F ≤ ‖B - A‖_F`. -/
theorem mul_frobenius_starProjection_comp_starProjection_le_frobenius_sub
    {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) {U V : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V)
    (h : End.PointIntervalExteriorGap (A : E →ₗ[𝕜] E) U
      (B : E →ₗ[𝕜] E) Vᗮ a b δ) :
    δ * frobenius 𝕜 E E (Vᗮ.starProjection ∘L U.starProjection) ≤
      frobenius 𝕜 E E (B - A) :=
  (frobenius 𝕜 E E).mul_map_starProjection_comp_starProjection_le_map_sub hA hB hU hV h

/-- The Frobenius perturbation `sin Θ` bound with the interval and exterior
spectral locations exchanged. -/
theorem mul_frobenius_starProjection_comp_starProjection_le_frobenius_sub_swap
    {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) {U V : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V)
    (h : End.PointIntervalExteriorGap (B : E →ₗ[𝕜] E) Vᗮ
      (A : E →ₗ[𝕜] E) U a b δ) :
    δ * frobenius 𝕜 E E (Vᗮ.starProjection ∘L U.starProjection) ≤
      frobenius 𝕜 E E (B - A) :=
  (frobenius 𝕜 E E).mul_map_starProjection_comp_starProjection_le_map_sub_swap hA hB hU hV h

/-- **Ky Fan residual `sin Θ` bound.** Under interval/exterior spectral separation,
`δ Kₖ(P_{Uᗮ} X) ≤ Kₖ(A X - X M)` for every trial map `X` and every `k`. -/
theorem mul_kyFan_starProjection_comp_le_kyFan_sylvester_apply (k : ℕ)
    {A : E →L[𝕜] E} {M : F →L[𝕜] F} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hM : (M : F →ₗ[𝕜] F).IsSymmetric) {U : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U)
    (h : End.PointIntervalExteriorGap (M : F →ₗ[𝕜] F) ⊤ (A : E →ₗ[𝕜] E) Uᗮ a b δ)
    (X : F →L[𝕜] E) :
    δ * kyFan 𝕜 F E k (Uᗮ.starProjection ∘L X) ≤
      kyFan 𝕜 F E k (A.sylvester M X) :=
  (kyFan 𝕜 F E k).mul_map_starProjection_comp_le_map_sylvester_apply hA hM hU h X

/-- **Ky Fan perturbation `sin Θ` bound.** For every `k`, interval/exterior
spectral separation implies `δ Kₖ(P_{Vᗮ} P_U) ≤ Kₖ(B - A)`. -/
theorem mul_kyFan_starProjection_comp_starProjection_le_kyFan_sub (k : ℕ)
    {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) {U V : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V)
    (h : End.PointIntervalExteriorGap (A : E →ₗ[𝕜] E) U
      (B : E →ₗ[𝕜] E) Vᗮ a b δ) :
    δ * kyFan 𝕜 E E k (Vᗮ.starProjection ∘L U.starProjection) ≤
      kyFan 𝕜 E E k (B - A) :=
  (kyFan 𝕜 E E k).mul_map_starProjection_comp_starProjection_le_map_sub hA hB hU hV h

/-- The Ky Fan perturbation `sin Θ` bound in the reversed interval/exterior
orientation, for every Ky Fan index `k`. -/
theorem mul_kyFan_starProjection_comp_starProjection_le_kyFan_sub_swap (k : ℕ)
    {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) {U V : Submodule 𝕜 E}
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V)
    (h : End.PointIntervalExteriorGap (B : E →ₗ[𝕜] E) Vᗮ
      (A : E →ₗ[𝕜] E) U a b δ) :
    δ * kyFan 𝕜 E E k (Vᗮ.starProjection ∘L U.starProjection) ≤
      kyFan 𝕜 E E k (B - A) :=
  (kyFan 𝕜 E E k).mul_map_starProjection_comp_starProjection_le_map_sub_swap hA hB hU hV h

end TauCeti.UnitarilyInvariantSeminorm

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- An interval/exterior spectral gap bounds the directed sine between invariant
subspaces by the operator perturbation. -/
theorem mul_norm_sinThetaMap_le_norm_sub_of_pointIntervalExteriorGap
    (U V : Submodule 𝕜 E) {A B : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V) {a b δ : ℝ}
    (hgap : Module.End.PointIntervalExteriorGap (A : E →ₗ[𝕜] E) U
      (B : E →ₗ[𝕜] E) Vᗮ a b δ) :
    δ * ‖U.sinThetaMap V‖ ≤ ‖B - A‖ := by
  simpa only [sinThetaMap_def, TauCeti.UnitarilyInvariantSeminorm.opNorm_apply,
    map_sub, LinearMap.toContinuousLinearMap_coe] using
    (TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_starProjection_le_map_sub
      (TauCeti.UnitarilyInvariantSeminorm.opNorm 𝕜 E E) hA hB hU hV hgap)

end Submodule

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **Residual `sin Θ` bound for a trial vector.** If `U` is invariant under a symmetric `A` and
the eigenvalues of `A` on `Uᗮ` lie outside `(m - δ, m + δ)`, then
`δ ‖P_{Uᗮ} x‖ ≤ ‖A x - m x‖` for every `x`. -/
theorem mul_norm_starProjection_orthogonal_le_norm_apply_sub_smul {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) {U : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U) {m δ : ℝ}
    (h : Module.End.PointSpectrumIn (A : E →ₗ[𝕜] E) Uᗮ (Set.Ioo (m - δ) (m + δ))ᶜ) (x : E) :
    δ * ‖Uᗮ.starProjection x‖ ≤ ‖A x - (m : 𝕜) • x‖ := by
  set M : 𝕜 →L[𝕜] 𝕜 := (m : 𝕜) • ContinuousLinearMap.id 𝕜 𝕜
  have hM : (M : 𝕜 →ₗ[𝕜] 𝕜).IsSymmetric := LinearMap.IsSymmetric.id.smul (RCLike.conj_ofReal m)
  have hgap : Module.End.PointIntervalExteriorGap (M : 𝕜 →ₗ[𝕜] 𝕜) ⊤ (A : E →ₗ[𝕜] E) Uᗮ m m δ := by
    refine ⟨Module.End.pointSpectrumIn_iff.mpr fun y _ hy0 μ hy ↦ ?_, h⟩
    have hμ : (m : 𝕜) = μ :=
      mul_right_cancel₀ hy0 (by simpa [M, RCLike.real_smul_eq_coe_mul] using hy)
    simp [RCLike.ofReal_inj.mp hμ]
  have h₁ : Uᗮ.starProjection ∘L ContinuousLinearMap.toSpanSingleton 𝕜 x =
      ContinuousLinearMap.toSpanSingleton 𝕜 (Uᗮ.starProjection x) :=
    ContinuousLinearMap.comp_toSpanSingleton _ _
  have h₂ : A.sylvester M (ContinuousLinearMap.toSpanSingleton 𝕜 x) =
      ContinuousLinearMap.toSpanSingleton 𝕜 (A x - (m : 𝕜) • x) := by
    ext
    simp [M]
  have h := TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_le_map_sylvester_apply
    (TauCeti.UnitarilyInvariantSeminorm.opNorm 𝕜 𝕜 E) hA hM hU hgap
    (ContinuousLinearMap.toSpanSingleton 𝕜 x)
  simp only [h₁, h₂, TauCeti.UnitarilyInvariantSeminorm.opNorm_apply,
    LinearMap.toContinuousLinearMap_coe, ContinuousLinearMap.norm_toSpanSingleton] at h
  exact h

/-- **Residual `sin Θ` bound at a unit eigenvector.** Let `u` be a unit eigenvector of a
symmetric `A`. If every real eigenvalue of `A` carried by a nonzero eigenvector orthogonal to `u`
is at most `m - δ`, then `δ ‖x - ⟪u, x⟫ u‖ ≤ ‖A x - m x‖` for every `x`. This is the residual
Davis–Kahan theorem for the invariant line `𝕜 ∙ u`. -/
theorem mul_norm_sub_inner_smul_le_norm_apply_sub_smul {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) {u : E} (hu : ‖u‖ = 1) {c : 𝕜} (hAu : A u = c • u)
    {m δ : ℝ}
    (h : ∀ {y : E}, y ≠ 0 → ⟪y, u⟫_𝕜 = 0 → ∀ μ : ℝ, A y = (μ : 𝕜) • y → μ ≤ m - δ) (x : E) :
    δ * ‖x - ⟪u, x⟫_𝕜 • u‖ ≤ ‖A x - (m : 𝕜) • x‖ := by
  have hU : ∀ y ∈ 𝕜 ∙ u, A y ∈ 𝕜 ∙ u := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_smul, hAu, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have hspec : Module.End.PointSpectrumIn (A : E →ₗ[𝕜] E) (𝕜 ∙ u)ᗮ (Set.Ioo (m - δ) (m + δ))ᶜ := by
    refine Module.End.pointSpectrumIn_iff.mpr fun y hy hy0 μ hAy ↦ ?_
    have := h hy0 (Submodule.mem_orthogonal_singleton_iff_inner_left.mp hy) μ hAy
    simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt]
    exact .inl this
  simpa [Submodule.starProjection_orthogonal_val, Submodule.starProjection_unit_singleton 𝕜 hu]
    using hA.mul_norm_starProjection_orthogonal_le_norm_apply_sub_smul hU hspec x

end LinearMap.IsSymmetric
