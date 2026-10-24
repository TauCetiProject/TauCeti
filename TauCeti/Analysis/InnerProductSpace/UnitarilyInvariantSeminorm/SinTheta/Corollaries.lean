/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.OpNorm
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Davis–Kahan `sin Θ` bounds for concrete norms

The Davis–Kahan bounds for an arbitrary unitarily invariant seminorm specialize to the
operator norm, the Frobenius norm and every Ky Fan norm, with constant `1` under
interval/exterior spectral separation.

The Frobenius and Ky Fan bounds include both the residual form, for a trial map `X`, and the
perturbation form, for invariant subspaces of two self-adjoint operators. The reverse
interval/exterior orientation is also available for these two norms. The operator-norm
perturbation bound controls the directed sine map `Submodule.sinThetaMap`.

These specialize the general bounds in `UnitarilyInvariantSeminorm.SinTheta.Basic`.

## Main results

* `Submodule.mul_norm_sinThetaMap_le_norm_sub_of_pointIntervalExteriorGap`:
  the operator-norm perturbation bound for the directed sine map.

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
