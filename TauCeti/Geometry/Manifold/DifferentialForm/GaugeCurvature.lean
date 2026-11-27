/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.DifferentialForm.Squared

/-!
# Covariant derivatives and curvature of connections on a trivial bundle

Let `P = M × K` be the trivial principal bundle over a manifold `M` with structure group a Lie
group `K`, with Lie algebra `𝔨`. Its connections are the operators `d + A` for the `𝔨`-valued
`1`-forms `A`. The bracket of `𝔨` enters as a continuous bilinear map
`β : 𝔨 →L[ℝ] 𝔨 →L[ℝ] 𝔨`, `[a, b] = β a b`, and wedge products of `𝔨`-valued forms are the paired
wedges `SmoothForm.wedgeWith β`. Each statement assumes only the identities of `β` it uses.

* The connection `d + A` has the covariant derivative `d_A ξ = dξ + [A, ξ]` on `𝔨`-valued
  functions (`TauCeti.gaugeCovariantDeriv`), the covariant exterior derivative
  `d_A b = db + [A ∧ b]` on `𝔨`-valued `1`-forms (`TauCeti.gaugeCovariantExtDeriv`) and the
  curvature `F_A = dA + ½ [A ∧ A]` (`TauCeti.gaugeCurvature`). For a skew-symmetric bracket,
  `F_A (v, w) = dA (v, w) + [A v, A w]` (`TauCeti.gaugeCurvature_val`).
* Along a line of connections, `F_(A + t b) = F_A + t d_A b + (t² / 2) [b ∧ b]`
  (`TauCeti.gaugeCurvature_add_smul`).
* The covariant derivative squares to the curvature, `d_A (d_A η) = [F_A, η]`, for a bracket
  satisfying the Jacobi identity (`TauCeti.gaugeCovariantExtDeriv_gaugeCovariantDeriv`).
* The trivial connection `d` (`A = 0`) is flat, `F_0 = 0` (`TauCeti.gaugeCurvature_zero`), and
  its covariant derivatives are the exterior derivative.
* For the zero bracket of an abelian Lie algebra, both covariant derivatives are the exterior
  derivative and `F_A = dA` (`TauCeti.gaugeCurvature_zero_bracket`).

## Main definitions

* `TauCeti.gaugeCovariantDeriv`, `TauCeti.gaugeCovariantExtDeriv`: the covariant derivatives
  `d_A` on `𝔨`-valued functions and `1`-forms.
* `TauCeti.gaugeCurvature`: the curvature `F_A = dA + ½ [A ∧ A]`.

## Main results

* `TauCeti.gaugeCurvature_add_smul`: the curvature along a line of connections.
* `TauCeti.gaugeCovariantExtDeriv_gaugeCovariantDeriv`: `d_A (d_A η) = [F_A, η]`.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M 𝔨 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [NormedAddCommGroup 𝔨] [NormedSpace ℝ 𝔨]
  (β : 𝔨 →L[ℝ] 𝔨 →L[ℝ] 𝔨)

/-- The **covariant derivative** `d_A ξ = dξ + [A, ξ]` of a `𝔨`-valued function `ξ`, regarded
as a `0`-form, for the connection `d + A` of the trivial bundle given by a `𝔨`-valued `1`-form
`A`, where the bracket of `𝔨` is the continuous bilinear map `β`. -/
def gaugeCovariantDeriv (A : SmoothForm I M 𝔨 1) :
    SmoothForm I M 𝔨 0 →ₗ[ℝ] SmoothForm I M 𝔨 1 :=
  mextDerivₗ I 0 + SmoothForm.wedgeWith β A

/-- The **covariant exterior derivative** `d_A b = db + [A ∧ b]` of a `𝔨`-valued `1`-form `b`,
for the connection `d + A` of the trivial bundle. -/
def gaugeCovariantExtDeriv (A : SmoothForm I M 𝔨 1) :
    SmoothForm I M 𝔨 1 →ₗ[ℝ] SmoothForm I M 𝔨 2 :=
  mextDerivₗ I 1 + SmoothForm.wedgeWith β A

/-- The **curvature** `F_A = dA + ½ [A ∧ A]` of the connection `d + A` of the trivial bundle,
given by a `𝔨`-valued `1`-form `A`. -/
def gaugeCurvature (A : SmoothForm I M 𝔨 1) : SmoothForm I M 𝔨 2 :=
  mextDerivₗ I 1 A + (2 : ℝ)⁻¹ • SmoothForm.wedgeWith β A A

theorem gaugeCovariantDeriv_apply (A : SmoothForm I M 𝔨 1) (ξ : SmoothForm I M 𝔨 0) :
    gaugeCovariantDeriv β A ξ = mextDerivₗ I 0 ξ + SmoothForm.wedgeWith β A ξ :=
  (rfl)

theorem gaugeCovariantExtDeriv_apply (A b : SmoothForm I M 𝔨 1) :
    gaugeCovariantExtDeriv β A b = mextDerivₗ I 1 b + SmoothForm.wedgeWith β A b :=
  (rfl)

theorem gaugeCurvature_def (A : SmoothForm I M 𝔨 1) :
    gaugeCurvature β A = mextDerivₗ I 1 A + (2 : ℝ)⁻¹ • SmoothForm.wedgeWith β A A :=
  (rfl)

/-- The covariant derivative `d_A ξ = dξ + [A, ξ]` evaluated at a tangent vector. -/
theorem gaugeCovariantDeriv_val (A : SmoothForm I M 𝔨 1) (ξ : SmoothForm I M 𝔨 0) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    (gaugeCovariantDeriv β A ξ).val x v = mextDeriv ξ.val x v + β (A.val x v) (ξ.val x 0) := by
  rw [gaugeCovariantDeriv_apply, Submodule.coe_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, mextDerivₗ_apply]
  exact congrArg _ (SmoothForm.wedgeWith_apply_zero_right β A ξ x v)

/-- The covariant exterior derivative `d_A b = db + [A ∧ b]` evaluated at two tangent vectors. -/
theorem gaugeCovariantExtDeriv_val (A b : SmoothForm I M 𝔨 1) (x : M)
    (v w : TangentSpace I x) :
    (gaugeCovariantExtDeriv β A b).val x ![v, w] = mextDeriv b.val x ![v, w] +
      (β (A.val x ![v]) (b.val x ![w]) - β (A.val x ![w]) (b.val x ![v])) := by
  rw [gaugeCovariantExtDeriv_apply, Submodule.coe_add, Pi.add_apply,
    ContinuousAlternatingMap.add_apply, mextDerivₗ_apply, SmoothForm.wedgeWith_apply_one_one]

/-- The curvature `F_A = dA + ½ [A ∧ A]` evaluated at two tangent vectors. For a skew-symmetric
bracket, `½ [A ∧ A] (v, w) = [A v, A w]`. -/
theorem gaugeCurvature_val (hβ : ∀ a b, β a b = -β b a) (A : SmoothForm I M 𝔨 1) (x : M)
    (v w : TangentSpace I x) :
    (gaugeCurvature β A).val x ![v, w] =
      mextDeriv A.val x ![v, w] + β (A.val x ![v]) (A.val x ![w]) := by
  simp only [gaugeCurvature_def, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    mextDerivₗ_apply, SmoothForm.wedgeWith_apply_one_one, hβ (A.val x ![w])]
  module

/-- **The curvature along a line of connections.** For a skew-symmetric bracket,
`F_(A + t b) = F_A + t d_A b + (t² / 2) [b ∧ b]`. -/
theorem gaugeCurvature_add_smul (hβ : ∀ a b, β a b = -β b a) (A b : SmoothForm I M 𝔨 1)
    (t : ℝ) :
    gaugeCurvature β (A + t • b) = gaugeCurvature β A + t • gaugeCovariantExtDeriv β A b +
      (t ^ 2 / 2) • SmoothForm.wedgeWith β b b := by
  simp only [gaugeCurvature_def, gaugeCovariantExtDeriv_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply,
    SmoothForm.wedgeWith_comm_one_one_of_antisymm β hβ A b]
  module

/-- The covariant derivative of the trivial connection `d` is the exterior derivative. -/
@[simp]
theorem gaugeCovariantDeriv_zero :
    gaugeCovariantDeriv β (0 : SmoothForm I M 𝔨 1) = mextDerivₗ I 0 :=
  LinearMap.ext fun ξ ↦ by
    rw [gaugeCovariantDeriv_apply, map_zero, LinearMap.zero_apply, add_zero]

/-- The covariant exterior derivative of the trivial connection `d` is the exterior derivative. -/
@[simp]
theorem gaugeCovariantExtDeriv_zero :
    gaugeCovariantExtDeriv β (0 : SmoothForm I M 𝔨 1) = mextDerivₗ I 1 :=
  LinearMap.ext fun b ↦ by
    rw [gaugeCovariantExtDeriv_apply, map_zero, LinearMap.zero_apply, add_zero]

/-- The trivial connection `d` is flat: `F_0 = 0`. -/
@[simp]
theorem gaugeCurvature_zero : gaugeCurvature β (0 : SmoothForm I M 𝔨 1) = 0 := by
  rw [gaugeCurvature_def, map_zero, map_zero, smul_zero, add_zero]

/-- For the zero bracket, that of an abelian Lie algebra, the covariant derivative is the
exterior derivative. -/
@[simp]
theorem gaugeCovariantDeriv_zero_bracket (A : SmoothForm I M 𝔨 1) :
    gaugeCovariantDeriv (0 : 𝔨 →L[ℝ] 𝔨 →L[ℝ] 𝔨) A = mextDerivₗ I 0 :=
  LinearMap.ext fun ξ ↦ Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by
    rw [gaugeCovariantDeriv_val, zero_apply, zero_apply,
      add_zero, mextDerivₗ_apply]

/-- For the zero bracket, the covariant exterior derivative is the exterior derivative. -/
@[simp]
theorem gaugeCovariantExtDeriv_zero_bracket (A : SmoothForm I M 𝔨 1) :
    gaugeCovariantExtDeriv (0 : 𝔨 →L[ℝ] 𝔨 →L[ℝ] 𝔨) A = mextDerivₗ I 1 :=
  LinearMap.ext fun b ↦ SmoothBundleForm.ext_eval₂ fun x v w ↦ by
    simp only [SmoothBundleForm.eval₂_apply, gaugeCovariantExtDeriv_val,
      zero_apply, sub_zero, add_zero, mextDerivₗ_apply]

/-- For the zero bracket, the curvature `F_A = dA` is the exterior derivative of `A`. -/
@[simp]
theorem gaugeCurvature_zero_bracket (A : SmoothForm I M 𝔨 1) :
    gaugeCurvature (0 : 𝔨 →L[ℝ] 𝔨 →L[ℝ] 𝔨) A = mextDerivₗ I 1 A :=
  SmoothBundleForm.ext_eval₂ fun x v w ↦ by
    simp only [SmoothBundleForm.eval₂_apply,
      gaugeCurvature_val (0 : 𝔨 →L[ℝ] 𝔨 →L[ℝ] 𝔨) fun _ _ ↦ by simp, zero_apply, add_zero,
      mextDerivₗ_apply]

/-- **The covariant derivative squares to the curvature.** On `𝔨`-valued functions,
`d_A (d_A η) = [F_A, η]` when the bracket `β` is skew-symmetric and satisfies the Leibniz form
`[a, [b, c]] = [[a, b], c] + [b, [a, c]]` of the Jacobi identity. -/
theorem gaugeCovariantExtDeriv_gaugeCovariantDeriv (hβ : ∀ a b, β a b = -β b a)
    (hJ : ∀ a b c, β a (β b c) = β (β a b) c + β b (β a c)) (A : SmoothForm I M 𝔨 1)
    (η : SmoothForm I M 𝔨 0) :
    gaugeCovariantExtDeriv β A (gaugeCovariantDeriv β A η) =
      SmoothForm.wedgeWith β (gaugeCurvature β A) η := by
  have hdA : mextDerivₗ I 1 (gaugeCovariantDeriv β A η) =
      mextDerivₗ I 1 (SmoothForm.wedgeWith β A η) := by
    have hdd : mextDerivₗ I 1 (mextDerivₗ I 0 η) = 0 :=
      LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ (I := I) (M := M) (F := 𝔨) 0) η
    rw [gaugeCovariantDeriv_apply, map_add, hdd, zero_add]
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  simp only [SmoothBundleForm.eval₂_apply, gaugeCovariantExtDeriv_apply, Submodule.coe_add,
    Pi.add_apply, ContinuousAlternatingMap.add_apply, hdA, mextDerivₗ_apply,
    SmoothForm.coe_wedgeWith, SmoothForm.mextDeriv_wedgeWith_apply_one_zero,
    RoughForm.wedgeWith_apply_one_one, RoughForm.wedgeWith_apply_zero_right,
    gaugeCovariantDeriv_val, gaugeCurvature_val β hβ, map_add, add_apply]
  linear_combination (norm := abel) hJ (A.val x ![v]) (A.val x ![w]) (η.val x 0)

end TauCeti
