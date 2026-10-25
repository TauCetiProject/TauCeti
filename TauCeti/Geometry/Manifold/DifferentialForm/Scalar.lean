/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared

/-!
# The exterior derivative over coefficient scalars

The exterior derivative on real tangent spaces is linear over any scalars acting continuously
on the coefficients and commuting with real scalars. This module bundles that linearity as
`SmoothForm.mextDerivLinearMap`. In particular, complex-valued forms on a real manifold have a
complex-linear differential, without changing the underlying differential-form carrier.

The underlying function is the existing `mextDerivₗ`, and successive differentials compose
to zero. These maps provide the differentials of de Rham complexes over the coefficient field.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti
namespace SmoothForm

variable {E H M F S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Semiring S] [Module S F]
  [ContinuousConstSMul S F] [SMulCommClass ℝ S F]

/-- The exterior derivative, linear over the scalars acting on the coefficients. -/
def mextDerivLinearMap (k : ℕ) : SmoothForm I M F k →ₗ[S] SmoothForm I M F (k + 1) where
  toFun := mextDerivₗ I k
  map_add' := map_add (mextDerivₗ I k)
  map_smul' := mextDerivₗ_smul

/-- The scalar-linear exterior derivative agrees with the real-linear exterior derivative. -/
@[simp]
theorem mextDerivLinearMap_apply (k : ℕ) (φ : SmoothForm I M F k) :
    mextDerivLinearMap (S := S) I k φ = mextDerivₗ I k φ := (rfl)

/-- The real-linear and real-scalar versions of the exterior derivative are the same map. -/
@[simp]
theorem mextDerivLinearMap_real (k : ℕ) :
    mextDerivLinearMap (S := ℝ) I (M := M) (F := F) k = mextDerivₗ I k := by
  ext φ
  rfl

/-- Successive scalar-linear exterior derivatives compose to zero. -/
@[simp]
theorem mextDerivLinearMap_comp (k : ℕ) :
    (mextDerivLinearMap (S := S) I (k + 1)).comp
      (mextDerivLinearMap (S := S) I (M := M) (F := F) k) = 0 := by
  ext φ : 1
  simpa only [LinearMap.comp_apply, mextDerivLinearMap_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I (F := F) k) φ

end SmoothForm
end TauCeti
