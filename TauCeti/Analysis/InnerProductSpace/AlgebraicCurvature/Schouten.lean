/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The algebraic Schouten form of a four-tensor

On a finite-dimensional real inner product space `V` of dimension `n`, the algebraic Schouten
bilinear form of `r : FourTensor V` is

`schouten r = (n - 2)⁻¹ • (ricci r - (scalar r / (2 (n - 1))) • innerₗ V)`.

When `n = 2`, Lean's totalized inverse `(0 : ℝ)⁻¹ = 0` gives `schouten r = 0`; when `n = 1`, the
scalar correction vanishes so `schouten r = -ricci r` (which vanishes whenever `scalar r = 0` or
`r` is pair-antisymmetric).

Away from dimension `2` (and assuming `scalar r = 0` in dimension `1`),
`bilinFormTrace (schouten r) = scalar r / (2 * (n - 1))` and
`ricci r = (n - 2) • schouten r + bilinFormTrace (schouten r) • innerₗ V`. In dimension at least
`3`, `schouten (constantCurvature V) = (1 / 2) • innerₗ V`, and `schouten` is equivariant under
linear isometric equivalences.

## Main definitions

* `TauCeti.FourTensor.schouten`: the algebraic Schouten bilinear form of a four-tensor.

## Main results

* `TauCeti.FourTensor.schouten_apply`, `TauCeti.FourTensor.schouten_apply_apply`, and
  `TauCeti.FourTensor.schouten_eq_zero_of_finrank_eq_two`: evaluation and dimension-two vanishing.
* `TauCeti.FourTensor.isSymm_schouten_of_isSymm_ricci` and `TauCeti.FourTensor.isSymm_schouten_iff`:
  symmetry of the Schouten form.
* `TauCeti.FourTensor.bilinFormTrace_schouten` and `TauCeti.FourTensor.ricci_eq_smul_schouten_add`:
  metric trace and Ricci reconstruction away from dimension `2`.
* `TauCeti.FourTensor.schouten_constantCurvature`: Schouten form of the constant-curvature tensor.
* `LinearIsometryEquiv.schouten_compContinuousLinearMap`: orthogonal equivariance.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
-/

public section

open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The algebraic Schouten bilinear form
`P(r) = (dim V - 2)⁻¹ • (Ric(r) - (Scal(r) / (2 (dim V - 1))) g)`.
Because Lean totalizes `(0 : ℝ)⁻¹ = 0`, `schouten r = 0` when `dim V = 2`; when `dim V = 1`, the
scalar correction vanishes so `schouten r = -ricci r` (which is `0` for pair-antisymmetric
four-tensors). -/
def schouten : FourTensor V →ₗ[ℝ] BilinForm ℝ V :=
  ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
    (ricci + (-(2 * ((Module.finrank ℝ V : ℝ) - 1))⁻¹ • scalar).smulRight (innerₗ V))

/-- Evaluation of the algebraic Schouten form. -/
theorem schouten_apply (r : FourTensor V) :
    schouten r = ((Module.finrank ℝ V : ℝ) - 2)⁻¹ •
      (ricci r - (scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V) := by
  ext u v
  simp only [schouten, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smulRight_apply, innerₗ_apply_apply, smul_eq_mul, div_eq_inv_mul]
  ring

/-- Pointwise evaluation of the algebraic Schouten form. -/
theorem schouten_apply_apply (r : FourTensor V) (u v : V) :
    schouten r u v = ((Module.finrank ℝ V : ℝ) - 2)⁻¹ *
      (ricci r u v - scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) * ⟪u, v⟫) := by
  simp [schouten_apply]

/-- In dimension `2`, `schouten r = 0` because Lean totalizes `(0 : ℝ)⁻¹ = 0`. -/
@[simp] theorem schouten_eq_zero_of_finrank_eq_two (hdim : Module.finrank ℝ V = 2)
    (r : FourTensor V) : schouten r = 0 := by
  simp [schouten, hdim]

/-- `schouten r` is symmetric whenever `ricci r` is symmetric. -/
theorem isSymm_schouten_of_isSymm_ricci {r : FourTensor V} (h : (ricci r).IsSymm) :
    (schouten r).IsSymm := ⟨fun u v ↦ by
  rw [schouten_apply_apply, schouten_apply_apply, h.eq u v, real_inner_comm u v]⟩

/-- Away from dimension `2`, `schouten r` is symmetric if and only if `ricci r` is symmetric. -/
theorem isSymm_schouten_iff (hdim : Module.finrank ℝ V ≠ 2) {r : FourTensor V} :
    (schouten r).IsSymm ↔ (ricci r).IsSymm := by
  refine ⟨fun h ↦ ⟨fun u v ↦ ?_⟩, isSymm_schouten_of_isSymm_ricci⟩
  have h2 : ((Module.finrank ℝ V : ℝ) - 2) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hdim)
  have heq := congrArg (((Module.finrank ℝ V : ℝ) - 2) * ·) (h.eq u v)
  simp only [schouten_apply_apply, ← mul_assoc, mul_inv_cancel₀ h2, one_mul,
    real_inner_comm u v] at heq
  linarith

/-- Away from dimension `2` (and assuming `scalar r = 0` in dimension `1`), the metric trace of
`schouten r` is `scalar r / (2 * (dim V - 1))`. -/
theorem bilinFormTrace_schouten {r : FourTensor V} (h2 : Module.finrank ℝ V ≠ 2)
    (h1 : Module.finrank ℝ V = 1 → scalar r = 0) :
    bilinFormTrace (schouten r) = scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1)) := by
  have hsub := map_sub bilinFormTrace (ricci r)
    ((scalar r / (2 * ((Module.finrank ℝ V : ℝ) - 1))) • innerₗ V)
  rw [schouten_apply, map_smul, hsub, map_smul, bilinFormTrace_inner, ← scalar_apply,
    smul_eq_mul, smul_eq_mul]
  have hn2 : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h2)
  by_cases hn1 : Module.finrank ℝ V = 1
  · simp [hn1, h1 hn1]
  · have hn1' : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn1)
    field_simp
    ring

/-- Away from dimension `2` (and assuming `scalar r = 0` in dimension `1`), the Ricci contraction
decomposes as `ricci r = (dim V - 2) • schouten r + bilinFormTrace (schouten r) • innerₗ V`. -/
theorem ricci_eq_smul_schouten_add {r : FourTensor V} (h2 : Module.finrank ℝ V ≠ 2)
    (h1 : Module.finrank ℝ V = 1 → scalar r = 0) :
    ricci r = ((Module.finrank ℝ V : ℝ) - 2) • schouten r +
      bilinFormTrace (schouten r) • innerₗ V := by
  have hn2 : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h2)
  ext u v
  simp only [bilinFormTrace_schouten h2 h1, LinearMap.add_apply, LinearMap.smul_apply,
    schouten_apply_apply, innerₗ_apply_apply, smul_eq_mul]
  field_simp
  ring

/-- In dimension at least `3`, the Schouten form of `constantCurvature V` is
`(1 / 2) • innerₗ V`. -/
theorem schouten_constantCurvature (hn : 3 ≤ Module.finrank ℝ V) :
    schouten (constantCurvature V) = (1 / 2 : ℝ) • innerₗ V := by
  have hn' : (3 : ℝ) ≤ Module.finrank ℝ V := by exact_mod_cast hn
  have hn2 : (Module.finrank ℝ V : ℝ) - 2 ≠ 0 := by linarith
  have hn1 : (Module.finrank ℝ V : ℝ) - 1 ≠ 0 := by linarith
  ext u v
  simp only [schouten_apply_apply, ricci_constantCurvature, scalar_constantCurvature,
    LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
  field_simp
  ring

end TauCeti.FourTensor

namespace LinearIsometryEquiv

open TauCeti TauCeti.FourTensor

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- `schouten` is equivariant under linear isometric equivalences. -/
theorem schouten_compContinuousLinearMap (e : W ≃ₗᵢ[ℝ] V) (r : FourTensor V) (u v : W) :
    schouten (r.compContinuousLinearMap fun _ ↦ e.toLinearIsometry.toContinuousLinearMap) u v =
      schouten r (e u) (e v) := by
  simp only [schouten_apply_apply, ricci_compContinuousLinearMap_linearIsometryEquiv,
    scalar_compContinuousLinearMap_linearIsometryEquiv, e.toLinearEquiv.finrank_eq, e.inner_map_map]

end LinearIsometryEquiv
