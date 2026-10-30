/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Symplectic.Liouville.VectorField

/-!
# The Liouville flow rescales the form and its primitive

Let `Z` be a complete `C²` Liouville vector field of a two-form `σ`, `L_Z σ = σ`, with flow `ψ`.
Then `ψₜ^* σ = e^t σ` for every time `t`
(`TauCeti.IsLiouvilleVectorField.mpullback_globalFlow_eq_exp_smul`): the Liouville flow is
conformally symplectic. If moreover `α` is a primitive of `σ` whose Liouville field is `Z`,
`dα = σ` and `ι_Z σ = α`, then also `ψₜ^* α = e^t α`
(`TauCeti.mpullback_globalFlow_eq_exp_smul_of_interior_eq`), so that the flow is an exact
conformal symplectomorphism.

Near a hypersurface `Σ` of contact type, such as the boundary of a Liouville domain, the flow
sweeps out a family of hypersurfaces `ψₜ(Σ)` whose characteristic foliations are conjugate under
`ψₜ`, because `ψₜ` multiplies the symplectic form by a constant; this is how almost existence of
closed characteristics near `Σ` yields closed characteristics on `Σ` itself. On the cylindrical end
of the completion of a Liouville domain, swept out from the boundary by the flow, the identity
`ψₜ^* α = e^t α` says that `α` has the form `e^t α|_Σ` of a symplectization.

Both identities integrate infinitesimal ones along the flow
(`TauCeti.mpullback_globalFlow_eq_exp_smul`): `L_Z σ = σ` by definition, and `L_Z α = α` by
Cartan's formula (`TauCeti.mlieDerivForm_eq_self_of_interior_eq`).

## Main results

* `TauCeti.IsLiouvilleVectorField.mpullback_globalFlow_eq_exp_smul`: `ψₜ^* σ = e^t σ`.
* `TauCeti.mpullback_globalFlow_eq_exp_smul_of_interior_eq`: `ψₜ^* α = e^t α`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (Liouville vector fields and hypersurfaces of contact type).
* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1 (Liouville domains and their completions).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {Z : (x : M) → TangentSpace I x}

variable [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M]
  (hc : IsCompleteVectorField Z)
  (hZ : ContMDiff I I.tangent 2 (fun y ↦ (⟨y, Z y⟩ : TangentBundle I M)))
include hc hZ

/-- **The Liouville flow is conformally symplectic.** The flow `ψ` of a complete `C²` Liouville
vector field `Z` of a differentiable two-form `σ`, `L_Z σ = σ`, satisfies `ψₜ^* σ = e^t σ`. -/
theorem IsLiouvilleVectorField.mpullback_globalFlow_eq_exp_smul {σ : RoughForm I M ℝ 2}
    (hσ : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ) y (σ y)))
    (hZσ : IsLiouvilleVectorField σ Z) (t : ℝ) :
    mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc t) σ = Real.exp t • σ := by
  have hL : mlieDerivForm Z σ = (1 : ℝ) • σ := by
    rw [one_smul]
    exact isLiouvilleVectorField_iff.mp hZσ
  simpa only [one_mul] using TauCeti.mpullback_globalFlow_eq_exp_smul hc hZ hσ hL t

/-- **The Liouville flow is exact conformally symplectic.** If `α` is a smooth primitive of the
smooth two-form `σ`, and the complete `C²` vector field `Z` is its Liouville field, `ι_Z σ = α`,
then the flow `ψ` of `Z` satisfies `ψₜ^* α = e^t α`. -/
theorem mpullback_globalFlow_eq_exp_smul_of_interior_eq {α : SmoothForm I M ℝ 1}
    {σ : SmoothForm I M ℝ 2} (hdα : mextDeriv α.1 = σ.1)
    (hZα : RoughForm.interior Z σ.1 = α.1) (t : ℝ) :
    mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc t) α.1 = Real.exp t • α.1 := by
  have hL : mlieDerivForm Z α.1 = (1 : ℝ) • α.1 := by
    rw [one_smul]
    exact mlieDerivForm_eq_self_of_interior_eq α.mdifferentiable
      (hZ.mdifferentiable (by norm_num)) (by rw [hdα, hZα])
  simpa only [one_mul] using mpullback_globalFlow_eq_exp_smul hc hZ α.mdifferentiable hL t

end TauCeti
