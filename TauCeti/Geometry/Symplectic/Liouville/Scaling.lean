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
(`TauCeti.IsLiouvilleVectorField.mpullback_globalFlow_eq_exp_smul`): the flow rescales `σ`, and
is conformally symplectic when `σ` is symplectic. If moreover `α` is a primitive of `σ` whose
Liouville field is `Z`, `dα = σ` and `ι_Z σ = α`, then also `ψₜ^* α = e^t α`
(`TauCeti.mpullback_globalFlow_eq_exp_smul_of_interior_eq`): the flow rescales the primitive, so
that it is an exact conformal symplectomorphism when `σ` is symplectic.

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

/-- **The Liouville flow rescales the two-form.** The flow `ψ` of a complete `C²` Liouville
vector field `Z` of a differentiable two-form `σ`, `L_Z σ = σ`, satisfies `ψₜ^* σ = e^t σ`; when `σ`
is symplectic, the flow is conformally symplectic. -/
theorem IsLiouvilleVectorField.mpullback_globalFlow_eq_exp_smul {σ : RoughForm I M ℝ 2}
    (hσ : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ) y (σ y)))
    (hZσ : IsLiouvilleVectorField σ Z) (t : ℝ) :
    mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc t) σ = Real.exp t • σ := by
  have hL : mlieDerivForm Z σ = (1 : ℝ) • σ := by
    rw [one_smul]
    exact isLiouvilleVectorField_iff.mp hZσ
  simpa only [one_mul] using TauCeti.mpullback_globalFlow_eq_exp_smul hc hZ hσ hL t

/-- **The Liouville flow rescales the primitive.** If `α` is a differentiable primitive of the
two-form `σ`, and the complete `C²` vector field `Z` is its Liouville field, `ι_Z σ = α`, then the
flow `ψ` of `Z` satisfies `ψₜ^* α = e^t α`; when `σ` is symplectic, the flow is exact conformally
symplectic. -/
theorem mpullback_globalFlow_eq_exp_smul_of_interior_eq {α : RoughForm I M ℝ 1}
    {σ : RoughForm I M ℝ 2}
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)))
    (hdα : mextDeriv α = σ) (hZα : σ.interior Z = α) (t : ℝ) :
    mpullback I I (globalFlow Z (hZ.of_le one_le_two) hc t) α = Real.exp t • α := by
  have hL : mlieDerivForm Z α = (1 : ℝ) • α := by
    rw [one_smul]
    exact mlieDerivForm_eq_self_of_interior_eq hα (hZ.mdifferentiable (by norm_num))
      (by rw [hdα, hZα])
  simpa only [one_mul] using mpullback_globalFlow_eq_exp_smul hc hZ hα hL t

end TauCeti
