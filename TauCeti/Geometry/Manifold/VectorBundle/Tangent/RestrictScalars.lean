/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

/-!
# Restriction of scalars of tangent bundles

The tangent bundle of a complex manifold and that of its underlying real manifold have
canonically homeomorphic total spaces. The identification fixes the base and reads a tangent
vector in the same preferred chart coordinates on both sides. It commutes with tangent maps
of differentiable maps. In particular, realification preserves not just pointwise derivatives
but the topology of the whole tangent bundle.

We work with arbitrary compatible normed field extensions and self-modelled manifolds.
The comparison uses `TauCeti.tangentCoordChange_restrictScalars` on chart overlaps;
no equality of the two tangent-bundle topologies is assumed. Both manifold instances are
explicit so that both tangent-bundle topologies can be named. The smaller-field instance can
always be installed locally using `IsManifold.restrictScalars`.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, Chapter 1.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold

namespace TangentBundle

variable (𝕜 : Type*) {𝕜' : Type*}
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]

/-- The identification of tangent-bundle carriers reads both tangent vectors in the same
preferred model coordinates. Continuity is established separately using bundle charts. -/
private def restrictScalarsEquiv : TangentBundle 𝓘(𝕜', E) M ≃ TangentBundle 𝓘(𝕜, E) M where
  toFun p := ⟨p.proj, (tangentSpaceCastModel 𝓘(𝕜, E) p.proj).symm
    (tangentSpaceCastModel 𝓘(𝕜', E) p.proj p.2)⟩
  invFun p := ⟨p.proj, (tangentSpaceCastModel 𝓘(𝕜', E) p.proj).symm
    (tangentSpaceCastModel 𝓘(𝕜, E) p.proj p.2)⟩
  left_inv p := by simp
  right_inv p := by simp

variable [IsManifold 𝓘(𝕜', E) 1 M] [IsManifold 𝓘(𝕜, E) 1 M]

private theorem trivializationAt_restrictScalarsEquiv (x : M)
    (p : TangentBundle 𝓘(𝕜', E) M) (hp : p.proj ∈ (chartAt E x).source) :
    trivializationAt E (TangentSpace 𝓘(𝕜, E)) x (restrictScalarsEquiv 𝕜 M p) =
      trivializationAt E (TangentSpace 𝓘(𝕜', E)) x p := by
  have h := TauCeti.tangentCoordChange_restrictScalars 𝕜 (𝕜' := 𝕜')
    (x := p.proj) (y := x) ⟨mem_chart_source E p.proj, hp⟩
  rw [TangentBundle.trivializationAt_apply, TangentBundle.trivializationAt_apply]
  -- The carrier equivalence is defined through the model casts; the coordinate changes
  -- below act on the resulting vectors in E.
  change (p.proj, tangentCoordChange 𝓘(𝕜, E) p.proj x p.proj
    (tangentSpaceCastModel 𝓘(𝕜', E) p.proj p.2)) =
    (p.proj, tangentCoordChange 𝓘(𝕜', E) p.proj x p.proj
      (tangentSpaceCastModel 𝓘(𝕜', E) p.proj p.2))
  rw [h]
  rfl

private theorem continuous_restrictScalarsEquiv :
    Continuous (restrictScalarsEquiv 𝕜 (𝕜' := 𝕜') (E := E) M) := by
  apply continuous_iff_continuousAt.2
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj E (TangentSpace 𝓘(𝕜', E))).continuousAt, ?_⟩
  have hchart := ((FiberBundle.continuousAt_totalSpace E
    (id : TangentBundle 𝓘(𝕜', E) M → _) (x₀ := p)).1 continuousAt_id).2
  apply hchart.congr_of_eventuallyEq
  filter_upwards [(FiberBundle.continuous_proj E (TangentSpace 𝓘(𝕜', E))).continuousAt
    ((chartAt E p.proj).open_source.mem_nhds (mem_chart_source E p.proj))] with q hq
  exact congrArg Prod.snd (trivializationAt_restrictScalarsEquiv 𝕜 (𝕜' := 𝕜') M p.proj q hq)

private theorem continuous_restrictScalarsEquiv_symm :
    Continuous (restrictScalarsEquiv 𝕜 (𝕜' := 𝕜') (E := E) M).symm := by
  apply continuous_iff_continuousAt.2
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(FiberBundle.continuous_proj E (TangentSpace 𝓘(𝕜, E))).continuousAt, ?_⟩
  have hchart := ((FiberBundle.continuousAt_totalSpace E
    (id : TangentBundle 𝓘(𝕜, E) M → _) (x₀ := p)).1 continuousAt_id).2
  apply hchart.congr_of_eventuallyEq
  filter_upwards [(FiberBundle.continuous_proj E (TangentSpace 𝓘(𝕜, E))).continuousAt
    ((chartAt E p.proj).open_source.mem_nhds (mem_chart_source E p.proj))] with q hq
  have h := congrArg Prod.snd
    (trivializationAt_restrictScalarsEquiv 𝕜 (𝕜' := 𝕜') M p.proj
      ((restrictScalarsEquiv 𝕜 (𝕜' := 𝕜') M).symm q) hq).symm
  rw [Equiv.apply_symm_apply] at h
  -- The inverse carrier equivalence fixes the base by its definition.
  convert h using 1 <;> rfl

/-- The tangent bundle over a normed field extension is canonically homeomorphic to the
tangent bundle of the manifold with scalars restricted. The base point and preferred tangent
coordinates are unchanged. For `ℝ ⊆ ℂ`, this identifies the complex tangent bundle with the
real tangent bundle as topological bundles. -/
def restrictScalarsHomeomorph : TangentBundle 𝓘(𝕜', E) M ≃ₜ TangentBundle 𝓘(𝕜, E) M where
  toEquiv := restrictScalarsEquiv 𝕜 M
  continuous_toFun := continuous_restrictScalarsEquiv 𝕜 M
  continuous_invFun := continuous_restrictScalarsEquiv_symm 𝕜 M

/-- Scalar restriction fixes the base point of a tangent vector. -/
@[simp]
theorem restrictScalarsHomeomorph_proj (p : TangentBundle 𝓘(𝕜', E) M) :
    (restrictScalarsHomeomorph 𝕜 M p).proj = p.proj := (rfl)

/-- The inverse scalar comparison also fixes the base point. -/
@[simp]
theorem restrictScalarsHomeomorph_symm_proj (p : TangentBundle 𝓘(𝕜, E) M) :
    ((restrictScalarsHomeomorph 𝕜 (𝕜' := 𝕜') M).symm p).proj = p.proj := (rfl)

/-- Scalar restriction reads the tangent vector in the same model coordinates. -/
@[simp]
theorem restrictScalarsHomeomorph_apply (x : M) (v : TangentSpace 𝓘(𝕜', E) x) :
    restrictScalarsHomeomorph 𝕜 M ⟨x, v⟩ =
      ⟨x, (tangentSpaceCastModel 𝓘(𝕜, E) x).symm
        (tangentSpaceCastModel 𝓘(𝕜', E) x v)⟩ := (rfl)

/-- The inverse scalar comparison reads the tangent vector in the same model coordinates. -/
@[simp]
theorem restrictScalarsHomeomorph_symm_apply (x : M) (v : TangentSpace 𝓘(𝕜, E) x) :
    (restrictScalarsHomeomorph 𝕜 (𝕜' := 𝕜') M).symm ⟨x, v⟩ =
      ⟨x, (tangentSpaceCastModel 𝓘(𝕜', E) x).symm
        (tangentSpaceCastModel 𝓘(𝕜, E) x v)⟩ := (rfl)

/-- On each bundle chart, scalar restriction is the identity in base and fibre coordinates. -/
@[simp]
theorem trivializationAt_restrictScalarsHomeomorph (x : M)
    (p : TangentBundle 𝓘(𝕜', E) M) (hp : p.proj ∈ (chartAt E x).source) :
    trivializationAt E (TangentSpace 𝓘(𝕜, E)) x (restrictScalarsHomeomorph 𝕜 M p) =
      trivializationAt E (TangentSpace 𝓘(𝕜', E)) x p :=
  trivializationAt_restrictScalarsEquiv 𝕜 M x p hp

variable {M} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜' E'] [IsScalarTower 𝕜 𝕜' E']
  {N : Type*} [TopologicalSpace N] [ChartedSpace E' N]
  [IsManifold 𝓘(𝕜', E') 1 N] [IsManifold 𝓘(𝕜, E') 1 N]

/-- The scalar comparison commutes with the tangent map at a vector whose base point is a
point of differentiability over the larger field. In particular, the real tangent map of a
holomorphic map is its complex tangent map under the canonical topological identifications. -/
theorem restrictScalarsHomeomorph_tangentMap {f : M → N}
    (p : TangentBundle 𝓘(𝕜', E) M) (hf : MDifferentiableAt 𝓘(𝕜', E) 𝓘(𝕜', E') f p.proj) :
    restrictScalarsHomeomorph 𝕜 N (tangentMap 𝓘(𝕜', E) 𝓘(𝕜', E') f p) =
      tangentMap 𝓘(𝕜, E) 𝓘(𝕜, E') f (restrictScalarsHomeomorph 𝕜 M p) := by
  have h := congrArg (fun L : E →L[𝕜] E' ↦
    L (tangentSpaceCastModel 𝓘(𝕜', E) p.proj p.2))
    (hf.mfderiv_restrictScalars 𝕜)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h
  -- Repackage the coordinate equality as a tangent vector over f p.proj. The carrier
  -- equivalence was defined with precisely these model casts.
  convert congrArg (fun w : E' ↦ (⟨f p.proj,
    (tangentSpaceCastModel 𝓘(𝕜, E') (f p.proj)).symm w⟩ : TangentBundle 𝓘(𝕜, E') N))
    h.symm using 1 <;> rfl

end TangentBundle
