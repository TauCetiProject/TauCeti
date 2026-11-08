/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Topology.VectorBundle.Coordinates

/-!
# The canonical line bundle of a manifold

Let `M` be a manifold modelled on `I : ModelWithCorners 𝕜 E H`, with `E` of finite dimension
`n`. Its canonical bundle `K_M = ⋀ⁿ T*M` is the top exterior power of the cotangent bundle. Its
fibre at `x` is realised here as the space `TangentSpace I x [⋀^Fin n]→L[𝕜] 𝕜` of top-degree
scalar-valued alternating forms on the tangent space, that is, as the dual `(⋀ⁿ T_xM)*`, which in
finite dimension is canonically isomorphic to `⋀ⁿ T*_xM`. The family of these fibres is
`TauCeti.CanonicalBundle I M`.

This is Mathlib's bundle of continuous alternating maps, the carrier of differential forms,
applied to the tangent bundle and the trivial line bundle. No topology, trivialization or atlas is
chosen here: the fibre bundle and vector bundle structures of `K_M` are Mathlib's, and over a field
of characteristic zero a `C^(k+1)` manifold has a `C^k` canonical bundle by
`ContMDiffVectorBundle.continuousAlternatingMap`. For a complex manifold, modelled on
`𝓘(ℂ, E)` with regularity `∞`, this is the holomorphic canonical line bundle, whose holomorphic
sections are the holomorphic forms of top degree `n = finrank ℂ E`.

Every fibre is a line (`TauCeti.CanonicalBundle.finrank_eq_one`). In the trivialization of `K_M`
induced by the chart at `x₀`, a form `ω` at `x` becomes `ω` evaluated on the coordinate tangent
vectors of that chart (`FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd`). Passing
from the chart at `x₀` to the chart at `x₁` multiplies its value on a basis `b` of `E` by the
determinant of `tangentCoordChange I x₁ x₀ x`, the derivative of the change from the coordinates of
the chart at `x₁` to those of the chart at `x₀`
(`TauCeti.CanonicalBundle.trivializationAt_apply_snd_basis_eq_det_mul`). Thus the transition
functions of the canonical bundle are the Jacobian determinants of the coordinate changes.

The same law, read on sections, concerns the coordinate form `dz₁ ∧ ⋯ ∧ dzₙ` of a chart,
`TauCeti.CanonicalBundle.coordForm`, the determinant form of `b` read through the chart. On the
source of the chart it vanishes nowhere and is `C^k` whenever the canonical bundle is a `C^k`
vector bundle, so it is holomorphic on a complex manifold. Every top-degree form there is a
multiple of it, with coefficient its value read in the trivialization of the chart, and the
coordinate forms of two charts satisfy `dz⁰₁ ∧ ⋯ ∧ dz⁰ₙ = det (∂z⁰/∂z¹) dz¹₁ ∧ ⋯ ∧ dz¹ₙ`.

## Main declarations

* `TauCeti.CanonicalBundle`: the canonical bundle, with fibres the top-degree alternating forms on
  the tangent spaces.
* `TauCeti.CanonicalBundle.finrank_eq_one`: its fibres are lines.
* `TauCeti.CanonicalBundle.trivializationAt_apply_snd_basis_eq_det_mul`: the transition functions
  are the Jacobian determinants of the coordinate changes.
* `TauCeti.CanonicalBundle.coordForm`: the coordinate form `dz₁ ∧ ⋯ ∧ dzₙ` of a chart, with
  `TauCeti.CanonicalBundle.contMDiffOn_coordForm`, `TauCeti.CanonicalBundle.coordForm_ne_zero`,
  `TauCeti.CanonicalBundle.eq_smul_coordForm` and
  `TauCeti.CanonicalBundle.coordForm_eq_det_smul_coordForm`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2 (the
  canonical bundle `K_X = det Ω_X` and its transition functions).
* Phillip Griffiths and Joseph Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 1,
  Section 1 (the canonical bundle of a complex manifold).
-/

public section

open Bundle Module
open scoped Manifold

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H]

/-- The canonical bundle `K_M = ⋀ⁿ T*M` of a manifold `M` modelled on `I`, where
`n = finrank 𝕜 E`: the fibre at `x` is the space of top-degree scalar-valued continuous
alternating forms on `TangentSpace I x`, the dual of `⋀ⁿ T_xM`. Its fibre bundle and vector bundle
structures, with model fibre `E [⋀^Fin n]→L[𝕜] 𝕜`, are Mathlib's bundle of continuous alternating
maps from the tangent bundle to the trivial line bundle. For a complex manifold modelled on
`𝓘(ℂ, E)` it is the holomorphic canonical line bundle. -/
abbrev CanonicalBundle (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : M → Type _ :=
  fun x ↦ TangentSpace I x [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜

namespace CanonicalBundle

variable {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The fibres of the canonical bundle are lines. -/
theorem finrank_eq_one [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] (x : M) :
    finrank 𝕜 (CanonicalBundle I M x) = 1 :=
  (finBasis 𝕜 E).finrank_continuousAlternatingMap_eq_one

variable [IsManifold I 1 M]

/-- The transition functions of the canonical bundle are the Jacobian determinants of the
coordinate changes. Evaluated on a basis `b` of the model space, a form at `x` read in the
trivialization of the chart at `x₁` is its value read in the trivialization of the chart at `x₀`,
multiplied by the determinant of the derivative `tangentCoordChange I x₁ x₀ x` of the change from
the coordinates at `x₁` to those at `x₀`. -/
theorem trivializationAt_apply_snd_basis_eq_det_mul {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hx₁ : x ∈ (chartAt H x₁).source)
    (ω : CanonicalBundle I M x) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) :
    (trivializationAt (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) x₁ ⟨x, ω⟩).2 b =
      LinearMap.det (tangentCoordChange I x₁ x₀ x : E →ₗ[𝕜] E) *
        (trivializationAt (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) x₀ ⟨x, ω⟩).2
          b := by
  set e₀ := trivializationAt E (TangentSpace I) x₀
  set e₁ := trivializationAt E (TangentSpace I) x₁
  have hx : x ∈ e₁.baseSet ∩ e₀.baseSet := ⟨by simpa [e₁] using hx₁, by simpa [e₀] using hx₀⟩
  -- The inverse of the trivialization at `x₁` factors through the coordinate change into the
  -- trivialization at `x₀`, which is `tangentCoordChange I x₁ x₀ x`.
  have hsymm : e₁.symmL 𝕜 x = (e₀.symmL 𝕜 x).comp (tangentCoordChange I x₁ x₀ x) := by
    -- `tangentCoordChange` is the coordinate change of the tangent bundle core.
    have hcoord : (e₁.coordChangeL 𝕜 e₀ x : E →L[𝕜] E) = tangentCoordChange I x₁ x₀ x :=
      (tangentBundleCore I M).trivializationAt_coordChangeL hx
    rw [← hcoord, ← e₁.comp_continuousLinearEquivAt_eq_coord_change e₀ hx]
    ext v
    simp [e₀.symmL_apply hx.2, e₁.symmL_apply hx.1, e₀.symm_apply_apply_mk hx.2]
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd, hsymm]
  simpa only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousLinearMap.coe_comp,
    Function.comp_assoc] using
    (ω.compContinuousLinearMap (e₀.symmL 𝕜 x)).compContinuousLinearMap_apply_basis b
      (tangentCoordChange I x₁ x₀ x)

/-! ### The coordinate form of a chart -/

section CoordForm

variable [CompleteSpace 𝕜]

variable (I) in
/-- The coordinate form `dz₁ ∧ ⋯ ∧ dzₙ` of the chart at `x₀`, relative to a basis `b` of the
model space: at `x` it is the determinant form of `b` read through the tangent-bundle
trivialization of that chart. On the source of the chart it is a nowhere-vanishing section of the
canonical bundle, `C^k` when the canonical bundle is a `C^k` vector bundle, so holomorphic on a
complex manifold. Outside the source the trivialization is zero, and so is this form in positive
dimension. -/
noncomputable def coordForm (x₀ : M) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) (x : M) :
    CanonicalBundle I M x :=
  b.continuousDet.compContinuousLinearMap
    ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x)

variable {x₀ x₁ x : M} {b : Basis (Fin (finrank 𝕜 E)) 𝕜 E}

/-- The coordinate form evaluates the determinant of the coordinates of tangent vectors in the
chart. -/
@[simp]
theorem coordForm_apply (v : Fin (finrank 𝕜 E) → TangentSpace I x) :
    coordForm I x₀ b x v =
      b.det fun i ↦ (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (v i) := by
  simp [coordForm, Function.comp_def]

/-- Evaluated on the coordinate tangent vectors of its own chart, the coordinate form is the
constant determinant form of the basis. This is the simp normal form of
`TauCeti.CanonicalBundle.trivializationAt_apply_snd_coordForm`. -/
@[simp]
theorem coordForm_compContinuousLinearMap_symmL (hx : x ∈ (chartAt H x₀).source) :
    (coordForm I x₀ b x).compContinuousLinearMap
      ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x) = b.continuousDet := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
  ext v
  simp only [coordForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    Trivialization.continuousLinearMapAt_symmL _ hx', Module.Basis.continuousDet_apply]

/-- Read in the trivialization of its own chart, the coordinate form is the constant determinant
form of the basis. -/
theorem trivializationAt_apply_snd_coordForm (hx : x ∈ (chartAt H x₀).source) :
    (trivializationAt (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) x₀
      ⟨x, coordForm I x₀ b x⟩).2 = b.continuousDet := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    coordForm_compContinuousLinearMap_symmL hx]

/-- The coordinate form does not vanish on the source of its chart. -/
@[simp]
theorem coordForm_ne_zero (hx : x ∈ (chartAt H x₀).source) : coordForm I x₀ b x ≠ 0 := by
  intro h
  have := congrArg (fun ω : CanonicalBundle I M x ↦
    (trivializationAt (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) x₀ ⟨x, ω⟩).2 b) h
  simp [trivializationAt_apply_snd_coordForm hx, b.det_self] at this

/-- On the source of the chart at `x₀`, every top-degree form is a multiple of the coordinate form
of that chart, with coefficient the value of the form read in the trivialization of the chart. -/
theorem eq_smul_coordForm (hx : x ∈ (chartAt H x₀).source) (ω : CanonicalBundle I M x) :
    ω = (trivializationAt (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) x₀
      ⟨x, ω⟩).2 b • coordForm I x₀ b x := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
  ext v
  have h := (ω.compContinuousLinearMap
    ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x)).apply_eq_det_mul b
      fun i ↦ (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (v i)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    Trivialization.symmL_continuousLinearMapAt _ hx'] at h
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, coordForm_apply,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, mul_comm]
  exact h

/-- The coordinate forms of two charts differ by the Jacobian determinant of the coordinate change:
`dz⁰₁ ∧ ⋯ ∧ dz⁰ₙ = det (∂z⁰/∂z¹) dz¹₁ ∧ ⋯ ∧ dz¹ₙ`, where `tangentCoordChange I x₁ x₀ x` is the
derivative of the change from the coordinates `z¹` at `x₁` to the coordinates `z⁰` at `x₀`. -/
theorem coordForm_eq_det_smul_coordForm (hx₀ : x ∈ (chartAt H x₀).source)
    (hx₁ : x ∈ (chartAt H x₁).source) :
    coordForm I x₀ b x =
      LinearMap.det (tangentCoordChange I x₁ x₀ x : E →ₗ[𝕜] E) • coordForm I x₁ b x := by
  conv_lhs => rw [eq_smul_coordForm (x₀ := x₁) (b := b) hx₁ (coordForm I x₀ b x)]
  rw [trivializationAt_apply_snd_basis_eq_det_mul hx₀ hx₁, trivializationAt_apply_snd_coordForm hx₀]
  simp [b.det_self]

variable {k : WithTop ℕ∞}
  [ContMDiffVectorBundle k (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M) I]

/-- The coordinate form is a `C^k` section of the canonical bundle over the source of its chart,
whenever the canonical bundle is a `C^k` vector bundle; for a complex manifold it is
holomorphic. -/
theorem contMDiffOn_coordForm (x₀ : M) (b : Basis (Fin (finrank 𝕜 E)) 𝕜 E) :
    ContMDiffOn I (I.prod 𝓘(𝕜, E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜)) k
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) x (coordForm I x₀ b x))
      (chartAt H x₀).source := by
  rw [(trivializationAt (E [⋀^Fin (finrank 𝕜 E)]→L[𝕜] 𝕜) (CanonicalBundle I M)
    x₀).contMDiffOn_section_iff (chartAt H x₀).open_source (by simp)]
  exact contMDiffOn_const.congr fun x hx ↦ trivializationAt_apply_snd_coordForm hx

end CoordForm

end CanonicalBundle

end TauCeti
