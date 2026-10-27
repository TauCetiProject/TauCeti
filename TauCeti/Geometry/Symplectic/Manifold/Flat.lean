/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The flat map of a two-form on a manifold

A two-form `σ` on a manifold `M` gives at each point its **flat map**
`σ♭_x : T_x M → T_x^* M`, `v ↦ ι_v σ = σ(v, ·)` (`TauCeti.SmoothTwoForm.flat`), the continuous
form of the algebraic bilinear form `TauCeti.SmoothForm.bilinFormAt`. The flat maps of a smooth
two-form form a smooth section of the bundle `Hom(TM, Hom(TM, ℝ))`
(`TauCeti.SmoothTwoForm.contMDiff_flat`). On a finite-dimensional manifold, the form is
nondegenerate exactly when every flat map is invertible
(`TauCeti.SmoothTwoForm.isNondegenerate_iff_isInvertible_flat`); the inverse maps then form a
smooth section as well, by `ContMDiff.clm_bundle_inverse`.

Inverting the flat map turns covector fields into vector fields: a Hamiltonian vector field is
`(σ♭)⁻¹ df`, and the Liouville field of a primitive `α` is `(σ♭)⁻¹ α`.

## Main declarations

* `TauCeti.SmoothTwoForm.flat`: the flat map `v ↦ σ(v, ·)` at a point.
* `TauCeti.SmoothTwoForm.interior_apply_eq_ofSubsingleton_flat`: the interior product `ι_X σ` is
  the flat map applied to `X`.
* `TauCeti.SmoothTwoForm.contMDiff_flat`: the flat maps form a smooth section.
* `TauCeti.SmoothTwoForm.isNondegenerate_iff_isInvertible_flat`: nondegeneracy is invertibility of
  the flat maps, in finite dimensions.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

/-- The **flat map** of a two-form at a point: the contraction `v ↦ ι_v σ = σ(v, ·)`, as a
continuous linear map from the tangent space to its dual. -/
def flat (σ : SmoothTwoForm I M) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  -- The tangent space is the model space `E`, whose norm gives continuous currying.
  ContinuousAlternatingMap.flatL ℝ E ℝ (σ.1 x)

/-- The flat map evaluates as the two-form. -/
@[simp]
theorem flat_apply (σ : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    σ.flat x v w = SmoothBundleForm.eval₂ σ x v w := by
  rw [SmoothBundleForm.eval₂_apply]
  exact ContinuousAlternatingMap.flatL_apply_apply (E := E) (σ.1 x) v w

/-- The interior product `ι_X σ` at a point is the flat map applied to `X`, read as a one-form. -/
theorem interior_apply_eq_ofSubsingleton_flat (σ : SmoothTwoForm I M)
    (X : (x : M) → TangentSpace I x) (x : M) :
    RoughForm.interior X σ.1 x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0 (σ.flat x (X x)) := by
  rw [RoughForm.interior_apply_eq_curryLeft]
  exact (ContinuousAlternatingMap.ofSubsingleton_flatL_apply (E := E) (σ.1 x) (X x)).symm

/-- **The flat maps of a two-form form a smooth section** of the bundle `Hom(TM, Hom(TM, ℝ))`. -/
theorem contMDiff_flat (σ : SmoothTwoForm I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (σ.flat x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hσ := (contMDiffAt_continuousAlternatingMap_bundle _).1 (σ.contMDiff x₀)
  -- In coordinates, the flat map is `flatL` applied to the coordinate expression of the form.
  refine ((ContinuousAlternatingMap.flatL ℝ E ℝ).contDiff.comp_contMDiffAt
    hσ.2).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with y hy
  ext v w
  rw [inCoordinates_apply_eq₂ (E₃ := Trivial M ℝ) hy hy (Set.mem_univ _), Function.comp_apply,
    ContinuousAlternatingMap.flatL_apply_apply]
  simp only [flat_apply, SmoothBundleForm.eval₂_apply, Trivial.fiberBundle_trivializationAt',
    Trivial.linearMapAt_trivialization, Trivial.continuousLinearMapAt_trivialization,
    ContinuousAlternatingMap.inCoordinates, ContinuousLinearMap.id_compContinuousAlternatingMap,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, LinearMap.id_coe, id_eq]
  congr 1
  ext i
  fin_cases i <;> exact (Trivialization.symmL_apply _ hy _).symm

/-- The flat map is the continuous form of the algebraic bilinear form of `σ` at a point. -/
theorem toBilinForm_flat (σ : SmoothTwoForm I M) (x : M) :
    (σ.flat x).toBilinForm = σ.bilinFormAt x := by
  ext v w
  simp

/-- In finite dimensions, a two-form is nondegenerate exactly when all its flat maps are
invertible. -/
theorem isNondegenerate_iff_isInvertible_flat [FiniteDimensional ℝ E] :
    σ.IsNondegenerate ↔ ∀ x, (σ.flat x).IsInvertible := by
  rw [isNondegenerate_iff_separatingLeft]
  refine ⟨fun h x ↦ ContinuousLinearMap.isInvertible_of_separatingLeft (E := E) fun v hv ↦
    h x v fun w ↦ (flat_apply σ x v w).symm.trans (hv w), fun h x v hv ↦ (h x).injective ?_⟩
  ext w
  simpa using hv w

/-- The flat maps of a nondegenerate two-form on a finite-dimensional manifold are invertible. -/
theorem IsNondegenerate.isInvertible_flat [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
    (x : M) : (σ.flat x).IsInvertible :=
  isNondegenerate_iff_isInvertible_flat.1 h x

end SmoothTwoForm

end TauCeti
