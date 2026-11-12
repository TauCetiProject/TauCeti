/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Chart
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The Floer equation in a chart of a manifold

Let `u : ℝ × ℝ → M` solve the Floer equation `(du - X_K)^{0,1} = 0` on a manifold `M` for a
perturbation `K = K_s ds + K_t dt` and domain-dependent almost complex structures `J(z, x)` on the
tangent spaces of `M`. This file reads the equation in the chart at a point `α`, where it becomes
a coordinate Floer equation on the model space `E`, so that analytic arguments for coordinate
equations (elliptic estimates, compactness) apply to the pieces of a solution with values in one
chart.

* `TauCeti.Floer.almostComplexInChartAt I α J` and
  `TauCeti.SmoothTwoForm.hamiltonianVectorFieldInChartAt ω α K` are `J` and the Hamiltonian
  vector field of `K`, read in the chart: at a chart coordinate `y`, the structure or the vector
  at `(extChartAt I α).symm y`, written in the tangent coordinates of the chart at `α` (the
  trivialization `trivializationAt E (TangentSpace I) α`). The structure in the chart squares to
  `-1` on the chart target (`TauCeti.Floer.almostComplexInChartAt_apply_apply`). For a jointly
  `Cⁿ` family it is the coordinate expression `ContMDiffAlmostComplexStructureFamily.inChart`
  (`TauCeti.Floer.almostComplexInChartAt_eq_inChart`), which is `Cⁿ` on the chart target.
* For a map `u` into the chart source, with coordinate expression `v = extChartAt I α ∘ u`, the
  perturbed derivative `du - X_K` in tangent coordinates is `dv` minus the Hamiltonian vector
  fields in the chart (`TauCeti.SmoothTwoForm.continuousLinearMapAt_perturbedMFDeriv_apply`).
  So if `u` solves the Floer equation, `v` solves `∂ₜv - X_{K_t} = J (∂ₛv - X_{K_s})` with the
  data read in the chart
  (`TauCeti.SmoothTwoForm.fderiv_extChartAt_comp_stdComplexLineImag_sub`).

Compactness of solutions with values in one chart is
`TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold`.
-/

public section

noncomputable section

open Bundle ContinuousLinearMap Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M]

namespace Floer

/-- The almost complex structures `J(z, x)` on the tangent spaces of `M`, read in the chart at
`α`: at `(z, y)`, the structure `J(z, x)` at the point `x = (extChartAt I α).symm y` with chart
coordinate `y`, written in the tangent coordinates of the chart at `α`. Outside the chart target
the value is junk.

This is the coordinate expression `ContMDiffAlmostComplexStructureFamily.inChart` for the unbundled
families of structures in which the manifold Floer equation `SmoothTwoForm.perturbedMFDeriv` is
stated (`TauCeti.Floer.almostComplexInChartAt_eq_inChart`). -/
def almostComplexInChartAt (I : ModelWithCorners ℝ E H) [IsManifold I (⊤ : ℕ∞) M] (α : M)
    (J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)) (p : (ℝ × ℝ) × E) :
    E →L[ℝ] E :=
  inCoordinates E (TangentSpace I) E (TangentSpace I) α ((extChartAt I α).symm p.2) α
    ((extChartAt I α).symm p.2)
    (J p.1 ((extChartAt I α).symm p.2)).toLinearMap.toContinuousLinearMap

variable {α : M} {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}

/-- At a chart coordinate `y`, the structure in the chart is the structure at
`x = (extChartAt I α).symm y` conjugated by the tangent coordinates of the chart. -/
theorem almostComplexInChartAt_apply (z : ℝ × ℝ) (y v : E) :
    almostComplexInChartAt I α J (z, y) v =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ ((extChartAt I α).symm y)
        (J z ((extChartAt I α).symm y)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) v)) := by
  rw [almostComplexInChartAt, inCoordinates, comp_apply, comp_apply,
    LinearMap.coe_toContinuousLinearMap']

/-- On the chart target, the structure in the chart squares to `-1`. -/
theorem almostComplexInChartAt_apply_apply {y : E} (hy : y ∈ (extChartAt I α).target)
    (z : ℝ × ℝ) (v : E) :
    almostComplexInChartAt I α J (z, y) (almostComplexInChartAt I α J (z, y) v) = -v := by
  have hx : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I] using
      (extChartAt I α).map_target hy
  rw [almostComplexInChartAt_apply, almostComplexInChartAt_apply,
    Trivialization.symmL_continuousLinearMapAt _ hx, AlmostComplexStructure.apply_apply, map_neg,
    Trivialization.continuousLinearMapAt_symmL _ hx]

/-- For a jointly regular family of structures over the domain `ℝ × ℝ`, the structure in the chart
is the coordinate expression of the family in the product chart at `(p, α)`, whatever `p`. In
particular it is `Cⁿ` on the chart target for a `Cⁿ` family
(`ContMDiffAlmostComplexStructureFamily.contDiffOn_inChart`). -/
theorem almostComplexInChartAt_eq_inChart {n : ℕ∞}
    (J : ContMDiffAlmostComplexStructureFamily I M 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) n) (p : ℝ × ℝ) (α : M) :
    almostComplexInChartAt I α (fun z x ↦ J.almostComplexStructureAt (z, x)) =
      J.inChart (p, α) := by
  ext ⟨z, y⟩ v
  refine (almostComplexInChartAt_apply (J := fun z x ↦ J.almostComplexStructureAt (z, x))
    z y v).trans ?_
  rw [ContMDiffAlmostComplexStructureFamily.inChart_mk,
    ContMDiffAlmostComplexStructure.inChart_def, extChartAt_model_space_eq_id, inCoordinates,
    comp_apply, comp_apply]
  simp only [ContMDiffAlmostComplexStructureFamily.almostComplexStructureAt_toLinearMap,
    ContMDiffAlmostComplexStructureFamily.freeze_toEndomorphism_apply, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq]
  -- The two sides apply the same endomorphism, once through its underlying linear map.
  rfl

end Floer

namespace SmoothTwoForm

variable {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ} {u : ℝ × ℝ → M} {z : ℝ × ℝ} {α : M}

/-- The Hamiltonian vector field of a family of Hamiltonians `K(z)`, read in the chart at `α`: at
`(z, y)`, the vector `X_{K(z)}(x)` at `x = (extChartAt I α).symm y`, in the tangent coordinates of
the chart at `α`. Outside the chart target the value is junk. -/
def hamiltonianVectorFieldInChartAt (ω : SmoothTwoForm I M) (α : M) (K : ℝ × ℝ → M → ℝ)
    (p : (ℝ × ℝ) × E) : E :=
  (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ ((extChartAt I α).symm p.2)
    (ω.hamiltonianVectorField (K p.1) ((extChartAt I α).symm p.2))

omit [FiniteDimensional ℝ E] in
/-- At a chart coordinate `y`, the Hamiltonian vector field in the chart is the tangent coordinate
of `X_{K(z)}` at `x = (extChartAt I α).symm y`. -/
theorem hamiltonianVectorFieldInChartAt_apply (ω : SmoothTwoForm I M) (α : M)
    (K : ℝ × ℝ → M → ℝ) (z : ℝ × ℝ) (y : E) :
    ω.hamiltonianVectorFieldInChartAt α K (z, y) =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ ((extChartAt I α).symm y)
        (ω.hamiltonianVectorField (K z) ((extChartAt I α).symm y)) :=
  (rfl)

omit [FiniteDimensional ℝ E] in
/-- **The perturbed derivative in a chart.** In the tangent coordinates of the chart at `α`, the
perturbed derivative `du - X_K` of a map `u` into the chart source is the derivative of its
coordinate expression `extChartAt I α ∘ u` minus the Hamiltonian vector fields read in the
chart. -/
theorem continuousLinearMapAt_perturbedMFDeriv_apply (ω : SmoothTwoForm I M)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hz : u z ∈ (extChartAt I α).source)
    (v : ℝ × ℝ) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ (u z)
        (ω.perturbedMFDeriv Ks Kt u z v) =
      fderiv ℝ (extChartAt I α ∘ u) z v -
        v.1 • ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z)) -
        v.2 • ω.hamiltonianVectorFieldInChartAt α Kt (z, extChartAt I α (u z)) := by
  rw [hamiltonianVectorFieldInChartAt_apply, hamiltonianVectorFieldInChartAt_apply,
    (extChartAt I α).left_inv hz, hu.fderiv_extChartAt_comp_apply hz,
    ← TangentBundle.continuousLinearMapAt_trivializationAt (by rwa [← extChartAt_source I]),
    perturbedMFDeriv_apply, map_sub, map_sub, map_smul, map_smul]
  -- The two sides differ only in the identification of `TangentSpace 𝓘(ℝ, E)` with `E`.
  rfl

/-- **The Floer equation in a chart.** Let `u` solve the Floer equation
`∂ₛu - X_{K_s} + J (∂ₜu - X_{K_t}) = 0` at `z`, with `u z` in the source of the chart at `α`.
Then its coordinate expression `v = extChartAt I α ∘ u` solves the coordinate Floer equation
`∂ₜv - X_{K_t} = J (∂ₛv - X_{K_s})` at `z`, where `J` and the Hamiltonian vector fields are
read in the chart. -/
theorem fderiv_extChartAt_comp_stdComplexLineImag_sub (ω : SmoothTwoForm I M)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hz : u z ∈ (extChartAt I α).source)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineImag -
        ω.hamiltonianVectorFieldInChartAt α Kt (z, extChartAt I α (u z)) =
      Floer.almostComplexInChartAt I α J (z, extChartAt I α (u z))
        (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal -
          ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z))) := by
  have hb : u z ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
  have hre := ω.continuousLinearMapAt_perturbedMFDeriv_apply (Ks := Ks) (Kt := Kt) hu hz
    stdComplexLineReal
  have him := ω.continuousLinearMapAt_perturbedMFDeriv_apply (Ks := Ks) (Kt := Kt) hu hz
    stdComplexLineImag
  simp only [stdComplexLineReal_fst, stdComplexLineReal_snd, stdComplexLineImag_fst,
    stdComplexLineImag_snd, zero_smul, one_smul, sub_zero] at hre him
  have h' := h.apply_stdComplexLineImag
  simp only [ContinuousLinearMap.coe_coe] at h'
  rw [← hre, ← him, h', Floer.almostComplexInChartAt_apply, (extChartAt I α).left_inv hz,
    Trivialization.symmL_continuousLinearMapAt _ hb]

end SmoothTwoForm

end TauCeti

end
