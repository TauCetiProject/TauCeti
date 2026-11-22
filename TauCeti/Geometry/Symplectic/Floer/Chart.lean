/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Family.Chart
import TauCeti.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The Floer equation in a chart of a manifold

Let `u : ℝ × ℝ → M` solve the Floer equation `(du - X_K)^{0,1} = 0` on a manifold `M` for a
perturbation `K = K_s ds + K_t dt` and domain-dependent almost complex structures `J(z, x)` on the
tangent spaces of `M`. This file reads the equation in a chart, where it becomes a coordinate
Floer equation on a vector space, so that analytic arguments for coordinate equations (elliptic
estimates, compactness) apply to the pieces of a solution with values in one chart. Two kinds of
chart are treated: the charts of the atlas of `M`, which need no closedness of `ω` and no inner
product on the model space, and symplectic charts, which carry `ω` to a constant symplectic form.

## Charts of the atlas

In the chart at a point `α`, the equation becomes a coordinate Floer equation on the model space
`E`.

* `TauCeti.Floer.almostComplexInChartAt I α J` and
  `TauCeti.SmoothTwoForm.hamiltonianVectorFieldInChartAt ω α K` are `J` and the Hamiltonian
  vector field of `K`, read in the chart: at a chart coordinate `y`, the structure or the vector
  at `(extChartAt I α).symm y`, written in the tangent coordinates of the chart at `α` (the
  trivialization `trivializationAt E (TangentSpace I) α`). The structure in the chart squares to
  `-1` on the chart target (`TauCeti.Floer.almostComplexInChartAt_apply_apply`). For a jointly
  `Cⁿ` family it is the coordinate expression `ContMDiffAlmostComplexStructureFamily.inChart`
  (`TauCeti.Floer.almostComplexInChartAt_eq_inChart`), which is `Cⁿ` on the chart target; for a
  family of smooth structures `J z`, such as a domain-independent one, it is
  `SmoothAlmostComplexStructure.inChart` of `J z`
  (`TauCeti.Floer.almostComplexInChartAt_almostComplexStructureAt`). More generally, jointly
  continuous or `Cⁿ` parametrized families of almost complex structures or Hamiltonian vector fields
  have jointly continuous or `Cⁿ` chart expressions
  (`TauCeti.Floer.continuousOn_almostComplexInChartAt`,
  `TauCeti.Floer.contDiffOn_almostComplexInChartAt`,
  `TauCeti.SmoothTwoForm.continuousOn_hamiltonianVectorFieldInChartAt`,
  `TauCeti.SmoothTwoForm.contDiffOn_hamiltonianVectorFieldInChartAt`).
* `TauCeti.SmoothTwoForm.associatedBilinFormInChartAt ω α J` is the bilinear form
  `ω(·, J(z, x) ·)` read in the chart, at `x = (extChartAt I α).symm y` and on tangent coordinates
  (`TauCeti.SmoothTwoForm.associatedBilinFormInChartAt_extChartAt`), that is, the coordinate
  expression of `ω` on a vector and the image of another under the structure read in the chart
  (`TauCeti.SmoothTwoForm.associatedBilinFormInChartAt_apply_eq_inChartAt`). It is continuous
  wherever the structures in the chart are
  (`TauCeti.SmoothTwoForm.continuousOn_associatedBilinFormInChartAt`), so tameness of `J` by `ω`
  becomes coercivity of a continuous family of forms on the model space.
* For a map `u` into the chart source, with coordinate expression `v = extChartAt I α ∘ u`, the
  perturbed derivative `du - X_K` in tangent coordinates is `dv` minus the Hamiltonian vector
  fields in the chart (`TauCeti.SmoothTwoForm.continuousLinearMapAt_perturbedMFDeriv_apply`).
  Thus `u` solves the Floer equation if and only if `v` solves
  `∂ₜv - X_{K_t} = J (∂ₛv - X_{K_s})` with the data read in the chart
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp`).
  The two vector fields together form the Hamiltonian one-form `X_K = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}`
  read in the chart (`TauCeti.SmoothTwoForm.hamiltonianOneFormInChartAt`), the one-form of this
  coordinate equation.
* `TauCeti.Floer.transportedAlmostComplexInChartAt` and
  `TauCeti.SmoothTwoForm.transportedHamiltonianOneFormInChartAt` transport chart data along
  linear equivalences on parameters and model spaces and complex identification on the domain, with
  shared regularity (`contDiffOn_transportedAlmostComplexInChartAt`,
  `contDiffOn_transportedHamiltonianOneFormInChartAt`) and equation equivalence
  (`transported_floerEquation_iff`).

Compactness of solutions with values in one chart, of either kind, is
`TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold`, and the mean-value inequality in a chart
of the atlas is `TauCeti.Geometry.Symplectic.Floer.Compactness.MeanValue`.

## Symplectic charts

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `φ : M → V` be a map into a vector space with a constant symplectic
form `ω₀` which pulls `ω₀` back to `ω` at a point `x`:

`ω_x(v, w) = ω₀(dφ_x v, dφ_x w)`.

A Darboux chart (`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart`) has this property at
every point of its source. This file shows that, at such a point, every ingredient of the
inhomogeneous Floer equation `(du - X_K)^{0,1} = 0` on the manifold is carried by `dφ_x` to the
corresponding ingredient of the Floer equation on `(V, ω₀)` for the coordinate expressions
`K'(z, y)` of the Hamiltonians, with `K(z, ·) = K'(z, ·) ∘ φ` near `x`. So solutions of the
Floer equation in `M` whose image stays in the chart are, read in the chart, solutions of the
Floer equation of a symplectic vector space, with the same energy density. This is how the
analysis of `TauCeti.Geometry.Symplectic.Floer`, carried out for a symplectic vector space target,
applies to a manifold target.

The pointwise symplectic linear algebra of such a map is in
`TauCeti.Geometry.Symplectic.Manifold.TwoForm` and
`TauCeti.Geometry.Symplectic.Hamiltonian.Manifold`: `dφ_x` is injective
(`TauCeti.SmoothTwoForm.IsNondegenerate.injective_mvfderiv`), and if it is also surjective it
carries the Hamiltonian vector field of `g ∘ φ` at `x` to the Hamiltonian vector field of `g` for
`ω₀` at `φ x` (`TauCeti.SmoothTwoForm.IsNondegenerate.mvfderiv_hamiltonianVectorField_comp`) and a
structure `J` tamed by `ω_x` to a structure tamed by `ω₀`
(`TauCeti.SmoothTwoForm.IsNondegenerate.tames_of_isComplexLinearMap_mvfderiv`). This file applies
them to the Floer equation.

* For `u : ℝ × ℝ → M` with `u z = x`, the perturbed derivative `d(φ ∘ u) - X_{K'}` of the coordinate
  map is `dφ_x ∘ (du - X_K)` (`TauCeti.SmoothTwoForm.IsNondegenerate.perturbedFDeriv_comp`), and
  the Floer energy densities agree
  (`TauCeti.SmoothTwoForm.IsNondegenerate.floerEnergyDensity_comp`).
* If `dφ_x ∘ J = J' ∘ dφ_x`, that is, `J'` is the structure `J` read in the chart, then `φ ∘ u`
  solves the coordinate Floer equation for `J'` at `z` exactly when `u` solves the Floer equation
  for `J` (`TauCeti.SmoothTwoForm.IsNondegenerate.isComplexLinearMap_perturbedFDeriv_comp_iff`).

All statements are pointwise and need differentiability only at the point; the chart is any map
with the pullback property there, not necessarily a chart of the manifold structure.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 8.1
  (the inhomogeneous Cauchy–Riemann equation and its energy).
-/

public section

noncomputable section

section

open Bundle ContinuousLinearMap Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M]

namespace Floer

/-- The almost complex structures `J(z, x)` on the tangent spaces of `M`, read in the chart at
`α`: at `(z, y)`, the structure `J(z, x)` at the point `x = (extChartAt I α).symm y` with chart
coordinate `y`, written in the tangent coordinates of the chart at `α`. Outside the chart target
the value is junk. The parameter `z` ranges over any type `P`, such as the domain `ℝ × ℝ` of the
Floer equation.

This is the coordinate expression `ContMDiffAlmostComplexStructureFamily.inChart` for the unbundled
families of structures in which the manifold Floer equation `SmoothTwoForm.perturbedMFDeriv` is
stated (`TauCeti.Floer.almostComplexInChartAt_eq_inChart`). -/
def almostComplexInChartAt (I : ModelWithCorners ℝ E H) [IsManifold I (⊤ : ℕ∞) M] (α : M)
    {P : Type*} (J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)) (p : P × E) :
    E →L[ℝ] E :=
  inCoordinates E (TangentSpace I) E (TangentSpace I) α ((extChartAt I α).symm p.2) α
    ((extChartAt I α).symm p.2)
    (J p.1 ((extChartAt I α).symm p.2)).toLinearMap.toContinuousLinearMap

variable {α : M} {P : Type*} {J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)}

/-- At a chart coordinate `y`, the structure in the chart is the structure at
`x = (extChartAt I α).symm y` conjugated by the tangent coordinates of the chart. -/
theorem almostComplexInChartAt_apply (z : P) (y v : E) :
    almostComplexInChartAt I α J (z, y) v =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ ((extChartAt I α).symm y)
        (J z ((extChartAt I α).symm y)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) v)) := by
  rw [almostComplexInChartAt, inCoordinates, comp_apply, comp_apply,
    LinearMap.coe_toContinuousLinearMap']

/-- On the chart target, the structure in the chart squares to `-1`. -/
theorem almostComplexInChartAt_apply_apply {y : E} (hy : y ∈ (extChartAt I α).target)
    (z : P) (v : E) :
    almostComplexInChartAt I α J (z, y) (almostComplexInChartAt I α J (z, y) v) = -v := by
  have hx : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hy
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

/-- For a family of smooth structures `J p`, the structure in the chart at `(p, y)` is `J p` read
in the chart at `α`. For a domain-independent structure (a constant family) it is therefore smooth
on the chart target (`SmoothAlmostComplexStructure.contDiffOn_inChart`). -/
@[simp]
theorem almostComplexInChartAt_almostComplexStructureAt (J : P → SmoothAlmostComplexStructure I M)
    (α : M) (p : P × E) :
    almostComplexInChartAt I α (fun z ↦ (J z).almostComplexStructureAt) p =
      (J p.1).inChart α p.2 := by
  rw [almostComplexInChartAt, SmoothAlmostComplexStructure.inChart_def]
  congr 1
  ext v
  rw [LinearMap.coe_toContinuousLinearMap']
  exact (J p.1).almostComplexStructureAt_apply _ v

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] in
/-- The inverse-chart pullback map `q ↦ (q.1, (q.2.1, (extChartAt I α).symm q.2.2))` is
continuous where `q.2.2 ∈ (extChartAt I α).target`. -/
theorem continuousOn_prod_extChartAt_symm {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    (α : M) :
    ContinuousOn (fun q : P × (Q × E) ↦ (q.1, (q.2.1, (extChartAt I α).symm q.2.2)))
      {q | q.2.2 ∈ (extChartAt I α).target} :=
  continuousOn_fst.prodMk ((continuous_fst.comp continuous_snd).continuousOn.prodMk
    ((continuousOn_extChartAt_symm α).comp (continuous_snd.comp continuous_snd).continuousOn
      fun _ hq ↦ hq))

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] in
/-- Lifting an open set `W ⊆ P × (Q × M)` through the chart at `α` yields an open subset of
`P × (Q × E)`. -/
theorem isOpen_preimage_prod_extChartAt_symm [I.Boundaryless] {P Q : Type*} [TopologicalSpace P]
    [TopologicalSpace Q] (α : M) {W : Set (P × (Q × M))} (hW : IsOpen W) :
    IsOpen {q : P × (Q × E) |
      q.2.2 ∈ (extChartAt I α).target ∧ (q.1, (q.2.1, (extChartAt I α).symm q.2.2)) ∈ W} :=
  (continuousOn_prod_extChartAt_symm (I := I) α).isOpen_inter_preimage
    ((isOpen_extChartAt_target α).preimage (continuous_snd.comp continuous_snd)) hW

omit [FiniteDimensional ℝ E] in
/-- The inverse-chart pullback map `q ↦ (q.1, (q.2.1, (extChartAt I α).symm q.2.2))` is `C^n` on
`{q | q.2.2 ∈ (extChartAt I α).target}` for `n ≤ ⊤`. -/
theorem contMDiffOn_prod_extChartAt_symm {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] {n : WithTop ℕ∞} (hn : n ≤ (⊤ : ℕ∞)) (α : M) :
    ContMDiffOn 𝓘(ℝ, P × (Q × E)) (𝓘(ℝ, P).prod (𝓘(ℝ, Q).prod I)) n
      (fun q : P × (Q × E) ↦ (q.1, (q.2.1, (extChartAt I α).symm q.2.2)))
      {q | q.2.2 ∈ (extChartAt I α).target} := by
  have heq : (extChartAt (𝓘(ℝ, P).prod (𝓘(ℝ, Q).prod I)) ((0 : P), ((0 : Q), α))).symm =
      fun q : P × (Q × E) ↦ (q.1, (q.2.1, (extChartAt I α).symm q.2.2)) := by
    funext q
    rw [extChartAt_prod_symm_apply, extChartAt_prod_symm_apply]
    simp
  rw [← heq]
  refine ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, P).prod (𝓘(ℝ, Q).prod I))
    ((0 : P), ((0 : Q), α))).of_le hn).mono fun q (hq : q.2.2 ∈ (extChartAt I α).target) ↦ ?_
  simpa only [extChartAt_prod_target, extChartAt_model_space_eq_id, PartialEquiv.refl_target,
    mem_prod, mem_univ, true_and] using hq

/-- **Chart continuity of a parametrized family of almost complex structures.** If `J` is jointly
continuous on a set `W ⊆ P × ((ℝ × ℝ) × M)` as a map into the tangent endomorphism bundle for a
topological parameter space `P`, then its coordinate expression in the chart at `α` is jointly
continuous on the preimage of `W` in `P × ((ℝ × ℝ) × (extChartAt I α).target)`. -/
theorem continuousOn_almostComplexInChartAt {P : Type*} [TopologicalSpace P] (α : M)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (P × ((ℝ × ℝ) × M))}
    (hJ : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
      (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W) :
    ContinuousOn (fun q : P × ((ℝ × ℝ) × E) ↦ almostComplexInChartAt I α (J q.1) q.2)
      {q | q.2.2 ∈ (extChartAt I α).target ∧ (q.1, (q.2.1, (extChartAt I α).symm q.2.2)) ∈ W} := by
  let e := trivializationAt E (TangentSpace I) α
  let eh := trivializationAt (E →L[ℝ] E)
    (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) α
  have hG : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      inCoordinates E (TangentSpace I) E (TangentSpace I) α q.2.2 α q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap)
      (W ∩ {q | q.2.2 ∈ e.baseSet}) :=
    continuous_snd.comp_continuousOn (eh.continuousOn_toFun.comp (hJ.mono inter_subset_left)
      fun _ hq ↦ eh.mem_source.2 ⟨hq.2, hq.2⟩)
  refine hG.comp ((continuousOn_prod_extChartAt_symm (I := I) α).mono ?_) ?_
  · exact fun _ hq ↦ hq.1
  · exact fun _ hq ↦ ⟨hq.2, TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hq.1⟩

/-- **Chart regularity of a parametrized family of almost complex structures.** If `J` is jointly
`Cⁿ` on a set `W ⊆ P × ((ℝ × ℝ) × M)` as a map into the tangent endomorphism bundle, then its
coordinate expression in the chart at `α` is jointly `Cⁿ` on the preimage of `W` in
`P × ((ℝ × ℝ) × (extChartAt I α).target)`. -/
theorem contDiffOn_almostComplexInChartAt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : WithTop ℕ∞} (hn : n ≤ (⊤ : ℕ∞)) (α : M)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (P × ((ℝ × ℝ) × M))}
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W) :
    ContDiffOn ℝ n (fun q : P × ((ℝ × ℝ) × E) ↦ almostComplexInChartAt I α (J q.1) q.2)
      {q | q.2.2 ∈ (extChartAt I α).target ∧ (q.1, (q.2.1, (extChartAt I α).symm q.2.2)) ∈ W} := by
  have : ContMDiffVectorBundle n (E →L[ℝ] E)
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) I :=
    ContMDiffVectorBundle.of_le (B := M) (n := (⊤ : ℕ∞)) hn
  let e := trivializationAt E (TangentSpace I) α
  let eh := trivializationAt (E →L[ℝ] E)
    (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) α
  have hG : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, E →L[ℝ] E) n
      (fun q : P × ((ℝ × ℝ) × M) ↦
        inCoordinates E (TangentSpace I) E (TangentSpace I) α q.2.2 α q.2.2
          (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap)
      (W ∩ {q | q.2.2 ∈ e.baseSet}) := by
    have h := (eh.contMDiffOn_iff (IM := 𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (n := n)
      (f := fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap)
      (s := W ∩ {q | q.2.2 ∈ e.baseSet})
      (fun q hq ↦ eh.mem_source.2 ⟨hq.2, hq.2⟩)).1 (hJ.mono inter_subset_left)
    exact h.2
  refine contMDiffOn_iff_contDiffOn.1 (hG.comp ((contMDiffOn_prod_extChartAt_symm hn α).mono ?_) ?_)
  · exact fun _ hq ↦ hq.1
  · exact fun _ hq ↦ ⟨hq.2, TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hq.1⟩

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

/-- The bilinear forms `ω(·, J(z, x) ·)` of the structures `J(z, x)`, read in the chart at `α`: at
`(z, y)`, the form at the point `x = (extChartAt I α).symm y` with both arguments in the tangent
coordinates of the chart at `α` (`associatedBilinFormInChartAt_apply`). The structures are tamed
by `ω` at `x` exactly when this form is positive on nonzero vectors. It is continuous wherever the
structures in the chart are (`continuousOn_associatedBilinFormInChartAt`). Outside the chart target
the value is junk. -/
def associatedBilinFormInChartAt (ω : SmoothTwoForm I M) (α : M) {P : Type*}
    (J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)) (p : P × E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ((compL ℝ E E ℝ).flip (Floer.almostComplexInChartAt I α J p)).comp
    (ContinuousAlternatingMap.flatL ℝ E ℝ (RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α p.2))

/-- The form `ω(·, J ·)` in the chart evaluates the coordinate expression of `ω` on the first
vector and the image of the second under the structure read in the chart. -/
theorem associatedBilinFormInChartAt_apply_eq_inChartAt (ω : SmoothTwoForm I M) {P : Type*}
    (J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)) (p : P × E)
    (a b : E) :
    ω.associatedBilinFormInChartAt α J p a b =
      RoughForm.inChartAt (ω : RoughForm I M ℝ 2) α p.2
        ![a, Floer.almostComplexInChartAt I α J p b] := by
  simp only [associatedBilinFormInChartAt, comp_apply, flip_apply, compL_apply,
    ContinuousAlternatingMap.flatL_apply_apply]

/-- At a chart coordinate `y`, the form `ω(·, J ·)` in the chart evaluates `ω` at
`x = (extChartAt I α).symm y` on the tangent vectors with chart coordinates `a` and `b`, the
second one rotated by `J(z, x)`. -/
theorem associatedBilinFormInChartAt_apply (ω : SmoothTwoForm I M) {P : Type*}
    (J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)) (z : P) {y : E}
    (hy : y ∈ (extChartAt I α).target) (a b : E) :
    ω.associatedBilinFormInChartAt α J (z, y) a b =
      SmoothBundleForm.eval₂ ω ((extChartAt I α).symm y)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) a)
        (J z ((extChartAt I α).symm y)
          ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) b)) := by
  set T := trivializationAt E (TangentSpace I) α
  have hx : (extChartAt I α).symm y ∈ T.baseSet :=
    TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hy
  rw [associatedBilinFormInChartAt_apply_eq_inChartAt]
  -- The coordinate expression of `ω` feeds it the vectors with the given tangent coordinates.
  have hS := TangentBundle.symmL_trivializationAt (I := I) (𝕜 := ℝ) (x₀ := α)
    (by simpa only [extChartAt_source] using (extChartAt I α).map_target hy)
  rw [(extChartAt I α).right_inv hy] at hS
  rw [RoughForm.inChartAt_apply, SmoothBundleForm.eval₂_apply, ← hS]
  congr 1
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [extChartAt_coe_symm, Function.comp_apply]
    -- `T` abbreviates `trivializationAt E (TangentSpace I) α`, which an instance argument of
    -- `symmL` also mentions, so it cannot be rewritten; `rfl` unfolds the local definition.
    rfl
  · exact (congrArg (T.symmL ℝ ((extChartAt I α).symm y))
      (Floer.almostComplexInChartAt_apply z y b)).trans
      (Trivialization.symmL_continuousLinearMapAt _ hx _)

/-- At the chart image of a point `x` of the chart source, the form `ω(·, J ·)` in the chart,
evaluated on the chart coordinates of tangent vectors `v` and `w` at `x`, is `ω_x(v, J(z, x) w)`. -/
theorem associatedBilinFormInChartAt_extChartAt (ω : SmoothTwoForm I M) {P : Type*}
    (J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)) (z : P) {x : M}
    (hx : x ∈ (extChartAt I α).source) (v w : TangentSpace I x) :
    ω.associatedBilinFormInChartAt α J (z, extChartAt I α x)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x w) =
      SmoothBundleForm.eval₂ ω x v (J z x w) := by
  have hxT : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    TangentBundle.mem_trivializationAt_baseSet_of_mem_extChartAt_source hx
  have h := ω.associatedBilinFormInChartAt_apply J z ((extChartAt I α).map_source hx)
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)
    ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x w)
  rwa [(extChartAt I α).left_inv hx, Trivialization.symmL_continuousLinearMapAt _ hxT,
    Trivialization.symmL_continuousLinearMapAt _ hxT] at h

/-- The form `ω(·, J ·)` in the chart is continuous on every set of pairs `(z, y)` with `y` in the
chart target on which the structures in the chart are continuous. -/
theorem continuousOn_associatedBilinFormInChartAt {ω : SmoothTwoForm I M} {P : Type*}
    [TopologicalSpace P] {J : P → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {S : Set (P × E)}
    (hS : ∀ p ∈ S, p.2 ∈ (extChartAt I α).target)
    (hJ : ContinuousOn (Floer.almostComplexInChartAt I α J) S) :
    ContinuousOn (ω.associatedBilinFormInChartAt α J) S :=
  ((compL ℝ E E ℝ).flip.continuous.comp_continuousOn hJ).clm_comp
    ((ContinuousAlternatingMap.flatL ℝ E ℝ).continuous.comp_continuousOn
      ((ω.isSmoothForm.continuousOn_inChartAt α).comp continuousOn_snd hS))

/-- The Hamiltonian one-form `X_K = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}` of a perturbation
`K = K_s ds + K_t dt`, read in the chart at `α`: at `(z, y)` it sends a tangent vector `(a, b)` of
the domain to `a X_{K_s} + b X_{K_t}`, with the Hamiltonian vector fields read in the chart. This is
the one-form of the coordinate Floer equation solved by the coordinate expressions of solutions
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp`). -/
def hamiltonianOneFormInChartAt (ω : SmoothTwoForm I M) (α : M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (p : (ℝ × ℝ) × E) : ℝ × ℝ →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorFieldInChartAt α Ks p) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorFieldInChartAt α Kt p)

omit [FiniteDimensional ℝ E] in
theorem hamiltonianOneFormInChartAt_apply (ω : SmoothTwoForm I M) (α : M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (p : (ℝ × ℝ) × E) (v : ℝ × ℝ) :
    ω.hamiltonianOneFormInChartAt α Ks Kt p v =
      v.1 • ω.hamiltonianVectorFieldInChartAt α Ks p +
        v.2 • ω.hamiltonianVectorFieldInChartAt α Kt p :=
  (rfl)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem hamiltonianOneFormInChartAt_stdComplexLineReal (ω : SmoothTwoForm I M) (α : M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (p : (ℝ × ℝ) × E) :
    ω.hamiltonianOneFormInChartAt α Ks Kt p stdComplexLineReal =
      ω.hamiltonianVectorFieldInChartAt α Ks p := by
  simp [hamiltonianOneFormInChartAt_apply]

omit [FiniteDimensional ℝ E] in
@[simp]
theorem hamiltonianOneFormInChartAt_stdComplexLineImag (ω : SmoothTwoForm I M) (α : M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (p : (ℝ × ℝ) × E) :
    ω.hamiltonianOneFormInChartAt α Ks Kt p stdComplexLineImag =
      ω.hamiltonianVectorFieldInChartAt α Kt p := by
  simp [hamiltonianOneFormInChartAt_apply]

omit [FiniteDimensional ℝ E] in
/-- The Hamiltonian one-form in a chart is as regular as the two Hamiltonian vector fields. -/
theorem contDiffOn_hamiltonianOneFormInChartAt {n : WithTop ℕ∞} {W : Set ((ℝ × ℝ) × E)}
    (hXs : ContDiffOn ℝ n (ω.hamiltonianVectorFieldInChartAt α Ks) W)
    (hXt : ContDiffOn ℝ n (ω.hamiltonianVectorFieldInChartAt α Kt) W) :
    ContDiffOn ℝ n (ω.hamiltonianOneFormInChartAt α Ks Kt) W :=
  (contDiffOn_const.smulRight hXs).add (contDiffOn_const.smulRight hXt)

omit [FiniteDimensional ℝ E] in
/-- **Joint regularity of a parametrized Hamiltonian one-form in a chart.** If the coordinate
Hamiltonian vector fields of `Ks, Kt` are jointly `C^n` on a set `W ⊆ P × ((ℝ × ℝ) × E)`, then so
is `hamiltonianOneFormInChartAt`. -/
theorem contDiffOn_hamiltonianOneFormInChartAt_param {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {n : WithTop ℕ∞} {Ks Kt : P → ℝ × ℝ → M → ℝ}
    {W : Set (P × ((ℝ × ℝ) × E))}
    (hXs : ContDiffOn ℝ n (fun q : P × ((ℝ × ℝ) × E) ↦
      ω.hamiltonianVectorFieldInChartAt α (Ks q.1) q.2) W)
    (hXt : ContDiffOn ℝ n (fun q : P × ((ℝ × ℝ) × E) ↦
      ω.hamiltonianVectorFieldInChartAt α (Kt q.1) q.2) W) :
    ContDiffOn ℝ n (fun q : P × ((ℝ × ℝ) × E) ↦
      ω.hamiltonianOneFormInChartAt α (Ks q.1) (Kt q.1) q.2) W :=
  (contDiffOn_const.smulRight hXs).add (contDiffOn_const.smulRight hXt)

omit [FiniteDimensional ℝ E] in
/-- **Chart continuity of a parametrized family of Hamiltonian vector fields.** If the Hamiltonian
vector fields of `K` form a jointly continuous map into `TangentBundle I M` on
`W ⊆ P × ((ℝ × ℝ) × M)` for a topological parameter space `P`, then their coordinate expressions in
the chart at `α` are jointly continuous on the preimage of `W` in
`P × ((ℝ × ℝ) × (extChartAt I α).target)`. -/
theorem continuousOn_hamiltonianVectorFieldInChartAt {P : Type*} [TopologicalSpace P]
    (ω : SmoothTwoForm I M) (α : M) {K : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    (hX : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      (⟨q.2.2, ω.hamiltonianVectorField (K q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W) :
    ContinuousOn (fun q : P × ((ℝ × ℝ) × E) ↦ ω.hamiltonianVectorFieldInChartAt α (K q.1) q.2)
      {q | q.2.2 ∈ (extChartAt I α).target ∧ (q.1, (q.2.1, (extChartAt I α).symm q.2.2)) ∈ W} := by
  let e := trivializationAt E (TangentSpace I) α
  have hG : ContinuousOn (fun q : P × ((ℝ × ℝ) × M) ↦
      e.continuousLinearMapAt ℝ q.2.2 (ω.hamiltonianVectorField (K q.1 q.2.1) q.2.2))
      (W ∩ {q | q.2.2 ∈ e.baseSet}) :=
    (continuous_snd.comp_continuousOn (e.continuousOn_toFun.comp (hX.mono inter_subset_left)
      fun _ hq ↦ e.mem_source.2 hq.2)).congr fun _ hq ↦
        e.continuousLinearMapAt_apply_of_mem (R := ℝ) hq.2 _
  refine hG.comp
    ((Floer.continuousOn_prod_extChartAt_symm (I := I) (P := P) (Q := ℝ × ℝ) α).mono ?_) ?_
  · exact fun _ hq ↦ hq.1
  · exact fun _ hq ↦ ⟨hq.2, TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hq.1⟩

omit [FiniteDimensional ℝ E] in
/-- **Chart regularity of a parametrized family of Hamiltonian vector fields.** If the Hamiltonian
vector fields of `K` form a jointly `Cⁿ` map into `TangentBundle I M` on `W ⊆ P × ((ℝ × ℝ) × M)`,
then their coordinate expressions in the chart at `α` are jointly `Cⁿ` on the preimage of `W` in
`P × ((ℝ × ℝ) × (extChartAt I α).target)`. -/
theorem contDiffOn_hamiltonianVectorFieldInChartAt {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {n : WithTop ℕ∞} (hn : n ≤ (⊤ : ℕ∞)) (ω : SmoothTwoForm I M) (α : M)
    {K : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    (hX : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) I.tangent n
      (fun q : P × ((ℝ × ℝ) × M) ↦
        (⟨q.2.2, ω.hamiltonianVectorField (K q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W) :
    ContDiffOn ℝ n (fun q : P × ((ℝ × ℝ) × E) ↦ ω.hamiltonianVectorFieldInChartAt α (K q.1) q.2)
      {q | q.2.2 ∈ (extChartAt I α).target ∧ (q.1, (q.2.1, (extChartAt I α).symm q.2.2)) ∈ W} := by
  have : ContMDiffVectorBundle n E (TangentSpace I) I :=
    ContMDiffVectorBundle.of_le (B := M) (n := (⊤ : ℕ∞)) hn
  let e := trivializationAt E (TangentSpace I) α
  have hG : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ, E) n
      (fun q : P × ((ℝ × ℝ) × M) ↦
        e.continuousLinearMapAt ℝ q.2.2 (ω.hamiltonianVectorField (K q.1 q.2.1) q.2.2))
      (W ∩ {q | q.2.2 ∈ e.baseSet}) := by
    have h := (e.contMDiffOn_iff (IM := 𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (n := n)
      (f := fun q : P × ((ℝ × ℝ) × M) ↦
        (⟨q.2.2, ω.hamiltonianVectorField (K q.1 q.2.1) q.2.2⟩ : TangentBundle I M))
      (s := W ∩ {q | q.2.2 ∈ e.baseSet})
      (fun q hq ↦ e.mem_source.2 hq.2)).1 (hX.mono inter_subset_left)
    exact h.2.congr fun q hq ↦ e.continuousLinearMapAt_apply_of_mem (R := ℝ) hq.2 _
  refine contMDiffOn_iff_contDiffOn.1 (hG.comp
    ((Floer.contMDiffOn_prod_extChartAt_symm (I := I) (P := P) (Q := ℝ × ℝ) hn α).mono ?_) ?_)
  · exact fun _ hq ↦ hq.1
  · exact fun _ hq ↦ ⟨hq.2, TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hq.1⟩

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
    (extChartAt I α).left_inv hz, hu.continuousAt.fderiv_extChartAt_comp_apply hz,
    ← TangentBundle.continuousLinearMapAt_trivializationAt (by rwa [← extChartAt_source I]),
    perturbedMFDeriv_apply, map_sub, map_sub, map_smul, map_smul]
  -- The two sides differ only in the identification of `TangentSpace 𝓘(ℝ, E)` with `E`.
  rfl

/-- **The Floer equation in a chart (equivalence).** For a map `u` differentiable at `z` with
`u z` in the source of the chart at `α`, `u` solves the intrinsic Floer equation
`(du - X_K)^{0,1} = 0` at `z` if and only if its coordinate expression `v = extChartAt I α ∘ u`
solves `∂ₜv - X_{K_t} = J (∂ₛv - X_{K_s})` at `z`, where `J` and the Hamiltonian vector fields
are read in the chart. -/
theorem isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp (ω : SmoothTwoForm I M)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hz : u z ∈ (extChartAt I α).source) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap ↔
      fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineImag -
          ω.hamiltonianVectorFieldInChartAt α Kt (z, extChartAt I α (u z)) =
        Floer.almostComplexInChartAt I α J (z, extChartAt I α (u z))
          (fderiv ℝ (extChartAt I α ∘ u) z stdComplexLineReal -
            ω.hamiltonianVectorFieldInChartAt α Ks (z, extChartAt I α (u z))) := by
  set T := trivializationAt E (TangentSpace I) α
  have hb : u z ∈ T.baseSet :=
    TangentBundle.mem_trivializationAt_baseSet_of_mem_extChartAt_source hz
  have hre := ω.continuousLinearMapAt_perturbedMFDeriv_apply (Ks := Ks) (Kt := Kt) hu hz
    stdComplexLineReal
  have him := ω.continuousLinearMapAt_perturbedMFDeriv_apply (Ks := Ks) (Kt := Kt) hu hz
    stdComplexLineImag
  simp only [stdComplexLineReal_fst, stdComplexLineReal_snd, stdComplexLineImag_fst,
    stdComplexLineImag_snd, zero_smul, one_smul, sub_zero] at hre him
  rw [← hre, ← him, Floer.almostComplexInChartAt_apply, (extChartAt I α).left_inv hz,
    Trivialization.symmL_continuousLinearMapAt _ hb, isComplexLinearMap_stdComplexLine_iff]
  simp only [ContinuousLinearMap.coe_coe]
  rw [← T.coe_continuousLinearEquivAt_eq hb]
  exact (T.continuousLinearEquivAt ℝ (u z) hb).injective.eq_iff.symm

omit [FiniteDimensional ℝ E] in
/-- **Continuity of a Hamiltonian vector field from its chart readings.** On a boundaryless
manifold, let the Hamiltonian vector field of a family of Hamiltonians `K(z)`, read in the chart at
every point `α`, be continuous on `U × (extChartAt I α).target` for an open set `U` of the domain.
Then `(z, x) ↦ X_{K(z)}(x)` is continuous on `U × M` as a map into the tangent bundle. -/
theorem continuousOn_hamiltonianVectorField_of_continuousOn_inChartAt [I.Boundaryless]
    (ω : SmoothTwoForm I M) {K : ℝ × ℝ → M → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hK : ∀ α, ContinuousOn (ω.hamiltonianVectorFieldInChartAt α K)
      (U ×ˢ (extChartAt I α).target)) :
    ContinuousOn (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (K p.1) p.2⟩ : TangentBundle I M)) (U ×ˢ univ) := by
  rintro ⟨z₀, x₀⟩ ⟨hz₀, -⟩
  refine ContinuousAt.continuousWithinAt <|
    (FiberBundle.continuousAt_totalSpace E _).2 ⟨continuousAt_snd, ?_⟩
  -- Near `(z₀, x₀)`, the fibre coordinate in the trivialization at `x₀` is the vector field read
  -- in the chart at `x₀`.
  have hev : (fun p : (ℝ × ℝ) × M ↦ ω.hamiltonianVectorFieldInChartAt x₀ K
      (p.1, extChartAt I x₀ p.2)) =ᶠ[𝓝 (z₀, x₀)] fun p ↦
      (trivializationAt E (TangentSpace I) x₀ ⟨p.2, ω.hamiltonianVectorField (K p.1) p.2⟩).2 := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) x₀)]
      with p hp
    rw [hamiltonianVectorFieldInChartAt_apply, (extChartAt I x₀).left_inv hp,
      Trivialization.continuousLinearMapAt_apply_of_mem]
    rwa [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
  refine ContinuousAt.congr ?_ hev
  exact ((hK x₀).continuousAt ((hU.prod (isOpen_extChartAt_target x₀)).mem_nhds
    ⟨hz₀, mem_extChartAt_target x₀⟩)).comp
    (continuousAt_fst.prodMk ((continuousAt_extChartAt (I := I) x₀).comp continuousAt_snd))

omit [FiniteDimensional ℝ E] in
/-- **Continuity of the Floer energy density from chart readings.** On a boundaryless manifold, if
`u` is `C¹` on an open set `U` of the domain and the Hamiltonian vector fields of `K_s` and `K_t`,
read in the chart at every point `α`, are continuous on `U × (extChartAt I α).target`, then the
Floer energy density of `u` is continuous on `U`. -/
theorem continuousOn_floerEnergyDensity_of_continuousOn_inChartAt [I.Boundaryless]
    (ω : SmoothTwoForm I M) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hXs : ∀ α, ContinuousOn (ω.hamiltonianVectorFieldInChartAt α Ks)
      (U ×ˢ (extChartAt I α).target))
    (hXt : ∀ α, ContinuousOn (ω.hamiltonianVectorFieldInChartAt α Kt)
      (U ×ˢ (extChartAt I α).target)) :
    ContinuousOn (ω.floerEnergyDensity Ks Kt u) U :=
  ω.continuousOn_floerEnergyDensity hU hu
    (ω.continuousOn_hamiltonianVectorField_of_continuousOn_inChartAt hU hXs)
    (ω.continuousOn_hamiltonianVectorField_of_continuousOn_inChartAt hU hXt)

end SmoothTwoForm

section ChartTransport

variable {P P' E' : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup P'] [NormedSpace ℝ P']
  [NormedAddCommGroup E'] [NormedSpace ℝ E']

namespace Floer

/-- Almost complex structures `J` read in the chart at `α` and transported along linear
equivalences `LP : P ≃L[ℝ] P'` on the parameter space and `L : E ≃L[ℝ] E'` on the model space,
together with `Complex.equivRealProdCLM` on the domain. -/
def transportedAlmostComplexInChartAt (I : ModelWithCorners ℝ E H) [IsManifold I (⊤ : ℕ∞) M]
    (α : M) (LP : P ≃L[ℝ] P') (L : E ≃L[ℝ] E')
    (J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x))
    (p' : P') (q' : ℂ × E') : E' →L[ℝ] E' :=
  L.toContinuousLinearMap.comp
    ((almostComplexInChartAt I α (J (LP.symm p'))
      (Complex.equivRealProdCLM q'.1, L.symm q'.2)).comp L.symm.toContinuousLinearMap)

/-- Evaluating `transportedAlmostComplexInChartAt` conjugates `almostComplexInChartAt` by `L`. -/
theorem transportedAlmostComplexInChartAt_apply (α : M) (LP : P ≃L[ℝ] P') (L : E ≃L[ℝ] E')
    (J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x))
    (p' : P') (q' : ℂ × E') (v : E') :
    transportedAlmostComplexInChartAt I α LP L J p' q' v =
      L (almostComplexInChartAt I α (J (LP.symm p'))
        (Complex.equivRealProdCLM q'.1, L.symm q'.2) (L.symm v)) :=
  (rfl)

/-- On the chart target, `transportedAlmostComplexInChartAt` squares to `-1`. -/
theorem transportedAlmostComplexInChartAt_apply_apply (α : M) (LP : P ≃L[ℝ] P') (L : E ≃L[ℝ] E')
    (J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x))
    (p' : P') {q' : ℂ × E'} (hq' : L.symm q'.2 ∈ (extChartAt I α).target) (v : E') :
    transportedAlmostComplexInChartAt I α LP L J p' q'
        (transportedAlmostComplexInChartAt I α LP L J p' q' v) = -v := by
  simp only [transportedAlmostComplexInChartAt_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [almostComplexInChartAt_apply_apply hq', map_neg, ContinuousLinearEquiv.apply_symm_apply]

/-- Joint `C^n` regularity of `transportedAlmostComplexInChartAt` on the lifted open window
when `J` is jointly `C^n` on `W`. -/
theorem contDiffOn_transportedAlmostComplexInChartAt {n : WithTop ℕ∞} (hn : n ≤ (⊤ : ℕ∞))
    (α : M) (LP : P ≃L[ℝ] P') (L : E ≃L[ℝ] E')
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (P × ((ℝ × ℝ) × M))}
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W) :
    ContDiffOn ℝ n (Function.uncurry (transportedAlmostComplexInChartAt I α LP L J))
      {q : P' × (ℂ × E') | L.symm q.2.2 ∈ (extChartAt I α).target ∧
        (LP.symm q.1, (Complex.equivRealProdCLM q.2.1, (extChartAt I α).symm (L.symm q.2.2))) ∈
          W} := by
  let g : P' × (ℂ × E') → P × ((ℝ × ℝ) × E) :=
    fun q ↦ (LP.symm q.1, (Complex.equivRealProdCLM q.2.1, L.symm q.2.2))
  have hg : ContDiff ℝ n g :=
    (LP.symm.contDiff.comp contDiff_fst).prodMk
      ((Complex.equivRealProdCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)).prodMk
        (L.symm.contDiff.comp (contDiff_snd.comp contDiff_snd)))
  exact contDiffOn_const.clm_comp
    (((contDiffOn_almostComplexInChartAt hn α hJ).comp hg.contDiffOn
      (mapsTo_preimage _ _)).clm_comp contDiffOn_const)

end Floer

namespace SmoothTwoForm

/-- Hamiltonian one-form `X_K` read in the chart at `α` and transported along linear
equivalences `LP : P ≃L[ℝ] P'` and `L : E ≃L[ℝ] E'`, and `Complex.equivRealProdCLM`. -/
def transportedHamiltonianOneFormInChartAt (ω : SmoothTwoForm I M) (α : M)
    (LP : P ≃L[ℝ] P') (L : E ≃L[ℝ] E') (Ks Kt : P → ℝ × ℝ → M → ℝ)
    (p' : P') (q' : ℂ × E') : ℂ →L[ℝ] E' :=
  L.toContinuousLinearMap.comp
    ((ω.hamiltonianOneFormInChartAt α (Ks (LP.symm p')) (Kt (LP.symm p'))
      (Complex.equivRealProdCLM q'.1, L.symm q'.2)).comp
      Complex.equivRealProdCLM.toContinuousLinearMap)

omit [FiniteDimensional ℝ E] in
/-- Evaluating the transported Hamiltonian one-form on `1 : ℂ` gives the transported `s`-component
`L (X_{K_s})`. -/
@[simp]
theorem transportedHamiltonianOneFormInChartAt_one (ω : SmoothTwoForm I M) (α : M)
    (LP : P ≃L[ℝ] P') (L : E ≃L[ℝ] E') (Ks Kt : P → ℝ × ℝ → M → ℝ)
    (p' : P') (q' : ℂ × E') :
    ω.transportedHamiltonianOneFormInChartAt α LP L Ks Kt p' q' 1 =
      L (ω.hamiltonianVectorFieldInChartAt α (Ks (LP.symm p'))
        (Complex.equivRealProdCLM q'.1, L.symm q'.2)) := by
  simp [transportedHamiltonianOneFormInChartAt, hamiltonianOneFormInChartAt_apply]

omit [FiniteDimensional ℝ E] in
/-- Evaluating the transported Hamiltonian one-form on `I : ℂ` gives the transported `t`-component
`L (X_{K_t})`. -/
@[simp]
theorem transportedHamiltonianOneFormInChartAt_I (ω : SmoothTwoForm I M) (α : M)
    (LP : P ≃L[ℝ] P') (L : E ≃L[ℝ] E') (Ks Kt : P → ℝ × ℝ → M → ℝ)
    (p' : P') (q' : ℂ × E') :
    ω.transportedHamiltonianOneFormInChartAt α LP L Ks Kt p' q' Complex.I =
      L (ω.hamiltonianVectorFieldInChartAt α (Kt (LP.symm p'))
        (Complex.equivRealProdCLM q'.1, L.symm q'.2)) := by
  simp [transportedHamiltonianOneFormInChartAt, hamiltonianOneFormInChartAt_apply]

omit [FiniteDimensional ℝ E] in
/-- Joint `C^n` regularity of `transportedHamiltonianOneFormInChartAt` on the lifted open window
when the Hamiltonian vector fields of `Ks, Kt` are jointly `C^n` on `W`. -/
theorem contDiffOn_transportedHamiltonianOneFormInChartAt {n : WithTop ℕ∞} (hn : n ≤ (⊤ : ℕ∞))
    (ω : SmoothTwoForm I M) (α : M) (LP : P ≃L[ℝ] P') (L : E ≃L[ℝ] E')
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    (hXs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) I.tangent n
      (fun q : P × ((ℝ × ℝ) × M) ↦
        (⟨q.2.2, ω.hamiltonianVectorField (Ks q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W)
    (hXt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) I.tangent n
      (fun q : P × ((ℝ × ℝ) × M) ↦
        (⟨q.2.2, ω.hamiltonianVectorField (Kt q.1 q.2.1) q.2.2⟩ : TangentBundle I M)) W) :
    ContDiffOn ℝ n (Function.uncurry (ω.transportedHamiltonianOneFormInChartAt α LP L Ks Kt))
      {q : P' × (ℂ × E') | L.symm q.2.2 ∈ (extChartAt I α).target ∧
        (LP.symm q.1, (Complex.equivRealProdCLM q.2.1, (extChartAt I α).symm (L.symm q.2.2))) ∈
          W} := by
  let g : P' × (ℂ × E') → P × ((ℝ × ℝ) × E) :=
    fun q ↦ (LP.symm q.1, (Complex.equivRealProdCLM q.2.1, L.symm q.2.2))
  have hg : ContDiff ℝ n g :=
    (LP.symm.contDiff.comp contDiff_fst).prodMk
      ((Complex.equivRealProdCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)).prodMk
        (L.symm.contDiff.comp (contDiff_snd.comp contDiff_snd)))
  exact contDiffOn_const.clm_comp
    (((ω.contDiffOn_hamiltonianOneFormInChartAt_param
        (ω.contDiffOn_hamiltonianVectorFieldInChartAt hn α hXs)
        (ω.contDiffOn_hamiltonianVectorFieldInChartAt hn α hXt)).comp hg.contDiffOn
      (mapsTo_preimage _ _)).clm_comp contDiffOn_const)

/-- **Coordinate Floer equation under linear chart transport.** For any map `v : ℝ × ℝ → E`, its
transported coordinate expression `w = fun z ↦ L (v (Complex.equivRealProdCLM z))` satisfies the
transported Floer equation with data `(transportedAlmostComplexInChartAt,
transportedHamiltonianOneFormInChartAt)` at `y` if and only if `v` satisfies the chart Floer
equation at `Complex.equivRealProdCLM y`. -/
theorem transported_floerEquation_iff (ω : SmoothTwoForm I M) (α : M)
    (LP : P ≃L[ℝ] P') (L : E ≃L[ℝ] E')
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} (p : P) (v : ℝ × ℝ → E) (y : ℂ) :
    let w : ℂ → E' := fun z ↦ L (v (Complex.equivRealProdCLM z))
    fderiv ℝ w y Complex.I -
        ω.transportedHamiltonianOneFormInChartAt α LP L Ks Kt (LP p) (y, w y) Complex.I =
      Floer.transportedAlmostComplexInChartAt I α LP L J (LP p) (y, w y)
        (fderiv ℝ w y 1 -
          ω.transportedHamiltonianOneFormInChartAt α LP L Ks Kt (LP p) (y, w y) 1) ↔
    fderiv ℝ v (Complex.equivRealProdCLM y) stdComplexLineImag -
        ω.hamiltonianVectorFieldInChartAt α (Kt p)
          (Complex.equivRealProdCLM y, v (Complex.equivRealProdCLM y)) =
      Floer.almostComplexInChartAt I α (J p)
          (Complex.equivRealProdCLM y, v (Complex.equivRealProdCLM y))
        (fderiv ℝ v (Complex.equivRealProdCLM y) stdComplexLineReal -
          ω.hamiltonianVectorFieldInChartAt α (Ks p)
            (Complex.equivRealProdCLM y, v (Complex.equivRealProdCLM y))) := by
  dsimp only
  have h1 : fderiv ℝ (fun z ↦ L (v (Complex.equivRealProdCLM z))) y 1 =
      L (fderiv ℝ v (Complex.equivRealProdCLM y) stdComplexLineReal) := by
    have hcomp := congrArg (fun f : ℂ →L[ℝ] E' ↦ f 1)
      (L.comp_fderiv (f := v ∘ Complex.equivRealProdCLM) (x := y))
    exact hcomp.trans (congrArg L (fderiv_comp_equivRealProdCLM_one v y))
  have hI : fderiv ℝ (fun z ↦ L (v (Complex.equivRealProdCLM z))) y Complex.I =
      L (fderiv ℝ v (Complex.equivRealProdCLM y) stdComplexLineImag) := by
    have hcomp := congrArg (fun f : ℂ →L[ℝ] E' ↦ f Complex.I)
      (L.comp_fderiv (f := v ∘ Complex.equivRealProdCLM) (x := y))
    exact hcomp.trans (congrArg L (fderiv_comp_equivRealProdCLM_I v y))
  simp only [h1, hI, transportedHamiltonianOneFormInChartAt_one,
    transportedHamiltonianOneFormInChartAt_I, Floer.transportedAlmostComplexInChartAt_apply,
    ContinuousLinearEquiv.symm_apply_apply, ← map_sub]
  exact L.injective.eq_iff

end SmoothTwoForm

end ChartTransport

end TauCeti

end

section

open Function
open scoped Manifold Topology

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {φ : M → V}
  {Ks Kt : ℝ × ℝ → M → ℝ} {Ks' Kt' : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → M} {z : ℝ × ℝ}

/-- **The perturbed derivative in a symplectic chart.** Let `φ` be differentiable at `u z` with
surjective differential there, pulling the symplectic form `ω₀` back to the nondegenerate form `ω`
at `u z`, and let the Hamiltonians `Ks z`, `Kt z` agree near `u z` with `Ks' z ∘ φ`, `Kt' z ∘ φ`
for functions `Ks' z`, `Kt' z` differentiable at `φ (u z)`. If `u` is differentiable at `z`, the
perturbed derivative `d(φ ∘ u) - X_{K'}` of the coordinate map for `ω₀` is the differential of `φ`
applied to the perturbed derivative `du - X_K` of `u` for `ω`. -/
theorem perturbedFDeriv_comp (hω : ω.IsNondegenerate) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hφ : MDifferentiableAt I 𝓘(ℝ, V) φ (u z)) (hsurj : Surjective (mvfderiv I φ (u z)))
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : Ks z =ᶠ[𝓝 (u z)] Ks' z ∘ φ) (hKt : Kt z =ᶠ[𝓝 (u z)] Kt' z ∘ φ)
    (hKs' : DifferentiableAt ℝ (Ks' z) (φ (u z))) (hKt' : DifferentiableAt ℝ (Kt' z) (φ (u z))) :
    ω₀.perturbedFDeriv Ks' Kt' (φ ∘ u) z =
      (mvfderiv I φ (u z)).comp (ω.perturbedMFDeriv Ks Kt u z) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hd : fderiv ℝ (φ ∘ u) z v = mvfderiv I φ (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z v) :=
    (mvfderiv_eq_fderiv_apply (φ ∘ u) z v).symm.trans (mvfderiv_comp_apply z hφ hu v)
  rw [SymplecticForm.perturbedFDeriv_apply, ContinuousLinearMap.comp_apply, perturbedMFDeriv_apply,
    map_sub, map_sub, map_smul, map_smul, hd, comp_apply, hKs.hamiltonianVectorField_eq,
    hKt.hamiltonianVectorField_eq, hω.mvfderiv_hamiltonianVectorField_comp hφ hsurj hform hKs',
    hω.mvfderiv_hamiltonianVectorField_comp hφ hsurj hform hKt', mvfderiv_apply_eq_mfderiv_apply]

/-- **The energy density in a symplectic chart.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.perturbedFDeriv_comp`, the Floer energy density of the
coordinate map `φ ∘ u` for `ω₀` and the coordinate Hamiltonians is the Floer energy density of `u`
for `ω`. -/
theorem floerEnergyDensity_comp (hω : ω.IsNondegenerate)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hφ : MDifferentiableAt I 𝓘(ℝ, V) φ (u z))
    (hsurj : Surjective (mvfderiv I φ (u z)))
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : Ks z =ᶠ[𝓝 (u z)] Ks' z ∘ φ) (hKt : Kt z =ᶠ[𝓝 (u z)] Kt' z ∘ φ)
    (hKs' : DifferentiableAt ℝ (Ks' z) (φ (u z))) (hKt' : DifferentiableAt ℝ (Kt' z) (φ (u z))) :
    ω₀.floerEnergyDensity Ks' Kt' (φ ∘ u) z = ω.floerEnergyDensity Ks Kt u z := by
  rw [SymplecticForm.floerEnergyDensity_def, floerEnergyDensity_def,
    hω.perturbedFDeriv_comp hu hφ hsurj hform hKs hKt hKs' hKt', ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, hform]

/-- **The Floer equation in a symplectic chart.** Under the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.perturbedFDeriv_comp`, let `J'` be the structure `J` on
`T_(u z) M` read in the chart, `dφ ∘ J = J' ∘ dφ`. Then the coordinate map `φ ∘ u` solves the
Floer equation for `ω₀` and `J'` at `z` exactly when `u` solves the Floer equation for `ω` and
`J`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_iff (hω : ω.IsNondegenerate)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) (hφ : MDifferentiableAt I 𝓘(ℝ, V) φ (u z))
    (hsurj : Surjective (mvfderiv I φ (u z)))
    (hform : ∀ v w : TangentSpace I (u z),
      ω.eval₂ (u z) v w = ω₀ (mvfderiv I φ (u z) v) (mvfderiv I φ (u z) w))
    (hKs : Ks z =ᶠ[𝓝 (u z)] Ks' z ∘ φ) (hKt : Kt z =ᶠ[𝓝 (u z)] Kt' z ∘ φ)
    (hKs' : DifferentiableAt ℝ (Ks' z) (φ (u z))) (hKt' : DifferentiableAt ℝ (Kt' z) (φ (u z)))
    {J : AlmostComplexStructure (TangentSpace I (u z))} {J' : AlmostComplexStructure V}
    (hJ : IsComplexLinearMap J J' (mvfderiv I φ (u z)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J'
        (ω₀.perturbedFDeriv Ks' Kt' (φ ∘ u) z).toLinearMap ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap := by
  rw [hω.perturbedFDeriv_comp hu hφ hsurj hform hKs hKt hKs' hKt']
  refine ⟨fun h ↦ ?_, fun h ↦ hJ.comp h⟩
  -- The differential of `φ` is injective and intertwines `J` with `J'`.
  rw [isComplexLinearMap_stdComplexLine_iff] at h ⊢
  refine hω.injective_mvfderiv hform ?_
  have hJv := LinearMap.congr_fun hJ (ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal)
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_comp] at h hJv ⊢
  exact h.trans hJv.symm

end TauCeti.SmoothTwoForm.IsNondegenerate

end

end
