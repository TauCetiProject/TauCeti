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
  (`TauCeti.Floer.almostComplexInChartAt_almostComplexStructureAt`).
* For a nondegenerate `ω` and Hamiltonians `K(z)` which are jointly `C^(n+1)` in `z` and the
  target point, the Hamiltonian vector field in the chart is `C^n` on the chart target
  (`TauCeti.SmoothTwoForm.IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`): it is
  the coordinate expression of the `C^n` section `(z, x) ↦ X_{K(z)}(x)` of the tangent bundle.
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
  So if `u` solves the Floer equation, `v` solves `∂ₜv - X_{K_t} = J (∂ₛv - X_{K_s})` with the
  data read in the chart
  (`TauCeti.SmoothTwoForm.fderiv_extChartAt_comp_stdComplexLineImag_sub`). The two vector fields
  together form the Hamiltonian one-form `X_K = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}` read in the chart
  (`TauCeti.SmoothTwoForm.hamiltonianOneFormInChartAt`), the one-form of this coordinate equation.

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

/-- Reparametrizing a family of structures reparametrizes the family read in the chart. -/
theorem almostComplexInChartAt_comp {Q : Type*} (f : Q → P) (p : Q × E) :
    almostComplexInChartAt I α (fun z ↦ J (f z)) p = almostComplexInChartAt I α J (f p.1, p.2) :=
  (rfl)

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

/-- **The Hamiltonian vector field in a chart is smooth.** For a nondegenerate two-form `ω` and a
family of Hamiltonians `K(z)` which is jointly `C^(n+1)` at every point of `U × M`, for an open set
`U` of the domain, the Hamiltonian vector field of `K` read in the chart at `α` is `C^n` on
`U × (extChartAt I α).target`. With `n = 2` this is the regularity of the data assumed by the
compactness theorems for Floer solutions in a manifold. -/
theorem IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt (hω : ω.IsNondegenerate)
    {U : Set (ℝ × ℝ)} {K : ℝ × ℝ → M → ℝ} {n : ℕ∞}
    (hK : ∀ z ∈ U, ∀ x, ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (n + 1) (Function.uncurry K) (z, x))
    (α : M) :
    ContDiffOn ℝ n (ω.hamiltonianVectorFieldInChartAt α K) (U ×ˢ (extChartAt I α).target) := by
  set T := trivializationAt E (TangentSpace I) α
  set φ := extChartAt I α
  -- The map `(z, y) ↦ (z, φ⁻¹ y)` into `(ℝ × ℝ) × M`.
  set ψ : (ℝ × ℝ) × E → (ℝ × ℝ) × M := fun p ↦ (p.1, φ.symm p.2)
  rintro ⟨z, y⟩ ⟨hz, hy⟩
  have hbase {w : E} (hw : w ∈ φ.target) : φ.symm w ∈ T.baseSet := by
    simpa [T, φ] using (extChartAt I α).map_target hw
  -- The Hamiltonian vector fields form a section of the tangent bundle which is `C^n` at
  -- `(z, φ⁻¹ y)`, so its coordinates in the trivialization at `α` are `C^n` there.
  have hX := hω.contMDiffAt_hamiltonianVectorField_uncurry (n := n) (by exact_mod_cast le_top)
    (hK z hz (φ.symm y))
  have hcoord := ((Bundle.Trivialization.contMDiffAt_iff (e := T)
    (by simpa [T] using hbase hy)).1 hX).2
  have hψ : ContMDiffWithinAt 𝓘(ℝ, (ℝ × ℝ) × E) (𝓘(ℝ, ℝ × ℝ).prod I) n ψ
      (U ×ˢ φ.target) (z, y) :=
    (contDiff_fst.contMDiff _).contMDiffWithinAt.prodMk
      (((contMDiffOn_extChartAt_symm (I := I) (n := n) α _ hy).comp (z, y)
        (contDiff_snd.contMDiff _).contMDiffWithinAt fun _ hp ↦ hp.2))
  refine (contMDiffWithinAt_iff_contDiffWithinAt.1 (hcoord.comp_contMDiffWithinAt (z, y) hψ)).congr
    (fun p hp ↦ ?_) ?_
  · rw [hamiltonianVectorFieldInChartAt_apply]
    exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) T (hbase hp.2) _
  · rw [hamiltonianVectorFieldInChartAt_apply]
    exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) T (hbase hy) _

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
(`TauCeti.SmoothTwoForm.fderiv_extChartAt_comp_stdComplexLineImag_sub`). -/
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
  have hb : u z ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    TangentBundle.mem_trivializationAt_baseSet_of_mem_extChartAt_source hz
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
