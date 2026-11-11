/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Straightening
public import TauCeti.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The straightening theorem for vector fields on a manifold

Near a point `x` where a `C^m` vector field `v` on a finite-dimensional boundaryless manifold does
not vanish, some chart of the `C^m` maximal atlas carries `v` to a constant vector field: the
differential of the chart, read in the model vector space, sends `v y` to one fixed nonzero vector
`u` at every point `y` of its domain (`TauCeti.exists_chart_mfderiv_eq_const`). In such a chart the
integral curves of `v` are parallel straight lines traversed with constant velocity `u`.

The field read in the extended chart at `x` is a nonvanishing `C^m` vector field on an open subset
of the model space, so the flat straightening theorem
`TauCeti.exists_openPartialHomeomorph_fderiv_eq_const` produces a change of coordinates there; read
back through the extended chart, it is a chart of the manifold
(`TauCeti.conj_chartAt_mem_maximalAtlas`).

The manifold is `C^n` with `m + 1 ≤ n`, since a vector field read in a chart loses one derivative
of the chart's regularity. Without the boundaryless hypothesis the statement fails: at a boundary
point a chart preserves the boundary, while a field tangent to the boundary at one boundary point
and transverse to it at nearby ones cannot become constant.

## Main results

* `TauCeti.exists_chart_mfderiv_eq_const`: a nonvanishing `C^m` vector field is constant in a
  suitable chart of the `C^m` maximal atlas.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.22 (canonical form near a regular point).
-/

public section

noncomputable section

open Set Filter Topology VectorField
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- **The straightening theorem** [Lee, Thm. 9.22]. Let `v` be a vector field on a `C^n` manifold
with finite-dimensional boundaryless model, `C^m` on a neighbourhood of `x`, with `1 ≤ m`,
`m + 1 ≤ n` and `v x ≠ 0`. Then some chart `e` of the `C^m` maximal atlas whose domain contains `x`
carries `v` to a constant nonzero vector field: the differential of `I ∘ e` sends `v y` to the same
vector `u ≠ 0` at every point `y` of the domain of `e`. -/
theorem exists_chart_mfderiv_eq_const {m : ℕ∞} {n : ℕ∞ω} (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    [IsManifold I 1 M] [IsManifold I n M] {v : (y : M) → TangentSpace I y} {U : Set M} {x : M}
    (hv : ContMDiffOn I I.tangent m (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) U) (hU : U ∈ 𝓝 x)
    (hx : v x ≠ 0) :
    ∃ (e : OpenPartialHomeomorph M H) (u : E), e ∈ IsManifold.maximalAtlas I m M ∧
      x ∈ e.source ∧ u ≠ 0 ∧ ∀ y ∈ e.source, mfderiv I 𝓘(ℝ, E) (I ∘ e) y (v y) = u := by
  have hm1 : (1 : ℕ∞ω) ≤ m := by exact_mod_cast hm
  have : IsManifold I m M := .of_le (le_self_add.trans hmn)
  set e₀ := extChartAt I x with he₀
  -- The field read in the extended chart at `x` is `C^m` near `e₀ x`.
  set w : E → E := fun z ↦ mpullback 𝓘(ℝ, E) I e₀.symm v z
  set S := e₀.target ∩ e₀.symm ⁻¹' interior U
  have hSo : IsOpen S :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
      isOpen_interior
  have hxS : e₀ x ∈ S := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    rw [mem_preimage, he₀, extChartAt_to_inv]
    exact mem_interior_iff_mem_nhds.2 hU
  have hwS : ContDiffOn ℝ m w S :=
    (hv.mono interior_subset).contDiffOn_mpullback_extChartAt_symm hmn
  -- At `e₀ y`, the coordinate field is the image of `v y` under the differential of `e₀`.
  have hwe (y : M) (hy : y ∈ e₀.source) : w (e₀ y) = mfderiv I 𝓘(ℝ, E) e₀ y (v y) :=
    mpullback_extChartAt_symm_apply_eq_mfderiv v hy
  have hwx : w (e₀ x) ≠ 0 := by
    rw [hwe x (mem_extChartAt_source x)]
    exact fun h ↦ hx ((isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)).injective
      (h.trans (map_zero _).symm))
  -- Straighten the coordinate field and read the new coordinates through the chart.
  obtain ⟨φ, hxφ, hφ, hφs, hφw⟩ :=
    exists_openPartialHomeomorph_fderiv_eq_const hm hwS (hSo.mem_nhds hxS) hwx
  have hφA : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) m E := by
    have h := trans_mem_maximalAtlas_of_contDiffAt
      ((contDiffGroupoid m 𝓘(ℝ, E)).id_mem_maximalAtlas) hφ hφs
    rwa [OpenPartialHomeomorph.refl_trans] at h
  set e := (((chartAt H x).transHomeomorph I.toHomeomorph).trans φ).transHomeomorph
    I.toHomeomorph.symm
  have hes (y : M) : y ∈ e.source ↔ y ∈ e₀.source ∧ e₀ y ∈ φ.source := by
    rw [conj_chartAt_source, mem_inter_iff, mem_preimage]
  have heq : I ∘ e = φ ∘ e₀ := comp_conj_chartAt x φ
  refine ⟨e, w (e₀ x), conj_chartAt_mem_maximalAtlas x hφA, (hes x).2
    ⟨mem_extChartAt_source x, hxφ⟩, hwx, fun y hy ↦ ?_⟩
  obtain ⟨hy₀, hyφ⟩ := (hes y).1 hy
  have hφd : DifferentiableAt ℝ φ (e₀ y) :=
    (hφ _ hyφ).differentiableAt (lt_of_lt_of_le zero_lt_one hm1).ne'
  -- The differential of `I ∘ e = φ ∘ e₀` at `y`, by the chain rule.
  have hd : mfderiv I 𝓘(ℝ, E) (I ∘ e) y = (fderiv ℝ φ (e₀ y)).comp (mfderiv I 𝓘(ℝ, E) e₀ y) := by
    rw [heq, mfderiv_comp y hφd.mdifferentiableAt
        (mdifferentiableAt_extChartAt (by rwa [← extChartAt_source (I := I)])),
      mfderiv_eq_fderiv]
    -- The tangent spaces of `E` are `E` by definition, so the remaining casts are identities.
    rfl
  rw [hd]
  exact (congrArg (fderiv ℝ φ (e₀ y)) (hwe y hy₀).symm).trans (hφw _ hyφ)

end TauCeti
