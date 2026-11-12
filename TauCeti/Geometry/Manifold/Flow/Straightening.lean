/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Straightening
public import TauCeti.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The straightening theorem for vector fields on a manifold

Near a point `x` where a `C^m` vector field `v` on a finite-dimensional boundaryless manifold does
not vanish, some chart of the `C^m` maximal atlas carries `v` to a constant vector field: the
differential of the chart, read in the model vector space, sends `v y` to one fixed nonzero vector
`u` at every point `y` of its domain (`TauCeti.exists_chart_mfderiv_eq_const`). In such a chart the
integral curves of `v` are parallel straight lines traversed with constant velocity `u`.

The manifold is `C^n` with `m + 1 ≤ n`, since a vector field read in a chart loses one derivative
of the chart's regularity. Without the boundaryless hypothesis the statement fails: at a boundary
point a chart preserves the boundary, while a field tangent to the boundary at one boundary point
and transverse to it at nearby ones cannot become constant.

The same holds for finitely many `C^m` vector fields `V i` whose values at `x` are linearly
independent and whose pairwise Lie brackets vanish near `x`: one chart carries every `V i` to a
constant field `u i`, with the `u i` linearly independent
(`TauCeti.exists_chart_mfderiv_eq_const_of_mlieBracket_eq_zero`); a single nonvanishing field is
the case of a one-element index set. The fields read in the extended chart at `x` are `C^m` vector
fields on an open subset of the model space, and by naturality of the bracket under the inverse
extended chart (`VectorField.lieBracket_mpullback_extChartAt_symm_eventuallyEq_zero`) they have
vanishing flat brackets. So the simultaneous flat straightening theorem
`TauCeti.exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eq_zero` produces a change of
coordinates there; read back through the extended chart, it is a chart of the manifold
(`TauCeti.conj_chartAt_mem_maximalAtlas`).

## Main results

* `TauCeti.exists_chart_mfderiv_eq_const`: a nonvanishing `C^m` vector field is constant in a
  suitable chart of the `C^m` maximal atlas.
* `TauCeti.exists_chart_mfderiv_eq_const_of_mlieBracket_eq_zero`: finitely many pointwise
  independent `C^m` vector fields with vanishing brackets are simultaneously constant in a
  suitable chart of the `C^m` maximal atlas.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 9.22 (canonical form near a regular point) and Theorem 9.46 (canonical
  form for commuting vector fields).
-/

public section

noncomputable section

open Set Filter Topology VectorField
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- **The canonical form for commuting vector fields** [Lee, Thm. 9.46]. Let `V i`, for `i` in a
finite index set, be vector fields on a `C^n` manifold with finite-dimensional boundaryless model,
`C^m` on a neighbourhood of `x`, with `1 ≤ m` and `m + 1 ≤ n`, whose values at `x` are linearly
independent and whose pairwise Lie brackets vanish near `x`. Then some chart `e` of the `C^m`
maximal atlas whose domain contains `x` carries all of them to constant vector fields: the
differential of `I ∘ e` sends `V i y` to the same vector `u i` at every point `y` of the domain of
`e`, and the vectors `u i` are linearly independent. -/
theorem exists_chart_mfderiv_eq_const_of_mlieBracket_eq_zero {ι : Type*} [Finite ι] {m : ℕ∞}
    {n : ℕ∞ω} (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n) [IsManifold I 1 M] [IsManifold I n M]
    {V : ι → (y : M) → TangentSpace I y} {U : Set M} {x : M}
    (hV : ∀ i, ContMDiffOn I I.tangent m (fun y ↦ (⟨y, V i y⟩ : TangentBundle I M)) U)
    (hU : U ∈ 𝓝 x) (hli : LinearIndependent ℝ fun i ↦ V i x)
    (hbr : Pairwise fun i j ↦ ∀ᶠ y in 𝓝 x, mlieBracket I (V i) (V j) y = 0) :
    ∃ (e : OpenPartialHomeomorph M H) (u : ι → E), e ∈ IsManifold.maximalAtlas I m M ∧
      x ∈ e.source ∧ LinearIndependent ℝ u ∧
        ∀ y ∈ e.source, ∀ i, mfderiv I 𝓘(ℝ, E) (I ∘ e) y (V i y) = u i := by
  have hm1 : (1 : ℕ∞ω) ≤ m := by exact_mod_cast hm
  have : IsManifold I m M := .of_le (le_self_add.trans hmn)
  have h2n : (2 : ℕ∞ω) ≤ n := by
    have : (1 : ℕ∞ω) + 1 ≤ (m : ℕ∞ω) + 1 := by gcongr
    exact (one_add_one_eq_two.symm.le.trans this).trans hmn
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact .of_le h2n
  set e₀ := extChartAt I x with he₀
  -- The fields read in the extended chart at `x` are `C^m` near `e₀ x`.
  set w : ι → E → E := fun i z ↦ mpullback 𝓘(ℝ, E) I e₀.symm (V i) z
  set S := e₀.target ∩ e₀.symm ⁻¹' interior U
  have hSo : IsOpen S :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
      isOpen_interior
  have hxS : e₀ x ∈ S := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    rw [mem_preimage, he₀, extChartAt_to_inv]
    exact mem_interior_iff_mem_nhds.2 hU
  have hwS (i : ι) : ContDiffOn ℝ m (w i) S :=
    ((hV i).mono interior_subset).contDiffOn_mpullback_extChartAt_symm hmn
  -- At `e₀ y`, the coordinate fields are the images of the `V i y` under the differential of `e₀`.
  have hwe (i : ι) (y : M) (hy : y ∈ e₀.source) :
      w i (e₀ y) = mfderiv I 𝓘(ℝ, E) e₀ y (V i y) :=
    mpullback_extChartAt_symm_apply_eq_mfderiv (V i) hy
  have hwx (i : ι) : w i (e₀ x) = V i x := by
    rw [hwe i x (mem_extChartAt_source x), he₀, mfderiv_extChartAt_eq_id]
    exact ContinuousLinearMap.id_apply _
  have hli' : LinearIndependent ℝ fun i ↦ w i (e₀ x) := by
    rw [show (fun i ↦ w i (e₀ x)) = fun i ↦ V i x from funext hwx]
    exact hli
  -- The coordinate fields have vanishing brackets near `e₀ x`, by naturality of the bracket.
  have hdiff (k : ι) : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I I.tangent (fun y ↦ (⟨y, V k y⟩ : TangentBundle I M)) y :=
    (eventually_mem_nhds_iff.2 hU).mono fun y hy ↦
      ((hV k).contMDiffAt hy).mdifferentiableAt (lt_of_lt_of_le zero_lt_one hm1).ne'
  have hbr' : Pairwise fun i j ↦ lieBracket ℝ (w i) (w j) =ᶠ[𝓝 (e₀ x)] 0 := fun i j hij ↦
    lieBracket_mpullback_extChartAt_symm_eventuallyEq_zero (hdiff i) (hdiff j) (hbr hij)
  -- Straighten the coordinate fields and read the new coordinates through the chart.
  obtain ⟨φ, hxφ, hφ, hφs, hφw⟩ :=
    exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eq_zero hm hwS
      (hSo.mem_nhds hxS) hli' hbr'
  have hφA : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) m E := by
    have h := trans_mem_maximalAtlas_of_contDiffAt
      ((contDiffGroupoid m 𝓘(ℝ, E)).id_mem_maximalAtlas) hφ hφs
    rwa [OpenPartialHomeomorph.refl_trans] at h
  set e := (((chartAt H x).transHomeomorph I.toHomeomorph).trans φ).transHomeomorph
    I.toHomeomorph.symm
  have hes (y : M) : y ∈ e.source ↔ y ∈ e₀.source ∧ e₀ y ∈ φ.source := by
    rw [conj_chartAt_source, mem_inter_iff, mem_preimage]
  have heq : I ∘ e = φ ∘ e₀ := comp_conj_chartAt x φ
  refine ⟨e, fun i ↦ w i (e₀ x), conj_chartAt_mem_maximalAtlas x hφA, (hes x).2
    ⟨mem_extChartAt_source x, hxφ⟩, hli', fun y hy i ↦ ?_⟩
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
  exact (congrArg (fderiv ℝ φ (e₀ y)) (hwe i y hy₀).symm).trans (hφw _ hyφ i)

/-- **The straightening theorem** [Lee, Thm. 9.22]. Let `v` be a vector field on a `C^n` manifold
with finite-dimensional boundaryless model, `C^m` on a neighbourhood of `x`, with `1 ≤ m`,
`m + 1 ≤ n` and `v x ≠ 0`. Then some chart `e` of the `C^m` maximal atlas whose domain contains `x`
carries `v` to a constant nonzero vector field: the differential of `I ∘ e` sends `v y` to the same
vector `u ≠ 0` at every point `y` of the domain of `e`. This is the case of a single field in
`TauCeti.exists_chart_mfderiv_eq_const_of_mlieBracket_eq_zero`. -/
theorem exists_chart_mfderiv_eq_const {m : ℕ∞} {n : ℕ∞ω} (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    [IsManifold I 1 M] [IsManifold I n M] {v : (y : M) → TangentSpace I y} {U : Set M} {x : M}
    (hv : ContMDiffOn I I.tangent m (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) U) (hU : U ∈ 𝓝 x)
    (hx : v x ≠ 0) :
    ∃ (e : OpenPartialHomeomorph M H) (u : E), e ∈ IsManifold.maximalAtlas I m M ∧
      x ∈ e.source ∧ u ≠ 0 ∧ ∀ y ∈ e.source, mfderiv I 𝓘(ℝ, E) (I ∘ e) y (v y) = u := by
  obtain ⟨e, u, he, hxe, hu, heu⟩ := exists_chart_mfderiv_eq_const_of_mlieBracket_eq_zero hm hmn
    (V := fun _ : Unit ↦ v) (fun _ ↦ hv) hU (linearIndependent_unique_iff.2 hx)
    fun i j h ↦ (h (Subsingleton.elim i j)).elim
  exact ⟨e, u (), he, hxe, linearIndependent_unique_iff.1 hu, fun y hy ↦ heu y hy ()⟩

end TauCeti
