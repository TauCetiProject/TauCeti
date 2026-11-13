/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Straightening
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.IsManifold.InteriorChart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The straightening theorem for vector fields on a manifold

Near an interior point `x` of a manifold with finite-dimensional model at which a `C^m` vector
field `v` does not vanish, some chart of the `C^m` maximal atlas carries `v` to a constant vector
field: the differential of the chart, read in the model vector space, sends `v y` to one fixed
nonzero vector `u` at every point `y` of its domain (`TauCeti.exists_chart_mfderiv_eq_const`). In
such a chart the integral curves of `v` are parallel straight lines traversed with constant
velocity `u`.

The manifold is `C^n` with `m + 1 ≤ n`, since a vector field read in a chart loses one derivative
of the chart's regularity. The model `I` itself may have a boundary, since only the base point has
to be interior, and on a boundaryless manifold `BoundarylessManifold.isInteriorPoint` supplies this
at every point. At a boundary point the statement fails: a chart preserves the boundary, while a
field tangent to the boundary at one boundary point and transverse to it at nearby ones cannot
become constant.

The same holds for finitely many `C^m` vector fields `V i` whose values at `x` are linearly
independent and whose pairwise Lie brackets vanish near `x`: one chart carries every `V i` to a
constant field `u i`, with the `u i` linearly independent
(`TauCeti.exists_chart_mfderiv_eq_const_of_eventually_mlieBracket_eq_zero`); a single nonvanishing
field is the case of a one-element index set. The fields read in the extended chart at `x` are
`C^m` vector fields on the interior of its target, and by naturality of the bracket under the
inverse extended chart they have vanishing flat brackets (in the `VectorField` namespace,
`lieBracket_mpullback_extChartAt_symm_eventuallyEq_zero_of_eventually_mlieBracket_eq_zero`). So the
simultaneous flat straightening theorem
`TauCeti.exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eventuallyEq_zero` produces a
change of coordinates there. Translated to fix the chart image of `x` and read back through the
interior chart of the model, it is a chart of the manifold
(`PartialDiffeomorph.trans_trans_interiorChart_symm_mem_maximalAtlas`).

## Main results

* `TauCeti.exists_chart_mfderiv_eq_const`: a nonvanishing `C^m` vector field is constant in a
  suitable chart of the `C^m` maximal atlas.
* `TauCeti.exists_chart_mfderiv_eq_const_of_eventually_mlieBracket_eq_zero`: finitely many
  pointwise independent `C^m` vector fields with vanishing brackets are simultaneously constant in a
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
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

omit [FiniteDimensional ℝ E] in
/-- A coordinate change `φ` of the model vector space, `C^m` with `C^m` inverse and defined at the
chart image of an interior point `x`, gives a chart `e` of the `C^m` maximal atlas around `x` that
reads as `φ ∘ extChartAt I x` up to a translation: at every point `y` of its domain, the
differential of `I ∘ e` is the differential of `φ` composed with that of the extended chart. -/
private theorem exists_mem_maximalAtlas_mfderiv_eq {m : ℕ∞} (hm : 1 ≤ m) [IsManifold I m M]
    {x : M} (hx : I.IsInteriorPoint x) {φ : OpenPartialHomeomorph E E}
    (hxφ : extChartAt I x x ∈ φ.source) (hφ : ∀ z ∈ φ.source, ContDiffAt ℝ m φ z)
    (hφs : ∀ z ∈ φ.target, ContDiffAt ℝ m φ.symm z) :
    ∃ e : OpenPartialHomeomorph M H, e ∈ IsManifold.maximalAtlas I m M ∧ x ∈ e.source ∧
      ∀ y ∈ e.source, (y ∈ (extChartAt I x).source ∧ range I ∈ 𝓝 (extChartAt I x y)) ∧
        extChartAt I x y ∈ φ.source ∧ mfderiv I 𝓘(ℝ, E) (I ∘ e) y =
          (fderiv ℝ φ (extChartAt I x y)).comp (mfderiv I 𝓘(ℝ, E) (extChartAt I x) y) := by
  have : IsManifold I 1 M := .of_le (n := m) (by exact_mod_cast hm)
  set e₀ := extChartAt I x with he₀
  -- The extended chart at `x`, restricted to the interior of its target, where the model range is
  -- a neighbourhood of every point.
  set Φ := extChartPartialDiffeomorph I m x
  have hΦ {y : M} (hy : y ∈ Φ.source) : y ∈ e₀.source ∧ range I ∈ 𝓝 (e₀ y) := by
    rw [extChartPartialDiffeomorph_source] at hy
    exact ⟨hy.1,
      mem_interior_iff_mem_nhds.1 (interior_mono (extChartAt_target_subset_range x) hy.2)⟩
  have hxΦ : x ∈ Φ.source := (mem_extChartPartialDiffeomorph_source I m x).2 hx
  -- Translate `φ` so that it fixes `e₀ x`.
  have hφA : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) m E := by
    have h := trans_mem_maximalAtlas_of_contDiffAt
      ((contDiffGroupoid m 𝓘(ℝ, E)).id_mem_maximalAtlas) hφ hφs
    rwa [OpenPartialHomeomorph.refl_trans] at h
  set T := (Homeomorph.addRight (e₀ x - φ (e₀ x))).toOpenPartialHomeomorph
  set σ := φ.trans T
  have hσ : (σ : E → E) = fun z ↦ φ z + (e₀ x - φ (e₀ x)) := rfl
  have hσA : σ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) m E :=
    trans_mem_maximalAtlas_of_contDiffAt hφA (fun _ _ ↦ contDiffAt_id.add contDiffAt_const)
      fun _ _ ↦ contDiffAt_id.add contDiffAt_const
  have hσx : σ (e₀ x) = e₀ x := by
    rw [hσ]
    exact add_sub_cancel _ _
  -- Read the new coordinates through the interior chart of the model.
  set e := (Φ.toOpenPartialHomeomorph.trans σ).trans I.interiorChart.symm
  have hes (y : M) : y ∈ e.source ↔
      (y ∈ Φ.source ∧ e₀ y ∈ φ.source) ∧ σ (e₀ y) ∈ interior (range I) := by
    simp [e, σ, T, Φ, he₀]
  have heq {y : M} (hy : y ∈ e.source) : I (e y) = σ (e₀ y) := by
    have h := I.right_inv (interior_subset ((hes y).1 hy).2)
    simpa [e, Φ, he₀] using h
  refine ⟨e, Φ.trans_trans_interiorChart_symm_mem_maximalAtlas hσA,
    (hes x).2 ⟨⟨hxΦ, hxφ⟩, by rwa [hσx]⟩, fun y hy ↦ ?_⟩
  obtain ⟨⟨hyΦ, hyφ⟩, -⟩ := (hes y).1 hy
  refine ⟨hΦ hyΦ, hyφ, ?_⟩
  have hσd : DifferentiableAt ℝ σ (e₀ y) := by
    rw [hσ]
    exact ((hφ _ hyφ).differentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hm).ne')).add_const _
  -- `I ∘ e` is `σ ∘ e₀` near `y`, so its differential follows from the chain rule.
  have hev : I ∘ e =ᶠ[𝓝 y] σ ∘ e₀ :=
    eventually_of_mem (e.open_source.mem_nhds hy) fun y' hy' ↦ heq hy'
  rw [hev.mfderiv_eq, mfderiv_comp y hσd.mdifferentiableAt
      (mdifferentiableAt_extChartAt (by rw [← extChartAt_source (I := I)]; exact (hΦ hyΦ).1)),
    mfderiv_eq_fderiv, hσ, fderiv_add_const]
  -- The tangent spaces of `E` are `E` by definition, so the remaining casts are identities.
  rfl

/-- **The canonical form for commuting vector fields** [Lee, Thm. 9.46]. Let `V i` be vector
fields on a `C^n` manifold with finite-dimensional model, `C^m` on a neighbourhood of an interior
point `x`, with `1 ≤ m` and `m + 1 ≤ n`, whose values at `x` are linearly independent (so the index
type is finite) and whose pairwise Lie brackets vanish near `x`. Then some chart `e` of the `C^m`
maximal atlas whose domain contains `x` carries all of them to constant vector fields: the
differential of `I ∘ e` sends `V i y` to the same vector `u i` at every point `y` of the domain of
`e`, and the vectors `u i` are linearly independent. On a boundaryless manifold
`BoundarylessManifold.isInteriorPoint` gives the interior hypothesis at every point. -/
theorem exists_chart_mfderiv_eq_const_of_eventually_mlieBracket_eq_zero {ι : Type*} {m : ℕ∞}
    {n : ℕ∞ω} (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n) [IsManifold I 1 M] [IsManifold I n M]
    {V : ι → (y : M) → TangentSpace I y} {U : Set M} {x : M} (hx : I.IsInteriorPoint x)
    (hV : ∀ i, ContMDiffOn I I.tangent m (fun y ↦ (⟨y, V i y⟩ : TangentBundle I M)) U)
    (hU : U ∈ 𝓝 x) (hli : LinearIndependent ℝ fun i ↦ V i x)
    (hbr : Pairwise fun i j ↦ ∀ᶠ y in 𝓝 x, mlieBracket I (V i) (V j) y = 0) :
    ∃ (e : OpenPartialHomeomorph M H) (u : ι → E), e ∈ IsManifold.maximalAtlas I m M ∧
      x ∈ e.source ∧ LinearIndependent ℝ u ∧
        ∀ y ∈ e.source, ∀ i, mfderiv I 𝓘(ℝ, E) (I ∘ e) y (V i y) = u i := by
  have : IsManifold I m M := .of_le (le_self_add.trans hmn)
  have h2n : (2 : ℕ∞ω) ≤ n := by
    have : (1 : ℕ∞ω) + 1 ≤ (m : ℕ∞ω) + 1 := by gcongr; exact_mod_cast hm
    exact (one_add_one_eq_two.symm.le.trans this).trans hmn
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact .of_le h2n
  set e₀ := extChartAt I x with he₀
  have hx' : e₀ x ∈ interior e₀.target := by
    have h := (mem_extChartPartialDiffeomorph_source I m x).2 hx
    rw [extChartPartialDiffeomorph_source] at h
    exact h.2
  -- The fields read in the extended chart at `x` are `C^m` near `e₀ x`.
  set w : ι → E → E := fun i z ↦ mpullback 𝓘(ℝ, E) I e₀.symm (V i) z
  set S := interior e₀.target ∩ e₀.symm ⁻¹' interior U
  have hSo : IsOpen S :=
    ((continuousOn_extChartAt_symm x).mono interior_subset).isOpen_inter_preimage isOpen_interior
      isOpen_interior
  have hxS : e₀ x ∈ S := by
    refine ⟨hx', ?_⟩
    rw [mem_preimage, he₀, extChartAt_to_inv]
    exact mem_interior_iff_mem_nhds.2 hU
  have hwS (i : ι) : ContDiffOn ℝ m (w i) S :=
    ((hV i).mono interior_subset).contDiffOn_mpullback_extChartAt_symm hmn
  -- Where the model range is a neighbourhood of `e₀ y`, the coordinate fields at `e₀ y` are the
  -- images of the `V i y` under the differential of `e₀`.
  have hwe (i : ι) {y : M} (hy : y ∈ e₀.source ∧ range I ∈ 𝓝 (e₀ y)) :
      w i (e₀ y) = mfderiv I 𝓘(ℝ, E) e₀ y (V i y) :=
    mpullback_extChartAt_symm_apply_eq_mfderiv (V i) hy.1 hy.2
  -- The differential of `e₀` at `x` is injective, so it keeps the `V i x` independent.
  have hli' : LinearIndependent ℝ fun i ↦ w i (e₀ x) := by
    have h := hli.map' (mfderiv I 𝓘(ℝ, E) e₀ x).toLinearMap
      (LinearMap.ker_eq_bot.2 (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)).injective)
    have hcomp : (fun i ↦ w i (e₀ x)) = (mfderiv I 𝓘(ℝ, E) e₀ x).toLinearMap ∘ fun i ↦ V i x :=
      funext fun i ↦ hwe i ⟨mem_extChartAt_source x,
        mem_interior_iff_mem_nhds.1 (interior_mono (extChartAt_target_subset_range x) hx')⟩
    rw [hcomp]
    -- The tangent spaces of `E` are `E` by definition, with the same module structure.
    exact h
  -- The coordinate fields have vanishing brackets near `e₀ x`, by naturality of the bracket.
  have hdiff (k : ι) : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I I.tangent (fun y ↦ (⟨y, V k y⟩ : TangentBundle I M)) y :=
    (eventually_mem_nhds_iff.2 hU).mono fun y hy ↦
      ((hV k).contMDiffAt hy).mdifferentiableAt (by exact_mod_cast (zero_lt_one.trans_le hm).ne')
  have hbr' : Pairwise fun i j ↦ lieBracket ℝ (w i) (w j) =ᶠ[𝓝 (e₀ x)] 0 := fun i j hij ↦
    lieBracket_mpullback_extChartAt_symm_eventuallyEq_zero_of_eventually_mlieBracket_eq_zero hx
      (hdiff i) (hdiff j) (hbr hij)
  -- Straighten the coordinate fields, and read the straightening as a chart of `M`.
  obtain ⟨φ, hxφ, hφ, hφs, hφw⟩ :=
    exists_openPartialHomeomorph_fderiv_eq_const_of_lieBracket_eventuallyEq_zero hm hwS
      (hSo.mem_nhds hxS) hli' hbr'
  obtain ⟨e, he, hxe, hed⟩ := exists_mem_maximalAtlas_mfderiv_eq hm hx hxφ hφ hφs
  refine ⟨e, fun i ↦ w i (e₀ x), he, hxe, hli', fun y hy i ↦ ?_⟩
  obtain ⟨hy₀, hyφ, hd⟩ := hed y hy
  rw [hd]
  exact (congrArg (fderiv ℝ φ (e₀ y)) (hwe i hy₀).symm).trans (hφw _ hyφ i)

/-- **The straightening theorem** [Lee, Thm. 9.22]. Let `v` be a vector field on a `C^n` manifold
with finite-dimensional model, `C^m` on a neighbourhood of an interior point `x`, with `1 ≤ m`,
`m + 1 ≤ n` and `v x ≠ 0`. Then some chart `e` of the `C^m` maximal atlas whose domain contains `x`
carries `v` to a constant nonzero vector field: the differential of `I ∘ e` sends `v y` to the same
vector `u ≠ 0` at every point `y` of the domain of `e`. This is the case of a single field in
`TauCeti.exists_chart_mfderiv_eq_const_of_eventually_mlieBracket_eq_zero`. -/
theorem exists_chart_mfderiv_eq_const {m : ℕ∞} {n : ℕ∞ω} (hm : 1 ≤ m) (hmn : (m : ℕ∞ω) + 1 ≤ n)
    [IsManifold I 1 M] [IsManifold I n M] {v : (y : M) → TangentSpace I y} {U : Set M} {x : M}
    (hxI : I.IsInteriorPoint x)
    (hv : ContMDiffOn I I.tangent m (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) U) (hU : U ∈ 𝓝 x)
    (hx : v x ≠ 0) :
    ∃ (e : OpenPartialHomeomorph M H) (u : E), e ∈ IsManifold.maximalAtlas I m M ∧
      x ∈ e.source ∧ u ≠ 0 ∧ ∀ y ∈ e.source, mfderiv I 𝓘(ℝ, E) (I ∘ e) y (v y) = u := by
  obtain ⟨e, u, he, hxe, hu, heu⟩ :=
    exists_chart_mfderiv_eq_const_of_eventually_mlieBracket_eq_zero hm hmn (V := fun _ : Unit ↦ v)
      hxI (fun _ ↦ hv) hU (linearIndependent_unique_iff.2 hx)
      fun i j h ↦ (h (Subsingleton.elim i j)).elim
  exact ⟨e, u (), he, hxe, linearIndependent_unique_iff.1 hu, fun y hy ↦ heu y hy ()⟩

end TauCeti
