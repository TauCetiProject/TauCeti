/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Vector fields read in the charts of a manifold modelled on its own model space

Let `M` be a manifold modelled on a real normed space `E` with the trivial model `𝓘(ℝ, E)`. A vector
field `V` on `E` pulls back by a chart `e` of the maximal atlas to the field
`VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V` on the source of `e`. This file computes the chart
derivative of the pullback and the derivative of a function along it, and shows that it is smooth
when `V` is. The pullbacks of constant fields in the preferred chart give, near any regular point
of a smooth function, a smooth field along which the function strictly decreases; finitely many
of them, cut off by bump functions, give a global field of unit-speed decrease near any compact set
of regular points.

## Main declarations

* `TauCeti.mfderiv_mpullback_apply`, `TauCeti.mvfderiv_mpullback_apply`,
  `TauCeti.contMDiffOn_mpullback`: the pullback of a vector field by a chart.
* `TauCeti.chartConstField`: a constant field in the preferred chart at a point, on the manifold.
* `TauCeti.mvfderiv_chartConstField_apply`: the derivative of a function along a constant chart
  field, read in the chart.
* `TauCeti.exists_mem_nhds_mvfderiv_chartConstField_lt_zero`: near a regular point of a smooth
  function, some constant field in the preferred chart is a direction of strict decrease.
* `TauCeti.exists_mem_nhds_contMDiffOn_mvfderiv_eq_neg_one`: near a regular point of a smooth
  function, a rescaled constant chart field is a smooth direction of unit-speed decrease.
* `TauCeti.exists_vectorField_mvfderiv_eq_neg_one`: a smooth vector field, vanishing outside a
  compact set, with `df(X) ≤ 0` everywhere and `df(X) = -1` on a neighbourhood of a compact set of
  regular points.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

section Pullback

variable {e : OpenPartialHomeomorph M E} {h : E → ℝ}

/-- The pullback `de_y⁻¹ (V (e y))` of a vector field `V` on the model space by a chart `e`. -/
theorem mfderiv_mpullback_apply (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (V : (z : E) → TangentSpace 𝓘(ℝ, E) z) {y : M} (hy : y ∈ e.source) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e y (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y) = V (e y) := by
  rw [VectorField.mpullback_apply]
  exact (isInvertible_mfderiv_chart
    (IsManifold.maximalAtlas_subset_of_le (by simp) he) hy).self_apply_inverse _

/-- The derivative of `f` along the pullback of a vector field `V` by a chart `e`, where
`f = h ∘ e` on the source of `e`. -/
theorem mvfderiv_mpullback_apply (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hfh : EqOn f (h ∘ e) e.source) (V : (z : E) → TangentSpace 𝓘(ℝ, E) z) {y : M}
    (hy : y ∈ e.source)
    (hh : DifferentiableAt ℝ h (e y)) :
    mvfderiv 𝓘(ℝ, E) f y (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y) =
      fderiv ℝ h (e y) (V (e y)) := by
  -- `mvfderiv` composes `mfderiv` with `NormedSpace.fromTangentSpace`, which is the identity of
  -- `ℝ`, so the two agree definitionally; Mathlib has no rewrite lemma between them.
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y (VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y) = _
  rw [mfderiv_eq_fderiv_comp_of_eqOn (IsManifold.maximalAtlas_subset_of_le (by simp) he) hfh hy hh]
  exact congrArg (fderiv ℝ h (e y)) (mfderiv_mpullback_apply he V hy)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The pullback of a smooth vector field on the model space by a chart of the maximal atlas is
smooth on the source of the chart. -/
theorem contMDiffOn_mpullback (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {V : (z : E) → TangentSpace 𝓘(ℝ, E) z}
    (hV : ContDiffOn ℝ ∞ V e.target) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e V y⟩ : TangentBundle 𝓘(ℝ, E) M))
      e.source := by
  intro y hy
  have hVy : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun z ↦ (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) E)) (e y) :=
    contMDiffAt_vectorSpace_iff_contDiffAt.2
      ((hV (e y) (e.map_source hy)).contDiffAt (e.open_target.mem_nhds (e.map_source hy)))
  exact (ContMDiffAt.mpullback_vectorField_preimage hVy (contMDiffAt_of_mem_maximalAtlas he hy)
    (isInvertible_mfderiv_chart (IsManifold.maximalAtlas_subset_of_le (by simp) he) hy)
    (by simp)).contMDiffWithinAt

end Pullback

section ConstField

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The constant vector field with value `v` on the model space. -/
noncomputable def constVectorField (v : E) : (z : E) → TangentSpace 𝓘(ℝ, E) z := fun _ ↦ v

omit [FiniteDimensional ℝ E] in
/-- The constant vector field takes the value `v` at every point, under the canonical
identification `NormedSpace.fromTangentSpace` of each tangent space of `E` with `E`. -/
theorem constVectorField_apply (v z : E) :
    constVectorField v z = (NormedSpace.fromTangentSpace z).symm v :=
  (rfl)

omit [FiniteDimensional ℝ E] in
/-- The constant vector field is smooth. -/
theorem contMDiff_constVectorField (v : E) {n : WithTop ℕ∞} :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent n
      (fun z ↦ (⟨z, constVectorField v z⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
  contMDiff_vectorSpace_iff_contDiff.2 contDiff_const

variable (E) in
/-- The constant vector field with value `v` in the preferred chart at `p`, pulled back to the
manifold. -/
noncomputable def chartConstField (p : M) (v : E) : (y : M) → TangentSpace 𝓘(ℝ, E) y :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p) (constVectorField v)

omit [FiniteDimensional ℝ E] in
/-- A constant field in a chart is smooth on the source of the chart. -/
theorem contMDiffOn_chartConstField [FiniteDimensional ℝ E] (p : M) (v : E) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, chartConstField E p v y⟩ : TangentBundle 𝓘(ℝ, E) M)) (chartAt E p).source :=
  contMDiffOn_mpullback (IsManifold.chart_mem_maximalAtlas p) contDiffOn_const

omit [FiniteDimensional ℝ E] in
/-- On the source of the preferred chart at `y₀`, the derivative of a smooth `f` along a constant
chart field with value `v` is the derivative of `f ∘ (chartAt E y₀).symm` in the direction `v`. -/
theorem mvfderiv_chartConstField_apply (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) {y₀ y : M} (v : E)
    (hy : y ∈ (chartAt E y₀).source) :
    mvfderiv 𝓘(ℝ, E) f y (chartConstField E y₀ v y) =
      fderiv ℝ (f ∘ (chartAt E y₀).symm) (chartAt E y₀ y) v :=
  mvfderiv_mpullback_apply (IsManifold.chart_mem_maximalAtlas y₀) (eqOn_comp_chartAt_symm y₀) _ hy
    (((contDiffOn_comp_chartAt_symm hf y₀).contDiffAt ((chartAt E y₀).open_target.mem_nhds
      ((chartAt E y₀).map_source hy))).differentiableAt (by simp))

omit [FiniteDimensional ℝ E] in
/-- Near a regular point of `f`, some constant field in the preferred chart is a direction of
strict decrease of `f`. -/
theorem exists_mem_nhds_mvfderiv_chartConstField_lt_zero (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    {y₀ : M} (hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ ≠ 0) :
    ∃ v : E, ∃ U ∈ 𝓝 y₀, U ⊆ (chartAt E y₀).source ∧
      ∀ y ∈ U, mvfderiv 𝓘(ℝ, E) f y (chartConstField E y₀ v y) < 0 := by
  set c := chartAt E y₀
  set h := f ∘ c.symm
  have hmem : y₀ ∈ c.source := mem_chart_source E y₀
  have hdiff : ∀ y ∈ c.source, DifferentiableAt ℝ h (c y) := fun y hy ↦
    ((contDiffOn_comp_chartAt_symm hf y₀).contDiffAt (c.open_target.mem_nhds
      (c.map_source hy))).differentiableAt (by simp)
  have hL : fderiv ℝ h (c y₀) ≠ 0 := fun h0 ↦ hcrit
    ((mfderiv_eq_zero_iff_of_eqOn (IsManifold.chart_mem_maximalAtlas y₀)
      (eqOn_comp_chartAt_symm y₀) hmem (hdiff y₀ hmem)).2 h0)
  obtain ⟨w, hw⟩ : ∃ w, fderiv ℝ h (c y₀) w ≠ 0 := by
    by_contra hno
    simp only [ne_eq, not_exists, not_not] at hno
    exact hL (ContinuousLinearMap.ext hno)
  obtain ⟨v, hv⟩ : ∃ v, fderiv ℝ h (c y₀) v < 0 := by
    rcases hw.lt_or_gt with hlt | hgt
    · exact ⟨w, hlt⟩
    · exact ⟨-w, by rw [map_neg]; linarith⟩
  have hcont : ContinuousAt (fun z ↦ fderiv ℝ h z v) (c y₀) :=
    (((contDiffOn_comp_chartAt_symm hf y₀).continuousOn_fderiv_of_isOpen c.open_target
      (by simp)).continuousAt (c.open_target.mem_nhds (c.map_source hmem))).clm_apply
      continuousAt_const
  have hev : ∀ᶠ y in 𝓝 y₀, fderiv ℝ h (c y) v < 0 :=
    (hcont.comp (c.continuousAt hmem)).eventually (gt_mem_nhds hv)
  refine ⟨v, {y | y ∈ c.source ∧ fderiv ℝ h (c y) v < 0},
    Filter.inter_mem (c.open_source.mem_nhds hmem) hev, fun y hy ↦ hy.1, fun y hy ↦ ?_⟩
  rw [mvfderiv_chartConstField_apply hf v hy.1]
  exact hy.2

/-- Near a regular point of a smooth function `f`, there is a smooth local vector field along which
`f` decreases at unit speed, `df(s) = -1`. -/
theorem exists_mem_nhds_contMDiffOn_mvfderiv_eq_neg_one (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    {y₀ : M} (hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y₀ ≠ 0) :
    ∃ U ∈ 𝓝 y₀, ∃ s : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
        (fun y ↦ (⟨y, s y⟩ : TangentBundle 𝓘(ℝ, E) M)) U ∧
      ∀ y ∈ U, mvfderiv 𝓘(ℝ, E) f y (s y) = -1 := by
  -- Divide a constant chart field `w` of strict decrease by `-df(w)`; read in the chart, `df(w)`
  -- is the smooth nonvanishing function `y ↦ fderiv h (c y) v`.
  obtain ⟨v, U, hU, hUc, hneg⟩ := exists_mem_nhds_mvfderiv_chartConstField_lt_zero hf hcrit
  set c := chartAt E y₀
  set h := f ∘ c.symm
  have hh := contDiffOn_comp_chartAt_symm hf y₀
  have hdf : ∀ y ∈ c.source,
      mvfderiv 𝓘(ℝ, E) f y (chartConstField E y₀ v y) = fderiv ℝ h (c y) v := fun y hy ↦
    mvfderiv_chartConstField_apply hf v hy
  have hg : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun y ↦ fderiv ℝ h (c y) v) U := by
    have h' : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ h z v) c.target :=
      (hh.fderiv_of_isOpen c.open_target (by simp)).clm_apply contDiffOn_const
    exact (h'.contMDiffOn.comp contMDiffOn_chart fun y hy ↦ c.map_source hy).mono hUc
  have hne : ∀ y ∈ U, fderiv ℝ h (c y) v ≠ 0 := fun y hy ↦ by
    rw [← hdf y (hUc hy)]
    exact (hneg y hy).ne
  refine ⟨U, hU, fun y ↦ (-(fderiv ℝ h (c y) v)⁻¹) • chartConstField E y₀ v y,
    (hg.inv₀ hne).neg.smul_section ((contMDiffOn_chartConstField y₀ v).mono hUc),
    fun y hy ↦ ?_⟩
  rw [map_smul, hdf y (hUc hy), smul_eq_mul, neg_mul, inv_mul_cancel₀ (hne y hy)]

end ConstField

section Glue

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- **A unit-speed descending field near a compact set of regular points.** If a compact set `K`
contains no critical point of the smooth function `f`, there is a smooth vector field `X`, vanishing
outside a compact set, along which `f` never increases, `df(X) ≤ 0`, and with `df(X) = -1` on an
open neighbourhood of `K`. -/
theorem exists_vectorField_mvfderiv_eq_neg_one (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) {K : Set M}
    (hK : IsCompact K) (hreg : ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, mvfderiv 𝓘(ℝ, E) f x (X x) ≤ 0) ∧
      (∃ U, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) f x (X x) = -1) ∧
      ∃ C, IsCompact C ∧ ∀ x ∉ C, X x = 0 := by
  -- Near each `x ∈ K` take a local field `s x` with `df(s x) = -1` on `V x`, and a bump function
  -- `ρ x` supported in the interior of `V x`.
  choose V hV s hs hsf using fun x : K ↦ exists_mem_nhds_contMDiffOn_mvfderiv_eq_neg_one hf
    (hreg x x.2)
  choose ρ hρ using fun x : K ↦
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (x : M)).mem_iff.1
      (interior_mem_nhds.2 (hV x))
  -- Finitely many of the open sets where some `ρ x` is `1` cover `K`.
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx ↦ interior {y | ρ ⟨x, hx⟩ y = 1})
    fun x hx ↦ interior_mem_nhds.2 (ρ ⟨x, hx⟩).eventuallyEq_one
  -- `Y = ∑ ρ i • s i` has `df(Y) = -g` with `g = ∑ ρ i`, and `g ≥ 1` near `K`; divide by `g`,
  -- smoothly modified where `g < 1` so that it stays positive.
  set g : M → ℝ := fun y ↦ ∑ i ∈ t, ρ i y with hg
  set d : M → ℝ := fun y ↦ g y + (1 - Real.smoothTransition (g y)) with hd
  set Y : (y : M) → TangentSpace 𝓘(ℝ, E) y := fun y ↦ ∑ i ∈ t, ((ρ i : M → ℝ) • s i) y with hY
  have hg0 : ∀ y, 0 ≤ g y := fun y ↦ Finset.sum_nonneg fun i _ ↦ (ρ i).nonneg
  have hgd : ∀ y, g y ≤ d y := fun y ↦ by
    have := Real.smoothTransition.le_one (g y)
    simp only [hd]
    linarith
  have hd0 : ∀ y, d y ≠ 0 := by
    intro y
    rcases (hg0 y).eq_or_lt with h | h
    · simp [hd, ← h]
    · exact (h.trans_le (hgd y)).ne'
  have hgC : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g := ContMDiff.sum fun i _ ↦ (ρ i).contMDiff
  have hdC : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ d :=
    hgC.add (contMDiff_const.sub (Real.smoothTransition.contDiff.contMDiff.comp hgC))
  have hYC : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, Y y⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    ContMDiff.sum_section fun i _ ↦ ContMDiffOn.smul_section_of_tsupport
      (ρ i).contMDiff.contMDiffOn isOpen_interior (hρ i).2 ((hs i).mono interior_subset)
  have hdfY : ∀ y, mvfderiv 𝓘(ℝ, E) f y (Y y) = -g y := by
    intro y
    simp only [hY, hg, map_sum, Pi.smul_apply', map_smul, smul_eq_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hy : ρ i y = 0
    · simp [hy]
    · rw [hsf i y (interior_subset ((hρ i).2 (subset_closure hy))), mul_neg_one]
  refine ⟨fun y ↦ (d y)⁻¹ • Y y, ContMDiff.smul_section (hdC.inv₀ hd0) hYC, fun y ↦ ?_,
    ⟨⋃ i ∈ t, interior {y | ρ i y = 1}, isOpen_biUnion fun _ _ ↦ isOpen_interior, ht, ?_⟩,
    ⋃ i ∈ t, tsupport (ρ i), t.isCompact_biUnion fun i _ ↦ (ρ i).hasCompactSupport, ?_⟩
  · rw [map_smul, hdfY, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ((hg0 y).trans (hgd y)))
      (neg_nonpos.2 (hg0 y))
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
    have h1 : 1 ≤ g y := by
      have := Finset.single_le_sum (fun j _ ↦ (ρ j).nonneg) hi (f := fun j ↦ ρ j y)
      rwa [(interior_subset hyi : ρ i y = 1)] at this
    have hdg : d y = g y := by simp [hd, Real.smoothTransition.one_of_one_le h1]
    rw [map_smul, hdfY, hdg, smul_eq_mul, mul_neg, inv_mul_cancel₀ (by linarith)]
  · intro y hy
    have h0 : ∀ i ∈ t, ρ i y = 0 := fun i hi ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (mem_iUnion₂.2 ⟨i, hi, h⟩)
    have hY0 : Y y = 0 := Finset.sum_eq_zero fun i hi ↦ by simp [h0 i hi]
    simp [hY0]

end Glue

end TauCeti
