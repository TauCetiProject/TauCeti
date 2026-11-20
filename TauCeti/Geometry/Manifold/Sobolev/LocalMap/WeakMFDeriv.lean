/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Bases
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.Sobolev.ChartTransition
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.CoordChange
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# The weak differential of a local Sobolev map

Let `X` be a Riemann surface, given as a charted space modelled on `ℂ`, and `M` a manifold
modelled on `I : ModelWithCorners ℝ F H`. A field `Du` of real linear maps
`Du x : T_x X → T_{u x} M` is a **weak differential** of `u : X → M` on `s ⊆ X`
(`TauCeti.HasWeakMFDerivOn I u Du s`) when, in the chart of `X` at every point `x₀` and the extended
chart of `M` at every point `y₀`, its coordinate expression is a weak derivative of the coordinate
expression `extChartAt I y₀ ∘ u ∘ (chartAt ℂ x₀).symm` of `u`, on the open part of the chart
target lying over `s` and mapped by `u` into the chart of `y₀`. As for `mfderiv`, the tangent
spaces are read in the preferred charts: `Du x` goes from the coordinates of the chart at `x` to
those of the chart at `u x`, and its coordinate expression composes it with the derivatives of the
changes of chart, `fderiv ℝ (chartAt ℂ x ∘ (chartAt ℂ x₀).symm)` on `X` and
`tangentCoordChange I (u x) y₀ (u x)` on `M`.

For an open set `s` this is the weak differential of a local Sobolev map in the sense of
McDuff–Salamon, Appendix B.1: an almost everywhere defined section of `Hom(TX, u*TM)` whose
coordinate expressions are the weak derivatives of those of `u`.

* **Existence.** On a second countable Riemann surface, every local Sobolev map
  `u ∈ W^{1,p}_loc(s, M)` into a boundaryless manifold has a weak differential on the open set
  `s` (`TauCeti.MemWkpLocMapOn.exists_hasWeakMFDerivOn`), whose coordinate expressions are locally
  `Lᵖ` (`TauCeti.HasWeakMFDerivOn.memLpLoc`). The weak derivatives of the coordinate expressions
  of `u` in countably many pairs of charts covering `s` are glued along the changes of chart, by
  the chain rules for weak derivatives under changes of chart of the source
  (`TauCeti.HasWeakFDerivOn.comp_symm_trans_of_mem_maximalAtlas`) and of the target
  (`TauCeti.HasWeakFDerivOn.extCoordChange_comp`), and by their uniqueness
  (`TauCeti.HasWeakFDerivOn.ae_eq`).
* **Uniqueness.** Two weak differentials agree almost everywhere in every chart
  (`TauCeti.HasWeakMFDerivOn.ae_eq`), and a field agreeing almost everywhere with a weak
  differential is one (`TauCeti.HasWeakMFDerivOn.congr_ae`).
* **Comparison.** The differential `mfderiv 𝓘(ℝ, ℂ) I u` of a map of class `C¹` on an open set is a
  weak differential there (`ContMDiffOn.hasWeakMFDerivOn_mfderiv`), so every weak differential of
  such a map agrees with it almost everywhere (`TauCeti.HasWeakMFDerivOn.ae_eq_mfderiv`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open Set Filter MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {u : X → M} {s t : Set X} {p : ENNReal}
  {Du Du' : (x : X) → TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)}

section Defs

variable [IsManifold I 1 M]

variable (I) in
/-- **The weak differential of a map from a Riemann surface.** A field `Du` of real linear maps
`Du x : T_x X → T_{u x} M` is a weak differential of `u : X → M` on `s` if, for every `x₀ : X` and
`y₀ : M`, its coordinate expression

`z ↦ tangentCoordChange I (u x) y₀ (u x) ∘ Du x ∘ fderiv ℝ (chartAt ℂ x ∘ (chartAt ℂ x₀).symm) z`,

where `x = (chartAt ℂ x₀).symm z`, is a weak derivative of the coordinate expression
`extChartAt I y₀ ∘ u ∘ (chartAt ℂ x₀).symm` of `u` on the interior of the set of points `z` of the
target of the chart at `x₀` with `x ∈ s` and `u x` in the source of the chart at `y₀`. The tangent
spaces are read in the preferred charts, as for `mfderiv`. The definition is intended for open
`s` and continuous `u`, where these sets are open. -/
def HasWeakMFDerivOn (u : X → M)
    (Du : (x : X) → TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x)) (s : Set X) : Prop :=
  ∀ x₀ : X, ∀ y₀ : M, HasWeakFDerivOn volume
    (Opens.interior ((chartAt ℂ x₀).target ∩
      (chartAt ℂ x₀).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)))
    (extChartAt I y₀ ∘ u ∘ (chartAt ℂ x₀).symm) fun z ↦
      tangentCoordChange I (u ((chartAt ℂ x₀).symm z)) y₀ (u ((chartAt ℂ x₀).symm z)) ∘L
        Du ((chartAt ℂ x₀).symm z) ∘L
          (fderiv ℝ (chartAt ℂ ((chartAt ℂ x₀).symm z) ∘ (chartAt ℂ x₀).symm) z : ℂ →L[ℝ] ℂ)

variable (I) in
/-- Unfolding the definition of a weak differential. -/
theorem hasWeakMFDerivOn_iff : HasWeakMFDerivOn I u Du s ↔ ∀ x₀ : X, ∀ y₀ : M,
    HasWeakFDerivOn volume (Opens.interior ((chartAt ℂ x₀).target ∩
      (chartAt ℂ x₀).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)))
    (extChartAt I y₀ ∘ u ∘ (chartAt ℂ x₀).symm) fun z ↦
      tangentCoordChange I (u ((chartAt ℂ x₀).symm z)) y₀ (u ((chartAt ℂ x₀).symm z)) ∘L
        Du ((chartAt ℂ x₀).symm z) ∘L
          (fderiv ℝ (chartAt ℂ ((chartAt ℂ x₀).symm z) ∘ (chartAt ℂ x₀).symm) z : ℂ →L[ℝ] ℂ) :=
  Iff.rfl

/-- A weak differential on `s` is a weak differential on every subset of `s`. -/
theorem HasWeakMFDerivOn.mono (h : HasWeakMFDerivOn I u Du s) (hts : t ⊆ s) :
    HasWeakMFDerivOn I u Du t := fun x₀ y₀ ↦
  (h x₀ y₀).mono fun _ hz ↦
    interior_mono (inter_subset_inter_right _ (preimage_mono (inter_subset_inter_left _ hts))) hz

/-- **A field agreeing almost everywhere with a weak differential is a weak differential.** If,
in the chart at every point `x₀`, the fields `Du` and `Du'` agree at almost every point of `s`,
then `Du'` is a weak differential of `u` on `s` as soon as `Du` is. -/
theorem HasWeakMFDerivOn.congr_ae (h : HasWeakMFDerivOn I u Du s)
    (h' : ∀ x₀ : X, ∀ᵐ z ∂volume.restrict ((chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' s),
      Du ((chartAt ℂ x₀).symm z) = Du' ((chartAt ℂ x₀).symm z)) :
    HasWeakMFDerivOn I u Du' s := fun x₀ y₀ ↦ by
  refine (h x₀ y₀).congr_ae_deriv ?_
  have hsub : (Opens.interior ((chartAt ℂ x₀).target ∩
      (chartAt ℂ x₀).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)) : Set ℂ) ⊆
      (chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' s := fun z hz ↦
    ⟨(interior_subset hz).1, (interior_subset hz).2.1⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (h' x₀)] with z hz
  rw [hz]

end Defs

/-! ### Changes of chart -/

section ChartChange

/-- For `u` continuous on an open set `s`, the points of the target of the chart at `x₀` lying over
`s` and mapped by `u` into an open set `t` form an open set, which is therefore its own interior. -/
private theorem coe_interior_chartAt_target_inter_preimage (hs : IsOpen s) (hu : ContinuousOn u s)
    {t : Set M} (ht : IsOpen t) (x₀ : X) :
    (Opens.interior ((chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' (s ∩ u ⁻¹' t)) : Set ℂ) =
      (chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' (s ∩ u ⁻¹' t) :=
  ((chartAt ℂ x₀).isOpen_inter_preimage_symm_inter_preimage hu hs ht).interior_eq

variable [IsManifold 𝓘(ℝ, ℂ) 1 X] [IsManifold I 1 M] [I.Boundaryless]

/-- **Change of the pair of charts.** Let `D` be a weak derivative of the coordinate expression of
`u` in the chart of `X` at `a` and the extended chart of `M` at `b`. Then, on the part of the
domain of the charts at `x₀` and `y₀` covered by the charts at `a` and `b`, the coordinate
expression of `u` in the charts at `x₀` and `y₀` has the weak derivative obtained from `D` by the
changes of chart. -/
private theorem hasWeakFDerivOn_extChartAt_comp_comp_chartAt_symm (hs : IsOpen s)
    (hu : ContinuousOn u s) {a x₀ : X} {b y₀ : M} {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior ((chartAt ℂ a).target ∩
      (chartAt ℂ a).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H b).source)))
      (extChartAt I b ∘ u ∘ (chartAt ℂ a).symm) D) :
    HasWeakFDerivOn volume (Opens.interior ((chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹'
        ((s ∩ (chartAt ℂ a).source) ∩ u ⁻¹' ((chartAt H y₀).source ∩ (chartAt H b).source))))
      (extChartAt I y₀ ∘ u ∘ (chartAt ℂ x₀).symm) fun z ↦
        tangentCoordChange I b y₀ (u ((chartAt ℂ x₀).symm z)) ∘L
          D (chartAt ℂ a ((chartAt ℂ x₀).symm z)) ∘L
            fderiv ℝ (chartAt ℂ a ∘ (chartAt ℂ x₀).symm) z := by
  have := hD.completeSpace
  set V := (chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹'
    ((s ∩ (chartAt ℂ a).source) ∩ u ⁻¹' ((chartAt H y₀).source ∩ (chartAt H b).source))
  have hV : (Opens.interior V : Set ℂ) = V :=
    coe_interior_chartAt_target_inter_preimage (hs.inter (chartAt ℂ a).open_source)
      (hu.mono inter_subset_left) ((chartAt H y₀).open_source.inter (chartAt H b).open_source) x₀
  -- First change the chart of `X` from `a` to `x₀`, on the part of the domain covered by both.
  have h1 := hD.comp_symm_trans_of_mem_maximalAtlas (U := Opens.interior V)
    (IsManifold.chart_mem_maximalAtlas x₀) (IsManifold.chart_mem_maximalAtlas a)
    (by rw [hV, OpenPartialHomeomorph.trans_source]; exact fun z hz ↦ ⟨hz.1, hz.2.1.2⟩)
    fun z hz ↦ by
      rw [hV] at hz
      rw [coe_interior_chartAt_target_inter_preimage hs hu (chartAt H b).open_source a]
      refine ⟨(chartAt ℂ a).map_source hz.2.1.2, ?_⟩
      simp only [Function.comp_apply, mem_preimage, (chartAt ℂ a).left_inv hz.2.1.2]
      exact ⟨hz.2.1.1, hz.2.2.2⟩
  have heq : ∀ᵐ z ∂volume.restrict (Opens.interior V),
      ((extChartAt I b ∘ u ∘ (chartAt ℂ a).symm) ∘ chartAt ℂ a ∘ (chartAt ℂ x₀).symm) z =
        (extChartAt I b ∘ u ∘ (chartAt ℂ x₀).symm) z :=
    ae_restrict_of_forall_mem (Opens.interior V).isOpen.measurableSet fun z hz ↦ by
      simp [(chartAt ℂ a).left_inv (interior_subset hz).2.1.2]
  -- Then change the chart of `M` from `b` to `y₀`.
  refine (h1.congr_ae heq).extCoordChange_comp ?_ fun z hz ↦ ?_
  · rw [hV]
    exact ((chartAt ℂ x₀).continuousOn_comp_comp_symm
      ((continuousOn_extChartAt b).mono fun y hy ↦ by simpa using hy.2)
      (hu.mono inter_subset_left)).mono fun z hz ↦ ⟨hz.1, hz.2.1, hz.2.2⟩
  · rw [← SetLike.mem_coe, hV] at hz
    exact ⟨hz.2.2.2, hz.2.2.1⟩

end ChartChange

/-! ### Existence -/

/-- On a second countable surface, a map continuous on an open set `s` admits a choice, at every
point `x` of `s`, of a point `sel x` among countably many such that `x` lies in the chart at
`sel x` and `u x` in the chart at `u (sel x)`. -/
private theorem exists_countable_chartAt_selection [SecondCountableTopology X] (hs : IsOpen s)
    (hc : ContinuousOn u s) : ∃ T : Set X, T.Countable ∧ ∃ sel : X → X, ∀ x ∈ s,
      sel x ∈ T ∧ x ∈ (chartAt ℂ (sel x)).source ∧ u x ∈ (chartAt H (u (sel x))).source := by
  classical
  set O : X → Set X := fun a ↦ (chartAt ℂ a).source ∩ (s ∩ u ⁻¹' (chartAt H (u a)).source)
  obtain ⟨T, hT, hTO⟩ := isOpen_iUnion_countable O fun a ↦
    (chartAt ℂ a).open_source.inter (hc.isOpen_inter_preimage hs (chartAt H (u a)).open_source)
  have hsel : ∀ x ∈ s, ∃ a ∈ T, x ∈ O a := fun x hx ↦ by
    have hx' : x ∈ ⋃ a, O a :=
      mem_iUnion.2 ⟨x, mem_chart_source ℂ x, hx, mem_chart_source H (u x)⟩
    rw [← hTO] at hx'
    simpa using hx'
  refine ⟨T, hT, fun x ↦ if h : ∃ a ∈ T, x ∈ O a then h.choose else x, fun x hx ↦ ?_⟩
  simp only [dite_eq_left (hsel x hx)]
  obtain ⟨haT, hxa, -, hua⟩ := (hsel x hx).choose_spec
  exact ⟨haT, hxa, hua⟩

/-- **Gluing weak derivatives in charts.** Let `D a` be a weak derivative of the coordinate
expression of `u` in the charts at `a` and `u a`, and let `sel` choose, at each point of `s`, one
of countably many such charts containing it. If the coordinate expression of `u` in the charts at
`x₀` and `y₀` has some weak derivative, then the field obtained from the `D (sel x)` by the changes
of chart is a weak derivative of it. -/
private theorem hasWeakFDerivOn_glue [IsManifold 𝓘(ℝ, ℂ) 1 X] [IsManifold I 1 M]
    [I.Boundaryless] (hs : IsOpen s) (hc : ContinuousOn u s)
    {D : X → ℂ → ℂ →L[ℝ] F} (hD : ∀ a, HasWeakFDerivOn volume
      (Opens.interior ((chartAt ℂ a).target ∩
        (chartAt ℂ a).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H (u a)).source)))
      (extChartAt I (u a) ∘ u ∘ (chartAt ℂ a).symm) (D a))
    {T : Set X} (hT : T.Countable) {sel : X → X} (hsel : ∀ x ∈ s,
      sel x ∈ T ∧ x ∈ (chartAt ℂ (sel x)).source ∧ u x ∈ (chartAt H (u (sel x))).source)
    {x₀ : X} {y₀ : M} {D' : ℂ → ℂ →L[ℝ] F}
    (hD' : HasWeakFDerivOn volume (Opens.interior ((chartAt ℂ x₀).target ∩
      (chartAt ℂ x₀).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)))
      (extChartAt I y₀ ∘ u ∘ (chartAt ℂ x₀).symm) D') :
    HasWeakFDerivOn volume (Opens.interior ((chartAt ℂ x₀).target ∩
      (chartAt ℂ x₀).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)))
      (extChartAt I y₀ ∘ u ∘ (chartAt ℂ x₀).symm) fun z ↦
        tangentCoordChange I (u ((chartAt ℂ x₀).symm z)) y₀ (u ((chartAt ℂ x₀).symm z)) ∘L
          (tangentCoordChange I (u (sel ((chartAt ℂ x₀).symm z))) (u ((chartAt ℂ x₀).symm z))
            (u ((chartAt ℂ x₀).symm z)) ∘L D (sel ((chartAt ℂ x₀).symm z))
              (chartAt ℂ (sel ((chartAt ℂ x₀).symm z)) ((chartAt ℂ x₀).symm z)) ∘L
                tangentCoordChange 𝓘(ℝ, ℂ) ((chartAt ℂ x₀).symm z)
                  (sel ((chartAt ℂ x₀).symm z)) ((chartAt ℂ x₀).symm z)) ∘L
            (fderiv ℝ (chartAt ℂ ((chartAt ℂ x₀).symm z) ∘ (chartAt ℂ x₀).symm) z :
              ℂ →L[ℝ] ℂ) := by
  have := hD'.completeSpace
  set φ₀ := chartAt ℂ x₀
  set W := φ₀.target ∩ φ₀.symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)
  -- On the part `V a` of `W` covered by the charts at `a ∈ T` and `u a`, the weak derivative `D'`
  -- is obtained from `D a` by the changes of chart.
  set V : X → Set ℂ := fun a ↦ φ₀.target ∩ φ₀.symm ⁻¹'
    ((s ∩ (chartAt ℂ a).source) ∩ u ⁻¹' ((chartAt H y₀).source ∩ (chartAt H (u a)).source))
  have hpiece : ∀ a ∈ T, ∀ᵐ z, z ∈ (Opens.interior (V a) : Set ℂ) →
      tangentCoordChange I (u a) y₀ (u (φ₀.symm z)) ∘L D a (chartAt ℂ a (φ₀.symm z)) ∘L
        fderiv ℝ (chartAt ℂ a ∘ φ₀.symm) z = D' z := fun a _ ↦ by
    refine (ae_restrict_iff' (Opens.interior (V a)).isOpen.measurableSet).1
      ((hasWeakFDerivOn_extChartAt_comp_comp_chartAt_symm hs hc (hD a)).ae_eq
        (hD'.mono fun z hz ↦ interior_mono (fun w hw ↦ ?_) hz))
    exact ⟨hw.1, hw.2.1.1, hw.2.2.1⟩
  refine hD'.congr_ae_deriv ?_
  rw [EventuallyEq, ae_restrict_iff' (Opens.interior W).isOpen.measurableSet]
  filter_upwards [(ae_ball_iff hT).2 hpiece] with z hz hzW
  rw [coe_interior_chartAt_target_inter_preimage hs hc (chartAt H y₀).open_source] at hzW
  obtain ⟨haT, hxa, hua⟩ := hsel _ hzW.2.1
  have hzV : z ∈ (Opens.interior (V (sel (φ₀.symm z))) : Set ℂ) := by
    rw [coe_interior_chartAt_target_inter_preimage (hs.inter (chartAt ℂ _).open_source)
      (hc.mono inter_subset_left) ((chartAt H y₀).open_source.inter (chartAt H _).open_source)]
    exact ⟨hzW.1, ⟨hzW.2.1, hxa⟩, hzW.2.2, hua⟩
  rw [← hz _ haT hzV, fderiv_chartAt_comp_chartAt_symm hzW.1,
    fderiv_chartAt_comp_chartAt_symm hzW.1]
  exact (Manifold.tangentCoordChange_comp_comp_tangentCoordChange ⟨φ₀.map_target hzW.1, hxa⟩
    ⟨hzW.2.2, hua⟩ _).symm

/-- **Existence of the weak differential.** On a second countable Riemann surface, a local Sobolev
map `u ∈ W^{1,p}_loc(s, M)` on an open set `s` into a manifold without boundary has a weak
differential on `s`. -/
theorem MemWkpLocMapOn.exists_hasWeakMFDerivOn [SecondCountableTopology X]
    [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M] [I.Boundaryless]
    (hu : MemWkpLocMapOn I p 1 u s) (hs : IsOpen s) :
    ∃ Du : (x : X) → TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace I (u x),
      HasWeakMFDerivOn I u Du s := by
  have : IsManifold 𝓘(ℝ, ℂ) 1 X := IsManifold.restrictScalars_of_ne_zero 1 one_ne_zero ‹_›
  -- The coordinate expressions of `u` have weak derivatives in every pair of charts.
  have hex : ∀ (a : X) (b : M), ∃ D : ℂ → ℂ →L[ℝ] F, HasWeakFDerivOn volume
      (Opens.interior ((chartAt ℂ a).target ∩
        (chartAt ℂ a).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H b).source)))
      (extChartAt I b ∘ u ∘ (chartAt ℂ a).symm) D := fun a b ↦
    (memWkpLoc_succ_iff.1 (hu.memWkpLoc_chart (IsManifold.chart_mem_maximalAtlas a)
      (IsManifold.chart_mem_maximalAtlas b))).2.imp fun _ hD ↦ hD.1
  choose D hD using hex
  -- Glue those in the charts at `a` and `u a`, for countably many `a`, along changes of chart.
  obtain ⟨T, hT, sel, hsel⟩ := exists_countable_chartAt_selection (H := H) hs hu.continuousOn
  exact ⟨fun x ↦ (tangentCoordChange I (u (sel x)) (u x) (u x) ∘L
    D (sel x) (u (sel x)) (chartAt ℂ (sel x) x) ∘L tangentCoordChange 𝓘(ℝ, ℂ) x (sel x) x :
      ℂ →L[ℝ] F), fun x₀ y₀ ↦
    hasWeakFDerivOn_glue hs hu.continuousOn (fun a ↦ hD a (u a)) hT hsel (hD x₀ y₀)⟩

/-! ### Uniqueness -/

/-- **Uniqueness of the weak differential.** Two weak differentials of a map `u` continuous on an
open set `s` agree, in the chart at every point `x₀`, at almost every point of `s`. -/
theorem HasWeakMFDerivOn.ae_eq [IsManifold 𝓘(ℝ, ℂ) 1 X] [IsManifold I 1 M]
    (h : HasWeakMFDerivOn I u Du s) (h' : HasWeakMFDerivOn I u Du' s) (hs : IsOpen s)
    (hu : ContinuousOn u s) (x₀ : X) :
    ∀ᵐ z ∂volume.restrict ((chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' s),
      Du ((chartAt ℂ x₀).symm z) = Du' ((chartAt ℂ x₀).symm z) := by
  set φ₀ := chartAt ℂ x₀
  set W : M → Set ℂ := fun y₀ ↦ φ₀.target ∩ φ₀.symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)
  have hW : ∀ y₀, (Opens.interior (W y₀) : Set ℂ) = W y₀ := fun y₀ ↦
    coe_interior_chartAt_target_inter_preimage hs hu (chartAt H y₀).open_source x₀
  -- Countably many charts of `M` cover the image of `s`, seen from the chart at `x₀`.
  obtain ⟨T, hT, hTW⟩ := isOpen_iUnion_countable W fun y₀ ↦ hW y₀ ▸ (Opens.interior _).isOpen
  have hpiece : ∀ y₀ ∈ T, ∀ᵐ z, z ∈ W y₀ →
      tangentCoordChange I (u (φ₀.symm z)) y₀ (u (φ₀.symm z)) ∘L Du (φ₀.symm z) ∘L
          (fderiv ℝ (chartAt ℂ (φ₀.symm z) ∘ φ₀.symm) z : ℂ →L[ℝ] ℂ) =
        tangentCoordChange I (u (φ₀.symm z)) y₀ (u (φ₀.symm z)) ∘L Du' (φ₀.symm z) ∘L
          (fderiv ℝ (chartAt ℂ (φ₀.symm z) ∘ φ₀.symm) z : ℂ →L[ℝ] ℂ) := fun y₀ _ ↦ by
    have hae := (h x₀ y₀).ae_eq (h' x₀ y₀)
    rw [hW y₀] at hae
    exact (ae_restrict_iff' (hW y₀ ▸ (Opens.interior _).isOpen.measurableSet)).1 hae
  rw [ae_restrict_iff' (φ₀.isOpen_inter_preimage_symm hs).measurableSet]
  filter_upwards [(ae_ball_iff hT).2 hpiece] with z hz hzs
  have hzW : z ∈ ⋃ y₀ ∈ T, W y₀ := by
    rw [hTW]
    exact mem_iUnion.2 ⟨u (φ₀.symm z), hzs.1, hzs.2, mem_chart_source H _⟩
  obtain ⟨y₀, hy₀, hzy⟩ := mem_iUnion₂.1 hzW
  have hcoord := hz y₀ hy₀ hzy
  rw [fderiv_chartAt_comp_chartAt_symm hzs.1] at hcoord
  exact Manifold.eq_of_tangentCoordChange_comp_comp_eq (φ₀.map_target hzs.1) hzy.2.2 hcoord

/-- The coordinate expressions of a weak differential of a local Sobolev map
`u ∈ W^{1,p}_loc(s, M)` on an open set `s` are locally `Lᵖ`. -/
theorem HasWeakMFDerivOn.memLpLoc [IsManifold 𝓘(ℂ) 1 X] [IsManifold I ∞ M]
    (h : HasWeakMFDerivOn I u Du s) (hu : MemWkpLocMapOn I p 1 u s) (hs : IsOpen s) (x₀ : X)
    (y₀ : M) :
    MemLpLoc p ((chartAt ℂ x₀).target ∩
      (chartAt ℂ x₀).symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)) fun z ↦
      tangentCoordChange I (u ((chartAt ℂ x₀).symm z)) y₀ (u ((chartAt ℂ x₀).symm z)) ∘L
        Du ((chartAt ℂ x₀).symm z) ∘L
          (fderiv ℝ (chartAt ℂ ((chartAt ℂ x₀).symm z) ∘ (chartAt ℂ x₀).symm) z : ℂ →L[ℝ] ℂ) := by
  obtain ⟨-, D', hD', hD'L⟩ := memWkpLoc_succ_iff.1
    (hu.memWkpLoc_chart (IsManifold.chart_mem_maximalAtlas x₀)
      (IsManifold.chart_mem_maximalAtlas y₀))
  have hae := hD'.ae_eq (h x₀ y₀)
  rw [coe_interior_chartAt_target_inter_preimage hs hu.continuousOn (chartAt H y₀).open_source]
    at hae
  exact (memWkpLoc_zero_iff.1 hD'L).congr_ae hae

/-! ### Comparison with the differential -/

/-- **The differential of a `C¹` map is a weak differential.** If `u` is of class `C¹` on an open
set `s`, then its differential `mfderiv 𝓘(ℝ, ℂ) I u` is a weak differential of `u` on `s`. -/
theorem _root_.ContMDiffOn.hasWeakMFDerivOn_mfderiv [IsManifold 𝓘(ℝ, ℂ) 1 X] [IsManifold I 1 M]
    [CompleteSpace F] (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s) (hs : IsOpen s) :
    HasWeakMFDerivOn I u (mfderiv 𝓘(ℝ, ℂ) I u) s := fun x₀ y₀ ↦ by
  set φ₀ := chartAt ℂ x₀
  set W := φ₀.target ∩ φ₀.symm ⁻¹' (s ∩ u ⁻¹' (chartAt H y₀).source)
  have hW : (Opens.interior W : Set ℂ) = W :=
    coe_interior_chartAt_target_inter_preimage hs hu.continuousOn (chartAt H y₀).open_source x₀
  -- The coordinate expression of `u` is `C¹`, so its derivative is a weak derivative.
  have hf : ContDiffOn ℝ 1 (extChartAt I y₀ ∘ u ∘ φ₀.symm) (Opens.interior W) := by
    rw [hW]
    exact contMDiffOn_iff_contDiffOn.1 (contMDiffOn_extChartAt.comp
      (hu.comp (contMDiffOn_chart_symm.mono inter_subset_left) fun _ hz ↦ hz.2.1)
      fun _ hz ↦ hz.2.2)
  refine hf.hasWeakFDerivOn_fderiv.congr_ae_deriv
    (ae_restrict_of_forall_mem (Opens.interior W).isOpen.measurableSet fun z hz ↦ ?_)
  rw [hW] at hz
  -- The derivative of the coordinate expression is the differential read in the two charts.
  have hd := ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm (I := 𝓘(ℝ, ℂ)) (I' := I)
    (hu.continuousOn.continuousAt (hs.mem_nhds hz.2.1)) (β := x₀) (α := y₀)
    (by simpa using φ₀.map_target hz.1) (by simpa using hz.2.2)
  -- The differential is a map between the model spaces `ℂ` and `F` of the tangent spaces.
  obtain ⟨D, hD⟩ : ∃ D : ℂ →L[ℝ] F, D = mfderiv 𝓘(ℝ, ℂ) I u (φ₀.symm z) := ⟨_, rfl⟩
  rw [← hD, ← fderiv_chartAt_comp_chartAt_symm hz.1] at hd
  simp only [φ₀, extChartAt_coe (I := 𝓘(ℝ, ℂ)), extChartAt_coe_symm (I := 𝓘(ℝ, ℂ)),
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id, range_id,
    fderivWithin_univ, Function.comp_apply, id_eq, (chartAt ℂ x₀).right_inv hz.1] at hd
  subst hD
  exact hd

/-- **A weak differential of a `C¹` map is its differential.** If `u` is of class `C¹` on an open
set `s`, then a weak differential of `u` on `s` agrees, in the chart at every point `x₀`, at almost
every point of `s` with the differential `mfderiv 𝓘(ℝ, ℂ) I u`. -/
theorem HasWeakMFDerivOn.ae_eq_mfderiv [IsManifold 𝓘(ℝ, ℂ) 1 X] [IsManifold I 1 M]
    (h : HasWeakMFDerivOn I u Du s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s) (hs : IsOpen s) (x₀ : X) :
    ∀ᵐ z ∂volume.restrict ((chartAt ℂ x₀).target ∩ (chartAt ℂ x₀).symm ⁻¹' s),
      Du ((chartAt ℂ x₀).symm z) = mfderiv 𝓘(ℝ, ℂ) I u ((chartAt ℂ x₀).symm z) :=
  have := (h x₀ (u x₀)).completeSpace
  h.ae_eq (hu.hasWeakMFDerivOn_mfderiv hs) hs hu.continuousOn x₀

end TauCeti
