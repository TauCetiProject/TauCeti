/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Topology.Algebra.GroupAction.FreeLocus

/-!
# Quotient manifolds of free properly discontinuous actions

Mathlib equips the orbit space of a free, properly discontinuous action on a charted space with
charts pushed forward along the orbit projection (`MulAction.instChartedSpaceQuotient`). This file
proves that for an action by `C^n` maps on a `C^n` manifold these charts form a `C^n` manifold,
and that the orbit projection is a `C^n` local diffeomorphism.

The argument is local and applies to any surjective local homeomorphism `f : M → M'` with the
pushed-forward charts `IsLocalHomeomorph.chartedSpaceOfRightInverse`. The only input is that
`f` has `C^n` local deck transformations: whenever `f z = f w`, some map that is `C^n` at `z`
sends `z` to `w` and commutes with `f` near `z`. Then every composite of a local inverse of `f`
with `f` is locally such a map, so the transition maps of the pushed-forward atlas are `C^n`
maps of `M` read in charts of `M`. For an orbit projection the deck transformations are the
group elements themselves.

A properly discontinuous action that is not free is free on its free locus `TauCeti.freeLocus`,
an open invariant subset. The free locus inherits the charts of the ambient manifold and the
`C^n` action, so the results above make its orbit space a `C^n` manifold by instance search.

## Main results

* `IsLocalHomeomorph.isManifold_chartedSpaceOfRightInverse`,
  `IsLocalHomeomorph.contMDiff_chartedSpaceOfRightInverse`,
  `IsLocalHomeomorph.isLocalDiffeomorph_chartedSpaceOfRightInverse`: the pushed-forward charts
  of a local homeomorphism with `C^n` local deck transformations form a `C^n` manifold, for which
  the map is a `C^n` local diffeomorphism.
* `TauCeti.instIsManifoldQuotient`: the orbit space of a free, properly discontinuous action by
  `C^n` maps on a `C^n` manifold is a `C^n` manifold.
* `TauCeti.contMDiff_quotientMk` and `TauCeti.isLocalDiffeomorph_quotientMk`: the orbit
  projection is a `C^n` local diffeomorphism.
* `TauCeti.freeLocus.instChartedSpace`, `TauCeti.freeLocus.instIsManifold` and
  `TauCeti.freeLocus.instContMDiffConstSMul`: the free locus of a properly discontinuous action
  is an open submanifold on which the group acts by `C^n` maps.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

open Set Filter Topology IsManifold
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}

namespace IsLocalHomeomorph

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M']
  {f : M → M'} (hf : IsLocalHomeomorph f)

include hf in
/-- If `f` has `C^n` local deck transformations, then a local inverse of `f` composed with `f` is
`C^n` wherever it is defined. -/
private theorem contMDiffAt_localInverseAt_comp
    (hdeck : ∀ z w, f z = f w → ∃ φ : M → M, ContMDiffAt I I n φ z ∧ φ z = w ∧ f ∘ φ =ᶠ[𝓝 z] f)
    {x z : M} (hz : f z ∈ (hf.localInverseAt x).source) :
    ContMDiffAt I I n (hf.localInverseAt x ∘ f) z := by
  set L := hf.localInverseAt x
  obtain ⟨φ, hφ, hφz, hfφ⟩ := hdeck z (L (f z)) (hf.apply_localInverseAt_of_mem hz).symm
  have hmem : ∀ᶠ z' in 𝓝 z, φ z' ∈ L.target :=
    hφ.continuousAt.preimage_mem_nhds (hφz ▸ L.open_target.mem_nhds (L.map_source hz))
  refine hφ.congr_of_eventuallyEq ?_
  filter_upwards [hmem, hfφ] with z' hz' hfz'
  have hL : L (L.symm (φ z')) = φ z' := L.right_inv hz'
  rw [hf.localInverseAt_symm] at hL
  simpa [← hfz'] using hL

variable {g : M' → M} (hg : Function.RightInverse g f)

/-- The charts that a local homeomorphism `f` with `C^n` local deck transformations pushes forward
from a `C^n` manifold form a `C^n` manifold. -/
theorem isManifold_chartedSpaceOfRightInverse [IsManifold I n M]
    (hdeck : ∀ z w, f z = f w → ∃ φ : M → M, ContMDiffAt I I n φ z ∧ φ z = w ∧ f ∘ φ =ᶠ[𝓝 z] f) :
    letI := hf.chartedSpaceOfRightInverse (H := H) hg
    IsManifold I n M' := by
  let := hf.chartedSpaceOfRightInverse (H := H) hg
  refine isManifold_of_contDiffOn I n M' ?_
  rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩ u hu
  set La := hf.localInverseAt (g p)
  set Lb := hf.localInverseAt (g q)
  set φa := chartAt H (g p)
  set φb := chartAt H (g q)
  have hLa : ⇑La.symm = f := hf.localInverseAt_symm _
  obtain ⟨⟨⟨hva, -⟩, hvLb, hvφb⟩, huI⟩ : ((I.symm u ∈ φa.target ∧ φa.symm (I.symm u) ∈ La.target) ∧
      f (φa.symm (I.symm u)) ∈ Lb.source ∧ Lb (f (φa.symm (I.symm u))) ∈ φb.source) ∧
      u ∈ range I := by
    simpa only [mfld_simps, hLa] using hu
  set z := φa.symm (I.symm u)
  have hz : z ∈ φa.source := φa.map_target hva
  have key := (contMDiffAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas (g p))
    (chart_mem_maximalAtlas (g q)) hz hvφb).1
    (contMDiffAt_localInverseAt_comp hf hdeck hvLb) |>.2
  have hu' : φa.extend I z = u := by
    simp [z, φa.right_inv hva, I.right_inv huI]
  rw [hu'] at key
  refine (key.mono inter_subset_right).congr_of_mem (fun y _ ↦ ?_) hu
  simp only [mfld_simps, hLa]
  -- the two sides agree once the `set` abbreviations `La`, `Lb`, `φa`, `φb` are unfolded
  rfl

/-- A local homeomorphism with `C^n` local deck transformations is `C^n` for the charts it pushes
forward from a `C^n` manifold. -/
theorem contMDiff_chartedSpaceOfRightInverse [IsManifold I n M]
    (hdeck : ∀ z w, f z = f w → ∃ φ : M → M, ContMDiffAt I I n φ z ∧ φ z = w ∧ f ∘ φ =ᶠ[𝓝 z] f) :
    letI := hf.chartedSpaceOfRightInverse (H := H) hg
    ContMDiff I I n f := by
  let := hf.chartedSpaceOfRightInverse (H := H) hg
  have := hf.isManifold_chartedSpaceOfRightInverse hg hdeck
  intro z
  have hz : f z ∈ (chartAt H (f z)).source := mem_chart_source H (f z)
  obtain ⟨hzL, hzφ⟩ := hz
  have key := (contMDiffAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas z)
    (chart_mem_maximalAtlas (g (f z))) (mem_chart_source H z) hzφ).1
    (contMDiffAt_localInverseAt_comp hf hdeck hzL) |>.2
  exact (contMDiffAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas z)
    (chart_mem_maximalAtlas (f z)) (mem_chart_source H z) (mem_chart_source H (f z))).2
    ⟨hf.continuous.continuousAt, key⟩

include hg in
/-- A local inverse of a local homeomorphism with `C^n` local deck transformations is `C^n` on its
source, for the charts the map pushes forward from a `C^n` manifold. -/
private theorem contMDiffOn_localInverseAt [IsManifold I n M]
    (hdeck : ∀ z w, f z = f w → ∃ φ : M → M, ContMDiffAt I I n φ z ∧ φ z = w ∧ f ∘ φ =ᶠ[𝓝 z] f)
    (x : M) :
    letI := hf.chartedSpaceOfRightInverse (H := H) hg
    ContMDiffOn I I n (hf.localInverseAt x) (hf.localInverseAt x).source := by
  let := hf.chartedSpaceOfRightInverse (H := H) hg
  have := hf.isManifold_chartedSpaceOfRightInverse hg hdeck
  intro y hy
  refine ContMDiffAt.contMDiffWithinAt ?_
  set L := hf.localInverseAt x
  set La := hf.localInverseAt (g y)
  set φa := chartAt H (g y)
  have hyc : y ∈ (chartAt H y).source := mem_chart_source H y
  have hyLa : y ∈ La.source := hyc.1
  -- `La` is the chart at `y` followed by the inverse of the chart `φa` of `M`.
  have hLa : ContMDiffAt I I n La y := by
    have hc := (contMDiffAt_symm_of_mem_maximalAtlas
      (chart_mem_maximalAtlas (I := I) (n := n) (g y)) (φa.map_source hyc.2)).comp y
      (contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (I := I) (n := n) y) hyc)
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [(chartAt H y).open_source.mem_nhds hyc] with y' hy'
    exact (φa.left_inv hy'.2).symm
  -- Near `y`, the local inverse `L` factors through `La` as `(L ∘ f) ∘ La`.
  have hLf : ContMDiffAt I I n (L ∘ f) (La y) :=
    contMDiffAt_localInverseAt_comp hf hdeck (by rwa [hf.apply_localInverseAt_of_mem hyLa])
  refine (hLf.comp y hLa).congr_of_eventuallyEq ?_
  filter_upwards [La.open_source.mem_nhds hyLa] with y' hy'
  exact congrArg L (hf.apply_localInverseAt_of_mem hy').symm

/-- A local homeomorphism with `C^n` local deck transformations is a `C^n` local diffeomorphism
for the charts it pushes forward from a `C^n` manifold. -/
theorem isLocalDiffeomorph_chartedSpaceOfRightInverse [IsManifold I n M]
    (hdeck : ∀ z w, f z = f w → ∃ φ : M → M, ContMDiffAt I I n φ z ∧ φ z = w ∧ f ∘ φ =ᶠ[𝓝 z] f) :
    letI := hf.chartedSpaceOfRightInverse (H := H) hg
    IsLocalDiffeomorph I I n f := by
  let := hf.chartedSpaceOfRightInverse (H := H) hg
  intro x
  set L := hf.localInverseAt x
  have hLs : ⇑L.symm = f := hf.localInverseAt_symm x
  let Φ : PartialDiffeomorph I I M M' n :=
    { toPartialEquiv := L.symm.toPartialEquiv.copy f hLs L rfl L.target rfl L.source rfl
      open_source := L.open_target
      open_target := L.open_source
      contMDiffOn_toFun := (hf.contMDiff_chartedSpaceOfRightInverse hg hdeck).contMDiffOn
      contMDiffOn_invFun := hf.contMDiffOn_localInverseAt hg hdeck x }
  exact Φ.isLocalDiffeomorphAt I I n hf.self_mem_localInverseAt_target

end IsLocalHomeomorph

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {G : Type*} [Group G]
  [MulAction G M]

section Quotient

variable [ContMDiffConstSMul I n G M]

/-- Two points in one orbit are related by the action of a group element, a `C^n` deck
transformation of the orbit projection. -/
private theorem quotientMk_deck (z w : M)
    (h : (Quotient.mk (MulAction.orbitRel G M) z) = Quotient.mk (MulAction.orbitRel G M) w) :
    ∃ φ : M → M, ContMDiffAt I I n φ z ∧ φ z = w ∧
      Quotient.mk (MulAction.orbitRel G M) ∘ φ =ᶠ[𝓝 z] Quotient.mk (MulAction.orbitRel G M) := by
  obtain ⟨γ, hγ⟩ := Quotient.exact h.symm
  exact ⟨(γ • ·), (contMDiff_const_smul γ).contMDiffAt, hγ,
    Eventually.of_forall fun x ↦ Quotient.sound ⟨γ, rfl⟩⟩

variable [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M] [T2Space M]
  [LocallyCompactSpace M]

/-- The orbit space of a free, properly discontinuous action by `C^n` maps on a `C^n` manifold is a
`C^n` manifold, for the charts pushed forward along the orbit projection. -/
instance instIsManifoldQuotient [IsManifold I n M] :
    IsManifold I n (MulAction.orbitRel.Quotient G M) :=
  (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G) (E := M)).isCoveringMap
    |>.isLocalHomeomorph |>.isManifold_chartedSpaceOfRightInverse
      Quotient.mk_surjective.hasRightInverse.choose_spec (quotientMk_deck (G := G) (M := M))

/-- The orbit projection of a free, properly discontinuous action by `C^n` maps on a `C^n` manifold
is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_quotientMk [IsManifold I n M] :
    IsLocalDiffeomorph I I n (Quotient.mk (MulAction.orbitRel G M)) :=
  (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G) (E := M)).isCoveringMap
    |>.isLocalHomeomorph |>.isLocalDiffeomorph_chartedSpaceOfRightInverse
      Quotient.mk_surjective.hasRightInverse.choose_spec (quotientMk_deck (G := G) (M := M))

/-- The orbit projection of a free, properly discontinuous action by `C^n` maps on a `C^n` manifold
is `C^n`. -/
theorem contMDiff_quotientMk [IsManifold I n M] :
    ContMDiff I I n (Quotient.mk (MulAction.orbitRel G M)) :=
  isLocalDiffeomorph_quotientMk.contMDiff

end Quotient

/-! ### The free locus -/

namespace freeLocus

variable [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [T2Space M]
  [LocallyCompactSpace M]

/-- The free locus of a properly discontinuous action is open, so it inherits the charts of the
ambient charted space. -/
noncomputable instance instChartedSpace : ChartedSpace H (freeLocus G M) :=
  inferInstanceAs (ChartedSpace H (⟨_, isOpen_freeLocus G M⟩ : TopologicalSpace.Opens M))

/-- The free locus of a properly discontinuous action on a `C^n` manifold is a `C^n` manifold. -/
instance instIsManifold [IsManifold I n M] : IsManifold I n (freeLocus G M) :=
  inferInstanceAs (IsManifold I n (⟨_, isOpen_freeLocus G M⟩ : TopologicalSpace.Opens M))

/-- An action by `C^n` maps restricts to an action by `C^n` maps on the free locus. -/
instance instContMDiffConstSMul [ContMDiffConstSMul I n G M] :
    ContMDiffConstSMul I n G (freeLocus G M) where
  contMDiff_const_smul γ := by
    let U : TopologicalSpace.Opens M := ⟨_, isOpen_freeLocus G M⟩
    have h : ContMDiff I I n
        (Subtype.val ∘ fun x : U ↦ (⟨γ • (x : M), (freeLocus G M).smul_mem γ x.2⟩ : U)) :=
      (contMDiff_const_smul γ).comp contMDiff_subtype_val
    exact fun x ↦ (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1 (h x)

end freeLocus

end TauCeti
