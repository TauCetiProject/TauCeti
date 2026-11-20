/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.Symmetric
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The bundle of `r`-jets of a vector bundle

For a `C^r` vector bundle `V → M` with model fibre `F` over a boundaryless `C^r` manifold modelled
on `E`, over `ℝ` or `ℂ`, the jet bundle `JᵣV` records the value and the derivatives up to order
`r` of local sections. We construct it as a vector bundle with fibre the symmetric `r`-jets
`TauCeti.SymmetricJet 𝕜 E F r`, the tuples `(A₀, …, Aᵣ)` of symmetric continuous multilinear maps
`Aₖ : E [×k]→L[𝕜] F`. Over the domain of the preferred chart `φᵢ` of `M` and the preferred
trivialization `eᵢ` of `V` at a point `i`, the `r`-jet of a section `s` at `y` is the tuple of
iterated derivatives at `φᵢ y` of its local representative `z ↦ eᵢ (s (φᵢ⁻¹ z))`. Changing from
`i` to `j` transforms these tuples by the higher-order chain and Leibniz rules for the change of
charts and the coordinate change of `V`, which are the coordinate changes of symmetric jets
`TauCeti.symmetricJetCoordChange`.

Iterated derivatives are taken in the model space itself, not within the range of the model with
corners, so the base is assumed boundaryless. The symmetry of iterated derivatives of `C^r` maps
holds over `ℝ` and `ℂ`, which is why the field is `RCLike`.

## Main definitions and results

* `TauCeti.JetBundle.coordChange`: the `r`-jet coordinate changes. They satisfy the identity and
  cocycle laws (`TauCeti.JetBundle.coordChange_self_apply`,
  `TauCeti.JetBundle.coordChange_comp_apply`), and they are `C^n` when `V` and `M` are `C^(n+r)`
  (`TauCeti.JetBundle.contMDiffOn_coordChange`).
* `TauCeti.jetBundleCore` and `TauCeti.JetBundle`: the vector bundle core and the jet bundle
  itself, a `C^n` vector bundle when `V` and `M` are `C^(n+r)`
  (`TauCeti.JetBundle.contMDiffVectorBundle`).
* `TauCeti.JetBundle.jet`: the `r`-jet `jʳs(x)` of a section. For a section that is `C^r` at the
  point, its components are the iterated derivatives of the local representative
  (`TauCeti.JetBundle.coeFn_jet`), in every chart (`TauCeti.JetBundle.coeFn_trivializationAt_jet`),
  and it is a `C^n` section of `JᵣV` for a `C^(n+r)` section `s`
  (`TauCeti.JetBundle.contMDiff_jet`). For the trivial bundle over a model space the components
  are the iterated derivatives of the section (`TauCeti.JetBundle.coeFn_jet_trivial`). Every jet
  is the jet of a section which is `C^n` at the base point, for any `n`
  (`TauCeti.JetBundle.exists_contMDiffAt_jet_eq`).
* `TauCeti.JetBundle.truncate`: the truncation `JᵣV → Jᵣ'V` for `r' ≤ r`, which reads in every
  chart as the truncation of tuples (`TauCeti.JetBundle.coordChange_truncate`) and sends `jʳs(x)`
  to `jʳ's(x)` (`TauCeti.JetBundle.truncate_jet`).
* `TauCeti.JetBundle.value`: the projection `JᵣV → V`, which sends `jʳs(x)` to `s x`
  (`TauCeti.JetBundle.value_jet`).

The construction follows `TauCeti.firstJetBundleCore`: the bundle is indexed by the points of `M`,
and the chart domains are the domains `TauCeti.FirstJetBundle.baseSet` of both the preferred chart
of `M` and the preferred trivialization of `V`.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.2–12.5 and 12.16–12.17.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommMonoid (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  (r : ℕ)

namespace JetBundle

open FirstJetBundle

/-- The change of `r`-jet coordinates at `y` from the chart and trivialization at `i` to the
ones at `j`: the coordinate change of symmetric jets for the change of charts
`φᵢ ∘ φⱼ⁻¹` and the coordinate change of `V` written in the chart at `j`. -/
def coordChange (i j y : M) : SymmetricJet 𝕜 E F r →L[𝕜] SymmetricJet 𝕜 E F r :=
  symmetricJetCoordChange r (extChartAt I i ∘ (extChartAt I j).symm)
    (fiberCoordChange I F V i j) (extChartAt I j y)

variable {I F V}

omit [NormedSpace 𝕜 F] [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V] in
/-- Near the image of a point of the first-jet chart domain at `i` that lies in the chart domain
at `j`, the inverse of the extended chart at `j` lands in the first-jet chart domain at `i`. On a
boundaryless manifold this is a neighbourhood statement. -/
private theorem eventually_extChartAt_symm_mem_baseSet {i j y : M}
    (hi : y ∈ baseSet (H := H) F V i) (hj : y ∈ (chartAt H j).source) :
    ∀ᶠ z in 𝓝 (extChartAt I j y), (extChartAt I j).symm z ∈ baseSet (H := H) F V i := by
  simpa [I.range_eq_univ] using FirstJetBundle.eventually_extChartAt_symm_mem_baseSet I hi hj

/-- The coordinate change of `V` from `i` to `j`, written in the chart at `j`, is `C^n` at the
image of a point of the domains. -/
private theorem contDiffAt_fiberCoordChange {n : ℕ∞ω} [IsManifold I n M]
    [ContMDiffVectorBundle n F V I] {i j y : M} (hi : y ∈ (trivializationAt F V i).baseSet)
    (hj : y ∈ baseSet (H := H) F V j) :
    ContDiffAt 𝕜 n (fiberCoordChange I F V i j) (extChartAt I j y) := by
  have h := contDiffWithinAt_fiberCoordChange (I := I) (n := n) hi hj
  rwa [I.range_eq_univ, contDiffWithinAt_univ] at h

/-- The `r`-jet coordinate changes of a `C^(n+r)` vector bundle over a boundaryless `C^(n+r)`
manifold are `C^n`. -/
theorem contMDiffOn_coordChange {n : ℕ∞ω} [IsManifold I (n + r) M]
    [ContMDiffVectorBundle (n + r) F V I] (i j : M) :
    ContMDiffOn I 𝓘(𝕜, SymmetricJet 𝕜 E F r →L[𝕜] SymmetricJet 𝕜 E F r) n
      (coordChange I F V r i j) (baseSet (H := H) F V i ∩ baseSet (H := H) F V j) := by
  have : IsManifold I n M := .of_le (n := n + r) le_self_add
  set U := baseSet (H := H) F V i ∩ baseSet (H := H) F V j
  have hUj : U ⊆ (chartAt H j).source := fun y hy ↦ ((mem_baseSet_iff F V).1 hy.2).2
  -- The overlap, read in the chart at `j`: an open set on which both coordinate maps are smooth.
  set T := (extChartAt I j).target ∩ (extChartAt I j).symm ⁻¹' U
  have hT : IsOpen T := (continuousOn_extChartAt_symm j).isOpen_inter_preimage
    (isOpen_extChartAt_target j) ((isOpen_baseSet F V i).inter (isOpen_baseSet F V j))
  have hTy : ∀ z ∈ T, extChartAt I j ((extChartAt I j).symm z) = z := fun z hz ↦
    (extChartAt I j).right_inv hz.1
  have hh : ContDiffOn 𝕜 (n + r) (extChartAt I i ∘ (extChartAt I j).symm) T := fun z hz ↦ by
    have h := contDiffAt_ext_coord_change_extChartAt (I := I) (n := n + r)
      ((mem_baseSet_iff F V).1 hz.2.1).2 ((mem_baseSet_iff F V).1 hz.2.2).2
    rw [hTy z hz] at h
    exact h.contDiffWithinAt
  have hg : ContDiffOn 𝕜 (n + r) (fiberCoordChange I F V i j) T := fun z hz ↦ by
    have h := contDiffAt_fiberCoordChange (I := I) (n := n + r)
      ((mem_baseSet_iff F V).1 hz.2.1).1 hz.2.2
    rw [hTy z hz] at h
    exact h.contDiffWithinAt
  have hmaps : MapsTo (extChartAt I j) U T := fun y hy ↦ by
    have hy' := mem_extChartAt_source_of_mem_baseSet I hy.2
    exact ⟨(extChartAt I j).map_source hy', by rwa [mem_preimage, (extChartAt I j).left_inv hy']⟩
  exact (contMDiffOn_iff_contDiffOn.2 (hT.contDiffOn_iff.2 fun z hz ↦
    (hh.symmetricJetCoordChange hT hg le_rfl).contDiffAt (hT.mem_nhds hz)
      |>.contDiffWithinAt)).comp (contMDiffOn_extChartAt.mono hUj) hmaps

/-- The `r`-jet coordinate change from a chart to itself is the identity. -/
theorem coordChange_self_apply {i y : M} (hy : y ∈ baseSet (H := H) F V i)
    (v : SymmetricJet 𝕜 E F r) : coordChange I F V r i i y v = v := by
  have hy' := mem_extChartAt_source_of_mem_baseSet I hy
  have hh : extChartAt I i ∘ (extChartAt I i).symm =ᶠ[𝓝 (extChartAt I i y)] id := by
    filter_upwards [extChartAt_target_mem_nhds' ((extChartAt I i).map_source hy')] with z hz
    exact (extChartAt I i).right_inv hz
  have hg : fiberCoordChange I F V i i =ᶠ[𝓝 (extChartAt I i y)]
      fun _ ↦ ContinuousLinearMap.id 𝕜 F := by
    filter_upwards [eventually_extChartAt_symm_mem_baseSet hy ((mem_baseSet_iff F V).1 hy).2]
      with z hz
    ext w
    rw [fiberCoordChange_apply]
    exact (trivializationAt F V i).coordChangeL_same_apply 𝕜 ((mem_baseSet_iff F V).1 hz).1 w
  rw [coordChange, symmetricJetCoordChange_congr hh hg, symmetricJetCoordChange_id]
  rfl

variable [IsManifold I r M] [ContMDiffVectorBundle r F V I]

/-- **Cocycle law for `r`-jet coordinate changes**. -/
theorem coordChange_comp_apply {i j k y : M} (hi : y ∈ baseSet (H := H) F V i)
    (hj : y ∈ baseSet (H := H) F V j) (hk : y ∈ baseSet (H := H) F V k)
    (v : SymmetricJet 𝕜 E F r) :
    coordChange I F V r j k y (coordChange I F V r i j y v) = coordChange I F V r i k y v := by
  have hk' := mem_extChartAt_source_of_mem_baseSet I hk
  rw [mem_baseSet_iff] at hi hj hk
  have hpt : extChartAt I j y = (extChartAt I j ∘ (extChartAt I k).symm) (extChartAt I k y) := by
    rw [Function.comp_apply, (extChartAt I k).left_inv hk']
  have hn : minSmoothness 𝕜 r ≤ r := by simp
  -- Compose the two coordinate changes of symmetric jets.
  have hcomp := symmetricJetCoordChange_comp (r := r) (n := r)
    (hpt ▸ contDiffAt_ext_coord_change_extChartAt (I := I) hi.2 hj.2)
    (hpt ▸ contDiffAt_fiberCoordChange (I := I) hi.1 ((mem_baseSet_iff F V).2 hj)) hn
    (contDiffAt_ext_coord_change_extChartAt (I := I) hj.2 hk.2)
    (contDiffAt_fiberCoordChange (I := I) hj.1 ((mem_baseSet_iff F V).2 hk))
  rw [coordChange, coordChange, hpt, ← ContinuousLinearMap.comp_apply, hcomp, coordChange]
  -- The composite coordinate maps agree with those from `i` to `k` near the image of `y`.
  congr 1
  refine symmetricJetCoordChange_congr ?_ ?_
  · filter_upwards [eventually_extChartAt_symm_mem_baseSet ((mem_baseSet_iff F V).2 hj) hk.2]
      with z hz
    simp only [Function.comp_apply,
      (extChartAt I j).left_inv (mem_extChartAt_source_of_mem_baseSet I hz)]
  · filter_upwards [eventually_extChartAt_symm_mem_baseSet ((mem_baseSet_iff F V).2 hi) hk.2,
      eventually_extChartAt_symm_mem_baseSet ((mem_baseSet_iff F V).2 hj) hk.2,
      eventually_extChartAt_symm_mem_baseSet ((mem_baseSet_iff F V).2 hk) hk.2]
      with z hzi hzj hzk
    ext w
    simp only [fiberCoordChange_apply, Function.comp_apply, ContinuousLinearMap.coe_comp,
      (extChartAt I j).left_inv (mem_extChartAt_source_of_mem_baseSet I hzj)]
    rw [mem_baseSet_iff] at hzi hzj hzk
    exact (trivializationAt F V i).coordChangeL_coordChangeL_apply 𝕜 _ _ hzi.1 hzj.1 hzk.1 w

end JetBundle

section

variable [IsManifold I r M] [ContMDiffVectorBundle r F V I]

/-- The vector bundle core of the bundle of `r`-jets of `V`, indexed by the points of `M`. Over
the chart at `i`, an `r`-jet is described by the iterated derivatives up to order `r` of the local
representative of a section in the preferred trivialization of `V` at `i`. -/
def jetBundleCore : VectorBundleCore 𝕜 M (SymmetricJet 𝕜 E F r) M where
  baseSet := FirstJetBundle.baseSet F V
  isOpen_baseSet := FirstJetBundle.isOpen_baseSet F V
  indexAt := id
  mem_baseSet_at := FirstJetBundle.mem_baseSet_self F V
  coordChange := JetBundle.coordChange I F V r
  coordChange_self _ _ hy v := JetBundle.coordChange_self_apply r hy v
  continuousOn_coordChange i j := by
    have : IsManifold I (0 + r) M := by simpa
    have : ContMDiffVectorBundle (0 + r) F V I := by simpa
    exact (JetBundle.contMDiffOn_coordChange r (n := 0) i j).continuousOn
  coordChange_comp _ _ _ _ hy v := JetBundle.coordChange_comp_apply r hy.1.1 hy.1.2 hy.2 v

/-- The `r`-jet chart domains are the domains `FirstJetBundle.baseSet`. -/
@[simp]
theorem jetBundleCore_baseSet :
    (jetBundleCore I F V r).baseSet = FirstJetBundle.baseSet (H := H) F V := (rfl)

/-- The `r`-jet chart at a point is the one indexed by that point. -/
@[simp]
theorem jetBundleCore_indexAt (x : M) : (jetBundleCore I F V r).indexAt x = x := (rfl)

/-- The coordinate changes of `jetBundleCore` are `JetBundle.coordChange`. -/
@[simp]
theorem jetBundleCore_coordChange :
    (jetBundleCore I F V r).coordChange = JetBundle.coordChange I F V r := (rfl)

/-- The bundle `JᵣV` of `r`-jets of a vector bundle `V`. Its fibre over `x` is the space of
symmetric jets `SymmetricJet 𝕜 E F r`, read as the iterated derivatives up to order `r` of the
local representative of a section in the preferred chart of `M` and the preferred trivialization
of `V` at `x`. -/
abbrev JetBundle : M → Type _ :=
  (jetBundleCore I F V r).Fiber

/-- An `r`-jet is a tuple of continuous multilinear maps; `j k` is its component of order `k`, in
the chart and trivialization at its base point. -/
instance JetBundle.instCoeFun (x : M) :
    CoeFun (JetBundle I F V r x) fun _ ↦ (k : Fin (r + 1)) → E [×k]→L[𝕜] F :=
  ⟨fun j ↦ SymmetricJet.subtypeL 𝕜 E F r j⟩

/-- The components of an `r`-jet are its components as a symmetric jet. -/
theorem JetBundle.coeFn_eq {x : M} (j : JetBundle I F V r x) :
    ⇑j = SymmetricJet.subtypeL 𝕜 E F r j :=
  (rfl)

end

/-- The vector bundle core of the bundle of `r`-jets of a `C^(n+r)` vector bundle over a
boundaryless `C^(n+r)` manifold has `C^n` coordinate changes. -/
theorem jetBundleCore_isContMDiff {n : ℕ∞ω} [IsManifold I (n + r) M]
    [ContMDiffVectorBundle (n + r) F V I] :
    haveI : IsManifold I r M := .of_le (n := n + r) le_add_self
    haveI : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
    (jetBundleCore I F V r).IsContMDiff I n :=
  ⟨JetBundle.contMDiffOn_coordChange r⟩

/-- The bundle of `r`-jets of a `C^(n+r)` vector bundle over a boundaryless `C^(n+r)` manifold is
a `C^n` vector bundle. -/
theorem JetBundle.contMDiffVectorBundle {n : ℕ∞ω} [IsManifold I (n + r) M]
    [ContMDiffVectorBundle (n + r) F V I] :
    haveI : IsManifold I r M := .of_le (n := n + r) le_add_self
    haveI : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
    ContMDiffVectorBundle n (SymmetricJet 𝕜 E F r) (JetBundle I F V r) I := by
  have : IsManifold I r M := .of_le (n := n + r) le_add_self
  have : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
  have := jetBundleCore_isContMDiff I F V r (n := n)
  exact (jetBundleCore I F V r).instContMDiffVectorBundle

/-- The bundle of `r`-jets of a smooth vector bundle over a boundaryless smooth manifold is
smooth. -/
instance [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I] :
    ContMDiffVectorBundle ∞ (SymmetricJet 𝕜 E F r) (JetBundle I F V r) I := by
  have hr : (∞ : ℕ∞ω) + r = ∞ := by norm_cast
  have : IsManifold I (∞ + r) M := by rw [hr]; infer_instance
  have : ContMDiffVectorBundle (∞ + r) F V I := by rw [hr]; infer_instance
  exact JetBundle.contMDiffVectorBundle I F V r

/-- The bundle of `r`-jets of an analytic vector bundle over a boundaryless analytic manifold is
analytic. -/
instance [IsManifold I ω M] [ContMDiffVectorBundle ω F V I] :
    ContMDiffVectorBundle ω (SymmetricJet 𝕜 E F r) (JetBundle I F V r) I := by
  have hr : (ω : ℕ∞ω) + r = ω := by simp
  have : IsManifold I (ω + r) M := by rw [hr]; infer_instance
  have : ContMDiffVectorBundle (ω + r) F V I := by rw [hr]; infer_instance
  exact JetBundle.contMDiffVectorBundle I F V r

namespace JetBundle

open FirstJetBundle

variable {I F V r}

section Jet

variable [IsManifold I r M] [ContMDiffVectorBundle r F V I]

/-- In the chart and trivialization at `i`, the local representative of a section that is `C^n`
at a point `y` of the first-jet chart domain at `i` is `C^n` at the image of `y`. -/
private theorem contDiffAt_localRep {n : ℕ∞ω} [IsManifold I n M] [ContMDiffVectorBundle n F V I]
    {s : ∀ x, V x} {i y : M}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) y)
    (hi : y ∈ baseSet (H := H) F V i) :
    ContDiffAt 𝕜 n (localRep I F s i) (extChartAt I i y) := by
  have h := contDiffWithinAt_localRep I F hs hi
  rwa [I.range_eq_univ, contDiffWithinAt_univ] at h

variable (I F r) in
/-- The `r`-jet `jʳs(x)` of a section `s` of `V` at `x`: the iterated derivatives up to order `r`
at `x` of the local representative of `s` in the chart and trivialization at `x`, symmetrized.
The symmetrization does nothing when `s` is `C^r` at `x` (`TauCeti.JetBundle.coeFn_jet`). -/
def jet (s : ∀ x, V x) (x : M) : JetBundle I F V r x :=
  jetSymmetrize 𝕜 E F r fun k ↦ iteratedFDeriv 𝕜 k.val (localRep I F s x) (extChartAt I x x)

/-- **The components of an `r`-jet.** For a section which is `C^r` at `x`, the components of
`jʳs(x)` are the iterated derivatives at `x` of its local representative in the chart and
trivialization at `x`. -/
theorem coeFn_jet {s : ∀ x, V x} {x : M}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) r (fun x ↦ TotalSpace.mk' F x (s x)) x) :
    ⇑(jet I F r s x) =
      fun k : Fin (r + 1) ↦ iteratedFDeriv 𝕜 k.val (localRep I F s x) (extChartAt I x x) := by
  rw [coeFn_eq, jet, SymmetricJet.subtypeL_apply]
  exact coeFn_jetSymmetrize_of_mem (iteratedFDeriv_mem_symmetricJets
    (contDiffAt_localRep hs (mem_baseSet_self F V x)) (by simp))

/-- The preferred trivialization of `JᵣV` at `i` reads an `r`-jet in the chart and
trivialization of `V` at `i`. -/
theorem trivializationAt_apply_snd (i : M)
    (p : TotalSpace (SymmetricJet 𝕜 E F r) (JetBundle I F V r)) :
    (trivializationAt (SymmetricJet 𝕜 E F r) (JetBundle I F V r) i p).2 =
      coordChange I F V r p.1 i p.1 p.2 := (rfl)

/-- **The `r`-jet in an arbitrary chart.** In the chart and trivialization at `i`, the
components of the `r`-jet of a section that is `C^r` at `y` are the iterated derivatives of the
local representative of the section. -/
theorem coeFn_coordChange_jet {s : ∀ x, V x} {y : M}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) r (fun x ↦ TotalSpace.mk' F x (s x)) y) {i : M}
    (hi : y ∈ baseSet (H := H) F V i) :
    ⇑(coordChange I F V r y i y (jet I F r s y)) =
      fun k : Fin (r + 1) ↦ iteratedFDeriv 𝕜 k.val (localRep I F s i) (extChartAt I i y) := by
  have hy := mem_baseSet_self (H := H) F V y
  have hyi := mem_extChartAt_source_of_mem_baseSet I hi
  have hpt : extChartAt I y y = (extChartAt I y ∘ (extChartAt I i).symm) (extChartAt I i y) := by
    rw [Function.comp_apply, (extChartAt I i).left_inv hyi]
  have hn : minSmoothness 𝕜 r ≤ r := by simp
  have hrep := contDiffAt_localRep hs hy
  rw [hpt] at hrep
  have hh := contDiffAt_ext_coord_change_extChartAt (I := I) (n := r)
    ((mem_baseSet_iff F V).1 hy).2 ((mem_baseSet_iff F V).1 hi).2
  have hg := contDiffAt_fiberCoordChange (I := I) (n := r) ((mem_baseSet_iff F V).1 hy).1 hi
  have hjet : ⇑(jetSymmetrize 𝕜 E F r fun k : Fin (r + 1) ↦
      iteratedFDeriv 𝕜 k.val (localRep I F s y) (extChartAt I y y)) =
      fun k : Fin (r + 1) ↦ iteratedFDeriv 𝕜 k.val (localRep I F s y) (extChartAt I y y) :=
    coeFn_jetSymmetrize_of_mem (iteratedFDeriv_mem_symmetricJets
      (contDiffAt_localRep hs hy) hn)
  rw [coordChange, jet, coeFn_symmetricJetCoordChange hh hg hn, hjet, hpt,
    linearJetCoordChange_iteratedFDeriv hrep hn hh hg]
  -- Near the image of `y`, the local representative at `i` is the transformed one at `y`.
  have heq := localRep_eventuallyEq_fiberCoordChange I F s hy hi
  rw [I.range_eq_univ, nhdsWithin_univ] at heq
  funext k
  exact ((heq.iteratedFDeriv 𝕜 k).eq_of_nhds).symm

/-- In the preferred trivialization of `JᵣV` at `i`, the components of the `r`-jet of a section
that is `C^r` at `y` are the iterated derivatives of its local representative at `i`. -/
theorem coeFn_trivializationAt_jet {s : ∀ x, V x} {y : M}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) r (fun x ↦ TotalSpace.mk' F x (s x)) y) {i : M}
    (hi : y ∈ baseSet (H := H) F V i) :
    ⇑(trivializationAt (SymmetricJet 𝕜 E F r) (JetBundle I F V r) i ⟨y, jet I F r s y⟩).2 =
      fun k : Fin (r + 1) ↦ iteratedFDeriv 𝕜 k.val (localRep I F s i) (extChartAt I i y) :=
  coeFn_coordChange_jet hs hi

/-- **Every `r`-jet is the `r`-jet of a section that is `C^n` at the base point.** In the chart
and trivialization at the base point, the section is the Taylor polynomial of the jet. -/
theorem exists_contMDiffAt_jet_eq {n : ℕ∞ω} (x : M) (j : JetBundle I F V r x) :
    ∃ s : ∀ y, V y, ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun y ↦ TotalSpace.mk' F y (s y)) x ∧
      jet I F r s x = j := by
  set e := trivializationAt F V x
  -- The Taylor polynomial of `j` about `φ x`, and its pullback by the chart.
  set A : (k : Fin (r + 1)) → E [×k]→L[𝕜] F := ⇑j
  set a : E → F := finiteJetPolynomial r A (extChartAt I x x)
  have hx := mem_baseSet_self (H := H) F V x
  have hx' := (mem_baseSet_iff F V).1 hx
  -- In the trivialization at `x`, the section `y ↦ e.symm y (a (φ y))` reads as `a ∘ φ`.
  have hsg : ∀ y ∈ e.baseSet, (e ⟨y, e.symm y (a (extChartAt I x y))⟩).2 = a (extChartAt I x y) :=
    fun y hy ↦ by rw [e.apply_mk_symm hy]
  refine ⟨fun y ↦ e.symm y (a (extChartAt I x y)), ?_, ?_⟩
  · rw [contMDiffAt_section_iff]
    exact ((contDiff_finiteJetPolynomial r A _).contMDiff.contMDiffAt.comp x
      contMDiffAt_extChartAt).congr_of_eventuallyEq
      (eventually_of_mem (e.open_baseSet.mem_nhds hx'.1) hsg)
  · -- Near `φ x`, the local representative is the Taylor polynomial `a`.
    have hrep : localRep I F (fun y ↦ e.symm y (a (extChartAt I x y))) x =ᶠ[𝓝 (extChartAt I x x)]
        a := by
      filter_upwards [eventually_extChartAt_symm_mem_baseSet hx hx'.2,
        extChartAt_target_mem_nhds x] with z hz hzt
      rw [localRep_apply, hsg _ ((mem_baseSet_iff F V).1 hz).1, (extChartAt I x).right_inv hzt]
    refine SymmetricJet.ext fun k ↦ ?_
    rw [jet, jetSymmetrize_apply, (hrep.iteratedFDeriv 𝕜 k).eq_of_nhds,
      iteratedFDeriv_finiteJetPolynomial_self r A _ k (SymmetricJet.apply_comp_perm _ k)]
    exact ContinuousMultilinearMap.symmetrize_eq_self (SymmetricJet.apply_comp_perm _ k)

end Jet

/-- **The `r`-jet of a `C^(n+r)` section is a `C^n` section of `JᵣV`.** -/
theorem contMDiffOn_jet {n : ℕ∞ω} [IsManifold I (n + r) M] [ContMDiffVectorBundle (n + r) F V I]
    {s : ∀ x, V x} {U : Set M} (hU : IsOpen U)
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) (n + r) (fun x ↦ TotalSpace.mk' F x (s x)) U) :
    haveI : IsManifold I r M := .of_le (n := n + r) le_add_self
    haveI : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
    ContMDiffOn I (I.prod 𝓘(𝕜, SymmetricJet 𝕜 E F r)) n
      (fun x ↦ TotalSpace.mk' (SymmetricJet 𝕜 E F r) x (jet I F r s x)) U := by
  have : IsManifold I r M := .of_le (n := n + r) le_add_self
  have : IsManifold I n M := .of_le (n := n + r) le_self_add
  have : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
  intro x₀ hx₀
  have hx₀b := mem_baseSet_self (H := H) F V x₀
  refine ContMDiffAt.contMDiffWithinAt ((contMDiffAt_section_iff x₀).2 ?_)
  -- In the chart at `x₀`, the jet is the symmetrized tuple of derivatives of the local
  -- representative at `x₀`, which is `C^n` since that representative is `C^(n+r)`.
  have hrep := contDiffAt_localRep (hs.contMDiffAt (hU.mem_nhds hx₀)) hx₀b
  have htuple : ContDiffAt 𝕜 n (fun z ↦ jetSymmetrize 𝕜 E F r fun k ↦
      iteratedFDeriv 𝕜 k (localRep I F s x₀) z) (extChartAt I x₀ x₀) :=
    (jetSymmetrize 𝕜 E F r).contDiff.contDiffAt.comp _ (contDiffAt_pi.2 fun k ↦
      hrep.iteratedFDeriv_right (add_le_add_right (by exact_mod_cast k.is_le) n))
  refine (htuple.comp_contMDiffAt contMDiffAt_extChartAt).congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx₀, (isOpen_baseSet (H := H) F V x₀).mem_nhds hx₀b] with x hxU hxb
  have hsx := ((hs x hxU).contMDiffAt (hU.mem_nhds hxU)).of_le (le_add_self (a := (r : ℕ∞ω)))
  rw [Function.comp_apply, ← coeFn_trivializationAt_jet hsx hxb, jetSymmetrize_coeFn]

/-- The `r`-jet of a `C^(n+r)` section is a `C^n` section of `JᵣV`. -/
theorem contMDiff_jet {n : ℕ∞ω} [IsManifold I (n + r) M] [ContMDiffVectorBundle (n + r) F V I]
    {s : ∀ x, V x} (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) (n + r) fun x ↦ TotalSpace.mk' F x (s x)) :
    haveI : IsManifold I r M := .of_le (n := n + r) le_add_self
    haveI : ContMDiffVectorBundle r F V I := .of_le (n := n + r) le_add_self
    ContMDiff I (I.prod 𝓘(𝕜, SymmetricJet 𝕜 E F r)) n
      fun x ↦ TotalSpace.mk' (SymmetricJet 𝕜 E F r) x (jet I F r s x) := by
  rw [← contMDiffOn_univ] at hs ⊢
  exact contMDiffOn_jet isOpen_univ hs

section Truncate

variable [IsManifold I r M] [ContMDiffVectorBundle r F V I]

/-- The **value** of an `r`-jet, the fibre of the projection `JᵣV → V`: its component of order
zero, read back through the trivialization at the base point. -/
def value (x : M) : JetBundle I F V r x →L[𝕜] V x :=
  (trivializationAt F V x).symmL 𝕜 x ∘L ContinuousMultilinearMap.apply 𝕜 _ F 0 ∘L
    ContinuousLinearMap.proj (R := 𝕜) (φ := fun k : Fin (r + 1) ↦ E [×k]→L[𝕜] F) 0 ∘L
    SymmetricJet.subtypeL 𝕜 E F r

/-- The value of an `r`-jet is its component of order zero read back through the
trivialization. -/
theorem value_apply (x : M) (j : JetBundle I F V r x) :
    value x j = (trivializationAt F V x).symm x (j 0 0) := by
  rw [coeFn_eq, ← Trivialization.symmL_apply (R := 𝕜) _ (mem_baseSet_trivializationAt F V x)]
  rfl

/-- The value of the `r`-jet of a section is the value of the section. -/
@[simp]
theorem value_jet (s : ∀ x, V x) (x : M) : value x (jet I F r s x) = s x := by
  -- The component of order `0` is a map of `(0 : Fin (r + 1)).val` arguments; state its value for
  -- any number `k = 0` of arguments.
  have hval : ∀ (k : ℕ) (_ : k = 0) (w : Fin k → E),
      iteratedFDeriv 𝕜 k (localRep I F s x) (extChartAt I x x) w =
        localRep I F s x (extChartAt I x x) := by
    rintro _ rfl w
    exact iteratedFDeriv_zero_apply w
  have h0 : (jet I F r s x) 0 0 = localRep I F s x (extChartAt I x x) := by
    rw [coeFn_eq, jet, SymmetricJet.subtypeL_apply, jetSymmetrize_apply,
      ContinuousMultilinearMap.symmetrize_eq_self fun v σ ↦
        congrArg _ (funext fun i ↦ absurd i.isLt (by simp))]
    exact hval _ (by simp) 0
  rw [value_apply, h0,
    localRep_extChartAt I F s ((mem_baseSet_iff F V).1 (mem_baseSet_self F V x)).2,
    Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt F V x)]

variable {r' : ℕ} [IsManifold I r' M] [ContMDiffVectorBundle r' F V I]

/-- The **truncation** `JᵣV → Jᵣ'V` of `r`-jets to order `r' ≤ r`, forgetting the derivatives of
order greater than `r'`. -/
def truncate (hr : r' ≤ r) (x : M) : JetBundle I F V r x →L[𝕜] JetBundle I F V r' x :=
  SymmetricJet.truncate 𝕜 E F hr

/-- The components of a truncated jet are those of the jet of the same order. -/
@[simp]
theorem truncate_apply (hr : r' ≤ r) (x : M) (j : JetBundle I F V r x) (k : Fin (r' + 1)) :
    truncate hr x j k = j (Fin.castLE (by omega) k) :=
  SymmetricJet.truncate_apply hr j k

/-- The truncation of the `r`-jet of a section is its `r'`-jet. -/
@[simp]
theorem truncate_jet (hr : r' ≤ r) (s : ∀ x, V x) (x : M) :
    truncate hr x (jet I F r s x) = jet I F r' s x :=
  SymmetricJet.truncate_jetSymmetrize hr _

/-- **The truncation is intrinsic**: in the chart and trivialization at `i`, it reads as the
truncation of symmetric jets. -/
theorem coordChange_truncate (hr : r' ≤ r) {y i : M} (hi : y ∈ baseSet (H := H) F V i)
    (j : JetBundle I F V r y) :
    coordChange I F V r' y i y (truncate hr y j) =
      SymmetricJet.truncate 𝕜 E F hr (coordChange I F V r y i y j) := by
  have hy := mem_baseSet_self (H := H) F V y
  exact (SymmetricJet.truncate_symmetricJetCoordChange hr
    (contDiffAt_ext_coord_change_extChartAt ((mem_baseSet_iff F V).1 hy).2
      ((mem_baseSet_iff F V).1 hi).2)
    (contDiffAt_fiberCoordChange ((mem_baseSet_iff F V).1 hy).1 hi) _).symm

/-- Truncation keeps the value of a jet. -/
@[simp]
theorem value_truncate (hr : r' ≤ r) (x : M) (j : JetBundle I F V r x) :
    value x (truncate hr x j) = value x j := by
  have h : truncate hr x j 0 0 = j 0 0 := by
    rw [truncate_apply]
    rfl
  rw [value_apply, value_apply, h]

end Truncate

section Trivial

/-- For the trivial bundle over a model space, the components of the `r`-jet of a section which
is `C^r` at `x` are its iterated derivatives at `x`. -/
theorem coeFn_jet_trivial {s : E → F} {x : E} (hs : ContDiffAt 𝕜 r s x) :
    ⇑(jet 𝓘(𝕜, E) F r (s : ∀ y, Bundle.Trivial E F y) x) =
      fun k : Fin (r + 1) ↦ iteratedFDeriv 𝕜 k.val s x := by
  rw [coeFn_eq, jet, SymmetricJet.subtypeL_apply, localRep_trivial, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, id]
  exact coeFn_jetSymmetrize_of_mem (iteratedFDeriv_mem_symmetricJets hs (by simp))

end Trivial

end JetBundle

end TauCeti
