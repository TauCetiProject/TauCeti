/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Analysis.Calculus.Jet.FirstOrder
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
public import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The first-jet bundle of a smooth vector bundle

Let `V → M` be a smooth vector bundle with model fibre `F` over a smooth manifold `M` modelled
on `E`. Its *first-jet bundle* `J¹V` records, at each point `x`, the value and the first
derivative at `x` of local sections of `V`. In the preferred chart of `M` at `x` and the
preferred trivialization of `V` at `x`, a first jet at `x` is a pair `(v, A)` in
`F × (E →L[𝕜] F)`, and changing to the chart and trivialization at another index transforms it
by the first-order chain and product rules (`ContinuousLinearMap.firstJetPullback`):

`(v, A) ↦ (g v, (Dg) v + g ∘ A ∘ (Dh))`,

where `g` is the transition function of `V` and `h` the transition function of the charts.
We glue these coordinate pieces with Mathlib's `VectorBundleCore` (`TauCeti.firstJetCore`); the
transition functions satisfy the cocycle law because of the chain rule, and they are smooth
because the transition functions of `V` and of the charts are. This makes
`TauCeti.FirstJet I F V` a vector bundle over `M`, with model fibre `F × (E →L[𝕜] F)`; it is a
`C^n` vector bundle when `V` and `M` are `C^(n+1)` (`TauCeti.FirstJet.contMDiffVectorBundle`).

The value of a jet gives a smooth bundle map `J¹V → V` (`TauCeti.FirstJet.value`,
`TauCeti.FirstJet.contMDiff_value`), and a `C^n` section `s` of `V` has a `C^m` jet extension
`j¹s` for `m + 1 ≤ n` (`TauCeti.firstJetExtension`, `TauCeti.contMDiff_firstJetExtension`) whose
value is `s`. In every preferred chart and trivialization, the coordinates of `j¹s` are the value
and the derivative of the local expression of `s` (`TauCeti.trivializationAt_firstJetExtension`).
On each fibre, the jets of value zero are exactly the linear maps `T_x M →L[𝕜] V_x`
(`TauCeti.FirstJet.ofHom`): this is the fibre of the exact sequence
`0 → Hom(TM, V) → J¹V → V → 0`, whose kernel is `T*M ⊗ V` in finite rank.

The bundle is built for `C^1` bundles over `C^1` manifolds with corners; derivatives in charts are
taken within the range of the model. The gluing follows Mathlib's
`tangentBundleCore`, whose chart-transition derivatives `tangentCoordChange` supply the
base-derivative coefficient of the transition functions here.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  Springer (1993), §§12.16–12.17.
-/

public section

noncomputable section

open Bundle Filter Function Set Topology ContinuousLinearMap
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]

namespace FirstJet

section Transition

variable (I F V) in
/-- The derivative, in the preferred extended chart at `j`, of the transition function of `V`
from its preferred trivialization at `i` to the one at `j`. It is the off-diagonal term of the
transition functions of the first-jet bundle. -/
def coordChangeDeriv (i j x : M) : E →L[𝕜] F →L[𝕜] F :=
  fderivWithin 𝕜 ((fun b ↦ ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) b :
    F →L[𝕜] F)) ∘ (extChartAt I j).symm) (range I) (extChartAt I j x)

/-- The transition derivative from a preferred trivialization to itself vanishes. -/
theorem coordChangeDeriv_self {i x : M} (hi : x ∈ (trivializationAt F V i).baseSet)
    (hc : x ∈ (chartAt H i).source) :
    coordChangeDeriv I F V i i x = 0 := by
  have hnhds : (extChartAt I i).symm ⁻¹' ((trivializationAt F V i).baseSet) ∈
      𝓝[range I] (extChartAt I i x) :=
    mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds'
      (by rwa [extChartAt_source]) ((trivializationAt F V i).open_baseSet.mem_nhds hi))
  have h₁ : ((fun b ↦ ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V i) b :
      F →L[𝕜] F)) ∘ (extChartAt I i).symm) =ᶠ[𝓝[range I] (extChartAt I i x)]
        fun _ ↦ ContinuousLinearMap.id 𝕜 F := by
    filter_upwards [hnhds] with y hy
    exact Trivialization.coe_coordChangeL_self _ _ hy
  have h₂ : ((fun b ↦ ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V i) b :
      F →L[𝕜] F)) ∘ (extChartAt I i).symm) (extChartAt I i x) = ContinuousLinearMap.id 𝕜 F := by
    rw [Function.comp_apply, (extChartAt I i).left_inv (by rwa [extChartAt_source])]
    exact Trivialization.coe_coordChangeL_self _ _ hi
  rw [coordChangeDeriv, h₁.fderivWithin_eq h₂, fderivWithin_fun_const, Pi.zero_apply]

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]

omit [ContMDiffVectorBundle 1 F V I] in
/-- The transition functions of the first-jet bundle are `C^m` on chart overlaps when `V` and `M`
are `C^n` with `m + 1 ≤ n`. -/
private theorem contMDiffAt_firstJetPullback {n m : WithTop ℕ∞} [IsManifold I n M]
    [ContMDiffVectorBundle n F V I] {i j x : M}
    (hi : x ∈ (trivializationAt F V i).baseSet ∩ (chartAt H i).source)
    (hj : x ∈ (trivializationAt F V j).baseSet ∩ (chartAt H j).source) (hmn : m + 1 ≤ n) :
    ContMDiffAt I 𝓘(𝕜, (F × (E →L[𝕜] F)) →L[𝕜] F × (E →L[𝕜] F)) m
      (fun z ↦ ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) z :
        F →L[𝕜] F).firstJetPullback (coordChangeDeriv I F V i j z)
          (tangentCoordChange I j i z)) x := by
  have hg := contMDiffAt_coordChangeL (IB := I) (n := n) hi.1 hj.1
  have hD : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] F →L[𝕜] F) m (coordChangeDeriv I F V i j) x :=
    hg.fderivWithin_comp_extChartAt_symm hj.2 hmn
  have hT : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E) m (tangentCoordChange I j i) x :=
    (contMDiffAt_extChartAt' (n := n) hi.2).fderivWithin_comp_extChartAt_symm hj.2 hmn
  exact contDiff_firstJetPullback.comp_contMDiffAt
    ((hg.of_le (le_self_add.trans hmn)).prodMk_space (hD.prodMk_space hT))

/-- The transition derivatives satisfy the product rule along a composite of transitions. -/
theorem coordChangeDeriv_comp {i j k x : M}
    (hi : x ∈ (trivializationAt F V i).baseSet) (hj : x ∈ (trivializationAt F V j).baseSet)
    (hk : x ∈ (trivializationAt F V k).baseSet) (hcj : x ∈ (chartAt H j).source)
    (hck : x ∈ (chartAt H k).source) :
    coordChangeDeriv I F V i k x =
      (compL 𝕜 F F F ((trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V k) x :
          F →L[𝕜] F)).comp ((coordChangeDeriv I F V i j x).comp (tangentCoordChange I k j x)) +
        ((compL 𝕜 F F F).flip ((trivializationAt F V i).coordChangeL 𝕜
          (trivializationAt F V j) x : F →L[𝕜] F)).comp (coordChangeDeriv I F V j k x) := by
  set g : M → M → M → F →L[𝕜] F := fun a b z ↦
    ((trivializationAt F V a).coordChangeL 𝕜 (trivializationAt F V b) z : F →L[𝕜] F)
  have hxk : x ∈ (extChartAt I k).source := by rwa [extChartAt_source]
  have hxj : x ∈ (extChartAt I j).source := by rwa [extChartAt_source]
  have hinv : (extChartAt I k).symm (extChartAt I k x) = x := (extChartAt I k).left_inv hxk
  -- Points of the `k`-chart lying over the common domain of all transitions.
  have hU : (trivializationAt F V i).baseSet ∩ (trivializationAt F V j).baseSet ∩
      (trivializationAt F V k).baseSet ∈ 𝓝 x :=
    (((trivializationAt F V i).open_baseSet.inter (trivializationAt F V j).open_baseSet).inter
      (trivializationAt F V k).open_baseSet).mem_nhds ⟨⟨hi, hj⟩, hk⟩
  have hnhds := mem_nhdsWithin_of_mem_nhds (t := range I) (extChartAt_preimage_mem_nhds' hxk hU)
  -- The `j`-to-`k` transition written in the `k`-chart.
  have h₁ : HasFDerivWithinAt (g j k ∘ (extChartAt I k).symm) (coordChangeDeriv I F V j k x)
      (range I) (extChartAt I k x) :=
    (trivializationAt F V j).hasFDerivWithinAt_coordChangeL_comp_extChartAt_symm _ hj hk hck
  -- The `i`-to-`j` transition written in the `k`-chart, through the `j`-chart.
  have h₂ : HasFDerivWithinAt (g i j ∘ (extChartAt I k).symm)
      ((coordChangeDeriv I F V i j x).comp (tangentCoordChange I k j x))
      (range I) (extChartAt I k x) :=
    ((trivializationAt F V i).hasFDerivWithinAt_coordChangeL_comp_extChartAt_symm _ hi hj
      hcj).comp_tangentCoordChange hxj hxk
  have h₃ := h₁.clm_comp h₂
  simp only [Function.comp_apply, hinv] at h₃
  rw [coordChangeDeriv]
  refine (h₃.congr_of_eventuallyEq ?_ ?_).fderivWithin (I.uniqueDiffOn _ (mem_range_self _))
  · filter_upwards [hnhds] with y hy
    exact (Trivialization.coordChangeL_comp_coordChangeL _ _ _ _ hy.1.1 hy.1.2 hy.2).symm
  · simp only [Function.comp_apply, hinv]
    exact (Trivialization.coordChangeL_comp_coordChangeL _ _ _ _ hi hj hk).symm

end Transition

end FirstJet

open FirstJet

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]

variable (I F V) in
/-- The vector bundle core of the first-jet bundle of `V`. It is indexed by the points of `M`:
the index `i` stands for the preferred chart of `M` at `i` and the preferred trivialization of
`V` at `i`, and a first jet in these coordinates is a value in `F` together with a derivative in
`E →L[𝕜] F`. The transition functions are the first-jet transformations
`ContinuousLinearMap.firstJetPullback` built from the transition functions of `V`, their
derivatives `FirstJet.coordChangeDeriv`, and the derivatives of the chart transitions. -/
@[expose, simps -isSimp baseSet, simps indexAt coordChange]
def firstJetCore : VectorBundleCore 𝕜 M (F × (E →L[𝕜] F)) M where
  baseSet i := (trivializationAt F V i).baseSet ∩ (chartAt H i).source
  isOpen_baseSet i := (trivializationAt F V i).open_baseSet.inter (chartAt H i).open_source
  indexAt := id
  mem_baseSet_at x := ⟨mem_baseSet_trivializationAt F V x, mem_chart_source H x⟩
  coordChange i j x := ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) x :
    F →L[𝕜] F).firstJetPullback (coordChangeDeriv I F V i j x) (tangentCoordChange I j i x)
  coordChange_self i x hx v := by
    have hxi : x ∈ (extChartAt I i).source := by rw [extChartAt_source]; exact hx.2
    rw [Trivialization.coe_coordChangeL_self _ _ hx.1, coordChangeDeriv_self hx.1 hx.2,
      Manifold.tangentCoordChange_self_eq_id hxi, firstJetPullback_id, ContinuousLinearMap.id_apply]
  continuousOn_coordChange i j := by
    intro x hx
    exact (contMDiffAt_firstJetPullback (I := I) (n := 1) (m := 0) hx.1 hx.2
      (by simp)).continuousAt.continuousWithinAt
  coordChange_comp i j k x hx v := by
    obtain ⟨⟨hi, hj⟩, hk⟩ := hx
    have hx : x ∈ (extChartAt I k).source ∩ (extChartAt I j).source ∩ (extChartAt I i).source := by
      simp only [extChartAt_source]
      exact ⟨⟨hk.2, hj.2⟩, hi.2⟩
    rw [← ContinuousLinearMap.comp_apply, firstJetPullback_comp,
      Trivialization.coordChangeL_comp_coordChangeL _ _ _ _ hi.1 hj.1 hk.1,
      Manifold.tangentCoordChange_comp_tangentCoordChange hx,
      coordChangeDeriv_comp hi.1 hj.1 hk.1 hj.2 hk.2]

/-- If `V` is a `C^(n+1)` vector bundle over a `C^(n+1)` manifold, the transition functions of
its first-jet bundle are `C^n`. -/
theorem firstJetCore.isContMDiff {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
    [ContMDiffVectorBundle (n + 1) F V I] : (firstJetCore I F V).IsContMDiff I n where
  contMDiffOn_coordChange _ _ := fun _ hx ↦
    (FirstJet.contMDiffAt_firstJetPullback (I := I) hx.1 hx.2 le_rfl).contMDiffWithinAt

variable (I F V) in
/-- The first-jet bundle `J¹V` of a smooth vector bundle `V`. Its fibre at `x` consists of the
first jets at `x` of local sections, written as a value and a derivative in the preferred chart
of `M` and the preferred trivialization of `V` at `x`. -/
@[expose] def FirstJet (x : M) : Type _ :=
  (firstJetCore I F V).Fiber x

instance (x : M) : AddCommGroup (FirstJet I F V x) :=
  inferInstanceAs (AddCommGroup ((firstJetCore I F V).Fiber x))

instance (x : M) : Module 𝕜 (FirstJet I F V x) :=
  inferInstanceAs (Module 𝕜 ((firstJetCore I F V).Fiber x))

instance (x : M) : TopologicalSpace (FirstJet I F V x) :=
  inferInstanceAs (TopologicalSpace ((firstJetCore I F V).Fiber x))

instance (x : M) : IsTopologicalAddGroup (FirstJet I F V x) :=
  inferInstanceAs (IsTopologicalAddGroup (F × (E →L[𝕜] F)))

instance (x : M) : ContinuousSMul 𝕜 (FirstJet I F V x) :=
  inferInstanceAs (ContinuousSMul 𝕜 (F × (E →L[𝕜] F)))

instance : TopologicalSpace (TotalSpace (F × (E →L[𝕜] F)) (FirstJet I F V)) :=
  inferInstanceAs (TopologicalSpace (firstJetCore I F V).TotalSpace)

instance : FiberBundle (F × (E →L[𝕜] F)) (FirstJet I F V) :=
  inferInstanceAs (FiberBundle (F × (E →L[𝕜] F)) (firstJetCore I F V).Fiber)

instance : VectorBundle 𝕜 (F × (E →L[𝕜] F)) (FirstJet I F V) :=
  inferInstanceAs (VectorBundle 𝕜 (F × (E →L[𝕜] F)) (firstJetCore I F V).Fiber)

/-- If `V` is a `C^(n+1)` vector bundle over a `C^(n+1)` manifold, its first-jet bundle is a `C^n`
vector bundle. -/
theorem FirstJet.contMDiffVectorBundle {n : WithTop ℕ∞} [IsManifold I (n + 1) M]
    [ContMDiffVectorBundle (n + 1) F V I] :
    ContMDiffVectorBundle n (F × (E →L[𝕜] F)) (FirstJet I F V) I :=
  have : (firstJetCore I F V).IsContMDiff I n := firstJetCore.isContMDiff
  inferInstanceAs (ContMDiffVectorBundle n (F × (E →L[𝕜] F)) (firstJetCore I F V).Fiber I)

instance [h : IsManifold I ∞ M] [h' : ContMDiffVectorBundle ∞ F V I] :
    ContMDiffVectorBundle ∞ (F × (E →L[𝕜] F)) (FirstJet I F V) I :=
  have : IsManifold I (∞ + 1) M := h
  have : ContMDiffVectorBundle (∞ + 1) F V I := h'
  FirstJet.contMDiffVectorBundle

namespace FirstJet

/-- The preferred trivialization of the first-jet bundle at `x₀` is defined over the base set of
the preferred trivialization of `V` at `x₀` inside the source of the preferred chart at `x₀`. -/
@[simp, mfld_simps]
theorem trivializationAt_baseSet (x₀ : M) :
    (trivializationAt (F × (E →L[𝕜] F)) (FirstJet I F V) x₀).baseSet =
      (trivializationAt F V x₀).baseSet ∩ (chartAt H x₀).source :=
  rfl

variable (I F V) in
/-- The coordinates of a first jet at `x`: its value in `F` and its derivative in `E →L[𝕜] F`,
read in the preferred chart of `M` and the preferred trivialization of `V` at `x`. This is the
fibre at `x` of the preferred trivialization of the first-jet bundle at `x`. -/
def coords (x : M) : FirstJet I F V x ≃L[𝕜] F × (E →L[𝕜] F) :=
  (trivializationAt (F × (E →L[𝕜] F)) (FirstJet I F V) x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt _ _ x)

/-- The coordinates of a jet at `x` are its image under the preferred trivialization at `x`. -/
theorem coords_apply (x : M) (w : FirstJet I F V x) :
    coords I F V x w = (trivializationAt (F × (E →L[𝕜] F)) (FirstJet I F V) x ⟨x, w⟩).2 := by
  rw [coords, Trivialization.continuousLinearEquivAt_apply]

/-- The preferred trivialization of the first-jet bundle at `x₀` applies the first-jet
transformation to the coordinates of a jet at a point `x` of its base set. -/
theorem trivializationAt_apply {x₀ x : M}
    (hx : x ∈ (trivializationAt F V x₀).baseSet ∩ (chartAt H x₀).source) (w : FirstJet I F V x) :
    trivializationAt (F × (E →L[𝕜] F)) (FirstJet I F V) x₀ ⟨x, w⟩ =
      (x, ((trivializationAt F V x).coordChangeL 𝕜 (trivializationAt F V x₀) x :
        F →L[𝕜] F).firstJetPullback (coordChangeDeriv I F V x x₀ x)
          (tangentCoordChange I x₀ x x) (coords I F V x w)) := by
  rw [coords_apply]
  -- `FirstJet I F V` is `(firstJetCore I F V).Fiber`, so its preferred trivialization at a point
  -- is the core's local trivialization there (`VectorBundleCore.trivializationAt`).
  change (firstJetCore I F V).localTrivAt x₀ ⟨x, w⟩ =
    (x, (firstJetCore I F V).coordChange x x₀ x (((firstJetCore I F V).localTrivAt x ⟨x, w⟩).2))
  rw [← VectorBundleCore.localTrivAt_def, ← VectorBundleCore.localTrivAt_def,
    VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply]
  exact Prod.ext rfl ((firstJetCore I F V).coordChange_comp x x x₀ x
    ⟨⟨(firstJetCore I F V).mem_baseSet_at x, (firstJetCore I F V).mem_baseSet_at x⟩, hx⟩ w).symm

variable (I F V) in
/-- The value of a first jet: the point of `V` whose coordinate is the value coordinate of the
jet. -/
def value (x : M) : FirstJet I F V x →L[𝕜] V x :=
  (trivializationAt F V x).symmL 𝕜 x ∘L ContinuousLinearMap.fst 𝕜 F (E →L[𝕜] F) ∘L
    (coords I F V x : FirstJet I F V x →L[𝕜] F × (E →L[𝕜] F))

/-- The value of a jet is the point of `V` with the value coordinate of the jet. -/
theorem value_apply (x : M) (w : FirstJet I F V x) :
    value I F V x w = (trivializationAt F V x).symm x (coords I F V x w).1 := by
  simp [value, Trivialization.symmL_apply _ (mem_baseSet_trivializationAt F V x)]

/-- The value map `J¹V → V` is a `C^n` map of total spaces, for every `n`. -/
theorem contMDiff_value {n : WithTop ℕ∞} :
    ContMDiff (I.prod 𝓘(𝕜, F × (E →L[𝕜] F))) (I.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace (F × (E →L[𝕜] F)) (FirstJet I F V) ↦
        (⟨p.1, value I F V p.1 p.2⟩ : TotalSpace F V)) := by
  intro p₀
  have hid : ContMDiffAt (I.prod 𝓘(𝕜, F × (E →L[𝕜] F))) (I.prod 𝓘(𝕜, F × (E →L[𝕜] F))) n
      (id : TotalSpace (F × (E →L[𝕜] F)) (FirstJet I F V) → _) p₀ := contMDiffAt_id
  rw [Bundle.contMDiffAt_totalSpace] at hid ⊢
  refine ⟨hid.1, (contDiff_fst.comp_contMDiffAt hid.2).congr_of_eventuallyEq ?_⟩
  have hU := (trivializationAt (F × (E →L[𝕜] F)) (FirstJet I F V) p₀.1).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ p₀.1)
  filter_upwards [(FiberBundle.continuous_proj (F × (E →L[𝕜] F)) (FirstJet I F V)).continuousAt
    hU] with p hp
  obtain ⟨x, w⟩ := p
  have hx : x ∈ (trivializationAt F V p₀.proj).baseSet ∩ (chartAt H p₀.proj).source :=
    trivializationAt_baseSet (I := I) (F := F) (V := V) p₀.proj ▸ hp
  simp only [Function.comp_apply, id_eq, trivializationAt_apply hx, firstJetPullback_apply,
    value_apply, ContinuousLinearEquiv.coe_coe]
  rw [Trivialization.coordChangeL_apply (trivializationAt F V x) (trivializationAt F V p₀.proj)
    ⟨mem_baseSet_trivializationAt F V x, hx.1⟩]

/-- Every point of `V_x` is the value of a jet at `x`. -/
theorem value_surjective (x : M) : Surjective (value I F V x) := by
  intro y
  refine ⟨(coords I F V x).symm ((trivializationAt F V x).continuousLinearMapAt 𝕜 x y, 0), ?_⟩
  rw [value_apply, ContinuousLinearEquiv.apply_symm_apply,
    ← Trivialization.symmL_apply (R := 𝕜) _ (mem_baseSet_trivializationAt F V x),
    Trivialization.symmL_continuousLinearMapAt _ (mem_baseSet_trivializationAt F V x)]

section Hom

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousConstSMul 𝕜 (V x)]

variable (I F V) in
/-- The jets of value zero at `x`: a continuous linear map `T_x M →L[𝕜] V_x`, read in the
preferred trivialization of `V`, is the derivative coordinate of a jet with value zero. -/
def ofHom (x : M) : (TangentSpace I x →L[𝕜] V x) →L[𝕜] FirstJet I F V x :=
  ((coords I F V x).symm : F × (E →L[𝕜] F) →L[𝕜] FirstJet I F V x) ∘L
    ContinuousLinearMap.inr 𝕜 F (E →L[𝕜] F) ∘L
      ContinuousLinearMap.postcomp E ((trivializationAt F V x).continuousLinearMapAt 𝕜 x)

/-- The jet attached to `A : T_x M →L[𝕜] V_x` has value coordinate zero and derivative
coordinate `A` read in the preferred trivialization of `V`. -/
@[simp]
theorem coords_ofHom (x : M) (A : TangentSpace I x →L[𝕜] V x) :
    coords I F V x (ofHom I F V x A) =
      (0, (trivializationAt F V x).continuousLinearMapAt 𝕜 x ∘L A) := by
  simp only [ofHom, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  -- `inr_apply` and `postcomp_apply` do not fire through `TangentSpace I x = E`; both sides agree
  -- by unfolding these two maps.
  rfl

/-- A jet coming from a linear map has value zero. -/
@[simp]
theorem value_ofHom (x : M) (A : TangentSpace I x →L[𝕜] V x) :
    value I F V x (ofHom I F V x A) = 0 := by
  rw [value_apply, coords_ofHom, ← Trivialization.symmL_apply (R := 𝕜) _
    (mem_baseSet_trivializationAt F V x), map_zero]

/-- Distinct linear maps `T_x M →L[𝕜] V_x` give distinct jets. -/
theorem ofHom_injective (x : M) : Injective (ofHom I F V x) := by
  intro A B hAB
  have h := congrArg (fun w ↦ (coords I F V x w).2) hAB
  simp only [coords_ofHom] at h
  ext v
  have hv := congrArg (fun C : E →L[𝕜] F ↦ (trivializationAt F V x).symmL 𝕜 x (C v)) h
  have hb := mem_baseSet_trivializationAt F V x
  -- `hv` compares `symmL (φ (A v))` and `symmL (φ (B v))`, where `φ` reads `V x` in coordinates.
  calc A v = (trivializationAt F V x).symmL 𝕜 x
        ((trivializationAt F V x).continuousLinearMapAt 𝕜 x (A v)) :=
        (Trivialization.symmL_continuousLinearMapAt _ hb _).symm
    _ = (trivializationAt F V x).symmL 𝕜 x
        ((trivializationAt F V x).continuousLinearMapAt 𝕜 x (B v)) := hv
    _ = B v := Trivialization.symmL_continuousLinearMapAt _ hb _

/-- Fibrewise exactness of `0 → Hom(T_x M, V_x) → J¹_x V → V_x → 0` in the middle: a jet has
value zero exactly when it comes from a linear map `T_x M →L[𝕜] V_x`. -/
theorem ker_value (x : M) :
    LinearMap.ker (value I F V x : FirstJet I F V x →ₗ[𝕜] V x) =
      LinearMap.range (ofHom I F V x : (TangentSpace I x →L[𝕜] V x) →ₗ[𝕜] FirstJet I F V x) := by
  ext w
  constructor
  · intro hw
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, value_apply] at hw
    have hv : (coords I F V x w).1 = 0 := by
      have h := congrArg ((trivializationAt F V x).continuousLinearMapAt 𝕜 x) hw
      rwa [← Trivialization.symmL_apply (R := 𝕜) _ (mem_baseSet_trivializationAt F V x),
        Trivialization.continuousLinearMapAt_symmL _ (mem_baseSet_trivializationAt F V x),
        map_zero] at h
    refine ⟨(trivializationAt F V x).symmL 𝕜 x ∘L (coords I F V x w).2, ?_⟩
    apply (coords I F V x).injective
    rw [ContinuousLinearMap.coe_coe, coords_ofHom]
    refine Prod.ext hv.symm ?_
    ext v
    exact Trivialization.continuousLinearMapAt_symmL _ (mem_baseSet_trivializationAt F V x) _
  · rintro ⟨B, rfl⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]
    exact value_ofHom x B

end Hom

end FirstJet

section JetExtension

variable (I F) in
/-- The first-jet extension `j¹s` of a section `s` of `V`: at `x`, the value and the derivative of
the local expression of `s` in the preferred chart of `M` and the preferred trivialization of `V`
at `x`. For differentiable `s` its coordinates in any other preferred chart and trivialization
are again the value and derivative of the local expression there
(`TauCeti.trivializationAt_firstJetExtension`). -/
def firstJetExtension (s : ∀ x, V x) (x : M) : FirstJet I F V x :=
  (FirstJet.coords I F V x).symm ((trivializationAt F V x ⟨x, s x⟩).2,
    fderivWithin 𝕜 ((fun z ↦ (trivializationAt F V x ⟨z, s z⟩).2) ∘ (extChartAt I x).symm)
      (range I) (extChartAt I x x))

/-- The coordinates of the jet extension of `s` at `x` are the value and the derivative of the
local expression of `s` at `x`. -/
@[simp]
theorem coords_firstJetExtension (s : ∀ x, V x) (x : M) :
    FirstJet.coords I F V x (firstJetExtension I F s x) =
      ((trivializationAt F V x ⟨x, s x⟩).2,
        fderivWithin 𝕜 ((fun z ↦ (trivializationAt F V x ⟨z, s z⟩).2) ∘ (extChartAt I x).symm)
          (range I) (extChartAt I x x)) :=
  (FirstJet.coords I F V x).apply_symm_apply _

/-- The value of the jet extension of `s` is `s`. -/
@[simp]
theorem value_firstJetExtension (s : ∀ x, V x) (x : M) :
    FirstJet.value I F V x (firstJetExtension I F s x) = s x := by
  rw [FirstJet.value_apply, coords_firstJetExtension,
    Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt F V x)]

/-- In the preferred chart and trivialization at `x₀`, the jet extension of a differentiable
section at a nearby point `x` has coordinates the value at `x` and the derivative at `x` of the
local expression of the section in the preferred chart and trivialization at `x₀`. -/
theorem trivializationAt_firstJetExtension {s : ∀ x, V x} {x₀ x : M}
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun z ↦ TotalSpace.mk' F z (s z)) x)
    (hx : x ∈ (trivializationAt F V x₀).baseSet ∩ (chartAt H x₀).source) :
    trivializationAt (F × (E →L[𝕜] F)) (FirstJet I F V) x₀ ⟨x, firstJetExtension I F s x⟩ =
      (x, ((trivializationAt F V x₀ ⟨x, s x⟩).2,
        fderivWithin 𝕜 ((fun z ↦ (trivializationAt F V x₀ ⟨z, s z⟩).2) ∘
          (extChartAt I x₀).symm) (range I) (extChartAt I x₀ x))) := by
  set e := trivializationAt F V x
  set e₀ := trivializationAt F V x₀
  -- The local expressions of `s` in the trivializations at `x` and at `x₀`.
  set sx : M → F := fun z ↦ (e ⟨z, s z⟩).2 with hsx_def
  set s₀ : M → F := fun z ↦ (e₀ ⟨z, s z⟩).2 with hs₀_def
  have hex : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hx₀ : x ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hx.2
  have hxx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hinv : (extChartAt I x₀).symm (extChartAt I x₀ x) = x := (extChartAt I x₀).left_inv hx₀
  -- On the common domain, the expression at `x₀` is the transition of the expression at `x`.
  have htrans : ∀ z ∈ e.baseSet ∩ e₀.baseSet,
      s₀ z = (e.coordChangeL 𝕜 e₀ z : F →L[𝕜] F) (sx z) := fun z hz ↦
    (DFunLike.congr_fun (Trivialization.continuousLinearEquivAt_trans_coordChangeL 𝕜 e e₀
      hz.1 hz.2) (s z)).symm
  -- The local expression of `s` at `x`, differentiated in the chart at `x` and moved to the
  -- chart at `x₀`.
  have hsx : HasFDerivWithinAt (sx ∘ (extChartAt I x₀).symm)
      ((fderivWithin 𝕜 (sx ∘ (extChartAt I x).symm) (range I) (extChartAt I x x)).comp
        (tangentCoordChange I x₀ x x)) (range I) (extChartAt I x₀ x) := by
    have h := ((mdifferentiableAt_iff _ _).1 ((mdifferentiableAt_section I s).1 hs)).2
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      id_comp] at h
    exact h.hasFDerivWithinAt.comp_tangentCoordChange hxx hx₀
  have hg : HasFDerivWithinAt ((fun b ↦ (e.coordChangeL 𝕜 e₀ b : F →L[𝕜] F)) ∘
      (extChartAt I x₀).symm) (coordChangeDeriv I F V x x₀ x) (range I) (extChartAt I x₀ x) :=
    e.hasFDerivWithinAt_coordChangeL_comp_extChartAt_symm e₀ hex hx.1 hx.2
  have hnhds := mem_nhdsWithin_of_mem_nhds (t := range I) (extChartAt_preimage_mem_nhds' hx₀
    ((e.open_baseSet.inter e₀.open_baseSet).mem_nhds ⟨hex, hx.1⟩))
  have hderiv := ((hg.clm_apply hsx).congr_of_eventuallyEq (f₁ := s₀ ∘ (extChartAt I x₀).symm)
    (by filter_upwards [hnhds] with y hy using htrans _ hy)
    (by simpa only [Function.comp_apply, hinv] using htrans x ⟨hex, hx.1⟩)).fderivWithin
    (I.uniqueDiffOn _ (mem_range_self _))
  rw [FirstJet.trivializationAt_apply hx, coords_firstJetExtension]
  simp only [Function.comp_apply, hinv] at hderiv
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only [firstJetPullback_apply]
    exact (htrans x ⟨hex, hx.1⟩).symm
  · rw [hderiv, firstJetPullback_apply, add_comm]

/-- The jet extension of a `C^n` section is a `C^m` section of the first-jet bundle when
`m + 1 ≤ n`; in particular (`m = n = ∞`) that of a smooth section is smooth. -/
theorem contMDiff_firstJetExtension {n m : WithTop ℕ∞} [IsManifold I n M] {s : ∀ x, V x}
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x))) (hmn : m + 1 ≤ n) :
    ContMDiff I (I.prod 𝓘(𝕜, F × (E →L[𝕜] F))) m
      (fun x ↦ TotalSpace.mk' (F × (E →L[𝕜] F)) x (firstJetExtension I F s x)) := by
  intro x₀
  rw [Bundle.contMDiffAt_section]
  have hloc : ContMDiffAt I 𝓘(𝕜, F) n (fun z ↦ (trivializationAt F V x₀ ⟨z, s z⟩).2) x₀ :=
    (Bundle.contMDiffAt_section x₀).1 (hs x₀)
  have hU : (trivializationAt F V x₀).baseSet ∩ (chartAt H x₀).source ∈ 𝓝 x₀ :=
    ((trivializationAt F V x₀).open_baseSet.inter (chartAt H x₀).open_source).mem_nhds
      ⟨mem_baseSet_trivializationAt F V x₀, mem_chart_source H x₀⟩
  have hn : n ≠ 0 := ne_bot_of_le_ne_bot (by simp) hmn
  refine ((hloc.of_le (le_self_add.trans hmn)).prodMk_space
    (hloc.fderivWithin_comp_extChartAt_symm (mem_chart_source H x₀) hmn)).congr_of_eventuallyEq ?_
  filter_upwards [hU] with x hx
  rw [trivializationAt_firstJetExtension ((hs x).mdifferentiableAt hn) hx]

/-- For the trivial bundle over a normed space, the coordinates of the jet extension of `s` at
`x` are the value `s x` and the Fréchet derivative `fderiv 𝕜 s x`. -/
theorem coords_firstJetExtension_trivial (s : E → F) (x : E) :
    FirstJet.coords 𝓘(𝕜, E) F (Bundle.Trivial E F) x (firstJetExtension 𝓘(𝕜, E) F s x) =
      (s x, fderiv 𝕜 s x) := by
  -- The trivialization of the trivial bundle is the identity on fibres.
  have he : (fun z ↦ (trivializationAt F (Bundle.Trivial E F) x ⟨z, s z⟩).2) = s := rfl
  rw [coords_firstJetExtension]
  refine Prod.ext (congrFun he x) ?_
  rw [he]
  simp

end JetExtension

end TauCeti
