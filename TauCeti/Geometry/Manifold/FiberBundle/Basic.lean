/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.ContMDiff.Groupoid

/-!
# Smooth fibre bundles with a manifold as fibre

Let `E` be a fibre bundle over a manifold `B` modelled on `IB`, whose model fibre `F` is itself a
manifold modelled on `IF`. It is a `C^n` fibre bundle, `TauCeti.ContMDiffFiberBundle n F E IB IF`,
when the coordinate changes `(b, v) ↦ e.coordChange e' b v` between the trivializations of its
atlas are `C^n` maps on the product manifold `B × F` over the overlaps of their base sets. For a
fibre that is a normed space with its self model, every `C^n` vector bundle is such a bundle.

The total space of a `C^n` fibre bundle is then a `C^n` manifold modelled on `IB.prod IF`: its
charts are the trivializations of the atlas followed by product charts of `B × F`. Mathlib already
charts the total space of every fibre bundle by `FiberBundle.chartedSpace`, modelled on
`ModelProd HB F` with the fibre `F` itself as fibre model, and `ChartedSpace` determines its model.
The new atlas therefore lives on the type copy `TauCeti.ManifoldTotalSpace F E`, which carries the
topology of `Bundle.TotalSpace F E` and is identified with it by the homeomorphism
`TauCeti.ManifoldTotalSpace.homeomorph`. No second topology is introduced. When `F` is a normed
space with its self model, this identification is a `C^n` diffeomorphism to Mathlib's charts.

The main tool for maps into the total space is `TauCeti.ManifoldTotalSpace.contMDiffWithinAt_iff`,
which mirrors Mathlib's `Bundle.contMDiffWithinAt_totalSpace_iff`: a map is `C^n` exactly when its
projection to the base is `C^n` and its fibre coordinate in the trivialization at the base point
is `C^n` into `F`. The trivializations of the atlas are `C^n` on their sources with `C^n` inverses,
and the projection is `C^n`.

Maps out of the base descend smoothly along the projection. For any `b₀ : B` and `v : F`, the
local section `b ↦ e⁻¹ (b, v)` of the preferred trivialization `e` at `b₀` is `C^n` at `b₀`.
In particular, every point `x` of the total space lies on such a section at its base point, with
constant fibre coordinate `(e x).2`. A map `h` out of the base therefore agrees, near the
base point of `x`, with the composite of `h ∘ π` and this section, so `h` is `C^n` at the base point
of `x` exactly when `h ∘ π` is `C^n` at `x`. When the fibre is nonempty the projection is
surjective, so a `C^n` map on the total space that is constant on the fibres descends uniquely to a
`C^n` map on the base. These descent statements use neither smoothness of the coordinate changes
nor `IsManifold` instances. For a principal bundle, a map on the total space invariant under the
right action is constant on the fibres, because each fibre is a single orbit.

## Main definitions

* `TauCeti.ContMDiffFiberBundle n F E IB IF`: the coordinate changes of the atlas are `C^n`.
* `TauCeti.ManifoldTotalSpace F E`: a copy of the total space charted through the charts of the
  fibre, modelled on `ModelProd HB HF`.
* `TauCeti.ManifoldTotalSpace.fiberwiseMap`: the map of charted total spaces induced by a family
  `∀ b, E b → E' b`, with no continuity assumed. It represents bundle maps over a fixed base.

## Main results

* `TauCeti.ManifoldTotalSpace.isManifold`: the total space of a `C^n` fibre bundle is a `C^n`
  manifold modelled on `IB.prod IF`.
* `TauCeti.ManifoldTotalSpace.contMDiffWithinAt_iff` and `contMDiffAt_iff`: maps into the total
  space are `C^n` exactly when their projection and their fibre coordinate are.
* `TauCeti.ManifoldTotalSpace.extChartAt_proj_extChartAt_symm`: in preferred charts, the projection
  is the first coordinate.
* `TauCeti.ManifoldTotalSpace.contMDiff_proj`: the projection is `C^n`.
* `TauCeti.ManifoldTotalSpace.contMDiffAt_trivializationAt_symm` and
  `TauCeti.ManifoldTotalSpace.contMDiffAt_totalSpaceMk_trivializationAt_symm`: the local section of
  the preferred trivialization with any constant fibre coordinate is `C^n` at its centre, using
  either the total-space inverse or the fibre-valued inverse followed by `TotalSpace.mk`.
* `TauCeti.ManifoldTotalSpace.contMDiffWithinAt_comp_proj_iff` and `contMDiffAt_comp_proj_iff`: a
  map out of the base is `C^n` at the base point of `x` exactly when its composite with the
  projection is `C^n` at `x`.
* `TauCeti.ManifoldTotalSpace.contMDiffOn_comp_proj_iff` and `contMDiff_comp_proj_iff`: for a
  nonempty fibre, the same on a set of the base and globally.
* `TauCeti.ManifoldTotalSpace.existsUnique_contMDiff_comp_proj_eq`: a `C^n` map constant on the
  fibres is the composite of a unique `C^n` map of the base with the projection.
* `TauCeti.ManifoldTotalSpace.contMDiffAt_trivializationAt_snd`: near each point, the fibre
  coordinate in the trivialization at its base point is `C^n`.
* `TauCeti.ManifoldTotalSpace.contMDiffOn_trivialization` and `contMDiffOn_trivialization_symm`:
  the trivializations of the atlas are `C^n` with `C^n` inverses.
* `TauCeti.ManifoldTotalSpace.contMDiff_homeomorph` and `contMDiff_homeomorph_symm`: for a normed
  space fibre with its self model, the new charts are `C^n` compatible with
  `FiberBundle.chartedSpace`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §9.1 and §9.2 (fibre bundles, their atlases and smooth transition functions).
* The characterization of maps into the total space follows the proof of Mathlib's
  `Bundle.contMDiffWithinAt_totalSpace_iff`, with a manifold fibre model in place of the fibre.
* The groupoid compatibility of the atlas and the resulting `IsManifold` instance follow Mathlib's
  `ContMDiffFiberwiseLinear.hasGroupoid` and `Bundle.TotalSpace.isManifold`, generalized from
  fibrewise-linear transitions to `TauCeti.contMDiffGroupoid`.
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorems 4.26 (local sections of submersions), 4.29 (characteristic property of
  surjective submersions) and 4.30 (passing smoothly to the quotient), for smooth descent.
-/

public section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {n : ℕ∞ω} {𝕜 B F M : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]

section ManifoldFiber

variable {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [FiberBundle F E]

variable (n F E IB IF) in
/-- A fibre bundle `E` over a manifold `B` modelled on `IB`, whose model fibre `F` is a manifold
modelled on `IF`, is a `C^n` fibre bundle when the coordinate changes between any two
trivializations of its atlas are `C^n` maps of `B × F` to `F` over the overlap of their base sets.
The base component of a coordinate change is the identity, so this makes the transition maps of
the atlas `C^n` maps of the product manifold `B × F`. -/
class ContMDiffFiberBundle : Prop where
  protected contMDiffOn_coordChange :
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContMDiffOn (IB.prod IF) IF n (fun p : B × F ↦ e.coordChange e' p.1 p.2)
        ((e.baseSet ∩ e'.baseSet) ×ˢ univ)

namespace ContMDiffFiberBundle

/-- A `C^n` fibre bundle is a `C^m` fibre bundle for `m ≤ n`. -/
protected theorem of_le {m : ℕ∞ω} (hmn : m ≤ n) [h : ContMDiffFiberBundle n F E IB IF] :
    ContMDiffFiberBundle m F E IB IF :=
  ⟨fun e e' _ _ ↦ (h.contMDiffOn_coordChange e e').of_le hmn⟩

variable [ContMDiffFiberBundle n F E IB IF]

variable (IB IF) in
/-- The transition map between two trivializations of the atlas of a `C^n` fibre bundle is `C^n`
on its source, as a map of the product manifold `B × F`. -/
theorem contMDiffOn_symm_trans (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] :
    ContMDiffOn (IB.prod IF) (IB.prod IF) n
      (e.toOpenPartialHomeomorph.symm ≫ₕ e'.toOpenPartialHomeomorph)
      ((e.baseSet ∩ e'.baseSet) ×ˢ univ) := by
  refine (contMDiffOn_fst.prodMk (ContMDiffFiberBundle.contMDiffOn_coordChange e e')).congr ?_
  rintro ⟨b, v⟩ ⟨hb, -⟩
  exact (e.mk_coordChange e' hb.1 hb.2 v).symm

/-- The trivializations of a `C^n` fibre bundle, viewed as charts of the total space with values
in the manifold `B × F`, have transition maps in the groupoid of `C^n` local diffeomorphisms of
`B × F`. -/
instance hasGroupoid :
    HasGroupoid (TotalSpace F E) (contMDiffGroupoid (IB.prod IF) n (B × F)) where
  compatible := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    have : MemTrivializationAtlas e := ⟨he⟩
    have : MemTrivializationAtlas e' := ⟨he'⟩
    refine mem_contMDiffGroupoid_iff.2 ⟨?_, ?_⟩
    · -- The source of the transition map is the product of the base overlap with the fibre.
      have hs : (e.toOpenPartialHomeomorph.symm ≫ₕ e'.toOpenPartialHomeomorph).source =
          (e.baseSet ∩ e'.baseSet) ×ˢ univ := e.symm_trans_source_eq e'
      exact hs ▸ contMDiffOn_symm_trans IB IF e e'
    · -- The inverse of the transition map from `e` to `e'` is the transition map from `e'` to `e`.
      have hs : (e.toOpenPartialHomeomorph.symm ≫ₕ e'.toOpenPartialHomeomorph).target =
          (e'.baseSet ∩ e.baseSet) ×ˢ univ := by
        rw [inter_comm]
        exact e.symm_trans_target_eq e'
      rw [hs, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm]
      exact contMDiffOn_symm_trans IB IF e' e

end ContMDiffFiberBundle

variable (n B F IB IF) in
/-- The trivial bundle `B × F` with a manifold `F` as fibre is a `C^n` fibre bundle: its atlas
consists of a single trivialization, whose coordinate change with itself is the identity. -/
instance ContMDiffFiberBundle.trivial : ContMDiffFiberBundle n F (Bundle.Trivial B F) IB IF where
  contMDiffOn_coordChange e e' _ _ := by
    obtain rfl := Bundle.Trivial.eq_trivialization B F e
    obtain rfl := Bundle.Trivial.eq_trivialization B F e'
    exact contMDiffOn_snd.congr fun p _ ↦
      Trivialization.coordChange_same_apply _ (by simp) p.2

variable (F E) in
/-- A copy of the total space of a fibre bundle whose model fibre `F` is a manifold modelled on
`HF`. It carries the topology of `Bundle.TotalSpace F E` and the charts obtained by following the
trivializations of the atlas with product charts of `B × F`, modelled on `ModelProd HB HF`. -/
-- Lean's module system needs this body to compile the instances on the copy and its carrier maps.
@[expose] def ManifoldTotalSpace := TotalSpace F E

namespace ManifoldTotalSpace

/-- The copy carries the topology of the total space. -/
instance : TopologicalSpace (ManifoldTotalSpace F E) :=
  inferInstanceAs (TopologicalSpace (TotalSpace F E))

variable (F E) in
/-- The identity homeomorphism from the total space to its copy charted through the fibre. -/
def homeomorph : TotalSpace F E ≃ₜ ManifoldTotalSpace F E where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

section FiberwiseMap

omit [TopologicalSpace B] [∀ b, TopologicalSpace (E b)] [TopologicalSpace F] [FiberBundle F E]

variable {E' : B → Type*} [TopologicalSpace (TotalSpace F E')]

/-- The map on charted total spaces induced by a family of maps between fibres over the same
base. No continuity or smoothness of the family is assumed. -/
def fiberwiseMap (φ : ∀ b, E b → E' b) (x : ManifoldTotalSpace F E) :
    ManifoldTotalSpace F E' :=
  homeomorph F E' ⟨((homeomorph F E).symm x).proj, φ _ ((homeomorph F E).symm x).2⟩

/-- A fibrewise map evaluated on a point transported from the original total space. -/
@[simp]
theorem fiberwiseMap_homeomorph (φ : ∀ b, E b → E' b) (p : TotalSpace F E) :
    fiberwiseMap φ (homeomorph F E p) = homeomorph F E' ⟨p.proj, φ _ p.2⟩ := by
  unfold fiberwiseMap
  rw [Homeomorph.symm_apply_apply]

/-- Reading a fibrewise map back in the original total space evaluates the map on its fibre. -/
@[simp]
theorem homeomorph_symm_fiberwiseMap (φ : ∀ b, E b → E' b) (x : ManifoldTotalSpace F E) :
    (homeomorph F E').symm (fiberwiseMap φ x) =
      ⟨((homeomorph F E).symm x).proj, φ _ ((homeomorph F E).symm x).2⟩ := by
  simp [fiberwiseMap]

end FiberwiseMap

/-- The copy is charted by the trivializations of the atlas followed by the charts of the product
manifold `B × F`. -/
instance : ChartedSpace (ModelProd HB HF) (ManifoldTotalSpace F E) :=
  ChartedSpace.comp (ModelProd HB HF) (B × F) (TotalSpace F E)

/-- The preferred chart at a point is the trivialization at its base point followed by the
product of the charts of the base and of the fibre at its coordinates. -/
theorem chartAt_homeomorph (x : TotalSpace F E) :
    chartAt (ModelProd HB HF) (homeomorph F E x) =
      (homeomorph F E).symm.transOpenPartialHomeomorph
        ((trivializationAt F E x.proj).toOpenPartialHomeomorph ≫ₕ
          (chartAt HB x.proj).prod (chartAt HF (trivializationAt F E x.proj x).2)) := by
  have hx : (trivializationAt F E x.proj x).1 = x.proj :=
    (trivializationAt F E x.proj).coe_fst' (mem_baseSet_trivializationAt F E x.proj)
  -- By definition of `ChartedSpace.comp`, the chart is the trivialization at `x.proj` followed by
  -- the product chart at the point `trivializationAt F E x.proj x` of `B × F`.
  have h : chartAt (ModelProd HB HF) (homeomorph F E x) =
      (homeomorph F E).symm.transOpenPartialHomeomorph
        ((trivializationAt F E x.proj).toOpenPartialHomeomorph ≫ₕ
          (chartAt HB (trivializationAt F E x.proj x).1).prod
            (chartAt HF (trivializationAt F E x.proj x).2)) :=
    rfl
  rw [h, hx]

/-- In the preferred extended chart at `x`, a point `y` of the total space has coordinates the
extended charts of the base and of the fibre applied to its coordinates in the trivialization at
the base point of `x`. -/
theorem extChartAt_homeomorph_apply (x y : TotalSpace F E) :
    extChartAt (IB.prod IF) (homeomorph F E x) (homeomorph F E y) =
      (extChartAt IB x.proj (trivializationAt F E x.proj y).1,
        extChartAt IF (trivializationAt F E x.proj x).2 (trivializationAt F E x.proj y).2) := by
  -- Unfold the extended chart into the trivialization followed by the product model and chart.
  simp only [extChartAt_coe, Function.comp_apply, chartAt_homeomorph,
    Homeomorph.transOpenPartialHomeomorph_apply, Homeomorph.symm_apply_apply,
    OpenPartialHomeomorph.coe_trans, Trivialization.coe_coe, modelWithCorners_prod_coe]
  -- The product chart acts componentwise. Its codomain is the synonym `ModelProd HB HF`, which
  -- keeps `simp` from matching `OpenPartialHomeomorph.prod_apply`, so it is rewritten instead.
  rw [OpenPartialHomeomorph.prod_apply, Prod.map_apply]

/-- Read through the inverse of a preferred extended chart of the total space, the projection
followed by the extended chart of the base at the same base point is the first coordinate. -/
theorem extChartAt_proj_extChartAt_symm (x : TotalSpace F E) {y : EB × EF}
    (hy : y ∈ (extChartAt (IB.prod IF) (homeomorph F E x)).target) :
    extChartAt IB x.proj
        ((homeomorph F E).symm ((extChartAt (IB.prod IF) (homeomorph F E x)).symm y)).proj =
      y.1 := by
  obtain ⟨w, hw⟩ :=
    (homeomorph F E).surjective ((extChartAt (IB.prod IF) (homeomorph F E x)).symm y)
  rw [← hw, Homeomorph.symm_apply_apply]
  -- The point `w` lies in the source of the trivialization at the base point of `x`.
  have hws : w ∈ (trivializationAt F E x.proj).source := by
    have h := (extChartAt (IB.prod IF) (homeomorph F E x)).map_target hy
    rw [← hw, extChartAt_source, chartAt_homeomorph] at h
    simp only [Homeomorph.transOpenPartialHomeomorph_source, mem_preimage,
      Homeomorph.symm_apply_apply, OpenPartialHomeomorph.trans_source] at h
    exact h.1
  have hy' := (extChartAt (IB.prod IF) (homeomorph F E x)).right_inv hy
  rw [← hw, extChartAt_homeomorph_apply] at hy'
  rw [← hy', (trivializationAt F E x.proj).coe_fst'
    ((trivializationAt F E x.proj).mem_source.1 hws)]

/-- A map into the total space is `C^n` within a set at a point, for the charts through the fibre,
exactly when its projection to the base and its fibre coordinate in the trivialization at the base
point are `C^n` there. -/
protected theorem contMDiffWithinAt_iff {f : M → TotalSpace F E} {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB.prod IF) n (fun x ↦ homeomorph F E (f x)) s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x ↦ (f x).proj) s x₀ ∧
        ContMDiffWithinAt IM IF n (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) s x₀ := by
  have hc : ContinuousWithinAt (fun x ↦ homeomorph F E (f x)) s x₀ ↔ ContinuousWithinAt f s x₀ :=
    (homeomorph F E).comp_continuousWithinAt_iff f s x₀
  simp +singlePass only [contMDiffWithinAt_iff_target]
  rw [and_and_and_comm, ← FiberBundle.continuousWithinAt_totalSpace, hc, and_congr_right_iff]
  intro hf
  rw [contMDiffWithinAt_prod_module_iff]
  have h1 : (fun x ↦ (f x).proj) ⁻¹' (trivializationAt F E (f x₀).proj).baseSet ∈ 𝓝[s] x₀ :=
    ((FiberBundle.continuous_proj F E).continuousWithinAt.comp hf (mapsTo_image f s))
      ((Trivialization.open_baseSet _).mem_nhds (mem_baseSet_trivializationAt F E _))
  refine and_congr (EventuallyEq.contMDiffWithinAt_iff (eventually_of_mem h1 fun x hx ↦ ?_) ?_)
    (EventuallyEq.contMDiffWithinAt_iff (Eventually.of_forall fun x ↦ ?_) ?_)
  · simp only [Function.comp_apply, extChartAt_homeomorph_apply]
    rw [Trivialization.coe_fst' _ hx]
  · simp only [Function.comp_apply, extChartAt_homeomorph_apply]
    rw [Trivialization.coe_fst' _ (mem_baseSet_trivializationAt F E (f x₀).proj)]
  · simp only [Function.comp_apply, extChartAt_homeomorph_apply]
  · simp only [Function.comp_apply, extChartAt_homeomorph_apply]

/-- A map into the total space is `C^n` at a point, for the charts through the fibre, exactly when
its projection to the base and its fibre coordinate in the trivialization at the base point are
`C^n` there. -/
protected theorem contMDiffAt_iff {f : M → TotalSpace F E} {x₀ : M} :
    ContMDiffAt IM (IB.prod IF) n (fun x ↦ homeomorph F E (f x)) x₀ ↔
      ContMDiffAt IM IB n (fun x ↦ (f x).proj) x₀ ∧
        ContMDiffAt IM IF n (fun x ↦ (trivializationAt F E (f x₀).proj (f x)).2) x₀ := by
  simp_rw [← contMDiffWithinAt_univ]
  exact ManifoldTotalSpace.contMDiffWithinAt_iff

variable (n F E IB IF) in
/-- The projection of the total space to the base is `C^n`. -/
theorem contMDiff_proj :
    ContMDiff (IB.prod IF) IB n fun x : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm x).proj :=
  fun x ↦ (ManifoldTotalSpace.contMDiffAt_iff.1 (contMDiffAt_id (x := x).congr_of_eventuallyEq
    (.of_forall (homeomorph F E).apply_symm_apply))).1

variable (n IB IF) in
/-- Near a point `x` of the total space, the fibre coordinate in the trivialization at the base
point of `x` is `C^n`. -/
theorem contMDiffAt_trivializationAt_snd (x : ManifoldTotalSpace F E) :
    ContMDiffAt (IB.prod IF) IF n
      (fun y ↦ (trivializationAt F E ((homeomorph F E).symm x).proj ((homeomorph F E).symm y)).2)
      x :=
  (ManifoldTotalSpace.contMDiffAt_iff.1 (contMDiffAt_id (x := x).congr_of_eventuallyEq
    (.of_forall (homeomorph F E).apply_symm_apply))).2

/-- The local section of the preferred trivialization with constant fibre coordinate `v` is
`C^n` at its centre. Smoothness of the bundle's coordinate changes is not needed. -/
theorem contMDiffAt_trivializationAt_symm (b₀ : B) (v : F) :
    ContMDiffAt IB (IB.prod IF) n
      (fun b ↦ homeomorph F E ((trivializationAt F E b₀).toOpenPartialHomeomorph.symm (b, v)))
      b₀ := by
  set e := trivializationAt F E b₀
  have hx : b₀ ∈ e.baseSet := mem_baseSet_trivializationAt F E b₀
  have hb : (e.toOpenPartialHomeomorph.symm (b₀, v)).proj = b₀ := e.proj_symm_apply' hx
  refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨contMDiffAt_id.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [e.open_baseSet.mem_nhds hx] with b hb
    exact e.proj_symm_apply' hb
  · rw [hb]
    refine (contMDiffAt_const (c := v)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hx] with b hb
    exact congrArg Prod.snd (e.apply_symm_apply' hb)

/-- The fibre-valued inverse of the preferred trivialization with constant coordinate `v`
defines a `C^n` local section at its centre. -/
theorem contMDiffAt_totalSpaceMk_trivializationAt_symm [∀ b, Nonempty (E b)] (b₀ : B) (v : F) :
    ContMDiffAt IB (IB.prod IF) n
      (fun b ↦ homeomorph F E ⟨b, (trivializationAt F E b₀).symm b v⟩) b₀ := by
  refine (contMDiffAt_trivializationAt_symm b₀ v).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt F E b₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E b₀)] with b hb
  exact congrArg (homeomorph F E) ((trivializationAt F E b₀).mk_symm hb v)

/-! #### Descent along the projection -/

/-- A map `h` out of the base is `C^n` within `s` at the base point of `x` exactly when its
composite with the projection is `C^n` within the preimage of `s` at `x`. -/
@[simp]
theorem contMDiffWithinAt_comp_proj_iff {h : B → M} {s : Set B} {x : TotalSpace F E} :
    ContMDiffWithinAt (IB.prod IF) IM n (fun y ↦ h ((homeomorph F E).symm y).proj)
        ((fun y ↦ ((homeomorph F E).symm y).proj) ⁻¹' s) (homeomorph F E x) ↔
      ContMDiffWithinAt IB IM n h s x.proj := by
  refine ⟨fun hh ↦ ?_, fun hh ↦ hh.comp_of_eq (contMDiff_proj n F E IB IF _).contMDiffWithinAt
    (mapsTo_preimage _ _) (by simp)⟩
  set e := trivializationAt F E x.proj
  have hx : x.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E x.proj
  have hsx : e.toOpenPartialHomeomorph.symm (x.proj, (e x).2) = x :=
    e.symm_apply_mk_proj (e.mem_source.2 hx)
  -- Near the base point of `x`, the map `h` is the composite of `h ∘ π` with the local section of
  -- `e` through `x`.
  rw [← contMDiffWithinAt_inter (e.open_baseSet.mem_nhds hx)]
  refine (hh.comp_of_eq (contMDiffAt_trivializationAt_symm x.proj (e x).2).contMDiffWithinAt
    (fun b hb ↦ ?_) (by simp [e, hsx])).congr (fun b hb ↦ ?_) (by simp [e, hsx])
  · simpa [(trivializationAt F E x.proj).proj_symm_apply' hb.2] using hb.1
  · simp [(trivializationAt F E x.proj).proj_symm_apply' hb.2]

/-- A map `h` out of the base is `C^n` at the base point of `x` exactly when its composite with the
projection is `C^n` at `x`. -/
@[simp]
theorem contMDiffAt_comp_proj_iff {h : B → M} {x : TotalSpace F E} :
    ContMDiffAt (IB.prod IF) IM n (fun y ↦ h ((homeomorph F E).symm y).proj) (homeomorph F E x) ↔
      ContMDiffAt IB IM n h x.proj := by
  simpa only [preimage_univ, contMDiffWithinAt_univ] using
    contMDiffWithinAt_comp_proj_iff (s := univ) (x := x) (h := h) (IF := IF) (n := n)

/-- For a nonempty fibre, a map `h` out of the base is `C^n` on `s` exactly when its composite with
the projection is `C^n` on the preimage of `s`. -/
@[simp]
theorem contMDiffOn_comp_proj_iff [Nonempty F] {h : B → M} {s : Set B} :
    ContMDiffOn (IB.prod IF) IM n (fun y ↦ h ((homeomorph F E).symm y).proj)
        ((fun y ↦ ((homeomorph F E).symm y).proj) ⁻¹' s) ↔ ContMDiffOn IB IM n h s := by
  refine ⟨fun hh b hb ↦ ?_, fun hh y hy ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := FiberBundle.surjective_proj F E b
    exact contMDiffWithinAt_comp_proj_iff.1 (hh _ (by simpa using hb))
  · obtain ⟨x, rfl⟩ := (homeomorph F E).surjective y
    exact contMDiffWithinAt_comp_proj_iff.2 (hh _ (by simpa using hy))

/-- For a nonempty fibre, a map out of the base is `C^n` exactly when its composite with the
projection is `C^n`. -/
@[simp]
theorem contMDiff_comp_proj_iff [Nonempty F] {h : B → M} :
    ContMDiff (IB.prod IF) IM n (fun y ↦ h ((homeomorph F E).symm y).proj) ↔
      ContMDiff IB IM n h := by
  simpa only [preimage_univ, contMDiffOn_univ] using
    contMDiffOn_comp_proj_iff (s := univ) (h := h) (IF := IF) (n := n)

/-- **Smooth descent along the projection.** For a nonempty fibre, a `C^n` map `g` on the total
space that is constant on each fibre is the composite of a unique `C^n` map of the base with the
projection. -/
theorem existsUnique_contMDiff_comp_proj_eq [Nonempty F] {g : ManifoldTotalSpace F E → M}
    (hg : ContMDiff (IB.prod IF) IM n g)
    (hfib : ∀ x y : TotalSpace F E, x.proj = y.proj → g (homeomorph F E x) = g (homeomorph F E y)) :
    ∃! h : B → M, ContMDiff IB IM n h ∧ ∀ x : TotalSpace F E, h x.proj = g (homeomorph F E x) := by
  have hπ := FiberBundle.surjective_proj F E
  have hh : ∀ x : TotalSpace F E,
      g (homeomorph F E (Function.surjInv hπ x.proj)) = g (homeomorph F E x) :=
    fun x ↦ hfib _ _ (Function.surjInv_eq hπ x.proj)
  refine ⟨fun b ↦ g (homeomorph F E (Function.surjInv hπ b)),
    ⟨(contMDiff_comp_proj_iff (F := F) (E := E) (IF := IF)).1 ?_, hh⟩, ?_⟩
  · refine hg.congr fun y ↦ ?_
    obtain ⟨x, rfl⟩ := (homeomorph F E).surjective y
    simp [hh]
  · rintro h' ⟨-, hh'⟩
    funext b
    obtain ⟨x, rfl⟩ := hπ b
    rw [hh', hh]

variable [ContMDiffFiberBundle n F E IB IF]

/-- A trivialization of the atlas of a `C^n` fibre bundle is `C^n` on its source, as a map from the
total space to the product manifold `B × F`. -/
theorem contMDiffOn_trivialization (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    ContMDiffOn (IB.prod IF) (IB.prod IF) n (fun x ↦ e ((homeomorph F E).symm x))
      ((homeomorph F E).symm ⁻¹' e.source) := by
  intro x hx
  obtain ⟨z, rfl⟩ := (homeomorph F E).surjective x
  rw [mem_preimage, Homeomorph.symm_apply_apply, e.mem_source] at hx
  let e₀ := trivializationAt F E z.proj
  have hz : z.proj ∈ e₀.baseSet := mem_baseSet_trivializationAt F E z.proj
  -- Near `z`, the projection and the fibre coordinate in `e₀` are `C^n`.
  have hproj := contMDiff_proj n F E IB IF (homeomorph F E z)
  have hcoord := contMDiffAt_trivializationAt_snd n IB IF (homeomorph F E z)
  simp only [Homeomorph.symm_apply_apply] at hcoord
  -- The fibre coordinate in `e` is the coordinate change from `e₀` to `e` applied to it.
  have hchange : ContMDiffAt (IB.prod IF) IF n (fun p : B × F ↦ e₀.coordChange e p.1 p.2)
      (z.proj, (e₀ z).2) :=
    (ContMDiffFiberBundle.contMDiffOn_coordChange e₀ e).contMDiffAt
      (((e₀.open_baseSet.inter e.open_baseSet).prod isOpen_univ).mem_nhds ⟨⟨hz, hx⟩, mem_univ _⟩)
  have hU : (fun y ↦ ((homeomorph F E).symm y).proj) ⁻¹' (e₀.baseSet ∩ e.baseSet) ∈
      𝓝 (homeomorph F E z) :=
    ((contMDiff_proj n F E IB IF).continuous.isOpen_preimage _
      (e₀.open_baseSet.inter e.open_baseSet)).mem_nhds (by simpa using ⟨hz, hx⟩)
  refine ((hproj.prodMk (hchange.comp_of_eq (hproj.prodMk hcoord) (by simp [e₀]))
    ).congr_of_eventuallyEq (eventually_of_mem hU fun y hy ↦ ?_)).contMDiffWithinAt
  exact Prod.ext (e.coe_fst' hy.2) (e₀.coordChange_apply_snd e hy.1).symm

/-- The inverse of a trivialization of the atlas of a `C^n` fibre bundle is `C^n` on its target,
as a map from the product manifold `B × F` to the total space. -/
theorem contMDiffOn_trivialization_symm (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] :
    ContMDiffOn (IB.prod IF) (IB.prod IF) n
      (fun p ↦ homeomorph F E (e.toOpenPartialHomeomorph.symm p)) e.target := by
  intro p hp
  have hproj : (e.toOpenPartialHomeomorph.symm p).proj = p.1 := e.proj_symm_apply hp
  let e₀ := trivializationAt F E p.1
  have hp₀ : p ∈ (e.baseSet ∩ e₀.baseSet) ×ˢ univ :=
    ⟨⟨e.mem_target.1 hp, mem_baseSet_trivializationAt F E p.1⟩, mem_univ _⟩
  refine (ManifoldTotalSpace.contMDiffAt_iff.2 ⟨?_, ?_⟩).contMDiffWithinAt
  · -- On the target of `e`, the projection of the inverse of `e` is the first coordinate.
    refine contMDiffAt_fst.congr_of_eventuallyEq
      (eventually_of_mem (e.open_target.mem_nhds hp) fun q hq ↦ e.proj_symm_apply hq)
  · rw [hproj]
    -- By definition of `coordChange`, the fibre coordinate in `e₀` of the inverse of `e` is the
    -- coordinate change from `e` to `e₀`.
    exact (ContMDiffFiberBundle.contMDiffOn_coordChange e e₀).contMDiffAt
      (((e.open_baseSet.inter e₀.open_baseSet).prod isOpen_univ).mem_nhds hp₀)

variable (n F E IB IF) in
/-- The total space of a `C^n` fibre bundle over a `C^n` manifold, with a `C^n` manifold as fibre,
is a `C^n` manifold modelled on `IB.prod IF`. -/
instance isManifold [IsManifold IB n B] [IsManifold IF n F] :
    IsManifold (IB.prod IF) n (ManifoldTotalSpace F E) :=
  isManifold_of_hasGroupoid_contMDiffGroupoid (IB.prod IF) n (TotalSpace F E)

end ManifoldTotalSpace

end ManifoldFiber

/-! ### Normed space fibres with their self model -/

section NormedFiber

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiberBundle F E]

/-- A `C^n` vector bundle is a `C^n` fibre bundle, for its fibre with its self model. -/
instance ContMDiffFiberBundle.ofContMDiffVectorBundle [∀ b, AddCommMonoid (E b)]
    [∀ b, Module 𝕜 (E b)] [VectorBundle 𝕜 F E]
    [ContMDiffVectorBundle n F E IB] : ContMDiffFiberBundle n F E IB 𝓘(𝕜, F) where
  contMDiffOn_coordChange e e' _ _ := by
    have h := contMDiff_snd.comp_contMDiffOn
      (Bundle.Trivialization.contMDiffOn_symm_trans (n := n) IB e e')
    rw [e.target_eq, e'.target_eq, prod_inter_prod, univ_inter] at h
    -- By definition, `e.coordChange e'` is the fibre component of the transition map.
    exact h.congr fun _ _ ↦ rfl

namespace ManifoldTotalSpace

variable (n F E IB) in
/-- For a normed space fibre with its self model, the identification of the total space with its
copy is `C^n` from the charts `FiberBundle.chartedSpace` to the charts through the fibre. -/
theorem contMDiff_homeomorph :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n (homeomorph F E) := fun _ ↦
  ManifoldTotalSpace.contMDiffAt_iff (f := fun y ↦ y).2
    ⟨Bundle.contMDiffAt_proj E, (Bundle.contMDiffAt_totalSpace_iff.1 contMDiffAt_id).2⟩

variable (n F E IB) in
/-- For a normed space fibre with its self model, the identification of the copy of the total
space with the total space is `C^n` from the charts through the fibre to the charts
`FiberBundle.chartedSpace`. -/
theorem contMDiff_homeomorph_symm :
    ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n (homeomorph F E).symm := fun x ↦
  Bundle.contMDiffAt_totalSpace_iff.2 ⟨contMDiff_proj n F E IB 𝓘(𝕜, F) x,
    contMDiffAt_trivializationAt_snd n IB 𝓘(𝕜, F) x⟩

end ManifoldTotalSpace

end NormedFiber

end TauCeti
