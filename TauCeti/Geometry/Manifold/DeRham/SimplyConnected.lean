/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Poincare
public import TauCeti.Geometry.Manifold.MFDeriv.Constancy
public import TauCeti.Geometry.Manifold.Topology
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.WithTopology

/-!
# Closed `1`-forms on simply connected manifolds are exact

On a simply connected manifold every closed `1`-form is the differential of a function
(`TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`), so the first de Rham cohomology vanishes
(`TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`).

The proof is the monodromy argument. By the Poincaré lemma (`TauCeti.exists_mextDeriv_eq_nhds`)
a closed `1`-form `φ` has a primitive near every point, and two primitives on a common open set
differ by a locally constant function. Pairs `(x, a)` of a point and a value are topologized so
that the graphs `{(y, g y) | y ∈ U}` of the primitives `g` of `φ` on open sets `U` form a basis.
Projecting to the point is a covering map: over an open set carrying a primitive `g`, the sheets
are the graphs of the translates `g + c`. A simply connected, locally path-connected base lifts
the identity through every covering map, and the second coordinate of such a lift is a global
primitive of `φ`, since near each point it agrees with a translate of a local primitive.

The Poincaré lemma is where finite dimensionality, the Hausdorff property and completeness of the
coefficient space are used. Manifolds with boundary or corners are included.

## Main declarations

* `TauCeti.exists_mextDeriv_eq_of_simplyConnectedSpace`: a closed `C^r` `1`-form (`1 ≤ r`) with
  values in a complete space on a simply connected manifold has a `C^r` primitive.
* `TauCeti.exactForms_one_eq_closedForms_of_simplyConnectedSpace`: on a simply connected manifold
  every closed smooth real `1`-form is exact.
* `TauCeti.subsingleton_deRhamCohomology_one_of_simplyConnectedSpace`: `H¹_dR(M) = 0` for simply
  connected `M`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section *Conservative
  Covector Fields* (closed covector fields on simply connected manifolds are exact), and
  Chapter 17.
* Allen Hatcher, *Algebraic Topology*, Proposition 1.33 (the lifting criterion).
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Local primitives and the covering space they define -/

/-- `g` is a primitive of the `1`-form `φ` on the open set `U`: it is differentiable on `U` and
its differential agrees with `φ` there. -/
private def IsPrimitiveOn (φ : RoughForm I M F 1) (g : M → F) (U : Set M) : Prop :=
  IsOpen U ∧ MDifferentiableOn I 𝓘(ℝ, F) g U ∧
    ∀ y ∈ U, mextDeriv (RoughForm.ofFunction I g) y = φ y

variable {φ : RoughForm I M F 1} {g h : M → F} {U V : Set M}

private theorem IsPrimitiveOn.mono (hg : IsPrimitiveOn φ g U) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsPrimitiveOn φ g V :=
  ⟨hV, hg.2.1.mono hVU, fun y hy ↦ hg.2.2 y (hVU hy)⟩

private theorem IsPrimitiveOn.add_const (hg : IsPrimitiveOn φ g U) (c : F) :
    IsPrimitiveOn φ (fun y ↦ g y + c) U := by
  refine ⟨hg.1, hg.2.1.add mdifferentiableOn_const, fun y hy ↦ ?_⟩
  rw [mextDeriv_ofFunction_eq_of_eventuallyEq_add_const
    ((hg.2.1 y hy).mdifferentiableAt (hg.1.mem_nhds hy)) (Eventually.of_forall fun _ ↦ rfl)]
  exact hg.2.2 y hy

/-- The set where two primitives of the same `1`-form agree is open: their difference has zero
differential, so it is locally constant. -/
private theorem IsPrimitiveOn.isOpen_setOf_eq [IsManifold I 1 M] (hg : IsPrimitiveOn φ g U)
    (hh : IsPrimitiveOn φ h V) : IsOpen {y | y ∈ U ∧ y ∈ V ∧ g y = h y} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, hyV, hy⟩
  have hUV : IsOpen (U ∩ V) := hg.1.inter hh.1
  have hdiff : MDifferentiableOn I 𝓘(ℝ, F) (g - h) (U ∩ V) :=
    (hg.2.1.mono inter_subset_left).sub (hh.2.1.mono inter_subset_right)
  have hzero : ∀ z ∈ U ∩ V, mfderiv I 𝓘(ℝ, F) (g - h) z = 0 := by
    rintro z ⟨hzU, hzV⟩
    rw [mfderiv_sub ((hg.2.1 z hzU).mdifferentiableAt (hg.1.mem_nhds hzU))
      ((hh.2.1 z hzV).mdifferentiableAt (hh.1.mem_nhds hzV))]
    ext v
    have := congrArg (fun A ↦ A fun _ ↦ v) ((hg.2.2 z hzU).trans (hh.2.2 z hzV).symm)
    simp only [mextDeriv_ofFunction, mvfderiv] at this
    -- `NormedSpace.fromTangentSpace` is the identity of `F`
    exact sub_eq_zero.mpr this
  filter_upwards [hdiff.eventuallyEq_const_of_mfderiv_eq_zero hUV hzero ⟨hyU, hyV⟩,
    hUV.mem_nhds ⟨hyU, hyV⟩] with z hz hzUV
  refine ⟨hzUV.1, hzUV.2, ?_⟩
  simpa [hy, sub_eq_zero] using hz

/-- Pairs of a point and a value, topologized so that the graphs of the primitives of `φ` on open
sets form a basis. -/
private def PrimitiveSpace (_φ : RoughForm I M F 1) : Type _ := M × F

private instance : TopologicalSpace (PrimitiveSpace φ) :=
  .generateFrom {S | ∃ g U, IsPrimitiveOn φ g U ∧ S = (fun y ↦ ((y, g y) : M × F)) '' U}

variable (φ) in
/-- The point underlying an element of `PrimitiveSpace φ`. -/
private def PrimitiveSpace.proj (e : PrimitiveSpace φ) : M := Prod.fst (α := M) (β := F) e

variable (φ) in
/-- The graph of a function, as a map into `PrimitiveSpace φ`. -/
private def PrimitiveSpace.graph (g : M → F) (y : M) : PrimitiveSpace φ := ((y, g y) : M × F)

private theorem PrimitiveSpace.proj_graph (y : M) : proj φ (graph φ g y) = y := rfl

private theorem PrimitiveSpace.snd_graph (y : M) :
    Prod.snd (α := M) (β := F) (graph φ g y) = g y := rfl

/-- Every element of `PrimitiveSpace φ` lies on the graph of the constant function at its
value. -/
private theorem PrimitiveSpace.eq_graph (e : PrimitiveSpace φ) :
    e = graph φ (fun _ ↦ Prod.snd (α := M) (β := F) e) (proj φ e) := rfl

private theorem PrimitiveSpace.isOpen_image_graph (hg : IsPrimitiveOn φ g U) :
    IsOpen (graph φ g '' U) :=
  TopologicalSpace.GenerateOpen.basic _ ⟨g, U, hg, rfl⟩

/-- The graph of a primitive on an open set is continuous there. -/
private theorem PrimitiveSpace.continuousOn_graph [IsManifold I 1 M] (hg : IsPrimitiveOn φ g U) :
    ContinuousOn (graph φ g) U := by
  refine fun y hy ↦ ContinuousAt.continuousWithinAt ?_
  refine TopologicalSpace.tendsto_nhds_generateFrom_iff.mpr ?_
  rintro _ ⟨h, V, hh, rfl⟩ ⟨w, hwV, hw⟩
  obtain ⟨rfl, hwy⟩ := Prod.ext_iff.mp hw
  filter_upwards [(hg.isOpen_setOf_eq hh).mem_nhds ⟨hy, hwV, hwy.symm⟩] with z hz
  exact ⟨z, hz.2.1, Prod.ext_iff.mpr ⟨rfl, hz.2.2.symm⟩⟩

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [CompleteSpace F]

/-- By the Poincaré lemma, a closed `C^r` `1`-form has a `C^r` primitive near every point. -/
private theorem exists_contMDiff_isPrimitiveOn {r : ℕ∞} (hr : 1 ≤ r)
    (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) (x : M) :
    ∃ g : M → F, ContMDiff I 𝓘(ℝ, F) r g ∧ ∃ U, x ∈ U ∧ IsPrimitiveOn φ g U := by
  obtain ⟨U, hU, ψ, hψ, hdψ⟩ :=
    exists_mextDeriv_eq_nhds hr hφ (x := x) (Eventually.of_forall fun y ↦ congrFun hclosed y)
  rw [RoughForm.eq_ofFunction ψ] at hψ hdψ
  have hg := isSmoothForm_ofFunction_iff.mp hψ
  refine ⟨_, hg, interior U, mem_interior_iff_mem_nhds.mpr hU, isOpen_interior,
    (hg.mdifferentiable (by simpa using (zero_lt_one.trans_le hr).ne')).mdifferentiableOn,
    fun y hy ↦ hdψ y (interior_subset hy)⟩

/-- Projecting `PrimitiveSpace φ` to the point is a covering map when `φ` is closed. Over an open
set `U` carrying a primitive `g`, the sheets are the graphs of the translates `g + c`. -/
private theorem PrimitiveSpace.isCoveringMap_proj {r : ℕ∞} (hr : 1 ≤ r) (hφ : IsSmoothForm I r φ)
    (hclosed : mextDeriv φ = 0) : IsCoveringMap (proj φ) := by
  choose g _hg U hxU hgU using exists_contMDiff_isPrimitiveOn hr hφ hclosed
  have : Nonempty (M → PrimitiveSpace φ) := ⟨graph φ 0⟩
  -- the translation constant of a sheet, read in `F`
  let c (i : WithDiscreteTopology F) : F := WithTopology.ofTopology i
  let sheet (x : M) (i : WithDiscreteTopology F) : Set (PrimitiveSpace φ) :=
    graph φ (fun y ↦ g x y + c i) '' U x
  refine IsCoveringMap.mk _ _ (fun x ↦ (hgU x).1.trivializationDiscrete (sheet x) (U x)
    (fun i W hWU ↦ ⟨fun hW ↦ ?_, fun hW ↦ ?_⟩) (fun _ ↦ InjOn.image_of_comp (injOn_id _))
    (fun i y hy ↦ ⟨_, mem_image_of_mem _ hy, proj_graph y⟩) (fun i j hij ↦ ?_) ?_) hxU
  · -- an open subset of `U x` has open preimage in each sheet
    rw [← LeftInvOn.image_inter' (fun _ _ ↦ rfl : LeftInvOn (proj φ) (graph φ _) (U x)),
      inter_eq_left.mpr hWU]
    exact isOpen_image_graph (((hgU x).add_const (c i)).mono hW hWU)
  · -- conversely, an open trace on a sheet comes from an open subset of `U x`
    convert (continuousOn_graph ((hgU x).add_const (c i))).isOpen_inter_preimage (hgU x).1 hW
      using 1
    ext y
    simp only [mem_inter_iff, mem_preimage, proj_graph]
    exact ⟨fun hy ↦ ⟨hWU hy, hy, mem_image_of_mem _ (hWU hy)⟩, fun hy ↦ hy.2.1⟩
  · -- distinct translates have disjoint graphs
    refine disjoint_left.mpr ?_
    rintro _ ⟨y, -, rfl⟩ ⟨z, -, hzy⟩
    obtain ⟨rfl, hzy⟩ := Prod.ext_iff.mp hzy
    exact hij (WithTopology.ofTopology_injective _ (add_left_cancel hzy).symm)
  · -- every point over `U x` lies on the sheet through its value
    intro e he
    refine mem_iUnion.mpr ⟨WithTopology.toTopology _ (Prod.snd (α := M) (β := F) e -
      g x (proj φ e)), proj φ e, he, ?_⟩
    refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
    rw [snd_graph]
    simp only [c, WithTopology.ofTopology_toTopology, add_sub_cancel]

/-! ### Exactness on simply connected manifolds -/

/-- **Closed `1`-forms on simply connected manifolds are exact.** A closed `C^r` `1`-form
(`1 ≤ r`) with values in a complete space on a simply connected manifold is the exterior
derivative of a `C^r` function. -/
theorem exists_mextDeriv_eq_of_simplyConnectedSpace [SimplyConnectedSpace M] {r : ℕ∞}
    (hr : 1 ≤ r) {φ : RoughForm I M F 1} (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0) :
    ∃ ψ : RoughForm I M F 0, IsSmoothForm I r ψ ∧ mextDeriv ψ = φ := by
  have := I.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace H M
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  -- lift the identity of `M` through the covering space of local primitives
  have hp := PrimitiveSpace.isCoveringMap_proj hr hφ hclosed
  obtain ⟨s, ⟨-, hs⟩, -⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id M) x₀ (PrimitiveSpace.graph φ 0 x₀) rfl
  set f : M → F := fun y ↦ Prod.snd (α := M) (β := F) (s y) with hf_def
  have hsf (y : M) : s y = PrimitiveSpace.graph φ f y := by
    rw [PrimitiveSpace.eq_graph (s y)]
    exact Prod.ext_iff.mpr ⟨congrFun hs y, rfl⟩
  -- Near each point `x`, `f` differs by a constant from a local primitive `g` of `φ`.
  refine exists_mextDeriv_eq_of_forall_eventuallyEq_add_const
    (by simpa using (zero_lt_one.trans_le hr).ne') (f := f) fun x ↦ ?_
  obtain ⟨g, hg, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn hr hφ hclosed x
  refine ⟨g, f x - g x, hg x, ?_, hgU.2.2 x hxU⟩
  have hmem : s x ∈ PrimitiveSpace.graph φ (fun y ↦ g y + (f x - g x)) '' U :=
    ⟨x, hxU, by
      rw [hsf]
      refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
      rw [PrimitiveSpace.snd_graph, PrimitiveSpace.snd_graph]
      abel⟩
  filter_upwards [s.continuous.continuousAt.preimage_mem_nhds
    ((PrimitiveSpace.isOpen_image_graph (hgU.add_const (f x - g x))).mem_nhds hmem)]
    with y hy
  obtain ⟨w, -, hw⟩ := hy
  rw [hsf] at hw
  obtain ⟨rfl, hw⟩ := Prod.ext_iff.mp hw
  exact hw.symm

variable (I M) in
/-- On a simply connected manifold every closed smooth real `1`-form is exact. -/
theorem exactForms_one_eq_closedForms_of_simplyConnectedSpace [SimplyConnectedSpace M] :
    exactForms I M 1 = closedForms I M 1 := by
  refine le_antisymm (exactForms_le_closedForms I 1) fun φ hφ ↦ ?_
  obtain ⟨ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_of_simplyConnectedSpace (r := ⊤) le_top
    φ.isSmoothForm ((mem_closedForms I φ).mp hφ)
  rw [exactForms_succ]
  exact ⟨⟨ψ, hψ.mem_smoothBundleForms⟩, Subtype.ext ((mextDerivₗ_apply I 0 _).trans hdψ)⟩

variable (I M) in
/-- **The first de Rham cohomology of a simply connected manifold vanishes.** -/
theorem subsingleton_deRhamCohomology_one_of_simplyConnectedSpace [SimplyConnectedSpace M] :
    Subsingleton (deRhamCohomology I M 1) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective _ _ c
  rw [deRhamCohomology.mk_eq_zero_iff, exactForms_one_eq_closedForms_of_simplyConnectedSpace]
  exact φ.2

end TauCeti
