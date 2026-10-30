/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeology.Subduction

/-!
# Induced and subspace diffeologies

This file constructs the diffeology induced by an arbitrary map `f : Y → X` into a diffeological
space: a map from a Cartesian space to `Y` is a plot precisely when its composite with `f` is a
plot of `X`. This is the coarsest diffeology making `f` smooth, that is, the one with the most
plots, and a map into `Y` is smooth exactly when its composite with `f` is smooth. Inducing
along a composite is inducing twice.

Inducing along `Subtype.val` gives the subspace diffeology on a subtype, the diffeological
counterpart of Mathlib's subspace topology `instTopologicalSpaceSubtype`. It is used to restrict
smooth spaces, such as the coarse spaces of finite quotient charts, to open subsets:

* On a subset that is open for the D-topology, the D-topology of the subspace diffeology is the
  subspace topology of the D-topology (`TauCeti.Diffeology.dTopology_subtype_of_isOpen`). Hence
  the subspace diffeology on an open subset of a space whose topology is its D-topology is
  compatible with the subspace topology (`TauCeti.Diffeology.isDTopologyCompatible_subtype`).
  This fails for general subsets: the plots of `ℚ ⊆ ℝ` are constant, so its D-topology is
  discrete.
* Restricting a subduction `q : X → Q` over any subset `t` of `Q` gives a subduction
  `q ⁻¹' t → t` (`TauCeti.Diffeology.IsSubduction.restrictPreimage`). For the projection onto a
  quotient, for instance the orbit space of a group action, this says that the subspace
  diffeology on a subset of the quotient is the quotient diffeology of its preimage.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapter 1 for pullbacks of diffeologies and subspace diffeologies,
  and Chapter 2 for the D-topology.
-/

public noncomputable section

open Function Set
open scoped ContDiff Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

variable {X Y Z Q : Type*} [DiffeologicalSpace X]

/-! ### Induced diffeologies -/

/-- The diffeology induced by a map into a diffeological space. Its plots are the maps whose
composite with the given map is a plot. This is the pullback diffeology of Iglesias-Zemmour,
*Diffeology*, Chapter 1. -/
@[instance_reducible]
def inducedDiffeology (f : Y → X) : DiffeologicalSpace Y where
  plots _ := {p | _root_.Diffeology.IsPlot (f ∘ p)}
  constant_plots _ := _root_.Diffeology.isPlot_const
  plot_reparam hp hf := _root_.Diffeology.isPlot_reparam hp hf
  locality hp := DiffeologicalSpace.locality fun x ↦
    let ⟨u, hu, hxu, h⟩ := hp x
    ⟨u, hu, hxu, fun hfu hf ↦ h hfu hf⟩

/-- A map is a plot of the induced diffeology exactly when its composite with the inducing map is
a plot. -/
@[simp]
theorem isPlot_inducedDiffeology_iff (f : Y → X) {n : ℕ} {p : 𝔼ⁿ → Y} :
    @_root_.Diffeology.IsPlot Y (inducedDiffeology f) n p ↔ _root_.Diffeology.IsPlot (f ∘ p) :=
  Iff.rfl

/-- A map is smooth for the diffeology it induces. -/
theorem dSmooth_inducedDiffeology_dom (f : Y → X) :
    @_root_.Diffeology.DSmooth Y X (inducedDiffeology f) inferInstance f :=
  fun _ _ hp ↦ hp

/-- A map into an induced diffeology is smooth exactly when its composite with the inducing map is
smooth. -/
@[simp]
theorem dSmooth_inducedDiffeology_rng [DiffeologicalSpace Z] (f : Y → X) (g : Z → Y) :
    @_root_.Diffeology.DSmooth Z Y inferInstance (inducedDiffeology f) g ↔
      _root_.Diffeology.DSmooth (f ∘ g) :=
  Iff.rfl

/-- The induced diffeology is the coarsest diffeology making the map smooth: every plot of a
diffeology making the map smooth is a plot of the induced diffeology. -/
theorem le_inducedDiffeology_iff (f : Y → X) {d : DiffeologicalSpace Y} :
    d ≤ inducedDiffeology f ↔ @_root_.Diffeology.DSmooth Y X d inferInstance f :=
  DiffeologicalSpace.le_iff'.trans Iff.rfl

/-- Inducing a diffeology along a composite is inducing it along each map in turn. -/
theorem inducedDiffeology_comp (f : Y → Z) (g : Z → X) :
    inducedDiffeology (g ∘ f) = @inducedDiffeology Z Y (inducedDiffeology g) f :=
  DiffeologicalSpace.ext rfl

/-! ### Subspace diffeologies -/

/-- The subspace diffeology on a subtype: the diffeology induced by the inclusion. -/
instance instDiffeologicalSpaceSubtype {P : X → Prop} : DiffeologicalSpace (Subtype P) :=
  inducedDiffeology Subtype.val

variable {P : X → Prop}

/-- A map is a plot of a subtype exactly when its composite with the inclusion is a plot. -/
theorem isPlot_subtype_iff {n : ℕ} {p : 𝔼ⁿ → Subtype P} :
    _root_.Diffeology.IsPlot p ↔ _root_.Diffeology.IsPlot (Subtype.val ∘ p) :=
  Iff.rfl

/-- A map is a plot of a subtype on a subset exactly when its composite with the inclusion is a
plot on that subset. -/
@[simp]
theorem isPlotOn_subtype_iff {n : ℕ} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → Subtype P} :
    IsPlotOn u p ↔ IsPlotOn u (Subtype.val ∘ p) := by
  simp only [isPlotOn_iff, isPlot_subtype_iff, comp_assoc]

/-- The inclusion of a subtype is smooth. -/
@[fun_prop]
theorem dSmooth_subtype_val : _root_.Diffeology.DSmooth (Subtype.val : Subtype P → X) :=
  dSmooth_inducedDiffeology_dom Subtype.val

/-- A smooth map with values in a subtype is smooth as a map into the subtype. -/
@[fun_prop]
theorem _root_.Diffeology.DSmooth.subtype_mk [DiffeologicalSpace Y] {f : Y → X}
    (hf : _root_.Diffeology.DSmooth f) (hP : ∀ y, P (f y)) :
    _root_.Diffeology.DSmooth fun y ↦ (⟨f y, hP y⟩ : Subtype P) :=
  (dSmooth_inducedDiffeology_rng Subtype.val _).mpr hf

/-! ### D-topologies of open subspaces -/

/-- On a subset that is open for the D-topology, the D-topology of the subspace diffeology is the
subspace topology of the D-topology. -/
theorem dTopology_subtype_of_isOpen {U : Set X} (hU : IsOpen[_root_.Diffeology.dTopology] U) :
    (_root_.Diffeology.dTopology : TopologicalSpace U) =
      TopologicalSpace.induced Subtype.val _root_.Diffeology.dTopology := by
  classical
  refine le_antisymm (continuous_iff_le_induced.mp dSmooth_subtype_val.continuous) ?_
  rw [TopologicalSpace.le_def]
  intro W hW
  -- `W` is the preimage of its image, so it suffices that the image is open in `X`.
  let : TopologicalSpace X := _root_.Diffeology.dTopology
  refine isOpen_induced_iff.mpr ⟨Subtype.val '' W, ?_, Subtype.val_injective.preimage_image W⟩
  refine _root_.Diffeology.isOpen_iff_preimages_plots.mpr fun n p hp ↦
    isOpen_iff_forall_mem_open.mpr fun z ⟨x, hxW, hx⟩ ↦ ?_
  -- On the open set where `p` lands in `U`, `p` is a plot of the subspace `U`.
  have ho : IsOpen (p ⁻¹' U) := _root_.Diffeology.isOpen_iff_preimages_plots.mp hU n p hp
  let p' : 𝔼ⁿ → U := fun y ↦ if h : p y ∈ U then ⟨p y, h⟩ else x
  have hp' : EqOn p (Subtype.val ∘ p') (p ⁻¹' U) := fun y hy ↦ by
    simp [p', show p y ∈ U from hy]
  have hplot : IsPlotOn (p ⁻¹' U) p' :=
    isPlotOn_subtype_iff.mpr ((isPlotOn_of_isPlot hp _).congr hp')
  have hzU : p z ∈ U := hx ▸ x.2
  let : TopologicalSpace U := _root_.Diffeology.dTopology
  refine ⟨p ⁻¹' U ∩ p' ⁻¹' W, fun y ⟨hyU, hyW⟩ ↦ ⟨p' y, hyW, (hp' hyU).symm⟩,
    (hplot.continuousOn ho).isOpen_inter_preimage ho hW, hzU, ?_⟩
  rwa [mem_preimage, show p' z = x from Subtype.ext ((hp' hzU).symm.trans hx.symm)]

/-- If the topology of a space is its D-topology, then the D-topology of an open subspace is the
subspace topology. -/
theorem isDTopologyCompatible_subtype [TopologicalSpace X]
    [_root_.Diffeology.IsDTopologyCompatible X] {U : Set X} (hU : IsOpen U) :
    _root_.Diffeology.IsDTopologyCompatible U where
  dTop_eq := by
    rw [dTopology_subtype_of_isOpen (by rwa [_root_.Diffeology.IsDTopologyCompatible.dTop_eq X]),
      _root_.Diffeology.IsDTopologyCompatible.dTop_eq X]
    rfl

/-- If the topology of a space is its D-topology, then so is the topology of each open subset. -/
instance instIsDTopologyCompatibleOpens [TopologicalSpace X]
    [_root_.Diffeology.IsDTopologyCompatible X] (U : TopologicalSpace.Opens X) :
    _root_.Diffeology.IsDTopologyCompatible U :=
  isDTopologyCompatible_subtype U.isOpen

/-! ### Restricting subductions -/

/-- The restriction of a subduction over a subset of its target is a subduction for the subspace
diffeologies. -/
theorem IsSubduction.restrictPreimage [DiffeologicalSpace Q] {q : X → Q} (hq : IsSubduction q)
    (t : Set Q) : IsSubduction (t.restrictPreimage q) where
  surjective := restrictPreimage_surjective t hq.surjective
  dSmooth n p hp := hq.dSmooth n (Subtype.val ∘ p) hp
  locallyLifts {n p} hp := locallyLifts_iff.mpr fun z _ ↦ by
    classical
    obtain ⟨v, hv, hzv, -, lift, hlift, hq'⟩ :=
      locallyLifts_iff.mp (hq.locallyLifts (isPlot_subtype_iff.mp hp)) z (mem_univ z)
    -- On `v`, the lift lands in the preimage of `t`, since its image under `q` is `p`.
    have hmem : ∀ y ∈ v, lift y ∈ q ⁻¹' t := fun y hy ↦ by
      rw [mem_preimage, ← comp_apply (f := q), hq' hy]
      exact (p y).2
    let lift' : 𝔼ⁿ → q ⁻¹' t := fun y ↦ if h : lift y ∈ q ⁻¹' t then ⟨lift y, h⟩
      else ⟨lift z, hmem z hzv⟩
    have hlift' : ∀ y (hy : y ∈ v), lift' y = ⟨lift y, hmem y hy⟩ := fun y hy ↦ by
      simp [lift', show q (lift y) ∈ t from hmem y hy]
    refine ⟨v, hv, hzv, subset_univ v, lift', isPlotOn_subtype_iff.mpr
      (hlift.congr fun y hy ↦ by simp [hlift' y hy]), fun y hy ↦ Subtype.ext ?_⟩
    simpa [hlift' y hy] using hq' hy

end TauCeti.Diffeology
