/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Diffeology.Basic

/-!
# Basic lemmas and instances on diffeological spaces

This file provides foundational lemmas and instances complementing
`Mathlib.Geometry.Diffeology.Basic`: continuity out of the D-topology tested against plots,
automatic smoothness and compatibility on subsingletons, and the canonical diffeology on `PUnit`.

## Main declarations

* `TauCeti.Diffeology.continuous_dTopology_iff`: continuity out of `dTopology` tested on plots.
* `TauCeti.Diffeology.isPlot_of_subsingleton`, `TauCeti.Diffeology.dSmooth_of_subsingleton`:
  automatic plot and smoothness into subsingleton spaces.
* `TauCeti.Diffeology.instIsDTopologyCompatibleOfSubsingleton`,
  `TauCeti.Diffeology.instIsContDiffCompatibleOfSubsingleton`: D-topology and `ContDiff`
  compatibility on subsingleton spaces.
* `TauCeti.Diffeology.instDiffeologicalSpacePUnit`: the canonical diffeology on `PUnit`.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapters 1 and 2.
-/

public noncomputable section

open Function Set _root_.Diffeology
open scoped ContDiff Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/-- A map out of a diffeological space equipped with its D-topology is continuous if and only if
its composite with every plot is continuous. -/
theorem continuous_dTopology_iff {X W : Type*} [DiffeologicalSpace X] [tW : TopologicalSpace W]
    {f : X → W} :
    Continuous[dTopology, tW] f ↔ ∀ (n : ℕ) (p : 𝔼ⁿ → X), IsPlot p → Continuous (f ∘ p) := by
  let : TopologicalSpace X := dTopology
  simp_rw [continuous_def, isOpen_iff_preimages_plots, preimage_comp]
  exact ⟨fun h n p hp s hs ↦ h s hs n p hp, fun h s hs n p hp ↦ h n p hp s hs⟩

/-! ### Subsingletons and `PUnit` -/

/-- Every map from a Cartesian space into a subsingleton diffeological space is a plot. -/
theorem isPlot_of_subsingleton {X : Type*} [DiffeologicalSpace X] [Subsingleton X] {n : ℕ}
    (p : 𝔼ⁿ → X) : IsPlot p := by
  convert isPlot_const (x := p 0)

/-- Every map into a subsingleton diffeological space is smooth. -/
theorem dSmooth_of_subsingleton {X Y : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y]
    [Subsingleton Y] (f : X → Y) : DSmooth f :=
  fun _ p _ ↦ isPlot_of_subsingleton (f ∘ p)

/-- On a subsingleton type, every topology agrees with the D-topology of any diffeology. -/
instance (priority := 100) instIsDTopologyCompatibleOfSubsingleton {X : Type*}
    [TopologicalSpace X] [DiffeologicalSpace X] [Subsingleton X] : IsDTopologyCompatible X :=
  ⟨Subsingleton.elim _ _⟩

/-- On a subsingleton real normed space, every diffeology agrees with the `ContDiff` diffeology. -/
instance (priority := 100) instIsContDiffCompatibleOfSubsingleton {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [DiffeologicalSpace X] [Subsingleton X] :
    IsContDiffCompatible X :=
  ⟨⟨fun _ ↦ contDiff_of_subsingleton, fun _ ↦ isPlot_of_subsingleton _⟩⟩

/-- The unique diffeology on `PUnit`, whose D-topology is definitionally the standard topology.
Unlike the `Prop`-valued compatibility classes above, `DiffeologicalSpace` carries data and is
registered specifically on `PUnit` to avoid data diamonds with subspace and product diffeologies
on other subsingleton types. -/
instance instDiffeologicalSpacePUnit : DiffeologicalSpace PUnit where
  plots _ := univ
  constant_plots _ := mem_univ _
  plot_reparam _ _ := mem_univ _
  locality _ := mem_univ _
  dTopology := inferInstance
  isOpen_iff_preimages_plots {u} :=
    ⟨fun _ _ p _ ↦ by
      rcases u.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · exact isOpen_empty
      · convert isOpen_univ
        exact eq_univ_of_forall fun z ↦ mem_preimage.mpr (Subsingleton.elim x (p z) ▸ hx),
      fun _ ↦ trivial⟩

end TauCeti.Diffeology
