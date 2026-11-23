/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Diffeology.Basic

/-!
# Basic D-topology and subsingleton lemmas for diffeological spaces

This file provides foundational lemmas depending only on `Mathlib.Geometry.Diffeology.Basic`:

* Plotwise characterization of continuity out of the D-topology (`continuous_dTopology_dom_iff`)
  and out of spaces carrying a compatible topology (`continuous_dom_iff_of_isDTopologyCompatible`).
* Smoothness, plot membership, and compatibility instances for subsingleton spaces
  (`isPlot_of_subsingleton`, `dSmooth_of_subsingleton`,
  `instIsDTopologyCompatibleOfSubsingleton`, `instIsContDiffCompatibleOfSubsingleton`), together
  with the canonical point diffeology on `PUnit` (`instDiffeologicalSpacePUnit`).

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), §1.12 and Chapter 2.
* J. D. Christensen, G. Sinnamon, and E. Wu, *The D-topology for diffeological spaces*, Pacific J.
  Math. **272** (2014), 87–110, §3.
-/

public noncomputable section

open Function Set
open scoped ContDiff Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/-! ### Continuity out of the D-topology -/

/-- A map out of a diffeological space is continuous for the D-topology if and only if its
composite with every plot is continuous. -/
theorem continuous_dTopology_dom_iff {X T : Type*} [DiffeologicalSpace X] [TopologicalSpace T]
    {f : X → T} :
    @Continuous X T _root_.Diffeology.dTopology ‹TopologicalSpace T› f ↔
      ∀ (n : ℕ) (p : 𝔼ⁿ → X), _root_.Diffeology.IsPlot p → Continuous (f ∘ p) := by
  let : TopologicalSpace X := _root_.Diffeology.dTopology
  exact ⟨fun h _ _ hp ↦ h.comp hp.continuous,
    fun h ↦ continuous_def.mpr fun s hs ↦
      _root_.Diffeology.isOpen_iff_preimages_plots.mpr fun n p hp ↦ (h n p hp).isOpen_preimage s hs⟩

/-- On a space whose topology agrees with its D-topology, a map is continuous if and only if its
composite with every plot is continuous. -/
theorem continuous_dom_iff_of_isDTopologyCompatible {X T : Type*} [TopologicalSpace X]
    [DiffeologicalSpace X] [_root_.Diffeology.IsDTopologyCompatible X] [TopologicalSpace T]
    {f : X → T} :
    Continuous f ↔ ∀ (n : ℕ) (p : 𝔼ⁿ → X), _root_.Diffeology.IsPlot p → Continuous (f ∘ p) := by
  rw [← _root_.Diffeology.IsDTopologyCompatible.dTop_eq X]
  exact continuous_dTopology_dom_iff

/-! ### Subsingleton spaces and `PUnit` -/

/-- Every parametrization into a subsingleton diffeological space is a plot. -/
@[nontriviality, fun_prop]
theorem isPlot_of_subsingleton {Y : Type*} [DiffeologicalSpace Y] [Subsingleton Y] {n : ℕ}
    {p : 𝔼ⁿ → Y} : _root_.Diffeology.IsPlot p :=
  Subsingleton.elim p (fun _ ↦ p 0) ▸ _root_.Diffeology.isPlot_const

/-- Every map from a diffeological space into a subsingleton diffeological space is smooth. -/
@[nontriviality, fun_prop]
theorem dSmooth_of_subsingleton {X Y : Type*} [DiffeologicalSpace X] [DiffeologicalSpace Y]
    [Subsingleton Y] {f : X → Y} : _root_.Diffeology.DSmooth f :=
  fun _ _ _ ↦ isPlot_of_subsingleton

/-- On a subsingleton space, any topology agrees with the D-topology of any diffeology. -/
instance (priority := 100) instIsDTopologyCompatibleOfSubsingleton {X : Type*}
    [TopologicalSpace X] [DiffeologicalSpace X] [Subsingleton X] :
    _root_.Diffeology.IsDTopologyCompatible X :=
  ⟨Subsingleton.elim _ _⟩

/-- On a subsingleton normed space, any diffeology agrees with the smooth normed-space
diffeology. -/
instance (priority := 100) instIsContDiffCompatibleOfSubsingleton {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DiffeologicalSpace E] [Subsingleton E] :
    _root_.Diffeology.IsContDiffCompatible E where
  isPlot_iff := ⟨fun _ ↦ contDiff_of_subsingleton, fun _ ↦ isPlot_of_subsingleton⟩

/-- The canonical diffeology on `PUnit`, in which every parametrization is a plot and the
D-topology is definitionally the standard topology. -/
instance instDiffeologicalSpacePUnit : DiffeologicalSpace PUnit where
  plots _ := univ
  constant_plots _ := trivial
  plot_reparam _ _ := trivial
  locality _ := trivial
  dTopology := inferInstance
  isOpen_iff_preimages_plots {u} := by
    rcases u.eq_empty_or_nonempty with rfl | ⟨⟨⟩, hu⟩
    · exact ⟨fun _ _ _ _ ↦ isOpen_empty, fun _ ↦ isOpen_empty⟩
    · obtain rfl : u = univ := eq_univ_of_forall fun ⟨⟩ ↦ hu
      exact ⟨fun _ _ _ _ ↦ isOpen_univ, fun _ ↦ isOpen_univ⟩

end TauCeti.Diffeology
