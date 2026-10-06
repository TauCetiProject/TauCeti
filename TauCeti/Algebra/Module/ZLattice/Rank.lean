/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# A rank criterion for discrete integer submodules

A finitely generated integer submodule of a real normed space is discrete
if and only if its integer rank equals the dimension of its real span. The converse to
Mathlib's `Real.finrank_eq_int_finrank_of_discrete` turns an integer basis into a real basis
of the span, then uses discreteness of the integer span of a real basis.

This criterion allows logarithmic images of finitely generated unit groups to be proved
discrete from their rank and real span, without a separate compactness argument.
-/

public section

open Submodule Module

namespace TauCeti.Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem discreteTopology_of_span_eq_top (L : Submodule ℤ E) [Module.Finite ℤ L]
    (hs : Submodule.span ℝ (L : Set E) = ⊤)
    (hr : Module.finrank ℤ L = Module.finrank ℝ E) : DiscreteTopology L := by
  classical
  have : Module ℚ E := Module.compHom E (algebraMap ℚ ℝ)
  have : IsAddTorsionFree E := .of_module_rat _
  let b := Module.Free.chooseBasis ℤ L
  let v := fun i ↦ (b i : E)
  have hz : Submodule.span ℤ (Set.range v) = L := by
    have hv : Set.range v = L.subtype '' Set.range b := Set.range_comp _ _
    rw [hv, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℤ, hz, hs]
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℝ E := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hr]
  let B := basisOfTopLeSpanOfCardEqFinrank v hspan.ge hc
  have he : Submodule.span ℤ (Set.range B) = L := by
    simpa only [coe_basisOfTopLeSpanOfCardEqFinrank, B] using hz
  rw [← he]
  infer_instance

/-- A finitely generated integer submodule is discrete exactly when its integer rank is
the dimension of its real span. The ambient space need not be finite-dimensional. -/
theorem discreteTopology_iff_finrank_eq (L : Submodule ℤ E) [Module.Finite ℤ L] :
    DiscreteTopology L ↔
      Module.finrank ℤ L = Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by
  -- Work inside the real span; the original submodule need not have full ambient rank.
  let F := Submodule.span ℝ (L : Set E)
  have hLF : L ≤ F.restrictScalars ℤ := Submodule.subset_span
  let L' : Submodule ℤ F := L.comap (F.restrictScalars ℤ).subtype
  let e := Submodule.comapSubtypeEquivOfLe hLF
  have : Module.Finite ℤ L' := Module.Finite.equiv e.symm
  have hs : Submodule.span ℝ (L' : Set F) = ⊤ := Submodule.span_span_coe_preimage
  have : FiniteDimensional ℝ F := by
    have hfg : L.FG := Module.Finite.iff_fg.mp inferInstance
    obtain ⟨s, hs, hL⟩ := Submodule.fg_def.mp hfg
    have he : Submodule.span ℝ s = F := by
      rw [← Submodule.span_span_of_tower ℤ, hL]
    rw [← he]
    exact FiniteDimensional.span_of_finite ℝ hs
  constructor
  · intro h
    have : DiscreteTopology L' := DiscreteTopology.of_continuous_injective
      (Isometry.continuous (fun _ _ ↦ rfl) : Continuous (e : L' → L)) e.injective
    have : IsZLattice ℝ L' := ⟨hs⟩
    exact e.symm.finrank_eq.trans (ZLattice.rank ℝ L')
  · intro hr
    have : DiscreteTopology L' := discreteTopology_of_span_eq_top L' hs
      (e.finrank_eq.trans hr)
    let f : L → L' := e.symm
    exact DiscreteTopology.of_continuous_injective
      (Isometry.continuous (fun _ _ ↦ rfl) : Continuous f) e.symm.injective

end TauCeti.Submodule
