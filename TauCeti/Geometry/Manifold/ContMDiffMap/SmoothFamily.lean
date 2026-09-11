/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
public import TauCeti.Geometry.Manifold.ContMDiffMap.WeakWhitney

/-!
# Smooth families are continuous for the weak Whitney topology

A jointly `C^n` map `P × E → F` gives a continuous family of `C^n` maps `E → F` for the
weak Whitney topology. This is the chart-level smooth-family construction: differentiating
in `E` restricts the total derivative to directions in the second factor, so each derivative
varies jointly continuously in `(p, x)`. Compact-open currying then gives continuity into
the function space. In particular the construction applies to smooth families (`n = ∞`).

We also characterize continuity of arbitrary families by their compact-open derivative maps.
When `E` is locally compact, this is equivalent to joint continuity of every spatial derivative;
no differentiability in the parameter is required for this characterization.

The topology is the weak topology of M. Hirsch, *Differential Topology*, Graduate Texts in
Mathematics 33, Chapter 2, §1. Only the forward implication from joint smoothness is asserted:
a continuous family in the weak Whitney topology need not be smooth in its parameter.
-/

public section

open Topology
open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}

/-- Continuity into the weak Whitney topology is equivalent to continuity of each derivative
as a map into its compact-open function space. -/
theorem continuous_weakWhitney_iff {X : Type*} [TopologicalSpace X]
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯} :
    Continuous f ↔ ∀ (m : ℕ) (hm : m ≤ n),
      Continuous (fun p ↦ ContMDiffMap.iteratedFDerivContinuousMap (f p) m hm) := by
  rw [ContMDiffMap.isInducing_weakWhitneyJet.continuous_iff]
  simp only [continuous_pi_iff, Function.comp_apply, ContMDiffMap.weakWhitneyJet_apply,
    Subtype.forall]

/-- A family is continuous in the weak Whitney topology if every spatial derivative through
order `n` varies jointly continuously in the parameter and evaluation point. -/
theorem continuous_weakWhitney_of_continuous_iteratedFDeriv {X : Type*} [TopologicalSpace X]
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯}
    (hf : ∀ (m : ℕ), m ≤ n →
      Continuous (fun z : X × E ↦ iteratedFDeriv 𝕜 m (f z.1) z.2)) :
    Continuous f := by
  rw [continuous_weakWhitney_iff]
  intro m hm
  apply ContinuousMap.continuous_of_continuous_uncurry
  simpa only [Function.uncurry_def, ContMDiffMap.iteratedFDerivContinuousMap_apply]
    using hf m hm

/-- For a locally compact source, continuity of a family in the weak Whitney topology is
exactly joint continuity of all spatial derivatives through order `n`. -/
theorem continuous_weakWhitney_iff_continuous_iteratedFDeriv [LocallyCompactSpace E]
    {X : Type*} [TopologicalSpace X]
    {f : X → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯} :
    Continuous f ↔ ∀ (m : ℕ), m ≤ n →
      Continuous (fun z : X × E ↦ iteratedFDeriv 𝕜 m (f z.1) z.2) := by
  constructor
  · intro hf m hm
    simpa only [Function.uncurry_def, ContinuousMap.coe_mk,
      ContMDiffMap.iteratedFDerivContinuousMap_apply] using
      ContinuousMap.continuous_uncurry_of_continuous
        ⟨_, (continuous_weakWhitney_iff.mp hf) m hm⟩
  · exact continuous_weakWhitney_of_continuous_iteratedFDeriv

/-- A jointly `C^n` family gives a continuous map into the weak Whitney `C^n` map space.
This requires neither finite dimensionality nor local compactness of the normed spaces. -/
theorem continuous_weakWhitney_of_contDiff
    {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    {f : P → C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯}
    (hf : ContDiff 𝕜 n (fun z : P × E ↦ f z.1 z.2)) : Continuous f :=
  continuous_weakWhitney_of_continuous_iteratedFDeriv
    (fun m hm ↦ continuous_iteratedFDeriv_prod_right hf m hm)

/-- Curry a jointly `C^n` map into a continuous family of `C^n` maps, where the inner map
space carries the weak Whitney topology. -/
noncomputable def weakWhitneyCurry
    {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    (f : C^n⟮𝓘(𝕜, P × E), P × E; 𝓘(𝕜, F), F⟯) :
    C(P, C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, F), F⟯) where
  toFun p := ⟨fun x ↦ f (p, x),
    (f.contMDiff.contDiff.comp (contDiff_const.prodMk contDiff_id)).contMDiff⟩
  continuous_toFun := continuous_weakWhitney_of_contDiff f.contMDiff.contDiff

@[simp]
theorem weakWhitneyCurry_apply
    {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    (f : C^n⟮𝓘(𝕜, P × E), P × E; 𝓘(𝕜, F), F⟯) (p : P) (x : E) :
    weakWhitneyCurry f p x = f (p, x) :=
  (rfl)

end TauCeti
