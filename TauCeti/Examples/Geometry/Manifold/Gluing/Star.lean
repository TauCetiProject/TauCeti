/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Basic
import TauCeti.Geometry.Manifold.Gluing.Star

/-!
# A three-piece complex star

Attach two extra copies of `ℂ` to a central copy, one along the left half-plane and one along
the right half-plane, by identity transitions. Both attachments are nonempty, while the two
leaf images are disjoint. The general compatible-gluing theorem supplies the complex atlas
and makes all three inclusions local biholomorphisms, despite the empty leaf-to-leaf overlaps.
-/

open Set TopologicalSpace Function TauCeti
open scoped Manifold ContDiff

-- A nondegenerate finite star, on the standard glued carrier and with the standard glued atlas.
example : ∃ (e : Bool → OpenPartialHomeomorph ℂ ℂ)
    (he : Pairwise (Disjoint on fun b ↦ (e b).source)),
    (∀ b, (e b).source.Nonempty) ∧
    (letI := (starGlueData e he).chartedSpace ℂ
     IsManifold 𝓘(ℂ) ω (starGlueData e he).toGlueData.glued ∧
     ∀ i : (starGlueData e he).J,
       IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω ((starGlueData e he).toGlueData.ι i)) ∧
    ∀ x y : ℂ, (starGlueData e he).toGlueData.ι (some false) x ≠
      (starGlueData e he).toGlueData.ι (some true) y := by
  let U : Bool → Opens ℂ := fun b ↦
    if b then ⟨{z | 0 < z.re}, isOpen_lt continuous_const Complex.continuous_re⟩
    else ⟨{z | z.re < 0}, isOpen_lt Complex.continuous_re continuous_const⟩
  let e : Bool → OpenPartialHomeomorph ℂ ℂ := fun b ↦
    OpenPartialHomeomorph.ofSet (U b) (U b).isOpen
  have he : Pairwise (Disjoint on fun b ↦ (e b).source) := by
    intro i j hij
    cases i <;> cases j <;>
      simp_all only [ne_eq, not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false,
        OpenPartialHomeomorph.ofSet_toPartialEquiv, PartialEquiv.ofSet_source, Set.disjoint_left,
        ↓reduceIte, Opens.coe_mk, Set.mem_ofPred_eq, e, U] <;>
      exact fun _ hz ↦ lt_asymm hz
  have h : (starGlueData e he).IsCompatible 𝓘(ℂ) ω :=
    isCompatible_starGlueData e he (fun _ ↦ contMDiff_id.contMDiffOn)
      (fun _ ↦ contMDiff_id.contMDiffOn)
  refine ⟨e, he, ?_, ⟨h.isManifold, h.isLocalDiffeomorph_ι⟩, ?_⟩
  · intro b
    cases b
    · exact ⟨-1, by norm_num [e, U]⟩
    · exact ⟨1, by norm_num [e, U]⟩
  · intro x y
    simp
