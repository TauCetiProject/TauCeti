/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.HalfPlane
import TauCeti.Geometry.Manifold.Gluing.Star

/-!
# A three-piece complex star

Attach two extra copies of `ℂ` to a central copy along the left and right half-planes by the
identity. The attaching sets are disjoint but their boundaries meet along the imaginary axis.
The general compatible-gluing theorem supplies the complex atlas and makes all three inclusions
local biholomorphisms. The quotient identifies a leaf point with its copy in the hub exactly
on its attaching half-plane, and never identifies points from distinct leaves.
-/

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti

example :
    let W : Option Bool → Opens ℂ
      | none => ⊤
      | some false => ⟨{z | z.re < 0}, Complex.isOpen_re_lt 0⟩
      | some true => ⟨{z | 0 < z.re}, Complex.isOpen_re_gt 0⟩
    let D := starGlueData (U := fun _ : Option Bool ↦ ℂ) (W := W) fun _ ↦ Homeomorph.refl _
    letI := D.chartedSpace ℂ
    IsManifold 𝓘(ℂ) ω D.toGlueData.glued ∧
      (∀ i : D.J, IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (D.toGlueData.ι i)) ∧
      (∀ b : Bool, (W (some b) : Set ℂ).Nonempty) ∧
      (∀ (b : Bool) (x y : ℂ), D.toGlueData.ι none x = D.toGlueData.ι (some b) y ↔
        y ∈ W (some b) ∧ x = y) ∧
      Disjoint (range (D.toGlueData.ι (some false))) (range (D.toGlueData.ι (some true))) := by
  intro W D
  have h := isCompatible_starGlueData (W := W) (ψ := fun _ ↦ Homeomorph.refl _)
    (fun _ ↦ (Diffeomorph.refl 𝓘(ℂ) _ ω).isLocalDiffeomorph)
  refine ⟨h.isManifold, h.isLocalDiffeomorph_ι, ?_, ?_, ?_⟩
  · intro b
    cases b
    · exact ⟨-1, by change (-1 : ℂ).re < 0; norm_num⟩
    · exact ⟨1, by change 0 < (1 : ℂ).re; norm_num⟩
  · intro b x y
    rw [starGlueData_ι_eq_iff_of_ne (by simp)]
    exact ⟨fun ⟨_, hy, hxy⟩ ↦ ⟨hy, hxy⟩, fun ⟨hy, hxy⟩ ↦ ⟨by trivial, hy, hxy⟩⟩
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨x, rfl⟩ ⟨y, hyx⟩
    obtain ⟨hx, hy, hxy⟩ := (starGlueData_ι_eq_iff_of_ne (by decide)).1 hyx.symm
    change x = y at hxy
    subst y
    exact lt_asymm (show x.re < 0 from hx) (show 0 < x.re from hy)

end TauCeti
