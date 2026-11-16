/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Maps to a finite product that are differentiable on a domain and continuous on its closure

A map `Φ : E → Π i, F' i` is differentiable on `s` and continuous on `closure s` exactly when each
coordinate is (`TauCeti.diffContOnCl_pi`). The assembly lemma
`TauCeti.forall_exists_diffContOnCl_iff` uses this to combine coordinatewise solutions of a
boundary problem, given as restrictions of such maps to a set `t` and subject to a pointwise
condition on a set `b`, into one solution with values in `ι → F`.
-/

public section

namespace TauCeti

open Set

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A map to a finite product is differentiable on `s` and continuous on `closure s` exactly when
each coordinate is. -/
theorem diffContOnCl_pi [Fintype ι] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
    [∀ i, NormedSpace 𝕜 (F' i)] {Φ : E → Π i, F' i} {s : Set E} :
    DiffContOnCl 𝕜 Φ s ↔ ∀ i, DiffContOnCl 𝕜 (fun x => Φ x i) s :=
  ⟨fun h i => ⟨differentiableOn_pi.mp h.differentiableOn i, continuousOn_pi.mp h.continuousOn i⟩,
    fun h => ⟨differentiableOn_pi.mpr fun i => (h i).differentiableOn,
      continuousOn_pi.mpr fun i => (h i).continuousOn⟩⟩

/-- Coordinatewise solutions assemble into one map to `ι → F`: a map `g` on `t` has each
coordinate the restriction of a function differentiable on `s`, continuous on its closure and
satisfying the condition `P i w` at the points `w ∈ b`, exactly when `g` itself is the restriction
of such a map `E → ι → F`. -/
theorem forall_exists_diffContOnCl_iff [Fintype ι] {s t b : Set E} (P : ι → E → F → Prop)
    (g : t → ι → F) :
    (∀ i, ∃ u : E → F, DiffContOnCl 𝕜 u s ∧ (∀ w ∈ b, P i w (u w)) ∧
        t.domRestrict u = fun z => g z i) ↔
      ∃ u : E → ι → F, DiffContOnCl 𝕜 u s ∧ (∀ w ∈ b, ∀ i, P i w (u w i)) ∧
        t.domRestrict u = g := by
  constructor
  · intro h
    choose u hu hb hg using h
    refine ⟨fun z i => u i z, diffContOnCl_pi.mpr hu, fun w hw i => hb i w hw, ?_⟩
    funext z i
    exact congrFun (hg i) z
  · rintro ⟨u, hu, hb, rfl⟩ i
    exact ⟨fun z => u z i, diffContOnCl_pi.mp hu i, fun w hw => hb w hw i, rfl⟩

end TauCeti
