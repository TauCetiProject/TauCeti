/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Topology.Covering.IsFiniteCover
public import TauCeti.Topology.Covering.Pullback

/-!
# Pullbacks of finite covers

The pullback of a finite covering map along a continuous map remains a finite cover. This
supplies the finite cover of a hypersurface obtained by pulling back an ambient finite cover.
-/

public section

open Function

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : X → Y} {p : Z → Y}

/-- A finite cover stays finite after pullback along a continuous map. -/
theorem IsFiniteCover.pullback_fst (hp : IsFiniteCover p) (hf : Continuous f) :
    IsFiniteCover (Pullback.fst : f.Pullback p → X) where
  isCoveringMap := hp.isCoveringMap.pullback_fst hf
  surjective := by
    intro x
    obtain ⟨z, hz⟩ := hp.surjective (f x)
    exact ⟨⟨(x, z), hz.symm⟩, rfl⟩
  finite_fiber := by
    intro x
    let k : (Pullback.fst ⁻¹' {x} : Set (f.Pullback p)) → (p ⁻¹' {f x} : Set Z) :=
      fun w ↦ ⟨w.val.snd, by
        change p w.val.snd = f x
        have hpw : p w.val.snd = f w.val.fst := w.val.property.symm
        have hxw : w.val.fst = x := w.property
        exact hpw.trans (congrArg f hxw)
      ⟩
    have hk : Function.Injective k := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact a.property.trans b.property.symm
      · exact congrArg Subtype.val hab
    let : Finite (p ⁻¹' {f x}) := hp.finite_fiber (f x)
    exact Finite.of_injective k hk

end TauCeti
