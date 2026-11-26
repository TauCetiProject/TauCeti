/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import TauCeti.Topology.ContinuousOn.Extension

/-!
# Extending uniformly continuous maps to closures

`UniformContinuousOn.exists_continuousOn_closure_eqOn` extends a uniformly continuous map
on a subset to a map continuous on its closure, with values in a complete Hausdorff uniform
space. The proof uses Mathlib's `uniformContinuous_uniformly_extend` on the dense inclusion
into the closure and `Continuous.continuousOn_extend_subtypeVal` for the ambient extension.
-/

public section

open Set

/-- A uniformly continuous map into a complete Hausdorff uniform space has a continuous
extension to the closure of its domain. -/
theorem UniformContinuousOn.exists_continuousOn_closure_eqOn {X Y : Type*}
    [UniformSpace X] [UniformSpace Y]
    [CompleteSpace Y] [T0Space Y] {U : Set X} {f : X → Y}
    (hf : UniformContinuousOn f U) :
    ∃ g : X → Y, ContinuousOn g (closure U) ∧ EqOn g f U := by
  let i : U → closure U := Set.inclusion subset_closure
  have hi : IsUniformInducing i :=
    (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing
  have hd : DenseRange i := (denseRange_inclusion_iff subset_closure).2 subset_rfl
  let g := (hi.isDenseInducing hd).extend (fun x : U ↦ f x)
  have hg : Continuous g :=
    (uniformContinuous_uniformly_extend hi hd (uniformContinuousOn_iff_restrict.1 hf)).continuous
  let G : X → Y := Function.extend (fun x : closure U ↦ (x : X)) g f
  have hG (x : closure U) : G x = g x := Subtype.val_injective.extend_apply g f x
  refine ⟨G, hg.continuousOn_extend_subtypeVal f, ?_⟩
  intro x hx
  rw [hG ⟨x, subset_closure hx⟩]
  exact (hi.isDenseInducing hd).extend_eq hf.restrict.continuous ⟨x, hx⟩
