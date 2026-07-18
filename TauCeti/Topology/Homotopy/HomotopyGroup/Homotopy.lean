/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Pointed homotopy invariance of homotopy groups

A homotopy between based maps must remain fixed at the basepoint in order to induce a
homotopy between their postcompositions with a generalized loop. This file makes that
construction explicit and proves that pointed-homotopic maps induce the same map on every
homotopy group. In positive dimensions it also gives the corresponding equality of bundled
monoid homomorphisms.

This supplies the pointed-homotopy part of the higher-homotopy API requested in Stage 3,
item 9 of the Tau Ceti universal-covers roadmap.
-/

public section

namespace TauCeti

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace GenLoop

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Postcomposing a generalized loop with pointed-homotopic maps gives homotopic generalized
loops. The homotopy is relative to the cube boundary because the original homotopy is fixed at
the basepoint. -/
theorem map_homotopic_of_homotopicRel {f g : C(X, Y)} (hf : f x = y) (hg : g x = y)
    (H : f.HomotopicRel g {x}) (p : Ω^ N X x) :
    _root_.GenLoop.Homotopic (map f hf p) (map g hg p) := by
  obtain ⟨H⟩ := H
  refine ⟨⟨⟨⟨fun tp ↦ H (tp.1, p.1 tp.2), ?_⟩, ?_, ?_⟩, ?_⟩⟩
  · fun_prop
  · intro t
    simpa only [map, ContinuousMap.comp_apply, _root_.GenLoop.mk_apply] using H.apply_zero (p.1 t)
  · intro t
    simpa only [map, ContinuousMap.comp_apply, _root_.GenLoop.mk_apply] using H.apply_one (p.1 t)
  · intro t u hu
    change H (t, p u) = f (p u)
    exact H.eq_fst t (Set.mem_singleton_iff.mpr (p.2 u hu))

end GenLoop

namespace HomotopyGroup

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Pointed-homotopic continuous maps induce the same function on homotopy groups. -/
theorem map_eq_of_homotopicRel {f g : C(X, Y)} (hf : f x = y) (hg : g x = y)
    (H : f.HomotopicRel g {x}) : map (N := N) f hf = map g hg := by
  funext a
  refine Quotient.inductionOn a ?_
  intro p
  exact Quotient.sound (GenLoop.map_homotopic_of_homotopicRel hf hg H p)

/-- Pointed-homotopic continuous maps have equal induced monoid homomorphisms on
positive-dimensional homotopy groups. -/
theorem mapHom_eq_of_homotopicRel [DecidableEq N] [Nonempty N] {f g : C(X, Y)}
    (hf : f x = y) (hg : g x = y) (H : f.HomotopicRel g {x}) :
    mapHom (N := N) f hf = mapHom g hg :=
  MonoidHom.ext fun a ↦ congrFun (map_eq_of_homotopicRel hf hg H) a

end HomotopyGroup

end TauCeti
