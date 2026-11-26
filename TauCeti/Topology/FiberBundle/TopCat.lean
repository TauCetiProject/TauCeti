/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import TauCeti.Topology.Category.TopCat.Fiber

/-!
# Fibres of fibre bundle projections in `TopCat`

For a fibre bundle `E : B → Type u` with model fibre `F`, the projection `TotalSpace.proj` defines a
morphism `TopCat.of (TotalSpace F E) ⟶ TopCat.of B` in `TopCat`. Its categorical fibre
`TopCat.Hom.fiber` over any `b : B` is homeomorphic to the model fibre `F` via the preferred local
trivialization `trivializationAt F E b` (`FiberBundle.projFiberHomeomorph`).

Unlike `Bundle.Trivialization.preimageSingletonHomeomorph` (whose domain is the set preimage
`TotalSpace.proj ⁻¹' {b}`), `FiberBundle.projFiberHomeomorph` has domain
`(TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩).fiber b`, so typeclass synthesis
and dot-notation lemmas stated on `TopCat.Hom.fiber` apply directly.

## Main definitions and results

* `FiberBundle.projFiberHomeomorph`: homeomorphism from the `TopCat.Hom.fiber` over `b` of the
  bundle projection to the model fibre `F`.
* `FiberBundle.projFiberHomeomorph_apply` and `FiberBundle.coe_projFiberHomeomorph_symm_apply`:
  evaluation of `FiberBundle.projFiberHomeomorph` and its inverse in terms of
  `trivializationAt F E b`.
-/

public section

open Bundle

universe u v

namespace FiberBundle

variable {B : Type u} (F : Type v) [TopologicalSpace B] [TopologicalSpace F]
  (E : B → Type u) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

/-- Each fibre of the `TopCat` projection morphism of a fibre bundle `FiberBundle F E` is
homeomorphic to the model fibre `F` via `trivializationAt F E b`. -/
noncomputable def projFiberHomeomorph (b : B) :
    ((_root_.TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ :
      _root_.TopCat.of (TotalSpace F E) ⟶ _root_.TopCat.of B).fiber b) ≃ₜ F :=
  (trivializationAt F E b).preimageSingletonHomeomorph (mem_baseSet_trivializationAt' b)

/-- Evaluating `FiberBundle.projFiberHomeomorph` reads the model-fibre coordinate in
`trivializationAt F E b`. Not `@[simp]`: `TopCat.hom_ofHom` simplifies the implicit carrier type in
`DFunLike.coe`, so `simpNF` rejects `@[simp]`. -/
theorem projFiberHomeomorph_apply (b : B)
    (x : (_root_.TopCat.ofHom ⟨TotalSpace.proj, FiberBundle.continuous_proj F E⟩ :
      _root_.TopCat.of (TotalSpace F E) ⟶ _root_.TopCat.of B).fiber b) :
    projFiberHomeomorph F E b x = (trivializationAt F E b x.val).2 :=
  (trivializationAt F E b).preimageSingletonHomeomorph_apply (mem_baseSet_trivializationAt' b) x

/-- Evaluating `(FiberBundle.projFiberHomeomorph F E b).symm` in `TotalSpace F E` applies the
inverse of `trivializationAt F E b` at `(b, y)`. Not `@[simp]`: `TopCat.hom_ofHom` simplifies the
implicit subtype predicate in `Subtype.val`, so `simpNF` rejects `@[simp]`. -/
theorem coe_projFiberHomeomorph_symm_apply (b : B) (y : F) :
    ((projFiberHomeomorph F E b).symm y : TotalSpace F E) =
      (trivializationAt F E b).toOpenPartialHomeomorph.symm (b, y) :=
  congrArg Subtype.val <|
    (trivializationAt F E b).preimageSingletonHomeomorph_symm_apply
      (mem_baseSet_trivializationAt' b) y

end FiberBundle
