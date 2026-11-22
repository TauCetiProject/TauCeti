/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# The local predicate of `C^n` regularity

The existing `ContMDiff` condition, including smooth and analytic regularity, is a local
predicate for functions whose source and target may lie in independent universes. This is the
`ContMDiff` specialization of `StructureGroupoid.LocalInvariantProp.localPredicate` with those
universes independent. Its public predicate law identifies the original regularity condition.
-/

public section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

universe u v

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners 𝕜 E' H')
  (n : ℕ∞ω) (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
  (Y : Type v) [TopologicalSpace Y] [ChartedSpace H' Y]

/-- The local predicate of `C^n` regularity, with independent source and target universes. -/
-- As for Mathlib's LocalInvariantProp.localPredicate, expose this data constructor so that
-- its subsheaf has the literal existing differentiable-map carrier.
@[expose]
def contMDiffLocalPredicate : TopCat.LocalPredicate (fun _ : TopCat.of X ↦ Y) where
  pred f := ContMDiff I J n f
  res i _ h := h.comp (contMDiff_inclusion (leOfHom i))
  locality {U} f h x := by
    obtain ⟨W, hx, i, hW⟩ := h x
    exact ((contDiffWithinAt_localInvariantProp n).liftPropAt_iff_comp_inclusion
      (leOfHom i) f ⟨x, hx⟩).2 (hW ⟨x, hx⟩)

variable {I J n X Y} in
/-- The predicate has the original `C^n` regularity condition. -/
@[simp]
theorem contMDiffLocalPredicate_pred {U : Opens (TopCat.of X)} (f : U → Y) :
    (contMDiffLocalPredicate I J n X Y).pred f ↔ ContMDiff I J n f :=
  Iff.rfl

end TauCeti
