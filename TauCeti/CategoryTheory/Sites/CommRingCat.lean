/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Sheaves of commutative rings are sheaves of rings

On any site, composing a sheaf of commutative rings with `forget₂ CommRingCat RingCat` gives a sheaf
of rings (`CategoryTheory.GrothendieckTopology.hasSheafCompose_forget₂_commRingCat`). This includes
large sites such as the big sites of schemes, on which `forget₂ CommRingCat RingCat` is not known
to preserve the limits that the sheaf condition involves.
-/

public section

open CategoryTheory Limits

universe u

/-- Sheaves of commutative rings are sheaves of rings, on any site. This includes large sites such
as the big sites of schemes, on which `forget₂ CommRingCat RingCat` is not known to preserve the
limits that the sheaf condition involves. -/
instance CategoryTheory.GrothendieckTopology.hasSheafCompose_forget₂_commRingCat {C : Type*}
    [Category* C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) where
  isSheaf P hP := by
    rw [Presheaf.isSheaf_iff_isLimit] at hP ⊢
    refine fun X S hS ↦ (hP S hS).map fun hc ↦ ?_
    -- The limit in `CommRingCat` is preserved by the forgetful functor to types, so its
    -- underlying sections form a small type. Then `RingCat` has the corresponding limit, and
    -- `forget₂ CommRingCat RingCat`, which creates it, preserves it.
    have hc' := isLimitOfPreserves (forget₂ CommRingCat CommMonCat ⋙ forget CommMonCat) hc
    have : Small.{u} ((S.arrows.diagram.op ⋙ P) ⋙ forget CommRingCat).sections :=
      ⟨_, ⟨(Types.isLimitEquivSections hc').symm⟩⟩
    have : Small.{u} (((S.arrows.diagram.op ⋙ P) ⋙ forget₂ CommRingCat RingCat) ⋙
      forget RingCat).sections := this
    exact isLimitOfPreserves (forget₂ CommRingCat RingCat) hc
