/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Group.Equiv.Opposite
import TauCeti.Algebra.Group.Subgroup.RangeOpposite

/-!
# Regression examples: anti-automorphisms of the range of a homomorphism

These examples exercise `TauCeti.Algebra.Group.Subgroup.RangeOpposite`: inversion, which
stabilizes every kernel, induces inversion on the range of a homomorphism, and the inverse of
the induced anti-automorphism reduces to the map itself.
-/

-- Inversion, which stabilizes every kernel, induces inversion on the range.
example {G C : Type*} [Group G] [Group C] (κ : G →* C) (g : G) :
    κ.rangeOpMulEquiv (MulEquiv.inv' G) (fun _ ↦ by simp) (fun _ ↦ by simp)
      (κ.rangeRestrict g) = MulOpposite.op (κ.rangeRestrict g)⁻¹ := by
  simp

-- The inverse of the induced anti-automorphism is computed by the forward map.
example {G C : Type*} [Group G] [Group C] (κ : G →* C) (g : G) :
    (κ.rangeOpMulEquiv (MulEquiv.inv' G) (fun _ ↦ by simp) (fun _ ↦ by simp)).symm
      (MulOpposite.op (κ.rangeRestrict g)) = (κ.rangeRestrict g)⁻¹ := by
  simp
