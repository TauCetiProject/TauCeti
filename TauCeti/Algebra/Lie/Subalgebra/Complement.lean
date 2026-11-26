/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Subalgebra

/-!
# Complementary subalgebras inside a sum

Disjoint Lie subalgebras whose underlying submodules sum to a Lie subalgebra become
complementary inside it. This transports the Borel decompositions used by both the finite-type
and Kac–Moody triangular PBW constructions.
-/

public section

namespace LieSubalgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {A B C : LieSubalgebra R L}

/-- Disjoint subalgebras summing to `C` are complementary when viewed inside `C`. -/
theorem isCompl_ofLe (hA : A ≤ C) (hB : B ≤ C)
    (hd : Disjoint A.toSubmodule B.toSubmodule)
    (hs : A.toSubmodule ⊔ B.toSubmodule = C.toSubmodule) :
    IsCompl (A.ofLe hA).toSubmodule (B.ofLe hB).toSubmodule := by
  rw [C.toSubmodule.mapIic.isCompl_iff, Set.Iic.isCompl_iff]
  simp only [Submodule.coe_mapIic_apply, LieSubalgebra.coe_ofLe,
    Submodule.map_subtype_range_inclusion]
  exact ⟨hd, hs⟩

end LieSubalgebra
