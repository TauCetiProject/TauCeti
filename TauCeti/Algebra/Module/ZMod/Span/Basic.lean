/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Spans in modules over `ℤ/nℤ`

In a `ZMod n`-module, additive generation and linear generation agree. This identifies
the group-theoretic generation criterion for an elementary abelian group with a spanning
criterion in its associated vector space.
-/

public section

namespace TauCeti

/-- The span over `ℤ/nℤ` has the same underlying additive subgroup as the subgroup generated
by the set. This also includes `n = 0`, where `ZMod 0 = ℤ`. -/
theorem span_zmod_eq_addSubgroupClosure {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    (s : Set M) :
    (Submodule.span (ZMod n) s).toAddSubgroup = AddSubgroup.closure s := by
  apply le_antisymm
  · exact (Submodule.span_le (p := (AddSubgroup.closure s).toZModSubmodule n)).mpr
      AddSubgroup.subset_closure
  · exact (AddSubgroup.closure_le _).mpr Submodule.subset_span

end TauCeti
