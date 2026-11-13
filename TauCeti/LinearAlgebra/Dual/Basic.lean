/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Common kernels and dual coannihilators

The dual coannihilator of the span of a family of functionals is their common
kernel. This relates equations defining a submodule to the span of its conormals,
without finiteness assumptions on either the family or the ambient module.

## Attribution

Adapted from `Mei/LinearAlgebra/Dual/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author: Codex; original copyright: Mei contributors.

-/

public section

namespace Submodule

/-- The dual coannihilator of a set's span is the intersection of its kernels. -/
theorem dualCoannihilator_span {R M : Type*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set (Module.Dual R M)) :
    (span R s).dualCoannihilator = ⨅ f ∈ s, f.ker := by
  ext v
  rw [← SetLike.mem_coe, coe_dualCoannihilator_span]
  simp only [Set.mem_ofPred_eq, mem_iInf, LinearMap.mem_ker]

/-- The dual coannihilator of a family's span is the intersection of its kernels. -/
@[simp]
theorem dualCoannihilator_span_range {R M : Type*} {ι : Sort*}
    [CommSemiring R] [AddCommMonoid M] [Module R M] (f : ι → Module.Dual R M) :
    (span R (Set.range f)).dualCoannihilator = ⨅ j, (f j).ker := by
  rw [dualCoannihilator_span, iInf_range]

end Submodule
