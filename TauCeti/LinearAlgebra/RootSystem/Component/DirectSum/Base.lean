/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Base
public import TauCeti.LinearAlgebra.RootSystem.Component.DirectSum.Basic
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Base

/-!
# Bases under the irreducible component direct-sum decomposition

Assembling the restricted bases `RootPairing.Base.componentBase` across all irreducible components
of a finite root system `P` recovers the base of `P` transported along
`RootPairing.equivInternalDirectSumComponentPairing`.

## Main results

* `RootPairing.Base.internalDirectSum_componentBase`: assembling `Base.componentBase` across all
  components recovers the base transported along `equivInternalDirectSumComponentPairing`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
-/

public section

namespace RootPairing

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] (P : RootPairing ι K M N)

/-- **Assembling the component bases `Base.componentBase` recovers the original base** under
`RootPairing.equivInternalDirectSumComponentPairing`. -/
@[simp]
theorem Base.internalDirectSum_componentBase [NeZero (2 : K)] [Finite ι] [P.IsRootSystem]
    (b : P.Base) :
    Base.internalDirectSum P.iSupIndep_componentSpace
        (P.iSup_componentSpace.trans IsRootSystem.span_root_eq_top)
        (fun C ↦ b.componentBase C) =
      b.map P.equivInternalDirectSumComponentPairing := by
  classical
  ext p
  obtain ⟨i, rfl⟩ := P.equivInternalDirectSumComponentPairing.indexEquiv.surjective p
  rw [Base.mem_support_map_iff, _root_.Equiv.symm_apply_apply]
  simp

end RootPairing
