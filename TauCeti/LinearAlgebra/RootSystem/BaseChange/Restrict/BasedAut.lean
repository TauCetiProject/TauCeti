/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Base.Basic
public import TauCeti.LinearAlgebra.RootSystem.BaseChange.Restrict.Hom
public import TauCeti.LinearAlgebra.RootSystem.Weyl.BasedAut

/-!
# Based automorphisms under scalar restriction

This file proves that an automorphism of a balanced root pairing `P` is based for a base `b` if
and only if its scalar restriction to `P.restrictScalars' K` is based for `b.restrictScalars' K`.

## Main results

* `RootPairing.Base.mem_basedAut_restrictScalars'_iff`: an automorphism is based if and only if
  its scalar restriction is based.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§1, 6.
-/

public section

namespace RootPairing.Base

variable {ι L M N : Type*} [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  {P : RootPairing ι L M N} (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced] [P.IsValuedIn K] (b : P.Base)

/-- An automorphism of `P` is based for `b` if and only if its restriction to
`P.restrictScalars' K` is based for `b.restrictScalars' K`. -/
theorem mem_basedAut_restrictScalars'_iff {g : P.Aut} :
    Equiv.restrictScalars'Hom P K g ∈ (b.restrictScalars' K).basedAut ↔ g ∈ b.basedAut := by
  simp only [Base.mem_basedAut_iff, Base.support_restrictScalars',
    Equiv.restrictScalars'Hom_apply, Equiv.indexEquiv_restrictScalars']

end RootPairing.Base
