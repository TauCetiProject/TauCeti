/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Squared root lengths of an invariant form on the Weyl orbits of the simple roots

The Weyl-group orbits of the simple roots cover all roots
(`TauCeti.exists_mem_support_weylGroupToPerm_eq`), and an invariant form is Weyl-invariant. So an
invariant form takes on the roots exactly the squared lengths it takes on the simple roots. This is
the analogue for `RootPairing.InvariantForm` of
`RootPairing.RootPositiveForm.exists_mem_support_rootLength_eq`.

## Main results

* `RootPairing.InvariantForm.exists_mem_support_apply_root_root_eq`: every root has the squared
  length of a simple root.
-/

public section

namespace RootPairing.InvariantForm

open TauCeti

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R] [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [P.IsCrystallographic]
  [P.IsReduced]

/-- **Every root has the squared length of one of the simple roots**, for any invariant form. -/
theorem exists_mem_support_apply_root_root_eq (B : P.InvariantForm) (b : P.Base) (j : ι) :
    ∃ i ∈ b.support, B.form (P.root j) (P.root j) = B.form (P.root i) (P.root i) := by
  obtain ⟨i, hi, w, rfl⟩ := exists_mem_support_weylGroupToPerm_eq b j
  refine ⟨i, hi, ?_⟩
  rw [← P.weylGroup_apply_root w i]
  exact apply_weylGroup_smul P w _ _

end RootPairing.InvariantForm
