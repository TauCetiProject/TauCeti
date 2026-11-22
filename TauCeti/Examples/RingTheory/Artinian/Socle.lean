/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Polynomial.AlgebraMap
import TauCeti.RingTheory.Artinian.Socle

/-!
# Checks for the occurrence of characters of Artinian algebras

`AlgHom.exists_ne_zero_forall_smul_eq_smul` says that every character of a commutative Artinian
`k`-algebra has a nonzero eigenvector in every faithful module. The checks below show that neither
faithfulness nor the Artinian hypothesis can be dropped.

* Let `k × k` act on `k` through the first projection. This action is not faithful, and the
  second-projection character has no nonzero eigenvector, although the first-projection character
  does.
* The polynomial ring `k[X]` acts faithfully on itself, but the character `X ↦ 0` has no nonzero
  eigenvector: it would be a nonzero polynomial killed by `X`.
-/

open Polynomial

namespace TauCeti.ArtinianSocleChecks

variable (k : Type*) [Field k]

/-- *Failure of occurrence for a nonfaithful action*: when `k × k` acts on `k` through the first
projection, the second-projection character has no nonzero eigenvector. -/
example :
    letI : Module (k × k) k := Module.compHom k (RingHom.fst k k)
    ¬ ∃ v : k, v ≠ 0 ∧ ∀ h : k × k, h • v = AlgHom.snd k k k h • v := by
  let : Module (k × k) k := Module.compHom k (RingHom.fst k k)
  rintro ⟨v, hv, h⟩
  have h01 := h (0, 1)
  simp only [AlgHom.snd_apply, one_smul] at h01
  exact hv (h01.symm.trans (zero_smul k v))

/-- The same action has the first-projection character on the eigenvector `1`, and its
annihilator contains `(0, 1)`, on which the second projection does not vanish. -/
example :
    letI : Module (k × k) k := Module.compHom k (RingHom.fst k k)
    (∀ h : k × k, h • (1 : k) = AlgHom.fst k k k h • (1 : k)) ∧
      ((0, 1) : k × k) ∈ Module.annihilator (k × k) k ∧
      ((0, 1) : k × k) ∉ RingHom.ker (AlgHom.snd k k k) := by
  let : Module (k × k) k := Module.compHom k (RingHom.fst k k)
  refine ⟨fun h ↦ rfl, Module.mem_annihilator.2 fun v ↦ zero_smul k v, by simp⟩

/-- The Artinian hypothesis cannot be dropped: `k[X]` acts faithfully on itself, but the character
`X ↦ 0` has no nonzero eigenvector. -/
example : ¬ ∃ v : k[X], v ≠ 0 ∧ ∀ h : k[X], h • v = aeval (0 : k) h • v := by
  rintro ⟨v, hv, h⟩
  have hX := h X
  simp only [aeval_X, zero_smul, smul_eq_mul, mul_eq_zero, X_ne_zero, false_or] at hX
  exact hv hX

end TauCeti.ArtinianSocleChecks
