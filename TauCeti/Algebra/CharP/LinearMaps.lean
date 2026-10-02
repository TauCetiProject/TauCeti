/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.RingTheory.Nilpotent.Defs
-- Non-public: `TauCeti.isNilpotent_sub_one_of_pow_expChar_pow_eq_one` is the ring-level dictionary
-- between `p`-power order and unipotence, read here in an endomorphism algebra.
import TauCeti.Algebra.CharP.Unipotent
-- Non-public: `expChar_of_injective_algebraMap`, together with the faithfulness of the action of
-- `k` on the endomorphisms of a nonzero module, transfers the exponential characteristic of `k` to
-- `Module.End k V`; that faithfulness is `Module.IsTorsionFree.to_faithfulSMul` applied to the
-- torsion-freeness of a module over a division semiring.
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Module.Torsion.Field

/-!
# Unipotent endomorphisms and `p`-power order in characteristic `p`

The endomorphism algebra of a nonzero vector space over a field `k` of exponential characteristic
`p` has the same exponential characteristic, because `k` acts faithfully on it, so an operator of
`p`-power order is unipotent: this is the ring-level
`TauCeti.isNilpotent_sub_one_of_pow_expChar_pow_eq_one` read in `Module.End k V`.  Over a zero
vector space the conclusion is vacuous, every endomorphism being `0`, so no nontriviality hypothesis
is needed.

Mathlib records the characteristic of an endomorphism algebra in
`Mathlib/Algebra/CharP/LinearMaps.lean`, whose `Module.charP_end` transfers a prime characteristic
along a non-torsion element; the exponential characteristic of a vector space needs no such element.

## Main results

* `Module.End.isNilpotent_sub_one_of_pow_expChar_pow_eq_one`: an endomorphism of `p`-power order of
  a vector space over a field of exponential characteristic `p` is unipotent.
-/

public section

namespace TauCeti

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- **In exponential characteristic `p`, an endomorphism of `p`-power order is unipotent.** Over a
nonzero vector space this is the ring-level
`TauCeti.isNilpotent_sub_one_of_pow_expChar_pow_eq_one` read in the endomorphism algebra, whose
exponential characteristic is that of `k` because `k` acts faithfully on it; over a zero vector
space every endomorphism is `0`. -/
theorem _root_.Module.End.isNilpotent_sub_one_of_pow_expChar_pow_eq_one (p n : ℕ) [ExpChar k p]
    {f : Module.End k V} (h : f ^ p ^ n = 1) : IsNilpotent (f - 1) := by
  rcases subsingleton_or_nontrivial V with _ | _
  · exact ⟨0, LinearMap.ext fun x => Subsingleton.elim _ _⟩
  · have : ExpChar (Module.End k V) p :=
      expChar_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k (Module.End k V)) p
    exact TauCeti.isNilpotent_sub_one_of_pow_expChar_pow_eq_one p n h

end TauCeti
