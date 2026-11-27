/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GroupAlgebra.PRegularClasses
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Examples of the `p`-power commutator subspace of a group algebra

Examples of the count `TauCeti.finrank_quotient_pPowerCommutatorSubmodule_monoidAlgebra` for
`C_p = Multiplicative (ZMod p)` over any field `k` of characteristic `p`:

* the only `p`-regular class of `C_p` is the class of `1`, so `k[C_p] / T(k[C_p])` is
  one-dimensional;
* `k[C_p]` is commutative, so its commutator submodule is zero and `k[C_p] / [A, A]` has dimension
  `p`: the `p`-power commutator subspace is much larger than `[A, A]`, and the count is not the
  number of conjugacy classes.
-/

public section

namespace TauCeti.PRegularClassesExamples

open Module

variable (p : ℕ) [hp : Fact p.Prime] (k : Type*) [Field k] [CharP k p]

/-- The only `p`-regular conjugacy class of `C_p` is the class of `1`. -/
theorem pRegularConjClasses_multiplicative_zmod :
    pRegularConjClasses p (Multiplicative (ZMod p)) = {ConjClasses.mk 1} := by
  ext c
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  rw [mk_mem_pRegularConjClasses_iff, Set.mem_singleton_iff, ConjClasses.mk_eq_mk_iff_isConj,
    isConj_one_left]
  constructor
  · intro h
    have hdvd : orderOf g ∣ p := by
      simpa [Nat.card_zmod] using orderOf_dvd_natCard g
    rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact orderOf_eq_one_iff.1 h1
    · rw [h1, Nat.coprime_self] at h
      exact absurd h hp.out.one_lt.ne'
  · rintro rfl
    simp

/-- `C_p` has exactly one `p`-regular conjugacy class. -/
theorem card_pRegularConjClasses_multiplicative_zmod :
    Nat.card (pRegularConjClasses p (Multiplicative (ZMod p))) = 1 := by
  rw [pRegularConjClasses_multiplicative_zmod, Nat.card_unique]

/-- Over a field of characteristic `p`, the quotient of `k[C_p]` by its `p`-power commutator
subspace is one-dimensional. -/
theorem finrank_quotient_pPowerCommutatorSubmodule_multiplicative_zmod :
    finrank k (MonoidAlgebra k (Multiplicative (ZMod p)) ⧸
      pPowerCommutatorSubmodule p k (MonoidAlgebra k (Multiplicative (ZMod p)))) = 1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [finrank_quotient_pPowerCommutatorSubmodule_monoidAlgebra,
    card_pRegularConjClasses_multiplicative_zmod]

omit [CharP k p] in
/-- The commutator submodule of the commutative algebra `k[C_p]` is zero, so the quotient by it
has dimension `p`. -/
theorem finrank_quotient_commutatorSubmodule_multiplicative_zmod :
    finrank k (MonoidAlgebra k (Multiplicative (ZMod p)) ⧸
      commutatorSubmodule k (MonoidAlgebra k (Multiplicative (ZMod p)))) = p := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hbot : commutatorSubmodule k (MonoidAlgebra k (Multiplicative (ZMod p))) = ⊥ :=
    le_bot_iff.1 (commutatorSubmodule_le_iff.2 fun x y ↦ by simp [mul_comm x y])
  rw [(Submodule.quotEquivOfEqBot _ hbot).finrank_eq,
    (MonoidAlgebra.coeffLinearEquiv k).finrank_eq, finrank_finsupp_self,
    Fintype.card_multiplicative, ZMod.card]

end TauCeti.PRegularClassesExamples
