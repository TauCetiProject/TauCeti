/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# The ramification groups of an ideal, in lower numbering

Let a group `M` act on a commutative ring `R` by ring automorphisms, and let `P` be an ideal.
The `i`-th ramification group of `P` collects the automorphisms that move every element of `R`
by something in `P ^ (i + 1)`:

`σ ∈ P.ramificationGroup M i ↔ ∀ x, σ • x - x ∈ P ^ (i + 1)`.

This is the lower numbering, and the indexing convention is the standard one: the shift by one
makes `ramificationGroup M P 0` the inertia group rather than the whole decomposition group.
The decomposition group is deliberately **not** a member of this family — it keeps its own name,
`MulAction.stabilizer`, and is never written `G (-1)`.

## What the family measures

The `i`-th group is the inertia subgroup of `P ^ (i + 1)`: it records how deeply an automorphism
acts trivially near `P`. The family is decreasing, sits inside the inertia group, and is normal
in the decomposition group, so it filters that group by depth of triviality — each step
identifying the automorphisms that are indistinguishable from the identity to one order further.
Over a Noetherian domain with a faithful action the filtration is separated: only the identity
survives every stage.

That filtration is what the exponents of the different and the discriminant are computed from,
and the indexing above is the numbering those formulas assume.

## Main results

* `Ideal.ramificationGroup`: the `i`-th ramification group, in lower numbering, with
  `Ideal.ramificationGroup_def` restating the definition.
* `Ideal.mem_ramificationGroup_iff`: its membership criterion, the simp normal form.
* `Ideal.ramificationGroup_zero`: the `0`-th ramification group is the inertia group.
* `Ideal.ramificationGroup_antitone`: vanishing to higher order is a stronger condition, so the
  family decreases.
* `Ideal.ramificationGroup_le_inertia`, `Ideal.ramificationGroup_le_stabilizer`: every
  ramification group sits inside the inertia group, hence inside the decomposition group.
* `Ideal.ramificationGroup_smul`: conjugation carries the ramification groups of `P` to those
  of `g • P`.
* `Ideal.instNormalRamificationGroupStabilizer`: they are normal in the decomposition group.
* `Ideal.iInf_ramificationGroup_eq_bot`: over a Noetherian domain with a faithful action, the
  ramification groups meet in the trivial group.

## References

* `TauCeti/RingTheory/LocalRing/RamificationGroup.lean` formalizes this filtration for the
  maximal ideal of a local ring, indexed by `ℤ`; the family here is the same construction for an
  arbitrary ideal, and that file is the prior formalization this ideal-level API generalizes.
* J-P. Serre, *Local Fields*, Chapter IV §1.
* J. Neukirch, *Algebraic Number Theory*, Chapter II §9.
-/

public section

open MulAction

open scoped Pointwise

namespace Ideal

variable (M : Type*) [Group M] {R : Type*} [CommRing R] [MulSemiringAction M R]

/-- **The `i`-th ramification group of `P`, in lower numbering**: the automorphisms that move
every element of `R` by something in `P ^ (i + 1)`. Equivalently, the inertia subgroup of
`P ^ (i + 1)`, which is how it is defined. -/
def ramificationGroup (P : Ideal R) (i : ℕ) : Subgroup M := (P ^ (i + 1)).inertia M

variable {M}

/-- **The defining restatement**, so that consumers never have to unfold the definition. -/
theorem ramificationGroup_def (P : Ideal R) (i : ℕ) :
    P.ramificationGroup M i = (P ^ (i + 1)).inertia M :=
  (rfl)

/-- **Membership in the `i`-th ramification group.** -/
@[simp]
theorem mem_ramificationGroup_iff {P : Ideal R} {i : ℕ} {σ : M} :
    σ ∈ P.ramificationGroup M i ↔ ∀ x, σ • x - x ∈ P ^ (i + 1) :=
  Ideal.mem_inertia

/-- **The `0`-th ramification group is the inertia group**: acting trivially to order `1` is
acting trivially modulo `P`. -/
@[simp]
theorem ramificationGroup_zero (P : Ideal R) : P.ramificationGroup M 0 = P.inertia M := by
  rw [ramificationGroup, zero_add, pow_one]

/-- The ramification groups decrease: vanishing to higher order is a stronger condition. -/
theorem ramificationGroup_antitone (P : Ideal R) : Antitone (P.ramificationGroup M) := by
  intro i j h σ hσ x
  exact Ideal.pow_le_pow_right (Nat.succ_le_succ h) (mem_ramificationGroup_iff.1 hσ x)

/-- Every ramification group sits inside the inertia group. -/
theorem ramificationGroup_le_inertia (P : Ideal R) (i : ℕ) :
    P.ramificationGroup M i ≤ P.inertia M :=
  (P.ramificationGroup_zero (M := M)) ▸ P.ramificationGroup_antitone (Nat.zero_le i)

/-- Every ramification group sits inside the decomposition group. -/
theorem ramificationGroup_le_stabilizer (P : Ideal R) (i : ℕ) :
    P.ramificationGroup M i ≤ stabilizer M P :=
  (P.ramificationGroup_le_inertia i).trans (inertia_le_stabilizer P)

/-- **Conjugation carries the ramification groups of `P` to those of `g • P`.** -/
theorem ramificationGroup_smul (g : M) (P : Ideal R) (i : ℕ) :
    (g • P).ramificationGroup M i = (P.ramificationGroup M i).map (MulAut.conj g) := by
  rw [ramificationGroup, ramificationGroup, ← smul_pow', inertia_smul]

/-- **The ramification groups are normal in the decomposition group.** -/
instance (P : Ideal R) (i : ℕ) : (P.ramificationGroup (stabilizer M P) i).Normal := by
  simp_rw [ramificationGroup, Subgroup.normal_iff_map_conj_eq, ← inertia_smul]
  exact fun g ↦ congrArg (inertia _)
    ((smul_pow' (g : M) P (i + 1)).trans (congrArg (· ^ (i + 1)) g.2))

/-- **The ramification groups meet in the trivial group**, so the filtration is separated: no
automorphism but the identity acts trivially to every order. -/
theorem iInf_ramificationGroup_eq_bot [IsNoetherianRing R] [IsDomain R] [FaithfulSMul M R]
    (P : Ideal R) (hP : P ≠ ⊤) : ⨅ i, P.ramificationGroup M i = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_iInf] at hσ
  rw [Subgroup.mem_bot]
  refine FaithfulSMul.eq_of_smul_eq_smul (α := R) fun x => ?_
  -- `P ^ 0 = ⊤` carries no information, so the `i = 0` step is separate.
  have hall : ∀ i : ℕ, σ • x - x ∈ P ^ i := fun i => by
    cases i with
    | zero => simp
    | succ n => exact mem_ramificationGroup_iff.1 (hσ n) x
  have hmem : σ • x - x ∈ (⊥ : Ideal R) :=
    Ideal.iInf_pow_eq_bot_of_isDomain P hP ▸ (Submodule.mem_iInf _).2 hall
  simpa [sub_eq_zero] using hmem

end Ideal

end
