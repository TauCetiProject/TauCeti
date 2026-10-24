/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Negation and topological nilpotence

Mathlib closes `IsTopologicallyNilpotent` under the operations that a topology on the ring makes
available — `zero`, `add`, `mul_left`, `mul_right`, `map` — but not under negation. This file adds
that, at the hypotheses the statement needs: a `MonoidWithZero` with a distributive negation, and
continuity of negation.

No uniformity, nonarchimedean neighbourhood basis or commutativity is involved. `(-a) ^ n` is
`a ^ n` for even `n` and `-(a ^ n)` for odd `n`, and both of those sequences tend to `0` as soon as
negation is continuous, so every neighbourhood of `0` eventually contains `(-a) ^ n` whichever
parity `n` has.

## Main results

* `IsTopologicallyNilpotent.neg` : the negation of a topologically nilpotent element is
  topologically nilpotent.
* `isTopologicallyNilpotent_neg` : the same fact as a `simp` iff, mirroring `isPowerBounded_neg`.
* `IsTopologicallyNilpotent.pow` : a positive power of a topologically nilpotent element is
  topologically nilpotent.
* `eventually_mul_pow_mem_of_isTopologicallyNilpotent`, and its `.exists` form: a topologically
  nilpotent element absorbs any fixed element into any open subring.
* `Prod.isTopologicallyNilpotent_iff` : an element of a product is topologically nilpotent exactly
  when both of its components are.
* `IsTopologicallyNilpotent.mem_jacobson_bot`, `topologicalNilradical_le_jacobson_bot` : if an
  open ideal lies in the Jacobson radical (for instance, the ring is adically complete with respect
  to it), so does every topologically nilpotent element.
* `IsTopologicallyNilpotent.isUnit_add_left` : when the topological nilradical lies in the
  Jacobson radical, a unit plus a topologically nilpotent element is a unit.

## Provenance

The statement is AINTLIB's `IsTopologicallyNilpotent.neg`, branch `dev/adic-spaces`, commit
`37bbdaeb`, Apache-2.0, Chris Birkbeck, `projects/AdicSpaces/Adic spaces/GeometricSeries.lean`.
There it sits inside the geometric-series development over a complete nonarchimedean uniform
commutative ring, and the sign on the odd powers is absorbed by an open subgroup. Only the
statement is followed here: the hypotheses are weakened to the ones the result needs, and the
open-subgroup step is replaced by the two-sequence argument above, which needs no nonarchimedean
basis. The iff form has no counterpart in the source.

## References

* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/GeometricSeries.lean`.
-/

open Filter Topology

public section

variable {R : Type*} [MonoidWithZero R] [HasDistribNeg R] [TopologicalSpace R] [ContinuousNeg R]

/-- **The negation of a topologically nilpotent element is topologically nilpotent.** -/
theorem IsTopologicallyNilpotent.neg {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (-a) := by
  -- `ha` is restated as a `Tendsto` before any dot notation: `ha.neg` would resolve to this very
  -- lemma rather than to `Filter.Tendsto.neg`.
  have ht : Tendsto (fun n : ℕ ↦ a ^ n) atTop (𝓝 0) := ha
  have hneg : Tendsto (fun n : ℕ ↦ -(a ^ n)) atTop (𝓝 0) := by simpa using ht.neg
  unfold IsTopologicallyNilpotent
  rw [tendsto_def] at ht hneg ⊢
  intro U hU
  filter_upwards [ht U hU, hneg U hU] with n h1 h2
  rcases Nat.even_or_odd n with he | ho
  · simpa [he.neg_pow] using h1
  · simpa [ho.neg_pow] using h2

/-- Topological nilpotence is invariant under negation. -/
@[simp]
theorem isTopologicallyNilpotent_neg {a : R} :
    IsTopologicallyNilpotent (-a) ↔ IsTopologicallyNilpotent a :=
  ⟨fun h ↦ by simpa using h.neg, IsTopologicallyNilpotent.neg⟩

section Pow

variable {M : Type*} [MonoidWithZero M] [TopologicalSpace M]

/-- **A positive power of a topologically nilpotent element is topologically nilpotent**: the
powers of `a ^ n` are a subsequence of the powers of `a`. -/
theorem IsTopologicallyNilpotent.pow {a : M} (ha : IsTopologicallyNilpotent a) {n : ℕ}
    (hn : n ≠ 0) : IsTopologicallyNilpotent (a ^ n) := by
  have h := ha.comp
    (tendsto_atTop_mono (fun m ↦ Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hn)) tendsto_id)
  simpa only [IsTopologicallyNilpotent, Function.comp_def, id, pow_mul] using h

end Pow

section Absorb

variable {A : Type*} [Ring A] [TopologicalSpace A] [SeparatelyContinuousMul A]

/-- **A topologically nilpotent element absorbs any element into any open subring.** For `s`
topologically nilpotent and `B` open, `a * s ^ n` lies in `B` for all large `n`.

Multiplication by `a` is continuous, so `B` pulls back to a neighbourhood of `0`, and the powers of
`s` converge to `0`. Neither commutativity nor continuity of addition is used — only
`SeparatelyContinuousMul` — and no Huber structure enters, which is why this sits here rather than
beside the ring-of-definition form it generalises,
`TauCeti.Huber.PairOfDefinition.exists_pow_idealOfDefinition_mul_mem`. -/
theorem eventually_mul_pow_mem_of_isTopologicallyNilpotent {s : A}
    (hs : IsTopologicallyNilpotent s) {B : Subring A} (hB : IsOpen (B : Set A)) (a : A) :
    ∀ᶠ n : ℕ in atTop, a * s ^ n ∈ B :=
  hs ((hB.preimage (continuous_const_mul a)).mem_nhds (by simp))

/-- The existential form of `eventually_mul_pow_mem_of_isTopologicallyNilpotent`: some power of a
topologically nilpotent element carries `a` into an open subring. -/
theorem exists_mul_pow_mem_of_isTopologicallyNilpotent {s : A}
    (hs : IsTopologicallyNilpotent s) {B : Subring A} (hB : IsOpen (B : Set A)) (a : A) :
    ∃ n : ℕ, a * s ^ n ∈ B :=
  (eventually_mul_pow_mem_of_isTopologicallyNilpotent hs hB a).exists

end Absorb

section Prod

variable {M N : Type*} [MonoidWithZero M] [MonoidWithZero N] [TopologicalSpace M]
  [TopologicalSpace N]

/-- An element of a product of topological monoids with zero is topologically nilpotent exactly
when both of its components are: the powers of `x` are taken componentwise, and a sequence in a
product converges exactly when both of its component sequences do. -/
@[simp]
theorem Prod.isTopologicallyNilpotent_iff {x : M × N} :
    IsTopologicallyNilpotent x ↔ IsTopologicallyNilpotent x.1 ∧ IsTopologicallyNilpotent x.2 := by
  simp only [IsTopologicallyNilpotent, Prod.tendsto_iff, Prod.pow_fst, Prod.pow_snd, Prod.fst_zero,
    Prod.snd_zero]

end Prod

section Jacobson

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- **Topologically nilpotent elements lie in the Jacobson radical** as soon as some open ideal
`I` does, for instance when `R` is `I`-adically complete (`IsAdicComplete.le_jacobson_bot`): a
power of a topologically nilpotent element lies in `I`, and the Jacobson radical is radical. -/
theorem IsTopologicallyNilpotent.mem_jacobson_bot {I : Ideal R} (hI : IsOpen (I : Set R))
    (hIJ : I ≤ (⊥ : Ideal R).jacobson) {a : R} (ha : IsTopologicallyNilpotent a) :
    a ∈ (⊥ : Ideal R).jacobson :=
  (Ideal.isRadical_jacobson ⊥).radical_le_iff.mpr hIJ
    (ha.exists_pow_mem_of_mem_nhds (hI.mem_nhds I.zero_mem))

/-- In a linearly topologized ring, the topological nilradical lies in the Jacobson radical as soon
as some open ideal does. -/
theorem topologicalNilradical_le_jacobson_bot [IsLinearTopology R R] {I : Ideal R}
    (hI : IsOpen (I : Set R)) (hIJ : I ≤ (⊥ : Ideal R).jacobson) :
    topologicalNilradical R ≤ (⊥ : Ideal R).jacobson := fun _ ha ↦
  (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp ha).mem_jacobson_bot hI hIJ

/-- When the topological nilradical lies in the Jacobson radical (for instance, by
`topologicalNilradical_le_jacobson_bot`), a unit plus a topologically nilpotent element is a unit.
Compare `IsNilpotent.isUnit_add_left_of_commute`. -/
theorem IsTopologicallyNilpotent.isUnit_add_left [IsLinearTopology R R]
    (hR : topologicalNilradical R ≤ (⊥ : Ideal R).jacobson) {t u : R}
    (ht : IsTopologicallyNilpotent t) (hu : IsUnit u) : IsUnit (u + t) := by
  obtain ⟨u, rfl⟩ := hu
  have h := Ideal.mem_jacobson_bot.mp
    (hR (IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr ht)) ↑u⁻¹
  simpa [mul_add, mul_left_comm (u : R) t, add_comm] using u.isUnit.mul h

end Jacobson

end
