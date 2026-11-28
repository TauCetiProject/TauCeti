/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.HighestWeight

/-!
# `K`-highest vectors of representations of `gl ι`

Let `ε : ι → Bool` be a signature, splitting the indices into two blocks `ι₊ ⊔ ι₋`. The matrix
units `E a b` with `ε a = ε b` span the block diagonal subalgebra `𝔨 = gl ι₊ × gl ι₋`, the
complexified Lie algebra of the maximal compact subgroup `U(p) × U(q)` of the unitary group
`U(p, q)` of the signature. A map `l : ι → α` to an order fixes the matrix units `E a b` with
`l b < l a` as the raising operators: the root `e_a - e_b` is positive for `l`.

A vector `x` of a representation `ρ : gl ι → End M` is **`K`-highest of weight `ν`** for `ε` and
`l` (`TauCeti.IsKHighest`) when each diagonal matrix unit `E a a` acts on `x` by `ν a`, and every
compact raising operator, `E a b` with `ε a = ε b` and `l b < l a`, kills `x`. The zero vector is
allowed, so for a fixed weight these vectors form a subspace (`TauCeti.isKHighest_zero`,
`TauCeti.IsKHighest.add`, `TauCeti.IsKHighest.smul`). This is the condition that the lowest
`K`-types of discrete series and the joint harmonics of the theta correspondence for unitary dual
pairs are stated with, for the representations on the Fock module of
`TauCeti/Algebra/Lie/GeneralLinear/Oscillator/DualPair.lean`, which are not module instances
because the same space carries two of them.

For a single block and the order reversing the order of the indices, a nonzero `K`-highest vector
is a highest weight vector of `TauCeti/Algebra/Lie/GeneralLinear/HighestWeight.lean`
(`TauCeti.isGlHighestWeightVector_iff_isKHighest`).

## Main definitions

* `TauCeti.IsKHighest ρ ε l ν x`: `x` is `K`-highest of weight `ν` for `ε` and the order of `l`.

## Main results

* `TauCeti.isKHighest_iff`: the predicate unfolded, with the projections
  `TauCeti.IsKHighest.map_single_self_apply` and `TauCeti.IsKHighest.map_single_apply_eq_zero`.
* `TauCeti.isKHighest_zero`, `TauCeti.IsKHighest.add`, `TauCeti.IsKHighest.smul`: the
  `K`-highest vectors of a weight form a subspace.
* `TauCeti.isGlHighestWeightVector_iff_isKHighest`: highest weight vectors are the nonzero
  `K`-highest vectors for one block.

## References

* M. Kashiwara and M. Vergne, *On the Segal–Shale–Weil representations and harmonic
  polynomials*, Invent. Math. 44 (1978), 1--47.
* R. Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989), 535--552.
* The predicate corresponds to `New.HCParam.IsKHighest` in
  `src/Lib/DiscreteSeries/Rigidity/RepresentationsAndCasimirs.lean` of grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

section KHighest

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [AddCommGroup M] [Module R M] {α : Type*} [LT α]
  {ρ : Matrix ι ι R →ₗ⁅R⁆ Module.End R M} {ε : ι → Bool} {l : ι → α} {ν : ι → R} {x y : M}

/-- A vector `x` of a representation `ρ` of `gl ι` is **`K`-highest of weight `ν`** for the signs
`ε` and the order of `l` when each diagonal matrix unit `E a a` acts on `x` by `ν a` and `x` is
killed by every matrix unit `E a b` with `ε a = ε b` and `l b < l a`: the raising operators for
`l` of the block diagonal subalgebra of the signature `ε`. The zero vector is allowed. -/
def IsKHighest (ρ : Matrix ι ι R →ₗ⁅R⁆ Module.End R M) (ε : ι → Bool) (l : ι → α) (ν : ι → R)
    (x : M) : Prop :=
  (∀ a, ρ (single a a 1) x = ν a • x) ∧
    ∀ a b, ε a = ε b → l b < l a → ρ (single a b 1) x = 0

/-- `TauCeti.IsKHighest` unfolded. The predicate is not exposed, so this is how it is introduced
and eliminated outside this file. -/
theorem isKHighest_iff :
    IsKHighest ρ ε l ν x ↔ (∀ a, ρ (single a a 1) x = ν a • x) ∧
      ∀ a b, ε a = ε b → l b < l a → ρ (single a b 1) x = 0 :=
  Iff.rfl

namespace IsKHighest

/-- The diagonal matrix unit `E a a` acts on a `K`-highest vector by the `a`-th entry of its
weight. -/
theorem map_single_self_apply (h : IsKHighest ρ ε l ν x) (a : ι) :
    ρ (single a a 1) x = ν a • x :=
  h.1 a

/-- The compact raising operators kill a `K`-highest vector. -/
theorem map_single_apply_eq_zero (h : IsKHighest ρ ε l ν x) {a b : ι} (hab : ε a = ε b)
    (hl : l b < l a) : ρ (single a b 1) x = 0 :=
  h.2 a b hab hl

/-- The sum of two `K`-highest vectors of the same weight is `K`-highest of that weight. -/
theorem add (hx : IsKHighest ρ ε l ν x) (hy : IsKHighest ρ ε l ν y) :
    IsKHighest ρ ε l ν (x + y) :=
  ⟨fun a ↦ by rw [map_add, hx.1 a, hy.1 a, smul_add],
    fun a b hab hl ↦ by rw [map_add, hx.2 a b hab hl, hy.2 a b hab hl, add_zero]⟩

/-- A multiple of a `K`-highest vector is `K`-highest of the same weight. -/
theorem smul (hx : IsKHighest ρ ε l ν x) (c : R) : IsKHighest ρ ε l ν (c • x) :=
  ⟨fun a ↦ by rw [map_smul, hx.1 a, smul_comm], fun a b hab hl ↦ by
    rw [map_smul, hx.2 a b hab hl, smul_zero]⟩

end IsKHighest

variable (ρ ε l ν) in
/-- The zero vector is `K`-highest of every weight. -/
@[simp]
theorem isKHighest_zero : IsKHighest ρ ε l ν 0 :=
  ⟨fun _ ↦ by simp, fun _ _ _ _ ↦ by simp⟩

end KHighest

/-! ### Highest weight vectors as `K`-highest vectors -/

section HighestWeight

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule (Matrix n n R) M]
  [LieModule R (Matrix n n R) M] {mu : n → R} {v : M}

/-- **Highest weight vectors are the nonzero `K`-highest vectors for one block.** For the
signature with a single block, every matrix unit is compact, and the raising operators `E i j`,
`i < j`, of a highest weight vector are those with `l j < l i` for `l` the order-reversing map
`OrderDual.toDual`. -/
theorem isGlHighestWeightVector_iff_isKHighest :
    IsGlHighestWeightVector mu v ↔
      v ≠ 0 ∧ IsKHighest (LieModule.toEnd R (Matrix n n R) M) (fun _ ↦ true) OrderDual.toDual
        mu v := by
  simp only [isGlHighestWeightVector_iff, isKHighest_iff, LieModule.toEnd_apply_apply,
    OrderDual.toDual_lt_toDual, forall_const]

end HighestWeight

end TauCeti
