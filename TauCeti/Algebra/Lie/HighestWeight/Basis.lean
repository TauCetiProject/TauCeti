/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basis.Borel
public import TauCeti.Algebra.Lie.Basis.Cartan
public import TauCeti.Algebra.Lie.HighestWeight.Basic

/-!
# Highest-weight vectors from a Lie algebra basis

This file connects a `LieAlgebra.Basis` to the positive-system definition of a highest-weight
vector. The positive-nilradical and Borel bridge is developed in
`TauCeti.Algebra.Lie.Basis.Borel`; here it reduces the highest-weight-vector condition to
annihilation by the raising operators `eᵢ`. Dually, the simple coroots of that base are the
Cartan generators `hᵢ`, so dominance is read on the `hᵢ`, and the basis of the dual of the Cartan
subalgebra dual to the `hᵢ` consists of the fundamental weights.

## Main results

* `LieAlgebra.Basis.isHighestWeightVector_iff_forall_e` reduces the highest-weight condition to
  annihilation by the raising operators.
* `LieAlgebra.Basis.isDominantIntegral_base_iff` reads dominance on the Cartan generators.
* `LieAlgebra.Basis.isDominantIntegral_cartanBasis_dualBasis`: the fundamental weights, the
  vectors of the basis dual to the Cartan generators, are dominant integral.
-/

public section

open LieAlgebra LieModule Module

namespace LieAlgebra.Basis

universe u v w

variable {ι : Type*} [Fintype ι]
  {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L}

variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M]
  [LieModule K L M]

/-- A vector is highest weight for the base of a Lie algebra basis exactly when it is a nonzero
weight vector annihilated by every raising operator. -/
theorem isHighestWeightVector_iff_forall_e (b : LieAlgebra.Basis ι H)
    {lam : Module.Dual K H} {v : M} :
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    TauCeti.IsHighestWeightVector b.base lam v ↔
      v ≠ 0 ∧ (∀ x : H, ⁅(x : L), v⁆ = lam x • v) ∧ ∀ i, ⁅b.e i, v⁆ = 0 := by
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  rw [TauCeti.isHighestWeightVector_iff, b.positiveNilradical_eq_lieSpan_e]
  refine and_congr_right' (and_congr_right' ?_)
  constructor
  · intro h i
    exact h (b.e i) (LieSubalgebra.subset_lieSpan (Set.mem_range_self i))
  · intro h x hx
    have hle : LieSubalgebra.lieSpan K L (Set.range b.e) ≤ TauCeti.lieAnnihilator K L v :=
      TauCeti.lieSpan_le_lieAnnihilator K L (by rintro - ⟨i, rfl⟩; exact h i)
    exact (TauCeti.mem_lieAnnihilator K L).mp (hle hx)

/-- **Dominance is read on the Cartan generators.** A linear form on the Cartan subalgebra is
dominant integral for the base of a Lie algebra basis exactly when its value on every Cartan
generator `hᵢ` is a natural number: those generators are the simple coroots of the base. -/
theorem isDominantIntegral_base_iff (b : LieAlgebra.Basis ι H) {lam : Module.Dual K H} :
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    TauCeti.IsDominantIntegral b.base lam ↔ ∀ i, ∃ n : ℕ, lam (b.h' i) = n := by
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  rw [TauCeti.isDominantIntegral_iff]
  refine ⟨fun h i ↦ by simpa using h _ (b.baseSupportEquiv i).2, fun h j hj ↦ ?_⟩
  obtain ⟨i, hi⟩ := b.baseSupportEquiv.surjective ⟨j, hj⟩
  obtain rfl : (b.baseSupportEquiv i : H.root) = j := congrArg Subtype.val hi
  simpa using h i

/-- **The fundamental weights are dominant integral.** The vector `ϖᵢ` of the basis dual to the
Cartan generators takes the value `1` on `hᵢ` and `0` on every other Cartan generator. -/
theorem isDominantIntegral_cartanBasis_dualBasis [DecidableEq ι] (b : LieAlgebra.Basis ι H)
    (i : ι) :
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    TauCeti.IsDominantIntegral b.base (b.cartanBasis.dualBasis i) := by
  rw [isDominantIntegral_base_iff]
  intro j
  refine ⟨if j = i then 1 else 0, ?_⟩
  rw [← cartanBasis_apply, Module.Basis.dualBasis_apply_self]
  split_ifs <;> simp

end LieAlgebra.Basis
