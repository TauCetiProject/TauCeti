/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basis.Borel
public import TauCeti.Algebra.Lie.HighestWeight.Basic

/-!
# Highest-weight vectors from a Lie algebra basis

This file connects a `LieAlgebra.Basis` to the positive-system definition of a highest-weight
vector. The positive-nilradical and Borel bridge is developed in
`TauCeti.Algebra.Lie.Basis.Borel`; here it reduces the highest-weight-vector condition to
annihilation by the raising operators `eᵢ`.

## Main results

* `LieAlgebra.Basis.isHighestWeightVector_iff_forall_e` reduces the highest-weight condition to
  annihilation by the raising operators.
-/

public section

open LieAlgebra LieModule Module

namespace LieAlgebra.Basis

universe u v w

variable {ι : Type*} [Finite ι]
  {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L}

variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M]
  [LieModule K L M]

/-- A vector is highest weight for the base of a Lie algebra basis exactly when it is a nonzero
weight vector annihilated by every raising operator. -/
theorem isHighestWeightVector_iff_forall_e (b : LieAlgebra.Basis ι H)
    {lam : Module.Dual K H} {v : M} :
    letI : Fintype ι := Fintype.ofFinite ι
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    TauCeti.IsHighestWeightVector b.base lam v ↔
      v ≠ 0 ∧ (∀ x : H, ⁅(x : L), v⁆ = lam x • v) ∧ ∀ i, ⁅b.e i, v⁆ = 0 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  rw [TauCeti.isHighestWeightVector_iff, b.positiveNilradical_eq_lieSpan_e]
  refine and_congr_right' (and_congr_right' ?_)
  constructor
  · intro h i
    exact h (b.e i) (LieSubalgebra.subset_lieSpan (Set.mem_range_self i))
  · intro h x hx
    have hle : LieSubalgebra.lieSpan K L (Set.range b.e) ≤ TauCeti.lieAnnihilator K L v :=
      LieSubalgebra.lieSpan_le.mpr fun _ hy => by
        obtain ⟨i, rfl⟩ := hy
        exact (TauCeti.mem_lieAnnihilator K L).mpr (h i)
    exact (TauCeti.mem_lieAnnihilator K L).mp (hle hx)

end LieAlgebra.Basis
