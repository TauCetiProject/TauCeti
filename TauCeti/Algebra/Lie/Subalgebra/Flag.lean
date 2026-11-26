/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NilpotentExtension
public import TauCeti.Algebra.Lie.Subalgebra.Normalizer

/-!
# Flags of Lie subalgebras by codimension-one steps

A Lie subalgebra `T` strictly inside a finite-dimensional Lie subalgebra `U` grows towards `U` one
dimension at a time whenever it is normalized by an element of `U` outside it: adjoining that
element gives a Lie subalgebra containing `T` as an ideal of codimension one
(`LieSubalgebra.finrank_lieSpan_insert`, `LieSubalgebra.lieSpan_insert_le_normalizer`). This file
iterates that step, keeping track of a property preserved by it, to join `T` to `U` by a flag.
Inside a nilpotent ideal `I` such an element always exists
(`LieIdeal.exists_mem_notMem_lie_mem_of_lt`), so every Lie subalgebra of `I` is joined to `I` by a
flag, in any characteristic.

## Main results

* `TauCeti.LieAlgebra.exists_flag_of_forall_lt`: if every `T` with a property `P` strictly below
  `U` is normalized by an element of `U` outside `T` whose adjunction preserves `P`, then every
  `T ≤ U` with `P T` is joined to `U` by a flag of Lie subalgebras satisfying `P`, each an ideal of
  codimension one in the next.
* `LieIdeal.exists_flag_of_le`: a Lie subalgebra of a finite-dimensional nilpotent ideal `I` is
  joined to `I` by a flag of Lie subalgebras, each an ideal of codimension one in the next.
-/

public section

open Module

namespace TauCeti

namespace LieAlgebra

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- **Climbing by codimension-one steps.** Let `P` be a property of Lie subalgebras such that every
`T` with `P T` strictly below a finite-dimensional Lie subalgebra `U` is normalized by some `x ∈ U`
outside `T` for which the Lie span of `T` and `x` again satisfies `P`. Then every `T ≤ U` with
`P T` is joined to `U` by a flag of Lie subalgebras satisfying `P`, each an ideal of codimension
one in the next. -/
theorem exists_flag_of_forall_lt (P : LieSubalgebra K L → Prop) {U : LieSubalgebra K L}
    [FiniteDimensional K U]
    (hstep : ∀ T, P T → T < U →
      ∃ x ∈ U, x ∉ T ∧ x ∈ T.normalizer ∧ P (LieSubalgebra.lieSpan K L (insert x (T : Set L))))
    {T : LieSubalgebra K L} (hPT : P T) (hTU : T ≤ U) :
    ∃ (S : ℕ → LieSubalgebra K L) (n : ℕ), S 0 = T ∧ S n = U ∧ (∀ i ≤ n, P (S i)) ∧
      ∀ i < n, S i ≤ S (i + 1) ∧ S (i + 1) ≤ (S i).normalizer ∧
        finrank K (S (i + 1)) = finrank K (S i) + 1 := by
  induction hd : finrank K U - finrank K T using Nat.strong_induction_on generalizing T with
  | _ d ih =>
    rcases hTU.lt_or_eq with hlt | rfl
    · obtain ⟨x, hxU, hxT, hx, hPT'⟩ := hstep T hPT hlt
      set T' := LieSubalgebra.lieSpan K L (insert x (T : Set L))
      have hT'U : T' ≤ U := LieSubalgebra.lieSpan_le.mpr (Set.insert_subset hxU hTU)
      have : FiniteDimensional K T :=
        .of_injective (LieSubalgebra.inclusion hTU).toLinearMap
          (LieSubalgebra.inclusion_injective hTU)
      have hrank : finrank K T' = finrank K T + 1 := T.finrank_lieSpan_insert hx hxT
      have hle : finrank K T' ≤ finrank K U :=
        LinearMap.finrank_le_finrank_of_injective (f := (LieSubalgebra.inclusion hT'U).toLinearMap)
          (LieSubalgebra.inclusion_injective hT'U)
      obtain ⟨S, n, hS0, hSn, hP, hS⟩ := ih _ (by omega) hPT' hT'U rfl
      -- Prepend `T` to the flag from `T'` to `U`.
      obtain ⟨S', hS'0, hS'succ⟩ : ∃ S' : ℕ → LieSubalgebra K L, S' 0 = T ∧ ∀ i, S' (i + 1) = S i :=
        ⟨fun | 0 => T | i + 1 => S i, rfl, fun _ ↦ rfl⟩
      refine ⟨S', n + 1, hS'0, by rw [hS'succ, hSn], fun i hi ↦ ?_, fun i hi ↦ ?_⟩
      · rcases i with _ | i
        · rwa [hS'0]
        · rw [hS'succ]
          exact hP i (by omega)
      · rcases i with _ | i
        · rw [hS'succ, hS'0, hS0]
          exact ⟨(T.lt_lieSpan_insert hxT).le, T.lieSpan_insert_le_normalizer hx, hrank⟩
        · rw [hS'succ, hS'succ]
          exact hS i (by omega)
    · exact ⟨fun _ ↦ T, 0, rfl, rfl, fun _ _ ↦ hPT, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩

end LieAlgebra

end TauCeti

namespace LieIdeal

open TauCeti.LieAlgebra

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- **A flag inside a nilpotent ideal.** A Lie subalgebra `T` of a finite-dimensional nilpotent
ideal `I` of a Lie algebra is joined to `I` by a flag of Lie subalgebras
`T = S 0 ≤ S 1 ≤ ⋯ ≤ S n = I` inside `I`, each an ideal of codimension one in the next. No
assumption on the characteristic is needed. -/
theorem exists_flag_of_le (I : LieIdeal K L) [LieRing.IsNilpotent I] [FiniteDimensional K I]
    {T : LieSubalgebra K L} (hTI : T ≤ I) :
    ∃ (S : ℕ → LieSubalgebra K L) (n : ℕ), S 0 = T ∧ S n = I ∧
      (∀ i < n, S i ≤ S (i + 1) ∧ S (i + 1) ≤ (S i).normalizer ∧
        finrank K (S (i + 1)) = finrank K (S i) + 1) ∧
      ∀ i ≤ n, S i ≤ I := by
  have hstep (T' : LieSubalgebra K L) (hT'I : T' ≤ I) (hlt : T' < I) :
      ∃ x ∈ (I : LieSubalgebra K L), x ∉ T' ∧ x ∈ T'.normalizer ∧
        LieSubalgebra.lieSpan K L (insert x (T' : Set L)) ≤ I := by
    obtain ⟨y, hyI, hyT⟩ := IsConcreteLE.exists_of_lt hlt
    have hlt' : T'.toSubmodule < I.toSubmodule :=
      IsConcreteLE.lt_iff_le_and_exists.mpr ⟨fun z hz ↦ hT'I hz, y, hyI, hyT⟩
    obtain ⟨x, hxI, hxT, hx⟩ := I.exists_mem_notMem_lie_mem_of_lt hlt'
    have hxnorm : x ∈ T'.normalizer := (T'.mem_normalizer_iff x).mpr fun y hy ↦ hx y (hT'I hy)
    exact ⟨x, hxI, hxT, hxnorm, LieSubalgebra.lieSpan_le.mpr (Set.insert_subset hxI hT'I)⟩
  have : FiniteDimensional K (I : LieSubalgebra K L) := ‹FiniteDimensional K I›
  obtain ⟨S, n, hS0, hSn, hSI, hS⟩ := exists_flag_of_forall_lt (fun T' ↦ T' ≤ I) hstep hTI hTI
  exact ⟨S, n, hS0, hSn, hS, hSI⟩

end LieIdeal
