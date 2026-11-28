/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.RootSystem.Weyl.ExtendedAffine.Bruhat
import TauCeti.LinearAlgebra.RootSystem.Weyl.ExtendedAffine.SpecialNode

/-!
# Checks for extended affine length and Bruhat order

In type `A₁` the alcove stabilizer in the extended affine Weyl group has two elements. They both
have length zero and are incomparable. At the coroot lattice the length-zero subgroup is trivial.
The rank-one check uses the characterization that the highest root belongs to the base.
-/

namespace RootPairing

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [Nonempty ι] [DecidableEq ι]
  [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] [Archimedean R] (b : P.Base)

/-- Over the coroot lattice, length zero characterizes the identity. -/
example (f : P.latticeAffineWeylGroup (P.corootSpan ℤ) le_rfl P.corootSpan_le_coweightLattice) :
    b.latticeAffineLength (P.corootSpan ℤ) le_rfl P.corootSpan_le_coweightLattice f = 0 ↔
      f = 1 := by
  rw [b.latticeAffineLength_eq_zero_iff, latticeFundamentalAlcoveStabilizer_corootSpan,
    Subgroup.mem_bot]
  constructor
  · intro h
    apply Subtype.ext
    simpa using h
  · rintro rfl
    simp

/-- Distinct alcove stabilizers are incomparable, in both directions. -/
example (ω : P.fundamentalAlcoveStabilizer b) (hω : ω ≠ 1) :
    let i := Subgroup.inclusion (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b)
    ¬ b.ExtendedAffineBruhatLE 1 (i ω) ∧ ¬ b.ExtendedAffineBruhatLE (i ω) 1 := by
  intro i
  have hi : Function.Injective i := Subgroup.inclusion_injective _
  have hω' : i ω ≠ 1 := fun h ↦ hω (hi (h.trans (map_one i).symm))
  rw [b.extendedAffineBruhatLE_stabilizer_iff,
    b.extendedAffineBruhatLE_iff_eq_of_length_eq_zero b.extendedAffineLength_one]
  exact ⟨Ne.symm hω', hω'⟩

variable [P.IsRootSystem]

/-- In type `A₁` the alcove stabilizer has order two. -/
example (hθ : b.highestRoot ∈ b.support) : Nat.card (P.fundamentalAlcoveStabilizer b) = 2 := by
  classical
  let j : b.support := ⟨b.highestRoot, hθ⟩
  have hmark (i : b.support) : b.affineMarks (some i) = if i = j then 1 else 0 :=
    b.affineMarks_some_eq_of_root_highestRoot_eq_sum
      (f := fun i ↦ if i = j then 1 else 0) (by simp [j]) i
  have hall (i : b.support) : i = j := by
    by_contra h
    have hz : b.affineMarks (some i) = 0 := by
      simp [hmark, h]
    have hp := b.affineMarks_pos (some i)
    omega
  have : Subsingleton b.support := ⟨fun i k ↦ (hall i).trans (hall k).symm⟩
  have : Nonempty b.support := ⟨j⟩
  have hs : b.specialNodes = Set.univ := by
    ext k
    cases k with
    | none => simp
    | some i => simp [Base.mem_specialNodes, hmark, hall i]
  rw [Nat.card_congr (fundamentalAlcoveStabilizerEquivSpecialNodes b), hs,
    Nat.card_congr (Equiv.Set.univ _), Nat.card_eq_fintype_card, Fintype.card_option]
  have hc : Fintype.card b.support = 1 := Fintype.card_eq_one_iff.mpr ⟨j, hall⟩
  omega

end RootPairing
