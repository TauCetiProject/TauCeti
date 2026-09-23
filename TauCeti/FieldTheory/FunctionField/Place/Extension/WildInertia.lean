/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.RamificationGroup
public import Mathlib.GroupTheory.PGroup

/-!
# Positive ramification groups are p-groups

For a place in residue characteristic `p`, every successive quotient of the positive
ramification filtration has exponent `p`. When the inertia group is finite, the filtration
eventually reaches the trivial group. Iterating the quotient statement shows that every
element of a positive ramification group has `p`-power order, so the whole group is a
`p`-group. In particular, the first positive group is the wild inertia group.

This is the group-theoretic conclusion of Stichtenoth, *Algebraic Function Fields and Codes*,
second edition, Proposition 3.8.5. It uses no perfectness assumption on the residue field.
-/

public section

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable (F)

/-- Every positive ramification group of a finite inertia group is a `p`-group in residue
characteristic `p`. This includes the wild inertia group `G₁`. -/
theorem isPGroup_ramificationGroup_succ (P : Place k F') (p i : ℕ)
    [Fact p.Prime] [CharP P.ResidueField p] [Finite (ramificationGroup F P 0)] :
    IsPGroup p (ramificationGroup F P (i + 1)) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot F P
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨N, ?_⟩
  have hpow : ∀ n : ℕ,
      (g : P.integers.decompositionSubgroup F) ^ (p ^ n) ∈
        ramificationGroup F P (i + n + 1) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, pow_one, Nat.add_zero] using g.property
    | succ n ih =>
      have h := pow_mem_ramificationGroup_of_charP F P p (i + n) ih
      simpa [pow_succ, pow_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hbot : ramificationGroup F P (i + N + 1) = ⊥ :=
    hN _ (by omega)
  have h : (g : P.integers.decompositionSubgroup F) ^ (p ^ N) = 1 := by
    have := hpow N
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact Subtype.ext h

/-- If the residue characteristic does not divide the order of inertia, every positive
ramification group is trivial. In a finite Galois extension with separable residue extension,
the order of inertia is the ramification index, so this is the tame case. -/
theorem ramificationGroup_succ_eq_bot_of_not_dvd_card_inertia
    (P : Place k F') (p i : ℕ) [Fact p.Prime] [CharP P.ResidueField p]
    [Finite (ramificationGroup F P 0)]
    (hp : ¬ p ∣ Nat.card (ramificationGroup F P 0)) :
    ramificationGroup F P (i + 1) = ⊥ := by
  let _ : Finite (ramificationGroup F P (i + 1)) :=
    Finite.of_injective
      (fun g : ramificationGroup F P (i + 1) ↦
        (⟨g, ramificationGroup_antitone F P (Nat.zero_le (i + 1)) g.2⟩ :
          ramificationGroup F P 0))
      (fun _ _ h ↦ Subtype.ext (congrArg
        (fun g : ramificationGroup F P 0 ↦ (g : P.integers.decompositionSubgroup F)) h))
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp (isPGroup_ramificationGroup_succ F P p i))
  have hdvd : Nat.card (ramificationGroup F P (i + 1)) ∣
      Nat.card (ramificationGroup F P 0) :=
    Subgroup.card_dvd_of_le (ramificationGroup_antitone F P (Nat.zero_le (i + 1)))
  cases n with
  | zero =>
    rw [Subgroup.eq_bot_iff_card]
    simpa [pow_zero] using hn
  | succ n =>
    have hpdvd : p ∣ Nat.card (ramificationGroup F P (i + 1)) := by
      rw [hn, pow_succ]
      exact dvd_mul_left p (p ^ n)
    exact (hp (hpdvd.trans hdvd)).elim

/-- Tame ramification has no wild inertia: in a finite Galois extension with separable
residue extension, if the residue characteristic does not divide the ramification index,
every positive ramification group is trivial. -/
theorem ramificationGroup_succ_eq_bot_of_tame (P : Place k F') (p i : ℕ)
    [Fact p.Prime] [CharP P.ResidueField p]
    [FiniteDimensional F F'] [IsGalois F F']
    [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]
    (hp : ¬ p ∣ ramificationIdx F P) :
    ramificationGroup F P (i + 1) = ⊥ := by
  have : Finite (ramificationGroup F P 0) :=
    Finite.of_injective
      (fun g : ramificationGroup F P 0 ↦ (g : F' ≃ₐ[F] F'))
      (fun _ _ h ↦ Subtype.ext (Subtype.ext h))
  apply ramificationGroup_succ_eq_bot_of_not_dvd_card_inertia F P p i
  rwa [ramificationGroup_zero, card_inertiaSubgroup F P]

end Place

end TauCeti
