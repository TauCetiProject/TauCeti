/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.LinearAlgebra.Trace.Basic
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Invariants

/-!
# Basic facts about characters

The trace character vanishes when the representation space is not finite-dimensional.
The character of the restriction of a representation along a monoid homomorphism `f` is the
composite of its character with `f` (`Representation.character_comp`).

The trace of the action is a class function for a representation over a commutative semiring on
any additive commutative monoid (`Representation.trace_conj`). `Representation.character` and
`Representation.char_conj` ask for an additive group structure on the carrier, so this form
applies to representations such as `Representation.symmetricPower`, which is built on the
additive monoid instance of the symmetric power rather than on the one underlying its additive
group.

An element `g` acting by a scalar `c` has character `dim V · c`
(`Representation.character_eq_finrank_mul_of_apply_eq_smul`).

A commutator `g x g⁻¹ x⁻¹` acting by a scalar `a ≠ 1` forces the character to vanish at `g`
(`Representation.character_eq_zero_of_commutator_apply_eq_smul`): conjugating `g` by `x`
multiplies `ρ g` by that scalar while preserving the trace.

The `n`-th power map is a bijection of a group `G` whenever `n` is coprime to `|G|`
(`Nat.Coprime.pow_left_bijective`), so the average `|G|⁻¹ ∑_g χ(gⁿ)` of an irreducible character
`χ` equals the average `|G|⁻¹ ∑_g χ(g)`, which is the dimension of the invariants
(`Representation.card_inv_mul_sum_char_eq_finrank`). An irreducible representation has a nonzero
invariant vector only when it is the trivial line, so the average is `1` for the trivial
character and `0` otherwise (`Representation.card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime`).

For a right action of a group `H`, written as a representation of `Hᵐᵒᵖ`, the dimension of the
invariants of a subgroup `S` whose order is finite and nonzero in the field is the average
`|S|⁻¹ ∑_{u ∈ S} tr(u)` of the character over `S`
(`Representation.natCast_finrank_invariants_comp_op_subtype`).
-/

public section

universe u v w

namespace Representation

/-- The character vanishes on a representation space that is not finite-dimensional. -/
theorem character_eq_zero_of_not_finite {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (h : ¬ FiniteDimensional k V) :
    ρ.character = 0 := by
  funext g
  simp [character, TauCeti.LinearMap.trace_eq_zero_of_not_finite h]

/-- The character of the restriction of `ρ` along `f : H →* G` is `ρ.character ∘ f`. -/
@[simp]
theorem character_comp {k G H V : Type*} [Field k] [Monoid G] [Monoid H] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (f : H →* G) :
    character (ρ.comp f) = ρ.character ∘ f :=
  rfl

/-- The trace of the action is constant on conjugacy classes. This is `Representation.char_conj`
for a representation on an additive commutative monoid. -/
theorem trace_conj {R G M : Type*} [CommSemiring R] [Group G] [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M) (g h : G) :
    LinearMap.trace R M (ρ (h * g * h⁻¹)) = LinearMap.trace R M (ρ g) := by
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]

/-- **The character at an element acting by a scalar.** If `g` acts on `V` as multiplication by
`c`, the character of `ρ` at `g` is `dim V · c`. When `V` is not finite-dimensional both sides are
`0`. -/
theorem character_eq_finrank_mul_of_apply_eq_smul {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) {g : G} {c : k}
    (h : ∀ v, ρ g v = c • v) : ρ.character g = Module.finrank k V * c := by
  by_cases hV : FiniteDimensional k V
  · have hg : ρ g = c • (1 : Module.End k V) := LinearMap.ext fun v => (h v).trans (by simp)
    simp [character, hg, mul_comm]
  · simp [character_eq_zero_of_not_finite ρ hV, Module.finrank_of_not_finite hV]

/-- **A commutator acting by a nontrivial scalar kills the character.** If the commutator
`g x g⁻¹ x⁻¹` acts on `V` as multiplication by a scalar `a ≠ 1`, then the character of `ρ`
vanishes at `g`. No finiteness of `G` or of `V` is needed. -/
theorem character_eq_zero_of_commutator_apply_eq_smul {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) {g x : G} {a : k} (ha : a ≠ 1)
    (h : ∀ v, ρ (g * x * g⁻¹ * x⁻¹) v = a • v) : ρ.character g = 0 := by
  have hc : ρ (g * x * g⁻¹ * x⁻¹) = a • (1 : Module.End k V) :=
    LinearMap.ext fun v => (h v).trans (by simp)
  have key : ρ.character g = a * ρ.character g :=
    calc ρ.character g = ρ.character (g * x * g⁻¹ * x⁻¹ * (x * g * x⁻¹)) := by
          congr 1
          group
      _ = a * ρ.character g := by
          simp [character, map_mul ρ _ (x * g * x⁻¹), hc, ← trace_conj ρ g x]
  have h1 : (1 - a) * ρ.character g = 0 := by linear_combination key
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm ha))

section Average

variable {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [Fintype G]
  [Invertible (Nat.card G : k)] [AddCommGroup V] [Module k V]

/-- **For an irreducible representation and `n` coprime to `|G|`, the average `|G|⁻¹ ∑_g χ(gⁿ)` is
`0` exactly when its character is nontrivial.** Over any field in which `|G|` is invertible. -/
theorem card_inv_mul_sum_char_pow_eq_zero_iff_of_coprime (ρ : Representation k G V)
    [ρ.IsIrreducible] {n : ℕ} (hn : (Nat.card G).Coprime n) :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character (g ^ n) = 0 ↔ ρ.character ≠ fun _ => 1 := by
  have : FiniteDimensional k V := ρ.asModuleEquiv.finiteDimensional
  -- The `n`-th power map permutes `G`, so the average of `χ(gⁿ)` is the dimension of the
  -- invariants.
  rw [Fintype.sum_bijective _ hn.pow_left_bijective _ (ρ.character ·)
    fun _ => rfl, card_inv_mul_sum_char_eq_finrank]
  refine ⟨fun h hχ => ?_, fun hχ => by_contra fun h => hχ ?_⟩
  · rw [← card_inv_mul_sum_char_eq_finrank, hχ, Finset.sum_const, Finset.card_univ,
      Fintype.card_eq_nat_card, nsmul_eq_mul, mul_one, inv_mul_cancel_of_invertible] at h
    exact one_ne_zero h
  · -- A nonzero invariant vector makes `ρ` the trivial line.
    have hne : ρ.invariants ≠ ⊥ := fun hb => h (by rw [hb, finrank_bot, Nat.cast_zero])
    funext g
    rw [‹ρ.IsIrreducible›.eq_trivial_of_invariants_ne_bot hne, char_trivial,
      ‹ρ.IsIrreducible›.finrank_eq_one_of_invariants_ne_bot hne, Nat.cast_one]

end Average

open MulOpposite Module in
/-- **The dimension of the invariants of a finite subgroup is the average of the character.**
For a right action of a group `H` on `M`, written as a representation of `Hᵐᵒᵖ`, and a subgroup
`S` of `H` whose order is finite and nonzero in `K`, `dim M^S = |S|⁻¹ ∑_{u ∈ S} tr(u | M)`. -/
theorem natCast_finrank_invariants_comp_op_subtype {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] [FiniteDimensional K M] {H : Type*} [Group H] (ρ : Representation K Hᵐᵒᵖ M)
    (S : Subgroup H) (hS : (Nat.card S : K) ≠ 0) :
    (finrank K (invariants (ρ.comp (MonoidHom.op S.subtype))) : K) =
      (Nat.card S : K)⁻¹ * ∑ᶠ u : S, ρ.character (op (u : H)) := by
  have := Nat.finite_of_card_ne_zero fun h ↦ hS (by rw [h, Nat.cast_zero])
  have := Fintype.ofFinite S
  have : Fintype Sᵐᵒᵖ := Fintype.ofEquiv S MulOpposite.opEquiv
  have hS' : Nat.card Sᵐᵒᵖ = Nat.card S := Nat.card_congr MulOpposite.opEquiv.symm
  have : Invertible (Nat.card Sᵐᵒᵖ : K) := invertibleOfNonzero (by rwa [hS'])
  rw [← card_inv_mul_sum_char_eq_finrank, hS', finsum_eq_sum_of_fintype, character_comp]
  congr 1
  exact (Fintype.sum_equiv MulOpposite.opEquiv _ _ fun _ ↦ rfl).symm

end Representation
