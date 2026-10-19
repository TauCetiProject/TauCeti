/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import TauCeti.GroupTheory.FiniteAbelian.Duality
public import TauCeti.GroupTheory.GroupAction.ConjAct

/-!
# An odd permutation inverts every linear character of the alternating group

Let `α` be a finite type and let `χ` be a homomorphism from `alternatingGroup α` to a commutative
monoid. Conjugation by an *even* permutation cannot move `χ`, the target being commutative. This
file proves that conjugation by an **odd** permutation inverts it, once the target has inverses:

`χ (s x s⁻¹) = (χ x)⁻¹` for every `s ∉ alternatingGroup α` and every `x`.

The consequence the file exists for is that a **nontrivial** linear character `χ` satisfies
`χ ∘ conj s ≠ χ` for every odd `s`: otherwise `χ` would be fixed by conjugation by `s` and the same
lemma would make it trivial. So the odd permutations move `χ`, and `{χ, χ⁻¹}` is a single orbit of
two characters under the conjugation action of `Equiv.Perm α`. That is exactly the hypothesis of the
Mackey irreducibility criterion for an induced linear character, applied to `A₄ ◁ S₄` in
`TauCeti.RepresentationTheory.Induction.Clifford.Alternating.Basic`.

For that application to be about something, `alternatingGroup α` must *have* a nontrivial linear
character, and for `Nat.card α = 4` this file lists the characters exactly. Mathlib's
`alternatingGroup.kleinFour_eq_commutator` identifies the commutator subgroup of `A₄` with the
Klein four subgroup, of order `4` inside a group of order `12`, so the abelianization `A₄ / V₄` has
order `3`. Two consequences are drawn, and they need different hypotheses.

Unconditionally on the coefficients, every linear character of `A₄` is cube-root-of-unity valued:
it factors through `A₄ / V₄`, in which every element cubes to `1`. Under the hypothesis that the
coefficients have enough roots of unity for that quotient, the character group of a finite group is
the dual of its abelianization (`TauCeti.card_monoidHom_eq_card_abelianization`), so `A₄` has
exactly **three** linear characters. Three is prime, so any nontrivial one generates: the characters
are `1`, `χ` and `χ⁻¹`. Combined with the inversion lemma above this closes the orbit picture at
`A₄ ◁ S₄` -- the two nontrivial characters are `χ` and `χ⁻¹`, and an odd permutation carries one to
the other, so they form a *single* orbit of the conjugation action of `Equiv.Perm α`, not merely a
pair of distinct characters inside one.

The roots-of-unity hypothesis on the last three statements is not merely a device to rule out too
*few* characters: the character group can also be too *large*. Over `M = ℂ × ℂ` the characters of
`A₄` are the pairs of cube roots of unity, nine of them, and a nontrivial one such as `(ω, 1)` has
neither `(1, ω)` nor its inverse among its powers, so the classification genuinely fails there.
`HasEnoughRootsOfUnity M (Monoid.exponent (Abelianization (alternatingGroup α)))` rules that out by
asking for a primitive cube root of unity in `M` and for the cube roots of unity in `M` to form a
cyclic group. It is a sufficient condition, not one shown here to be necessary.

For `4 < Nat.card α` the alternating group is perfect instead, and the statements above are then all
vacuously about the trivial character.

## Main statements

* `MonoidHom.eq_one_of_map_conjNormal_eq_alternatingGroup`: **a linear character of the alternating
  group fixed by conjugation by an odd permutation is trivial.**
* `MonoidHom.alternatingGroup_le_ker`: **every homomorphism from `Equiv.Perm α` to a commutative
  monoid kills the alternating group**.
* `MonoidHom.map_conjNormal_alternatingGroup_eq_inv`: **an odd permutation inverts every linear
  character of the alternating group**, with `MonoidHom.comp_conjNormal_alternatingGroup_eq_inv`
  its form as an equality of homomorphisms.
* `MonoidHom.exists_map_conjNormal_alternatingGroup_ne`: an odd permutation moves every nontrivial
  linear character -- the hypothesis of the Mackey irreducibility criterion.
* `MonoidHom.comp_conjNormal_alternatingGroup_ne`: the same as an inequality of homomorphisms, so
  that a nontrivial linear character and its conjugate by an odd permutation are two distinct
  members of one orbit.
* `TauCeti.card_abelianization_alternatingGroup`: **the abelianization of `A₄` has order three.**
* `TauCeti.monoidHom_alternatingGroup_apply_pow_three` and
  `TauCeti.monoidHom_alternatingGroup_pow_three`: **the linear characters of `A₄` are
  cube-root-of-unity valued**, over arbitrary commutative coefficients.
* `TauCeti.card_monoidHom_alternatingGroup`: **`A₄` has exactly three linear characters**, with
  `TauCeti.exists_monoidHom_alternatingGroup_ne_one` the corollary that one of them is nontrivial.
* `TauCeti.monoidHom_alternatingGroup_eq_one_or_eq_or_eq_inv`: **the linear characters of `A₄` are
  `1`, `χ` and `χ⁻¹`** for any nontrivial `χ`.
* `TauCeti.exists_comp_conjNormal_alternatingGroup_eq`: **the two nontrivial linear characters of
  `A₄` form a single orbit** of the conjugation action of `Equiv.Perm α`.

## Implementation notes

The inversion lemma is proved uniformly in `α`. The product of `χ` with its conjugate by `s` is
fixed by conjugation by `s`, because `s * s` is even; and a character fixed by conjugation by *one*
odd permutation is fixed by conjugation by *every* permutation, since the odd permutations form a
single coset of the even ones. Such a character kills every three-cycle `c`, because `c` is
conjugate in `Equiv.Perm α` to its own inverse, so the value at `c` squares to `1` while also
cubing to `1`. Three-cycles generate the alternating group, so the character is trivial, which is
the claim.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 5.
-/

public section

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace MonoidHom

section Fixed

variable {M : Type*} [CommMonoid M] (χ : alternatingGroup α →* M)

/-- A linear character of the alternating group fixed by conjugation by one odd permutation is
fixed by conjugation by every permutation. -/
private theorem map_conjNormal_alternatingGroup_of_fixed {s : Perm α}
    (hs : s ∉ alternatingGroup α)
    (h : ∀ x : alternatingGroup α, χ (MulAut.conjNormal s x) = χ x) (g : Perm α)
    (x : alternatingGroup α) : χ (MulAut.conjNormal g x) = χ x := by
  by_cases hg : g ∈ alternatingGroup α
  · exact map_conjNormal_val χ ⟨g, hg⟩ x
  -- Every odd permutation is an even one times `s`.
  have hgs : g * s⁻¹ ∈ alternatingGroup α := by
    simp only [mem_alternatingGroup, ← ne_eq, Int.units_ne_iff_eq_neg] at hg hs
    simp [mem_alternatingGroup, hg, hs]
  calc χ (MulAut.conjNormal g x)
      = χ (MulAut.conjNormal (g * s⁻¹) (MulAut.conjNormal s x)) := by
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel_right]
    _ = χ x := (map_conjNormal_val χ ⟨g * s⁻¹, hgs⟩ _).trans (h x)

/-- **A linear character of the alternating group fixed by conjugation by an odd permutation is
trivial.** Equivalently, the conjugation action of `Equiv.Perm α` on the linear characters of
`alternatingGroup α` has only the trivial character as a fixed point. -/
theorem eq_one_of_map_conjNormal_eq_alternatingGroup {s : Perm α} (hs : s ∉ alternatingGroup α)
    (h : ∀ x : alternatingGroup α, χ (MulAut.conjNormal s x) = χ x) : χ = 1 := by
  have hall := map_conjNormal_alternatingGroup_of_fixed χ hs h
  -- Three-cycles generate the alternating group, so it suffices that `χ` kills each of them.
  have hgen : Subgroup.closure {c : alternatingGroup α | (c : Perm α).IsThreeCycle} = ⊤ := by
    rw [← closure_three_cycles_eq_alternating]
    exact Subgroup.closure_closure_coe_preimage
  refine eq_of_eqOn_dense hgen fun c (hc : (c : Perm α).IsThreeCycle) => ?_
  -- A three-cycle is conjugate in `Equiv.Perm α` to its inverse, so its value squares to `1`.
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_inv (c : Perm α)).symm)
  have hinv : χ c⁻¹ = χ c := by
    rw [← hall g c]
    congr 1
    exact Subtype.ext (by simpa using hg.symm)
  have hsq : χ c ^ 2 = 1 := by
    rw [sq]
    nth_rw 2 [← hinv]
    rw [← map_mul, mul_inv_cancel, map_one]
  have hcube : χ c ^ 3 = 1 := by
    rw [← map_pow, ← hc.orderOf, Subgroup.orderOf_coe, pow_orderOf_eq_one, map_one]
  simpa using pow_gcd_eq_one.mpr ⟨hsq, hcube⟩

/-- **Every homomorphism from a permutation group to a commutative monoid kills the alternating
group.** -/
theorem alternatingGroup_le_ker (χ : Perm α →* M) : alternatingGroup α ≤ χ.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  rcases subsingleton_or_nontrivial α with hα | hα
  · rw [Subsingleton.elim x 1, map_one]
  obtain ⟨s, hs⟩ := sign_surjective α (-1)
  have hs' : s ∉ alternatingGroup α := by
    rw [mem_alternatingGroup, hs]
    decide
  have hone := eq_one_of_map_conjNormal_eq_alternatingGroup (χ.comp (alternatingGroup α).subtype)
    hs' fun y => (isConj_iff_eq.mp
      (χ.map_isConj (isConj_iff.mpr ⟨s, (MulAut.conjNormal_apply s y).symm⟩))).symm
  simpa using DFunLike.congr_fun hone ⟨x, hx⟩

end Fixed

section Inversion

/-- **An odd permutation inverts every linear character of the alternating group.** -/
@[simp]
theorem map_conjNormal_alternatingGroup_eq_inv {M : Type*} [DivisionCommMonoid M]
    (χ : alternatingGroup α →* M) {s : Perm α} (hs : s ∉ alternatingGroup α)
    (x : alternatingGroup α) : χ (MulAut.conjNormal s x) = (χ x)⁻¹ := by
  have hsq : s * s ∈ alternatingGroup α := by simp [mem_alternatingGroup, Int.units_mul_self]
  -- The product of `χ` with its conjugate by `s` is fixed by conjugation by `s`, hence trivial.
  have hone := eq_one_of_map_conjNormal_eq_alternatingGroup
    (χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)).toMonoidHom * χ) hs fun y => by
      have hss : χ (MulAut.conjNormal (s * s) y) = χ y := map_conjNormal_val χ ⟨s * s, hsq⟩ y
      simp only [MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
        MulEquiv.coe_toMonoidHom]
      rw [← MulAut.mul_apply, ← map_mul MulAut.conjNormal, hss, mul_comm]
  exact eq_inv_of_mul_eq_one_left (by simpa using DFunLike.congr_fun hone x)

variable {M : Type*} [CommGroup M] (χ : alternatingGroup α →* M)

/-- **An odd permutation inverts every linear character of the alternating group**, as an equality
of homomorphisms. -/
@[simp]
theorem comp_conjNormal_alternatingGroup_eq_inv {s : Perm α} (hs : s ∉ alternatingGroup α) :
    χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)) = χ⁻¹ :=
  MonoidHom.ext fun x => map_conjNormal_alternatingGroup_eq_inv χ hs x

end Inversion

section Nontrivial

variable {M : Type*} [CommMonoid M] (χ : alternatingGroup α →* M)

/-- **An odd permutation moves every nontrivial linear character of the alternating group.** This
is the hypothesis of the Mackey irreducibility criterion for an induced linear character, checked
at `A₄ ◁ S₄`. -/
theorem exists_map_conjNormal_alternatingGroup_ne (hχ : χ ≠ 1) {s : Perm α}
    (hs : s ∉ alternatingGroup α) : ∃ x : alternatingGroup α, χ (MulAut.conjNormal s x) ≠ χ x :=
  not_forall.mp fun hcon => hχ (eq_one_of_map_conjNormal_eq_alternatingGroup χ hs hcon)

/-- **A nontrivial linear character of the alternating group and its conjugate by an odd
permutation are distinct**, so the two of them make up a single orbit of the conjugation action of
`Equiv.Perm α` on the characters. -/
theorem comp_conjNormal_alternatingGroup_ne (hχ : χ ≠ 1) {s : Perm α}
    (hs : s ∉ alternatingGroup α) :
    χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)) ≠ χ := fun hcon =>
  hχ (eq_one_of_map_conjNormal_eq_alternatingGroup χ hs fun x => DFunLike.congr_fun hcon x)

end Nontrivial

end MonoidHom

namespace TauCeti

section CharacterGroup

/-- **The abelianization of `A₄` has order three.** -/
theorem card_abelianization_alternatingGroup (hα : Nat.card α = 4) :
    Nat.card (Abelianization (alternatingGroup α)) = 3 := by
  have hcomm : Nat.card (commutator (alternatingGroup α)) = 4 := by
    rw [← alternatingGroup.kleinFour_eq_commutator hα,
      alternatingGroup.kleinFour_card_of_card_eq_four hα]
  have hsplit : Nat.card (alternatingGroup α) =
      Nat.card (Abelianization (alternatingGroup α)) *
        Nat.card (commutator (alternatingGroup α)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [alternatingGroup.card_of_card_eq_four hα, hcomm] at hsplit
  omega

section CubeRoots

variable {M : Type*} [CommMonoid M]

-- The two reductions below spell their hypothesis with `Fintype.card α`, the `simp`-normal form of
-- `Nat.card α = 4`, so that `simp` can discharge it and they can carry `@[simp]`.

/-- **The linear characters of `A₄` are cube-root-of-unity valued**, over arbitrary commutative
coefficients. -/
@[simp]
theorem monoidHom_alternatingGroup_apply_pow_three (hα : Fintype.card α = 4)
    (χ : alternatingGroup α →* M) (x : alternatingGroup α) : χ x ^ 3 = 1 := by
  have hx : Abelianization.of x ^ 3 = 1 := by
    rw [← card_abelianization_alternatingGroup (α := α) (by rwa [Nat.card_eq_fintype_card])]
    exact pow_card_eq_one'
  rw [← χ.coe_toHomUnits, ← Units.val_pow_eq_pow_val, ← Abelianization.lift_apply_of, ← map_pow,
    hx, map_one, Units.val_one]

/-- **A linear character of `A₄` is a cube root of unity in the character group**, the form of
`TauCeti.monoidHom_alternatingGroup_apply_pow_three` as an equation between homomorphisms. -/
@[simp]
theorem monoidHom_alternatingGroup_pow_three (hα : Fintype.card α = 4)
    (χ : alternatingGroup α →* M) : χ ^ 3 = 1 := by
  ext x
  rw [MonoidHom.pow_apply, MonoidHom.one_apply,
    monoidHom_alternatingGroup_apply_pow_three hα χ x]

end CubeRoots

section EnoughRoots

variable (M : Type*) [CommMonoid M]
  [HasEnoughRootsOfUnity M (Monoid.exponent (Abelianization (alternatingGroup α)))]

/-- **The linear characters of `A₄` form a group of order three**, when `M` has enough roots of
unity for the exponent of the abelianization `A₄ / V₄`. -/
theorem card_monoidHom_alternatingGroup (hα : Nat.card α = 4) :
    Nat.card (alternatingGroup α →* Mˣ) = 3 := by
  rw [card_monoidHom_eq_card_abelianization, card_abelianization_alternatingGroup hα]

/-- **`A₄` has a nontrivial linear character** valued in any commutative monoid with enough roots
of unity for the exponent of the abelianization `A₄ / V₄`, such as an algebraically closed field of
characteristic zero. -/
theorem exists_monoidHom_alternatingGroup_ne_one (hα : Nat.card α = 4) :
    ∃ χ : alternatingGroup α →* Mˣ, χ ≠ 1 := by
  have h3 := card_monoidHom_alternatingGroup M hα
  have : Finite (alternatingGroup α →* Mˣ) := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial (alternatingGroup α →* Mˣ) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact exists_ne 1

variable {M}

/-- **`A₄` has exactly three linear characters**, and once a nontrivial one `χ` is fixed they are
`1`, `χ` and `χ⁻¹`. Some hypothesis on `M` is needed on both counts: without roots of unity there
are too few characters, while over `M = ℂ × ℂ` there are nine of them and the conclusion fails. -/
theorem monoidHom_alternatingGroup_eq_one_or_eq_or_eq_inv (hα : Nat.card α = 4)
    {χ : alternatingGroup α →* Mˣ} (hχ : χ ≠ 1) (ψ : alternatingGroup α →* Mˣ) :
    ψ = 1 ∨ ψ = χ ∨ ψ = χ⁻¹ := by
  have h3 := card_monoidHom_alternatingGroup M hα
  have _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  -- The character group has prime order three, so `χ` has order three and generates it.
  have hcube : χ ^ 3 = 1 := h3 ▸ pow_card_eq_one'
  have hord : orderOf χ = 3 := orderOf_eq_prime hcube hχ
  have hsq : χ ^ 2 = χ⁻¹ := eq_inv_of_mul_eq_one_left (by rwa [← pow_succ])
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff ψ χ).mp (mem_powers_of_prime_card h3 hχ)
  rw [← pow_mod_orderOf, hord]
  have : n % 3 < 3 := n.mod_lt three_pos
  interval_cases n % 3 <;> simp [hsq]

/-- **The two nontrivial linear characters of `A₄` make up a single `S₄`-orbit**: the conjugation
action of `Equiv.Perm α` is transitive on them. -/
theorem exists_comp_conjNormal_alternatingGroup_eq (hα : Nat.card α = 4)
    {χ ψ : alternatingGroup α →* Mˣ} (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ s : Perm α, χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)) = ψ := by
  rcases monoidHom_alternatingGroup_eq_one_or_eq_or_eq_inv hα hχ ψ with h | rfl | rfl
  · exact absurd h hψ
  · exact ⟨1, by ext; simp⟩
  · -- An odd permutation inverts `χ`.
    have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨s, hs⟩ := sign_surjective α (-1)
    have hs' : s ∉ alternatingGroup α := by
      rw [mem_alternatingGroup, hs]
      decide
    exact ⟨s, MonoidHom.comp_conjNormal_alternatingGroup_eq_inv χ hs'⟩

end EnoughRoots

end CharacterGroup

end TauCeti
