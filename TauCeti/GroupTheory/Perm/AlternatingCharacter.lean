/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import TauCeti.GroupTheory.FiniteAbelian.Duality
public import TauCeti.GroupTheory.GroupAction.ConjAct

/-!
# An odd permutation inverts every linear character of the alternating group

Let `α` be a finite type and let `χ` be a homomorphism from `alternatingGroup α` to a commutative
monoid. Conjugation by an *even* permutation cannot move `χ`, the target being commutative. This
file proves that conjugation by an **odd** permutation inverts it, once the target has inverses:

`χ (s x s⁻¹) = (χ x)⁻¹` for every `s ∉ alternatingGroup α` and every `x`.

The argument is short and uniform in `α`. The product of `χ` with its conjugate by `s` is fixed by
conjugation by `s`, because `s * s` is even; and a character fixed by conjugation by *one* odd
permutation is fixed by conjugation by *every* permutation, since the odd permutations form a
single coset of the even ones. Such a character kills every three-cycle `c`, because `c` is
conjugate in `Equiv.Perm α` to its own inverse, so the value at `c` squares to `1` while also
cubing to `1`. Three-cycles generate the alternating group, so the character is trivial, which is
the claim.

The consequence the file exists for is that a **nontrivial** linear character `χ` satisfies
`χ ∘ conj s ≠ χ` for every odd `s`: otherwise `χ` would be fixed by conjugation by `s` and the same
lemma would make it trivial. So the odd permutations move `χ`, and `{χ, χ⁻¹}` is a single orbit of
two characters under the conjugation action of `Equiv.Perm α`. That is exactly the hypothesis of the
Mackey irreducibility criterion for an induced linear character, applied to `A₄ ◁ S₄` in
`TauCeti.RepresentationTheory.Induction.Clifford.Alternating`.

For that application to be about something, `alternatingGroup α` must *have* a nontrivial linear
character, and for `Nat.card α = 4` the file counts them exactly. Mathlib's
`alternatingGroup.kleinFour_eq_commutator` identifies the commutator subgroup of `A₄` with the
Klein four subgroup, of order `4` inside a group of order `12`, so the abelianization `A₄ / V₄` has
order `3`; the character group of a finite group is the dual of its abelianization
(`TauCeti.card_monoidHom_eq_card_abelianization`), so `A₄` has exactly **three** linear characters
whenever `M` has enough roots of unity. Three is prime, so any nontrivial one generates: the
characters are `1`, `χ` and `χ⁻¹`, each of them a cube root of unity. Combined with the inversion
lemma above this closes the orbit picture at `A₄ ◁ S₄` -- the two nontrivial characters are `χ` and
`χ⁻¹`, and an odd permutation carries one to the other, so they form a *single* orbit of the
conjugation action of `S₄`, not merely a pair of distinct characters inside one. For
`4 < Nat.card α` the alternating group is perfect instead, and the statements above are then all
vacuously about the trivial character.

## Main statements

* `MonoidHom.eq_one_of_map_conjNormal_eq_alternatingGroup`: **a linear character of the alternating
  group fixed by conjugation by an odd permutation is trivial.**
* `MonoidHom.map_conjNormal_alternatingGroup_eq_inv`: **an odd permutation inverts every linear
  character of the alternating group**, with `MonoidHom.comp_conjNormal_alternatingGroup_eq_inv`
  its form as an equality of homomorphisms.
* `MonoidHom.exists_map_conjNormal_alternatingGroup_ne`: an odd permutation moves every nontrivial
  linear character -- the hypothesis of the Mackey irreducibility criterion.
* `MonoidHom.comp_conjNormal_alternatingGroup_ne`: the same as an inequality of homomorphisms, so
  that a nontrivial linear character and its conjugate by an odd permutation are two distinct
  members of one orbit.
* `TauCeti.card_abelianization_alternatingGroup`: **the abelianization of `A₄` has order three.**
* `TauCeti.card_monoidHom_alternatingGroup`: **`A₄` has exactly three linear characters**, with
  `TauCeti.exists_monoidHom_alternatingGroup_ne_one` the corollary that one of them is nontrivial.
* `TauCeti.monoidHom_alternatingGroup_pow_three` and
  `TauCeti.monoidHom_alternatingGroup_apply_pow_three`: the linear characters of `A₄` are
  cube-root-of-unity valued.
* `TauCeti.monoidHom_alternatingGroup_eq_one_or_eq_or_eq_inv`: **the linear characters of `A₄` are
  `1`, `χ` and `χ⁻¹`** for any nontrivial `χ`.
* `TauCeti.exists_comp_conjNormal_alternatingGroup_eq`: **the two nontrivial linear characters of
  `A₄` form a single orbit** of the conjugation action of `Equiv.Perm α`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 5.
* [Induction and restriction roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md),
  the "Clifford on `A₄ ◁ S₄`" worked example, which asks for the linear characters of `A₄` to be
  the trivial one and two cube-root-of-unity valued ones forming a single `S₄`-orbit.
-/

public section

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace TauCeti

/-- Two odd permutations differ by an even one. -/
private theorem mul_inv_mem_alternatingGroup {g s : Perm α} (hg : g ∉ alternatingGroup α)
    (hs : s ∉ alternatingGroup α) : g * s⁻¹ ∈ alternatingGroup α := by
  simp only [mem_alternatingGroup] at hg hs ⊢
  rw [map_mul, map_inv]
  rcases Int.units_eq_one_or (sign g) with h | h
  · exact absurd h hg
  · rcases Int.units_eq_one_or (sign s) with h' | h'
    · exact absurd h' hs
    · rw [h, h']
      decide

/-- The square of an odd permutation is even. -/
private theorem mul_self_mem_alternatingGroup {s : Perm α} (hs : s ∉ alternatingGroup α) :
    s * s ∈ alternatingGroup α := by
  simp only [mem_alternatingGroup] at hs ⊢
  rw [map_mul]
  rcases Int.units_eq_one_or (sign s) with h | h
  · exact absurd h hs
  · rw [h]
    decide

end TauCeti

namespace MonoidHom

open TauCeti

section Fixed

variable {M : Type*} [CommMonoid M] (χ : alternatingGroup α →* M)

/-- A linear character fixed by conjugation by one odd permutation is fixed by conjugation by
every permutation: the even ones fix it because the target is commutative, and every odd one is an
even one times the given one. -/
private theorem map_conjNormal_alternatingGroup_of_fixed {s : Perm α}
    (hs : s ∉ alternatingGroup α)
    (h : ∀ x : alternatingGroup α, χ (MulAut.conjNormal s x) = χ x) (g : Perm α)
    (x : alternatingGroup α) : χ (MulAut.conjNormal g x) = χ x := by
  by_cases hg : g ∈ alternatingGroup α
  · exact map_conjNormal_val χ ⟨g, hg⟩ x
  · have hgs : g * s⁻¹ ∈ alternatingGroup α := mul_inv_mem_alternatingGroup hg hs
    have hfac : (MulAut.conjNormal g : MulAut (alternatingGroup α)) =
        MulAut.conjNormal ((⟨g * s⁻¹, hgs⟩ : alternatingGroup α) : Perm α) *
          MulAut.conjNormal s := by
      rw [← map_mul]
      congr 1
      simp
    rw [hfac]
    exact (map_conjNormal_val χ ⟨g * s⁻¹, hgs⟩ _).trans (h x)

/-- **A linear character of the alternating group fixed by conjugation by an odd permutation is
trivial.** Equivalently, the conjugation action of `Equiv.Perm α` on the linear characters of
`alternatingGroup α` has only the trivial character as a fixed point. -/
theorem eq_one_of_map_conjNormal_eq_alternatingGroup {s : Perm α} (hs : s ∉ alternatingGroup α)
    (h : ∀ x : alternatingGroup α, χ (MulAut.conjNormal s x) = χ x) : χ = 1 := by
  have hall := map_conjNormal_alternatingGroup_of_fixed χ hs h
  -- The character kills every three-cycle.
  have hthree : ∀ c : Perm α, c.IsThreeCycle → ∀ hc : c ∈ alternatingGroup α, χ ⟨c, hc⟩ = 1 := by
    intro c hc hcmem
    -- Every permutation is conjugate to its inverse: the two have the same cycle type.
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_inv c).symm)
    have hconj : MulAut.conjNormal g (⟨c, hcmem⟩ : alternatingGroup α) = (⟨c, hcmem⟩)⁻¹ :=
      Subtype.ext (by simpa using hg)
    have hinv : χ ((⟨c, hcmem⟩ : alternatingGroup α)⁻¹) = χ ⟨c, hcmem⟩ := by
      rw [← hconj]
      exact hall g _
    have hsq : χ (⟨c, hcmem⟩ : alternatingGroup α) ^ 2 = 1 := by
      have hmul : χ (⟨c, hcmem⟩ : alternatingGroup α) * χ ((⟨c, hcmem⟩ : alternatingGroup α)⁻¹)
          = 1 := by
        rw [← map_mul, mul_inv_cancel, _root_.map_one]
      rwa [hinv, ← pow_two] at hmul
    have hpow : (⟨c, hcmem⟩ : alternatingGroup α) ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [Subgroup.orderOf_mk, hc.orderOf])
    have hcube : χ (⟨c, hcmem⟩ : alternatingGroup α) ^ 3 = 1 := by
      rw [← _root_.map_pow, hpow, _root_.map_one]
    have hstep : χ (⟨c, hcmem⟩ : alternatingGroup α) ^ 2 * χ (⟨c, hcmem⟩ : alternatingGroup α)
        = 1 := by
      rw [← pow_succ]
      exact hcube
    rwa [hsq, one_mul] at hstep
  -- Three-cycles generate the alternating group, so the kernel is everything.
  have hle : alternatingGroup α ≤ χ.ker.map (alternatingGroup α).subtype := by
    refine le_trans (le_of_eq closure_three_cycles_eq_alternating.symm) ?_
    rw [Subgroup.closure_le]
    rintro c (hc : c.IsThreeCycle)
    exact Subgroup.mem_map.mpr ⟨⟨c, hc.mem_alternatingGroup⟩, hthree c hc _, rfl⟩
  ext x
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp (hle x.2)
  have hyx : y = x := Subtype.ext hxy
  rw [MonoidHom.one_apply, ← hyx]
  exact hy

end Fixed

section Inversion

variable {M : Type*} [CommGroup M] (χ : alternatingGroup α →* M)

/-- **An odd permutation inverts every linear character of the alternating group.** -/
@[simp]
theorem map_conjNormal_alternatingGroup_eq_inv {s : Perm α} (hs : s ∉ alternatingGroup α)
    (x : alternatingGroup α) : χ (MulAut.conjNormal s x) = (χ x)⁻¹ := by
  have hsq : s * s ∈ alternatingGroup α := mul_self_mem_alternatingGroup hs
  have hcomp : ∀ y : alternatingGroup α,
      (MulAut.conjNormal s) ((MulAut.conjNormal s) y) = MulAut.conjNormal (s * s) y := by
    intro y
    rw [map_mul, MulAut.mul_apply]
  have hfix : ∀ y : alternatingGroup α,
      (χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)).toMonoidHom * χ)
          (MulAut.conjNormal s y) =
        (χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)).toMonoidHom * χ) y := by
    intro y
    -- Conjugation by `s * s` lies inside the alternating group, so `χ` does not see it.
    have hss : χ (MulAut.conjNormal (s * s) y) = χ y := map_conjNormal_val χ ⟨s * s, hsq⟩ y
    simp only [MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rw [hcomp y, hss, mul_comm]
  have hone := eq_one_of_map_conjNormal_eq_alternatingGroup _ hs hfix
  have hx : (χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)).toMonoidHom * χ) x = 1 := by
    rw [hone, MonoidHom.one_apply]
  simp only [MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom] at hx
  exact eq_inv_of_mul_eq_one_left hx

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
    (hs : s ∉ alternatingGroup α) : ∃ x : alternatingGroup α, χ (MulAut.conjNormal s x) ≠ χ x := by
  by_contra hcon
  push Not at hcon
  exact hχ (eq_one_of_map_conjNormal_eq_alternatingGroup χ hs hcon)

/-- **A nontrivial linear character of the alternating group and its conjugate by an odd
permutation are distinct**, so the two of them make up a single orbit of the conjugation action of
`Equiv.Perm α` on the characters. -/
theorem comp_conjNormal_alternatingGroup_ne (hχ : χ ≠ 1) {s : Perm α}
    (hs : s ∉ alternatingGroup α) :
    χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)) ≠ χ := fun hcon =>
  hχ (eq_one_of_map_conjNormal_eq_alternatingGroup χ hs
    fun x => congrArg (fun f : alternatingGroup α →* M => f x) hcon)

end Nontrivial

end MonoidHom

namespace TauCeti

section CharacterGroup

/-- **The abelianization of `A₄` has order three.** The commutator subgroup of `alternatingGroup α`
is its Klein four subgroup (`alternatingGroup.kleinFour_eq_commutator`), of order `4` inside a
group of order `12`, so the quotient has order `3`. -/
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

/-- A four-element type carries an odd permutation, namely a transposition. This is what turns the
inversion lemma above into transitivity of the conjugation action on the nontrivial characters. -/
private theorem exists_notMem_alternatingGroup (hα : Nat.card α = 4) :
    ∃ s : Perm α, s ∉ alternatingGroup α := by
  have hnt : Nontrivial α := by
    rw [← Finite.one_lt_card_iff_nontrivial, hα]
    omega
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine ⟨Equiv.swap a b, ?_⟩
  rw [mem_alternatingGroup, Equiv.Perm.sign_swap hab]
  decide

variable (M : Type*) [CommMonoid M]
  [HasEnoughRootsOfUnity M (Monoid.exponent (Abelianization (alternatingGroup α)))]

/-- **The linear characters of `A₄` form a group of order three.** Every linear character factors
through the abelianization `A₄ / V₄`, whose order is three by
`TauCeti.card_abelianization_alternatingGroup`, and a finite commutative group with enough roots of
unity in `M` has exactly as many characters as elements. -/
theorem card_monoidHom_alternatingGroup (hα : Nat.card α = 4) :
    Nat.card (alternatingGroup α →* Mˣ) = 3 := by
  rw [card_monoidHom_eq_card_abelianization, card_abelianization_alternatingGroup hα]

/-- **`A₄` has a nontrivial linear character** valued in any commutative monoid with enough roots
of unity for the exponent of the abelianization `A₄ / V₄`, through which every such character
factors and for which an algebraically closed field of characteristic zero supplies the roots.
This is the count `TauCeti.card_monoidHom_alternatingGroup` read as a nonvanishing statement. -/
theorem exists_monoidHom_alternatingGroup_ne_one (hα : Nat.card α = 4) :
    ∃ χ : alternatingGroup α →* Mˣ, χ ≠ 1 := by
  have hfin : Finite (alternatingGroup α →* Mˣ) :=
    Nat.finite_of_card_ne_zero (by rw [card_monoidHom_alternatingGroup M hα]; omega)
  have hnt : Nontrivial (alternatingGroup α →* Mˣ) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [card_monoidHom_alternatingGroup M hα]; omega)
  exact exists_ne 1

variable {M}

/-- **A linear character of `A₄` is a cube root of unity in the character group**, that group
having order three. -/
theorem monoidHom_alternatingGroup_pow_three (hα : Nat.card α = 4)
    (χ : alternatingGroup α →* Mˣ) : χ ^ 3 = 1 := by
  rw [← card_monoidHom_alternatingGroup M hα]
  exact pow_card_eq_one'

/-- **The linear characters of `A₄` are cube-root-of-unity valued**, the pointwise form of
`TauCeti.monoidHom_alternatingGroup_pow_three`. -/
theorem monoidHom_alternatingGroup_apply_pow_three (hα : Nat.card α = 4)
    (χ : alternatingGroup α →* Mˣ) (x : alternatingGroup α) : χ x ^ 3 = 1 := by
  have h : (χ ^ 3) x = (1 : alternatingGroup α →* Mˣ) x :=
    congrArg (fun f : alternatingGroup α →* Mˣ => f x)
      (monoidHom_alternatingGroup_pow_three hα χ)
  rwa [MonoidHom.pow_apply, MonoidHom.one_apply] at h

/-- **`A₄` has exactly three linear characters**, and once a nontrivial one `χ` is fixed they are
`1`, `χ` and `χ⁻¹`. The character group has prime order three, so every nontrivial element
generates it, and the three powers of `χ` are these. -/
theorem monoidHom_alternatingGroup_eq_one_or_eq_or_eq_inv (hα : Nat.card α = 4)
    {χ : alternatingGroup α →* Mˣ} (hχ : χ ≠ 1) (ψ : alternatingGroup α →* Mˣ) :
    ψ = 1 ∨ ψ = χ ∨ ψ = χ⁻¹ := by
  have hcard := card_monoidHom_alternatingGroup M hα
  have _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf χ = 3 := by
    have hdvd : orderOf χ ∣ 3 := hcard ▸ orderOf_dvd_natCard χ
    rcases (Nat.prime_three).eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hχ
    · exact h
  obtain ⟨n, hn⟩ :=
    Submonoid.mem_powers_iff ψ χ |>.mp (mem_powers_of_prime_card hcard hχ)
  have hstep : χ ^ (n % 3) = ψ := by
    rw [← hord, pow_mod_orderOf]
    exact hn
  have hthree : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hthree with h | h | h
  · rw [h, pow_zero] at hstep
    exact Or.inl hstep.symm
  · rw [h, pow_one] at hstep
    exact Or.inr (Or.inl hstep.symm)
  · refine Or.inr (Or.inr ?_)
    rw [h] at hstep
    have hsq : χ ^ 2 = χ⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      calc χ ^ 2 * χ = χ ^ 3 := (pow_succ χ 2).symm
        _ = 1 := monoidHom_alternatingGroup_pow_three hα χ
    rw [← hstep]
    exact hsq

/-- **The two nontrivial linear characters of `A₄` make up a single `S₄`-orbit.** Conjugation by an
odd permutation inverts a linear character
(`MonoidHom.comp_conjNormal_alternatingGroup_eq_inv`), and by
`TauCeti.monoidHom_alternatingGroup_eq_one_or_eq_or_eq_inv` a character and its inverse are the
only nontrivial ones, so the conjugation action of `Equiv.Perm α` is transitive on them. This is
the orbit datum Clifford theory reads off the pair `A₄ ◁ S₄`. -/
theorem exists_comp_conjNormal_alternatingGroup_eq (hα : Nat.card α = 4)
    {χ ψ : alternatingGroup α →* Mˣ} (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    ∃ s : Perm α, χ.comp (MulAut.conjNormal s : MulAut (alternatingGroup α)) = ψ := by
  rcases monoidHom_alternatingGroup_eq_one_or_eq_or_eq_inv hα hχ ψ with h | h | h
  · exact absurd h hψ
  · refine ⟨1, ?_⟩
    rw [h]
    ext x
    simp
  · obtain ⟨s, hs⟩ := exists_notMem_alternatingGroup hα
    exact ⟨s, by rw [MonoidHom.comp_conjNormal_alternatingGroup_eq_inv χ hs, h]⟩

end CharacterGroup

end TauCeti
