/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Conj
public import Mathlib.GroupTheory.Solvable
import TauCeti.RepresentationTheory.CharacterTable.Table
import TauCeti.RepresentationTheory.CharacterTable.Vanishing
import TauCeti.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow

/-!
# Burnside's `pᵃqᵇ` theorem

A finite group whose order has at most two prime divisors is solvable. The proof is the classical
character-theoretic one, and it runs through the statement that a **conjugacy class of prime-power
size larger than one forces a proper nontrivial normal subgroup**
(`TauCeti.not_isSimpleGroup_of_card_carrier_eq_prime_pow`), which is where all the representation
theory is spent.

## The class-size step

Let `g` have a conjugacy class of size `p ^ k` with `k ≠ 0`, and suppose `G` were simple. Column
orthogonality at the classes of `g` and of `1` reads `∑_χ χ(1) χ(g) = 0`, the sum being over the
irreducible characters. The trivial character contributes `1`. If every other irreducible character
either vanished at `g` or had degree divisible by `p`, the remaining terms would add up to `p` times
an algebraic integer, making `-1/p` an algebraic integer; it is rational and not an integer, so some
irreducible character `χ ≠ 1` has `χ(g) ≠ 0` and degree prime to `p`.

Its degree is then coprime to the class size, so Burnside's vanishing theorem
(`Representation.char_eq_zero_or_norm_char_eq_finrank`) applies and gives `‖χ(g)‖ = χ(1)`.
That is the equality case of the bound on a character value, so the affording representation sends
`g` to a scalar (`Representation.exists_apply_eq_smul_of_norm_char_eq_finrank`). Its kernel
is normal, hence trivial or everything: if it is everything the character is constant and row
orthogonality against the trivial character makes its degree `0`, which is absurd; and if it is
trivial the representation is faithful, so `g` commutes with everything and its class is a single
point, contradicting `k ≠ 0`.

## The induction

`TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow` follows by induction on the order. A group
with a proper nontrivial normal subgroup is solvable as soon as that subgroup and the quotient are,
and both are smaller. A simple group with no `q`-torsion is a `p`-group, hence nilpotent. Otherwise
the centre of a Sylow `q`-subgroup `Q` supplies a nontrivial `g` whose centralizer contains `Q`, so
its class has size dividing the index of `Q`, a power of `p`. A class of size one puts `g` in the
centre, which simplicity then makes all of `G`, and a larger one contradicts the class-size step.

## Main results

* `TauCeti.not_isSimpleGroup_of_card_carrier_eq_prime_pow`: **a conjugacy class of prime-power size
  larger than one forces a proper nontrivial normal subgroup.**
* `TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow`: **Burnside's `pᵃqᵇ` theorem**, that a
  finite group of order `pᵃqᵇ` is solvable, with
  `TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow` the divisibility form that the induction
  runs in.

## References

* W. Burnside, *Theory of Groups of Finite Order*, 2nd ed. (1911).
* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Theorem 3.8 and its corollaries.
-/

public section

namespace TauCeti

open Module

universe u

section ClassSize

variable {G : Type u} [Group G] [Finite G]

/-- **Column orthogonality supplies a nontrivial irreducible character that neither vanishes at
`g` nor has degree divisible by `p`.** Summing the column at `g` against the column at `1` gives
`0`, and the trivial character `i₀` contributes `1`; were every other contribution `0` or a
multiple of `p`, the identity would exhibit `-1/p` as an algebraic integer. -/
private theorem exists_ne_of_not_dvd_characterDegree [Invertible (Nat.card G : ℂ)]
    {g : G} (hg1 : g ≠ 1) {p : ℕ} (hp : p.Prime)
    {i₀ : Fin (Nat.card (ConjClasses G))} (hi₀ : irreducibleCharacter ℂ i₀ = fun _ : G => (1 : ℂ)) :
    ∃ i, i ≠ i₀ ∧ irreducibleCharacter ℂ i g ≠ 0 ∧ ¬ p ∣ characterDegree ℂ i := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hd₀ : characterDegree ℂ i₀ = 1 := by
    have h1 : ((characterDegree ℂ i₀ : ℕ) : ℂ) = 1 := by
      rw [← irreducibleCharacter_one (k := ℂ) i₀, hi₀]
    exact_mod_cast h1
  have hsum : ∑ i, irreducibleCharacter ℂ i g * (characterDegree ℂ i : ℂ) = 0 := by
    simpa [hg1] using sum_characterTable_mul_characterTable_inv (k := ℂ) (G := G) g 1
  by_contra hcon
  push Not at hcon
  set z : ℂ := ∑ i ∈ Finset.univ.erase i₀,
    irreducibleCharacter ℂ i g * ((characterDegree ℂ i / p : ℕ) : ℂ) with hzdef
  have hpz : (p : ℂ) * z = ∑ i ∈ Finset.univ.erase i₀,
      irreducibleCharacter ℂ i g * (characterDegree ℂ i : ℂ) := by
    rw [hzdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rcases eq_or_ne (irreducibleCharacter ℂ i g) 0 with h0 | h0
    · rw [h0]; ring
    · have hdvd := hcon i (Finset.mem_erase.1 hi).1 h0
      have hcancel : (p : ℂ) * ((characterDegree ℂ i / p : ℕ) : ℂ)
          = (characterDegree ℂ i : ℂ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      linear_combination irreducibleCharacter ℂ i g * hcancel
  have hsplit := (Finset.add_sum_erase Finset.univ
    (fun i => irreducibleCharacter ℂ i g * (characterDegree ℂ i : ℂ))
    (Finset.mem_univ i₀)).trans hsum
  rw [hi₀, hd₀] at hsplit
  have hone : (1 : ℂ) + (p : ℂ) * z = 0 := by rw [hpz]; simpa using hsplit
  have hzint : IsIntegral ℤ z := by
    rw [hzdef]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (isIntegral_natCast _)
    rw [← character_irreducibleRepresentation ℂ i]
    exact Representation.isIntegral_char _ (isOfFinOrder_of_finite g).orderOf_pos.ne'
      (pow_orderOf_eq_one g)
  -- `p · (-z) = 1` with `-z` an algebraic integer makes `p` divide `1`
  exact hp.ne_one (Nat.dvd_one.1 (dvd_of_isIntegral_of_natCast_mul_eq (m := 1) hzint.neg
    (by push_cast; linear_combination -hone) hp.pos.ne'))

/-- **A conjugacy class of prime-power size larger than one forces a proper normal subgroup.** If
some element of a finite group has a conjugacy class of size `p ^ k` with `p` prime and `k ≠ 0`,
then the group is not simple.

This is the character-theoretic heart of Burnside's `pᵃqᵇ` theorem: it is what a Sylow argument is
fed into. -/
theorem not_isSimpleGroup_of_card_carrier_eq_prime_pow {g : G} {p k : ℕ} (hp : p.Prime)
    (hk : k ≠ 0) (hcard : Nat.card (ConjClasses.mk g).carrier = p ^ k) : ¬ IsSimpleGroup G := by
  intro hsimple
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hgcenter : g ∉ Subgroup.center G := fun hg => (Nat.one_lt_pow hk hp.one_lt).ne' <| by
    rw [← hcard, Nat.card_coe_set_eq, ConjClasses.ncard_carrier_mk_of_mem_center hg]
  -- some nontrivial irreducible character survives at `g` with degree prime to `p`
  obtain ⟨i₀, hi₀⟩ := exists_irreducibleCharacter_eq_one ℂ G
  obtain ⟨i, hne, hchi, hpdvd⟩ := exists_ne_of_not_dvd_characterDegree
    (ne_of_mem_of_not_mem (Subgroup.one_mem _) hgcenter).symm hp hi₀
  -- its degree is coprime to the class size, so the affording representation sends `g` to a scalar
  obtain ⟨μ, hμ⟩ := ((irreducibleRepresentation ℂ i).char_eq_zero_or_exists_apply_eq_smul <| by
    rw [hcard, finrank_fin_fun]; exact (hp.coprime_iff_not_dvd.2 hpdvd).pow_left k).resolve_left
    (by rwa [character_irreducibleRepresentation])
  rcases hsimple.eq_bot_or_eq_top_of_normal
    (MonoidHom.ker (irreducibleRepresentation ℂ i)) with hker | hker
  · -- the representation is faithful, so a scalar value makes `g` central
    refine hgcenter (Subgroup.mem_center_iff.2 fun h => (MonoidHom.ker_eq_bot_iff _).1 hker ?_)
    rw [map_mul, map_mul, hμ, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  · -- the representation is trivial, so its character is constantly its degree, which the
    -- character of a nontrivial irreducible representation is not
    obtain ⟨h, hh⟩ := exists_irreducibleCharacter_ne_characterDegree hi₀ hne
    rw [← character_irreducibleRepresentation ℂ i] at hh
    exact hh (by simp [Representation.character, MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top h)])

end ClassSize

section Burnside

/-- The simple case of Burnside's `pᵃqᵇ` theorem: a finite simple group whose order divides
`pᵃqᵇ`, for primes `p` and `q`, is solvable. -/
private theorem isSolvable_of_isSimpleGroup {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {a b : ℕ} (hdvd : Nat.card G ∣ p ^ a * q ^ b) :
    Group.IsSolvable G := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  by_cases hqdvd : q ∣ Nat.card G
  · -- a nontrivial `g` centralizing a Sylow `q`-subgroup `Q` has class size dividing `[G : Q]`
    obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
    obtain ⟨g, -, hg1, hle⟩ := Q.isPGroup'.exists_ne_one_le_centralizer fun h =>
      Q.not_dvd_index (by rwa [h, Subgroup.index_bot])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 <| (Subgroup.index_dvd_of_le hle).trans <|
      ((hq.coprime_iff_not_dvd.2 Q.not_dvd_index).symm.pow_right b).dvd_of_dvd_mul_right
        ((Subgroup.index_dvd_card _).trans hdvd)
    obtain rfl | hk0 := eq_or_ne k 0
    · -- the class is a point, so `g` is central, and simplicity makes `G` abelian
      have hgc : g ∈ Subgroup.center G := Subgroup.centralizer_eq_top_iff_subset.1
        (Subgroup.index_eq_one.1 (hk.trans (pow_zero p))) (Set.mem_singleton g)
      have := Subgroup.center_eq_top_iff.1 <| (Subgroup.Normal.eq_bot_or_eq_top
        (Subgroup.center G)).resolve_left fun h => hg1 (Subgroup.mem_bot.1 (h ▸ hgc))
      exact inferInstance
    · exact absurd ‹IsSimpleGroup G› (not_isSimpleGroup_of_card_carrier_eq_prime_pow hp hk0
        ((ConjClasses.card_carrier_mk g).trans hk))
  · -- no `q`-torsion: the group is a `p`-group, hence nilpotent
    have := (IsPGroup.of_card_dvd_pow (p := p) <|
      ((hq.coprime_iff_not_dvd.2 hqdvd).symm.pow_right b).dvd_of_dvd_mul_right hdvd).isNilpotent
    exact inferInstance

/-- The induction behind Burnside's `pᵃqᵇ` theorem, on the order of the group. -/
private theorem isSolvable_aux {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (a b : ℕ) (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → Nat.card G ∣ p ^ a * q ^ b →
      Group.IsSolvable G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro G _ _ rfl hdvd
    rcases subsingleton_or_nontrivial G with hsub | hnt
    · exact inferInstance
    by_cases hN : IsSimpleGroup G
    · exact isSolvable_of_isSimpleGroup hp hq hdvd
    -- otherwise split along a proper nontrivial normal subgroup; it and the quotient are smaller
    obtain ⟨N, hnorm, hbot, htop⟩ : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
      simpa [isSimpleGroup_iff, hnt, not_or] using hN
    rw [← N.index_mul_card] at ih
    exact (Group.isSolvable_iff_subgroup_quotient N).2
      ⟨ih _ (lt_mul_of_one_lt_left Nat.card_pos (N.one_lt_index_of_ne_top htop)) N rfl
        ((Subgroup.card_subgroup_dvd_card N).trans hdvd),
        ih _ (lt_mul_of_one_lt_right (Nat.pos_of_ne_zero N.index_ne_zero_of_finite)
          (N.one_lt_card_iff_ne_bot.2 hbot)) (G ⧸ N) N.index_eq_card.symm
          ((Subgroup.card_quotient_dvd_card N).trans hdvd)⟩

/-- **Burnside's `pᵃqᵇ` theorem**, in the form the induction runs in: a finite group whose order
divides a product of two prime powers is solvable. -/
theorem isSolvable_of_card_dvd_prime_pow_mul_prime_pow {G : Type u} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) {a b : ℕ} (h : Nat.card G ∣ p ^ a * q ^ b) : Group.IsSolvable G :=
  isSolvable_aux hp hq a b (Nat.card G) G rfl h

/-- **Burnside's `pᵃqᵇ` theorem**: a finite group of order `pᵃqᵇ`, for primes `p` and `q`, is
solvable. -/
theorem isSolvable_of_card_eq_prime_pow_mul_prime_pow {G : Type u} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) {a b : ℕ} (h : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G :=
  isSolvable_of_card_dvd_prime_pow_mul_prime_pow hp hq (by rw [h])

end Burnside

end TauCeti
