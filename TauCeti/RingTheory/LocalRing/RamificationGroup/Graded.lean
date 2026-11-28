/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Sylow
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.Algebra.Group.Action.MulDistribMulAction
import TauCeti.GroupTheory.GroupAction.Norm
import TauCeti.RingTheory.LocalRing.Monogenic

/-!
# The successive quotients of the ramification filtration of a local ring

Let a group `G` act by ring automorphisms on a local ring `S` with residue field `k`, and write
`G_i = TauCeti.IsLocalRing.ramificationGroup G S i`. This file describes the successive quotients
`G_i / G_{i+1}`, with no completeness of `S` and no finiteness of `k`.

**Positive depth, on any local ring.** For `i ≥ 1`, an element `σ ∈ G_i` satisfies
`σ ^ m x - x ≡ m (σ x - x)` modulo `𝔪 ^ (i + 2)`, because `σ - 1` raises the `𝔪`-adic order of
`𝔪 ^ (i + 1)` by `i + 1 ≥ 2`. Hence `σ ^ p ∈ G_{i+1}` when `k` has characteristic `p`, and
`σ ∈ G_{i+1}` as soon as some power `σ ^ m` with `m` invertible in `k` is. So every `G_i / G_{i+1}`
with `i ≥ 1` is a `p`-group; every `G_i` with `i ≥ 1` is a `p`-group once the filtration vanishes
at some index, as it does when the action is faithful, `S` is Noetherian and `G_0` is finite; and
in residue characteristic zero a finite `G_i` with `i ≥ 1` is trivial once the filtration meets
in the trivial group. Moreover, conjugation by `G_1` acts trivially on every `G_i / G_{i+1}`.

**A uniformizer decides the filtration.** Suppose that `G` fixes a local subring `R`, through an
algebra `R → S` with local structure map, and that the residue extension of `S` over `R` is
separable; the invariant subalgebra of `S` is such a local subring
(`TauCeti.FixedPoints.isLocalRing_subalgebra`). If `π` generates the
maximal ideal of `S`, then an element `σ ∈ G_0` lies in `G_n` exactly when `σ π ≡ π` modulo
`𝔪 ^ (n + 1)`, and over a discrete valuation ring its lower index is `v (σ π - π)`. Every residue
class is a simple root of a polynomial over `R`, and a Taylor expansion of that polynomial
transfers the congruence from `π` to the class. Without separability this fails: an element of
`G_0` can fix `π` and still act nontrivially on `S ⧸ 𝔪 ^ 2`.

**The graded embeddings over a discrete valuation ring.** Writing `σ π = π c_σ`, the residue of
`c_σ` is the **tame character** `G_0 →* kˣ`, which does not depend on the uniformizer and is
equivariant under conjugation by `G`. Writing `σ π - π = π ^ (n + 2) c_σ` for `σ ∈ G_{n+1}`, the
residue of `c_σ` gives a homomorphism `G_{n+1} →* Multiplicative k`, which depends on `π` and
transforms under conjugation by `G_0` through `tameCharacter` to the `(n + 1)`-st power. Their
kernels contain `G_1` and `G_{n+2}`, with equality for a separable residue extension, so they induce
embeddings `G_0 / G_1 → kˣ` and `G_{n+1} / G_{n+2} → k`. Consequently a finite `G_0 / G_1` is
cyclic of order prime to the residue characteristic, `G_0` is cyclic when `G_0` is finite,
the residue extension is separable, and `G_1 = ⊥`, and for a faithful action with finite `G_0` in
residue characteristic `p`, the group `G_1` is the unique Sylow `p`-subgroup of `G_0`. In residue
characteristic zero, if `G_0` is finite, the kernel of the tame character is already `G_1` without
separability, so `G_0 / G_1` embeds into `kˣ`, and if the action is also faithful then `G_0` is
cyclic.

## Main definitions

* `TauCeti.IsLocalRing.tameCharacter G S`: the tame character `G_0 →* kˣ`, and
  `TauCeti.IsLocalRing.tameCharacterGraded G S`: its factorization through `G_0 / G_1`.
* `TauCeti.IsLocalRing.ramificationGroupToResidueField hπ n`: the homomorphism
  `G_{n+1} →* Multiplicative k` in the coordinate of the uniformizer `π`, and
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField hπ n`: its factorization through
  `G_{n+1} / G_{n+2}`.
* `TauCeti.IsLocalRing.ramificationGroupOneSylow G S R p`: `G_1` as a Sylow `p`-subgroup of `G_0`.

## Main results

* `TauCeti.IsLocalRing.ramificationGroupGradedConj_of_mem_ramificationGroup_one` and
  `TauCeti.IsLocalRing.isMulCommutative_ramificationGroupGraded`: conjugation by `G_1` acts
  trivially on every successive quotient `G_i / G_{i+1}`, and every positive graded piece
  `G_i / G_{i+1}` (`0 < i`) is commutative.
* `TauCeti.IsLocalRing.pow_mem_ramificationGroup_of_charP` and
  `TauCeti.IsLocalRing.isPGroup_ramificationGroupGraded`: in residue characteristic `p`, the
  `p`-th power of an element of `G_i` lies in `G_{i+1}` for `i ≥ 1`, so `G_i / G_{i+1}` is a
  `p`-group.
* `TauCeti.IsLocalRing.isPGroup_ramificationGroup_of_eq_bot` and
  `TauCeti.IsLocalRing.isPGroup_ramificationGroup`: the groups `G_i` with `i ≥ 1` are `p`-groups
  once the filtration vanishes at some index, in particular for a faithful action on a Noetherian
  local ring with finite `G_0`.
* `TauCeti.IsLocalRing.mem_ker_toRingAut_of_mem_ramificationGroup_one_of_pow_eq_one`: over a
  Noetherian local ring, an element of `G_1` killed by a power nonzero in the residue field acts
  trivially on `S`.
* `TauCeti.IsLocalRing.ramificationGroup_eq_bot_of_charZero` and
  `TauCeti.IsLocalRing.ramificationGroup_one_eq_bot_of_charZero`: in residue characteristic zero,
  a finite `G_i` (`i > 0`) is trivial if the filtration has trivial intersection, and in particular
  `G_1 = ⊥` when the action on a Noetherian local ring is faithful and `G_1` is finite.
* `TauCeti.IsLocalRing.ramificationGroup_eq_bot_of_not_dvd_card_ramificationGroup_zero`: for a
  faithful action on a Noetherian local ring, every positive-depth `G_i` (`i > 0`) is trivial when
  the residue characteristic does not divide `#G_0`.
* `TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem`: for a separable residue
  extension, membership of `σ ∈ G_0` in `G_n` is decided at a generator of the maximal ideal, and
  `TauCeti.IsLocalRing.lowerIndex_eq_addVal_smul_sub` computes the lower index there.
* `TauCeti.IsLocalRing.coe_tameCharacter_of_smul_eq_mul`: the tame character computed at any
  uniformizer.
* `TauCeti.IsLocalRing.toAdd_ramificationGroupToResidueField_of_mul_eq`: changing the uniformizer
  from `π` to `π a` multiplies the positive-depth coordinate by the `(n + 1)`-st power of `a`.
* `TauCeti.IsLocalRing.ker_tameCharacter` and `TauCeti.IsLocalRing.tameCharacterGraded_injective`,
  `TauCeti.IsLocalRing.ker_ramificationGroupToResidueField` and
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_injective`: for a separable residue
  extension, the kernels are `G_1` and `G_{n+2}`, and the graded maps are injective.
* `TauCeti.IsLocalRing.tameCharacter_injective_iff` and
  `TauCeti.IsLocalRing.isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot`: for a
  separable residue extension, `tameCharacter` is injective if and only if `G_1 = ⊥`, and when
  `G_0` is also finite and `G_1 = ⊥`, `G_0` is cyclic.
* `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_conj`,
  `TauCeti.IsLocalRing.tameCharacter_conj`,
  `TauCeti.IsLocalRing.tameCharacter_conj_of_smul_eq_pow`,
  `TauCeti.IsLocalRing.tameCharacterGraded_ramificationGroupGradedConj`,
  `TauCeti.IsLocalRing.tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow`, and
  `TauCeti.IsLocalRing.ramificationGroupGradedConj_zero`: conjugation equivariance of the tame
  character and positive-depth residue coordinate, and triviality of inertia conjugation on
  `G_0 / G_1` under separable residue extension.
* `TauCeti.IsLocalRing.isCyclic_ramificationGroupGraded_zero`,
  `TauCeti.IsLocalRing.card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one`, and
  `TauCeti.IsLocalRing.not_dvd_index_ramificationGroup_one`: a finite `G_0 / G_1` is
  cyclic of order prime to the residue characteristic and dividing `#k - 1`.
* `TauCeti.IsLocalRing.ker_tameCharacter_of_charZero`,
  `TauCeti.IsLocalRing.tameCharacterGraded_injective_of_charZero`,
  `TauCeti.IsLocalRing.tameCharacter_injective_of_charZero`, and
  `TauCeti.IsLocalRing.isCyclic_ramificationGroup_zero_of_charZero`: in residue characteristic zero
  with finite inertia `G_0` (and without separability hypotheses), `ker tameCharacter = G_1` and
  `tameCharacterGraded` is injective, and when the action is also faithful, `tameCharacter` is
  injective and `G_0` is cyclic.
* `TauCeti.IsLocalRing.eq_ramificationGroupOneSylow`,
  `TauCeti.IsLocalRing.natCard_ramificationGroup_one`, and
  `TauCeti.IsLocalRing.ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`:
  `G_1` is the only Sylow `p`-subgroup of `G_0`, of order the `p`-part of `#G_0`, and is trivial
  exactly when `p ∤ #G_0`.
* `ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero_of_finite_residueField`
  (in `TauCeti.IsLocalRing`): the same criterion `G_1 = ⊥ ↔ ¬ p ∣ #G_0` without assuming `G_0`
  is finite, under `[Finite (ResidueField S)]`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5 to 7, 9, and the
  corollaries of Proposition 7.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, §3.1, Proposition 1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.8.5, for the Taylor-expansion form of the uniformizer criterion.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti

namespace IsLocalRing

/-! ### Positive depth over a local ring -/

section Positive

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- At positive depth the powers of `σ ∈ G_{n+1}` act to first order like multiples of `σ`:
`σ ^ m x - x ≡ m (σ x - x)` modulo `𝔪 ^ (n + 3)`. -/
private theorem smul_pow_sub_sub_nsmul_mem {n : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S (n + 1 : ℕ)) (m : ℕ) (x : S) :
    σ ^ m • x - x - m • (σ • x - x) ∈ maximalIdeal S ^ (n + 3) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hy : σ ^ m • x - x ∈ maximalIdeal S ^ (n + 1 + 1) :=
      mem_ramificationGroup_natCast_iff.mp (pow_mem hσ m) x
    have hD := smul_sub_mem_maximalIdeal_pow_of_mem_ramificationGroup hσ hy
    have hsplit : σ ^ (m + 1) • x - x - (m + 1) • (σ • x - x) =
        (σ ^ m • x - x - m • (σ • x - x)) + (σ • (σ ^ m • x - x) - (σ ^ m • x - x)) := by
      simp only [pow_succ', mul_smul, smul_sub, add_nsmul, one_nsmul]
      abel
    rw [hsplit]
    exact add_mem ih (Ideal.pow_le_pow_right (by omega) hD)

/-- A positive integer index is a successor of a natural number. -/
private theorem exists_natCast_add_one_eq {i : ℤ} (hi : 0 < i) : ∃ n : ℕ, i = (n + 1 : ℕ) :=
  ⟨(i - 1).toNat, by omega⟩

/-- **In residue characteristic `p` the `p`-th power of an element of `G_i`, `i ≥ 1`, lies in
`G_{i+1}`.** -/
theorem pow_mem_ramificationGroup_of_charP (p : ℕ) [CharP (ResidueField S) p] {i : ℤ}
    (hi : 0 < i) {σ : G} (hσ : σ ∈ ramificationGroup G S i) :
    σ ^ p ∈ ramificationGroup G S (i + 1) := by
  obtain ⟨n, rfl⟩ := exists_natCast_add_one_eq hi
  rw [(by push_cast; ring : ((n + 1 : ℕ) : ℤ) + 1 = (n + 2 : ℕ)),
    mem_ramificationGroup_natCast_iff]
  intro x
  have hp : (p : S) ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  have hpd : p • (σ • x - x) ∈ maximalIdeal S ^ (n + 3) := by
    rw [nsmul_eq_mul, pow_succ']
    exact Ideal.mul_mem_mul hp (mem_ramificationGroup_natCast_iff.mp hσ x)
  simpa using add_mem (smul_pow_sub_sub_nsmul_mem hσ p x) hpd

/-- At positive depth, `σ ∈ G_i` lies in `G_{i+1}` as soon as some power `σ ^ m` does, for an
exponent `m` that is nonzero in the residue field. -/
theorem mem_ramificationGroup_add_one_of_pow_mem {i : ℤ} (hi : 0 < i) {σ : G}
    (hσ : σ ∈ ramificationGroup G S i) {m : ℕ} (hm : (m : ResidueField S) ≠ 0)
    (hpow : σ ^ m ∈ ramificationGroup G S (i + 1)) : σ ∈ ramificationGroup G S (i + 1) := by
  obtain ⟨n, rfl⟩ := exists_natCast_add_one_eq hi
  rw [(by push_cast; ring : ((n + 1 : ℕ) : ℤ) + 1 = (n + 2 : ℕ)),
    mem_ramificationGroup_natCast_iff] at hpow ⊢
  intro x
  have hu : IsUnit (m : S) := by
    rwa [← residue_ne_zero_iff_isUnit, map_natCast]
  refine (Ideal.unit_mul_mem_iff_mem _ hu).mp ?_
  rw [← nsmul_eq_mul]
  simpa using sub_mem (hpow x) (smul_pow_sub_sub_nsmul_mem hσ m x)

/-- **In residue characteristic `p` the positive-depth graded pieces `G_i / G_{i+1}` are
`p`-groups**: every element has order dividing `p`, by
`TauCeti.IsLocalRing.pow_mem_ramificationGroup_of_charP`. -/
theorem isPGroup_ramificationGroupGraded (p : ℕ) [CharP (ResidueField S) p] {i : ℤ}
    (hi : 0 < i) : IsPGroup p (RamificationGroupGraded G S i) := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H σ =>
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact pow_mem_ramificationGroup_of_charP p hi σ.property

/-- **The positive-depth ramification groups are `p`-groups** once the filtration vanishes at some
index `N`, for `p` the residue characteristic: the `p ^ k`-th power of an element of `G_i` lies in
`G_{i+k}`. -/
theorem isPGroup_ramificationGroup_of_eq_bot (p : ℕ) [CharP (ResidueField S) p] {i N : ℤ}
    (hi : 0 < i) (hN : ramificationGroup G S N = ⊥) : IsPGroup p (ramificationGroup G S i) := by
  intro σ
  have hpow : ∀ k : ℕ, (σ : G) ^ p ^ k ∈ ramificationGroup G S (i + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, Nat.cast_succ, ← add_assoc]
      exact pow_mem_ramificationGroup_of_charP p (by omega) ih
  refine ⟨(N - i).toNat, Subtype.ext ?_⟩
  have h := ramificationGroup_antitone G S (by omega : N ≤ i + (N - i).toNat) (hpow (N - i).toNat)
  rw [hN, Subgroup.mem_bot] at h
  simpa using h

/-- An element of `G_i` (`0 < i`) whose `m`-th power is `1`, for an `m` nonzero in the residue
field, lies in every ramification group `G_j`. -/
private theorem mem_iInf_ramificationGroup_of_pow_eq_one {i : ℤ} (hi : 0 < i) {σ : G}
    (hσ : σ ∈ ramificationGroup G S i) {m : ℕ} (hm : (m : ResidueField S) ≠ 0)
    (hpow : σ ^ m = 1) : σ ∈ ⨅ j, ramificationGroup G S j := by
  have hstep : ∀ k : ℕ, σ ∈ ramificationGroup G S (i + k) := by
    intro k
    induction k with
    | zero => simpa using hσ
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact mem_ramificationGroup_add_one_of_pow_mem (by omega) ih hm (hpow ▸ one_mem _)
  rw [Subgroup.mem_iInf]
  intro j
  exact ramificationGroup_antitone G S (by omega : j ≤ i + (j - i).toNat) (hstep (j - i).toNat)

/-- **In residue characteristic zero a finite positive-depth ramification group is trivial** if
the filtration has trivial intersection: a finite `G_i` with `i > 0` lies in every `G_j`. -/
theorem ramificationGroup_eq_bot_of_charZero [CharZero (ResidueField S)] {i : ℤ} (hi : 0 < i)
    [Finite (ramificationGroup G S i)] (hbot : ⨅ j, ramificationGroup G S j = ⊥) :
    ramificationGroup G S i = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  have hm : 0 < orderOf σ := by
    rw [← Subgroup.orderOf_mk σ hσ]
    exact orderOf_pos _
  rw [← hbot]
  exact mem_iInf_ramificationGroup_of_pow_eq_one hi hσ (Nat.cast_ne_zero.mpr hm.ne')
    (pow_orderOf_eq_one σ)

section

variable (G S) [IsNoetherianRing S] [FaithfulSMul G S]

/-- **The positive-depth ramification groups are `p`-groups**, for `p` the residue characteristic,
when the action on the Noetherian local ring `S` is faithful and `G_0` is finite. In particular the
first ramification group `G_1` is a `p`-group. -/
theorem isPGroup_ramificationGroup (p : ℕ) [CharP (ResidueField S) p]
    [Finite (ramificationGroup G S 0)] {i : ℤ} (hi : 0 < i) :
    IsPGroup p (ramificationGroup G S i) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G S
  exact isPGroup_ramificationGroup_of_eq_bot p hi (hN N le_rfl)

/-- **Positive-depth vanishing in the tame case**: when `G` acts faithfully on a Noetherian local
ring `S` and the residue characteristic `p` does not divide `#G_0` (which forces `G_0` to be
finite), every positive-depth ramification group `G_i` (`i > 0`) is trivial. -/
theorem ramificationGroup_eq_bot_of_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [CharP (ResidueField S) p] {i : ℤ} (hi : 0 < i)
    (hp : ¬ p ∣ Nat.card (ramificationGroup G S 0)) :
    ramificationGroup G S i = ⊥ := by
  have : Finite (ramificationGroup G S 0) := by
    by_contra hinf
    have := not_finite_iff_infinite.mp hinf
    rw [Nat.card_eq_zero_of_infinite] at hp
    exact hp (dvd_zero p)
  have : Finite (ramificationGroup G S i) := finite_ramificationGroup_of_le G S hi.le
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    rcases (isPGroup_ramificationGroup G S p hi).card_eq_or_dvd with hcard | hpdvd
    · exact Subgroup.card_eq_one.mp hcard
    · exact (hp (hpdvd.trans (Subgroup.card_dvd_of_le (ramificationGroup_antitone G S hi.le)))).elim
  · have : CharZero (ResidueField S) := CharP.charP_to_charZero (ResidueField S)
    exact ramificationGroup_eq_bot_of_charZero hi (iInf_ramificationGroup_eq_bot G S)

end

end Positive

section HigherRamification

open scoped commutatorElement

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- Conjugation by wild inertia `G_1` acts trivially on every successive quotient
`G_i / G_{i+1}`. -/
@[simp]
theorem ramificationGroupGradedConj_of_mem_ramificationGroup_one (i : ℤ)
    (σ : ramificationGroup G S 1) (τ : RamificationGroupGraded G S i) :
    ramificationGroupGradedConj G S (σ : G) i τ = τ := by
  induction τ using QuotientGroup.induction_on with
  | _ x =>
    rw [ramificationGroupGradedConj_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hcomm : (((MulAut.conjNormal (σ : G) x)⁻¹ * x : ramificationGroup G S i) : G) =
        ⁅(σ : G), (x : G)⁻¹⁆ := by
      simp [commutatorElement_def, MulAut.conjNormal_apply, mul_assoc]
    rw [hcomm, add_comm i 1]
    exact commutator_ramificationGroup_le G S 1 i
      (Subgroup.commutator_mem_commutator σ.property (inv_mem x.property))

/-- Each positive graded piece `G_i / G_{i+1}` (`0 < i`) is commutative. -/
theorem isMulCommutative_ramificationGroupGraded {i : ℤ} (hi : 0 < i) :
    IsMulCommutative (RamificationGroupGraded G S i) := by
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, Subgroup.subgroupOf,
    ← Subgroup.map_le_iff_le_comap, Subgroup.map_subtype_commutator]
  exact (commutator_ramificationGroup_le G S i i).trans
    (ramificationGroup_antitone G S (by omega : i + 1 ≤ i + i))

/-- Each positive graded piece `G_{n+1} / G_{n+2}` (`n : ℕ`) is commutative. -/
instance instIsMulCommutativeRamificationGroupGradedNatCastSucc {n : ℕ} :
    IsMulCommutative (RamificationGroupGraded G S ((n : ℤ) + 1)) :=
  isMulCommutative_ramificationGroupGraded (by omega)

/-- Over a Noetherian local ring, every element of `G_1` whose order is nonzero in
`ResidueField S` acts trivially on `S`. -/
theorem mem_ker_toRingAut_of_mem_ramificationGroup_one_of_pow_eq_one
    [IsNoetherianRing S] {σ : G} (hσ : σ ∈ ramificationGroup G S 1) {m : ℕ}
    (hm : (m : ResidueField S) ≠ 0) (hpow : σ ^ m = 1) :
    σ ∈ MonoidHom.ker (MulSemiringAction.toRingAut G S) := by
  rw [← iInf_ramificationGroup_eq_ker]
  exact mem_iInf_ramificationGroup_of_pow_eq_one zero_lt_one hσ hm hpow

variable (G S) in
/-- Over a Noetherian local ring with residue field of characteristic zero, faithful action, and
finite wild inertia group `G_1`, the wild inertia group `G_1` is trivial. -/
theorem ramificationGroup_one_eq_bot_of_charZero
    [IsNoetherianRing S] [FaithfulSMul G S] [CharZero (ResidueField S)]
    [Finite (ramificationGroup G S 1)] :
    ramificationGroup G S 1 = ⊥ :=
  ramificationGroup_eq_bot_of_charZero zero_lt_one (iInf_ramificationGroup_eq_bot G S)

end HigherRamification

/-! ### The uniformizer criterion for a separable residue extension -/

section Separable

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
variable (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)]
  [SMulCommClass G R S] [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
include R

/-- The inductive step of the uniformizer criterion: an element of `G_n` that moves a generator of
the maximal ideal by an element of `𝔪 ^ (n + 2)` lies in `G_{n+1}`. The residue class of `x` is a
simple root of the reduction of some `g : R[X]`; Taylor expansion of `g` at `x` reads
`σ (g x) - g x ≡ g' x (σ x - x)` modulo `𝔪 ^ (n + 2)`, and `g x` is a multiple of the generator. -/
private theorem mem_ramificationGroup_succ_of_smul_sub_mem {π : S}
    (hπ : maximalIdeal S = Ideal.span {π}) {n : ℕ} {σ : G} (hσ : σ ∈ ramificationGroup G S n)
    (hσπ : σ • π - π ∈ maximalIdeal S ^ (n + 2)) : σ ∈ ramificationGroup G S (n + 1 : ℕ) := by
  rw [mem_ramificationGroup_natCast_iff] at hσ ⊢
  intro x
  obtain ⟨g, hval, hder⟩ := exists_aeval_mem_maximalIdeal_isUnit_aeval_derivative (R := R) x
  -- Taylor expansion of `g` at `x` in the direction `d = σ x - x`.
  obtain ⟨c, hc⟩ := binomExpansion (g.map (algebraMap R S)) x (σ • x - x)
  rw [add_sub_cancel, derivative_map] at hc
  simp only [eval_map, ← aeval_def, aeval_smul] at hc
  -- The left side `σ (g x) - g x` lies in `𝔪 ^ (n + 2)`, since `g x` is a multiple of `π`.
  obtain ⟨y, hy⟩ : π ∣ aeval x g := Ideal.mem_span_singleton.mp (hπ ▸ hval)
  have h₁ : σ • aeval x g - aeval x g ∈ maximalIdeal S ^ (n + 2) := by
    rw [hy, smul_mul',
      (by ring : σ • π * σ • y - π * y = (σ • π - π) * σ • y + π * (σ • y - y))]
    refine add_mem (Ideal.mul_mem_right _ _ hσπ) ?_
    rw [pow_succ']
    exact Ideal.mul_mem_mul (hπ ▸ Ideal.mem_span_singleton_self π) (hσ y)
  have h₂ : c * (σ • x - x) ^ 2 ∈ maximalIdeal S ^ (n + 2) := by
    refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega : n + 2 ≤ (n + 1) * 2) ?_)
    rw [pow_mul]
    exact Ideal.pow_mem_pow (hσ x) 2
  refine (Ideal.unit_mul_mem_iff_mem _ hder).mp ?_
  rw [(by rw [hc]; ring : aeval x (derivative g) * (σ • x - x) =
    (σ • aeval x g - aeval x g) - c * (σ • x - x) ^ 2)]
  exact sub_mem h₁ h₂

/-- **The uniformizer criterion.** If the residue extension of `S` over a local ring `R` fixed by
`G` is separable and `π` generates the maximal ideal of `S`, then an element `σ` of `G_0` lies in
`G_n` exactly when `σ π ≡ π` modulo `𝔪 ^ (n + 1)`. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem {π : S}
    (hπ : maximalIdeal S = Ideal.span {π}) {σ : G} (hσ : σ ∈ ramificationGroup G S 0) {n : ℕ} :
    σ ∈ ramificationGroup G S n ↔ σ • π - π ∈ maximalIdeal S ^ (n + 1) := by
  refine ⟨fun h ↦ mem_ramificationGroup_natCast_iff.mp h π, fun h ↦ ?_⟩
  induction n with
  | zero => simpa using hσ
  | succ n ih =>
    exact mem_ramificationGroup_succ_of_smul_sub_mem R hπ
      (ih (Ideal.pow_le_pow_right (by omega) h)) h

end Separable

section DiscreteValuationRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [MulSemiringAction G S]

/-! ### The lower index at a uniformizer -/

/-- For a separable residue extension, the lower index of an element of `G_0` acting on a discrete
valuation ring is read at a uniformizer: `i_G(σ) = v (σ π - π)`. -/
theorem lowerIndex_eq_addVal_smul_sub (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {π : S} (hπ : Irreducible π) {σ : G}
    (hσ : σ ∈ ramificationGroup G S 0) :
    lowerIndex S σ = IsDiscreteValuationRing.addVal S (σ • π - π) := by
  refine (lowerIndex_le_addVal σ π).antisymm (ENat.forall_natCast_le_iff_le.mp fun m hm ↦ ?_)
  rw [natCast_le_lowerIndex_iff_mem_ramificationGroup]
  cases m with
  | zero => simp [ramificationGroup_eq_top_of_le_neg_one]
  | succ m =>
    rw [(by push_cast; ring : ((m + 1 : ℕ) : ℤ) - 1 = m),
      mem_ramificationGroup_natCast_iff_smul_sub_mem R hπ.maximalIdeal_eq hσ,
      TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]
    exact hm

/-! ### The tame character -/

/-- Every element of `G` carries a uniformizer to a multiple of it. -/
private theorem dvd_smul_of_irreducible {π : S} (hπ : Irreducible π) (σ : G) : π ∣ σ • π := by
  rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq, ← pow_one (maximalIdeal S),
    smul_mem_maximalIdeal_pow_iff, pow_one, hπ.maximalIdeal_eq]
  exact Ideal.mem_span_singleton_self π

/-- If `σ π = π c` for a uniformizer `π`, then `c` is a unit. -/
private theorem residue_ne_zero_of_smul_eq_mul {π c : S} (hπ : Irreducible π) {σ : G}
    (hc : σ • π = π * c) : residue S c ≠ 0 := by
  rw [residue_ne_zero_iff_isUnit]
  by_contra h
  -- Otherwise `σ π ∈ 𝔪 ^ 2`, hence `π ∈ 𝔪 ^ 2`, against `v π = 1`.
  have hπ2 : σ • π ∈ maximalIdeal S ^ 2 := by
    rw [hc, pow_two]
    exact Ideal.mul_mem_mul ((mem_maximalIdeal π).mpr hπ.not_isUnit) ((mem_maximalIdeal c).mpr h)
  rw [smul_mem_maximalIdeal_pow_iff,
    TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal,
    IsDiscreteValuationRing.addVal_uniformizer hπ] at hπ2
  norm_num at hπ2

/-- For `σ ∈ G_0`, the residue of the factor `c` with `σ π = π c` does not depend on the
uniformizer `π`. -/
private theorem residue_eq_of_smul_eq_mul {σ : G} (hσ : σ ∈ ramificationGroup G S 0)
    {π π' c c' : S} (hπ : Irreducible π) (hπ' : Irreducible π') (hc : σ • π = π * c)
    (hc' : σ • π' = π' * c') : residue S c = residue S c' := by
  obtain ⟨v, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible S hπ hπ'
  have h : π * (c * σ • (v : S)) = π * ((v : S) * c') := by
    calc π * (c * σ • (v : S)) = σ • π * σ • (v : S) := by rw [hc]; ring
      _ = π * v * c' := by rw [← smul_mul', hc']
      _ = π * ((v : S) * c') := by ring
  have h' := congrArg (residue S) (mul_left_cancel₀ hπ.ne_zero h)
  rw [map_mul, map_mul, residue_smul_eq_of_mem_ramificationGroup_zero G S hσ,
    mul_comm (residue S (v : S))] at h'
  exact mul_right_cancel₀ ((residue_ne_zero_iff_isUnit _).mpr v.isUnit) h'

/-- The unit `c` with `σ π = π c`, for a fixed uniformizer `π` of `S`. -/
private noncomputable def smulDivUniformizer (σ : G) : S :=
  (dvd_smul_of_irreducible (IsDiscreteValuationRing.exists_irreducible S).choose_spec σ).choose

private theorem smul_eq_mul_smulDivUniformizer (σ : G) :
    σ • (IsDiscreteValuationRing.exists_irreducible S).choose =
      (IsDiscreteValuationRing.exists_irreducible S).choose * smulDivUniformizer σ :=
  (dvd_smul_of_irreducible (IsDiscreteValuationRing.exists_irreducible S).choose_spec σ).choose_spec

variable (G S) in
/-- The **tame character** `G_0 →* kˣ` of a group acting on a discrete valuation ring: it sends
`σ` to the residue of the unit `c` with `σ π = π c`, for any uniformizer `π`
(`TauCeti.IsLocalRing.coe_tameCharacter_of_smul_eq_mul`). Its kernel contains `G_1`, with
equality for a separable residue extension (`TauCeti.IsLocalRing.ker_tameCharacter`). -/
noncomputable def tameCharacter : ramificationGroup G S 0 →* (ResidueField S)ˣ :=
  MonoidHom.mk'
    (fun σ ↦ Units.mk0 (residue S (smulDivUniformizer (σ : G)))
      (residue_ne_zero_of_smul_eq_mul (IsDiscreteValuationRing.exists_irreducible S).choose_spec
        (smul_eq_mul_smulDivUniformizer _)))
    (fun σ τ ↦ by
      have hπ := (IsDiscreteValuationRing.exists_irreducible S).choose_spec
      set π := (IsDiscreteValuationRing.exists_irreducible S).choose
      -- `σ τ π = σ (π c_τ) = π c_σ σ c_τ`, and `σ c_τ ≡ c_τ` modulo `𝔪`.
      have h : ((σ * τ : ramificationGroup G S 0) : G) • π =
          π * (smulDivUniformizer (σ : G) * (σ : G) • smulDivUniformizer (τ : G)) := by
        rw [Subgroup.coe_mul, mul_smul, smul_eq_mul_smulDivUniformizer (τ : G), smul_mul',
          smul_eq_mul_smulDivUniformizer (σ : G), mul_assoc]
      ext
      simp only [Units.val_mk0, Units.val_mul]
      rw [residue_eq_of_smul_eq_mul (σ * τ).property hπ hπ (smul_eq_mul_smulDivUniformizer _) h,
        map_mul, residue_smul_eq_of_mem_ramificationGroup_zero G S σ.property])

/-- **The tame character at a uniformizer**: if `σ π = π c` for a uniformizer `π`, then the tame
character of `σ` is the residue of `c`. In particular it does not depend on the uniformizer. -/
theorem coe_tameCharacter_of_smul_eq_mul {π c : S} (hπ : Irreducible π)
    {σ : ramificationGroup G S 0} (hc : (σ : G) • π = π * c) :
    (tameCharacter G S σ : ResidueField S) = residue S c :=
  residue_eq_of_smul_eq_mul σ.property (IsDiscreteValuationRing.exists_irreducible S).choose_spec hπ
    (smul_eq_mul_smulDivUniformizer _) hc

/-- The tame character of `σ` is trivial exactly when `σ π ≡ π` modulo `𝔪 ^ 2`, for any
uniformizer `π`. -/
theorem tameCharacter_eq_one_iff_smul_sub_mem {π : S} (hπ : Irreducible π)
    {σ : ramificationGroup G S 0} :
    tameCharacter G S σ = 1 ↔ (σ : G) • π - π ∈ maximalIdeal S ^ 2 := by
  obtain ⟨c, hc⟩ := dvd_smul_of_irreducible hπ (σ : G)
  rw [Units.ext_iff, coe_tameCharacter_of_smul_eq_mul hπ hc, Units.val_one, ← sub_eq_zero,
    ← map_one (residue S), ← map_sub, residue_eq_zero_iff, hc,
    (by ring : π * c - π = (c - 1) * π ^ 1)]
  refine ⟨fun h ↦ ?_, fun h ↦
    TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_of_mul_pow_mem_maximalIdeal_pow_succ hπ h⟩
  rw [pow_two, pow_one]
  exact Ideal.mul_mem_mul h ((mem_maximalIdeal π).mpr hπ.not_isUnit)

/-- The tame character is trivial on the first ramification group. -/
theorem ramificationGroup_one_subgroupOf_le_ker_tameCharacter :
    (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) ≤ (tameCharacter G S).ker := by
  intro σ hσ
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  rw [MonoidHom.mem_ker, tameCharacter_eq_one_iff_smul_sub_mem hπ]
  exact (mem_ramificationGroup_natCast_iff (n := 1)).mp hσ π

/-- **The kernel of the tame character is `G_1`**, viewed inside `G_0`, when the residue extension
over a local ring `R` fixed by `G` is separable. -/
theorem ker_tameCharacter (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    (tameCharacter G S).ker = (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) := by
  refine le_antisymm (fun σ hσ ↦ ?_) ramificationGroup_one_subgroupOf_le_ker_tameCharacter
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  rw [MonoidHom.mem_ker, tameCharacter_eq_one_iff_smul_sub_mem hπ] at hσ
  exact (mem_ramificationGroup_natCast_iff_smul_sub_mem R hπ.maximalIdeal_eq σ.property
    (n := 1)).mpr hσ

variable (G S) in
/-- The tame character on the tame quotient `G_0 / G_1`. -/
noncomputable def tameCharacterGraded : RamificationGroupGraded G S 0 →* (ResidueField S)ˣ :=
  QuotientGroup.lift _ (tameCharacter G S) (by
    rw [zero_add]
    exact ramificationGroup_one_subgroupOf_le_ker_tameCharacter)

@[simp]
theorem tameCharacterGraded_mk (σ : ramificationGroup G S 0) :
    tameCharacterGraded G S (σ : RamificationGroupGraded G S 0) = tameCharacter G S σ :=
  (rfl)

/-- For a separable residue extension, the tame character embeds `G_0 / G_1` into `kˣ`. -/
theorem tameCharacterGraded_injective (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    Function.Injective (tameCharacterGraded G S) := by
  unfold tameCharacterGraded
  rw [QuotientGroup.injective_lift_iff, zero_add]
  exact (ker_tameCharacter R).symm

/-- **The tame quotient is cyclic**: a finite `G_0 / G_1` embeds into the multiplicative group of
the residue field, when the residue extension is separable. -/
theorem isCyclic_ramificationGroupGraded_zero (R : Type*) [CommRing R] [IsLocalRing R]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    [Finite (RamificationGroupGraded G S 0)] :
    IsCyclic (RamificationGroupGraded G S 0) :=
  isCyclic_of_injective_ringHom ((Units.coeHom _).comp (tameCharacterGraded G S))
    (Units.val_injective.comp (tameCharacterGraded_injective R))

variable (G S) in
/-- Under a separable residue extension, the tame character `G_0 →* (ResidueField S)ˣ` is
injective if and only if wild inertia `G_1` is trivial. -/
theorem tameCharacter_injective_iff (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] :
    Function.Injective (tameCharacter G S) ↔ ramificationGroup G S 1 = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_tameCharacter R, Subgroup.subgroupOf_eq_bot, disjoint_iff,
    inf_of_le_left (ramificationGroup_antitone G S zero_le_one)]

variable (G S) in
/-- When `G_0` is finite, the residue extension is separable, and wild inertia `G_1` is trivial,
inertia `G_0` is cyclic. -/
theorem isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot (R : Type*) [CommRing R]
    [IsLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    [Finite (ramificationGroup G S 0)] (h : ramificationGroup G S 1 = ⊥) :
    IsCyclic (ramificationGroup G S 0) :=
  isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField S)).comp (tameCharacter G S))
    (Units.val_injective.comp ((tameCharacter_injective_iff G S R).mpr h))

/-- **The order of the tame quotient is prime to the residue characteristic**: the index of
`G_1` in `G_0` is not divisible by `p` when `G_0 / G_1` is finite and the residue extension is
separable. The quotient embeds into `kˣ`, which has no element of order `p` when `k` has
characteristic `p`, and for `p = 0` the statement is the nonvanishing of the index. -/
theorem not_dvd_index_ramificationGroup_one (R : Type*) [CommRing R] [IsLocalRing R]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    [Finite (RamificationGroupGraded G S 0)] (p : ℕ) [CharP (ResidueField S) p] :
    ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index := by
  rw [Subgroup.index, ← zero_add (1 : ℤ)]
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := RamificationGroupGraded G S 0) p hdvd
    -- The image of `x` would be a primitive `p`-th root of unity in characteristic `p`.
    have hord : orderOf ((tameCharacterGraded G S x : (ResidueField S)ˣ) : ResidueField S) = p := by
      rw [orderOf_units, orderOf_injective _ (tameCharacterGraded_injective R) x, hx]
    have : NeZero p := ⟨hp.ne_zero⟩
    exact (hord ▸ IsPrimitiveRoot.orderOf _).neZero'.out (CharP.cast_eq_zero _ p)
  · rw [zero_dvd_iff]
    exact Nat.card_pos.ne'

/-! ### The positive-depth graded embeddings -/

/-- An element of `G_{n+1}` moves a uniformizer `π` by a multiple of `π ^ (n + 2)`. -/
private theorem pow_dvd_smul_sub {π : S} (hπ : Irreducible π) {n : ℕ}
    (σ : ramificationGroup G S ((n : ℤ) + 1)) : π ^ (n + 2) ∣ (σ : G) • π - π := by
  have h := mem_ramificationGroup_iff.mp σ.property π
  rwa [(by omega : ((n : ℤ) + 1 + 1).toNat = n + 2), hπ.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h

omit [IsDiscreteValuationRing S] in
/-- The factor `c` with `σ π - π = π ^ (n + 2) c` is unique. -/
private theorem eq_of_smul_sub_eq_pow_mul {π : S} (hπ : Irreducible π) {n : ℕ} {σ : G} {c c' : S}
    (hc : σ • π - π = π ^ (n + 2) * c) (hc' : σ • π - π = π ^ (n + 2) * c') : c = c' :=
  mul_left_cancel₀ (pow_ne_zero _ hπ.ne_zero) (hc.symm.trans hc')

/-- The homomorphism `G_{n+1} →* Multiplicative k` in the coordinate of the uniformizer `π`: it
sends `σ` to the residue of the `c` with `σ π - π = π ^ (n + 2) c`
(`TauCeti.IsLocalRing.ramificationGroupToResidueField_apply_of_smul_sub_eq`). Its kernel contains
`G_{n+2}`, with equality for a separable residue extension
(`TauCeti.IsLocalRing.ker_ramificationGroupToResidueField`). -/
noncomputable def ramificationGroupToResidueField {π : S} (hπ : Irreducible π) (n : ℕ) :
    ramificationGroup G S ((n : ℤ) + 1) →* Multiplicative (ResidueField S) :=
  MonoidHom.mk' (fun σ ↦ Multiplicative.ofAdd (residue S (pow_dvd_smul_sub hπ σ).choose))
    (fun σ τ ↦ by
      -- `σ τ π - π = σ (π ^ (n + 2) c_τ) + π ^ (n + 2) c_σ`, and `σ - 1` moves
      -- `π ^ (n + 2) c_τ` into `𝔪 ^ (n + 3)`.
      have hcσ := (pow_dvd_smul_sub hπ σ).choose_spec
      have hcτ := (pow_dvd_smul_sub hπ τ).choose_spec
      have hcστ := (pow_dvd_smul_sub hπ (σ * τ)).choose_spec
      set cσ := (pow_dvd_smul_sub hπ σ).choose
      set cτ := (pow_dvd_smul_sub hπ τ).choose
      have hσ : (σ : G) ∈ ramificationGroup G S (n + 1 : ℕ) := by exact_mod_cast σ.property
      have hy : π ^ (n + 2) * cτ ∈ maximalIdeal S ^ (n + 1 + 1) := by
        rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      obtain ⟨e, he⟩ : π ^ (n + 3) ∣ (σ : G) • (π ^ (n + 2) * cτ) - π ^ (n + 2) * cτ := by
        rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
        exact Ideal.pow_le_pow_right (by omega)
          (smul_sub_mem_maximalIdeal_pow_of_mem_ramificationGroup hσ hy)
      have h : ((σ * τ : ramificationGroup G S ((n : ℤ) + 1)) : G) • π - π =
          π ^ (n + 2) * (cσ + cτ + π * e) := by
        rw [Subgroup.coe_mul, mul_smul, ← sub_add_cancel ((τ : G) • π) π, hcτ, smul_add,
          ← sub_add_cancel ((σ : G) • (π ^ (n + 2) * cτ)) (π ^ (n + 2) * cτ), he,
          ← sub_add_cancel ((σ : G) • π) π, hcσ]
        ring
      have hπ0 : residue S π = 0 :=
        (residue_eq_zero_iff π).mpr ((mem_maximalIdeal π).mpr hπ.not_isUnit)
      rw [eq_of_smul_sub_eq_pow_mul hπ hcστ h, (residue S).map_add, (residue S).map_add,
        (residue S).map_mul, hπ0, zero_mul, add_zero, ofAdd_add])

/-- The positive-depth homomorphism at an element `σ` with `σ π - π = π ^ (n + 2) c` is the residue
of `c`. -/
theorem ramificationGroupToResidueField_apply_of_smul_sub_eq {π : S} (hπ : Irreducible π) {n : ℕ}
    {σ : ramificationGroup G S ((n : ℤ) + 1)} {c : S} (hc : (σ : G) • π - π = π ^ (n + 2) * c) :
    ramificationGroupToResidueField hπ n σ = Multiplicative.ofAdd (residue S c) := by
  rw [ramificationGroupToResidueField, MonoidHom.mk'_apply,
    eq_of_smul_sub_eq_pow_mul hπ (pow_dvd_smul_sub hπ σ).choose_spec hc]

/-- The positive-depth homomorphism at `σ` is trivial exactly when `σ π ≡ π` modulo
`𝔪 ^ (n + 3)`. -/
theorem ramificationGroupToResidueField_eq_one_iff {π : S} (hπ : Irreducible π) {n : ℕ}
    {σ : ramificationGroup G S ((n : ℤ) + 1)} :
    ramificationGroupToResidueField hπ n σ = 1 ↔ (σ : G) • π - π ∈ maximalIdeal S ^ (n + 3) := by
  obtain ⟨c, hc⟩ := pow_dvd_smul_sub hπ σ
  rw [ramificationGroupToResidueField_apply_of_smul_sub_eq hπ hc, ← ofAdd_zero,
    Multiplicative.ofAdd.apply_eq_iff_eq, residue_eq_zero_iff, hc, mul_comm]
  refine ⟨fun h ↦ ?_, fun h ↦
    TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_of_mul_pow_mem_maximalIdeal_pow_succ hπ h⟩
  rw [pow_succ']
  exact Ideal.mul_mem_mul h (Ideal.pow_mem_pow ((mem_maximalIdeal π).mpr hπ.not_isUnit) _)

/-- **Changing the uniformizer** in the positive-depth homomorphism: if `π' = π a`, then the
coordinate of `σ` at `π` is `a ^ (n + 1)` times its coordinate at `π'`, modulo `𝔪`. -/
theorem toAdd_ramificationGroupToResidueField_of_mul_eq {π π' a : S} (hπ : Irreducible π)
    (hπ' : Irreducible π') (ha : π * a = π') {n : ℕ} (σ : ramificationGroup G S ((n : ℤ) + 1)) :
    (ramificationGroupToResidueField hπ n σ).toAdd =
      residue S a ^ (n + 1) * (ramificationGroupToResidueField hπ' n σ).toAdd := by
  obtain ⟨c, hc⟩ := pow_dvd_smul_sub hπ σ
  obtain ⟨a', ha'⟩ := ((hπ'.isUnit_or_isUnit ha.symm).resolve_left hπ.not_isUnit).exists_right_inv
  obtain ⟨b, hb⟩ : π ^ (n + 2) ∣ (σ : G) • a - a := by
    have h := mem_ramificationGroup_iff.mp σ.property a
    rwa [(by omega : ((n : ℤ) + 1 + 1).toNat = n + 2), hπ.maximalIdeal_eq,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  -- `σ π' - π' = π' ^ (n + 2) a' ^ (n + 2) (π b + c a + c π ^ (n + 2) b)`, with `a a' = 1`.
  have hpow : (a * a') ^ (n + 2) = 1 := by rw [ha', one_pow]
  have hc' : (σ : G) • π' - π' =
      π' ^ (n + 2) * (a' ^ (n + 2) * (π * b + c * a + c * π ^ (n + 2) * b)) := by
    rw [← ha, smul_mul']
    linear_combination (σ : G) • a * hc + (π + π ^ (n + 2) * c) * hb -
      π ^ (n + 2) * (π * b + c * a + c * π ^ (n + 2) * b) * hpow
  have hπ0 : residue S π = 0 :=
    (residue_eq_zero_iff π).mpr ((mem_maximalIdeal π).mpr hπ.not_isUnit)
  have hres : (residue S a * residue S a') ^ (n + 2) = 1 := by
    rw [← map_mul, ha', map_one, one_pow]
  rw [ramificationGroupToResidueField_apply_of_smul_sub_eq hπ hc,
    ramificationGroupToResidueField_apply_of_smul_sub_eq hπ' hc', toAdd_ofAdd, toAdd_ofAdd]
  simp only [map_mul, map_add, map_pow, hπ0, zero_mul, zero_add, ne_eq, add_eq_zero,
    OfNat.ofNat_ne_zero, and_false, not_false_eq_true, zero_pow, mul_zero, add_zero]
  linear_combination (-residue S c) * hres

/-- The positive-depth homomorphism is trivial on `G_{n+2}`. -/
theorem ramificationGroup_add_one_subgroupOf_le_ker_ramificationGroupToResidueField {π : S}
    (hπ : Irreducible π) (n : ℕ) :
    (ramificationGroup G S ((n : ℤ) + 1 + 1)).subgroupOf (ramificationGroup G S ((n : ℤ) + 1)) ≤
      (ramificationGroupToResidueField hπ n).ker := by
  intro σ hσ
  rw [MonoidHom.mem_ker, ramificationGroupToResidueField_eq_one_iff hπ]
  have h := mem_ramificationGroup_iff.mp hσ π
  rwa [(by omega : ((n : ℤ) + 1 + 1 + 1).toNat = n + 3)] at h

/-- **The kernel of the positive-depth homomorphism is `G_{n+2}`**, viewed inside `G_{n+1}`, when
the residue extension over a local ring `R` fixed by `G` is separable. -/
theorem ker_ramificationGroupToResidueField (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {π : S} (hπ : Irreducible π)
    (n : ℕ) :
    (ramificationGroupToResidueField hπ n).ker =
      (ramificationGroup G S ((n : ℤ) + 1 + 1)).subgroupOf
        (ramificationGroup G S ((n : ℤ) + 1)) := by
  refine le_antisymm (fun σ hσ ↦ ?_)
    (ramificationGroup_add_one_subgroupOf_le_ker_ramificationGroupToResidueField hπ n)
  rw [MonoidHom.mem_ker, ramificationGroupToResidueField_eq_one_iff hπ] at hσ
  rw [Subgroup.mem_subgroupOf, (by push_cast; ring : (n : ℤ) + 1 + 1 = (n + 2 : ℕ)),
    mem_ramificationGroup_natCast_iff_smul_sub_mem R hπ.maximalIdeal_eq
      (ramificationGroup_antitone G S (by omega) σ.property)]
  exact hσ

/-- The positive-depth homomorphism on the graded piece `G_{n+1} / G_{n+2}`. -/
noncomputable def ramificationGroupGradedToResidueField {π : S} (hπ : Irreducible π) (n : ℕ) :
    RamificationGroupGraded G S ((n : ℤ) + 1) →* Multiplicative (ResidueField S) :=
  QuotientGroup.lift _ (ramificationGroupToResidueField hπ n)
    (ramificationGroup_add_one_subgroupOf_le_ker_ramificationGroupToResidueField hπ n)

@[simp]
theorem ramificationGroupGradedToResidueField_mk {π : S} (hπ : Irreducible π) (n : ℕ)
    (σ : ramificationGroup G S ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField hπ n (σ : RamificationGroupGraded G S ((n : ℤ) + 1)) =
      ramificationGroupToResidueField hπ n σ :=
  (rfl)

/-- For a separable residue extension, the positive-depth graded piece `G_{n+1} / G_{n+2}` embeds
into the additive group of the residue field. -/
theorem ramificationGroupGradedToResidueField_injective (R : Type*) [CommRing R] [IsLocalRing R]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {π : S} (hπ : Irreducible π)
    (n : ℕ) : Function.Injective (ramificationGroupGradedToResidueField (G := G) hπ n) := by
  unfold ramificationGroupGradedToResidueField
  rw [QuotientGroup.injective_lift_iff]
  exact (ker_ramificationGroupToResidueField R hπ n).symm

/-! ### Conjugation action on graded quotients and the tame character -/

variable (G) in
/-- **The conjugation action formula on positive ramification quotients.** In the residue
coordinate `ramificationGroupGradedToResidueField` determined by `ϖ`, conjugation by `σ ∈ G_0` acts
on `G_{n+1} / G_{n+2}` as multiplication by `theta_0(σ) ^ (n + 1)`, where `theta_0` is
`tameCharacter`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S 0) (τ : RamificationGroupGraded G S ((n : ℤ) + 1)) :
    (ramificationGroupGradedToResidueField hϖ n
        (ramificationGroupGradedConj G S (σ : G) ((n : ℤ) + 1) τ)).toAdd =
      (tameCharacter G S σ : ResidueField S) ^ (n + 1) *
        (ramificationGroupGradedToResidueField hϖ n τ).toAdd := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    let ϖ' : S := g⁻¹ • ϖ
    have hϖ' : Irreducible ϖ' := hϖ.smul g⁻¹
    obtain ⟨v, hv⟩ := IsDiscreteValuationRing.associated_of_irreducible S hϖ hϖ'
    have hres_v :
        residue S (v : S) = ((tameCharacter G S σ : (ResidueField S)ˣ)⁻¹ : ResidueField S) := by
      have ha : ((σ⁻¹ : ramificationGroup G S 0) : G) • ϖ = ϖ * (v : S) := by
        simpa [ϖ', g, Subgroup.coe_inv] using hv.symm
      rw [← Units.val_inv_eq_inv_val, ← map_inv, coe_tameCharacter_of_smul_eq_mul hϖ ha]
    have hmove : (τ : G) • ϖ' - ϖ' ∈ maximalIdeal S ^ (n + 2) :=
      (mem_ramificationGroup_natCast_iff.mp τ.property) ϖ'
    rw [hϖ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    have hτcoord : (ramificationGroupToResidueField hϖ' n τ).toAdd = residue S y := by
      rw [ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ' (by rw [← hy, mul_comm]),
        toAdd_ofAdd]
    have hconjMove :
        ((MulAut.conjNormal g τ : ramificationGroup G S ((n : ℤ) + 1)) : G) • ϖ - ϖ =
          ϖ ^ (n + 2) * g • y := by
      calc
        _ = g • ((τ : G) • ϖ' - ϖ') := by simp [ϖ', MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * ϖ' ^ (n + 2)) := by rw [hy]
        _ = ϖ ^ (n + 2) * g • y := by
          rw [smul_mul', smul_pow', show g • ϖ' = ϖ by simp [ϖ'], mul_comm]
    have hresidue : residue S (g • y) = residue S y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G S σ.property y
    have hchange := toAdd_ramificationGroupToResidueField_of_mul_eq hϖ hϖ' hv τ
    rw [hres_v] at hchange
    simp only [ramificationGroupGradedConj_mk]
    rw [ramificationGroupGradedToResidueField_mk, ramificationGroupGradedToResidueField_mk,
      ramificationGroupToResidueField_apply_of_smul_sub_eq hϖ hconjMove, toAdd_ofAdd, hresidue,
      ← hτcoord, hchange, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (Units.ne_zero _), one_pow,
      one_mul]

variable (G S) in
/-- **The tame character is equivariant.** For `g ∈ G` and `σ ∈ G_0`, the tame character of
`g σ g⁻¹` is the image of the tame character of `σ` under the automorphism of the residue field
induced by `g`: `theta_0(g σ g⁻¹) = g • theta_0(σ)`. -/
@[simp]
theorem tameCharacter_conj (g : G) (σ : ramificationGroup G S 0) :
    (tameCharacter G S (MulAut.conjNormal g σ) : ResidueField S) =
      g • (tameCharacter G S σ : ResidueField S) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨u, hu⟩ := dvd_smul_of_irreducible hϖ (σ : G)
  have hgϖ : Irreducible (g • ϖ) := hϖ.smul g
  have hgu : (MulAut.conjNormal g σ : G) • (g • ϖ) = g • ϖ * g • u := by
    rw [MulAut.conjNormal_apply, mul_smul, mul_smul, inv_smul_smul, hu, smul_mul']
  rw [coe_tameCharacter_of_smul_eq_mul hgϖ hgu, coe_tameCharacter_of_smul_eq_mul hϖ hu,
    ResidueField.residue_smul]

variable (G S) in
/-- **The tame character twisted by a power map.** If `g ∈ G` acts on the residue field as the
`q`-th power map, then `theta_0(g σ g⁻¹) = theta_0(σ) ^ q` for every `σ ∈ G_0`. -/
theorem tameCharacter_conj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : ResidueField S, g • x = x ^ q) (σ : ramificationGroup G S 0) :
    tameCharacter G S (MulAut.conjNormal g σ) = tameCharacter G S σ ^ q :=
  Units.ext (by rw [tameCharacter_conj, hg, Units.val_pow_eq_pow_val])

variable (G S) in
/-- The equivariance of the tame character, read on the tame quotient `G_0 / G_1`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj (g : G)
    (τ : RamificationGroupGraded G S 0) :
    (tameCharacterGraded G S (ramificationGroupGradedConj G S g 0 τ) : ResidueField S) =
      g • (tameCharacterGraded G S τ : ResidueField S) := by
  induction τ using QuotientGroup.induction_on with
  | _ σ =>
    rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk,
      tameCharacter_conj]

variable (G S) in
/-- The power-map twist of the tame character, read on the tame quotient `G_0 / G_1`. -/
theorem tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : ResidueField S, g • x = x ^ q) (τ : RamificationGroupGraded G S 0) :
    tameCharacterGraded G S (ramificationGroupGradedConj G S g 0 τ) =
      tameCharacterGraded G S τ ^ q :=
  Units.ext (by rw [tameCharacterGraded_ramificationGroupGradedConj, hg,
    Units.val_pow_eq_pow_val])

/-- Conjugation by inertia acts trivially on the tame quotient `G_0 / G_1` under a separable
residue extension. -/
theorem ramificationGroupGradedConj_zero (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    (σ : ramificationGroup G S 0) (τ : RamificationGroupGraded G S 0) :
    ramificationGroupGradedConj G S (σ : G) 0 τ = τ := by
  apply tameCharacterGraded_injective (G := G) R
  apply Units.val_injective
  rw [tameCharacterGraded_ramificationGroupGradedConj]
  exact TauCeti.MulSemiringAction.mem_ker_toRingAut_iff.mp
    (ramificationGroup_zero_eq_ker_toRingAut G S ▸ σ.property) _

/-! ### Wild inertia as the Sylow subgroup of inertia -/

section

variable (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)]
  [SMulCommClass G R S] [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
variable (G S)
include R

/-- When the residue extension is separable, the order of the tame quotient `G_0 / G_1` divides
`#(ResidueField S) - 1`. -/
theorem card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one :
    Nat.card (RamificationGroupGraded G S 0) ∣ Nat.card (ResidueField S) - 1 := by
  rw [← Nat.card_units]
  exact Subgroup.card_dvd_of_injective _ (tameCharacterGraded_injective R)

section

variable [FaithfulSMul G S]

section

variable [Finite (ramificationGroup G S 0)]

/-- **Wild inertia is a Sylow subgroup of inertia.** For a faithful action with finite `G_0`, a
separable residue extension and residue characteristic `p`, the first ramification group `G_1`,
viewed inside `G_0`, is a Sylow `p`-subgroup: it is a `p`-group
(`TauCeti.IsLocalRing.isPGroup_ramificationGroup`) whose index is prime to `p`
(`TauCeti.IsLocalRing.not_dvd_index_ramificationGroup_one`). -/
noncomputable def ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p] :
    Sylow p (ramificationGroup G S 0) :=
  (isPGroup_ramificationGroup G S p (i := 1) one_pos).comap_subtype.toSylow
    (not_dvd_index_ramificationGroup_one R p)

@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p] :
    (ramificationGroupOneSylow G S R p : Subgroup (ramificationGroup G S 0)) =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) :=
  (rfl)

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
instance ramificationGroupOneSylow_normal (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p] :
    (ramificationGroupOneSylow G S R p : Subgroup (ramificationGroup G S 0)).Normal := by
  rw [ramificationGroupOneSylow_coe]
  infer_instance

/-- **`G_1` is the only Sylow `p`-subgroup of `G_0`**: the Sylow subgroup
`TauCeti.IsLocalRing.ramificationGroupOneSylow` is normal. -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    (Q : Sylow p (ramificationGroup G S 0)) : Q = ramificationGroupOneSylow G S R p := by
  let _ := Sylow.unique_of_normal (ramificationGroupOneSylow G S R p) inferInstance
  exact Subsingleton.elim _ _

/-- The order of `G_1` is the `p`-part of the order of `G_0`: `#G_1 = p ^ (v_p #G_0)`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p] :
    Nat.card (ramificationGroup G S 1) =
      p ^ (Nat.card (ramificationGroup G S 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow G S R p),
    ramificationGroupOneSylow_coe]
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe
      (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

/-- **Wild inertia is trivial if and only if `p` does not divide `#G_0`** (the tamely ramified
case). -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [Fact p.Prime] [CharP (ResidueField S) p] :
    ramificationGroup G S 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G S 0) := by
  have hp : p.Prime := Fact.out
  rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one G S R p,
    pow_eq_one_iff_right hp.ne_one, Nat.factorization_eq_zero_iff]
  simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]

end

/-- **Wild inertia is trivial if and only if `p` does not divide `#G_0`** when `ResidueField S` is
finite (the tamely ramified case), without assuming `G_0` is finite. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero_of_finite_residueField
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p] [Finite (ResidueField S)] :
    ramificationGroup G S 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G S 0) := by
  by_cases hfin : Finite (ramificationGroup G S 0)
  · exact ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero G S R p
  · have hinf := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    simp only [dvd_zero, not_true_eq_false, iff_false]
    intro h
    have hker := ker_tameCharacter R (G := G) (S := S)
    rw [h, Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff] at hker
    exact hfin (Finite.of_injective _ hker)

end

end

/-! ### Residue characteristic zero -/

section CharZero

variable [CharZero (ResidueField S)] [Finite (ramificationGroup G S 0)]

variable (G S) in
/-- In residue characteristic zero with finite inertia `G_0`, every element in the kernel of
`tameCharacter` lies in `G_1` (without any base ring `R`, separability, or faithfulness
hypothesis). -/
private theorem mem_ramificationGroup_one_of_mem_ker_tameCharacter_of_charZero
    {σ : ramificationGroup G S 0} (hσker : σ ∈ (tameCharacter G S).ker) :
    (σ : G) ∈ ramificationGroup G S 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  let : Fintype (ramificationGroup G S 0) := Fintype.ofFinite _
  -- Because `ResidueField S` has characteristic zero, `#G_0` is a unit in `S`.
  have hunit : IsUnit ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  rw [← Nat.cast_one, mem_ramificationGroup_natCast_iff]
  intro x
  -- Average `x` over `G_0` to obtain a `G_0`-invariant element `s` congruent to `#G_0 * x`
  -- mod `𝔪`.
  let s : S := ∑ τ : ramificationGroup G S 0, (τ : G) • x
  have hs_inv : (σ : G) • s = s := TauCeti.smul_sum_smul σ x
  have hdiff_mem : ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s ∈
      maximalIdeal S := by
    have heq : ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s =
        ∑ τ : ramificationGroup G S 0, (x - (τ : G) • x) := by
      simp only [s, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [heq]
    exact Ideal.sum_mem _ fun τ _ ↦
      neg_mem_iff.mp (by simpa [neg_sub] using mem_ramificationGroup_zero_iff.mp τ.property x)
  -- Write `#G_0 * x - s = ϖ * c`; then `#G_0 * (σ x - x) = σ(ϖ * c) - ϖ * c ∈ 𝔪 ^ 2`.
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hdiff_mem
  obtain ⟨c, hc⟩ := hdiff_mem
  have hmul : ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * ((σ : G) • x - x) ∈
      maximalIdeal S ^ 2 := by
    have hsmul_nat :
        (σ : G) • ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) =
          (Fintype.card (ramificationGroup G S 0) : S) := by
      rw [← MulSemiringAction.toRingHom_apply, map_natCast]
    have hid : ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * ((σ : G) • x - x) =
        (σ : G) • (ϖ * c) - ϖ * c := by
      calc
        ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * ((σ : G) • x - x)
          = ((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * ((σ : G) • x) - s -
              (((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s) := by ring
        _ = (σ : G) • (((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s) -
              (((Fintype.card (ramificationGroup G S 0) : ℕ) : S) * x - s) := by
            rw [smul_sub, smul_mul', hsmul_nat, hs_inv]
        _ = (σ : G) • (ϖ * c) - ϖ * c := by rw [hc]
    rw [hid]
    have hsplit : (σ : G) • (ϖ * c) - ϖ * c =
        ((σ : G) • ϖ - ϖ) * ((σ : G) • c) + ϖ * ((σ : G) • c - c) := by
      rw [smul_mul']
      ring
    rw [hsplit]
    refine add_mem ?_ ?_
    · exact Ideal.mul_mem_right _ _
        ((tameCharacter_eq_one_iff_smul_sub_mem hϖ).mp (MonoidHom.mem_ker.mp hσker))
    · have hϖm : ϖ ∈ maximalIdeal S := by rw [hϖ.maximalIdeal_eq]; exact Ideal.subset_span rfl
      rw [pow_two]
      exact Ideal.mul_mem_mul hϖm (mem_ramificationGroup_zero_iff.mp σ.property c)
  exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp hmul

variable (G S) in
/-- In residue characteristic zero with finite inertia `G_0`, the kernel of `tameCharacter` is
`G_1` (without any base ring `R`, separability, or faithfulness hypothesis). -/
theorem ker_tameCharacter_of_charZero :
    (tameCharacter G S).ker =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) := by
  refine le_antisymm (fun σ hσker ↦ ?_) ramificationGroup_one_subgroupOf_le_ker_tameCharacter
  exact mem_ramificationGroup_one_of_mem_ker_tameCharacter_of_charZero G S hσker

variable (G S) in
/-- **Tame character embedding in characteristic zero.** In residue characteristic zero with
finite inertia `G_0`, `G_0 / G_1` embeds into `(ResidueField S)ˣ` (without any base ring `R`,
separability, or faithfulness hypothesis). -/
theorem tameCharacterGraded_injective_of_charZero :
    Function.Injective (tameCharacterGraded G S) := by
  unfold tameCharacterGraded
  rw [QuotientGroup.injective_lift_iff, zero_add]
  exact (ker_tameCharacter_of_charZero G S).symm

variable (G S) in
/-- In residue characteristic zero with faithful action and finite inertia `G_0`, the tame
character `G_0 →* (ResidueField S)ˣ` is injective (without any base ring `R` or separability
hypothesis). -/
theorem tameCharacter_injective_of_charZero [FaithfulSMul G S] :
    Function.Injective (tameCharacter G S) := by
  have : Finite (ramificationGroup G S 1) :=
    finite_ramificationGroup_of_le G S zero_le_one
  rw [← MonoidHom.ker_eq_bot_iff, ker_tameCharacter_of_charZero G S,
    ramificationGroup_one_eq_bot_of_charZero G S, Subgroup.bot_subgroupOf]

variable (G S) in
/-- **Inertia is cyclic in residue characteristic zero.** When `ResidueField S` has characteristic
zero, the action is faithful, and `G_0` is finite, `G_0` itself is cyclic (without any base ring
`R` or separability hypothesis). -/
theorem isCyclic_ramificationGroup_zero_of_charZero [FaithfulSMul G S] :
    IsCyclic (ramificationGroup G S 0) :=
  isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField S)).comp (tameCharacter G S))
    (Units.val_injective.comp (tameCharacter_injective_of_charZero G S))

end CharZero

end DiscreteValuationRing

end IsLocalRing

end TauCeti
