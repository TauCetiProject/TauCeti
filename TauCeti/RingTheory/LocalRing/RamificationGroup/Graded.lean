/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Sylow
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.LocalRing.ResidueField.Lift

/-!
# The successive quotients of the ramification filtration of a local ring

Let a group `G` act by ring automorphisms on a local ring `S` with residue field `k`, and write
`G_i = TauCeti.IsLocalRing.ramificationGroup G S i`. This file describes the successive quotients
`G_i / G_{i+1}`, with no completeness of `S` and no finiteness of `k`.

**Positive depth, on any local ring.** For `i ≥ 1`, an element `σ ∈ G_i` satisfies
`σ ^ m x - x ≡ m (σ x - x)` modulo `𝔪 ^ (i + 2)`, because `σ - 1` raises the `𝔪`-adic order of
`𝔪 ^ (i + 1)` by `i + 1 ≥ 2`. Hence `σ ^ p ∈ G_{i+1}` when `k` has characteristic `p`, and
`σ ∈ G_{i+1}` as soon as some power `σ ^ m` with `m` invertible in `k` is. Moreover, the
displacement map `σ ↦ (x ↦ [σ x - x])` gives a homomorphism `displacementHom` into the additive
group `S → 𝔪 ^ (i + 1) / 𝔪 ^ (i + 2)` with kernel `G_{i+1}`, so every `G_i / G_{i+1}` with
`i ≥ 1` is abelian and a `p`-group; every `G_i` with `i ≥ 1` is a `p`-group once the filtration
vanishes at some index, as it does when the action is faithful, `S` is Noetherian and `G_0` is
finite; and in residue characteristic zero a finite `G_i` with `i ≥ 1` is trivial once the
filtration meets in the trivial group.

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
`c_σ` is the **tame character** `G_0 →* kˣ`, which does not depend on the uniformizer. Writing
`σ π - π = π ^ (n + 2) c_σ` for `σ ∈ G_{n+1}`, the residue of `c_σ` gives a homomorphism
`G_{n+1} →* Multiplicative k`, which depends on `π`. Their kernels contain `G_1` and `G_{n+2}`,
with equality for a separable residue extension, so they induce embeddings `G_0 / G_1 → kˣ` and
`G_{n+1} / G_{n+2} → k`. Consequently a finite `G_0 / G_1` is cyclic of order prime to the residue
characteristic, and for a faithful action with finite `G_0` in residue characteristic `p`, the
group `G_1` is the unique Sylow `p`-subgroup of `G_0`.

## Main definitions

* `TauCeti.IsLocalRing.displacementHom G S n`: the additive displacement homomorphism
  `G_{n+1} →* Multiplicative (S → 𝔪^(n+2) / 𝔪^(n+3))`.
* `TauCeti.IsLocalRing.ramificationGroupOneSylow G S p hidx`: `G_1` as a Sylow `p`-subgroup of
  `G_0` whenever `p ∤ [G_0 : G_1]`.
* `TauCeti.IsLocalRing.tameCharacter G S`: the tame character `G_0 →* kˣ`, and
  `TauCeti.IsLocalRing.tameCharacterGraded G S`: its factorization through `G_0 / G_1`.
* `TauCeti.IsLocalRing.ramificationGroupToResidueField hπ n`: the homomorphism
  `G_{n+1} →* Multiplicative k` in the coordinate of the uniformizer `π`, and
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField hπ n`: its factorization through
  `G_{n+1} / G_{n+2}`.

## Main results

* `TauCeti.IsLocalRing.pow_mem_ramificationGroup_of_charP` and
  `TauCeti.IsLocalRing.isPGroup_ramificationGroupGraded`: in residue characteristic `p`, the
  `p`-th power of an element of `G_i` lies in `G_{i+1}` for `i ≥ 1`, so `G_i / G_{i+1}` is a
  `p`-group.
* `TauCeti.IsLocalRing.ker_displacementHom`, `TauCeti.IsLocalRing.commutator_ramificationGroup_le`,
  and `TauCeti.IsLocalRing.isMulCommutative_ramificationGroupGraded`: positive-depth graded pieces
  `G_i / G_{i+1}` (`i > 0`) are commutative.
* `TauCeti.IsLocalRing.isPGroup_ramificationGroup_of_eq_bot` and
  `TauCeti.IsLocalRing.isPGroup_ramificationGroup`: the groups `G_i` with `i ≥ 1` are `p`-groups
  once the filtration vanishes at some index, in particular for a faithful action on a Noetherian
  local ring with finite `G_0`.
* `TauCeti.IsLocalRing.ramificationGroup_eq_bot_of_charZero`: in residue characteristic zero, a
  finite `G_i` with `i ≥ 1` is trivial when the filtration meets in the trivial group.
* `TauCeti.IsLocalRing.eq_ramificationGroupOneSylow`: `G_1` is the only Sylow `p`-subgroup
  of `G_0` when `p ∤ [G_0 : G_1]`.
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
* `TauCeti.IsLocalRing.isCyclic_ramificationGroupGraded_zero` and
  `TauCeti.IsLocalRing.not_dvd_index_ramificationGroup_one`: a finite `G_0 / G_1` is
  cyclic of order prime to the residue characteristic.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5 to 7 and the
  corollaries of Proposition 7.
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

/-- An element of `G_n` moves every element of `𝔪 ^ (k + 1)` by an element of
`𝔪 ^ (n + k + 1)`: the operator `σ - 1` raises the `𝔪`-adic order by `n`, and by `n + 1` on `S`
itself. -/
theorem smul_sub_mem_maximalIdeal_pow_of_mem_ramificationGroup {n k : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S n) {y : S} (hy : y ∈ maximalIdeal S ^ (k + 1)) :
    σ • y - y ∈ maximalIdeal S ^ (n + k + 1) := by
  rw [mem_ramificationGroup_natCast_iff] at hσ
  induction k generalizing y with
  | zero => simpa using hσ y
  | succ k ih =>
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
    · -- `σ (a b) - a b = (σ a - a) σ b + a (σ b - b)`, with each term of order `n + k + 2`.
      have hb' : σ • b ∈ maximalIdeal S ^ 1 := by
        rw [smul_mem_maximalIdeal_pow_iff, pow_one]; exact hb
      rw [smul_mul',
        (by ring : σ • a * σ • b - a * b = (σ • a - a) * σ • b + a * (σ • b - b))]
      refine add_mem ?_ ?_
      · rw [(by omega : n + (k + 1) + 1 = (n + k + 1) + 1), pow_add]
        exact Ideal.mul_mem_mul (ih ha) hb'
      · rw [(by omega : n + (k + 1) + 1 = (k + 1) + (n + 1)), pow_add]
        exact Ideal.mul_mem_mul ha (hσ b)
    · rw [smul_add, (by ring : σ • a + σ • b - (a + b) = (σ • a - a) + (σ • b - b))]
      exact add_mem ha hb

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

/-- **In residue characteristic zero the positive-depth ramification groups are trivial** when
they are finite and the filtration meets in the trivial group: each positive-depth step
`G_j / G_{j+1}` is a finite group without torsion, so `G_i` lies in every `G_j`. -/
theorem ramificationGroup_eq_bot_of_charZero [CharZero (ResidueField S)] {i : ℤ} (hi : 0 < i)
    [Finite (ramificationGroup G S i)] (hbot : ⨅ j, ramificationGroup G S j = ⊥) :
    ramificationGroup G S i = ⊥ := by
  have hstep : ∀ j : ℤ, i ≤ j → ramificationGroup G S j ≤ ramificationGroup G S (j + 1) := by
    intro j hij σ hσ
    -- `σ` has finite order, since it lies in the finite group `G_i`.
    have hm : 0 < orderOf σ := by
      rw [← Subgroup.orderOf_mk σ (ramificationGroup_antitone G S hij hσ)]
      exact orderOf_pos _
    refine mem_ramificationGroup_add_one_of_pow_mem (by omega) hσ (Nat.cast_ne_zero.mpr hm.ne') ?_
    rw [pow_orderOf_eq_one]
    exact one_mem _
  have hle : ∀ k : ℕ, ramificationGroup G S i ≤ ramificationGroup G S (i + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc]
      exact ih.trans (hstep _ (by omega))
  refine eq_bot_iff.mpr (hbot ▸ le_iInf fun j ↦ ?_)
  exact (hle (j - i).toNat).trans (ramificationGroup_antitone G S (by omega))

variable (G S) [IsNoetherianRing S] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]

/-- **The positive-depth ramification groups are `p`-groups**, for `p` the residue characteristic,
when the action on the Noetherian local ring `S` is faithful and `G_0` is finite. In particular the
first ramification group `G_1` is a `p`-group. -/
theorem isPGroup_ramificationGroup (p : ℕ) [CharP (ResidueField S) p] {i : ℤ} (hi : 0 < i) :
    IsPGroup p (ramificationGroup G S i) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G S
  exact isPGroup_ramificationGroup_of_eq_bot p hi (hN N le_rfl)

end Positive

section PositiveExtra

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The positive-depth **displacement homomorphism** on `G_{n+1}`, sending `σ` to the function
`x ↦ [σ • x - x]` in the `(n + 2)`-nd graded piece `𝔪^(n+2) / 𝔪^(n+3)` of the maximal-ideal
filtration. Its kernel is `G_{n+2}` (`ker_displacementHom`). -/
def displacementHom (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S]
    [MulSemiringAction G S] (n : ℕ) :
    ramificationGroup G S ((n : ℤ) + 1) →*
      Multiplicative (S → (maximalIdeal S ^ (n + 2) : Ideal S) ⧸
        (maximalIdeal S • ⊤ : Submodule S (maximalIdeal S ^ (n + 2) : Ideal S))) :=
  MonoidHom.mk'
    (fun σ ↦ .ofAdd fun x ↦
      Submodule.Quotient.mk ⟨(σ : G) • x - x,
        mem_ramificationGroup_natCast_iff.mp ((Nat.cast_succ (R := ℤ) n).symm ▸ σ.property) x⟩)
    fun σ τ ↦ by
      rw [← ofAdd_add]
      refine congrArg Multiplicative.ofAdd (funext fun x ↦ ?_)
      rw [Pi.add_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq,
        Ideal.mem_smul_top_pow_iff]
      simp only [Submodule.coe_sub, Submodule.coe_add]
      have hσ : (σ : G) ∈ ramificationGroup G S ((n + 1 : ℕ) : ℤ) :=
        (Nat.cast_succ (R := ℤ) n).symm ▸ σ.property
      have hy : (τ : G) • x - x ∈ maximalIdeal S ^ (n + 2) :=
        mem_ramificationGroup_natCast_iff.mp ((Nat.cast_succ (R := ℤ) n).symm ▸ τ.property) x
      have hστ : (σ : G) • ((τ : G) • x - x) - ((τ : G) • x - x) ∈
          maximalIdeal S ^ (n + 3) :=
        Ideal.pow_le_pow_right (by omega)
          (smul_sub_mem_maximalIdeal_pow_of_mem_ramificationGroup hσ hy)
      convert hστ using 1
      rw [Subgroup.coe_mul, mul_smul, smul_sub]
      ring

/-- Evaluating `displacementHom G S n σ` at `x` gives the class of `σ • x - x` in
`𝔪^(n+2) / 𝔪^(n+3)`. -/
@[simp]
theorem toAdd_displacementHom_apply (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [MulSemiringAction G S] (n : ℕ)
    (σ : ramificationGroup G S ((n : ℤ) + 1)) (x : S) :
    Multiplicative.toAdd (displacementHom G S n σ) x =
      Submodule.Quotient.mk ⟨(σ : G) • x - x,
        mem_ramificationGroup_natCast_iff.mp ((Nat.cast_succ (R := ℤ) n).symm ▸ σ.property) x⟩ :=
  (rfl)

/-- The kernel of `displacementHom G S n` is `G_{n+2}`, viewed inside `G_{n+1}`. -/
theorem ker_displacementHom (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [MulSemiringAction G S] (n : ℕ) :
    (displacementHom G S n).ker =
      (ramificationGroup G S ((n : ℤ) + 1 + 1)).subgroupOf
        (ramificationGroup G S ((n : ℤ) + 1)) := by
  ext σ
  rw [MonoidHom.mem_ker, ← toAdd_eq_zero, Subgroup.mem_subgroupOf,
    (by omega : (n : ℤ) + 1 + 1 = (n + 2 : ℕ)), mem_ramificationGroup_natCast_iff, funext_iff]
  refine forall_congr' fun x ↦ ?_
  rw [Pi.zero_apply, toAdd_displacementHom_apply, Submodule.Quotient.mk_eq_zero,
    Ideal.mem_smul_top_pow_iff]

/-- At positive depth `i > 0`, the commutator subgroup `⁅G_i, G_i⁆` lies in `G_{i+1}`. -/
theorem commutator_ramificationGroup_le (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [MulSemiringAction G S] {i : ℤ} (hi : 0 < i) :
    ⁅ramificationGroup G S i, ramificationGroup G S i⁆ ≤ ramificationGroup G S (i + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
  have hker := Group.Abelianization.commutator_le_ker (displacementHom G S n)
  rw [ker_displacementHom] at hker
  exact (Subgroup.map_subtype_commutator _).symm.trans_le (Subgroup.map_le_iff_le_comap.mpr hker)

/-- Every positive-depth graded piece `G_i / G_{i+1}` (`i > 0`) of the ramification filtration is
commutative. -/
theorem isMulCommutative_ramificationGroupGraded (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [MulSemiringAction G S] {i : ℤ} (hi : 0 < i) :
    IsMulCommutative (RamificationGroupGraded G S i) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr <|
    Subgroup.map_le_iff_le_comap.mp <|
      (Subgroup.map_subtype_commutator _).trans_le (commutator_ramificationGroup_le G S hi)

/-- Each positive-depth graded piece `G_{n+1} / G_{n+2}` (indexed by `(n : ℤ) + 1`) is
commutative. -/
instance instIsMulCommutativeRamificationGroupGradedAddOne (G : Type*) [Group G] (S : Type*)
    [CommRing S] [IsLocalRing S] [MulSemiringAction G S] (n : ℕ) :
    IsMulCommutative (RamificationGroupGraded G S ((n : ℤ) + 1)) :=
  isMulCommutative_ramificationGroupGraded G S (by omega)

/-- Each positive-depth graded piece `G_{n+1} / G_{n+2}` (indexed by `((n + 1 : ℕ) : ℤ)`) is
commutative. -/
instance instIsMulCommutativeRamificationGroupGradedNatCastSucc (G : Type*) [Group G] (S : Type*)
    [CommRing S] [IsLocalRing S] [MulSemiringAction G S] (n : ℕ) :
    IsMulCommutative (RamificationGroupGraded G S ((n + 1 : ℕ) : ℤ)) :=
  isMulCommutative_ramificationGroupGraded G S (by omega)

/-- At positive depth `i > 0`, for `σ ∈ G_i` and `m : ℕ`, `σ ^ m` lies in `G_{i+1}` if and only if
`m * (σ • x - x) ∈ 𝔪 ^ (i + 2)` for every `x : S`. -/
theorem pow_mem_ramificationGroup_succ_iff {i : ℤ} (hi : 0 < i) {σ : G}
    (hσ : σ ∈ ramificationGroup G S i) (m : ℕ) :
    σ ^ m ∈ ramificationGroup G S (i + 1) ↔
      ∀ x : S, (m : S) * (σ • x - x) ∈ maximalIdeal S ^ (i + 2).toNat := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
  have htoNat : ((n : ℤ) + 1 + 2).toNat = n + 3 := by omega
  have hmem : (⟨σ, hσ⟩ : ramificationGroup G S ((n : ℤ) + 1)) ^ m ∈
        (displacementHom G S n).ker ↔
      σ ^ m ∈ ramificationGroup G S ((n : ℤ) + 1 + 1) := by
    rw [ker_displacementHom, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  rw [htoNat, ← hmem, MonoidHom.mem_ker, map_pow, ← toAdd_eq_zero, funext_iff]
  refine forall_congr' fun x ↦ ?_
  rw [toAdd_pow, Pi.smul_apply, Pi.zero_apply, toAdd_displacementHom_apply,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Ideal.mem_smul_top_pow_iff, Submodule.coe_smul_of_tower, nsmul_eq_mul]

/-- In residue characteristic zero, any finite positive-depth graded piece `G_i / G_{i+1}`
(`i > 0`) is trivial. -/
theorem subsingleton_ramificationGroupGraded_of_charZero (G : Type*) [Group G] (S : Type*)
    [CommRing S] [IsLocalRing S] [MulSemiringAction G S] [CharZero (ResidueField S)] {i : ℤ}
    (hi : 0 < i) [Finite (RamificationGroupGraded G S i)] :
    Subsingleton (RamificationGroupGraded G S i) := by
  refine subsingleton_iff_forall_eq 1 |>.mpr fun q ↦ ?_
  induction q using QuotientGroup.induction_on with
  | _ g =>
    set m := orderOf (QuotientGroup.mk g : RamificationGroupGraded G S i)
    have hm : 0 < m := orderOf_pos _
    have hpow : (g : G) ^ m ∈ ramificationGroup G S (i + 1) := by
      have hq : QuotientGroup.mk (g ^ m) = (1 : RamificationGroupGraded G S i) := by
        rw [QuotientGroup.mk_pow]
        exact pow_orderOf_eq_one _
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow] at hq
      exact hq
    have hmx := (pow_mem_ramificationGroup_succ_iff hi g.property m).mp hpow
    have hunit : IsUnit (m : S) := by
      rw [← residue_ne_zero_iff_isUnit, map_natCast]
      exact Nat.cast_ne_zero.mpr hm.ne'
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_ramificationGroup_iff]
    intro x
    have htoNat : (i + 1 + 1).toNat = (i + 2).toNat := by omega
    rw [htoNat]
    exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp (hmx x)

/-- **Wild inertia is a Sylow subgroup of inertia.** For a faithful action on a Noetherian local
ring `S` in prime residue characteristic `p` with finite inertia `G_0` and `p ∤ [G_0 : G_1]`, the
group `G_1` viewed inside `G_0` is a Sylow `p`-subgroup. -/
def ramificationGroupOneSylow (G S : Type*) [Group G] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    Sylow p (ramificationGroup G S 0) :=
  ((TauCeti.IsLocalRing.isPGroup_ramificationGroup G S p (i := 1) one_pos).comap_subtype).toSylow
    hidx

/-- The subgroup underlying `TauCeti.IsLocalRing.ramificationGroupOneSylow` is `G_1` inside
`G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (G S : Type*) [Group G] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    (ramificationGroupOneSylow G S p hidx : Subgroup (ramificationGroup G S 0)) =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) :=
  (rfl)

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
instance ramificationGroupOneSylow_normal (G S : Type*) [Group G] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    (ramificationGroupOneSylow G S p hidx :
      Subgroup (ramificationGroup G S 0)).Normal := by
  rw [ramificationGroupOneSylow_coe]
  infer_instance

/-- **`G_1` is the only Sylow `p`-subgroup of `G_0`**: for a faithful action on a Noetherian local
ring `S` in prime residue characteristic `p` with finite inertia `G_0` and `p ∤ [G_0 : G_1]`, the
Sylow subgroup `TauCeti.IsLocalRing.ramificationGroupOneSylow` is normal and hence unique. -/
theorem eq_ramificationGroupOneSylow (G S : Type*) [Group G] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index)
    (Q : Sylow p (ramificationGroup G S 0)) :
    Q = ramificationGroupOneSylow G S p hidx := by
  let _ : Unique (Sylow p (ramificationGroup G S 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow G S p hidx) inferInstance
  exact Subsingleton.elim _ _

/-- For a faithful action on a Noetherian local ring `S` in prime residue characteristic `p` with
finite inertia `G_0` and `p ∤ [G_0 : G_1]`, the cardinality of `G_1` is `p ^ v_p(#G_0)`. -/
theorem natCard_ramificationGroup_one_of_not_dvd_index (G S : Type*) [Group G] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    Nat.card (ramificationGroup G S 1) =
      p ^ (Nat.card (ramificationGroup G S 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow G S p hidx)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

/-- For a faithful action on a Noetherian local ring `S` in residue characteristic `p` with finite
inertia `G_0` and `p ∤ [G_0 : G_1]`, `G_1 = ⊥` if and only if `p ∤ #G_0`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_of_not_dvd_index
    (G S : Type*) [Group G] [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    [MulSemiringAction G S] (p : ℕ) [CharP (ResidueField S) p] [FaithfulSMul G S]
    [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    ramificationGroup G S 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G S 0) := by
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    rw [← Subgroup.card_eq_one,
      natCard_ramificationGroup_one_of_not_dvd_index G S p hidx,
      pow_eq_one_iff_right hp.ne_one, Nat.factorization_eq_zero_iff]
    simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]
  · have : CharZero (ResidueField S) := CharP.charP_to_charZero (ResidueField S)
    have : Finite (ramificationGroup G S 1) :=
      finite_ramificationGroup_of_le G S zero_le_one
    rw [ramificationGroup_eq_bot_of_charZero (G := G) (S := S) one_pos
        (iInf_ramificationGroup_eq_bot G S), zero_dvd_iff]
    exact iff_of_true rfl Nat.card_pos.ne'

end PositiveExtra

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

/-- Over a local `R`-algebra `S` on which `G` acts by `R`-algebra automorphisms with separable
residue extension, an element of `G_0` moving every element of the maximal ideal into an ideal `I`
moves every element of `S` into `I`. -/
theorem smul_sub_mem_of_mem_ramificationGroup_zero_of_forall_mem_maximalIdeal {I : Ideal S} {σ : G}
    (hσ : σ ∈ ramificationGroup G S 0) (hm : ∀ y ∈ maximalIdeal S, σ • y - y ∈ I) (x : S) :
    σ • x - x ∈ I := by
  obtain ⟨g, hval, hder⟩ := exists_aeval_mem_maximalIdeal_isUnit_aeval_derivative (R := R) x
  set f : S[X] := g.map (algebraMap R S)
  set d : S := σ • x - x
  obtain ⟨k, hk⟩ := binomExpansion f x d
  rw [add_sub_cancel] at hk
  have hfσ : f.eval (σ • x) - f.eval x ∈ I := by
    simpa only [f, eval_map_algebraMap, g.aeval_smul σ x] using hm (aeval x g) hval
  have hdu : d * ((derivative f).eval x + k * d) = f.eval (σ • x) - f.eval x := by
    rw [hk]
    ring
  have hd0 : residue S d = 0 := by
    rw [residue_eq_zero_iff]
    exact mem_ramificationGroup_zero_iff.mp hσ x
  have hunit : IsUnit ((derivative f).eval x + k * d) := by
    rw [← residue_ne_zero_iff_isUnit, map_add, map_mul, hd0, mul_zero, add_zero]
    rw [← residue_ne_zero_iff_isUnit] at hder
    rwa [derivative_map, eval_map_algebraMap]
  exact (I.mul_unit_mem_iff_mem hunit).mp (hdu ▸ hfσ)

/-- When `S` is a local `R`-algebra on which `G` acts by `R`-algebra automorphisms with separable
residue extension, membership of an element `σ ∈ G_0` in `G_i` is decided on any generating set `s`
of the maximal ideal of `S`. -/
theorem mem_ramificationGroup_iff_of_span_eq_maximalIdeal {s : Set S}
    (hs : Ideal.span s = maximalIdeal S) {i : ℤ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S 0) :
    σ ∈ ramificationGroup G S i ↔
      ∀ z ∈ s, σ • z - z ∈ maximalIdeal S ^ (i + 1).toNat := by
  rw [mem_ramificationGroup_iff]
  refine ⟨fun h z _ ↦ h z, ?_⟩
  suffices ∀ m : ℕ, (∀ z ∈ s, σ • z - z ∈ maximalIdeal S ^ m) →
      ∀ x : S, σ • x - x ∈ maximalIdeal S ^ m from this (i + 1).toNat
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hz
    have ihm : ∀ x : S, σ • x - x ∈ maximalIdeal S ^ m :=
      ih fun z hzs ↦ Ideal.pow_le_pow_right m.le_succ (hz z hzs)
    refine smul_sub_mem_of_mem_ramificationGroup_zero_of_forall_mem_maximalIdeal R hσ
      fun y hy ↦ ?_
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem z hzs => exact hz z hzs
    | zero => simp
    | add y₁ y₂ _ _ h₁ h₂ =>
      rw [smul_add, add_sub_add_comm]
      exact add_mem h₁ h₂
    | smul c y hy hcy =>
      rw [smul_eq_mul,
        (by rw [smul_mul']; ring : σ • (c * y) - c * y = σ • c * (σ • y - y) + (σ • c - c) * y)]
      refine add_mem (Ideal.mul_mem_left _ _ hcy) ?_
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ihm c) (hs ▸ hy)

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
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦ ?_
  induction g using QuotientGroup.induction_on with
  | H σ =>
    rw [tameCharacterGraded_mk, ← MonoidHom.mem_ker, ker_tameCharacter R] at hg
    rwa [QuotientGroup.eq_one_iff, zero_add]

/-- **The tame quotient is cyclic**: a finite `G_0 / G_1` embeds into the multiplicative group of
the residue field, when the residue extension is separable. -/
theorem isCyclic_ramificationGroupGraded_zero (R : Type*) [CommRing R] [IsLocalRing R]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    [Finite (RamificationGroupGraded G S 0)] :
    IsCyclic (RamificationGroupGraded G S 0) :=
  isCyclic_of_injective_ringHom ((Units.coeHom _).comp (tameCharacterGraded G S))
    (Units.val_injective.comp (tameCharacterGraded_injective R))

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
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦ ?_
  induction g using QuotientGroup.induction_on with
  | H σ =>
    rw [ramificationGroupGradedToResidueField_mk, ← MonoidHom.mem_ker,
      ker_ramificationGroupToResidueField R hπ n] at hg
    rwa [QuotientGroup.eq_one_iff]

end DiscreteValuationRing

end IsLocalRing

end TauCeti
