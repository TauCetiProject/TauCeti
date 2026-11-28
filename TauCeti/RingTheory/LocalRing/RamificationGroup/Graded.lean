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
in the trivial group.

**A uniformizer decides the filtration.** Suppose that `G` fixes a local subring `R`, through an
algebra `R → S` with local structure map, and that the residue extension of `S` over `R` is
separable; the invariant subalgebra of `S` is such a local subring
(`TauCeti.FixedPoints.isLocalRing_subalgebra`). If `π` generates the
maximal ideal of `S`, then an element `σ ∈ G_0` lies in `G_n` exactly when `σ π ≡ π` modulo
`𝔪 ^ (n + 1)`, and over a discrete valuation ring its lower index is `v (σ π - π)`. Every residue
class is a simple root of a polynomial over `R`, and a Taylor expansion of that polynomial
transfers the congruence from `π` to the class. Without separability this fails: an element of
`G_0` can fix `π` and still act nontrivially on `S ⧸ 𝔪 ^ 2`.

The DVR-specific graded embeddings (`TauCeti.IsLocalRing.tameCharacter`,
`TauCeti.IsLocalRing.tameCharacterGraded`, `TauCeti.IsLocalRing.ramificationGroupToResidueField`,
`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`) live in
`TauCeti/RingTheory/DiscreteValuationRing/RamificationGroup.lean`, where they factor through
`PrincipalUnitGroupGraded`.

The positive-depth homomorphism `ramificationGroupToMaximalIdealGraded` and its kernel/injectivity
generalize the uniformizer-dependent residue map of
`TauCeti/FieldTheory/FunctionField/Place/Extension/RamificationGroup.lean`; maximal-ideal
propagation (`mem_inertia_of_forall_mem_maximalIdeal`) is adapted from
`TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean`; and the Sylow API
(`ramificationGroupOneSylow`, `natCard_ramificationGroup_one`,
`ramificationGroup_one_eq_bot_iff_not_dvd_natCard`) generalizes
`TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean`.

## Main definitions

* `TauCeti.IsLocalRing.ramificationGroupToMaximalIdealGraded G S n` and
  `TauCeti.IsLocalRing.ramificationGroupGradedToMaximalIdealGraded G S n`: at positive depth
  `n + 1`, the canonical homomorphisms
  `G_{n+1} →* Multiplicative (S → 𝔪 ^ (n + 2) ⧸ 𝔪 • ⊤)` and
  `G_{n+1} / G_{n+2} →* Multiplicative (S → 𝔪 ^ (n + 2) ⧸ 𝔪 • ⊤)`.
* `TauCeti.IsLocalRing.ramificationGroupOneSylow G S p hp`: `G_1` as a Sylow `p`-subgroup of
  `G_0`, over any Noetherian local ring with faithful action and finite `G_0` when `[G_0 : G_1]` is
  prime to `p`.

## Main results

* `TauCeti.IsLocalRing.ker_ramificationGroupToMaximalIdealGraded`,
  `TauCeti.IsLocalRing.ramificationGroupGradedToMaximalIdealGraded_injective`, and
  `TauCeti.IsLocalRing.instIsMulCommutativeRamificationGroupGradedNatCastSucc`: over any
  commutative local ring, the positive-depth graded piece `G_{n+1} / G_{n+2}` embeds into
  `S → 𝔪 ^ (n + 2) ⧸ 𝔪 • ⊤` and is commutative.
* `TauCeti.IsLocalRing.pow_mem_ramificationGroup_of_charP` and
  `TauCeti.IsLocalRing.isPGroup_ramificationGroupGraded`: in residue characteristic `p`, the
  `p`-th power of an element of `G_i` lies in `G_{i+1}` for `i ≥ 1`, so `G_i / G_{i+1}` is a
  `p`-group.
* `TauCeti.IsLocalRing.isPGroup_ramificationGroup_of_eq_bot` and
  `TauCeti.IsLocalRing.isPGroup_ramificationGroup`: the groups `G_i` with `i ≥ 1` are `p`-groups
  once the filtration vanishes at some index, in particular for a faithful action on a Noetherian
  local ring with finite `G_i`.
* `TauCeti.IsLocalRing.ramificationGroup_eq_bot_of_charZero`: in residue characteristic zero, a
  finite `G_i` with `i ≥ 1` is trivial when the filtration meets in the trivial group.
* `TauCeti.IsLocalRing.smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer`: propagation of
  `σ • x - x ∈ 𝔪 ^ m` to `𝔪 ^ (m + 1)` on `𝔪` from a generator of `𝔪`.
* `TauCeti.IsLocalRing.mem_inertia_of_forall_mem_of_pow_mem` and
  `TauCeti.IsLocalRing.mem_inertia_of_forall_mem_maximalIdeal`: congruence modulo an ideal `I`
  propagates from an ideal `J` to `S` when `σ ∈ J.inertia G` and `σ ^ m ∈ I.inertia G` with `m`
  nonzero in `k`, or from `𝔪(S)` for any `σ ∈ G_0` under a separable residue extension over `R`.
* `TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem`: for a separable residue
  extension, membership of `σ ∈ G_0` in `G_n` is decided at a generator of the maximal ideal, and
  `TauCeti.IsLocalRing.lowerIndex_eq_addVal_smul_sub` computes the lower index there.
* `TauCeti.IsLocalRing.eq_ramificationGroupOneSylow`,
  `TauCeti.IsLocalRing.natCard_ramificationGroup_one`, and
  `TauCeti.IsLocalRing.ramificationGroup_one_eq_bot_iff_not_dvd_natCard`: `G_1` is the unique
  Sylow `p`-subgroup of `G_0`, has order equal to the `p`-part of `#G_0`, and vanishes iff
  `p ∤ #G_0`.

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
      rw [smul_mul_sub_mul]
      refine add_mem ?_ ?_
      · rw [(by omega : n + (k + 1) + 1 = (n + k + 1) + 1), pow_add]
        exact Ideal.mul_mem_mul (ih ha) hb'
      · rw [(by omega : n + (k + 1) + 1 = (k + 1) + (n + 1)), pow_add]
        exact Ideal.mul_mem_mul ha (hσ b)
    · rw [smul_add, (by ring : σ • a + σ • b - (a + b) = (σ • a - a) + (σ • b - b))]
      exact add_mem ha hb

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
  have hrem : σ ^ p • x - x - p • (σ • x - x) ∈ maximalIdeal S ^ (n + 3) :=
    TauCeti.Ideal.smul_pow_sub_sub_nsmul_mem_of_inertia
      (Ideal.mem_inertia.mpr (mem_ramificationGroup_natCast_iff.mp hσ))
      (fun _ hy ↦ Ideal.pow_le_pow_right (by omega)
        (smul_sub_mem_maximalIdeal_pow_of_mem_ramificationGroup hσ hy))
      p x
  simpa using add_mem hrem hpd

/-- **Propagation from an ideal `J` when a coprime power acts trivially modulo `I`.** Let `G` act
on a commutative local ring `S`, and let `I J : Ideal S`. If `σ ∈ J.inertia G` moves every element
of `J` into `I`, and some power `σ ^ m` with `m` nonzero in `ResidueField S` lies in
`I.inertia G`, then `σ` lies in `I.inertia G`. -/
theorem mem_inertia_of_forall_mem_of_pow_mem {I J : Ideal S} {σ : G}
    (hσ : σ ∈ J.inertia G) (hJ : ∀ w ∈ J, σ • w - w ∈ I)
    {m : ℕ} (hm : (m : ResidueField S) ≠ 0) (hpow : σ ^ m ∈ I.inertia G) :
    σ ∈ I.inertia G := by
  rw [Ideal.mem_inertia] at hpow ⊢
  intro x
  have hrem := TauCeti.Ideal.smul_pow_sub_sub_nsmul_mem_of_inertia hσ hJ m x
  have hu : IsUnit (m : S) := by
    rwa [← residue_ne_zero_iff_isUnit, map_natCast]
  refine (Ideal.unit_mul_mem_iff_mem _ hu).mp ?_
  rw [← nsmul_eq_mul]
  simpa using sub_mem (hpow x) hrem

/-- At positive depth, `σ ∈ G_i` lies in `G_{i+1}` as soon as some power `σ ^ m` does, for an
exponent `m` that is nonzero in the residue field. -/
theorem mem_ramificationGroup_add_one_of_pow_mem {i : ℤ} (hi : 0 < i) {σ : G}
    (hσ : σ ∈ ramificationGroup G S i) {m : ℕ} (hm : (m : ResidueField S) ≠ 0)
    (hpow : σ ^ m ∈ ramificationGroup G S (i + 1)) : σ ∈ ramificationGroup G S (i + 1) := by
  obtain ⟨n, rfl⟩ := exists_natCast_add_one_eq hi
  rw [(by push_cast; ring : ((n + 1 : ℕ) : ℤ) + 1 = (n + 2 : ℕ)),
    ramificationGroup_natCast, Ideal.ramificationGroup_def] at hpow ⊢
  exact mem_inertia_of_forall_mem_of_pow_mem
    (Ideal.mem_inertia.mpr (mem_ramificationGroup_natCast_iff.mp hσ))
    (fun _ hw ↦ Ideal.pow_le_pow_right (by omega)
      (smul_sub_mem_maximalIdeal_pow_of_mem_ramificationGroup hσ hw))
    hm hpow

variable (G S) in
/-- At positive depth `n + 1`, sending `σ ∈ G_{n+1}` to the function
`x ↦ [σ • x - x] ∈ 𝔪 ^ (n + 2) ⧸ 𝔪 • ⊤` is a group homomorphism into the multiplicative form of an
additive `ResidueField S`-vector space, with kernel `G_{n+2}`
(`ker_ramificationGroupToMaximalIdealGraded`). This generalizes the uniformizer-dependent residue
map of `TauCeti/FieldTheory/FunctionField/Place/Extension/RamificationGroup.lean` to an arbitrary
commutative local ring. -/
def ramificationGroupToMaximalIdealGraded (n : ℕ) :
    ramificationGroup G S ((n : ℤ) + 1) →*
      Multiplicative
        (S → ↥(maximalIdeal S ^ (n + 2)) ⧸
          (maximalIdeal S • ⊤ : Submodule S ↥(maximalIdeal S ^ (n + 2)))) :=
  MonoidHom.mk'
    (fun σ ↦ .ofAdd fun x ↦ Submodule.Quotient.mk ⟨(σ : G) • x - x,
      mem_ramificationGroup_add_one_iff.mp σ.property x⟩)
    fun σ τ ↦ by
      rw [← ofAdd_add]
      refine congrArg Multiplicative.ofAdd (funext fun x ↦ ?_)
      rw [Pi.add_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq,
        Ideal.smul_top_eq_comap_mul, Submodule.mem_comap, Submodule.coe_subtype,
        Submodule.coe_sub, Submodule.coe_add]
      have hdiff : ((σ * τ : ramificationGroup G S ((n : ℤ) + 1)) : G) • x - x -
          (((σ : G) • x - x) + ((τ : G) • x - x)) =
          (σ : G) • ((τ : G) • x - x) - ((τ : G) • x - x) := by
        rw [Subgroup.coe_mul, mul_smul, smul_sub]
        ring
      have hσ' : (σ : G) ∈ ramificationGroup G S (n + 1 : ℕ) := by exact_mod_cast σ.property
      have hτ' : (τ : G) • x - x ∈ maximalIdeal S ^ (n + 1 + 1) :=
        mem_ramificationGroup_add_one_iff.mp τ.property x
      rw [hdiff, ← pow_succ]
      exact Ideal.pow_le_pow_right (by omega)
        (smul_sub_mem_maximalIdeal_pow_of_mem_ramificationGroup (k := n + 1) hσ' hτ')

variable (G S) in
/-- Evaluating `ramificationGroupToMaximalIdealGraded` at `σ` and `x` yields the class of
`σ • x - x` in `𝔪 ^ (n + 2) ⧸ 𝔪 • ⊤`. -/
@[simp]
theorem toAdd_ramificationGroupToMaximalIdealGraded_apply (n : ℕ)
    (σ : ramificationGroup G S ((n : ℤ) + 1)) (x : S) :
    Multiplicative.toAdd (ramificationGroupToMaximalIdealGraded G S n σ) x =
      Submodule.Quotient.mk ⟨(σ : G) • x - x,
        mem_ramificationGroup_add_one_iff.mp σ.property x⟩ :=
  (rfl)

variable (G S) in
/-- **The kernel of `ramificationGroupToMaximalIdealGraded` is `G_{n+2}`.** -/
theorem ker_ramificationGroupToMaximalIdealGraded (n : ℕ) :
    (ramificationGroupToMaximalIdealGraded G S n).ker =
      (ramificationGroup G S (((n : ℤ) + 1) + 1)).subgroupOf
        (ramificationGroup G S ((n : ℤ) + 1)) := by
  have hidx : ((n : ℤ) + 1) + 1 = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← toAdd_eq_zero, funext_iff,
    hidx, mem_ramificationGroup_natCast_iff]
  simp only [toAdd_ramificationGroupToMaximalIdealGraded_apply, Pi.zero_apply,
    Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_comap_mul, Submodule.mem_comap,
    Submodule.coe_subtype, ← pow_succ]

variable (G S) in
/-- The canonical positive-depth embedding
`G_{n+1} / G_{n+2} →* Multiplicative (S → 𝔪 ^ (n + 2) ⧸ 𝔪 • ⊤)`. -/
def ramificationGroupGradedToMaximalIdealGraded (n : ℕ) :
    RamificationGroupGraded G S ((n : ℤ) + 1) →*
      Multiplicative
        (S → ↥(maximalIdeal S ^ (n + 2)) ⧸
          (maximalIdeal S • ⊤ : Submodule S ↥(maximalIdeal S ^ (n + 2)))) :=
  QuotientGroup.lift _ (ramificationGroupToMaximalIdealGraded G S n)
    (ker_ramificationGroupToMaximalIdealGraded G S n).ge

variable (G S) in
/-- Evaluating `ramificationGroupGradedToMaximalIdealGraded` on the class of `σ` agrees with
`ramificationGroupToMaximalIdealGraded`. -/
@[simp]
theorem ramificationGroupGradedToMaximalIdealGraded_mk (n : ℕ)
    (σ : ramificationGroup G S ((n : ℤ) + 1)) :
    ramificationGroupGradedToMaximalIdealGraded G S n (QuotientGroup.mk σ) =
      ramificationGroupToMaximalIdealGraded G S n σ :=
  (rfl)

variable (G S) in
/-- **The positive-depth graded homomorphism into `S → 𝔪 ^ (n + 2) ⧸ 𝔪 • ⊤` is injective**, for
every group action on a commutative local ring. -/
theorem ramificationGroupGradedToMaximalIdealGraded_injective (n : ℕ) :
    Function.Injective (ramificationGroupGradedToMaximalIdealGraded G S n) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToMaximalIdealGraded G S n).symm

/-- Every positive-depth ramification quotient `G_{n+1} / G_{n+2}` of a commutative local ring is
commutative. -/
instance instIsMulCommutativeRamificationGroupGradedNatCastSucc {G : Type*} [Group G]
    {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S] (n : ℕ) :
    IsMulCommutative (RamificationGroupGraded G S ((n : ℤ) + 1)) :=
  IsMulCommutative.of_comm fun a b ↦
    ramificationGroupGradedToMaximalIdealGraded_injective G S n (by rw [map_mul, map_mul, mul_comm])

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

variable (G S) [IsNoetherianRing S] [FaithfulSMul G S]

/-- **The positive-depth ramification groups are `p`-groups**, for `p` the residue characteristic,
when the action on the Noetherian local ring `S` is faithful and `G_i` is finite. In particular the
first ramification group `G_1` is a `p`-group when `G_1` is finite. -/
theorem isPGroup_ramificationGroup (p : ℕ) [CharP (ResidueField S) p] {i : ℤ} (hi : 0 < i)
    [Finite (ramificationGroup G S i)] :
    IsPGroup p (ramificationGroup G S i) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot_of_finite G S i
  exact isPGroup_ramificationGroup_of_eq_bot p hi (hN N le_rfl)

end Positive

/-! ### The uniformizer criterion for a separable residue extension -/

section Separable

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- Propagating congruence along a generator `π` of the maximal ideal: if `σ • π - π ∈ 𝔪 ^ (m + 1)`
and `σ • y - y ∈ 𝔪 ^ m` for every `y : S`, then `σ • w - w ∈ 𝔪 ^ (m + 1)` for every `w ∈ 𝔪`. -/
theorem smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer {π : S}
    (hπ : maximalIdeal S = Ideal.span {π}) {m : ℕ} {σ : G}
    (hπm : σ • π - π ∈ maximalIdeal S ^ (m + 1)) (hS : ∀ y : S, σ • y - y ∈ maximalIdeal S ^ m)
    {w : S} (hw : w ∈ maximalIdeal S) :
    σ • w - w ∈ maximalIdeal S ^ (m + 1) := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp (hπ ▸ hw)
  rw [smul_mul_sub_mul]
  refine add_mem (Ideal.mul_mem_right _ _ hπm) ?_
  rw [pow_succ']
  exact Ideal.mul_mem_mul (hπ ▸ Ideal.mem_span_singleton_self π) (hS y)

variable (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)]
  [SMulCommClass G R S] [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
include R

/-- **Propagation from the maximal ideal under a separable residue extension.** Let `G` act on a
local ring `S` by `R`-algebra automorphisms over a local ring `R` such that
`ResidueField S / ResidueField R` is separable, and let `I : Ideal S`. If an inertia element
`σ ∈ G_0` moves every element of `𝔪(S)` by an element of `I`, then `σ` lies in `I.inertia G`.
The residue class of `x` is a simple root of the reduction of some `g : R[X]`, and Taylor
expansion of `g` at `x` reads `σ (g x) - g x ≡ g' x (σ x - x)` modulo `𝔪(S) · (σ x - x)`. -/
theorem mem_inertia_of_forall_mem_maximalIdeal {I : Ideal S} {σ : G}
    (hσ : σ ∈ ramificationGroup G S 0) (hmax : ∀ w ∈ maximalIdeal S, σ • w - w ∈ I) :
    σ ∈ I.inertia G := by
  rw [Ideal.mem_inertia]
  intro x
  obtain ⟨g, hval, hder⟩ := exists_aeval_mem_maximalIdeal_isUnit_aeval_derivative (R := R) x
  obtain ⟨c, hc⟩ := binomExpansion (g.map (algebraMap R S)) x (σ • x - x)
  rw [add_sub_cancel, derivative_map] at hc
  simp only [eval_map, ← aeval_def, aeval_smul] at hc
  set u : S := aeval x (derivative g) + c * (σ • x - x)
  have hu : IsUnit u := by
    refine notMem_maximalIdeal.mp fun hu_mem ↦ notMem_maximalIdeal.mpr hder ?_
    simpa [u] using sub_mem hu_mem (Ideal.mul_mem_left _ c (mem_ramificationGroup_zero_iff.mp hσ x))
  refine (Ideal.unit_mul_mem_iff_mem _ hu).mp ?_
  rw [(by rw [hc]; ring : u * (σ • x - x) = σ • aeval x g - aeval x g)]
  exact hmax _ hval

/-- The inductive step of the uniformizer criterion: an element of `G_n` that moves a generator of
the maximal ideal by an element of `𝔪 ^ (n + 2)` lies in `G_{n+1}`. -/
private theorem mem_ramificationGroup_succ_of_smul_sub_mem {π : S}
    (hπ : maximalIdeal S = Ideal.span {π}) {n : ℕ} {σ : G} (hσ : σ ∈ ramificationGroup G S n)
    (hσπ : σ • π - π ∈ maximalIdeal S ^ (n + 2)) : σ ∈ ramificationGroup G S (n + 1 : ℕ) := by
  rw [ramificationGroup_natCast, Ideal.ramificationGroup_def]
  exact mem_inertia_of_forall_mem_maximalIdeal R
    (ramificationGroup_antitone G S (Int.natCast_nonneg n) hσ) fun _ hw ↦
      smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer hπ hσπ
        (mem_ramificationGroup_natCast_iff.mp hσ) hw

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

end DiscreteValuationRing

/-! ### Wild inertia as the Sylow subgroup of inertia -/

section Sylow

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
  [MulSemiringAction G S] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]

/-- **Wild inertia `G_1` as a Sylow `p`-subgroup of inertia `G_0`**, for a faithful action on a
Noetherian local ring `S` with finite `G_0` in prime residue characteristic `p` whenever the index
`[G_0 : G_1]` is prime to `p`. -/
noncomputable def ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    (hp : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    Sylow p (ramificationGroup G S 0) :=
  have : Finite (ramificationGroup G S 1) :=
    finite_ramificationGroup_of_le (by omega : (0 : ℤ) ≤ 1)
  ((isPGroup_ramificationGroup G S p (i := 1) one_pos).comap_subtype).toSylow hp

variable {G S}

/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` viewed inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    (hp : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    (ramificationGroupOneSylow G S p hp : Subgroup (ramificationGroup G S 0)) =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) :=
  (rfl)

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
theorem ramificationGroupOneSylow_normal (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    (hp : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    (ramificationGroupOneSylow G S p hp : Subgroup (ramificationGroup G S 0)).Normal := by
  rw [ramificationGroupOneSylow_coe]
  infer_instance

/-- **`G_1` is the only Sylow `p`-subgroup of `G_0`**: the Sylow subgroup
`TauCeti.IsLocalRing.ramificationGroupOneSylow` is normal. -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    (hp : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index)
    (Q : Sylow p (ramificationGroup G S 0)) : Q = ramificationGroupOneSylow G S p hp := by
  let _ : Unique (Sylow p (ramificationGroup G S 0)) :=
    Sylow.unique_of_normal _ (ramificationGroupOneSylow_normal p hp)
  exact Subsingleton.elim _ _

/-- The order of wild inertia `G_1` is the `p`-part of the order of inertia `G_0`, for a faithful
action on a Noetherian local ring `S` with finite `G_0` in prime residue characteristic `p` when
`[G_0 : G_1]` is prime to `p`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    (hp : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    Nat.card (ramificationGroup G S 1) =
      p ^ (Nat.card (ramificationGroup G S 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow G S p hp)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

/-- **Wild inertia is trivial if and only if `p` does not divide `#G_0`**, for a faithful action
on a Noetherian local ring `S` with finite `G_0` in prime residue characteristic `p` when
`[G_0 : G_1]` is prime to `p`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_natCard (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p]
    (hp : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    ramificationGroup G S 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G S 0) := by
  have hp' : p.Prime := Fact.out
  rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one p hp,
    pow_eq_one_iff_right hp'.ne_one, Nat.factorization_eq_zero_iff]
  simp only [hp', not_true_eq_false, false_or, Nat.card_pos.ne', or_false]

end Sylow

end IsLocalRing

end TauCeti
