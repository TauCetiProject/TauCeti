/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup.Basic
public import TauCeti.RingTheory.LocalRing.UnitFiltration
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Group.Irreducible.Lemmas
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.Ring
import TauCeti.GroupTheory.PGroup
import TauCeti.RingTheory.LocalRing.Basic
import TauCeti.RingTheory.LocalRing.Monogenic

/-!
# Graded quotients of the ramification filtration and tame/wild structure

Let a group `G` act by ring automorphisms on a commutative local ring `S` with maximal ideal `𝔪`
and residue field `k`, giving the lower ramification filtration
`G_i = TauCeti.IsLocalRing.ramificationGroup G S i` and successive quotients
`RamificationGroupGraded G S i = G_i / G_{i+1}`.

## General local rings (wild inertia)

At every positive depth `n + 1`, sending `σ ∈ G_{n+1}` to the map
`x ↦ [σ • x - x] ∈ 𝔪 ^ (n + 2) / 𝔪 ^ (n + 3)` defines a homomorphism
`G_{n+1} →* Multiplicative (S → MaximalIdealGraded S (n + 2))` with exact kernel `G_{n+2}`.
Because `𝔪` annihilates `MaximalIdealGraded S (n + 2)`, this already gives the structure of the
wild filtration for every commutative local ring, without a discrete-valuation or separability
hypothesis:

* Each `G_{n+1} / G_{n+2}` is abelian (`⁅G_{n+1}, G_{n+1}⁆ ≤ G_{n+2}`).
* In residue characteristic `p`, `G_{n+1} / G_{n+2}` has exponent `p` and is a `p`-group; when
  `S` is Noetherian, the action is faithful, and `G_i` is finite (`i > 0`), `G_i` is a `p`-group.
* In residue characteristic `0`, every finite `G_{n+1} / G_{n+2}` is trivial; when `S` is
  Noetherian, the action is faithful, and `G_i` is finite (`i > 0`), `G_i = ⊥`.

## Discrete valuation rings (uniformizer embeddings and tame structure)

When `B` is a discrete valuation ring with uniformizer `π`, an element `σ ∈ G_i` (`i : ℕ`) moves
`π` by a unique unit `u_σ ∈ U(B, i)` satisfying `π * u_σ = σ • π`. The class of `u_σ` in
`UnitFiltrationGraded B i = U(B, i) / U(B, i + 1)` is independent of `π`, multiplicative in `σ`,
and trivial on `G_{i+1}`, defining canonical homomorphisms:

* `ramificationGroupGradedToUnitFiltrationGraded : G_i / G_{i+1} →* U(B, i) / U(B, i + 1)`,
* `tameCharacter : G_0 →* (ResidueField B)ˣ` and
  `tameCharacterGraded : G_0 / G_1 →* (ResidueField B)ˣ`,
* `ramificationGroupGradedToResidueField : Additive (G_{n+1} / G_{n+2}) →+ ResidueField B`,
  sending `σ` with `σ • π - π = y * π ^ (n + 2)` to `residue B y`, scaling by
  `residue B a ^ (n + 1)` under `π' = π * a`, and transforming under conjugation by `σ ∈ G_0` by
  multiplication by `(tameCharacter σ) ^ (n + 1)`.

When `B` is a local `A`-algebra fixed by `G` with separable residue extension
`ResidueField B / ResidueField A`, Taylor expansion of a lifted minimal polynomial shows that for
every `i : ℕ` and `σ ∈ G_i`, membership `σ ∈ G_{i+1}` is decided on `π` alone:
`σ ∈ G_{i+1} ↔ σ • π - π ∈ 𝔪 ^ (i + 2)` (and by induction, for `σ ∈ G_0`,
`σ ∈ G_n ↔ σ • π - π ∈ 𝔪 ^ (n + 1)`). No completeness, finiteness of the residue field, or
finiteness of `B` over `A` is needed. Consequently all three graded homomorphisms above are
injective, and whenever the relevant quotient or inertia group is finite:

* `G_0 / G_1` is cyclic, of order prime to the residue characteristic `p` when `p` is prime.
* When the action is faithful and the residue characteristic is a prime `p`, `G_1` is the unique
  normal Sylow `p`-subgroup of `G_0`, of order `p ^ ((#G_0).factorization p)`, and `G_1 = ⊥`
  exactly when `p ∤ #G_0`.
* When the action is faithful and the residue characteristic is `0`, `G_1 = ⊥` and `G_0` itself
  is cyclic.

## Main definitions

* `TauCeti.IsLocalRing.ramificationGroupToMaximalIdealGradedMap`: the homomorphism
  `G_{n+1} →* Multiplicative (S → MaximalIdealGraded S (n + 2))` on any local ring.
* `TauCeti.IsLocalRing.uniformizerRatio`: the unit `u ∈ U(B, i)` with `π * u = σ • π`.
* `TauCeti.IsLocalRing.ramificationGroupToUnitFiltrationGraded` and
  `TauCeti.IsLocalRing.ramificationGroupGradedToUnitFiltrationGraded`: the uniformizer-independent
  graded homomorphisms `G_i →* U(B, i) / U(B, i + 1)` and `G_i / G_{i+1} →* U(B, i) / U(B, i + 1)`.
* `TauCeti.IsLocalRing.tameCharacter` and `TauCeti.IsLocalRing.tameCharacterGraded`: the
  uniformizer-independent depth-zero homomorphisms into `(ResidueField B)ˣ`.
* `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField`: the positive-depth additive
  coordinate `Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` attached to a uniformizer.
* `TauCeti.IsLocalRing.ramificationGroupOneSylow`: `G_1` as the Sylow `p`-subgroup of `G_0`.

## Main results

* `TauCeti.IsLocalRing.commutator_ramificationGroup_le`,
  `TauCeti.IsLocalRing.isPGroup_ramificationGroupGraded_natCast_succ`,
  `TauCeti.IsLocalRing.isPGroup_ramificationGroup`,
  `TauCeti.IsLocalRing.ramificationGroup_eq_bot_of_charZero`: wild-filtration structure over any
  local ring.
* `TauCeti.IsLocalRing.ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible`,
  `TauCeti.IsLocalRing.tameCharacter_eq_of_irreducible`,
  `TauCeti.IsLocalRing.tameCharacterGraded_eq_of_irreducible`: independence of uniformizer.
* `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_of_smul_sub_eq`,
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_change`,
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_conj`: explicit formula,
  change of uniformizer, and conjugation action by `G_0`.
* `TauCeti.IsLocalRing.mem_ramificationGroup_succ_iff_smul_sub_mem` and
  `TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem`: for separable residue
  extension, membership in `G_{i+1}` (and `G_n`) is decided at a uniformizer.
* `TauCeti.IsLocalRing.ramificationGroupGradedToUnitFiltrationGraded_injective`,
  `TauCeti.IsLocalRing.tameCharacterGraded_injective`,
  `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_injective`: injectivity of all graded
  embeddings for separable residue extensions.
* `TauCeti.IsLocalRing.isCyclic_ramificationGroupGraded_zero`,
  `TauCeti.IsLocalRing.not_dvd_index_ramificationGroup_one`,
  `TauCeti.IsLocalRing.eq_ramificationGroupOneSylow`,
  `TauCeti.IsLocalRing.natCard_ramificationGroup_one`,
  `TauCeti.IsLocalRing.ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`,
  `TauCeti.IsLocalRing.isCyclic_ramificationGroup_zero_of_charZero`: tame and wild group structure.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5, 7, and 9, and
  Corollaries 1–4.
-/

public section
noncomputable section

open IsLocalRing Polynomial

namespace TauCeti

namespace IsLocalRing

/-! ### Positive-depth structure on a general local ring -/

section LocalRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- For `σ ∈ G_k` (`k : ℕ`) and any unit `v` of a local ring `S`, the ratio `(σ • v) * v⁻¹` lies
one step deeper in the unit filtration, in `U(S, k + 1)`. -/
theorem smul_mul_inv_mem_unitFiltration_succ {k : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S (k : ℤ)) (v : Sˣ) :
    Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom v * v⁻¹ ∈
      unitFiltration S (k + 1) := by
  rw [mem_unitFiltration_iff]
  have hsplit : ((Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom v * v⁻¹ : Sˣ) : S) - 1 =
      (σ • (v : S) - (v : S)) * ((v⁻¹ : Sˣ) : S) := by
    rw [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulSemiringAction.toRingHom_apply]
    calc σ • (v : S) * ((v⁻¹ : Sˣ) : S) - 1
        = σ • (v : S) * ((v⁻¹ : Sˣ) : S) - (v : S) * ((v⁻¹ : Sˣ) : S) := by rw [Units.mul_inv]
      _ = (σ • (v : S) - (v : S)) * ((v⁻¹ : Sˣ) : S) := by ring
  rw [hsplit]
  exact Ideal.mul_mem_right _ _ (mem_ramificationGroup_natCast_iff.mp hσ (v : S))

/-- An element of `G_k` (`k : ℕ`) moves every element of `𝔪 ^ 2` by an element of `𝔪 ^ (k + 2)`. -/
theorem smul_sub_mem_maximalIdeal_pow_add_two {k : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S (k : ℤ)) {y : S} (hy : y ∈ maximalIdeal S ^ 2) :
    σ • y - y ∈ maximalIdeal S ^ (k + 2) := by
  rw [pow_two] at hy
  refine Submodule.mul_induction_on hy (fun a ha b hb ↦ ?_) (fun x z hx hz ↦ ?_)
  · have hsplit : σ • (a * b) - a * b = (σ • a - a) * (σ • b) + a * (σ • b - b) := by
      rw [smul_mul']
      ring
    rw [hsplit]
    have hb' : σ • b ∈ maximalIdeal S := by
      simpa only [pow_one] using
        (smul_mem_maximalIdeal_pow_iff σ (n := 1)).mpr (by simpa only [pow_one] using hb)
    have h1 : (σ • a - a) * (σ • b) ∈ maximalIdeal S ^ (k + 2) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_add, pow_one]
      exact Ideal.mul_mem_mul (mem_ramificationGroup_natCast_iff.mp hσ a) hb'
    have h2 : a * (σ • b - b) ∈ maximalIdeal S ^ (k + 2) := by
      rw [show k + 2 = 1 + (k + 1) by omega, pow_add, pow_one]
      exact Ideal.mul_mem_mul ha (mem_ramificationGroup_natCast_iff.mp hσ b)
    exact add_mem h1 h2
  · have hsplit : σ • (x + z) - (x + z) = (σ • x - x) + (σ • z - z) := by
      rw [smul_add]
      ring
    rw [hsplit]
    exact add_mem hx hz

variable (G S) in
/-- At positive depth `n + 1`, sending `σ ∈ G_{n+1}` to the map
`x ↦ [σ • x - x] ∈ 𝔪 ^ (n + 2) / 𝔪 ^ (n + 3)` is a group homomorphism with exact kernel `G_{n+2}`.
This holds for every commutative local ring without a discrete-valuation or separability
hypothesis. -/
def ramificationGroupToMaximalIdealGradedMap (n : ℕ) :
    ramificationGroup G S ((n : ℤ) + 1) →* Multiplicative (S → MaximalIdealGraded S (n + 2)) where
  toFun σ := Multiplicative.ofAdd fun x ↦
    Submodule.Quotient.mk ⟨(σ : G) • x - x, by
      have hσ := mem_ramificationGroup_natCast_iff (n := n + 1).mp
        (by simpa only [Nat.cast_add, Nat.cast_one] using σ.2)
      exact hσ x⟩
  map_one' := by
    rw [← ofAdd_zero]
    refine congrArg Multiplicative.ofAdd (funext fun x ↦ ?_)
    have h0 : (⟨(1 : G) • x - x, by simp⟩ : (maximalIdeal S ^ (n + 2) : Ideal S)) = 0 := by
      ext
      simp
    simpa [Pi.zero_apply] using congrArg Submodule.Quotient.mk h0
  map_mul' σ τ := by
    rw [← ofAdd_add]
    refine congrArg Multiplicative.ofAdd (funext fun x ↦ ?_)
    rw [Pi.add_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq,
      Submodule.mem_smul_top_iff (I := maximalIdeal S)
        (maximalIdeal S ^ (n + 2) : Submodule S S), smul_eq_mul, ← pow_succ']
    have hσ : (σ : G) ∈ ramificationGroup G S ((n + 1 : ℕ) : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using σ.2
    have hτ : (τ : G) ∈ ramificationGroup G S ((n + 1 : ℕ) : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using τ.2
    have hτx : (τ : G) • x - x ∈ maximalIdeal S ^ 2 :=
      Ideal.pow_le_pow_right (by omega : 2 ≤ n + 2) (mem_ramificationGroup_natCast_iff.mp hτ x)
    have hmove : (σ : G) • ((τ : G) • x - x) - ((τ : G) • x - x) ∈ maximalIdeal S ^ (n + 3) :=
      smul_sub_mem_maximalIdeal_pow_add_two hσ hτx
    convert hmove using 1
    simp only [Submodule.coe_sub, Submodule.coe_add, Subgroup.coe_mul, mul_smul, smul_sub]
    ring

/-- Evaluating `ramificationGroupToMaximalIdealGradedMap` on `σ` sends `x` to the class of
`σ • x - x` in `𝔪 ^ (n + 2) / 𝔪 ^ (n + 3)`. -/
@[simp]
theorem ramificationGroupToMaximalIdealGradedMap_apply (n : ℕ)
    (σ : ramificationGroup G S ((n : ℤ) + 1)) :
    ramificationGroupToMaximalIdealGradedMap G S n σ =
      Multiplicative.ofAdd fun x : S ↦ Submodule.Quotient.mk
        ⟨(σ : G) • x - x,
          mem_ramificationGroup_natCast_iff (n := n + 1).mp
            (by simpa only [Nat.cast_add, Nat.cast_one] using σ.2) x⟩ :=
  (rfl)

variable (G S) in
/-- The kernel of `ramificationGroupToMaximalIdealGradedMap G S n` is `G_{n+2}` inside `G_{n+1}`. -/
theorem ker_ramificationGroupToMaximalIdealGradedMap (n : ℕ) :
    (ramificationGroupToMaximalIdealGradedMap G S n).ker =
      (ramificationGroup G S ((n : ℤ) + 2)).subgroupOf (ramificationGroup G S ((n : ℤ) + 1)) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hcast : ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, mem_ramificationGroup_natCast_iff, ramificationGroupToMaximalIdealGradedMap_apply,
    ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, funext_iff]
  refine forall_congr' fun x ↦ ?_
  rw [Pi.zero_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_top_iff (I := maximalIdeal S)
      (maximalIdeal S ^ (n + 2) : Submodule S S), smul_eq_mul, ← pow_succ']

variable (G S) in
/-- **Positive-depth successive ramification quotients are abelian** over any commutative local
ring: every commutator of `G_{n+1}` lies in `G_{n+2}`. -/
theorem commutator_ramificationGroup_le (n : ℕ) :
    ⁅ramificationGroup G S ((n : ℤ) + 1), ramificationGroup G S ((n : ℤ) + 1)⁆ ≤
      ramificationGroup G S ((n : ℤ) + 2) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  let a' : ramificationGroup G S ((n : ℤ) + 1) := ⟨a, ha⟩
  let b' : ramificationGroup G S ((n : ℤ) + 1) := ⟨b, hb⟩
  have hmem : a' * b' * a'⁻¹ * b'⁻¹ ∈ (ramificationGroupToMaximalIdealGradedMap G S n).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm,
      mul_inv_cancel]
  rw [ker_ramificationGroupToMaximalIdealGradedMap, Subgroup.mem_subgroupOf] at hmem
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, a', b'] using hmem

variable (G S) in
/-- In residue characteristic `p`, the `p`-th power of an element of `G_{n+1}` lies in `G_{n+2}`,
over any commutative local ring. -/
theorem pow_mem_ramificationGroup_of_charP (p : ℕ) [CharP (ResidueField S) p] (n : ℕ)
    {σ : G} (hσ : σ ∈ ramificationGroup G S ((n : ℤ) + 1)) :
    σ ^ p ∈ ramificationGroup G S ((n : ℤ) + 2) := by
  have hp : (p : S) ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero (ResidueField S) p
  have hmem : (⟨σ, hσ⟩ : ramificationGroup G S ((n : ℤ) + 1)) ^ p ∈
      (ramificationGroupToMaximalIdealGradedMap G S n).ker := by
    rw [MonoidHom.mem_ker, map_pow, ramificationGroupToMaximalIdealGradedMap_apply, ← ofAdd_nsmul,
      ← ofAdd_zero]
    refine congrArg Multiplicative.ofAdd (funext fun x ↦ ?_)
    rw [Pi.smul_apply, Pi.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_top_iff (I := maximalIdeal S)
        (maximalIdeal S ^ (n + 2) : Submodule S S), smul_eq_mul]
    simpa only [Submodule.coe_smul_of_tower, nsmul_eq_mul] using
      Ideal.mul_mem_mul hp (mem_ramificationGroup_natCast_iff (n := n + 1).mp
        (by simpa only [Nat.cast_add, Nat.cast_one] using hσ) x)
  rw [ker_ramificationGroupToMaximalIdealGradedMap, Subgroup.mem_subgroupOf] at hmem
  simpa only [Subgroup.coe_pow] using hmem

variable (G S) in
/-- At every positive depth `n + 1`, the graded ramification quotient `G_{n+1} / G_{n+2}` is a
`p`-group for the residue characteristic `p`, over any commutative local ring without finiteness
or separability assumptions. -/
theorem isPGroup_ramificationGroupGraded_natCast_succ (p : ℕ) [CharP (ResidueField S) p] (n : ℕ) :
    IsPGroup p (RamificationGroupGraded G S ((n : ℤ) + 1)) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa only [add_assoc, one_add_one_eq_two, Subgroup.coe_pow] using
      pow_mem_ramificationGroup_of_charP G S p n σ.2

/-- Over a Noetherian local ring with a faithful action, if `G_i` is finite, then `G_k = ⊥` for all
sufficiently large `k`. -/
private theorem exists_forall_ramificationGroup_eq_bot_of_finite [IsNoetherianRing S]
    [FaithfulSMul G S] (i : ℤ) [Finite (ramificationGroup G S i)] :
    ∃ N : ℕ, ∀ k : ℤ, i + N ≤ k → ramificationGroup G S k = ⊥ := by
  have hanti : Antitone fun d : ℕ ↦ ramificationGroup G S (i + d) :=
    fun _ _ h ↦ ramificationGroup_antitone G S (by omega)
  have : Finite ((fun d : ℕ ↦ ramificationGroup G S (i + d)) 0) := by
    simpa using ‹Finite (ramificationGroup G S i)›
  obtain ⟨N, hN⟩ := TauCeti.Subgroup.exists_forall_eq_iInf_of_antitone _ hanti
  have hiInf : ⨅ d : ℕ, ramificationGroup G S (i + d) = ⊥ := by
    rw [← iInf_ramificationGroup_eq_bot G S]
    refine le_antisymm ?_ (le_iInf fun d ↦ iInf_le _ _)
    refine le_iInf fun j ↦ (iInf_le _ (j - i).toNat).trans (ramificationGroup_antitone G S ?_)
    omega
  refine ⟨N, fun k hk ↦ ?_⟩
  have hkeq : i + ((k - i).toNat : ℤ) = k := by omega
  have h := hN (k - i).toNat (by omega)
  rwa [hkeq, hiInf] at h

variable (G S) in
/-- **Positive-depth ramification groups are `p`-groups** in residue characteristic `p`, over any
Noetherian local ring on which `G` acts faithfully with `G_i` finite (`0 < i`). Neither a
discrete valuation nor a separable residue extension is required. -/
theorem isPGroup_ramificationGroup (p : ℕ) [IsNoetherianRing S] [CharP (ResidueField S) p]
    [FaithfulSMul G S] {i : ℤ} (hi : 0 < i) [Finite (ramificationGroup G S i)] :
    IsPGroup p (ramificationGroup G S i) := by
  obtain ⟨N, hvanish⟩ := exists_forall_ramificationGroup_eq_bot_of_finite (G := G) (S := S) i
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
  suffices ∀ d m : ℕ, ((j : ℤ) + 1) + N ≤ ((m : ℤ) + 1) + d →
      IsPGroup p (ramificationGroup G S ((m : ℤ) + 1)) from
    this N j (by omega)
  intro d
  induction d with
  | zero =>
    intro m hm
    rw [hvanish _ (by omega)]
    exact IsPGroup.of_bot
  | succ d ih =>
    intro m hm
    have hsucc : IsPGroup p (ramificationGroup G S (((m + 1 : ℕ) : ℤ) + 1)) :=
      ih (m + 1) (by push_cast; omega)
    have hsucc' : IsPGroup p (ramificationGroup G S (((m : ℤ) + 1) + 1)) := by
      rw [Int.natCast_succ] at hsucc
      exact hsucc
    exact IsPGroup.of_subgroup_of_quotient hsucc'.comap_subtype
      (isPGroup_ramificationGroupGraded_natCast_succ G S p m)

variable (G S) in
/-- In residue characteristic zero, every finite positive-depth graded ramification quotient
`G_{n+1} / G_{n+2}` is trivial, over any commutative local ring. -/
theorem subsingleton_ramificationGroupGraded_natCast_succ [CharZero (ResidueField S)] (n : ℕ)
    [Finite (RamificationGroupGraded G S ((n : ℤ) + 1))] :
    Subsingleton (RamificationGroupGraded G S ((n : ℤ) + 1)) := by
  let φ : RamificationGroupGraded G S ((n : ℤ) + 1) →*
      Multiplicative (S → MaximalIdealGraded S (n + 2)) :=
    QuotientGroup.lift _ (ramificationGroupToMaximalIdealGradedMap G S n) <| by
      rw [add_assoc, one_add_one_eq_two, ← ker_ramificationGroupToMaximalIdealGradedMap]
  have hφ : Function.Injective φ :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr
      (by rw [add_assoc, one_add_one_eq_two, ker_ramificationGroupToMaximalIdealGradedMap])
  refine ⟨fun a b ↦ ?_⟩
  suffices ∀ x : RamificationGroupGraded G S ((n : ℤ) + 1), x = 1 by
    rw [this a, this b]
  intro x
  have hordpos : 0 < orderOf x := orderOf_pos x
  have hunit : IsUnit ((orderOf x : ℕ) : S) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    exact Nat.cast_ne_zero.mpr hordpos.ne'
  apply hφ
  rw [map_one]
  have hpow : φ x ^ orderOf x = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  set f : S → MaximalIdealGraded S (n + 2) := Multiplicative.toAdd (φ x)
  have hf : φ x = Multiplicative.ofAdd f := rfl
  rw [hf, ← ofAdd_nsmul, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff] at hpow
  rw [hf, ← ofAdd_zero]
  refine congrArg Multiplicative.ofAdd (funext fun s ↦ ?_)
  have hs : ((orderOf x : ℕ) : S) • f s = 0 := by
    simpa only [Pi.smul_apply, Pi.zero_apply, natCast_zsmul, Nat.cast_smul_eq_nsmul] using
      congrFun hpow s
  obtain ⟨u, hu⟩ := hunit
  calc f s = ((u⁻¹ : Sˣ) : S) • ((u : S) • f s) := by
        rw [smul_smul, Units.inv_mul, one_smul]
    _ = ((u⁻¹ : Sˣ) : S) • (((orderOf x : ℕ) : S) • f s) := by rw [hu]
    _ = 0 := by rw [hs, smul_zero]

variable (G S) in
/-- **In residue characteristic zero, every finite positive-depth ramification group is trivial**
for a faithful action on a Noetherian local ring. -/
theorem ramificationGroup_eq_bot_of_charZero [IsNoetherianRing S] [CharZero (ResidueField S)]
    [FaithfulSMul G S] {i : ℤ} (hi : 0 < i) [Finite (ramificationGroup G S i)] :
    ramificationGroup G S i = ⊥ := by
  obtain ⟨N, hvanish⟩ := exists_forall_ramificationGroup_eq_bot_of_finite (G := G) (S := S) i
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
  suffices ∀ d m : ℕ, j ≤ m → ((j : ℤ) + 1) + N ≤ ((m : ℤ) + 1) + d →
      ramificationGroup G S ((m : ℤ) + 1) = ⊥ from
    this N j le_rfl (by omega)
  intro d
  induction d with
  | zero =>
    intro m _ hm
    exact hvanish _ (by omega)
  | succ d ih =>
    intro m hjm hm
    have hfin : Finite (ramificationGroup G S ((m : ℤ) + 1)) :=
      Finite.of_injective
        (Subgroup.inclusion (ramificationGroup_antitone G S (by omega : (j : ℤ) + 1 ≤ (m : ℤ) + 1)))
        (Subgroup.inclusion_injective _)
    have hsub := subsingleton_ramificationGroupGraded_natCast_succ G S m
    have hnext : ramificationGroup G S (((m : ℤ) + 1) + 1) = ⊥ := by
      simpa only [Nat.cast_add, Nat.cast_one] using ih (m + 1) (by omega) (by push_cast; omega)
    rw [eq_bot_iff]
    intro σ hσ
    have hq : (QuotientGroup.mk ⟨σ, hσ⟩ : RamificationGroupGraded G S ((m : ℤ) + 1)) = 1 :=
      Subsingleton.elim _ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hnext] at hq
    exact hq

variable (G S) in
/-- In residue characteristic zero, a faithful action with finite first ramification group on a
Noetherian local ring has trivial wild inertia `G_1 = ⊥`. -/
theorem ramificationGroup_one_eq_bot_of_charZero [IsNoetherianRing S] [CharZero (ResidueField S)]
    [FaithfulSMul G S] [Finite (ramificationGroup G S 1)] :
    ramificationGroup G S 1 = ⊥ :=
  ramificationGroup_eq_bot_of_charZero G S (i := 1) one_pos

end LocalRing

/-! ### Uniformizer-ratio graded homomorphisms on a discrete valuation ring -/

section DiscreteValuationRing

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [MulSemiringAction G B]

omit [IsDomain B] [IsDiscreteValuationRing B] in
/-- An automorphism of a discrete valuation ring carries a uniformizer to a uniformizer. -/
private theorem irreducible_smul {π : B} (hπ : Irreducible π) (σ : G) :
    Irreducible (σ • π) :=
  hπ.map (MulSemiringAction.toRingAut G B σ).toMulEquiv

omit [IsDomain B] [IsDiscreteValuationRing B] in
/-- Reindexing `ramificationGroup` along an equality of integer indices. -/
private def ramificationGroupCongr {i j : ℤ} (h : i = j) :
    ramificationGroup G B i ≃* ramificationGroup G B j :=
  MulEquiv.subgroupCongr (congrArg (ramificationGroup G B) h)

omit [IsDomain B] [IsDiscreteValuationRing B] in
/-- Reindexing `RamificationGroupGraded` along an equality of integer indices. -/
private def ramificationGroupGradedCongr {i j : ℤ} (h : i = j) :
    RamificationGroupGraded G B i ≃* RamificationGroupGraded G B j :=
  QuotientGroup.congr
    ((ramificationGroup G B (i + 1)).subgroupOf (ramificationGroup G B i))
    ((ramificationGroup G B (j + 1)).subgroupOf (ramificationGroup G B j))
    (ramificationGroupCongr h) <| by
      subst h
      ext x
      exact ⟨fun ⟨_, hy, hyx⟩ ↦ hyx ▸ hy, fun hx ↦ ⟨x, hx, rfl⟩⟩

variable (G) in
/-- For `σ ∈ G_i` (`i : ℕ`) and a uniformizer `π` of a discrete valuation ring `B`, the unique
unit `u` with `π * u = σ • π`, viewed in `U(B, i)`. -/
def uniformizerRatio (i : ℕ) {π : B} (hπ : Irreducible π)
    (σ : ramificationGroup G B (i : ℤ)) : unitFiltration B i :=
  ⟨TauCeti.uniformizerChangeUnit π ((σ : G) • π) hπ (irreducible_smul hπ (σ : G)), by
    rw [mem_unitFiltration_iff, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    have hmem : (σ : G) • π - π ∈ maximalIdeal B ^ (i + 1) :=
      mem_ramificationGroup_natCast_iff.mp σ.2 π
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ'] at hmem
    have hmul : (σ : G) • π - π =
        π * ((TauCeti.uniformizerChangeUnit π ((σ : G) • π) hπ
          (irreducible_smul hπ (σ : G)) : B) - 1) := by
      rw [mul_sub, mul_one, TauCeti.mul_uniformizerChangeUnit]
    rw [hmul] at hmem
    exact (mul_dvd_mul_iff_left hπ.ne_zero).mp hmem⟩

/-- The defining equation `π * uniformizerRatio G i hπ σ = σ • π`. -/
@[simp]
theorem mul_uniformizerRatio (i : ℕ) {π : B} (hπ : Irreducible π)
    (σ : ramificationGroup G B (i : ℤ)) :
    π * ((uniformizerRatio G i hπ σ : Bˣ) : B) = (σ : G) • π :=
  TauCeti.mul_uniformizerChangeUnit π ((σ : G) • π) hπ (irreducible_smul hπ (σ : G))

/-- The underlying ring element of `uniformizerRatio G i hπ σ` is uniquely characterized by
`π * y = σ • π`. -/
theorem coe_uniformizerRatio_eq_of_mul_eq (i : ℕ) {π : B} (hπ : Irreducible π)
    (σ : ramificationGroup G B (i : ℤ)) {y : B} (hy : π * y = (σ : G) • π) :
    ((uniformizerRatio G i hπ σ : Bˣ) : B) = y :=
  mul_left_cancel₀ hπ.ne_zero (by rw [mul_uniformizerRatio, hy])

variable (G) in
/-- The **quotient homomorphism** `G_i →* U(B, i) / U(B, i + 1)` attached to a uniformizer `π`,
carrying `σ` to the class of `uniformizerRatio G i hπ σ`. It does not depend on `π`
(`TauCeti.IsLocalRing.ramificationGroupToUnitFiltrationGraded_eq_of_irreducible`) and kills
`G_{i+1}`, descending to `TauCeti.IsLocalRing.ramificationGroupGradedToUnitFiltrationGraded`. -/
def ramificationGroupToUnitFiltrationGraded (i : ℕ) {π : B} (hπ : Irreducible π) :
    ramificationGroup G B (i : ℤ) →* UnitFiltrationGraded B i :=
  MonoidHom.mk' (fun σ ↦ QuotientGroup.mk (uniformizerRatio G i hπ σ)) <| by
    intro σ τ
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf, ← Subgroup.inv_mem_iff]
    let uσ : Bˣ := uniformizerRatio G i hπ σ
    let uτ : Bˣ := uniformizerRatio G i hπ τ
    let uστ : Bˣ := uniformizerRatio G i hπ (σ * τ)
    have hrel : uστ = uσ * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom uτ := by
      apply Units.ext
      apply mul_left_cancel₀ hπ.ne_zero
      rw [mul_uniformizerRatio, Subgroup.coe_mul, mul_smul, ← mul_uniformizerRatio i hπ τ,
        smul_mul', ← mul_uniformizerRatio i hπ σ, Units.val_mul, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulSemiringAction.toRingHom_apply,
        mul_assoc]
    have hdiff : (((uniformizerRatio G i hπ (σ * τ))⁻¹ *
          (uniformizerRatio G i hπ σ * uniformizerRatio G i hπ τ) :
          unitFiltration B i) : Bˣ)⁻¹ =
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom uτ * uτ⁻¹ := by
      simp only [Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev, inv_inv]
      calc uτ⁻¹ * uσ⁻¹ * uστ
          = uτ⁻¹ * uσ⁻¹ *
              (uσ * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom uτ) := by
            rw [hrel]
        _ = Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom uτ * uτ⁻¹ := by
            rw [mul_assoc uτ⁻¹ uσ⁻¹, inv_mul_cancel_left, mul_comm]
    rw [hdiff]
    exact smul_mul_inv_mem_unitFiltration_succ σ.2 uτ

/-- Evaluating `ramificationGroupToUnitFiltrationGraded` on `σ` yields the class of
`uniformizerRatio G i hπ σ`. -/
@[simp]
theorem ramificationGroupToUnitFiltrationGraded_apply (i : ℕ) {π : B} (hπ : Irreducible π)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupToUnitFiltrationGraded G i hπ σ =
      QuotientGroup.mk (uniformizerRatio G i hπ σ) :=
  (rfl)

variable (G) in
/-- The quotient homomorphism `G_i →* U(B, i) / U(B, i + 1)` does not depend on the choice of
uniformizer: two uniformizers differ by a unit `a`, and `σ ∈ G_i` moves `a` inside `U(B, i + 1)`. -/
theorem ramificationGroupToUnitFiltrationGraded_eq_of_irreducible (i : ℕ) {π π' : B}
    (hπ : Irreducible π) (hπ' : Irreducible π') :
    ramificationGroupToUnitFiltrationGraded G i hπ =
      ramificationGroupToUnitFiltrationGraded G i hπ' := by
  let a : Bˣ := TauCeti.uniformizerChangeUnit π π' hπ hπ'
  ext σ
  rw [ramificationGroupToUnitFiltrationGraded_apply, ramificationGroupToUnitFiltrationGraded_apply,
    QuotientGroup.eq, Subgroup.mem_subgroupOf]
  let uσ : Bˣ := uniformizerRatio G i hπ σ
  let uσ' : Bˣ := uniformizerRatio G i hπ' σ
  have hπa : π * (a : B) = π' := TauCeti.mul_uniformizerChangeUnit π π' hπ hπ'
  have hrel : uσ' = uσ *
      (Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a * a⁻¹) := by
    apply Units.ext
    apply mul_left_cancel₀ hπ'.ne_zero
    rw [mul_uniformizerRatio, ← hπa, smul_mul', ← mul_uniformizerRatio i hπ σ,
      Units.val_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, MulSemiringAction.toRingHom_apply]
    have ha : (a : B) * ((a⁻¹ : Bˣ) : B) = 1 := Units.mul_inv a
    calc π * (uσ : B) * ((σ : G) • (a : B))
        = π * (uσ : B) * ((σ : G) • (a : B)) * ((a : B) * ((a⁻¹ : Bˣ) : B)) := by
          rw [ha, mul_one]
      _ = π * (a : B) * ((uσ : B) * (((σ : G) • (a : B)) * ((a⁻¹ : Bˣ) : B))) := by ring
  have hdiff : (((uniformizerRatio G i hπ σ)⁻¹ * uniformizerRatio G i hπ' σ :
        unitFiltration B i) : Bˣ) =
      Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a * a⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc uσ⁻¹ * uσ'
        = uσ⁻¹ * (uσ *
            (Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a * a⁻¹)) := by
          rw [hrel]
      _ = Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a * a⁻¹ := by
          rw [inv_mul_cancel_left]
  rw [hdiff]
  exact smul_mul_inv_mem_unitFiltration_succ σ.2 a

/-- An element of `G_i` lies in the kernel of `ramificationGroupToUnitFiltrationGraded G i hπ`
exactly when it moves the uniformizer `π` by an element of `𝔪 ^ (i + 2)`. -/
theorem mem_ker_ramificationGroupToUnitFiltrationGraded_iff (i : ℕ) {π : B} (hπ : Irreducible π)
    (σ : ramificationGroup G B (i : ℤ)) :
    σ ∈ (ramificationGroupToUnitFiltrationGraded G i hπ).ker ↔
      (σ : G) • π - π ∈ maximalIdeal B ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToUnitFiltrationGraded_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, mem_unitFiltration_iff, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
    pow_succ' π (i + 1)]
  have hmul : (σ : G) • π - π = π * (((uniformizerRatio G i hπ σ : Bˣ) : B) - 1) := by
    rw [mul_sub, mul_one, mul_uniformizerRatio]
  rw [hmul, mul_dvd_mul_iff_left hπ.ne_zero]

/-- `G_{i+1}` lies in the kernel of `ramificationGroupToUnitFiltrationGraded G i hπ`. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (i : ℕ) {π : B} (hπ : Irreducible π) :
    (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) ≤
      (ramificationGroupToUnitFiltrationGraded G i hπ).ker := by
  intro σ hσ
  rw [mem_ker_ramificationGroupToUnitFiltrationGraded_iff]
  rw [Subgroup.mem_subgroupOf] at hσ
  have hσ' : (σ : G) ∈ ramificationGroup G B ((i + 1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hσ
  exact mem_ramificationGroup_natCast_iff.mp hσ' π

variable (G) in
/-- The **graded ramification homomorphism** `θ_i : G_i / G_{i+1} →* U(B, i) / U(B, i + 1)`
induced by `σ ↦ σ • π / π`. It is independent of the choice of uniformizer `π`, and is injective
when the residue extension is separable
(`TauCeti.IsLocalRing.ramificationGroupGradedToUnitFiltrationGraded_injective`). -/
def ramificationGroupGradedToUnitFiltrationGraded (i : ℕ) {π : B} (hπ : Irreducible π) :
    RamificationGroupGraded G B (i : ℤ) →* UnitFiltrationGraded B i :=
  QuotientGroup.lift _ (ramificationGroupToUnitFiltrationGraded G i hπ)
    (ramificationGroup_succ_subgroupOf_le_ker i hπ)

/-- Evaluating `ramificationGroupGradedToUnitFiltrationGraded` on a coset `QuotientGroup.mk σ`. -/
@[simp]
theorem ramificationGroupGradedToUnitFiltrationGraded_mk (i : ℕ) {π : B} (hπ : Irreducible π)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToUnitFiltrationGraded G i hπ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio G i hπ σ) :=
  (rfl)

variable (G) in
/-- The graded ramification homomorphism `G_i / G_{i+1} →* U(B, i) / U(B, i + 1)` does not depend
on the choice of uniformizer. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible (i : ℕ) {π π' : B}
    (hπ : Irreducible π) (hπ' : Irreducible π') :
    ramificationGroupGradedToUnitFiltrationGraded G i hπ =
      ramificationGroupGradedToUnitFiltrationGraded G i hπ' := by
  refine MonoidHom.ext fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    exact DFunLike.congr_fun
      (ramificationGroupToUnitFiltrationGraded_eq_of_irreducible G i hπ hπ') σ

/-! ### The tame character -/

variable (G) in
/-- The **tame character** `G_0 →* (ResidueField B)ˣ`: the depth-zero quotient homomorphism
composed with `U(B, 0) / U(B, 1) ≃* (ResidueField B)ˣ`. It sends `σ ∈ G_0` to the residue of
the unique unit `u` with `π * u = σ • π`, does not depend on `π`, and kills `G_1`. -/
def tameCharacter {π : B} (hπ : Irreducible π) :
    ramificationGroup G B (0 : ℤ) →* (ResidueField B)ˣ :=
  (unitFiltrationGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
    (ramificationGroupToUnitFiltrationGraded G 0 hπ)

/-- Evaluating `tameCharacter` on `σ` reduces `uniformizerRatio G 0 hπ σ` modulo `𝔪`. -/
@[simp]
theorem tameCharacter_apply {π : B} (hπ : Irreducible π) (σ : ramificationGroup G B (0 : ℤ)) :
    tameCharacter G hπ σ =
      Units.map (residue B).toMonoidHom (uniformizerRatio G 0 hπ σ : Bˣ) := by
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToUnitFiltrationGraded_apply (i := 0),
    unitFiltrationGradedZeroEquivResidueFieldUnits_mk]

/-- If `π * y = σ • π` for `σ ∈ G_0`, then the tame character sends `σ` to the residue of `y`. -/
theorem coe_tameCharacter_of_mul_eq_smul {π : B} (hπ : Irreducible π)
    (σ : ramificationGroup G B (0 : ℤ)) {y : B} (hy : π * y = (σ : G) • π) :
    (tameCharacter G hπ σ : ResidueField B) = residue B y := by
  rw [tameCharacter_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    coe_uniformizerRatio_eq_of_mul_eq 0 hπ σ hy]

variable (G) in
/-- The tame character does not depend on the choice of uniformizer. -/
theorem tameCharacter_eq_of_irreducible {π π' : B} (hπ : Irreducible π) (hπ' : Irreducible π') :
    tameCharacter G hπ = tameCharacter G hπ' := by
  rw [tameCharacter, tameCharacter,
    ramificationGroupToUnitFiltrationGraded_eq_of_irreducible G 0 hπ hπ']

variable (G) in
/-- The **graded tame character** `G_0 / G_1 →* (ResidueField B)ˣ`. It does not depend on the
choice of uniformizer, and is injective when the residue extension is separable
(`TauCeti.IsLocalRing.tameCharacterGraded_injective`). -/
def tameCharacterGraded {π : B} (hπ : Irreducible π) :
    RamificationGroupGraded G B (0 : ℤ) →* (ResidueField B)ˣ :=
  (unitFiltrationGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
    (ramificationGroupGradedToUnitFiltrationGraded G 0 hπ)

/-- Evaluating `tameCharacterGraded` on a coset `QuotientGroup.mk σ`. -/
@[simp]
theorem tameCharacterGraded_mk {π : B} (hπ : Irreducible π)
    (σ : ramificationGroup G B (0 : ℤ)) :
    tameCharacterGraded G hπ (QuotientGroup.mk σ) = tameCharacter G hπ σ :=
  (rfl)

variable (G) in
/-- The graded tame character does not depend on the choice of uniformizer. -/
theorem tameCharacterGraded_eq_of_irreducible {π π' : B}
    (hπ : Irreducible π) (hπ' : Irreducible π') :
    tameCharacterGraded G hπ = tameCharacterGraded G hπ' := by
  rw [tameCharacterGraded, tameCharacterGraded,
    ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible G 0 hπ hπ']

/-! ### Positive-depth additive residue coordinates -/

variable (G) in
/-- The positive-depth additive homomorphism
`Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` determined by a uniformizer `π`, sending an
element `τ ∈ G_{n+1}` with `τ • π - π = y * π ^ (n + 2)` to `residue B y`. It is injective when
the residue extension is separable
(`TauCeti.IsLocalRing.ramificationGroupGradedToResidueField_injective`). -/
def ramificationGroupGradedToResidueField (n : ℕ) (π : B) (hπ : Irreducible π) :
    Additive (RamificationGroupGraded G B ((n : ℤ) + 1)) →+ ResidueField B :=
  (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ).toAddMonoidHom.comp <|
    ((ramificationGroupGradedToUnitFiltrationGraded G (n + 1) hπ).comp
      (ramificationGroupGradedCongr (Int.natCast_succ n).symm).toMonoidHom).toAdditive

/-- Evaluating `ramificationGroupGradedToResidueField` on a coset `QuotientGroup.mk τ`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) (π : B) (hπ : Irreducible π)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G n π hπ (Additive.ofMul (QuotientGroup.mk τ)) =
      unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ
        (Additive.ofMul (QuotientGroup.mk
          (uniformizerRatio G (n + 1) hπ
            ⟨τ, by simpa only [Nat.cast_add, Nat.cast_one] using τ.2⟩))) := by
  rw [ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, MonoidHom.toAdditive_apply_apply,
    toMul_ofMul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  congr 2

/-- If `τ ∈ G_{n+1}` moves `π` by `τ • π - π = y * π ^ (n + 2)`, then the positive-depth residue
coordinate of `τ` relative to `π` is `residue B y`. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq (n : ℕ) (π : B) (hπ : Irreducible π)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) (y : B)
    (hmove : (τ : G) • π - π = y * π ^ (n + 2)) :
    ramificationGroupGradedToResidueField G n π hπ (Additive.ofMul (QuotientGroup.mk τ)) =
      residue B y := by
  rw [ramificationGroupGradedToResidueField_ofMul_mk]
  refine unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue n π hπ _ y ?_
  apply mul_left_cancel₀ hπ.ne_zero
  rw [mul_sub, mul_one, mul_uniformizerRatio, hmove]
  ring

/-- Replacing `π` by `π' = π * a` scales the positive-depth residue coordinate relative to `π'` by
the residue of `a ^ (n + 1)`. -/
theorem ramificationGroupGradedToResidueField_change (n : ℕ) (π π' : B)
    (hπ : Irreducible π) (hπ' : Irreducible π')
    (x : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G n π hπ (Additive.ofMul x) =
      residue B (TauCeti.uniformizerChangeUnit π π' hπ hπ' : B) ^ (n + 1) *
        ramificationGroupGradedToResidueField G n π' hπ' (Additive.ofMul x) := by
  have hchange :=
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change n π π' hπ hπ'
      (Additive.ofMul (ramificationGroupGradedToUnitFiltrationGraded G (n + 1) hπ
        (ramificationGroupGradedCongr (Int.natCast_succ n).symm x)))
  have htheta := DFunLike.congr_fun
    (ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible G (n + 1) hπ hπ')
    (ramificationGroupGradedCongr (Int.natCast_succ n).symm x)
  rw [ramificationGroupGradedToResidueField, ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, MonoidHom.toAdditive_apply_apply,
    toMul_ofMul, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  simpa only [htheta] using hchange

/-- **Conjugation action on positive-depth ramification quotients** (Serre, *Corps Locaux*, IV §2,
Proposition 9): conjugating a class in `G_{n+1} / G_{n+2}` by `σ ∈ G_0` multiplies its additive
residue coordinate by `(tameCharacter G hπ σ) ^ (n + 1)`. -/
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) (π : B) (hπ : Irreducible π)
    (σ : ramificationGroup G B (0 : ℤ)) (x : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G n π hπ
        (Additive.ofMul (ramificationGroupGradedConj G B (σ : G) ((n : ℤ) + 1) x)) =
      (tameCharacter G hπ σ : ResidueField B) ^ (n + 1) *
        ramificationGroupGradedToResidueField G n π hπ (Additive.ofMul x) := by
  induction x using QuotientGroup.induction_on with
  | _ τ =>
    set π' : B := (σ : G) • π
    have hπ' : Irreducible π' := irreducible_smul hπ (σ : G)
    have hτπ : (τ : G) • π - π ∈ maximalIdeal B ^ (n + 2) :=
      mem_ramificationGroup_natCast_iff (n := n + 1).mp
        (by simpa only [Nat.cast_add, Nat.cast_one] using τ.2) π
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hτπ
    obtain ⟨y, hy⟩ := hτπ
    have hmove : (τ : G) • π - π = y * π ^ (n + 2) := by
      rw [hy, mul_comm]
    have hconjmove : ((MulAut.conjNormal (σ : G) τ :
          ramificationGroup G B ((n : ℤ) + 1)) : G) • π' - π' =
        ((σ : G) • y) * π' ^ (n + 2) := by
      have hconj : ((MulAut.conjNormal (σ : G) τ :
          ramificationGroup G B ((n : ℤ) + 1)) : G) = (σ : G) * (τ : G) * (σ : G)⁻¹ := rfl
      rw [hconj, mul_smul, mul_smul, show (σ : G)⁻¹ • π' = π by simp [π'], ← smul_sub, hmove,
        smul_mul', smul_pow']
    rw [ramificationGroupGradedToResidueField_change n π π' hπ hπ',
      ramificationGroupGradedConj_mk,
      ramificationGroupGradedToResidueField_of_smul_sub_eq n π' hπ' _ ((σ : G) • y) hconjmove,
      residue_smul_eq_of_mem_ramificationGroup_zero G B σ.2 y,
      ramificationGroupGradedToResidueField_of_smul_sub_eq n π hπ τ y hmove,
      coe_tameCharacter_of_mul_eq_smul hπ σ (TauCeti.mul_uniformizerChangeUnit π π' hπ hπ')]

end DiscreteValuationRing

/-! ### Separable residue extensions: injectivity and tame/wild group structure -/

section Separable

variable (A : Type*) [CommRing A] [IsLocalRing A]
variable {G : Type*} [Group G]
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [MulSemiringAction G B] [hcomm : SMulCommClass G A B]

omit [IsLocalRing A] [IsDomain B] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap A B)] in
/-- An automorphism fixing `A` commutes with evaluating a polynomial mapped from `A[X]`. -/
private theorem smul_eval_map (σ : G) (f : A[X]) (z : B) :
    σ • (f.map (algebraMap A B)).eval z = (f.map (algebraMap A B)).eval (σ • z) := by
  have hfix : (MulSemiringAction.toRingHom G B σ).comp (algebraMap A B) = algebraMap A B := by
    ext a
    simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply,
      Algebra.algebraMap_eq_smul_one, smul_comm σ a (1 : B), smul_one]
  rw [eval_map, eval_map]
  calc σ • eval₂ (algebraMap A B) z f
      = MulSemiringAction.toRingHom G B σ (eval₂ (algebraMap A B) z f) := rfl
    _ = eval₂ ((MulSemiringAction.toRingHom G B σ).comp (algebraMap A B))
          (MulSemiringAction.toRingHom G B σ z) f := hom_eval₂ f (algebraMap A B) _ z
    _ = eval₂ (algebraMap A B) (σ • z) f := by rw [hfix]; rfl

/-- **Taylor step.** For `σ ∈ G_i` (`i : ℕ`) and `f : B[X]` whose derivative is a unit at `z`,
`f(σ • z) - f(z) = (σ • z - z) * u` for a unit `u` of `B`. -/
private theorem exists_unit_eval_smul_sub_eval {i : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G B (i : ℤ)) (f : B[X]) (z : B)
    (hder : IsUnit ((derivative f).eval z)) :
    ∃ u : Bˣ, f.eval (σ • z) - f.eval z = (σ • z - z) * (u : B) := by
  obtain ⟨K, hK⟩ := binomExpansion f z (σ • z - z)
  rw [add_sub_cancel] at hK
  have hd : σ • z - z ∈ maximalIdeal B := by
    simpa only [pow_one] using Ideal.pow_le_pow_right (Nat.succ_pos i)
      (mem_ramificationGroup_natCast_iff.mp hσ z)
  have hKd : ¬ IsUnit (K * (σ • z - z)) :=
    (mem_maximalIdeal _).mp (Ideal.mul_mem_left _ K hd)
  have hunit : IsUnit ((derivative f).eval z + K * (σ • z - z)) :=
    TauCeti.isUnit_add_of_isUnit_of_not_isUnit hder hKd
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, hK]
  ring

/-- If `σ ∈ G_i` moves a uniformizer `π` by an element of `𝔪 ^ (i + 2)`, then `σ` moves every
element of `𝔪` by an element of `𝔪 ^ (i + 2)`. -/
private theorem smul_sub_mem_maximalIdeal_pow_add_two_of_mem_maximalIdeal {i : ℕ} {π : B}
    (hπ : Irreducible π) {σ : G} (hσ : σ ∈ ramificationGroup G B (i : ℤ))
    (hσπ : σ • π - π ∈ maximalIdeal B ^ (i + 2)) {w : B} (hw : w ∈ maximalIdeal B) :
    σ • w - w ∈ maximalIdeal B ^ (i + 2) := by
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hw
  obtain ⟨v, rfl⟩ := hw
  have hsplit : σ • (π * v) - π * v = (σ • π - π) * (σ • v) + π * (σ • v - v) := by
    rw [smul_mul']
    ring
  rw [hsplit]
  refine add_mem (Ideal.mul_mem_right _ _ hσπ) ?_
  rw [show i + 2 = 1 + (i + 1) by omega, pow_add, pow_one]
  exact Ideal.mul_mem_mul ((mem_maximalIdeal π).mpr hπ.not_isUnit)
    (mem_ramificationGroup_natCast_iff.mp hσ v)

variable [hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B)]

include hcomm hsep

/-- **Membership in `G_{i+1}` is decided at a uniformizer** when the residue extension is
separable: for every `i : ℕ` and `σ ∈ G_i`, `σ ∈ G_{i+1}` if and only if
`σ • π - π ∈ 𝔪 ^ (i + 2)`. No completeness or residue-field finiteness is needed. -/
theorem mem_ramificationGroup_succ_iff_smul_sub_mem {i : ℕ} {π : B} (hπ : Irreducible π)
    {σ : G} (hσ : σ ∈ ramificationGroup G B (i : ℤ)) :
    σ ∈ ramificationGroup G B ((i : ℤ) + 1) ↔ σ • π - π ∈ maximalIdeal B ^ (i + 2) := by
  have hcast : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, mem_ramificationGroup_natCast_iff]
  refine ⟨fun h ↦ h π, fun hσπ z ↦ ?_⟩
  -- Lift the minimal polynomial of `residue B z` over `ResidueField A` to `A[X]`.
  obtain ⟨f, hf⟩ := Polynomial.map_surjective (residue A) residue_surjective
    (minpoly (ResidueField A) (residue B z))
  set fB : B[X] := f.map (algebraMap A B)
  have hmap : ∀ g : A[X],
      residue B ((g.map (algebraMap A B)).eval z) =
        aeval (residue B z) (g.map (residue A)) := fun g ↦ by
    rw [eval_map, hom_eval₂, ← residue_comp_algebraMap, aeval_def, eval₂_map]
  have hroot : fB.eval z ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, hmap f, hf]
    exact minpoly.aeval _ _
  have hder : IsUnit ((derivative fB).eval z) := by
    rw [← residue_ne_zero_iff_isUnit, show derivative fB = (derivative f).map (algebraMap A B) from
      derivative_map f (algebraMap A B), hmap (derivative f), ← derivative_map, hf]
    exact (Algebra.IsSeparable.isSeparable (ResidueField A) (residue B z)).aeval_derivative_ne_zero
      (minpoly.aeval _ _)
  obtain ⟨u, hu⟩ := exists_unit_eval_smul_sub_eval hσ fB z hder
  have hw := smul_sub_mem_maximalIdeal_pow_add_two_of_mem_maximalIdeal hπ hσ hσπ hroot
  rw [smul_eval_map A σ f z, hu] at hw
  have hcancel : σ • z - z = (σ • z - z) * (u : B) * ((u⁻¹ : Bˣ) : B) := by
    rw [mul_assoc, Units.mul_inv, mul_one]
  rw [hcancel]
  exact Ideal.mul_mem_right _ _ hw

/-- **Membership of an inertia element in `G_n` is decided at a uniformizer** when the residue
extension is separable: for every `n : ℕ` and `σ ∈ G_0`, `σ ∈ G_n` if and only if
`σ • π - π ∈ 𝔪 ^ (n + 1)`. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem {n : ℕ} {π : B} (hπ : Irreducible π)
    {σ : G} (hσ : σ ∈ ramificationGroup G B 0) :
    σ ∈ ramificationGroup G B (n : ℤ) ↔ σ • π - π ∈ maximalIdeal B ^ (n + 1) := by
  induction n with
  | zero =>
    exact ⟨fun h ↦ mem_ramificationGroup_natCast_iff.mp h π, fun _ ↦ hσ⟩
  | succ n ih =>
    refine ⟨fun h ↦ mem_ramificationGroup_natCast_iff.mp h π, fun hπn ↦ ?_⟩
    have hn : σ ∈ ramificationGroup G B (n : ℤ) :=
      ih.mpr (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) hπn)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (mem_ramificationGroup_succ_iff_smul_sub_mem A hπ hn).mpr hπn

variable (G) in
/-- **The kernel of `ramificationGroupToUnitFiltrationGraded` is `G_{i+1}`** when the residue
extension is separable. -/
theorem ker_ramificationGroupToUnitFiltrationGraded (i : ℕ) {π : B} (hπ : Irreducible π) :
    (ramificationGroupToUnitFiltrationGraded G i hπ).ker =
      (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) := by
  ext σ
  rw [mem_ker_ramificationGroupToUnitFiltrationGraded_iff, Subgroup.mem_subgroupOf,
    mem_ramificationGroup_succ_iff_smul_sub_mem A hπ σ.2]

variable (G) in
/-- **Injectivity of the graded ramification homomorphisms** (Serre, *Corps Locaux*, IV §2,
Proposition 7): when the residue extension is separable,
`θ_i : G_i / G_{i+1} →* U(B, i) / U(B, i + 1)` is injective for every `i : ℕ`. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_injective (i : ℕ) {π : B}
    (hπ : Irreducible π) :
    Function.Injective (ramificationGroupGradedToUnitFiltrationGraded G i hπ) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr
    (ker_ramificationGroupToUnitFiltrationGraded A G i hπ).symm

variable (G) in
/-- The kernel of the tame character `G_0 →* (ResidueField B)ˣ` is `G_1` when the residue
extension is separable. -/
theorem ker_tameCharacter {π : B} (hπ : Irreducible π) :
    (tameCharacter G hπ).ker =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) := by
  ext σ
  rw [MonoidHom.mem_ker, tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (unitFiltrationGradedZeroEquivResidueFieldUnits B).injective,
    ← MonoidHom.mem_ker, ker_ramificationGroupToUnitFiltrationGraded A G 0 hπ]
  simp

variable (G) in
/-- **The graded tame character `G_0 / G_1 →* (ResidueField B)ˣ` is injective** when the residue
extension is separable. -/
theorem tameCharacterGraded_injective {π : B} (hπ : Irreducible π) :
    Function.Injective (tameCharacterGraded G hπ) :=
  (unitFiltrationGradedZeroEquivResidueFieldUnits B).injective.comp
    (ramificationGroupGradedToUnitFiltrationGraded_injective A G 0 hπ)

variable (G) in
/-- **The positive-depth additive residue embedding
`Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` is injective** when the residue extension is
separable. -/
theorem ramificationGroupGradedToResidueField_injective (n : ℕ) (π : B) (hπ : Irreducible π) :
    Function.Injective (ramificationGroupGradedToResidueField G n π hπ) :=
  (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer n π hπ).injective.comp
    ((ramificationGroupGradedToUnitFiltrationGraded_injective A G (n + 1) hπ).comp
      (ramificationGroupGradedCongr (Int.natCast_succ n).symm).injective)

variable (G B) in
/-- **The tame quotient `G_0 / G_1` is cyclic** when it is finite and the residue extension is
separable: it embeds in the multiplicative group of `ResidueField B`. -/
theorem isCyclic_ramificationGroupGraded_zero [Finite (RamificationGroupGraded G B 0)] :
    IsCyclic (RamificationGroupGraded G B 0) := by
  obtain ⟨_, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (tameCharacterGraded G hπ))
    (Units.val_injective.comp (tameCharacterGraded_injective A G hπ))

variable (G B) in
/-- **The index of `G_1` in `G_0` is prime to the residue characteristic `p`** when `p` is prime,
`G_0 / G_1` is finite, and the residue extension is separable: `(ResidueField B)ˣ` contains no
element of order `p`. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [Finite (RamificationGroupGraded G B 0)] :
    ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index := by
  obtain ⟨_, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  let φ := tameCharacterGraded G hπ
  have hφ : Function.Injective φ := tameCharacterGraded_injective A G hπ
  intro hp
  have hpcard : p ∣ Nat.card (RamificationGroupGraded G B 0) := by
    rwa [RamificationGroupGraded, zero_add, ← Subgroup.index_eq_card]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpcard
  have hpow : ((φ x : (ResidueField B)ˣ) : ResidueField B) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hx, pow_orderOf_eq_one, map_one, Units.val_one]
  have hsub : (((φ x : (ResidueField B)ˣ) : ResidueField B) - 1) ^ p = 0 := by
    rw [sub_pow_char, hpow, one_pow, sub_self]
  have h1 : φ x = 1 := Units.ext (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsub))
  have hx1 : x = 1 := hφ (h1.trans (map_one φ).symm)
  exact (Fact.out : p.Prime).ne_one (hx ▸ hx1 ▸ orderOf_one)

variable (G B) in
/-- **Wild inertia is the Sylow `p`-subgroup of inertia** in prime residue characteristic `p`,
when `G` acts faithfully on a discrete valuation ring `B` with finite `G_0` and separable residue
extension over `A`. -/
def ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Sylow p (ramificationGroup G B 0) :=
  have : Finite (ramificationGroup G B 1) :=
    Finite.of_injective
      (Subgroup.inclusion (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1)))
      (Subgroup.inclusion_injective _)
  ((isPGroup_ramificationGroup G B p (i := 1) one_pos).comap_subtype).toSylow
    (not_dvd_index_ramificationGroup_one A G B p)

variable (G B) in
/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` viewed inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    (ramificationGroupOneSylow A G B p : Subgroup (ramificationGroup G B 0)) =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) :=
  (rfl)

variable (G B) in
/-- The wild inertia Sylow subgroup is normal in inertia. -/
theorem ramificationGroupOneSylow_normal (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    (ramificationGroupOneSylow A G B p : Subgroup (ramificationGroup G B 0)).Normal := by
  rw [ramificationGroupOneSylow_coe, Subgroup.normal_subgroupOf_iff_le_normalizer
    (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1)),
    Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact le_top

variable (G B) in
/-- The wild inertia Sylow subgroup is the unique Sylow `p`-subgroup of inertia. -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (Q : Sylow p (ramificationGroup G B 0)) :
    Q = ramificationGroupOneSylow A G B p := by
  have : Unique (Sylow p (ramificationGroup G B 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow A G B p)
      (ramificationGroupOneSylow_normal A G B p)
  exact Subsingleton.elim _ _

variable (G B) in
/-- The order of wild inertia is the `p`-part of the order of inertia:
`#G_1 = p ^ ((#G_0).factorization p)`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Nat.card (ramificationGroup G B 1) =
      p ^ (Nat.card (ramificationGroup G B 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow A G B p)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

variable (G B) in
/-- **Wild inertia is trivial exactly in the tame case**: in prime residue characteristic `p`,
`G_1 = ⊥` if and only if `p ∤ #G_0`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [Fact p.Prime] [CharP (ResidueField B) p] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    ramificationGroup G B 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G B 0) := by
  have hp : p.Prime := Fact.out
  rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one A G B p,
    pow_eq_one_iff_right hp.ne_one, Nat.factorization_eq_zero_iff]
  simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]

variable (G B) in
/-- **In residue characteristic zero, a finite inertia group is cyclic** for a faithful action on
a discrete valuation ring with separable residue extension: wild inertia `G_1` is trivial, so `G_0`
embeds in `(ResidueField B)ˣ` via the tame character. -/
theorem isCyclic_ramificationGroup_zero_of_charZero [CharZero (ResidueField B)]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    IsCyclic (ramificationGroup G B 0) := by
  have : Finite (ramificationGroup G B 1) :=
    Finite.of_injective
      (Subgroup.inclusion (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1)))
      (Subgroup.inclusion_injective _)
  obtain ⟨_, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hker : (tameCharacter G hπ).ker = ⊥ := by
    rw [ker_tameCharacter A G hπ, ramificationGroup_one_eq_bot_of_charZero G B,
      Subgroup.bot_subgroupOf]
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (tameCharacter G hπ))
    (Units.val_injective.comp ((MonoidHom.ker_eq_bot_iff _).mp hker))

end Separable

end IsLocalRing

end TauCeti
