/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import TauCeti.Algebra.Group.Subgroup.FiniteFiltration
public import TauCeti.Algebra.Ring.Action.End
public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.Ideal.Inertia
public import TauCeti.RingTheory.Ideal.RamificationGroup
public import TauCeti.RingTheory.LocalRing.Pointwise
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import TauCeti.RingTheory.LocalRing.Monogenic

/-!
# The ramification filtration of a group acting on a local ring

Let `G` act by ring automorphisms on a local ring `S`. The **ramification groups** of the action
are the decreasing family of subgroups

`ramificationGroup G S i = {σ | ∀ x : S, σ • x - x ∈ 𝔪 ^ (i + 1)}`,

indexed by `i : ℤ` with the convention that `𝔪 ^ 0 = ⊤`, so that the family is total and equals
`⊤` below `0`. This is Serre's lower-numbering filtration `G_i`, written here for the pair
`(G, S)` rather than for an extension of local fields: nothing in the definition, and nothing in
the results below, uses a valuation on a fraction field. The filtration of a finite Galois
extension of nonarchimedean local fields is the case `G = L ≃ₐ[K] L`, `S = 𝒪[L]`.

Mathlib's `Ideal.inertia` already names `{σ | ∀ x, σ • x - x ∈ I}` for an ideal `I`; the content
here is the family it forms as `I` runs through the powers of the maximal ideal, together with the
integer indexing that Herbrand theory uses.

## Main definitions

* `TauCeti.IsLocalRing.ramificationGroup G S i`: the `i`-th ramification group, for `i : ℤ`.
* `TauCeti.IsLocalRing.ramificationGroupReal G S u`: the same family reindexed by a real number
  through `⌈·⌉`, the convention under which the step function is constant on `(i - 1, i]`.
* `TauCeti.IsLocalRing.RamificationGroupGraded G S i`: the successive quotient `G_i / G_{i+1}`.
* `TauCeti.IsLocalRing.lowerIndex S σ`: over a discrete valuation ring, Serre's lower index
  `i_G(σ) = min_x v (σ x - x)` in `ℕ∞`.
* `TauCeti.IsLocalRing.displacementHom`: at positive depth `n + 1`, the homomorphism
  `G_{n+1} →* Multiplicative (S → 𝔪^(n+2) / 𝔪^(n+3))` sending `σ` to `x ↦ [σ • x - x]`.
* `TauCeti.IsLocalRing.ramificationGroupOneSylowOfNotDvdIndex`: in prime residue characteristic
  `p`, `G_1` as the unique normal Sylow `p`-subgroup of a finite inertia group `G_0` whenever
  `p ∤ [G_0 : G_1]`.

## Main results

* `TauCeti.IsLocalRing.ramificationGroup_natCast`: at a nonnegative index `G_i` is
  `Ideal.ramificationGroup` of the maximal ideal.
* `TauCeti.IsLocalRing.ramificationGroup_eq_top_of_le_neg_one` and
  `TauCeti.IsLocalRing.ramificationGroup_antitone`: the filtration starts at `⊤` and decreases.
* `TauCeti.IsLocalRing.ramificationGroup_zero_eq_inertia`: `G_0` is the inertia subgroup of the
  maximal ideal, `TauCeti.IsLocalRing.ramificationGroup_zero_eq_ker_toRingAut` identifies it with
  the kernel of the action on the residue field, and
  `TauCeti.IsLocalRing.residue_smul_eq_of_mem_ramificationGroup_zero` is its pointwise form, while
  `TauCeti.IsLocalRing.ramificationGroup_zero_eq_inertiaSubgroup` reads that off as Mathlib's
  `ValuationSubring.inertiaSubgroup` for a valuation subring of a field.
* `TauCeti.IsLocalRing.instNormalRamificationGroup`: each `G_i` is normal in `G`.
* `TauCeti.IsLocalRing.ramificationGroupGradedSubgroupHom`: subgroup inclusion induces an
  injective homomorphism `H_i / H_{i+1} → G_i / G_{i+1}` on successive quotients.
* `TauCeti.IsLocalRing.ramificationGroupGradedConj`: conjugation by an element of the ambient
  group induces an automorphism of each successive quotient.
* `TauCeti.IsLocalRing.iInf_ramificationGroup_eq_ker` and
  `TauCeti.IsLocalRing.exists_forall_ramificationGroup_eq_ker`: over a Noetherian local ring the
  filtration cuts out the kernel of the action, and reaches it at a finite index once `G_0` is
  finite; `TauCeti.IsLocalRing.iInf_ramificationGroup_eq_bot` and
  `TauCeti.IsLocalRing.exists_forall_ramificationGroup_eq_bot` are the faithful case.
* `TauCeti.IsLocalRing.mem_ramificationGroup_iff_of_adjoin_eq_top`: when `S` is generated over a
  base ring `R` whose elements `G` fixes by a set `s`, membership in `G_i` is decided on `s`
  alone; `TauCeti.IsLocalRing.mem_ramificationGroup_iff_of_adjoin_singleton_eq_top` is the
  monogenic case, where a single generator decides it.
* `TauCeti.IsLocalRing.mem_ramificationGroup_iff_of_span_eq_maximalIdeal` and
  `TauCeti.IsLocalRing.mem_ramificationGroup_iff_of_span_singleton_eq_maximalIdeal`: when `S` is a
  local `R`-algebra on which `G` acts by `R`-algebra automorphisms and
  `ResidueField S / ResidueField R` is separable, membership of an element of `G_0` in `G_i` is
  already decided on any generating set of the maximal ideal of `S`.
* `TauCeti.IsLocalRing.ker_displacementHom`,
  `TauCeti.IsLocalRing.commutator_ramificationGroup_le`,
  `TauCeti.IsLocalRing.isMulCommutative_ramificationGroupGraded`,
  `TauCeti.IsLocalRing.pow_mem_ramificationGroup_succ_iff`,
  `TauCeti.IsLocalRing.pow_mem_ramificationGroup_of_charP`,
  `TauCeti.IsLocalRing.isPGroup_ramificationGroupGraded`,
  `TauCeti.IsLocalRing.isPGroup_ramificationGroup`,
  `TauCeti.IsLocalRing.eq_ramificationGroupOneSylowOfNotDvdIndex`,
  `TauCeti.IsLocalRing.natCard_ramificationGroup_one_of_not_dvd_index`,
  `TauCeti.IsLocalRing.ramificationGroup_one_eq_bot_iff_not_dvd_card_of_not_dvd_index`,
  `TauCeti.IsLocalRing.subsingleton_ramificationGroupGraded_of_charZero`, and
  `TauCeti.IsLocalRing.ramificationGroup_eq_bot_of_charZero`: at positive depth `i > 0`, the
  displacement homomorphism has kernel `G_{i+1}`, so the successive quotients `G_i / G_{i+1}` are
  abelian, killed by the residue characteristic `p` (so `G_i` is a `p`-group for a faithful action
  with finite `G_0` over a Noetherian local ring, giving the Sylow `p`-subgroup package for `G_1`
  whenever `p ∤ [G_0 : G_1]`), and trivial when finite in residue characteristic zero (so
  `G_i = ⊥` for a faithful action with finite `G_0` over a Noetherian local ring).
* `TauCeti.IsLocalRing.mem_ramificationGroup_iff_le_addVal`: over a discrete valuation ring the
  defining condition is the valuation inequality `v (σ x - x) ≥ i + 1`;
  `TauCeti.IsLocalRing.mem_ramificationGroup_iff_le_lowerIndex` reads it as `i + 1 ≤ i_G(σ)`.
* `TauCeti.IsLocalRing.lowerIndex_eq_top_iff`: for a faithful action only the identity has lower
  index `⊤`, and `TauCeti.IsLocalRing.lowerIndex_eq_addVal_of_adjoin_singleton_eq_top` computes
  the lower index at a single generator.
* `TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_le_addVal_of_adjoin_singleton_eq_top`
  tests membership in `G_n` at a single generator.
* `TauCeti.IsLocalRing.sum_addVal_smul_sub_eq_finsum_card_ramificationGroup_sub_one`:
  **Hilbert's counting identity** `∑_{σ ≠ 1} v (σ ξ - ξ) = ∑_{i ≥ 0} (#G_i - 1)` for a generator
  `ξ` of a discrete valuation ring under a faithful action of a finite group.
* `TauCeti.IsLocalRing.sum_min_lowerIndex_natCast`: the truncated count
  `∑_{σ ∈ G} min (i_G(σ), m) = ∑_{k < m} #G_k` for a finite group `G`.
* `TauCeti.IsLocalRing.ramificationGroup_eq_comap_of_comap_maximalIdeal_pow`: along an
  equivariant homomorphism of local rings inducing isomorphisms `S ⧸ 𝔪 ^ n ≃ T ⧸ 𝔪 ^ n`, such as
  the inclusion of a discrete valuation ring into its completion, the ramification groups are the
  preimages of each other.
* `TauCeti.IsLocalRing.mem_ramificationGroup_iff_of_lowerIndex_eq` and
  `TauCeti.IsLocalRing.mem_ramificationGroupReal_iff_of_lowerIndex_eq`: when `i_G(σ) = n` is
  finite, `σ ∈ G_i ↔ i + 1 ≤ n` and `σ ∈ G_u ↔ u ≤ n - 1`.

## Implementation notes

The monogenicity-free separable-residue criterion in `section Separable` adapts the lifted
minimal-polynomial Taylor-expansion proof from
`TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean`, and the separability-free
positive-depth displacement homomorphism and `p`-group / characteristic-zero results in
`section PositiveDepth` adapt
`TauCeti/FieldTheory/FunctionField/Place/Extension/RamificationGroup.lean` and
`TauCeti/FieldTheory/FunctionField/Place/Extension/WildInertia.lean` (following Stichtenoth,
Proposition 3.8.5) to arbitrary commutative local rings.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.8.5.
-/

public section

open IsLocalRing

open scoped Pointwise

namespace TauCeti

namespace IsLocalRing

section Defs

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The `i`-th **ramification group**, in the lower numbering, of a group `G` acting by ring
automorphisms on a local ring `S`: the subgroup of elements acting trivially on `S ⧸ 𝔪 ^ (i + 1)`.
The index is an integer, and `𝔪 ^ (i + 1)` is read as `𝔪 ^ (i + 1).toNat`, so that the family is
total and constantly `⊤` for `i ≤ -1`. -/
def ramificationGroup (i : ℤ) : Subgroup G :=
  Ideal.inertia G (maximalIdeal S ^ (i + 1).toNat)

/-- The ramification groups are the inertia subgroups of the powers of the maximal ideal. -/
theorem ramificationGroup_def (i : ℤ) :
    ramificationGroup G S i = Ideal.inertia G (maximalIdeal S ^ (i + 1).toNat) :=
  -- `(rfl)`, not `rfl`: the body of `ramificationGroup` is not `@[expose]`d, so a bare `rfl`
  -- proof would be rechecked against the exported environment, where it is opaque.
  (rfl)

variable {G S}

/-- The defining membership criterion of the ramification groups. -/
@[simp]
theorem mem_ramificationGroup_iff {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔ ∀ x : S, σ • x - x ∈ maximalIdeal S ^ (i + 1).toNat :=
  Ideal.mem_inertia

/-- At a nonnegative index the truncation disappears from the membership criterion. -/
theorem mem_ramificationGroup_natCast_iff {n : ℕ} {σ : G} :
    σ ∈ ramificationGroup G S n ↔ ∀ x : S, σ • x - x ∈ maximalIdeal S ^ (n + 1) := by
  have h : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [mem_ramificationGroup_iff, h]

/-- At a nonnegative index, the ramification group of the local ring is the ramification group
`Ideal.ramificationGroup` of its maximal ideal. -/
@[simp]
theorem ramificationGroup_natCast (n : ℕ) :
    ramificationGroup G S n = (maximalIdeal S).ramificationGroup G n := by
  have h : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [ramificationGroup_def, Ideal.ramificationGroup_def, h]

/-- At the index `0` the defining condition is congruence modulo the maximal ideal itself. -/
theorem mem_ramificationGroup_zero_iff {σ : G} :
    σ ∈ ramificationGroup G S 0 ↔ ∀ x : S, σ • x - x ∈ maximalIdeal S := by
  have h : ((0 : ℤ) + 1).toNat = 1 := by omega
  rw [mem_ramificationGroup_iff, h, pow_one]

/-- Membership in `G_i` says that `σ` acts trivially on `S ⧸ 𝔪 ^ (i + 1)`. -/
theorem mem_ramificationGroup_iff_quotient_mk_smul_eq {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔ ∀ x : S,
      Ideal.Quotient.mk (maximalIdeal S ^ (i + 1).toNat) (σ • x) =
        Ideal.Quotient.mk (maximalIdeal S ^ (i + 1).toNat) x := by
  simp [mem_ramificationGroup_iff, Ideal.Quotient.eq]

variable (G S)

/-- Below the index `0` the filtration is the whole group. -/
theorem ramificationGroup_eq_top_of_le_neg_one {i : ℤ} (hi : i ≤ -1) :
    ramificationGroup G S i = ⊤ := by
  have h : (i + 1).toNat = 0 := by omega
  ext σ
  simp [mem_ramificationGroup_iff, h]

/-- The zeroth ramification group is the inertia subgroup of the maximal ideal. -/
theorem ramificationGroup_zero_eq_inertia :
    ramificationGroup G S 0 = Ideal.inertia G (maximalIdeal S) := by
  have h : ((0 : ℤ) + 1).toNat = 1 := by omega
  rw [ramificationGroup_def, h, pow_one]

/-- The successive quotient `G_i / G_{i+1}` of the ramification filtration. -/
abbrev RamificationGroupGraded (i : ℤ) :=
  ramificationGroup G S i ⧸ (ramificationGroup G S (i + 1)).subgroupOf (ramificationGroup G S i)

/-- The ramification filtration is decreasing. -/
theorem ramificationGroup_antitone : Antitone (ramificationGroup G S) := by
  intro i j hij σ hσ
  rw [mem_ramificationGroup_iff] at hσ ⊢
  exact fun x ↦ Ideal.pow_le_pow_right (by omega) (hσ x)

end Defs

section Adjoin

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
variable {R : Type*} [CommSemiring R] [Algebra R S] [SMulCommClass G R S]

/-- **Serre's criterion** for the ramification filtration: when `S` is generated over `R` by a set
`s` and `G` acts by `R`-algebra automorphisms, membership in `G_i` is decided on `s` alone. This
is `TauCeti.Ideal.mem_inertia_iff_of_adjoin_eq_top` at a power of the maximal ideal. -/
theorem mem_ramificationGroup_iff_of_adjoin_eq_top {s : Set S} (hs : Algebra.adjoin R s = ⊤)
    {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔ ∀ x ∈ s, σ • x - x ∈ maximalIdeal S ^ (i + 1).toNat := by
  rw [ramificationGroup_def, TauCeti.Ideal.mem_inertia_iff_of_adjoin_eq_top hs]

/-- The monogenic case of **Serre's criterion**: when `S` is generated over `R` by a single
element `ξ`, membership in `G_i` is decided at `ξ` alone. This is what makes the filtration
computable, and it applies to the integer ring of a finite separable extension of local fields
through local monogenicity. -/
theorem mem_ramificationGroup_iff_of_adjoin_singleton_eq_top {ξ : S}
    (hξ : Algebra.adjoin R {ξ} = ⊤) {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔ σ • ξ - ξ ∈ maximalIdeal S ^ (i + 1).toNat := by
  rw [ramificationGroup_def, TauCeti.Ideal.mem_inertia_iff_of_adjoin_singleton_eq_top hξ]

end Adjoin

section Normal

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- Every ramification group is normal, because the action fixes the powers of the maximal
ideal. -/
instance instNormalRamificationGroup (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [MulSemiringAction G S] (i : ℤ) : (ramificationGroup G S i).Normal := by
  simp_rw [ramificationGroup_def, Subgroup.normal_iff_map_conj_eq, ← Ideal.inertia_smul]
  exact fun σ ↦ congrArg (Ideal.inertia G) (smul_maximalIdeal_pow σ _)

end Normal

section ResidueField

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The zeroth ramification group is the inertia group: the kernel of the induced action on the
residue field. -/
theorem ramificationGroup_zero_eq_ker_toRingAut :
    ramificationGroup G S 0 = MonoidHom.ker (MulSemiringAction.toRingAut G (ResidueField S)) := by
  ext σ
  rw [mem_ramificationGroup_zero_iff, TauCeti.MulSemiringAction.mem_ker_toRingAut_iff]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have hx : residue S (σ • x - x) = 0 := by
      rw [residue_eq_zero_iff]
      exact h x
    rwa [map_sub, ResidueField.residue_smul, sub_eq_zero] at hx
  · intro h x
    have hx : residue S (σ • x - x) = 0 := by
      rw [map_sub, ResidueField.residue_smul, sub_eq_zero]
      exact h (residue S x)
    rwa [residue_eq_zero_iff] at hx

/-- An element of the zeroth ramification group acts trivially on every residue class. -/
theorem residue_smul_eq_of_mem_ramificationGroup_zero {g : G}
    (hg : g ∈ ramificationGroup G S 0) (x : S) :
    residue S (g • x) = residue S x := by
  have hx := mem_ramificationGroup_zero_iff.mp hg x
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero] at hx
  exact hx

/-- For a valuation subring of a field, the zeroth ramification group of the decomposition
subgroup is Mathlib's `ValuationSubring.inertiaSubgroup`, which is defined as that same kernel. -/
theorem ramificationGroup_zero_eq_inertiaSubgroup (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) :
    ramificationGroup (A.decompositionSubgroup K) A 0 = A.inertiaSubgroup K := by
  rw [ramificationGroup_zero_eq_ker_toRingAut, ValuationSubring.inertiaSubgroup]

end ResidueField

section Separated

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
variable [IsNoetherianRing S]

/-- Over a Noetherian local ring the ramification filtration cuts out the kernel of the action:
an element moving no point of `S` into every power of the maximal ideal is one that moves no
point at all. -/
theorem iInf_ramificationGroup_eq_ker :
    ⨅ i : ℤ, ramificationGroup G S i = MonoidHom.ker (MulSemiringAction.toRingAut G S) := by
  ext σ
  rw [Subgroup.mem_iInf, TauCeti.MulSemiringAction.mem_ker_toRingAut_iff]
  refine ⟨fun hσ x ↦ ?_, fun h i ↦ mem_ramificationGroup_iff.2 fun x ↦ ?_⟩
  · have hmem : σ • x - x ∈ ⨅ n : ℕ, maximalIdeal S ^ n := by
      refine Submodule.mem_iInf _ |>.2 fun n ↦ ?_
      have h : (((n : ℤ) - 1) + 1).toNat = n := by omega
      have hx := mem_ramificationGroup_iff.1 (hσ ((n : ℤ) - 1)) x
      rwa [h] at hx
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal S).ne_top,
      Ideal.mem_bot, sub_eq_zero] at hmem
    exact hmem
  · rw [h x, sub_self]
    exact zero_mem _

/-- A faithful action on a Noetherian local ring is separated by its ramification filtration. -/
theorem iInf_ramificationGroup_eq_bot [FaithfulSMul G S] :
    ⨅ i : ℤ, ramificationGroup G S i = ⊥ := by
  rw [iInf_ramificationGroup_eq_ker, TauCeti.MulSemiringAction.ker_toRingAut_eq_bot]

omit [IsNoetherianRing S] in
/-- The intersection over the integer indices is already attained over the natural ones, since the
filtration is constantly `⊤` below `0`. -/
private theorem iInf_natCast_ramificationGroup :
    ⨅ n : ℕ, ramificationGroup G S (n : ℤ) = ⨅ i : ℤ, ramificationGroup G S i :=
  le_antisymm
    (le_iInf fun i ↦ (iInf_le _ i.toNat).trans
      (ramificationGroup_antitone G S (Int.self_le_toNat i)))
    (le_iInf fun n ↦ iInf_le _ (n : ℤ))

/-- Once the zeroth ramification group is finite, the filtration over a Noetherian local ring
reaches the kernel of the action at a finite index. -/
theorem exists_forall_ramificationGroup_eq_ker [Finite (ramificationGroup G S 0)] :
    ∃ N : ℤ, ∀ i : ℤ, N ≤ i →
      ramificationGroup G S i = MonoidHom.ker (MulSemiringAction.toRingAut G S) := by
  have hanti : Antitone fun n : ℕ ↦ ramificationGroup G S (n : ℤ) :=
    fun _ _ hmn ↦ ramificationGroup_antitone G S (by exact_mod_cast hmn)
  have h0 : (fun n : ℕ ↦ ramificationGroup G S (n : ℤ)) 0 = ramificationGroup G S 0 := by
    norm_num
  have : Finite ((fun n : ℕ ↦ ramificationGroup G S (n : ℤ)) 0) := h0 ▸ ‹_›
  obtain ⟨N, hN⟩ := TauCeti.Subgroup.exists_forall_eq_iInf_of_antitone _ hanti
  refine ⟨(N : ℤ), fun i hi ↦ ?_⟩
  have hi0 : (0 : ℤ) ≤ i := (Int.natCast_nonneg N).trans hi
  have hcast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi0
  have hiN : N ≤ i.toNat := by omega
  rw [← hcast, hN i.toNat hiN, iInf_natCast_ramificationGroup, iInf_ramificationGroup_eq_ker]

/-- For a faithful action whose zeroth ramification group is finite, the ramification groups over
a Noetherian local ring vanish from some index on. -/
theorem exists_forall_ramificationGroup_eq_bot [FaithfulSMul G S]
    [Finite (ramificationGroup G S 0)] :
    ∃ N : ℤ, ∀ i : ℤ, N ≤ i → ramificationGroup G S i = ⊥ := by
  simpa only [TauCeti.MulSemiringAction.ker_toRingAut_eq_bot] using
    exists_forall_ramificationGroup_eq_ker G S

end Separated

section DiscreteValuationRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
variable [MulSemiringAction G S]

/-- Over a discrete valuation ring the ramification groups are cut out by the valuation
inequality `v (σ x - x) ≥ i + 1`, which is Serre's definition. -/
theorem mem_ramificationGroup_iff_le_addVal {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔
      ∀ x : S, ((i + 1).toNat : ℕ∞) ≤ IsDiscreteValuationRing.addVal S (σ • x - x) := by
  simp only [mem_ramificationGroup_iff,
    TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]

variable (S) in
/-- Serre's **lower index** `i_G(σ)` of an element `σ` acting on a discrete valuation ring `S`:
the least valuation `v (σ x - x)` over all `x : S`, with value `⊤` when `σ` acts trivially.
Its superlevel sets are the ramification groups:
`σ ∈ G_i ↔ i + 1 ≤ i_G(σ)`. -/
noncomputable def lowerIndex (σ : G) : ℕ∞ :=
  ⨅ x : S, IsDiscreteValuationRing.addVal S (σ • x - x)

/-- The lower index is the infimum of the valuations of all displacements. -/
theorem lowerIndex_def (σ : G) :
    lowerIndex S σ = ⨅ x : S, IsDiscreteValuationRing.addVal S (σ • x - x) :=
  (rfl)

/-- A lower bound for the lower index is a lower bound for every `v (σ x - x)`. -/
theorem le_lowerIndex_iff {n : ℕ∞} {σ : G} :
    n ≤ lowerIndex S σ ↔ ∀ x : S, n ≤ IsDiscreteValuationRing.addVal S (σ • x - x) :=
  le_iInf_iff

/-- An element of a subgroup `H`, acting on `S` by restriction, has the same lower index in `H` as
in `G`. -/
@[simp]
theorem lowerIndex_coe {H : Subgroup G} (τ : H) : lowerIndex S (τ : G) = lowerIndex S τ :=
  (rfl)

/-- The lower index is at most the valuation `v (σ x - x)` at any `x`. -/
theorem lowerIndex_le_addVal (σ : G) (x : S) :
    lowerIndex S σ ≤ IsDiscreteValuationRing.addVal S (σ • x - x) :=
  iInf_le _ x

/-- The ramification groups are the superlevel sets of the lower index: `σ ∈ G_i` exactly when
`i + 1 ≤ i_G(σ)`. -/
theorem mem_ramificationGroup_iff_le_lowerIndex {i : ℤ} {σ : G} :
    σ ∈ ramificationGroup G S i ↔ ((i + 1).toNat : ℕ∞) ≤ lowerIndex S σ := by
  rw [mem_ramificationGroup_iff_le_addVal, le_lowerIndex_iff]

/-- A natural number bounds the lower index exactly when the automorphism belongs to the
corresponding ramification group. -/
theorem natCast_le_lowerIndex_iff_mem_ramificationGroup {n : ℕ} {σ : G} :
    (n : ℕ∞) ≤ lowerIndex S σ ↔ σ ∈ ramificationGroup G S ((n : ℤ) - 1) := by
  rw [mem_ramificationGroup_iff_le_lowerIndex]
  norm_num

/-- When the lower index of `σ` is the natural number `n`, `σ ∈ G_i` exactly when `i + 1 ≤ n`. -/
theorem mem_ramificationGroup_iff_of_lowerIndex_eq {i : ℤ} {σ : G} {n : ℕ}
    (hn : lowerIndex S σ = n) :
    σ ∈ ramificationGroup G S i ↔ i + 1 ≤ n := by
  rw [mem_ramificationGroup_iff_le_lowerIndex, hn, Nat.cast_le, Int.toNat_le]

/-- The lower index is unchanged by inversion. -/
@[simp]
theorem lowerIndex_inv (σ : G) : lowerIndex S σ⁻¹ = lowerIndex S σ := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_lowerIndex_iff_mem_ramificationGroup,
    natCast_le_lowerIndex_iff_mem_ramificationGroup]
  exact ⟨fun h ↦ by
    simpa only [inv_inv] using (ramificationGroup G S ((n : ℤ) - 1)).inv_mem h,
    fun h ↦ (ramificationGroup G S ((n : ℤ) - 1)).inv_mem h⟩

/-- The lower index is constant on conjugacy classes. -/
@[simp]
theorem lowerIndex_conj (σ τ : G) :
    lowerIndex S (σ * τ * σ⁻¹) = lowerIndex S τ := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_lowerIndex_iff_mem_ramificationGroup,
    natCast_le_lowerIndex_iff_mem_ramificationGroup]
  exact ⟨fun h ↦ by
    have h' := (inferInstance : (ramificationGroup G S ((n : ℤ) - 1)).Normal).conj_mem
      _ h σ⁻¹
    convert h' using 1; group,
    fun h ↦ (inferInstance : (ramificationGroup G S ((n : ℤ) - 1)).Normal).conj_mem _ h σ⟩

/-- The lower index of a product is at least the minimum of the two lower indices. -/
theorem min_le_lowerIndex_mul (σ τ : G) :
    min (lowerIndex S σ) (lowerIndex S τ) ≤ lowerIndex S (σ * τ) := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  rw [natCast_le_lowerIndex_iff_mem_ramificationGroup]
  exact (ramificationGroup G S ((n : ℤ) - 1)).mul_mem
    (natCast_le_lowerIndex_iff_mem_ramificationGroup (n := n) (σ := σ) |>.mp
      (le_trans hn (min_le_left ..)))
    (natCast_le_lowerIndex_iff_mem_ramificationGroup (n := n) (σ := τ) |>.mp
      (le_trans hn (min_le_right ..)))

/-- If the product `σ τ` has lower index at most that of `σ`, then
`i_G(σ τ) = min (i_G(τ), i_G(σ))`. This applies to every `τ ∈ H` when `σ` has the largest lower
index in its coset `σ H`. -/
theorem lowerIndex_mul_eq_min_of_le {σ τ : G} (h : lowerIndex S (σ * τ) ≤ lowerIndex S σ) :
    lowerIndex S (σ * τ) = min (lowerIndex S τ) (lowerIndex S σ) := by
  -- `i(τ) = i(σ⁻¹ (σ τ)) ≥ min (i(σ), i(σ τ)) = i(σ τ)`.
  have h₂ := min_le_lowerIndex_mul (S := S) σ⁻¹ (σ * τ)
  rw [inv_mul_cancel_left, lowerIndex_inv, min_eq_right h] at h₂
  exact le_antisymm (le_min h₂ h) (min_comm (lowerIndex S τ) _ ▸ min_le_lowerIndex_mul σ τ)

variable (S) in
/-- The identity has lower index `⊤`. -/
@[simp]
theorem lowerIndex_one : lowerIndex S (1 : G) = ⊤ := by
  simp [lowerIndex]

/-- For a faithful action, only the identity has lower index `⊤`. -/
@[simp]
theorem lowerIndex_eq_top_iff [FaithfulSMul G S] {σ : G} : lowerIndex S σ = ⊤ ↔ σ = 1 := by
  refine ⟨fun h ↦ FaithfulSMul.eq_of_smul_eq_smul (α := S) fun x ↦ ?_, ?_⟩
  · have hx := le_lowerIndex_iff.1 h.ge x
    rw [top_le_iff, IsDiscreteValuationRing.addVal_eq_top_iff, sub_eq_zero] at hx
    rw [hx, one_smul]
  · rintro rfl
    exact lowerIndex_one S

/-- When `S` is generated over a base ring `R` fixed by `G` by a single element `ξ`, the lower
index is read at `ξ` alone: `i_G(σ) = v (σ ξ - ξ)`. This recovers Serre's monogenic
computation formula. -/
theorem lowerIndex_eq_addVal_of_adjoin_singleton_eq_top {R : Type*} [CommSemiring R]
    [Algebra R S] [SMulCommClass G R S] {ξ : S} (hξ : Algebra.adjoin R {ξ} = ⊤) (σ : G) :
    lowerIndex S σ = IsDiscreteValuationRing.addVal S (σ • ξ - ξ) := by
  refine (lowerIndex_le_addVal σ ξ).antisymm (le_lowerIndex_iff.2 fun x ↦ ?_)
  exact IsDiscreteValuationRing.addVal_le_iff_dvd.2
    (TauCeti.smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hξ σ x)

variable {R : Type*} [CommSemiring R] [Algebra R S] [SMulCommClass G R S]

/-- When the discrete valuation ring `S` is generated over a base `R` fixed by `G` by a single
element `ξ`, membership in `G_n` for `n : ℕ` is the single inequality `v (σ • ξ - ξ) ≥ n + 1`. -/
theorem mem_ramificationGroup_natCast_iff_le_addVal_of_adjoin_singleton_eq_top {ξ : S}
    (hξ : Algebra.adjoin R {ξ} = ⊤) {n : ℕ} {σ : G} :
    σ ∈ ramificationGroup G S n ↔
      ((n + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal S (σ • ξ - ξ) := by
  have h : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [mem_ramificationGroup_iff_le_lowerIndex,
    lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hξ, h]

open Finset in
/-- **Hilbert's counting identity.** Let a finite group `G` act faithfully on a discrete valuation
ring `S` generated over a base `R` fixed by `G` by a single element `ξ`. Then the sum over the
nontrivial `σ ∈ G` of the valuations `v (σ • ξ - ξ)` is `∑_{i ≥ 0} (#G_i - 1)`, where `G_i` is
the `i`-th ramification group: each `σ ≠ 1` lies in exactly `v (σ • ξ - ξ)` of the groups
`G_0, G_1, …`, and the sum is finite because the filtration is eventually trivial. -/
theorem sum_addVal_smul_sub_eq_finsum_card_ramificationGroup_sub_one [Fintype G] [DecidableEq G]
    [FaithfulSMul G S] {ξ : S} (hξ : Algebra.adjoin R {ξ} = ⊤) :
    ∑ σ ∈ (univ : Finset G).erase 1, IsDiscreteValuationRing.addVal S (σ • ξ - ξ) =
      ((∑ᶠ i : ℕ, (Nat.card (ramificationGroup G S i) - 1) : ℕ) : ℕ∞) := by
  classical
  -- The filtration vanishes from some natural index `N` on.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : ℕ, N ≤ i → ramificationGroup G S i = ⊥ := by
    obtain ⟨N₀, hN₀⟩ := exists_forall_ramificationGroup_eq_bot G S
    exact ⟨N₀.toNat, fun i hi ↦ hN₀ i (by omega)⟩
  -- For `σ ≠ 1`, the valuation `v (σ • ξ - ξ)` counts the indices `i < N` with `σ ∈ G_i`.
  have hval : ∀ σ ∈ univ.erase (1 : G), IsDiscreteValuationRing.addVal S (σ • ξ - ξ) =
      (((range N).filter fun i : ℕ ↦ σ ∈ ramificationGroup G S i).card : ℕ∞) := by
    intro σ hσ
    have hσ1 : σ ≠ 1 := ne_of_mem_erase hσ
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 <|
      IsDiscreteValuationRing.addVal_eq_top_iff.not.2 <| sub_ne_zero.2 fun h ↦
        hσ1 (eq_one_of_smul_eq_of_adjoin_singleton_eq_top hξ h)
    have hnN : n ≤ N := by
      by_contra hlt
      have hmem : σ ∈ ramificationGroup G S N := by
        rw [mem_ramificationGroup_natCast_iff_le_addVal_of_adjoin_singleton_eq_top hξ, ← hn]
        exact_mod_cast (by omega : N + 1 ≤ n)
      rw [hN N le_rfl, Subgroup.mem_bot] at hmem
      exact hσ1 hmem
    have hfilter : ((range N).filter fun i : ℕ ↦ σ ∈ ramificationGroup G S i) = range n := by
      ext i
      simp only [mem_filter, mem_range,
        mem_ramificationGroup_natCast_iff_le_addVal_of_adjoin_singleton_eq_top hξ, ← hn,
        Nat.cast_le]
      omega
    rw [hfilter, card_range, hn]
  rw [sum_congr rfl hval, ← Nat.cast_sum]
  congr 1
  -- Double counting: `∑_{σ ≠ 1} #{i < N | σ ∈ G_i} = ∑_{i < N} #{σ ≠ 1 | σ ∈ G_i}`.
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (σ : G) (i : ℕ) ↦ σ ∈ ramificationGroup G S i) (s := univ.erase 1) (t := range N)
  simp only [bipartiteAbove, bipartiteBelow] at hdc
  rw [hdc, finsum_eq_sum_of_support_subset (s := range N)]
  · refine sum_congr rfl fun i _ ↦ ?_
    rw [filter_erase, card_erase_of_mem (mem_filter.2 ⟨mem_univ _, one_mem _⟩),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro i hi
    by_contra h
    rw [coe_range, Set.mem_Iio, not_lt] at h
    rw [Function.mem_support, hN i h, Subgroup.card_bot] at hi
    exact hi rfl

open Finset in
/-- **Counting the filtration by truncated lower indices.** For a finite group `G`,
`∑_{σ ∈ G} min (i_G(σ), m) = ∑_{k < m} #G_k`: each `σ` lies in exactly `min (i_G(σ), m)` of the
groups `G_0, …, G_{m-1}`. -/
theorem sum_min_lowerIndex_natCast [Fintype G] (m : ℕ) :
    ∑ σ : G, min (lowerIndex S σ) (m : ℕ∞) =
      ∑ k ∈ range m, (Nat.card (ramificationGroup G S k) : ℕ∞) := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    -- Passing from `m` to `m + 1` adds `1` exactly for the `σ` with `m + 1 ≤ i_G(σ)`, that is
    -- for `σ ∈ G_m`.
    have key : ∀ a : ℕ∞, min a ((m + 1 : ℕ) : ℕ∞) =
        min a m + if ((m + 1 : ℕ) : ℕ∞) ≤ a then 1 else 0 := by
      intro a
      have hm : (m : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ m
      split_ifs with h
      · rw [min_eq_right h, min_eq_right (hm.trans h)]
        push_cast
        rfl
      · have h' : a ≤ m := by
          lift a to ℕ using (not_le.1 h).ne_top
          exact_mod_cast Nat.le_of_lt_succ (by exact_mod_cast not_le.1 h)
        rw [min_eq_left h', min_eq_left (h'.trans hm), add_zero]
    have hcard : (Nat.card (ramificationGroup G S m) : ℕ∞) =
        #{σ : G | ((m + 1 : ℕ) : ℕ∞) ≤ lowerIndex S σ} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 2
      ext σ
      rw [mem_filter, mem_filter, natCast_le_lowerIndex_iff_mem_ramificationGroup]
      push_cast
      rw [add_sub_cancel_right]
    simp_rw [key]
    rw [sum_add_distrib, ih, sum_boole, sum_range_succ, hcard]

end DiscreteValuationRing

section Subgroup

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The ramification filtration of a subgroup is the trace on it of the ramification filtration of
the ambient group. -/
@[simp]
theorem subgroupOf_ramificationGroup (H : Subgroup G) (i : ℤ) :
    (ramificationGroup G S i).subgroupOf H = ramificationGroup H S i :=
  AddSubgroup.subgroupOf_inertia _ H

/-- Inclusion of the `i`-th ramification group for a subgroup `H ≤ G` into the `i`-th
ramification group for `G`. -/
def ramificationGroupSubgroupHom (H : Subgroup G) (i : ℤ) :
    ramificationGroup H S i →* ramificationGroup G S i where
  toFun σ := ⟨((σ : H) : G), by
    have hσ : (σ : H) ∈ (ramificationGroup G S i).subgroupOf H := by
      rw [subgroupOf_ramificationGroup]
      exact σ.property
    exact hσ⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The inclusion of a subgroup ramification group agrees with the ambient inclusion. -/
@[simp]
theorem coe_ramificationGroupSubgroupHom (H : Subgroup G) (i : ℤ)
    (σ : ramificationGroup H S i) :
    (ramificationGroupSubgroupHom G S H i σ : G) = σ := by
  simp [ramificationGroupSubgroupHom]

/-- Inclusion `H → G` induces a homomorphism `H_i/H_{i+1} → G_i/G_{i+1}` on every
successive ramification quotient. -/
def ramificationGroupGradedSubgroupHom (H : Subgroup G) (i : ℤ) :
    RamificationGroupGraded H S i →* RamificationGroupGraded G S i :=
  QuotientGroup.map
    ((ramificationGroup H S (i + 1)).subgroupOf (ramificationGroup H S i))
    ((ramificationGroup G S (i + 1)).subgroupOf (ramificationGroup G S i))
    (ramificationGroupSubgroupHom G S H i) fun σ hσ ↦ by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf] at hσ
      have hσ' : (σ : H) ∈ (ramificationGroup G S (i + 1)).subgroupOf H := by
        rw [subgroupOf_ramificationGroup]
        exact hσ
      exact hσ'

/-- The map on ramification quotients induced by subgroup inclusion sends the class of an element
to the class of the same element in the ambient group. -/
@[simp]
theorem ramificationGroupGradedSubgroupHom_mk (H : Subgroup G) (i : ℤ)
    (σ : ramificationGroup H S i) :
    ramificationGroupGradedSubgroupHom G S H i (QuotientGroup.mk σ) =
      QuotientGroup.mk (ramificationGroupSubgroupHom G S H i σ) :=
  QuotientGroup.map_mk _ _ _ _ _

/-- The map `H_i/H_{i+1} → G_i/G_{i+1}` induced by subgroup inclusion is injective. -/
theorem ramificationGroupGradedSubgroupHom_injective (H : Subgroup G) (i : ℤ) :
    Function.Injective (ramificationGroupGradedSubgroupHom G S H i) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    induction y using QuotientGroup.induction_on with
    | _ τ =>
      rw [ramificationGroupGradedSubgroupHom_mk,
        ramificationGroupGradedSubgroupHom_mk] at hxy
      rw [QuotientGroup.eq] at hxy ⊢
      rw [Subgroup.mem_subgroupOf] at hxy ⊢
      have hmem : ((σ⁻¹ * τ : ramificationGroup H S i) : H) ∈
          (ramificationGroup G S (i + 1)).subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        simpa only [coe_ramificationGroupSubgroupHom, Subgroup.coe_inv,
          Subgroup.coe_mul] using hxy
      rw [subgroupOf_ramificationGroup] at hmem
      exact hmem

/-! ### Conjugation on the graded pieces -/

/-- Conjugation by an element of the ambient group induces an automorphism on every successive
quotient `G_i/G_{i+1}` of the ramification filtration. -/
noncomputable def ramificationGroupGradedConj (g : G) (i : ℤ) :
    RamificationGroupGraded G S i ≃* RamificationGroupGraded G S i :=
  QuotientGroup.congr
    ((ramificationGroup G S (i + 1)).subgroupOf (ramificationGroup G S i))
    ((ramificationGroup G S (i + 1)).subgroupOf (ramificationGroup G S i))
    (MulAut.conjNormal g) <| by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr
          ((inferInstance : (ramificationGroup G S (i + 1)).Normal).conj_mem y
            (Subgroup.mem_subgroupOf.mp hy) g)
      · intro hx
        refine ⟨(MulAut.conjNormal g).symm x, ?_, (MulAut.conjNormal g).apply_symm_apply x⟩
        exact Subgroup.mem_subgroupOf.mpr
          ((inferInstance : (ramificationGroup G S (i + 1)).Normal).conj_mem x
            (Subgroup.mem_subgroupOf.mp hx) g⁻¹)

/-- On a class represented by `x ∈ G_i`, the induced conjugation is represented by
`g * x * g⁻¹`. -/
@[simp]
theorem ramificationGroupGradedConj_mk (g : G) (i : ℤ)
    (x : ramificationGroup G S i) :
    ramificationGroupGradedConj G S g i (QuotientGroup.mk x) =
      QuotientGroup.mk (MulAut.conjNormal g x) := by
  exact QuotientGroup.congr_mk _ _ _ _ x

/-- Conjugation by the identity acts trivially on each ramification quotient. -/
@[simp]
theorem ramificationGroupGradedConj_one (i : ℤ)
    (x : RamificationGroupGraded G S i) :
    ramificationGroupGradedConj G S 1 i x = x := by
  induction x using QuotientGroup.induction_on with
  | _ x => simp

/-- Conjugation by a product is the composite of the corresponding conjugation automorphisms. -/
@[simp]
theorem ramificationGroupGradedConj_mul (g h : G) (i : ℤ)
    (x : RamificationGroupGraded G S i) :
    ramificationGroupGradedConj G S (g * h) i x =
      ramificationGroupGradedConj G S g i (ramificationGroupGradedConj G S h i x) := by
  induction x using QuotientGroup.induction_on with
  | _ x => simp

end Subgroup

section Comap

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]
  {H : Type*} [Group H] {T : Type*} [CommRing T] [IsLocalRing T] [MulSemiringAction H T]

/-- **Ramification groups along a map that is an isomorphism modulo every power of the maximal
ideal.** Let `f : S →+* T` be a homomorphism of local rings, equivariant along `φ : G →* H`, such
that `f⁻¹ (𝔪_T ^ n) = 𝔪_S ^ n` and `S` surjects onto `T ⧸ 𝔪_T ^ n` for every `n`, as for the
inclusion of a discrete valuation ring into its completion. Then `G_i` is the preimage of `H_i`
under `φ`.

The approximation argument generalizes
`IsDedekindDomain.HeightOneSpectrum.mem_ramificationGroup_iff_decompositionHom_mem` from
`TauCeti/NumberTheory/NumberField/LocalGlobal/RamificationGroup.lean`. -/
theorem ramificationGroup_eq_comap_of_comap_maximalIdeal_pow (φ : G →* H) (f : S →+* T)
    (hf : ∀ (g : G) (x : S), f (g • x) = φ g • f x)
    (hcomap : ∀ n : ℕ, (maximalIdeal T ^ n).comap f = maximalIdeal S ^ n)
    (hdense : ∀ (n : ℕ) (y : T), ∃ x : S, y - f x ∈ maximalIdeal T ^ n) (i : ℤ) :
    ramificationGroup G S i = (ramificationGroup H T i).comap φ := by
  ext σ
  rw [Subgroup.mem_comap, mem_ramificationGroup_iff, mem_ramificationGroup_iff]
  refine ⟨fun h y ↦ ?_, fun h x ↦ ?_⟩
  · -- approximate `y` by `f x`; then `φ σ` moves `y - f x` within `𝔪_T ^ n`, and moves `f x` by
    -- the image of `σ • x - x`
    obtain ⟨x, hx⟩ := hdense (i + 1).toNat y
    have hσx : f (σ • x - x) ∈ maximalIdeal T ^ (i + 1).toNat := by
      rw [← Ideal.mem_comap, hcomap]
      exact h x
    have hsplit : φ σ • y - y = φ σ • (y - f x) + f (σ • x - x) - (y - f x) := by
      rw [map_sub, hf, smul_sub]
      ring
    rw [hsplit]
    exact sub_mem (add_mem ((smul_mem_maximalIdeal_pow_iff _).2 hx) hσx) hx
  · rw [← hcomap, Ideal.mem_comap, map_sub, hf]
    exact h (f x)

end Comap

section Real

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The ramification filtration reindexed by a real number, through the ceiling. This is the
indexing convention of Herbrand theory: the resulting step function is constant on `(i - 1, i]`. -/
noncomputable def ramificationGroupReal (u : ℝ) : Subgroup G :=
  ramificationGroup G S ⌈u⌉

/-- The real-indexed filtration at `u` is the integer-indexed one at `⌈u⌉`. -/
theorem ramificationGroupReal_def (u : ℝ) :
    ramificationGroupReal G S u = ramificationGroup G S ⌈u⌉ :=
  -- `(rfl)` for the same reason as in `ramificationGroup_def`.
  (rfl)

variable {G S} in
/-- The defining membership criterion of the real-indexed ramification groups. -/
@[simp]
theorem mem_ramificationGroupReal_iff {u : ℝ} {σ : G} :
    σ ∈ ramificationGroupReal G S u ↔ ∀ x : S, σ • x - x ∈ maximalIdeal S ^ (⌈u⌉ + 1).toNat := by
  rw [ramificationGroupReal_def, mem_ramificationGroup_iff]

/-- Every real-indexed ramification group is normal in `G`. -/
instance instNormalRamificationGroupReal (u : ℝ) : (ramificationGroupReal G S u).Normal := by
  rw [ramificationGroupReal_def]
  infer_instance

/-- The real-indexed ramification filtration is decreasing. -/
theorem ramificationGroupReal_antitone : Antitone (ramificationGroupReal G S) :=
  fun _ _ huv ↦ ramificationGroup_antitone G S (Int.ceil_mono huv)

/-- The real-indexed filtration of a subgroup is the trace on it of the real-indexed filtration of
the ambient group. -/
@[simp]
theorem subgroupOf_ramificationGroupReal (H : Subgroup G) (u : ℝ) :
    (ramificationGroupReal G S u).subgroupOf H = ramificationGroupReal H S u := by
  rw [ramificationGroupReal_def, ramificationGroupReal_def, subgroupOf_ramificationGroup]

/-- At an integer argument the real-indexed filtration agrees with the integer-indexed one. -/
@[simp]
theorem ramificationGroupReal_intCast (i : ℤ) :
    ramificationGroupReal G S (i : ℝ) = ramificationGroup G S i := by
  rw [ramificationGroupReal_def, Int.ceil_intCast]

/-- The real indexing is constant on the interval `(i - 1, i]`. -/
theorem ramificationGroupReal_eq_of_sub_one_lt_of_le {i : ℤ} {u : ℝ} (hleft : (i : ℝ) - 1 < u)
    (hright : u ≤ i) : ramificationGroupReal G S u = ramificationGroup G S i := by
  rw [ramificationGroupReal_def, Int.ceil_eq_iff.2 ⟨hleft, hright⟩]

end Real

section RealDiscreteValuationRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
variable [MulSemiringAction G S]

/-- When the lower index of `σ` is the natural number `n`, `σ ∈ G_u` for a real `u` exactly when
`u ≤ n - 1`. -/
theorem mem_ramificationGroupReal_iff_of_lowerIndex_eq {u : ℝ} {σ : G} {n : ℕ}
    (hn : lowerIndex S σ = n) :
    σ ∈ ramificationGroupReal G S u ↔ u ≤ (n : ℝ) - 1 := by
  rw [ramificationGroupReal_def, mem_ramificationGroup_iff_of_lowerIndex_eq hn, Int.add_one_le_iff,
    ← Int.le_sub_one_iff, Int.ceil_le]
  push_cast
  exact Iff.rfl

end RealDiscreteValuationRing

/-! ### Separable residue extensions -/

private theorem smul_mul_sub_mul {G : Type*} [Group G] {S : Type*} [CommRing S]
    [MulSemiringAction G S] (σ : G) (a b : S) :
    σ • (a * b) - a * b = σ • a * (σ • b - b) + (σ • a - a) * b := by
  rw [smul_mul']
  ring

section Separable

open Polynomial

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- Over a local `R`-algebra `S` on which `G` acts by `R`-algebra automorphisms with separable
residue extension, an element of `G_0` moving every element of the maximal ideal into an ideal `I`
moves every element of `S` into `I`. -/
theorem smul_sub_mem_of_mem_ramificationGroup_zero_of_forall_mem_maximalIdeal (R : Type*)
    [CommRing R] [IsLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {I : Ideal S} {σ : G}
    (hσ : σ ∈ ramificationGroup G S 0) (hm : ∀ y ∈ maximalIdeal S, σ • y - y ∈ I) (x : S) :
    σ • x - x ∈ I := by
  -- Lift the minimal polynomial of `residue S x` over `ResidueField R` to `g : R[X]`: then
  -- `g(x) ∈ 𝔪_S` and `g'(x)` is a unit in `S` (adapting
  -- `TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean`, Stichtenoth Prop. 3.8.5).
  obtain ⟨g, hg⟩ := (mem_lifts _).mp
    (mem_lifts_of_surjective residue_surjective (minpoly (ResidueField R) (residue S x)))
  have hval : aeval x g ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, map_aeval_eq_aeval_map residue_comp_algebraMap, hg]
    exact minpoly.aeval _ _
  have hder : IsUnit (aeval x (derivative g)) := by
    rw [← residue_ne_zero_iff_isUnit, map_aeval_eq_aeval_map residue_comp_algebraMap,
      ← derivative_map, hg]
    exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  -- Taylor expansion writes `g(σ • x) - g(x) = (σ • x - x) * u` with `u` a unit of `S`.
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
  obtain ⟨u, hu⟩ := hunit.exists_right_inv
  have hd_eq : d = d * ((derivative f).eval x + k * d) * u := by
    rw [mul_assoc, hu, mul_one]
  rw [hd_eq, hdu]
  exact I.mul_mem_right u hfσ

/-- When `S` is a local `R`-algebra on which `G` acts by `R`-algebra automorphisms with separable
residue extension, membership of an element `σ ∈ G_0` in `G_i` is decided on any generating set `s`
of the maximal ideal of `S`. -/
theorem mem_ramificationGroup_iff_of_span_eq_maximalIdeal (R : Type*) [CommRing R]
    [IsLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {s : Set S}
    (hs : Ideal.span s = maximalIdeal S) {i : ℤ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S 0) :
    σ ∈ ramificationGroup G S i ↔
      ∀ z ∈ s, σ • z - z ∈ maximalIdeal S ^ (i + 1).toNat := by
  rw [mem_ramificationGroup_iff]
  refine ⟨fun h z _ ↦ h z, ?_⟩
  -- Propagate from `s` to `𝔪_S` by the Leibniz rule and from `𝔪_S` to `S` by Taylor expansion,
  -- advancing one power of `𝔪_S` at a time.
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
      rw [smul_eq_mul, smul_mul_sub_mul]
      refine add_mem (Ideal.mul_mem_left _ _ hcy) ?_
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ihm c) (hs ▸ hy)

/-- When `S` is a local `R`-algebra on which `G` acts by `R`-algebra automorphisms with separable
residue extension and principal maximal ideal generated by `π`, membership of an element `σ ∈ G_0`
in `G_i` is decided at `π` alone. -/
theorem mem_ramificationGroup_iff_of_span_singleton_eq_maximalIdeal (R : Type*) [CommRing R]
    [IsLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {π : S}
    (hπ : Ideal.span {π} = maximalIdeal S) {i : ℤ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S 0) :
    σ ∈ ramificationGroup G S i ↔ σ • π - π ∈ maximalIdeal S ^ (i + 1).toNat := by
  rw [mem_ramificationGroup_iff_of_span_eq_maximalIdeal R hπ hσ, Set.forall_mem_singleton]

/-- At a nonnegative index, over a local `R`-algebra `S` on which `G` acts by `R`-algebra
automorphisms with separable residue extension, membership of an element `σ ∈ G_0` in `G_n` is
decided on any generating set `s` of `𝔪_S`. -/
theorem mem_ramificationGroup_natCast_iff_of_span_eq_maximalIdeal (R : Type*) [CommRing R]
    [IsLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {s : Set S}
    (hs : Ideal.span s = maximalIdeal S) {n : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S 0) :
    σ ∈ ramificationGroup G S n ↔ ∀ z ∈ s, σ • z - z ∈ maximalIdeal S ^ (n + 1) := by
  have h : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [mem_ramificationGroup_iff_of_span_eq_maximalIdeal R hs hσ, h]

/-- At a nonnegative index, over a local `R`-algebra `S` on which `G` acts by `R`-algebra
automorphisms with separable residue extension and principal maximal ideal `(π)`, membership of an
element `σ ∈ G_0` in `G_n` is decided at `π` alone. -/
theorem mem_ramificationGroup_natCast_iff_of_span_singleton_eq_maximalIdeal (R : Type*)
    [CommRing R] [IsLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)] [SMulCommClass G R S]
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {π : S}
    (hπ : Ideal.span {π} = maximalIdeal S) {n : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S 0) :
    σ ∈ ramificationGroup G S n ↔ σ • π - π ∈ maximalIdeal S ^ (n + 1) := by
  rw [mem_ramificationGroup_natCast_iff_of_span_eq_maximalIdeal R hπ hσ, Set.forall_mem_singleton]

end Separable

/-! ### Positive-depth structure

The displacement homomorphism and positive-depth structure theorems below adapt
`TauCeti.Place.ramificationResidueHom` and the positive-depth structure proofs from
`TauCeti/FieldTheory/FunctionField/Place/Extension/RamificationGroup.lean` and
`TauCeti/FieldTheory/FunctionField/Place/Extension/WildInertia.lean` (following Stichtenoth,
Proposition 3.8.5) to arbitrary commutative local rings without assuming a DVR or residue
separability. -/

section PositiveDepth

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- An element of `G_k` moves every element of `𝔪 ^ m` by an element of `𝔪 ^ (k + m)`. -/
theorem smul_sub_mem_maximalIdeal_pow_of_mem_ramificationGroup {k m : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G S k) {y : S} (hy : y ∈ maximalIdeal S ^ m) :
    σ • y - y ∈ maximalIdeal S ^ (k + m) := by
  induction m generalizing y with
  | zero =>
    rw [add_zero]
    exact Ideal.pow_le_pow_right (Nat.le_succ k) (mem_ramificationGroup_natCast_iff.mp hσ y)
  | succ m ih =>
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb ↦ ?_) (fun y₁ y₂ h₁ h₂ ↦ ?_)
    · rw [smul_mul_sub_mul]
      have h₁ : σ • a * (σ • b - b) ∈ maximalIdeal S ^ (k + (m + 1)) := by
        have hexp : k + (m + 1) = m + (k + 1) := by omega
        rw [hexp, pow_add]
        exact Ideal.mul_mem_mul ((smul_mem_maximalIdeal_pow_iff σ).mpr ha)
          (mem_ramificationGroup_natCast_iff.mp hσ b)
      have h₂ : (σ • a - a) * b ∈ maximalIdeal S ^ (k + (m + 1)) := by
        rw [← add_assoc, pow_succ]
        exact Ideal.mul_mem_mul (ih ha) hb
      exact add_mem h₁ h₂
    · rw [smul_add, add_sub_add_comm]
      exact add_mem h₁ h₂

/-- The positive-depth **displacement homomorphism** on `G_{n+1}`, sending `σ` to the function
`x ↦ [σ • x - x]` in the `(n + 2)`-nd graded piece `𝔪^(n+2) / 𝔪^(n+3)` of the maximal-ideal
filtration. Its kernel is `G_{n+2}` (`ker_displacementHom`). -/
def displacementHom (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S]
    [MulSemiringAction G S] (n : ℕ) :
    ramificationGroup G S ((n + 1 : ℕ) : ℤ) →*
      Multiplicative (S → (maximalIdeal S ^ (n + 2) : Ideal S) ⧸
        (maximalIdeal S • ⊤ : Submodule S (maximalIdeal S ^ (n + 2) : Ideal S))) :=
  MonoidHom.mk'
    (fun σ ↦ .ofAdd fun x ↦
      Submodule.Quotient.mk ⟨(σ : G) • x - x, mem_ramificationGroup_natCast_iff.mp σ.property x⟩)
    fun σ τ ↦ by
      rw [← ofAdd_add]
      refine congrArg Multiplicative.ofAdd (funext fun x ↦ ?_)
      rw [Pi.add_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq,
        Submodule.mem_smul_top_iff]
      change ((σ * τ : ramificationGroup G S ((n + 1 : ℕ) : ℤ)) : G) • x - x -
          (((σ : G) • x - x) + ((τ : G) • x - x)) ∈
        maximalIdeal S • maximalIdeal S ^ (n + 2)
      have hy : (τ : G) • x - x ∈ maximalIdeal S ^ (n + 2) :=
        mem_ramificationGroup_natCast_iff.mp τ.property x
      have hστ : (σ : G) • ((τ : G) • x - x) - ((τ : G) • x - x) ∈
          maximalIdeal S ^ (n + 3) :=
        Ideal.pow_le_pow_right (by omega)
          (smul_sub_mem_maximalIdeal_pow_of_mem_ramificationGroup σ.property hy)
      rw [smul_eq_mul, ← pow_succ']
      convert hστ using 1
      rw [Subgroup.coe_mul, mul_smul, smul_sub]
      ring

/-- Evaluating `displacementHom G S n σ` at `x` gives the class of `σ • x - x` in
`𝔪^(n+2) / 𝔪^(n+3)`. -/
theorem toAdd_displacementHom_apply (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [MulSemiringAction G S] (n : ℕ)
    (σ : ramificationGroup G S ((n + 1 : ℕ) : ℤ)) (x : S) :
    Multiplicative.toAdd (displacementHom G S n σ) x =
      Submodule.Quotient.mk ⟨(σ : G) • x - x, mem_ramificationGroup_natCast_iff.mp σ.property x⟩ :=
  (rfl)

/-- The kernel of `displacementHom G S n` is `G_{n+2}`, viewed inside `G_{n+1}`. -/
theorem ker_displacementHom (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [MulSemiringAction G S] (n : ℕ) :
    (displacementHom G S n).ker =
      (ramificationGroup G S (((n + 1 : ℕ) : ℤ) + 1)).subgroupOf
        (ramificationGroup G S ((n + 1 : ℕ) : ℤ)) := by
  ext σ
  rw [MonoidHom.mem_ker, ← toAdd_eq_zero, Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff, funext_iff]
  refine forall_congr' fun x ↦ ?_
  rw [Pi.zero_apply, toAdd_displacementHom_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_top_iff]
  change (σ : G) • x - x ∈ maximalIdeal S • maximalIdeal S ^ (n + 2) ↔
    (σ : G) • x - x ∈ maximalIdeal S ^ (n + 3)
  rw [smul_eq_mul, ← pow_succ']

/-- At positive depth `i > 0`, the commutator subgroup `⁅G_i, G_i⁆` lies in `G_{i+1}`. -/
theorem commutator_ramificationGroup_le (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [MulSemiringAction G S] {i : ℤ} (hi : 0 < i) :
    ⁅ramificationGroup G S i, ramificationGroup G S i⁆ ≤ ramificationGroup G S (i + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = ((n + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
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
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = ((n + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
  have htoNat : (((n + 1 : ℕ) : ℤ) + 2).toNat = n + 3 := by omega
  have hmem : (⟨σ, hσ⟩ : ramificationGroup G S ((n + 1 : ℕ) : ℤ)) ^ m ∈
        (displacementHom G S n).ker ↔
      σ ^ m ∈ ramificationGroup G S (((n + 1 : ℕ) : ℤ) + 1) := by
    rw [ker_displacementHom, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  rw [htoNat, ← hmem, MonoidHom.mem_ker, map_pow, ← toAdd_eq_zero, funext_iff]
  refine forall_congr' fun x ↦ ?_
  rw [toAdd_pow, Pi.smul_apply, Pi.zero_apply, toAdd_displacementHom_apply,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff]
  change m • (σ • x - x) ∈ maximalIdeal S • maximalIdeal S ^ (n + 2) ↔
    (m : S) * (σ • x - x) ∈ maximalIdeal S ^ (n + 3)
  rw [nsmul_eq_mul, smul_eq_mul, ← pow_succ']

/-- At positive depth `i > 0` in residue characteristic `p`, the `p`-th power of every element of
`G_i` lies in `G_{i+1}`. -/
theorem pow_mem_ramificationGroup_of_charP (p : ℕ) [CharP (ResidueField S) p] {i : ℤ}
    (hi : 0 < i) {σ : G} (hσ : σ ∈ ramificationGroup G S i) :
    σ ^ p ∈ ramificationGroup G S (i + 1) := by
  rw [pow_mem_ramificationGroup_succ_iff hi hσ p]
  intro x
  have hp : (p : S) ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero (ResidueField S) p
  have hpow : (i + 2).toNat = 1 + (i + 1).toNat := by omega
  rw [hpow, pow_add, pow_one]
  exact Ideal.mul_mem_mul hp (mem_ramificationGroup_iff.mp hσ x)

/-- Every positive-depth graded piece `G_i / G_{i+1}` (`i > 0`) is a `p`-group in residue
characteristic `p`. -/
theorem isPGroup_ramificationGroupGraded (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [MulSemiringAction G S] (p : ℕ) [CharP (ResidueField S) p] {i : ℤ}
    (hi : 0 < i) :
    IsPGroup p (RamificationGroupGraded G S i) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ g =>
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact pow_mem_ramificationGroup_of_charP p hi g.property

/-- Over a Noetherian local ring in residue characteristic `p`, every positive-depth ramification
group `G_i` (`i > 0`) of a faithful action with finite `G_0` is a `p`-group. -/
protected theorem isPGroup_ramificationGroup (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ)
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] {i : ℤ}
    (hi : 0 < i) :
    IsPGroup p (ramificationGroup G S i) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G S
  intro g
  have hpow : ∀ k : ℕ, (g : G) ^ p ^ k ∈ ramificationGroup G S (i + k) := by
    intro k
    induction k with
    | zero => simp [g.property]
    | succ k ih =>
      rw [pow_succ, pow_mul, Nat.cast_succ, ← add_assoc]
      exact pow_mem_ramificationGroup_of_charP p (by omega) ih
  refine ⟨(N - i).toNat, Subtype.ext ?_⟩
  have hmem := hpow (N - i).toNat
  rw [hN _ (by omega), Subgroup.mem_bot] at hmem
  exact hmem

/-- In residue characteristic zero, any finite positive-depth graded piece `G_i / G_{i+1}`
(`i > 0`) is trivial. -/
theorem subsingleton_ramificationGroupGraded_of_charZero (G : Type*) [Group G] (S : Type*)
    [CommRing S] [IsLocalRing S] [MulSemiringAction G S] [CharZero (ResidueField S)] {i : ℤ}
    (hi : 0 < i) [Finite (RamificationGroupGraded G S i)] :
    Subsingleton (RamificationGroupGraded G S i) := by
  refine subsingleton_iff_forall_eq 1 |>.mpr fun q ↦ ?_
  induction q using QuotientGroup.induction_on with
  | _ g =>
    -- Let `m` be the order of the class of `g` in `G_i / G_{i+1}`. Since `ResidueField S` has
    -- characteristic zero, `m` is a unit in `S`, so `m * (g • x - x) ∈ 𝔪^(i+2)` forces
    -- `g ∈ G_{i+1}`.
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

/-- Over a Noetherian local ring in residue characteristic zero, every positive-depth ramification
group `G_i` (`i > 0`) of a faithful action with finite `G_0` is trivial. -/
theorem ramificationGroup_eq_bot_of_charZero (G : Type*) [Group G] (S : Type*) [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] [CharZero (ResidueField S)]
    [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] {i : ℤ} (hi : 0 < i) :
    ramificationGroup G S i = ⊥ := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G S
  have hstep : ∀ j : ℤ, 0 < j → ramificationGroup G S j = ramificationGroup G S (j + 1) := by
    intro j hj
    have : Finite (ramificationGroup G S j) :=
      Finite.of_injective _ (Subgroup.inclusion_injective
        (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ j)))
    have hsub := subsingleton_ramificationGroupGraded_of_charZero G S hj
    rw [RamificationGroupGraded, QuotientGroup.subsingleton_iff,
      Subgroup.subgroupOf_eq_top] at hsub
    exact le_antisymm hsub (ramificationGroup_antitone G S (Int.le_add_one le_rfl))
  have hiter : ∀ k : ℕ, ramificationGroup G S i = ramificationGroup G S (i + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc, ← hstep (i + k) (by omega), ih]
  rw [hiter (N - i).toNat, hN _ (by omega)]

/-- For a faithful action on a Noetherian local ring `S` in prime residue characteristic `p` with
finite inertia `G_0` and `p ∤ [G_0 : G_1]`, the group `G_1` viewed inside `G_0` is a Sylow
`p`-subgroup. -/
def ramificationGroupOneSylowOfNotDvdIndex (G S : Type*) [Group G] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    Sylow p (ramificationGroup G S 0) :=
  ((TauCeti.IsLocalRing.isPGroup_ramificationGroup G S p (i := 1) one_pos).comap_subtype).toSylow
    hidx

/-- The subgroup underlying `ramificationGroupOneSylowOfNotDvdIndex` is `G_1` inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylowOfNotDvdIndex_coe (G S : Type*) [Group G] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    (ramificationGroupOneSylowOfNotDvdIndex G S p hidx : Subgroup (ramificationGroup G S 0)) =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) :=
  (rfl)

/-- Membership in `ramificationGroupOneSylowOfNotDvdIndex` is membership in `G_1`. -/
@[simp]
theorem mem_ramificationGroupOneSylowOfNotDvdIndex (G S : Type*) [Group G] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index)
    (σ : ramificationGroup G S 0) :
    σ ∈ ramificationGroupOneSylowOfNotDvdIndex G S p hidx ↔
      (σ : G) ∈ ramificationGroup G S 1 := by
  rw [← SetLike.mem_coe, ← Sylow.coe_coe, ramificationGroupOneSylowOfNotDvdIndex_coe,
    SetLike.mem_coe, Subgroup.mem_subgroupOf]

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
instance ramificationGroupOneSylowOfNotDvdIndex_normal (G S : Type*) [Group G] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    (ramificationGroupOneSylowOfNotDvdIndex G S p hidx :
      Subgroup (ramificationGroup G S 0)).Normal := by
  rw [ramificationGroupOneSylowOfNotDvdIndex_coe]
  infer_instance

/-- For a faithful action on a Noetherian local ring `S` in prime residue characteristic `p` with
finite inertia `G_0` and `p ∤ [G_0 : G_1]`, the group `G_1` is the unique Sylow `p`-subgroup of
`G_0`. -/
theorem eq_ramificationGroupOneSylowOfNotDvdIndex (G S : Type*) [Group G] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index)
    (Q : Sylow p (ramificationGroup G S 0)) :
    Q = ramificationGroupOneSylowOfNotDvdIndex G S p hidx := by
  let _ : Unique (Sylow p (ramificationGroup G S 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylowOfNotDvdIndex G S p hidx) inferInstance
  exact Subsingleton.elim _ _

/-- For a faithful action on a Noetherian local ring `S` in prime residue characteristic `p` with
finite inertia `G_0` and `p ∤ [G_0 : G_1]`, the cardinality of `G_1` is `p ^ v_p(#G_0)`. -/
theorem natCard_ramificationGroup_one_of_not_dvd_index (G S : Type*) [Group G] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [MulSemiringAction G S] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hidx : ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index) :
    Nat.card (ramificationGroup G S 1) =
      p ^ (Nat.card (ramificationGroup G S 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylowOfNotDvdIndex G S p hidx)]
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
    rw [ramificationGroup_eq_bot_of_charZero G S one_pos, zero_dvd_iff]
    exact iff_of_true rfl Nat.card_pos.ne'

end PositiveDepth

end IsLocalRing

end TauCeti

namespace Subgroup

open TauCeti.IsLocalRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [MulSemiringAction G S]

/-- Every coset `σ H` of a finite subgroup contains an element `σ τ₀` of largest lower index. -/
theorem exists_mem_forall_lowerIndex_mul_le (H : Subgroup G) [Finite H] (σ : G) :
    ∃ τ₀ ∈ H, ∀ τ ∈ H, lowerIndex S (σ * τ₀ * τ) ≤ lowerIndex S (σ * τ₀) := by
  obtain ⟨τ₀, hτ₀⟩ := Finite.exists_max fun τ : H ↦ lowerIndex S (σ * τ)
  refine ⟨τ₀, τ₀.property, fun τ hτ ↦ ?_⟩
  simpa only [coe_mul, mul_assoc] using hτ₀ (τ₀ * ⟨τ, hτ⟩)

end Subgroup
