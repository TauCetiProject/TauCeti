/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.PGroup
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
* `TauCeti.IsLocalRing.mem_ramificationGroup_natCast_iff_smul_sub_mem_of_span_eq_maximalIdeal`:
  when `S` has principal maximal ideal `(π)` and separable residue extension over a base local
  ring `R` fixed by `G`, membership of `σ ∈ G_0` in `G_n` is decided at `π` alone.
* `TauCeti.IsLocalRing.commutator_ramificationGroup_natCast_succ_le`: each positive graded piece
  `G_{n+1} / G_{n+2}` is abelian.
* `TauCeti.IsLocalRing.isPGroup_ramificationGroupGraded_natCast_succ` and
  `TauCeti.IsLocalRing.isPGroup_ramificationGroup`: in residue characteristic `p`, each positive
  graded piece has exponent dividing `p`, and over a Noetherian local ring with faithful action
  and finite inertia each `G_i` (`i > 0`) is a `p`-group.
* `TauCeti.IsLocalRing.ramificationGroup_eq_bot_of_charZero` and
  `TauCeti.IsLocalRing.ramificationGroup_one_eq_bot_of_charZero`: in residue characteristic zero,
  every finite-order element of `G_1` over a Noetherian local ring acts trivially, so when `G_0`
  is finite and the action is faithful every `G_i` (`i > 0`) is trivial.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–2.
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
      exact σ.2
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

section SeparableResidue

open Polynomial

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- **Testing `G_n` at a generator of the maximal ideal.** Let `S` be a local `R`-algebra whose
maximal ideal is generated by `π` and whose residue extension over `ResidueField R` is separable,
and let `G` act on `S` by `R`-algebra automorphisms. Then an element `σ ∈ G_0` lies in `G_n` if
and only if `σ • π - π ∈ 𝔪 ^ (n + 1)`.

Unlike `mem_ramificationGroup_iff_of_adjoin_singleton_eq_top`, this needs neither monogenicity nor
module finiteness of `S` over `R`: each element `x : S` is tested individually by Taylor-expanding
a lift of the separable minimal polynomial of `residue S x`. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem_of_span_eq_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S] [IsLocalHom (algebraMap R S)]
    [SMulCommClass G R S] [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
    {π : S} (hπ : Ideal.span {π} = maximalIdeal S) {n : ℕ} {σ : G}
    (hσ₀ : σ ∈ ramificationGroup G S 0) :
    σ ∈ ramificationGroup G S n ↔ σ • π - π ∈ maximalIdeal S ^ (n + 1) := by
  refine ⟨fun hσ ↦ mem_ramificationGroup_natCast_iff.mp hσ π, ?_⟩
  induction n with
  | zero => exact fun _ ↦ by exact_mod_cast hσ₀
  | succ n ih =>
    intro hπn
    have hσn : σ ∈ ramificationGroup G S n := ih (Ideal.pow_le_pow_right (by omega) hπn)
    have hπmem : π ∈ maximalIdeal S := hπ ▸ Ideal.mem_span_singleton_self π
    refine mem_ramificationGroup_natCast_iff.mpr fun x ↦ ?_
    -- Lift the separable minimal polynomial of `residue S x` to `g : R[X]`; then `aeval x g`
    -- lies in `(π)`, say `aeval x g = π * y`, while `aeval x (derivative g)` is a unit.
    obtain ⟨g, hg⟩ := (mem_lifts _).mp
      (mem_lifts_of_surjective residue_surjective (minpoly (ResidueField R) (residue S x)))
    have hg₀ : aeval x g ∈ maximalIdeal S := by
      rw [← residue_eq_zero_iff, map_aeval_eq_aeval_map (residue_comp_algebraMap (R := R)), hg]
      exact minpoly.aeval _ _
    obtain ⟨y, hy⟩ : ∃ y : S, aeval x g = π * y :=
      Ideal.mem_span_singleton.mp (hπ.symm ▸ hg₀)
    have hσg : aeval (σ • x) g = σ • aeval x g := by
      simpa only [MulSemiringAction.toAlgEquiv_apply] using
        aeval_algHom_apply (MulSemiringAction.toAlgEquiv R S σ) x g
    -- Applying `σ` to `aeval x g = π * y` and using the induction hypothesis on `y` shows
    -- `aeval (σ • x) g - aeval x g ∈ 𝔪 ^ (n + 2)`.
    have hg_diff : aeval (σ • x) g - aeval x g ∈ maximalIdeal S ^ (n + 2) := by
      have hsplit : aeval (σ • x) g - aeval x g = (σ • π - π) * (σ • y) + π * (σ • y - y) := by
        rw [hσg, hy, smul_mul']
        ring
      rw [hsplit]
      refine add_mem (Ideal.mul_mem_right _ _ hπn) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hπmem (mem_ramificationGroup_natCast_iff.mp hσn y)
    -- Taylor-expand `g` at `x`: the quadratic remainder lies in `(𝔪 ^ (n + 1)) ^ 2 ≤ 𝔪 ^ (n + 2)`,
    -- and the linear coefficient `aeval x (derivative g)` is a unit by separability.
    obtain ⟨k, hk⟩ := binomExpansion (g.map (algebraMap R S)) x (σ • x - x)
    have hlin : aeval x (derivative g) * (σ • x - x) =
        (aeval (σ • x) g - aeval x g) - (σ • x - x) ^ 2 * k := by
      rw [add_sub_cancel, eval_map, eval_map, ← aeval_def, ← aeval_def,
        derivative_map, eval_map, ← aeval_def] at hk
      linear_combination -hk
    have hsq : (σ • x - x) ^ 2 * k ∈ maximalIdeal S ^ (n + 2) :=
      Ideal.mul_mem_right k _ <| Ideal.pow_le_pow_right (by omega : n + 2 ≤ (n + 1) * 2) <| by
        rw [pow_mul]
        exact Ideal.pow_mem_pow (mem_ramificationGroup_natCast_iff.mp hσn x) 2
    have hder : IsUnit (aeval x (derivative g)) := by
      rw [← residue_ne_zero_iff_isUnit,
        map_aeval_eq_aeval_map (residue_comp_algebraMap (R := R)), ← derivative_map, hg]
      exact (Algebra.IsSeparable.isSeparable (ResidueField R) (residue S x))
        |>.aeval_derivative_ne_zero (minpoly.aeval _ _)
    have hprod : aeval x (derivative g) * (σ • x - x) ∈ maximalIdeal S ^ (n + 2) :=
      hlin.symm ▸ sub_mem hg_diff hsq
    simpa only [IsUnit.val_inv_mul, one_mul, ← mul_assoc] using
      Ideal.mul_mem_left _ (↑hder.unit⁻¹ : S) hprod

end SeparableResidue

section HigherRamification

open scoped commutatorElement

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- An element of `G_1` moves every positive power `𝔪 ^ k` (`k ≥ 1`) into `𝔪 ^ (k + 1)`. -/
theorem smul_sub_mem_maximalIdeal_pow_succ_of_mem_ramificationGroup_one
    {σ : G} (hσ : σ ∈ ramificationGroup G S 1) {k : ℕ} (hk : 1 ≤ k) {y : S}
    (hy : y ∈ maximalIdeal S ^ k) :
    σ • y - y ∈ maximalIdeal S ^ (k + 1) := by
  have hσ₁ : σ ∈ ramificationGroup G S (1 : ℕ) := by exact_mod_cast hσ
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  induction m generalizing y with
  | zero => exact mem_ramificationGroup_natCast_iff.mp hσ₁ y
  | succ m ih =>
    rw [pow_succ'] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb ↦ ?_) (fun u v hu hv ↦ ?_)
    · have hsplit : σ • (a * b) - a * b = (σ • a - a) * (σ • b) + a * (σ • b - b) := by
        rw [smul_mul']
        ring
      rw [hsplit]
      have hleft : (σ • a - a) * (σ • b) ∈ maximalIdeal S ^ (m + 1 + 1 + 1) := by
        have hadd : 2 + (m + 1) = m + 1 + 1 + 1 := by omega
        rw [← hadd, pow_add]
        exact Ideal.mul_mem_mul (mem_ramificationGroup_natCast_iff.mp hσ₁ a)
          ((smul_mem_maximalIdeal_pow_iff σ).mpr hb)
      have hright : a * (σ • b - b) ∈ maximalIdeal S ^ (m + 1 + 1 + 1) := by
        rw [pow_succ' (maximalIdeal S) (m + 1 + 1)]
        exact Ideal.mul_mem_mul ha (ih (Nat.succ_pos m) hb)
      exact add_mem hleft hright
    · have hadd : σ • (u + v) - (u + v) = (σ • u - u) + (σ • v - v) := by
        rw [smul_add]
        ring
      rw [hadd]
      exact add_mem hu hv

/-- At positive depth `n + 1`, the displacement of `σ * τ` is the sum of the displacements of `σ`
and `τ` modulo `𝔪 ^ (n + 3)`. -/
private theorem mul_smul_sub_mem_maximalIdeal_pow_add_three
    {n : ℕ} {σ τ : G} (hσ : σ ∈ ramificationGroup G S ((n : ℤ) + 1))
    (hτ : τ ∈ ramificationGroup G S ((n : ℤ) + 1)) (x : S) :
    (σ * τ) • x - x - ((σ • x - x) + (τ • x - x)) ∈ maximalIdeal S ^ (n + 3) := by
  have hσ₁ : σ ∈ ramificationGroup G S 1 := ramificationGroup_antitone G S (by omega) hσ
  have hτn : τ ∈ ramificationGroup G S (n + 1 : ℕ) := by exact_mod_cast hτ
  have hid : (σ * τ) • x - x - ((σ • x - x) + (τ • x - x)) = σ • (τ • x - x) - (τ • x - x) := by
    rw [mul_smul, smul_sub]
    ring
  rw [hid]
  exact smul_sub_mem_maximalIdeal_pow_succ_of_mem_ramificationGroup_one hσ₁ (by omega)
    (mem_ramificationGroup_natCast_iff.mp hτn x)

variable (G S) in
/-- **Positive ramification quotients are abelian.** For every `n : ℕ`, the commutator subgroup of
`G_{n+1}` lies in `G_{n+2}`. -/
theorem commutator_ramificationGroup_natCast_succ_le (n : ℕ) :
    ⁅ramificationGroup G S ((n : ℤ) + 1), ramificationGroup G S ((n : ℤ) + 1)⁆ ≤
      ramificationGroup G S ((n : ℤ) + 2) := by
  rw [Subgroup.commutator_le]
  intro σ hσ τ hτ
  have hcast : ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, mem_ramificationGroup_natCast_iff]
  intro z
  let x : S := (σ⁻¹ * τ⁻¹) • z
  have hcomm : ⁅σ, τ⁆ • z - z =
      ((σ * τ) • x - x - ((σ • x - x) + (τ • x - x))) -
        ((τ * σ) • x - x - ((τ • x - x) + (σ • x - x))) := by
    simp only [x, commutatorElement_def, mul_smul, smul_inv_smul]
    ring
  rw [hcomm]
  exact sub_mem (mul_smul_sub_mem_maximalIdeal_pow_add_three hσ hτ x)
    (mul_smul_sub_mem_maximalIdeal_pow_add_three hτ hσ x)

/-- Multiplication in each positive graded piece `G_{n+1} / G_{n+2}` is commutative. -/
theorem ramificationGroupGraded_natCast_succ_mul_comm {n : ℕ}
    (a b : RamificationGroupGraded G S ((n : ℤ) + 1)) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | _ σ =>
    induction b using QuotientGroup.induction_on with
    | _ τ =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have hmem : ⁅(τ⁻¹ : G), (σ⁻¹ : G)⁆ ∈
          ⁅ramificationGroup G S ((n : ℤ) + 1), ramificationGroup G S ((n : ℤ) + 1)⁆ :=
        Subgroup.commutator_mem_commutator (inv_mem τ.2) (inv_mem σ.2)
      have h := commutator_ramificationGroup_natCast_succ_le G S n hmem
      have heq : (((σ * τ)⁻¹ * (τ * σ) : ramificationGroup G S ((n : ℤ) + 1)) : G) =
          ⁅(τ⁻¹ : G), (σ⁻¹ : G)⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      have hidx : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by ring
      rwa [heq, hidx]

/-- Iterating an element `σ ∈ G_{n+1}` multiplies its displacement by `m` modulo `𝔪 ^ (n + 3)`. -/
theorem pow_smul_sub_mem_maximalIdeal_pow_add_three
    {n : ℕ} {σ : G} (hσ : σ ∈ ramificationGroup G S ((n : ℤ) + 1)) (m : ℕ) (x : S) :
    (σ ^ m) • x - x - (m : S) * (σ • x - x) ∈ maximalIdeal S ^ (n + 3) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hid : (σ ^ (m + 1)) • x - x - ((m + 1 : ℕ) : S) * (σ • x - x) =
        ((σ * σ ^ m) • x - x - ((σ • x - x) + ((σ ^ m) • x - x))) +
          ((σ ^ m) • x - x - (m : S) * (σ • x - x)) := by
      rw [pow_succ']
      push_cast
      ring
    rw [hid]
    exact add_mem (mul_smul_sub_mem_maximalIdeal_pow_add_three hσ (pow_mem hσ m) x) ih

/-- In residue characteristic `p`, the `p`-th power of every element of `G_{n+1}` lies in
`G_{n+2}`. -/
theorem pow_mem_ramificationGroup_natCast_add_two (p : ℕ) [CharP (ResidueField S) p]
    {n : ℕ} {σ : G} (hσ : σ ∈ ramificationGroup G S ((n : ℤ) + 1)) :
    σ ^ p ∈ ramificationGroup G S ((n : ℤ) + 2) := by
  have hp : (p : S) ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero (ResidueField S) p
  have hσn : σ ∈ ramificationGroup G S (n + 1 : ℕ) := by exact_mod_cast hσ
  have hcast : ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, mem_ramificationGroup_natCast_iff]
  intro x
  have hpmul : (p : S) * (σ • x - x) ∈ maximalIdeal S ^ (n + 3) := by
    rw [pow_succ' (maximalIdeal S) (n + 2)]
    exact Ideal.mul_mem_mul hp (mem_ramificationGroup_natCast_iff.mp hσn x)
  simpa only [sub_add_cancel] using
    add_mem (pow_smul_sub_mem_maximalIdeal_pow_add_three hσ p x) hpmul

variable (G S) in
/-- In residue characteristic `p`, every positive graded piece `G_{n+1} / G_{n+2}` is a
`p`-group. -/
theorem isPGroup_ramificationGroupGraded_natCast_succ (p : ℕ) [CharP (ResidueField S) p] (n : ℕ) :
    IsPGroup p (RamificationGroupGraded G S ((n : ℤ) + 1)) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  induction g using QuotientGroup.induction_on with
  | _ σ =>
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hidx : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by ring
    rw [hidx]
    exact pow_mem_ramificationGroup_natCast_add_two p σ.2

variable (G S) in
/-- **Positive-depth ramification groups are `p`-groups.** Over a Noetherian local ring of residue
characteristic `p` with faithful action and finite inertia group `G_0`, every ramification group
`G_i` with `0 < i` is a `p`-group. -/
theorem isPGroup_ramificationGroup (p : ℕ) [CharP (ResidueField S) p]
    [IsNoetherianRing S] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    {i : ℤ} (hi : 0 < i) :
    IsPGroup p (ramificationGroup G S i) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G S
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨N.toNat, ?_⟩
  have hpow : ∀ k : ℕ, (g : G) ^ (p ^ k) ∈ ramificationGroup G S (i + k) := by
    intro k
    induction k with
    | zero => simp [g.2]
    | succ k ih =>
      have hidx1 : i + (k : ℤ) = (((i + k - 1).toNat : ℤ) + 1) := by omega
      have hidx2 : (((i + k - 1).toNat : ℤ) + 2) = i + ((k + 1 : ℕ) : ℤ) := by omega
      rw [pow_succ, pow_mul, ← hidx2]
      exact pow_mem_ramificationGroup_natCast_add_two p (hidx1 ▸ ih)
  have hbot : ramificationGroup G S (i + (N.toNat : ℤ)) = ⊥ := hN _ (by omega)
  have hg1 : (g : G) ^ (p ^ N.toNat) = 1 := by
    have hmem := hpow N.toNat
    rwa [hbot, Subgroup.mem_bot] at hmem
  exact Subtype.ext hg1

/-- In residue characteristic zero, each positive graded piece `G_{n+1} / G_{n+2}` is torsion-free:
if `σ ∈ G_{n+1}` and `σ ^ m ∈ G_{n+2}` with `m ≠ 0`, then `σ ∈ G_{n+2}`. -/
theorem mem_ramificationGroup_natCast_add_two_of_pow_mem [CharZero (ResidueField S)]
    {n : ℕ} {σ : G} (hσ : σ ∈ ramificationGroup G S ((n : ℤ) + 1)) {m : ℕ} (hm : m ≠ 0)
    (hpow : σ ^ m ∈ ramificationGroup G S ((n : ℤ) + 2)) :
    σ ∈ ramificationGroup G S ((n : ℤ) + 2) := by
  have hm_unit : IsUnit (m : S) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    exact Nat.cast_ne_zero.mpr hm
  have hcast : ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, mem_ramificationGroup_natCast_iff] at hpow ⊢
  intro x
  have hmul : (m : S) * (σ • x - x) ∈ maximalIdeal S ^ (n + 3) := by
    simpa only [sub_sub_cancel] using
      sub_mem (hpow x) (pow_smul_sub_mem_maximalIdeal_pow_add_three hσ m x)
  simpa only [IsUnit.val_inv_mul, one_mul, ← mul_assoc] using
    Ideal.mul_mem_left _ (↑hm_unit.unit⁻¹ : S) hmul

/-- Over a Noetherian local ring of residue characteristic zero, every finite-order element of
`G_1` acts trivially on `S`. -/
theorem mem_ker_toRingAut_of_mem_ramificationGroup_one_of_isOfFinOrder
    [IsNoetherianRing S] [CharZero (ResidueField S)] {σ : G}
    (hσ : σ ∈ ramificationGroup G S 1) (hfin : IsOfFinOrder σ) :
    σ ∈ MonoidHom.ker (MulSemiringAction.toRingAut G S) := by
  have hstep : ∀ n : ℕ, σ ∈ ramificationGroup G S ((n : ℤ) + 1) := by
    intro n
    induction n with
    | zero => simpa using hσ
    | succ n ih =>
      refine mem_ramificationGroup_natCast_add_two_of_pow_mem ih hfin.orderOf_pos.ne' ?_
      rw [pow_orderOf_eq_one]
      exact one_mem _
  rw [← iInf_ramificationGroup_eq_ker, Subgroup.mem_iInf]
  intro i
  by_cases hi : 1 ≤ i
  · have hidx : i = ((i - 1).toNat : ℤ) + 1 := by omega
    rw [hidx]
    exact hstep (i - 1).toNat
  · exact ramificationGroup_antitone G S (by omega : i ≤ 1) hσ

/-- Over a Noetherian local ring of residue characteristic zero with faithful action, the only
finite-order element of `G_1` is `1`. -/
theorem eq_one_of_mem_ramificationGroup_one_of_isOfFinOrder
    [IsNoetherianRing S] [FaithfulSMul G S] [CharZero (ResidueField S)] {σ : G}
    (hσ : σ ∈ ramificationGroup G S 1) (hfin : IsOfFinOrder σ) : σ = 1 := by
  have hmem := mem_ker_toRingAut_of_mem_ramificationGroup_one_of_isOfFinOrder hσ hfin
  rwa [TauCeti.MulSemiringAction.ker_toRingAut_eq_bot, Subgroup.mem_bot] at hmem

variable (G S) in
/-- **Positive-depth ramification groups vanish in residue characteristic zero.** Over a Noetherian
local ring with residue field of characteristic zero, faithful action, and finite inertia group
`G_0`, every ramification group `G_i` with `0 < i` is trivial. -/
theorem ramificationGroup_eq_bot_of_charZero
    [IsNoetherianRing S] [FaithfulSMul G S] [CharZero (ResidueField S)]
    [Finite (ramificationGroup G S 0)] {i : ℤ} (hi : 0 < i) :
    ramificationGroup G S i = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  have hσ₁ : σ ∈ ramificationGroup G S 1 := ramificationGroup_antitone G S (by omega) hσ
  have hσ₀ : σ ∈ ramificationGroup G S 0 := ramificationGroup_antitone G S (by omega) hσ
  have hfin₀ : IsOfFinOrder (⟨σ, hσ₀⟩ : ramificationGroup G S 0) := isOfFinOrder_of_finite _
  have hfin : IsOfFinOrder σ := by
    rw [isOfFinOrder_iff_pow_eq_one] at hfin₀ ⊢
    obtain ⟨m, hm, hpow⟩ := hfin₀
    exact ⟨m, hm, congrArg Subtype.val hpow⟩
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_ramificationGroup_one_of_isOfFinOrder hσ₁ hfin

variable (G S) in
/-- Over a Noetherian local ring with residue field of characteristic zero, faithful action, and
finite inertia group `G_0`, the wild inertia group `G_1` is trivial. -/
theorem ramificationGroup_one_eq_bot_of_charZero
    [IsNoetherianRing S] [FaithfulSMul G S] [CharZero (ResidueField S)]
    [Finite (ramificationGroup G S 0)] :
    ramificationGroup G S 1 = ⊥ :=
  ramificationGroup_eq_bot_of_charZero G S zero_lt_one

end HigherRamification

end IsLocalRing

end TauCeti
