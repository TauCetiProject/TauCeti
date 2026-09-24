/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import TauCeti.Algebra.Group.Subgroup.FiniteFiltration
public import TauCeti.Algebra.Ring.Action.End
public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.Ideal.Inertia
public import TauCeti.RingTheory.Ideal.RamificationGroup
public import TauCeti.RingTheory.LocalRing.Pointwise

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

## Main results

* `TauCeti.IsLocalRing.ramificationGroup_natCast`: at a nonnegative index `G_i` is
  `Ideal.ramificationGroup` of the maximal ideal.
* `TauCeti.IsLocalRing.ramificationGroup_eq_top_of_le_neg_one` and
  `TauCeti.IsLocalRing.ramificationGroup_antitone`: the filtration starts at `⊤` and decreases.
* `TauCeti.IsLocalRing.ramificationGroup_zero_eq_inertia`: `G_0` is the inertia subgroup of the
  maximal ideal, `TauCeti.IsLocalRing.ramificationGroup_zero_eq_ker_toRingAut` identifies it with
  the kernel of the action on the residue field, and
  `TauCeti.IsLocalRing.ramificationGroup_zero_eq_inertiaSubgroup` reads that off as Mathlib's
  `ValuationSubring.inertiaSubgroup` for a valuation subring of a field.
* `TauCeti.IsLocalRing.instNormalRamificationGroup`: each `G_i` is normal in `G`.
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
  defining condition is the valuation inequality `v (σ x - x) ≥ i + 1`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1.
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

end DiscreteValuationRing

section Subgroup

variable (G : Type*) [Group G] (S : Type*) [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- The ramification filtration of a subgroup is the trace on it of the ramification filtration of
the ambient group. -/
@[simp]
theorem subgroupOf_ramificationGroup (H : Subgroup G) (i : ℤ) :
    (ramificationGroup G S i).subgroupOf H = ramificationGroup H S i :=
  AddSubgroup.subgroupOf_inertia _ H

end Subgroup

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

end IsLocalRing

end TauCeti
