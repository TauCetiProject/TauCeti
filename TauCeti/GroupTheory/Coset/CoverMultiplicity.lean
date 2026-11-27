/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Orbit.Weight
import TauCeti.GroupTheory.Index.DvdPow

/-!
# Cover multiplicities

Let a group `G` act on `X`, let `S` and `A` be subgroups of `G` and `T ⊆ X`. The
**cover multiplicity** of a point `t` counts the classes `r (S ∩ A)` of elements `r ∈ S` with
`r⁻¹ • t ∈ T`, a class being counted when at least one of its representatives qualifies, and it is
`0` when there are infinitely many. Inverting representatives identifies these classes with the
right cosets `(S ∩ A) g`, `g ∈ S`, with `g • t ∈ T`, so the cover multiplicity is the orbit weight
`(A.subgroupOf S).orbitWeight T t` of the action of `S` (`Subgroup.coverMultiplicity_def`), and
the whole orbit-weight API applies to it; in particular the counted cosets are
`(A.subgroupOf S).orbitWeightCosets T t`, tested on a chosen representative by
`Subgroup.mk_mem_orbitWeightCosets_iff` when `T` is stable under `S ∩ A`. Read on left cosets of
`A` in `G`, it is the number of cosets `r A` of the `r ∈ S` with `r⁻¹ • t ∈ T`
(`Subgroup.coverMultiplicity_eq_ncard_image`).

When `T` is stable under `S ∩ A`, the condition `r⁻¹ • t ∈ T` depends only on the class of `r`, so
the multiplicity of `t` counts the classes `r (S ∩ A)` with `t ∈ r • T`. It is constant on
`S`-orbits (`Subgroup.coverMultiplicity_smul`), so dividing by it normalizes the cover by the
translates of `T` pointwise: at a point `t` of finite, nonzero multiplicity, the sum of
`1_T(r⁻¹ • t) / mult(r⁻¹ • t)` over all classes `r (S ∩ A)` is `1`.

When the points of `T` in the `S`-orbit of `t` lie in the `(S ∩ A)`-orbit of `t`, and there is
at least one, the multiplicity of `t` is the relative index `A.relIndex H`, the index of `A ∩ H`
in the stabiliser `H` of `t` in `S`. If it is finite (nonzero) and every element of `H` has a
`q`-power power in `A`, it divides a power of `q`, by
`Subgroup.exists_index_dvd_pow_of_forall_exists_pow_pow_mem`.

For the left cosets of compact open subgroups of a topological group, finite sets `T` with these
properties are constructed in `TauCeti.Topology.Algebra.Group.CoverMultiplicity`.

## Main definitions

* `Subgroup.coverMultiplicity S A T t`: the number of classes of `r ∈ S` modulo `S ∩ A` with
  `r⁻¹ • t ∈ T`, and `0` if there are infinitely many.

## Main results

* `Subgroup.coverMultiplicity_eq_ncard_image`: the cover multiplicity counts the cosets `r A` of
  the `r ∈ S` with `r⁻¹ • t ∈ T`; `Subgroup.finite_orbitWeightCosets_subgroupOf_iff` is the same
  comparison for finiteness.
* `Subgroup.coverMultiplicity_smul`: the cover multiplicity is constant on `S`-orbits.
* `Subgroup.coverMultiplicity_eq_relIndex`: if the points of `T` in the `S`-orbit of `t` lie in
  the `(S ∩ A)`-orbit of `t`, and there is at least one, the cover multiplicity of `t` is the
  relative index `A.relIndex H`, the index of `A ∩ H` in the stabiliser `H` of `t` in `S`.
* `Subgroup.exists_coverMultiplicity_dvd_pow`: in that situation, if the multiplicity is finite
  (nonzero) and every element of `H` has a `q`-power power in `A`, the multiplicity divides a
  power of `q`.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93, for the class sets of
  groups compact at infinity weighted by inverse orders of stabilisers.
* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/New/UpperBound/Seesaw/IntegralAsCosetSum.lean` (declarations
  `New.Seesaw.coverMultiplicity` and `New.Seesaw.coverMultiplicity_smul`); Apache 2.0, Copyright
  2026 Anthropic, PBC. The definition and the description of the multiplicity as the index of a
  stabiliser follow the method of this proof.
-/

public section

open MulAction QuotientGroup

namespace Subgroup

variable {G X : Type*} [Group G] [MulAction G X] (S A : Subgroup G) (T : Set X)

/-- The **cover multiplicity** of a point `t`, for subgroups `S`, `A` of `G` and a set `T ⊆ X`:
the number of classes `r (S ∩ A)` of elements `r ∈ S` with `r⁻¹ • t ∈ T`, a class being counted
when at least one of its representatives qualifies, and `0` if there are infinitely many. It is
the orbit weight of the action of `S`, the class `r (S ∩ A)` being recorded by the right coset
`(S ∩ A) r⁻¹` of `A.subgroupOf S`. When `T` is stable under `S ∩ A`, the condition `r⁻¹ • t ∈ T`
depends only on the class of `r`. -/
noncomputable def coverMultiplicity (t : X) : ℕ :=
  (A.subgroupOf S).orbitWeight T t

/-- The cover multiplicity is the orbit weight of the action of `S` relative to `S ∩ A`: the
number of right cosets `(S ∩ A) g`, `g ∈ S`, with `g • t ∈ T`. -/
theorem coverMultiplicity_def (t : X) :
    S.coverMultiplicity A T t = (A.subgroupOf S).orbitWeight T t :=
  (rfl)

/-- Inverting representatives, `(S ∩ A) g ↦ g⁻¹ A`, embeds the right cosets of `S ∩ A` in `S`
into the left cosets of `A` in `G`, and carries the cosets counted by the cover multiplicity onto
the cosets `r A` of the `r ∈ S` with `r⁻¹ • t ∈ T`. -/
private theorem exists_injective_image_orbitWeightCosets_eq (t : X) :
    ∃ F : Quotient (rightRel (A.subgroupOf S)) → G ⧸ A, F.Injective ∧
      F '' (A.subgroupOf S).orbitWeightCosets T t =
        ((↑) : G → G ⧸ A) '' {r | r ∈ S ∧ r⁻¹ • t ∈ T} := by
  have hrel (a b : S) :
      rightRel (A.subgroupOf S) a b ↔ (((a : G)⁻¹ : G) : G ⧸ A) = ((b : G)⁻¹ : G) := by
    rw [rightRel_apply, QuotientGroup.eq, inv_inv, mem_subgroupOf, ← inv_mem_iff]
    simp
  refine ⟨Quotient.lift (fun g : S ↦ (((g : G)⁻¹ : G) : G ⧸ A)) fun a b hab ↦ (hrel a b).1 hab,
    fun c d hcd ↦ ?_, ?_⟩
  · induction c using Quotient.inductionOn
    induction d using Quotient.inductionOn
    exact Quotient.sound ((hrel _ _).2 hcd)
  · ext q
    simp only [Set.mem_image, mem_orbitWeightCosets, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨(g : G)⁻¹, ⟨inv_mem g.property, by rwa [inv_inv, ← Subgroup.smul_def]⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hrt⟩, rfl⟩
      exact ⟨_, ⟨⟨r⁻¹, inv_mem hr⟩, by rwa [Subgroup.mk_smul], rfl⟩, by simp⟩

/-- The cover multiplicity is the number of left cosets `r A` of the elements `r ∈ S` with
`r⁻¹ • t ∈ T`. -/
theorem coverMultiplicity_eq_ncard_image (t : X) :
    S.coverMultiplicity A T t = (((↑) : G → G ⧸ A) '' {r | r ∈ S ∧ r⁻¹ • t ∈ T}).ncard := by
  obtain ⟨F, hF, himage⟩ := exists_injective_image_orbitWeightCosets_eq S A T t
  rw [coverMultiplicity_def, orbitWeight_def, ← himage, Set.ncard_image_of_injective _ hF]

/-- Finitely many classes are counted by the cover multiplicity exactly when finitely many left
cosets `r A` of elements `r ∈ S` satisfy `r⁻¹ • t ∈ T`. -/
theorem finite_orbitWeightCosets_subgroupOf_iff (t : X) :
    ((A.subgroupOf S).orbitWeightCosets T t).Finite ↔
      (((↑) : G → G ⧸ A) '' {r | r ∈ S ∧ r⁻¹ • t ∈ T}).Finite := by
  obtain ⟨F, hF, himage⟩ := exists_injective_image_orbitWeightCosets_eq S A T t
  rw [← himage, Set.finite_image_iff hF.injOn]

variable {S A T}

/-- **The cover multiplicity is constant on `S`-orbits.** -/
@[simp]
theorem coverMultiplicity_smul {s : G} (hs : s ∈ S) (t : X) :
    S.coverMultiplicity A T (s • t) = S.coverMultiplicity A T t := by
  rw [coverMultiplicity_def, coverMultiplicity_def, ← Subgroup.mk_smul s hs, orbitWeight_smul]

/-- **The cover multiplicity as the index of a stabiliser.** If `T` meets the `S`-orbit of `t`,
and only in points of the `(S ∩ A)`-orbit of `t`, then the cover multiplicity of `t` is the index
of `A ∩ H` in the stabiliser `H = S ∩ Stab(t)` of `t` in `S`. -/
theorem coverMultiplicity_eq_relIndex {t : X} (hT : (T ∩ orbit S t).Nonempty)
    (hTA : T ∩ orbit S t ⊆ orbit (S ⊓ A : Subgroup G) t) :
    S.coverMultiplicity A T t = A.relIndex (S ⊓ stabilizer G t) := by
  -- The only `(S ∩ A)`-orbit of a point of `T` in the `S`-orbit of `t` is the orbit of `t`.
  have hclasses : (A.subgroupOf S).orbitCountClasses T t =
      {Quotient.mk (orbitRel (A.subgroupOf S) X) t} := by
    have hmk : ∀ x ∈ T ∩ orbit S t,
        Quotient.mk (orbitRel (A.subgroupOf S) X) x = Quotient.mk _ t := by
      intro x hx
      obtain ⟨⟨a, ha⟩, rfl⟩ := hTA hx
      exact Quotient.sound (orbitRel_apply.2
        ⟨⟨⟨a, ha.1⟩, mem_subgroupOf.2 ha.2⟩, by simp only [Subgroup.mk_smul]⟩)
    refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hT
      exact mem_orbitCountClasses.2 ⟨x, hx.2, hx.1, hmk x hx⟩
    · intro o ho
      obtain ⟨x, hxS, hxT, rfl⟩ := mem_orbitCountClasses.1 ho
      exact hmk x ⟨hxT, hxS⟩
  rw [coverMultiplicity_def, orbitWeight_def, orbitWeightCosets_eq_preimage, hclasses,
    ncard_fiber_orbitOfRightCoset_eq_relIndex (mem_orbit_self t), ← stabilizer_subgroupOf,
    ← inf_subgroupOf_left (stabilizer G t) S, relIndex_subgroupOf inf_le_left]

/-- **The cover multiplicity divides a power of `q`.** If the points of `T` in the `S`-orbit of
`t` lie in the `(S ∩ A)`-orbit of `t`, the cover multiplicity of `t` is finite and nonzero, and
every element `g` of the stabiliser of `t` in `S` has a power `g ^ q ^ n` in `A`, then the cover
multiplicity of `t` divides a power of `q`. -/
theorem exists_coverMultiplicity_dvd_pow {t : X}
    (hTA : T ∩ orbit S t ⊆ orbit (S ⊓ A : Subgroup G) t)
    (hne : S.coverMultiplicity A T t ≠ 0) {q : ℕ}
    (hq : ∀ g ∈ S ⊓ stabilizer G t, ∃ n : ℕ, g ^ q ^ n ∈ A) :
    ∃ n : ℕ, S.coverMultiplicity A T t ∣ q ^ n := by
  -- A nonzero multiplicity counts some coset, whose representatives carry `t` into `T`.
  have hT : (T ∩ orbit S t).Nonempty := by
    rw [coverMultiplicity_def, orbitWeight_def] at hne
    obtain ⟨c, hc⟩ := Set.nonempty_of_ncard_ne_zero hne
    obtain ⟨g, hg, -⟩ := mem_orbitWeightCosets.1 hc
    exact ⟨g • t, hg, mem_orbit t g⟩
  rw [coverMultiplicity_eq_relIndex hT hTA] at hne ⊢
  have : (A.subgroupOf (S ⊓ stabilizer G t)).FiniteIndex := ⟨hne⟩
  exact (A.subgroupOf _).exists_index_dvd_pow_of_forall_exists_pow_pow_mem fun g ↦ by
    simpa [mem_subgroupOf] using hq g g.property

end Subgroup
