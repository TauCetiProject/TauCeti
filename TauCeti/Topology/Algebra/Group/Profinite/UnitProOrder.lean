/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Order
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
import TauCeti.Topology.Algebra.Group.Profinite.Basic
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Order

/-!
# Profinite groups of invertible pro-order

Averaging over a compact open subgroup `K` of a locally profinite group, the step that makes
compact-open invariants of smooth representations exact, divides by the indices `[K : N]` of
open normal subgroups `N`. Over a coefficient ring `A` this is possible exactly when all these
indices are units of `A`, which is the condition that `K` has *pro-order invertible in `A`*.
For a nontrivial pro-`p` group it says that `p` is a unit in `A`.

We define `HasUnitProOrder A K` as the invertibility in `A` of the order of every quotient of `K`
by an open normal subgroup, and relate it to the indices of all open subgroups and to the
supernatural order `profiniteOrder K`. We show that it passes to open subgroups of a compact
group, to all subgroups of a profinite group, and along ring homomorphisms.

The condition on open subgroups needs compactness: the circle group has unit pro-order over
`𝔽_p`, since its only open normal subgroup is itself, while its finite subgroup `μ_p` with the
discrete topology does not. This is why the passage to arbitrary subgroups assumes `K`
profinite, whereas the passage to open subgroups only assumes `K` compact.

## Main definitions

* `HasUnitProOrder A K`: every quotient of `K` by an open normal subgroup has order a unit of `A`.

## Main results

* `hasUnitProOrder_iff_isUnit_index`: for compact `K`, it suffices that the index of every open
  subgroup is a unit.
* `hasUnitProOrder_iff_isUnit_of_profiniteOrder_ne_zero`: for compact `K`, it says that every
  prime dividing the supernatural order of `K` is a unit.
* `hasUnitProOrder_iff_isUnit_card`: a discrete group has unit pro-order exactly when its
  cardinality is a unit.
* `HasUnitProOrder.of_isOpenEmbedding`, `HasUnitProOrder.mono`: the condition passes to open
  subgroups of a compact group.
* `HasUnitProOrder.subgroup`: in a profinite group, it passes to every subgroup.
* `HasUnitProOrder.map`: it is inherited along ring homomorphisms.
* `IsProP.hasUnitProOrder`, `IsProP.hasUnitProOrder_iff`: a compact pro-`p` group has unit
  pro-order whenever `p` is a unit, and conversely if it is profinite and nontrivial.

## References

* J. Bernstein, *Second adjointness for representations of reductive p-adic groups*, 1987
  manuscript, §1.3.
* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, Ch. I, §2.1.
-/

public section

namespace TauCeti

universe u v w

/-- A topological group `K` has **pro-order invertible in `A`** when the order of every quotient
of `K` by an open normal subgroup is a unit of `A`. For a profinite group these quotients are the
continuous finite quotients, and the condition says that every prime dividing the supernatural
order of `K` is a unit of `A` (see `hasUnitProOrder_iff_isUnit_of_profiniteOrder_ne_zero`). -/
def HasUnitProOrder (A : Type v) [CommSemiring A] (K : Type u) [Group K] [TopologicalSpace K] :
    Prop :=
  ∀ N : OpenNormalSubgroup K, IsUnit (Nat.card (K ⧸ N.toSubgroup) : A)

variable (A : Type v) [CommSemiring A] {K : Type u} [Group K] [TopologicalSpace K]

/-- The defining property of `HasUnitProOrder`, available to modules that only see the
declaration and not its body. -/
theorem hasUnitProOrder_iff :
    HasUnitProOrder A K ↔ ∀ N : OpenNormalSubgroup K, IsUnit (Nat.card (K ⧸ N.toSubgroup) : A) :=
  Iff.rfl

/-- The trivial group has pro-order invertible in every commutative semiring. -/
theorem hasUnitProOrder_of_subsingleton [Subsingleton K] : HasUnitProOrder A K := fun N ↦ by
  have : Subsingleton (K ⧸ N.toSubgroup) := QuotientGroup.mk_surjective.subsingleton
  rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩, Nat.cast_one]
  exact isUnit_one

/-- A group with the discrete topology has unit pro-order exactly when its cardinality is a unit.
For an infinite discrete group the cardinality is `0`, so this happens only over the zero
semiring. -/
theorem hasUnitProOrder_iff_isUnit_card [DiscreteTopology K] :
    HasUnitProOrder A K ↔ IsUnit (Nat.card K : A) := by
  refine ⟨fun h ↦ ?_, fun h N ↦ ?_⟩
  · simpa only [← Subgroup.index_eq_card, OpenNormalSubgroup.toSubgroup_bot,
      Subgroup.index_bot] using h ⊥
  · rw [← Subgroup.index_eq_card]
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast N.toSubgroup.index_dvd_card) h

variable {A} in
/-- Invertible pro-order is inherited along ring homomorphisms. -/
theorem HasUnitProOrder.map {B : Type w} [CommSemiring B] (h : HasUnitProOrder A K)
    (f : A →+* B) : HasUnitProOrder B K := fun N ↦ by
  simpa only [map_natCast] using (h N).map f

section Compact

variable [SeparatelyContinuousMul K] [CompactSpace K]

/-- **Invertible pro-order through open subgroups.** A compact group has unit pro-order exactly
when the index of every open subgroup, normal or not, is a unit. -/
theorem hasUnitProOrder_iff_isUnit_index :
    HasUnitProOrder A K ↔ ∀ H : OpenSubgroup K, IsUnit (H.toSubgroup.index : A) := by
  refine ⟨fun h H ↦ ?_, fun h N ↦ ?_⟩
  · obtain ⟨N, hNH, -⟩ := H.exists_openNormalSubgroup_le
    refine isUnit_of_dvd_unit (Nat.cast_dvd_cast (Subgroup.index_dvd_of_le hNH)) ?_
    simpa only [Subgroup.index_eq_card] using h N
  · simpa only [Subgroup.index_eq_card] using h N.toOpenSubgroup

/-- **Invertible pro-order through the supernatural order.** A compact group has unit pro-order
exactly when every prime dividing its supernatural order is a unit. -/
theorem hasUnitProOrder_iff_isUnit_of_profiniteOrder_ne_zero :
    HasUnitProOrder A K ↔ ∀ p : Nat.Primes, profiniteOrder K p ≠ 0 → IsUnit ((p : ℕ) : A) := by
  refine ⟨fun h p hp ↦ ?_, fun h N ↦ ?_⟩
  · obtain ⟨N, hN⟩ : ∃ N : OpenNormalSubgroup K,
        padicValNat p (Nat.card (K ⧸ N.toSubgroup)) ≠ 0 := by
      by_contra! hN
      exact hp (by simp [hN])
    simp only [Nat.padicValNat_def] at hN
    exact isUnit_of_dvd_unit
      (Nat.cast_dvd_cast (dvd_of_one_le_multiplicity (Nat.one_le_iff_ne_zero.mpr hN))) (h N)
  · rw [isUnit_natCast_iff_forall_prime_dvd Nat.card_pos.ne']
    intro q hq hdvd
    have : Fact q.Prime := ⟨hq⟩
    let p : Nat.Primes := ⟨q, hq⟩
    refine h p ?_
    rw [profiniteOrder_apply]
    refine (lt_of_lt_of_le ?_ (le_iSup (fun N : OpenNormalSubgroup K ↦
      (padicValNat q (Nat.card (K ⧸ N.toSubgroup)) : ℕ∞)) N)).ne'
    simp only [Nat.padicValNat_def]
    exact_mod_cast one_le_multiplicity_of_dvd Nat.card_pos.ne' hdvd

variable {A}

/-- **Invertible pro-order passes to open subgroups.** If `K` is compact with unit pro-order and
`f : H →* K` is a homomorphism that is an open embedding, then `H` has unit pro-order. -/
theorem HasUnitProOrder.of_isOpenEmbedding {H : Type w} [Group H] [TopologicalSpace H]
    (h : HasUnitProOrder A K) {f : H →* K} (hf : Topology.IsOpenEmbedding f) :
    HasUnitProOrder A H := fun N ↦ by
  let L : OpenSubgroup K := ⟨N.toSubgroup.map f, hf.isOpenMap _ N.isOpen⟩
  rw [← Subgroup.index_eq_card]
  refine isUnit_of_dvd_unit (Nat.cast_dvd_cast ?_) ((hasUnitProOrder_iff_isUnit_index A).mp h L)
  exact Dvd.intro _ (Subgroup.index_map_of_injective N.toSubgroup hf.injective).symm

end Compact

variable {A}

/-- **Invertible pro-order passes from a compact subgroup to its open subgroups.** If `U` is a
compact subgroup of a topological group `G` with unit pro-order, then so does every open subgroup
`V ≤ U` of `G`. -/
theorem HasUnitProOrder.mono {G : Type w} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] {U V : Subgroup G} (h : HasUnitProOrder A U)
    (hU : IsCompact (U : Set G)) (hV : IsOpen (V : Set G)) (hVU : V ≤ U) :
    HasUnitProOrder A V :=
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  h.of_isOpenEmbedding (f := Subgroup.inclusion hVU)
    (Topology.IsOpenEmbedding.inclusion hVU (hV.preimage continuous_subtype_val))

/-- **Invertible pro-order passes to all subgroups of a profinite group.** If a profinite group
`K` has unit pro-order, then so does every subgroup `H ≤ K` with the subspace topology, closed
or not. -/
theorem HasUnitProOrder.subgroup [IsTopologicalGroup K]
    [CompactSpace K] [TotallyDisconnectedSpace K] (h : HasUnitProOrder A K) (H : Subgroup K) :
    HasUnitProOrder A H := fun N ↦ by
  obtain ⟨M, hM⟩ := H.exists_openNormalSubgroup_comap_le N
  rw [← Subgroup.index_eq_card]
  refine isUnit_of_dvd_unit (Nat.cast_dvd_cast ((Subgroup.index_dvd_of_le hM).trans
    (M.toSubgroup.relIndex_dvd_index_of_normal H))) ?_
  simpa only [Subgroup.index_eq_card] using h M

/-- **Compact pro-`p` groups have pro-order invertible wherever `p` is.** A compact pro-`p` group
has unit pro-order over every commutative semiring in which `p` is a unit. Here `p` is any
natural number, not necessarily prime. -/
theorem IsProP.hasUnitProOrder {p : ℕ} [SeparatelyContinuousMul K]
    [CompactSpace K] (hK : IsProP p K) (hp : IsUnit (p : A)) : HasUnitProOrder A K := fun N ↦ by
  rw [isUnit_natCast_iff_forall_prime_dvd Nat.card_pos.ne']
  intro q hq hdvd
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hdvd
  obtain ⟨k, hk⟩ := isProP_iff.mp hK N x
  exact isUnit_of_dvd_unit
    (Nat.cast_dvd_cast (hq.dvd_of_dvd_pow (hx ▸ orderOf_dvd_of_pow_eq_one hk))) hp

variable (A) in
/-- **The pro-order of a nontrivial pro-`p` group.** For a prime `p`, a nontrivial profinite
pro-`p` group has pro-order invertible in `A` exactly when `p` is a unit of `A`. -/
theorem IsProP.hasUnitProOrder_iff {p : ℕ} [Fact p.Prime]
    [IsTopologicalGroup K] [CompactSpace K] [TotallyDisconnectedSpace K] [Nontrivial K]
    (hK : IsProP p K) : HasUnitProOrder A K ↔ IsUnit (p : A) := by
  refine ⟨fun h ↦ ?_, hK.hasUnitProOrder⟩
  obtain ⟨q, hq⟩ : ∃ q : Nat.Primes, profiniteOrder K q ≠ 0 := by
    by_contra! hq
    exact not_subsingleton K <| (profiniteOrder_eq_bot_iff K).mp <|
      Supernatural.ext fun q ↦ by rw [hq, Supernatural.bot_apply]
  obtain rfl : (q : ℕ) = p := by
    by_contra hqp
    exact hq (isProP_iff_profiniteOrder_apply_eq_zero.mp hK q hqp)
  exact (hasUnitProOrder_iff_isUnit_of_profiniteOrder_ne_zero A).mp h q hq

end TauCeti
