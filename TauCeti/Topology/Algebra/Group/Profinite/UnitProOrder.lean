/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import TauCeti.Algebra.Algebra.NatCast
public import TauCeti.Topology.Algebra.Group.Profinite.Order
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Separation.Connected
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# Profinite groups of invertible pro-order

Let `A` be a semiring and `U` a topological group. We say that `U` has **invertible pro-order** in
`A` (`TauCeti.HasUnitProOrder A U`) when for every open normal subgroup `N` of `U` the quotient
cardinality `Nat.card (U ⧸ N)` casts to a unit of `A`. On a compact group with separately
continuous multiplication these quotients are finite; passing to the open normal core shows that the
condition is equivalent to invertibility in `A` of the index of every open subgroup of `U`, and
factoring those positive quotient orders into primes shows that it is equivalent to invertibility in
`A` of every prime in the support of `TauCeti.profiniteOrder U`.

Invertible pro-order is preserved along ring homomorphisms `A →+* B` and continuous surjective group
homomorphisms. It passes from a compact group with separately continuous multiplication to every
open subgroup, and from a profinite group to every subgroup (closedness of the subgroup is not
needed, since every open normal subgroup of the subgroup still contains the pullback of an ambient
open normal subgroup). By Cauchy's theorem, every compact pro-`p` group (`TauCeti.IsProP p U`) has
invertible pro-order in `A` whenever `(p : A)` is a unit; when `p` is prime and `U` is a nontrivial
profinite pro-`p` group, the converse holds as well.

For an ambient topological group `G`, `TauCeti.HasCofinalUnitProOrder A G` asserts that every
neighbourhood of `1 : G` contains a compact open subgroup `K` with `HasUnitProOrder A K`, or
equivalently that the compact open subgroups of `G` with invertible pro-order in `A` form a
neighbourhood basis of `1`. Every discrete group satisfies this condition via the trivial subgroup.
In a nonarchimedean group (and hence in every locally profinite group), it is equivalent to those
compact open subgroups forming a coinitial family inside `OpenSubgroup G`. Finally, if `G` is a
non-discrete totally disconnected topological group admitting a compact open pro-`p` subgroup (for
`p` prime), then `HasCofinalUnitProOrder A G` holds if and only if `(p : A)` is a unit.

## Main definitions

* `TauCeti.HasUnitProOrder A U`: every quotient `U ⧸ N` by an open normal subgroup has `Nat.card`
  invertible in `A`.
* `TauCeti.HasCofinalUnitProOrder A G`: every neighbourhood of `1 : G` contains a compact open
  subgroup `K` with `HasUnitProOrder A K`.

## Main results

* `TauCeti.hasUnitProOrder_iff_forall_openSubgroup_isUnit_index`: for a compact group with
  separately continuous multiplication, `HasUnitProOrder A U` is equivalent to every open subgroup
  having index invertible in `A`.
* `TauCeti.hasUnitProOrder_iff_forall_profiniteOrder_ne_zero`,
  `TauCeti.hasUnitProOrder_iff_forall_dvd_profiniteOrder`: equivalence with every prime dividing
  `TauCeti.profiniteOrder U` casting to a unit of `A`.
* `TauCeti.HasUnitProOrder.of_isOpen`, `TauCeti.HasUnitProOrder.openSubgroup`,
  `OpenSubgroup.hasUnitProOrder_and_isUnit_index_iff`: open-subgroup inheritance and the index
  multiplicativity equivalence on compact groups.
* `TauCeti.HasUnitProOrder.subgroup`: inheritance from a profinite group to an arbitrary subgroup
  (in particular to every closed subgroup).
* `TauCeti.IsProP.hasUnitProOrder`, `TauCeti.IsProP.hasUnitProOrder_iff`: invertible pro-order for
  compact pro-`p` groups when `IsUnit (p : A)`, and the exact criterion for nontrivial profinite
  pro-`p` groups.
* `TauCeti.HasUnitProOrder.map`, `TauCeti.HasCofinalUnitProOrder.map`: base change along ring
  homomorphisms `A →+* B`.
* `TauCeti.hasUnitProOrder_prod_iff`, `TauCeti.hasCofinalUnitProOrder_prod_iff`: finite products
  have (cofinal) invertible pro-order in `A` if and only if both factors do.
* `TauCeti.hasCofinalUnitProOrder_iff_hasBasis_nhds_one`,
  `TauCeti.hasCofinalUnitProOrder_iff_forall_openSubgroup_exists_le`: neighbourhood-basis and
  coinitiality characterizations of `HasCofinalUnitProOrder`.
* `TauCeti.hasCofinalUnitProOrder_of_discreteTopology`: discrete groups have cofinal unit pro-order
  over every semiring.
* `TauCeti.hasCofinalUnitProOrder_iff_isUnit_of_isProP`: for a non-discrete totally disconnected
  topological group with a compact open pro-`p` subgroup (`p` prime), `HasCofinalUnitProOrder A G`
  holds if and only if `IsUnit (p : A)`.

## References

* J. Bernstein, *Second adjointness for representations of reductive p-adic groups*, Section 1.3.
* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.2 and 2.3.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

universe u v w

/-! ### Groups of invertible pro-order -/

/-- A topological group `U` has **invertible pro-order** in a semiring `A` when the `Nat.card` of
every quotient by an open normal subgroup casts to a unit in `A`. For a compact group with
separately continuous multiplication, these quotients are finite and represent all continuous finite
quotients of `U`. -/
def HasUnitProOrder (A : Type u) [Semiring A] (U : Type v) [Group U] [TopologicalSpace U] : Prop :=
  ∀ N : OpenNormalSubgroup U, IsUnit (Nat.card (U ⧸ N.toSubgroup) : A)

section Basic

variable {A : Type u} [Semiring A] {U : Type v} [Group U] [TopologicalSpace U]

/-- Defining characterization of `TauCeti.HasUnitProOrder`. -/
theorem hasUnitProOrder_iff :
    HasUnitProOrder A U ↔ ∀ N : OpenNormalSubgroup U, IsUnit (Nat.card (U ⧸ N.toSubgroup) : A) :=
  (Iff.rfl)

/-- For a group of invertible pro-order in `A`, every quotient by an open normal subgroup has order
invertible in `A`. -/
theorem HasUnitProOrder.isUnit_card_quotient (hU : HasUnitProOrder A U)
    (N : OpenNormalSubgroup U) : IsUnit (Nat.card (U ⧸ N.toSubgroup) : A) :=
  hU N

/-- For a group of invertible pro-order in `A`, every open normal subgroup has index invertible in
`A`. -/
theorem HasUnitProOrder.isUnit_index_openNormalSubgroup (hU : HasUnitProOrder A U)
    (N : OpenNormalSubgroup U) : IsUnit (N.toSubgroup.index : A) := by
  rw [Subgroup.index_eq_card]
  exact hU N

/-- Over a subsingleton semiring every group has invertible pro-order. -/
@[simp]
theorem hasUnitProOrder_of_subsingleton_left [Subsingleton A] : HasUnitProOrder A U :=
  fun _ ↦ isUnit_of_subsingleton _

/-- A trivial group has invertible pro-order in every semiring. -/
@[simp]
theorem hasUnitProOrder_of_subsingleton [Subsingleton U] : HasUnitProOrder A U := by
  intro N
  have : Subsingleton (U ⧸ N.toSubgroup) := QuotientGroup.mk_surjective.subsingleton
  rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩, Nat.cast_one]
  exact isUnit_one

/-- A preconnected group with separately continuous multiplication has invertible pro-order in every
semiring, because its only open normal subgroup is `⊤`. -/
theorem hasUnitProOrder_of_preconnectedSpace [SeparatelyContinuousMul U] [PreconnectedSpace U] :
    HasUnitProOrder A U := by
  intro N
  have htop : N.toSubgroup = ⊤ :=
    Subgroup.coe_eq_univ.mp (N.toOpenSubgroup.isClopen.eq_univ ⟨1, N.one_mem⟩)
  have : Subsingleton (U ⧸ N.toSubgroup) := QuotientGroup.subsingleton_iff.mpr htop
  rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩, Nat.cast_one]
  exact isUnit_one

/-- Every compact group with separately continuous multiplication has invertible pro-order in any
`ℚ`-algebra. -/
theorem hasUnitProOrder_of_algebra_rat [SeparatelyContinuousMul U] [CompactSpace U]
    [Algebra ℚ A] : HasUnitProOrder A U :=
  fun _ ↦ isUnit_natCast_of_ne_zero Nat.card_pos.ne'

/-- Invertible pro-order is preserved along semiring homomorphisms. -/
theorem HasUnitProOrder.map {B : Type w} [Semiring B] (hU : HasUnitProOrder A U) (f : A →+* B) :
    HasUnitProOrder B U :=
  fun N ↦ map_natCast f (Nat.card (U ⧸ N.toSubgroup)) ▸ (hU N).map f

/-- Invertible pro-order is invariant under ring isomorphism of the coefficient semiring. -/
theorem hasUnitProOrder_congr_ring {B : Type w} [Semiring B] (e : A ≃+* B) :
    HasUnitProOrder A U ↔ HasUnitProOrder B U :=
  ⟨fun h ↦ h.map e.toRingHom, fun h ↦ h.map e.symm.toRingHom⟩

/-- A continuous surjective homomorphism carries invertible pro-order to its target. -/
theorem HasUnitProOrder.of_surjective {V : Type w} [Group V] [TopologicalSpace V]
    (hU : HasUnitProOrder A U) (f : U →* V) (hf : Continuous f) (hsurj : Function.Surjective f) :
    HasUnitProOrder A V := by
  intro M
  let N := OpenNormalSubgroup.comap M f hf
  let q : U →* V ⧸ M.toSubgroup := (QuotientGroup.mk' M.toSubgroup).comp f
  have hqsurj : Function.Surjective q := (QuotientGroup.mk'_surjective M.toSubgroup).comp hsurj
  have hker : q.ker = N.toSubgroup := by
    ext x
    simp [q, N]
  have hcard : Nat.card (V ⧸ M.toSubgroup) = Nat.card (U ⧸ N.toSubgroup) := by
    simpa only [hker] using
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hqsurj).toEquiv).symm
  rw [hcard]
  exact hU N

/-- Every quotient of a group of invertible pro-order by a normal subgroup again has invertible
pro-order. -/
theorem HasUnitProOrder.quotient (hU : HasUnitProOrder A U) (N : Subgroup U) [N.Normal] :
    HasUnitProOrder A (U ⧸ N) :=
  hU.of_surjective (QuotientGroup.mk' N) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective N)

/-- Invertible pro-order is preserved along topological group isomorphisms. -/
theorem HasUnitProOrder.of_equiv {V : Type w} [Group V] [TopologicalSpace V]
    (hU : HasUnitProOrder A U) (e : U ≃ₜ* V) : HasUnitProOrder A V :=
  hU.of_surjective e.toMulEquiv.toMonoidHom e.continuous e.surjective

/-- Invertible pro-order is invariant under topological group isomorphism. -/
theorem hasUnitProOrder_congr {V : Type w} [Group V] [TopologicalSpace V] (e : U ≃ₜ* V) :
    HasUnitProOrder A U ↔ HasUnitProOrder A V :=
  ⟨fun h ↦ h.of_equiv e, fun h ↦ h.of_equiv e.symm⟩

/-- For subgroups `H ≤ K` of a topological group, `H` has invertible pro-order exactly when
`H.subgroupOf K` does. -/
theorem _root_.Subgroup.hasUnitProOrder_subgroupOf_iff {H K : Subgroup U} (hHK : H ≤ K) :
    HasUnitProOrder A (H.subgroupOf K) ↔ HasUnitProOrder A H :=
  hasUnitProOrder_congr
    { toMulEquiv := Subgroup.subgroupOfEquivOfLe hHK
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

/-- The top subgroup of `U` has invertible pro-order if and only if `U` does. -/
@[simp]
theorem hasUnitProOrder_top_iff : HasUnitProOrder A (⊤ : Subgroup U) ↔ HasUnitProOrder A U :=
  hasUnitProOrder_congr
    { toMulEquiv := Subgroup.topEquiv
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }

/-- The top open subgroup of `U` has invertible pro-order if and only if `U` does. -/
@[simp]
theorem _root_.OpenSubgroup.hasUnitProOrder_top_iff :
    HasUnitProOrder A (⊤ : OpenSubgroup U) ↔ HasUnitProOrder A U :=
  TauCeti.hasUnitProOrder_top_iff

/-- On a discrete group `U` (finite or infinite), `HasUnitProOrder A U` holds if and only if
`Nat.card U` casts to a unit in `A`. When `U` is infinite, `Nat.card U = 0`, and both sides hold
only for the zero semiring. -/
theorem hasUnitProOrder_iff_isUnit_card [DiscreteTopology U] :
    HasUnitProOrder A U ↔ IsUnit (Nat.card U : A) := by
  refine ⟨fun h ↦ ?_, fun hu N ↦ ?_⟩
  · have hcard : Nat.card (U ⧸ (⊥ : OpenNormalSubgroup U).toSubgroup) = Nat.card U :=
      Nat.card_congr QuotientGroup.quotientBot.toEquiv
    exact hcard ▸ h ⊥
  · rw [← Subgroup.index_eq_card]
    exact hu.natCast_of_dvd ⟨Nat.card N.toSubgroup, by
      rw [mul_comm]
      exact N.toSubgroup.card_mul_index.symm⟩

/-- A product of two topological groups with invertible pro-order in `A` again has invertible
pro-order in `A`. -/
theorem HasUnitProOrder.prod {V : Type w} [Group V] [TopologicalSpace V]
    (hU : HasUnitProOrder A U) (hV : HasUnitProOrder A V) : HasUnitProOrder A (U × V) := by
  intro N
  let N₁ : OpenNormalSubgroup U :=
    N.comap (MonoidHom.inl U V) (continuous_id.prodMk continuous_const)
  let N₂ : OpenNormalSubgroup V :=
    N.comap (MonoidHom.inr U V) (continuous_const.prodMk continuous_id)
  have hle : N₁.toSubgroup.prod N₂.toSubgroup ≤ N.toSubgroup := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    simpa only [MonoidHom.inl_apply, MonoidHom.inr_apply, Prod.mk_mul_mk, mul_one, one_mul] using
      N.toSubgroup.mul_mem hu hv
  have hdvd : Nat.card ((U × V) ⧸ N.toSubgroup) ∣
      Nat.card (U ⧸ N₁.toSubgroup) * Nat.card (V ⧸ N₂.toSubgroup) := by
    rw [← Nat.card_prod,
      ← Nat.card_congr (QuotientGroup.prodEquiv N₁.toSubgroup N₂.toSubgroup),
      ← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_of_le hle
  have hmul : IsUnit ((Nat.card (U ⧸ N₁.toSubgroup) * Nat.card (V ⧸ N₂.toSubgroup) : ℕ) : A) := by
    rw [Nat.cast_mul]
    exact (hU N₁).mul (hV N₂)
  exact hmul.natCast_of_dvd hdvd

/-- A product `U × V` of topological groups has invertible pro-order in `A` if and only if both
factors do. -/
@[simp]
theorem hasUnitProOrder_prod_iff {V : Type w} [Group V] [TopologicalSpace V] :
    HasUnitProOrder A (U × V) ↔ HasUnitProOrder A U ∧ HasUnitProOrder A V :=
  ⟨fun h ↦ ⟨h.of_surjective (MonoidHom.fst U V) continuous_fst fun u ↦ ⟨(u, 1), rfl⟩,
    h.of_surjective (MonoidHom.snd U V) continuous_snd fun v ↦ ⟨(1, v), rfl⟩⟩,
    fun ⟨hU, hV⟩ ↦ hU.prod hV⟩

end Basic

/-! ### Open-subgroup index and supernatural-order criteria -/

section Characterizations

variable {A : Type u} [Semiring A] {U : Type v} [Group U] [TopologicalSpace U]

/-- If every open subgroup of `U` has index invertible in `A`, then `U` has invertible pro-order in
`A`. -/
theorem hasUnitProOrder_of_forall_openSubgroup_isUnit_index
    (h : ∀ U' : OpenSubgroup U, IsUnit (U'.toSubgroup.index : A)) : HasUnitProOrder A U :=
  fun N ↦ Subgroup.index_eq_card N.toSubgroup ▸ h N.toOpenSubgroup

/-- Every prime in the support of `TauCeti.profiniteOrder U` casts to a unit in `A` whenever
`HasUnitProOrder A U` holds. -/
theorem HasUnitProOrder.isUnit_of_profiniteOrder_ne_zero (hU : HasUnitProOrder A U)
    {p : Nat.Primes} (hp : profiniteOrder U p ≠ 0) : IsUnit ((p : ℕ) : A) := by
  rw [profiniteOrder_apply] at hp
  have hex : ∃ N : OpenNormalSubgroup U,
      (padicValNat p (Nat.card (U ⧸ N.toSubgroup)) : ℕ∞) ≠ 0 := by
    by_contra! hall
    exact hp (ENat.iSup_eq_zero.mpr hall)
  obtain ⟨N, hN⟩ := hex
  have hdvd : (p : ℕ) ∣ Nat.card (U ⧸ N.toSubgroup) := by
    by_contra hndvd
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hndvd, Nat.cast_zero] at hN
    exact hN rfl
  exact (hU N).natCast_of_dvd hdvd

/-- In a group with separately continuous multiplication and invertible pro-order, every open
subgroup of finite index has index invertible in `A`, via its open normal core. -/
theorem HasUnitProOrder.isUnit_index_of_finiteIndex [SeparatelyContinuousMul U]
    (hU : HasUnitProOrder A U) {H : Subgroup U} (hH : IsOpen (H : Set U)) [H.FiniteIndex] :
    IsUnit (H.index : A) := by
  have : (OpenSubgroup.mk H hH).toSubgroup.FiniteIndex := ‹_›
  obtain ⟨N, hNH, -⟩ := (OpenSubgroup.mk H hH).exists_openNormalSubgroup_le
  exact (hU.isUnit_index_openNormalSubgroup N).natCast_of_dvd (Subgroup.index_dvd_of_le hNH)

section Compact

variable [SeparatelyContinuousMul U] [CompactSpace U]

/-- In a compact group with separately continuous multiplication and invertible pro-order, every
open subgroup has index invertible in `A`. -/
theorem HasUnitProOrder.isUnit_index (hU : HasUnitProOrder A U) {H : Subgroup U}
    (hH : IsOpen (H : Set U)) : IsUnit (H.index : A) := by
  have : Finite (U ⧸ H) := H.quotient_finite_of_isOpen hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact hU.isUnit_index_of_finiteIndex hH

/-- Bundled `OpenSubgroup` form of `TauCeti.HasUnitProOrder.isUnit_index`. -/
theorem HasUnitProOrder.isUnit_index_openSubgroup (hU : HasUnitProOrder A U)
    (U' : OpenSubgroup U) : IsUnit (U'.toSubgroup.index : A) :=
  hU.isUnit_index U'.isOpen

/-- **Open-subgroup index criterion.** A compact group with separately continuous multiplication has
invertible pro-order in `A` if and only if the index of every open subgroup is invertible in `A`. -/
theorem hasUnitProOrder_iff_forall_openSubgroup_isUnit_index :
    HasUnitProOrder A U ↔ ∀ U' : OpenSubgroup U, IsUnit (U'.toSubgroup.index : A) :=
  ⟨fun hU U' ↦ hU.isUnit_index_openSubgroup U',
    hasUnitProOrder_of_forall_openSubgroup_isUnit_index⟩

/-- **Supernatural-order criterion.** A compact group with separately continuous multiplication has
invertible pro-order in `A` if and only if every prime in the support of `TauCeti.profiniteOrder U`
casts to a unit in `A`. -/
theorem hasUnitProOrder_iff_forall_profiniteOrder_ne_zero :
    HasUnitProOrder A U ↔ ∀ p : Nat.Primes, profiniteOrder U p ≠ 0 → IsUnit ((p : ℕ) : A) := by
  refine ⟨fun hU _ hp ↦ hU.isUnit_of_profiniteOrder_ne_zero hp, fun hp N ↦ ?_⟩
  have hn : Nat.card (U ⧸ N.toSubgroup) ≠ 0 := Nat.card_pos.ne'
  refine isUnit_natCast_of_forall_prime_dvd hn fun q hq hqd ↦ ?_
  have : Fact q.Prime := ⟨hq⟩
  let P : Nat.Primes := ⟨q, hq⟩
  refine hp P fun hzero ↦ ?_
  have hval : (padicValNat q (Nat.card (U ⧸ N.toSubgroup)) : ℕ∞) ≤ 0 := by
    rw [← hzero, profiniteOrder_apply]
    exact le_iSup
      (fun M : OpenNormalSubgroup U ↦ (padicValNat P (Nat.card (U ⧸ M.toSubgroup)) : ℕ∞)) N
  have hpos : 1 ≤ padicValNat q (Nat.card (U ⧸ N.toSubgroup)) := by
    rw [Nat.padicValNat_def]
    exact one_le_multiplicity_of_dvd hn hqd
  exact absurd (Nat.cast_le.mpr hpos) (not_le_of_gt (lt_of_le_of_lt hval zero_lt_one))

/-- Supernatural-divisibility form of `TauCeti.hasUnitProOrder_iff_forall_profiniteOrder_ne_zero`:
a compact group with separately continuous multiplication has invertible pro-order in `A` if and
only if every prime dividing `TauCeti.profiniteOrder U` casts to a unit in `A`. -/
theorem hasUnitProOrder_iff_forall_dvd_profiniteOrder :
    HasUnitProOrder A U ↔
      ∀ p : Nat.Primes, (p : Supernatural) ∣ profiniteOrder U → IsUnit ((p : ℕ) : A) := by
  simp_rw [Supernatural.coe_prime_dvd_iff]
  exact hasUnitProOrder_iff_forall_profiniteOrder_ne_zero

end Compact

end Characterizations

/-! ### Subgroup inheritance -/

section Subgroups

variable {A : Type u} [Semiring A] {U : Type v} [Group U] [TopologicalSpace U]

/-- If a subgroup `H` of `U` has invertible pro-order in `A` and its index `[U : H]` is invertible
in `A`, then `U` itself has invertible pro-order in `A`. Neither openness of `H` nor compactness of
`U` is needed. -/
theorem HasUnitProOrder.of_subgroup_of_isUnit_index {H : Subgroup U} (hH : HasUnitProOrder A H)
    (hind : IsUnit (H.index : A)) : HasUnitProOrder A U := by
  intro N
  let V : OpenNormalSubgroup H := N.comap H.subtype continuous_subtype_val
  have hV : V.toSubgroup = N.toSubgroup.comap H.subtype :=
    OpenNormalSubgroup.toSubgroup_comap N H.subtype continuous_subtype_val
  have hcard_img : IsUnit (Nat.card (H.map (QuotientGroup.mk' N.toSubgroup)) : A) := by
    rw [← Subgroup.index_comap_subtype_eq_card_map, ← hV, Subgroup.index_eq_card]
    exact hH V
  have hind_img : IsUnit ((H.map (QuotientGroup.mk' N.toSubgroup)).index : A) := by
    rw [Subgroup.index_map_mk'_eq_index_sup]
    exact hind.natCast_of_dvd (Subgroup.index_dvd_of_le le_sup_left)
  rw [← (H.map (QuotientGroup.mk' N.toSubgroup)).card_mul_index, Nat.cast_mul]
  exact hcard_img.mul hind_img

/-- In a compact group with separately continuous multiplication, invertible pro-order passes to
every open subgroup, through the open normal core in the ambient group. -/
theorem HasUnitProOrder.of_isOpen [SeparatelyContinuousMul U] [CompactSpace U]
    (hU : HasUnitProOrder A U) {H : Subgroup U} (hH : IsOpen (H : Set U)) :
    HasUnitProOrder A H := by
  intro M
  let M' : Subgroup U := M.toSubgroup.map H.subtype
  have hM'open : IsOpen (M' : Set U) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ M.toOpenSubgroup.isOpen
  have hM'sub : M'.subgroupOf H = M.toSubgroup := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
  have hdvd : Nat.card (H ⧸ M.toSubgroup) ∣ M'.index := by
    rw [← Subgroup.index_eq_card, ← hM'sub]
    exact ⟨H.index, (Subgroup.relIndex_mul_index (Subgroup.map_subtype_le M.toSubgroup)).symm⟩
  exact (hU.isUnit_index hM'open).natCast_of_dvd hdvd

/-- Bundled `OpenSubgroup` form of `TauCeti.HasUnitProOrder.of_isOpen`. -/
theorem HasUnitProOrder.openSubgroup [SeparatelyContinuousMul U] [CompactSpace U]
    (hU : HasUnitProOrder A U) (K : OpenSubgroup U) : HasUnitProOrder A K :=
  hU.of_isOpen K.isOpen

/-- In a compact group with separately continuous multiplication, an ambient group `U` has
invertible pro-order in `A` if and only if an open subgroup `K` has invertible pro-order and
invertible index in `A`. -/
theorem _root_.OpenSubgroup.hasUnitProOrder_and_isUnit_index_iff
    [SeparatelyContinuousMul U] [CompactSpace U] (K : OpenSubgroup U) :
    HasUnitProOrder A K ∧ IsUnit (K.toSubgroup.index : A) ↔ HasUnitProOrder A U :=
  ⟨fun ⟨hK, hind⟩ ↦ hK.of_subgroup_of_isUnit_index hind,
    fun hU ↦ ⟨hU.openSubgroup K, hU.isUnit_index_openSubgroup K⟩⟩

/-- If `K` is a compact open subgroup of `G` with invertible pro-order in `A`, then for every open
subgroup `H` of `G` the relative index `[K : H ∩ K]` is invertible in `A`. -/
theorem HasUnitProOrder.isUnit_relIndex_openSubgroup [SeparatelyContinuousMul U]
    {K : OpenSubgroup U} (hK : HasUnitProOrder A K) (hKc : IsCompact (K : Set U))
    (H : OpenSubgroup U) : IsUnit ((H.toSubgroup.relIndex K.toSubgroup) : A) := by
  have : SeparatelyContinuousMul K :=
    { continuous_const_mul := ((continuous_const_mul _).comp continuous_subtype_val).subtype_mk _
      continuous_mul_const := ((continuous_mul_const _).comp continuous_subtype_val).subtype_mk _ }
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  exact hK.isUnit_index (H.isOpen.preimage continuous_subtype_val)

/-- If `K` is a compact open subgroup of `G` with invertible pro-order in `A`, then every open
subgroup `H ≤ K` also has invertible pro-order in `A`. -/
theorem HasUnitProOrder.mono_openSubgroup [SeparatelyContinuousMul U]
    {H K : OpenSubgroup U} (hK : HasUnitProOrder A K) (hKc : IsCompact (K : Set U))
    (hHK : H ≤ K) : HasUnitProOrder A H := by
  have : SeparatelyContinuousMul K :=
    { continuous_const_mul := ((continuous_const_mul _).comp continuous_subtype_val).subtype_mk _
      continuous_mul_const := ((continuous_mul_const _).comp continuous_subtype_val).subtype_mk _ }
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  exact (Subgroup.hasUnitProOrder_subgroupOf_iff hHK).mp
    (hK.of_isOpen (H.isOpen.preimage continuous_subtype_val))

/-- In a profinite group, invertible pro-order passes to every subgroup `H` in the subspace
topology. Closedness of `H` is not needed here (it is needed only when `H` must itself be
compact); in particular, every closed subgroup of a profinite group inherits invertible
pro-order. -/
theorem HasUnitProOrder.subgroup [IsTopologicalGroup U] [CompactSpace U]
    [TotallyDisconnectedSpace U] (hU : HasUnitProOrder A U) (H : Subgroup U) :
    HasUnitProOrder A H := by
  intro V
  obtain ⟨N, hNV⟩ := H.exists_openNormalSubgroup_comap_le V
  have hdvd₁ : Nat.card (H ⧸ V.toSubgroup) ∣
      Nat.card (H.map (QuotientGroup.mk' N.toSubgroup)) := by
    rw [← V.toSubgroup.index_eq_card, ← Subgroup.index_comap_subtype_eq_card_map]
    exact Subgroup.index_dvd_of_le hNV
  have hdvd₂ : Nat.card (H.map (QuotientGroup.mk' N.toSubgroup)) ∣
      Nat.card (U ⧸ N.toSubgroup) :=
    ⟨(H.map (QuotientGroup.mk' N.toSubgroup)).index,
      (H.map (QuotientGroup.mk' N.toSubgroup)).card_mul_index.symm⟩
  exact (hU N).natCast_of_dvd (hdvd₁.trans hdvd₂)

end Subgroups

/-! ### Pro-`p` groups -/

section ProP

variable {p : ℕ} {A : Type u} [Semiring A] {U : Type v} [Group U] [TopologicalSpace U]

/-- **Every compact pro-`p` group with separately continuous multiplication has invertible
pro-order in any semiring `A` where `(p : A)` is a unit.** Primality of `p` is not required: by
Cauchy's theorem, every prime dividing a finite quotient order divides `p`. -/
theorem IsProP.hasUnitProOrder [SeparatelyContinuousMul U] [CompactSpace U]
    (hU : IsProP p U) (hp : IsUnit (p : A)) : HasUnitProOrder A U := by
  intro N
  have : Finite (U ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.toOpenSubgroup.isOpen
  refine isUnit_natCast_of_forall_prime_dvd Nat.card_pos.ne' fun q hq hqd ↦ ?_
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := U ⧸ N.toSubgroup) q hqd
  obtain ⟨m, hm⟩ := isProP_iff.mp hU N x
  have hqp : q ∣ p := hq.dvd_of_dvd_pow (hx ▸ orderOf_dvd_of_pow_eq_one hm)
  exact hp.natCast_of_dvd hqp

/-- A nontrivial profinite pro-`p` group (with `p` prime) has invertible pro-order in `A` if and
only if `(p : A)` is a unit. -/
theorem IsProP.hasUnitProOrder_iff [Fact p.Prime] [IsTopologicalGroup U] [CompactSpace U]
    [TotallyDisconnectedSpace U] [Nontrivial U] (hU : IsProP p U) :
    HasUnitProOrder A U ↔ IsUnit (p : A) := by
  refine ⟨fun hunit ↦ ?_, hU.hasUnitProOrder⟩
  obtain ⟨x, hx⟩ := exists_ne (1 : U)
  have hex : ∃ N : OpenNormalSubgroup U, x ∉ N.toSubgroup := by
    by_contra! hall
    exact hx (Subgroup.eq_one_of_mem_iInf_openNormalSubgroup hall)
  obtain ⟨N, hN⟩ := hex
  have : Nontrivial (U ⧸ N.toSubgroup) :=
    ⟨⟨(x : U ⧸ N.toSubgroup), 1, fun h ↦ hN ((QuotientGroup.eq_one_iff x).mp h)⟩⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isProP_iff.mp hU N)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact (Finite.one_lt_card (α := U ⧸ N.toSubgroup)).ne' hk
  exact (hunit N).natCast_of_dvd (hk ▸ dvd_pow_self p hk0)

end ProP

/-! ### Cofinal families of compact open subgroups of invertible pro-order -/

/-- A topological group `G` has **cofinal invertible pro-order** in a semiring `A` when every
neighbourhood of `1 : G` contains a compact open subgroup `K` with `HasUnitProOrder A K`. -/
def HasCofinalUnitProOrder (A : Type u) [Semiring A] (G : Type v) [Group G]
    [TopologicalSpace G] : Prop :=
  ∀ s ∈ 𝓝 (1 : G), ∃ K : OpenSubgroup G,
    IsCompact (K : Set G) ∧ HasUnitProOrder A K ∧ (K : Set G) ⊆ s

section Cofinal

variable {A : Type u} [Semiring A] {G : Type v} [Group G] [TopologicalSpace G]

/-- Defining characterization of `TauCeti.HasCofinalUnitProOrder`. -/
theorem hasCofinalUnitProOrder_iff :
    HasCofinalUnitProOrder A G ↔
      ∀ s ∈ 𝓝 (1 : G), ∃ K : OpenSubgroup G,
        IsCompact (K : Set G) ∧ HasUnitProOrder A K ∧ (K : Set G) ⊆ s :=
  (Iff.rfl)

/-- Every neighbourhood of `1` in a group with `HasCofinalUnitProOrder A G` contains a compact open
subgroup of invertible pro-order in `A`. -/
theorem HasCofinalUnitProOrder.exists_openSubgroup_subset (hG : HasCofinalUnitProOrder A G)
    {s : Set G} (hs : s ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ HasUnitProOrder A K ∧ (K : Set G) ⊆ s :=
  hG s hs

/-- **Neighbourhood-basis characterization.** `HasCofinalUnitProOrder A G` holds if and only if the
compact open subgroups of `G` with invertible pro-order in `A` form a neighbourhood basis of `1`. -/
theorem hasCofinalUnitProOrder_iff_hasBasis_nhds_one :
    HasCofinalUnitProOrder A G ↔
      (𝓝 (1 : G)).HasBasis
        (fun K : OpenSubgroup G ↦ IsCompact (K : Set G) ∧ HasUnitProOrder A K)
        (fun K ↦ (K : Set G)) := by
  rw [Filter.hasBasis_iff, hasCofinalUnitProOrder_iff]
  refine forall_congr' fun s ↦ ⟨fun h ↦ ⟨fun hs ↦ ?_, ?_⟩, fun h hs ↦ ?_⟩
  · obtain ⟨K, hKc, hKu, hKs⟩ := h hs
    exact ⟨K, ⟨hKc, hKu⟩, hKs⟩
  · rintro ⟨K, -, hKs⟩
    exact Filter.mem_of_superset (K.isOpen.mem_nhds K.one_mem) hKs
  · obtain ⟨K, ⟨hKc, hKu⟩, hKs⟩ := h.mp hs
    exact ⟨K, hKc, hKu, hKs⟩

/-- The compact open subgroups of `G` with invertible pro-order in `A` form a neighbourhood basis
of `1`. -/
theorem HasCofinalUnitProOrder.hasBasis_nhds_one (hG : HasCofinalUnitProOrder A G) :
    (𝓝 (1 : G)).HasBasis
      (fun K : OpenSubgroup G ↦ IsCompact (K : Set G) ∧ HasUnitProOrder A K)
      (fun K ↦ (K : Set G)) :=
  hasCofinalUnitProOrder_iff_hasBasis_nhds_one.mp hG

/-- Every open subgroup of a group with `HasCofinalUnitProOrder A G` contains a compact open
subgroup of invertible pro-order in `A`. -/
theorem HasCofinalUnitProOrder.exists_le (hG : HasCofinalUnitProOrder A G) (U : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ HasUnitProOrder A K ∧ K ≤ U :=
  hG (U : Set G) (U.isOpen.mem_nhds U.one_mem)

/-- Under `HasCofinalUnitProOrder A G`, the compact open subgroups of `G` with invertible pro-order
in `A` form a downward-directed family. -/
theorem HasCofinalUnitProOrder.directedOn_ge (hG : HasCofinalUnitProOrder A G) :
    DirectedOn (· ≥ ·) {K : OpenSubgroup G | IsCompact (K : Set G) ∧ HasUnitProOrder A K} := by
  rintro K₁ - K₂ -
  obtain ⟨K, hKc, hKu, hK⟩ := hG.exists_le (K₁ ⊓ K₂)
  exact ⟨K, ⟨hKc, hKu⟩, le_inf_iff.mp hK⟩

/-- In a group with separately continuous multiplication, the compact open subgroups of invertible
pro-order in `A` are closed under binary intersection and hence downward-directed, even without
`HasCofinalUnitProOrder A G`. -/
theorem directedOn_ge_isCompact_hasUnitProOrder [SeparatelyContinuousMul G] :
    DirectedOn (· ≥ ·) {K : OpenSubgroup G | IsCompact (K : Set G) ∧ HasUnitProOrder A K} := by
  rintro K₁ ⟨hK₁c, hK₁u⟩ K₂ -
  exact ⟨K₁ ⊓ K₂, ⟨hK₁c.inter_right K₂.isClosed, hK₁u.mono_openSubgroup hK₁c inf_le_left⟩,
    inf_le_left, inf_le_right⟩

/-- In a nonarchimedean topological group (and hence in every locally profinite group),
`HasCofinalUnitProOrder A G` holds if and only if every open subgroup contains a compact open
subgroup with invertible pro-order in `A`. -/
theorem hasCofinalUnitProOrder_iff_forall_openSubgroup_exists_le [NonarchimedeanGroup G] :
    HasCofinalUnitProOrder A G ↔
      ∀ U : OpenSubgroup G, ∃ K : OpenSubgroup G,
        IsCompact (K : Set G) ∧ HasUnitProOrder A K ∧ K ≤ U := by
  refine ⟨fun hG ↦ hG.exists_le, fun h s hs ↦ ?_⟩
  obtain ⟨U, hUs⟩ := NonarchimedeanGroup.is_nonarchimedean s hs
  obtain ⟨K, hKc, hKu, hKU⟩ := h U
  exact ⟨K, hKc, hKu, Set.Subset.trans hKU hUs⟩

/-- Every discrete group has `HasCofinalUnitProOrder A G` over every semiring `A`, witnessed by the
trivial subgroup. -/
theorem hasCofinalUnitProOrder_of_discreteTopology [DiscreteTopology G] :
    HasCofinalUnitProOrder A G := by
  intro s hs
  let B : OpenSubgroup G := ⟨⊥, isOpen_discrete _⟩
  have hB : (B : Set G) = {1} := Subgroup.coe_bot
  have : Subsingleton B :=
    ⟨fun x y ↦ Subtype.ext ((Subgroup.mem_bot.mp x.2).trans (Subgroup.mem_bot.mp y.2).symm)⟩
  refine ⟨B, hB ▸ isCompact_singleton, hasUnitProOrder_of_subsingleton, ?_⟩
  rw [hB, Set.singleton_subset_iff]
  exact mem_of_mem_nhds hs

/-- `HasCofinalUnitProOrder` is preserved along semiring homomorphisms. -/
theorem HasCofinalUnitProOrder.map {B : Type w} [Semiring B] (hG : HasCofinalUnitProOrder A G)
    (f : A →+* B) : HasCofinalUnitProOrder B G := by
  intro s hs
  obtain ⟨K, hKc, hKu, hKs⟩ := hG s hs
  exact ⟨K, hKc, hKu.map f, hKs⟩

/-- `HasCofinalUnitProOrder` is invariant under ring isomorphism of the coefficient semiring. -/
theorem hasCofinalUnitProOrder_congr_ring {B : Type w} [Semiring B] (e : A ≃+* B) :
    HasCofinalUnitProOrder A G ↔ HasCofinalUnitProOrder B G :=
  ⟨fun h ↦ h.map e.toRingHom, fun h ↦ h.map e.symm.toRingHom⟩

/-- `HasCofinalUnitProOrder` is preserved along topological group isomorphisms. -/
theorem HasCofinalUnitProOrder.of_equiv {H : Type w} [Group H] [TopologicalSpace H]
    (hG : HasCofinalUnitProOrder A G) (e : G ≃ₜ* H) : HasCofinalUnitProOrder A H := by
  intro s hs
  have hpre : e ⁻¹' s ∈ 𝓝 (1 : G) :=
    ((map_continuous e).continuousAt (x := 1)).preimage_mem_nhds (by rwa [map_one])
  obtain ⟨K, hKc, hKu, hKs⟩ := hG (e ⁻¹' s) hpre
  let K' : OpenSubgroup H := K.comap e.symm.toMulEquiv.toMonoidHom (map_continuous e.symm)
  have hcoe : (K' : Set H) = e '' (K : Set G) := by
    ext y
    refine ⟨fun hy ↦ ⟨e.symm y, hy, e.apply_symm_apply y⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩
    have hx' : e.symm (e x) ∈ K := (e.symm_apply_apply x).symm ▸ hx
    exact hx'
  have hmem (x : K) : e x.1 ∈ K' := by
    rw [← SetLike.mem_coe, hcoe]
    exact ⟨x.1, x.2, rfl⟩
  have hequiv : K ≃ₜ* K' :=
    { toMulEquiv :=
        { toFun := fun x ↦ ⟨e x.1, hmem x⟩
          invFun := fun y ↦ ⟨e.symm y.1, y.2⟩
          left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.1)
          right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y.1)
          map_mul' := fun x y ↦ Subtype.ext (map_mul e x.1 y.1) }
      continuous_toFun := ((map_continuous e).comp continuous_subtype_val).subtype_mk hmem
      continuous_invFun := ((map_continuous e.symm).comp continuous_subtype_val).subtype_mk
        fun y ↦ y.2 }
  refine ⟨K', hcoe ▸ hKc.image (map_continuous e), hKu.of_equiv hequiv, ?_⟩
  rw [hcoe, Set.image_subset_iff]
  exact hKs

/-- `HasCofinalUnitProOrder` is invariant under topological group isomorphism. -/
theorem hasCofinalUnitProOrder_congr {H : Type w} [Group H] [TopologicalSpace H] (e : G ≃ₜ* H) :
    HasCofinalUnitProOrder A G ↔ HasCofinalUnitProOrder A H :=
  ⟨fun h ↦ h.of_equiv e, fun h ↦ h.of_equiv e.symm⟩

/-- A product of two topological groups with `HasCofinalUnitProOrder` in `A` again has
`HasCofinalUnitProOrder` in `A`. -/
theorem HasCofinalUnitProOrder.prod {H : Type w} [Group H] [TopologicalSpace H]
    (hG : HasCofinalUnitProOrder A G) (hH : HasCofinalUnitProOrder A H) :
    HasCofinalUnitProOrder A (G × H) := by
  intro s hs
  rw [Prod.one_eq_mk, nhds_prod_eq, Filter.mem_prod_iff] at hs
  obtain ⟨s₁, hs₁, s₂, hs₂, hsub⟩ := hs
  obtain ⟨K₁, hK₁c, hK₁u, hK₁s⟩ := hG s₁ hs₁
  obtain ⟨K₂, hK₂c, hK₂u, hK₂s⟩ := hH s₂ hs₂
  have hequiv : (K₁ × K₂) ≃ₜ* K₁.prod K₂ :=
    { toMulEquiv := (Subgroup.prodEquiv K₁.toSubgroup K₂.toSubgroup).symm
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)).subtype_mk fun x ↦ ⟨x.1.2, x.2.2⟩
      continuous_invFun :=
        ((continuous_fst.comp continuous_subtype_val).subtype_mk fun x ↦ x.2.1).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk fun x ↦ x.2.2) }
  refine ⟨K₁.prod K₂, ?_, (hK₁u.prod hK₂u).of_equiv hequiv, ?_⟩
  · rw [OpenSubgroup.coe_prod]
    exact hK₁c.prod hK₂c
  · rw [OpenSubgroup.coe_prod]
    exact (Set.prod_mono hK₁s hK₂s).trans hsub

private theorem HasCofinalUnitProOrder.of_prod_left {H : Type w} [Group H] [TopologicalSpace H]
    (hGH : HasCofinalUnitProOrder A (G × H)) : HasCofinalUnitProOrder A G := by
  intro s hs
  have hprod : s ×ˢ (Set.univ : Set H) ∈ 𝓝 (1 : G × H) := by
    rw [Prod.one_eq_mk, nhds_prod_eq]
    exact Filter.prod_mem_prod hs Filter.univ_mem
  obtain ⟨K, hKc, hKu, hKs⟩ := hGH (s ×ˢ Set.univ) hprod
  have hK₁open : IsOpen ((K.toSubgroup.map (MonoidHom.fst G H) : Subgroup G) : Set G) := by
    rw [Subgroup.coe_map]
    exact isOpenMap_fst _ K.isOpen
  let K₁ : OpenSubgroup G := ⟨K.toSubgroup.map (MonoidHom.fst G H), hK₁open⟩
  have hcoe : (K₁ : Set G) = Prod.fst '' (K : Set (G × H)) := Subgroup.coe_map _ _
  let p₁ : K →* K₁ :=
    { toFun := fun x ↦ ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hp₁c : Continuous p₁ :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk fun x ↦ ⟨x.1, x.2, rfl⟩
  have hp₁s : Function.Surjective p₁ := by
    rintro ⟨g, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨K₁, hcoe ▸ hKc.image continuous_fst, hKu.of_surjective p₁ hp₁c hp₁s, ?_⟩
  rw [hcoe, Set.image_subset_iff]
  exact fun x hx ↦ (hKs hx).1

/-- A product `G × H` of topological groups has `HasCofinalUnitProOrder` in `A` if and only if both
factors do. -/
@[simp]
theorem hasCofinalUnitProOrder_prod_iff {H : Type w} [Group H] [TopologicalSpace H] :
    HasCofinalUnitProOrder A (G × H) ↔
      HasCofinalUnitProOrder A G ∧ HasCofinalUnitProOrder A H := by
  have eswap : (G × H) ≃ₜ* (H × G) :=
    { toMulEquiv := MulEquiv.prodComm
      continuous_toFun := continuous_swap
      continuous_invFun := continuous_swap }
  exact ⟨fun h ↦ ⟨h.of_prod_left, (h.of_equiv eswap).of_prod_left⟩, fun ⟨hG, hH⟩ ↦ hG.prod hH⟩

/-- An open subgroup `U` of `G` has `HasCofinalUnitProOrder A U` if and only if `G` does. -/
@[simp]
theorem _root_.OpenSubgroup.hasCofinalUnitProOrder_iff (U : OpenSubgroup G) :
    HasCofinalUnitProOrder A U ↔ HasCofinalUnitProOrder A G := by
  constructor
  · intro hU s hs
    have hpre : Subtype.val ⁻¹' s ∈ 𝓝 (1 : U) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hs
    obtain ⟨K', hK'c, hK'u, hK's⟩ := hU (Subtype.val ⁻¹' s) hpre
    have hKopen : IsOpen ((K'.toSubgroup.map U.toSubgroup.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.coe_map]
      exact U.isOpen.isOpenMap_subtype_val _ K'.isOpen
    let K : OpenSubgroup G := ⟨K'.toSubgroup.map U.toSubgroup.subtype, hKopen⟩
    have hcoe : (K : Set G) = Subtype.val '' (K' : Set U) := Subgroup.coe_map _ _
    have hsub : K.toSubgroup.subgroupOf U.toSubgroup = K'.toSubgroup := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
    have hKu : HasUnitProOrder A K := by
      refine (Subgroup.hasUnitProOrder_subgroupOf_iff (Subgroup.map_subtype_le K'.toSubgroup)).mp ?_
      rw [hsub]
      exact hK'u
    exact ⟨K, hcoe ▸ hK'c.image continuous_subtype_val, hKu, hcoe ▸ Set.image_subset_iff.mpr hK's⟩
  · intro hG s hs
    have himg : (Subtype.val '' s : Set G) ∈ 𝓝 (1 : G) :=
      U.isOpen.isOpenMap_subtype_val.image_mem_nhds hs
    obtain ⟨K, hKc, hKu, hKs⟩ := hG (Subtype.val '' s) himg
    have hKU : K.toSubgroup ≤ U.toSubgroup :=
      fun g hg ↦ let ⟨u, _, hu⟩ := hKs hg; hu ▸ u.2
    let K' : OpenSubgroup U := K.comap U.toSubgroup.subtype continuous_subtype_val
    have himg_K' : Subtype.val '' (K' : Set U) = (K : Set G) := by
      ext g
      simp only [K', Set.mem_image]
      exact ⟨fun ⟨_, hu, hug⟩ ↦ hug ▸ hu, fun hg ↦ ⟨⟨g, hKU hg⟩, hg, rfl⟩⟩
    have hK'c : IsCompact (K' : Set U) :=
      Topology.IsInducing.subtypeVal.isCompact_iff.mpr (himg_K' ▸ hKc)
    have hK'u : HasUnitProOrder A K' :=
      (Subgroup.hasUnitProOrder_subgroupOf_iff hKU).mpr hKu
    refine ⟨K', hK'c, hK'u, fun x hx ↦ ?_⟩
    obtain ⟨y, hy, hyx⟩ := hKs hx
    exact Subtype.ext hyx ▸ hy

/-- `HasCofinalUnitProOrder` passes to every open subgroup. -/
theorem HasCofinalUnitProOrder.openSubgroup (hG : HasCofinalUnitProOrder A G)
    (U : OpenSubgroup G) : HasCofinalUnitProOrder A U :=
  U.hasCofinalUnitProOrder_iff.mpr hG

/-- Every profinite group of invertible pro-order in `A` also has `HasCofinalUnitProOrder A U`. -/
theorem HasUnitProOrder.hasCofinalUnitProOrder [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (hG : HasUnitProOrder A G) :
    HasCofinalUnitProOrder A G := by
  intro s hs
  obtain ⟨W, hWs, hWopen, h1W⟩ := mem_nhds_iff.mp hs
  obtain ⟨N, hNW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWopen h1W
  exact ⟨N.toOpenSubgroup, N.toOpenSubgroup.isClosed.isCompact,
    hG.openSubgroup N.toOpenSubgroup, hNW.trans hWs⟩

/-- **Locally pro-`p` criterion for `HasCofinalUnitProOrder`.** Let `G` be a non-discrete totally
disconnected topological group admitting a compact open pro-`p` subgroup `U₀` (with `p` prime).
Then `HasCofinalUnitProOrder A G` holds if and only if `(p : A)` is a unit. -/
theorem hasCofinalUnitProOrder_iff_isUnit_of_isProP {p : ℕ} [Fact p.Prime]
    [IsTopologicalGroup G] [TotallyDisconnectedSpace G] (hnd : ¬ DiscreteTopology G)
    {U₀ : OpenSubgroup G} (hU₀ : IsCompact (U₀ : Set G)) (hproP : IsProP p U₀) :
    HasCofinalUnitProOrder A G ↔ IsUnit (p : A) := by
  have : IsTopologicalGroup U₀ :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup U₀.toSubgroup.subtype
  have : CompactSpace U₀ := isCompact_iff_compactSpace.mp hU₀
  rw [← U₀.hasCofinalUnitProOrder_iff]
  refine ⟨fun h ↦ ?_, fun hp ↦ (hproP.hasUnitProOrder hp).hasCofinalUnitProOrder⟩
  obtain ⟨K, -, hKu, -⟩ := h Set.univ Filter.univ_mem
  have : IsTopologicalGroup K :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup K.toSubgroup.subtype
  have : CompactSpace K := isCompact_iff_compactSpace.mp K.isClosed.isCompact
  have hK_inf : Infinite K := by
    refine Infinite.mk fun _ ↦ hnd ?_
    have h1K : IsOpen ({(1 : K)} : Set K) := isOpen_discrete _
    have h1U₀ : IsOpen ({(1 : U₀)} : Set U₀) := by
      simpa using K.isOpen.isOpenMap_subtype_val _ h1K
    have h1G : IsOpen ({(1 : G)} : Set G) := by
      simpa using U₀.isOpen.isOpenMap_subtype_val _ h1U₀
    exact discreteTopology_iff_isOpen_singleton_one.mpr h1G
  exact ((hproP.subgroup K.toSubgroup).hasUnitProOrder_iff).mp hKu

end Cofinal

end TauCeti
