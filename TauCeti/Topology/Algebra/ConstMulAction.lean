/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.LocallyFinite

import Mathlib.Topology.Algebra.Group.Basic

/-!
# Transfer instances for restricted and properly discontinuous actions

This file records generic instances for actions on a topological space that typeclass search
cannot otherwise reach. A submonoid, and hence a subgroup, inherits `ContinuousConstSMul` from
an ambient scalar action; and a properly discontinuous action has `Finite` point stabilisers.
It also records that a properly discontinuous scalar family on a nonempty σ-compact space is
countable, and that the translates of a compact set under it form a locally finite family.
Conversely, for a jointly continuous action of a `T₁` group with separately continuous
multiplication, local finiteness of the translates of any nonempty set forces the group topology
to be discrete. Likewise, a nonempty open set disjoint from all of its nontrivial translates
forces the acting topological group to be discrete, and on such a set the orbit projection is an
open embedding.

## Main results

* `Submonoid.continuousConstSMul` and `TauCeti.Subgroup.continuousConstSMul`: continuity
  in the point is inherited by a submonoid, hence by a subgroup.
* `SubMulAction.properlyDiscontinuousSMul`: proper discontinuity is inherited by every invariant
  subspace.
* `TauCeti.properlyDiscontinuousSMul_of_conjAct_smul_eq`: a conjugate `g H g⁻¹` of a
  properly discontinuous subgroup `H` acts properly discontinuously.
* `TauCeti.finite_stabilizer_of_properlyDiscontinuousSMul`: a properly discontinuous action has
  finite point stabilisers, as an instance rather than as `Set.Finite` of the carrier.
* `TauCeti.countable_of_properlyDiscontinuousSMul`: a properly discontinuous scalar family on a
  nonempty σ-compact space is countable.
* `TauCeti.locallyFinite_smul_of_isCompact`: under a properly discontinuous action on a weakly
  locally compact space, the translates of a compact set form a locally finite family.
* `TauCeti.discreteTopology_of_locallyFinite_smul`: if the translates of a nonempty set under a
  continuous action are locally finite, then the acting group is discrete.
* `TauCeti.isClosed_iUnion_smul_of_isCompact`: the union of the translates of a closed compact set
  under such an action of a group is closed.
* `TauCeti.isOpenEmbedding_quotientMk_domRestrict_of_disjoint_smul`: the orbit projection is an
  open embedding on an open set disjoint from its nontrivial translates.
* `TauCeti.discreteTopology_of_disjoint_smul`: the existence of a nonempty such open set makes the
  acting topological group discrete.
-/

public section

namespace TauCeti

open Topology
open scoped Pointwise

section DisjointTranslates

open Set

variable {G X : Type*} [Group G] [MulAction G X] {U : Set X}

/-- The orbit projection is injective on a set disjoint from each of its nontrivial translates. -/
theorem injOn_quotientMk_of_disjoint_smul
    (hU : ∀ g : G, g ≠ 1 → Disjoint (g • U) U) :
    Set.InjOn (Quotient.mk'' : X → MulAction.orbitRel.Quotient G X) U := by
  intro x hx y hy hxy
  obtain ⟨g, rfl⟩ :=
    MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hxy))
  have hg_one : g = 1 := by
    by_contra hg_ne
    exact Set.disjoint_left.mp (hU g hg_ne) (Set.smul_mem_smul_set hy) hx
  rw [hg_one, one_smul]

variable [TopologicalSpace X] [ContinuousConstSMul G X]

/-- On an open set disjoint from each of its nontrivial translates, the orbit projection is an
open embedding. Thus this set is an honest open chart in the orbit space, not merely a set of
orbit representatives. -/
theorem isOpenEmbedding_quotientMk_domRestrict_of_disjoint_smul (hU_open : IsOpen U)
    (hU : ∀ g : G, g ≠ 1 → Disjoint (g • U) U) :
    IsOpenEmbedding
      (U.domRestrict (Quotient.mk'' : X → MulAction.orbitRel.Quotient G X)) := by
  refine .of_continuous_injective_isOpenMap
    (continuous_quot_mk.comp continuous_subtype_val) ?_
    (MulAction.isOpenQuotientMap_quotientMk.isOpenMap.domRestrict hU_open)
  intro x y hxy
  exact Subtype.ext (injOn_quotientMk_of_disjoint_smul hU x.2 y.2 hxy)

end DisjointTranslates

section DisjointTranslatesAdd

open Set

variable {A X : Type*} [AddGroup A] [AddAction A X] {U : Set X}

/-- The additive orbit projection is injective on a set disjoint from each of its nontrivial
translates. -/
theorem injOn_quotientMk_of_disjoint_vadd
    (hU : ∀ a : A, a ≠ 0 → Disjoint (a +ᵥ U) U) :
    Set.InjOn (Quotient.mk'' : X → AddAction.orbitRel.Quotient A X) U := by
  intro x hx y hy hxy
  obtain ⟨a, rfl⟩ :=
    AddAction.mem_orbit_iff.mp (AddAction.orbitRel_apply.mp (Quotient.exact hxy))
  have ha_zero : a = 0 := by
    by_contra ha_ne
    exact Set.disjoint_left.mp (hU a ha_ne) (Set.vadd_mem_vadd_set hy) hx
  rw [ha_zero, zero_vadd]

variable [TopologicalSpace X] [ContinuousConstVAdd A X]

/-- On an open set disjoint from each of its nontrivial additive translates, the additive orbit
projection is an open embedding. -/
theorem isOpenEmbedding_quotientMk_domRestrict_of_disjoint_vadd (hU_open : IsOpen U)
    (hU : ∀ a : A, a ≠ 0 → Disjoint (a +ᵥ U) U) :
    IsOpenEmbedding
      (U.domRestrict (Quotient.mk'' : X → AddAction.orbitRel.Quotient A X)) := by
  refine .of_continuous_injective_isOpenMap
    (continuous_quot_mk.comp continuous_subtype_val) ?_
    (AddAction.isOpenQuotientMap_quotientMk.isOpenMap.domRestrict hU_open)
  intro x y hxy
  exact Subtype.ext (injOn_quotientMk_of_disjoint_vadd hU x.2 y.2 hxy)

end DisjointTranslatesAdd

section DiscreteTopology

open Set

variable {G X : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [TopologicalSpace X] [MulAction G X] {U : Set X}

/-- **Discreteness from a disjoint open translate.** If a topological group acts with continuous
orbit maps and some nonempty open set is disjoint from all of its translates by nonidentity
elements, then the group is discrete. -/
@[to_additive
/-- **Discreteness from a disjoint open translate.** If a topological additive group acts with
continuous orbit maps and some nonempty open set is disjoint from all of its translates by nonzero
elements, then the group is discrete. -/]
theorem discreteTopology_of_disjoint_smul (hcont : ∀ x : X, Continuous fun g : G ↦ g • x)
    (hU_open : IsOpen U) (hU_nonempty : U.Nonempty) (hU : ∀ g : G, g ≠ 1 → Disjoint (g • U) U) :
    DiscreteTopology G := by
  apply discreteTopology_of_isOpen_singleton_one
  -- The elements carrying a chosen point of `U` back into `U` form an open set equal to `{1}`.
  obtain ⟨x, hx⟩ := hU_nonempty
  have hopen : IsOpen ((fun g : G ↦ g • x) ⁻¹' U) := hU_open.preimage (hcont x)
  have heq : (fun g : G ↦ g • x) ⁻¹' U = {1} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hgx
      by_contra hg_ne
      exact Set.disjoint_left.mp (hU g hg_ne) (Set.smul_mem_smul_set hx) hgx
    · rintro rfl
      simpa using hx
  rwa [heq] at hopen

variable [ContinuousSMul G X] [T1Space G] {S : Set X}

/-- **Local finiteness of the translates of a nonempty set forces the acting group to be
discrete.**

The set need not be open, closed, or compact, and the action need not be faithful. This is the
discreteness criterion for a group whose translates of a fundamental polygon form a locally
finite tessellation. -/
@[to_additive
/-- **Local finiteness of the translates of a nonempty set forces the acting additive group to be
discrete.** -/]
theorem discreteTopology_of_locallyFinite_smul (hS : S.Nonempty)
    (hlocal : LocallyFinite fun g : G ↦ g • S) : DiscreteTopology G := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨U, hU, hfinite⟩ := hlocal x
  let V : Set G := (fun g ↦ g • x) ⁻¹' U
  have hV : V ∈ nhds (1 : G) := by
    exact (continuous_smul.comp (continuous_id.prodMk continuous_const)).continuousAt
      (by simpa only [Function.comp_apply, id_eq, one_smul] using hU)
  have hVF : V ⊆ {g : G | (g • S ∩ U).Nonempty} := by
    intro g hg
    exact ⟨g • x, ⟨x, hx, rfl⟩, hg⟩
  exact discreteTopology_of_isOpen_singleton_one <|
    isOpen_singleton_of_finite_mem_nhds 1 (Filter.mem_of_superset hV hVF) hfinite

end DiscreteTopology

/-- A submonoid inherits continuity in the point from an ambient continuous action. -/
@[to_additive
  /-- An additive submonoid inherits continuity in the point from an ambient continuous additive
  action. -/]
instance _root_.Submonoid.continuousConstSMul {M X : Type*} [MulOneClass M] [TopologicalSpace X]
    [SMul M X] [ContinuousConstSMul M X] (S : Submonoid M) : ContinuousConstSMul S X :=
  ⟨fun g => by
    simpa only [Submonoid.smul_def] using continuous_const_smul (g : M)⟩

namespace Subgroup

/-- A subgroup inherits continuity in the point from an ambient continuous action. -/
instance continuousConstSMul {G X : Type*} [Group G] [TopologicalSpace X] [SMul G X]
    [ContinuousConstSMul G X] (S : Subgroup G) : ContinuousConstSMul S X :=
  Submonoid.continuousConstSMul S.toSubmonoid

end Subgroup

open scoped Pointwise in
/-- **Conjugation preserves proper discontinuity**: if `H'` is the conjugate `g H g⁻¹` of a
subgroup `H` acting properly discontinuously, then `H'` acts properly discontinuously, since
`g k g⁻¹` moves `K` to meet `L` exactly when `k` moves `g⁻¹ • K` to meet `g⁻¹ • L`. -/
theorem properlyDiscontinuousSMul_of_conjAct_smul_eq {G X : Type*} [Group G] [TopologicalSpace X]
    [MulAction G X] [ContinuousConstSMul G X] {H H' : _root_.Subgroup G} {g : G}
    [ProperlyDiscontinuousSMul H X] (h : ConjAct.toConjAct g • H = H') :
    ProperlyDiscontinuousSMul H' X where
  finite_disjoint_inter_image {K L} hK hL := by
    subst h
    let φ : H → (ConjAct.toConjAct g • H : _root_.Subgroup G) := fun k ↦
      ⟨g * k * g⁻¹, by
        simpa [ConjAct.toConjAct_smul] using
          _root_.Subgroup.smul_mem_pointwise_smul _ (ConjAct.toConjAct g) H k.2⟩
    refine ((ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := H)
      (hK.image (continuous_const_smul g⁻¹)) (hL.image (continuous_const_smul g⁻¹))).image
        φ).subset ?_
    intro k hk
    have hk' : g⁻¹ * k * g ∈ H := by
      have := _root_.Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp k.2
      rwa [← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, inv_inv] at this
    refine ⟨⟨g⁻¹ * k * g, hk'⟩, ?_, Subtype.ext (by simp [φ, mul_assoc])⟩
    -- a point `x ∈ K` with `k • x ∈ L` gives `g⁻¹ • x ∈ g⁻¹ • K` moved into `g⁻¹ • L`
    obtain ⟨_, ⟨x, hx, rfl⟩, hxL⟩ := hk
    refine ⟨g⁻¹ • ((k : G) • x), ⟨g⁻¹ • x, ⟨x, hx, rfl⟩, ?_⟩, ⟨_, hxL, rfl⟩⟩
    simp [_root_.Subgroup.smul_def, mul_smul]

end TauCeti

namespace SubMulAction

/-- A properly discontinuous action remains properly discontinuous on every invariant subspace. -/
theorem properlyDiscontinuousSMul {G X : Type*} [TopologicalSpace X] [SMul G X]
    [ProperlyDiscontinuousSMul G X] (S : SubMulAction G X) : ProperlyDiscontinuousSMul G S where
  finite_disjoint_inter_image {K L} hK hL := by
    refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image
      (hK.image continuous_subtype_val) (hL.image continuous_subtype_val)).subset ?_
    rintro g ⟨y, ⟨x, hx, hxy⟩, hy⟩
    exact
      ⟨(y : X), ⟨(x : X), ⟨x, hx, rfl⟩, congrArg Subtype.val hxy⟩, ⟨y, hy, rfl⟩⟩

end SubMulAction

namespace TauCeti

/-- **A properly discontinuous action has finite point stabilisers**, as a `Finite` instance.

Mathlib's `ProperlyDiscontinuousSMul.finite_stabilizer` (Alex Kontorovich and Heather Macbeth,
`Mathlib/Topology/Algebra/ConstMulAction.lean`) states this as `Set.Finite` of the stabiliser's
carrier. That form does not drive typeclass search, so a count through `Nat.card` — which is the
junk value `0` on an infinite type — has to bridge to `Finite` by hand at each use. This does it
once, for every properly discontinuous action.

For an action of a subgroup of `GL(2, ℝ)` no further instance is needed: Mathlib's
`Subgroup.IsArithmetic.properlyDiscontinuous` supplies proper discontinuity for an arithmetic
`𝒢 ≤ GL(2, ℝ)`, and the image of a finite-index `Γ ≤ SL(2, ℤ)` is arithmetic, so both shapes
reach `Finite` through this instance alone. The stabiliser of a point under `SL(2, ℤ)` itself is
*not* one of those shapes — `SL(2, ℤ)` is a type, not a `Subgroup (GL (Fin 2) ℝ)`, so there is no
`ProperlyDiscontinuousSMul SL(2, ℤ) ℍ` to apply — and stays with the hand-proved
`TauCeti.ModularGroup.finite_stabilizer`. -/
@[to_additive
/-- **A properly discontinuous additive action has finite point stabilisers**, as a `Finite`
instance. Mathlib's `ProperlyDiscontinuousVAdd.finite_stabilizer` states it as `Set.Finite` of
the stabiliser's carrier, which does not drive typeclass search; this bridges it once. -/]
instance finite_stabilizer_of_properlyDiscontinuousSMul {G T : Type*} [Group G]
    [TopologicalSpace T] [MulAction G T] [ProperlyDiscontinuousSMul G T] (x : T) :
    Finite (MulAction.stabilizer G x) :=
  (ProperlyDiscontinuousSMul.finite_stabilizer x).to_subtype

open Set in
/-- **A properly discontinuous scalar family on a nonempty σ-compact space is countable.**
Each element carries a chosen point `x₀` into one of countably many compact sets `Kₙ ∋ x₀`, and
only finitely many elements move a given `Kₙ` to meet itself. -/
@[to_additive
/-- **A properly discontinuous additive scalar family on a nonempty σ-compact space is
countable.** -/]
theorem countable_of_properlyDiscontinuousSMul (G : Type*) {T : Type*} [TopologicalSpace T]
    [SMul G T] [ProperlyDiscontinuousSMul G T] [SigmaCompactSpace T]
    [Nonempty T] : Countable G := by
  obtain ⟨x₀⟩ := ‹Nonempty T›
  let K : ℕ → Set T := fun n ↦ insert x₀ (compactCovering T n)
  have hK : ∀ n, IsCompact (K n) := fun n ↦ (isCompact_compactCovering T n).insert x₀
  refine countable_univ_iff.mp <| (countable_iUnion fun n ↦
    (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) (hK n) (hK n)).countable).mono
      fun g _ ↦ ?_
  obtain ⟨n, hn⟩ := mem_iUnion.mp (iUnion_compactCovering T ▸ mem_univ (g • x₀))
  exact mem_iUnion.mpr ⟨n, g • x₀, ⟨x₀, mem_insert _ _, rfl⟩, mem_insert_of_mem _ hn⟩

section LocallyFinite

open scoped Pointwise

variable {Γ T : Type*} [TopologicalSpace T] [SMul Γ T] [ProperlyDiscontinuousSMul Γ T]
  {S : Set T}

/-- **The translates of a compact set under a properly discontinuous action are locally
finite**, in the sense of Katok (*Fuchsian groups, geodesic flows on surfaces of constant negative
curvature and symbolic coding of geodesics*, Clay Math. Proc. 10 (2010), Definition 8.2, p. 27):
every point has a neighbourhood meeting only finitely many of them. -/
@[to_additive
/-- **The translates of a compact set under a properly discontinuous additive action are locally
finite.** -/]
theorem locallyFinite_smul_of_isCompact [WeaklyLocallyCompactSpace T] (hS : IsCompact S) :
    LocallyFinite fun γ : Γ ↦ γ • S := fun x ↦
  let ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  ⟨K, hKx, properlyDiscontinuousSMul_iff.1 ‹_› hS hK⟩

end LocallyFinite

section IsClosedIUnion

open scoped Pointwise

variable {G T : Type*} [TopologicalSpace T] [Group G] [MulAction G T] [ContinuousConstSMul G T]
  [ProperlyDiscontinuousSMul G T] [WeaklyLocallyCompactSpace T] {S : Set T}

/-- **The union of the translates of a closed compact set under a properly discontinuous action
is closed.** -/
@[to_additive
/-- **The union of the translates of a closed compact set under a properly discontinuous additive
action is closed.** -/]
theorem isClosed_iUnion_smul_of_isCompact (hS : IsCompact S) (hS' : IsClosed S) :
    IsClosed (⋃ g : G, g • S) :=
  (locallyFinite_smul_of_isCompact hS).isClosed_iUnion fun g ↦ hS'.smul g

end IsClosedIUnion

end TauCeti
