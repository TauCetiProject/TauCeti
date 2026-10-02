/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Submonoid.MulAction
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.LocallyFinite

/-!
# Transfer instances for restricted and properly discontinuous actions

This file records generic instances for actions on a topological space that typeclass search
cannot otherwise reach. A submonoid, and hence a subgroup, inherits `ContinuousConstSMul` from
an ambient scalar action; and a properly discontinuous action has `Finite` point stabilisers.
It also records that a properly discontinuous scalar family on a nonempty σ-compact space is
countable, and that the translates of a compact set under it form a locally finite family.

## Main results

* `Submonoid.continuousConstSMul` and `TauCeti.Subgroup.continuousConstSMul`: continuity
  in the point is inherited by a submonoid, hence by a subgroup.
* `SubMulAction.properlyDiscontinuousSMul`: proper discontinuity is inherited by every invariant
  subspace.
* `TauCeti.finite_stabilizer_of_properlyDiscontinuousSMul`: a properly discontinuous action has
  finite point stabilisers, as an instance rather than as `Set.Finite` of the carrier.
* `TauCeti.countable_of_properlyDiscontinuousSMul`: a properly discontinuous scalar family on a
  nonempty σ-compact space is countable.
* `TauCeti.locallyFinite_smul_of_isCompact`: under a properly discontinuous action on a weakly
  locally compact space, the translates of a compact set form a locally finite family.
* `TauCeti.isClosed_iUnion_smul_of_isCompact`: the union of the translates of a closed compact set
  under such an action of a group is closed.
-/

public section

namespace TauCeti

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
