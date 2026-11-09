/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Immersion

/-!
# Immersed Lie subgroups

An immersed Lie subgroup of a Lie group `G` need not use the topology inherited from `G`.  For
example, a dense one-parameter subgroup of a torus has its natural one-dimensional manifold
topology, which is finer than its subspace topology.  Consequently, an immersed subgroup is
represented here by a connected Lie group `X` together with an injective smooth immersion into
`G`, rather than by putting manifold instances on the subtype of a `Subgroup G`.

`TauCeti.Lie.ImmersedLieSubgroupData I K` records such a presentation whose image is exactly `K`.
The existential predicate `TauCeti.Lie.IsImmersedLieSubgroup I K` forgets the choice of source and
its manifold structure.  Mathlib's `Manifold.IsImmersion` is used directly, so smoothness and
injectivity of the differential are consequences rather than duplicated fields.

This is the carrier interface for constructing connected immersed subgroups from integral leaves
of left-invariant distributions.

## Main definitions and results

* `TauCeti.Lie.ImmersedLieSubgroupData`: a connected Lie group mapping injectively and immersively
  onto a specified subgroup, with a finite-dimensional source model.
* `TauCeti.Lie.IsImmersedLieSubgroup`: existence of immersed-Lie-subgroup data.
* `TauCeti.Lie.ImmersedLieSubgroupData.contMDiff_toHom`: the presenting homomorphism is smooth.
* `TauCeti.Lie.ImmersedLieSubgroupData.injective_mfderiv_toHom`: its differential is injective.
* `TauCeti.Lie.isImmersedLieSubgroup_top`: a connected Lie group is an immersed subgroup of itself.

* `TauCeti.Lie.ImmersedLieSubgroupData.homOfLe`: the canonical algebraic factorization,
  with ambient apply, uniqueness, identity and composition formulas, including the applied
  `TauCeti.Lie.ImmersedLieSubgroupData.homOfLe_homOfLe`.
* `TauCeti.Lie.ImmersedLieSubgroupData.existsUnique_monoidHom_of_le`: uniqueness among all
  algebraic factorizations.
* `TauCeti.Lie.ImmersedLieSubgroupData.mulEquivOfEq`: the canonical algebraic equivalence,
  with ambient apply, inverse, coercion, uniqueness, identity and composition formulas, including
  the applied `TauCeti.Lie.ImmersedLieSubgroupData.mulEquivOfEq_mulEquivOfEq`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Chapter 19.
-/

public section

noncomputable section

open scoped ContDiff Manifold

universe u v w

namespace TauCeti.Lie

/-- Data presenting a subgroup `K` of a Lie group modeled on `I` as a connected immersed Lie
subgroup.

The source `X` carries its own topology and smooth structure.  The homomorphism `toHom` is
injective, has range exactly `K`, and is an immersion.  Thus the topology of `X` is not required
to agree with the subspace topology on `K`; this is the distinction between immersed and embedded
Lie subgroups. -/
structure ImmersedLieSubgroupData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G]
    [LieGroup I ∞ G]
    (K : Subgroup G) where
  /-- The smooth manifold structure on the ambient group. -/
  [ambientIsManifold : IsManifold I ∞ G]
  /-- The connected Lie group which parametrizes the immersed subgroup. -/
  X : Type w
  /-- The group structure on the source. -/
  [group : Group X]
  /-- The intrinsic topology on the source. -/
  [topologicalSpace : TopologicalSpace X]
  /-- The model vector space of the source. -/
  E' : Type u
  /-- The additive topological structure on the source model space. -/
  [normedAddCommGroup : NormedAddCommGroup E']
  /-- The real normed-space structure on the source model space. -/
  [normedSpace : NormedSpace ℝ E']
  /-- The source model space is finite-dimensional. -/
  [finiteDimensional : FiniteDimensional ℝ E']
  /-- The model chart target of the source. -/
  H' : Type v
  /-- The topology on the source model chart target. -/
  [modelTopology : TopologicalSpace H']
  /-- The model with corners for the source. -/
  I' : ModelWithCorners ℝ E' H'
  /-- The charted-space structure on the source. -/
  [chartedSpace : ChartedSpace H' X]
  /-- The smooth manifold structure on the source. -/
  [isManifold : IsManifold I' ∞ X]
  /-- The smooth Lie-group structure on the source. -/
  [lieGroup : LieGroup I' ∞ X]
  /-- The source is connected. -/
  [connectedSpace : ConnectedSpace X]
  /-- The homomorphism from the source to the ambient Lie group. -/
  toHom : X →* G
  /-- The presenting homomorphism is injective. -/
  injective : Function.Injective toHom
  /-- The image of the presenting homomorphism is exactly the specified subgroup. -/
  range_eq : MonoidHom.range toHom = K
  /-- The presenting homomorphism is a smooth immersion. -/
  isImmersion : Manifold.IsImmersion I' I ∞ (toHom : X → G)

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type w} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

namespace ImmersedLieSubgroupData

variable {K L M : Subgroup G}

attribute [local instance] ImmersedLieSubgroupData.group
  ImmersedLieSubgroupData.topologicalSpace ImmersedLieSubgroupData.normedAddCommGroup
  ImmersedLieSubgroupData.normedSpace ImmersedLieSubgroupData.modelTopology
  ImmersedLieSubgroupData.chartedSpace ImmersedLieSubgroupData.isManifold
  ImmersedLieSubgroupData.lieGroup

/-- The homomorphism presenting an immersed Lie subgroup is smooth. -/
theorem contMDiff_toHom (d : ImmersedLieSubgroupData I K) :
    ContMDiff d.I' I ∞ (d.toHom : d.X → G) :=
  d.isImmersion.contMDiff

/-- The differential of the homomorphism presenting an immersed Lie subgroup is injective at
every point. -/
theorem injective_mfderiv_toHom (d : ImmersedLieSubgroupData I K) (x : d.X) :
    Function.Injective (mfderiv d.I' I (d.toHom : d.X → G) x) :=
  d.isImmersion.mfderiv_injective (by simp) x

/-- The canonical algebraic factorization between presentations of included subgroups. -/
noncomputable def homOfLe (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : K ≤ L) : d.X →* e.X :=
  let hr : d.toHom.range ≤ e.toHom.range := by
    rw [d.range_eq, e.range_eq]
    exact h
  (MonoidHom.ofInjective e.injective).symm.toMonoidHom.comp
    ((Subgroup.inclusion hr).comp d.toHom.rangeRestrict)

/-- The canonical algebraic factorization commutes with the ambient injections. -/
@[simp]
theorem toHom_homOfLe_apply (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : K ≤ L) (x : d.X) :
    e.toHom (d.homOfLe e h x) = d.toHom x := by
  simp only [homOfLe, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MonoidHom.apply_ofInjective_symm, Subgroup.coe_inclusion, MonoidHom.coe_rangeRestrict]

/-- The ambient commuting diagram determines an algebraic factorization uniquely. -/
theorem eq_homOfLe (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : K ≤ L) (φ : d.X →* e.X)
    (hφ : ∀ x, e.toHom (φ x) = d.toHom x) : φ = d.homOfLe e h := by
  ext x
  apply e.injective
  rw [hφ, toHom_homOfLe_apply]

/-- Included underlying subgroups give a unique algebraic factorization. No smoothness
assumption is required for uniqueness. -/
theorem existsUnique_monoidHom_of_le (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : K ≤ L) :
    ∃! φ : d.X →* e.X, ∀ x, e.toHom (φ x) = d.toHom x := by
  refine ⟨d.homOfLe e h, d.toHom_homOfLe_apply e h, ?_⟩
  intro φ hφ
  exact d.eq_homOfLe e h φ hφ

/-- Factoring a presentation through itself gives the identity homomorphism. -/
@[simp]
theorem homOfLe_refl (d : ImmersedLieSubgroupData I K) :
    d.homOfLe d le_rfl = MonoidHom.id d.X := by
  symm
  apply d.eq_homOfLe d le_rfl
  intro x
  rfl

/-- Canonical factorizations compose according to subgroup inclusion. -/
@[simp]
theorem homOfLe_comp (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (f : ImmersedLieSubgroupData I M)
    (hKL : K ≤ L) (hLM : L ≤ M) :
    (e.homOfLe f hLM).comp (d.homOfLe e hKL) = d.homOfLe f (hKL.trans hLM) := by
  apply d.eq_homOfLe f (hKL.trans hLM)
  intro x
  simp only [MonoidHom.comp_apply, toHom_homOfLe_apply]

/-- Successive canonical factorizations evaluate as the factorization of the composed inclusion. -/
@[simp]
theorem homOfLe_homOfLe (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (f : ImmersedLieSubgroupData I M)
    (hKL : K ≤ L) (hLM : L ≤ M) (x : d.X) :
    e.homOfLe f hLM (d.homOfLe e hKL x) = d.homOfLe f (hKL.trans hLM) x := by
  simpa only [MonoidHom.comp_apply] using
    DFunLike.congr_fun (d.homOfLe_comp e f hKL hLM) x

/-- The canonical algebraic group equivalence between presentations of equal subgroups. -/
noncomputable def mulEquivOfEq (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : K = L) : d.X ≃* e.X where
  toFun := d.homOfLe e h.le
  invFun := e.homOfLe d h.ge
  left_inv x := by
    apply d.injective
    simp only [toHom_homOfLe_apply]
  right_inv x := by
    apply e.injective
    simp only [toHom_homOfLe_apply]
  map_mul' := (d.homOfLe e h.le).map_mul

/-- The canonical equivalence commutes with the ambient injections. -/
@[simp]
theorem toHom_mulEquivOfEq_apply (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : K = L) (x : d.X) :
    e.toHom (d.mulEquivOfEq e h x) = d.toHom x :=
  d.toHom_homOfLe_apply e h.le x

/-- The inverse canonical equivalence commutes with the ambient injections. -/
theorem toHom_mulEquivOfEq_symm_apply (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : K = L) (y : e.X) :
    d.toHom ((d.mulEquivOfEq e h).symm y) = e.toHom y :=
  e.toHom_homOfLe_apply d h.ge y

/-- The underlying homomorphism of the canonical equivalence is its canonical factorization. -/
@[simp]
theorem coe_mulEquivOfEq (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : K = L) :
    (d.mulEquivOfEq e h : d.X →* e.X) = d.homOfLe e h.le := by
  rfl

/-- The ambient commuting diagram determines the canonical equivalence uniquely. -/
theorem eq_mulEquivOfEq (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : K = L) (f : d.X ≃* e.X)
    (hf : ∀ x, e.toHom (f x) = d.toHom x) : f = d.mulEquivOfEq e h := by
  ext x
  apply e.injective
  rw [hf, toHom_mulEquivOfEq_apply]

/-- The inverse canonical equivalence is the canonical equivalence in the opposite direction. -/
@[simp]
theorem mulEquivOfEq_symm (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (h : K = L) :
    (d.mulEquivOfEq e h).symm = e.mulEquivOfEq d h.symm := by
  apply e.eq_mulEquivOfEq d h.symm
  exact d.toHom_mulEquivOfEq_symm_apply e h

/-- The canonical equivalence of a presentation with itself is the identity. -/
@[simp]
theorem mulEquivOfEq_refl (d : ImmersedLieSubgroupData I K) :
    d.mulEquivOfEq d rfl = MulEquiv.refl d.X := by
  symm
  apply d.eq_mulEquivOfEq d rfl
  intro x
  rfl

/-- Canonical equivalences compose according to equality of the underlying subgroups. -/
@[simp]
theorem mulEquivOfEq_trans (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (f : ImmersedLieSubgroupData I M)
    (hKL : K = L) (hLM : L = M) :
    (d.mulEquivOfEq e hKL).trans (e.mulEquivOfEq f hLM) = d.mulEquivOfEq f (hKL.trans hLM) := by
  apply d.eq_mulEquivOfEq f (hKL.trans hLM)
  intro x
  simp only [MulEquiv.trans_apply, toHom_mulEquivOfEq_apply]

/-- Successive canonical equivalences evaluate as the equivalence of the transitive equality. -/
@[simp]
theorem mulEquivOfEq_mulEquivOfEq (d : ImmersedLieSubgroupData I K)
    (e : ImmersedLieSubgroupData I L) (f : ImmersedLieSubgroupData I M)
    (hKL : K = L) (hLM : L = M) (x : d.X) :
    e.mulEquivOfEq f hLM (d.mulEquivOfEq e hKL x) =
      d.mulEquivOfEq f (hKL.trans hLM) x := by
  simpa only [MulEquiv.trans_apply] using
    DFunLike.congr_fun (d.mulEquivOfEq_trans e f hKL hLM) x

end ImmersedLieSubgroupData

/-- A subgroup is an immersed Lie subgroup when it is the image of an injective smooth immersion
from a connected Lie group carrying its own manifold topology. -/
def IsImmersedLieSubgroup (K : Subgroup G) : Prop :=
  Nonempty (ImmersedLieSubgroupData I K)

/-- Characterization of `TauCeti.Lie.IsImmersedLieSubgroup` by the data it forgets. -/
@[simp]
theorem isImmersedLieSubgroup_iff {K : Subgroup G} :
    IsImmersedLieSubgroup (I := I) K ↔ Nonempty (ImmersedLieSubgroupData I K) :=
  Iff.rfl

/-- Immersed-Lie-subgroup data exhibits its specified subgroup as an immersed Lie subgroup. -/
theorem ImmersedLieSubgroupData.isImmersedLieSubgroup {K : Subgroup G}
    (d : ImmersedLieSubgroupData I K) : IsImmersedLieSubgroup (I := I) K :=
  ⟨d⟩

/-- A connected Lie group is an immersed Lie subgroup of itself via the identity homomorphism. -/
@[simp 1100]
theorem isImmersedLieSubgroup_top [FiniteDimensional ℝ E] [ConnectedSpace G] :
    IsImmersedLieSubgroup (I := I) (⊤ : Subgroup G) := by
  exact ⟨{
    ambientIsManifold := IsManifold.mk' I ∞ G
    X := G
    E' := E
    H' := H
    I' := I
    isManifold := IsManifold.mk' I ∞ G
    toHom := MonoidHom.id G
    injective := Function.injective_id
    range_eq := MonoidHom.range_eq_top.mpr Function.surjective_id
    isImmersion := Manifold.IsImmersion.id
  }⟩

end TauCeti.Lie
