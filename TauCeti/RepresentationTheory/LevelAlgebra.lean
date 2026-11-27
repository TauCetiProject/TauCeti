/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.RepresentationTheory.WeightSpace
import Mathlib.Algebra.Module.Shrink
import TauCeti.LinearAlgebra.End.Restrict
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.OfMulAction.Coset.Lift
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# The level algebra of a representation

For a representation `ρ` of a monoid `G` on a module `V` over a commutative semiring `k` and a
submonoid `K` of `G`, the elements of the monoid algebra `k[G]` whose action `ρ.asAlgebraHom a`
preserves the `K`-fixed vectors `Representation.weightSpace (ρ.comp K.subtype) 1` form a
`k`-subalgebra `ρ.levelAlgebra K` of `k[G]`. Restricting the monoid-algebra action gives an
algebra homomorphism `ρ.levelAlgebraAction K` from `ρ.levelAlgebra K` to the endomorphism algebra
of the `K`-fixed vectors. When `G` is a group, `K` is a subgroup, `k` is a commutative ring, and
`V` is an additive commutative group, the `K`-fixed vectors agree with
`Representation.invariants (ρ.comp K.subtype)` (`Representation.weightSpace_one`).

The **universal level algebra** `K.universalLevelAlgebra k` is the intersection of
`ρ.levelAlgebra K` over all representations `ρ` of `G` over `k` on modules in `Type (max u v)`,
where `k : Type u` and `G : Type v`. Because any `K`-fixed vector generates a cyclic
`k[G]`-subrepresentation that is a quotient of `k[G]` and hence `Small.{max u v}`, every element
of `K.universalLevelAlgebra k` preserves the `K`-fixed vectors in every representation of `G` over
`k` in any universe (`Submonoid.universalLevelAlgebra_le`).

For a subgroup `K` of a group `G`, the universal property of the permutation representation on
left cosets `Representation.ofMulAction k G (G ⧸ K)` (`Representation.cosetLift`) shows that
`K.toSubmonoid.universalLevelAlgebra k` equals the level algebra of that single representation,
and an element `a ∈ k[G]` lies in it if and only if `a` maps the basis vector
`MonoidAlgebra.single ((1 : G) : G ⧸ K) 1` into the `K`-fixed vectors of `k[G ⧸ K]`.

## Main definitions

* `Representation.levelAlgebra ρ K`: the subalgebra of `MonoidAlgebra k G` preserving the
  `K`-fixed vectors of `ρ`.
* `Representation.levelAlgebraAction ρ K`: the restricted algebra homomorphism from
  `ρ.levelAlgebra K` to `Module.End k (Representation.weightSpace (ρ.comp K.subtype) 1)`.
* `Submonoid.universalLevelAlgebra K k`: the intersection of `ρ.levelAlgebra K` over all
  representations of `G` over `k`.

## Main results

* `Representation.mem_levelAlgebra`: membership characterization of `ρ.levelAlgebra K`.
* `Representation.coe_levelAlgebraAction_apply`: `ρ.levelAlgebraAction K` agrees with
  `ρ.asAlgebraHom` on `K`-fixed vectors.
* `Representation.Equiv.levelAlgebra_eq`: equivalent representations have the same level algebra.
* `Representation.comap_mapDomainAlgHom_levelAlgebra`: pullback of a level algebra along
  `MonoidAlgebra.mapDomainAlgHom`.
* `Submonoid.mem_universalLevelAlgebra`, `Submonoid.universalLevelAlgebra_le`: membership
  characterization and universe-polymorphic inclusion of `K.universalLevelAlgebra k`.
* `Submonoid.map_mapDomainAlgHom_universalLevelAlgebra_le`,
  `Submonoid.mapDomain_mem_universalLevelAlgebra`: pushforward of universal level algebras along
  a monoid homomorphism.
* `Subgroup.mem_universalLevelAlgebra_toSubmonoid_iff`,
  `Subgroup.universalLevelAlgebra_toSubmonoid_eq_levelAlgebra_ofMulAction`: characterization of
  the universal level algebra of a subgroup via `Representation.ofMulAction k G (G ⧸ K)`.

## References

* Adapted from `grh/src/Lib/Adelic/TraceFormula/LevelAlgebra.lean` in
  `lsernau/grh-lean` (https://github.com/lsernau/grh-lean, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.levelAlgebra`, `New.mem_levelAlgebra`, `New.levelAction` (here
  `Representation.levelAlgebraAction`), `New.universalLevelAlgebra`,
  `New.mem_universalLevelAlgebra`, and `New.universalLevelAlgebra_le`, generalized to monoids over
  commutative semirings and arbitrary representation universes (`New.asAlgebraHom_mapDomain` from
  the same file is placed in `TauCeti/RepresentationTheory/AsAlgebraHom.lean` as
  `Representation.asAlgebraHom_mapDomain`).
-/

public section

universe u v w

namespace Representation

section LevelAlgebra

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- The **level algebra** of a representation `ρ` at a submonoid `K`: the subalgebra of
`MonoidAlgebra k G` consisting of the elements whose action preserves the `K`-fixed vectors of
`ρ`. -/
noncomputable def levelAlgebra (ρ : Representation k G V) (K : Submonoid G) :
    Subalgebra k (MonoidAlgebra k G) where
  carrier := {a | ∀ v ∈ weightSpace (ρ.comp K.subtype) 1,
    ρ.asAlgebraHom a v ∈ weightSpace (ρ.comp K.subtype) 1}
  mul_mem' {a b} ha hb v hv := by
    rw [map_mul, mul_apply_eq_comp]
    exact ha _ (hb v hv)
  add_mem' {a b} ha hb v hv := by
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ (ha v hv) (hb v hv)
  algebraMap_mem' c v hv := by
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ c hv

/-- An element of `MonoidAlgebra k G` lies in `ρ.levelAlgebra K` if and only if its action
preserves the `K`-fixed vectors of `ρ`. -/
@[simp]
theorem mem_levelAlgebra {ρ : Representation k G V} {K : Submonoid G} {a : MonoidAlgebra k G} :
    a ∈ ρ.levelAlgebra K ↔
      ∀ v ∈ weightSpace (ρ.comp K.subtype) 1,
        ρ.asAlgebraHom a v ∈ weightSpace (ρ.comp K.subtype) 1 :=
  Iff.rfl

/-- At the trivial submonoid `⊥`, every vector is fixed, so the level algebra is the whole monoid
algebra. -/
@[simp]
theorem levelAlgebra_bot (ρ : Representation k G V) : ρ.levelAlgebra ⊥ = ⊤ := by
  ext a
  simp only [mem_levelAlgebra, Algebra.mem_top, iff_true]
  intro v _
  refine mem_weightSpace.2 fun g ↦ ?_
  have hg : (g : G) = 1 := Submonoid.mem_bot.1 g.property
  simp [hg]

/-- Every monomial supported on `K` lies in `ρ.levelAlgebra K`. -/
theorem single_mem_levelAlgebra_of_mem (ρ : Representation k G V) {K : Submonoid G} {g : G}
    (hg : g ∈ K) (c : k) : MonoidAlgebra.single g c ∈ ρ.levelAlgebra K := by
  refine mem_levelAlgebra.2 fun v hv ↦ ?_
  have hgv := mem_weightSpace.1 hv ⟨g, hg⟩
  simp only [MonoidHom.comp_apply, Submonoid.coe_subtype, MonoidHom.one_apply, one_smul] at hgv
  rw [asAlgebraHom_single, LinearMap.smul_apply, hgv]
  exact Submodule.smul_mem _ c hv

/-- An element of `MonoidAlgebra k G` whose action commutes with every element of `K` preserves
the `K`-fixed vectors of `ρ`. -/
theorem mem_levelAlgebra_of_forall_commute {ρ : Representation k G V} {K : Submonoid G}
    {a : MonoidAlgebra k G} (h : ∀ g ∈ K, Commute (ρ g) (ρ.asAlgebraHom a)) :
    a ∈ ρ.levelAlgebra K :=
  mem_levelAlgebra.2 fun _ hv ↦ map_mem_weightSpace_of_commute hv fun g ↦ h g g.property

/-- Equivalent representations have the same level algebra at every submonoid. -/
theorem Equiv.levelAlgebra_eq {W : Type*} [AddCommMonoid W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ) (K : Submonoid G) :
    ρ.levelAlgebra K = σ.levelAlgebra K := by
  have hws (v : V) : v ∈ weightSpace (ρ.comp K.subtype) 1 ↔
      e v ∈ weightSpace (σ.comp K.subtype) 1 := by
    simp only [mem_weightSpace, MonoidHom.comp_apply, Submonoid.coe_subtype, MonoidHom.one_apply,
      one_smul]
    refine forall_congr' fun g ↦ ?_
    have hint : e (ρ g v) = σ g (e v) := by
      rw [← e.coe_toIntertwiningMap]
      exact e.toIntertwiningMap.isIntertwining _ _ g v
    rw [← hint]
    exact (EquivLike.injective e).eq_iff.symm
  have halg (a : MonoidAlgebra k G) (v : V) : e (ρ.asAlgebraHom a v) = σ.asAlgebraHom a (e v) := by
    rw [← e.coe_toIntertwiningMap]
    exact e.toIntertwiningMap.apply_asAlgebraHom a v
  ext a
  simp only [mem_levelAlgebra]
  constructor
  · intro ha w hw
    obtain ⟨v, rfl⟩ := EquivLike.surjective e w
    rw [← halg, ← hws]
    exact ha v ((hws v).2 hw)
  · intro ha v hv
    rw [hws, halg]
    exact ha (e v) ((hws v).1 hv)

/-- Pulling back the level algebra of `ρ` at `K.map f` along `MonoidAlgebra.mapDomainAlgHom` gives
the level algebra of the restricted representation `ρ.comp f` at `K`. -/
theorem comap_mapDomainAlgHom_levelAlgebra {H : Type*} [Monoid H] (ρ : Representation k G V)
    (f : H →* G) (K : Submonoid H) :
    (ρ.levelAlgebra (K.map f)).comap (MonoidAlgebra.mapDomainAlgHom k k f) =
      levelAlgebra (ρ.comp f) K := by
  ext a
  simp only [Subalgebra.mem_comap, MonoidAlgebra.mapDomainAlgHom_apply, mem_levelAlgebra,
    asAlgebraHom_mapDomain, weightSpace_comp_map_subtype_one]

/-- The action of `ρ.levelAlgebra K` on the `K`-fixed vectors of `ρ`. -/
noncomputable def levelAlgebraAction (ρ : Representation k G V) (K : Submonoid G) :
    ρ.levelAlgebra K →ₐ[k] Module.End k (weightSpace (ρ.comp K.subtype) 1) :=
  (ρ.asAlgebraHom.comp (ρ.levelAlgebra K).val).restrictEnd _ fun a _ hv ↦
    mem_levelAlgebra.1 a.property _ hv

/-- Evaluating `ρ.levelAlgebraAction K` at an element of the level algebra and a `K`-fixed vector
recovers the ambient monoid-algebra action. -/
@[simp]
theorem coe_levelAlgebraAction_apply (ρ : Representation k G V) (K : Submonoid G)
    (a : ρ.levelAlgebra K) (v : weightSpace (ρ.comp K.subtype) 1) :
    (ρ.levelAlgebraAction K a v : V) = ρ.asAlgebraHom a v :=
  AlgHom.coe_restrictEnd_apply _ _ _ a v

end LevelAlgebra

end Representation

namespace Submonoid

section UniversalLevelAlgebra

/-- The **universal level algebra** of a submonoid `K` over a commutative semiring `k`: the
subalgebra of `MonoidAlgebra k G` consisting of the elements that preserve the `K`-fixed vectors
in every representation of `G` over `k` in `Type (max u v)`. By `universalLevelAlgebra_le`,
these elements preserve the `K`-fixed vectors in every representation of `G` over `k` in any
universe. -/
noncomputable def universalLevelAlgebra {G : Type v} [Monoid G] (K : Submonoid G)
    (k : Type u) [CommSemiring k] : Subalgebra k (MonoidAlgebra k G) :=
  ⨅ (V : Type (max u v)) (_ : AddCommMonoid V) (_ : Module k V) (ρ : Representation k G V),
    ρ.levelAlgebra K

/-- An element of `MonoidAlgebra k G` lies in `K.universalLevelAlgebra k` if and only if it lies
in `ρ.levelAlgebra K` for every representation `ρ` of `G` over `k` in `Type (max u v)`. -/
@[simp]
theorem mem_universalLevelAlgebra {k : Type u} {G : Type v} [CommSemiring k] [Monoid G]
    {K : Submonoid G} {a : MonoidAlgebra k G} :
    a ∈ K.universalLevelAlgebra k ↔
      ∀ (V : Type (max u v)) [AddCommMonoid V] [Module k V] (ρ : Representation k G V),
        a ∈ ρ.levelAlgebra K := by
  simp only [universalLevelAlgebra, Algebra.mem_iInf]

/-- For every representation `ρ` of `G` over `k` in any universe, the universal level algebra
`K.universalLevelAlgebra k` is contained in `ρ.levelAlgebra K`. -/
theorem universalLevelAlgebra_le {k : Type u} {G : Type v} {V : Type w}
    [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
    (K : Submonoid G) (ρ : Representation k G V) :
    K.universalLevelAlgebra k ≤ ρ.levelAlgebra K := by
  intro a ha
  refine Representation.mem_levelAlgebra.2 fun v hv ↦ ?_
  -- Pass to the cyclic `k[G]`-subrepresentation generated by `v`, which is `Small.{max u v}`.
  let S := Representation.cyclicSubrepresentation ρ v
  have hvS : v ∈ S.toSubmodule :=
    Subrepresentation.mem_toSubmodule.2 (Representation.mem_cyclicSubrepresentation_self v)
  have : Small.{max u v} S.toSubmodule := by
    rw [Representation.toSubmodule_cyclicSubrepresentation, ← Finsupp.range_linearCombination]
    exact small_range _
  let e : Shrink.{max u v} S.toSubmodule ≃ₗ[k] S.toSubmodule := Shrink.linearEquiv k S.toSubmodule
  let ρ' : Representation k G (Shrink.{max u v} S.toSubmodule) :=
    (e.symm.conjAlgEquiv k).toMonoidHom.comp S.toRepresentation
  have heq : ρ'.Equiv S.toRepresentation :=
    Representation.Equiv.mk e fun g ↦ by ext x; simp [ρ']
  have haS : a ∈ S.toRepresentation.levelAlgebra K := by
    rw [← heq.levelAlgebra_eq K]
    exact mem_universalLevelAlgebra.1 ha _ ρ'
  have hv' : (⟨v, hvS⟩ : S.toSubmodule) ∈ Representation.weightSpace
      (S.toRepresentation.comp K.subtype) 1 := by
    refine Representation.mem_weightSpace.2 fun g ↦ Subtype.ext ?_
    have hvg := Representation.mem_weightSpace.1 hv g
    simp only [MonoidHom.comp_apply, Submonoid.coe_subtype, MonoidHom.one_apply, one_smul]
      at hvg ⊢
    rw [Subrepresentation.coe_toRepresentation_apply]
    exact hvg
  have hact := Representation.mem_levelAlgebra.1 haS _ hv'
  refine Representation.mem_weightSpace.2 fun g ↦ ?_
  have hcoe := congrArg Subtype.val (Representation.mem_weightSpace.1 hact g)
  simp only [MonoidHom.comp_apply, Submonoid.coe_subtype, MonoidHom.one_apply, one_smul,
    Subrepresentation.coe_toRepresentation_apply,
    Subrepresentation.coe_toRepresentation_asAlgebraHom_apply] at hcoe ⊢
  exact hcoe

/-- At the trivial submonoid `⊥`, the universal level algebra is the whole monoid algebra. -/
@[simp]
theorem universalLevelAlgebra_bot (k : Type u) [CommSemiring k] {G : Type v} [Monoid G] :
    (⊥ : Submonoid G).universalLevelAlgebra k = ⊤ := by
  ext a
  simp

/-- Every monomial supported on `K` lies in `K.universalLevelAlgebra k`. -/
theorem single_mem_universalLevelAlgebra_of_mem {k : Type u} {G : Type v} [CommSemiring k]
    [Monoid G] {K : Submonoid G} {g : G} (hg : g ∈ K) (c : k) :
    MonoidAlgebra.single g c ∈ K.universalLevelAlgebra k :=
  mem_universalLevelAlgebra.2 fun _ _ _ ρ ↦ ρ.single_mem_levelAlgebra_of_mem hg c

/-- An element of `MonoidAlgebra k G` that commutes with `MonoidAlgebra.single g 1` for every
`g ∈ K` lies in `K.universalLevelAlgebra k`. -/
theorem mem_universalLevelAlgebra_of_forall_commute {k : Type u} {G : Type v} [CommSemiring k]
    [Monoid G] {K : Submonoid G} {a : MonoidAlgebra k G}
    (h : ∀ g ∈ K, Commute (MonoidAlgebra.single g (1 : k)) a) :
    a ∈ K.universalLevelAlgebra k :=
  mem_universalLevelAlgebra.2 fun _ _ _ ρ ↦
    Representation.mem_levelAlgebra_of_forall_commute fun g hg ↦ by
      simpa only [Representation.asAlgebraHom_single_one] using (h g hg).map ρ.asAlgebraHom

/-- Pushing `K.universalLevelAlgebra k` forward along `f : H →* G` lands in
`(K.map f).universalLevelAlgebra k`. -/
theorem map_mapDomainAlgHom_universalLevelAlgebra_le {k : Type u} {H : Type v} {G : Type w}
    [CommSemiring k] [Monoid H] [Monoid G] (K : Submonoid H) (f : H →* G) :
    (K.universalLevelAlgebra k).map (MonoidAlgebra.mapDomainAlgHom k k f) ≤
      (K.map f).universalLevelAlgebra k := by
  rw [Subalgebra.map_le]
  intro a ha
  refine (Subalgebra.mem_comap ..).2 (mem_universalLevelAlgebra.2 fun V _ _ ρ ↦ ?_)
  have hmem : a ∈ Representation.levelAlgebra (ρ.comp f) K :=
    K.universalLevelAlgebra_le (ρ.comp f) ha
  rw [← ρ.comap_mapDomainAlgHom_levelAlgebra f K] at hmem
  exact hmem

/-- Pushing an element of `K.universalLevelAlgebra k` forward along `f : H →* G` yields an
element of `(K.map f).universalLevelAlgebra k`. -/
theorem mapDomain_mem_universalLevelAlgebra {k : Type u} {H : Type v} {G : Type w}
    [CommSemiring k] [Monoid H] [Monoid G] {K : Submonoid H} {a : MonoidAlgebra k H}
    (ha : a ∈ K.universalLevelAlgebra k) (f : H →* G) :
    MonoidAlgebra.mapDomain f a ∈ (K.map f).universalLevelAlgebra k :=
  K.map_mapDomainAlgHom_universalLevelAlgebra_le f ⟨a, ha, rfl⟩

end UniversalLevelAlgebra

end Submonoid

namespace Subgroup

section UniversalLevelAlgebra

private theorem single_one_mem_weightSpace_ofMulAction {k : Type u} {G : Type v} [CommSemiring k]
    [Group G] (K : Subgroup G) :
    MonoidAlgebra.single ((1 : G) : G ⧸ K) (1 : k) ∈
      Representation.weightSpace ((Representation.ofMulAction k G (G ⧸ K)).comp K.subtype) 1 := by
  refine Representation.mem_weightSpace.2 fun u ↦ ?_
  have hu : (u : G) • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := by
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
    exact K.inv_mem u.property
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.one_apply, one_smul,
    Representation.ofMulAction_single, hu]

/-- An element `a ∈ MonoidAlgebra k G` lies in the universal level algebra of a subgroup `K` of a
group `G` if and only if its action on `Representation.ofMulAction k G (G ⧸ K)` sends the coset
basis vector `MonoidAlgebra.single ((1 : G) : G ⧸ K) 1` into the `K`-fixed vectors. -/
theorem mem_universalLevelAlgebra_toSubmonoid_iff {k : Type u} {G : Type v} [CommSemiring k]
    [Group G] {K : Subgroup G} {a : MonoidAlgebra k G} :
    a ∈ K.toSubmonoid.universalLevelAlgebra k ↔
      (Representation.ofMulAction k G (G ⧸ K)).asAlgebraHom a
        (MonoidAlgebra.single ((1 : G) : G ⧸ K) 1) ∈
          Representation.weightSpace
            ((Representation.ofMulAction k G (G ⧸ K)).comp K.subtype) 1 := by
  let ρ₀ := Representation.ofMulAction k G (G ⧸ K)
  let e₁ : MonoidAlgebra k (G ⧸ K) := MonoidAlgebra.single ((1 : G) : G ⧸ K) 1
  refine ⟨fun ha ↦ ?_, fun ha ↦ Submonoid.mem_universalLevelAlgebra.2 fun V _ _ ρ ↦ ?_⟩
  · have hmem := K.toSubmonoid.universalLevelAlgebra_le ρ₀ ha
    rw [Representation.mem_levelAlgebra, Representation.weightSpace_comp_toSubmonoid_subtype_one]
      at hmem
    exact hmem e₁ (single_one_mem_weightSpace_ofMulAction K)
  · rw [Representation.mem_levelAlgebra, Representation.weightSpace_comp_toSubmonoid_subtype_one]
    intro v hv
    have hK : K ≤ ρ.stabilizer v := fun u hu ↦ by
      have hvu := Representation.mem_weightSpace.1 hv ⟨u, hu⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.one_apply, one_smul] at hvu
      exact Representation.mem_stabilizer.2 hvu
    let φ := ρ.cosetLift K v hK
    have hφ : φ (ρ₀.asAlgebraHom a e₁) = ρ.asAlgebraHom a v := by
      rw [φ.apply_asAlgebraHom]
      simp only [φ, e₁, Representation.cosetLift_single, map_one, one_apply_eq_self, one_smul]
    refine Representation.mem_weightSpace.2 fun u ↦ ?_
    have hau := Representation.mem_weightSpace.1 ha u
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MonoidHom.one_apply, one_smul] at hau ⊢
    rw [← hφ, ← φ.isIntertwining]
    exact congrArg φ hau

/-- For a subgroup `K` of a group `G`, the universal level algebra of `K` equals the level algebra
of the single permutation representation `Representation.ofMulAction k G (G ⧸ K)`. -/
theorem universalLevelAlgebra_toSubmonoid_eq_levelAlgebra_ofMulAction {G : Type v} [Group G]
    (K : Subgroup G) (k : Type u) [CommSemiring k] :
    K.toSubmonoid.universalLevelAlgebra k =
      (Representation.ofMulAction k G (G ⧸ K)).levelAlgebra K.toSubmonoid := by
  refine le_antisymm (K.toSubmonoid.universalLevelAlgebra_le _) fun _ ha ↦ ?_
  rw [Representation.mem_levelAlgebra, Representation.weightSpace_comp_toSubmonoid_subtype_one]
    at ha
  exact mem_universalLevelAlgebra_toSubmonoid_iff.2
    (ha _ (single_one_mem_weightSpace_ofMulAction K))

end UniversalLevelAlgebra

end Subgroup
