/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup.Basic
import Mathlib.Algebra.Group.Action.Hom
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Action
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.GroupTheory.GroupAction.Hom
import TauCeti.GroupTheory.GroupAction.Orbit.Basic

/-!
# Descent of homomorphisms and actions for closed-subgroup component groups

For any closed subgroup `N = V(I)` of a finite-type affine group `G = Spec H` over an
algebraically closed field `k`, `CommHopfAlgCat.quotientPointsSubgroupIso` identifies `N(k)` with
the rational points `(H ⧸ I)(k)` of the quotient affine group `Spec (H ⧸ I)`, transporting `N°(k)`
to `(H ⧸ I)°(k)`. Transporting the ambient descent API in
`TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Action` through this isomorphism yields:

* Any homomorphism `φ : N(k) →* M` vanishing on `N°(k)` descends uniquely to `π₀(N)`
  (`TauCeti.FiniteTypeCommHopfAlgCat.descSubgroupComponentGroupHom`), with the kernel,
  injectivity, range, and naturality laws.
* Any `N(k)`-action on `X` whose restriction to `N°(k)` is trivial descends uniquely to a
  `π₀(N)`-action (`TauCeti.FiniteTypeCommHopfAlgCat.subgroupComponentGroupActionHom`,
  `TauCeti.FiniteTypeCommHopfAlgCat.subgroupComponentGroupMulAction`) with the same orbits and
  fixed points, transported stabilizers, kernel formula, and equivariant naturality.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and §5.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.1.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

section ClosedSubgroup

variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)

private lemma ker_quotientPointsSubgroupIso_hom_le (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    CommHopfAlgCat.quotientPointsSubgroup (quotient H I).obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := quotient H I))
        (CommAlgCat.of k k) ≤
      (φ.comp (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I
        (CommAlgCat.of k k)).hom.hom).ker := by
  intro p hp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply]
  exact hφ _ ((I.quotientPointsHom_mem_quotientPointsSubgroup_identityComponent_iff
    (CommAlgCat.of k k) p).mpr hp)

/-- Descend a homomorphism `N(k) →* M` vanishing on `N°(k)` to `π₀(N)`. -/
noncomputable def descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    I.ComponentGroup →* M :=
  descComponentGroupHom (quotient H I)
    (φ.comp (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom.hom)
    (ker_quotientPointsSubgroupIso_hom_le H I φ hφ)

/-- The descended subgroup homomorphism agrees with `φ` on `N(k)`. -/
@[simp]
theorem descSubgroupComponentGroupHom_rationalComponentMap (I : HopfIdeal k H)
    {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    descSubgroupComponentGroupHom H I φ hφ (I.rationalComponentMap g) = φ g := by
  rw [descSubgroupComponentGroupHom, I.rationalComponentMap_def, MonoidHom.comp_apply,
    descComponentGroupHom_rationalComponentMap, MonoidHom.comp_apply]
  congr 1
  rw [← MonoidHom.comp_apply, ← GrpCat.hom_comp, Iso.inv_hom_id, GrpCat.hom_id, MonoidHom.id_apply]

/-- Composing the descended subgroup homomorphism with `I.rationalComponentMap` recovers `φ`. -/
@[simp]
theorem descSubgroupComponentGroupHom_comp_rationalComponentMap (I : HopfIdeal k H)
    {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    (descSubgroupComponentGroupHom H I φ hφ).comp I.rationalComponentMap = φ :=
  MonoidHom.ext (descSubgroupComponentGroupHom_rationalComponentMap H I φ hφ)

/-- The descended subgroup homomorphism is uniquely determined on `N(k)`. -/
theorem descSubgroupComponentGroupHom_unique (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1)
    (ψ : I.ComponentGroup →* M)
    (hψ : ∀ g, ψ (I.rationalComponentMap g) = φ g) :
    ψ = descSubgroupComponentGroupHom H I φ hφ := by
  refine descComponentGroupHom_unique (quotient H I) _ _ ψ fun p ↦ ?_
  rw [MonoidHom.comp_apply, ← hψ ((CommHopfAlgCat.quotientPointsSubgroupIso H.obj I
    (CommAlgCat.of k k)).hom.hom p), I.rationalComponentMap_def, MonoidHom.comp_apply]
  congr 2
  rw [← MonoidHom.comp_apply, ← GrpCat.hom_comp, Iso.hom_inv_id, GrpCat.hom_id, MonoidHom.id_apply]

/-- The kernel of the descended subgroup homomorphism is the image of `ker φ` under
`HopfIdeal.rationalComponentMap`. -/
theorem ker_descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    (descSubgroupComponentGroupHom H I φ hφ).ker =
      φ.ker.map I.rationalComponentMap := by
  let hiso := CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)
  rw [descSubgroupComponentGroupHom, ker_descComponentGroupHom, ← MonoidHom.comap_ker,
    ← Subgroup.map_comap_eq_self_of_surjective
      (ConcreteCategory.bijective_of_isIso hiso.inv).2 (φ.ker.comap hiso.hom.hom),
    Subgroup.comap_comap, ← GrpCat.hom_comp, Iso.inv_hom_id, GrpCat.hom_id, Subgroup.comap_id,
    Subgroup.map_map, ← I.rationalComponentMap_def]

/-- The descended subgroup homomorphism is injective exactly when `ker φ` consists of rational
points of `N°`. -/
theorem injective_descSubgroupComponentGroupHom_iff (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    Function.Injective (descSubgroupComponentGroupHom H I φ hφ) ↔
      φ.ker = (CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent
          (CommAlgCat.of k k)).subgroupOf
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) := by
  rw [descSubgroupComponentGroupHom, injective_descComponentGroupHom_iff, ← MonoidHom.comap_ker]
  let hiso := CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)
  constructor
  · intro h
    ext g
    have hg := SetLike.ext_iff.mp h (hiso.inv.hom g)
    rw [Subgroup.mem_comap, ← MonoidHom.comp_apply, ← GrpCat.hom_comp, Iso.inv_hom_id,
      GrpCat.hom_id, MonoidHom.id_apply] at hg
    refine hg.trans ?_
    rw [Subgroup.mem_subgroupOf,
      ← I.quotientPointsHom_mem_quotientPointsSubgroup_identityComponent_iff (CommAlgCat.of k k)]
    change (CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k))
        ((hiso.inv g : HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k))) ∈
      _ ↔ _
    rw [CommHopfAlgCat.quotientPointsSubgroupIso_inv_apply,
      CommHopfAlgCat.quotientPointsHom_liftQuotientPoint]
  · intro h
    ext p
    have hp := SetLike.ext_iff.mp h (hiso.hom.hom p)
    rw [Subgroup.mem_comap, hp, Subgroup.mem_subgroupOf,
      ← I.quotientPointsHom_mem_quotientPointsSubgroup_identityComponent_iff (CommAlgCat.of k k)]
    change (hiso.hom p : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈ _ ↔ _
    rw [CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply]

/-- The descended subgroup homomorphism has the same set-theoretic range as `φ`. -/
@[simp]
theorem range_coe_descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    Set.range (descSubgroupComponentGroupHom H I φ hφ) = Set.range φ := by
  rw [descSubgroupComponentGroupHom, range_coe_descComponentGroupHom, MonoidHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom).2.range_comp φ

/-- For a group target `M`, the descended subgroup homomorphism has the same subgroup range as
`φ`. -/
@[simp]
theorem range_descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Group M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    (descSubgroupComponentGroupHom H I φ hφ).range = φ.range := by
  rw [descSubgroupComponentGroupHom, range_descComponentGroupHom,
    MonoidHom.range_comp_of_surjective _ _
      (ConcreteCategory.bijective_of_isIso
        (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom).2]

/-- Descent to a closed subgroup's component group is natural along maps of closed subgroups. -/
theorem descSubgroupComponentGroupHom_comp_componentGroupMap
    {K : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H} {J : HopfIdeal k K}
    (f : H ⟶ K) (h : I.map (toBialgHom f) ≤ J) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    (descSubgroupComponentGroupHom H I φ hφ).comp (HopfIdeal.componentGroupMap I J f h) =
      descSubgroupComponentGroupHom K J
        (φ.comp (f.hom.mapDomainQuotientPointsSubgroup h (CommAlgCat.of k k)))
        (fun g hg ↦ by
          have hsq :
              (HopfIdeal.componentGroupMap I J f h).comp J.rationalComponentMap =
                I.rationalComponentMap.comp
                  (f.hom.mapDomainQuotientPointsSubgroup h (CommAlgCat.of k k)) :=
            MonoidHom.ext (HopfIdeal.componentGroupMap_rationalComponentMap I J f h)
          have hker := MonoidHom.ker_le_comap_ker_of_comp_eq hsq
          rw [J.ker_rationalComponentMap, I.ker_rationalComponentMap] at hker
          exact hφ _ (Subgroup.mem_subgroupOf.mp (hker (Subgroup.mem_subgroupOf.mpr hg)))) := by
  refine descSubgroupComponentGroupHom_unique K J _ _ _ fun g ↦ ?_
  rw [MonoidHom.comp_apply, HopfIdeal.componentGroupMap_rationalComponentMap,
    descSubgroupComponentGroupHom_rationalComponentMap, MonoidHom.comp_apply]

@[instance_reducible]
private noncomputable def quotientMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X] :
    MulAction (HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k)) X :=
  MulAction.compHom X
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom.hom

private lemma quotientMulAction_triv (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) :
    letI := quotientMulAction H I X
    ∀ p ∈ CommHopfAlgCat.quotientPointsSubgroup (quotient H I).obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := quotient H I)) (CommAlgCat.of k k),
      ∀ x : X, p • x = x := by
  let _ := quotientMulAction H I X
  intro p hp x
  change ((CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom p) • x = x
  refine htriv _ ?_ x
  rw [CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply]
  exact (I.quotientPointsHom_mem_quotientPointsSubgroup_identityComponent_iff
    (CommAlgCat.of k k) p).mpr hp

/-- Descend an action of the closed subgroup `N(k) ≤ G(k)` on `X` whose restriction to `N°(k)` is
trivial to a permutation action of `π₀(N)`. -/
noncomputable def subgroupComponentGroupActionHom (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) :
    I.ComponentGroup →* Equiv.Perm X :=
  letI := quotientMulAction H I X
  componentGroupActionHom (quotient H I) X (quotientMulAction_triv H I X htriv)

/-- The descended closed-subgroup component action agrees with the `N(k)`-action. -/
@[simp]
theorem subgroupComponentGroupActionHom_rationalComponentMap (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) (x : X) :
    subgroupComponentGroupActionHom H I X htriv (I.rationalComponentMap g) x = g • x := by
  let _ := quotientMulAction H I X
  rw [subgroupComponentGroupActionHom, I.rationalComponentMap_def, MonoidHom.comp_apply,
    componentGroupActionHom_rationalComponentMap]
  change ((CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom.hom
    ((CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv.hom g)) • x =
      g • x
  rw [← MonoidHom.comp_apply, ← GrpCat.hom_comp, Iso.inv_hom_id, GrpCat.hom_id, MonoidHom.id_apply]

/-- The descended `MulAction` of `π₀(N)` on `X` from an `N(k)`-action trivial on `N°(k)`. -/
@[instance_reducible]
noncomputable def subgroupComponentGroupMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) :
    MulAction I.ComponentGroup X :=
  letI := quotientMulAction H I X
  componentGroupMulAction (quotient H I) X (quotientMulAction_triv H I X htriv)

/-- The scalar action of any component class under `subgroupComponentGroupMulAction` is given by
`subgroupComponentGroupActionHom`. -/
theorem subgroupComponentGroupMulAction_smul (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x)
    (C : I.ComponentGroup) (x : X) :
    letI := subgroupComponentGroupMulAction H I X htriv
    C • x = subgroupComponentGroupActionHom H I X htriv C x := by
  let _ := quotientMulAction H I X
  exact componentGroupMulAction_smul (quotient H I) X (quotientMulAction_triv H I X htriv) C x

/-- The scalar action of a rational-point component under `subgroupComponentGroupMulAction` agrees
with the `N(k)`-action. -/
@[simp]
theorem subgroupComponentGroupMulAction_rationalComponentMap_smul (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) (x : X) :
    letI := subgroupComponentGroupMulAction H I X htriv
    I.rationalComponentMap g • x = g • x := by
  rw [subgroupComponentGroupMulAction_smul, subgroupComponentGroupActionHom_rationalComponentMap]

/-- The orbits of the descended `π₀(N)`-action coincide with the `N(k)`-orbits. -/
theorem orbit_subgroupComponentGroupMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) (x : X) :
    letI := subgroupComponentGroupMulAction H I X htriv
    MulAction.orbit I.ComponentGroup x =
      MulAction.orbit (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) x := by
  let _ := quotientMulAction H I X
  let _ := subgroupComponentGroupMulAction H I X htriv
  refine (orbit_componentGroupMulAction (quotient H I) X
    (quotientMulAction_triv H I X htriv) x).trans ?_
  exact ((ConcreteCategory.bijective_of_isIso
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom).2.orbit_eq
      x fun _ ↦ rfl).symm

/-- The stabilizer in `π₀(N)` of a point is the image of its `N(k)`-stabilizer. -/
theorem stabilizer_subgroupComponentGroupMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) (x : X) :
    letI := subgroupComponentGroupMulAction H I X htriv
    MulAction.stabilizer I.ComponentGroup x =
      (MulAction.stabilizer
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) x).map
        I.rationalComponentMap := by
  let _ := quotientMulAction H I X
  let _ := subgroupComponentGroupMulAction H I X htriv
  let hiso := CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)
  rw [stabilizer_componentGroupMulAction (quotient H I) X
    (quotientMulAction_triv H I X htriv) x,
    (ConcreteCategory.bijective_of_isIso hiso.inv).2.stabilizer_eq_map x (fun g ↦ by
      change (hiso.hom.hom (hiso.inv.hom g)) • x = g • x
      rw [← MonoidHom.comp_apply, ← GrpCat.hom_comp, Iso.inv_hom_id, GrpCat.hom_id,
        MonoidHom.id_apply]),
    Subgroup.map_map, ← I.rationalComponentMap_def]

/-- The fixed points of the descended `π₀(N)`-action coincide with the `N(k)`-fixed points. -/
theorem fixedPoints_subgroupComponentGroupMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) :
    letI := subgroupComponentGroupMulAction H I X htriv
    MulAction.fixedPoints I.ComponentGroup X =
      MulAction.fixedPoints
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X := by
  let _ := quotientMulAction H I X
  let _ := subgroupComponentGroupMulAction H I X htriv
  refine (fixedPoints_componentGroupMulAction (quotient H I) X
    (quotientMulAction_triv H I X htriv)).trans ?_
  exact ((ConcreteCategory.bijective_of_isIso
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom).2.fixedPoints_eq
      fun _ _ ↦ rfl).symm

/-- The kernel of the descended closed-subgroup component action is the image of the kernel of
the `N(k)`-action. -/
theorem ker_subgroupComponentGroupActionHom (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) :
    (subgroupComponentGroupActionHom H I X htriv).ker =
      (MulAction.toPermHom
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X).ker.map
        I.rationalComponentMap := by
  let _ := quotientMulAction H I X
  let hiso := CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)
  rw [subgroupComponentGroupActionHom,
    ker_componentGroupActionHom (quotient H I) X (quotientMulAction_triv H I X htriv)]
  have hperm :
      MulAction.toPermHom
          (HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k)) X =
        (MulAction.toPermHom
          (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X).comp
          hiso.hom.hom := by
    ext p x
    rfl
  rw [hperm, ← MonoidHom.comap_ker,
    ← Subgroup.map_comap_eq_self_of_surjective
      (ConcreteCategory.bijective_of_isIso hiso.inv).2
      ((MulAction.toPermHom _ X).ker.comap hiso.hom.hom),
    Subgroup.comap_comap, ← GrpCat.hom_comp, Iso.inv_hom_id, GrpCat.hom_id, Subgroup.comap_id,
    Subgroup.map_map, ← I.rationalComponentMap_def]

/-- Equivariant maps along maps of closed subgroups remain equivariant for the descended
component-group actions. -/
theorem map_subgroupComponentGroupActionHom_apply
    {K : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H} {J : HopfIdeal k K}
    (f : H ⟶ K) (h : I.map (toBialgHom f) ≤ J) {X Y : Type*}
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup K.obj J (CommAlgCat.of k k)) X]
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) Y]
    (hX : ∀ g : CommHopfAlgCat.quotientPointsSubgroup K.obj J (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup K.obj J.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x)
    (hY : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ y : Y, g • y = y)
    (α : X → Y)
    (hα : ∀ (g : CommHopfAlgCat.quotientPointsSubgroup K.obj J (CommAlgCat.of k k)) (x : X),
      α (g • x) =
        f.hom.mapDomainQuotientPointsSubgroup h (CommAlgCat.of k k) g • α x)
    (C : J.ComponentGroup) (x : X) :
    α (subgroupComponentGroupActionHom K J X hX C x) =
      subgroupComponentGroupActionHom H I Y hY
        (HopfIdeal.componentGroupMap I J f h C) (α x) := by
  let _ := quotientMulAction K J X
  let _ := quotientMulAction H I Y
  rw [subgroupComponentGroupActionHom, subgroupComponentGroupActionHom,
    HopfIdeal.componentGroupMap_eq_mapComponentGroup]
  refine map_componentGroupActionHom_apply (quotient H I) (quotientMap I J f h)
    (quotientMulAction_triv K J X hX) (quotientMulAction_triv H I Y hY) α (fun p x ↦ ?_) C x
  change α ((CommHopfAlgCat.quotientPointsSubgroupIso K.obj J (CommAlgCat.of k k)).hom p • x) =
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom
      (BialgHom.mapDomain (A := k) (toBialgHom (quotientMap I J f h)) p) • α x
  rw [hα]
  congr 1
  apply Subtype.ext
  rw [CommHopfAlgCat.Hom.coe_mapDomainQuotientPointsSubgroup_apply,
    CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply,
    CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply]
  apply WithConv.ofConv_injective
  ext a
  rw [BialgHom.mapDomain_apply_apply, CommHopfAlgCat.quotientPointsHom_apply_apply,
    CommHopfAlgCat.quotientPointsHom_apply_apply, BialgHom.mapDomain_apply_apply,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mkₐ_eq_mk, quotientMap_mk]

end ClosedSubgroup

end TauCeti.FiniteTypeCommHopfAlgCat
