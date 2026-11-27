/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Action
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup
import Mathlib.Algebra.Group.Action.Hom
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.GroupTheory.GroupAction.CompHom

/-!
# Descent of homomorphisms and actions for closed-subgroup component groups

For any closed subgroup `N = V(I)` of a finite-type affine group `G = Spec H` over an
algebraically closed field `k`, `TauCeti.HopfIdeal.rationalComponentMap I : N(k) →* π₀(N)`
identifies `π₀(N)` with `N(k) ⧸ N°(k)` by transporting along the quotient-points isomorphism
`CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)` from the affine group
`quotient H I`.

By transporting along that isomorphism and applying the ambient descent API from
`TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Action` to `quotient H I`:

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

private theorem rationalComponentMap_eq_comp (I : HopfIdeal k H) :
    I.rationalComponentMap =
      (FiniteTypeCommHopfAlgCat.rationalComponentMap (quotient H I)).comp
        (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv.hom := by
  ext n
  exact (I.rationalComponentMap_apply n).trans
    (congrArg (FiniteTypeCommHopfAlgCat.rationalComponentMap (quotient H I))
      (CommHopfAlgCat.quotientPointsSubgroupIso_inv_apply H.obj I _ n).symm)

omit [IsAlgClosed k] in
private theorem quotientPointsSubgroupIso_inv_hom_apply (I : HopfIdeal k H)
    (q : HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k)) :
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv.hom
      ((CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom.hom q) = q := by
  rw [← MonoidHom.comp_apply, ← GrpCat.hom_comp, Iso.hom_inv_id, GrpCat.hom_id, MonoidHom.id_apply]

omit [IsAlgClosed k] in
private theorem quotientPointsSubgroupIso_hom_inv_apply (I : HopfIdeal k H)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom.hom
      ((CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv.hom g) = g := by
  rw [← MonoidHom.comp_apply, ← GrpCat.hom_comp, Iso.inv_hom_id, GrpCat.hom_id, MonoidHom.id_apply]

private theorem quotientPointsSubgroup_identityComponent_of_mem_ambient (I : HopfIdeal k H)
    {q : HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k)}
    (hq : q ∈ CommHopfAlgCat.quotientPointsSubgroup (quotient H I).obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := quotient H I))
        (CommAlgCat.of k k)) :
    ((CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom.hom q :
        HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) := by
  rw [← I.rationalComponentMap_eq_one_iff, rationalComponentMap_eq_comp H I, MonoidHom.comp_apply,
    quotientPointsSubgroupIso_inv_hom_apply, rationalComponentMap_eq_one_iff]
  exact hq

private theorem quotientPointsSubgroupIso_inv_hom_mem_identityComponent_iff (I : HopfIdeal k H)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv.hom g ∈
        CommHopfAlgCat.quotientPointsSubgroup (quotient H I).obj
          (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := quotient H I))
          (CommAlgCat.of k k) ↔
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) := by
  rw [← rationalComponentMap_eq_one_iff (quotient H I),
    ← I.rationalComponentMap_eq_one_iff, rationalComponentMap_eq_comp H I, MonoidHom.comp_apply]

private theorem descSubgroupComponentGroupHom_mem_ker (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    CommHopfAlgCat.quotientPointsSubgroup (quotient H I).obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := quotient H I))
        (CommAlgCat.of k k) ≤
      (φ.comp
        (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom.hom).ker :=
  fun _ hq ↦ hφ _ (quotientPointsSubgroup_identityComponent_of_mem_ambient H I hq)

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
    (descSubgroupComponentGroupHom_mem_ker H I φ hφ)

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
  rw [descSubgroupComponentGroupHom, rationalComponentMap_eq_comp H I, MonoidHom.comp_apply,
    descComponentGroupHom_rationalComponentMap, MonoidHom.comp_apply,
    quotientPointsSubgroupIso_hom_inv_apply]

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
  refine descComponentGroupHom_unique (quotient H I) _ _ ψ fun q ↦ ?_
  rw [MonoidHom.comp_apply, ← hψ]
  congr 1
  exact (I.rationalComponentMap_quotientPointsHom q).symm

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
  rw [descSubgroupComponentGroupHom, ker_descComponentGroupHom,
    rationalComponentMap_eq_comp H I, ← Subgroup.map_map]
  congr 1
  ext q
  simp only [Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro hq
    exact ⟨(CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom.hom q,
      hq, quotientPointsSubgroupIso_inv_hom_apply H I q⟩
  · rintro ⟨g, hg, rfl⟩
    rwa [quotientPointsSubgroupIso_hom_inv_apply]

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
  refine (injective_descComponentGroupHom_iff (quotient H I) _ _).trans ?_
  constructor
  · intro h
    ext g
    have hg := Subgroup.ext_iff.mp h
      ((CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv.hom g)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, quotientPointsSubgroupIso_hom_inv_apply,
      quotientPointsSubgroupIso_inv_hom_mem_identityComponent_iff] at hg
    exact hg
  · intro h
    ext q
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv).2 q
    have hg := Subgroup.ext_iff.mp h g
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, quotientPointsSubgroupIso_hom_inv_apply,
      quotientPointsSubgroupIso_inv_hom_mem_identityComponent_iff]
    exact hg

/-- The descended subgroup homomorphism has the same set-theoretic range as `φ`. -/
@[simp]
theorem range_coe_descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    Set.range (descSubgroupComponentGroupHom H I φ hφ) = Set.range φ := by
  refine (range_coe_descComponentGroupHom (quotient H I) _ _).trans ?_
  rw [MonoidHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom).2).range_comp φ

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
  refine (range_descComponentGroupHom (quotient H I) _ _).trans ?_
  exact MonoidHom.range_comp_of_surjective φ _
    (ConcreteCategory.bijective_of_isIso
      (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom).2

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
        (φ.comp (CommHopfAlgCat.mapDomainQuotientPointsSubgroup f.hom h (CommAlgCat.of k k)))
        (fun g hg ↦ by
          have hsq :
              (HopfIdeal.componentGroupMap I J f h).comp J.rationalComponentMap =
                I.rationalComponentMap.comp
                  (CommHopfAlgCat.mapDomainQuotientPointsSubgroup f.hom h (CommAlgCat.of k k)) :=
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
  MulAction.compHom X (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom.hom

omit [IsAlgClosed k] in
private theorem quotientMulAction_iso_inv_smul (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) (y : X) :
    letI := quotientMulAction H I X
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv.hom g • y =
      g • y := by
  unfold quotientMulAction
  rw [MulAction.compHom_smul_def, quotientPointsSubgroupIso_hom_inv_apply]

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
  componentGroupActionHom (quotient H I) X fun _ hq x ↦
    htriv _ (quotientPointsSubgroup_identityComponent_of_mem_ambient H I hq) x

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
  rw [subgroupComponentGroupActionHom, rationalComponentMap_eq_comp H I, MonoidHom.comp_apply,
    componentGroupActionHom_rationalComponentMap]
  exact quotientMulAction_iso_inv_smul H I X g x

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
  componentGroupMulAction (quotient H I) X fun _ hq x ↦
    htriv _ (quotientPointsSubgroup_identityComponent_of_mem_ambient H I hq) x

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
  unfold subgroupComponentGroupMulAction
  exact componentGroupMulAction_smul (quotient H I) X _ C x

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
  have horb := orbit_componentGroupMulAction (quotient H I) X
    (fun _ hq x ↦ htriv _ (quotientPointsSubgroup_identityComponent_of_mem_ambient H I hq) x) x
  have hiso :
      MulAction.orbit
          (HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k)) x =
        MulAction.orbit (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) x :=
    TauCeti.MulAction.orbit_eq_of_surjective
      (ConcreteCategory.bijective_of_isIso
        (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv).2
      (quotientMulAction_iso_inv_smul H I X) x
  exact horb.trans hiso

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
  have hstab := stabilizer_componentGroupMulAction (quotient H I) X
    (fun _ hq x ↦ htriv _ (quotientPointsSubgroup_identityComponent_of_mem_ambient H I hq) x) x
  have hiso :
      MulAction.stabilizer
          (HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k)) x =
        (MulAction.stabilizer
          (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) x).map
          (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv.hom :=
    TauCeti.MulAction.stabilizer_eq_map_of_surjective
      (ConcreteCategory.bijective_of_isIso
        (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv).2
      (quotientMulAction_iso_inv_smul H I X) x
  rw [hstab, hiso, Subgroup.map_map, rationalComponentMap_eq_comp H I]

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
  have hfix := fixedPoints_componentGroupMulAction (quotient H I) X
    (fun _ hq x ↦ htriv _ (quotientPointsSubgroup_identityComponent_of_mem_ambient H I hq) x)
  have hiso :
      MulAction.fixedPoints
          (HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k)) X =
        MulAction.fixedPoints
          (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X :=
    TauCeti.MulAction.fixedPoints_eq_of_surjective
      (ConcreteCategory.bijective_of_isIso
        (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv).2
      (quotientMulAction_iso_inv_smul H I X)
  exact hfix.trans hiso

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
  rw [subgroupComponentGroupActionHom, ker_componentGroupActionHom,
    rationalComponentMap_eq_comp H I, ← Subgroup.map_map]
  congr 1
  ext q
  simp only [Subgroup.mem_map, MonoidHom.mem_ker, Equiv.Perm.ext_iff,
    MulAction.toPermHom_apply, MulAction.toPerm_apply]
  constructor
  · intro hq
    exact ⟨(CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).hom.hom q,
      hq, quotientPointsSubgroupIso_inv_hom_apply H I q⟩
  · rintro ⟨g, hg, rfl⟩ x
    rw [quotientMulAction_iso_inv_smul]
    exact hg x

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
        CommHopfAlgCat.mapDomainQuotientPointsSubgroup f.hom h (CommAlgCat.of k k) g • α x)
    (C : J.ComponentGroup) (x : X) :
    α (subgroupComponentGroupActionHom K J X hX C x) =
      subgroupComponentGroupActionHom H I Y hY
        (HopfIdeal.componentGroupMap I J f h C) (α x) := by
  obtain ⟨g, rfl⟩ := J.rationalComponentMap_surjective C
  rw [subgroupComponentGroupActionHom_rationalComponentMap,
    HopfIdeal.componentGroupMap_rationalComponentMap,
    subgroupComponentGroupActionHom_rationalComponentMap, hα]

end ClosedSubgroup

end TauCeti.FiniteTypeCommHopfAlgCat
