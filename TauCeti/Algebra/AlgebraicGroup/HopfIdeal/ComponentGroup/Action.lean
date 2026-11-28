/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup.Basic
import Mathlib.Algebra.Group.Action.Hom
import TauCeti.Algebra.Group.Hom.Lift
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.GroupTheory.GroupAction.CompHom

/-!
# Descent of homomorphisms and actions for closed-subgroup component groups

For any closed subgroup `N = V(I)` of a finite-type affine group `G = Spec H` over an
algebraically closed field `k`, `TauCeti.HopfIdeal.rationalComponentMap I : N(k) →* π₀(N)`
is surjective with kernel `N°(k)` (`TauCeti.HopfIdeal.rationalComponentMap_surjective`,
`TauCeti.HopfIdeal.ker_rationalComponentMap`). Lifting directly along `I.rationalComponentMap`
with `MonoidHom.liftOfSurjectiveToMonoid` yields:

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

/-- Descend a homomorphism `N(k) →* M` vanishing on `N°(k)` to `π₀(N)`. -/
noncomputable def descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    I.ComponentGroup →* M :=
  I.rationalComponentMap.liftOfSurjectiveToMonoid I.rationalComponentMap_surjective φ
    (by rw [I.ker_rationalComponentMap]; exact hφ)

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
    descSubgroupComponentGroupHom H I φ hφ (I.rationalComponentMap g) = φ g :=
  MonoidHom.liftOfSurjectiveToMonoid_apply _ _ _ _ g

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
  MonoidHom.liftOfSurjectiveToMonoid_comp _ _ _ _

/-- The descended subgroup homomorphism is uniquely determined on `N(k)`. -/
theorem descSubgroupComponentGroupHom_unique (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1)
    (ψ : I.ComponentGroup →* M)
    (hψ : ∀ g, ψ (I.rationalComponentMap g) = φ g) :
    ψ = descSubgroupComponentGroupHom H I φ hφ :=
  MonoidHom.liftOfSurjectiveToMonoid_unique _ _ _ _ ψ hψ

/-- The kernel of the descended subgroup homomorphism is the image of `ker φ` under
`HopfIdeal.rationalComponentMap`. -/
theorem ker_descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    (descSubgroupComponentGroupHom H I φ hφ).ker =
      φ.ker.map I.rationalComponentMap :=
  MonoidHom.ker_eq_map_of_comp_eq I.rationalComponentMap_surjective
    (descSubgroupComponentGroupHom_comp_rationalComponentMap H I φ hφ)

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
  rw [descSubgroupComponentGroupHom, MonoidHom.injective_liftOfSurjectiveToMonoid_iff,
    I.ker_rationalComponentMap]

/-- The descended subgroup homomorphism has the same set-theoretic range as `φ`. -/
@[simp]
theorem range_coe_descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    Set.range (descSubgroupComponentGroupHom H I φ hφ) = Set.range φ := by
  rw [← I.rationalComponentMap_surjective.range_comp (descSubgroupComponentGroupHom H I φ hφ),
    ← MonoidHom.coe_comp, descSubgroupComponentGroupHom_comp_rationalComponentMap]

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
  rw [← MonoidHom.range_comp_of_surjective (descSubgroupComponentGroupHom H I φ hφ)
      I.rationalComponentMap I.rationalComponentMap_surjective,
    descSubgroupComponentGroupHom_comp_rationalComponentMap]

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

/-- Descend an action of the closed subgroup `N(k) ≤ G(k)` on `X` whose restriction to `N°(k)` is
trivial to a permutation action of `π₀(N)`. -/
noncomputable def subgroupComponentGroupActionHom (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) :
    I.ComponentGroup →* Equiv.Perm X :=
  descSubgroupComponentGroupHom H I (MulAction.toPermHom _ X) fun g hg ↦ by
    ext x
    exact htriv g hg x

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
  rw [subgroupComponentGroupActionHom, descSubgroupComponentGroupHom_rationalComponentMap,
    MulAction.toPermHom_apply, MulAction.toPerm_apply]

/-- The descended `MulAction` of `π₀(N)` on `X` from an `N(k)`-action trivial on `N°(k)`. -/
@[instance_reducible]
noncomputable def subgroupComponentGroupMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) :
    MulAction I.ComponentGroup X :=
  MulAction.compHom X (subgroupComponentGroupActionHom H I X htriv)

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
  unfold subgroupComponentGroupMulAction
  exact MulAction.compHom_smul_def _ _ _

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
  let _ := subgroupComponentGroupMulAction H I X htriv
  exact TauCeti.MulAction.orbit_eq_of_surjective I.rationalComponentMap_surjective x fun g ↦
    subgroupComponentGroupMulAction_rationalComponentMap_smul H I X htriv g x

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
  let _ := subgroupComponentGroupMulAction H I X htriv
  exact TauCeti.MulAction.stabilizer_eq_map_of_surjective I.rationalComponentMap_surjective x
    fun g ↦ subgroupComponentGroupMulAction_rationalComponentMap_smul H I X htriv g x

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
  let _ := subgroupComponentGroupMulAction H I X htriv
  exact TauCeti.MulAction.fixedPoints_eq_of_surjective I.rationalComponentMap_surjective
    (subgroupComponentGroupMulAction_rationalComponentMap_smul H I X htriv)

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
        I.rationalComponentMap :=
  ker_descSubgroupComponentGroupHom H I (MulAction.toPermHom _ X) _

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
  obtain ⟨g, rfl⟩ := J.rationalComponentMap_surjective C
  rw [subgroupComponentGroupActionHom_rationalComponentMap,
    HopfIdeal.componentGroupMap_rationalComponentMap,
    subgroupComponentGroupActionHom_rationalComponentMap, hα]

end ClosedSubgroup

end TauCeti.FiniteTypeCommHopfAlgCat
