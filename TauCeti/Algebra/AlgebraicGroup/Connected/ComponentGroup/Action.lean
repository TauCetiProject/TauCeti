/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.GroupTheory.GroupAction.CompHom
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# Component-group actions and closed-subgroup descent

Over an algebraically closed field `k`, the rational points `G(k)` of a finite-type affine group
`G = Spec H` surject onto its finite component group `π₀(G) = ConnectedComponents (PrimeSpectrum H)`
with kernel `G°(k)`. Consequently:

* Any homomorphism `φ : G(k) →* M` vanishing on `G°(k)` descends uniquely to a homomorphism
  `π₀(G) →* M` (`TauCeti.FiniteTypeCommHopfAlgCat.descComponentGroupHom`), whose kernel is the
  image of `ker φ` in `π₀(G)` and whose range agrees with that of `φ`.
* Any `G(k)`-action on a type `X` on which `G°(k)` acts trivially descends uniquely to a
  `π₀(G)`-action (`TauCeti.FiniteTypeCommHopfAlgCat.componentGroupActionHom`,
  `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupMulAction`) with the same orbits and fixed
  points, stabilizers transported by the rational component map, and kernel recording the
  effective component action.
* For any closed subgroup `N = V(I)` of `G` cut out by a Hopf ideal `I`, using
  `TauCeti.HopfIdeal.rationalComponentMap I : N(k) →* π₀(N)`, `N(k)`-homomorphisms and actions
  that are trivial on `N°(k)` descend directly to `π₀(N)`
  (`TauCeti.FiniteTypeCommHopfAlgCat.descSubgroupComponentGroupHom`,
  `TauCeti.FiniteTypeCommHopfAlgCat.subgroupComponentGroupActionHom`,
  `TauCeti.FiniteTypeCommHopfAlgCat.subgroupComponentGroupMulAction`), with the parallel
  injectivity, range, kernel, orbit, stabilizer, fixed-point, and naturality laws.

No smoothness, reducedness, or characteristic hypothesis is required.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.descComponentGroupHom`: descend a homomorphism `G(k) →* M`
  vanishing on `G°(k)` to `π₀(G)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupActionHom` and
  `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupMulAction`: descend a `G(k)`-action trivial on
  `G°(k)` to `π₀(G)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.descSubgroupComponentGroupHom`,
  `TauCeti.FiniteTypeCommHopfAlgCat.subgroupComponentGroupActionHom`, and
  `TauCeti.FiniteTypeCommHopfAlgCat.subgroupComponentGroupMulAction`: homomorphism and action
  descent directly from `N(k)` to `π₀(N)`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and §5.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.1, for component groups and their actions.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

section HomDescent

variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- Descend a homomorphism `G(k) →* M` that vanishes on `G°(k)` to the component group `π₀(G)`. -/
noncomputable def descComponentGroupHom {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    ConnectedComponents (PrimeSpectrum H) →* M :=
  QuotientGroup.descOfSurjective (rationalComponentMap H) (rationalComponentMap_surjective H) φ
    (by rw [rationalComponentMap_ker]; exact hφ)

/-- The descended homomorphism agrees with `φ` on rational points. -/
@[simp]
theorem descComponentGroupHom_rationalComponentMap {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    descComponentGroupHom H φ hφ (rationalComponentMap H g) = φ g :=
  QuotientGroup.descOfSurjective_apply _ _ _ _ g

/-- Composing the descended homomorphism with the rational component map recovers `φ`. -/
@[simp]
theorem descComponentGroupHom_comp_rationalComponentMap {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).comp (rationalComponentMap H) = φ :=
  QuotientGroup.descOfSurjective_comp _ _ _ _

/-- A homomorphism out of the component group is uniquely determined by its values on rational
points. -/
theorem descComponentGroupHom_unique {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker)
    (ψ : ConnectedComponents (PrimeSpectrum H) →* M)
    (hψ : ∀ g, ψ (rationalComponentMap H g) = φ g) :
    ψ = descComponentGroupHom H φ hφ :=
  QuotientGroup.descOfSurjective_unique _ _ _ _ ψ hψ

/-- The kernel of the descended homomorphism is the image of `ker φ` in the component group. -/
theorem ker_descComponentGroupHom {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).ker = φ.ker.map (rationalComponentMap H) :=
  MonoidHom.ker_eq_map_of_comp_eq (rationalComponentMap_surjective H)
    (descComponentGroupHom_comp_rationalComponentMap H φ hφ)

/-- The descended homomorphism is injective exactly when `ker φ` is contained in `G°(k)`. -/
theorem injective_descComponentGroupHom_iff {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    Function.Injective (descComponentGroupHom H φ hφ) ↔
      φ.ker = CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) := by
  rw [descComponentGroupHom, QuotientGroup.injective_descOfSurjective_iff,
    rationalComponentMap_ker]

/-- The descended homomorphism has the same set-theoretic range as `φ`. -/
@[simp]
theorem range_coe_descComponentGroupHom {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    Set.range (descComponentGroupHom H φ hφ) = Set.range φ := by
  rw [← (rationalComponentMap_surjective H).range_comp (descComponentGroupHom H φ hφ),
    ← MonoidHom.coe_comp, descComponentGroupHom_comp_rationalComponentMap]

/-- For a group target `M`, the descended homomorphism has the same subgroup range as `φ`. -/
@[simp]
theorem range_descComponentGroupHom {M : Type*} [Group M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).range = φ.range := by
  rw [← MonoidHom.range_comp_of_surjective (descComponentGroupHom H φ hφ)
      (rationalComponentMap H) (rationalComponentMap_surjective H),
    descComponentGroupHom_comp_rationalComponentMap]

/-- Descent to the component group is natural along affine group homomorphisms. -/
theorem descComponentGroupHom_comp_mapComponentGroup {K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).comp (mapComponentGroup f) =
      descComponentGroupHom K (φ.comp (BialgHom.mapDomain (A := k) f.hom.hom))
        (fun g hg ↦ by
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
          have h1 : rationalComponentMap H (BialgHom.mapDomain (A := k) f.hom.hom g) = 1 := by
            rw [← mapComponentGroup_rationalComponentMap f,
              (rationalComponentMap_eq_one_iff K g).mpr hg, map_one]
          exact hφ ((rationalComponentMap_eq_one_iff H _).mp h1)) := by
  apply descComponentGroupHom_unique
  intro g
  rw [MonoidHom.comp_apply, mapComponentGroup_rationalComponentMap,
    descComponentGroupHom_rationalComponentMap, MonoidHom.comp_apply]

end HomDescent

section ActionDescent

variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- Descend a `G(k)`-action on `X` whose restriction to `G°(k)` is trivial to a permutation
representation of `π₀(G)`. -/
noncomputable def componentGroupActionHom (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x) :
    ConnectedComponents (PrimeSpectrum H) →* Equiv.Perm X :=
  descComponentGroupHom H (MulAction.toPermHom _ X) fun g hg ↦ by
    rw [MonoidHom.mem_ker]
    ext x
    exact htriv g hg x

/-- The descended permutation action agrees with the rational-point action. -/
@[simp]
theorem componentGroupActionHom_rationalComponentMap (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) (x : X) :
    componentGroupActionHom H X htriv (rationalComponentMap H g) x = g • x := by
  rw [componentGroupActionHom, descComponentGroupHom_rationalComponentMap,
    MulAction.toPermHom_apply, MulAction.toPerm_apply]

/-- The descended `MulAction` of `π₀(G)` on `X`. -/
noncomputable abbrev componentGroupMulAction (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x) :
    MulAction (ConnectedComponents (PrimeSpectrum H)) X :=
  MulAction.compHom X (componentGroupActionHom H X htriv)

/-- The scalar action of a rational-point component under `componentGroupMulAction` agrees with
the rational-point action. -/
@[simp]
theorem componentGroupMulAction_rationalComponentMap_smul (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) (x : X) :
    letI := componentGroupMulAction H X htriv
    rationalComponentMap H g • x = g • x :=
  componentGroupActionHom_rationalComponentMap H X htriv g x

/-- The orbits of the descended `π₀(G)`-action coincide with the `G(k)`-orbits. -/
theorem orbit_componentGroupMulAction (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x) (x : X) :
    letI := componentGroupMulAction H X htriv
    MulAction.orbit (ConnectedComponents (PrimeSpectrum H)) x =
      MulAction.orbit (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) x :=
  TauCeti.MulAction.orbit_compHom_eq_of_surjective (rationalComponentMap_surjective H)
    (componentGroupActionHom H X htriv)
    (componentGroupActionHom_rationalComponentMap H X htriv) x

/-- The stabilizer in `π₀(G)` of a point is the image of its `G(k)`-stabilizer. -/
theorem stabilizer_componentGroupMulAction (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x) (x : X) :
    letI := componentGroupMulAction H X htriv
    MulAction.stabilizer (ConnectedComponents (PrimeSpectrum H)) x =
      (MulAction.stabilizer (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) x).map
        (rationalComponentMap H) :=
  TauCeti.MulAction.stabilizer_compHom_eq_of_surjective (rationalComponentMap_surjective H)
    (componentGroupActionHom H X htriv)
    (componentGroupActionHom_rationalComponentMap H X htriv) x

/-- The fixed points of the descended `π₀(G)`-action coincide with the `G(k)`-fixed points. -/
theorem fixedPoints_componentGroupMulAction (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x) :
    letI := componentGroupMulAction H X htriv
    MulAction.fixedPoints (ConnectedComponents (PrimeSpectrum H)) X =
      MulAction.fixedPoints (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X :=
  TauCeti.MulAction.fixedPoints_compHom_eq_of_surjective (rationalComponentMap_surjective H)
    (componentGroupActionHom H X htriv)
    (componentGroupActionHom_rationalComponentMap H X htriv)

/-- The kernel of the descended component action is the image of the kernel of the `G(k)`-action.
Equivalently, `π₀(G) / ker` is the effective finite action group. -/
theorem ker_componentGroupActionHom (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x) :
    (componentGroupActionHom H X htriv).ker =
      (MulAction.toPermHom
        (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X).ker.map
        (rationalComponentMap H) :=
  ker_descComponentGroupHom H (MulAction.toPermHom _ X) _

/-- Equivariant maps along affine group homomorphisms remain equivariant for the descended
component-group actions. -/
theorem map_componentGroupActionHom_apply {K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) {X Y : Type*}
    [MulAction (HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k)) X]
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) Y]
    (hX : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup K.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := K)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x)
    (hY : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ y : Y, g • y = y)
    (α : X → Y)
    (hα : ∀ (g : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k)) (x : X),
      α (g • x) = BialgHom.mapDomain (A := k) f.hom.hom g • α x)
    (C : ConnectedComponents (PrimeSpectrum K)) (x : X) :
    α (componentGroupActionHom K X hX C x) =
      componentGroupActionHom H Y hY (mapComponentGroup f C) (α x) := by
  obtain ⟨g, rfl⟩ := rationalComponentMap_surjective K C
  rw [componentGroupActionHom_rationalComponentMap, mapComponentGroup_rationalComponentMap,
    componentGroupActionHom_rationalComponentMap, hα]

end ActionDescent

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
  QuotientGroup.descOfSurjective I.rationalComponentMap I.rationalComponentMap_surjective φ
    (fun g hg ↦ hφ g (by rwa [I.ker_rationalComponentMap, Subgroup.mem_subgroupOf] at hg))

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
  QuotientGroup.descOfSurjective_apply _ _ _ _ g

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
  QuotientGroup.descOfSurjective_comp _ _ _ _

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
  QuotientGroup.descOfSurjective_unique _ _ _ _ ψ hψ

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
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :=
  (QuotientGroup.injective_descOfSurjective_iff I.rationalComponentMap
      I.rationalComponentMap_surjective φ _).trans
    (by rw [I.ker_rationalComponentMap])

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
        (φ.comp (((BialgHom.mapDomain (A := k) (toBialgHom f)).comp
          (CommHopfAlgCat.quotientPointsSubgroup K.obj J (CommAlgCat.of k k)).subtype).codRestrict
          (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k))
          fun g ↦ CommHopfAlgCat.mapDomain_mem_quotientPointsSubgroup_of_map_le
            f.hom h _ g.property))
        (fun g hg ↦ by
          have h1 : I.rationalComponentMap
              ⟨BialgHom.mapDomain (A := k) (toBialgHom f) g,
                CommHopfAlgCat.mapDomain_mem_quotientPointsSubgroup_of_map_le
                  f.hom h _ g.property⟩ = 1 := by
            rw [← HopfIdeal.componentGroupMap_rationalComponentMap I J f h,
              (J.rationalComponentMap_eq_one_iff g).mpr hg, map_one]
          exact hφ _ ((I.rationalComponentMap_eq_one_iff _).mp h1)) := by
  apply descSubgroupComponentGroupHom_unique
  intro g
  rw [MonoidHom.comp_apply, HopfIdeal.componentGroupMap_rationalComponentMap,
    descSubgroupComponentGroupHom_rationalComponentMap]
  rfl

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
noncomputable abbrev subgroupComponentGroupMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) :
    MulAction I.ComponentGroup X :=
  MulAction.compHom X (subgroupComponentGroupActionHom H I X htriv)

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
    I.rationalComponentMap g • x = g • x :=
  subgroupComponentGroupActionHom_rationalComponentMap H I X htriv g x

/-- The orbits of the descended `π₀(N)`-action coincide with the `N(k)`-orbits. -/
theorem orbit_subgroupComponentGroupMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) (x : X) :
    letI := subgroupComponentGroupMulAction H I X htriv
    MulAction.orbit I.ComponentGroup x =
      MulAction.orbit (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) x :=
  TauCeti.MulAction.orbit_compHom_eq_of_surjective I.rationalComponentMap_surjective
    (subgroupComponentGroupActionHom H I X htriv)
    (subgroupComponentGroupActionHom_rationalComponentMap H I X htriv) x

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
        I.rationalComponentMap :=
  TauCeti.MulAction.stabilizer_compHom_eq_of_surjective I.rationalComponentMap_surjective
    (subgroupComponentGroupActionHom H I X htriv)
    (subgroupComponentGroupActionHom_rationalComponentMap H I X htriv) x

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
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X :=
  TauCeti.MulAction.fixedPoints_compHom_eq_of_surjective I.rationalComponentMap_surjective
    (subgroupComponentGroupActionHom H I X htriv)
    (subgroupComponentGroupActionHom_rationalComponentMap H I X htriv)

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
        (⟨BialgHom.mapDomain (A := k) (toBialgHom f) g,
          CommHopfAlgCat.mapDomain_mem_quotientPointsSubgroup_of_map_le
            f.hom h _ g.property⟩ :
          CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) • α x)
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
