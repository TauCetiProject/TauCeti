/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
import Mathlib.Algebra.Group.Action.Hom
import TauCeti.Algebra.Group.Hom.Lift
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.GroupTheory.GroupAction.Hom
import TauCeti.GroupTheory.GroupAction.Orbit.Basic

/-!
# Descent of homomorphisms and actions to the component group

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

Closed-subgroup descent lives in `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup.Action`.
No smoothness, reducedness, or characteristic hypothesis is required.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.descComponentGroupHom`: descend a homomorphism `G(k) →* M`
  vanishing on `G°(k)` to `π₀(G)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupActionHom` and
  `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupMulAction`: descend a `G(k)`-action trivial on
  `G°(k)` to `π₀(G)`.

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
  (rationalComponentMap H).liftOfSurjectiveToMonoid (rationalComponentMap_surjective H) φ
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
  MonoidHom.liftOfSurjectiveToMonoid_apply _ _ _ _ g

/-- Composing the descended homomorphism with the rational component map recovers `φ`. -/
@[simp]
theorem descComponentGroupHom_comp_rationalComponentMap {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).comp (rationalComponentMap H) = φ :=
  MonoidHom.liftOfSurjectiveToMonoid_comp _ _ _ _

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
  MonoidHom.liftOfSurjectiveToMonoid_unique _ _ _ _ ψ hψ

/-- The kernel of the descended homomorphism is the image of `ker φ` in the component group. -/
theorem ker_descComponentGroupHom {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).ker = φ.ker.map (rationalComponentMap H) :=
  (rationalComponentMap_surjective H).ker_eq_map_of_comp_eq
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
  rw [descComponentGroupHom, MonoidHom.injective_liftOfSurjectiveToMonoid_iff,
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
      descComponentGroupHom K (φ.comp (BialgHom.mapDomain (A := k) f.hom.hom)) (by
        have hsq :
            (mapComponentGroup f).comp (rationalComponentMap K) =
              (rationalComponentMap H).comp (BialgHom.mapDomain (A := k) f.hom.hom) :=
          MonoidHom.ext (mapComponentGroup_rationalComponentMap f)
        have hker := MonoidHom.ker_le_comap_ker_of_comp_eq hsq
        rw [rationalComponentMap_ker, rationalComponentMap_ker] at hker
        rw [← MonoidHom.comap_ker]
        exact hker.trans (Subgroup.comap_mono hφ)) := by
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
@[instance_reducible]
noncomputable def componentGroupMulAction (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x) :
    MulAction (ConnectedComponents (PrimeSpectrum H)) X :=
  MulAction.compHom X (componentGroupActionHom H X htriv)

/-- The scalar action of any component class under `componentGroupMulAction` is given by
`componentGroupActionHom`. -/
theorem componentGroupMulAction_smul (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x)
    (C : ConnectedComponents (PrimeSpectrum H)) (x : X) :
    letI := componentGroupMulAction H X htriv
    C • x = componentGroupActionHom H X htriv C x := by
  unfold componentGroupMulAction
  exact MulAction.compHom_smul_def _ _ _

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
    rationalComponentMap H g • x = g • x := by
  rw [componentGroupMulAction_smul, componentGroupActionHom_rationalComponentMap]

/-- The orbits of the descended `π₀(G)`-action coincide with the `G(k)`-orbits. -/
theorem orbit_componentGroupMulAction (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x) (x : X) :
    letI := componentGroupMulAction H X htriv
    MulAction.orbit (ConnectedComponents (PrimeSpectrum H)) x =
      MulAction.orbit (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) x := by
  let _ := componentGroupMulAction H X htriv
  exact (rationalComponentMap_surjective H).orbit_eq x fun g ↦
    componentGroupMulAction_rationalComponentMap_smul H X htriv g x

/-- The stabilizer in `π₀(G)` of a point is the image of its `G(k)`-stabilizer. -/
theorem stabilizer_componentGroupMulAction (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x) (x : X) :
    letI := componentGroupMulAction H X htriv
    MulAction.stabilizer (ConnectedComponents (PrimeSpectrum H)) x =
      (MulAction.stabilizer (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) x).map
        (rationalComponentMap H) := by
  let _ := componentGroupMulAction H X htriv
  exact (rationalComponentMap_surjective H).stabilizer_eq_map x fun g ↦
    componentGroupMulAction_rationalComponentMap_smul H X htriv g x

/-- The fixed points of the descended `π₀(G)`-action coincide with the `G(k)`-fixed points. -/
theorem fixedPoints_componentGroupMulAction (X : Type*)
    [MulAction (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X]
    (htriv : ∀ g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k),
      ∀ x : X, g • x = x) :
    letI := componentGroupMulAction H X htriv
    MulAction.fixedPoints (ConnectedComponents (PrimeSpectrum H)) X =
      MulAction.fixedPoints (HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) X := by
  let _ := componentGroupMulAction H X htriv
  exact (rationalComponentMap_surjective H).fixedPoints_eq
    (componentGroupMulAction_rationalComponentMap_smul H X htriv)

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

end TauCeti.FiniteTypeCommHopfAlgCat
