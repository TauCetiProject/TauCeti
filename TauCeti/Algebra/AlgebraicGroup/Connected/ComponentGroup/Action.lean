/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup

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
  `TauCeti.FiniteTypeCommHopfAlgCat.subgroupComponentGroupMulAction`).

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

section SurjectiveDescent

-- `MonoidHom.liftOfSurjective` requires `[Group M]`; `QuotientGroup.lift` supports `[Monoid M]`.
private noncomputable def descOfSurjective {P Q M : Type*} [Group P] [Group Q] [Monoid M]
    (p : P →* Q) (hp : Function.Surjective p) (φ : P →* M) (hφ : p.ker ≤ φ.ker) :
    Q →* M :=
  (QuotientGroup.lift p.ker φ hφ).comp (QuotientGroup.liftEquiv p.ker hp rfl).symm.toMonoidHom

private theorem descOfSurjective_apply {P Q M : Type*} [Group P] [Group Q] [Monoid M]
    (p : P →* Q) (hp : Function.Surjective p) (φ : P →* M) (hφ : p.ker ≤ φ.ker) (g : P) :
    descOfSurjective p hp φ hφ (p g) = φ g := by
  have hmk : (QuotientGroup.liftEquiv p.ker hp rfl).symm (p g) = (g : P ⧸ p.ker) :=
    (QuotientGroup.liftEquiv p.ker hp rfl).symm_apply_eq.mpr rfl
  dsimp only [descOfSurjective]
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hmk, QuotientGroup.lift_mk]

private theorem descOfSurjective_comp {P Q M : Type*} [Group P] [Group Q] [Monoid M]
    (p : P →* Q) (hp : Function.Surjective p) (φ : P →* M) (hφ : p.ker ≤ φ.ker) :
    (descOfSurjective p hp φ hφ).comp p = φ :=
  MonoidHom.ext (descOfSurjective_apply p hp φ hφ)

private theorem descOfSurjective_unique {P Q M : Type*} [Group P] [Group Q] [Monoid M]
    (p : P →* Q) (hp : Function.Surjective p) (φ : P →* M) (hφ : p.ker ≤ φ.ker)
    (ψ : Q →* M) (hψ : ∀ g, ψ (p g) = φ g) :
    ψ = descOfSurjective p hp φ hφ := by
  ext q
  obtain ⟨g, rfl⟩ := hp q
  rw [hψ, descOfSurjective_apply]

private theorem ker_eq_map_of_comp_eq {P Q M : Type*} [Group P] [Group Q] [Monoid M]
    {p : P →* Q} (hp : Function.Surjective p) {φ : P →* M} {ψ : Q →* M}
    (hcomp : ψ.comp p = φ) :
    ψ.ker = φ.ker.map p := by
  rw [← Subgroup.map_comap_eq_self_of_surjective hp ψ.ker, MonoidHom.comap_ker, hcomp]

private theorem range_coe_eq_of_comp_eq {P Q M : Type*} [Monoid P] [Monoid Q] [Monoid M]
    {p : P →* Q} (hp : Function.Surjective p) {φ : P →* M} {ψ : Q →* M}
    (hcomp : ψ.comp p = φ) :
    Set.range ψ = Set.range φ := by
  rw [← hcomp, MonoidHom.coe_comp, hp.range_comp]

private theorem orbit_compHom_eq_of_surjective {P Q X : Type*} [Group P] [Group Q]
    [MulAction P X] {p : P →* Q} (hp : Function.Surjective p) (α : Q →* Equiv.Perm X)
    (hα : ∀ g x, α (p g) x = g • x) (x : X) :
    letI := MulAction.compHom X α
    MulAction.orbit Q x = MulAction.orbit P x := by
  let _ := MulAction.compHom X α
  have h : (fun q : Q ↦ q • x) ∘ p = fun g : P ↦ g • x := funext fun g ↦ hα g x
  exact (hp.range_comp (fun q : Q ↦ q • x)).symm.trans (congrArg Set.range h)

private theorem stabilizer_compHom_eq_of_surjective {P Q X : Type*} [Group P] [Group Q]
    [MulAction P X] {p : P →* Q} (hp : Function.Surjective p) (α : Q →* Equiv.Perm X)
    (hα : ∀ g x, α (p g) x = g • x) (x : X) :
    letI := MulAction.compHom X α
    MulAction.stabilizer Q x = (MulAction.stabilizer P x).map p := by
  let _ := MulAction.compHom X α
  rw [← Subgroup.map_comap_eq_self_of_surjective hp (MulAction.stabilizer Q x)]
  congr 1
  ext g
  simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  exact iff_of_eq (congrArg (· = x) (hα g x))

private theorem fixedPoints_compHom_eq_of_surjective {P Q X : Type*} [Group P] [Group Q]
    [MulAction P X] {p : P →* Q} (hp : Function.Surjective p) (α : Q →* Equiv.Perm X)
    (hα : ∀ g x, α (p g) x = g • x) :
    letI := MulAction.compHom X α
    MulAction.fixedPoints Q X = MulAction.fixedPoints P X := by
  let _ := MulAction.compHom X α
  ext x
  simp only [MulAction.mem_fixedPoints]
  exact hp.forall.trans (forall_congr' fun g ↦ iff_of_eq (congrArg (· = x) (hα g x)))

end SurjectiveDescent

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
  descOfSurjective (rationalComponentMap H) (rationalComponentMap_surjective H) φ
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
  descOfSurjective_apply _ _ _ _ g

/-- Composing the descended homomorphism with the rational component map recovers `φ`. -/
@[simp]
theorem descComponentGroupHom_comp_rationalComponentMap {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).comp (rationalComponentMap H) = φ :=
  descOfSurjective_comp _ _ _ _

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
  descOfSurjective_unique _ _ _ _ ψ hψ

/-- The kernel of the descended homomorphism is the image of `ker φ` in the component group. -/
theorem ker_descComponentGroupHom {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).ker = φ.ker.map (rationalComponentMap H) :=
  ker_eq_map_of_comp_eq (rationalComponentMap_surjective H)
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
  rw [← MonoidHom.ker_eq_bot_iff, ker_descComponentGroupHom, Subgroup.map_eq_bot_iff,
    rationalComponentMap_ker]
  exact ⟨fun h ↦ le_antisymm h hφ, fun h ↦ h.le⟩

/-- The descended homomorphism has the same set-theoretic range as `φ`. -/
@[simp]
theorem range_coe_descComponentGroupHom {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    Set.range (descComponentGroupHom H φ hφ) = Set.range φ :=
  range_coe_eq_of_comp_eq (rationalComponentMap_surjective H)
    (descComponentGroupHom_comp_rationalComponentMap H φ hφ)

/-- For a group target `M`, the descended homomorphism has the same subgroup range as `φ`. -/
@[simp]
theorem range_descComponentGroupHom {M : Type*} [Group M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).range = φ.range := by
  ext m
  exact Set.ext_iff.mp (range_coe_descComponentGroupHom H φ hφ) m

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
  orbit_compHom_eq_of_surjective (rationalComponentMap_surjective H)
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
  stabilizer_compHom_eq_of_surjective (rationalComponentMap_surjective H)
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
  fixedPoints_compHom_eq_of_surjective (rationalComponentMap_surjective H)
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
  descOfSurjective I.rationalComponentMap I.rationalComponentMap_surjective φ
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
  descOfSurjective_apply _ _ _ _ g

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
  descOfSurjective_comp _ _ _ _

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
  descOfSurjective_unique _ _ _ _ ψ hψ

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
  ker_eq_map_of_comp_eq I.rationalComponentMap_surjective
    (descSubgroupComponentGroupHom_comp_rationalComponentMap H I φ hφ)

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
  orbit_compHom_eq_of_surjective I.rationalComponentMap_surjective
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
  stabilizer_compHom_eq_of_surjective I.rationalComponentMap_surjective
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
  fixedPoints_compHom_eq_of_surjective I.rationalComponentMap_surjective
    (subgroupComponentGroupActionHom H I X htriv)
    (subgroupComponentGroupActionHom_rationalComponentMap H I X htriv)

end ClosedSubgroup

end TauCeti.FiniteTypeCommHopfAlgCat
