/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

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
  (QuotientGroup.lift (rationalComponentMap H).ker φ
    (by rwa [rationalComponentMap_ker])).comp
    (QuotientGroup.liftEquiv (rationalComponentMap H).ker
      (rationalComponentMap_surjective H) rfl).symm.toMonoidHom

/-- The descended homomorphism agrees with `φ` on rational points. -/
@[simp]
theorem descComponentGroupHom_rationalComponentMap {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    descComponentGroupHom H φ hφ (rationalComponentMap H g) = φ g := by
  have hmk :
      (QuotientGroup.liftEquiv (rationalComponentMap H).ker
        (rationalComponentMap_surjective H) rfl).symm (rationalComponentMap H g) =
      (g : _ ⧸ (rationalComponentMap H).ker) := by
    apply (QuotientGroup.liftEquiv (rationalComponentMap H).ker
      (rationalComponentMap_surjective H) rfl).injective
    simp
  dsimp only [descComponentGroupHom]
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hmk, QuotientGroup.lift_mk]

/-- Composing the descended homomorphism with the rational component map recovers `φ`. -/
@[simp]
theorem descComponentGroupHom_comp_rationalComponentMap {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).comp (rationalComponentMap H) = φ := by
  ext g
  exact descComponentGroupHom_rationalComponentMap H φ hφ g

/-- A homomorphism out of the component group is uniquely determined by its values on rational
points. -/
theorem descComponentGroupHom_unique {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker)
    (ψ : ConnectedComponents (PrimeSpectrum H) →* M)
    (hψ : ∀ g, ψ (rationalComponentMap H g) = φ g) :
    ψ = descComponentGroupHom H φ hφ := by
  ext C
  obtain ⟨g, rfl⟩ := rationalComponentMap_surjective H C
  rw [hψ, descComponentGroupHom_rationalComponentMap]

/-- The kernel of the descended homomorphism is the image of `ker φ` in the component group. -/
theorem ker_descComponentGroupHom {M : Type*} [Monoid M]
    (φ : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) →* M)
    (hφ : CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) ≤
      φ.ker) :
    (descComponentGroupHom H φ hφ).ker = φ.ker.map (rationalComponentMap H) := by
  ext C
  obtain ⟨g, rfl⟩ := rationalComponentMap_surjective H C
  rw [MonoidHom.mem_ker, descComponentGroupHom_rationalComponentMap, Subgroup.mem_map]
  constructor
  · exact fun hg ↦ ⟨g, hg, rfl⟩
  · rintro ⟨g', hg', heq⟩
    have hdiff : g'⁻¹ * g ∈ (rationalComponentMap H).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
    rw [rationalComponentMap_ker] at hdiff
    calc
      φ g = φ (g' * (g'⁻¹ * g)) := by rw [mul_inv_cancel_left]
      _ = φ g' * φ (g'⁻¹ * g) := map_mul φ g' (g'⁻¹ * g)
      _ = 1 * 1 := by rw [MonoidHom.mem_ker.mp hg', MonoidHom.mem_ker.mp (hφ hdiff)]
      _ = 1 := mul_one 1

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
    Set.range (descComponentGroupHom H φ hφ) = Set.range φ := by
  conv_rhs => rw [← descComponentGroupHom_comp_rationalComponentMap H φ hφ]
  rw [MonoidHom.coe_comp, Set.range_comp, (rationalComponentMap_surjective H).range_eq,
    Set.image_univ]

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
  ext y
  constructor
  · rintro ⟨C, rfl⟩
    obtain ⟨g, rfl⟩ := rationalComponentMap_surjective H C
    exact ⟨g, (componentGroupActionHom_rationalComponentMap H X htriv g x).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨rationalComponentMap H g, componentGroupActionHom_rationalComponentMap H X htriv g x⟩

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
  ext C
  obtain ⟨g, rfl⟩ := rationalComponentMap_surjective H C
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_map]
  -- Under `MulAction.compHom`, scalar multiplication is application of `componentGroupActionHom`.
  change componentGroupActionHom H X htriv (rationalComponentMap H g) x = x ↔ _
  rw [componentGroupActionHom_rationalComponentMap]
  constructor
  · exact fun hg ↦ ⟨g, hg, rfl⟩
  · rintro ⟨g', hg', heq⟩
    have hdiff : g'⁻¹ * g ∈ (rationalComponentMap H).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
    rw [rationalComponentMap_ker] at hdiff
    calc
      g • x = (g' * (g'⁻¹ * g)) • x := by rw [mul_inv_cancel_left]
      _ = g' • ((g'⁻¹ * g) • x) := mul_smul g' (g'⁻¹ * g) x
      _ = g' • x := by rw [htriv _ hdiff x]
      _ = x := hg'

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
  ext x
  simp only [MulAction.mem_fixedPoints]
  constructor
  · intro hx g
    have h := hx (rationalComponentMap H g)
    -- Under `MulAction.compHom`, the action of a component is `componentGroupActionHom`.
    change componentGroupActionHom H X htriv (rationalComponentMap H g) x = x at h
    rwa [componentGroupActionHom_rationalComponentMap] at h
  · intro hx C
    obtain ⟨g, rfl⟩ := rationalComponentMap_surjective H C
    -- Under `MulAction.compHom`, the action of a component is `componentGroupActionHom`.
    change componentGroupActionHom H X htriv (rationalComponentMap H g) x = x
    rw [componentGroupActionHom_rationalComponentMap]
    exact hx g

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
theorem componentGroupActionHom_equivariant {K : FiniteTypeCommHopfAlgCat.{u, u} k}
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

/-- For nested closed subgroups `V(J) ⊆ V(I)` (`I ≤ J`), the induced component-group map
`π₀(V(J)) → π₀(V(I))` agrees with the inclusion `V(J)(k) ⊆ V(I)(k)`. -/
@[simp]
theorem mapComponentGroup_quotientMapOfLe_rationalComponentMap {I J : HopfIdeal k H}
    (hIJ : I ≤ J)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k)) :
    mapComponentGroup (quotientMapOfLe H hIJ) (J.rationalComponentMap g) =
      I.rationalComponentMap
        ⟨g.val, CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj hIJ _ g.property⟩ := by
  obtain ⟨q, rfl⟩ := (CommHopfAlgCat.quotientPointsSubgroupIso H.obj J
    (CommAlgCat.of k k)).groupIsoToMulEquiv.surjective g
  have hqeq :
      (CommHopfAlgCat.quotientPointsSubgroupIso H.obj J (CommAlgCat.of k k)).groupIsoToMulEquiv q =
      ⟨CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) q,
        CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj J _ q⟩ :=
    CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply H.obj J (CommAlgCat.of k k) q
  rw [hqeq, HopfIdeal.rationalComponentMap_quotientPointsHom,
    mapComponentGroup_rationalComponentMap]
  let q' : HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k) :=
    (CommHopfAlgCat.Hom.mapPointsFunctor
      (CommHopfAlgCat.quotientMapOfLe H.obj hIJ)).app (CommAlgCat.of k k) q
  have hq'_eq : BialgHom.mapDomain (A := k) (quotientMapOfLe H hIJ).hom.hom q = q' := by
    simp [q', BialgHom.mapDomain_apply, CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
  have hval : CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q' =
      CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) q :=
    (CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
      I (CommHopfAlgCat.quotientMapOfLe H.obj hIJ) (CommHopfAlgCat.mkQuotient H.obj J)
      (CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe H.obj hIJ) (CommAlgCat.of k k) q).symm
  have hsub :
      (⟨CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) q,
        CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj hIJ _
          (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj J _ q)⟩ :
        CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) =
      ⟨CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q',
        CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj I _ q'⟩ :=
    Subtype.ext hval.symm
  rw [hq'_eq, hsub, HopfIdeal.rationalComponentMap_quotientPointsHom]

/-- Descend a homomorphism `N(k) →* M` vanishing on `N°(k)` to `π₀(N)`. -/
noncomputable def descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    I.ComponentGroup →* M :=
  descComponentGroupHom (quotient H I)
    (φ.comp (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I
      (CommAlgCat.of k k)).groupIsoToMulEquiv.toMonoidHom)
    (fun q hq ↦ by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      apply hφ
      have hqeq :
          (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I
            (CommAlgCat.of k k)).groupIsoToMulEquiv q =
          ⟨CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q,
            CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj I _ q⟩ :=
        CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply H.obj I (CommAlgCat.of k k) q
      rw [← HopfIdeal.rationalComponentMap_eq_one_iff I, MulEquiv.coe_toMonoidHom, hqeq,
        HopfIdeal.rationalComponentMap_quotientPointsHom, rationalComponentMap_eq_one_iff]
      exact hq)

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
  obtain ⟨q, rfl⟩ := (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I
    (CommAlgCat.of k k)).groupIsoToMulEquiv.surjective g
  have hqeq :
      (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).groupIsoToMulEquiv q =
      ⟨CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q,
        CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj I _ q⟩ :=
    CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply H.obj I (CommAlgCat.of k k) q
  rw [hqeq, HopfIdeal.rationalComponentMap_quotientPointsHom, descSubgroupComponentGroupHom,
    descComponentGroupHom_rationalComponentMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    hqeq]

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
  ext C
  obtain ⟨g, rfl⟩ := I.rationalComponentMap_surjective C
  rw [hψ, descSubgroupComponentGroupHom_rationalComponentMap]

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
  ext C
  obtain ⟨g, rfl⟩ := I.rationalComponentMap_surjective C
  rw [MonoidHom.mem_ker, descSubgroupComponentGroupHom_rationalComponentMap, Subgroup.mem_map]
  constructor
  · exact fun hg ↦ ⟨g, hg, rfl⟩
  · rintro ⟨g', hg', heq⟩
    have hdiff :
        (g'⁻¹ * g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)).val ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) := by
      rw [← HopfIdeal.rationalComponentMap_eq_one_iff I, map_mul, map_inv, heq, inv_mul_cancel]
    calc
      φ g = φ (g' * (g'⁻¹ * g)) := by rw [mul_inv_cancel_left]
      _ = φ g' * φ (g'⁻¹ * g) := map_mul φ g' (g'⁻¹ * g)
      _ = 1 * 1 := by rw [MonoidHom.mem_ker.mp hg', hφ (g'⁻¹ * g) hdiff]
      _ = 1 := mul_one 1

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
  ext y
  constructor
  · rintro ⟨C, rfl⟩
    obtain ⟨g, rfl⟩ := I.rationalComponentMap_surjective C
    exact ⟨g, (subgroupComponentGroupActionHom_rationalComponentMap H I X htriv g x).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨I.rationalComponentMap g,
      subgroupComponentGroupActionHom_rationalComponentMap H I X htriv g x⟩

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
  ext C
  obtain ⟨g, rfl⟩ := I.rationalComponentMap_surjective C
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_map]
  -- Under `MulAction.compHom`, scalar multiplication is `subgroupComponentGroupActionHom`.
  change subgroupComponentGroupActionHom H I X htriv (I.rationalComponentMap g) x = x ↔ _
  rw [subgroupComponentGroupActionHom_rationalComponentMap]
  constructor
  · exact fun hg ↦ ⟨g, hg, rfl⟩
  · rintro ⟨g', hg', heq⟩
    have hdiff :
        (g'⁻¹ * g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)).val ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) := by
      rw [← HopfIdeal.rationalComponentMap_eq_one_iff I, map_mul, map_inv, heq, inv_mul_cancel]
    calc
      g • x = (g' * (g'⁻¹ * g)) • x := by rw [mul_inv_cancel_left]
      _ = g' • ((g'⁻¹ * g) • x) := mul_smul g' (g'⁻¹ * g) x
      _ = g' • x := by rw [htriv _ hdiff x]
      _ = x := hg'

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
  ext x
  simp only [MulAction.mem_fixedPoints]
  constructor
  · intro hx g
    have h := hx (I.rationalComponentMap g)
    -- Under `MulAction.compHom`, the action of a component is `subgroupComponentGroupActionHom`.
    change subgroupComponentGroupActionHom H I X htriv (I.rationalComponentMap g) x = x at h
    rwa [subgroupComponentGroupActionHom_rationalComponentMap] at h
  · intro hx C
    obtain ⟨g, rfl⟩ := I.rationalComponentMap_surjective C
    -- Under `MulAction.compHom`, the action of a component is `subgroupComponentGroupActionHom`.
    change subgroupComponentGroupActionHom H I X htriv (I.rationalComponentMap g) x = x
    rw [subgroupComponentGroupActionHom_rationalComponentMap]
    exact hx g

end ClosedSubgroup

end TauCeti.FiniteTypeCommHopfAlgCat
