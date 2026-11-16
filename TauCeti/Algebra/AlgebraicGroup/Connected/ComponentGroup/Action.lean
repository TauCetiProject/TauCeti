/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# Component-group actions and closed-subgroup component maps

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
* For any closed subgroup `N = V(I)` of `G` cut out by a Hopf ideal `I`, the ambient subgroup
  `N(k) ≤ G(k)` surjects onto `π₀(N)` (`TauCeti.FiniteTypeCommHopfAlgCat.subgroupComponentMap`)
  with kernel exactly `N°(k)`, identifying `N(k) / N°(k)` with `π₀(N)` and descending `N(k)`-actions
  that are trivial on `N°(k)` directly to `π₀(N)`.

No smoothness, reducedness, or characteristic hypothesis is required.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.descComponentGroupHom`: descend a homomorphism `G(k) →* M`
  vanishing on `G°(k)` to `π₀(G)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupActionHom` and
  `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupMulAction`: descend a `G(k)`-action trivial on
  `G°(k)` to `π₀(G)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.subgroupComponentMap`: surjective homomorphism `N(k) →* π₀(N)`
  with kernel `N°(k)` for a closed subgroup `N = V(I)`.
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
    have hdiff : g'⁻¹ * g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)) (CommAlgCat.of k k) := by
      rw [← rationalComponentMap_eq_one_iff, map_mul, map_inv, heq, inv_mul_cancel]
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

section ClosedSubgroupPoints

/-- The canonical isomorphism between the `A`-points of `H ⧸ I` and the ambient point subgroup
`quotientPointsSubgroup H.obj I A`. -/
noncomputable def quotientPointsSubgroupMulEquiv {k : Type u} [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H) (A : CommAlgCat.{u} k) :
    HopfAlgebra.points (R := k) (H := quotient H I) A ≃*
      CommHopfAlgCat.quotientPointsSubgroup H.obj I A :=
  MonoidHom.ofInjective
    (f := (CommHopfAlgCat.quotientPointsHom H.obj I A).hom)
    (CommHopfAlgCat.quotientPointsHom_injective H.obj I A)

/-- The underlying ambient point of `quotientPointsSubgroupMulEquiv` is `quotientPointsHom`. -/
@[simp]
theorem quotientPointsSubgroupMulEquiv_apply_val {k : Type u} [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H) (A : CommAlgCat.{u} k)
    (q : HopfAlgebra.points (R := k) (H := quotient H I) A) :
    (quotientPointsSubgroupMulEquiv H I A q :
      HopfAlgebra.points (R := k) (H := H) A) =
      CommHopfAlgCat.quotientPointsHom H.obj I A q :=
  MonoidHom.ofInjective_apply (CommHopfAlgCat.quotientPointsHom_injective H.obj I A)

/-- Applying `quotientPointsHom` to the inverse of `quotientPointsSubgroupMulEquiv` recovers the
ambient point. -/
@[simp]
theorem quotientPointsHom_quotientPointsSubgroupMulEquiv_symm {k : Type u} [Field k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H) (A : CommAlgCat.{u} k)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I A) :
    CommHopfAlgCat.quotientPointsHom H.obj I A
      ((quotientPointsSubgroupMulEquiv H I A).symm g) = g.1 :=
  MonoidHom.apply_ofInjective_symm (CommHopfAlgCat.quotientPointsHom_injective H.obj I A) g

end ClosedSubgroupPoints

section ClosedSubgroup

/-- The component group of a closed subgroup `V(I)` carries the component-group structure of its
quotient coordinate algebra. -/
noncomputable instance instGroupConnectedComponentsQuotient
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H) :
    Group (ConnectedComponents (PrimeSpectrum (quotient H I))) :=
  instGroupConnectedComponents (quotient H I)

/-- A closed subgroup of a finite-type affine group has finitely many connected components. -/
instance instFiniteConnectedComponentsQuotient
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H) :
    Finite (ConnectedComponents (PrimeSpectrum (quotient H I))) :=
  instFiniteConnectedComponents (quotient H I)

variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- The rational component map for a closed subgroup `N = V(I)`, defined directly on the ambient
subgroup `N(k) ≤ G(k)`. -/
noncomputable def subgroupComponentMap (I : HopfIdeal k H) :
    CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →*
      ConnectedComponents (PrimeSpectrum (quotient H I)) :=
  (rationalComponentMap (quotient H I)).comp
    (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k)).symm.toMonoidHom

/-- On an image of `quotientPointsSubgroupMulEquiv`, `subgroupComponentMap` is
`rationalComponentMap`. -/
@[simp]
theorem subgroupComponentMap_quotientPointsSubgroupMulEquiv (I : HopfIdeal k H)
    (q : HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k)) :
    subgroupComponentMap H I (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k) q) =
      rationalComponentMap (quotient H I) q := by
  rw [subgroupComponentMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

/-- On an included quotient point, `subgroupComponentMap` agrees with `rationalComponentMap`. -/
@[simp]
theorem subgroupComponentMap_quotientPointsHom (I : HopfIdeal k H)
    (q : HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k)) :
    subgroupComponentMap H I
        ⟨CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q,
          CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj I _ q⟩ =
      rationalComponentMap (quotient H I) q := by
  have heq :
      (⟨CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q,
        CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj I _ q⟩ :
        CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) =
      quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k) q :=
    Subtype.ext (quotientPointsSubgroupMulEquiv_apply_val H I (CommAlgCat.of k k) q).symm
  rw [heq, subgroupComponentMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

/-- Every connected component of a closed subgroup `N = V(I)` is represented by a rational point
in `N(k)`. -/
theorem subgroupComponentMap_surjective (I : HopfIdeal k H) :
    Function.Surjective (subgroupComponentMap H I) :=
  (rationalComponentMap_surjective (quotient H I)).comp
    (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k)).symm.surjective

/-- A rational point of a closed subgroup `N = V(I)` maps to the identity component of `N`
exactly when it belongs to the identity component `N°(k)`. -/
@[simp]
theorem subgroupComponentMap_eq_one_iff (I : HopfIdeal k H)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    subgroupComponentMap H I g = 1 ↔
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) := by
  obtain ⟨q, rfl⟩ := (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k)).surjective g
  rw [quotientPointsSubgroupMulEquiv_apply_val]
  have hmk : subgroupComponentMap H I
      (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k) q) =
      rationalComponentMap (quotient H I) q := by
    simp [subgroupComponentMap]
  rw [hmk, rationalComponentMap_eq_one_iff,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  constructor
  · intro hq x hx
    rw [CommHopfAlgCat.quotientPointsHom_apply_apply, ← CommHopfAlgCat.mkQuotient_apply]
    exact hq _ ((HopfIdeal.mem_identityComponent I x).mp hx)
  · intro hq y hy
    obtain ⟨x, rfl⟩ := CommHopfAlgCat.mkQuotient_surjective H.obj I y
    have hx := hq x ((HopfIdeal.mem_identityComponent I x).mpr hy)
    rwa [CommHopfAlgCat.quotientPointsHom_apply_apply, ← CommHopfAlgCat.mkQuotient_apply] at hx

/-- The kernel of `subgroupComponentMap H I` is the rational-point subgroup of `N°` viewed inside
`N(k)`. -/
theorem ker_subgroupComponentMap (I : HopfIdeal k H) :
    (subgroupComponentMap H I).ker =
      (CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent
        (CommAlgCat.of k k)).subgroupOf
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) := by
  ext g
  exact subgroupComponentMap_eq_one_iff H I g

/-- The rational points of `N°` form a normal subgroup of `N(k)`. -/
instance normal_identityComponent_subgroupOf (I : HopfIdeal k H) :
    ((CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent
      (CommAlgCat.of k k)).subgroupOf
      (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k))).Normal := by
  rw [← ker_subgroupComponentMap H I]
  infer_instance

/-- The rational-point quotient `N(k) / N°(k)` is isomorphic to `π₀(N)`. -/
noncomputable def subgroupComponentGroupEquivQuotient (I : HopfIdeal k H) :
    CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) ⧸
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent
          (CommAlgCat.of k k)).subgroupOf
          (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) ≃*
      ConnectedComponents (PrimeSpectrum (quotient H I)) :=
  QuotientGroup.liftEquiv _ (subgroupComponentMap_surjective H I)
    (ker_subgroupComponentMap H I).symm

/-- Including `π₀(N)` into `π₀(G)` agrees with the ambient rational component map on `N(k)`. -/
@[simp]
theorem mapComponentGroup_mkQuotient_subgroupComponentMap (I : HopfIdeal k H)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    mapComponentGroup (mkQuotient H I) (subgroupComponentMap H I g) =
      rationalComponentMap H g.1 := by
  obtain ⟨q, rfl⟩ := (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k)).surjective g
  have hmk : subgroupComponentMap H I
      (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k) q) =
      rationalComponentMap (quotient H I) q := by
    simp [subgroupComponentMap]
  rw [hmk, mapComponentGroup_rationalComponentMap (mkQuotient H I),
    quotientPointsSubgroupMulEquiv_apply_val]
  rfl

/-- For nested closed subgroups `V(J) ⊆ V(I)` (`I ≤ J`), the induced component-group map
`π₀(V(J)) → π₀(V(I))` agrees with the inclusion `V(J)(k) ⊆ V(I)(k)`. -/
@[simp]
theorem mapComponentGroup_quotientMapOfLe_subgroupComponentMap {I J : HopfIdeal k H}
    (hIJ : I ≤ J)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k)) :
    mapComponentGroup (quotientMapOfLe H hIJ) (subgroupComponentMap H J g) =
      subgroupComponentMap H I
        ⟨g.1, CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj hIJ _ g.2⟩ := by
  obtain ⟨q, rfl⟩ := (quotientPointsSubgroupMulEquiv H J (CommAlgCat.of k k)).surjective g
  have hq : subgroupComponentMap H J
      (quotientPointsSubgroupMulEquiv H J (CommAlgCat.of k k) q) =
      rationalComponentMap (quotient H J) q := by
    simp [subgroupComponentMap]
  rw [hq, mapComponentGroup_rationalComponentMap]
  let q' : HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k) :=
    (CommHopfAlgCat.Hom.mapPointsFunctor
      (CommHopfAlgCat.quotientMapOfLe H.obj hIJ)).app (CommAlgCat.of k k) q
  have hq'_eq : BialgHom.mapDomain (A := k) (quotientMapOfLe H hIJ).hom.hom q = q' := by
    simp [q', BialgHom.mapDomain_apply, CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
  have hval : CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q' =
      (quotientPointsSubgroupMulEquiv H J (CommAlgCat.of k k) q).1 := by
    rw [quotientPointsSubgroupMulEquiv_apply_val]
    exact (CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
      I (CommHopfAlgCat.quotientMapOfLe H.obj hIJ) (CommHopfAlgCat.mkQuotient H.obj J)
      (CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe H.obj hIJ) (CommAlgCat.of k k) q).symm
  have hsub :
      (⟨(quotientPointsSubgroupMulEquiv H J (CommAlgCat.of k k) q).1,
        CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj hIJ _
          (quotientPointsSubgroupMulEquiv H J (CommAlgCat.of k k) q).2⟩ :
        CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) =
      ⟨CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) q',
        CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj I _ q'⟩ :=
    Subtype.ext hval.symm
  rw [hq'_eq, hsub, subgroupComponentMap_quotientPointsHom]

/-- Descend a homomorphism `N(k) →* M` vanishing on `N°(k)` to `π₀(N)`. -/
noncomputable def descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    ConnectedComponents (PrimeSpectrum (quotient H I)) →* M :=
  descComponentGroupHom (quotient H I)
    (φ.comp (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k)).toMonoidHom)
    (fun q hq ↦ by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      apply hφ
      rw [← subgroupComponentMap_eq_one_iff, MulEquiv.coe_toMonoidHom,
        subgroupComponentMap_quotientPointsSubgroupMulEquiv, rationalComponentMap_eq_one_iff]
      exact hq)

/-- The descended subgroup homomorphism agrees with `φ` on `N(k)`. -/
@[simp]
theorem descSubgroupComponentGroupHom_subgroupComponentMap (I : HopfIdeal k H)
    {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    descSubgroupComponentGroupHom H I φ hφ (subgroupComponentMap H I g) = φ g := by
  obtain ⟨q, rfl⟩ := (quotientPointsSubgroupMulEquiv H I (CommAlgCat.of k k)).surjective g
  rw [subgroupComponentMap_quotientPointsSubgroupMulEquiv, descSubgroupComponentGroupHom,
    descComponentGroupHom_rationalComponentMap]
  rfl

/-- The descended subgroup homomorphism is uniquely determined on `N(k)`. -/
theorem descSubgroupComponentGroupHom_unique (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1)
    (ψ : ConnectedComponents (PrimeSpectrum (quotient H I)) →* M)
    (hψ : ∀ g, ψ (subgroupComponentMap H I g) = φ g) :
    ψ = descSubgroupComponentGroupHom H I φ hφ := by
  ext C
  obtain ⟨g, rfl⟩ := subgroupComponentMap_surjective H I C
  rw [hψ, descSubgroupComponentGroupHom_subgroupComponentMap]

/-- The kernel of the descended subgroup homomorphism is the image of `ker φ` under
`subgroupComponentMap`. -/
theorem ker_descSubgroupComponentGroupHom (I : HopfIdeal k H) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      φ g = 1) :
    (descSubgroupComponentGroupHom H I φ hφ).ker =
      φ.ker.map (subgroupComponentMap H I) := by
  ext C
  obtain ⟨g, rfl⟩ := subgroupComponentMap_surjective H I C
  rw [MonoidHom.mem_ker, descSubgroupComponentGroupHom_subgroupComponentMap, Subgroup.mem_map]
  constructor
  · exact fun hg ↦ ⟨g, hg, rfl⟩
  · rintro ⟨g', hg', heq⟩
    have hdiff : (g'⁻¹ * g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)).1 ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) := by
      rw [← subgroupComponentMap_eq_one_iff, map_mul, map_inv, heq, inv_mul_cancel]
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
    ConnectedComponents (PrimeSpectrum (quotient H I)) →* Equiv.Perm X :=
  descSubgroupComponentGroupHom H I (MulAction.toPermHom _ X) fun g hg ↦ by
    ext x
    exact htriv g hg x

/-- The descended closed-subgroup component action agrees with the `N(k)`-action. -/
@[simp]
theorem subgroupComponentGroupActionHom_subgroupComponentMap (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) (x : X) :
    subgroupComponentGroupActionHom H I X htriv (subgroupComponentMap H I g) x = g • x := by
  rw [subgroupComponentGroupActionHom, descSubgroupComponentGroupHom_subgroupComponentMap,
    MulAction.toPermHom_apply, MulAction.toPerm_apply]

/-- The descended `MulAction` of `π₀(N)` on `X` from an `N(k)`-action trivial on `N°(k)`. -/
noncomputable abbrev subgroupComponentGroupMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) :
    MulAction (ConnectedComponents (PrimeSpectrum (quotient H I))) X :=
  MulAction.compHom X (subgroupComponentGroupActionHom H I X htriv)

/-- The orbits of the descended `π₀(N)`-action coincide with the `N(k)`-orbits. -/
theorem orbit_subgroupComponentGroupMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) (x : X) :
    letI := subgroupComponentGroupMulAction H I X htriv
    MulAction.orbit (ConnectedComponents (PrimeSpectrum (quotient H I))) x =
      MulAction.orbit (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) x := by
  let _ := subgroupComponentGroupMulAction H I X htriv
  ext y
  constructor
  · rintro ⟨C, rfl⟩
    obtain ⟨g, rfl⟩ := subgroupComponentMap_surjective H I C
    exact ⟨g, (subgroupComponentGroupActionHom_subgroupComponentMap H I X htriv g x).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨subgroupComponentMap H I g,
      subgroupComponentGroupActionHom_subgroupComponentMap H I X htriv g x⟩

/-- The stabilizer in `π₀(N)` of a point is the image of its `N(k)`-stabilizer. -/
theorem stabilizer_subgroupComponentGroupMulAction (I : HopfIdeal k H) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) →
      ∀ x : X, g • x = x) (x : X) :
    letI := subgroupComponentGroupMulAction H I X htriv
    MulAction.stabilizer (ConnectedComponents (PrimeSpectrum (quotient H I))) x =
      (MulAction.stabilizer
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) x).map
        (subgroupComponentMap H I) := by
  let _ := subgroupComponentGroupMulAction H I X htriv
  ext C
  obtain ⟨g, rfl⟩ := subgroupComponentMap_surjective H I C
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_map]
  -- Under `MulAction.compHom`, scalar multiplication is `subgroupComponentGroupActionHom`.
  change subgroupComponentGroupActionHom H I X htriv (subgroupComponentMap H I g) x = x ↔ _
  rw [subgroupComponentGroupActionHom_subgroupComponentMap]
  constructor
  · exact fun hg ↦ ⟨g, hg, rfl⟩
  · rintro ⟨g', hg', heq⟩
    have hdiff : (g'⁻¹ * g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)).1 ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) := by
      rw [← subgroupComponentMap_eq_one_iff, map_mul, map_inv, heq, inv_mul_cancel]
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
    MulAction.fixedPoints (ConnectedComponents (PrimeSpectrum (quotient H I))) X =
      MulAction.fixedPoints
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) X := by
  let _ := subgroupComponentGroupMulAction H I X htriv
  ext x
  simp only [MulAction.mem_fixedPoints]
  constructor
  · intro hx g
    have h := hx (subgroupComponentMap H I g)
    -- Under `MulAction.compHom`, the action of a component is `subgroupComponentGroupActionHom`.
    change subgroupComponentGroupActionHom H I X htriv (subgroupComponentMap H I g) x = x at h
    rwa [subgroupComponentGroupActionHom_subgroupComponentMap] at h
  · intro hx C
    obtain ⟨g, rfl⟩ := subgroupComponentMap_surjective H I C
    -- Under `MulAction.compHom`, the action of a component is `subgroupComponentGroupActionHom`.
    change subgroupComponentGroupActionHom H I X htriv (subgroupComponentMap H I g) x = x
    rw [subgroupComponentGroupActionHom_subgroupComponentMap]
    exact hx g

end ClosedSubgroup

end TauCeti.FiniteTypeCommHopfAlgCat
