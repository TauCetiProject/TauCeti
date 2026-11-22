/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat.Basic
public import TauCeti.Topology.CWComplex.Classical.CWType
public import TauCeti.Topology.Homotopy.Extension.Basic
import TauCeti.AlgebraicTopology.ClassifyingSpace.Cellular
import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat.HomotopyEquiv

/-!
# Classification of pointed maps out of a well-pointed aspherical space

Pointed maps out of a well-pointed aspherical space `X` of CW type into a space `Z` whose higher
homotopy groups vanish from degree `2` on are classified by the homomorphism they induce on
fundamental groups:

* Every homomorphism `π₁(X, x) →* π₁(Z, z)` is realized by a continuous map sending `x` to `z`
  (`TauCeti.IsAspherical.exists_mapOfEq`).
* Two maps `X → Z` sending `x` to `z` that induce the same homomorphism on `π₁` are homotopic
  relative to `{x}` (`TauCeti.IsAspherical.homotopicRel_of_mapOfEq_eq`), provided `πₙ(Z, z')`
  vanishes for `n ≥ 2` at every point `z' ∈ Z`.
* In `TauCeti.PointedHomotopyCat`, taking `π₁` gives a bijection from pointed homotopy classes
  `X ⟶ Y` to group homomorphisms `π₁(X) ⟶ π₁(Y)`
  (`TauCeti.IsAspherical.fundamentalGroupFunctor_map_bijective`).
* Consequently, any two well-pointed aspherical spaces of CW type are isomorphic in
  `TauCeti.PointedHomotopyCat` by a unique isomorphism realizing a prescribed isomorphism on `π₁`
  (`TauCeti.IsAspherical.pointedHomotopyCatIso`,
  `TauCeti.IsAspherical.eq_pointedHomotopyCatIso_of_fundamentalGroupFunctor_map_eq`).

The proofs transport the corresponding results for the cellular classifying space
(`TauCeti.exists_mapOfEq_cellularClassifyingSpace`,
`TauCeti.homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace`) along the pointed homotopy
equivalence `TauCeti.cellularClassifyingSpaceHomotopyEquivIso`, applied to a cellular presentation
from `TauCeti.exists_cellularClassifyingSpace_isEilenbergMacLaneSpaceOne`.

## Main definitions

* `TauCeti.IsAspherical.pointedHomotopyCatIso`: **the unique isomorphism in `PointedHomotopyCat`
  between well-pointed aspherical spaces of CW type realizing a prescribed isomorphism on `π₁`.**

## Main results

* `TauCeti.IsAspherical.exists_mapOfEq`: homomorphisms out of `π₁` of a well-pointed aspherical
  space of CW type are induced by pointed maps.
* `TauCeti.IsAspherical.homotopicRel_of_mapOfEq_eq`: pointed maps out of a well-pointed aspherical
  space of CW type are determined up to pointed homotopy by `π₁`.
* `TauCeti.IsAspherical.fundamentalGroupFunctor_map_bijective`: pointed homotopy classes out of a
  well-pointed aspherical space of CW type correspond bijectively to homomorphisms on `π₁`.
* `TauCeti.IsAspherical.eq_pointedHomotopyCatIso_of_fundamentalGroupFunctor_map_eq`: uniqueness of
  the pointed isomorphism realizing a prescribed isomorphism on `π₁`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (Proposition 0.19)
  and Section 1.B, Proposition 1B.9.
-/

public section

noncomputable section

open scoped Topology Topology.Homotopy

universe u v

namespace TauCeti

/-- **Homomorphisms out of `π₁` of a well-pointed aspherical space of CW type are induced by
pointed maps.** If the homotopy groups of `(Z, z)` vanish from degree `2` on, every homomorphism
`π₁(X, x) →* π₁(Z, z)` is induced by a continuous map sending `x` to `z`. -/
theorem IsAspherical.exists_mapOfEq {X Z : Type u} [TopologicalSpace X] [CWType X]
    [TopologicalSpace Z] {x : X} {z : Z} (hX : IsAspherical X x)
    (hX_hep : HasHomotopyExtensionProperty ({x} : Set X))
    (hZ : ∀ k, 2 ≤ k → Subsingleton (π_ k Z z))
    (fπ : FundamentalGroup X x →* FundamentalGroup Z z) :
    ∃ (f : C(X, Z)) (hf : f x = z), FundamentalGroup.mapOfEq f hf = fπ := by
  obtain ⟨R, hC⟩ :=
    exists_cellularClassifyingSpace_isEilenbergMacLaneSpaceOne (FundamentalGroup X x)
  obtain ⟨φ⟩ := hC.nonempty_fundamentalGroupMulEquiv
  let e := cellularClassifyingSpaceHomotopyEquivIso (Y := ⟨X, x⟩) R hX hX_hep φ
  let v : C(X, cellularClassifyingSpace R) := (PointedHomotopyCat.homotopyEquivOfIso e).invFun
  have hv : v x = cellularClassifyingSpaceBasepoint R :=
    PointedHomotopyCat.homotopyEquivOfIso_invFun_basepoint e
  have hvπ : FundamentalGroup.mapOfEq v hv = φ.symm.toMonoidHom :=
    congrArg GrpCat.Hom.hom <|
      (congrArg PointedHomotopyCat.fundamentalGroupFunctor.map
        (PointedHomotopyCat.quotient_map_homotopyEquivOfIso_invFun e)).trans
        (fundamentalGroupFunctor_map_cellularClassifyingSpaceHomotopyEquivIso_inv
          (Y := ⟨X, x⟩) R hX hX_hep φ)
  obtain ⟨f, hf, hfπ⟩ := exists_mapOfEq_cellularClassifyingSpace R hZ (fπ.comp φ.toMonoidHom)
  refine ⟨f.comp v, by rw [ContinuousMap.comp_apply, hv, hf], MonoidHom.ext fun a ↦ ?_⟩
  rw [← FundamentalGroup.mapOfEq_comp f v hv hf a, hvπ, hfπ]
  exact congrArg fπ (φ.apply_symm_apply a)

/-- **Pointed maps out of a well-pointed aspherical space of CW type are determined up to pointed
homotopy by `π₁`.** If the homotopy groups of `Z` vanish from degree `2` on, at every point, two
maps `X → Z` sending `x` to `z` and inducing the same homomorphism on `π₁` are homotopic relative
to `{x}`. -/
theorem IsAspherical.homotopicRel_of_mapOfEq_eq {X : Type u} {Z : Type v} [TopologicalSpace X]
    [CWType X] [TopologicalSpace Z] {x : X} (hX : IsAspherical X x)
    (hX_hep : HasHomotopyExtensionProperty ({x} : Set X))
    (hZ : ∀ (z : Z) (n : ℕ), Subsingleton (π_ (n + 2) Z z))
    {f g : C(X, Z)} {z : Z} (hf : f x = z) (hg : g x = z)
    (hfg : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    f.HomotopicRel g {x} := by
  obtain ⟨R, hC⟩ :=
    exists_cellularClassifyingSpace_isEilenbergMacLaneSpaceOne (FundamentalGroup X x)
  obtain ⟨φ⟩ := hC.nonempty_fundamentalGroupMulEquiv
  let e := cellularClassifyingSpaceHomotopyEquivIso (Y := ⟨X, x⟩) R hX hX_hep φ
  let u : C(cellularClassifyingSpace R, X) := (PointedHomotopyCat.homotopyEquivOfIso e).toFun
  let v : C(X, cellularClassifyingSpace R) := (PointedHomotopyCat.homotopyEquivOfIso e).invFun
  have hu : u (cellularClassifyingSpaceBasepoint R) = x :=
    PointedHomotopyCat.homotopyEquivOfIso_toFun_basepoint e
  have hv : v x = cellularClassifyingSpaceBasepoint R :=
    PointedHomotopyCat.homotopyEquivOfIso_invFun_basepoint e
  have hright : (u.comp v).HomotopicRel (ContinuousMap.id X) {x} :=
    PointedHomotopyCat.homotopyEquivOfIso_right_inv_homotopicRel e
  -- Pulling back along `u` transfers the problem to the cellular model.
  have hcell : (f.comp u).HomotopicRel (g.comp u) {cellularClassifyingSpaceBasepoint R} :=
    homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace R hZ
      (by rw [ContinuousMap.comp_apply, hu, hf]) (by rw [ContinuousMap.comp_apply, hu, hg]) <|
      MonoidHom.ext fun a ↦ by
        rw [← FundamentalGroup.mapOfEq_comp f u hu hf a,
          ← FundamentalGroup.mapOfEq_comp g u hu hg a, hfg]
  have hpre : ((f.comp u).comp v).HomotopicRel ((g.comp u).comp v) {x} :=
    (hcell.precomp v).mono (Set.singleton_subset_iff.2 hv)
  exact ((hright.comp_continuousMap f).symm.trans hpre).trans (hright.comp_continuousMap g)

/-- **Pointed maps out of a well-pointed aspherical space of CW type are classified by `π₁`.** If
the homotopy groups of `Y` vanish from degree `2` on, at every point, then `π₁` gives a bijection
from pointed homotopy classes `X ⟶ Y` to group homomorphisms `π₁(X) ⟶ π₁(Y)`. -/
theorem IsAspherical.fundamentalGroupFunctor_map_bijective {X Y : BasedTopologicalSpace.{u}}
    [CWType X.carrier] (hX : IsAspherical X.carrier X.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY : ∀ (y : Y.carrier) (n : ℕ), Subsingleton (π_ (n + 2) Y.carrier y)) :
    Function.Bijective (PointedHomotopyCat.fundamentalGroupFunctor.map
      (X := PointedHomotopyCat.quotient.obj X) (Y := PointedHomotopyCat.quotient.obj Y)) := by
  refine ⟨fun a b hab ↦ ?_, fun ψ ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := PointedHomotopyCat.quotient.map_surjective a
    obtain ⟨g, rfl⟩ := PointedHomotopyCat.quotient.map_surjective b
    rw [PointedHomotopyCat.quotient_map_eq_iff]
    exact hX.homotopicRel_of_mapOfEq_eq hX_hep hY f.map_basepoint g.map_basepoint
      (congrArg GrpCat.Hom.hom hab)
  · obtain ⟨f, hf, hfψ⟩ := hX.exists_mapOfEq hX_hep
      (fun k hk ↦ by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hk
        exact hY _ n) ψ.hom
    exact ⟨PointedHomotopyCat.quotient.map ⟨f, hf⟩, GrpCat.hom_ext <|
      (congrArg GrpCat.Hom.hom
        (PointedHomotopyCat.fundamentalGroupFunctor_map_quotient_map _)).trans
        ((BasedTopologicalSpace.fundamentalGroupFunctor_map_hom _).trans hfψ)⟩

/-- **Pointed uniqueness of well-pointed aspherical spaces of CW type.** Two well-pointed
aspherical spaces of CW type are isomorphic in `PointedHomotopyCat` by a canonical isomorphism
realizing any prescribed isomorphism `φ` on fundamental groups. This isomorphism is unique
(`TauCeti.IsAspherical.eq_pointedHomotopyCatIso_of_fundamentalGroupFunctor_map_eq`).

The well-pointedness hypotheses (`HasHomotopyExtensionProperty`) cannot be dropped in general:
for example, the comb space based at a non-locally-contractible point is contractible (hence
aspherical and of CW type) without being pointed homotopy equivalent to a point. -/
def IsAspherical.pointedHomotopyCatIso {X Y : BasedTopologicalSpace.{u}} [CWType X.carrier]
    [CWType Y.carrier] (hX : IsAspherical X.carrier X.basepoint)
    (hY : IsAspherical Y.carrier Y.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY_hep : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (φ : FundamentalGroup X.carrier X.basepoint ≃* FundamentalGroup Y.carrier Y.basepoint) :
    PointedHomotopyCat.quotient.obj X ≅ PointedHomotopyCat.quotient.obj Y :=
  let hXY := hX.fundamentalGroupFunctor_map_bijective hX_hep
    (fun y n ↦ (hY.of_basepoint y).subsingleton_homotopyGroup n)
  let hYX := hY.fundamentalGroupFunctor_map_bijective hY_hep
    (fun x n ↦ (hX.of_basepoint x).subsingleton_homotopyGroup n)
  let hf := hXY.2 (GrpCat.ofHom φ.toMonoidHom)
  let hg := hYX.2 (GrpCat.ofHom φ.symm.toMonoidHom)
  { hom := hf.choose
    inv := hg.choose
    hom_inv_id := (hX.fundamentalGroupFunctor_map_bijective hX_hep
        (fun x n ↦ (hX.of_basepoint x).subsingleton_homotopyGroup n)).1 <| by
      rw [CategoryTheory.Functor.map_comp, hf.choose_spec, hg.choose_spec,
        CategoryTheory.Functor.map_id]
      exact GrpCat.hom_ext <| MonoidHom.ext fun a ↦ φ.symm_apply_apply a
    inv_hom_id := (hY.fundamentalGroupFunctor_map_bijective hY_hep
        (fun y n ↦ (hY.of_basepoint y).subsingleton_homotopyGroup n)).1 <| by
      rw [CategoryTheory.Functor.map_comp, hg.choose_spec, hf.choose_spec,
        CategoryTheory.Functor.map_id]
      exact GrpCat.hom_ext <| MonoidHom.ext fun a ↦ φ.apply_symm_apply a }

/-- The forward morphism of `IsAspherical.pointedHomotopyCatIso` induces `φ` on `π₁`. -/
@[simp]
theorem IsAspherical.fundamentalGroupFunctor_map_pointedHomotopyCatIso_hom
    {X Y : BasedTopologicalSpace.{u}} [CWType X.carrier] [CWType Y.carrier]
    (hX : IsAspherical X.carrier X.basepoint) (hY : IsAspherical Y.carrier Y.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY_hep : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (φ : FundamentalGroup X.carrier X.basepoint ≃* FundamentalGroup Y.carrier Y.basepoint) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (hX.pointedHomotopyCatIso hY hX_hep hY_hep φ).hom =
      GrpCat.ofHom φ.toMonoidHom :=
  ((hX.fundamentalGroupFunctor_map_bijective hX_hep
    (fun y n ↦ (hY.of_basepoint y).subsingleton_homotopyGroup n)).2
      (GrpCat.ofHom φ.toMonoidHom)).choose_spec

/-- The inverse morphism of `IsAspherical.pointedHomotopyCatIso` induces `φ⁻¹` on `π₁`. -/
@[simp]
theorem IsAspherical.fundamentalGroupFunctor_map_pointedHomotopyCatIso_inv
    {X Y : BasedTopologicalSpace.{u}} [CWType X.carrier] [CWType Y.carrier]
    (hX : IsAspherical X.carrier X.basepoint) (hY : IsAspherical Y.carrier Y.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY_hep : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (φ : FundamentalGroup X.carrier X.basepoint ≃* FundamentalGroup Y.carrier Y.basepoint) :
    PointedHomotopyCat.fundamentalGroupFunctor.map
        (hX.pointedHomotopyCatIso hY hX_hep hY_hep φ).inv =
      GrpCat.ofHom φ.symm.toMonoidHom :=
  ((hY.fundamentalGroupFunctor_map_bijective hY_hep
    (fun x n ↦ (hX.of_basepoint x).subsingleton_homotopyGroup n)).2
      (GrpCat.ofHom φ.symm.toMonoidHom)).choose_spec

/-- **Uniqueness of the pointed isomorphism realizing `φ`.** Every isomorphism in
`PointedHomotopyCat` between well-pointed aspherical spaces of CW type that induces `φ` on `π₁`
agrees with `IsAspherical.pointedHomotopyCatIso`. -/
theorem IsAspherical.eq_pointedHomotopyCatIso_of_fundamentalGroupFunctor_map_eq
    {X Y : BasedTopologicalSpace.{u}} [CWType X.carrier] [CWType Y.carrier]
    (hX : IsAspherical X.carrier X.basepoint) (hY : IsAspherical Y.carrier Y.basepoint)
    (hX_hep : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hY_hep : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (φ : FundamentalGroup X.carrier X.basepoint ≃* FundamentalGroup Y.carrier Y.basepoint)
    {e : PointedHomotopyCat.quotient.obj X ≅ PointedHomotopyCat.quotient.obj Y}
    (he : PointedHomotopyCat.fundamentalGroupFunctor.map e.hom = GrpCat.ofHom φ.toMonoidHom) :
    e = hX.pointedHomotopyCatIso hY hX_hep hY_hep φ :=
  CategoryTheory.Iso.ext <| (hX.fundamentalGroupFunctor_map_bijective hX_hep
    (fun y n ↦ (hY.of_basepoint y).subsingleton_homotopyGroup n)).1
    (he.trans (hX.fundamentalGroupFunctor_map_pointedHomotopyCatIso_hom hY hX_hep hY_hep φ).symm)

end TauCeti
