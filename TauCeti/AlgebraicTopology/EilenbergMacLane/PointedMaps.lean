/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.Homotopy.PointedHomotopyCat
public import TauCeti.Topology.CWComplex.Classical.CWType
import TauCeti.AlgebraicTopology.ClassifyingSpace.Comparison

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

The proofs transport the corresponding results for the cellular classifying space
(`TauCeti.exists_mapOfEq_cellularClassifyingSpace`,
`TauCeti.homotopicRel_of_mapOfEq_eq_cellularClassifyingSpace`) along the pointed homotopy
equivalence `TauCeti.cellularClassifyingSpaceHomotopyEquivIso`.

## Main results

* `TauCeti.IsAspherical.exists_mapOfEq`: homomorphisms out of `π₁` of a well-pointed aspherical
  space of CW type are induced by pointed maps.
* `TauCeti.IsAspherical.homotopicRel_of_mapOfEq_eq`: pointed maps out of a well-pointed aspherical
  space of CW type are determined up to pointed homotopy by `π₁`.
* `TauCeti.IsAspherical.fundamentalGroupFunctor_map_bijective`: pointed homotopy classes out of a
  well-pointed aspherical space of CW type correspond bijectively to homomorphisms on `π₁`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B,
  Proposition 1B.9.
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
  obtain ⟨R, -, -, hC⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (FundamentalGroup X x)
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
  obtain ⟨R, -, -, hC⟩ :=
    exists_isEilenbergMacLaneSpaceOne_cellularClassifyingSpace (FundamentalGroup X x)
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

end TauCeti
