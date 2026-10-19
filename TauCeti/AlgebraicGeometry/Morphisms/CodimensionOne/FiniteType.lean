/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.CodimensionOne
public import TauCeti.RingTheory.KrullDimension.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Images of codimension-one points over a field

A finite dominant morphism of integral schemes sends codimension-one points to
codimension-one points when its target is locally of finite type over a field.
On affine charts, Noether normalization compares both prime heights with their
common contraction to a polynomial subalgebra, where going down applies.
The field-algebra structure on a target chart comes from the given structure
morphism, rather than an additional choice of finite-type algebra instances.

## Main results

* `AlgebraicGeometry.Scheme.Hom.coheight_apply_eq_one`: the image of a point of
  coheight one has coheight one. It supplies the preservation hypothesis of
  `AlgebraicGeometry.Scheme.Hom.codimensionOneMap`.

## References

* [Stacks Project, Lemma 33.20.3](https://stacks.math.columbia.edu/tag/0A21) and
  [Lemma 29.45.9](https://stacks.math.columbia.edu/tag/0ECG) give the dimension
  formula and integral-morphism dimension comparison underlying the roadmap's
  alternative dimension argument. We prove only the stated codimension-one
  consequence, using Noether normalization instead.
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `Pcf.coheight_apply_eq_one_of_mem_affine_finiteType` and
  `Pcf.coheight_apply_eq_one_of_finiteType` in `lean/Pcf/Bounding/SchemeExtraction.lean`.
-/

public section

open CategoryTheory AlgebraicGeometry Order

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite dominant morphism of integral schemes whose target is locally of finite type over
a field sends points of coheight one to points of coheight one. -/
theorem coheight_apply_eq_one {X Y : Scheme.{u}} (morphism : X ⟶ Y)
    (field : Type u) [Field field]
    (structureMap : Y ⟶ Spec (.of field)) [LocallyOfFiniteType structureMap]
    [IsFinite morphism] [IsDominant morphism] [IsIntegral X] [IsIntegral Y]
    (point : X) (hpoint : coheight point = 1) : coheight (morphism point) = 1 := by
  obtain ⟨_, ⟨targetOpen, htargetOpen, rfl⟩, htargetPoint, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (morphism point)) isOpen_univ
  change IsAffineOpen targetOpen at htargetOpen
  let sourceOpen := morphism ⁻¹ᵁ targetOpen
  have hsourceOpen : IsAffineOpen sourceOpen := htargetOpen.preimage morphism
  have hsourcePoint : point ∈ sourceOpen := htargetPoint
  have : Nonempty targetOpen := ⟨⟨morphism point, htargetPoint⟩⟩
  have : Nonempty sourceOpen := ⟨⟨point, hsourcePoint⟩⟩
  obtain ⟨chartMap, hchartMap⟩ :=
    Spec.homEquiv.symm.surjective (htargetOpen.fromSpec ≫ structureMap)
  change Spec.map chartMap = htargetOpen.fromSpec ≫ structureMap at hchartMap
  have hchartFinite : LocallyOfFiniteType (Spec.map chartMap) :=
    hchartMap.symm ▸ inferInstance
  have : RingHom.FiniteType chartMap.hom := HasRingHomProperty.Spec_iff.mp hchartFinite
  algebraize [chartMap.hom, (morphism.app targetOpen).hom]
  have : Module.Finite Γ(Y, targetOpen) Γ(X, sourceOpen) :=
    morphism.finite_app targetOpen htargetOpen
  have : IsSchemeTheoreticallyDominant morphism :=
    IsSchemeTheoreticallyDominant.of_isDominant morphism
  have : FaithfulSMul Γ(Y, targetOpen) Γ(X, sourceOpen) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (morphism.app_injective targetOpen)
  let sourcePrime : Spec Γ(X, sourceOpen) :=
    hsourceOpen.primeIdealOf ⟨point, hsourcePoint⟩
  let targetPrime : Spec Γ(Y, targetOpen) :=
    htargetOpen.primeIdealOf ⟨morphism point, htargetPoint⟩
  have hcontract : sourcePrime.asIdeal.under Γ(Y, targetOpen) = targetPrime.asIdeal := by
    change sourcePrime.asIdeal.comap (morphism.app targetOpen).hom = targetPrime.asIdeal
    rw [← morphism.appLE_eq_app]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE targetOpen htargetOpen sourceOpen hsourceOpen
        le_rfl hsourcePoint)
  have hsourceHeight : sourcePrime.asIdeal.height = coheight point := by
    rw [idealHeight_eq_coheight Γ(X, sourceOpen) sourcePrime]
    exact (coheight_eq_of_isOpenImmersion hsourceOpen.fromSpec).symm.trans
      (congrArg coheight (hsourceOpen.fromSpec_primeIdealOf ⟨point, hsourcePoint⟩))
  have htargetHeight : targetPrime.asIdeal.height = coheight (morphism point) := by
    rw [idealHeight_eq_coheight Γ(Y, targetOpen) targetPrime]
    exact (coheight_eq_of_isOpenImmersion htargetOpen.fromSpec).symm.trans
      (congrArg coheight (htargetOpen.fromSpec_primeIdealOf ⟨morphism point, htargetPoint⟩))
  rw [← htargetHeight, ← hcontract,
    ← Ideal.height_eq_height_under_of_finite_of_finiteType field, hsourceHeight, hpoint]

end AlgebraicGeometry.Scheme.Hom
