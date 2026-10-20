/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.Morphisms.CodimensionOne.Basic
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Images of codimension-one points over a field

A finite dominant morphism of integral schemes sends codimension-one points to
codimension-one points when its target is locally of finite type over a field.
More generally, a finite scheme-theoretically dominant morphism from an integral
scheme preserves the coheight of every point when its target is locally of finite
type over a field.
No normality or global Noetherian hypothesis is required. The coheight-one
specialization supplies the preservation hypothesis for mapping codimension-one
points with `AlgebraicGeometry.Scheme.Hom.codimensionOneMap`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.coheight_apply_eq`: a finite scheme-theoretically dominant
  morphism from an integral scheme with target locally of finite type over a field
  preserves coheight.
* `AlgebraicGeometry.Scheme.Hom.coheight_apply_eq_one`: the image of a point of
  coheight one has coheight one. It supplies the preservation hypothesis of
  `AlgebraicGeometry.Scheme.Hom.codimensionOneMap`.

## References

* [Stacks Project, Lemma 33.20.3](https://stacks.math.columbia.edu/tag/0A21) and
  [Lemma 29.45.9](https://stacks.math.columbia.edu/tag/0ECG) give the dimension
  formula and integral-morphism dimension comparison underlying preservation of
  coheight over a field. The results here are consequences, not formalizations of
  all clauses of these lemmas.
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

/-- A finite scheme-theoretically dominant morphism from an integral scheme whose target is
locally of finite type over a field preserves the coheight of every point. -/
theorem coheight_apply_eq {X Y : Scheme.{u}} (morphism : X ⟶ Y)
    (field : Type u) [Field field]
    (structureMap : Y ⟶ Spec (.of field)) [LocallyOfFiniteType structureMap]
    [IsFinite morphism] [IsSchemeTheoreticallyDominant morphism] [IsIntegral X]
    (point : X) : coheight (morphism point) = coheight point := by
  obtain ⟨_, ⟨targetOpen, htargetOpen, rfl⟩, htargetPoint, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (morphism point)) isOpen_univ
  simp only [Scheme.affineOpens, Set.mem_ofPred_eq] at htargetOpen
  let sourceOpen := morphism ⁻¹ᵁ targetOpen
  have hsourceOpen : IsAffineOpen sourceOpen := htargetOpen.preimage morphism
  have hsourcePoint : point ∈ sourceOpen := htargetPoint
  have : Nonempty targetOpen := ⟨⟨morphism point, htargetPoint⟩⟩
  have : Nonempty sourceOpen := ⟨⟨point, hsourcePoint⟩⟩
  obtain ⟨chartMap, hchartMap⟩ :=
    Spec.homEquiv.symm.surjective (htargetOpen.fromSpec ≫ structureMap)
  rw [Spec.homEquiv_symm_apply] at hchartMap
  have hchartFinite : LocallyOfFiniteType (Spec.map chartMap) :=
    hchartMap.symm ▸ inferInstance
  have : RingHom.FiniteType chartMap.hom := HasRingHomProperty.Spec_iff.mp hchartFinite
  algebraize [chartMap.hom, (morphism.app targetOpen).hom]
  have : Module.Finite Γ(Y, targetOpen) Γ(X, sourceOpen) :=
    morphism.finite_app targetOpen htargetOpen
  have : FaithfulSMul Γ(Y, targetOpen) Γ(X, sourceOpen) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (morphism.app_injective targetOpen)
  let sourcePrime : Spec Γ(X, sourceOpen) :=
    hsourceOpen.primeIdealOf ⟨point, hsourcePoint⟩
  let targetPrime : Spec Γ(Y, targetOpen) :=
    htargetOpen.primeIdealOf ⟨morphism point, htargetPoint⟩
  have hcontract : sourcePrime.asIdeal.under Γ(Y, targetOpen) = targetPrime.asIdeal := by
    rw [Ideal.under_def, RingHom.algebraMap_toAlgebra, ← morphism.appLE_eq_app]
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
    ← Ideal.height_eq_height_under_of_finite_of_finiteType field, hsourceHeight]

/-- A finite scheme-theoretically dominant morphism from an integral scheme whose target is
locally of finite type over a field sends points of coheight one to points of coheight one. -/
theorem coheight_apply_eq_one {X Y : Scheme.{u}} (morphism : X ⟶ Y)
    (field : Type u) [Field field]
    (structureMap : Y ⟶ Spec (.of field)) [LocallyOfFiniteType structureMap]
    [IsFinite morphism] [IsSchemeTheoreticallyDominant morphism] [IsIntegral X]
    (point : X) (hpoint : coheight point = 1) : coheight (morphism point) = 1 := by
  rw [morphism.coheight_apply_eq field structureMap, hpoint]

end AlgebraicGeometry.Scheme.Hom
