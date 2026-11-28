/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.AlgebraicGeometry.AbelianVariety.TateModule.Basic
public import TauCeti.AlgebraicGeometry.RationalPoint.Galois
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic

/-!
# Galois action on the Tate module of an abelian variety

The absolute Galois group acts on each level of the integral Tate module by precomposition
with the spectrum of an automorphism of the separable closure. The action is jointly continuous
for the Krull and inverse-limit topologies, and homomorphisms of abelian varieties intertwine it.

## References

* J. S. Milne, *Abelian Varieties* (2022), Remark 8.4.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Over

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K] {A B : AbelianVariety K}

/-- The additive map on geometric points induced by a Galois element, as group-valued
Yoneda precomposition. -/
private noncomputable def geometricPointsGaloisMap (A : AbelianVariety K)
    (σ : AbsoluteGaloisGroup K) : A.geometricPoints →+ A.geometricPoints :=
  ((yonedaGrpObj A.toOver).map
    ((algSpec (.of K)).map (CommAlgCat.ofHom σ.toAlgHom).op).op).hom.toAdditive

private lemma geometricPointsGaloisMap_apply
    (σ : AbsoluteGaloisGroup K) (x : A.geometricPoints) :
    (geometricPointsGaloisMap A σ x).toMul = σ • x.toMul := by
  rw [Over.pointGaloisAction_smul, geometricPointsGaloisMap]
  simp only [yonedaGrpObj]
  rfl

variable (A) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The absolute Galois representation on the integral `ℓ`-adic Tate module. -/
noncomputable def tateModuleGaloisRepresentation :
    Representation ℤ_[ℓ] (AbsoluteGaloisGroup K) (A.tateModule ℓ) where
  toFun σ := TateModule.mapLinearMap (geometricPointsGaloisMap A σ)
  map_one' := LinearMap.ext fun x ↦ TateModule.ext fun n ↦ Subtype.ext <| by
    apply Additive.toMul.injective
    simp only [TateModule.mapLinearMap_apply, TateModule.proj_map, TateModule.levelMap_apply,
      geometricPointsGaloisMap_apply, one_smul, one_apply_eq_self]
  map_mul' σ τ := LinearMap.ext fun x ↦ TateModule.ext fun n ↦ Subtype.ext <| by
    apply Additive.toMul.injective
    simp only [TateModule.mapLinearMap_apply, TateModule.proj_map, TateModule.levelMap_apply,
      mul_apply_eq_comp, geometricPointsGaloisMap_apply, mul_smul]

variable {A}

/-- On the `n`-th torsion level the Galois representation acts on the geometric point. -/
@[simp]
theorem coe_proj_tateModuleGaloisRepresentation
    (σ : AbsoluteGaloisGroup K) (x : A.tateModule ℓ) (n : ℕ) :
    (TateModule.proj n (A.tateModuleGaloisRepresentation ℓ σ x) : A.geometricPoints).toMul =
      σ • (TateModule.proj n x : A.geometricPoints).toMul := by
  simp only [tateModuleGaloisRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
    TateModule.mapLinearMap_apply, TateModule.proj_map, TateModule.levelMap_apply,
    geometricPointsGaloisMap_apply]

/-- The Galois action on the Tate module is jointly continuous. -/
theorem continuous_tateModuleGaloisRepresentation_apply (A : AbelianVariety K) :
    Continuous fun q : AbsoluteGaloisGroup K × A.tateModule ℓ ↦
      A.tateModuleGaloisRepresentation ℓ q.1 q.2 := by
  refine (TateModule.continuous_map_apply (p := ℓ) (f := geometricPointsGaloisMap A) ?_).congr ?_
  · intro n x
    have h (σ : AbsoluteGaloisGroup K) :
        geometricPointsGaloisMap A σ x =
          Additive.ofMul (σ • (x : A.geometricPoints).toMul) := by
      rw [← geometricPointsGaloisMap_apply (A := A) σ (x : A.geometricPoints)]
      rfl
    simp_rw [h]
    exact (Over.isLocallyConstant_pointGaloisAction A.toOver
      (x : A.geometricPoints).toMul).comp Additive.ofMul
  · intro q
    exact (TateModule.mapLinearMap_apply (p := ℓ) (geometricPointsGaloisMap A q.1) q.2).symm

/-- The map induced by a homomorphism of abelian varieties is Galois-equivariant. -/
theorem tateMap_tateModuleGaloisRepresentation (f : A ⟶ B)
    (σ : AbsoluteGaloisGroup K) (x : A.tateModule ℓ) :
    tateMap ℓ f (A.tateModuleGaloisRepresentation ℓ σ x) =
      B.tateModuleGaloisRepresentation ℓ σ (tateMap ℓ f x) := by
  refine TateModule.ext fun n ↦ Subtype.ext ?_
  apply Additive.toMul.injective
  simp only [coe_proj_tateMap, coe_proj_tateModuleGaloisRepresentation,
    Over.pointGaloisAction_smul]
  exact Category.assoc _ _ _

end TauCeti.AlgebraicGeometry.AbelianVariety
