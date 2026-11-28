/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.TateModule
public import TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup
public import Mathlib.FieldTheory.SeparableClosure

/-!
# The Tate module of an abelian variety over a field

The integral Tate module is the inverse limit of the prime-power torsion of the points over the
separable closure, with multiplication by the prime as transition maps. A homomorphism of abelian
varieties acts by postcomposition on each torsion level and gives a continuous linear map on the
inverse limit.

## References

* J. S. Milne, *Abelian Varieties* (2022), Remark 8.4.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K]

/-- The additive group of points of an abelian variety over the separable closure of its base
field. -/
noncomputable abbrev geometricPoints (A : AbelianVariety K) :=
  Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))) ⟶ A.toOver)

/-- The integral `ℓ`-adic Tate module, formed from the `ℓ`-power torsion in the points of `A`
over the separable closure. -/
noncomputable abbrev tateModule (A : AbelianVariety K) (ℓ : ℕ) :=
  TateModule ℓ A.geometricPoints

variable {A B C : AbelianVariety K}

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The linear map on integral Tate modules induced by a homomorphism of abelian varieties. -/
noncomputable def tateMap (f : A ⟶ B) :
    A.tateModule ℓ →ₗ[ℤ_[ℓ]] B.tateModule ℓ :=
  TateModule.mapLinearMap (IsMonHom.monoidHom (Hom.toOverHom f) _).toAdditive

/-- On the `n`-th torsion level, the Tate map is postcomposition with the homomorphism. -/
@[simp]
theorem coe_proj_tateMap (f : A ⟶ B) (x : A.tateModule ℓ) (n : ℕ) :
    (TateModule.proj n (tateMap ℓ f x) : B.geometricPoints).toMul =
      (TateModule.proj n x : A.geometricPoints).toMul ≫ Hom.toOverHom f := by
  simp only [tateMap, TateModule.mapLinearMap_apply, TateModule.proj_map, TateModule.levelMap_apply]
  rfl

/-- The map on Tate modules is continuous for the inverse-limit topology. -/
theorem continuous_tateMap (f : A ⟶ B) :
    Continuous (tateMap ℓ f : A.tateModule ℓ → B.tateModule ℓ) :=
  (TateModule.continuous_map (p := ℓ) (IsMonHom.monoidHom (Hom.toOverHom f) _).toAdditive).congr
    fun x ↦ (TateModule.mapLinearMap_apply _ x).symm

/-- The identity of an abelian variety induces the identity on its Tate module. -/
@[simp]
theorem tateMap_id :
    tateMap ℓ (𝟙 A) = LinearMap.id := by
  ext x
  simp only [tateMap, TateModule.mapLinearMap_apply, Hom.toOverHom_id,
    IsMonHom.monoidHom_id, MonoidHom.toAdditive_id, TateModule.map_id,
    AddMonoidHom.id_apply, LinearMap.id_apply]

/-- The induced maps on Tate modules preserve composition. -/
@[simp]
theorem tateMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    tateMap ℓ (f ≫ g) = (tateMap ℓ g).comp (tateMap ℓ f) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [tateMap, LinearMap.comp_apply, TateModule.mapLinearMap_apply, Hom.toOverHom_comp,
    IsMonHom.monoidHom_comp]
  exact DFunLike.congr_fun (TateModule.map_comp (p := ℓ)
    (IsMonHom.monoidHom (Hom.toOverHom g) _).toAdditive
    (IsMonHom.monoidHom (Hom.toOverHom f) _).toAdditive) x

open scoped Hom in
/-- The pointwise product of abelian-variety homomorphisms induces the sum of their Tate maps. -/
@[simp]
theorem tateMap_mul (f g : A ⟶ B) :
    tateMap ℓ (f * g) = tateMap ℓ f + tateMap ℓ g := by
  apply LinearMap.ext
  intro x
  refine TateModule.ext fun n ↦ Subtype.ext ?_
  -- Addition in the point group is multiplication in the group-object Hom.
  apply Additive.toMul.injective
  simp only [LinearMap.add_apply, map_add, AddSubgroup.coe_add]
  rw [coe_proj_tateMap, Hom.toOverHom_mul, MonObj.comp_mul]
  exact congrArg₂ (· * ·) (coe_proj_tateMap ℓ f x n).symm (coe_proj_tateMap ℓ g x n).symm

open scoped Hom in
/-- The zero homomorphism induces the zero map on Tate modules. -/
@[simp]
theorem tateMap_one :
    tateMap ℓ (1 : A ⟶ B) = 0 := by
  apply add_left_cancel (a := tateMap ℓ (1 : A ⟶ B))
  simpa only [one_mul, add_zero] using (tateMap_mul ℓ (1 : A ⟶ B) 1).symm

end TauCeti.AlgebraicGeometry.AbelianVariety
