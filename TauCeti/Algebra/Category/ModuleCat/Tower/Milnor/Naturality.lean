/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Milnor.Basic
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Naturality of the Milnor sequence

A map of towers of complexes induces maps on their limit and product complexes. These
commute with the inclusion and the difference map, so the two maps of the Milnor short
exact sequence are natural. The connecting square retains the actual connecting morphism
of the product-complex short exact sequence.

The complex shape is arbitrary, in particular allowing integer-graded chain and cochain
complexes. Naturality of the map to the limit of homology requires no surjectivity;
naturality of the connecting map assumes only that the difference maps on terms are
surjective, as in `ComplexTower.shortComplex_shortExact`.

The construction uses Mathlib's `Limits.IsLimit.map` and
`HomologicalComplex.HomologySequence.δ_naturality` and the product and limit cones of
`ComplexTower`.

## References

* C. A. Weibel, *An introduction to homological algebra*, Theorem 3.5.8.
* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
-/

public section

noncomputable section

namespace TauCeti.ComplexTower

open CategoryTheory Limits Opposite

universe v u w

variable {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
  {C D E : ComplexTower.{v} R c}

/-- The map of limit complexes induced by a map of towers. -/
def limComplexMap (f : C ⟶ D) : C.limComplex ⟶ D.limComplex :=
  D.isLimitLimComplexCone.map C.limComplexCone f

/-- The induced limit map commutes with every projection. -/
@[reassoc (attr := simp)]
theorem limComplexMap_comp_π (f : C ⟶ D) (n : ℕ) :
    limComplexMap f ≫ D.limComplexπ n = C.limComplexπ n ≫ f.app (op n) :=
  D.isLimitLimComplexCone.map_π C.limComplexCone f (op n)

@[simp]
theorem limComplexMap_id : limComplexMap (𝟙 C) = 𝟙 C.limComplex := by
  apply C.isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  -- State the equality on the named complexes so simplification does not have to
  -- unfold the cone point inside the category instance.
  have h : limComplexMap (𝟙 C) ≫ C.limComplexπ n = 𝟙 C.limComplex ≫ C.limComplexπ n := by
    simp
  exact h

@[simp]
theorem limComplexMap_comp (f : C ⟶ D) (g : D ⟶ E) :
    limComplexMap (f ≫ g) = limComplexMap f ≫ limComplexMap g := by
  apply E.isLimitLimComplexCone.hom_ext
  rintro ⟨n⟩
  -- The cone point is the named limit complex, as in the identity law.
  have h : limComplexMap (f ≫ g) ≫ E.limComplexπ n =
      (limComplexMap f ≫ limComplexMap g) ≫ E.limComplexπ n := by
    simp
  exact h

/-- The map of product complexes induced by a map of towers. -/
def productComplexMap (f : C ⟶ D) : C.productComplex ⟶ D.productComplex :=
  D.isLimitProductComplexFan.lift
    (Fan.mk C.productComplex fun n ↦ C.productComplexπ n ≫ f.app (op n))

/-- The induced product map commutes with every projection. -/
@[reassoc (attr := simp)]
theorem productComplexMap_comp_π (f : C ⟶ D) (n : ℕ) :
    productComplexMap f ≫ D.productComplexπ n = C.productComplexπ n ≫ f.app (op n) :=
  D.isLimitProductComplexFan.fac _ ⟨n⟩

@[simp]
theorem productComplexMap_id : productComplexMap (𝟙 C) = 𝟙 C.productComplex := by
  apply C.isLimitProductComplexFan.hom_ext
  rintro ⟨n⟩
  simp

@[simp]
theorem productComplexMap_comp (f : C ⟶ D) (g : D ⟶ E) :
    productComplexMap (f ≫ g) = productComplexMap f ≫ productComplexMap g := by
  apply E.isLimitProductComplexFan.hom_ext
  rintro ⟨n⟩
  simp

/-- The inclusion of the limit into the product is natural in the tower. -/
@[reassoc]
theorem limComplexι_naturality (f : C ⟶ D) :
    C.limComplexι ≫ productComplexMap f = limComplexMap f ≫ D.limComplexι := by
  apply D.isLimitProductComplexFan.hom_ext
  rintro ⟨n⟩
  simp

/-- The difference map on the product complex is natural in the tower. -/
@[reassoc]
theorem productComplexShift_naturality (f : C ⟶ D) :
    C.productComplexShift ≫ productComplexMap f =
      productComplexMap f ≫ D.productComplexShift := by
  apply D.isLimitProductComplexFan.hom_ext
  rintro ⟨n⟩
  simp only [Fan.mk_π_app, Category.assoc, productComplexMap_comp_π,
    productComplexShift_comp_productComplexπ, Preadditive.comp_sub,
    productComplexMap_comp_π_assoc]
  rw [← Category.assoc, productComplexShift_comp_productComplexπ, Preadditive.sub_comp,
    Category.assoc, f.naturality]

/-- A tower map induces a morphism of the inclusion-and-difference short complexes. -/
def shortComplexMap (f : C ⟶ D) : C.shortComplex ⟶ D.shortComplex :=
  ShortComplex.homMk (limComplexMap f) (productComplexMap f) (productComplexMap f)
    (limComplexι_naturality f).symm (productComplexShift_naturality f).symm

@[simp]
theorem shortComplexMap_τ₁ (f : C ⟶ D) : (shortComplexMap f).τ₁ = limComplexMap f := (rfl)

@[simp]
theorem shortComplexMap_τ₂ (f : C ⟶ D) : (shortComplexMap f).τ₂ = productComplexMap f := (rfl)

@[simp]
theorem shortComplexMap_τ₃ (f : C ⟶ D) : (shortComplexMap f).τ₃ = productComplexMap f := (rfl)

/-- The product-homology comparison is natural in maps of towers. -/
theorem productHomologyEquiv_naturality (f : C ⟶ D) (i : ι) :
    (D.productHomologyEquiv i).toLinearMap ∘ₗ
        (HomologicalComplex.homologyMap (productComplexMap f) i).hom =
      ModuleTower.productMap (Functor.whiskerRight f
        (HomologicalComplex.homologyFunctor _ c i)) ∘ₗ
          (C.productHomologyEquiv i).toLinearMap := by
  ext x n
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, productHomologyEquiv_apply,
    ModuleTower.productMap_apply, Functor.whiskerRight_app]
  simp only [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
    productComplexMap_comp_π]
  simp only [HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply,
    HomologicalComplex.homologyFunctor_map]
  rfl

/-- The map from homology of the limit to the limit of homology is natural, without
surjectivity assumptions on the towers. -/
theorem homologyToLim_naturality (f : C ⟶ D) (i : ι) :
    D.homologyToLim i ∘ₗ (HomologicalComplex.homologyMap (limComplexMap f) i).hom =
      ModuleTower.limMap (Functor.whiskerRight f
        (HomologicalComplex.homologyFunctor _ c i)) ∘ₗ C.homologyToLim i := by
  apply (D.homology i).lim_hom_ext
  intro n
  ext x
  simp only [LinearMap.comp_apply, ModuleTower.limπ_apply, coe_homologyToLim_apply,
    ModuleTower.coe_limMap_apply, ModuleTower.productMap_apply, Functor.whiskerRight_app]
  simp only [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
    limComplexMap_comp_π]
  simp only [HomologicalComplex.homologyMap_comp, ModuleCat.comp_apply,
    HomologicalComplex.homologyFunctor_map]
  rfl

/-- The connecting map from `lim¹` to limit-complex homology is natural for towers
whose difference maps on terms are surjective. -/
theorem limOneToHomology_naturality (f : C ⟶ D)
    (hC : ∀ i, Function.Surjective (C.term i).shift)
    (hD : ∀ i, Function.Surjective (D.term i).shift)
    {i j : ι} (hij : c.Rel i j) :
    (HomologicalComplex.homologyMap (limComplexMap f) j).hom ∘ₗ
        C.limOneToHomology hC hij =
      D.limOneToHomology hD hij ∘ₗ
        ModuleTower.limOneMap (Functor.whiskerRight f
          (HomologicalComplex.homologyFunctor _ c i)) := by
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, limOneToHomology_mk,
    ModuleTower.limOneMap_mk]
  have hδ := HomologicalComplex.HomologySequence.δ_naturality (shortComplexMap f)
    (C.shortComplex_shortExact hC) (D.shortComplex_shortExact hD) i j hij
  rw [shortComplexMap_τ₁, shortComplexMap_τ₃] at hδ
  -- The short-complex projections reduce to the product and limit complexes;
  -- `erw` also identifies the homology instances on these carriers.
  erw [← ModuleCat.comp_apply, hδ, ModuleCat.comp_apply]
  have hp : HomologicalComplex.homologyMap (productComplexMap f) i
        ((C.productHomologyEquiv i).symm x) =
      (D.productHomologyEquiv i).symm
        (ModuleTower.productMap (Functor.whiskerRight f
          (HomologicalComplex.homologyFunctor _ c i)) x) := by
    apply (D.productHomologyEquiv i).injective
    have hn := LinearMap.congr_fun (productHomologyEquiv_naturality f i)
      ((C.productHomologyEquiv i).symm x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hn
  exact congrArg ((D.shortComplex_shortExact hD).δ i j hij) hp

end TauCeti.ComplexTower
