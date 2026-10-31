/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Data.Matrix.Mul
public import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

/-!
# Coordinates and matrices for finite free sheaves of modules

Let `I` be a finite type and `X` a scheme. The free sheaf `𝒪_X^I` is the biproduct of `I`
copies of `𝒪_X` (`FiniteLocallyFreeSheaf.freeBicone`), so a global section `𝒪_X ⟶ 𝒪_X^I` is
the same as an `I`-indexed vector of global functions on `X`
(`FiniteLocallyFreeSheaf.unitHomFreeEquiv`): the `i`-th coordinate of a section is the global
function by which its `i`-th component, an endomorphism of `𝒪_X`, multiplies.

A matrix `A : Matrix J I Γ(X, ⊤)` defines the morphism `𝒪_X^I ⟶ 𝒪_X^J` sending the `i`-th basis
vector to the `i`-th column of `A` (`FiniteLocallyFreeSheaf.freeMatrixHom`). It acts on
coordinate vectors of global sections by `Matrix.mulVec`
(`FiniteLocallyFreeSheaf.unitHomFreeEquiv_comp_freeMatrixHom`), it turns matrix products into
composites (`FiniteLocallyFreeSheaf.freeMatrixHom_mul`), and its pullback along a morphism of
schemes `f : Y ⟶ X` is, through the identification `f^* 𝒪_X^I ≅ 𝒪_Y^I`, the morphism of the
matrix obtained by pulling back every entry of `A` along `f`
(`FiniteLocallyFreeSheaf.pullback_map_freeMatrixHom_comp_pullbackObjFreeIso_hom`).

These are the coordinate descriptions used for the geometric vector bundles of free sheaves,
which are affine spaces.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 5.
-/

public section

open CategoryTheory Limits MonoidalCategory Matrix

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry Scheme.Modules

variable {X : Scheme.{u}}

section Extensionality

variable {I : Type u} [Finite I]

/-- Morphisms out of the free sheaf `𝒪_X^I` agree when they agree on every basis section. -/
@[ext]
lemma free_obj_hom_ext {M : X.Modules} {f g : (free X I).obj ⟶ M}
    (h : ∀ i, SheafOfModules.ιFree i ≫ f = SheafOfModules.ιFree i ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) _ _ h

/-- Morphisms out of the free bundle `𝒪_X^I` agree when they agree on every basis section. -/
@[ext]
lemma free_hom_ext {E : FiniteLocallyFreeSheaf X} {f g : free X I ⟶ E}
    (h : ∀ i, SheafOfModules.ιFree i ≫ f.hom = SheafOfModules.ιFree i ≫ g.hom) : f = g :=
  ObjectProperty.hom_ext _ (free_obj_hom_ext h)

end Extensionality

section Coordinates

variable (X) (I : Type u) [Fintype I]

-- Reducible, with the cone point and inclusions given explicitly, so that its point is the free
-- sheaf `𝒪_X^I` itself and its inclusions are the basis inclusions, also for rewriting.
-- `TauCeti.SheafOfModules.biproductIsoFree` is stated over the site-level `ringCatSheaf X.sheaf`,
-- which is not reducibly `X.ringCatSheaf`, so its biproduct does not live in `X.Modules`.
/-- The free sheaf `𝒪_X^I` on a finite type `I`, as a bicone over `I` copies of `𝒪_X`: its
inclusions are the basis inclusions `SheafOfModules.ιFree` and its projections are the coordinate
projections. It is a biproduct (`FiniteLocallyFreeSheaf.isBilimitFreeBicone`). -/
abbrev freeBicone : Bicone (C := X.Modules) fun _ : I ↦ 𝟙_ X.Modules :=
  { Bicone.ofColimitCocone (C := X.Modules) (SheafOfModules.isColimitFreeCofan I) with
    pt := (free X I).obj
    ι := SheafOfModules.ιFree }

/-- The free sheaf on a finite type is the biproduct of copies of `𝒪_X`. -/
def isBilimitFreeBicone : (freeBicone X I).IsBilimit :=
  biconeIsBilimitOfColimitCoconeOfIsColimit (SheafOfModules.isColimitFreeCofan I)

variable {X} {I}

/-- The `j`-th component of `∑ i, v i • ιFree i` is multiplication by `v j`. -/
private lemma sum_comp_freeBicone_π (v : I → Γ(X, ⊤)) (j : I) :
    (∑ i, globalSectionsSmul (𝟙_ X.Modules) (v i) ≫ (freeBicone X I).ι i) ≫
        (freeBicone X I).π j =
      globalSectionsSmul _ (v j) := by
  rw [Preadditive.sum_comp, Finset.sum_eq_single j
    (fun i _ hij ↦ by rw [Category.assoc, Bicone.ι_π]; split; exacts [absurd ‹_› hij, comp_zero])
    (fun h ↦ absurd (Finset.mem_univ j) h), Category.assoc, Bicone.ι_π]
  split
  · rw [eqToHom_refl, Category.comp_id]
  · exact absurd rfl ‹_›

variable (X I) in
/-- **Coordinates of a global section of a free sheaf.** For a finite type `I`, global sections
`𝒪_X ⟶ 𝒪_X^I` of the free sheaf correspond additively to `I`-indexed vectors of global
functions. The `i`-th coordinate of a section `s` is the global function by which the endomorphism
`s ≫ π_i` of `𝒪_X` multiplies, and the vector `v` corresponds to the section
`∑ i, v i • ιFree i`. -/
def unitHomFreeEquiv : (𝟙_ X.Modules ⟶ (free X I).obj) ≃+ (I → Γ(X, ⊤)) where
  toFun s i := (globalSectionsActionRingEquiv (𝟙_ X.Modules)).symm
    (End.of (s ≫ (freeBicone X I).π i))
  invFun v := ∑ i, globalSectionsSmul (𝟙_ X.Modules) (v i) ≫ (freeBicone X I).ι i
  left_inv s := (isBilimitFreeBicone X I).isLimit.hom_ext fun ⟨j⟩ ↦
    (sum_comp_freeBicone_π _ j).trans (globalSectionsSmul_globalSectionsActionRingEquiv_symm _ _)
  right_inv v := funext fun j ↦
    (congrArg _ (congrArg End.of (sum_comp_freeBicone_π v j))).trans
      (globalSectionsActionRingEquiv_symm_globalSectionsSmul _ (v j))
  map_add' s t := funext fun i ↦ by
    rw [Pi.add_apply, Preadditive.add_comp]
    exact map_add (globalSectionsActionRingEquiv (𝟙_ X.Modules)).symm _ _

/-- The `i`-th coordinate of a global section `s` of `𝒪_X^I` is the global function by which the
`i`-th component `s ≫ π_i` multiplies. -/
lemma globalSectionsSmul_unitHomFreeEquiv_apply (s : 𝟙_ X.Modules ⟶ (free X I).obj) (i : I) :
    globalSectionsSmul _ (unitHomFreeEquiv X I s i) =
      s ≫ (freeBicone X I).π i :=
  globalSectionsSmul_globalSectionsActionRingEquiv_symm _ _

/-- The global section of `𝒪_X^I` with coordinate vector `v` is `∑ i, v i • ιFree i`. -/
lemma unitHomFreeEquiv_symm_apply (v : I → Γ(X, ⊤)) :
    (unitHomFreeEquiv X I).symm v =
      ∑ i, globalSectionsSmul (𝟙_ X.Modules) (v i) ≫ (freeBicone X I).ι i :=
  (rfl)

/-- The basis section `ιFree i` of `𝒪_X^I` has coordinate vector `Pi.single i 1`. -/
@[simp]
lemma unitHomFreeEquiv_ιFree [DecidableEq I] (i : I) :
    unitHomFreeEquiv X I (SheafOfModules.ιFree i) = Pi.single i 1 := by
  -- The basis inclusions are those of `freeBicone`, whose composites live in `X.Modules`.
  change unitHomFreeEquiv X I ((freeBicone X I).ι i) = _
  refine ((unitHomFreeEquiv X I).eq_symm_apply).1 ?_
  rw [unitHomFreeEquiv_symm_apply, Finset.sum_eq_single i
    (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, globalSectionsSmul_zero, zero_comp])
    (fun h ↦ absurd (Finset.mem_univ i) h), Pi.single_eq_same, globalSectionsSmul_one,
    Category.id_comp]

/-- Multiplying a global section of `𝒪_X^I` by a global function `r` multiplies its coordinate
vector by `r`. -/
@[simp]
lemma unitHomFreeEquiv_globalSectionsSmul_comp (r : Γ(X, ⊤))
    (s : 𝟙_ X.Modules ⟶ (free X I).obj) :
    unitHomFreeEquiv X I (globalSectionsSmul _ r ≫ s) = r • unitHomFreeEquiv X I s := by
  funext i
  refine (globalSectionsActionRingEquiv (𝟙_ X.Modules)).injective (End.ext ?_)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, End.mul_asHom, globalSectionsActionRingEquiv_apply,
    globalSectionsActionRingEquiv_apply, globalSectionsActionRingEquiv_apply,
    globalSectionsSmul_unitHomFreeEquiv_apply, globalSectionsSmul_unitHomFreeEquiv_apply]
  exact (Category.assoc _ _ _).trans (globalSectionsSmul_naturality _ r)

end Coordinates

section Matrix

variable {I J : Type u} [Fintype I] [Fintype J]

/-- The morphism of free sheaves `𝒪_X^I ⟶ 𝒪_X^J` with matrix `A : Matrix J I Γ(X, ⊤)`: it sends
the `i`-th basis vector `ιFree i` to the global section of `𝒪_X^J` whose coordinates are the
`i`-th column of `A`. -/
def freeMatrixHom (A : Matrix J I Γ(X, ⊤)) : free X I ⟶ free X J :=
  ObjectProperty.homMk <| Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan I) fun i ↦
    (unitHomFreeEquiv X J).symm fun j ↦ A j i

/-- The morphism with matrix `A` sends the `i`-th basis vector to the `i`-th column of `A`. -/
@[simp, reassoc]
lemma ιFree_freeMatrixHom (A : Matrix J I Γ(X, ⊤)) (i : I) :
    SheafOfModules.ιFree i ≫ (freeMatrixHom A).hom = (unitHomFreeEquiv X J).symm fun j ↦ A j i :=
  Cofan.IsColimit.fac _ _ i

/-- **Matrices act on coordinates.** Composing a global section of `𝒪_X^I` with the morphism of
matrix `A` multiplies its coordinate vector by `A`. -/
@[simp]
lemma unitHomFreeEquiv_comp_freeMatrixHom (A : Matrix J I Γ(X, ⊤))
    (s : 𝟙_ X.Modules ⟶ (free X I).obj) :
    unitHomFreeEquiv X J (s ≫ (freeMatrixHom A).hom) = A *ᵥ unitHomFreeEquiv X I s := by
  obtain ⟨v, rfl⟩ := (unitHomFreeEquiv X I).symm.surjective s
  -- The basis vector `i` scaled by `v i` is sent to the `i`-th column of `A` scaled by `v i`.
  have h (i : I) : unitHomFreeEquiv X J
      ((globalSectionsSmul (𝟙_ X.Modules) (v i) ≫ (freeBicone X I).ι i) ≫ (freeMatrixHom A).hom) =
        v i • fun j ↦ A j i := by
    rw [Category.assoc, show (freeBicone X I).ι i ≫ (freeMatrixHom A).hom = _ from
      ιFree_freeMatrixHom A i, unitHomFreeEquiv_globalSectionsSmul_comp, AddEquiv.apply_symm_apply]
  rw [AddEquiv.apply_symm_apply, unitHomFreeEquiv_symm_apply, Preadditive.sum_comp, map_sum]
  simp only [h]
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, mul_comm]

/-- The morphism of free sheaves with the identity matrix is the identity. -/
@[simp]
lemma freeMatrixHom_one [DecidableEq I] :
    freeMatrixHom (1 : Matrix I I Γ(X, ⊤)) = 𝟙 _ :=
  -- Composites with Mathlib's `ιFree` are not reducibly composites in `X.Modules`, so they are
  -- rewritten by `Eq.trans` rather than `rw`.
  free_hom_ext fun i ↦ (ιFree_freeMatrixHom 1 i).trans <| ((unitHomFreeEquiv X I).symm_apply_eq.2 <|
    (funext fun j ↦ by simp [Matrix.one_apply, Pi.single_apply, eq_comm]).trans
      (unitHomFreeEquiv_ιFree i).symm).trans (Category.comp_id _).symm

/-- The morphism of free sheaves with matrix `A * B` is the composite of those with matrices `B`
and `A`. -/
lemma freeMatrixHom_mul {K : Type u} [Fintype K] (A : Matrix K J Γ(X, ⊤))
    (B : Matrix J I Γ(X, ⊤)) :
    freeMatrixHom (A * B) = freeMatrixHom B ≫ freeMatrixHom A :=
  free_hom_ext fun i ↦ (ιFree_freeMatrixHom (A * B) i).trans <|
    ((unitHomFreeEquiv X K).symm_apply_eq.2 <|
      (funext fun k ↦ by simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]).trans
        ((unitHomFreeEquiv_comp_freeMatrixHom A _).trans
          (congrArg (A *ᵥ ·) ((unitHomFreeEquiv X J).apply_symm_apply _))).symm).trans
      (ιFree_freeMatrixHom_assoc B i (freeMatrixHom A).hom).symm

end Matrix

section Pullback

variable {Y : Scheme.{u}} (f : Y ⟶ X) {I J : Type u}

-- Mathlib's pullback of free sheaves is stated for pushforwards known to be right adjoints; the
-- adjunction is recorded for `Scheme.Modules.pushforward`, which instance search does not unfold.
local instance : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint

/-- **Pullback of a morphism of free sheaves with a matrix.** Through the identifications
`f^* 𝒪_X^I ≅ 𝒪_Y^I` and `f^* 𝒪_X^J ≅ 𝒪_Y^J`, the pullback along `f : Y ⟶ X` of the morphism with
matrix `A` is the morphism whose matrix is obtained by pulling back every entry of `A` along
`f`. -/
lemma pullback_map_freeMatrixHom_comp_pullbackObjFreeIso_hom [Fintype I] [Fintype J]
    (A : Matrix J I Γ(X, ⊤)) :
    (Scheme.Modules.pullback f).map (freeMatrixHom A).hom ≫
        (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom J).hom =
      (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).hom ≫
        (freeMatrixHom (A.map f.appTop)).hom := by
  let u := pullbackObjUnitIso f
  refine (Iso.inv_comp_eq _).1 (free_obj_hom_ext fun i ↦ ?_)
  refine Eq.trans ?_ (ιFree_freeMatrixHom (A.map f.appTop) i).symm
  refine ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (ιFree_pullbackObjFreeIso_inv f i))).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (u.inv ≫ ·)
    ((Functor.map_comp_assoc _ _ _ _).symm.trans (congrArg
      (fun t ↦ (Scheme.Modules.pullback f).map t ≫ _) (ιFree_freeMatrixHom A i)))).trans ?_)
  rw [unitHomFreeEquiv_symm_apply, unitHomFreeEquiv_symm_apply, Functor.map_sum]
  -- The sums are formed in `Y.Modules`, where the free sheaf `𝒪_Y^J` has its additive structure.
  exact (congrArg (u.inv ≫ ·)
    (Preadditive.sum_comp (C := Y.Modules) (R := (free Y J).obj) _ _ _)).trans
    ((Preadditive.comp_sum (C := Y.Modules) (R := (free Y J).obj) _ _ _).trans
      (Finset.sum_congr rfl fun j _ ↦ (congrArg (u.inv ≫ ·)
        (pullback_map_globalSectionsSmul_comp_ιFree_comp_pullbackObjFreeIso_hom f (A j i) j)).trans
          (Iso.inv_hom_id_assoc u _)))

end Pullback

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
