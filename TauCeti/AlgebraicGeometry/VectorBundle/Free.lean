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
(`FiniteLocallyFreeSheaf.pullback_map_freeMatrixHom`).

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

section Coordinates

variable (X) (I : Type u) [Fintype I]

-- Reducible, with the cone point and inclusions given explicitly, so that its point is the free
-- sheaf `𝒪_X^I` itself and its inclusions are the basis inclusions, also for rewriting.
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

-- `SheafOfModules.isInvertible_unit` is stated for `SheafOfModules.unit`, which instance search
-- does not identify with the monoidal unit `𝟙_ X.Modules`.
private instance : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (𝟙_ X.Modules) :=
  TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_unit X

/-- The global function by which an endomorphism of `𝒪_X` multiplies. Every endomorphism of the
invertible sheaf `𝒪_X` is multiplication by a unique global function. -/
private def unitEndScalar (e : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) : Γ(X, ⊤) :=
  (globalSectionsActionRingEquiv (𝟙_ X.Modules)).symm (End.of e)

private lemma globalSectionsSmul_unitEndScalar (e : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    globalSectionsSmul _ (unitEndScalar e) = e :=
  globalSectionsSmul_globalSectionsActionRingEquiv_symm _ e

private lemma unitEndScalar_globalSectionsSmul (r : Γ(X, ⊤)) :
    unitEndScalar (globalSectionsSmul (𝟙_ X.Modules) r) = r :=
  ((globalSectionsActionRingEquiv (𝟙_ X.Modules)).symm_apply_eq).2
    (globalSectionsActionRingEquiv_apply _ r).symm

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
  toFun s i := unitEndScalar (s ≫ (freeBicone X I).π i)
  invFun v := ∑ i, globalSectionsSmul (𝟙_ X.Modules) (v i) ≫ (freeBicone X I).ι i
  left_inv s := (isBilimitFreeBicone X I).isLimit.hom_ext fun ⟨j⟩ ↦
    (sum_comp_freeBicone_π _ j).trans (globalSectionsSmul_unitEndScalar _)
  right_inv v := funext fun j ↦
    (congrArg unitEndScalar (sum_comp_freeBicone_π v j)).trans
      (unitEndScalar_globalSectionsSmul (v j))
  map_add' s t := funext fun i ↦ by
    rw [Pi.add_apply, Preadditive.add_comp]
    exact map_add (globalSectionsActionRingEquiv (𝟙_ X.Modules)).symm _ _

/-- The `i`-th coordinate of a global section `s` of `𝒪_X^I` is the global function by which the
`i`-th component `s ≫ π_i` multiplies. -/
lemma globalSectionsSmul_unitHomFreeEquiv_apply (s : 𝟙_ X.Modules ⟶ (free X I).obj) (i : I) :
    globalSectionsSmul _ (unitHomFreeEquiv X I s i) = s ≫ (freeBicone X I).π i :=
  globalSectionsSmul_unitEndScalar _

/-- The global section of `𝒪_X^I` with coordinate vector `v` is `∑ i, v i • ιFree i`. -/
lemma unitHomFreeEquiv_symm_apply (v : I → Γ(X, ⊤)) :
    (unitHomFreeEquiv X I).symm v =
      ∑ i, globalSectionsSmul (𝟙_ X.Modules) (v i) ≫ (freeBicone X I).ι i :=
  (rfl)

-- Not a simp lemma: `simp` unfolds the reducible `freeBicone` on its left-hand side.
/-- The basis section `ιFree i` of `𝒪_X^I` has coordinate vector `Pi.single i 1`. -/
lemma unitHomFreeEquiv_ι [DecidableEq I] (i : I) :
    unitHomFreeEquiv X I ((freeBicone X I).ι i) = Pi.single i 1 := by
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
        v i • fun j ↦ A j i :=
    (congrArg (unitHomFreeEquiv X J) ((Category.assoc _ _ _).trans
      (congrArg (globalSectionsSmul _ (v i) ≫ ·) (ιFree_freeMatrixHom A i)))).trans
      ((unitHomFreeEquiv_globalSectionsSmul_comp _ _).trans
        (congrArg (v i • ·) ((unitHomFreeEquiv X J).apply_symm_apply _)))
  rw [AddEquiv.apply_symm_apply, unitHomFreeEquiv_symm_apply, Preadditive.sum_comp, map_sum]
  refine (Finset.sum_congr rfl fun i _ ↦ h i).trans (funext fun j ↦ ?_)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, mul_comm]

/-- The morphism of free sheaves with the identity matrix is the identity. -/
@[simp]
lemma freeMatrixHom_one [DecidableEq I] :
    freeMatrixHom (1 : Matrix I I Γ(X, ⊤)) = 𝟙 _ :=
  ObjectProperty.hom_ext _ <| Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) _ _
    fun i ↦ (ιFree_freeMatrixHom 1 i).trans <| ((unitHomFreeEquiv X I).symm_apply_eq.2 <|
      (funext fun j ↦ by simp [Matrix.one_apply, Pi.single_apply, eq_comm]).trans
        (unitHomFreeEquiv_ι i).symm).trans (Category.comp_id _).symm

/-- The morphism of free sheaves with matrix `A * B` is the composite of those with matrices `B`
and `A`. -/
lemma freeMatrixHom_mul {K : Type u} [Fintype K] (A : Matrix K J Γ(X, ⊤))
    (B : Matrix J I Γ(X, ⊤)) :
    freeMatrixHom (A * B) = freeMatrixHom B ≫ freeMatrixHom A :=
  ObjectProperty.hom_ext _ <| Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) _ _
    fun i ↦ (ιFree_freeMatrixHom (A * B) i).trans <|
      ((unitHomFreeEquiv X K).symm_apply_eq.2 <|
        (funext fun k ↦ by simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]).trans
          ((unitHomFreeEquiv_comp_freeMatrixHom A _).trans
            (congrArg (A *ᵥ ·) ((unitHomFreeEquiv X J).apply_symm_apply _))).symm).trans
        (ιFree_freeMatrixHom_assoc B i (freeMatrixHom A).hom).symm

end Matrix

section Pullback

variable {Y : Scheme.{u}} (f : Y ⟶ X) {I J : Type u} [Fintype I] [Fintype J]

/-- **Pullback of a morphism of free sheaves with a matrix.** Through the identifications
`f^* 𝒪_X^I ≅ 𝒪_Y^I` and `f^* 𝒪_X^J ≅ 𝒪_Y^J`, the pullback along `f : Y ⟶ X` of the morphism with
matrix `A` is the morphism whose matrix is obtained by pulling back every entry of `A` along
`f`. -/
lemma pullback_map_freeMatrixHom (A : Matrix J I Γ(X, ⊤)) :
    letI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
    (Scheme.Modules.pullback f).map (freeMatrixHom A).hom ≫
        (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom J).hom =
      (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).hom ≫
        (freeMatrixHom (A.map f.appTop)).hom := by
  let : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let u := pullbackObjUnitIso f
  -- The basis vector `ιFree i` of `𝒪_Y^I` is the pullback of that of `𝒪_X^I`.
  have hι (i : I) : (freeBicone Y I).ι i ≫
      (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).inv =
        u.inv ≫ (Scheme.Modules.pullback f).map ((freeBicone X I).ι i) :=
    (Iso.comp_inv_eq _).2 ((Category.assoc _ _ _).trans ((congrArg (u.inv ≫ ·)
      (SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ i)).trans
        (by rw [← pullbackObjUnitIso_hom]; exact Iso.inv_hom_id_assoc u _))).symm
  -- Pulling back the basis vector `j` scaled by `r` gives the basis vector `j` scaled by `f^♯ r`.
  have hsmul (r : Γ(X, ⊤)) (j : J) :
      (Scheme.Modules.pullback f).map (globalSectionsSmul (𝟙_ X.Modules) r ≫
          (freeBicone X J).ι j) ≫ (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom J).hom =
        u.hom ≫ globalSectionsSmul (𝟙_ Y.Modules) (f.appTop r) ≫ (freeBicone Y J).ι j := by
    refine (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans ?_)
    refine (congrArg (_ ≫ ·)
      (SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ j)).trans ?_
    rw [pullback_map_globalSectionsSmul, ← pullbackObjUnitIso_hom]
    exact globalSectionsSmul_naturality_assoc u.hom _ _
  refine (Iso.inv_comp_eq _).1 (Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) _ _
    fun i ↦ ?_)
  refine Eq.trans ?_ (ιFree_freeMatrixHom (A.map f.appTop) i).symm
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (hι i))).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (u.inv ≫ ·)
    ((Functor.map_comp_assoc _ _ _ _).symm.trans (congrArg
      (fun t ↦ (Scheme.Modules.pullback f).map t ≫ _) (ιFree_freeMatrixHom A i)))).trans ?_)
  rw [unitHomFreeEquiv_symm_apply, unitHomFreeEquiv_symm_apply, Functor.map_sum]
  -- The sums are formed in `Y.Modules`, where the free sheaf `𝒪_Y^J` has its additive structure.
  exact (congrArg (u.inv ≫ ·)
    (Preadditive.sum_comp (C := Y.Modules) (R := (free Y J).obj) _ _ _)).trans
    ((Preadditive.comp_sum (C := Y.Modules) (R := (free Y J).obj) _ _ _).trans
      (Finset.sum_congr rfl fun j _ ↦
        (congrArg (u.inv ≫ ·) (hsmul (A j i) j)).trans (Iso.inv_hom_id_assoc u _)))

end Pullback

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
