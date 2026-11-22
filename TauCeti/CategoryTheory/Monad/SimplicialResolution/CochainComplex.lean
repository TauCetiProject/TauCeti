/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monad.SimplicialResolution.Augmented
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.BigOperators

/-!
# The cochain complex of a comonad

Let `G` be a comonad on an `R`-linear category `C`, and let `X Y : C`. Applying the
contravariant functor `Hom (-, Y)` to the augmented simplicial resolution of `X` gives an
augmented cosimplicial `R`-module with `Hom (G^(n+1) X, Y)` in degree `n` and augmentation
object `Hom (X, Y)`: `Comonad.homAugmentedResolution`. Its alternating coface map complex
is the comonad cochain complex `Comonad.cochainComplex`, whose differential in degree `n` is

  `f ↦ ∑ i : Fin (n + 2), (-1) ^ i • (d_i ≫ f)`,

with `d_i` the counit applied at position `i`, counted from the outermost layer
(`Comonad.cochainComplex_d_apply`). The augmentation is precomposition with the counit
`G X ⟶ X` (`Comonad.homAugmentedResolution_hom_app_zero_apply`). Both constructions are
functors of `X : Cᵒᵖ` and `Y : C`, acting by precomposition with `G^(n+1)` of a morphism and
by postcomposition respectively.

The comonad need not be additive: precomposition with any morphism is `R`-linear.

For the identity comonad every face is an identity, so the differential vanishes in even
degrees and is the identity in odd degrees (`Comonad.id_cochainComplex_d_apply`).

The cochain complex is the alternating coface map complex of an augmented cosimplicial object,
rather than `Hom (-, Y)` applied to the alternating face map complex of the resolution, so that
extra codegeneracies of the augmented cosimplicial object, such as the image under `Hom (-, Y)`
of an extra degeneracy of the resolution, contract it directly. Contracting this complex when
`X` is projective relative to `G` is the vanishing theorem for comonad cohomology.

## Main definitions

* `CategoryTheory.Comonad.homAugmentedResolution G R`: the bifunctor
  `Cᵒᵖ ⥤ C ⥤ CosimplicialObject.Augmented (ModuleCat R)` sending `X`, `Y` to
  `Hom (-, Y)` applied to the augmented resolution of `X`.
* `CategoryTheory.Comonad.cochainComplex G R`: the bifunctor
  `Cᵒᵖ ⥤ C ⥤ CochainComplex (ModuleCat R) ℕ` of comonad cochains.

## References

* M. Barr and J. Beck, *Homology and standard constructions*, in *Seminar on Triples and
  Categorical Homology Theory*, Lecture Notes in Math. 80, Springer, 1969, §1.
* A. M. Gainutdinov, J. Haferkamp and C. Schweigert, *Davydov–Yetter cohomology, comonads and
  Ocneanu rigidity*, Adv. Math. 414 (2023), arXiv:1910.06094, Definition 2.8.
-/

public noncomputable section

open CategoryTheory Opposite AlgebraicTopology

namespace CategoryTheory.Comonad

universe w v u

variable {C : Type u} [Category.{v} C] (G : Comonad C)
variable (R : Type w) [Ring R] [Preadditive C] [Linear R C]

/-- `Hom (-, Y)` applied to the augmented simplicial resolution of `X`, as a functor of
`X : Cᵒᵖ` and `Y : C`. In degree `n` it is `Hom (G^(n+1) X, Y)`, its cofaces precompose with
the counits of the resolution, and its augmentation object is `Hom (X, Y)`.
The body is exposed so its terms compute to these `Hom` modules in dependent statements. -/
@[expose] def homAugmentedResolution :
    Cᵒᵖ ⥤ C ⥤ CosimplicialObject.Augmented (ModuleCat.{v} R) :=
  (linearYoneda R C ⋙ CosimplicialObject.Augmented.whiskering Cᵒᵖ (ModuleCat.{v} R) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (G.augmentedSimplicialResolution.op ⋙ simplicialToCosimplicialAugmented C)).flip

/-- The comonad cochain complex, as a functor of `X : Cᵒᵖ` and `Y : C`: the alternating coface
map complex of `Comonad.homAugmentedResolution`, with `Hom (G^(n+1) X, Y)` in degree `n`.
The body is exposed so its terms compute to these `Hom` modules in dependent statements. -/
@[expose] def cochainComplex : Cᵒᵖ ⥤ C ⥤ CochainComplex (ModuleCat.{v} R) ℕ :=
  G.homAugmentedResolution R ⋙ (Functor.whiskeringRight _ _ _).obj
    (CosimplicialObject.Augmented.drop ⋙ alternatingCofaceMapComplex _)

variable {R}

section homAugmentedResolution

variable (X Y : C)

@[simp] lemma homAugmentedResolution_left :
    (((G.homAugmentedResolution R).obj (op X)).obj Y).left = ModuleCat.of R (X ⟶ Y) := (rfl)

@[simp] lemma homAugmentedResolution_right_obj (n : ℕ) :
    (((G.homAugmentedResolution R).obj (op X)).obj Y).right.obj (SimplexCategory.mk n) =
      ModuleCat.of R ((G.resolutionStage (n + 1)).obj X ⟶ Y) := (rfl)

/-- The augmentation in degree `n` precomposes with the collapse of all `n + 1` layers. -/
lemma homAugmentedResolution_hom_app_apply (n : ℕ) (f : X ⟶ Y) :
    ((((G.homAugmentedResolution R).obj (op X)).obj Y).hom.app (SimplexCategory.mk n)).hom f =
      (G.resolutionCounit (n + 1)).app X ≫ f :=
  -- The augmentation is `Hom (-, Y)` applied to that of the resolution, by unfolding.
  (rfl : _ = (G.simplicialResolutionAugmentation X).app (op (SimplexCategory.mk n)) ≫ f).trans
    (congrArg (· ≫ f) (G.simplicialResolutionAugmentation_app X n))

/-- The augmentation in degree `0` precomposes with the counit `G X ⟶ X`. -/
lemma homAugmentedResolution_hom_app_zero_apply (f : X ⟶ Y) :
    ((((G.homAugmentedResolution R).obj (op X)).obj Y).hom.app (SimplexCategory.mk 0)).hom f =
      G.ε.app X ≫ f :=
  (rfl : _ = (G.simplicialResolutionAugmentation X).app (op (SimplexCategory.mk 0)) ≫ f).trans
    (congrArg (· ≫ f) (G.simplicialResolutionAugmentation_app_zero X))

/-- The `i`th coface precomposes with the counit applied at position `i`. -/
@[simp] lemma homAugmentedResolution_right_δ_apply {n : ℕ} (i : Fin (n + 2))
    (f : (G.resolutionStage (n + 1)).obj X ⟶ Y) :
    ((((G.homAugmentedResolution R).obj (op X)).obj Y).right.δ i).hom f =
      (G.resolutionFace (n + 1) i).app X ≫ f :=
  -- The coface is `Hom (-, Y)` applied to the face of the resolution, by unfolding.
  (rfl : _ = (G.simplicialResolution.obj X).δ i ≫ f).trans
    (congrArg (· ≫ f) (G.simplicialResolution_δ X i))

/-- The `i`th codegeneracy precomposes with the comultiplication applied at position `i`. -/
@[simp] lemma homAugmentedResolution_right_σ_apply {n : ℕ} (i : Fin (n + 1))
    (f : (G.resolutionStage (n + 2)).obj X ⟶ Y) :
    ((((G.homAugmentedResolution R).obj (op X)).obj Y).right.σ i).hom f =
      (G.resolutionDegeneracy n i).app X ≫ f :=
  -- The codegeneracy is `Hom (-, Y)` applied to the degeneracy of the resolution, by unfolding.
  (rfl : _ = (G.simplicialResolution.obj X).σ i ≫ f).trans
    (congrArg (· ≫ f) (G.simplicialResolution_σ X i))

/-- A morphism `Y ⟶ Y'` acts on the augmentation object by postcomposition. -/
@[simp] lemma homAugmentedResolution_obj_map_left_apply {Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y) :
    (((G.homAugmentedResolution R).obj (op X)).map g).left.hom f = f ≫ g := (rfl)

/-- A morphism `Y ⟶ Y'` acts on cochains by postcomposition. -/
@[simp] lemma homAugmentedResolution_obj_map_right_app_apply {Y Y' : C} (g : Y ⟶ Y') (n : ℕ)
    (f : (G.resolutionStage (n + 1)).obj X ⟶ Y) :
    ((((G.homAugmentedResolution R).obj (op X)).map g).right.app
      (SimplexCategory.mk n)).hom f = f ≫ g := (rfl)

/-- A morphism `X' ⟶ X` acts on the augmentation object by precomposition. -/
@[simp] lemma homAugmentedResolution_map_app_left_apply {X' : C} (h : X' ⟶ X) (f : X ⟶ Y) :
    (((G.homAugmentedResolution R).map h.op).app Y).left.hom f = h ≫ f := (rfl)

/-- A morphism `h : X' ⟶ X` acts on cochains of degree `n` by precomposition with
`G^(n+1) h`. -/
@[simp] lemma homAugmentedResolution_map_app_right_app_apply {X' : C} (h : X' ⟶ X) (n : ℕ)
    (f : (G.resolutionStage (n + 1)).obj X ⟶ Y) :
    ((((G.homAugmentedResolution R).map h.op).app Y).right.app
      (SimplexCategory.mk n)).hom f = (G.resolutionStage (n + 1)).map h ≫ f := (rfl)

end homAugmentedResolution

section cochainComplex

variable (X Y : C)

@[simp] lemma cochainComplex_X (n : ℕ) :
    (((G.cochainComplex R).obj (op X)).obj Y).X n =
      ModuleCat.of R ((G.resolutionStage (n + 1)).obj X ⟶ Y) := (rfl)

/-- The comonad differential is the alternating sum of the precompositions with the counit
applied at each position. -/
lemma cochainComplex_d_apply (n : ℕ) (f : (G.resolutionStage (n + 1)).obj X ⟶ Y) :
    ((((G.cochainComplex R).obj (op X)).obj Y).d n (n + 1)).hom f =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ((G.resolutionFace (n + 1) i).app X ≫ f) := by
  let K := (((G.homAugmentedResolution R).obj (op X)).obj Y).right
  have hd : (((G.cochainComplex R).obj (op X)).obj Y).d n (n + 1) =
      AlternatingCofaceMapComplex.objD K n :=
    CochainComplex.of_d (fun n ↦ K.obj (SimplexCategory.mk n))
      (AlternatingCofaceMapComplex.objD K) n
  have hK (x : K.obj (SimplexCategory.mk n)) : (AlternatingCofaceMapComplex.objD K n).hom x =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (K.δ i).hom x := by
    simp only [AlternatingCofaceMapComplex.objD, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply]
  rw [hd]
  exact (hK f).trans (Finset.sum_congr rfl fun i _ ↦
    congrArg _ (G.homAugmentedResolution_right_δ_apply X Y i f))

/-- A morphism `Y ⟶ Y'` acts on cochains by postcomposition. -/
@[simp] lemma cochainComplex_obj_map_f_apply {Y Y' : C} (g : Y ⟶ Y') (n : ℕ)
    (f : (G.resolutionStage (n + 1)).obj X ⟶ Y) :
    ((((G.cochainComplex R).obj (op X)).map g).f n).hom f = f ≫ g := (rfl)

/-- A morphism `h : X' ⟶ X` acts on cochains of degree `n` by precomposition with
`G^(n+1) h`. -/
@[simp] lemma cochainComplex_map_app_f_apply {X' : C} (h : X' ⟶ X) (n : ℕ)
    (f : (G.resolutionStage (n + 1)).obj X ⟶ Y) :
    ((((G.cochainComplex R).map h.op).app Y).f n).hom f =
      (G.resolutionStage (n + 1)).map h ≫ f := (rfl)

end cochainComplex

section id

variable (C) (R)

/-- For the identity comonad, the comonad differential vanishes in even degrees and is the
identity in odd degrees. -/
lemma id_cochainComplex_d_apply (X Y : C) (n : ℕ)
    (f : ((Comonad.id C).resolutionStage (n + 1)).obj X ⟶ Y) :
    (((((Comonad.id C).cochainComplex R).obj (op X)).obj Y).d n (n + 1)).hom f =
      if Even n then 0 else f := by
  rw [cochainComplex_d_apply]
  simp only [id_resolutionFace_app]
  rw [← Finset.sum_smul, Fin.sum_neg_one_pow ℤ (n + 2)]
  have h₂ : Even (n + 2) ↔ Even n := by simp [Nat.even_add]
  -- The remaining identity morphisms and zeros live on iterates of the identity comonad,
  -- whose objects are `X` by definition, so they are closed by explicit terms.
  by_cases h : Even n
  · simp only [h, h₂.2 h, ↓reduceIte]
    exact zero_smul ℤ _
  · simp only [h, mt h₂.1 h, ↓reduceIte, one_smul]
    exact Category.id_comp f

end id

end CategoryTheory.Comonad
