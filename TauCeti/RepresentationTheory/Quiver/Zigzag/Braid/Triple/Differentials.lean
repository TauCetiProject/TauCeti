/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Triple.Terms
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.TensorEvaluation
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Coproducts
public import Mathlib.Algebra.Homology.BifunctorAssociator

/-!
# Signed differentials of triple zigzag braid products

The actual left-associated totalization evaluates each of its three factors.
The lowest differential has signs `+,-,+`, while the next differential evaluates
one of each pair with the signs determined by its cohomological position.
These are the differential blocks used in the adjacent braid cancellation.
-/

public section
noncomputable section
namespace TauCeti
open CategoryTheory CategoryTheory.Limits
universe u w
variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
attribute [local instance] zigzagAlgebraIntegerGradedAlgebra
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "T" => GradedModuleCat.bimoduleTensorObj Γ Γ Γ
local notation "F" => zigzagBimoduleTensor k G
local notation "B" => zigzagBraidComplex k G
local notation "E" => zigzagBraidEvaluationHom k G
local notation "L" => zigzagBraidTensorEvaluationLeft k G
local notation "R" => zigzagBraidTensorEvaluationRight k G
local notation "c" => ComplexShape.up ℤ
local notation "M" => GradedModuleCat.bimoduleTensorMap Γ Γ Γ
local notation "I₀" => zigzagBraidComplexXIso₀ k G
local notation "I₁" => zigzagBraidComplexXIso₁ k G

/-- The signed three-factor evaluation from the triple tensor to its three pair terms. -/
def zigzagBraidTripleFirstDifferential (i j l : V) :
    T (T (U i) (U j)) (U l) ⟶ T (U i) (U j) ⊞ (T (U i) (U l) ⊞ T (U j) (U l)) :=
  biprod.lift
    (GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (T (U i) (U j))) (E l) ≫
      (zigzagBimoduleRightUnitor k G (T (U i) (U j))).hom)
    (biprod.lift (-GradedModuleCat.bimoduleTensorMap Γ Γ Γ (R i j) (𝟙 (U l)))
      (GradedModuleCat.bimoduleTensorMap Γ Γ Γ (L i j) (𝟙 (U l))))

/-- Evaluating the third factor gives the first pair component. -/
@[simp, reassoc]
theorem zigzagBraidTripleFirstDifferential_fst (i j l : V) :
    zigzagBraidTripleFirstDifferential k G i j l ≫ biprod.fst =
      M (𝟙 (T (U i) (U j))) (E l) ≫
        (zigzagBimoduleRightUnitor k G (T (U i) (U j))).hom := by
  simp only [zigzagBraidTripleFirstDifferential, biprod.lift_fst]

/-- Evaluating the middle factor gives the negative of the second pair component. -/
@[simp, reassoc]
theorem zigzagBraidTripleFirstDifferential_snd_fst (i j l : V) :
    zigzagBraidTripleFirstDifferential k G i j l ≫ biprod.snd ≫ biprod.fst =
      -M (R i j) (𝟙 (U l)) := by
  simp only [zigzagBraidTripleFirstDifferential, biprod.lift_snd_assoc, biprod.lift_fst]

/-- Evaluating the first factor gives the third pair component. -/
@[simp, reassoc]
theorem zigzagBraidTripleFirstDifferential_snd_snd (i j l : V) :
    zigzagBraidTripleFirstDifferential k G i j l ≫ biprod.snd ≫ biprod.snd =
      M (L i j) (𝟙 (U l)) := by
  simp only [zigzagBraidTripleFirstDifferential, biprod.lift_snd_assoc, biprod.lift_snd]

/-- The signed pair evaluations from three pair terms to three vertex terms. -/
def zigzagBraidTripleSecondDifferential (i j l : V) :
    T (U i) (U j) ⊞ (T (U i) (U l) ⊞ T (U j) (U l)) ⟶ (U i ⊞ U j) ⊞ U l :=
  Biprod.ofComponents (biprod.lift (-R i j) (L i j)) 0
    (Biprod.ofComponents (-R i l) 0 0 (-R j l)) (biprod.desc (L i l) (L j l))

/-- The first pair evaluates to the first two vertex components. -/
@[simp, reassoc]
theorem zigzagBraidTripleSecondDifferential_inl (i j l : V) :
    biprod.inl ≫ zigzagBraidTripleSecondDifferential k G i j l =
      biprod.lift (biprod.lift (-R i j) (L i j)) 0 := by
  apply biprod.hom_ext <;> simp [zigzagBraidTripleSecondDifferential]

/-- The second pair evaluates to the first and third vertex components. -/
@[simp, reassoc]
theorem zigzagBraidTripleSecondDifferential_inl_inr (i j l : V) :
    biprod.inl ≫ biprod.inr ≫ zigzagBraidTripleSecondDifferential k G i j l =
      biprod.lift (biprod.lift (-R i l) 0) (L i l) := by
  apply biprod.hom_ext
  · apply biprod.hom_ext <;> simp [zigzagBraidTripleSecondDifferential]
  · simp [zigzagBraidTripleSecondDifferential]

/-- The third pair evaluates to the second and third vertex components. -/
@[simp, reassoc]
theorem zigzagBraidTripleSecondDifferential_inr_inr (i j l : V) :
    biprod.inr ≫ biprod.inr ≫ zigzagBraidTripleSecondDifferential k G i j l =
      biprod.lift (biprod.lift 0 (-R j l)) (L j l) := by
  apply biprod.hom_ext
  · apply biprod.hom_ext <;> simp [zigzagBraidTripleSecondDifferential]
  · simp [zigzagBraidTripleSecondDifferential]

@[reassoc]
private theorem tripleLowestInclusion_d (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) (-1) (-1) (-3) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-3) (-2) =
    ((F).map (((F).map ((B i).d (-1) 0)).app ((B j).X (-1)))).app ((B l).X (-1)) ≫
        HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
          0 (-1) (-1) (-2) (by norm_num [ComplexShape.r]) -
      ((F).map (((F).obj ((B i).X (-1))).map ((B j).d (-1) 0))).app ((B l).X (-1)) ≫
        HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
          (-1) 0 (-1) (-2) (by norm_num [ComplexShape.r]) +
      ((F).obj (((F).obj ((B i).X (-1))).obj ((B j).X (-1)))).map ((B l).d (-1) 0) ≫
        HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
          (-1) (-1) 0 (-2) (by norm_num [ComplexShape.r]) := by
  rw [HomologicalComplex.mapBifunctor₁₂.d_eq]
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor₁₂.ι_D₁,
    HomologicalComplex.mapBifunctor₁₂.ι_D₂, HomologicalComplex.mapBifunctor₁₂.ι_D₃]
  rw [sub_eq_add_neg]
  congr 1
  · congr 1
    · rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq F F (B i) (B j) (B l) c c
        (by simp : (c).Rel (-1) 0) (-1) (-1) (-2)]
      simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r,
        ComplexShape.ε₁]
    · rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq F F (B i) (B j) (B l) c c (-1)
        (by simp : (c).Rel (-1) 0) (-1) (-2)]
      simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r,
        ComplexShape.ε₁, ComplexShape.ε₂]
  · rw [HomologicalComplex.mapBifunctor₁₂.d₃_eq F F (B i) (B j) (B l) c c (-1) (-1)
      (by simp : (c).Rel (-1) 0) (-2)]
    simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r,
      ComplexShape.ε₂]
    norm_num [Int.negOnePow]


private theorem tripleFirstZero_d (i j l : V) (q r n : ℤ) :
    HomologicalComplex.mapBifunctor₁₂.d₁ F F (B i) (B j) (B l) c c 0 q r n = 0 := by
  rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq F F (B i) (B j) (B l) c c
    (by simp : (c).Rel 0 1) q r n, zigzagBraidComplex_d_eq_zero₀ i 1 (by decide)]
  simp only [Functor.map_zero, NatTrans.app_zero, zero_comp, smul_zero]

private theorem tripleSecondZero_d (i j l : V) (p r n : ℤ) :
    HomologicalComplex.mapBifunctor₁₂.d₂ F F (B i) (B j) (B l) c c p 0 r n = 0 := by
  rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq F F (B i) (B j) (B l) c c p
    (by simp : (c).Rel 0 1) r n, zigzagBraidComplex_d_eq_zero₀ j 1 (by decide)]
  simp only [Functor.map_zero, NatTrans.app_zero, zero_comp, smul_zero]

private theorem tripleThirdZero_d (i j l : V) (p q n : ℤ) :
    HomologicalComplex.mapBifunctor₁₂.d₃ F F (B i) (B j) (B l) c c p q 0 n = 0 := by
  rw [HomologicalComplex.mapBifunctor₁₂.d₃_eq F F (B i) (B j) (B l) c c p q
    (by simp : (c).Rel 0 1) n, zigzagBraidComplex_d_eq_zero₀ l 1 (by decide)]
  simp only [Functor.map_zero, zero_comp, smul_zero]

@[reassoc]
private theorem tripleFirstPairInclusion_d (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) (-1) 0 (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-2) (-1) =
    ((F).map (((F).map ((B i).d (-1) 0)).app ((B j).X (-1)))).app ((B l).X 0) ≫
        HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
          0 (-1) 0 (-1) (by norm_num [ComplexShape.r]) -
      ((F).map (((F).obj ((B i).X (-1))).map ((B j).d (-1) 0))).app ((B l).X 0) ≫
        HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
          (-1) 0 0 (-1) (by norm_num [ComplexShape.r]) := by
  rw [HomologicalComplex.mapBifunctor₁₂.d_eq]
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor₁₂.ι_D₁,
    HomologicalComplex.mapBifunctor₁₂.ι_D₂, HomologicalComplex.mapBifunctor₁₂.ι_D₃]
  rw [tripleThirdZero_d]
  simp only [add_zero]
  rw [sub_eq_add_neg]
  congr 1
  · rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq F F (B i) (B j) (B l) c c
      (by simp : (c).Rel (-1) 0) (-1) 0 (-1)]
    simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r, ComplexShape.ε₁]
  · rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq F F (B i) (B j) (B l) c c (-1)
      (by simp : (c).Rel (-1) 0) 0 (-1)]
    simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r,
      ComplexShape.ε₁, ComplexShape.ε₂]

@[reassoc]
private theorem tripleLeftPairInclusion_d (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) 0 (-1) (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-2) (-1) =
    ((F).map (((F).map ((B i).d (-1) 0)).app ((B j).X 0))).app ((B l).X (-1)) ≫
        HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
          0 0 (-1) (-1) (by norm_num [ComplexShape.r]) -
      ((F).obj (((F).obj ((B i).X (-1))).obj ((B j).X 0))).map ((B l).d (-1) 0) ≫
        HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
          (-1) 0 0 (-1) (by norm_num [ComplexShape.r]) := by
  rw [HomologicalComplex.mapBifunctor₁₂.d_eq]
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor₁₂.ι_D₁,
    HomologicalComplex.mapBifunctor₁₂.ι_D₂, HomologicalComplex.mapBifunctor₁₂.ι_D₃]
  rw [tripleSecondZero_d]
  simp only [add_zero]
  rw [sub_eq_add_neg]
  congr 1
  · rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq F F (B i) (B j) (B l) c c
      (by simp : (c).Rel (-1) 0) 0 (-1) (-1)]
    simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r, ComplexShape.ε₁]
  · rw [HomologicalComplex.mapBifunctor₁₂.d₃_eq F F (B i) (B j) (B l) c c (-1) 0
      (by simp : (c).Rel (-1) 0) (-1)]
    simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r, ComplexShape.ε₂]

@[reassoc]
private theorem tripleRightPairInclusion_d (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 (-1) (-1) (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-2) (-1) =
    ((F).map (((F).obj ((B i).X 0)).map ((B j).d (-1) 0))).app ((B l).X (-1)) ≫
        HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
          0 0 (-1) (-1) (by norm_num [ComplexShape.r]) -
      ((F).obj (((F).obj ((B i).X 0)).obj ((B j).X (-1)))).map ((B l).d (-1) 0) ≫
        HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
          0 (-1) 0 (-1) (by norm_num [ComplexShape.r]) := by
  rw [HomologicalComplex.mapBifunctor₁₂.d_eq]
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor₁₂.ι_D₁,
    HomologicalComplex.mapBifunctor₁₂.ι_D₂, HomologicalComplex.mapBifunctor₁₂.ι_D₃]
  rw [tripleFirstZero_d]
  simp only [zero_add]
  rw [sub_eq_add_neg]
  congr 1
  · rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq F F (B i) (B j) (B l) c c 0
      (by simp : (c).Rel (-1) 0) (-1) (-1)]
    simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r,
      ComplexShape.ε₁, ComplexShape.ε₂]
  · rw [HomologicalComplex.mapBifunctor₁₂.d₃_eq F F (B i) (B j) (B l) c c 0 (-1)
      (by simp : (c).Rel (-1) 0) (-1)]
    simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r, ComplexShape.ε₂]


@[reassoc]
private theorem tripleLowestInclusion_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) (-1) (-1) (-3) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusThreeIso k G i j l).hom =
    M (M (I₀ i).hom (I₀ j).hom) (I₀ l).hom := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq F F (B i) (B j) (B l) c c
    (-1) (-1) (-1) (-2) (-3) (by simp) (by simp)]
  simp only [Category.assoc, ιMapBifunctor_zigzagBraidComplexTripleXMinusThreeIso_hom]
  simp only [← Functor.flip_obj_map]
  rw [← Category.assoc, ← Functor.map_comp,
    ιMapBifunctor_zigzagBraidComplexTensorXMinusTwoIso_hom]
  simp only [Functor.flip_obj_map, zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
    ← GradedModuleCat.bimoduleTensorMap_comp,
    Category.comp_id, Category.id_comp]

@[reassoc]
private theorem tripleFirstPairInclusion_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) (-1) 0 (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusTwoIso k G i j l).hom =
    M (M (I₀ i).hom (I₀ j).hom) (I₁ l).hom ≫
      (zigzagBimoduleRightUnitor k G (T (U i) (U j))).hom ≫ biprod.inl := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq F F (B i) (B j) (B l) c c
    (-1) (-1) 0 (-2) (-2) (by simp) (by simp)]
  simp only [Category.assoc, ιMapBifunctor_zigzagBraidComplexTripleXMinusTwoIso_hom_left]
  simp only [← Functor.flip_obj_map]
  rw [← Category.assoc, ← Functor.map_comp,
    ιMapBifunctor_zigzagBraidComplexTensorXMinusTwoIso_hom]
  simp only [Functor.flip_obj_map, zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
    Category.comp_id, Category.id_comp]
  -- The two unitor arguments are the same computed tensor-functor object.
  rfl


@[reassoc]
private theorem tripleLeftPairInclusion_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) 0 (-1) (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusTwoIso k G i j l).hom =
    M (M (I₀ i).hom (I₁ j).hom ≫ (zigzagBimoduleRightUnitor k G (U i)).hom)
        (I₀ l).hom ≫ biprod.inl ≫ biprod.inr := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq F F (B i) (B j) (B l) c c
    (-1) 0 (-1) (-1) (-2) (by simp) (by simp)]
  simp only [Category.assoc, ιMapBifunctor_zigzagBraidComplexTripleXMinusTwoIso_hom_right]
  simp only [← Functor.flip_obj_map]
  rw [← Category.assoc, ← Functor.map_comp,
    ιMapBifunctor_zigzagBraidComplexTensorXMinusOneIso_hom_left]
  simp only [Functor.map_comp, Category.assoc]
  simp only [Functor.flip_obj_map]
  rw [← ((F).map (biprod.inl : U i ⟶ U i ⊞ U j)).naturality_assoc (I₀ l).hom]
  have hinl : ((F).map (biprod.inl : U i ⟶ U i ⊞ U j)).app (U l) ≫
      biprod.lift (((F).map (biprod.fst : U i ⊞ U j ⟶ U i)).app (U l))
        (((F).map (biprod.snd : U i ⊞ U j ⟶ U j)).app (U l)) = biprod.inl := by
    simp only [← Functor.flip_obj_map]
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, ← Functor.map_comp, biprod.inl_fst,
        CategoryTheory.Functor.map_id]
      exact biprod.inl_fst.symm
    · rw [Category.assoc, biprod.lift_snd, ← Functor.map_comp, biprod.inl_snd,
        Functor.map_zero]
      exact biprod.inl_snd.symm
  have hinl' := congrArg (fun f ↦ f ≫ (biprod.inr :
    ((F).obj (U i)).obj (U l) ⊞ ((F).obj (U j)).obj (U l) ⟶
      ((F).obj (U i)).obj (U j) ⊞
        (((F).obj (U i)).obj (U l) ⊞ ((F).obj (U j)).obj (U l)))) hinl
  simp only [Category.assoc] at hinl'
  refine (congrArg (fun f ↦
    (((F).map (((F).map (I₀ i).hom).app ((B j).X 0))).app ((B l).X (-1))) ≫
      (((F).map (((F).obj (U i)).map (I₁ j).hom)).app ((B l).X (-1))) ≫
        (((F).map (zigzagBimoduleRightUnitor k G (U i)).hom).app ((B l).X (-1))) ≫
          ((F).obj (U i)).map (I₀ l).hom ≫ f) hinl').trans ?_
  simp only [zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
    Category.comp_id, Category.id_comp]
  rfl

@[reassoc]
private theorem tripleRightPairInclusion_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 (-1) (-1) (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusTwoIso k G i j l).hom =
    M (M (I₁ i).hom (I₀ j).hom ≫ (zigzagBimoduleLeftUnitor k G (U j)).hom)
        (I₀ l).hom ≫ biprod.inr ≫ biprod.inr := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq F F (B i) (B j) (B l) c c
    0 (-1) (-1) (-1) (-2) (by simp) (by simp)]
  simp only [Category.assoc, ιMapBifunctor_zigzagBraidComplexTripleXMinusTwoIso_hom_right]
  simp only [← Functor.flip_obj_map]
  rw [← Category.assoc, ← Functor.map_comp,
    ιMapBifunctor_zigzagBraidComplexTensorXMinusOneIso_hom_right]
  simp only [Functor.map_comp, Category.assoc]
  simp only [Functor.flip_obj_map]
  rw [← ((F).map (biprod.inr : U j ⟶ U i ⊞ U j)).naturality_assoc (I₀ l).hom]
  have hinr : ((F).map (biprod.inr : U j ⟶ U i ⊞ U j)).app (U l) ≫
      biprod.lift (((F).map (biprod.fst : U i ⊞ U j ⟶ U i)).app (U l))
        (((F).map (biprod.snd : U i ⊞ U j ⟶ U j)).app (U l)) = biprod.inr := by
    simp only [← Functor.flip_obj_map]
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, ← Functor.map_comp, biprod.inr_fst,
        Functor.map_zero]
      exact biprod.inr_fst.symm
    · rw [Category.assoc, biprod.lift_snd, ← Functor.map_comp, biprod.inr_snd,
        CategoryTheory.Functor.map_id]
      exact biprod.inr_snd.symm
  have hinr' := congrArg (fun f ↦ f ≫ (biprod.inr :
    ((F).obj (U i)).obj (U l) ⊞ ((F).obj (U j)).obj (U l) ⟶
      ((F).obj (U i)).obj (U j) ⊞
        (((F).obj (U i)).obj (U l) ⊞ ((F).obj (U j)).obj (U l)))) hinr
  simp only [Category.assoc] at hinr'
  refine (congrArg (fun f ↦
    (((F).map (((F).map (I₁ i).hom).app ((B j).X (-1)))).app ((B l).X (-1))) ≫
      (((F).map (((F).obj (zigzagGradedBimodule k G)).map (I₀ j).hom)).app ((B l).X (-1))) ≫
        (((F).map (zigzagBimoduleLeftUnitor k G (U j)).hom).app ((B l).X (-1))) ≫
          ((F).obj (U j)).map (I₀ l).hom ≫ f) hinr').trans ?_
  simp only [zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
    Category.comp_id, Category.id_comp]
  rfl


@[reassoc]
private theorem tripleFirstVertexInclusion_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) 0 0 (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom =
    M (M (I₀ i).hom (I₁ j).hom ≫ (zigzagBimoduleRightUnitor k G (U i)).hom)
        (I₁ l).hom ≫ (zigzagBimoduleRightUnitor k G (U i)).hom ≫
      biprod.inl ≫ biprod.inl := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq F F (B i) (B j) (B l) c c
    (-1) 0 0 (-1) (-1) (by simp) (by simp)]
  simp only [Category.assoc, ιMapBifunctor_zigzagBraidComplexTripleXMinusOneIso_hom_left]
  simp only [← Functor.flip_obj_map]
  rw [← Category.assoc, ← Functor.map_comp,
    ιMapBifunctor_zigzagBraidComplexTensorXMinusOneIso_hom_left]
  simp only [Functor.map_comp, Category.assoc, Functor.flip_obj_map, NatTrans.comp_app]
  rw [← ((F).map (biprod.inl : U i ⟶ U i ⊞ U j)).naturality_assoc (I₁ l).hom]
  simp only [zigzagBimoduleTensor, GradedModuleCat.bimoduleTensor_map_app,
    GradedModuleCat.bimoduleTensor_obj_map]
  rw [zigzagBimoduleRightUnitor_naturality_assoc]
  simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
    Category.comp_id, Category.id_comp]

@[reassoc]
private theorem tripleSecondVertexInclusion_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 (-1) 0 (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom =
    M (M (I₁ i).hom (I₀ j).hom ≫ (zigzagBimoduleLeftUnitor k G (U j)).hom)
        (I₁ l).hom ≫ (zigzagBimoduleRightUnitor k G (U j)).hom ≫
      biprod.inr ≫ biprod.inl := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq F F (B i) (B j) (B l) c c
    0 (-1) 0 (-1) (-1) (by simp) (by simp)]
  simp only [Category.assoc, ιMapBifunctor_zigzagBraidComplexTripleXMinusOneIso_hom_left]
  simp only [← Functor.flip_obj_map]
  rw [← Category.assoc, ← Functor.map_comp,
    ιMapBifunctor_zigzagBraidComplexTensorXMinusOneIso_hom_right]
  simp only [Functor.map_comp, Category.assoc, Functor.flip_obj_map, NatTrans.comp_app]
  rw [← ((F).map (biprod.inr : U j ⟶ U i ⊞ U j)).naturality_assoc (I₁ l).hom]
  simp only [zigzagBimoduleTensor, GradedModuleCat.bimoduleTensor_map_app,
    GradedModuleCat.bimoduleTensor_obj_map]
  rw [zigzagBimoduleRightUnitor_naturality_assoc]
  simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
    Category.comp_id, Category.id_comp]

@[reassoc]
private theorem tripleThirdVertexInclusion_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 0 (-1) (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom =
    M (M (I₁ i).hom (I₁ j).hom ≫
        (zigzagBimoduleLeftUnitor k G (zigzagGradedBimodule k G)).hom) (I₀ l).hom ≫
      (zigzagBimoduleLeftUnitor k G (U l)).hom ≫ biprod.inr := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq F F (B i) (B j) (B l) c c
    0 0 (-1) 0 (-1) (by simp) (by simp)]
  simp only [Category.assoc, ιMapBifunctor_zigzagBraidComplexTripleXMinusOneIso_hom_right]
  simp only [← Functor.flip_obj_map]
  rw [← Category.assoc, ← Functor.map_comp,
    ιMapBifunctor_zigzagBraidComplexTensorXZeroIso_hom]
  simp only [Functor.flip_obj_map, zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
    Category.comp_id, Category.id_comp]


private theorem isZero_tripleLeaf (i j l : V) (p q r : ℤ)
    (h : ¬ ((p = -1 ∨ p = 0) ∧ (q = -1 ∨ q = 0) ∧ (r = -1 ∨ r = 0))) :
    IsZero (((F).obj (((F).obj ((B i).X p)).obj ((B j).X q))).obj ((B l).X r)) := by
  by_cases hpq : (p = -1 ∨ p = 0) ∧ (q = -1 ∨ q = 0)
  · exact ((F).obj (((F).obj ((B i).X p)).obj ((B j).X q))).map_isZero
      (isZero_zigzagBraidComplex_X l (by omega) (by omega))
  · exact ((F).flip.obj ((B l).X r)).map_isZero
      (isZero_zigzagBraidComplexTensor_pair k G i j p q hpq)

/-- The lowest actual triple differential has the signed three-factor evaluation matrix. -/
@[reassoc]
theorem zigzagBraidComplexTriple_d_minusThree (i j l : V) :
    (zigzagBraidComplexTriple k G i j l).d (-3) (-2) ≫
        (zigzagBraidComplexTripleXMinusTwoIso k G i j l).hom =
      (zigzagBraidComplexTripleXMinusThreeIso k G i j l).hom ≫
        zigzagBraidTripleFirstDifferential k G i j l := by
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r hpqr
  by_cases h : (p = -1 ∨ p = 0) ∧ (q = -1 ∨ q = 0) ∧ (r = -1 ∨ r = 0)
  · simp only [ComplexShape.r, ComplexShape.π_eq_add] at hpqr
    have hp : p = -1 := by omega
    have hq : q = -1 := by omega
    have hr : r = -1 := by omega
    subst p; subst q; subst r
    rw [tripleLowestInclusion_hom_assoc]
    rw [← Category.assoc, tripleLowestInclusion_d]
    simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc,
      tripleRightPairInclusion_hom, tripleLeftPairInclusion_hom, tripleFirstPairInclusion_hom]
    simp only [zigzagBraidComplex_d, zigzagBimoduleTensor,
      GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
      ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hsplit
        (a : T (T ((B i).X (-1)) ((B j).X (-1))) ((B l).X (-1)) ⟶ T (U j) (U l))
        (b : T (T ((B i).X (-1)) ((B j).X (-1))) ((B l).X (-1)) ⟶ T (U i) (U l))
        (d : T (T ((B i).X (-1)) ((B j).X (-1))) ((B l).X (-1)) ⟶ T (U i) (U j)) :
        a ≫ biprod.inr ≫ biprod.inr - b ≫ biprod.inl ≫ biprod.inr + d ≫ biprod.inl =
          biprod.lift d (biprod.lift (-b) a) := by
      apply biprod.hom_ext
      · simp
      · apply biprod.hom_ext <;> simp
    refine (hsplit
      (M (M ((I₀ i).hom ≫ E i) (I₀ j).hom ≫
        (zigzagBimoduleLeftUnitor k G (U j)).hom) (I₀ l).hom)
      (M (M (I₀ i).hom ((I₀ j).hom ≫ E j) ≫
        (zigzagBimoduleRightUnitor k G (U i)).hom) (I₀ l).hom)
      (M (M (I₀ i).hom (I₀ j).hom) ((I₀ l).hom ≫ E l) ≫
        (zigzagBimoduleRightUnitor k G (T (U i) (U j))).hom)).trans ?_
    rw [zigzagBraidTripleFirstDifferential]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst]
      simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
        Category.comp_id]
    · apply biprod.hom_ext
      · simp only [Category.assoc, biprod.lift_snd, biprod.lift_fst,
          Preadditive.comp_neg]
        congr 1
        rw [zigzagBraidTensorEvaluationRight_eq]
        simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
          Category.comp_id]
      · simp only [Category.assoc, biprod.lift_snd]
        rw [zigzagBraidTensorEvaluationLeft_eq]
        simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
          Category.comp_id]
  · exact (isZero_tripleLeaf k G i j l p q r h).eq_of_src _ _


private theorem tripleFirstPairInclusion_d_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) (-1) 0 (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-2) (-1) ≫
        (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom =
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) (-1) 0 (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusTwoIso k G i j l).hom ≫
        zigzagBraidTripleSecondDifferential k G i j l := by
  rw [tripleFirstPairInclusion_hom_assoc]
  rw [← Category.assoc, tripleFirstPairInclusion_d]
  simp only [Preadditive.sub_comp, Category.assoc, tripleFirstVertexInclusion_hom,
    tripleSecondVertexInclusion_hom]
  simp only [zigzagBraidComplex_d, zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  have hsplit
      (a : T (T ((B i).X (-1)) ((B j).X (-1))) ((B l).X 0) ⟶ U j)
      (b : T (T ((B i).X (-1)) ((B j).X (-1))) ((B l).X 0) ⟶ U i) :
      a ≫ biprod.inr ≫ biprod.inl - b ≫ biprod.inl ≫ biprod.inl =
        biprod.lift (biprod.lift (-b) a)
          (0 : T (T ((B i).X (-1)) ((B j).X (-1))) ((B l).X 0) ⟶ U l) := by
    apply biprod.hom_ext
    · apply biprod.hom_ext <;> simp
    · simp
  refine (hsplit
    (M (M ((I₀ i).hom ≫ E i) (I₀ j).hom ≫
      (zigzagBimoduleLeftUnitor k G (U j)).hom) (I₁ l).hom ≫
        (zigzagBimoduleRightUnitor k G (U j)).hom)
    (M (M (I₀ i).hom ((I₀ j).hom ≫ E j) ≫
      (zigzagBimoduleRightUnitor k G (U i)).hom) (I₁ l).hom ≫
        (zigzagBimoduleRightUnitor k G (U i)).hom)).trans ?_
  have hcol := congrArg (fun f ↦ M (M (I₀ i).hom (I₀ j).hom) (I₁ l).hom ≫
    (zigzagBimoduleRightUnitor k G (T (U i) (U j))).hom ≫ f)
      (zigzagBraidTripleSecondDifferential_inl k G i j l)
  refine Eq.trans ?_ hcol.symm
  apply biprod.hom_ext
  · apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, Preadditive.comp_neg]
      congr 1
      rw [← zigzagBimoduleRightUnitor_naturality k G (T (U i) (U j)) (R i j),
        zigzagBraidTensorEvaluationRight_eq]
      simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
        Category.comp_id]
    · simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd]
      rw [← zigzagBimoduleRightUnitor_naturality k G (T (U i) (U j)) (L i j),
        zigzagBraidTensorEvaluationLeft_eq]
      simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
        Category.comp_id]
  · simp only [Category.assoc, biprod.lift_snd, comp_zero]


private theorem tripleLeftPairInclusion_d_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) 0 (-1) (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-2) (-1) ≫
        (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom =
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) 0 (-1) (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusTwoIso k G i j l).hom ≫
        zigzagBraidTripleSecondDifferential k G i j l := by
  rw [tripleLeftPairInclusion_hom_assoc]
  rw [← Category.assoc, tripleLeftPairInclusion_d]
  simp only [Preadditive.sub_comp, Category.assoc, tripleFirstVertexInclusion_hom,
    tripleThirdVertexInclusion_hom]
  simp only [zigzagBraidComplex_d, zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  have hsplit
      (a : T (T ((B i).X (-1)) ((B j).X 0)) ((B l).X (-1)) ⟶ U l)
      (b : T (T ((B i).X (-1)) ((B j).X 0)) ((B l).X (-1)) ⟶ U i) :
      a ≫ biprod.inr - b ≫ biprod.inl ≫ biprod.inl =
        biprod.lift (biprod.lift (-b)
          (0 : T (T ((B i).X (-1)) ((B j).X 0)) ((B l).X (-1)) ⟶ U j)) a := by
    apply biprod.hom_ext
    · apply biprod.hom_ext <;> simp
    · simp
  refine (hsplit
    (M (M ((I₀ i).hom ≫ E i) (I₁ j).hom ≫
      (zigzagBimoduleLeftUnitor k G (zigzagGradedBimodule k G)).hom) (I₀ l).hom ≫
        (zigzagBimoduleLeftUnitor k G (U l)).hom)
    (M (M (I₀ i).hom (I₁ j).hom ≫ (zigzagBimoduleRightUnitor k G (U i)).hom)
      ((I₀ l).hom ≫ E l) ≫ (zigzagBimoduleRightUnitor k G (U i)).hom)).trans ?_
  have hcol := congrArg (fun f ↦
    M (M (I₀ i).hom (I₁ j).hom ≫ (zigzagBimoduleRightUnitor k G (U i)).hom)
      (I₀ l).hom ≫ f) (zigzagBraidTripleSecondDifferential_inl_inr k G i j l)
  refine Eq.trans ?_ hcol.symm
  apply biprod.hom_ext
  · apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, Preadditive.comp_neg]
      congr 1
      rw [zigzagBraidTensorEvaluationRight_eq]
      simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
        Category.comp_id]
    · simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, comp_zero]
  · simp only [Category.assoc, biprod.lift_snd]
    rw [zigzagBraidTensorEvaluationLeft_eq]
    simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
      Category.comp_id]
    rw [Category.assoc, ← zigzagBimoduleRightUnitor_naturality k G (U i) (E i),
      zigzagBimoduleUnitHom_eq k G]
    simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
      Category.comp_id]

private theorem tripleRightPairInclusion_d_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 (-1) (-1) (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-2) (-1) ≫
        (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom =
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 (-1) (-1) (-2) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusTwoIso k G i j l).hom ≫
        zigzagBraidTripleSecondDifferential k G i j l := by
  rw [tripleRightPairInclusion_hom_assoc]
  rw [← Category.assoc, tripleRightPairInclusion_d]
  simp only [Preadditive.sub_comp, Category.assoc, tripleSecondVertexInclusion_hom,
    tripleThirdVertexInclusion_hom]
  simp only [zigzagBraidComplex_d, zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  have hsplit
      (a : T (T ((B i).X 0) ((B j).X (-1))) ((B l).X (-1)) ⟶ U l)
      (b : T (T ((B i).X 0) ((B j).X (-1))) ((B l).X (-1)) ⟶ U j) :
      a ≫ biprod.inr - b ≫ biprod.inr ≫ biprod.inl =
        biprod.lift (biprod.lift
          (0 : T (T ((B i).X 0) ((B j).X (-1))) ((B l).X (-1)) ⟶ U i) (-b)) a := by
    apply biprod.hom_ext
    · apply biprod.hom_ext <;> simp
    · simp
  refine (hsplit
    (M (M (I₁ i).hom ((I₀ j).hom ≫ E j) ≫
      (zigzagBimoduleLeftUnitor k G (zigzagGradedBimodule k G)).hom) (I₀ l).hom ≫
        (zigzagBimoduleLeftUnitor k G (U l)).hom)
    (M (M (I₁ i).hom (I₀ j).hom ≫ (zigzagBimoduleLeftUnitor k G (U j)).hom)
      ((I₀ l).hom ≫ E l) ≫ (zigzagBimoduleRightUnitor k G (U j)).hom)).trans ?_
  have hcol := congrArg (fun f ↦
    M (M (I₁ i).hom (I₀ j).hom ≫ (zigzagBimoduleLeftUnitor k G (U j)).hom)
      (I₀ l).hom ≫ f) (zigzagBraidTripleSecondDifferential_inr_inr k G i j l)
  refine Eq.trans ?_ hcol.symm
  apply biprod.hom_ext
  · apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, comp_zero]
    · simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, Preadditive.comp_neg]
      congr 1
      rw [zigzagBraidTensorEvaluationRight_eq]
      simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
        Category.comp_id]
  · simp only [Category.assoc, biprod.lift_snd]
    rw [zigzagBraidTensorEvaluationLeft_eq]
    simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
      Category.comp_id]
    rw [Category.assoc, ← zigzagBimoduleLeftUnitor_naturality k G (U j) (E j)]
    simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
      Category.comp_id]


/-- The middle actual triple differential has the three signed pair-evaluation columns. -/
@[reassoc]
theorem zigzagBraidComplexTriple_d_minusTwo (i j l : V) :
    (zigzagBraidComplexTriple k G i j l).d (-2) (-1) ≫
        (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom =
      (zigzagBraidComplexTripleXMinusTwoIso k G i j l).hom ≫
        zigzagBraidTripleSecondDifferential k G i j l := by
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r hpqr
  by_cases h : (p = -1 ∨ p = 0) ∧ (q = -1 ∨ q = 0) ∧ (r = -1 ∨ r = 0)
  · simp only [ComplexShape.r, ComplexShape.π_eq_add] at hpqr
    by_cases hr : r = 0
    · subst r
      have hp : p = -1 := by omega
      have hq : q = -1 := by omega
      subst p; subst q
      exact tripleFirstPairInclusion_d_hom k G i j l
    · by_cases hq : q = 0
      · subst q
        have hp : p = -1 := by omega
        have hr : r = -1 := by omega
        subst p; subst r
        exact tripleLeftPairInclusion_d_hom k G i j l
      · have hp : p = 0 := by omega
        have hq : q = -1 := by omega
        have hr : r = -1 := by omega
        subst p; subst q; subst r
        exact tripleRightPairInclusion_d_hom k G i j l
  · exact (isZero_tripleLeaf k G i j l p q r h).eq_of_src _ _

@[reassoc]
private theorem tripleZeroInclusion_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 0 0 0 (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXZeroIso k G i j l).hom =
    M (M (I₁ i).hom (I₁ j).hom ≫
      (zigzagBimoduleLeftUnitor k G (zigzagGradedBimodule k G)).hom) (I₁ l).hom ≫
        (zigzagBimoduleLeftUnitor k G (zigzagGradedBimodule k G)).hom := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq F F (B i) (B j) (B l) c c
    0 0 0 0 0 (by simp) (by simp)]
  simp only [Category.assoc, ιMapBifunctor_zigzagBraidComplexTripleXZeroIso_hom]
  simp only [← Functor.flip_obj_map]
  rw [← Category.assoc, ← Functor.map_comp,
    ιMapBifunctor_zigzagBraidComplexTensorXZeroIso_hom]
  simp only [Functor.flip_obj_map, zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
    Category.comp_id, Category.id_comp]

@[reassoc]
private theorem tripleFirstVertexInclusion_d (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) 0 0 (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-1) 0 =
    ((F).map (((F).map ((B i).d (-1) 0)).app ((B j).X 0))).app ((B l).X 0) ≫
      HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 0 0 0 (by norm_num [ComplexShape.r]) := by
  rw [HomologicalComplex.mapBifunctor₁₂.d_eq]
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor₁₂.ι_D₁,
    HomologicalComplex.mapBifunctor₁₂.ι_D₂, HomologicalComplex.mapBifunctor₁₂.ι_D₃]
  rw [tripleSecondZero_d, tripleThirdZero_d]
  simp only [add_zero]
  rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq F F (B i) (B j) (B l) c c
    (by simp : (c).Rel (-1) 0) 0 0 0]
  simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r, ComplexShape.ε₁]

@[reassoc]
private theorem tripleSecondVertexInclusion_d (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 (-1) 0 (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-1) 0 =
    ((F).map (((F).obj ((B i).X 0)).map ((B j).d (-1) 0))).app ((B l).X 0) ≫
      HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 0 0 0 (by norm_num [ComplexShape.r]) := by
  rw [HomologicalComplex.mapBifunctor₁₂.d_eq]
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor₁₂.ι_D₁,
    HomologicalComplex.mapBifunctor₁₂.ι_D₂, HomologicalComplex.mapBifunctor₁₂.ι_D₃]
  rw [tripleFirstZero_d, tripleThirdZero_d]
  simp only [zero_add, add_zero]
  rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq F F (B i) (B j) (B l) c c 0
    (by simp : (c).Rel (-1) 0) 0 0]
  simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r,
    ComplexShape.ε₁, ComplexShape.ε₂]

@[reassoc]
private theorem tripleThirdVertexInclusion_d (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 0 (-1) (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-1) 0 =
    ((F).obj (((F).obj ((B i).X 0)).obj ((B j).X 0))).map ((B l).d (-1) 0) ≫
      HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 0 0 0 (by norm_num [ComplexShape.r]) := by
  rw [HomologicalComplex.mapBifunctor₁₂.d_eq]
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor₁₂.ι_D₁,
    HomologicalComplex.mapBifunctor₁₂.ι_D₂, HomologicalComplex.mapBifunctor₁₂.ι_D₃]
  rw [tripleFirstZero_d, tripleSecondZero_d]
  simp only [zero_add]
  rw [HomologicalComplex.mapBifunctor₁₂.d₃_eq F F (B i) (B j) (B l) c c 0 0
    (by simp : (c).Rel (-1) 0) 0]
  simp [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq, ComplexShape.r, ComplexShape.ε₂]

private theorem tripleFirstVertexInclusion_d_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) 0 0 (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-1) 0 ≫
        (zigzagBraidComplexTripleXZeroIso k G i j l).hom =
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        (-1) 0 0 (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom ≫
        biprod.desc (biprod.desc (E i) (E j)) (E l) := by
  rw [tripleFirstVertexInclusion_hom_assoc]
  rw [← Category.assoc, tripleFirstVertexInclusion_d]
  simp only [Category.assoc, tripleZeroInclusion_hom, biprod.inl_desc]
  simp only [zigzagBraidComplex_d, zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  rw [← zigzagBimoduleRightUnitor_naturality k G (U i) (E i)]
  simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp, Category.comp_id]
  rw [Category.assoc, ← zigzagBimoduleRightUnitor_naturality k G (U i) (E i),
    zigzagBimoduleUnitHom_eq k G]
  simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp, Category.comp_id]

private theorem tripleSecondVertexInclusion_d_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 (-1) 0 (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-1) 0 ≫
        (zigzagBraidComplexTripleXZeroIso k G i j l).hom =
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 (-1) 0 (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom ≫
        biprod.desc (biprod.desc (E i) (E j)) (E l) := by
  rw [tripleSecondVertexInclusion_hom_assoc]
  rw [← Category.assoc, tripleSecondVertexInclusion_d]
  simp only [Category.assoc, tripleZeroInclusion_hom, biprod.inl_desc, biprod.inr_desc]
  simp only [zigzagBraidComplex_d, zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_map_app, GradedModuleCat.bimoduleTensor_obj_map,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  rw [← zigzagBimoduleRightUnitor_naturality k G (U j) (E j)]
  simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp, Category.comp_id]
  rw [Category.assoc, ← zigzagBimoduleLeftUnitor_naturality k G (U j) (E j),
    zigzagBimoduleUnitHom_eq k G]
  simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp, Category.comp_id]

private theorem tripleThirdVertexInclusion_d_hom (i j l : V) :
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 0 (-1) (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTriple k G i j l).d (-1) 0 ≫
        (zigzagBraidComplexTripleXZeroIso k G i j l).hom =
    HomologicalComplex.mapBifunctor₁₂.ι F F (B i) (B j) (B l) c c
        0 0 (-1) (-1) (by norm_num [ComplexShape.r]) ≫
      (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom ≫
        biprod.desc (biprod.desc (E i) (E j)) (E l) := by
  rw [tripleThirdVertexInclusion_hom_assoc]
  rw [← Category.assoc, tripleThirdVertexInclusion_d]
  simp only [Category.assoc, tripleZeroInclusion_hom, biprod.inr_desc]
  simp only [zigzagBraidComplex_d, zigzagBimoduleTensor,
    GradedModuleCat.bimoduleTensor_obj_map,
    ← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  rw [← zigzagBimoduleLeftUnitor_naturality k G (U l) (E l)]
  simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp, Category.comp_id]

/-- The final actual triple differential is the sum of the three vertex evaluations. -/
@[reassoc]
theorem zigzagBraidComplexTriple_d_minusOne (i j l : V) :
    (zigzagBraidComplexTriple k G i j l).d (-1) 0 ≫
        (zigzagBraidComplexTripleXZeroIso k G i j l).hom =
      (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom ≫
        biprod.desc (biprod.desc (E i) (E j)) (E l) := by
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r hpqr
  by_cases h : (p = -1 ∨ p = 0) ∧ (q = -1 ∨ q = 0) ∧ (r = -1 ∨ r = 0)
  · simp only [ComplexShape.r, ComplexShape.π_eq_add] at hpqr
    by_cases hp : p = -1
    · subst p
      have hq : q = 0 := by omega
      have hr : r = 0 := by omega
      subst q; subst r
      exact tripleFirstVertexInclusion_d_hom k G i j l
    · by_cases hq : q = -1
      · subst q
        have hp : p = 0 := by omega
        have hr : r = 0 := by omega
        subst p; subst r
        exact tripleSecondVertexInclusion_d_hom k G i j l
      · have hp : p = 0 := by omega
        have hq : q = 0 := by omega
        have hr : r = -1 := by omega
        subst p; subst q; subst r
        exact tripleThirdVertexInclusion_d_hom k G i j l
  · exact (isZero_tripleLeaf k G i j l p q r h).eq_of_src _ _

end TauCeti
