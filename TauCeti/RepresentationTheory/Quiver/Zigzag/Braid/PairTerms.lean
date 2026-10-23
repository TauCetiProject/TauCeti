/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Unit

/-!
# Terms of graded zigzag braid tensor products

The actual signed tensor product of two braid complexes is supported in
cohomological degrees −2, −1 and 0. These terms identify with the tensor of the
vertex bimodules, the biproduct of the two vertex bimodules, and the regular
bimodule. Unit identifications preserve internal grading and both outer actions.

The supported-inclusion equations compute the component maps. Under these
identifications, the differential from degree −1 to 0 is the sum of the two
evaluations. These formulas supply the pair terms used in commuting and triple
braid calculations.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "F" => (GradedModuleCat.bimoduleTensor Γ Γ Γ :
  GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ ⥤ GradedBimoduleCat k Γ)
local notation "Z" => zigzagGradedBimodule k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "B" => zigzagBraidComplex k G
local notation "T" => zigzagBraidComplexTensor k G
local notation "c" => ComplexShape.up ℤ

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

/-- The degree-minus-two term of a braid tensor product is the tensor of the vertex bimodules. -/
def zigzagBraidComplexTensorXMinusTwoIso (i j : V) :
    (T i j).X (-2) ≅ ((F).obj (U i)).obj (U j) :=
  HomologicalComplex.mapBifunctorSingleSummandIso (B i) (B j) F c (-1) (-1) (-2) (by norm_num)
      (by
        intro p q hpq h
        rw [ComplexShape.π_eq_add] at hpq
        exact isZero_zigzagBraidComplexTensor_pair k G i j p q (by omega)) ≪≫
    ((F).flip.obj ((B j).X (-1))).mapIso (zigzagBraidComplexXIso₀ k G i) ≪≫
      ((F).obj (U i)).mapIso (zigzagBraidComplexXIso₀ k G j)

private def tensorPairZeroIso (i j : V) :
    ((F).obj ((B i).X 0)).obj ((B j).X 0) ≅ Z :=
  ((F).flip.obj ((B j).X 0)).mapIso (zigzagBraidComplexXIso₁ k G i) ≪≫
    ((F).obj Z).mapIso (zigzagBraidComplexXIso₁ k G j) ≪≫
      zigzagBimoduleLeftUnitor k G Z

private def tensorPairLeftIso (i j : V) :
    ((F).obj ((B i).X (-1))).obj ((B j).X 0) ≅ U i :=
  ((F).flip.obj ((B j).X 0)).mapIso (zigzagBraidComplexXIso₀ k G i) ≪≫
    ((F).obj (U i)).mapIso (zigzagBraidComplexXIso₁ k G j) ≪≫
      zigzagBimoduleRightUnitor k G (U i)

private def tensorPairRightIso (i j : V) :
    ((F).obj ((B i).X 0)).obj ((B j).X (-1)) ≅ U j :=
  ((F).flip.obj ((B j).X (-1))).mapIso (zigzagBraidComplexXIso₁ k G i) ≪≫
    ((F).obj Z).mapIso (zigzagBraidComplexXIso₀ k G j) ≪≫
      zigzagBimoduleLeftUnitor k G (U j)

private theorem tensorPairZeroIso_hom (i j : V) :
    (tensorPairZeroIso k G i j).hom =
      ((F).map (zigzagBraidComplexXIso₁ k G i).hom).app ((B j).X 0) ≫
        ((F).obj Z).map (zigzagBraidComplexXIso₁ k G j).hom ≫
          (zigzagBimoduleLeftUnitor k G Z).hom := by
  -- Compute the two mapped components and the unitor of the constructed isomorphism.
  rfl

private theorem tensorPairLeftIso_hom (i j : V) :
    (tensorPairLeftIso k G i j).hom =
      ((F).map (zigzagBraidComplexXIso₀ k G i).hom).app ((B j).X 0) ≫
        ((F).obj (U i)).map (zigzagBraidComplexXIso₁ k G j).hom ≫
          (zigzagBimoduleRightUnitor k G (U i)).hom := by
  -- Compute the two mapped components and the unitor of the constructed isomorphism.
  rfl

private theorem tensorPairRightIso_hom (i j : V) :
    (tensorPairRightIso k G i j).hom =
      ((F).map (zigzagBraidComplexXIso₁ k G i).hom).app ((B j).X (-1)) ≫
        ((F).obj Z).map (zigzagBraidComplexXIso₀ k G j).hom ≫
          (zigzagBimoduleLeftUnitor k G (U j)).hom := by
  -- Compute the two mapped components and the unitor of the constructed isomorphism.
  rfl

/-- The degree-zero term of the actual braid tensor product is the regular bimodule. -/
def zigzagBraidComplexTensorXZeroIso (i j : V) : (T i j).X 0 ≅ Z :=
  HomologicalComplex.mapBifunctorSingleSummandIso (B i) (B j) F c 0 0 0 (by simp) (by
    intro p q hpq h
    rw [ComplexShape.π_eq_add] at hpq
    exact isZero_zigzagBraidComplexTensor_pair k G i j p q (by omega)) ≪≫
      tensorPairZeroIso k G i j

/-- The regular summand in degree zero evaluates through the two component unit maps. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTensorXZeroIso_hom (i j : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B j) F c 0 0 0 (by simp) ≫
        (zigzagBraidComplexTensorXZeroIso k G i j).hom =
      ((F).map (zigzagBraidComplexXIso₁ k G i).hom).app ((B j).X 0) ≫
        ((F).obj Z).map (zigzagBraidComplexXIso₁ k G j).hom ≫
          (zigzagBimoduleLeftUnitor k G Z).hom := by
  simp only [zigzagBraidComplexTensorXZeroIso, Iso.trans_hom,
    HomologicalComplex.ι_mapBifunctorSingleSummandIso_hom_assoc]
  rw [tensorPairZeroIso_hom]

/-- The degree-minus-one term is the biproduct of the two actual vertex bimodules. -/
def zigzagBraidComplexTensorXMinusOneIso (i j : V) : (T i j).X (-1) ≅ U i ⊞ U j :=
  HomologicalComplex.mapBifunctorTwoSummandIso (B i) (B j) F c (-1) 0 0 (-1) (-1)
    (by simp) (by simp) (by decide) (by
      intro p q hpq h
      rw [ComplexShape.π_eq_add] at hpq
      exact isZero_zigzagBraidComplexTensor_pair k G i j p q (by omega)) ≪≫
        biprod.mapIso (tensorPairLeftIso k G i j) (tensorPairRightIso k G i j)

/-- The `(-1,0)` summand identifies with the first vertex summand via the right unitor. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTensorXMinusOneIso_hom_left (i j : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B j) F c (-1) 0 (-1) (by simp) ≫
        (zigzagBraidComplexTensorXMinusOneIso k G i j).hom =
      (((F).map (zigzagBraidComplexXIso₀ k G i).hom).app ((B j).X 0) ≫
        ((F).obj (U i)).map (zigzagBraidComplexXIso₁ k G j).hom ≫
          (zigzagBimoduleRightUnitor k G (U i)).hom) ≫ biprod.inl := by
  simp only [zigzagBraidComplexTensorXMinusOneIso, Iso.trans_hom,
    HomologicalComplex.ι_mapBifunctorTwoSummandIso_hom_left_assoc, biprod.mapIso_hom,
    biprod.inl_map]
  rw [tensorPairLeftIso_hom]

/-- The `(0,-1)` summand identifies with the second vertex summand via the left unitor. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTensorXMinusOneIso_hom_right (i j : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B j) F c 0 (-1) (-1) (by simp) ≫
        (zigzagBraidComplexTensorXMinusOneIso k G i j).hom =
      (((F).map (zigzagBraidComplexXIso₁ k G i).hom).app ((B j).X (-1)) ≫
        ((F).obj Z).map (zigzagBraidComplexXIso₀ k G j).hom ≫
          (zigzagBimoduleLeftUnitor k G (U j)).hom) ≫ biprod.inr := by
  simp only [zigzagBraidComplexTensorXMinusOneIso, Iso.trans_hom,
    HomologicalComplex.ι_mapBifunctorTwoSummandIso_hom_right_assoc, biprod.mapIso_hom,
    biprod.inr_map]
  rw [tensorPairRightIso_hom]

private theorem tensorPairLeft_d (i j : V) :
    (((F).map ((B i).d (-1) 0)).app ((B j).X 0)) ≫ (tensorPairZeroIso k G i j).hom =
      (tensorPairLeftIso k G i j).hom ≫ zigzagBraidEvaluationHom k G i := by
  rw [tensorPairZeroIso_hom, tensorPairLeftIso_hom]
  simp only [zigzagBraidComplex_d, Functor.map_comp, NatTrans.comp_app, Category.assoc,
    Iso.map_inv_hom_id_app_assoc]
  rw [zigzagBimoduleUnitHom_eq k G,
    ← ((F).map (zigzagBraidEvaluationHom k G i)).naturality_assoc
      (zigzagBraidComplexXIso₁ k G j).hom (zigzagBimoduleRightUnitor k G Z).hom]
  exact (congrArg
    (fun f ↦ ((F).map (zigzagBraidComplexXIso₀ k G i).hom).app ((B j).X 0) ≫
      ((F).obj (U i)).map (zigzagBraidComplexXIso₁ k G j).hom ≫ f)
    (zigzagBimoduleRightUnitor_naturality k G (U i) (zigzagBraidEvaluationHom k G i))).trans
      (congrArg (fun f ↦ ((F).map (zigzagBraidComplexXIso₀ k G i).hom).app ((B j).X 0) ≫ f)
        (Category.assoc (((F).obj (U i)).map (zigzagBraidComplexXIso₁ k G j).hom)
          (zigzagBimoduleRightUnitor k G (U i)).hom
          (zigzagBraidEvaluationHom k G i)).symm)

private theorem tensorPairRight_d (i j : V) :
    ((F).obj ((B i).X 0)).map ((B j).d (-1) 0) ≫ (tensorPairZeroIso k G i j).hom =
      (tensorPairRightIso k G i j).hom ≫ zigzagBraidEvaluationHom k G j := by
  rw [tensorPairZeroIso_hom, tensorPairRightIso_hom]
  rw [((F).map (zigzagBraidComplexXIso₁ k G i).hom).naturality_assoc
    ((B j).d (-1) 0)
    (((F).obj Z).map (zigzagBraidComplexXIso₁ k G j).hom ≫
      (zigzagBimoduleLeftUnitor k G Z).hom)]
  simp only [zigzagBraidComplex_d, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_map_assoc (zigzagBraidComplexXIso₁ k G j) ((F).obj Z)
      (zigzagBimoduleLeftUnitor k G Z).hom]
  exact (congrArg
    (fun f ↦ ((F).map (zigzagBraidComplexXIso₁ k G i).hom).app ((B j).X (-1)) ≫
      ((F).obj Z).map (zigzagBraidComplexXIso₀ k G j).hom ≫ f)
    (zigzagBimoduleLeftUnitor_naturality k G (U j) (zigzagBraidEvaluationHom k G j))).trans
      (congrArg (fun f ↦ ((F).map (zigzagBraidComplexXIso₁ k G i).hom).app ((B j).X (-1)) ≫ f)
        (Category.assoc (((F).obj Z).map (zigzagBraidComplexXIso₀ k G j).hom)
          (zigzagBimoduleLeftUnitor k G (U j)).hom
          (zigzagBraidEvaluationHom k G j)).symm)

/-- Under the component identifications, the mixed differential is the pair of evaluations. -/
theorem zigzagBraidComplexTensor_d (i j : V) :
    (T i j).d (-1) 0 ≫ (zigzagBraidComplexTensorXZeroIso k G i j).hom =
      (zigzagBraidComplexTensorXMinusOneIso k G i j).hom ≫
        biprod.desc (zigzagBraidEvaluationHom k G i) (zigzagBraidEvaluationHom k G j) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [ComplexShape.π_eq_add] at hpq
  by_cases hp : p = -1
  · subst p
    have hq : q = 0 := by omega
    subst q
    rw [HomologicalComplex.mapBifunctor.d_eq]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq (B i) (B j) F c
        (by simp : (c).Rel (-1) 0) 0 0 (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq (B i) (B j) F c (-1)
        (by simp : (c).Rel 0 1) 0 (by simp),
      zigzagBraidComplex_d_eq_zero₀ j 1 (by decide)]
    -- For a cochain totalization, ε₁ is constantly +1. Reduction computes
    -- this scalar in ℤ before applying the first-factor differential.
    simp only [show ComplexShape.ε₁ c c c (-1, 0) = 1 from rfl,
      one_smul, Functor.map_zero, zero_comp, smul_zero, zero_comp, add_zero,
      Category.assoc, ιMapBifunctor_zigzagBraidComplexTensorXZeroIso_hom,
      ιMapBifunctor_zigzagBraidComplexTensorXMinusOneIso_hom_left_assoc,
      biprod.inl_desc]
    simpa only [tensorPairZeroIso_hom, tensorPairLeftIso_hom, Category.assoc] using
      tensorPairLeft_d k G i j
  · by_cases hp' : p = 0
    · subst p
      have hq : q = -1 := by omega
      subst q
      rw [HomologicalComplex.mapBifunctor.d_eq]
      simp only [Preadditive.comp_add, Preadditive.add_comp,
        HomologicalComplex.mapBifunctor.ι_D₁_assoc,
        HomologicalComplex.mapBifunctor.ι_D₂_assoc]
      rw [HomologicalComplex.mapBifunctor.d₁_eq (B i) (B j) F c
          (by simp : (c).Rel 0 1) (-1) 0 (by simp),
        HomologicalComplex.mapBifunctor.d₂_eq (B i) (B j) F c 0
          (by simp : (c).Rel (-1) 0) 0 (by simp),
        zigzagBraidComplex_d_eq_zero₀ i 1 (by decide)]
      -- The second-factor sign is (-1)^p; here the first degree p is 0.
      -- Reduction therefore computes the integer scalar (-1)^0 = +1.
      simp only [show ComplexShape.ε₂ c c c (0, -1) = 1 from rfl,
        one_smul, Functor.map_zero, NatTrans.app_zero, zero_comp, smul_zero,
        zero_comp, zero_add, Category.assoc,
        ιMapBifunctor_zigzagBraidComplexTensorXZeroIso_hom,
        ιMapBifunctor_zigzagBraidComplexTensorXMinusOneIso_hom_right_assoc,
        biprod.inr_desc]
      simpa only [tensorPairZeroIso_hom, tensorPairRightIso_hom, Category.assoc] using
        tensorPairRight_d k G i j
    · exact (isZero_zigzagBraidComplexTensor_pair k G i j p q (by omega)).eq_of_src _ _

/-- The lowest pair summand is identified by the two existing vertex component maps. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTensorXMinusTwoIso_hom (i j : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B j) F c (-1) (-1) (-2) (by simp) ≫
        (zigzagBraidComplexTensorXMinusTwoIso k G i j).hom =
      ((F).flip.obj ((B j).X (-1))).map (zigzagBraidComplexXIso₀ k G i).hom ≫
        ((F).obj (U i)).map (zigzagBraidComplexXIso₀ k G j).hom := by
  simp only [zigzagBraidComplexTensorXMinusTwoIso, Iso.trans_hom,
    HomologicalComplex.ι_mapBifunctorSingleSummandIso_hom_assoc, Functor.mapIso_hom]

end TauCeti
