/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Unit
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Commutation of nonadjacent graded zigzag braid complexes

For distinct nonadjacent vertices, the actual tensor product of braid complexes has
only the mixed vertex terms and the regular bimodule term. Unit identifications put
these terms in the two-term complex with differential given by the two evaluations.
Swapping the two vertex summands then gives commutation.

The component identifications describe the commuting map explicitly: in degree zero it
is the identity of the regular bimodule, and in degree minus one it exchanges the two
vertex summands by the biproduct braiding. The supported totalization-inclusion formulas
identify each individual tensor summand with its unit or vertex component.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "F" => zigzagBimoduleTensor k G
local notation "Z" => zigzagGradedBimodule k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "B" => zigzagBraidComplex k G
local notation "T" => zigzagBraidComplexTensor k G
local notation "c" => ComplexShape.up ℤ

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

private theorem isZero_tensorPair_of_not_support (i j : V) (p q : ℤ)
    (h : ¬ ((p = -1 ∨ p = 0) ∧ (q = -1 ∨ q = 0))) :
    IsZero (((F).obj ((B i).X p)).obj ((B j).X q)) := by
  by_cases hp : p = -1 ∨ p = 0
  · exact ((F).obj ((B i).X p)).map_isZero
      (isZero_zigzagBraidComplex_X j (by omega) (by omega))
  · exact ((F).flip.obj ((B j).X q)).map_isZero
      (isZero_zigzagBraidComplex_X i (by omega) (by omega))

private def tensorZeroMap (i j : V) (p q : ℤ) :
    ((F).obj ((B i).X p)).obj ((B j).X q) ⟶ Z := by
  by_cases hp : p = 0
  · subst p
    by_cases hq : q = 0
    · subst q
      exact (tensorPairZeroIso k G i j).hom
    · exact 0
  · exact 0

private def tensorZeroHom (i j : V) : (T i j).X 0 ⟶ Z :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ tensorZeroMap k G i j p q)

private theorem tensorZeroMap_zero_zero (i j : V) :
    tensorZeroMap k G i j 0 0 = (tensorPairZeroIso k G i j).hom := by
  simp only [tensorZeroMap, dite_true]

private def tensorZeroInv (i j : V) : Z ⟶ (T i j).X 0 :=
  (tensorPairZeroIso k G i j).inv ≫
    HomologicalComplex.ιMapBifunctor (B i) (B j) F c 0 0 0 (by simp)

/-- The degree-zero term of the actual braid tensor product is the regular bimodule. -/
def zigzagBraidComplexTensorXZeroIso (i j : V) : (T i j).X 0 ≅ Z where
  hom := tensorZeroHom k G i j
  inv := tensorZeroInv k G i j
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    -- The cochain totalization index is the sum of the two integer degrees.
    change p + q = 0 at hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = 0 := by omega
      subst q
      simp only [tensorZeroHom, tensorZeroInv,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, tensorZeroMap_zero_zero,
        Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (isZero_tensorPair_of_not_support k G i j p q (by omega)).eq_of_src _ _
  inv_hom_id := by
    simp only [tensorZeroHom, tensorZeroInv, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, tensorZeroMap_zero_zero, Iso.inv_hom_id]

/-- The regular summand in degree zero evaluates through the two component unit maps. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTensorXZeroIso_hom (i j : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B j) F c 0 0 0 (by simp) ≫
        (zigzagBraidComplexTensorXZeroIso k G i j).hom =
      ((((F).flip.obj ((B j).X 0)).mapIso (zigzagBraidComplexXIso₁ k G i) ≪≫
        ((F).obj Z).mapIso (zigzagBraidComplexXIso₁ k G j)) ≪≫
          zigzagBimoduleLeftUnitor k G Z).hom := by
  -- Expose the constructed hom projections as the desc map and unit comparison
  -- so the totalization summand-inclusion equation computes the regular summand.
  change HomologicalComplex.ιMapBifunctor (B i) (B j) F c 0 0 0 (by simp) ≫
      tensorZeroHom k G i j = (tensorPairZeroIso k G i j).hom
  simp only [tensorZeroHom, HomologicalComplex.ι_mapBifunctorDesc,
    tensorZeroMap_zero_zero]

private def tensorMinusOneMap (i j : V) (p q : ℤ) :
    ((F).obj ((B i).X p)).obj ((B j).X q) ⟶ U i ⊞ U j := by
  by_cases hp : p = -1
  · subst p
    by_cases hq : q = 0
    · subst q
      exact (tensorPairLeftIso k G i j).hom ≫ biprod.inl
    · exact 0
  · by_cases hp' : p = 0
    · subst p
      by_cases hq : q = -1
      · subst q
        exact (tensorPairRightIso k G i j).hom ≫ biprod.inr
      · exact 0
    · exact 0

private def tensorMinusOneHom (i j : V) : (T i j).X (-1) ⟶ U i ⊞ U j :=
  HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ tensorMinusOneMap k G i j p q)

private theorem tensorMinusOneMap_left (i j : V) :
    tensorMinusOneMap k G i j (-1) 0 = (tensorPairLeftIso k G i j).hom ≫ biprod.inl := by
  simp only [tensorMinusOneMap, dite_true]

private theorem tensorMinusOneMap_right (i j : V) :
    tensorMinusOneMap k G i j 0 (-1) = (tensorPairRightIso k G i j).hom ≫ biprod.inr := by
  simp only [tensorMinusOneMap, show (0 : ℤ) ≠ -1 by decide, dite_false, dite_true]

private def tensorMinusOneInv (i j : V) : U i ⊞ U j ⟶ (T i j).X (-1) :=
  biprod.desc
    ((tensorPairLeftIso k G i j).inv ≫
      HomologicalComplex.ιMapBifunctor (B i) (B j) F c (-1) 0 (-1) (by simp))
    ((tensorPairRightIso k G i j).inv ≫
      HomologicalComplex.ιMapBifunctor (B i) (B j) F c 0 (-1) (-1) (by simp))

/-- The degree-minus-one term is the biproduct of the two actual vertex bimodules. -/
def zigzagBraidComplexTensorXMinusOneIso (i j : V) : (T i j).X (-1) ≅ U i ⊞ U j where
  hom := tensorMinusOneHom k G i j
  inv := tensorMinusOneInv k G i j
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    -- The cochain totalization index is the sum of the two integer degrees.
    change p + q = -1 at hpq
    by_cases hp : p = -1
    · subst p
      have hq : q = 0 := by omega
      subst q
      simp only [tensorMinusOneHom, tensorMinusOneInv, Category.assoc,
        HomologicalComplex.ι_mapBifunctorDesc_assoc, tensorMinusOneMap_left,
        biprod.inl_desc, Iso.hom_inv_id_assoc, Category.comp_id]
    · by_cases hp' : p = 0
      · subst p
        have hq : q = -1 := by omega
        subst q
        simp only [tensorMinusOneHom, tensorMinusOneInv, Category.assoc,
          HomologicalComplex.ι_mapBifunctorDesc_assoc, tensorMinusOneMap_right,
          biprod.inr_desc, Iso.hom_inv_id_assoc, Category.comp_id]
      · exact (isZero_tensorPair_of_not_support k G i j p q (by omega)).eq_of_src _ _
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp only [tensorMinusOneHom, tensorMinusOneInv, Category.assoc,
        biprod.inl_desc_assoc, HomologicalComplex.ι_mapBifunctorDesc,
        tensorMinusOneMap_left, Iso.inv_hom_id_assoc, Category.comp_id]
    · simp only [tensorMinusOneHom, tensorMinusOneInv, Category.assoc,
        biprod.inr_desc_assoc, HomologicalComplex.ι_mapBifunctorDesc,
        tensorMinusOneMap_right, Iso.inv_hom_id_assoc, Category.comp_id]

/-- The `(-1,0)` summand identifies with the first vertex summand via the right unitor. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTensorXMinusOneIso_hom_left (i j : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B j) F c (-1) 0 (-1) (by simp) ≫
        (zigzagBraidComplexTensorXMinusOneIso k G i j).hom =
      ((((F).flip.obj ((B j).X 0)).mapIso (zigzagBraidComplexXIso₀ k G i) ≪≫
        ((F).obj (U i)).mapIso (zigzagBraidComplexXIso₁ k G j)) ≪≫
          zigzagBimoduleRightUnitor k G (U i)).hom ≫ biprod.inl := by
  -- Expose the constructed hom projections as the desc map and right-unit comparison
  -- so the (-1,0) summand-inclusion equation computes the first biproduct summand.
  change HomologicalComplex.ιMapBifunctor (B i) (B j) F c (-1) 0 (-1) (by simp) ≫
      tensorMinusOneHom k G i j = (tensorPairLeftIso k G i j).hom ≫ biprod.inl
  simp only [tensorMinusOneHom, HomologicalComplex.ι_mapBifunctorDesc,
    tensorMinusOneMap_left]

/-- The `(0,-1)` summand identifies with the second vertex summand via the left unitor. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTensorXMinusOneIso_hom_right (i j : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B j) F c 0 (-1) (-1) (by simp) ≫
        (zigzagBraidComplexTensorXMinusOneIso k G i j).hom =
      ((((F).flip.obj ((B j).X (-1))).mapIso (zigzagBraidComplexXIso₁ k G i) ≪≫
        ((F).obj Z).mapIso (zigzagBraidComplexXIso₀ k G j)) ≪≫
          zigzagBimoduleLeftUnitor k G (U j)).hom ≫ biprod.inr := by
  -- Expose the constructed hom projections as the desc map and left-unit comparison
  -- so the (0,-1) summand-inclusion equation computes the second biproduct summand.
  change HomologicalComplex.ιMapBifunctor (B i) (B j) F c 0 (-1) (-1) (by simp) ≫
      tensorMinusOneHom k G i j = (tensorPairRightIso k G i j).hom ≫ biprod.inr
  simp only [tensorMinusOneHom, HomologicalComplex.ι_mapBifunctorDesc,
    tensorMinusOneMap_right]

private theorem tensorPairLeft_d (i j : V) :
    (((F).map ((B i).d (-1) 0)).app ((B j).X 0)) ≫ (tensorPairZeroIso k G i j).hom =
      (tensorPairLeftIso k G i j).hom ≫ zigzagBraidEvaluationHom k G i := by
  -- Flatten the component isomorphisms to expose the right-unit naturality square.
  change ((F).map ((B i).d (-1) 0)).app ((B j).X 0) ≫
      ((F).map (zigzagBraidComplexXIso₁ k G i).hom).app ((B j).X 0) ≫
        ((F).obj Z).map (zigzagBraidComplexXIso₁ k G j).hom ≫
          (zigzagBimoduleLeftUnitor k G Z).hom =
    (((F).map (zigzagBraidComplexXIso₀ k G i).hom).app ((B j).X 0) ≫
      ((F).obj (U i)).map (zigzagBraidComplexXIso₁ k G j).hom ≫
        (zigzagBimoduleRightUnitor k G (U i)).hom) ≫ zigzagBraidEvaluationHom k G i
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
  -- Flatten the component isomorphisms to expose the left-unit naturality square.
  change ((F).obj ((B i).X 0)).map ((B j).d (-1) 0) ≫
      ((F).map (zigzagBraidComplexXIso₁ k G i).hom).app ((B j).X 0) ≫
        ((F).obj Z).map (zigzagBraidComplexXIso₁ k G j).hom ≫
          (zigzagBimoduleLeftUnitor k G Z).hom =
    (((F).map (zigzagBraidComplexXIso₁ k G i).hom).app ((B j).X (-1)) ≫
      ((F).obj Z).map (zigzagBraidComplexXIso₀ k G j).hom ≫
        (zigzagBimoduleLeftUnitor k G (U j)).hom) ≫ zigzagBraidEvaluationHom k G j
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
  -- The component isomorphisms were constructed with these totalization desc maps.
  change (T i j).d (-1) 0 ≫ tensorZeroHom k G i j =
    tensorMinusOneHom k G i j ≫
      biprod.desc (zigzagBraidEvaluationHom k G i) (zigzagBraidEvaluationHom k G j)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  -- The cochain totalization index is the sum of the two integer degrees.
  change p + q = -1 at hpq
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
    simp only [show ComplexShape.ε₁ c c c (-1, 0) = 1 from rfl,
      one_smul, Functor.map_zero, zero_comp, smul_zero, zero_comp, add_zero,
      tensorZeroHom, tensorMinusOneHom, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc,
      HomologicalComplex.ι_mapBifunctorDesc_assoc,
      tensorZeroMap_zero_zero, tensorMinusOneMap_left, biprod.inl_desc]
    exact tensorPairLeft_d k G i j
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
      simp only [show ComplexShape.ε₂ c c c (0, -1) = 1 from rfl,
        one_smul, Functor.map_zero, NatTrans.app_zero, zero_comp, smul_zero,
        zero_comp, zero_add, tensorZeroHom, tensorMinusOneHom, Category.assoc,
        HomologicalComplex.ι_mapBifunctorDesc,
        HomologicalComplex.ι_mapBifunctorDesc_assoc,
        tensorZeroMap_zero_zero, tensorMinusOneMap_right, biprod.inr_desc]
      exact tensorPairRight_d k G i j
    · exact (isZero_tensorPair_of_not_support k G i j p q (by omega)).eq_of_src _ _

private def commutingNormal (i j : V) :
    HomologicalComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) c :=
  HomologicalComplex.double
    (biprod.desc (zigzagBraidEvaluationHom k G i) (zigzagBraidEvaluationHom k G j))
    (i₀ := -1) (i₁ := 0) (by simp)

private def normalXMinusOneIso (i j : V) : (commutingNormal k G i j).X (-1) ≅ U i ⊞ U j :=
  HomologicalComplex.doubleXIso₀ _ _

private def normalXZeroIso (i j : V) : (commutingNormal k G i j).X 0 ≅ Z :=
  HomologicalComplex.doubleXIso₁ _ _ (by decide)

private theorem normal_d (i j : V) :
    (commutingNormal k G i j).d (-1) 0 =
      (normalXMinusOneIso k G i j).hom ≫
        biprod.desc (zigzagBraidEvaluationHom k G i) (zigzagBraidEvaluationHom k G j) ≫
          (normalXZeroIso k G i j).inv :=
  HomologicalComplex.double_d _ _ (by decide)

private theorem isZero_normal_X (i j : V) (p : ℤ) (h₀ : p ≠ -1) (h₁ : p ≠ 0) :
    IsZero ((commutingNormal k G i j).X p) :=
  HomologicalComplex.isZero_double_X _ _ p h₀ h₁

private def tensorNormalComponentIso (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) (p : ℤ) :
    (T i j).X p ≅ (commutingNormal k G i j).X p := by
  by_cases h₀ : p = -1
  · subst p
    exact zigzagBraidComplexTensorXMinusOneIso k G i j ≪≫
      (normalXMinusOneIso k G i j).symm
  · by_cases h₁ : p = 0
    · subst p
      exact zigzagBraidComplexTensorXZeroIso k G i j ≪≫ (normalXZeroIso k G i j).symm
    · exact (isZero_zigzagBraidComplexTensor_X_of_ne_of_not_adj hij hadj h₀ h₁).iso
        (isZero_normal_X k G i j p h₀ h₁)

private def tensorNormalIso (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    T i j ≅ commutingNormal k G i j :=
  HomologicalComplex.Hom.isoOfComponents (tensorNormalComponentIso k G i j hij hadj) (by
    intro p q hpq
    -- Successive integer cochain degrees differ by one.
    change p + 1 = q at hpq
    by_cases hp : p = -1
    · subst p
      have hq : q = 0 := by omega
      subst q
      -- Compute the two supported components of the componentwise isomorphism.
      change ((zigzagBraidComplexTensorXMinusOneIso k G i j).hom ≫
          (normalXMinusOneIso k G i j).inv) ≫ (commutingNormal k G i j).d (-1) 0 =
        (T i j).d (-1) 0 ≫ (zigzagBraidComplexTensorXZeroIso k G i j).hom ≫
          (normalXZeroIso k G i j).inv
      rw [normal_d]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact congrArg (fun f ↦ f ≫ (normalXZeroIso k G i j).inv)
        (zigzagBraidComplexTensor_d k G i j).symm
    · by_cases hp' : p = 0
      · exact (isZero_normal_X k G i j q (by omega) (by omega)).eq_of_tgt _ _
      · exact (isZero_zigzagBraidComplexTensor_X_of_ne_of_not_adj hij hadj hp hp').eq_of_src _ _)

private theorem braiding_evaluations (i j : V) :
    (biprod.braiding (U i) (U j)).hom ≫
        biprod.desc (zigzagBraidEvaluationHom k G j) (zigzagBraidEvaluationHom k G i) =
      biprod.desc (zigzagBraidEvaluationHom k G i) (zigzagBraidEvaluationHom k G j) := by
  apply biprod.hom_ext' <;> simp [biprod.braiding_hom]

private def normalSwapComponentIso (i j : V) (p : ℤ) :
    (commutingNormal k G i j).X p ≅ (commutingNormal k G j i).X p := by
  by_cases h₀ : p = -1
  · subst p
    exact normalXMinusOneIso k G i j ≪≫ biprod.braiding (U i) (U j) ≪≫
      (normalXMinusOneIso k G j i).symm
  · by_cases h₁ : p = 0
    · subst p
      exact normalXZeroIso k G i j ≪≫ (normalXZeroIso k G j i).symm
    · exact (isZero_normal_X k G i j p h₀ h₁).iso (isZero_normal_X k G j i p h₀ h₁)

private def normalSwapIso (i j : V) : commutingNormal k G i j ≅ commutingNormal k G j i :=
  HomologicalComplex.Hom.isoOfComponents (normalSwapComponentIso k G i j) (by
    intro p q hpq
    -- Successive integer cochain degrees differ by one.
    change p + 1 = q at hpq
    by_cases hp : p = -1
    · subst p
      have hq : q = 0 := by omega
      subst q
      -- Compute the two supported components of the summand swap.
      change ((normalXMinusOneIso k G i j).hom ≫ (biprod.braiding (U i) (U j)).hom ≫
          (normalXMinusOneIso k G j i).inv) ≫ (commutingNormal k G j i).d (-1) 0 =
        (commutingNormal k G i j).d (-1) 0 ≫ (normalXZeroIso k G i j).hom ≫
          (normalXZeroIso k G j i).inv
      rw [normal_d, normal_d]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      exact congrArg (fun f ↦ (normalXMinusOneIso k G i j).hom ≫ f ≫
        (normalXZeroIso k G j i).inv) (braiding_evaluations k G i j)
    · by_cases hp' : p = 0
      · exact (isZero_normal_X k G j i q (by omega) (by omega)).eq_of_tgt _ _
      · exact (isZero_normal_X k G i j p hp hp').eq_of_src _ _)

/-- The actual graded braid complexes commute under tensoring at distinct nonadjacent vertices. -/
def zigzagBraidComplexTensorCommIso (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    T i j ≅ T j i :=
  tensorNormalIso k G i j hij hadj ≪≫ normalSwapIso k G i j ≪≫
    (tensorNormalIso k G j i hij.symm (fun h ↦ hadj h.symm)).symm

/-- The nonadjacent commuting isomorphism gives a homotopy equivalence of
actual graded complexes. -/
def zigzagBraidComplexTensorCommHomotopyEquiv (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    HomotopyEquiv (T i j) (T j i) :=
  HomotopyEquiv.ofIso (zigzagBraidComplexTensorCommIso k G i j hij hadj)

/-- In degree zero the commuting map is the identity under the regular-bimodule identifications. -/
@[reassoc (attr := simp)]
theorem zigzagBraidComplexTensorCommIso_hom_f_zero
    (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    (zigzagBraidComplexTensorCommIso k G i j hij hadj).hom.f 0 ≫
        (zigzagBraidComplexTensorXZeroIso k G j i).hom =
      (zigzagBraidComplexTensorXZeroIso k G i j).hom := by
  -- Compute the supported components of the three componentwise isomorphisms.
  change ((zigzagBraidComplexTensorXZeroIso k G i j).hom ≫ (normalXZeroIso k G i j).inv) ≫
      ((normalXZeroIso k G i j).hom ≫ (normalXZeroIso k G j i).inv) ≫
        ((normalXZeroIso k G j i).hom ≫ (zigzagBraidComplexTensorXZeroIso k G j i).inv) ≫
          (zigzagBraidComplexTensorXZeroIso k G j i).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- In degree minus one the commuting map exchanges the vertex summands by biproduct braiding. -/
@[reassoc (attr := simp)]
theorem zigzagBraidComplexTensorCommIso_hom_f_minus_one
    (i j : V) (hij : i ≠ j) (hadj : ¬ G.Adj i j) :
    (zigzagBraidComplexTensorCommIso k G i j hij hadj).hom.f (-1) ≫
        (zigzagBraidComplexTensorXMinusOneIso k G j i).hom =
      (zigzagBraidComplexTensorXMinusOneIso k G i j).hom ≫ (biprod.braiding (U i) (U j)).hom := by
  -- The degree-minus-one component swaps the two vertex summands.
  change ((zigzagBraidComplexTensorXMinusOneIso k G i j).hom ≫
      (normalXMinusOneIso k G i j).inv) ≫
        ((normalXMinusOneIso k G i j).hom ≫ (biprod.braiding (U i) (U j)).hom ≫
          (normalXMinusOneIso k G j i).inv) ≫
            ((normalXMinusOneIso k G j i).hom ≫
              (zigzagBraidComplexTensorXMinusOneIso k G j i).inv) ≫
                (zigzagBraidComplexTensorXMinusOneIso k G j i).hom = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end TauCeti
