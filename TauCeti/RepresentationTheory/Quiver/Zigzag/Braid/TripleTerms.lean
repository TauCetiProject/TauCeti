/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Commuting
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor


/-!
# Terms of the actual triple braid complex

The left-associated cochain totalization has terms in degrees −3 through 0.
Its lowest term is the tensor of the three vertex bimodules; its two middle
terms are the three pairwise tensors and the three individual vertex bimodules,
and its degree-zero term is the regular graded bimodule. The component
isomorphisms preserve internal degrees and both outer actions.

These identifications supply the terms for the adjacent braid cancellation.
They reuse the existing degree-zero and degree-minus-one pair comparisons and
Mathlib's additive-functor biproduct comparison. The totalization and its
cohomological signs are the existing Mathlib construction.
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
attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

/-- Select the binary biproduct comparison supplied by tensor additivity. -/
private local instance tensorPreservesBinaryBiproducts
    (M : GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) :
    PreservesBinaryBiproducts ((F).flip.obj M) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

private theorem pairOutside (i j : V) (p q : ℤ)
    (h : ¬ ((p = -1 ∨ p = 0) ∧ (q = -1 ∨ q = 0))) :
    IsZero (((F).obj ((B i).X p)).obj ((B j).X q)) := by
  by_cases hp : p = -1 ∨ p = 0
  · exact ((F).obj ((B i).X p)).map_isZero
      (isZero_zigzagBraidComplex_X j (by omega) (by omega))
  · exact ((F).flip.obj ((B j).X q)).map_isZero
      (isZero_zigzagBraidComplex_X i (by omega) (by omega))

private theorem pairRange (i j : V) (n : ℤ) (h : n < -2 ∨ 0 < n) :
    IsZero ((T i j).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  exact (pairOutside k G i j p q (by omega)).eq_of_src _ _

/-- The actual left-associated signed cochain tensor product of three braid complexes. -/
abbrev zigzagBraidComplexTriple (i j l : V) :
    CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ :=
  HomologicalComplex.mapBifunctor (T i j) (B l) F c

private theorem triplePairOutside (i j l : V) (p q : ℤ)
    (h : ¬ ((-2 ≤ p ∧ p ≤ 0) ∧ (q = -1 ∨ q = 0))) :
    IsZero (((F).obj ((T i j).X p)).obj ((B l).X q)) := by
  by_cases hp : p < -2 ∨ 0 < p
  · exact ((F).flip.obj ((B l).X q)).map_isZero (pairRange k G i j p hp)
  · exact ((F).obj ((T i j).X p)).map_isZero
      (isZero_zigzagBraidComplex_X l (by omega) (by omega))

/-- The actual triple tensor complex vanishes outside cohomological degrees −3 through 0. -/
theorem isZero_zigzagBraidComplexTriple_X (i j l : V) (n : ℤ) (h : n < -3 ∨ 0 < n) :
    IsZero ((zigzagBraidComplexTriple k G i j l).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  exact (triplePairOutside k G i j l p q (by omega)).eq_of_src _ _

private def onePairMap
    (K L : CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ)
    (p₀ q₀ p q : ℤ) :
    ((F).obj (K.X p)).obj (L.X q) ⟶ ((F).obj (K.X p₀)).obj (L.X q₀) := by
  by_cases hp : p = p₀
  · subst p
    by_cases hq : q = q₀
    · subst q
      exact 𝟙 _
    · exact 0
  · exact 0

private theorem onePairMap_eq
    (K L : CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ)
    (p₀ q₀ : ℤ) :
    onePairMap k G K L p₀ q₀ p₀ q₀ = 𝟙 _ := by
  simp only [onePairMap, dite_true]

private def onePairIso
    (K L : CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ)
    (p₀ q₀ n : ℤ)
    (h : p₀ + q₀ = n)
    (hzero : ∀ p q : ℤ, p + q = n → ¬ (p = p₀ ∧ q = q₀) →
      IsZero (((F).obj (K.X p)).obj (L.X q))) :
    (HomologicalComplex.mapBifunctor K L F c).X n ≅
      ((F).obj (K.X p₀)).obj (L.X q₀) where
  hom := HomologicalComplex.mapBifunctorDesc (fun p q _ ↦ onePairMap k G K L p₀ q₀ p q)
  inv := HomologicalComplex.ιMapBifunctor K L F c p₀ q₀ n (by simpa using h)
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n at hpq
    by_cases hp : p = p₀
    · subst p
      have hq : q = q₀ := by omega
      subst q
      simp only [HomologicalComplex.ι_mapBifunctorDesc_assoc, onePairMap_eq,
        Category.id_comp, Category.comp_id]
    · exact (hzero p q hpq (by tauto)).eq_of_src _ _
  inv_hom_id := by
    simp only [HomologicalComplex.ι_mapBifunctorDesc, onePairMap_eq]

/-- The degree-minus-two term of a braid tensor product is the tensor of the vertex bimodules. -/
def zigzagBraidComplexTensorXMinusTwoIso (i j : V) :
    (T i j).X (-2) ≅ ((F).obj (U i)).obj (U j) :=
  onePairIso k G (B i) (B j) (-1) (-1) (-2) (by norm_num)
      (fun p q hpq h ↦ pairOutside k G i j p q (by omega)) ≪≫
    ((F).flip.obj ((B j).X (-1))).mapIso (zigzagBraidComplexXIso₀ k G i) ≪≫
      ((F).obj (U i)).mapIso (zigzagBraidComplexXIso₀ k G j)

/-- The lowest triple term is the left-associated tensor of the three vertex bimodules. -/
def zigzagBraidComplexTripleXMinusThreeIso (i j l : V) :
    (zigzagBraidComplexTriple k G i j l).X (-3) ≅ ((F).obj (((F).obj (U i)).obj (U j))).obj (U l) :=
  onePairIso k G (T i j) (B l) (-2) (-1) (-3) (by norm_num)
      (fun p q hpq h ↦ triplePairOutside k G i j l p q (by omega)) ≪≫
    ((F).flip.obj ((B l).X (-1))).mapIso (zigzagBraidComplexTensorXMinusTwoIso k G i j) ≪≫
      ((F).obj (((F).obj (U i)).obj (U j))).mapIso (zigzagBraidComplexXIso₀ k G l)

/-- The degree-zero triple term is the actual regular graded bimodule. -/
def zigzagBraidComplexTripleXZeroIso (i j l : V) : (zigzagBraidComplexTriple k G i j l).X 0 ≅ Z :=
  onePairIso k G (T i j) (B l) 0 0 0 (by norm_num)
      (fun p q hpq h ↦ triplePairOutside k G i j l p q (by omega)) ≪≫
    ((F).flip.obj ((B l).X 0)).mapIso (zigzagBraidComplexTensorXZeroIso k G i j) ≪≫
      ((F).obj Z).mapIso (zigzagBraidComplexXIso₁ k G l) ≪≫
        zigzagBimoduleLeftUnitor k G Z

private def twoPairMap
    (K L : CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ)
    (p₀ q₀ p₁ q₁ p q : ℤ) :
    ((F).obj (K.X p)).obj (L.X q) ⟶
      ((F).obj (K.X p₀)).obj (L.X q₀) ⊞ ((F).obj (K.X p₁)).obj (L.X q₁) := by
  by_cases hp : p = p₀
  · subst p
    by_cases hq : q = q₀
    · subst q
      exact biprod.inl
    · exact 0
  · by_cases hp' : p = p₁
    · subst p
      by_cases hq : q = q₁
      · subst q
        exact biprod.inr
      · exact 0
    · exact 0

private theorem twoPairMap_left
    (K L : CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ)
    (p₀ q₀ p₁ q₁ : ℤ) : twoPairMap k G K L p₀ q₀ p₁ q₁ p₀ q₀ = biprod.inl := by
  simp only [twoPairMap, dite_true]

private theorem twoPairMap_right
    (K L : CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ)
    (p₀ q₀ p₁ q₁ : ℤ) (hp : p₁ ≠ p₀) :
    twoPairMap k G K L p₀ q₀ p₁ q₁ p₁ q₁ = biprod.inr := by
  simp only [twoPairMap, hp, dite_false, dite_true]

private def twoPairIso
    (K L : CochainComplex (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece) ℤ)
    (p₀ q₀ p₁ q₁ n : ℤ) (h₀ : p₀ + q₀ = n) (h₁ : p₁ + q₁ = n) (hne : p₁ ≠ p₀)
    (hzero : ∀ p q : ℤ, p + q = n →
      ¬ ((p = p₀ ∧ q = q₀) ∨ (p = p₁ ∧ q = q₁)) →
        IsZero (((F).obj (K.X p)).obj (L.X q))) :
    (HomologicalComplex.mapBifunctor K L F c).X n ≅
      ((F).obj (K.X p₀)).obj (L.X q₀) ⊞ ((F).obj (K.X p₁)).obj (L.X q₁) where
  hom := HomologicalComplex.mapBifunctorDesc
    (fun p q _ ↦ twoPairMap k G K L p₀ q₀ p₁ q₁ p q)
  inv := biprod.desc
    (HomologicalComplex.ιMapBifunctor K L F c p₀ q₀ n (by simpa using h₀))
    (HomologicalComplex.ιMapBifunctor K L F c p₁ q₁ n (by simpa using h₁))
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n at hpq
    by_cases hp : p = p₀
    · subst p
      have hq : q = q₀ := by omega
      subst q
      simp only [HomologicalComplex.ι_mapBifunctorDesc_assoc, twoPairMap_left,
        biprod.inl_desc, Category.comp_id]
    · by_cases hp' : p = p₁
      · subst p
        have hq : q = q₁ := by omega
        subst q
        simp only [HomologicalComplex.ι_mapBifunctorDesc_assoc,
          twoPairMap_right k G K L p₀ q₀ p₁ q₁ hne, biprod.inr_desc, Category.comp_id]
      · exact (hzero p q hpq (by tauto)).eq_of_src _ _
  inv_hom_id := by
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc, HomologicalComplex.ι_mapBifunctorDesc,
        twoPairMap_left, Category.comp_id]
    · simp only [biprod.inr_desc_assoc, HomologicalComplex.ι_mapBifunctorDesc,
        twoPairMap_right k G K L p₀ q₀ p₁ q₁ hne, Category.comp_id]

/-- The degree-minus-two triple term consists of the three pairwise vertex tensor products. -/
def zigzagBraidComplexTripleXMinusTwoIso (i j l : V) :
    (zigzagBraidComplexTriple k G i j l).X (-2) ≅
      ((F).obj (U i)).obj (U j) ⊞
        (((F).obj (U i)).obj (U l) ⊞ ((F).obj (U j)).obj (U l)) :=
  twoPairIso k G (T i j) (B l) (-2) 0 (-1) (-1) (-2)
      (by norm_num) (by norm_num) (by norm_num)
      (fun p q hpq h ↦ triplePairOutside k G i j l p q (by omega)) ≪≫
    biprod.mapIso
      (((F).flip.obj ((B l).X 0)).mapIso (zigzagBraidComplexTensorXMinusTwoIso k G i j) ≪≫
        ((F).obj (((F).obj (U i)).obj (U j))).mapIso (zigzagBraidComplexXIso₁ k G l) ≪≫
          zigzagBimoduleRightUnitor k G (((F).obj (U i)).obj (U j)))
      (((F).flip.obj ((B l).X (-1))).mapIso
          (zigzagBraidComplexTensorXMinusOneIso k G i j) ≪≫
        ((F).obj (U i ⊞ U j)).mapIso (zigzagBraidComplexXIso₀ k G l) ≪≫
          ((F).flip.obj (U l)).mapBiprod (U i) (U j))

/-- The degree-minus-one triple term consists of the three vertex bimodules. -/
def zigzagBraidComplexTripleXMinusOneIso (i j l : V) :
    (zigzagBraidComplexTriple k G i j l).X (-1) ≅ (U i ⊞ U j) ⊞ U l :=
  twoPairIso k G (T i j) (B l) (-1) 0 0 (-1) (-1)
      (by norm_num) (by norm_num) (by norm_num)
      (fun p q hpq h ↦ triplePairOutside k G i j l p q (by omega)) ≪≫
    biprod.mapIso
      (((F).flip.obj ((B l).X 0)).mapIso (zigzagBraidComplexTensorXMinusOneIso k G i j) ≪≫
        ((F).obj (U i ⊞ U j)).mapIso (zigzagBraidComplexXIso₁ k G l) ≪≫
          zigzagBimoduleRightUnitor k G (U i ⊞ U j))
      (((F).flip.obj ((B l).X (-1))).mapIso (zigzagBraidComplexTensorXZeroIso k G i j) ≪≫
        ((F).obj Z).mapIso (zigzagBraidComplexXIso₀ k G l) ≪≫
          zigzagBimoduleLeftUnitor k G (U l))

/-- The lowest pair summand is identified by the two existing vertex component maps. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTensorXMinusTwoIso_hom (i j : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B j) F c (-1) (-1) (-2) (by simp) ≫
        (zigzagBraidComplexTensorXMinusTwoIso k G i j).hom =
      ((F).flip.obj ((B j).X (-1))).map (zigzagBraidComplexXIso₀ k G i).hom ≫
        ((F).obj (U i)).map (zigzagBraidComplexXIso₀ k G j).hom := by
  simp only [zigzagBraidComplexTensorXMinusTwoIso, Iso.trans_hom, onePairIso,
    HomologicalComplex.ι_mapBifunctorDesc_assoc,
    onePairMap_eq, Category.id_comp, Functor.mapIso_hom]

/-- The lowest triple summand uses the pair comparison followed by the third vertex map. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTripleXMinusThreeIso_hom (i j l : V) :
    HomologicalComplex.ιMapBifunctor (T i j) (B l) F c (-2) (-1) (-3) (by simp) ≫
        (zigzagBraidComplexTripleXMinusThreeIso k G i j l).hom =
      ((F).flip.obj ((B l).X (-1))).map
          (zigzagBraidComplexTensorXMinusTwoIso k G i j).hom ≫
        ((F).obj (((F).obj (U i)).obj (U j))).map (zigzagBraidComplexXIso₀ k G l).hom := by
  simp only [zigzagBraidComplexTripleXMinusThreeIso, Iso.trans_hom, onePairIso,
    HomologicalComplex.ι_mapBifunctorDesc_assoc,
    onePairMap_eq, Category.id_comp, Functor.mapIso_hom]

/-- The degree-zero triple summand is identified by the regular pair map and left unitor. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTripleXZeroIso_hom (i j l : V) :
    HomologicalComplex.ιMapBifunctor (T i j) (B l) F c 0 0 0 (by simp) ≫
        (zigzagBraidComplexTripleXZeroIso k G i j l).hom =
      ((F).flip.obj ((B l).X 0)).map (zigzagBraidComplexTensorXZeroIso k G i j).hom ≫
        ((F).obj Z).map (zigzagBraidComplexXIso₁ k G l).hom ≫
          (zigzagBimoduleLeftUnitor k G Z).hom := by
  simp only [zigzagBraidComplexTripleXZeroIso, Iso.trans_hom, onePairIso,
    HomologicalComplex.ι_mapBifunctorDesc_assoc,
    onePairMap_eq, Category.id_comp, Functor.mapIso_hom]
  rfl

/-- The pair of the first two vertices is the first summand of the degree-minus-two term. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTripleXMinusTwoIso_hom_left (i j l : V) :
    HomologicalComplex.ιMapBifunctor (T i j) (B l) F c (-2) 0 (-2) (by simp) ≫
        (zigzagBraidComplexTripleXMinusTwoIso k G i j l).hom =
      ((F).flip.obj ((B l).X 0)).map (zigzagBraidComplexTensorXMinusTwoIso k G i j).hom ≫
        ((F).obj (((F).obj (U i)).obj (U j))).map (zigzagBraidComplexXIso₁ k G l).hom ≫
          (zigzagBimoduleRightUnitor k G (((F).obj (U i)).obj (U j))).hom ≫ biprod.inl := by
  simp only [zigzagBraidComplexTripleXMinusTwoIso, Iso.trans_hom, twoPairIso,
    Category.assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc, twoPairMap_left,
    biprod.mapIso_hom, biprod.inl_map, Functor.mapIso_hom]
  rfl

/-- The other two pairwise tensors form the second summand of the degree-minus-two term. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTripleXMinusTwoIso_hom_right (i j l : V) :
    HomologicalComplex.ιMapBifunctor (T i j) (B l) F c (-1) (-1) (-2) (by simp) ≫
        (zigzagBraidComplexTripleXMinusTwoIso k G i j l).hom =
      ((F).flip.obj ((B l).X (-1))).map
          (zigzagBraidComplexTensorXMinusOneIso k G i j).hom ≫
        ((F).obj (U i ⊞ U j)).map (zigzagBraidComplexXIso₀ k G l).hom ≫
          biprod.lift (((F).flip.obj (U l)).map biprod.fst)
            (((F).flip.obj (U l)).map biprod.snd) ≫ biprod.inr := by
  simp only [zigzagBraidComplexTripleXMinusTwoIso, Iso.trans_hom, twoPairIso,
    Category.assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc,
    twoPairMap_right k G (T i j) (B l) (-2) 0 (-1) (-1) (by decide),
    biprod.mapIso_hom, biprod.inr_map, Functor.mapIso_hom, Functor.mapBiprod_hom]
  rfl

/-- The first two vertex terms form the first summand of the degree-minus-one term. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTripleXMinusOneIso_hom_left (i j l : V) :
    HomologicalComplex.ιMapBifunctor (T i j) (B l) F c (-1) 0 (-1) (by simp) ≫
        (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom =
      ((F).flip.obj ((B l).X 0)).map (zigzagBraidComplexTensorXMinusOneIso k G i j).hom ≫
        ((F).obj (U i ⊞ U j)).map (zigzagBraidComplexXIso₁ k G l).hom ≫
          (zigzagBimoduleRightUnitor k G (U i ⊞ U j)).hom ≫ biprod.inl := by
  simp only [zigzagBraidComplexTripleXMinusOneIso, Iso.trans_hom, twoPairIso,
    Category.assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc, twoPairMap_left,
    biprod.mapIso_hom, biprod.inl_map, Functor.mapIso_hom]
  rfl

/-- The third vertex term is the second summand of the degree-minus-one term. -/
@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidComplexTripleXMinusOneIso_hom_right (i j l : V) :
    HomologicalComplex.ιMapBifunctor (T i j) (B l) F c 0 (-1) (-1) (by simp) ≫
        (zigzagBraidComplexTripleXMinusOneIso k G i j l).hom =
      ((F).flip.obj ((B l).X (-1))).map (zigzagBraidComplexTensorXZeroIso k G i j).hom ≫
        ((F).obj Z).map (zigzagBraidComplexXIso₀ k G l).hom ≫
          (zigzagBimoduleLeftUnitor k G (U l)).hom ≫ biprod.inr := by
  simp only [zigzagBraidComplexTripleXMinusOneIso, Iso.trans_hom, twoPairIso,
    Category.assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc,
    twoPairMap_right k G (T i j) (B l) (-1) 0 0 (-1) (by decide),
    biprod.mapIso_hom, biprod.inr_map, Functor.mapIso_hom]
  rfl

end TauCeti
