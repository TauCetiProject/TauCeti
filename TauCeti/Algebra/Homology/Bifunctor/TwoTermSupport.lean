/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import TauCeti.Algebra.Homology.Bifunctor.Support
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Two-term support sequences under cochain bifunctor totalization

The high term of a two-term cochain complex is a subcomplex, and the low term
is its quotient. A zero-preserving bifunctor carries this support sequence to
a natural short exact sequence after cochain totalization. The proof compares
each degree with its two supported summands. Splittings are degreewise data;
they do not assert that the sequence splits as cochain complexes.

Single-row comparisons identify the endpoint functors with shifted row actions.
Specified changes of endpoint functors transport both the short exactness and
the degreewise splitting through an isomorphism of short complexes.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace HomologicalComplex.BifunctorSupport

variable (C₁ : Type*) [Category* C₁] [HasZeroMorphisms C₁]

/-- A cochain complex with two distinct supported rows, its chosen endpoint identifications,
and vanishing differentials required for the high inclusion and low projection. -/
structure TwoTermSupport where
  /-- The supported cochain complex. -/
  K : CochainComplex C₁ ℤ
  /-- The degree of the low term. -/
  a : ℤ
  /-- The degree of the high term. -/
  b : ℤ
  /-- The chosen low-term object. -/
  A : C₁
  /-- The chosen high-term object. -/
  B : C₁
  /-- Identify the actual low term. -/
  low : K.X a ≅ A
  /-- Identify the actual high term. -/
  high : K.X b ≅ B
  /-- The two supported degrees are distinct. -/
  ne : a ≠ b
  /-- All differentials out of the high term vanish. -/
  outgoing : ∀ j, K.d b j = 0
  /-- All differentials into the low term vanish. -/
  incoming : ∀ j, K.d j a = 0
  /-- Every other term is zero. -/
  support : ∀ j, j ≠ a → j ≠ b → IsZero (K.X j)

variable {C₁}
  {C₂ D : Type*} [Category* C₂] [Category* D] [HasZeroMorphisms C₂] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ A, (F.obj A).PreservesZeroMorphisms]
  [∀ (K : CochainComplex C₁ ℤ) (N : CochainComplex C₂ ℤ),
    HasMapBifunctor K N F (ComplexShape.up ℤ)]

local notation "c" => ComplexShape.up ℤ

-- Compute the totalization fields before comparing components.
private abbrev total :
    CochainComplex C₁ ℤ ⥤ CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ :=
  dsimp% only [Functor.map₂CochainComplex, Functor.map₂HomologicalComplex]
    F.map₂CochainComplex

private theorem supportTotalIndex (a j : ℤ) :
    ComplexShape.π c c c (a, j + -a) = j := by
  -- Cochain π is integer addition; expose its definition before the arithmetic solver.
  change a + (j + -a) = j
  omega

private abbrev row (A : C₁) : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ :=
  ((F).obj A).mapHomologicalComplex c

-- Only the zero-map property is needed to map the support short complex.
private local instance tensorCochainPreservesZero :
    (total F).PreservesZeroMorphisms where
  map_zero K L := by
    apply NatTrans.ext
    funext N
    apply Hom.ext
    funext j
    -- Evaluate the curried totalization map and its degree projection to reach
    -- mapBifunctorMap; the inclusion formula applies only after this reduction.
    change (mapBifunctorMap (0 : K ⟶ L) (𝟙 N) (F) c).f j = 0
    apply mapBifunctor.hom_ext
    intro p q hpq
    simp only [ι_mapBifunctorMap, HomologicalComplex.zero_f, Functor.map_zero,
      NatTrans.app_zero, comp_zero, zero_comp]

section SingleRows

variable [HasZeroObject C₁]

private def singleX (A : C₁) (a : ℤ) (N : CochainComplex C₂ ℤ) (q j : ℤ)
    (h : a + q = j) :
    (mapBifunctor ((single C₁ c a).obj A) N (F) c).X j ≅ ((F).obj A).obj (N.X q) :=
  mapBifunctorSingleSummandIso _ N (F) c a q j h (fun p r hpr hne ↦ by
    have hp : p ≠ a := by
      intro hp
      subst p
      -- Reduce the cochain total-index condition to addition so its fixed row cancels.
      change a + r = j at hpr
      exact hne ⟨rfl, add_left_cancel (hpr.trans h.symm)⟩
    exact ((F).flip.obj (N.X r)).map_isZero (isZero_single_obj_X c a A p hp)) ≪≫
      ((F).mapIso (singleObjXSelf c a A)).app (N.X q)

private theorem singleX_inv (A : C₁) (a : ℤ) (N : CochainComplex C₂ ℤ)
    (q j : ℤ)
    (h : a + q = j) :
    (singleX F A a N q j h).inv =
      ((F).map (singleObjXSelf c a A).inv).app (N.X q) ≫
        ιMapBifunctor ((single C₁ c a).obj A) N (F) c a q j h := by
  simp [singleX]

private theorem singleX_inv_d (A : C₁) (a : ℤ) (N : CochainComplex C₂ ℤ)
    (j j' : ℤ) :
    (singleX F A a N (j + -a) j (supportTotalIndex _ _)).inv ≫
        (mapBifunctor ((single C₁ c a).obj A) N (F) c).d j j' =
      (((row F A).obj N)⟦-a⟧).d j j' ≫
        (singleX F A a N (j' + -a) j'
          (supportTotalIndex _ _)).inv := by
  by_cases hjj' : (c).Rel j j'
  · have hqq' : (c).Rel (j + -a) (j' + -a) := by
      -- Cochain shape relations mean successor equality, including the shifted indices.
      change (j + -a) + 1 = j' + -a
      -- Expose the same successor relation in the hypothesis for integer arithmetic.
      change j + 1 = j' at hjj'
      omega
    have hd₁ : mapBifunctor.d₁ ((single C₁ c a).obj A) N (F) c a (j +
      -a) j' = 0 := by
      rw [mapBifunctor.d₁_eq' _ _ _ _ (by simp : (c).Rel a (a + 1))]
      simp
    -- Cochain totalization has vertical sign (-1)^a; a shift by -a has the same sign.
    have hε : ComplexShape.ε₂ c c c (a, j + -a) = a.negOnePow := rfl
    have hd₂ := mapBifunctor.d₂_eq ((single C₁ c a).obj A) N
      (F) c a hqq' j' (supportTotalIndex a j')
    rw [singleX_inv, singleX_inv]
    simp only [Category.assoc, mapBifunctor.d_eq, Preadditive.comp_add,
      mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, hd₁, comp_zero, zero_add,
      hd₂, hε,
      CochainComplex.shiftFunctor_obj_d', Functor.mapHomologicalComplex_obj_d,
      Int.negOnePow_neg, Linear.comp_units_smul, Linear.units_smul_comp]
    rw [← NatTrans.naturality_assoc]
  · simp only [shape _ _ _ hjj', comp_zero, zero_comp]

private def singleRowIso (A : C₁) (a : ℤ) (N : CochainComplex C₂ ℤ) :
    ((total F).obj ((single C₁ c a).obj A)).obj N ≅
      ((row F A).obj N)⟦-a⟧ :=
  (Hom.isoOfComponents
    (C₁ := ((row F A).obj N)⟦-a⟧)
    (C₂ := ((total F).obj
      ((single C₁ c a).obj A)).obj N)
    (fun j ↦ (singleX F A a N (j + -a) j
      (supportTotalIndex _ _)).symm)
    (fun j j' _ ↦ singleX_inv_d F A a N j j')).symm

private theorem singleRowIso_inv_f (A : C₁) (a : ℤ) (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (singleRowIso F A a N).inv.f j =
      ((F).map (singleObjXSelf c a A).inv).app (N.X (j + -a)) ≫
        ιMapBifunctor ((single C₁ c a).obj A) N (F) c a (j + -a) j
          (supportTotalIndex _ _) := by
  exact singleX_inv F A a N (j + -a) j (supportTotalIndex a j)

private def singleRowNatIsoCore (A : C₁) (a : ℤ) :
    (total F).obj ((single C₁ c a).obj A) ≅ row F A ⋙ shiftFunctor _ (-a) :=
  NatIso.ofComponents (singleRowIso F A a) (fun {N N'} f ↦ by
    apply (cancel_epi (singleRowIso F A a N).inv).1
    apply (cancel_mono (singleRowIso F A a N').inv).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id]
    apply Hom.ext
    funext j
    -- Evaluate map₂CochainComplex and the shifted map at a degree; their nested
    -- functor projections must reduce before the totalization inclusion formula applies.
    change (singleRowIso F A a N).inv.f j ≫
        (mapBifunctorMap (𝟙 ((single C₁ c a).obj A)) f
          (F) c).f j =
      (((row F A).map f)⟦-a⟧').f j ≫
        (singleRowIso F A a N').inv.f j
    simp only [singleRowIso_inv_f, Category.assoc, CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplex_map_f]
    have hm := ι_mapBifunctorMap (𝟙 ((single C₁ c a).obj A)) f
      (F) c a (j + -a) j (supportTotalIndex a j)
    simp only [HomologicalComplex.id_f] at hm
    rw [(F).map_id, NatTrans.id_app, id_comp] at hm
    rw [hm, ← NatTrans.naturality_assoc])

/-- Totalization against a single supported row is the corresponding shifted row functor. -/
def singleRowNatIso (A : C₁) (a : ℤ) :
    F.map₂CochainComplex.obj ((single C₁ c a).obj A) ≅
      (F.obj A).mapHomologicalComplex c ⋙ shiftFunctor (CochainComplex D ℤ) (-a) :=
  singleRowNatIsoCore F A a

/-- A row supported in cochain degree zero has the unshifted row functor. -/
def singleRowZeroNatIso (A : C₁) :
    F.map₂CochainComplex.obj ((single C₁ c 0).obj A) ≅
      (F.obj A).mapHomologicalComplex c :=
  singleRowNatIso F A 0 ≪≫
    Functor.isoWhiskerLeft (row F A) (shiftFunctorZero (CochainComplex D ℤ) ℤ) ≪≫
      (row F A).rightUnitor

/-- The supported high term includes as a single-row subcomplex. -/
def supportι (s : TwoTermSupport C₁) : (single C₁ c s.b).obj s.B ⟶ s.K :=
  mkHomFromSingle s.high.inv (fun j _ ↦ by rw [s.outgoing j, comp_zero])

/-- The supported low term is the single-row quotient complex. -/
def supportπ (s : TwoTermSupport C₁) : s.K ⟶ (single C₁ c s.a).obj s.A :=
  mkHomToSingle s.low.hom (fun j _ ↦ by rw [s.incoming j, zero_comp])

/-- The high-row inclusion and low-row projection form a short complex. -/
def shortComplex (s : TwoTermSupport C₁) : ShortComplex (CochainComplex C₁ ℤ)
    :=
  ShortComplex.mk (supportι s) (supportπ s) (by
    apply from_single_hom_ext
    exact (isZero_single_obj_X c s.a s.A s.b s.ne.symm).eq_of_tgt _ _)

/-- Apply cochain totalization to the supported short complex. -/
def mapShortComplex (s : TwoTermSupport C₁) :
    ShortComplex (CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ) :=
  (shortComplex s).map (total F)

end SingleRows

private theorem row_index {a q j : ℤ} (h : a + q = j) : q = j + -a := by
  omega

private def twoSummandX (s : TwoTermSupport C₁) (N : CochainComplex C₂ ℤ) (j :
    ℤ) :
    (mapBifunctor s.K N (F) c).X j ≅
      ((F).obj s.B).obj (N.X (j + -s.b)) ⊞ ((F).obj s.A).obj
        (N.X (j + -s.a)) :=
  mapBifunctorTwoSummandIso s.K N (F) c s.b (j + -s.b) s.a (j + -s.a) j
    (supportTotalIndex _ _)
    (supportTotalIndex _ _)
    (by intro h; exact s.ne (congrArg Prod.fst h))
    (fun p q hpq hne ↦ by
      have hp₀ : p ≠ s.a := by
        intro hp
        subst p
        exact hne (Or.inr ⟨rfl, row_index hpq⟩)
      have hp₁ : p ≠ s.b := by
        intro hp
        subst p
        exact hne (Or.inl ⟨rfl, row_index hpq⟩)
      exact ((F).flip.obj (N.X q)).map_isZero (s.support p hp₀ hp₁)) ≪≫
    biprod.mapIso (((F).mapIso s.high).app (N.X (j + -s.b)))
      (((F).mapIso s.low).app (N.X (j + -s.a)))

private theorem twoSummandX_ι_high (s : TwoTermSupport C₁)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    ιMapBifunctor s.K N (F) c s.b (j + -s.b) j
        (supportTotalIndex s.b j) ≫ (twoSummandX F s N j).hom =
      ((F).map s.high.hom).app (N.X (j + -s.b)) ≫ biprod.inl := by
  dsimp only [twoSummandX, Iso.trans_hom, biprod.mapIso, Functor.mapIso, Iso.app]
  rw [ι_mapBifunctorTwoSummandIso_hom_left_assoc, biprod.inl_map]

private theorem twoSummandX_ι_low (s : TwoTermSupport C₁)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    ιMapBifunctor s.K N (F) c s.a (j + -s.a) j
        (supportTotalIndex s.a j) ≫ (twoSummandX F s N j).hom =
      ((F).map s.low.hom).app (N.X (j + -s.a)) ≫ biprod.inr := by
  dsimp only [twoSummandX, Iso.trans_hom, biprod.mapIso, Functor.mapIso, Iso.app]
  rw [ι_mapBifunctorTwoSummandIso_hom_right_assoc, biprod.inr_map]

variable [HasZeroObject C₁]

private theorem supportι_twoSummandX (s : TwoTermSupport C₁)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (((mapShortComplex F s).f.app N).f j) ≫ (twoSummandX F s N j).hom =
      (singleX F s.B s.b N (j + -s.b) j
        (supportTotalIndex _ _)).hom ≫ biprod.inl := by
  -- Reduce ShortComplex.map and evaluation of the curried totalization functor
  -- to mapBifunctorMap, exposing the support inclusion for its component formula.
  change (mapBifunctorMap (supportι s) (𝟙 N) (F) c).f j ≫
      (twoSummandX F s N j).hom =
    (singleX F s.B s.b N (j + -s.b) j
      (supportTotalIndex s.b j)).hom ≫ biprod.inl
  apply (cancel_epi (singleX F s.B s.b N (j + -s.b) j
    (supportTotalIndex _ _)).inv).1
  simp only [Iso.inv_hom_id_assoc]
  rw [singleX_inv, Category.assoc]
  have hm := ι_mapBifunctorMap (supportι s) (𝟙 N) (F)
    c s.b (j + -s.b) j (supportTotalIndex s.b j)
  simp only [HomologicalComplex.id_f] at hm
  rw [((F).obj (s.K.X s.b)).map_id, id_comp] at hm
  rw [reassoc_of% hm, twoSummandX_ι_high]
  simp only [supportι, mkHomFromSingle_f, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, Iso.map_inv_hom_id_app_assoc]

private theorem supportπ_twoSummandX (s : TwoTermSupport C₁)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (((mapShortComplex F s).g.app N).f j) ≫
        (singleX F s.A s.a N (j + -s.a) j
          (supportTotalIndex _ _)).hom =
      (twoSummandX F s N j).hom ≫ biprod.snd := by
  -- Reduce ShortComplex.map and evaluation of the curried totalization functor
  -- to mapBifunctorMap, exposing the support projection for its component formula.
  change (mapBifunctorMap (supportπ s) (𝟙 N) (F) c).f j ≫
      (singleX F s.A s.a N (j + -s.a) j
        (supportTotalIndex s.a j)).hom =
    (twoSummandX F s N j).hom ≫ biprod.snd
  apply (cancel_mono (singleX F s.A s.a N (j + -s.a) j
    (supportTotalIndex s.a j)).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, comp_id]
  rw [singleX_inv]
  apply mapBifunctor.hom_ext (K₁ := s.K) (K₂ := N) (F := F) («c» := c)
  intro p q hpq
  by_cases hp₀ : p = s.a
  · subst p
    obtain rfl : q = j + -s.a := row_index hpq
    have hm := ι_mapBifunctorMap (supportπ s) (𝟙 N) (F)
      c s.a (j + -s.a) j hpq
    simp only [HomologicalComplex.id_f] at hm
    rw [((F).obj
      (((single C₁ c s.a).obj s.A).X s.a)).map_id, id_comp] at hm
    rw [hm, reassoc_of% (twoSummandX_ι_low F s N j)]
    simp only [supportπ, mkHomToSingle_f, Functor.map_comp, NatTrans.comp_app, Category.assoc,
      biprod.inr_snd_assoc]
  · by_cases hp₁ : p = s.b
    · subst p
      obtain rfl : q = j + -s.b := row_index hpq
      have hπ : (supportπ s).f s.b = 0 :=
        (isZero_single_obj_X c s.a s.A s.b s.ne.symm).eq_of_tgt _ _
      have hm := ι_mapBifunctorMap (supportπ s) (𝟙 N) (F)
        c s.b (j + -s.b) j hpq
      rw [hm, reassoc_of% (twoSummandX_ι_high F s N j)]
      simp only [hπ, Functor.map_zero, NatTrans.app_zero, zero_comp,
        biprod.inl_snd_assoc, comp_zero]
    · have hzero := ((F).flip.obj (N.X q)).map_isZero
        (s.support p hp₀ hp₁)
      exact hzero.eq_of_src _ _

/-- In each cochain degree the mapped support sequence is the canonical biproduct sequence. -/
def mapShortComplexDegreewiseIso (s : TwoTermSupport C₁) (N : CochainComplex C₂ ℤ)
    (j : ℤ) :
    (((mapShortComplex F s).map ((evaluation _ _).obj N)).map (eval D c
      j)) ≅
      ShortComplex.mk
        (biprod.inl : ((F).obj s.B).obj (N.X (j + -s.b)) ⟶
          ((F).obj s.B).obj (N.X (j + -s.b)) ⊞ ((F).obj
            s.A).obj (N.X (j + -s.a)))
        biprod.snd (by simp) :=
  ShortComplex.isoMk
    (singleX F s.B s.b N (j + -s.b) j
      (supportTotalIndex _ _))
    (twoSummandX F s N j)
    (singleX F s.A s.a N (j + -s.a) j
      (supportTotalIndex _ _))
    (supportι_twoSummandX F s N j).symm (supportπ_twoSummandX F s N j).symm

/-- The mapped support sequence has its canonical splitting in each cochain degree. -/
def mapShortComplexDegreewiseSplitting (s : TwoTermSupport C₁)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (((mapShortComplex F s).map ((evaluation _ _).obj N)).map (eval D c
      j)).Splitting :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct
    (((F).obj s.B).obj (N.X (j + -s.b))) (((F).obj s.A).obj
      (N.X (j + -s.a)))).ofIso
      (mapShortComplexDegreewiseIso F s N j).symm

/-- The mapped support short complex is short exact in the functor category. -/
theorem mapShortComplex_shortExact (s : TwoTermSupport C₁) :
    (mapShortComplex F s).ShortExact := by
  apply ShortComplex.shortExact_of_forall_evaluation
  intro N
  apply shortExact_of_degreewise_shortExact
  intro j
  exact (mapShortComplexDegreewiseSplitting F s N j).shortExact

@[simp]
theorem mapShortComplex_X₁ (s : TwoTermSupport C₁) :
    (mapShortComplex F s).X₁ =
      F.map₂CochainComplex.obj ((single C₁ c s.b).obj s.B) := (rfl)

@[simp]
theorem mapShortComplex_X₂ (s : TwoTermSupport C₁) :
    (mapShortComplex F s).X₂ = F.map₂CochainComplex.obj s.K := (rfl)

@[simp]
theorem mapShortComplex_X₃ (s : TwoTermSupport C₁) :
    (mapShortComplex F s).X₃ =
      F.map₂CochainComplex.obj ((single C₁ c s.a).obj s.A) := (rfl)

/-- Replace the two endpoint functors using specified natural isomorphisms. -/
def reframedShortComplex {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (s : TwoTermSupport C₁)
    (u₁ : F.map₂CochainComplex.obj ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.map₂CochainComplex.obj ((single C₁ c s.a).obj s.A) ≅ E₃) :
    ShortComplex (CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ) :=
  ShortComplex.mk
    ((eqToIso (mapShortComplex_X₁ F s) ≪≫ u₁).inv ≫ (mapShortComplex F s).f)
    ((mapShortComplex F s).g ≫ (eqToIso (mapShortComplex_X₃ F s) ≪≫ u₃).hom)
    (by simp [Category.assoc])

/-- The endpoint replacement is isomorphic to the mapped support short complex. -/
def reframedShortComplexIso {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (s : TwoTermSupport C₁)
    (u₁ : F.map₂CochainComplex.obj ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.map₂CochainComplex.obj ((single C₁ c s.a).obj s.A) ≅ E₃) :
    mapShortComplex F s ≅ reframedShortComplex F s u₁ u₃ :=
  ShortComplex.isoMk (eqToIso (mapShortComplex_X₁ F s) ≪≫ u₁) (Iso.refl _)
    (eqToIso (mapShortComplex_X₃ F s) ≪≫ u₃)
    (by simp [reframedShortComplex, Category.assoc])
    (by simp [reframedShortComplex])


@[simp]
theorem reframedShortComplex_X₁ {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (s : TwoTermSupport C₁)
    (u₁ : F.map₂CochainComplex.obj ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.map₂CochainComplex.obj ((single C₁ c s.a).obj s.A) ≅ E₃) :
    (reframedShortComplex F s u₁ u₃).X₁ = E₁ := (rfl)

@[simp]
theorem reframedShortComplex_X₂ {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (s : TwoTermSupport C₁)
    (u₁ : F.map₂CochainComplex.obj ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.map₂CochainComplex.obj ((single C₁ c s.a).obj s.A) ≅ E₃) :
    (reframedShortComplex F s u₁ u₃).X₂ = F.map₂CochainComplex.obj s.K := (rfl)

@[simp]
theorem reframedShortComplex_X₃ {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (s : TwoTermSupport C₁)
    (u₁ : F.map₂CochainComplex.obj ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.map₂CochainComplex.obj ((single C₁ c s.a).obj s.A) ≅ E₃) :
    (reframedShortComplex F s u₁ u₃).X₃ = E₃ := (rfl)

/-- Transport the canonical degreewise splitting through the endpoint-change isomorphism. -/
def reframedShortComplexDegreewiseSplitting
    {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (s : TwoTermSupport C₁)
    (u₁ : F.map₂CochainComplex.obj ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.map₂CochainComplex.obj ((single C₁ c s.a).obj s.A) ≅ E₃)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (((reframedShortComplex F s u₁ u₃).map ((evaluation _ _).obj N)).map
      (eval D c j)).Splitting :=
  (mapShortComplexDegreewiseSplitting F s N j).ofIso
    ((eval D c j).mapShortComplex.mapIso
      (((evaluation _ _).obj N).mapShortComplex.mapIso
        (reframedShortComplexIso F s u₁ u₃)))


private theorem splitting_f_isoBinaryBiproduct (S : ShortComplex D) (h : S.Splitting) :
    S.f ≫ h.isoBinaryBiproduct.hom = biprod.inl := by
  apply biprod.hom_ext <;> simp [ShortComplex.Splitting.isoBinaryBiproduct]

private theorem splitting_isoBinaryBiproduct_hom_snd (S : ShortComplex D) (h : S.Splitting) :
    h.isoBinaryBiproduct.hom ≫ biprod.snd = S.g := by
  simp [ShortComplex.Splitting.isoBinaryBiproduct]

/-- The reframed totalization term is the biproduct of its two public endpoint terms. -/
def reframedShortComplexDegreewiseIso
    {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (s : TwoTermSupport C₁)
    (u₁ : F.map₂CochainComplex.obj ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.map₂CochainComplex.obj ((single C₁ c s.a).obj s.A) ≅ E₃)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    ((reframedShortComplex F s u₁ u₃).X₂.obj N).X j ≅
      ((reframedShortComplex F s u₁ u₃).X₁.obj N).X j ⊞
        ((reframedShortComplex F s u₁ u₃).X₃.obj N).X j :=
  (reframedShortComplexDegreewiseSplitting F s u₁ u₃ N j).isoBinaryBiproduct

/-- The reframed inclusion is the first inclusion under its degreewise comparison. -/
@[reassoc (attr := simp)]
theorem reframedShortComplex_f_degreewiseIso_hom
    {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (s : TwoTermSupport C₁)
    (u₁ : F.map₂CochainComplex.obj ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.map₂CochainComplex.obj ((single C₁ c s.a).obj s.A) ≅ E₃)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (((reframedShortComplex F s u₁ u₃).f.app N).f j) ≫
        (reframedShortComplexDegreewiseIso F s u₁ u₃ N j).hom = biprod.inl := by
  exact splitting_f_isoBinaryBiproduct
    (((reframedShortComplex F s u₁ u₃).map ((evaluation _ _).obj N)).map (eval D c j))
    (reframedShortComplexDegreewiseSplitting F s u₁ u₃ N j)

/-- The reframed projection is the second projection under its degreewise comparison. -/
@[reassoc (attr := simp)]
theorem reframedShortComplex_degreewiseIso_hom_snd
    {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (s : TwoTermSupport C₁)
    (u₁ : F.map₂CochainComplex.obj ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.map₂CochainComplex.obj ((single C₁ c s.a).obj s.A) ≅ E₃)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (reframedShortComplexDegreewiseIso F s u₁ u₃ N j).hom ≫ biprod.snd =
      (((reframedShortComplex F s u₁ u₃).g.app N).f j) := by
  exact splitting_isoBinaryBiproduct_hom_snd
    (((reframedShortComplex F s u₁ u₃).map ((evaluation _ _).obj N)).map (eval D c j))
    (reframedShortComplexDegreewiseSplitting F s u₁ u₃ N j)

end HomologicalComplex.BifunctorSupport
