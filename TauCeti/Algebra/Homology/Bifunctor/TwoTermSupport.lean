/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import TauCeti.Algebra.Homology.Bifunctor.Basic
public import TauCeti.Algebra.Homology.Bifunctor.Support
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Homology.ShortComplex.Splitting

/-!
# Two-term support sequences under cochain bifunctor totalization

The high term of a two-term cochain complex is a subcomplex, and the low term
is its quotient. A zero-preserving bifunctor carries this support sequence to
a natural short exact sequence after cochain totalization. The proof compares
each degree with its two supported summands. Splittings are degreewise data;
they do not assert that the sequence splits as cochain complexes.

Single-row comparisons identify the endpoint functors with shifted row actions.
Specified changes of endpoint functors transport both the short exactness and
the degreewise splitting through an isomorphism of short complexes. Only the chosen
left complex and its two single-row endpoints need totalizations. Row comparisons and
short-complex constructions require a preadditive target; degreewise splittings also
require binary biproducts. Abelian hypotheses enter only the short-exactness theorem.

## Attribution

The single-row component comparison, inverse, differential calculation and
`Hom.isoOfComponents` construction adapt
`CategoryTheory.Functor.mapBifunctorLeftUnitor` in
`TauCeti.Algebra.Homology.Bifunctor.Unitor` to a row in arbitrary cochain degree.
That formalization adapts Mathlib's `CategoryTheory.GradedObject.mapBifunctorLeftUnitor`
and `HomologicalComplex.leftUnitor`, both due to Joël Riou. The original sources are
`Mathlib.CategoryTheory.GradedObject.Unitor` and
`Mathlib.Algebra.Homology.Monoidal`.
The totalization primitives are also Joël Riou's Mathlib bifunctor construction.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex TauCeti

namespace TauCeti

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

namespace TwoTermSupport

variable {C₁} [HasZeroObject C₁]

local notation "c" => ComplexShape.up ℤ

/-- The supported high term includes as a single-row subcomplex. -/
def ι (s : TwoTermSupport C₁) : (single C₁ c s.b).obj s.B ⟶ s.K :=
  mkHomFromSingle s.high.inv (fun j _ ↦ by rw [s.outgoing j, comp_zero])

/-- The supported low term is the single-row quotient complex. -/
def π (s : TwoTermSupport C₁) : s.K ⟶ (single C₁ c s.a).obj s.A :=
  mkHomToSingle s.low.hom (fun j _ ↦ by rw [s.incoming j, zero_comp])

/-- The high-row inclusion is the supplied high-term identification at its supported degree. -/
@[reassoc, simp]
theorem ι_f (s : TwoTermSupport C₁) :
    s.ι.f s.b = (singleObjXSelf c s.b s.B).hom ≫ s.high.inv := by
  simp only [ι, mkHomFromSingle_f]

/-- The low-row projection is the supplied low-term identification at its supported degree. -/
@[reassoc, simp]
theorem π_f (s : TwoTermSupport C₁) :
    s.π.f s.a = s.low.hom ≫ (singleObjXSelf c s.a s.A).inv := by
  simp only [π, mkHomToSingle_f]

/-- The high-row inclusion and low-row projection form a short complex. -/
def shortComplex (s : TwoTermSupport C₁) : ShortComplex (CochainComplex C₁ ℤ) :=
  ShortComplex.mk (ι s) (π s) (by
    apply from_single_hom_ext
    exact (isZero_single_obj_X c s.a s.A s.b s.ne.symm).eq_of_tgt _ _)

@[simp]
theorem shortComplex_X₁ (s : TwoTermSupport C₁) :
    s.shortComplex.X₁ = (single C₁ c s.b).obj s.B := (rfl)

@[simp]
theorem shortComplex_X₂ (s : TwoTermSupport C₁) : s.shortComplex.X₂ = s.K := (rfl)

@[simp]
theorem shortComplex_X₃ (s : TwoTermSupport C₁) :
    s.shortComplex.X₃ = (single C₁ c s.a).obj s.A := (rfl)

-- Normalize the arrow before its endpoint equality transports simplify.
/-- After identifying the endpoints, the support short-complex inclusion is the high map. -/
@[reassoc (attr := simp↓), simp↓]
theorem shortComplex_f (s : TwoTermSupport C₁) :
    s.shortComplex.f ≫ eqToHom (s.shortComplex_X₂) =
      eqToHom (s.shortComplex_X₁) ≫ s.ι := by
  -- The constructor endpoint identifications are reflexive; only the identity laws remain.
  exact (Category.comp_id s.ι).trans (Category.id_comp s.ι).symm

/-- After identifying the endpoints, the support short-complex projection is the low map. -/
@[reassoc (attr := simp↓), simp↓]
theorem shortComplex_g (s : TwoTermSupport C₁) :
    s.shortComplex.g ≫ eqToHom (s.shortComplex_X₃) =
      eqToHom (s.shortComplex_X₂) ≫ s.π := by
  exact (Category.comp_id s.π).trans (Category.id_comp s.π).symm

end TwoTermSupport

end TauCeti

namespace CategoryTheory.Functor

section Preadditive

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ A, (F.obj A).PreservesZeroMorphisms]

local notation "c" => ComplexShape.up ℤ

-- Fixing the left input requires no totalizations for unrelated left complexes.
private abbrev total (K : CochainComplex C₁ ℤ)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor K N F c] :
    CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ :=
  dsimp% only [Functor.mapBifunctorLeft] F.mapBifunctorLeft c c K

private abbrev row (A : C₁) : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ :=
  ((F).obj A).mapHomologicalComplex c

variable [HasZeroObject C₁]

private def singleX (A : C₁) (a : ℤ)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c a).obj A) N F c]
    (N : CochainComplex C₂ ℤ) (q j : ℤ)
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

private theorem singleX_inv (A : C₁) (a : ℤ)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c a).obj A) N F c]
    (N : CochainComplex C₂ ℤ)
    (q j : ℤ)
    (h : a + q = j) :
    (F.singleX A a N q j h).inv =
      ((F).map (singleObjXSelf c a A).inv).app (N.X q) ≫
        ιMapBifunctor ((single C₁ c a).obj A) N (F) c a q j h := by
  simp [singleX]

private theorem singleX_inv_d (A : C₁) (a : ℤ)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c a).obj A) N F c]
    (N : CochainComplex C₂ ℤ)
    (j j' : ℤ) :
    (F.singleX A a N (j + -a) j (add_neg_cancel_comm_assoc _ _)).inv ≫
        (mapBifunctor ((single C₁ c a).obj A) N (F) c).d j j' =
      (((F.row A).obj N)⟦-a⟧).d j j' ≫
        (F.singleX A a N (j' + -a) j'
          (add_neg_cancel_comm_assoc _ _)).inv := by
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
      (F) c a hqq' j' (add_neg_cancel_comm_assoc a j')
    rw [singleX_inv, singleX_inv]
    simp only [Category.assoc, mapBifunctor.d_eq, Preadditive.comp_add,
      mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, hd₁, comp_zero, zero_add,
      hd₂, hε,
      CochainComplex.shiftFunctor_obj_d', Functor.mapHomologicalComplex_obj_d,
      Int.negOnePow_neg, Linear.comp_units_smul, Linear.units_smul_comp]
    rw [← NatTrans.naturality_assoc]
  · simp only [shape _ _ _ hjj', comp_zero, zero_comp]

private def singleRowIso (A : C₁) (a : ℤ)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c a).obj A) N F c]
    (N : CochainComplex C₂ ℤ) :
    (F.total ((single C₁ c a).obj A)).obj N ≅
      ((F.row A).obj N)⟦-a⟧ :=
  (Hom.isoOfComponents
    (C₁ := ((F.row A).obj N)⟦-a⟧)
    (C₂ := (F.total
      ((single C₁ c a).obj A)).obj N)
    (fun j ↦ (F.singleX A a N (j + -a) j
      (add_neg_cancel_comm_assoc _ _)).symm)
    (fun j j' _ ↦ F.singleX_inv_d A a N j j')).symm

private theorem singleRowIso_inv_f (A : C₁) (a : ℤ)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c a).obj A) N F c]
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (F.singleRowIso A a N).inv.f j =
      ((F).map (singleObjXSelf c a A).inv).app (N.X (j + -a)) ≫
        ιMapBifunctor ((single C₁ c a).obj A) N (F) c a (j + -a) j
          (add_neg_cancel_comm_assoc _ _) := by
  exact F.singleX_inv A a N (j + -a) j (add_neg_cancel_comm_assoc a j)

private def mapBifunctorSingleRowNatIsoCore (A : C₁) (a : ℤ)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c a).obj A) N F c] :
    F.total ((single C₁ c a).obj A) ≅ F.row A ⋙ shiftFunctor _ (-a) :=
  NatIso.ofComponents (F.singleRowIso A a) (fun {N N'} f ↦ by
    apply (cancel_epi (F.singleRowIso A a N).inv).1
    apply (cancel_mono (F.singleRowIso A a N').inv).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id]
    apply Hom.ext
    funext j
    -- Evaluate map₂CochainComplex and the shifted map at a degree; their nested
    -- functor projections must reduce before the totalization inclusion formula applies.
    change (F.singleRowIso A a N).inv.f j ≫
        (mapBifunctorMap (𝟙 ((single C₁ c a).obj A)) f
          (F) c).f j =
      (((F.row A).map f)⟦-a⟧').f j ≫
        (F.singleRowIso A a N').inv.f j
    simp only [singleRowIso_inv_f, Category.assoc, CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplex_map_f]
    have hm := ι_mapBifunctorMap (𝟙 ((single C₁ c a).obj A)) f
      (F) c a (j + -a) j (add_neg_cancel_comm_assoc a j)
    simp only [HomologicalComplex.id_f] at hm
    rw [(F).map_id, NatTrans.id_app, id_comp] at hm
    rw [hm, ← NatTrans.naturality_assoc])

/-- Totalization against a single supported row is the corresponding shifted row functor. -/
def mapBifunctorSingleRowNatIso (A : C₁) (a : ℤ)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c a).obj A) N F c] :
    F.mapBifunctorLeft c c ((single C₁ c a).obj A) ≅
      (F.obj A).mapHomologicalComplex c ⋙ shiftFunctor (CochainComplex D ℤ) (-a) :=
  F.mapBifunctorSingleRowNatIsoCore A a

/-- A row supported in cochain degree zero has the unshifted row functor. -/
def mapBifunctorSingleRowZeroNatIso (A : C₁)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c 0).obj A) N F c] :
    F.mapBifunctorLeft c c ((single C₁ c 0).obj A) ≅
      (F.obj A).mapHomologicalComplex c :=
  F.mapBifunctorSingleRowNatIso A 0 ≪≫
    Functor.isoWhiskerLeft (F.row A) (shiftFunctorZero (CochainComplex D ℤ) ℤ) ≪≫
      (F.row A).rightUnitor

/-- The inverse row comparison includes its supported totalization summand. -/
@[reassoc, simp]
theorem mapBifunctorSingleRowNatIso_inv_app_f (A : C₁) (a : ℤ)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c a).obj A) N F c]
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    ((F.mapBifunctorSingleRowNatIso A a).inv.app N).f j =
      (F.map (singleObjXSelf c a A).inv).app (N.X (j + -a)) ≫
        ιMapBifunctor ((single C₁ c a).obj A) N F c a (j + -a) j
          -- For cochain up ℤ, ComplexShape.π is addition of the two integer indices.
          (by change a + (j + -a) = j; omega) := by
  exact F.singleRowIso_inv_f A a N j

/-- The row comparison sends the supported inclusion to the row-object identification. -/
@[reassoc (attr := simp), simp]
theorem ι_mapBifunctorSingleRowNatIso_hom_app_f (A : C₁) (a : ℤ)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c a).obj A) N F c]
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    ιMapBifunctor ((single C₁ c a).obj A) N F c a (j + -a) j
        -- For cochain up ℤ, ComplexShape.π is addition of the two integer indices.
        (by change a + (j + -a) = j; omega) ≫
        ((F.mapBifunctorSingleRowNatIso A a).hom.app N).f j =
      (F.map (singleObjXSelf c a A).hom).app (N.X (j + -a)) := by
  apply (cancel_epi ((F.map (singleObjXSelf c a A).inv).app (N.X (j + -a)))).1
  rw [← Category.assoc, ← mapBifunctorSingleRowNatIso_inv_app_f]
  simp only [← HomologicalComplex.comp_f, Iso.inv_hom_id_app,
    HomologicalComplex.id_f, Iso.map_inv_hom_id_app]
  rfl

/-- The inverse degree-zero comparison includes the unshifted supported summand. -/
@[reassoc, simp]
theorem mapBifunctorSingleRowZeroNatIso_inv_app_f (A : C₁)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c 0).obj A) N F c]
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    ((F.mapBifunctorSingleRowZeroNatIso A).inv.app N).f j =
      (F.map (singleObjXSelf c 0 A).inv).app (N.X j) ≫
        ιMapBifunctor ((single C₁ c 0).obj A) N F c 0 j j
          -- For cochain up ℤ, ComplexShape.π is addition of the two integer indices.
          (by change (0 : ℤ) + j = j; omega) := by
  -- Splitting the integer index makes the zero-shift index transport reflexive.
  cases j <;> simp [mapBifunctorSingleRowZeroNatIso, mapBifunctorSingleRowNatIso_inv_app_f,
    CochainComplex.shiftFunctorZero_inv_app_f, HomologicalComplex.XIsoOfEq] <;> rfl

/-- The degree-zero comparison sends its inclusion to the unshifted row identification. -/
@[reassoc (attr := simp), simp]
theorem ι_mapBifunctorSingleRowZeroNatIso_hom_app_f (A : C₁)
    [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c 0).obj A) N F c]
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    ιMapBifunctor ((single C₁ c 0).obj A) N F c 0 j j
        -- For cochain up ℤ, ComplexShape.π is addition of the two integer indices.
        (by change (0 : ℤ) + j = j; omega) ≫
        ((F.mapBifunctorSingleRowZeroNatIso A).hom.app N).f j =
      (F.map (singleObjXSelf c 0 A).hom).app (N.X j) := by
  apply (cancel_epi ((F.map (singleObjXSelf c 0 A).inv).app (N.X j))).1
  rw [← Category.assoc, ← mapBifunctorSingleRowZeroNatIso_inv_app_f]
  simp only [← HomologicalComplex.comp_f, Iso.inv_hom_id_app,
    HomologicalComplex.id_f, Iso.map_inv_hom_id_app]
  rfl

variable (s : TwoTermSupport C₁)
  [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor s.K N F c]
  [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c s.b).obj s.B) N F c]
  [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c s.a).obj s.A) N F c]

/-- Apply totalization to the supported short complex, using only its three left complexes. -/
def mapTwoTermSupport :
    ShortComplex (CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ) :=
  ShortComplex.mk (F.mapBifunctorLeftMap c c s.ι) (F.mapBifunctorLeftMap c c s.π)
    (by
      have h := s.shortComplex.zero
      dsimp only [TwoTermSupport.shortComplex] at h
      have h' : s.ι ≫ s.π = 0 := h
      rw [← mapBifunctorLeftMap_comp, h', mapBifunctorLeftMap_zero])

section Biproducts

variable [HasBinaryBiproducts D]

private def twoSummandX (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (mapBifunctor s.K N (F) c).X j ≅
      ((F).obj s.B).obj (N.X (j + -s.b)) ⊞ ((F).obj s.A).obj
        (N.X (j + -s.a)) :=
  mapBifunctorTwoSummandIso s.K N (F) c s.b (j + -s.b) s.a (j + -s.a) j
    (add_neg_cancel_comm_assoc _ _)
    (add_neg_cancel_comm_assoc _ _)
    (by intro h; exact s.ne (congrArg _root_.Prod.fst h))
    (fun p q hpq hne ↦ by
      have hp₀ : p ≠ s.a := by
        intro hp
        subst p
        exact hne (Or.inr ⟨rfl, by simpa only [sub_eq_add_neg] using (eq_sub_of_add_eq' hpq)⟩)
      have hp₁ : p ≠ s.b := by
        intro hp
        subst p
        exact hne (Or.inl ⟨rfl, by simpa only [sub_eq_add_neg] using (eq_sub_of_add_eq' hpq)⟩)
      exact ((F).flip.obj (N.X q)).map_isZero (s.support p hp₀ hp₁)) ≪≫
    biprod.mapIso (((F).mapIso s.high).app (N.X (j + -s.b)))
      (((F).mapIso s.low).app (N.X (j + -s.a)))

omit [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c s.b).obj s.B) N F c]
  [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c s.a).obj s.A) N F c]
  [HasZeroObject C₁] in
private theorem twoSummandX_ι_high (N : CochainComplex C₂ ℤ) (j : ℤ) :
    ιMapBifunctor s.K N (F) c s.b (j + -s.b) j
        (add_neg_cancel_comm_assoc s.b j) ≫ (F.twoSummandX s N j).hom =
      ((F).map s.high.hom).app (N.X (j + -s.b)) ≫ biprod.inl := by
  dsimp only [twoSummandX, Iso.trans_hom, biprod.mapIso, Functor.mapIso, Iso.app]
  rw [ι_mapBifunctorTwoSummandIso_hom_left_assoc, biprod.inl_map]

omit [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c s.b).obj s.B) N F c]
  [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ c s.a).obj s.A) N F c]
  [HasZeroObject C₁] in
private theorem twoSummandX_ι_low (N : CochainComplex C₂ ℤ) (j : ℤ) :
    ιMapBifunctor s.K N (F) c s.a (j + -s.a) j
        (add_neg_cancel_comm_assoc s.a j) ≫ (F.twoSummandX s N j).hom =
      ((F).map s.low.hom).app (N.X (j + -s.a)) ≫ biprod.inr := by
  dsimp only [twoSummandX, Iso.trans_hom, biprod.mapIso, Functor.mapIso, Iso.app]
  rw [ι_mapBifunctorTwoSummandIso_hom_right_assoc, biprod.inr_map]


private theorem supportι_twoSummandX (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (((F.mapTwoTermSupport s).f.app N).f j) ≫ (F.twoSummandX s N j).hom =
      (F.singleX s.B s.b N (j + -s.b) j
        (add_neg_cancel_comm_assoc _ _)).hom ≫ biprod.inl := by
  -- Reduce ShortComplex.map and evaluation of the curried totalization functor
  -- to mapBifunctorMap, exposing the support inclusion for its component formula.
  simp only [mapTwoTermSupport, mapBifunctorLeftMap_app]
  change (mapBifunctorMap (TwoTermSupport.ι s) (𝟙 N) (F) c).f j ≫
      (F.twoSummandX s N j).hom =
    (F.singleX s.B s.b N (j + -s.b) j
      (add_neg_cancel_comm_assoc s.b j)).hom ≫ biprod.inl
  apply (cancel_epi (F.singleX s.B s.b N (j + -s.b) j
    (add_neg_cancel_comm_assoc _ _)).inv).1
  simp only [Iso.inv_hom_id_assoc]
  rw [singleX_inv, Category.assoc]
  have hm := ι_mapBifunctorMap (TwoTermSupport.ι s) (𝟙 N) (F)
    c s.b (j + -s.b) j (add_neg_cancel_comm_assoc s.b j)
  simp only [HomologicalComplex.id_f] at hm
  rw [((F).obj (s.K.X s.b)).map_id, id_comp] at hm
  rw [reassoc_of% hm, twoSummandX_ι_high]
  simp only [TwoTermSupport.ι, mkHomFromSingle_f, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, Iso.map_inv_hom_id_app_assoc]

private theorem supportπ_twoSummandX (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (((F.mapTwoTermSupport s).g.app N).f j) ≫
        (F.singleX s.A s.a N (j + -s.a) j
          (add_neg_cancel_comm_assoc _ _)).hom =
      (F.twoSummandX s N j).hom ≫ biprod.snd := by
  -- Reduce ShortComplex.map and evaluation of the curried totalization functor
  -- to mapBifunctorMap, exposing the support projection for its component formula.
  simp only [mapTwoTermSupport, mapBifunctorLeftMap_app]
  change (mapBifunctorMap (TwoTermSupport.π s) (𝟙 N) (F) c).f j ≫
      (F.singleX s.A s.a N (j + -s.a) j
        (add_neg_cancel_comm_assoc s.a j)).hom =
    (F.twoSummandX s N j).hom ≫ biprod.snd
  apply (cancel_mono (F.singleX s.A s.a N (j + -s.a) j
    (add_neg_cancel_comm_assoc s.a j)).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, comp_id]
  rw [singleX_inv]
  apply mapBifunctor.hom_ext (K₁ := s.K) (K₂ := N) (F := F) («c» := c)
  intro p q hpq
  by_cases hp₀ : p = s.a
  · subst p
    obtain rfl : q = j + -s.a := by
      simpa only [sub_eq_add_neg] using (eq_sub_of_add_eq' hpq)
    have hm := ι_mapBifunctorMap (TwoTermSupport.π s) (𝟙 N) (F)
      c s.a (j + -s.a) j hpq
    simp only [HomologicalComplex.id_f] at hm
    rw [((F).obj (((single C₁ c s.a).obj s.A).X s.a)).map_id, id_comp] at hm
    rw [hm, reassoc_of% (F.twoSummandX_ι_low s N j)]
    simp only [TwoTermSupport.π, mkHomToSingle_f, Functor.map_comp, NatTrans.comp_app,
      Category.assoc,
      biprod.inr_snd_assoc]
  · by_cases hp₁ : p = s.b
    · subst p
      obtain rfl : q = j + -s.b := by
        simpa only [sub_eq_add_neg] using (eq_sub_of_add_eq' hpq)
      have hπ : (TwoTermSupport.π s).f s.b = 0 :=
        (isZero_single_obj_X c s.a s.A s.b s.ne.symm).eq_of_tgt _ _
      have hm := ι_mapBifunctorMap (TwoTermSupport.π s) (𝟙 N) (F)
        c s.b (j + -s.b) j hpq
      rw [hm, reassoc_of% (F.twoSummandX_ι_high s N j)]
      simp only [hπ, Functor.map_zero, NatTrans.app_zero, zero_comp,
        biprod.inl_snd_assoc, comp_zero]
    · have hzero := ((F).flip.obj (N.X q)).map_isZero
        (s.support p hp₀ hp₁)
      exact hzero.eq_of_src _ _

/-- In each cochain degree the mapped support sequence is the canonical biproduct sequence. -/
def mapTwoTermSupportDegreewiseIso (N : CochainComplex C₂ ℤ)
    (j : ℤ) :
    (((F.mapTwoTermSupport s).map ((evaluation _ _).obj N)).map (eval D c
      j)) ≅
      ShortComplex.mk
        (biprod.inl : ((F).obj s.B).obj (N.X (j + -s.b)) ⟶
          ((F).obj s.B).obj (N.X (j + -s.b)) ⊞ ((F).obj
            s.A).obj (N.X (j + -s.a)))
        biprod.snd (by simp) :=
  ShortComplex.isoMk
    (F.singleX s.B s.b N (j + -s.b) j
      (add_neg_cancel_comm_assoc _ _))
    (F.twoSummandX s N j)
    (F.singleX s.A s.a N (j + -s.a) j
      (add_neg_cancel_comm_assoc _ _))
    (F.supportι_twoSummandX s N j).symm (F.supportπ_twoSummandX s N j).symm

/-- The mapped support sequence has its canonical splitting in each cochain degree. -/
def mapTwoTermSupportDegreewiseSplitting (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (((F.mapTwoTermSupport s).map ((evaluation _ _).obj N)).map (eval D c
      j)).Splitting :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct
    (((F).obj s.B).obj (N.X (j + -s.b))) (((F).obj s.A).obj
      (N.X (j + -s.a)))).ofIso
      (F.mapTwoTermSupportDegreewiseIso s N j).symm

end Biproducts

@[simp]
theorem mapTwoTermSupport_X₁ :
    (F.mapTwoTermSupport s).X₁ =
      F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) := (rfl)

@[simp]
theorem mapTwoTermSupport_X₂ :
    (F.mapTwoTermSupport s).X₂ = F.mapBifunctorLeft c c s.K := (rfl)

@[simp]
theorem mapTwoTermSupport_X₃ :
    (F.mapTwoTermSupport s).X₃ =
      F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) := (rfl)

-- Normalize the map before its endpoint equality transports simplify.
/-- The mapped support inclusion is the totalization of the supplied high-row map. -/
@[reassoc (attr := simp↓), simp↓]
theorem mapTwoTermSupport_f :
    (F.mapTwoTermSupport s).f ≫ eqToHom (F.mapTwoTermSupport_X₂ s) =
      eqToHom (F.mapTwoTermSupport_X₁ s) ≫ F.mapBifunctorLeftMap c c s.ι := by
  exact (Category.comp_id (F.mapBifunctorLeftMap c c s.ι)).trans
    (Category.id_comp (F.mapBifunctorLeftMap c c s.ι)).symm

/-- The mapped support projection is the totalization of the supplied low-row map. -/
@[reassoc (attr := simp↓), simp↓]
theorem mapTwoTermSupport_g :
    (F.mapTwoTermSupport s).g ≫ eqToHom (F.mapTwoTermSupport_X₃ s) =
      eqToHom (F.mapTwoTermSupport_X₂ s) ≫ F.mapBifunctorLeftMap c c s.π := by
  exact (Category.comp_id (F.mapBifunctorLeftMap c c s.π)).trans
    (Category.id_comp (F.mapBifunctorLeftMap c c s.π)).symm

/-- Replace the two endpoint functors using specified natural isomorphisms. -/
def mapTwoTermSupportReframed {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃) :
    ShortComplex (CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ) :=
  ShortComplex.mk
    ((eqToIso (F.mapTwoTermSupport_X₁ s) ≪≫ u₁).inv ≫ (F.mapTwoTermSupport s).f)
    ((F.mapTwoTermSupport s).g ≫ (eqToIso (F.mapTwoTermSupport_X₃ s) ≪≫ u₃).hom)
    (by simp only [Category.assoc, ShortComplex.zero_assoc, comp_zero, zero_comp])

/-- The endpoint replacement is isomorphic to the mapped support short complex. -/
def mapTwoTermSupportReframedIso {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃) :
    F.mapTwoTermSupport s ≅ F.mapTwoTermSupportReframed s u₁ u₃ :=
  ShortComplex.isoMk (eqToIso (F.mapTwoTermSupport_X₁ s) ≪≫ u₁) (Iso.refl _)
    (eqToIso (F.mapTwoTermSupport_X₃ s) ≪≫ u₃)
    (by simp [mapTwoTermSupportReframed, Category.assoc])
    (by simp [mapTwoTermSupportReframed])


@[simp]
theorem mapTwoTermSupportReframed_X₁ {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃) :
    (F.mapTwoTermSupportReframed s u₁ u₃).X₁ = E₁ := (rfl)

@[simp]
theorem mapTwoTermSupportReframed_X₂ {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃) :
    (F.mapTwoTermSupportReframed s u₁ u₃).X₂ = F.mapBifunctorLeft c c s.K := (rfl)

@[simp]
theorem mapTwoTermSupportReframed_X₃ {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃) :
    (F.mapTwoTermSupportReframed s u₁ u₃).X₃ = E₃ := (rfl)

/-- The reframed inclusion is the high-row totalization precomposed with its endpoint change. -/
@[reassoc (attr := simp↓), simp↓]
theorem mapTwoTermSupportReframed_f {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃) :
    (F.mapTwoTermSupportReframed s u₁ u₃).f ≫
        eqToHom (F.mapTwoTermSupportReframed_X₂ s u₁ u₃) =
      eqToHom (F.mapTwoTermSupportReframed_X₁ s u₁ u₃) ≫
        u₁.inv ≫ F.mapBifunctorLeftMap c c s.ι := by
  calc
    _ = u₁.inv ≫ (eqToIso (F.mapTwoTermSupport_X₁ s)).inv ≫
        ((F.mapTwoTermSupport s).f ≫ eqToHom (F.mapTwoTermSupport_X₂ s)) :=
      (Category.assoc _ _ _).trans (Category.assoc _ _ _)
    _ = u₁.inv ≫ (eqToIso (F.mapTwoTermSupport_X₁ s)).inv ≫
        (eqToHom (F.mapTwoTermSupport_X₁ s) ≫ F.mapBifunctorLeftMap c c s.ι) :=
      congrArg (fun f ↦ u₁.inv ≫ (eqToIso (F.mapTwoTermSupport_X₁ s)).inv ≫ f)
        (F.mapTwoTermSupport_f s)
    _ = u₁.inv ≫ F.mapBifunctorLeftMap c c s.ι :=
      congrArg (fun f ↦ u₁.inv ≫ f)
        (Iso.inv_hom_id_assoc (eqToIso (F.mapTwoTermSupport_X₁ s)) _)
    _ = _ := (Category.id_comp _).symm

/-- The reframed projection is the low-row totalization followed by its endpoint change. -/
@[reassoc (attr := simp↓), simp↓]
theorem mapTwoTermSupportReframed_g {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃) :
    (F.mapTwoTermSupportReframed s u₁ u₃).g ≫
        eqToHom (F.mapTwoTermSupportReframed_X₃ s u₁ u₃) =
      eqToHom (F.mapTwoTermSupportReframed_X₂ s u₁ u₃) ≫
        F.mapBifunctorLeftMap c c s.π ≫ u₃.hom := by
  calc
    _ = ((F.mapTwoTermSupport s).g ≫ eqToHom (F.mapTwoTermSupport_X₃ s)) ≫ u₃.hom :=
      (Category.comp_id _).trans (Category.assoc _ _ _).symm
    _ = (eqToHom (F.mapTwoTermSupport_X₂ s) ≫ F.mapBifunctorLeftMap c c s.π) ≫
        u₃.hom := congrArg (fun f ↦ f ≫ u₃.hom) (F.mapTwoTermSupport_g s)
    _ = _ := Category.assoc _ _ _

section Biproducts

variable [HasBinaryBiproducts D]

/-- Transport the canonical degreewise splitting through the endpoint-change isomorphism. -/
def mapTwoTermSupportReframedDegreewiseSplitting
    {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (((F.mapTwoTermSupportReframed s u₁ u₃).map ((evaluation _ _).obj N)).map
      (eval D c j)).Splitting :=
  (F.mapTwoTermSupportDegreewiseSplitting s N j).ofIso
    ((eval D c j).mapShortComplex.mapIso
      (((evaluation _ _).obj N).mapShortComplex.mapIso
        (F.mapTwoTermSupportReframedIso s u₁ u₃)))


/-- The reframed totalization term is the biproduct of its two public endpoint terms. -/
def mapTwoTermSupportReframedDegreewiseIso
    {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    ((F.mapTwoTermSupportReframed s u₁ u₃).X₂.obj N).X j ≅
      ((F.mapTwoTermSupportReframed s u₁ u₃).X₁.obj N).X j ⊞
        ((F.mapTwoTermSupportReframed s u₁ u₃).X₃.obj N).X j :=
  (F.mapTwoTermSupportReframedDegreewiseSplitting s u₁ u₃ N j).isoBinaryBiproduct

/-- The reframed inclusion is the first inclusion under its degreewise comparison. -/
@[reassoc (attr := simp)]
theorem mapTwoTermSupportReframed_f_degreewiseIso_hom
    {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (((F.mapTwoTermSupportReframed s u₁ u₃).f.app N).f j) ≫
        (F.mapTwoTermSupportReframedDegreewiseIso s u₁ u₃ N j).hom = biprod.inl := by
  exact (F.mapTwoTermSupportReframedDegreewiseSplitting s u₁ u₃ N j).f_isoBinaryBiproduct_hom

/-- The reframed projection is the second projection under its degreewise comparison. -/
@[reassoc (attr := simp)]
theorem mapTwoTermSupportReframed_degreewiseIso_hom_snd
    {E₁ E₃ : CochainComplex C₂ ℤ ⥤ CochainComplex D ℤ}
    (u₁ : F.mapBifunctorLeft c c ((single C₁ c s.b).obj s.B) ≅ E₁)
    (u₃ : F.mapBifunctorLeft c c ((single C₁ c s.a).obj s.A) ≅ E₃)
    (N : CochainComplex C₂ ℤ) (j : ℤ) :
    (F.mapTwoTermSupportReframedDegreewiseIso s u₁ u₃ N j).hom ≫ biprod.snd =
      (((F.mapTwoTermSupportReframed s u₁ u₃).g.app N).f j) := by
  exact (F.mapTwoTermSupportReframedDegreewiseSplitting s u₁ u₃ N j).isoBinaryBiproduct_hom_snd

end Biproducts

end Preadditive

section Abelian

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroObject C₁] [HasZeroMorphisms C₂] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
  [∀ A, (F.obj A).PreservesZeroMorphisms]
  (s : TwoTermSupport C₁)
  [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor s.K N F (.up ℤ)]
  [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ (.up ℤ) s.b).obj s.B) N F (.up ℤ)]
  [∀ N : CochainComplex C₂ ℤ, HasMapBifunctor ((single C₁ (.up ℤ) s.a).obj s.A) N F (.up ℤ)]

/-- The mapped support short complex is short exact in the functor category. -/
theorem mapTwoTermSupport_shortExact :
    (F.mapTwoTermSupport s).ShortExact := by
  apply ShortComplex.shortExact_of_forall_evaluation
  intro N
  apply shortExact_of_degreewise_shortExact
  intro j
  exact (F.mapTwoTermSupportDegreewiseSplitting s N j).shortExact

end Abelian

end CategoryTheory.Functor
