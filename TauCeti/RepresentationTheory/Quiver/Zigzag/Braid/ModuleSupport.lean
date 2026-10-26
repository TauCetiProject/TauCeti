/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Module.Coproducts
public import TauCeti.Algebra.Homology.Bifunctor.Support
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Basic

/-!
# The two support sequences of the zigzag braid tensor action

The highest nonzero term of a two-term bimodule complex is a subcomplex, and its
lowest term is the quotient. Totalized tensoring with a module complex gives a short
exact sequence, split in every cochain degree. The two supported rows are identified
by the canonical two-summand totalization isomorphism.

For the positive braid complex the outer complexes are the regular tensor action and
the vertex tensor action shifted cohomologically by one. For the inverse complex they
are the internally shifted vertex action shifted cohomologically by minus one, and the
regular action. The internal shift by minus two and these cohomological shifts are
separate. The sequences are objects of a functor category, so their chain maps are
natural in the module complex. No boundedness or flatness assumption on that complex
is needed for these degreewise split sequences.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

universe u v w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "c" => ComplexShape.up ℤ

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private abbrev Bimod :=
  GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece

private abbrev Mod :=
  GradedModuleCat.{max v u w} (Γ).piece

private abbrev tensor :
    Bimod k G ⥤
      Mod.{u, v, w} k G ⥤ Mod.{u, v, w} k G :=
  GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ

-- Compute the totalization functor fields before comparing complex components.
private abbrev total :
    CochainComplex (Bimod k G) ℤ ⥤
      CochainComplex (Mod.{u, v, w} k G) ℤ ⥤ CochainComplex (Mod.{u, v, w} k G) ℤ :=
  dsimp% only [Functor.map₂CochainComplex, Functor.map₂HomologicalComplex]
    (tensor.{u, v, w} k G).map₂CochainComplex

private theorem supportTotalIndex (a j : ℤ) :
    ComplexShape.π c c c (a, j + -a) = j := by
  change a + (j + -a) = j
  omega

private abbrev row (A : (Bimod k G)) : CochainComplex (Mod.{u, v, w} k G) ℤ ⥤ CochainComplex
    (Mod.{u, v, w} k G) ℤ :=
  ((tensor.{u, v, w} k G).obj A).mapHomologicalComplex c

-- Only the zero-map property is needed to map the support short complex.
private local instance tensorCochainPreservesZero :
    (total.{u, v, w} k G).PreservesZeroMorphisms where
  map_zero K L := by
    apply NatTrans.ext
    funext N
    apply Hom.ext
    funext j
    change (mapBifunctorMap (0 : K ⟶ L) (𝟙 N) (tensor.{u, v, w} k G) c).f j = 0
    apply mapBifunctor.hom_ext
    intro p q hpq
    simp only [ι_mapBifunctorMap, HomologicalComplex.zero_f, Functor.map_zero,
      NatTrans.app_zero, comp_zero, zero_comp]

private def singleX (A : (Bimod k G)) (a : ℤ) (N : CochainComplex (Mod.{u, v, w} k G) ℤ) (q j : ℤ)
    (h : a + q = j) :
    (mapBifunctor ((single (Bimod k G) c a).obj A) N (tensor.{u, v, w} k G) c).X j ≅ ((tensor.{u,
      v, w} k G).obj A).obj (N.X q) :=
  mapBifunctorSingleSummandIso _ N (tensor.{u, v, w} k G) c a q j h (fun p r hpr hne ↦ by
    have hp : p ≠ a := by
      intro hp
      subst p
      change a + r = j at hpr
      exact hne ⟨rfl, add_left_cancel (hpr.trans h.symm)⟩
    exact ((tensor.{u, v, w} k G).flip.obj (N.X r)).map_isZero (isZero_single_obj_X c a A p hp)) ≪≫
      ((tensor.{u, v, w} k G).mapIso (singleObjXSelf c a A)).app (N.X q)

private theorem singleX_inv (A : (Bimod k G)) (a : ℤ) (N : CochainComplex (Mod.{u, v, w} k G) ℤ)
    (q j : ℤ)
    (h : a + q = j) :
    (singleX.{u, v, w} k G A a N q j h).inv =
      ((tensor.{u, v, w} k G).map (singleObjXSelf c a A).inv).app (N.X q) ≫
        ιMapBifunctor ((single (Bimod k G) c a).obj A) N (tensor.{u, v, w} k G) c a q j h := by
  simp [singleX]

private theorem singleX_inv_d (A : (Bimod k G)) (a : ℤ) (N : CochainComplex (Mod.{u, v, w} k G) ℤ)
    (j j' : ℤ) :
    (singleX.{u, v, w} k G A a N (j + -a) j (supportTotalIndex _ _)).inv ≫
        (mapBifunctor ((single (Bimod k G) c a).obj A) N (tensor.{u, v, w} k G) c).d j j' =
      (((row.{u, v, w} k G A).obj N)⟦-a⟧).d j j' ≫
        (singleX.{u, v, w} k G A a N (j' + -a) j'
          (supportTotalIndex _ _)).inv := by
  by_cases hjj' : (c).Rel j j'
  · have hqq' : (c).Rel (j + -a) (j' + -a) := by
      change (j + -a) + 1 = j' + -a
      change j + 1 = j' at hjj'
      omega
    have hd₁ : mapBifunctor.d₁ ((single (Bimod k G) c a).obj A) N (tensor.{u, v, w} k G) c a (j +
      -a) j' = 0 := by
      rw [mapBifunctor.d₁_eq' _ _ _ _ (by simp : (c).Rel a (a + 1))]
      simp
    -- Cochain totalization has vertical sign (-1)^a; a shift by -a has the same sign.
    have hε : ComplexShape.ε₂ c c c (a, j + -a) = a.negOnePow := rfl
    have hd₂ := mapBifunctor.d₂_eq ((single (Bimod k G) c a).obj A) N
      (tensor.{u, v, w} k G) c a hqq' j' (supportTotalIndex a j')
    rw [singleX_inv, singleX_inv]
    simp only [Category.assoc, mapBifunctor.d_eq, Preadditive.comp_add,
      mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, hd₁, comp_zero, zero_add,
      hd₂, hε,
      CochainComplex.shiftFunctor_obj_d', Functor.mapHomologicalComplex_obj_d,
      Int.negOnePow_neg, Linear.comp_units_smul, Linear.units_smul_comp]
    rw [← NatTrans.naturality_assoc]
  · simp only [shape _ _ _ hjj', comp_zero, zero_comp]

private def singleRowIso (A : (Bimod k G)) (a : ℤ) (N : CochainComplex (Mod.{u, v, w} k G) ℤ) :
    ((total.{u, v, w} k G).obj ((single (Bimod k G) c a).obj A)).obj N ≅
      ((row.{u, v, w} k G A).obj N)⟦-a⟧ :=
  (Hom.isoOfComponents
    (C₁ := ((row.{u, v, w} k G A).obj N)⟦-a⟧)
    (C₂ := ((total.{u, v, w} k G).obj
      ((single (Bimod k G) c a).obj A)).obj N)
    (fun j ↦ (singleX.{u, v, w} k G A a N (j + -a) j
      (supportTotalIndex _ _)).symm)
    (fun j j' _ ↦ singleX_inv_d.{u, v, w} k G A a N j j')).symm

private theorem singleRowIso_inv_f (A : (Bimod k G)) (a : ℤ) (N : CochainComplex (Mod.{u, v, w} k
    G) ℤ) (j : ℤ) :
    (singleRowIso.{u, v, w} k G A a N).inv.f j =
      ((tensor.{u, v, w} k G).map (singleObjXSelf c a A).inv).app (N.X (j + -a)) ≫
        ιMapBifunctor ((single (Bimod k G) c a).obj A) N (tensor.{u, v, w} k G) c a (j + -a) j
          (supportTotalIndex _ _) := by
  exact singleX_inv.{u, v, w} k G A a N (j + -a) j (supportTotalIndex a j)

private def singleRowNatIso (A : (Bimod k G)) (a : ℤ) :
    (total.{u, v, w} k G).obj ((single (Bimod k G) c a).obj A) ≅ row.{u, v,
      w} k G A ⋙ shiftFunctor _ (-a) :=
  NatIso.ofComponents (singleRowIso.{u, v, w} k G A a) (fun {N N'} f ↦ by
    apply (cancel_epi (singleRowIso.{u, v, w} k G A a N).inv).1
    apply (cancel_mono (singleRowIso.{u, v, w} k G A a N').inv).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id]
    apply Hom.ext
    funext j
    change (singleRowIso.{u, v, w} k G A a N).inv.f j ≫
        (mapBifunctorMap (𝟙 ((single (Bimod k G) c a).obj A)) f
          (tensor.{u, v, w} k G) c).f j =
      (((row.{u, v, w} k G A).map f)⟦-a⟧').f j ≫
        (singleRowIso.{u, v, w} k G A a N').inv.f j
    simp only [singleRowIso_inv_f, Category.assoc, CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplex_map_f]
    have hm := ι_mapBifunctorMap (𝟙 ((single (Bimod k G) c a).obj A)) f
      (tensor.{u, v, w} k G) c a (j + -a) j (supportTotalIndex a j)
    simp only [HomologicalComplex.id_f] at hm
    rw [(tensor.{u, v, w} k G).map_id, NatTrans.id_app, id_comp] at hm
    rw [hm, ← NatTrans.naturality_assoc])

private def singleRowZeroNatIso (A : (Bimod k G)) :
    (total.{u, v, w} k G).obj ((single (Bimod k G) c 0).obj A) ≅ row.{u, v, w} k G A :=
  singleRowNatIso.{u, v, w} k G A 0 ≪≫
    Functor.isoWhiskerLeft (row.{u, v, w} k G A) (shiftFunctorZero (CochainComplex (Mod.{u, v, w}
      k G) ℤ) ℤ) ≪≫
      (row.{u, v, w} k G A).rightUnitor

private structure TwoTermSupport where
  K : CochainComplex (Bimod k G) ℤ
  a : ℤ
  b : ℤ
  A : (Bimod k G)
  B : (Bimod k G)
  low : K.X a ≅ A
  high : K.X b ≅ B
  ne : a ≠ b
  outgoing : ∀ j, K.d b j = 0
  incoming : ∀ j, K.d j a = 0
  support : ∀ j, j ≠ a → j ≠ b → IsZero (K.X j)

private def supportι (s : TwoTermSupport k G) : (single (Bimod k G) c s.b).obj s.B ⟶ s.K :=
  mkHomFromSingle s.high.inv (fun j _ ↦ by rw [s.outgoing j, comp_zero])

private def supportπ (s : TwoTermSupport k G) : s.K ⟶ (single (Bimod k G) c s.a).obj s.A :=
  mkHomToSingle s.low.hom (fun j _ ↦ by rw [s.incoming j, zero_comp])

private def supportSequence (s : TwoTermSupport k G) : ShortComplex (CochainComplex (Bimod k G) ℤ)
    :=
  ShortComplex.mk (supportι k G s) (supportπ k G s) (by
    apply from_single_hom_ext
    exact (isZero_single_obj_X c s.a s.A s.b s.ne.symm).eq_of_tgt _ _)

private def rawSequence (s : TwoTermSupport k G) :
    ShortComplex (CochainComplex (Mod.{u, v, w} k G) ℤ ⥤ CochainComplex (Mod.{u, v, w} k G) ℤ) :=
  (supportSequence k G s).map (total.{u, v, w} k G)

private theorem row_index {a q j : ℤ} (h : a + q = j) : q = j + -a := by
  omega

private def twoSummandX (s : TwoTermSupport k G) (N : CochainComplex (Mod.{u, v, w} k G) ℤ) (j :
    ℤ) :
    (mapBifunctor s.K N (tensor.{u, v, w} k G) c).X j ≅
      ((tensor.{u, v, w} k G).obj s.B).obj (N.X (j + -s.b)) ⊞ ((tensor.{u, v, w} k G).obj s.A).obj
        (N.X (j + -s.a)) :=
  mapBifunctorTwoSummandIso s.K N (tensor.{u, v, w} k G) c s.b (j + -s.b) s.a (j + -s.a) j
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
      exact ((tensor.{u, v, w} k G).flip.obj (N.X q)).map_isZero (s.support p hp₀ hp₁)) ≪≫
    biprod.mapIso (((tensor.{u, v, w} k G).mapIso s.high).app (N.X (j + -s.b)))
      (((tensor.{u, v, w} k G).mapIso s.low).app (N.X (j + -s.a)))

private theorem twoSummandX_ι_high (s : TwoTermSupport k G)
    (N : CochainComplex (Mod.{u, v, w} k G) ℤ) (j : ℤ) :
    ιMapBifunctor s.K N (tensor.{u, v, w} k G) c s.b (j + -s.b) j
        (supportTotalIndex s.b j) ≫ (twoSummandX.{u, v, w} k G s N j).hom =
      ((tensor.{u, v, w} k G).map s.high.hom).app (N.X (j + -s.b)) ≫ biprod.inl := by
  dsimp only [twoSummandX, Iso.trans_hom, biprod.mapIso, Functor.mapIso, Iso.app]
  rw [ι_mapBifunctorTwoSummandIso_hom_left_assoc, biprod.inl_map]

private theorem twoSummandX_ι_low (s : TwoTermSupport k G)
    (N : CochainComplex (Mod.{u, v, w} k G) ℤ) (j : ℤ) :
    ιMapBifunctor s.K N (tensor.{u, v, w} k G) c s.a (j + -s.a) j
        (supportTotalIndex s.a j) ≫ (twoSummandX.{u, v, w} k G s N j).hom =
      ((tensor.{u, v, w} k G).map s.low.hom).app (N.X (j + -s.a)) ≫ biprod.inr := by
  dsimp only [twoSummandX, Iso.trans_hom, biprod.mapIso, Functor.mapIso, Iso.app]
  rw [ι_mapBifunctorTwoSummandIso_hom_right_assoc, biprod.inr_map]

private theorem supportι_twoSummandX (s : TwoTermSupport k G)
    (N : CochainComplex (Mod.{u, v, w} k G) ℤ) (j : ℤ) :
    (((rawSequence.{u, v, w} k G s).f.app N).f j) ≫ (twoSummandX.{u, v, w} k G s N j).hom =
      (singleX.{u, v, w} k G s.B s.b N (j + -s.b) j
        (supportTotalIndex _ _)).hom ≫ biprod.inl := by
  change (mapBifunctorMap (supportι k G s) (𝟙 N) (tensor.{u, v, w} k G) c).f j ≫
      (twoSummandX.{u, v, w} k G s N j).hom =
    (singleX.{u, v, w} k G s.B s.b N (j + -s.b) j
      (supportTotalIndex s.b j)).hom ≫ biprod.inl
  apply (cancel_epi (singleX.{u, v, w} k G s.B s.b N (j + -s.b) j
    (supportTotalIndex _ _)).inv).1
  simp only [Iso.inv_hom_id_assoc]
  rw [singleX_inv, Category.assoc]
  have hm := ι_mapBifunctorMap (supportι k G s) (𝟙 N) (tensor.{u, v, w} k G)
    c s.b (j + -s.b) j (supportTotalIndex s.b j)
  simp only [HomologicalComplex.id_f] at hm
  rw [((tensor.{u, v, w} k G).obj (s.K.X s.b)).map_id, id_comp] at hm
  rw [reassoc_of% hm, twoSummandX_ι_high]
  simp only [supportι, mkHomFromSingle_f, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, Iso.map_inv_hom_id_app_assoc]

private theorem supportπ_twoSummandX (s : TwoTermSupport k G)
    (N : CochainComplex (Mod.{u, v, w} k G) ℤ) (j : ℤ) :
    (((rawSequence.{u, v, w} k G s).g.app N).f j) ≫
        (singleX.{u, v, w} k G s.A s.a N (j + -s.a) j
          (supportTotalIndex _ _)).hom =
      (twoSummandX.{u, v, w} k G s N j).hom ≫ biprod.snd := by
  change (mapBifunctorMap (supportπ k G s) (𝟙 N) (tensor.{u, v, w} k G) c).f j ≫
      (singleX.{u, v, w} k G s.A s.a N (j + -s.a) j
        (supportTotalIndex s.a j)).hom =
    (twoSummandX.{u, v, w} k G s N j).hom ≫ biprod.snd
  apply (cancel_mono (singleX.{u, v, w} k G s.A s.a N (j + -s.a) j
    (supportTotalIndex s.a j)).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, comp_id]
  rw [singleX_inv]
  apply mapBifunctor.hom_ext (K₁ := s.K) (K₂ := N) (F := tensor.{u, v, w} k G) («c» := c)
  intro p q hpq
  by_cases hp₀ : p = s.a
  · subst p
    obtain rfl : q = j + -s.a := row_index hpq
    have hm := ι_mapBifunctorMap (supportπ k G s) (𝟙 N) (tensor.{u, v, w} k G)
      c s.a (j + -s.a) j hpq
    simp only [HomologicalComplex.id_f] at hm
    rw [((tensor.{u, v, w} k G).obj
      (((single (Bimod k G) c s.a).obj s.A).X s.a)).map_id, id_comp] at hm
    rw [hm, reassoc_of% (twoSummandX_ι_low.{u, v, w} k G s N j)]
    simp only [supportπ, mkHomToSingle_f, Functor.map_comp, NatTrans.comp_app, Category.assoc,
      biprod.inr_snd_assoc]
  · by_cases hp₁ : p = s.b
    · subst p
      obtain rfl : q = j + -s.b := row_index hpq
      have hπ : (supportπ k G s).f s.b = 0 :=
        (isZero_single_obj_X c s.a s.A s.b s.ne.symm).eq_of_tgt _ _
      have hm := ι_mapBifunctorMap (supportπ k G s) (𝟙 N) (tensor.{u, v, w} k G)
        c s.b (j + -s.b) j hpq
      rw [hm, reassoc_of% (twoSummandX_ι_high.{u, v, w} k G s N j)]
      simp only [hπ, Functor.map_zero, NatTrans.app_zero, zero_comp,
        biprod.inl_snd_assoc, comp_zero]
    · have hzero := ((tensor.{u, v, w} k G).flip.obj (N.X q)).map_isZero
        (s.support p hp₀ hp₁)
      exact hzero.eq_of_src _ _

private def rawDegreewiseIso (s : TwoTermSupport k G) (N : CochainComplex (Mod.{u, v, w} k G) ℤ)
    (j : ℤ) :
    (((rawSequence.{u, v, w} k G s).map ((evaluation _ _).obj N)).map (eval (Mod.{u, v, w} k G) c
      j)) ≅
      ShortComplex.mk
        (biprod.inl : ((tensor.{u, v, w} k G).obj s.B).obj (N.X (j + -s.b)) ⟶
          ((tensor.{u, v, w} k G).obj s.B).obj (N.X (j + -s.b)) ⊞ ((tensor.{u, v, w} k G).obj
            s.A).obj (N.X (j + -s.a)))
        biprod.snd (by simp) :=
  ShortComplex.isoMk
    (singleX.{u, v, w} k G s.B s.b N (j + -s.b) j
      (supportTotalIndex _ _))
    (twoSummandX.{u, v, w} k G s N j)
    (singleX.{u, v, w} k G s.A s.a N (j + -s.a) j
      (supportTotalIndex _ _))
    (supportι_twoSummandX.{u, v, w} k G s N j).symm (supportπ_twoSummandX.{u, v, w} k G s N j).symm

private def rawDegreewiseSplitting (s : TwoTermSupport k G)
    (N : CochainComplex (Mod.{u, v, w} k G) ℤ) (j : ℤ) :
    (((rawSequence.{u, v, w} k G s).map ((evaluation _ _).obj N)).map (eval (Mod.{u, v, w} k G) c
      j)).Splitting :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct
    (((tensor.{u, v, w} k G).obj s.B).obj (N.X (j + -s.b))) (((tensor.{u, v, w} k G).obj s.A).obj
      (N.X (j + -s.a)))).ofIso
      (rawDegreewiseIso.{u, v, w} k G s N j).symm

private theorem rawSequence_shortExact (s : TwoTermSupport k G) :
    (rawSequence.{u, v, w} k G s).ShortExact := by
  apply ShortComplex.shortExact_of_forall_evaluation
  intro N
  apply shortExact_of_degreewise_shortExact
  intro j
  exact (rawDegreewiseSplitting.{u, v, w} k G s N j).shortExact

private def reframe {E₁ E₃ : CochainComplex (Mod.{u, v, w} k G) ℤ ⥤ CochainComplex (Mod.{u, v, w}
    k G) ℤ}
    (s : TwoTermSupport k G)
    (u₁ : (rawSequence.{u, v, w} k G s).X₁ ≅ E₁) (u₃ : (rawSequence.{u, v, w} k G s).X₃ ≅ E₃) :
    ShortComplex (CochainComplex (Mod.{u, v, w} k G) ℤ ⥤ CochainComplex (Mod.{u, v, w} k G) ℤ) :=
  ShortComplex.mk (u₁.inv ≫ (rawSequence.{u, v, w} k G s).f) ((rawSequence.{u, v, w} k G s).g ≫
    u₃.hom)
    (by simp [Category.assoc])

private def reframeIso {E₁ E₃ : CochainComplex (Mod.{u, v, w} k G) ℤ ⥤ CochainComplex (Mod.{u, v,
    w} k G) ℤ}
    (s : TwoTermSupport k G)
    (u₁ : (rawSequence.{u, v, w} k G s).X₁ ≅ E₁) (u₃ : (rawSequence.{u, v, w} k G s).X₃ ≅ E₃) :
    rawSequence.{u, v, w} k G s ≅ reframe.{u, v, w} k G s u₁ u₃ :=
  ShortComplex.isoMk u₁ (Iso.refl _) u₃ (by simp [reframe]) (by simp [reframe])

private def positiveSupport (i : V) : TwoTermSupport k G where
  K := zigzagBraidComplex k G i
  a := -1
  b := 0
  A := zigzagGradedBraidBimodule k G i
  B := zigzagGradedBimodule k G
  low := zigzagBraidComplexXIso₀ k G i
  high := zigzagBraidComplexXIso₁ k G i
  ne := by decide
  outgoing j := zigzagBraidComplex_d_eq_zero₀ i j (by decide)
  incoming j := zigzagBraidComplex_d_eq_zero₁ i j (by decide)
  support j := isZero_zigzagBraidComplex_X i

private def inverseSupport (i : V) : TwoTermSupport k G where
  K := zigzagBraidInverseComplex k G i
  a := 0
  b := 1
  A := zigzagGradedBimodule k G
  B := (GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)
  low := zigzagBraidInverseComplexXIso₀ k G i
  high := zigzagBraidInverseComplexXIso₁ k G i
  ne := by decide
  outgoing j := zigzagBraidInverseComplex_d_eq_zero₀ i j (by decide)
  incoming j := zigzagBraidInverseComplex_d_eq_zero₁ i j (by decide)
  support j := isZero_zigzagBraidInverseComplex_X i

/-- The natural two-support sequence of the positive braid tensor action has outer functors
`T_Z` and `T_U[1]`. The maps are chain maps, natural in every module complex. -/
def zigzagBraidTensorSupportSequence (i : V) :
    ShortComplex (CochainComplex
      (GradedModuleCat.{max v u w} (Γ).piece) ℤ ⥤
        CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) :=
  reframe.{u, v, w} k G (positiveSupport k G i)
    (singleRowZeroNatIso.{u, v, w} k G (zigzagGradedBimodule k G))
    (singleRowNatIso.{u, v, w} k G (zigzagGradedBraidBimodule k G i) (-1))

/-- The natural two-support sequence of the inverse braid tensor action has outer functors
`T_(U{-2})[-1]` and `T_Z`, with distinct internal and cohomological shifts. -/
def zigzagBraidInverseTensorSupportSequence (i : V) :
    ShortComplex (CochainComplex
      (GradedModuleCat.{max v u w} (Γ).piece) ℤ ⥤
        CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) :=
  reframe.{u, v, w} k G (inverseSupport k G i)
    (singleRowNatIso.{u, v, w} k G
      ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
    (singleRowZeroNatIso.{u, v, w} k G (zigzagGradedBimodule k G))

@[simp]
theorem zigzagBraidTensorSupportSequence_X₁ (i : V) :
    (zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₁ =
      Functor.mapHomologicalComplex
        ((GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).obj
          (zigzagGradedBimodule k G)) c := (rfl)

@[simp]
theorem zigzagBraidTensorSupportSequence_X₂ (i : V) :
    (zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₂ =
      (GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).map₂CochainComplex.obj
        (zigzagBraidComplex k G i) := (rfl)

@[simp]
theorem zigzagBraidTensorSupportSequence_X₃ (i : V) :
    (zigzagBraidTensorSupportSequence.{u, v, w} k G i).X₃ =
      Functor.mapHomologicalComplex
        ((GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).obj
          (zigzagGradedBraidBimodule k G i)) c ⋙
        shiftFunctor (CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (1 : ℤ) := (rfl)

@[simp]
theorem zigzagBraidInverseTensorSupportSequence_X₁ (i : V) :
    (zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₁ =
      Functor.mapHomologicalComplex
        ((GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).obj
          ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i))) c ⋙
        shiftFunctor (CochainComplex (GradedModuleCat.{max v u w} (Γ).piece) ℤ) (-1 : ℤ) := (rfl)

@[simp]
theorem zigzagBraidInverseTensorSupportSequence_X₂ (i : V) :
    (zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₂ =
      (GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).map₂CochainComplex.obj
        (zigzagBraidInverseComplex k G i) := (rfl)

@[simp]
theorem zigzagBraidInverseTensorSupportSequence_X₃ (i : V) :
    (zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).X₃ =
      Functor.mapHomologicalComplex
        ((GradedModuleCat.bimoduleModuleTensor.{max u w, max v u w} Γ Γ).obj
          (zigzagGradedBimodule k G)) c := (rfl)

/-- The positive support sequence is short exact in the functor category. -/
theorem zigzagBraidTensorSupportSequence_shortExact (i : V) :
    (zigzagBraidTensorSupportSequence.{u, v, w} k G i).ShortExact :=
  ShortComplex.shortExact_of_iso
    (reframeIso.{u, v, w} k G (positiveSupport k G i)
      (singleRowZeroNatIso.{u, v, w} k G (zigzagGradedBimodule k G))
      (singleRowNatIso.{u, v, w} k G (zigzagGradedBraidBimodule k G i) (-1)))
    (rawSequence_shortExact.{u, v, w} k G (positiveSupport k G i))

/-- The inverse support sequence is short exact in the functor category. -/
theorem zigzagBraidInverseTensorSupportSequence_shortExact (i : V) :
    (zigzagBraidInverseTensorSupportSequence.{u, v, w} k G i).ShortExact :=
  ShortComplex.shortExact_of_iso
    (reframeIso.{u, v, w} k G (inverseSupport k G i)
      (singleRowNatIso.{u, v, w} k G
        ((GradedModuleCat.shiftFunctor (-2)).obj (zigzagGradedBraidBimodule k G i)) 1)
      (singleRowZeroNatIso.{u, v, w} k G (zigzagGradedBimodule k G)))
    (rawSequence_shortExact.{u, v, w} k G (inverseSupport k G i))

end TauCeti
