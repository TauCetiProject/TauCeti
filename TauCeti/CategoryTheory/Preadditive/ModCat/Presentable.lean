/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import TauCeti.CategoryTheory.Functor.LocallySmall
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

/-!
# Presentability of modules over a preadditive category

A representable module is finitely presentable because maps from it are computed by evaluation,
which preserves filtered colimits. The representables of an essentially small preadditive
category form a small strong generating family. This gives local finite presentability and
identifies presentability with a presentation by sums of representables.

The finite case extends the functor-category theorem of Crawley-Boevey
(*Locally finitely presented additive categories*, §1.2, p. 1645) from additive to preadditive
source categories. A colimit of presented modules uses the generators and relations at each
object, together with one relation per arrow and source generator. This construction works with
size bounds at any regular cardinal, including the first uncountable cardinal.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Representable modules preserve filtered colimits under covariant Hom in the
morphism universe of the source category. -/
instance (X : C) : IsFinitelyPresentable.{v} ((yoneda C).obj X) := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  exact ⟨fun J _ _ ↦ preservesColimitsOfShape_of_natIso (coyonedaYonedaIsoEvaluation X).symm⟩

private lemma isSeparating_ofObj_yoneda [EssentiallySmall.{v} C] :
    (ObjectProperty.ofObj ((equivSmallModel.{v} C).inverse ⋙ yoneda C).obj).IsSeparating := by
  intro F G f g h
  apply ObjectProperty.hom_ext
  ext Y x
  let e := equivSmallModel.{v} C
  let X := e.functor.obj Y.unop
  have hs := (isIso_iff_bijective
    ((coyonedaYonedaIsoEvaluation Y.unop).hom.app F)).1 inferInstance
  obtain ⟨a, ha⟩ := hs.2 (ULift.up x)
  let i := (yoneda C).mapIso (e.unitIso.app Y.unop)
  have eq := h _ (ObjectProperty.ofObj_apply (e.inverse ⋙ yoneda C).obj X) (i.inv ≫ a)
  have hab : a ≫ f = a ≫ g := by
    simpa using congrArg (i.hom ≫ ·) eq
  have hx : a.hom.app Y (𝟙 Y.unop) = x := by
    simpa only [coyonedaYonedaIsoEvaluation_hom_app_down] using
      congrArg (fun y : ULift.{u} (F.obj.obj Y) ↦ y.down) ha
  simpa [Function.comp_def, hx] using
    congrArg (fun t : (yoneda C).obj Y.unop ⟶ G ↦ t.hom.app Y (𝟙 Y.unop)) hab

/-- The representable modules indexed by a small model of `C` form a strong generating family. -/
lemma isStrongGenerator_ofObj_yoneda [EssentiallySmall.{v} C] :
    (ObjectProperty.ofObj ((equivSmallModel.{v} C).inverse ⋙ yoneda C).obj).IsStrongGenerator := by
  have h := isSeparating_ofObj_yoneda (C := C)
  exact ObjectProperty.isStrongGenerator_iff.2
    ⟨h, fun _ _ i _ hi ↦ (h.isDetecting.isIso_iff_of_mono i).2 hi⟩

local instance : HasColimitsOfSize.{v, v} (ModCat.{v} C) where
  has_colimits_of_shape _ := inferInstance

/-- An essentially small preadditive category has a locally finitely presentable
category of modules. -/
instance [EssentiallySmall.{v} C] : IsLocallyFinitelyPresentable.{v} (ModCat.{v} C) := by
  have := Cardinal.fact_isRegular_aleph0.{v}
  refine (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator _ Cardinal.aleph0).2
    ⟨_, inferInstance, isStrongGenerator_ofObj_yoneda, ?_⟩
  rintro _ ⟨X⟩
  exact inferInstanceAs (IsFinitelyPresentable.{v} ((yoneda C).obj
    ((equivSmallModel.{v} C).inverse.obj X)))

section Cardinal

open Cardinal

variable (κ : Cardinal.{v}) [Fact κ.IsRegular]

/-- A coproduct of fewer than `κ` representable modules is `κ`-presentable. -/
lemma isCardinalPresentable_sigma_yoneda {I : Type v} (hI : HasCardinalLT I κ) (X : I → C) :
    IsCardinalPresentable (∐ fun i ↦ (yoneda C).obj (X i)) κ := by
  have := Cardinal.fact_isRegular_aleph0.{v}
  have (i : Discrete I) :
      IsCardinalPresentable ((Discrete.functor fun i ↦ (yoneda C).obj (X i)).obj i) κ :=
    isCardinalPresentable_monotone _ (IsRegular.aleph0_le Fact.out) _
      (inferInstanceAs (IsFinitelyPresentable.{v} ((yoneda C).obj (X i.as))))
  exact isCardinalPresentable_of_isColimit' _ (coproductIsCoproduct _) κ
    ((hasCardinalLT_iff_of_equiv (Arrow.discreteEquiv I) κ).2 hI)

private structure Presentation (F : ModCat.{v} C) where
  I : Type v
  J : Type v
  X : I → C
  Y : J → C
  relation : (∐ fun j ↦ (yoneda C).obj (Y j)) ⟶ ∐ fun i ↦ (yoneda C).obj (X i)
  π : (∐ fun i ↦ (yoneda C).obj (X i)) ⟶ F
  zero : relation ≫ π = 0
  isCokernel : IsColimit (CokernelCofork.ofπ π zero)

/-- A presentation whose generator and relation families each have cardinality below `κ`. -/
private def hasPresentationLT : ObjectProperty (ModCat.{v} C) :=
  fun F ↦ ∃ P : Presentation F, HasCardinalLT P.I κ ∧ HasCardinalLT P.J κ

private instance : (hasPresentationLT (C := C) κ).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨⟨I, J, X, Y, d, p, hp, hc⟩, hI, hJ⟩
    exact ⟨⟨I, J, X, Y, d, p ≫ e.hom, by simp [reassoc_of% hp],
      IsColimit.ofIsoColimit hc (Cofork.ext e (by simp))⟩, hI, hJ⟩

private lemma hasPresentationLT_yoneda (X : C) :
    hasPresentationLT κ ((yoneda C).obj X) := by
  let e := coproductUniqueIso (fun _ : PUnit.{v + 1} ↦ (yoneda C).obj X)
  refine (hasPresentationLT κ).prop_of_iso e ?_
  exact ⟨⟨PUnit.{v + 1}, PEmpty, fun _ ↦ X, PEmpty.elim, 0, 𝟙 _, zero_comp,
      CokernelCofork.IsColimit.ofId _ rfl⟩,
    hasCardinalLT_of_finite _ _ (IsRegular.aleph0_le Fact.out),
    hasCardinalLT_of_finite _ _ (IsRegular.aleph0_le Fact.out)⟩

namespace Presentation

noncomputable section

variable {K : Type v} [SmallCategory K] {D : K ⥤ ModCat.{v} C}

private abbrev generator (P : ∀ k : K, Presentation (D.obj k)) (i : Σ k : K, (P k).I) : C :=
  (P i.1).X i.2

private abbrev relationGenerator (P : ∀ k : K, Presentation (D.obj k))
    (j : (Σ k : K, (P k).J) ⊕ (Σ a : Arrow K, (P a.left).I)) : C :=
  match j with
  | .inl ⟨k, j⟩ => (P k).Y j
  | .inr ⟨a, i⟩ => (P a.left).X i

private def ι (P : ∀ k : K, Presentation (D.obj k)) (k : K) :
    (∐ fun i ↦ (yoneda C).obj ((P k).X i)) ⟶ ∐ fun i ↦ (yoneda C).obj (generator P i) :=
  Sigma.desc fun i ↦ Sigma.ι (fun j ↦ (yoneda C).obj (generator P j)) ⟨k, i⟩

private def projection (P : ∀ k : K, Presentation (D.obj k)) (c : Cocone D) :
    (∐ fun i ↦ (yoneda C).obj (generator P i)) ⟶ c.pt :=
  Sigma.desc fun i ↦
    Sigma.ι (fun j ↦ (yoneda C).obj ((P i.1).X j)) i.2 ≫ (P i.1).π ≫ c.ι.app i.1

@[reassoc]
private lemma ι_projection (P : ∀ k : K, Presentation (D.obj k)) (c : Cocone D) (k : K) :
    ι P k ≫ projection P c = (P k).π ≫ c.ι.app k := by
  apply Sigma.hom_ext
  intro i
  simp only [ι, projection, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]

private def lift (P : ∀ k : K, Presentation (D.obj k)) (a : Arrow K) :
    (∐ fun i ↦ (yoneda C).obj ((P a.left).X i)) ⟶
      ∐ fun i ↦ (yoneda C).obj ((P a.right).X i) :=
  have : Epi (P a.right).π := Cofork.IsColimit.epi (P a.right).isCokernel
  -- Mathlib's coproduct projectivity instance uses the module category's morphism universe.
  let e := Sigma.reindex (Equiv.ulift : ULift.{u} (P a.left).I ≃ (P a.left).I)
    (fun i ↦ (yoneda C).obj ((P a.left).X i))
  have hProjective (i : ULift.{u} (P a.left).I) :
      Projective ((yoneda C).obj ((P a.left).X i.down)) := inferInstance
  have : Projective (∐ fun i ↦ (yoneda C).obj ((P a.left).X i)) :=
    Projective.of_iso e (@Projective.instSigmaObj _ _ _ _ _ hProjective)
  Projective.factorThru ((P a.left).π ≫ D.map a.hom) (P a.right).π

@[reassoc]
private lemma lift_π (P : ∀ k : K, Presentation (D.obj k)) (a : Arrow K) :
    lift P a ≫ (P a.right).π = (P a.left).π ≫ D.map a.hom := by
  unfold lift
  exact @Projective.factorThru_comp ..

-- The first family gives the relations of the individual modules. The second imposes
-- compatibility along each arrow of the diagram, on each generator of its source.
private def relations (P : ∀ k : K, Presentation (D.obj k)) :
    (∐ fun j ↦ (yoneda C).obj (relationGenerator P j)) ⟶
      ∐ fun i ↦ (yoneda C).obj (generator P i) :=
  Sigma.desc fun j ↦ by
    rcases j with (⟨k, j⟩ | ⟨a, i⟩)
    · exact Sigma.ι (fun j ↦ (yoneda C).obj ((P k).Y j)) j ≫ (P k).relation ≫ ι P k
    · exact Sigma.ι (fun j ↦ (yoneda C).obj ((P a.left).X j)) i ≫
        (ι P a.left - lift P a ≫ ι P a.right)

@[reassoc]
private lemma ι_inl_relations (P : ∀ k : K, Presentation (D.obj k)) (k : K) (j : (P k).J) :
    Sigma.ι (fun j ↦ (yoneda C).obj (relationGenerator P j)) (Sum.inl ⟨k, j⟩) ≫ relations P =
      Sigma.ι (fun j ↦ (yoneda C).obj ((P k).Y j)) j ≫ (P k).relation ≫ ι P k :=
  Sigma.ι_comp_desc _ _

@[reassoc]
private lemma ι_inr_relations (P : ∀ k : K, Presentation (D.obj k))
    (a : Arrow K) (i : (P a.left).I) :
    Sigma.ι (fun j ↦ (yoneda C).obj (relationGenerator P j)) (Sum.inr ⟨a, i⟩) ≫ relations P =
      Sigma.ι (fun j ↦ (yoneda C).obj ((P a.left).X j)) i ≫
        (ι P a.left - lift P a ≫ ι P a.right) :=
  Sigma.ι_comp_desc _ _

private lemma relations_projection (P : ∀ k : K, Presentation (D.obj k)) (c : Cocone D) :
    relations P ≫ projection P c = 0 := by
  apply Sigma.hom_ext
  rintro (⟨k, j⟩ | ⟨a, i⟩)
  · rw [ι_inl_relations_assoc]
    simp only [ι_projection, reassoc_of% (P k).zero, zero_comp, comp_zero]
  · rw [ι_inr_relations_assoc]
    simp only [Preadditive.sub_comp, Category.assoc, ι_projection, lift_π_assoc,
      c.w, sub_self, comp_zero]

private lemma epi_projection (P : ∀ k : K, Presentation (D.obj k)) {c : Cocone D}
    (hc : IsColimit c) : Epi (projection P c) := by
  constructor
  intro Z f g h
  apply hc.hom_ext
  intro k
  have : Epi (P k).π := Cofork.IsColimit.epi (P k).isCokernel
  apply (cancel_epi (P k).π).1
  simpa only [ι_projection_assoc] using congrArg (ι P k ≫ ·) h

private def isCokernelOfDiagram (P : ∀ k : K, Presentation (D.obj k)) {c : Cocone D}
    (hc : IsColimit c) :
    IsColimit (CokernelCofork.ofπ (projection P c) (relations_projection P c)) := by
  have (k : K) : Epi (P k).π := Cofork.IsColimit.epi (P k).isCokernel
  have := epi_projection P hc
  refine CokernelCofork.IsColimit.ofπ' _ _ fun t ht ↦ ?_
  have ht₁ (k : K) : (P k).relation ≫ ι P k ≫ t = 0 := by
    apply Sigma.hom_ext
    intro j
    have e := congrArg (Sigma.ι (fun j ↦ (yoneda C).obj (relationGenerator P j))
      (Sum.inl ⟨k, j⟩) ≫ ·) ht
    rw [ι_inl_relations_assoc, comp_zero] at e
    simpa only [Category.assoc, comp_zero] using! e
  let s (k : K) := (CokernelCofork.IsColimit.desc' (P k).isCokernel (ι P k ≫ t) (ht₁ k)).val
  have hs (k : K) : (P k).π ≫ s k = ι P k ≫ t :=
    (CokernelCofork.IsColimit.desc' (P k).isCokernel (ι P k ≫ t) (ht₁ k)).property
  have hs' (a : Arrow K) : s a.left = D.map a.hom ≫ s a.right := by
    apply (cancel_epi (P a.left).π).1
    rw [hs a.left, ← lift_π_assoc, hs a.right]
    apply sub_eq_zero.mp
    apply Sigma.hom_ext
    intro i
    have e := congrArg (Sigma.ι (fun j ↦ (yoneda C).obj (relationGenerator P j))
      (Sum.inr ⟨a, i⟩) ≫ ·) ht
    rw [ι_inr_relations_assoc, comp_zero] at e
    simpa only [Category.assoc, Preadditive.sub_comp, Preadditive.comp_sub, comp_zero] using! e
  let c' : Cocone D :=
    Cocone.mk _ {
      app := s
      naturality := fun _ _ f ↦ by simpa using (hs' (Arrow.mk f)).symm }
  refine ⟨hc.desc c', ?_⟩
  apply Sigma.hom_ext
  rintro ⟨k, i⟩
  rw [← Category.assoc, projection, Sigma.ι_comp_desc]
  simp only [Category.assoc, hc.fac c' k]
  simpa only [ι, Category.assoc, Sigma.ι_comp_desc_assoc] using
    congrArg (Sigma.ι (fun j ↦ (yoneda C).obj ((P k).X j)) i ≫ ·) (hs k)

end

end Presentation

private theorem hasPresentationLT_of_isColimit {K : Type v} [SmallCategory K]
    (hK : HasCardinalLT (Arrow K) κ) {D : K ⥤ ModCat.{v} C} {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ k, hasPresentationLT κ (D.obj k)) :
    hasPresentationLT κ c.pt := by
  classical
  simp only [hasPresentationLT] at hD
  choose P hI hJ using hD
  have hK' := hasCardinalLT_of_hasCardinalLT_arrow hK
  exact ⟨⟨_, _, _, _, _, _, _, Presentation.isCokernelOfDiagram P hc⟩,
    hasCardinalLT_sigma _ κ hK' hI,
    (hasCardinalLT_sum_iff _ _ _ (IsRegular.aleph0_le Fact.out)).2
      ⟨hasCardinalLT_sigma _ κ hK' hJ, hasCardinalLT_sigma _ κ hK (fun a ↦ hI a.left)⟩⟩

private theorem hasPresentationLT_iff_isCardinalPresentable [EssentiallySmall.{v} C]
    (F : ModCat.{v} C) : hasPresentationLT κ F ↔ IsCardinalPresentable F κ := by
  constructor
  · rintro ⟨P, hI, hJ⟩
    have (i : WalkingParallelPair) :
        IsCardinalPresentable ((parallelPair P.relation 0).obj i) κ := by
      cases i
      · exact isCardinalPresentable_sigma_yoneda κ hJ P.Y
      · exact isCardinalPresentable_sigma_yoneda κ hI P.X
    exact isCardinalPresentable_of_isColimit' _ P.isCokernel κ
      (hasCardinalLT_of_finite _ _ (IsRegular.aleph0_le Fact.out))
  · intro hF
    have := Cardinal.fact_isRegular_aleph0.{v}
    have hgen := isStrongGenerator_ofObj_yoneda (C := C)
    have hpres : (ObjectProperty.ofObj ((equivSmallModel.{v} C).inverse ⋙ yoneda C).obj) ≤
        isCardinalPresentable (ModCat.{v} C) κ := by
      rintro _ ⟨X⟩
      refine isCardinalPresentable_monotone _ (IsRegular.aleph0_le Fact.out) _ ?_
      exact inferInstanceAs (IsFinitelyPresentable.{v} ((yoneda C).obj
        ((equivSmallModel.{v} C).inverse.obj X)))
    rw [← isCardinalPresentable_iff,
      IsStrongGenerator.colimitsCardinalClosure_eq_isCardinalPresentable hgen hpres] at hF
    refine ObjectProperty.colimitsCardinalClosure_le _ _ (fun K _ hK ↦ ?_) ?_ _ hF
    · exact ⟨fun _ ⟨h⟩ ↦ hasPresentationLT_of_isColimit κ hK h.isColimit h.prop_diag_obj⟩
    · rintro _ ⟨X⟩
      exact hasPresentationLT_yoneda κ _

/-- Over an essentially small preadditive category, a module is `κ`-presentable if and only if
it is a cokernel between coproducts of representable modules indexed by types of size below
the regular cardinal `κ`. -/
theorem isCardinalPresentable_iff_cokernel_of_representables [EssentiallySmall.{v} C]
    (F : ModCat.{v} C) :
    IsCardinalPresentable F κ ↔
      ∃ (I J : Type v), HasCardinalLT I κ ∧ HasCardinalLT J κ ∧
        ∃ (X : I → C) (Y : J → C)
          (d : (∐ fun j ↦ (yoneda C).obj (Y j)) ⟶ ∐ fun i ↦ (yoneda C).obj (X i)),
          Nonempty (cokernel d ≅ F) := by
  rw [← hasPresentationLT_iff_isCardinalPresentable κ]
  constructor
  · rintro ⟨P, hI, hJ⟩
    exact ⟨P.I, P.J, hI, hJ, P.X, P.Y, P.relation,
      ⟨(cokernelIsCokernel P.relation).coconePointUniqueUpToIso P.isCokernel⟩⟩
  · rintro ⟨I, J, hI, hJ, X, Y, d, ⟨e⟩⟩
    exact ⟨⟨I, J, X, Y, d, _, _, cokernel.cokernelIso d (cokernel.π d ≫ e.hom) e rfl⟩, hI, hJ⟩

local instance : Fact (ℵ₁ : Cardinal.{v}).IsRegular := ⟨isRegular_aleph_one⟩

/-- The `ℵ₁`-presentable modules are precisely the cokernels of maps between countable sums
of representables. -/
theorem isCardinalPresentable_aleph_one_iff [EssentiallySmall.{v} C] (F : ModCat.{v} C) :
    IsCardinalPresentable F (ℵ₁ : Cardinal.{v}) ↔
      ∃ (I J : Type v) (_ : Countable I) (_ : Countable J) (X : I → C) (Y : J → C)
        (d : (∐ fun j ↦ (yoneda C).obj (Y j)) ⟶ ∐ fun i ↦ (yoneda C).obj (X i)),
        Nonempty (cokernel d ≅ F) := by
  simpa [HasCardinalLT, lt_aleph_one_iff, mk_le_aleph0_iff, and_assoc, and_left_comm,
    exists_prop] using isCardinalPresentable_iff_cokernel_of_representables ℵ₁ F

private theorem exists_cokernel_yoneda_iff {I J : Type*} [Small.{v} I] [Small.{v} J]
    (X : I → C) (Y : J → C) (F : ModCat.{v} C) :
    (∃ (d : (∐ fun j ↦ (yoneda C).obj (Y j)) ⟶ ∐ fun i ↦ (yoneda C).obj (X i)),
      Nonempty (cokernel d ≅ F)) ↔
    ∃ (d : (∐ fun j ↦ preadditiveYoneda.obj (Y j)) ⟶ ∐ fun i ↦ preadditiveYoneda.obj (X i)),
      Nonempty (cokernel d ≅ F.obj) := by
  let incl := (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι
  let eX : incl.obj (∐ fun i ↦ (yoneda C).obj (X i)) ≅ ∐ fun i ↦ preadditiveYoneda.obj (X i) :=
    PreservesCoproduct.iso incl _
  let eY : incl.obj (∐ fun j ↦ (yoneda C).obj (Y j)) ≅ ∐ fun j ↦ preadditiveYoneda.obj (Y j) :=
    PreservesCoproduct.iso incl _
  constructor
  · rintro ⟨d, ⟨e⟩⟩
    let f := eY.inv ≫ incl.map d ≫ eX.hom
    let i := cokernel.mapIso (incl.map d) f eY eX (by simp [f])
    exact ⟨f, ⟨i.symm ≪≫ (PreservesCokernel.iso incl d).symm ≪≫ incl.mapIso e⟩⟩
  · rintro ⟨f, ⟨e⟩⟩
    let d := incl.preimage (eY.hom ≫ f ≫ eX.inv)
    let i := cokernel.mapIso (incl.map d) f eY eX (by
      dsimp only [d]
      rw [Functor.map_preimage]
      simp)
    exact ⟨d, ⟨incl.preimageIso (PreservesCokernel.iso incl d ≪≫ i ≪≫ e)⟩⟩

/-- A module is finitely presentable exactly when its underlying functor has a finite
presentation by representables. -/
theorem isFinitelyPresentable_iff_isFinitelyPresentedFunctor [EssentiallySmall.{v} C]
    (F : ModCat.{v} C) : IsFinitelyPresentable.{v} F ↔ IsFinitelyPresentedFunctor F.obj := by
  have := Cardinal.fact_isRegular_aleph0.{v}
  simp only [IsFinitelyPresentable, isFinitelyPresentedFunctor_iff_exists_isColimit,
    isCardinalPresentable_iff_cokernel_of_representables Cardinal.aleph0]
  constructor
  · rintro ⟨I, J, hI, hJ, X, Y, d, ⟨e⟩⟩
    have := (hasCardinalLT_aleph0_iff I).1 hI
    have := (hasCardinalLT_aleph0_iff J).1 hJ
    obtain ⟨n, ⟨i⟩⟩ := Finite.exists_equiv_fin I
    obtain ⟨m, ⟨j⟩⟩ := Finite.exists_equiv_fin J
    obtain ⟨d', ⟨e'⟩⟩ := (exists_cokernel_yoneda_iff X Y F).1 ⟨d, ⟨e⟩⟩
    let eX := Sigma.reindex i.symm (fun k ↦ preadditiveYoneda.obj (X k))
    let eY := Sigma.reindex j.symm (fun k ↦ preadditiveYoneda.obj (Y k))
    let f := eY.hom ≫ d' ≫ eX.inv
    let iso := cokernel.mapIso f d' eY eX (by simp [f])
    let q := cokernel.π f ≫ (iso ≪≫ e').hom
    exact ⟨m, n, Y ∘ j.symm, X ∘ i.symm, f, q, by simp [q],
      ⟨cokernel.cokernelIso f q (iso ≪≫ e') rfl⟩⟩
  · rintro ⟨m, n, Y, X, d, p, hp, ⟨hc⟩⟩
    let eX := Sigma.reindex (Equiv.ulift : ULift.{v} (Fin n) ≃ Fin n)
      (fun k ↦ preadditiveYoneda.obj (X k))
    let eY := Sigma.reindex (Equiv.ulift : ULift.{v} (Fin m) ≃ Fin m)
      (fun k ↦ preadditiveYoneda.obj (Y k))
    let f := eY.hom ≫ d ≫ eX.inv
    let iso := cokernel.mapIso f d eY eX (by simp [f])
    let e := (cokernelIsCokernel d).coconePointUniqueUpToIso hc
    obtain ⟨g, hg⟩ := (exists_cokernel_yoneda_iff (X ∘ ULift.down) (Y ∘ ULift.down) F).2
      ⟨f, ⟨iso ≪≫ e⟩⟩
    exact ⟨ULift.{v} (Fin n), ULift.{v} (Fin m), (hasCardinalLT_aleph0_iff _).2 inferInstance,
      (hasCardinalLT_aleph0_iff _).2 inferInstance, _, _, g, hg⟩

end Cardinal

end TauCeti.ModCat
