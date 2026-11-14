/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Singularity.Stable
public import TauCeti.CategoryTheory.Exact.DerivedCategory.BoundedPlus
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Mk
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Injective.Stalk
public import TauCeti.CategoryTheory.Exact.Frobenius
public import TauCeti.CategoryTheory.Exact.Stable.Autoequivalence

/-!
# The Keller–Vossieck theorem

Let `E` be a Frobenius exact structure. The functor `stable(E) ⥤ D_sg(E)` placing an object in
degree zero is an equivalence onto the singularity category `Dᵇ(E) / Kᵇ(proj E)` (Keller–Vossieck,
Example 2.3). No idempotent completeness is assumed.

Morphisms of `D_sg(E)` are computed through the bounded below derived category
`D⁺(E) ≃ K⁺(inj E)`, in which `Dᵇ(E)` is a full subcategory.

* **Faithfulness.** A morphism `f : M ⟶ N` vanishing in `D_sg(E)` factors in `Dᵇ(E)` through a
  bounded complex of projectives. Passing to injective resolutions `I_M` and `I_N`, the induced map
  `I_M ⟶ I_N` factors in the homotopy category through a bounded complex, so it is eventually
  null-homotopic, and its restriction `f` to the cycles in degree `0` factors through a
  projective object.
* **Fullness.** A morphism `M ⟶ N` of `D_sg(E)` is a right fraction `M ← X → N` whose first map
  has cone a bounded complex of projectives `K`. Truncating `I_M` above a degree `k + 1` beyond `K`
  gives a bounded complex `T ≃ M` whose lower terms are projective and whose top term is the
  object of cycles `Zᵏ⁺¹` of `I_M`; the inclusion of the top term is inverted in `D_sg(E)` and
  admits no nonzero map to `K`, so it factors through `X`. The resulting map `Zᵏ⁺¹[-k-1] ⟶ N` is a
  map of cycles of injective resolutions, which lifts to a map `I_M ⟶ I_N`.
* **Essential surjectivity.** The same truncation of the injective resolution of a bounded complex
  shows that it is isomorphic in `D_sg(E)` to an object placed in a positive degree `t`, and
  `Zᵗ ≃ Σᵗ` together with stable loops brings it to degree zero.

## Main results

* `TauCeti.ExactStructure.IsFrobenius.mem_projectiveStableIdeal_of_singleToSingularity_map_eq_zero`:
  a morphism vanishing in the singularity category factors through a projective object.
* `TauCeti.ExactStructure.IsFrobenius.singleToSingularity_map_surjective`: every morphism of the
  singularity category between objects in degree zero comes from the category.
* `TauCeti.ExactStructure.IsFrobenius.fullyFaithfulStableToSingularity`: `stable(E) ⥤ D_sg(E)` is
  fully faithful.
* `TauCeti.ExactStructure.IsFrobenius.essSurj_stableToSingularity`: it is essentially surjective.
* `TauCeti.ExactStructure.IsFrobenius.isEquivalence_stableToSingularity`: **the Keller–Vossieck
  theorem**, it is an equivalence.

## References

* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris
  **305** (1987), 225--228, Example 2.3.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open HomotopyCategory.Bounded (mkMap singleFunctorObjIsoMk)

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C}

namespace IsFrobenius

variable (hF : E.IsFrobenius)

/-- The object `M` in degree zero, in `K⁺(C)`. -/
private noncomputable abbrev singlePlus (M : C) : _root_.HomotopyCategory.Plus C :=
  (HomotopyCategory.Bounded.toPlus C).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj M)

/-- The injective resolution of `M`, in `K⁺(C)`. -/
private noncomputable abbrev resPlus (M : C) : _root_.HomotopyCategory.Plus C :=
  ⟨(_root_.HomotopyCategory.quotient C (.up ℤ)).obj (hF.enoughInjectives.stalkResolution M),
    (_root_.HomotopyCategory.plus_quotient_obj_iff _).2 ⟨0, inferInstance⟩⟩

/-- The injective resolution of `M`, as a morphism of `K⁺(C)`. -/
private noncomputable abbrev resHom (M : C) : singlePlus M ⟶ resPlus hF M :=
  ObjectProperty.homMk ((HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M ≫
    (_root_.HomotopyCategory.quotient C (.up ℤ)).map (hF.enoughInjectives.stalkResolutionι M))

private instance (M : C) : IsIso ((PlusDerivedCategory.Q E).map (resHom hF M)) :=
  Localization.inverts _ E.acyclicPlus.trW _ ((E.acyclicPlus_trW_iff _).2
    (MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
      (E.homotopyAcyclic_trW_quotient_map _
        (hF.enoughInjectives.acyclic_mappingCone_stalkResolutionι M))))

/-- Maps into a bounded below complex of injectives are the same in `K⁺(C)` and in `D⁺(E)`. -/
private theorem map_bijective_of_injectivePlus {Y : _root_.HomotopyCategory.Plus C}
    (hY : E.injectivePlus Y) (X : _root_.HomotopyCategory.Plus C) :
    Function.Bijective ((PlusDerivedCategory.Q E).map : (X ⟶ Y) → _) :=
  ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated
    (E.injectivePlus_le_rightOrthogonal _ hY) _ X

private theorem injectivePlus_resPlus (M : C) : E.injectivePlus (resPlus hF M) :=
  (E.injectivePlus_iff _).2 ((E.plusInjective_iff _).2
    ⟨_, ⟨0, inferInstance⟩, hF.enoughInjectives.isInjective_stalkResolution_X M, ⟨Iso.refl _⟩⟩)

omit [HasBinaryBiproducts C] in
/-- Two maps from an object in degree zero to a complex vanishing in negative degrees which are
homotopic agree in degree zero. -/
private theorem f_zero_eq_of_homotopy {M : C} {I : CochainComplex C ℤ} [I.IsStrictlyGE 0]
    {g₁ g₂ : (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ I} (h : Homotopy g₁ g₂) :
    g₁.f 0 = g₂.f 0 := by
  have := h.comm 0
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at this
  rw [this, (HomologicalComplex.isZero_single_obj_X _ 0 M 1 (by lia)).eq_of_src (h.hom 1 0) 0,
    (I.isZero_of_isStrictlyGE 0 (-1) (by lia)).eq_of_tgt (h.hom 0 (-1)) 0]
  simp

/-- A morphism of `C` vanishing in the singularity category factors in `Dᵇ(E)` through the class of
a bounded complex of projectives. -/
private theorem exists_Q_map_eq_comp_of_singleToSingularity_map_eq_zero {M N : C} (f : M ⟶ N)
    (hf : E.singleToSingularity.map f = 0) :
    ∃ (K : CochainComplex.Bounded C) (_ : ∀ n, E.isProjective (K.obj.X n))
      (a : (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj M) ⟶
        (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.quotient C).obj K))
      (g : (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.quotient C).obj K) ⟶
        (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj N)),
      a ≫ g =
        (BoundedDerivedCategory.Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f) := by
  rw [singleToSingularity_eq] at hf
  obtain ⟨Z, s, ⟨W, a, b, hT, hW⟩, hs⟩ := (MorphismProperty.map_eq_iff_precomp
    (SingularityCategory.Q E) E.boundedProjective.trW
      ((BoundedDerivedCategory.Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f))
        0).1 (by
      rw [Functor.map_zero]
      exact hf)
  rw [comp_zero] at hs
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ hT _ hs
  obtain ⟨K, hK, ⟨e⟩⟩ := (E.boundedProjective_iff W).1 hW
  exact ⟨K, hK, a ≫ e.hom, e.inv ≫ g, by simpa using hg.symm⟩

include hF in
/-- If the image of `f : M ⟶ N` in `Dᵇ(E)` factors through the class of a bounded complex of
projectives, then `f` lifts to an eventually null-homotopic map of injective resolutions. -/
private theorem exists_isEventuallyNullHomotopic {M N : C} (f : M ⟶ N)
    (K : CochainComplex.Bounded C) (hK : ∀ n, E.isProjective (K.obj.X n))
    (a : (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj M) ⟶
      (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.quotient C).obj K))
    (g : (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.quotient C).obj K) ⟶
      (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj N))
    (hag : a ≫ g =
      (BoundedDerivedCategory.Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f)) :
    ∃ φ : hF.enoughInjectives.stalkResolution M ⟶ hF.enoughInjectives.stalkResolution N,
      CochainComplex.IsEventuallyNullHomotopic φ ∧
        resHom hF M ≫ ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map φ) =
          (HomotopyCategory.Bounded.toPlus C).map
            ((HomotopyCategory.Bounded.singleFunctor C 0).map f) ≫ resHom hF N := by
  obtain ⟨_, bK, _, _⟩ := (CochainComplex.bounded_iff C K.obj).1 K.property
  let K' := (HomotopyCategory.Bounded.quotient C).obj K
  have hKinj : E.injectivePlus ((HomotopyCategory.Bounded.toPlus C).obj K') :=
    (E.injectivePlus_iff _).2 ((E.plusInjective_iff _).2 ⟨K.obj, (CochainComplex.bounded_iff C
      K.obj).1 K.property |>.elim fun a h ↦ h.elim fun _ h ↦ ⟨a, h.1⟩,
        fun n ↦ (hF.injective_iff_projective _).2 (hK n),
        ⟨eqToIso (HomotopyCategory.Bounded.quotient_obj_obj C K)⟩⟩)
  -- In `D⁺(E)`, the induced map of resolutions factors through `K`.
  let η := BoundedDerivedCategory.QCompToPlusIso E
  obtain ⟨u, hu⟩ := (map_bijective_of_injectivePlus hKinj _).2
    (inv ((PlusDerivedCategory.Q E).map (resHom hF M)) ≫ η.inv.app _ ≫
      (BoundedDerivedCategory.toPlus E).map a ≫ η.hom.app K')
  obtain ⟨v, hv⟩ := (map_bijective_of_injectivePlus (injectivePlus_resPlus hF N) _).2
    (η.inv.app K' ≫ (BoundedDerivedCategory.toPlus E).map g ≫ η.hom.app _ ≫
      (PlusDerivedCategory.Q E).map (resHom hF N))
  have hcomp : resHom hF M ≫ u ≫ v = (HomotopyCategory.Bounded.toPlus C).map
      ((HomotopyCategory.Bounded.singleFunctor C 0).map f) ≫ resHom hF N := by
    apply (map_bijective_of_injectivePlus (injectivePlus_resPlus hF N) _).1
    rw [Functor.map_comp, Functor.map_comp, hu, hv, Functor.map_comp]
    simp only [IsIso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp_assoc, hag, BoundedDerivedCategory.toPlus_map_Q]
    simp [η]
  -- A cochain representative of `u ≫ v` is eventually null-homotopic.
  obtain ⟨φ, hφ⟩ := (_root_.HomotopyCategory.quotient C (.up ℤ)).map_surjective (u ≫ v).hom
  refine ⟨φ, CochainComplex.isEventuallyNullHomotopic_of_quotient_map_eq_comp bK
    (u.hom ≫ eqToHom (HomotopyCategory.Bounded.quotient_obj_obj C K))
    (eqToHom (HomotopyCategory.Bounded.quotient_obj_obj C K).symm ≫ v.hom)
    (by rw [hφ]; simp), ?_⟩
  rw [← hcomp]
  congr 1
  exact ObjectProperty.hom_ext _ hφ

include hF in
/-- A map of injective resolutions lifting the image of `f : M ⟶ N` in `K⁺(C)` restricts to `f`
on the cycles in degree zero. -/
private theorem cyclesMap_zero_eq {M N : C} (f : M ⟶ N)
    (φ : hF.enoughInjectives.stalkResolution M ⟶ hF.enoughInjectives.stalkResolution N)
    (h : resHom hF M ≫ ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map φ) =
      (HomotopyCategory.Bounded.toPlus C).map
        ((HomotopyCategory.Bounded.singleFunctor C 0).map f) ≫ resHom hF N) :
    (hF.enoughInjectives.stalkTailData M).cyclesMap (hF.enoughInjectives.stalkTailData N) φ 0 =
      f := by
  let hE := hF.enoughInjectives
  have h1 := congrArg (fun x ↦ x.hom) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    ObjectProperty.ιOfLE_map] at h1
  have nat := (HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.naturality f
  have h3 : (_root_.HomotopyCategory.quotient C (.up ℤ)).map (hE.stalkResolutionι M) ≫
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map φ =
        (_root_.HomotopyCategory.singleFunctor C 0).map f ≫
          (_root_.HomotopyCategory.quotient C (.up ℤ)).map (hE.stalkResolutionι N) := by
    refine (cancel_epi ((HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M)).1 ?_
    refine (Category.assoc _ _ _).symm.trans (h1.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun x ↦ x ≫
        (_root_.HomotopyCategory.quotient C (.up ℤ)).map (hE.stalkResolutionι N)) nat).trans
          (Category.assoc _ _ _))))
  -- Homotopic maps out of an object in degree zero agree in degree zero.
  have h2 := f_zero_eq_of_homotopy (_root_.HomotopyCategory.homotopyOfEq
    (hE.stalkResolutionι M ≫ φ) ((HomologicalComplex.single C (.up ℤ) 0).map f ≫
      hE.stalkResolutionι N) (by rw [Functor.map_comp, Functor.map_comp]; exact h3))
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hE.stalkResolutionι_f_zero M,
    hE.stalkResolutionι_f_zero N, HomologicalComplex.single_map_f_self] at h2
  have h4 : (hE.stalkTailData M).i 0 ≫ φ.f 0 = f ≫ (hE.stalkTailData N).i 0 :=
    (cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom).1
      ((Category.assoc _ _ _).symm.trans (h2.trans ((Category.assoc _ _ _).trans
        (congrArg (fun x ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫ x)
          ((Category.assoc _ _ _).trans (congrArg (fun x ↦ f ≫ x)
            (Iso.inv_hom_id_assoc _ _)))))))
  exact (cancel_mono ((hE.stalkTailData N).i 0)).1
    ((TailData.cyclesMap_i _ _ _ _).trans h4)

include hF in
/-- **Faithfulness in the Keller–Vossieck theorem**: a morphism of a Frobenius exact category which
vanishes in the singularity category factors through a projective object. -/
theorem mem_projectiveStableIdeal_of_singleToSingularity_map_eq_zero {M N : C} (f : M ⟶ N)
    (hf : E.singleToSingularity.map f = 0) : f ∈ E.projectiveStableIdeal.hom M N := by
  let hE := hF.enoughInjectives
  obtain ⟨K, hK, a, g, hag⟩ := exists_Q_map_eq_comp_of_singleToSingularity_map_eq_zero f hf
  obtain ⟨φ, hnull, hφ⟩ := exists_isEventuallyNullHomotopic hF f K hK a g hag
  rw [mem_projectiveStableIdeal_iff, ← cyclesMap_zero_eq hF f φ hφ]
  exact (hE.stalkTailData M).factorsThrough_cyclesMap_zero_of_isEventuallyNullHomotopic
    (hE.stalkTailData N) φ
    (fun k ↦ (hF.injective_iff_projective _).1 (hE.isInjective_stalkResolution_X M k))
    (fun k ↦ (hF.injective_iff_projective _).1 (hE.isInjective_stalkResolution_X N k)) hnull

/-- If a map from `M` in degree zero to a complex `T` vanishing above degree `k + 1` has acyclic
mapping cone, the top differential `Tᵏ ⟶ Tᵏ⁺¹` of `T` is an epimorphism. -/
private theorem epi_d_of_acyclic_mappingCone {M : C} {T : CochainComplex C ℤ} (k : ℕ)
    [T.IsStrictlyLE ((k + 1 : ℕ) : ℤ)] (r' : (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ T)
    (hcone : E.acyclic (CochainComplex.mappingCone r')) : Epi (T.d k ((k + 1 : ℕ) : ℤ)) := by
  -- In degrees `k` and `k + 1`, the mapping cone of `r'` is `T`, and its differential into the
  -- last nonzero degree is an epimorphism.
  obtain ⟨hC⟩ := (E.acyclic_iff _).1 hcone
  have := CochainComplex.mappingCone.isIso_inr_f r' (k : ℤ)
    (HomologicalComplex.isZero_single_obj_X _ 0 M _ (by lia))
  have := CochainComplex.mappingCone.isIso_inr_f r' ((k + 1 : ℕ) : ℤ)
    (HomologicalComplex.isZero_single_obj_X _ 0 M _ (by lia))
  have : Epi ((CochainComplex.mappingCone r').d k ((k + 1 : ℕ) : ℤ)) :=
    hC.epi_d (k : ℤ) ((CochainComplex.mappingCone.isZero_X_iff r' _).2
      ⟨HomologicalComplex.isZero_single_obj_X _ 0 M _ (by lia),
        T.isZero_of_isStrictlyLE ((k + 1 : ℕ) : ℤ) _ (by lia)⟩)
  have h : T.d k ((k + 1 : ℕ) : ℤ) = (CochainComplex.mappingCone.inr r').f k ≫
      (CochainComplex.mappingCone r').d k ((k + 1 : ℕ) : ℤ) ≫
        inv ((CochainComplex.mappingCone.inr r').f ((k + 1 : ℕ) : ℤ)) := by
    rw [CochainComplex.mappingCone.inr_f_d_assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- Let `j : T ⟶ I_M` map a complex vanishing above degree `k + 1` to the injective resolution of
`M`, invertible in degree `k` and monic in degree `k + 1`, with `Tᵏ ⟶ Tᵏ⁺¹` an epimorphism.
Then `j` identifies the top term `Tᵏ⁺¹` with the object of cycles `Zᵏ⁺¹` of `I_M`. -/
private theorem exists_iso_stalkTailData_Z (hE : E.EnoughInjectives) {M : C}
    {T : CochainComplex C ℤ} (k : ℕ) [T.IsStrictlyLE ((k + 1 : ℕ) : ℤ)]
    (j : T ⟶ hE.stalkResolution M) [IsIso (j.f k)] [Mono (j.f ((k + 1 : ℕ) : ℤ))]
    [Epi (T.d k ((k + 1 : ℕ) : ℤ))] :
    ∃ θ : T.X ((k + 1 : ℕ) : ℤ) ≅ (hE.stalkTailData M).Z (k + 1),
      θ.hom ≫ (hE.stalkTailData M).i (k + 1) = j.f ((k + 1 : ℕ) : ℤ) := by
  let tM := hE.stalkTailData M
  have hjp : j.f ((k + 1 : ℕ) : ℤ) ≫ tM.p (k + 1) = 0 := by
    rw [← cancel_mono (tM.i (k + 1 + 1)), Category.assoc, tM.fac, zero_comp]
    refine (j.comm _ _).trans ?_
    rw [(T.isZero_of_isStrictlyLE ((k + 1 : ℕ) : ℤ) _ (by lia)).eq_of_tgt (T.d _ _) 0, zero_comp]
  let θ : T.X ((k + 1 : ℕ) : ℤ) ⟶ tM.Z (k + 1) := tM.liftZ (k + 1) _ hjp
  have hθ : θ ≫ tM.i (k + 1) = j.f ((k + 1 : ℕ) : ℤ) := tM.liftZ_i _ _ _
  let ψ : tM.Z (k + 1) ⟶ T.X ((k + 1 : ℕ) : ℤ) :=
    tM.descZ k (inv (j.f k) ≫ T.d k ((k + 1 : ℕ) : ℤ)) (by
    rw [← cancel_mono (j.f ((k + 1 : ℕ) : ℤ)), Category.assoc, Category.assoc, zero_comp]
    refine (congrArg (fun x ↦ tM.i k ≫ inv (j.f k) ≫ x) (j.comm _ _).symm).trans ?_
    rw [IsIso.inv_hom_id_assoc]
    exact tM.i_d k)
  have hψ : tM.p k ≫ ψ = inv (j.f k) ≫ T.d k ((k + 1 : ℕ) : ℤ) := tM.p_descZ _ _ _
  have hθψ : θ ≫ ψ = 𝟙 _ := by
    rw [← cancel_epi (T.d k ((k + 1 : ℕ) : ℤ))]
    refine (?_ : _ = T.d k ((k + 1 : ℕ) : ℤ)).trans (Category.comp_id _).symm
    have h : T.d k ((k + 1 : ℕ) : ℤ) ≫ θ = j.f k ≫ tM.p k := by
      rw [← cancel_mono (tM.i (k + 1)), Category.assoc, hθ, Category.assoc, tM.fac]
      exact (j.comm _ _).symm
    rw [reassoc_of% h, hψ, IsIso.hom_inv_id_assoc]
  have hψθ : ψ ≫ θ = 𝟙 _ := by
    rw [← cancel_mono (tM.i (k + 1)), ← cancel_epi (tM.p k)]
    simp only [Category.assoc, Category.id_comp]
    rw [hθ, reassoc_of% hψ, tM.fac]
    refine (congrArg (fun x ↦ inv (j.f k) ≫ x) (j.comm _ _).symm).trans ?_
    exact IsIso.inv_hom_id_assoc _ _
  exact ⟨⟨θ, ψ, hθψ, hψθ⟩, hθ⟩

include hF in
/-- **The truncated resolution of an object.** The injective resolution `I_M` of `M`, cut off above
degree `k + 1`, is a bounded complex `T` under `M` with acyclic mapping cone, whose terms below
`k + 1` are projective and whose top term is the object of cycles `Zᵏ⁺¹` of `I_M`. -/
private theorem exists_truncation_stalk (M : C) (k : ℕ) :
    ∃ (T : CochainComplex C ℤ) (j : T ⟶ hF.enoughInjectives.stalkResolution M)
      (r' : (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ T)
      (θ : T.X ((k + 1 : ℕ) : ℤ) ≅ (hF.enoughInjectives.stalkTailData M).Z (k + 1)),
      CochainComplex.bounded C T ∧ T.IsStrictlyLE ((k + 1 : ℕ) : ℤ) ∧
        r' ≫ j = hF.enoughInjectives.stalkResolutionι M ∧
        θ.hom ≫ (hF.enoughInjectives.stalkTailData M).i (k + 1) = j.f ((k + 1 : ℕ) : ℤ) ∧
        E.acyclic (CochainComplex.mappingCone r') ∧
        ∀ l < ((k + 1 : ℕ) : ℤ), E.isProjective (T.X l) := by
  let hE := hF.enoughInjectives
  have : CochainComplex.IsStrictlyLE ((HomologicalComplex.single C (.up ℤ) 0).obj M) (k : ℤ) :=
    CochainComplex.isStrictlyLE_of_le _ 0 (k : ℤ) (by lia)
  obtain ⟨T, j, r', hr'j, hiso, hmono, hTle, hge, hcone⟩ :=
    exists_truncation_of_acyclic_mappingCone (hE.stalkResolutionι M)
      (hE.acyclic_mappingCone_stalkResolutionι M) (k : ℤ)
  have : T.IsStrictlyLE ((k + 1 : ℕ) : ℤ) := hTle
  have := hiso k le_rfl
  have : Mono (j.f ((k + 1 : ℕ) : ℤ)) := hmono
  have := epi_d_of_acyclic_mappingCone k r' hcone
  obtain ⟨θ, hθ⟩ := exists_iso_stalkTailData_Z hE k j
  refine ⟨T, j, r', θ, (CochainComplex.bounded_iff C T).2 ⟨_, _, hge 0 inferInstance, hTle⟩,
    hTle, hr'j, hθ, hcone, fun l hl ↦ ?_⟩
  have := hiso l (by lia)
  exact E.isProjective.prop_of_iso (asIso (j.f l)).symm
    ((hF.injective_iff_projective _).1 (hE.isInjective_stalkResolution_X M l))

/-- A map from an object in degree zero to a bounded complex with acyclic mapping cone is inverted
in `Dᵇ(E)`. -/
private theorem acyclicBounded_trW_homMk_single {M : C}
    {T : CochainComplex C ℤ} (hT : CochainComplex.bounded C T)
    (r' : (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ T)
    (hr' : E.acyclic (CochainComplex.mappingCone r')) :
    E.acyclicBounded.trW (ObjectProperty.homMk
      ((HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M ≫
        (_root_.HomotopyCategory.quotient C (.up ℤ)).map r') :
      (HomotopyCategory.Bounded.singleFunctor C 0).obj M ⟶ HomotopyCategory.Bounded.mk T hT) := by
  have h : (ObjectProperty.homMk ((HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M ≫
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map r') :
        (HomotopyCategory.Bounded.singleFunctor C 0).obj M ⟶ HomotopyCategory.Bounded.mk T hT) =
      (singleFunctorObjIsoMk 0 M).hom ≫ mkMap r' := by
    apply (HomotopyCategory.Bounded.ι C).map_injective
    rw [Functor.map_comp, HomotopyCategory.Bounded.ι_map_singleFunctorObjIsoMk_hom]
    rfl
  rw [h]
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
    (E.acyclicBounded_trW_homMk_quotient_map
      (X := HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single 0 M))
      (Y := HomotopyCategory.Bounded.mk T hT) r' hr')

/-- The inclusion `Tⁿ[-n] ⟶ T` of the top term of a bounded complex vanishing above degree `n`,
whose terms below `n` are projective, is inverted in the singularity category. -/
private theorem boundedProjective_trW_Q_map_mkMap_ιTop (T : CochainComplex C ℤ) (n : ℤ)
    [T.IsStrictlyLE n] (hT : CochainComplex.bounded C T)
    (hP : ∀ k < n, E.isProjective (T.X k)) :
    E.boundedProjective.trW ((BoundedDerivedCategory.Q E).map
      (mkMap (T.ιTop n) : HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n (T.X n)) ⟶
        HomotopyCategory.Bounded.mk T hT)) := by
  let e : (HomotopyCategory.Bounded.quotient C).obj ⟨T, hT⟩ ≅ HomotopyCategory.Bounded.mk T hT :=
    (HomotopyCategory.Bounded.fullyFaithfulι C).preimageIso
      (eqToIso (HomotopyCategory.Bounded.quotient_obj_obj C ⟨T, hT⟩))
  have h : (mkMap (T.ιTop n) :
      HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n (T.X n)) ⟶
        HomotopyCategory.Bounded.mk T hT) =
      (singleFunctorObjIsoMk n (T.X n)).inv ≫ HomotopyCategory.Bounded.ιTop T n hT ≫ e.hom := by
    rw [Iso.eq_inv_comp]
    have h₁ : (singleFunctorObjIsoMk n (T.X n)).hom.hom =
        (HomotopyCategory.Bounded.singleFunctorCompιIso C n).hom.app (T.X n) :=
      HomotopyCategory.Bounded.ι_map_singleFunctorObjIsoMk_hom n _
    have h₂ : e.hom.hom = eqToHom (HomotopyCategory.Bounded.quotient_obj_obj C ⟨T, hT⟩) :=
      (HomotopyCategory.Bounded.fullyFaithfulι C).map_preimage _
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, h₁, h₂, HomotopyCategory.Bounded.ιTop_hom,
      ObjectProperty.homMk_hom, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact congrArg (_ ≫ ·) (Category.id_comp _).symm
  rw [h, Functor.map_comp, Functor.map_comp]
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
    (MorphismProperty.comp_mem _ _ _ (boundedProjective_trW_Q_map_ιTop T n hT hP)
      (MorphismProperty.of_isIso _ _))

include hF in
/-- In `Dᵇ(E)`, every morphism from an object placed in degree `n` to the class of a bounded
complex of projectives vanishing above degree `b < n` is zero. -/
private theorem eq_zero_of_isStrictlyLE {n b : ℤ} (hbn : b < n) (A : C)
    (K : CochainComplex.Bounded C) [K.obj.IsStrictlyLE b] (hK : ∀ l, E.isProjective (K.obj.X l))
    (z : (BoundedDerivedCategory.Q E).obj
      (HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n A)) ⟶
        (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.quotient C).obj K)) :
    z = 0 := by
  -- Maps into `K` are computed in `Kᵇ(C)`, where they vanish for degree reasons.
  obtain ⟨g, rfl⟩ := ((E.acyclicBounded_rightOrthogonal_quotient_obj K fun l ↦
    (hF.injective_iff_projective _).2 (hK l)).map_bijective_of_isTriangulated
      (BoundedDerivedCategory.Q E) _).2 z
  have hg0 : g = 0 := by
    apply ObjectProperty.hom_ext
    obtain ⟨g', hg'⟩ := (_root_.HomotopyCategory.quotient C (.up ℤ)).map_surjective
      (g.hom ≫ eqToHom (HomotopyCategory.Bounded.quotient_obj_obj C K))
    have hg'0 : g' = 0 := by
      refine HomologicalComplex.hom_ext _ _ fun l ↦ ?_
      by_cases hl : l = n
      · exact (K.obj.isZero_of_isStrictlyLE b l (by lia)).eq_of_tgt _ _
      · exact (HomologicalComplex.isZero_single_obj_X _ _ _ l hl).eq_of_src _ _
    rw [← cancel_mono (eqToHom (HomotopyCategory.Bounded.quotient_obj_obj C K)), ← hg', hg'0,
      Functor.map_zero]
    simp
  rw [hg0, Functor.map_zero]

include hF in
/-- Let `s : X ⟶ Y` be a morphism of `Dᵇ(E)` inverted in the singularity category. For some `k`,
every morphism to `Y` from an object placed in degree `k + 1` factors through `s`. -/
private theorem exists_comp_eq_of_boundedProjective_trW {X Y : E.BoundedDerivedCategory}
    {s : X ⟶ Y} (hs : E.boundedProjective.trW s) :
    ∃ k : ℕ, ∀ (A : C) (c : (BoundedDerivedCategory.Q E).obj
      (HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single ((k + 1 : ℕ) : ℤ) A)) ⟶ Y),
        ∃ w, c = w ≫ s := by
  -- The cone of `s` is a bounded complex of projectives `K`, vanishing above some degree `k`.
  obtain ⟨P, u, v, hT, hP⟩ := hs
  obtain ⟨K, hK, ⟨e⟩⟩ := (E.boundedProjective_iff P).1 hP
  obtain ⟨_, b, _, _⟩ := (CochainComplex.bounded_iff C K.obj).1 K.property
  refine ⟨b.toNat, fun A c ↦ Triangle.coyoneda_exact₂ _ hT c ?_⟩
  rw [← cancel_mono e.hom, zero_comp]
  exact eq_zero_of_isStrictlyLE hF (by lia : b < ((b.toNat + 1 : ℕ) : ℤ)) _ K hK _

include hF in
/-- Let `j : T ⟶ I_M` identify the top term `Tᵏ⁺¹` of a complex vanishing above degree `k + 1`
with the cycles `Zᵏ⁺¹` of the injective resolution of `M`. Every map from the top term, placed in
degree `k + 1`, to the injective resolution of `N` factors as `ιTop ≫ j ≫ Φ` through a map of
resolutions `Φ`. -/
private theorem exists_ιTop_comp_eq {M N : C} (k : ℕ) {T : CochainComplex C ℤ}
    [T.IsStrictlyLE ((k + 1 : ℕ) : ℤ)] (j : T ⟶ hF.enoughInjectives.stalkResolution M)
    (θ : T.X ((k + 1 : ℕ) : ℤ) ≅ (hF.enoughInjectives.stalkTailData M).Z (k + 1))
    (hθ : θ.hom ≫ (hF.enoughInjectives.stalkTailData M).i (k + 1) = j.f ((k + 1 : ℕ) : ℤ))
    (g : (HomologicalComplex.single C (.up ℤ) ((k + 1 : ℕ) : ℤ)).obj (T.X ((k + 1 : ℕ) : ℤ)) ⟶
      hF.enoughInjectives.stalkResolution N) :
    ∃ Φ : hF.enoughInjectives.stalkResolution M ⟶ hF.enoughInjectives.stalkResolution N,
      T.ιTop _ ≫ j ≫ Φ = g := by
  let hE := hF.enoughInjectives
  let tM := hE.stalkTailData M
  let tN := hE.stalkTailData N
  -- The degree `k + 1` component of `g` lands in the cycles `Z'ᵏ⁺¹` of the resolution of `N`.
  let y : T.X ((k + 1 : ℕ) : ℤ) ⟶ (hE.stalkResolution N).X ((k + 1 : ℕ) : ℤ) :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) ((k + 1 : ℕ) : ℤ) (T.X ((k + 1 : ℕ) : ℤ))).inv ≫
      g.f ((k + 1 : ℕ) : ℤ)
  have hy : y ≫ tN.p (k + 1) = 0 := by
    rw [← cancel_mono (tN.i (k + 1 + 1)), Category.assoc, Category.assoc, tN.fac, zero_comp]
    refine (congrArg (fun x ↦ _ ≫ x) (g.comm _ _)).trans ?_
    rw [(HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)).eq_of_tgt
      (((HomologicalComplex.single C (.up ℤ) ((k + 1 : ℕ) : ℤ)).obj
        (T.X ((k + 1 : ℕ) : ℤ))).d _ _) 0, zero_comp, comp_zero]
  -- The map of cycles `Zᵏ⁺¹ ⟶ Z'ᵏ⁺¹` lifts to a map of resolutions.
  obtain ⟨Φ, hΦ⟩ := tM.exists_hom_cyclesMap_eq tN
    (fun l ↦ (hF.injective_iff_projective _).1 (hE.isInjective_stalkResolution_X M l))
    (fun l ↦ hE.isInjective_stalkResolution_X N l) (k + 1) (θ.inv ≫ tN.liftZ (k + 1) y hy)
  refine ⟨Φ, ?_⟩
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, T.ιTop_f]
  refine (cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) ((k + 1 : ℕ) : ℤ)
    (T.X ((k + 1 : ℕ) : ℤ))).inv).1 ?_
  rw [Iso.inv_hom_id_assoc]
  change j.f ((k + 1 : ℕ) : ℤ) ≫ Φ.f ((k + 1 : ℕ) : ℤ) = y
  rw [← hθ, Category.assoc, ← TailData.cyclesMap_i, hΦ]
  simp only [Category.assoc, TailData.liftZ_i, Iso.hom_inv_id_assoc]

include hF in
/-- A map of resolutions `Φ : I_M ⟶ I_N`, restricted along a factorization `M ⟶ T ⟶ I_M` of the
resolution map, extends in `K⁺(C)` the image of its map of cycles in degree zero. -/
private theorem toPlus_map_comp_resHom {M N : C} {T : CochainComplex C ℤ}
    (hT : CochainComplex.bounded C T) (r' : (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ T)
    (j : T ⟶ hF.enoughInjectives.stalkResolution M)
    (hr'j : r' ≫ j = hF.enoughInjectives.stalkResolutionι M)
    (Φ : hF.enoughInjectives.stalkResolution M ⟶ hF.enoughInjectives.stalkResolution N)
    (f : M ⟶ N)
    (hf : (hF.enoughInjectives.stalkTailData M).cyclesMap (hF.enoughInjectives.stalkTailData N) Φ
      0 = f) :
    (HomotopyCategory.Bounded.toPlus C).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f) ≫
      resHom hF N =
      (HomotopyCategory.Bounded.toPlus C).map (ObjectProperty.homMk
        ((HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M ≫
          (_root_.HomotopyCategory.quotient C (.up ℤ)).map r') :
            (HomotopyCategory.Bounded.singleFunctor C 0).obj M ⟶
              HomotopyCategory.Bounded.mk T hT) ≫
        (ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map (j ≫ Φ)) :
          (HomotopyCategory.Bounded.toPlus C).obj (HomotopyCategory.Bounded.mk T hT) ⟶
            resPlus hF N) := by
  let hE := hF.enoughInjectives
  apply ObjectProperty.hom_ext
  have nat := (HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.naturality f
  change ((HomotopyCategory.Bounded.singleFunctor C 0).map f).hom ≫
      (HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app N ≫
        (_root_.HomotopyCategory.quotient C (.up ℤ)).map (hE.stalkResolutionι N) =
    ((HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M ≫
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map r') ≫
        (_root_.HomotopyCategory.quotient C (.up ℤ)).map (j ≫ Φ)
  calc _ = ((HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M ≫
        (_root_.HomotopyCategory.singleFunctor C 0).map f) ≫
          (_root_.HomotopyCategory.quotient C (.up ℤ)).map (hE.stalkResolutionι N) :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ _) nat)
    _ = (HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M ≫
        (_root_.HomotopyCategory.quotient C (.up ℤ)).map
          ((HomologicalComplex.single C (.up ℤ) 0).map f ≫ hE.stalkResolutionι N) :=
        (Category.assoc _ _ _).trans (congrArg (fun z ↦ _ ≫ z)
          (Functor.map_comp (_root_.HomotopyCategory.quotient C (.up ℤ)) _ _).symm)
    _ = _ := by
        rw [hE.single_map_comp_stalkResolutionι M Φ f hf, ← hr'j, Category.assoc]
        exact (congrArg (fun z ↦ _ ≫ z)
          (Functor.map_comp (_root_.HomotopyCategory.quotient C (.up ℤ)) _ _)).trans
            (Category.assoc _ _ _).symm

/-- Let `s : X ⟶ Z` be inverted in `Dᵇ(E)` and `ρ : X' ⟶ R` in `D⁺(E)`. If `J : Z ⟶ R`
satisfies `f ≫ ρ = s ≫ J` in `K⁺(C)`, and `t ≫ J` is the image of `γ` followed by `ρ` in
`D⁺(E)`, then `t ≫ s⁻¹ ≫ f = γ` in `Dᵇ(E)`. -/
private theorem Q_map_comp_inv_comp_eq (hE : E.EnoughInjectives)
    {X X' Y Z : HomotopyCategory.Bounded C} {R : _root_.HomotopyCategory.Plus C} (s : X ⟶ Z)
    (hs : E.acyclicBounded.trW s) (t : Y ⟶ Z) (f : X ⟶ X')
    (ρ : (HomotopyCategory.Bounded.toPlus C).obj X' ⟶ R)
    [IsIso ((PlusDerivedCategory.Q E).map ρ)]
    (J : (HomotopyCategory.Bounded.toPlus C).obj Z ⟶ R)
    (hJ : (HomotopyCategory.Bounded.toPlus C).map f ≫ ρ =
      (HomotopyCategory.Bounded.toPlus C).map s ≫ J)
    (γ : (BoundedDerivedCategory.Q E).obj Y ⟶ (BoundedDerivedCategory.Q E).obj X')
    (hγ : (PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map t ≫ J) =
      (BoundedDerivedCategory.QCompToPlusIso E).inv.app Y ≫
        (BoundedDerivedCategory.toPlus E).map γ ≫
          (BoundedDerivedCategory.QCompToPlusIso E).hom.app X' ≫
            (PlusDerivedCategory.Q E).map ρ) :
    have := Localization.inverts (BoundedDerivedCategory.Q E) E.acyclicBounded.trW s hs
    (BoundedDerivedCategory.Q E).map t ≫ inv ((BoundedDerivedCategory.Q E).map s) ≫
      (BoundedDerivedCategory.Q E).map f = γ := by
  intro
  let η := BoundedDerivedCategory.QCompToPlusIso E
  have : IsIso ((PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map s)) :=
    Localization.inverts _ E.acyclicPlus.trW _ (E.acyclicBounded_trW_le s hs)
  have := hE.faithful_toPlus
  apply (BoundedDerivedCategory.toPlus E).map_injective
  have h2 := congrArg (PlusDerivedCategory.Q E).map hJ
  rw [Functor.map_comp, Functor.map_comp] at h2
  have h1 : η.inv.app Y ≫ (BoundedDerivedCategory.toPlus E).map
      ((BoundedDerivedCategory.Q E).map t ≫ inv ((BoundedDerivedCategory.Q E).map s) ≫
        (BoundedDerivedCategory.Q E).map f) ≫ η.hom.app X' ≫ (PlusDerivedCategory.Q E).map ρ =
      (PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map t ≫ J) := by
    simp only [Functor.map_comp, Functor.map_inv, BoundedDerivedCategory.toPlus_map_Q,
      IsIso.inv_comp, Category.assoc, Iso.inv_hom_id_app_assoc, NatIso.inv_inv_app, h2,
      IsIso.inv_hom_id_assoc, η]
  exact (cancel_mono (η.hom.app X' ≫ (PlusDerivedCategory.Q E).map ρ)).1
    ((cancel_epi (η.inv.app Y)).1 (h1.trans hγ))

/-- If `w ≫ φ.s` is inverted by a localization functor `L` and `w ≫ φ.s ≫ f = w ≫ φ.f`, then the
right fraction `φ` is sent by `L` to `L.map f`. -/
private theorem rightFraction_map_eq {D D' : Type*} [Category D] [Category D'] (L : D ⥤ D')
    {W : MorphismProperty D} [L.IsLocalization W] {X Y Z : D} (φ : W.RightFraction X Y)
    (w : Z ⟶ φ.X') (f : X ⟶ Y) [IsIso (L.map (w ≫ φ.s))] (h : (w ≫ φ.s) ≫ f = w ≫ φ.f) :
    φ.map L (Localization.inverts L W) = L.map f := by
  have : IsIso (L.map φ.s) := Localization.inverts L W _ φ.hs
  have : IsIso (L.map w) := by
    have : IsIso (L.map w ≫ L.map φ.s) := by
      rw [← L.map_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (L.map φ.s)
  rw [← cancel_epi (L.map φ.s), MorphismProperty.RightFraction.map_s_comp_map,
    ← cancel_epi (L.map w)]
  have := congrArg L.map h
  simp only [Functor.map_comp, Category.assoc] at this
  exact this.symm

include hF in
/-- **Fullness in the Keller–Vossieck theorem**: every morphism between objects of a Frobenius exact
category in the singularity category comes from a morphism of the category. -/
theorem singleToSingularity_map_surjective (M N : C) :
    Function.Surjective (E.singleToSingularity.map : (M ⟶ N) → _) := by
  rw [singleToSingularity_eq]
  intro α
  let hE := hF.enoughInjectives
  let XM := (HomotopyCategory.Bounded.singleFunctor C 0).obj M
  -- A right fraction `M ← X → N`, with `X ⟶ M` inverted in `D_sg(E)`.
  obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction (SingularityCategory.Q E)
    E.boundedProjective.trW α
  obtain ⟨k, hk⟩ := exists_comp_eq_of_boundedProjective_trW hF φ.hs
  -- The truncation `T` of the resolution of `M` above degree `k + 1`, and the inclusion `c` of
  -- its top term, inverted in `D_sg(E)`.
  obtain ⟨T, j, r', θ, hTb, hTle, hr'j, hθ, hcone, hTproj⟩ := exists_truncation_stalk hF M k
  let bW := HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single ((k + 1 : ℕ) : ℤ)
    (T.X ((k + 1 : ℕ) : ℤ)))
  let sT : bW ⟶ HomotopyCategory.Bounded.mk T hTb := mkMap (T.ιTop _)
  let sR : XM ⟶ HomotopyCategory.Bounded.mk T hTb := ObjectProperty.homMk
    ((HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M ≫
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map r')
  have hsR : E.acyclicBounded.trW sR := acyclicBounded_trW_homMk_single hTb r' hcone
  have := Localization.inverts (BoundedDerivedCategory.Q E) _ _ hsR
  let c := (BoundedDerivedCategory.Q E).map sT ≫ inv ((BoundedDerivedCategory.Q E).map sR)
  have : IsIso ((SingularityCategory.Q E).map ((BoundedDerivedCategory.Q E).map sT)) :=
    Localization.inverts _ _ _ (boundedProjective_trW_Q_map_mkMap_ιTop T _ hTb hTproj)
  have : IsIso ((SingularityCategory.Q E).map c) := by
    simp only [c, Functor.map_comp, Functor.map_inv]
    infer_instance
  obtain ⟨w, hw⟩ := hk _ c
  -- In `D⁺(E)`, the map from the top term through `X` to `N` is a map into the resolution of
  -- `N`, which comes from a map of resolutions `Φ`.
  let η := BoundedDerivedCategory.QCompToPlusIso E
  obtain ⟨g, hg⟩ := (map_bijective_of_injectivePlus (injectivePlus_resPlus hF N) _).2
    (η.inv.app bW ≫ (BoundedDerivedCategory.toPlus E).map (w ≫ φ.f) ≫ η.hom.app _ ≫
      (PlusDerivedCategory.Q E).map (resHom hF N))
  obtain ⟨g', hg'⟩ := (_root_.HomotopyCategory.quotient C (.up ℤ)).map_surjective g.hom
  obtain ⟨Φ, hΦ⟩ := exists_ιTop_comp_eq hF k j θ hθ g'
  let f : M ⟶ N := (hE.stalkTailData M).cyclesMap (hE.stalkTailData N) Φ 0
  refine ⟨f, ?_⟩
  have hgJ : (HomotopyCategory.Bounded.toPlus C).map sT ≫
      ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map (j ≫ Φ)) = g := by
    apply ObjectProperty.hom_ext
    change (_root_.HomotopyCategory.quotient C (.up ℤ)).map (T.ιTop _) ≫
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map (j ≫ Φ) = g.hom
    rw [← hg', ← hΦ]
    simp only [Functor.map_comp]
  have key := Q_map_comp_inv_comp_eq hE sR hsR sT _ (resHom hF N) _
    (toPlus_map_comp_resHom hF hTb r' j hr'j Φ f rfl) (w ≫ φ.f) (by rw [hgJ, hg])
  have : IsIso ((SingularityCategory.Q E).map (w ≫ φ.s)) := hw ▸ inferInstance
  rw [hφ]
  exact (rightFraction_map_eq _ φ w _ (by rw [← hw, ← key, Category.assoc])).symm

include hF in
/-- **The functor `stable(E) ⥤ D_sg(E)` is faithful** for a Frobenius exact structure. -/
theorem faithful_stableToSingularity : E.stableToSingularity.Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨f, rfl⟩ := E.projectiveStableFunctor.map_surjective f
    obtain ⟨g, rfl⟩ := E.projectiveStableFunctor.map_surjective g
    rw [stableToSingularity_map_projectiveStableFunctor_map,
      stableToSingularity_map_projectiveStableFunctor_map, cancel_epi, cancel_mono] at h
    replace h : E.singleToSingularity.map (f - g) = 0 := by
      rw [Functor.map_sub, h, sub_self]
    exact CategoryTheory.Quotient.sound _ ((MorphismIdeal.rel_iff _).2
      (hF.mem_projectiveStableIdeal_of_singleToSingularity_map_eq_zero _ h))

include hF in
/-- **The functor `stable(E) ⥤ D_sg(E)` is full** for a Frobenius exact structure. -/
theorem full_stableToSingularity : E.stableToSingularity.Full where
  map_surjective {X Y} α := by
    obtain ⟨f, hf⟩ := hF.singleToSingularity_map_surjective X.as Y.as
      (eqToHom (stableToSingularity_obj_projectiveStableFunctor_obj E X.as).symm ≫ α ≫
        eqToHom (stableToSingularity_obj_projectiveStableFunctor_obj E Y.as))
    exact ⟨E.projectiveStableFunctor.map f, by
      rw [stableToSingularity_map_projectiveStableFunctor_map, hf]
      simp⟩

/-- **The functor `stable(E) ⥤ D_sg(E)` is fully faithful** for a Frobenius exact structure. -/
noncomputable def fullyFaithfulStableToSingularity : E.stableToSingularity.FullyFaithful :=
  have := hF.full_stableToSingularity
  have := hF.faithful_stableToSingularity
  .ofFullyFaithful _

/-! ### Essential surjectivity -/

/-- The object `X` placed in degree `a`, in the singularity category. -/
private noncomputable abbrev sg (E : ExactStructure C) (a : ℤ) (X : C) : E.SingularityCategory :=
  (SingularityCategory.Q E).obj ((BoundedDerivedCategory.Q E).obj
    ((HomotopyCategory.Bounded.singleFunctor C a).obj X))

/-- Shifting an object placed in degree `a'` by `n` places it in degree `a`, when `n + a = a'`. -/
private noncomputable def sgShiftIso (n a a' : ℤ) (h : n + a = a') (X : C) :
    (sg E a' X)⟦n⟧ ≅ sg E a X :=
  ((BoundedDerivedCategory.Q E ⋙ SingularityCategory.Q E).commShiftIso n).symm.app _ ≪≫
    (BoundedDerivedCategory.Q E ⋙ SingularityCategory.Q E).mapIso
      (((HomotopyCategory.Bounded.singleFunctors C).shiftIso n a a' h).app X)

/-- Objects isomorphic in the stable category are isomorphic in the singularity category in every
degree. -/
private noncomputable def sgIsoOfStableIso (a : ℤ) {X Y : C}
    (e : E.projectiveStableFunctor.obj X ≅ E.projectiveStableFunctor.obj Y) :
    sg E a X ≅ sg E a Y :=
  (shiftEquiv E.SingularityCategory a).fullyFaithfulFunctor.preimageIso
    (sgShiftIso a 0 a (add_zero a) X ≪≫ (E.stableToSingularityObjIso X).symm ≪≫
      E.stableToSingularity.mapIso e ≪≫ E.stableToSingularityObjIso Y ≪≫
        (sgShiftIso a 0 a (add_zero a) Y).symm)

include hF in
/-- The object of cycles `Zᵏ⁺¹` of the injective resolution of `M`, placed in degree `k + 1`, is
isomorphic to `M` in the singularity category. -/
private theorem nonempty_sg_stalkZ_iso (M : C) (k : ℕ) :
    Nonempty (sg E ((k + 1 : ℕ) : ℤ) (hF.enoughInjectives.stalkZ M (k + 1)) ≅ sg E 0 M) := by
  obtain ⟨T, j, r', θ, hTb, hTle, -, -, hcone, hTproj⟩ := exists_truncation_stalk hF M k
  have : T.IsStrictlyLE ((k + 1 : ℕ) : ℤ) := hTle
  let sT : HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single _ (T.X ((k + 1 : ℕ) : ℤ))) ⟶
      HomotopyCategory.Bounded.mk T hTb :=
    mkMap (T.ιTop _)
  have : IsIso ((SingularityCategory.Q E).map ((BoundedDerivedCategory.Q E).map sT)) :=
    Localization.inverts _ E.boundedProjective.trW _
      (boundedProjective_trW_Q_map_mkMap_ιTop T _ hTb hTproj)
  have : IsIso ((BoundedDerivedCategory.Q E).map (ObjectProperty.homMk
      ((HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M ≫
        (_root_.HomotopyCategory.quotient C (.up ℤ)).map r') :
      (HomotopyCategory.Bounded.singleFunctor C 0).obj M ⟶ HomotopyCategory.Bounded.mk T hTb)) :=
    Localization.inverts _ E.acyclicBounded.trW _ (acyclicBounded_trW_homMk_single hTb r' hcone)
  exact ⟨(BoundedDerivedCategory.Q E ⋙ SingularityCategory.Q E).mapIso
    ((HomotopyCategory.Bounded.singleFunctor C _).mapIso θ.symm ≪≫
      HomotopyCategory.Bounded.singleFunctorObjIsoMk _ _) ≪≫
      asIso ((SingularityCategory.Q E).map ((BoundedDerivedCategory.Q E).map sT)) ≪≫
        (SingularityCategory.Q E).mapIso (asIso ((BoundedDerivedCategory.Q E).map
          (ObjectProperty.homMk ((HomotopyCategory.Bounded.singleFunctorCompιIso C 0).hom.app M ≫
            (_root_.HomotopyCategory.quotient C (.up ℤ)).map r')))).symm⟩

include hF in
/-- Every object is, in the stable category, isomorphic to the object of cycles `Zᵗ` of the
injective resolution of some object. -/
private theorem exists_stalkZ_iso (t : ℕ) (Z : C) : ∃ M : C,
    Nonempty (E.projectiveStableFunctor.obj (hF.enoughInjectives.stalkZ M t) ≅
      E.projectiveStableFunctor.obj Z) := by
  -- Take `t`-fold stable loops: `Zᵗ⁺¹` is the suspension of `Zᵗ`.
  induction t generalizing Z with
  | zero => exact ⟨Z, ⟨Iso.refl _⟩⟩
  | succ t ih =>
    obtain ⟨M, ⟨e⟩⟩ := ih (hF.enoughProjectives.stableLoop.obj
      (E.projectiveStableFunctor.obj Z)).as
    exact ⟨M, ⟨hF.projectiveStableIsoSuspensionObj
      (hF.enoughInjectives.injectivePresentation _) ≪≫
        eqToIso (hF.stableSuspension_obj_projectiveStableFunctor_obj _).symm ≪≫
          hF.stableSuspension.mapIso e ≪≫ hF.stableLoopCompStableSuspensionIso.app _⟩⟩

include hF in
/-- In the singularity category, a bounded complex is isomorphic to an object placed in a positive
degree. -/
private theorem exists_sg_iso_of_bounded (L : CochainComplex C ℤ)
    (hL : CochainComplex.bounded C L) : ∃ (k : ℕ) (Z : C),
      Nonempty ((SingularityCategory.Q E).obj ((BoundedDerivedCategory.Q E).obj
        (HomotopyCategory.Bounded.mk L hL)) ≅
        sg E ((k + 1 : ℕ) : ℤ) Z) := by
  obtain ⟨a, b, _, _⟩ := (CochainComplex.bounded_iff C L).1 hL
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b ≤ (k : ℤ) := ⟨b.toNat, Int.self_le_toNat b⟩
  have : L.IsStrictlyLE (k : ℤ) := L.isStrictlyLE_of_le b k hk
  obtain ⟨I, α, hIa, hI, hα⟩ := hF.enoughInjectives.exists_injectiveResolution L a
  obtain ⟨T, j, r', -, hiso, -, hTle, hge, hcone⟩ :=
    exists_truncation_of_acyclic_mappingCone α hα (k : ℤ)
  have hTb : CochainComplex.bounded C T :=
    (CochainComplex.bounded_iff C T).2 ⟨_, _, hge a hIa, hTle⟩
  have : T.IsStrictlyLE ((k + 1 : ℕ) : ℤ) := hTle
  let sT : HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single _ (T.X ((k + 1 : ℕ) : ℤ))) ⟶
      HomotopyCategory.Bounded.mk T hTb :=
    mkMap (T.ιTop _)
  have : IsIso ((SingularityCategory.Q E).map ((BoundedDerivedCategory.Q E).map sT)) :=
    Localization.inverts _ E.boundedProjective.trW _
      (boundedProjective_trW_Q_map_mkMap_ιTop T _ hTb fun l hl ↦ by
        have := hiso l (by lia)
        exact E.isProjective.prop_of_iso (asIso (j.f l)).symm
          ((hF.injective_iff_projective _).1 (hI l)))
  let sR : HomotopyCategory.Bounded.mk L hL ⟶ HomotopyCategory.Bounded.mk T hTb :=
    ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map r')
  have : IsIso ((BoundedDerivedCategory.Q E).map sR) :=
    Localization.inverts _ E.acyclicBounded.trW _
      (E.acyclicBounded_trW_homMk_quotient_map (X := HomotopyCategory.Bounded.mk L hL)
        (Y := HomotopyCategory.Bounded.mk T hTb) r' hcone)
  exact ⟨k, T.X ((k + 1 : ℕ) : ℤ), ⟨(SingularityCategory.Q E).mapIso
    (asIso ((BoundedDerivedCategory.Q E).map sR)) ≪≫
      (asIso ((SingularityCategory.Q E).map ((BoundedDerivedCategory.Q E).map sT))).symm ≪≫
        (BoundedDerivedCategory.Q E ⋙ SingularityCategory.Q E).mapIso
          (HomotopyCategory.Bounded.singleFunctorObjIsoMk _ _).symm⟩⟩

include hF in
/-- **Essential surjectivity in the Keller–Vossieck theorem**: every object of the singularity
category of a Frobenius exact category is isomorphic to an object of the category placed in degree
zero. -/
theorem essSurj_stableToSingularity : E.stableToSingularity.EssSurj where
  mem_essImage Y := by
    have := Localization.essSurj (SingularityCategory.Q E) E.boundedProjective.trW
    have := Localization.essSurj (BoundedDerivedCategory.Q E) E.acyclicBounded.trW
    let X := (SingularityCategory.Q E).objPreimage Y
    let X' := (BoundedDerivedCategory.Q E).objPreimage X
    have hL : CochainComplex.bounded C X'.obj.as :=
      (HomotopyCategory.bounded_quotient_obj_iff _).1 X'.property
    obtain ⟨k, Z, ⟨e⟩⟩ := exists_sg_iso_of_bounded hF X'.obj.as hL
    obtain ⟨M, ⟨e'⟩⟩ := exists_stalkZ_iso hF (k + 1) Z
    obtain ⟨e''⟩ := nonempty_sg_stalkZ_iso hF M k
    exact ⟨E.projectiveStableFunctor.obj M, ⟨E.stableToSingularityObjIso M ≪≫ e''.symm ≪≫
      sgIsoOfStableIso _ e' ≪≫ e.symm ≪≫
      (SingularityCategory.Q E).mapIso ((BoundedDerivedCategory.Q E).objObjPreimageIso X) ≪≫
        (SingularityCategory.Q E).objObjPreimageIso Y⟩⟩

include hF in
/-- **The Keller–Vossieck theorem**: for a Frobenius exact category, the functor
`stable(E) ⥤ D_sg(E)` placing an object in degree zero is an equivalence. -/
theorem isEquivalence_stableToSingularity : E.stableToSingularity.IsEquivalence where
  faithful := hF.faithful_stableToSingularity
  full := hF.full_stableToSingularity
  essSurj := hF.essSurj_stableToSingularity

end IsFrobenius

end TauCeti.ExactStructure
