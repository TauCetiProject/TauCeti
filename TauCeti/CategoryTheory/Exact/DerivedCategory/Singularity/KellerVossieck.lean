/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Singularity.Stable.Basic
public import TauCeti.CategoryTheory.Exact.Frobenius
import TauCeti.CategoryTheory.Exact.DerivedCategory.BoundedPlus
import TauCeti.CategoryTheory.Exact.HomologicalComplex.Injective.Stalk
import TauCeti.CategoryTheory.Exact.Stable.Autoequivalence
import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Equivalence

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
* **Fullness.** Truncating `I_M` above a degree `k + 1` gives a bounded complex `T ≃ M` whose
  lower terms are projective and whose top term is the object of cycles `Zᵏ⁺¹` of `I_M`; the
  inclusion `δₖ : Zᵏ⁺¹[-k-1] ⟶ T ≃ M` of the top term is inverted in `D_sg(E)`. A map from `M` to a
  bounded complex of projectives `K` is killed by `δₖ` once `k` lies beyond `K`, so every morphism
  `M ⟶ N` of `D_sg(E)` becomes, after composing with `δₖ`, a morphism `Zᵏ⁺¹[-k-1] ⟶ N` of `Dᵇ(E)`
  (`ObjectProperty.TrWLocalization.exists_map_comp_eq_map`). This is a map of cycles of injective
  resolutions, which lifts to a map `I_M ⟶ I_N`.
* **Essential surjectivity.** The same truncation of the injective resolution of a bounded complex
  shows that it is isomorphic in `D_sg(E)` to an object placed in a positive degree `t`, and
  `Zᵗ ≃ Σᵗ` together with stable loops brings it to degree zero.

## Main results

* `TauCeti.ExactStructure.IsFrobenius.mem_projectiveStableIdeal_of_singleToSingularity_map_eq_zero`:
  a morphism vanishing in the singularity category factors through a projective object.
* `TauCeti.ExactStructure.IsFrobenius.kerIdeal_singleToSingularity`: the kernel of `C ⥤ D_sg(E)`
  is the ideal of morphisms factoring through a projective object.
* `TauCeti.ExactStructure.IsFrobenius.singleToSingularity_map_surjective`: every morphism of the
  singularity category between objects in degree zero comes from the category.
* `TauCeti.ExactStructure.IsFrobenius.essSurj_singleToSingularity`: every object of the
  singularity category is isomorphic to an object placed in degree zero.
* `TauCeti.ExactStructure.IsFrobenius.fullyFaithfulStableToSingularity`: `stable(E) ⥤ D_sg(E)` is
  fully faithful.
* `TauCeti.ExactStructure.IsFrobenius.essSurj_stableToSingularity`: it is essentially surjective.
* `TauCeti.ExactStructure.IsFrobenius.isEquivalence_stableToSingularity`: **the Keller–Vossieck
  theorem**, it is an equivalence.

## References

* Bernhard Keller, Dieter Vossieck, *Sous les catégories dérivées*, C. R. Acad. Sci. Paris
  **305** (1987), 225--228, Example 2.3.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Math. **67** (1990),
  379--417, Section 4, for morphisms of `Dᵇ(E)` computed in `D⁺(E) ≃ K⁺(inj E)` without
  idempotent completeness.
* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Sections 10--13, for acyclic complexes, resolutions and
  Frobenius exact categories.
-/

public section

namespace TauCeti.ExactStructure.IsFrobenius

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open HomotopyCategory.Bounded (mkMap singleFunctorObjIsoMk)

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-! ### Injective resolutions in `K⁺(C)` -/

section Resolutions

/-- The object `M` in degree zero, in `K⁺(C)`. -/
private noncomputable abbrev singlePlus (M : C) : _root_.HomotopyCategory.Plus C :=
  (HomotopyCategory.Bounded.toPlus C).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj M)

variable {E : ExactStructure C} (hE : E.EnoughInjectives)

/-- The injective resolution of `M`, in `K⁺(C)`. -/
private noncomputable abbrev resPlus (M : C) : _root_.HomotopyCategory.Plus C :=
  ⟨(_root_.HomotopyCategory.quotient C (.up ℤ)).obj (hE.stalkResolution M),
    (_root_.HomotopyCategory.plus_quotient_obj_iff _).2 ⟨0, inferInstance⟩⟩

/-- The injective resolution of `M`, as a morphism of `K⁺(C)`. -/
private noncomputable abbrev resHom (M : C) : singlePlus M ⟶ resPlus hE M :=
  (HomotopyCategory.Bounded.toPlus C).map (singleFunctorObjIsoMk 0 M).hom ≫
    ObjectProperty.homMk
      ((_root_.HomotopyCategory.quotient C (.up ℤ)).map (hE.stalkResolutionι M))

private instance (M : C) : IsIso ((PlusDerivedCategory.Q E).map (resHom hE M)) := by
  have : IsIso ((PlusDerivedCategory.Q E).map (ObjectProperty.homMk
      ((_root_.HomotopyCategory.quotient C (.up ℤ)).map (hE.stalkResolutionι M)) :
        (HomotopyCategory.Bounded.toPlus C).obj
          (HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single 0 M)) ⟶ resPlus hE M)) :=
    Localization.inverts _ E.acyclicPlus.trW _ ((E.acyclicPlus_trW_iff _).2
      (E.homotopyAcyclic_trW_quotient_map _ (hE.acyclic_mappingCone_stalkResolutionι M)))
  rw [Functor.map_comp]
  infer_instance

private theorem injectivePlus_resPlus (M : C) : E.injectivePlus (resPlus hE M) :=
  (E.injectivePlus_iff _).2 ((E.plusInjective_iff _).2
    ⟨_, ⟨0, inferInstance⟩, hE.isInjective_stalkResolution_X M, ⟨Iso.refl _⟩⟩)

/-- The square of resolutions of `f : M ⟶ N` along `φ : I_M ⟶ I_N` commutes in `K⁺(C)` exactly
when the corresponding square of complexes commutes in the homotopy category. -/
private theorem toPlus_map_comp_resHom_eq_iff {M N : C} (f : M ⟶ N)
    (φ : hE.stalkResolution M ⟶ hE.stalkResolution N) :
    (HomotopyCategory.Bounded.toPlus C).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f) ≫
        resHom hE N =
      resHom hE M ≫ ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map φ) ↔
    (_root_.HomotopyCategory.quotient C (.up ℤ)).map
        ((HomologicalComplex.single C (.up ℤ) 0).map f ≫ hE.stalkResolutionι N) =
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map (hE.stalkResolutionι M ≫ φ) := by
  -- Move `f` past the identification of `M` in degree zero, and cancel it.
  simp only [resHom, Category.assoc]
  rw [← Functor.map_comp_assoc,
    HomotopyCategory.Bounded.singleFunctor_map_comp_singleFunctorObjIsoMk_hom, Functor.map_comp,
    Category.assoc, cancel_epi]
  simp only [ObjectProperty.hom_ext_iff, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.homMk_hom, ObjectProperty.ιOfLE_map, ← Functor.map_comp]

/-- A map of injective resolutions lifting the image of `f : M ⟶ N` in `K⁺(C)` restricts to `f`
on the cycles in degree zero. -/
private theorem cyclesMap_zero_eq {M N : C} (f : M ⟶ N)
    (φ : hE.stalkResolution M ⟶ hE.stalkResolution N)
    (h : resHom hE M ≫ ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map φ) =
      (HomotopyCategory.Bounded.toPlus C).map
        ((HomotopyCategory.Bounded.singleFunctor C 0).map f) ≫ resHom hE N) :
    (hE.stalkTailDataZZeroIso M).inv ≫
      (hE.stalkTailData M).cyclesMap (hE.stalkTailData N) φ 0 ≫
        (hE.stalkTailDataZZeroIso N).hom = f :=
  hE.cyclesMap_stalkTailData_zero_eq_of_homotopy φ f
    (_root_.HomotopyCategory.homotopyOfEq _ _
      ((toPlus_map_comp_resHom_eq_iff hE f φ).1 h.symm).symm)

include hE in
/-- Let `s : X ⟶ Z` be inverted in `Dᵇ(E)` and `ρ : X' ⟶ R` in `D⁺(E)`. If `J : Z ⟶ R`
satisfies `f ≫ ρ = s ≫ J` in `K⁺(C)`, and `t ≫ J` is the image of `γ` followed by `ρ` in
`D⁺(E)`, then `t ≫ s⁻¹ ≫ f = γ` in `Dᵇ(E)`. -/
private theorem Q_map_comp_inv_comp_eq {X X' Y Z : HomotopyCategory.Bounded C}
    {R : _root_.HomotopyCategory.Plus C} (s : X ⟶ Z) [IsIso ((BoundedDerivedCategory.Q E).map s)]
    (t : Y ⟶ Z) (f : X ⟶ X') (ρ : (HomotopyCategory.Bounded.toPlus C).obj X' ⟶ R)
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
    (BoundedDerivedCategory.Q E).map t ≫ inv ((BoundedDerivedCategory.Q E).map s) ≫
      (BoundedDerivedCategory.Q E).map f = γ := by
  let η := BoundedDerivedCategory.QCompToPlusIso E
  have : IsIso ((PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map s)) := by
    rw [← Functor.comp_map (HomotopyCategory.Bounded.toPlus C) (PlusDerivedCategory.Q E),
      ← NatIso.naturality_1 η s, Functor.comp_map]
    infer_instance
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

end Resolutions

/-! ### Faithfulness -/

section Faithfulness

variable {E : ExactStructure C} (hF : E.IsFrobenius)
include hF

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
        resHom hF.enoughInjectives M ≫
            ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map φ) =
          (HomotopyCategory.Bounded.toPlus C).map
            ((HomotopyCategory.Bounded.singleFunctor C 0).map f) ≫
            resHom hF.enoughInjectives N := by
  let hE := hF.enoughInjectives
  obtain ⟨aK, bK, _, _⟩ := (CochainComplex.bounded_iff C K.obj).1 K.property
  let K' := (HomotopyCategory.Bounded.quotient C).obj K
  have hKinj : E.injectivePlus ((HomotopyCategory.Bounded.toPlus C).obj K') :=
    (E.injectivePlus_iff _).2 ((E.plusInjective_iff _).2
      ⟨K.obj, ⟨aK, inferInstance⟩, fun n ↦ (hF.injective_iff_projective _).2 (hK n),
        ⟨eqToIso (HomotopyCategory.Bounded.quotient_obj_obj C K)⟩⟩)
  -- In `D⁺(E)`, the induced map of resolutions factors through `K`.
  let η := BoundedDerivedCategory.QCompToPlusIso E
  obtain ⟨u, hu⟩ := ((E.injectivePlus_le_rightOrthogonal _ hKinj).map_bijective_of_isTriangulated
      (PlusDerivedCategory.Q E) _).2
    (inv ((PlusDerivedCategory.Q E).map (resHom hE M)) ≫ η.inv.app _ ≫
      (BoundedDerivedCategory.toPlus E).map a ≫ η.hom.app K')
  have hN := (E.injectivePlus_le_rightOrthogonal _
    (injectivePlus_resPlus hE N)).map_bijective_of_isTriangulated (PlusDerivedCategory.Q E)
  obtain ⟨v, hv⟩ := (hN _).2
    (η.inv.app K' ≫ (BoundedDerivedCategory.toPlus E).map g ≫ η.hom.app _ ≫
      (PlusDerivedCategory.Q E).map (resHom hE N))
  have hcomp : resHom hE M ≫ u ≫ v = (HomotopyCategory.Bounded.toPlus C).map
      ((HomotopyCategory.Bounded.singleFunctor C 0).map f) ≫ resHom hE N := by
    apply (hN _).1
    rw [Functor.map_comp _ (resHom hE M), Functor.map_comp _ u v, hu, hv,
      Functor.map_comp _ _ (resHom hE N)]
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

/-- **Faithfulness in the Keller–Vossieck theorem**: a morphism of a Frobenius exact category which
vanishes in the singularity category factors through a projective object. -/
theorem mem_projectiveStableIdeal_of_singleToSingularity_map_eq_zero {M N : C} (f : M ⟶ N)
    (hf : E.singleToSingularity.map f = 0) : f ∈ E.projectiveStableIdeal.hom M N := by
  let hE := hF.enoughInjectives
  rw [singleToSingularity_eq] at hf
  -- In `Dᵇ(E)`, `f` factors through an object of `Kᵇ(proj E)`.
  obtain ⟨W, hW, a, g, hag⟩ := (ObjectProperty.factorsThrough_iff _ _).1
    ((ObjectProperty.TrWLocalization.map_eq_zero_iff_factorsThrough E.boundedProjective
      (SingularityCategory.Q E)
      ((BoundedDerivedCategory.Q E).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f))).1
        hf)
  obtain ⟨K, hK, ⟨e⟩⟩ := (E.boundedProjective_iff W).1 hW
  obtain ⟨φ, hnull, hφ⟩ := exists_isEventuallyNullHomotopic hF f K hK (a ≫ e.hom) (e.inv ≫ g)
    (by simpa using hag.symm)
  rw [mem_projectiveStableIdeal_iff, ← cyclesMap_zero_eq hE f φ hφ]
  exact (((hE.stalkTailData M).factorsThrough_cyclesMap_zero_of_isEventuallyNullHomotopic
    (hE.stalkTailData N) φ
    (fun k ↦ (hF.injective_iff_projective _).1 (hE.isInjective_stalkResolution_X M k))
      hnull).comp_right _).comp_left _

/-- **The kernel of `C ⥤ D_sg(E)`** for a Frobenius exact structure: a morphism vanishes in the
singularity category exactly when it factors through a projective object. -/
theorem kerIdeal_singleToSingularity :
    E.singleToSingularity.kerIdeal = E.projectiveStableIdeal :=
  le_antisymm (fun _ _ f hf ↦ hF.mem_projectiveStableIdeal_of_singleToSingularity_map_eq_zero f
    ((Functor.mem_kerIdeal_hom _).1 hf)) E.projectiveStableIdeal_le_kerIdeal_singleToSingularity

/-- **The functor `stable(E) ⥤ D_sg(E)` is faithful** for a Frobenius exact structure. -/
theorem faithful_stableToSingularity : E.stableToSingularity.Faithful := by
  rw [stableToSingularity_eq, MorphismIdeal.faithful_lift_iff, hF.kerIdeal_singleToSingularity]

end Faithfulness

/-! ### Fullness -/

section StalkTruncation

variable {E : ExactStructure C}

/-- The terms of a complex mapping to a complex of injectives by isomorphisms are projective. -/
private theorem isProjective_X_of_isIso (hF : E.IsFrobenius) {T I : CochainComplex C ℤ} (j : T ⟶ I)
    (hI : ∀ l, E.isInjective (I.X l)) (l : ℤ) [IsIso (j.f l)] : E.isProjective (T.X l) :=
  E.isProjective.prop_of_iso (asIso (j.f l)).symm ((hF.injective_iff_projective _).1 (hI l))

/-- **The truncated resolution of an object.** The injective resolution `I_M` of `M`, cut off above
degree `k + 1`, is a bounded complex `T` under `M` with acyclic mapping cone, whose terms below
`k + 1` are projective and whose top term is the object of cycles `Zᵏ⁺¹` of `I_M`. -/
private structure StalkTruncation (hF : E.IsFrobenius) (M : C) (k : ℕ) where
  T : CochainComplex C ℤ
  j : T ⟶ hF.enoughInjectives.stalkResolution M
  r' : (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ T
  θ : T.X ((k + 1 : ℕ) : ℤ) ≅ (hF.enoughInjectives.stalkTailData M).Z (k + 1)
  bounded : CochainComplex.bounded C T
  isStrictlyLE : T.IsStrictlyLE ((k + 1 : ℕ) : ℤ)
  r'_comp_j : r' ≫ j = hF.enoughInjectives.stalkResolutionι M
  θ_hom_comp_i : θ.hom ≫ (hF.enoughInjectives.stalkTailData M).i (k + 1) = j.f ((k + 1 : ℕ) : ℤ)
  acyclic : E.acyclic (CochainComplex.mappingCone r')
  isProjective_X : ∀ l < ((k + 1 : ℕ) : ℤ), E.isProjective (T.X l)

attribute [instance] StalkTruncation.isStrictlyLE

private theorem nonempty_stalkTruncation (hF : E.IsFrobenius) (M : C) (k : ℕ) :
    Nonempty (StalkTruncation hF M k) := by
  let hE := hF.enoughInjectives
  have : CochainComplex.IsStrictlyLE ((HomologicalComplex.single C (.up ℤ) 0).obj M) (k : ℤ) :=
    CochainComplex.isStrictlyLE_of_le _ 0 (k : ℤ) (by lia)
  obtain ⟨T, j, r', hr'j, hiso, hmono, hTle, hge, hcone⟩ :=
    exists_truncation_of_acyclic_mappingCone (hE.stalkResolutionι M)
      (hE.acyclic_mappingCone_stalkResolutionι M) (k : ℤ)
  have : T.IsStrictlyLE ((k + 1 : ℕ) : ℤ) := hTle
  have := hiso k le_rfl
  have : Mono (j.f ((k + 1 : ℕ) : ℤ)) := hmono
  -- `T` vanishes above degree `k + 1`, so `jᵏ⁺¹` lands in the cycles.
  obtain ⟨θ, hθ⟩ := (hE.stalkTailData M).exists_iso_Z k j (by
    rw [← cancel_mono ((hE.stalkTailData M).i (k + 1 + 1)), Category.assoc, TailData.fac,
      zero_comp, j.comm, (T.isZero_of_isStrictlyLE ((k + 1 : ℕ) : ℤ) _ (by lia)).eq_of_tgt
        (T.d _ _) 0, zero_comp])
  refine ⟨⟨T, j, r', θ, (CochainComplex.bounded_iff C T).2 ⟨_, _, hge 0 inferInstance, hTle⟩,
    hTle, hr'j, hθ, hcone, fun l hl ↦ ?_⟩⟩
  have := hiso l (by lia)
  exact isProjective_X_of_isIso hF j (hE.isInjective_stalkResolution_X M) l

/-- The class of the truncated resolution `T` in `Kᵇ(C)`. -/
private abbrev StalkTruncation.obj {hF : E.IsFrobenius} {M : C} {k : ℕ}
    (τ : StalkTruncation hF M k) : HomotopyCategory.Bounded C :=
  HomotopyCategory.Bounded.mk τ.T τ.bounded

/-- The inclusion of the top term of `T`, placed in degree `k + 1`, into `T` in `Kᵇ(C)`. -/
private noncomputable abbrev StalkTruncation.sT {hF : E.IsFrobenius} {M : C} {k : ℕ}
    (τ : StalkTruncation hF M k) :
    HomotopyCategory.Bounded.mk _
      (CochainComplex.bounded_single ((k + 1 : ℕ) : ℤ) (τ.T.X ((k + 1 : ℕ) : ℤ))) ⟶ τ.obj :=
  mkMap (τ.T.ιTop _)

/-- The quasi-isomorphism from `M` in degree zero to the truncated resolution `T` in `Kᵇ(C)`. -/
private noncomputable abbrev StalkTruncation.sR {hF : E.IsFrobenius} {M : C} {k : ℕ}
    (τ : StalkTruncation hF M k) :
    (HomotopyCategory.Bounded.singleFunctor C 0).obj M ⟶ τ.obj :=
  (singleFunctorObjIsoMk 0 M).hom ≫ mkMap τ.r'

private instance {hF : E.IsFrobenius} {M : C} {k : ℕ} (τ : StalkTruncation hF M k) :
    IsIso ((BoundedDerivedCategory.Q E).map τ.sR) :=
  Localization.inverts (BoundedDerivedCategory.Q E) E.acyclicBounded.trW τ.sR
    (MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
      (E.acyclicBounded_trW_homMk_quotient_map
        (X := HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single 0 M))
        (Y := τ.obj) τ.r' τ.acyclic))

/-- The inclusion of the top term of `T` into `M` in `Dᵇ(E)`, inverted in `D_sg(E)`. -/
private noncomputable abbrev StalkTruncation.δ {hF : E.IsFrobenius} {M : C} {k : ℕ}
    (τ : StalkTruncation hF M k) :
    (BoundedDerivedCategory.Q E).obj (HomotopyCategory.Bounded.mk _
        (CochainComplex.bounded_single ((k + 1 : ℕ) : ℤ) (τ.T.X ((k + 1 : ℕ) : ℤ)))) ⟶
      (BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj M) :=
  (BoundedDerivedCategory.Q E).map τ.sT ≫ inv ((BoundedDerivedCategory.Q E).map τ.sR)

private instance {hF : E.IsFrobenius} {M : C} {k : ℕ} (τ : StalkTruncation hF M k) :
    IsIso ((SingularityCategory.Q E).map τ.δ) := by
  have : IsIso ((SingularityCategory.Q E).map ((BoundedDerivedCategory.Q E).map τ.sT)) :=
    Localization.inverts _ _ _
      (boundedProjective_trW_Q_map_ιTop τ.T _ τ.bounded τ.isProjective_X)
  simp only [StalkTruncation.δ, Functor.map_comp, Functor.map_inv]
  infer_instance

/-- Every map from the top term of a truncated resolution of `M`, placed in degree `k + 1`, to the
injective resolution of `N` factors as `ιTop ≫ j ≫ Φ` through a map of resolutions `Φ`. -/
private theorem StalkTruncation.exists_ιTop_comp_eq {hF : E.IsFrobenius} {M N : C} {k : ℕ}
    (τ : StalkTruncation hF M k)
    (g : (HomologicalComplex.single C (.up ℤ) ((k + 1 : ℕ) : ℤ)).obj
        (τ.T.X ((k + 1 : ℕ) : ℤ)) ⟶ hF.enoughInjectives.stalkResolution N) :
    ∃ Φ : hF.enoughInjectives.stalkResolution M ⟶ hF.enoughInjectives.stalkResolution N,
      τ.T.ιTop _ ≫ τ.j ≫ Φ = g := by
  let hE := hF.enoughInjectives
  let tM := hE.stalkTailData M
  let tN := hE.stalkTailData N
  -- The degree `k + 1` component of `g` lands in the cycles `Z'ᵏ⁺¹` of the resolution of `N`.
  let y : τ.T.X ((k + 1 : ℕ) : ℤ) ⟶ (hE.stalkResolution N).X ((k + 1 : ℕ) : ℤ) :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) ((k + 1 : ℕ) : ℤ) (τ.T.X ((k + 1 : ℕ) : ℤ))).inv ≫
      g.f ((k + 1 : ℕ) : ℤ)
  have hy : y ≫ tN.p (k + 1) = 0 := by
    rw [← cancel_mono (tN.i (k + 1 + 1)), Category.assoc, Category.assoc, tN.fac, zero_comp]
    refine (congrArg (fun x ↦ _ ≫ x) (g.comm _ _)).trans ?_
    rw [(HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)).eq_of_tgt
      (((HomologicalComplex.single C (.up ℤ) ((k + 1 : ℕ) : ℤ)).obj
        (τ.T.X ((k + 1 : ℕ) : ℤ))).d _ _) 0, zero_comp, comp_zero]
  -- The map of cycles `Zᵏ⁺¹ ⟶ Z'ᵏ⁺¹` lifts to a map of resolutions.
  obtain ⟨Φ, hΦ⟩ := tM.exists_hom_cyclesMap_eq tN (k + 1)
    (fun l _ ↦ (hF.injective_iff_projective _).1 (hE.isInjective_stalkResolution_X M l))
    (fun l _ ↦ hE.isInjective_stalkResolution_X N l) (τ.θ.inv ≫ tN.liftZ (k + 1) y hy)
  refine ⟨Φ, ?_⟩
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, τ.T.ιTop_f]
  refine (cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) ((k + 1 : ℕ) : ℤ)
    (τ.T.X ((k + 1 : ℕ) : ℤ))).inv).1 ?_
  rw [Iso.inv_hom_id_assoc, ← τ.θ_hom_comp_i, Category.assoc, ← TailData.cyclesMap_i, hΦ]
  simp only [Category.assoc, TailData.liftZ_i, Iso.hom_inv_id_assoc, y]

/-- A map of resolutions `Φ : I_M ⟶ I_N`, restricted along a truncated resolution of `M`, extends
in `K⁺(C)` the image of its map of cycles in degree zero. -/
private theorem StalkTruncation.toPlus_map_comp_resHom {hF : E.IsFrobenius} {M N : C} {k : ℕ}
    (τ : StalkTruncation hF M k)
    (Φ : hF.enoughInjectives.stalkResolution M ⟶ hF.enoughInjectives.stalkResolution N)
    (f : M ⟶ N)
    (hf : (hF.enoughInjectives.stalkTailDataZZeroIso M).inv ≫
      (hF.enoughInjectives.stalkTailData M).cyclesMap (hF.enoughInjectives.stalkTailData N) Φ 0 ≫
        (hF.enoughInjectives.stalkTailDataZZeroIso N).hom = f) :
    (HomotopyCategory.Bounded.toPlus C).map ((HomotopyCategory.Bounded.singleFunctor C 0).map f) ≫
        resHom hF.enoughInjectives N =
      (HomotopyCategory.Bounded.toPlus C).map τ.sR ≫
        (ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map (τ.j ≫ Φ)) :
          (HomotopyCategory.Bounded.toPlus C).obj τ.obj ⟶ resPlus hF.enoughInjectives N) := by
  have h := hF.enoughInjectives.single_map_comp_stalkResolutionι Φ
  rw [hf] at h
  -- The right-hand side is `resHom ≫ Φ`, since `r' ≫ j` is the resolution map.
  have hR : (HomotopyCategory.Bounded.toPlus C).map τ.sR ≫
      (ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map (τ.j ≫ Φ)) :
        (HomotopyCategory.Bounded.toPlus C).obj τ.obj ⟶ resPlus hF.enoughInjectives N) =
      resHom hF.enoughInjectives M ≫
        ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map Φ) := by
    simp only [resHom, Functor.map_comp, Category.assoc]
    congr 1
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.ιOfLE_map, ← Functor.map_comp]
    rw [reassoc_of% τ.r'_comp_j]
  rw [hR, toPlus_map_comp_resHom_eq_iff, h]

end StalkTruncation

section Fullness

variable {E : ExactStructure C} (hF : E.IsFrobenius)
include hF

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

/-- Given maps `δ k` to `X₀` from objects placed in degree `k + 1`, every map from `X₀` to an
object of `Kᵇ(proj E)` is killed by some `δ k`. -/
private theorem exists_comp_eq_zero_of_boundedProjective {X₀ : E.BoundedDerivedCategory}
    (A : ℕ → C) (δ : ∀ k : ℕ, (BoundedDerivedCategory.Q E).obj (HomotopyCategory.Bounded.mk _
      (CochainComplex.bounded_single ((k + 1 : ℕ) : ℤ) (A k))) ⟶ X₀)
    (K : E.BoundedDerivedCategory) (hK : E.boundedProjective K) (a : X₀ ⟶ K) :
    ∃ k, δ k ≫ a = 0 := by
  -- `K` vanishes above some degree `b`; take `k + 1 > b`.
  obtain ⟨K', hK', ⟨e⟩⟩ := (E.boundedProjective_iff K).1 hK
  obtain ⟨_, b, _, _⟩ := (CochainComplex.bounded_iff C K'.obj).1 K'.property
  refine ⟨b.toNat, ?_⟩
  rw [← cancel_mono e.hom, zero_comp, Category.assoc]
  exact eq_zero_of_isStrictlyLE hF (by lia : b < ((b.toNat + 1 : ℕ) : ℤ)) _ K' hK' _

/-- **Fullness in the Keller–Vossieck theorem**: every morphism between objects of a Frobenius exact
category in the singularity category comes from a morphism of the category. -/
theorem singleToSingularity_map_surjective (M N : C) :
    Function.Surjective (E.singleToSingularity.map : (M ⟶ N) → _) := by
  rw [singleToSingularity_eq]
  intro α
  let hE := hF.enoughInjectives
  -- For each `k`, truncate the resolution of `M` above degree `k + 1`. A map from `M` to a bounded
  -- complex of projectives `K` is killed by `(τ k).δ` once `k` lies beyond `K`.
  let τ (k : ℕ) : StalkTruncation hF M k := Classical.choice (nonempty_stalkTruncation hF M k)
  obtain ⟨k, h, hh⟩ := ObjectProperty.TrWLocalization.exists_map_comp_eq_map E.boundedProjective
    (SingularityCategory.Q E) (fun k ↦ (τ k).δ)
    (exists_comp_eq_zero_of_boundedProjective hF _ (fun k ↦ (τ k).δ)) α
  -- In `D⁺(E)`, `h` is a map from the top term to the resolution of `N`, which comes from a map
  -- of resolutions `Φ`.
  let η := BoundedDerivedCategory.QCompToPlusIso E
  obtain ⟨g, hg⟩ := ((E.injectivePlus_le_rightOrthogonal _
      (injectivePlus_resPlus hE N)).map_bijective_of_isTriangulated (PlusDerivedCategory.Q E) _).2
    (η.inv.app _ ≫ (BoundedDerivedCategory.toPlus E).map h ≫ η.hom.app _ ≫
      (PlusDerivedCategory.Q E).map (resHom hE N))
  obtain ⟨g', hg'⟩ := (_root_.HomotopyCategory.quotient C (.up ℤ)).map_surjective g.hom
  obtain ⟨Φ, hΦ⟩ := (τ k).exists_ιTop_comp_eq g'
  refine ⟨(hE.stalkTailDataZZeroIso M).inv ≫
    (hE.stalkTailData M).cyclesMap (hE.stalkTailData N) Φ 0 ≫ (hE.stalkTailDataZZeroIso N).hom, ?_⟩
  have hgJ : (HomotopyCategory.Bounded.toPlus C).map (τ k).sT ≫
      ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map ((τ k).j ≫ Φ)) =
        g := by
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.ιOfLE_map, ← Functor.map_comp, hΦ, hg']
  have key := Q_map_comp_inv_comp_eq hE (τ k).sR (τ k).sT _ (resHom hE N) _
    ((τ k).toPlus_map_comp_resHom Φ _ rfl) h (by rw [hgJ, hg])
  rw [← cancel_epi ((SingularityCategory.Q E).map (τ k).δ), hh, ← key]
  simp only [StalkTruncation.δ, Functor.comp_map, Functor.map_comp, Category.assoc]

/-- The functor `C ⥤ D_sg(E)` is full for a Frobenius exact structure. -/
theorem full_singleToSingularity : E.singleToSingularity.Full :=
  ⟨hF.singleToSingularity_map_surjective _ _⟩

/-- **The functor `stable(E) ⥤ D_sg(E)` is full** for a Frobenius exact structure. -/
theorem full_stableToSingularity : E.stableToSingularity.Full := by
  have := hF.full_singleToSingularity
  rw [stableToSingularity_eq]
  infer_instance

/-- **The functor `stable(E) ⥤ D_sg(E)` is fully faithful** for a Frobenius exact structure. -/
noncomputable def fullyFaithfulStableToSingularity : E.stableToSingularity.FullyFaithful :=
  have := hF.full_stableToSingularity
  have := hF.faithful_stableToSingularity
  .ofFullyFaithful _

end Fullness

/-! ### Essential surjectivity and the equivalence -/

section SingularitySingle

/-- The object `X` placed in degree `a`, in the singularity category. -/
private noncomputable abbrev sg (E : ExactStructure C) (a : ℤ) (X : C) : E.SingularityCategory :=
  (SingularityCategory.Q E).obj ((BoundedDerivedCategory.Q E).obj
    ((HomotopyCategory.Bounded.singleFunctor C a).obj X))

variable {E : ExactStructure C}

/-- Objects isomorphic in the stable category are isomorphic in the singularity category in every
degree. -/
private noncomputable def sgIsoOfStableIso (a : ℤ) {X Y : C}
    (e : E.projectiveStableFunctor.obj X ≅ E.projectiveStableFunctor.obj Y) :
    sg E a X ≅ sg E a Y :=
  -- The single functors `C ⥤ D_sg(E)`, with their shift isomorphisms.
  let S := (HomotopyCategory.Bounded.singleFunctors C).postcomp
    (BoundedDerivedCategory.Q E ⋙ SingularityCategory.Q E)
  (shiftEquiv E.SingularityCategory a).fullyFaithfulFunctor.preimageIso
    ((S.shiftIso a 0 a (add_zero a)).app X ≪≫ (E.stableToSingularityObjIso X).symm ≪≫
      E.stableToSingularity.mapIso e ≪≫ E.stableToSingularityObjIso Y ≪≫
        ((S.shiftIso a 0 a (add_zero a)).app Y).symm)

/-- Let `r : L ⟶ T` be a map of bounded complexes with acyclic mapping cone, where `T` vanishes
above degree `n` and its terms below `n` are projective. Then `L` is isomorphic in the singularity
category to the top term `Tⁿ` placed in degree `n`. -/
private noncomputable def sgIsoOfTruncation {L T : CochainComplex C ℤ}
    (hL : CochainComplex.bounded C L) (hT : CochainComplex.bounded C T) (n : ℤ)
    [T.IsStrictlyLE n] (hP : ∀ l < n, E.isProjective (T.X l)) (r : L ⟶ T)
    (hr : E.acyclic (CochainComplex.mappingCone r)) :
    (SingularityCategory.Q E).obj
      ((BoundedDerivedCategory.Q E).obj (HomotopyCategory.Bounded.mk L hL)) ≅ sg E n (T.X n) :=
  have : IsIso ((SingularityCategory.Q E).map ((BoundedDerivedCategory.Q E).map
      (mkMap (T.ιTop n) : HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n (T.X n)) ⟶
        HomotopyCategory.Bounded.mk T hT))) :=
    Localization.inverts _ E.boundedProjective.trW _
      (boundedProjective_trW_Q_map_ιTop T n hT hP)
  have : IsIso ((BoundedDerivedCategory.Q E).map
      (mkMap r : HomotopyCategory.Bounded.mk L hL ⟶ HomotopyCategory.Bounded.mk T hT)) :=
    Localization.inverts _ E.acyclicBounded.trW _ (E.acyclicBounded_trW_homMk_quotient_map
      (X := HomotopyCategory.Bounded.mk L hL) (Y := HomotopyCategory.Bounded.mk T hT) r hr)
  (SingularityCategory.Q E).mapIso (asIso ((BoundedDerivedCategory.Q E).map
      (mkMap r : HomotopyCategory.Bounded.mk L hL ⟶ HomotopyCategory.Bounded.mk T hT))) ≪≫
    (asIso ((SingularityCategory.Q E).map ((BoundedDerivedCategory.Q E).map
      (mkMap (T.ιTop n) : HomotopyCategory.Bounded.mk _ (CochainComplex.bounded_single n (T.X n)) ⟶
        HomotopyCategory.Bounded.mk T hT)))).symm ≪≫
      (BoundedDerivedCategory.Q E ⋙ SingularityCategory.Q E).mapIso
        (singleFunctorObjIsoMk n (T.X n)).symm

end SingularitySingle

section EssentialSurjectivity

variable {E : ExactStructure C} (hF : E.IsFrobenius)
include hF

/-- The object of cycles `Zᵏ⁺¹` of the injective resolution of `M`, placed in degree `k + 1`, is
isomorphic to `M` in the singularity category. -/
private theorem nonempty_sg_Z_iso (M : C) (k : ℕ) :
    Nonempty (sg E ((k + 1 : ℕ) : ℤ) ((hF.enoughInjectives.stalkTailData M).Z (k + 1)) ≅
      sg E 0 M) := by
  obtain ⟨τ⟩ := nonempty_stalkTruncation hF M k
  exact ⟨(BoundedDerivedCategory.Q E ⋙ SingularityCategory.Q E).mapIso
    ((HomotopyCategory.Bounded.singleFunctor C _).mapIso τ.θ.symm) ≪≫
      (sgIsoOfTruncation (CochainComplex.bounded_single 0 M) τ.bounded _ τ.isProjective_X
        τ.r' τ.acyclic).symm ≪≫
        (BoundedDerivedCategory.Q E ⋙ SingularityCategory.Q E).mapIso
          (singleFunctorObjIsoMk 0 M).symm⟩

/-- Every object is, in the stable category, isomorphic to the object of cycles `Zᵗ` of the
injective resolution of some object. -/
private theorem exists_Z_iso (t : ℕ) (Z : C) : ∃ M : C,
    Nonempty (E.projectiveStableFunctor.obj ((hF.enoughInjectives.stalkTailData M).Z t) ≅
      E.projectiveStableFunctor.obj Z) := by
  -- Take `t`-fold stable loops: `Zᵗ⁺¹` is the suspension of `Zᵗ`.
  induction t generalizing Z with
  | zero =>
    exact ⟨Z, ⟨E.projectiveStableFunctor.mapIso (hF.enoughInjectives.stalkTailDataZZeroIso Z)⟩⟩
  | succ t ih =>
    obtain ⟨M, ⟨e⟩⟩ := ih (hF.enoughProjectives.loopObj Z)
    have e' := hF.projectiveStableIsoSuspensionObj
      ((hF.enoughInjectives.stalkTailData M).injectivePresentation t
        (hF.enoughInjectives.isInjective_stalkResolution_X M t))
    rw [TailData.injectivePresentation_K] at e'
    exact ⟨M, ⟨e' ≪≫ eqToIso (hF.stableSuspension_obj_projectiveStableFunctor_obj _).symm ≪≫
      hF.stableSuspension.mapIso (e ≪≫ eqToIso
        (hF.enoughProjectives.stableLoop_obj_projectiveStableFunctor_obj Z).symm) ≪≫
        hF.stableLoopCompStableSuspensionIso.app _⟩⟩

/-- In the singularity category, a bounded complex is isomorphic to an object placed in a positive
degree. -/
private theorem exists_sg_iso_of_bounded (L : CochainComplex C ℤ)
    (hL : CochainComplex.bounded C L) : ∃ (k : ℕ) (Z : C),
      Nonempty ((SingularityCategory.Q E).obj ((BoundedDerivedCategory.Q E).obj
        (HomotopyCategory.Bounded.mk L hL)) ≅
        sg E ((k + 1 : ℕ) : ℤ) Z) := by
  obtain ⟨a, b, _, _⟩ := (CochainComplex.bounded_iff C L).1 hL
  have : L.IsStrictlyLE (b.toNat : ℤ) := L.isStrictlyLE_of_le b b.toNat (Int.self_le_toNat b)
  obtain ⟨I, α, hIa, hI, hα⟩ := hF.enoughInjectives.exists_injectiveResolution L a
  obtain ⟨T, j, r', -, hiso, -, hTle, hge, hcone⟩ :=
    exists_truncation_of_acyclic_mappingCone α hα (b.toNat : ℤ)
  have : T.IsStrictlyLE ((b.toNat + 1 : ℕ) : ℤ) := hTle
  exact ⟨b.toNat, T.X ((b.toNat + 1 : ℕ) : ℤ), ⟨sgIsoOfTruncation hL
    ((CochainComplex.bounded_iff C T).2 ⟨_, _, hge a hIa, hTle⟩) _ (fun l hl ↦ by
      have := hiso l (by lia)
      exact isProjective_X_of_isIso hF j hI l) r' hcone⟩⟩

/-- **Essential surjectivity in the Keller–Vossieck theorem**: every object of the singularity
category of a Frobenius exact category is isomorphic to an object of the category placed in degree
zero. -/
theorem essSurj_singleToSingularity : E.singleToSingularity.EssSurj where
  mem_essImage Y := by
    have := Localization.essSurj (SingularityCategory.Q E) E.boundedProjective.trW
    have := Localization.essSurj (BoundedDerivedCategory.Q E) E.acyclicBounded.trW
    obtain ⟨⟨X₀, hX₀⟩, ⟨e₀⟩⟩ : ∃ X, Nonempty
        ((SingularityCategory.Q E).obj ((BoundedDerivedCategory.Q E).obj X) ≅ Y) :=
      ⟨_, ⟨(SingularityCategory.Q E).mapIso ((BoundedDerivedCategory.Q E).objObjPreimageIso _) ≪≫
        (SingularityCategory.Q E).objObjPreimageIso Y⟩⟩
    obtain ⟨L, rfl⟩ := _root_.HomotopyCategory.quotient_obj_surjective X₀
    have hL : CochainComplex.bounded C L := (HomotopyCategory.bounded_quotient_obj_iff _).1 hX₀
    obtain ⟨k, Z, ⟨e⟩⟩ := exists_sg_iso_of_bounded hF L hL
    obtain ⟨M, ⟨e'⟩⟩ := exists_Z_iso hF (k + 1) Z
    obtain ⟨e''⟩ := nonempty_sg_Z_iso hF M k
    exact ⟨M, ⟨eqToIso (E.singleToSingularity_obj M) ≪≫ e''.symm ≪≫ sgIsoOfStableIso _ e' ≪≫
      e.symm ≪≫ e₀⟩⟩

/-- The functor `stable(E) ⥤ D_sg(E)` is essentially surjective for a Frobenius exact
structure. -/
theorem essSurj_stableToSingularity : E.stableToSingularity.EssSurj := by
  have := hF.essSurj_singleToSingularity
  rw [stableToSingularity_eq]
  infer_instance

/-- **The Keller–Vossieck theorem**: for a Frobenius exact category, the functor
`stable(E) ⥤ D_sg(E)` placing an object in degree zero is an equivalence. -/
theorem isEquivalence_stableToSingularity : E.stableToSingularity.IsEquivalence :=
  { faithful := hF.faithful_stableToSingularity
    full := hF.full_stableToSingularity
    essSurj := hF.essSurj_stableToSingularity }

end EssentialSurjectivity

end TauCeti.ExactStructure.IsFrobenius
