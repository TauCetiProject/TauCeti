/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Shift
public import TauCeti.CategoryTheory.Exact.Stable.Triangulated
public import TauCeti.CategoryTheory.Localization.Triangulated

/-!
# The homotopy category of curved duplexes is triangulated

Let `C` be an `R`-linear additive category and `w : R`. The componentwise split exact structure
on curved duplexes of curvature `w` is Frobenius, and its stable category is identified with the
homotopy category `CurvedDuplex.HomotopyCategory C w` by
`ExactStructure.curvedDuplexSplitStableToHomotopy`, compatibly with the shifts by `ℤ` (stable
suspension on one side, the parity shift on the other). This file transports Happel's
triangulation of the stable category along this equivalence, which makes the homotopy category of
curved duplexes a triangulated category whose shift by `1` is the parity shift.

The distinguished triangles are described concretely. Let `X₁ ⟶ X₂ ⟶ X₃` be a short complex of
curved duplexes which splits in both components. Since the disk sum `diskSum X₁` is contractible,
the inflation `X₁ ⟶ diskSum X₁` extends along `X₁ ⟶ X₂` to a map `a : X₂ ⟶ diskSum X₁`, which
induces `δ : X₃ ⟶ X₁[1]` on cokernels. Then

`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]`

with third map the homotopy class of `δ` is distinguished, and every distinguished triangle is
isomorphic to one of these.

## Main definitions

* `TauCeti.CurvedDuplex.HomotopyCategory.instPretriangulated`: the pretriangulated structure on
  the homotopy category of curved duplexes.

## Main results

* `TauCeti.CurvedDuplex.HomotopyCategory.instIsTriangulated`: the homotopy category of curved
  duplexes is triangulated.
* `TauCeti.ExactStructure.curvedDuplexSplitStableToHomotopy_isTriangulated`: the comparison from
  the componentwise split stable category is a triangle functor.
* `TauCeti.CurvedDuplex.HomotopyCategory.mk_distinguished_of_conflation`: componentwise split
  short complexes give distinguished triangles.
* `TauCeti.CurvedDuplex.HomotopyCategory.mem_distTriang_iff`: every distinguished triangle is
  isomorphic to the triangle of a componentwise split short complex.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, Theorem 2.6: the stable category of a Frobenius category is
  triangulated.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1, for complexes with the componentwise split exact structure.
* I. Frenkel, M. Khovanov, O. Schiffmann, *Homological realization of Nakajima varieties and Weyl
  group actions*, Compos. Math. **141** (2005), 1479–1503, Sections 2–3, for curved duplexes and
  their triangulated homotopy category.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CurvedDuplex
  ExactStructure

universe w' v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {R : Type w'} [Semiring R] [Linear R C] {w : R}

namespace CurvedDuplex.HomotopyCategory

variable (C w)

/-- The homotopy category of curved duplexes is pretriangulated: its distinguished triangles are
the images of Happel's distinguished triangles under the equivalence with the componentwise split
stable category. -/
noncomputable instance instPretriangulated : Pretriangulated (HomotopyCategory C w) :=
  letI := (curvedDuplex_split_isFrobenius C w).stableHasShift
  letI := (curvedDuplex_split_isFrobenius C w).stableShiftFunctor_additive
  letI := (curvedDuplex_split_isFrobenius C w).stablePretriangulated
  letI := curvedDuplexSplitStableToHomotopyCommShift C w
  Triangulated.Localization.pretriangulated (curvedDuplexSplitStableToHomotopy C w)
    (MorphismProperty.isomorphisms _)

end CurvedDuplex.HomotopyCategory

namespace ExactStructure

variable (C w)

/-- The comparison from the componentwise split stable category of curved duplexes to their
homotopy category is a triangle functor. -/
theorem curvedDuplexSplitStableToHomotopy_isTriangulated :
    letI := (curvedDuplex_split_isFrobenius C w).stableHasShift
    letI := (curvedDuplex_split_isFrobenius C w).stableShiftFunctor_additive
    letI := (curvedDuplex_split_isFrobenius C w).stablePretriangulated
    letI := curvedDuplexSplitStableToHomotopyCommShift C w
    (curvedDuplexSplitStableToHomotopy C w).IsTriangulated :=
  letI := (curvedDuplex_split_isFrobenius C w).stableHasShift
  letI := (curvedDuplex_split_isFrobenius C w).stableShiftFunctor_additive
  letI := (curvedDuplex_split_isFrobenius C w).stablePretriangulated
  letI := curvedDuplexSplitStableToHomotopyCommShift C w
  Triangulated.Localization.isTriangulated_functor _ (MorphismProperty.isomorphisms _)

end ExactStructure

namespace CurvedDuplex.HomotopyCategory

variable (C w) in
/-- **The homotopy category of curved duplexes is triangulated**, with the shift by `1` given by
the parity shift. -/
instance instIsTriangulated : IsTriangulated (HomotopyCategory C w) :=
  letI := (curvedDuplex_split_isFrobenius C w).stableHasShift
  letI := (curvedDuplex_split_isFrobenius C w).stableShiftFunctor_additive
  letI := (curvedDuplex_split_isFrobenius C w).stablePretriangulated
  letI := curvedDuplexSplitStableToHomotopyCommShift C w
  haveI := (curvedDuplex_split_isFrobenius C w).stableIsTriangulated
  haveI := curvedDuplexSplitStableToHomotopy_isTriangulated C w
  Triangulated.Localization.isTriangulated (curvedDuplexSplitStableToHomotopy C w)
    (MorphismProperty.isomorphisms _)

variable {S : ShortComplex (CurvedDuplex C w)}

/-- The image of Happel's standard triangle of a componentwise split conflation is isomorphic to
the triangle of homotopy classes whose third map is induced by an extension to the disk sum. -/
private noncomputable def mapStableConflationTriangleIso
    (hS : ((split C).curvedDuplex w).Conflation S) (a : S.X₂ ⟶ diskSum S.X₁)
    (δ : S.X₃ ⟶ (parityShift C w).obj S.X₁) (ha : S.f ≫ a = toDiskSum S.X₁)
    (hδ : S.g ≫ δ = a ≫ diskSumToParityShift S.X₁) :
    letI := (curvedDuplex_split_isFrobenius C w).stableHasShift
    letI := curvedDuplexSplitStableToHomotopyCommShift C w
    Triangle.mk ((nullHomotopic C w).quotientFunctor.map S.f)
        ((nullHomotopic C w).quotientFunctor.map S.g)
        ((nullHomotopic C w).quotientFunctor.map δ ≫
          (parityShiftCompQuotientFunctorIso C w).hom.app S.X₁) ≅
      (curvedDuplexSplitStableToHomotopy C w).mapTriangle.obj
        ((curvedDuplex_split_isFrobenius C w).stableConflationTriangle S hS) := by
  letI := (curvedDuplex_split_isFrobenius C w).stableHasShift
  letI := curvedDuplexSplitStableToHomotopyCommShift C w
  -- The image of `δ` is the image of the connecting map, read through the disk-sum presentation.
  have key : (curvedDuplexSplitStableToHomotopy C w).map
      (((split C).curvedDuplex w).projectiveStableFunctor.map δ) =
      (curvedDuplexSplitStableToHomotopy C w).map
        (((split C).curvedDuplex w).projectiveStableFunctor.map
          ((curvedDuplex_split_isFrobenius C w).connectingMap hS) ≫
        ((curvedDuplex_split_isFrobenius C w).projectiveStableIsoSuspensionObj
          (curvedDuplexSplitSuspensionPresentation S.X₁)).inv) :=
    congrArg _ <|
      (curvedDuplex_split_isFrobenius C w).projectiveStableFunctor_map_eq_connectingMap_comp hS
        (curvedDuplexSplitSuspensionPresentation S.X₁) a δ ha hδ
  simp only [curvedDuplexSplitStableToHomotopy_map_projectiveStableFunctor_map, Functor.map_comp,
    IsFrobenius.projectiveStableIsoSuspensionObj_inv, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp] at key
  rw [IsFrobenius.stableConflationTriangle_eq_mk]
  refine Triangle.isoMk _ _ (eqToIso (by simp)) (eqToIso (by simp)) (eqToIso (by simp)) ?_ ?_ ?_
  · simp [curvedDuplexSplitStableToHomotopy_map_projectiveStableFunctor_map]
  · simp [curvedDuplexSplitStableToHomotopy_map_projectiveStableFunctor_map]
  · simp only [Triangle.mk_obj₃, Functor.mapTriangle_obj, Triangle.mk_obj₁, Triangle.mk_mor₃,
      parityShiftCompQuotientFunctorIso_hom_app, eqToIso.hom, Category.assoc, Functor.map_comp,
      curvedDuplexSplitStableToHomotopy_map_projectiveStableFunctor_map,
      curvedDuplexSplitStableToHomotopyCommShift_iso_one, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.comp_obj, Functor.whiskerRight_app,
      stableSuspensionCompCurvedDuplexSplitStableToHomotopyIso_hom_app, Functor.whiskerLeft_app,
      Iso.inv_hom_id_app_map_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    -- `δ` is typed at the parity shift and the cokernel map at the cokernel term of the disk-sum
    -- presentation; unfolding the presentation makes the two agree reducibly.
    dsimp only [curvedDuplexSplitSuspensionPresentation] at key ⊢
    rw [eqToHom_comp_iff, comp_eqToHom_iff] at key
    simp only [key, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc,
      eqToHom_map, curvedDuplexSplitStableToHomotopy_obj_projectiveStableFunctor_obj,
      eqToHom_naturality]
    -- The two remaining identifications of objects pass through the unfolded presentation, whose
    -- cokernel term is the parity shift only definitionally; `rw` cannot match across them.
    congr 2
    erw [eqToHom_trans_assoc]

/-- **Componentwise split conflations give distinguished triangles.** Let `X₁ ⟶ X₂ ⟶ X₃` be a
short complex of curved duplexes which splits in both components, let `a : X₂ ⟶ diskSum X₁`
extend the inclusion of `X₁` into its disk sum, and let `δ : X₃ ⟶ X₁[1]` be the map induced by
`a` on cokernels. Then the triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` of homotopy classes, with third map
the class of `δ`, is distinguished. -/
theorem mk_distinguished_of_conflation (hS : ((split C).curvedDuplex w).Conflation S)
    (a : S.X₂ ⟶ diskSum S.X₁) (δ : S.X₃ ⟶ (parityShift C w).obj S.X₁)
    (ha : S.f ≫ a = toDiskSum S.X₁) (hδ : S.g ≫ δ = a ≫ diskSumToParityShift S.X₁) :
    Triangle.mk ((nullHomotopic C w).quotientFunctor.map S.f)
        ((nullHomotopic C w).quotientFunctor.map S.g)
        ((nullHomotopic C w).quotientFunctor.map δ ≫
          (parityShiftCompQuotientFunctorIso C w).hom.app S.X₁) ∈
      distTriang (HomotopyCategory C w) := by
  let := (curvedDuplex_split_isFrobenius C w).stableHasShift
  let := (curvedDuplex_split_isFrobenius C w).stableShiftFunctor_additive
  let := (curvedDuplex_split_isFrobenius C w).stablePretriangulated
  let := curvedDuplexSplitStableToHomotopyCommShift C w
  refine ⟨_, mapStableConflationTriangleIso hS a δ ha hδ, ?_⟩
  rw [IsFrobenius.stablePretriangulated_distinguishedTriangles]
  exact (curvedDuplex_split_isFrobenius C w).stableConflationTriangle_mem S hS

variable (C w) in
/-- The distinguished triangles of the homotopy category of curved duplexes are exactly the
triangles isomorphic to the triangle of homotopy classes `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` of a
componentwise split short complex, with third map induced by an extension `X₂ ⟶ diskSum X₁` of
the inclusion of `X₁` into its disk sum. -/
theorem mem_distTriang_iff (T : Triangle (HomotopyCategory C w)) :
    T ∈ distTriang (HomotopyCategory C w) ↔
      ∃ (S : ShortComplex (CurvedDuplex C w)) (_ : ((split C).curvedDuplex w).Conflation S)
        (a : S.X₂ ⟶ diskSum S.X₁) (δ : S.X₃ ⟶ (parityShift C w).obj S.X₁)
        (_ : S.f ≫ a = toDiskSum S.X₁) (_ : S.g ≫ δ = a ≫ diskSumToParityShift S.X₁),
        Nonempty (T ≅ Triangle.mk ((nullHomotopic C w).quotientFunctor.map S.f)
          ((nullHomotopic C w).quotientFunctor.map S.g)
          ((nullHomotopic C w).quotientFunctor.map δ ≫
            (parityShiftCompQuotientFunctorIso C w).hom.app S.X₁)) := by
  refine ⟨fun ⟨T', e, hT'⟩ ↦ ?_, fun ⟨S, hS, a, δ, ha, hδ, ⟨e⟩⟩ ↦
    isomorphic_distinguished _ (mk_distinguished_of_conflation hS a δ ha hδ) _ e⟩
  let := (curvedDuplex_split_isFrobenius C w).stableHasShift
  let := (curvedDuplex_split_isFrobenius C w).stableShiftFunctor_additive
  let := (curvedDuplex_split_isFrobenius C w).stablePretriangulated
  let := curvedDuplexSplitStableToHomotopyCommShift C w
  rw [IsFrobenius.stablePretriangulated_distinguishedTriangles] at hT'
  obtain ⟨S, hS, ⟨e'⟩⟩ := ((curvedDuplex_split_isFrobenius C w).mem_stableDistinguishedTriangles_iff
    T').1 hT'
  -- Extend the inclusion into the disk sum across the inflation of `S`, and pass to cokernels.
  have hI := (curvedDuplexSplitSuspensionPresentation S.X₁).isInjective
  have hi := ((split C).curvedDuplex w).isInflation_f hS
  let a : S.X₂ ⟶ diskSum S.X₁ := hI.factorThru hi (toDiskSum S.X₁)
  have ha : S.f ≫ a = toDiskSum S.X₁ := hI.comp_factorThru hi _
  have hkc := ((split C).curvedDuplex w).isKernelCokernelPair S hS
  refine ⟨S, hS, a, hkc.desc (a ≫ diskSumToParityShift S.X₁)
    (by rw [reassoc_of% ha, toDiskSum_comp_diskSumToParityShift]), ha, hkc.g_desc _ _, ⟨?_⟩⟩
  exact e ≪≫ (curvedDuplexSplitStableToHomotopy C w).mapTriangle.mapIso e' ≪≫
    (mapStableConflationTriangleIso hS a _ ha (hkc.g_desc _ _)).symm

end CurvedDuplex.HomotopyCategory

end TauCeti
