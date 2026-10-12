/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Shift
public import TauCeti.CategoryTheory.Exact.Stable.Triangulated
public import TauCeti.CategoryTheory.Localization.Triangulated

/-!
# The homotopy category of matrix factorizations is triangulated

Let `S` be a commutative ring and `w : S`. Finite-projective matrix factorizations of `w` with
the componentwise split exact structure form a Frobenius exact category, and its stable category
is identified with `HMF(S,w)`, here `MatrixFactorization.HomotopyCategory`, by
`MatrixFactorization.stableToHomotopy`, compatibly with the shifts by `ℤ` (stable suspension on
one side, the parity shift on the other). This file transports Happel's triangulation of the
stable category along this equivalence, which makes `HMF(S,w)` a triangulated category whose
shift by `1` is the parity shift. No regularity hypothesis on `S` or `w` is needed.

The distinguished triangles are described concretely. Let `X₁ ⟶ X₂ ⟶ X₃` be a short complex of
matrix factorizations which splits in both components. Since the disk sum `diskSum X₁` is
contractible, the inflation `X₁ ⟶ diskSum X₁` extends along `X₁ ⟶ X₂` to a map
`a : X₂ ⟶ diskSum X₁`, which induces `δ : X₃ ⟶ X₁[1]` on cokernels. Then

`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]`

with third map the homotopy class of `δ` is distinguished, and every distinguished triangle is
isomorphic to one of these.

## Main definitions

* `TauCeti.MatrixFactorization.HomotopyCategory.instPretriangulated`: the pretriangulated
  structure on `HMF(S,w)`.

## Main results

* `TauCeti.MatrixFactorization.HomotopyCategory.instIsTriangulated`: `HMF(S,w)` is
  triangulated.
* `TauCeti.MatrixFactorization.stableToHomotopy_isTriangulated`: the comparison from the
  componentwise split stable category is a triangle functor.
* `TauCeti.MatrixFactorization.HomotopyCategory.mk_distinguished_of_conflation`: componentwise
  split short complexes give distinguished triangles.
* `TauCeti.MatrixFactorization.HomotopyCategory.mem_distTriang_iff`: every distinguished
  triangle is isomorphic to the triangle of a componentwise split short complex.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, Theorem 2.6: the stable category of a Frobenius category is
  triangulated.
* D. Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg models*,
  Proc. Steklov Inst. Math. **246** (2004), Section 3, for the triangulated category of
  finite-projective matrix factorizations.

The argument follows the curved-duplex version in
`TauCeti.Algebra.Homology.Curved.Triangulated`, restricted to finite-projective components.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {S : Type u} [CommRing S] {w : S}

namespace HomotopyCategory

variable (S w)

/-- The homotopy category of matrix factorizations is pretriangulated: its distinguished triangles
are the images of Happel's distinguished triangles under the equivalence with the componentwise
split stable category. -/
noncomputable instance instPretriangulated : Pretriangulated (HomotopyCategory (S := S) (w := w)) :=
  letI := (splitExact_isFrobenius S w).stableHasShift
  letI := (splitExact_isFrobenius S w).stableShiftFunctor_additive
  letI := (splitExact_isFrobenius S w).stablePretriangulated
  letI := stableToHomotopyCommShift S w
  Triangulated.Localization.pretriangulated (stableToHomotopy S w)
    (MorphismProperty.isomorphisms _)

end HomotopyCategory

variable (S w) in
/-- The comparison from the componentwise split stable category of matrix factorizations to
`HMF(S,w)` is a triangle functor. -/
theorem stableToHomotopy_isTriangulated :
    letI := (splitExact_isFrobenius S w).stableHasShift
    letI := (splitExact_isFrobenius S w).stableShiftFunctor_additive
    letI := (splitExact_isFrobenius S w).stablePretriangulated
    letI := stableToHomotopyCommShift S w
    (stableToHomotopy S w).IsTriangulated :=
  letI := (splitExact_isFrobenius S w).stableHasShift
  letI := (splitExact_isFrobenius S w).stableShiftFunctor_additive
  letI := (splitExact_isFrobenius S w).stablePretriangulated
  letI := stableToHomotopyCommShift S w
  Triangulated.Localization.isTriangulated_functor _ (MorphismProperty.isomorphisms _)

namespace HomotopyCategory

variable (S w) in
/-- **The homotopy category of matrix factorizations is triangulated**, with the shift by `1`
given by the parity shift. -/
instance instIsTriangulated : IsTriangulated (HomotopyCategory (S := S) (w := w)) :=
  letI := (splitExact_isFrobenius S w).stableHasShift
  letI := (splitExact_isFrobenius S w).stableShiftFunctor_additive
  letI := (splitExact_isFrobenius S w).stablePretriangulated
  letI := stableToHomotopyCommShift S w
  haveI := (splitExact_isFrobenius S w).stableIsTriangulated
  haveI := stableToHomotopy_isTriangulated S w
  Triangulated.Localization.isTriangulated (stableToHomotopy S w)
    (MorphismProperty.isomorphisms _)

variable {T : ShortComplex (MatrixFactorization S w)}

/-- The image of Happel's standard triangle of a componentwise split conflation is isomorphic to
the triangle of homotopy classes whose third map is induced by an extension to the disk sum. -/
private noncomputable def mapStableConflationTriangleIso (hT : (splitExact S w).Conflation T)
    (a : T.X₂ ⟶ diskSum T.X₁) (δ : T.X₃ ⟶ parityShift.obj T.X₁)
    (ha : T.f ≫ a = toDiskSum T.X₁) (hδ : T.g ≫ δ = a ≫ diskSumToParityShift T.X₁) :
    letI := (splitExact_isFrobenius S w).stableHasShift
    letI := stableToHomotopyCommShift S w
    Triangle.mk ((nullHomotopic (S := S) (w := w)).quotientFunctor.map T.f)
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map T.g)
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map δ ≫
          (parityShiftCompQuotientFunctorIso S w).hom.app T.X₁) ≅
      (stableToHomotopy S w).mapTriangle.obj
        ((splitExact_isFrobenius S w).stableConflationTriangle T hT) := by
  letI := (splitExact_isFrobenius S w).stableHasShift
  letI := stableToHomotopyCommShift S w
  -- The image of `δ` is the image of the connecting map, read through the disk-sum presentation.
  have key : (stableToHomotopy S w).map ((splitExact S w).projectiveStableFunctor.map δ) =
      (stableToHomotopy S w).map
        ((splitExact S w).projectiveStableFunctor.map
          ((splitExact_isFrobenius S w).connectingMap hT) ≫
        ((splitExact_isFrobenius S w).projectiveStableIsoSuspensionObj
          (splitSuspensionPresentation T.X₁)).inv) :=
    congrArg _ <|
      (splitExact_isFrobenius S w).projectiveStableFunctor_map_eq_connectingMap_comp hT
        (splitSuspensionPresentation T.X₁) a δ ha hδ
  simp only [stableToHomotopy_map, Functor.map_comp,
    ExactStructure.IsFrobenius.projectiveStableIsoSuspensionObj_inv, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  rw [ExactStructure.IsFrobenius.stableConflationTriangle_eq_mk]
  refine Triangle.isoMk _ _ (eqToIso (by simp)) (eqToIso (by simp)) (eqToIso (by simp)) ?_ ?_ ?_
  · simp [stableToHomotopy_map]
  · simp [stableToHomotopy_map]
  · simp only [Triangle.mk_obj₃, Functor.mapTriangle_obj, Triangle.mk_obj₁, Triangle.mk_mor₃,
      parityShiftCompQuotientFunctorIso_hom_app, eqToIso.hom, Category.assoc, Functor.map_comp,
      stableToHomotopy_map, stableToHomotopyCommShift_iso_one, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.comp_obj, Functor.whiskerRight_app, stableSuspensionCompStableToHomotopyIso_hom_app,
      Functor.whiskerLeft_app, Iso.inv_hom_id_app_map_assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    -- `δ` is typed at the parity shift and the cokernel map at the cokernel term of the disk-sum
    -- presentation; unfolding the presentation makes the two agree reducibly.
    dsimp only [splitSuspensionPresentation] at key ⊢
    rw [eqToHom_comp_iff, comp_eqToHom_iff] at key
    simp only [key, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc,
      eqToHom_map, stableToHomotopy_obj, eqToHom_naturality]
    -- The two remaining identifications of objects pass through the unfolded presentation, whose
    -- cokernel term is the parity shift only definitionally; `rw` cannot match across them.
    congr 2
    erw [eqToHom_trans_assoc]

/-- **Componentwise split conflations give distinguished triangles.** Let `X₁ ⟶ X₂ ⟶ X₃` be a
short complex of matrix factorizations which splits in both components, let
`a : X₂ ⟶ diskSum X₁` extend the inclusion of `X₁` into its disk sum, and let `δ : X₃ ⟶ X₁[1]` be
the map induced by `a` on cokernels. Then the triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` of homotopy
classes, with third map the class of `δ`, is distinguished. -/
theorem mk_distinguished_of_conflation (hT : (splitExact S w).Conflation T)
    (a : T.X₂ ⟶ diskSum T.X₁) (δ : T.X₃ ⟶ parityShift.obj T.X₁)
    (ha : T.f ≫ a = toDiskSum T.X₁) (hδ : T.g ≫ δ = a ≫ diskSumToParityShift T.X₁) :
    Triangle.mk ((nullHomotopic (S := S) (w := w)).quotientFunctor.map T.f)
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map T.g)
        ((nullHomotopic (S := S) (w := w)).quotientFunctor.map δ ≫
          (parityShiftCompQuotientFunctorIso S w).hom.app T.X₁) ∈
      distTriang (HomotopyCategory (S := S) (w := w)) := by
  let := (splitExact_isFrobenius S w).stableHasShift
  let := (splitExact_isFrobenius S w).stableShiftFunctor_additive
  let := (splitExact_isFrobenius S w).stablePretriangulated
  let := stableToHomotopyCommShift S w
  refine ⟨_, mapStableConflationTriangleIso hT a δ ha hδ, ?_⟩
  rw [ExactStructure.IsFrobenius.stablePretriangulated_distinguishedTriangles]
  exact (splitExact_isFrobenius S w).stableConflationTriangle_mem T hT

variable (S w) in
/-- The distinguished triangles of the homotopy category of matrix factorizations are exactly the
triangles isomorphic to the triangle of homotopy classes `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` of a
componentwise split short complex, with third map induced by an extension `X₂ ⟶ diskSum X₁` of
the inclusion of `X₁` into its disk sum. -/
theorem mem_distTriang_iff (D : Triangle (HomotopyCategory (S := S) (w := w))) :
    D ∈ distTriang (HomotopyCategory (S := S) (w := w)) ↔
      ∃ (T : ShortComplex (MatrixFactorization S w)) (_ : (splitExact S w).Conflation T)
        (a : T.X₂ ⟶ diskSum T.X₁) (δ : T.X₃ ⟶ parityShift.obj T.X₁)
        (_ : T.f ≫ a = toDiskSum T.X₁) (_ : T.g ≫ δ = a ≫ diskSumToParityShift T.X₁),
        Nonempty (D ≅ Triangle.mk ((nullHomotopic (S := S) (w := w)).quotientFunctor.map T.f)
          ((nullHomotopic (S := S) (w := w)).quotientFunctor.map T.g)
          ((nullHomotopic (S := S) (w := w)).quotientFunctor.map δ ≫
            (parityShiftCompQuotientFunctorIso S w).hom.app T.X₁)) := by
  refine ⟨fun ⟨D', e, hD'⟩ ↦ ?_, fun ⟨T, hT, a, δ, ha, hδ, ⟨e⟩⟩ ↦
    isomorphic_distinguished _ (mk_distinguished_of_conflation hT a δ ha hδ) _ e⟩
  let := (splitExact_isFrobenius S w).stableHasShift
  let := (splitExact_isFrobenius S w).stableShiftFunctor_additive
  let := (splitExact_isFrobenius S w).stablePretriangulated
  let := stableToHomotopyCommShift S w
  rw [ExactStructure.IsFrobenius.stablePretriangulated_distinguishedTriangles] at hD'
  obtain ⟨T, hT, ⟨e'⟩⟩ :=
    ((splitExact_isFrobenius S w).mem_stableDistinguishedTriangles_iff D').1 hD'
  -- Extend the inclusion into the disk sum across the inflation of `T`, and pass to cokernels.
  have hI := (splitSuspensionPresentation T.X₁).isInjective
  have hi := (splitExact S w).isInflation_f hT
  let a : T.X₂ ⟶ diskSum T.X₁ := hI.factorThru hi (toDiskSum T.X₁)
  have ha : T.f ≫ a = toDiskSum T.X₁ := hI.comp_factorThru hi _
  have hkc := (splitExact S w).isKernelCokernelPair T hT
  refine ⟨T, hT, a, hkc.desc (a ≫ diskSumToParityShift T.X₁)
    (by rw [reassoc_of% ha, toDiskSum_comp_diskSumToParityShift]), ha, hkc.g_desc _ _, ⟨?_⟩⟩
  exact e ≪≫ (stableToHomotopy S w).mapTriangle.mapIso e' ≪≫
    (mapStableConflationTriangleIso hT a _ ha (hkc.g_desc _ _)).symm

end HomotopyCategory

end TauCeti.MatrixFactorization
