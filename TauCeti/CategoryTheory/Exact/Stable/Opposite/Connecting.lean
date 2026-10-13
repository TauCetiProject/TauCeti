/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Opposite.Suspension
public import TauCeti.CategoryTheory.Exact.Stable.Autoequivalence

/-!
# Connecting maps in opposite stable categories

For a conflation `X ⟶ Y ⟶ Z` in a Frobenius exact category, its opposite has a connecting
map `op X ⟶ Σ(op Z)`. The opposite stable comparison identifies this suspension with
`op (ΩZ)`. Unopposing the resulting arrow gives a map `ΩZ ⟶ X` in the original stable
category. It is computed by lifting the projective presentation of `Z` to the conflation.

This map is the transpose of the original connecting map `Z ⟶ ΣX`: applying suspension
gives the original connecting map after the canonical counit `ΣΩZ ⟶ Z`. The equation uses
the chosen suspension-loop comparison and has no additional minus sign. It supplies the
connecting-arrow compatibility needed to compare opposite stable triangles; a coherent
comparison of integral shifts and a triangle-functor assertion are separate constructions.

## Main results

* `stableConnectingMapOp_eq_of_lift`: computation from a projective lift and its kernel map.
* `stableSuspension_map_stableConnectingMapOp`: compatibility with the original connecting map
  through the suspension-loop counit.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* `TauCeti.CategoryTheory.Exact.Stable.Connecting`: computation from an arbitrary injective
  presentation and naturality of connecting maps.
* `TauCeti.CategoryTheory.Exact.Stable.Opposite.Suspension`: the canonical opposite
  suspension-loop comparison.
-/

public section

namespace TauCeti.ExactStructure.IsFrobenius

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} (hE : E.IsFrobenius)
  {S : ShortComplex C} (hS : E.Conflation S)

/-- The connecting map of the opposite conflation, carried through the opposite stable
comparison and its suspension-loop comparison, then unopposed to an arrow `ΩZ ⟶ X`. -/
noncomputable def stableConnectingMapOp :
    hE.enoughProjectives.stableLoop.obj (E.projectiveStableFunctor.obj S.X₃) ⟶
      E.projectiveStableFunctor.obj S.X₁ :=
  (eqToHom (E.projectiveStableOpFunctor_obj hE.projective_iff_injective (Opposite.op S.X₁)).symm ≫
    (E.projectiveStableOpFunctor hE.projective_iff_injective).map
      (E.op.projectiveStableFunctor.map
        (hE.op.connectingMap ((E.op_conflation_op_iff S).mpr hS))) ≫
    (E.projectiveStableOpFunctor hE.projective_iff_injective).map
      (eqToHom (hE.op.stableSuspension_obj_projectiveStableFunctor_obj (Opposite.op S.X₃)).symm) ≫
    hE.stableSuspensionCompProjectiveStableOpFunctorIso.hom.app
      (E.op.projectiveStableFunctor.obj (Opposite.op S.X₃)) ≫
    hE.enoughProjectives.stableLoop.op.map
      (eqToHom (E.projectiveStableOpFunctor_obj hE.projective_iff_injective
        (Opposite.op S.X₃)))).unop

/-- The characteristic expression for the transpose, in terms of the existing opposite
connecting map and the canonical opposite suspension-loop comparison. -/
theorem stableConnectingMapOp_eq :
    hE.stableConnectingMapOp hS =
      (eqToHom (E.projectiveStableOpFunctor_obj hE.projective_iff_injective
          (Opposite.op S.X₁)).symm ≫
        (E.projectiveStableOpFunctor hE.projective_iff_injective).map
          (E.op.projectiveStableFunctor.map
            (hE.op.connectingMap ((E.op_conflation_op_iff S).mpr hS))) ≫
        (E.projectiveStableOpFunctor hE.projective_iff_injective).map
          (eqToHom (hE.op.stableSuspension_obj_projectiveStableFunctor_obj
            (Opposite.op S.X₃)).symm) ≫
        hE.stableSuspensionCompProjectiveStableOpFunctorIso.hom.app
          (E.op.projectiveStableFunctor.obj (Opposite.op S.X₃)) ≫
        hE.enoughProjectives.stableLoop.op.map
          (eqToHom (E.projectiveStableOpFunctor_obj hE.projective_iff_injective
            (Opposite.op S.X₃)))).unop := (rfl)

/-- A lift of the chosen projective presentation of `Z` to a conflation `X ⟶ Y ⟶ Z`
computes the transpose of its opposite connecting map. The kernel map is independent of
the chosen lift after passing to the stable category. -/
theorem stableConnectingMapOp_eq_of_lift
    (b : hE.enoughProjectives.loopProjective S.X₃ ⟶ S.X₂)
    (k : hE.enoughProjectives.loopObj S.X₃ ⟶ S.X₁)
    (hb : b ≫ S.g = hE.enoughProjectives.loopDeflation S.X₃)
    (hk : k ≫ S.f = hE.enoughProjectives.loopInflation S.X₃ ≫ b) :
    hE.stableConnectingMapOp hS =
      eqToHom (hE.enoughProjectives.stableLoop_obj_projectiveStableFunctor_obj S.X₃) ≫
        E.projectiveStableFunctor.map k := by
  let P := hE.enoughProjectives.projectivePresentation S.X₃
  have ha : S.g.op ≫ (b.op ≫ eqToHom P.op_I.symm) = P.op.i := by
    rw [← cancel_mono (eqToHom P.op_I)]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      ProjectivePresentation.op_i]
    exact Quiver.Hom.unop_inj hb
  have hd : S.f.op ≫ (k.op ≫ eqToHom P.op_K.symm) =
      (b.op ≫ eqToHom P.op_I.symm) ≫ P.op.p := by
    rw [← cancel_mono (eqToHom P.op_K)]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    calc
      S.f.op ≫ k.op = b.op ≫ P.i.op := Quiver.Hom.unop_inj hk
      _ = b.op ≫ eqToHom P.op_I.symm ≫ P.op.p ≫ eqToHom P.op_K := by
        simpa only [Category.assoc] using congrArg (fun f ↦ b.op ≫ f) P.op_p.symm
  have hδ := hE.op.projectiveStableFunctor_map_eq_connectingMap_comp
    ((E.op_conflation_op_iff S).mpr hS) P.op
    (b.op ≫ eqToHom P.op_I.symm) (k.op ≫ eqToHom P.op_K.symm) ha hd
  -- Normalize Mathlib's opposite short-complex constructor so its dependent endpoints agree
  -- with the explicit opposite endpoints in the suspension comparison.
  dsimp only [ShortComplex.op] at hδ
  rw [stableConnectingMapOp_eq]
  simp only [stableSuspensionCompProjectiveStableOpFunctorIso_hom_app,
    Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp,
    projectiveStableIsoSuspensionObj_inv, ShortComplex.op] at *
  rw [← Functor.map_comp_assoc, ← hδ, Functor.map_comp_assoc]
  simp [E.projectiveStableOpFunctor_map, eqToHom_map, Category.assoc]

/-- Suspending the transpose of the opposite connecting map gives the original connecting
map after the canonical counit `ΣΩZ ⟶ Z`. This is the connecting-arrow equation for opposite
stable triangles, expressed before introducing integral shifts. -/
theorem stableSuspension_map_stableConnectingMapOp :
    hE.stableSuspension.map (hE.stableConnectingMapOp hS) =
      hE.stableLoopCompStableSuspensionIso.hom.app (E.projectiveStableFunctor.obj S.X₃) ≫
        E.projectiveStableFunctor.map (hE.connectingMap hS) ≫
          eqToHom (hE.stableSuspension_obj_projectiveStableFunctor_obj S.X₁).symm := by
  let b := (hE.enoughProjectives.isProjective_loopProjective S.X₃).factorThru
    (E.isDeflation_g hS) (hE.enoughProjectives.loopDeflation S.X₃)
  have hb : b ≫ S.g = hE.enoughProjectives.loopDeflation S.X₃ :=
    isProjective.factorThru_comp _ _ _
  let k := (E.isKernelCokernelPair S hS).lift
    (hE.enoughProjectives.loopInflation S.X₃ ≫ b) (by simp [hb])
  have hk : k ≫ S.f = hE.enoughProjectives.loopInflation S.X₃ ≫ b :=
    (E.isKernelCokernelPair S hS).lift_f _ _
  let φ : ShortComplex.mk (hE.enoughProjectives.loopInflation S.X₃)
      (hE.enoughProjectives.loopDeflation S.X₃)
      (hE.enoughProjectives.loopInflation_comp_loopDeflation S.X₃) ⟶ S :=
    { τ₁ := k, τ₂ := b, τ₃ := 𝟙 _, comm₁₂ := hk, comm₂₃ := by simpa using hb }
  have hδ := hE.projectiveStableFunctor_map_connectingMap_naturality
    (hE.enoughProjectives.conflation_loopInflation_loopDeflation S.X₃) hS φ
  rw [hE.stableConnectingMapOp_eq_of_lift hS b k hb hk]
  rw [Functor.map_comp, eqToHom_map,
    hE.stableSuspension_map_projectiveStableFunctor_map,
    hE.stableLoopCompStableSuspensionIso_hom_app]
  simp only [φ, Category.id_comp, Functor.map_comp] at hδ
  rw [hδ]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc,
    hE.projectiveStableFunctor_map_fromSuspensionLoop_comp_connectingMap]
  simp

end TauCeti.ExactStructure.IsFrobenius
