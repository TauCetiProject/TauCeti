/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Frame
public import TauCeti.Analysis.CStarAlgebra.Module.FiniteFree
public import TauCeti.Analysis.CStarAlgebra.Module.Gram
public import TauCeti.Analysis.CStarAlgebra.Module.Matrix
public import TauCeti.Analysis.CStarAlgebra.Module.Unitary

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Order

/-!
# Gram-projection coordinate models, retract splitting, and polar decomposition

For a right Hilbert `A`-module `E` (`CStarModule Aᵐᵒᵖ E`, with right action `x a = op a • x` and
`⟨x, y⟩_A = unop (inner Aᵐᵒᵖ x y)`), this file builds on the finite Parseval frame API in
`TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Frame` and automatic continuity in
`TauCeti.Analysis.CStarAlgebra.Module.FiniteFree` to establish:

* Over a unital C⋆-algebra `A`, Parseval frames correspond unitarily to projection-cutdown modules
  `LinearMap.range (CStarMatrix.mulVecLinearMap p)` (`CStarModule.IsParsevalFrame.equivRangeGram`,
  `IsStarProjection.exists_isParsevalFrame_and_gram_eq`,
  `TauCeti.CStarModule.exists_isParsevalFrame_iff_exists_isStarProjection_linearIsometryEquiv`).
* Every complete right `A`-linear retract of `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` admits an `ι`-indexed Parseval
  frame (`LinearMap.exists_isParsevalFrame_of_comp_eq_id`, applied downstream in
  `TauCeti.Analysis.CStarAlgebra.Module.Projective` to finitely generated projective modules).
* For a right `A`-linear equivalence `T : E ≃ₗ[Aᵐᵒᵖ] F` out of a module with a finite Parseval
  frame into a complete right Hilbert `A`-module `F`, the frame gives the canonical polar
  decomposition `T = U ∘ |T|` (`CStarModule.IsParsevalFrame.polarModulus`,
  `CStarModule.IsParsevalFrame.polarUnitary`,
  `CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply`), shown to be unique and
  independent of the chosen frame (`CStarModule.IsParsevalFrame.eq_polarModulus_of_inner_eq`,
  `CStarModule.IsParsevalFrame.eq_polarModulus_toLinearMap`,
  `CStarModule.IsParsevalFrame.polarModulus_eq`, `CStarModule.IsParsevalFrame.polarUnitary_eq`).

## Main declarations

* `CStarModule.IsParsevalFrame.equivRangeGram`,
  `IsStarProjection.exists_isParsevalFrame_and_gram_eq`,
  `TauCeti.CStarModule.exists_isParsevalFrame_iff_exists_isStarProjection_linearIsometryEquiv`
* `LinearMap.exists_isParsevalFrame_of_comp_eq_id`
* `TauCeti.CStarModule.polarMatrix`,
  `CStarModule.IsParsevalFrame.polarModulus`, `CStarModule.IsParsevalFrame.polarUnitary`,
  `CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply`,
  `CStarModule.IsParsevalFrame.eq_polarModulus_of_inner_eq`,
  `CStarModule.IsParsevalFrame.eq_polarModulus_toLinearMap`,
  `CStarModule.IsParsevalFrame.polarModulus_eq`, `CStarModule.IsParsevalFrame.polarUnitary_eq`

## References

* M. Frank and D. R. Larson, *Frames in Hilbert C⋆-modules and C⋆-algebras*, J. Operator Theory 48
  (2002), 273–314.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1–4 and 6.
* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Chapter 2.
* J. Roe, *Lectures on K-Theory and Operator Algebras*, Proposition 10.2.
-/

public section

open MulOpposite Matrix CStarModule TauCeti
open CStarMatrix (mulVecCLM mulVecLinearMap)
open scoped WithCStarModule

private noncomputable abbrev normedAddCommGroupOfCStarModule (A E : Type*)
    [NonUnitalCStarAlgebra A] [PartialOrder A] [SeminormedAddCommGroup E] [Module ℂ E] [SMul A E]
    [CStarModule A E] : NormedAddCommGroup E :=
  NormedAddCommGroup.ofSeparation fun x ↦ (CStarModule.norm_zero_iff A x).mp

/-! ### Unital coefficient algebras: projection comparison -/

namespace TauCeti.CStarModule

section Unital

private def opSynthesisLinearMap (A : Type*) {ι E : Type*} [Fintype ι] [Ring A]
    [AddCommMonoid E] [Module Aᵐᵒᵖ E] (x : ι → E) : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E :=
  (Fintype.linearCombination Aᵐᵒᵖ x).comp (TauCeti.WithCStarModule.piOpLinearEquiv A ι).toLinearMap

@[simp]
private theorem opSynthesisLinearMap_apply {A ι E : Type*} [Fintype ι] [Ring A] [AddCommMonoid E]
    [Module Aᵐᵒᵖ E] (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    opSynthesisLinearMap A x v = ∑ i, op (v i) • x i := by
  simp [opSynthesisLinearMap, Fintype.linearCombination_apply]

private theorem opSynthesisLinearMap_single_one {A ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Ring A] [AddCommMonoid E] [Module Aᵐᵒᵖ E] (x : ι → E) (i : ι) :
    opSynthesisLinearMap A x ((WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))) =
      x i := by
  simp [Pi.single_apply, apply_ite op, ite_smul]

private noncomputable def opAnalysisLinearMap (A : Type*) {ι E : Type*} [Ring A] [StarRing A]
    [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ] [AddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E]
    [Norm E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  (TauCeti.WithCStarModule.piOpLinearEquiv A ι).symm.toLinearMap.comp
    (CStarModule.analysisLinearMap x)

@[simp]
private theorem opAnalysisLinearMap_apply_apply {A ι E : Type*} [Ring A] [StarRing A]
    [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ] [AddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E]
    [Norm E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) (z : E) (i : ι) :
    opAnalysisLinearMap A x z i = unop (inner Aᵐᵒᵖ (x i) z) := by
  simp [opAnalysisLinearMap]

private theorem opSynthesisLinearMap_comp_opAnalysisLinearMap {A ι E : Type*} [Fintype ι] [Ring A]
    [StarRing A] [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ] [AddCommGroup E] [Module ℂ E]
    [Module Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E] {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    (opSynthesisLinearMap A x).comp (opAnalysisLinearMap A x) = LinearMap.id := by
  ext z
  simpa [LinearMap.comp_apply] using hx.sum_inner_smul z

private theorem opAnalysisLinearMap_comp_opSynthesisLinearMap {A ι E : Type*} [Fintype ι]
    [Ring A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ] [AddCommGroup E] [Module ℂ E]
    [Module Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) :
    (opAnalysisLinearMap A x).comp (opSynthesisLinearMap A x) =
      mulVecLinearMap (CStarMatrix.gram A x) := by
  ext v i
  simp [TauCeti.CStarModule.inner_sum_right' (A := Aᵐᵒᵖ), CStarModule.inner_op_smul_right,
    Finset.unop_sum]

private theorem inner_opSynthesisLinearMap_left {A ι E : Type*} [Fintype ι] [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [AddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E] [Norm E]
    [CStarModule Aᵐᵒᵖ E] (x : ι → E) (w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) (u : E) :
    inner Aᵐᵒᵖ (opSynthesisLinearMap A x w) u = inner Aᵐᵒᵖ w (opAnalysisLinearMap A x u) := by
  apply unop_injective
  simp [WithCStarModule.pi_inner, inner_sum_left, Finset.unop_sum]

private theorem inner_opSynthesisLinearMap_right {A ι E : Type*} [Fintype ι] [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [AddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E] [Norm E]
    [CStarModule Aᵐᵒᵖ E] (x : ι → E) (u : E) (w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    inner Aᵐᵒᵖ u (opSynthesisLinearMap A x w) = inner Aᵐᵒᵖ (opAnalysisLinearMap A x u) w :=
  star_injective <| by simpa [star_inner] using inner_opSynthesisLinearMap_left x w u

private theorem range_opAnalysisLinearMap {A ι E : Type*} [Fintype ι] [Ring A] [StarRing A]
    [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ] [AddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E]
    [Norm E] [CStarModule Aᵐᵒᵖ E] {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    LinearMap.range (opAnalysisLinearMap A x) =
      LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    refine ⟨opAnalysisLinearMap A x z, ?_⟩
    rw [← opAnalysisLinearMap_comp_opSynthesisLinearMap, LinearMap.comp_apply]
    simpa using congrArg (opAnalysisLinearMap A x) (hx.sum_inner_smul z)
  · rw [← opAnalysisLinearMap_comp_opSynthesisLinearMap (A := A) x]
    exact LinearMap.range_comp_le_range _ _

variable {A ι E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [Fintype ι]

/-- A Parseval frame `x : ι → E` identifies `E` unitarily (`E ≃ₗᵢ[Aᵐᵒᵖ] _`) with
`LinearMap.range (CStarMatrix.mulVecLinearMap (CStarMatrix.gram A x))`, with inverse given
by `v ↦ ∑ i, op (v.val i) • x i`. -/
noncomputable def _root_.CStarModule.IsParsevalFrame.equivRangeGram {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x)) := by
  let S := LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x))
  have hisom : ∀ z : E,
      inner Aᵐᵒᵖ (opAnalysisLinearMap A x z) (opAnalysisLinearMap A x z) = inner Aᵐᵒᵖ z z := by
    intro z
    apply unop_injective
    simpa [WithCStarModule.pi_inner, Finset.unop_sum, inner_mulOpposite, ← unop_star] using
      (isParsevalFrame_iff_sum_star_unop_inner_mul_unop_inner.mp hx) z
  let f : E →ₗᵢ[Aᵐᵒᵖ] S :=
    { toLinearMap := (opAnalysisLinearMap A x).codRestrict S fun z ↦ by
        dsimp only [S]
        rw [← range_opAnalysisLinearMap hx]
        exact LinearMap.mem_range_self _ z
      norm_map' := fun z ↦ by
        simpa using ((opAnalysisLinearMap A x).isometryOfInnerCStarModule hisom).norm_map z }
  refine LinearIsometryEquiv.ofLinearIsometry f ((opSynthesisLinearMap A x).comp S.subtype) ?_
    (LinearMap.ext fun z ↦ by simpa [f, LinearMap.comp_apply] using hx.sum_inner_smul z)
  apply LinearMap.ext
  rintro ⟨w, v, rfl⟩
  apply Subtype.ext
  dsimp only [f, LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearIsometry.coe_toLinearMap,
    Submodule.coe_subtype, LinearMap.id_apply]
  rw [← LinearMap.comp_apply, opAnalysisLinearMap_comp_opSynthesisLinearMap,
    CStarMatrix.mulVecLinearMap_mulVecLinearMap,
    (CStarMatrix.isStarProjection_gram hx).isIdempotentElem.eq]

@[simp]
theorem _root_.CStarModule.IsParsevalFrame.coe_equivRangeGram_apply_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (z : E) (i : ι) :
    (hx.equivRangeGram z : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) i = unop (inner Aᵐᵒᵖ (x i) z) := by
  simp [_root_.CStarModule.IsParsevalFrame.equivRangeGram]

@[simp]
theorem _root_.CStarModule.IsParsevalFrame.equivRangeGram_symm_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (u : LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x))) :
    hx.equivRangeGram.symm u = ∑ i, op (u.val i) • x i := by
  simp [_root_.CStarModule.IsParsevalFrame.equivRangeGram]

/-- If `p : CStarMatrix ι ι A` is a star projection and
`U : E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (CStarMatrix.mulVecLinearMap p)` is a unitary isomorphism,
then `E` admits an `ι`-indexed Parseval frame whose Gram matrix is `p`. -/
theorem _root_.IsStarProjection.exists_isParsevalFrame_and_gram_eq {p : CStarMatrix ι ι A}
    (hp : IsStarProjection p) (U : E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (mulVecLinearMap p)) :
    ∃ x : ι → E, IsParsevalFrame Aᵐᵒᵖ x ∧ CStarMatrix.gram A x = p := by
  classical
  let e := fun j : ι ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single j (1 : A))
  let u : ι → LinearMap.range (mulVecLinearMap p) := fun j ↦ ⟨mulVecLinearMap p (e j), e j, rfl⟩
  let x : ι → E := fun j ↦ U.symm (u j)
  have hgram : CStarMatrix.gram A x = p := by
    have hU : CStarMatrix.gram A x = CStarMatrix.gram A (fun j ↦ mulVecCLM p (e j)) := by
      ext i j; simp [x, u]
    rw [hU, CStarMatrix.gram_mulVecCLM_single_one, ← CStarMatrix.star_eq_conjTranspose,
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  refine ⟨x, isParsevalFrame_iff.mpr fun z ↦ U.toLinearEquiv.injective ?_, hgram⟩
  obtain ⟨v, hv⟩ := (U z).property
  have hUz : mulVecLinearMap p (U z).val = (U z).val := by
    rw [← hv, CStarMatrix.mulVecLinearMap_mulVecLinearMap, hp.isIdempotentElem.eq]
  have hinner (i : ι) : inner Aᵐᵒᵖ (x i) z = op ((U z).val i) := by
    have hsym : U (x i) = u i := U.apply_symm_apply (u i)
    rw [← U.inner_map_map_cstarModule (x i) z, hsym]
    apply unop_injective
    calc unop (inner Aᵐᵒᵖ (u i) (U z))
        = unop (inner Aᵐᵒᵖ (mulVecCLM p (e i)) (U z).val) := by simp [u]
      _ = unop (inner Aᵐᵒᵖ (e i) (mulVecCLM (star p) (U z).val)) :=
          congrArg unop ((CStarMatrix.isAdjointPair_mulVecCLM_star p).inner_eq_cstarModule _ _)
      _ = unop (inner Aᵐᵒᵖ (e i) (U z).val) := by
          rw [hp.isSelfAdjoint.star_eq, ← CStarMatrix.coe_mulVecLinearMap, hUz]
      _ = (U z).val i := by
          simp [e, WithCStarModule.inner_single_left, inner_mulOpposite]
  apply Subtype.ext
  rw [map_sum]
  simp only [map_smul, LinearIsometryEquiv.coe_toLinearEquiv, hinner]
  calc (↑(∑ i, op ((U z).val i) • U (x i)) : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))
      = ∑ i, op ((U z).val i) • mulVecLinearMap p (e i) := by
          simp [x, u]
    _ = mulVecLinearMap p (∑ i, op ((U z).val i) • e i) := by
          simp_rw [map_sum, map_smul]
    _ = (U z).val := by rw [WithCStarModule.sum_op_smul_single_one, hUz]

/-- Over a unital C⋆-algebra, `E` admits an `ι`-indexed Parseval frame iff `E` is unitarily
isomorphic to `LinearMap.range (CStarMatrix.mulVecLinearMap p)` for a star projection `p`.
-/
theorem exists_isParsevalFrame_iff_exists_isStarProjection_linearIsometryEquiv :
    (∃ x : ι → E, IsParsevalFrame Aᵐᵒᵖ x) ↔
      ∃ p : CStarMatrix ι ι A, IsStarProjection p ∧
        Nonempty (E ≃ₗᵢ[Aᵐᵒᵖ] LinearMap.range (mulVecLinearMap p)) :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨CStarMatrix.gram A x, CStarMatrix.isStarProjection_gram hx, ⟨hx.equivRangeGram⟩⟩,
    fun ⟨_, hp, ⟨U⟩⟩ ↦ (hp.exists_isParsevalFrame_and_gram_eq U).imp fun _ h ↦ h.1⟩

end Unital

end TauCeti.CStarModule

/-! ### Splitting Gram matrices and Parseval frames on retracts of free modules -/

namespace LinearMap

open TauCeti.CStarModule

private def stdBasis (A ι : Type*) [DecidableEq ι] [Ring A] (i : ι) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single i (1 : A))

private def splittingMap {A ι E : Type*} [Ring A] [AddCommGroup E] [Module Aᵐᵒᵖ E]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
  (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ _).symm.toLinearMap ∘ₗ f.prod (LinearMap.id - g ∘ₗ f)

private theorem splittingMap_apply {A ι E : Type*} [Ring A] [AddCommGroup E]
    [Module Aᵐᵒᵖ E] (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E)
    (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    splittingMap f g v = (WithCStarModule.equiv Aᵐᵒᵖ _).symm (f v, v - g (f v)) := by
  simp [splittingMap]

private def splittingFamily {A ι E : Type*} [DecidableEq ι] [Ring A] [AddCommGroup E]
    [Module Aᵐᵒᵖ E] (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E)
    (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) (i : ι) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
  splittingMap f g (stdBasis A ι i)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem algebraMap_inv_le_gram_of_le_smul {ι W : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module ℂ W] [SMul Aᵐᵒᵖ W] [Norm W] [CStarModule Aᵐᵒᵖ W]
    (y : ι → W) {C : ℝ} (hC : 0 < C) (hbound : ∀ w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A),
      unop (inner Aᵐᵒᵖ w w) ≤ C • unop (inner Aᵐᵒᵖ (∑ i, op (w i) • y i) (∑ i, op (w i) • y i))) :
    algebraMap ℝ (CStarMatrix ι ι A) C⁻¹ ≤ CStarMatrix.gram A y := by
  rw [CStarMatrix.algebraMap_le_iff_forall_sum_le]; intro a
  let w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm a
  have hw : ∑ i, star (a i) * a i = unop (inner Aᵐᵒᵖ w w) := by
    simp [WithCStarModule.pi_inner, Finset.unop_sum, w]
  rw [hw, CStarMatrix.sum_star_mul_gram_mul, inv_smul_le_iff_of_pos hC]; exact hbound w

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E]
  [CStarModule Aᵐᵒᵖ E] [CompleteSpace E]

private theorem isStrictlyPositive_gram_splitting {ι E' : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [Module Aᵐᵒᵖ E'] [CStarModule Aᵐᵒᵖ E']
    [CompleteSpace E'] (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E')
    (g : E' →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) (hfg : f ∘ₗ g = LinearMap.id) :
    IsStrictlyPositive (CStarMatrix.gram A (splittingFamily f g)) := by
  have : IsScalarTower ℂ Aᵐᵒᵖ E' := CStarModule.isScalarTower Aᵐᵒᵖ E'
  have : IsScalarTower ℂ Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := CStarModule.isScalarTower _ _
  let gL : E' →L[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
    ⟨g.restrictScalars ℂ, f.continuous_rightInverse_of_comp_eq_id_of_finite_pi_cstarModule g hfg⟩
  have hC : (0 : ℝ) < 2 * (1 + ‖gL‖ ^ 2) := by positivity
  refine (isStrictlyPositive_algebraMap (inv_pos.mpr hC)).of_le <|
    algebraMap_inv_le_gram_of_le_smul _ hC fun w ↦ ?_
  have hw_sum : ∑ i, op (w i) • splittingFamily f g i = splittingMap f g w := by
    simp_rw [splittingFamily, ← map_smul, ← map_sum, stdBasis,
      WithCStarModule.sum_op_smul_single_one]
  rw [hw_sum, splittingMap_apply f g w, WithCStarModule.prod_inner, WithCStarModule.equiv_symm_fst,
    WithCStarModule.equiv_symm_snd, unop_add]
  set u := unop (inner Aᵐᵒᵖ (f w) (f w)); set v := unop (inner Aᵐᵒᵖ (w - g (f w)) (w - g (f w)))
  have hg_le : unop (inner Aᵐᵒᵖ (g (f w)) (g (f w))) ≤ ‖gL‖ ^ 2 • u :=
    gL.unop_inner_map_map_le_norm_sq_smul (fun b z ↦ g.map_smul (op b) z) (f w)
  have hw_split : unop (inner Aᵐᵒᵖ w w) ≤ (2 : ℝ) • (‖gL‖ ^ 2 • u + v) := by
    have hadd := unop_inner_add_add_self_le (A := A) (g (f w)) (w - g (f w))
    rw [add_sub_cancel] at hadd
    exact hadd.trans
      ((nsmul_le_nsmul_right (add_le_add hg_le (le_refl v)) 2).trans_eq (by simp only [two_smul]))
  have hu : 0 ≤ u := unop_nonneg.mpr CStarModule.inner_self_nonneg
  have hv : 0 ≤ v :=
    unop_nonneg.mpr (CStarModule.inner_self_nonneg (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)))
  have hCu : ‖gL‖ ^ 2 • u + v ≤ (1 + ‖gL‖ ^ 2) • (u + v) :=
    (add_le_add (le_add_of_nonneg_left hu)
      (le_add_of_nonneg_right (smul_nonneg (sq_nonneg _) hv))).trans_eq
      (by rw [add_add_add_comm, add_smul, one_smul, smul_add])
  exact hw_split.trans
    ((smul_le_smul_of_nonneg_left hCu zero_le_two).trans_eq (mul_smul _ _ _).symm)

/-- Any complete right Hilbert `A`-module `E` that splits as a right `A`-linear retract of
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` (`f ∘ₗ g = LinearMap.id`) admits an `ι`-indexed Parseval frame. -/
theorem exists_isParsevalFrame_of_comp_eq_id {ι : Type*} [Fintype ι]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))
    (hfg : f ∘ₗ g = LinearMap.id) : ∃ x : ι → E, IsParsevalFrame Aᵐᵒᵖ x := by
  classical
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  obtain ⟨B, S, hgram_η, hy_recover⟩ :=
    CStarMatrix.exists_gram_eq_one_of_isStrictlyPositive (A := A) (y := splittingFamily f g)
      (isStrictlyPositive_gram_splitting f g hfg)
  let η : ι → C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
    fun j ↦ ∑ k, op (B k j) • splittingFamily f g k
  let x : ι → E := fun j ↦ ∑ k, op (B k j) • f (stdBasis A ι k)
  let π_fst : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) →ₗ[Aᵐᵒᵖ] E :=
    LinearMap.fst Aᵐᵒᵖ _ _ ∘ₗ (WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ _).toLinearMap
  have hπ_fst (w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))) : π_fst w = w.fst := by simp [π_fst]
  have hη_fst (j : ι) : (η j).fst = x j := by
    rw [← hπ_fst, map_sum]; simp [hπ_fst, splittingFamily, splittingMap_apply, x]
  refine ⟨x, isParsevalFrame_iff.mpr fun z ↦ ?_⟩
  let u₀ : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) := (WithCStarModule.equiv Aᵐᵒᵖ _).symm (z, 0)
  have hfg_z : f (g z) = z := LinearMap.congr_fun hfg z
  have hu₀_eq : splittingMap f g (g z) = u₀ := by
    rw [splittingMap_apply, hfg_z, sub_self]
  have hu₀_span : ∃ c : ι → A, ∑ j, op (c j) • η j = u₀ := ⟨fun j ↦ ∑ k, S j k * g z k, by
    calc ∑ j, op (∑ k, S j k * g z k) • η j
        = ∑ k, op (g z k) • ∑ j, op (S j k) • η j := by
            simp_rw [Finset.op_sum, Finset.sum_smul, op_mul, mul_smul, Finset.smul_sum]
            exact Finset.sum_comm
      _ = splittingMap f g (∑ k, op (g z k) • stdBasis A ι k) := by
            simp_rw [η, hy_recover, splittingFamily, ← map_smul, ← map_sum]
      _ = u₀ := by
            simp_rw [stdBasis]
            rw [WithCStarModule.sum_op_smul_single_one, hu₀_eq]⟩
  have hu₀_rec : ∑ i, inner Aᵐᵒᵖ (η i) u₀ • η i = u₀ :=
    TauCeti.CStarMatrix.sum_inner_smul_of_gram_eq_one hgram_η hu₀_span
  have hinner_x (i : ι) : inner Aᵐᵒᵖ (x i) z = inner Aᵐᵒᵖ (η i) u₀ := by
    rw [WithCStarModule.prod_inner]; simp [u₀, hη_fst]
  calc ∑ i, inner Aᵐᵒᵖ (x i) z • x i
      = π_fst (∑ i, inner Aᵐᵒᵖ (η i) u₀ • η i) := by
          simp_rw [hinner_x, map_sum, map_smul, hπ_fst, hη_fst]
    _ = z := by rw [hu₀_rec, hπ_fst, WithCStarModule.equiv_symm_fst]

end LinearMap

namespace TauCeti.CStarModule

/-! ### Polar decomposition -/

section Polar

/-- Matrix `CStarMatrix.gram A (fun i ↦ T (x i)) + (1 - CStarMatrix.gram A x)` in
`CStarMatrix ι ι A` for a family `x : ι → E` and a function `T : E → F`. When `x` is a Parseval
frame and `T` is right `A`-linear, this represents `T* T ⊕ 1` on `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` with
the identity on the complementary summand `ker (CStarMatrix.gram A x)`. -/
def polarMatrix (A : Type*) {ι E F : Type*} [DecidableEq ι] [AddGroupWithOne A] [Inner Aᵐᵒᵖ E]
    [Inner Aᵐᵒᵖ F] (x : ι → E) (T : E → F) : CStarMatrix ι ι A :=
  CStarMatrix.gram A (fun i ↦ T (x i)) + (1 - CStarMatrix.gram A x)

section PolarBasic

variable {A ι E F : Type*} [DecidableEq ι] [AddGroupWithOne A] [Inner Aᵐᵒᵖ E] [Inner Aᵐᵒᵖ F]

theorem polarMatrix_def (x : ι → E) (T : E → F) :
    polarMatrix A x T = CStarMatrix.gram A (fun i ↦ T (x i)) + (1 - CStarMatrix.gram A x) := (rfl)

@[simp] theorem polarMatrix_apply (x : ι → E) (T : E → F) (i j : ι) : polarMatrix A x T i j =
    unop (inner Aᵐᵒᵖ (T (x i)) (T (x j))) + (1 - CStarMatrix.gram A x) i j := by
  simp [polarMatrix_def]

end PolarBasic

/-- Over a unital C⋆-algebra, for a Parseval frame `x` and an arbitrary function `T : E → F`,
`polarMatrix A x T` is positive (`0 ≤ polarMatrix A x T`). -/
theorem _root_.CStarModule.IsParsevalFrame.polarMatrix_nonneg {A ι E F : Type*} [Fintype ι]
    [DecidableEq ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]
    [AddCommGroup F] [Module ℂ F] [SMul Aᵐᵒᵖ F] [Norm F] [CStarModule Aᵐᵒᵖ F]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E → F) : 0 ≤ polarMatrix A x T :=
  add_nonneg (CStarMatrix.gram_nonneg _) (CStarMatrix.isStarProjection_gram hx).one_sub.nonneg

section PolarAlg

variable {A ι E F 𝓕 : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [StarRing A]
  [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ] [AddCommGroup E] [Module ℂ E]
  [Module Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E] [AddCommGroup F] [Module ℂ F] [Module Aᵐᵒᵖ F]
  [Norm F] [CStarModule Aᵐᵒᵖ F] [FunLike 𝓕 E F] [LinearMapClass 𝓕 Aᵐᵒᵖ E F]

/-- When `T` is right `A`-linear, multiplying `polarMatrix A x T` on the right by the Gram
projection `CStarMatrix.gram A x` isolates the Gram matrix of `T ∘ x`:
`polarMatrix A x T * CStarMatrix.gram A x = CStarMatrix.gram A (fun i ↦ T (x i))`. -/
theorem _root_.CStarModule.IsParsevalFrame.polarMatrix_mul_gram {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : 𝓕) :
    polarMatrix A x T * CStarMatrix.gram A x = CStarMatrix.gram A (fun i ↦ T (x i)) := by
  rw [polarMatrix_def, add_mul, (CStarMatrix.isStarProjection_gram hx).one_sub_mul_self, add_zero]
  ext i j
  conv_rhs => rw [CStarMatrix.gram_apply, ← hx.sum_inner_smul (x j), map_sum, inner_sum_right']
  simp [CStarMatrix.mul_apply, map_smul, Finset.unop_sum]

/-- When `T` is right `A`-linear, `polarMatrix A x T` commutes with the Gram projection
`CStarMatrix.gram A x`, so functional-calculus operations on `polarMatrix A x T` preserve the
Gram range. -/
theorem _root_.CStarModule.IsParsevalFrame.commute_polarMatrix_gram {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : 𝓕) : Commute (polarMatrix A x T) (CStarMatrix.gram A x) :=
  IsSelfAdjoint.commute_of_mul_eq_isSelfAdjoint _ _ _
    ((TauCeti.CStarMatrix.isSelfAdjoint_gram _).add
      (CStarMatrix.isStarProjection_gram hx).one_sub.isSelfAdjoint)
    (CStarMatrix.isStarProjection_gram hx).isSelfAdjoint (TauCeti.CStarMatrix.isSelfAdjoint_gram _)
    (hx.polarMatrix_mul_gram T)

end PolarAlg

variable {A ι E F : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [SeminormedAddCommGroup F] [NormedSpace ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

omit [StarOrderedRing A] in
private theorem opSynthesis_mulVec_comp_eq_id [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) {M N : CStarMatrix ι ι A} (hMN : M * N = 1)
    (hcomm : Commute N (CStarMatrix.gram A x)) :
    (opSynthesisLinearMap A x ∘ₗ mulVecLinearMap M ∘ₗ opAnalysisLinearMap A x) ∘ₗ
      (opSynthesisLinearMap A x ∘ₗ mulVecLinearMap N ∘ₗ opAnalysisLinearMap A x) =
      LinearMap.id := by
  have hmul : M * (CStarMatrix.gram A x * N) = CStarMatrix.gram A x := by
    rw [← hcomm.eq, ← mul_assoc, hMN, one_mul]
  ext z
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [← LinearMap.comp_apply (f := opAnalysisLinearMap A x),
    opAnalysisLinearMap_comp_opSynthesisLinearMap,
    CStarMatrix.mulVecLinearMap_mulVecLinearMap,
    CStarMatrix.mulVecLinearMap_mulVecLinearMap, mul_assoc M, hmul,
    ← opAnalysisLinearMap_comp_opSynthesisLinearMap, LinearMap.comp_apply]
  simp_rw [← LinearMap.comp_apply (f := opSynthesisLinearMap A x),
    opSynthesisLinearMap_comp_opAnalysisLinearMap hx, LinearMap.id_apply]

variable [CompleteSpace F]

/-- When `x : ι → E` is a Parseval frame and `T : E ≃ₗ[Aᵐᵒᵖ] F` is a right `A`-linear
equivalence into a complete right Hilbert `A`-module `F`, `polarMatrix A x T` is strictly positive
in `CStarMatrix ι ι A`. -/
theorem _root_.CStarModule.IsParsevalFrame.isStrictlyPositive_polarMatrix [DecidableEq ι]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    IsStrictlyPositive (polarMatrix A x T) := by
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] F := T.toLinearMap ∘ₗ opSynthesisLinearMap A x
  let g : F →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) := opAnalysisLinearMap A x ∘ₗ T.symm.toLinearMap
  have hfg : f ∘ₗ g = LinearMap.id := LinearMap.ext fun w ↦ by
    simpa [f, g, LinearMap.comp_apply] using congrArg T
      (LinearMap.congr_fun (opSynthesisLinearMap_comp_opAnalysisLinearMap hx) (T.symm w))
  suffices polarMatrix A x T = CStarMatrix.gram A (LinearMap.splittingFamily f g) from
    this ▸ LinearMap.isStrictlyPositive_gram_splitting f g hfg
  set p := CStarMatrix.gram A x with hp_def
  let e := LinearMap.stdBasis A ι
  have hfe (i : ι) : f (e i) = T (x i) := by
    dsimp [e, LinearMap.stdBasis]
    rw [LinearMap.comp_apply, opSynthesisLinearMap_single_one, LinearEquiv.coe_coe]
  have h1p (i : ι) : mulVecCLM (1 - p) (e i) = e i - g (f (e i)) := by
    rw [hfe, ← CStarMatrix.coe_mulVecLinearMap, map_sub, LinearMap.sub_apply,
      CStarMatrix.mulVecLinearMap_one, LinearMap.id_apply, hp_def,
      ← opAnalysisLinearMap_comp_opSynthesisLinearMap, LinearMap.comp_apply]
    dsimp [e, LinearMap.stdBasis]
    rw [opSynthesisLinearMap_single_one]
    simp [g]
  have hy_fst (i : ι) : (LinearMap.splittingFamily f g i).fst = T (x i) := by
    simp [LinearMap.splittingFamily, LinearMap.splittingMap_apply, hfe, e]
  have hy_snd (i : ι) : (LinearMap.splittingFamily f g i).snd = mulVecCLM (1 - p) (e i) := by
    rw [h1p]; simp [LinearMap.splittingFamily, LinearMap.splittingMap_apply, e]
  have h1p_gram : CStarMatrix.gram A (fun j ↦ mulVecCLM (1 - p) (e j)) = 1 - p := by
    dsimp only [e, LinearMap.stdBasis]
    rw [CStarMatrix.gram_mulVecCLM_single_one, ← CStarMatrix.star_eq_conjTranspose,
      (CStarMatrix.isStarProjection_gram hx).one_sub.isSelfAdjoint.star_eq,
      (CStarMatrix.isStarProjection_gram hx).one_sub.isIdempotentElem.eq]
  ext i j
  rw [polarMatrix_apply, ← hp_def, CStarMatrix.gram_apply, WithCStarModule.prod_inner, unop_add,
    hy_fst, hy_fst, hy_snd, hy_snd,
    ← CStarMatrix.gram_apply (A := A) (x := fun k ↦ mulVecCLM (1 - p) (e k)), h1p_gram]

theorem _root_.CStarModule.IsParsevalFrame.isUnit_sqrt_polarMatrix [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) : IsUnit (CFC.sqrt (polarMatrix A x T)) :=
  have : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  (hx.isStrictlyPositive_polarMatrix T).isUnit_cfcSqrt _

/-- Positive self-adjoint modulus `|T| : E ≃ₗ[Aᵐᵒᵖ] E` of `T : E ≃ₗ[Aᵐᵒᵖ] F` into a complete right
Hilbert `A`-module `F`. -/
noncomputable def _root_.CStarModule.IsParsevalFrame.polarModulus {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) : E ≃ₗ[Aᵐᵒᵖ] E :=
  letI := Classical.decEq ι
  let S := CFC.sqrt (polarMatrix A x T)
  LinearEquiv.ofLinearMap
    ((opSynthesisLinearMap A x).comp ((mulVecLinearMap S).comp (opAnalysisLinearMap A x)))
    ((opSynthesisLinearMap A x).comp
      ((mulVecLinearMap (Ring.inverse S)).comp (opAnalysisLinearMap A x)))
    (opSynthesis_mulVec_comp_eq_id hx (Ring.mul_inverse_cancel S (hx.isUnit_sqrt_polarMatrix T))
      (by rw [Ring.inverse_of_isUnit (hx.isUnit_sqrt_polarMatrix T)]
          exact Commute.units_inv_left <| (hx.commute_polarMatrix_gram T).cfcₙ_nnreal NNReal.sqrt))
    (opSynthesis_mulVec_comp_eq_id hx (Ring.inverse_mul_cancel S (hx.isUnit_sqrt_polarMatrix T))
      ((hx.commute_polarMatrix_gram T).cfcₙ_nnreal NNReal.sqrt))

private theorem op_polarModulus_apply [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarModulus T z = opSynthesisLinearMap A x
      (mulVecCLM (CFC.sqrt (polarMatrix A x T)) (opAnalysisLinearMap A x z)) := by
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  simp [_root_.CStarModule.IsParsevalFrame.polarModulus]

theorem _root_.CStarModule.IsParsevalFrame.polarModulus_apply [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarModulus T z =
      ∑ i, (∑ j, inner Aᵐᵒᵖ (x j) z * op (CFC.sqrt (polarMatrix A x T) i j)) • x i := by
  rw [op_polarModulus_apply hx T z]
  simp [CStarMatrix.mulVecCLM_apply_apply, Finset.op_sum, op_mul]

theorem _root_.CStarModule.IsParsevalFrame.polarModulus_symm_apply [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    (hx.polarModulus T).symm z =
      ∑ i, (∑ j, inner Aᵐᵒᵖ (x j) z *
        op (Ring.inverse (CFC.sqrt (polarMatrix A x T)) i j)) • x i := by
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  simp [_root_.CStarModule.IsParsevalFrame.polarModulus, Finset.op_sum, op_mul]

/-- `hx.polarModulus T` is self-adjoint as a module operator on `E`. -/
theorem _root_.CStarModule.IsParsevalFrame.isAdjointPair_polarModulus {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (hx.polarModulus T) (hx.polarModulus T) := by
  classical
  rw [isAdjointPair_inner_iff]; intro y z
  rw [op_polarModulus_apply hx T y, op_polarModulus_apply hx T z, inner_opSynthesisLinearMap_left,
    (CStarMatrix.isAdjointPair_mulVecCLM_star _).inner_eq_cstarModule,
    (CFC.sqrt_nonneg (polarMatrix A x T)).isSelfAdjoint.star_eq,
    ← inner_opSynthesisLinearMap_right]

/-- `hx.polarModulus T` is positive: `0 ≤ ⟨z, |T| z⟩_A` for all `z : E`. -/
theorem _root_.CStarModule.IsParsevalFrame.inner_polarModulus_right_nonneg {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    0 ≤ inner Aᵐᵒᵖ z (hx.polarModulus T z) := by
  classical
  rw [op_polarModulus_apply hx T z]
  set S := CFC.sqrt (polarMatrix A x T); set R := CFC.sqrt S
  have hRR (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) : mulVecCLM S v = mulVecCLM (star R) (mulVecCLM R v) := by
    rw [(CFC.sqrt_nonneg S).isSelfAdjoint.star_eq, CStarMatrix.mulVecCLM_mulVecCLM,
      CFC.sqrt_mul_sqrt_self S (CFC.sqrt_nonneg _)]
  rw [inner_opSynthesisLinearMap_right, hRR,
    ← (CStarMatrix.isAdjointPair_mulVecCLM_star R).inner_eq_cstarModule]
  exact CStarModule.inner_self_nonneg (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))

/-- `hx.polarModulus T` has the same Gram inner products as `T`:
`⟨|T| y, |T| z⟩_A = ⟨T y, T z⟩_A`. -/
@[simp]
theorem _root_.CStarModule.IsParsevalFrame.inner_polarModulus_polarModulus {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (y z : E) :
    inner Aᵐᵒᵖ (hx.polarModulus T y) (hx.polarModulus T z) = inner Aᵐᵒᵖ (T y) (T z) := by
  classical
  apply unop_injective; rw [op_polarModulus_apply hx T y, op_polarModulus_apply hx T z]
  set S := CFC.sqrt (polarMatrix A x T)
  have hSpS : S * CStarMatrix.gram A x * S = CStarMatrix.gram A (fun i ↦ T (x i)) := by
    have hcomm : Commute S (CStarMatrix.gram A x) :=
      (hx.commute_polarMatrix_gram T).cfcₙ_nnreal NNReal.sqrt
    rw [mul_assoc, ← hcomm.eq, ← mul_assoc, CFC.sqrt_mul_sqrt_self _ (hx.polarMatrix_nonneg T),
      hx.polarMatrix_mul_gram T]
  have hcomp (w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
      opAnalysisLinearMap A x (opSynthesisLinearMap A x w) =
        mulVecCLM (CStarMatrix.gram A x) w := by
    rw [← CStarMatrix.coe_mulVecLinearMap, ← opAnalysisLinearMap_comp_opSynthesisLinearMap,
      LinearMap.comp_apply]
  rw [inner_opSynthesisLinearMap_left, hcomp,
    (CStarMatrix.isAdjointPair_mulVecCLM_star S).inner_eq_cstarModule,
    (CFC.sqrt_nonneg (polarMatrix A x T)).isSelfAdjoint.star_eq,
    CStarMatrix.mulVecCLM_mulVecCLM, CStarMatrix.mulVecCLM_mulVecCLM, hSpS]
  have hT (w : E) : ∑ i, op (opAnalysisLinearMap A x w i) • T (x i) = T w := by
    conv_rhs => rw [← hx.sum_inner_smul w, map_sum]
    simp
  have hquad := CStarMatrix.sum_star_mul_gram_mul (A := A) (fun i ↦ T (x i))
    (opAnalysisLinearMap A x y) (opAnalysisLinearMap A x z)
  rw [hT y, hT z] at hquad
  simpa [WithCStarModule.pi_inner, Finset.unop_sum, CStarMatrix.mulVecCLM_apply_apply,
    Finset.mul_sum, mul_assoc] using hquad

/-- The square of `hx.polarModulus T` equals `T* ∘ T`:
`|T| (|T| z) = frameAdjoint Aᵐᵒᵖ x T (T z)`. -/
theorem _root_.CStarModule.IsParsevalFrame.polarModulus_polarModulus_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarModulus T (hx.polarModulus T z) = frameAdjoint Aᵐᵒᵖ x T (T z) :=
  ext_inner_left (A := Aᵐᵒᵖ) fun y ↦ by
    rw [← (hx.isAdjointPair_polarModulus T).inner_eq_cstarModule,
      hx.inner_polarModulus_polarModulus T y z,
      (hx.isAdjointPair_frameAdjoint T).inner_eq_cstarModule]

/-- Uniqueness of the positive self-adjoint modulus: any map `P : E → E` that is symmetric for
`⟪·, ·⟫_{Aᵐᵒᵖ}`, positive (`0 ≤ ⟪z, P z⟫_{Aᵐᵒᵖ}`), and satisfies `⟪P y, P z⟫ = ⟪T y, T z⟫`
agrees pointwise with `hx.polarModulus T`. -/
theorem _root_.CStarModule.IsParsevalFrame.eq_polarModulus_of_inner_eq {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (P : E → E)
    (hP_sa : ∀ y z : E, inner Aᵐᵒᵖ (P y) z = inner Aᵐᵒᵖ y (P z))
    (hP_nonneg : ∀ z : E, 0 ≤ inner Aᵐᵒᵖ z (P z))
    (hP_inner : ∀ y z : E, inner Aᵐᵒᵖ (P y) (P z) = inner Aᵐᵒᵖ (T y) (T z)) (z : E) :
    P z = hx.polarModulus T z := by
  have : CompleteSpace E := hx.completeSpace
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let P_op : AdjointableMap Aᵐᵒᵖ E E := AdjointableMap.ofAdjointPair P P hP_sa
  let M_op : AdjointableMap Aᵐᵒᵖ E E := AdjointableMap.ofAdjointPair
    (hx.polarModulus T) (hx.polarModulus T) (hx.isAdjointPair_polarModulus T).inner_eq_cstarModule
  let T_op : AdjointableMap Aᵐᵒᵖ E F := AdjointableMap.ofAdjointPair
    T (frameAdjoint Aᵐᵒᵖ x T) (hx.isAdjointPair_frameAdjoint T).inner_eq_cstarModule
  have hP_pos : 0 ≤ P_op := AdjointableMap.nonneg_iff_forall_inner_nonneg.mpr fun w ↦ by
    simpa [P_op] using hP_nonneg w
  have hM_pos : 0 ≤ M_op := AdjointableMap.nonneg_iff_forall_inner_nonneg.mpr fun w ↦ by
    simpa [M_op] using hx.inner_polarModulus_right_nonneg T w
  have hsq (S_op : AdjointableMap Aᵐᵒᵖ E E)
      (hS : ∀ u v : E, inner Aᵐᵒᵖ (S_op u) (S_op v) = inner Aᵐᵒᵖ (T_op u) (T_op v)) :
      S_op.adjoint.comp S_op = T_op.adjoint.comp T_op := by
    refine AdjointableMap.ext fun v ↦ ext_inner_left (A := Aᵐᵒᵖ) fun u ↦ ?_
    rw [AdjointableMap.comp_apply, S_op.adjoint_inner_right, hS u v,
      ← T_op.adjoint_inner_right, ← AdjointableMap.comp_apply]
  have hP_sq := hsq P_op fun u v ↦ by simpa [P_op, T_op] using hP_inner u v
  have hM_sq := hsq M_op fun u v ↦ by simp [M_op, T_op]
  have hPM : P_op = M_op := calc
    P_op = P_op.abs := (AdjointableMap.abs_of_nonneg hP_pos).symm
    _ = CFC.sqrt (P_op.abs * P_op.abs) := (CFC.sqrt_mul_self _ (AdjointableMap.abs_nonneg _)).symm
    _ = CFC.sqrt (T_op.adjoint.comp T_op) := by rw [AdjointableMap.abs_mul_abs, hP_sq]
    _ = CFC.sqrt (M_op.abs * M_op.abs) := by rw [← hM_sq, ← AdjointableMap.abs_mul_abs]
    _ = M_op.abs := CFC.sqrt_mul_self _ (AdjointableMap.abs_nonneg _)
    _ = M_op := AdjointableMap.abs_of_nonneg hM_pos
  simpa [P_op, M_op] using congrArg (fun (f : AdjointableMap Aᵐᵒᵖ E E) ↦ f z) hPM

/-- A positive self-adjoint `Aᵐᵒᵖ`-linear endomorphism `P : E →ₗ[Aᵐᵒᵖ] E` satisfying
`P ∘ₗ P = (frameAdjoint Aᵐᵒᵖ x T).comp T.toLinearMap` equals `(hx.polarModulus T).toLinearMap`. -/
theorem _root_.CStarModule.IsParsevalFrame.eq_polarModulus_toLinearMap {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (P : E →ₗ[Aᵐᵒᵖ] E)
    (hP_sa : LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip P P)
    (hP_nonneg : ∀ z : E, 0 ≤ inner Aᵐᵒᵖ z (P z))
    (hP_sq : P.comp P = (frameAdjoint Aᵐᵒᵖ x T).comp T.toLinearMap) :
    P = (hx.polarModulus T).toLinearMap := by
  refine LinearMap.ext fun z ↦ hx.eq_polarModulus_of_inner_eq T P
    (isAdjointPair_inner_iff.mp hP_sa) hP_nonneg (fun u v ↦ ?_) z
  rw [(isAdjointPair_inner_iff.mp hP_sa) u (P v), ← LinearMap.comp_apply, hP_sq,
    LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← (hx.isAdjointPair_frameAdjoint T).inner_eq_cstarModule]

/-- `hx.polarModulus T` is independent of the choice of finite Parseval frame `x` (even across
different finite index types). -/
theorem _root_.CStarModule.IsParsevalFrame.polarModulus_eq {κ : Type*} [Fintype κ]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F)
    {y : κ → E} (hy : IsParsevalFrame Aᵐᵒᵖ y) :
    hx.polarModulus T = hy.polarModulus T :=
  LinearEquiv.ext fun z ↦ (hx.eq_polarModulus_of_inner_eq T (hy.polarModulus T)
    (hy.isAdjointPair_polarModulus T).inner_eq_cstarModule
    (hy.inner_polarModulus_right_nonneg T) (hy.inner_polarModulus_polarModulus T) z).symm

/-- Polar unitary `U = T ∘ |T|⁻¹ : E ≃ₗᵢ[Aᵐᵒᵖ] F` of a right `A`-linear equivalence
`T : E ≃ₗ[Aᵐᵒᵖ] F` into a complete right Hilbert `A`-module `F`. -/
noncomputable def _root_.CStarModule.IsParsevalFrame.polarUnitary {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) : E ≃ₗᵢ[Aᵐᵒᵖ] F :=
  ((hx.polarModulus T).symm.trans T).isometryOfInnerCStarModule fun z ↦ by
    simp only [LinearEquiv.trans_apply]
    rw [← hx.inner_polarModulus_polarModulus T, LinearEquiv.apply_symm_apply]

theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarUnitary T z = T ((hx.polarModulus T).symm z) := by
  simp [_root_.CStarModule.IsParsevalFrame.polarUnitary]

theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_symm_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (w : F) :
    (hx.polarUnitary T).symm w = hx.polarModulus T (T.symm w) := by
  simp [_root_.CStarModule.IsParsevalFrame.polarUnitary]

/-- The polar decomposition factorization `T = U ∘ |T|`: applying `hx.polarUnitary T` after
`hx.polarModulus T` recovers `T`. -/
@[simp] theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarUnitary T (hx.polarModulus T z) = T z := by
  simp [_root_.CStarModule.IsParsevalFrame.polarUnitary]

@[simp] theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_symm_map {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    (hx.polarUnitary T).symm (T z) = hx.polarModulus T z := by
  rw [hx.polarUnitary_symm_apply, T.symm_apply_apply]

/-- `hx.polarUnitary T` is independent of the choice of finite Parseval frame `x` (even across
different finite index types). -/
theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_eq {κ : Type*} [Fintype κ]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F)
    {y : κ → E} (hy : IsParsevalFrame Aᵐᵒᵖ y) :
    hx.polarUnitary T = hy.polarUnitary T := by
  ext z
  rw [hx.polarUnitary_apply, hy.polarUnitary_apply, hx.polarModulus_eq T hy]

end Polar

end TauCeti.CStarModule
