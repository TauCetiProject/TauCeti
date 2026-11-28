/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Frame
public import TauCeti.Analysis.CStarAlgebra.Module.FiniteFree
public import TauCeti.Analysis.CStarAlgebra.Module.Matrix
public import TauCeti.Analysis.CStarAlgebra.Module.Submodule

/-!
# Gram-projection coordinate models and retract splitting

For a right Hilbert `A`-module `E` (`CStarModule Aᵐᵒᵖ E`, with right action `x a = op a • x` and
`⟨x, y⟩_A = unop (inner Aᵐᵒᵖ x y)`), this file builds on the finite Parseval frame API in
`TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Frame` and automatic continuity in
`TauCeti.Analysis.CStarAlgebra.Module.FiniteFree` to establish:

* Over a unital C⋆-algebra `A`, Parseval frames correspond unitarily to projection-cutdown modules
  `LinearMap.range (CStarMatrix.mulVecLinearMap p)` (`CStarModule.IsParsevalFrame.equivRangeGram`,
  `IsStarProjection.exists_isParsevalFrame_and_gram_eq`, and
  `exists_isParsevalFrame_iff_exists_isStarProjection_and_nonempty_linearIsometryEquiv` in
  `TauCeti.CStarModule`).
* Every complete right `A`-linear retract of `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` admits an `ι`-indexed Parseval
  frame (`LinearMap.exists_isParsevalFrame_of_comp_eq_id`, applied downstream in
  `TauCeti.Analysis.CStarAlgebra.Module.Projective` to finitely generated projective modules).

## Main declarations

* `CStarModule.IsParsevalFrame.equivRangeGram`,
  `IsStarProjection.exists_isParsevalFrame_and_gram_eq`,
  `exists_isParsevalFrame_iff_exists_isStarProjection_and_nonempty_linearIsometryEquiv`
* `LinearMap.exists_isParsevalFrame_of_comp_eq_id`

## References

* M. Frank and D. R. Larson, *Frames in Hilbert C⋆-modules and C⋆-algebras*, J. Operator Theory 48
  (2002), 273–314.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 1–4.
* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Chapter 2.
* J. Roe, *Lectures on K-Theory and Operator Algebras*, Proposition 10.2.
-/

public section

open MulOpposite Matrix CStarModule TauCeti
open CStarMatrix (mulVecCLM mulVecLinearMap)
open scoped WithCStarModule

/-! ### Unital coefficient algebras: projection comparison -/

namespace TauCeti.CStarModule

section Unital

private def piOpEquiv (A ι : Type*) [Ring A] :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) ≃ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → Aᵐᵒᵖ) :=
  (TauCeti.WithCStarModule.piOpLinearEquiv A ι).trans
    (_root_.WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ (ι → Aᵐᵒᵖ)).symm

@[simp]
private theorem piOpEquiv_apply {A ι : Type*} [Ring A] (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) (i : ι) :
    piOpEquiv A ι v i = op (v i) := by
  simp [piOpEquiv]

@[simp]
private theorem piOpEquiv_symm_apply {A ι : Type*} [Ring A] (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → Aᵐᵒᵖ))
    (i : ι) : (piOpEquiv A ι).symm v i = unop (v i) := by
  simp [piOpEquiv]

private theorem inner_piOpEquiv {A ι : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (v w : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    inner Aᵐᵒᵖ (piOpEquiv A ι v) (piOpEquiv A ι w) = inner Aᵐᵒᵖ v w := by
  simp [WithCStarModule.pi_inner, CStarModule.inner_op_op]

private noncomputable def adjointableToLinearMap {A E F : Type*} [Ring A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Module A F] [CStarModule A F]
    (T : AdjointableMap A E F) : E →ₗ[A] F where
  toFun := T
  map_add' := map_add T
  map_smul' := T.map_smul_coeff

@[simp]
private theorem adjointableToLinearMap_apply {A E F : Type*} [Ring A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] [PartialOrder A] [Norm A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module A E] [CStarModule A E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Module A F] [CStarModule A F]
    (T : AdjointableMap A E F) (x : E) :
    adjointableToLinearMap T x = T x := (rfl)

private noncomputable def opSynthesisLinearMap (A : Type*) {ι E : Type*} [Fintype ι]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
    (x : ι → E) : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E :=
  (adjointableToLinearMap (AdjointableMap.synthesis Aᵐᵒᵖ x)).comp (piOpEquiv A ι).toLinearMap

@[simp]
private theorem opSynthesisLinearMap_apply {A ι E : Type*} [Fintype ι] [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    opSynthesisLinearMap A x v = ∑ i, op (v i) • x i := by
  simp [opSynthesisLinearMap]

private noncomputable def opAnalysisLinearMap (A : Type*) {ι E : Type*} [Fintype ι]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
    (x : ι → E) : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
  (piOpEquiv A ι).symm.toLinearMap.comp (adjointableToLinearMap (AdjointableMap.analysis Aᵐᵒᵖ x))

@[simp]
private theorem opAnalysisLinearMap_apply_apply {A ι E : Type*} [Fintype ι] [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] (x : ι → E) (z : E) (i : ι) :
    opAnalysisLinearMap A x z i = unop (inner Aᵐᵒᵖ (x i) z) := by
  simp [opAnalysisLinearMap]

private theorem opSynthesisLinearMap_opAnalysisLinearMap {A ι E : Type*} [Fintype ι]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (z : E) :
    opSynthesisLinearMap A x (opAnalysisLinearMap A x z) = z := by
  simpa [opSynthesisLinearMap, opAnalysisLinearMap] using
    congrArg (fun S : AdjointableMap Aᵐᵒᵖ E E ↦ S z) hx.synthesis_comp_analysis_eq_id

private theorem opAnalysisLinearMap_opSynthesisLinearMap {A ι E : Type*} [Fintype ι]
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
    (x : ι → E) (v : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :
    opAnalysisLinearMap A x (opSynthesisLinearMap A x v) =
      mulVecLinearMap (CStarMatrix.gram A x) v := by
  ext i
  simp [opSynthesisLinearMap, opAnalysisLinearMap]

private theorem range_opAnalysisLinearMap {A ι E : Type*} [Fintype ι] [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E] {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) :
    LinearMap.range (opAnalysisLinearMap A x) =
      LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    refine ⟨opAnalysisLinearMap A x z, ?_⟩
    rw [← opAnalysisLinearMap_opSynthesisLinearMap, opSynthesisLinearMap_opAnalysisLinearMap hx]
  · have hcomp : (opAnalysisLinearMap A x).comp (opSynthesisLinearMap A x) =
        mulVecLinearMap (CStarMatrix.gram A x) :=
      LinearMap.ext (opAnalysisLinearMap_opSynthesisLinearMap x)
    rw [← hcomp]
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
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let S := LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x))
  have hisom : ∀ z : E,
      inner Aᵐᵒᵖ (opAnalysisLinearMap A x z) (opAnalysisLinearMap A x z) = inner Aᵐᵒᵖ z z := by
    intro z
    calc inner Aᵐᵒᵖ (opAnalysisLinearMap A x z) (opAnalysisLinearMap A x z)
        = inner Aᵐᵒᵖ (piOpEquiv A ι (opAnalysisLinearMap A x z))
            (piOpEquiv A ι (opAnalysisLinearMap A x z)) := (inner_piOpEquiv _ _).symm
      _ = inner Aᵐᵒᵖ (AdjointableMap.analysis Aᵐᵒᵖ x z) (AdjointableMap.analysis Aᵐᵒᵖ x z) := by
            simp [opAnalysisLinearMap]
      _ = inner Aᵐᵒᵖ z z := hx.inner_analysis_analysis z z
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
  rw [opAnalysisLinearMap_opSynthesisLinearMap, CStarMatrix.mulVecLinearMap_mulVecLinearMap,
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
      ext i j
      rw [CStarMatrix.gram_apply, CStarMatrix.gram_apply]
      apply congrArg unop
      dsimp only [x]
      rw [U.symm.inner_map_map_cstarModule, Submodule.coe_inner_cstarModule]
      dsimp only [u]
      rw [CStarMatrix.coe_mulVecLinearMap]
    rw [hU, hp.gram_mulVecCLM_single_one]
  refine ⟨x, isParsevalFrame_iff.mpr fun z ↦ U.toLinearEquiv.injective ?_, hgram⟩
  obtain ⟨v, hv⟩ := (U z).property
  have hUz : mulVecLinearMap p (U z).val = (U z).val := by
    rw [← hv, CStarMatrix.mulVecLinearMap_mulVecLinearMap, hp.isIdempotentElem.eq]
  have hinner (i : ι) : inner Aᵐᵒᵖ (x i) z = op ((U z).val i) := by
    have hsym : U (x i) = u i := U.apply_symm_apply (u i)
    rw [← U.inner_map_map_cstarModule (x i) z, hsym]
    apply unop_injective
    calc unop (inner Aᵐᵒᵖ (u i) (U z))
        = unop (inner Aᵐᵒᵖ (u i : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) (U z).val) :=
            congrArg unop (Submodule.coe_inner_cstarModule _ (u i) (U z))
      _ = unop (inner Aᵐᵒᵖ (mulVecCLM p (e i)) (U z).val) := by
            dsimp only [u]
            rw [CStarMatrix.coe_mulVecLinearMap]
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
isomorphic to `LinearMap.range (CStarMatrix.mulVecLinearMap p)` for a star projection `p`. -/
theorem exists_isParsevalFrame_iff_exists_isStarProjection_and_nonempty_linearIsometryEquiv :
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

variable {A E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [CompleteSpace E]

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
    (CStarMatrix.algebraMap_le_gram_iff (splittingFamily f g)).mpr fun w ↦ ?_
  rw [inv_smul_le_iff_of_pos hC]
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
    TauCeti.CStarMatrix.exists_gram_eq_one_of_isStrictlyPositive (A := A)
      (y := splittingFamily f g) (isStrictlyPositive_gram_splitting f g hfg)
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
