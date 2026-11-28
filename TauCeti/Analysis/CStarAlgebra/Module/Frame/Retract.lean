/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.FiniteFree
public import TauCeti.Analysis.CStarAlgebra.Module.Frame.Operators
public import TauCeti.Analysis.CStarAlgebra.Module.Submodule

/-!
# Gram-projection coordinate models and retract splitting

Over a unital C⋆-algebra `A` and with finite index type `ι`, this file builds on the analysis and
synthesis operators in `TauCeti.Analysis.CStarAlgebra.Module.Frame.Operators` and automatic
continuity in `TauCeti.Analysis.CStarAlgebra.Module.FiniteFree` to establish:

* Parseval frames in a right Hilbert `A`-module `E` correspond unitarily to projection-cutdown
  submodules `LinearMap.range (CStarMatrix.mulVecLinearMap p)`
  (`CStarModule.IsParsevalFrame.equivRangeGram`,
  `IsStarProjection.exists_isParsevalFrame_and_gram_eq`, and
  `exists_isParsevalFrame_iff_exists_isStarProjection_and_nonempty_linearIsometryEquiv`).
* Every complete right `A`-linear retract of `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` admits an `ι`-indexed Parseval
  frame (`LinearMap.exists_isParsevalFrame_of_comp_eq_id`, applied downstream in
  `TauCeti.Analysis.CStarAlgebra.Module.Projective.Basic` to finitely generated projective modules).

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
  let f : E →ₗᵢ[Aᵐᵒᵖ] S :=
    { toLinearMap := (opAnalysisLinearMap A x).codRestrict S fun z ↦ by
        dsimp only [S]
        rw [← range_opAnalysisLinearMap hx]
        exact LinearMap.mem_range_self _ z
      norm_map' := fun z ↦ by
        simpa using ((opAnalysisLinearMap A x).isometryOfInnerCStarModule
          fun w ↦ inner_opAnalysisLinearMap hx w w).norm_map z }
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
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  dsimp only [CStarModule.IsParsevalFrame.equivRangeGram]
  exact opAnalysisLinearMap_apply_apply x z i

@[simp]
theorem _root_.CStarModule.IsParsevalFrame.equivRangeGram_symm_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (u : LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x))) :
    hx.equivRangeGram.symm u = ∑ i, op (u.val i) • x i := by
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  dsimp only [CStarModule.IsParsevalFrame.equivRangeGram]
  exact opSynthesisLinearMap_apply x u.val

/-- The forward map of `hx.equivRangeGram` sends `z` to `opAnalysisLinearMap A x z`. -/
theorem _root_.CStarModule.IsParsevalFrame.coe_equivRangeGram_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [Module Aᵐᵒᵖ E']
    [CStarModule Aᵐᵒᵖ E'] {x : ι → E'} (hx : IsParsevalFrame Aᵐᵒᵖ x) (z : E') :
    (hx.equivRangeGram z : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) = opAnalysisLinearMap A x z := by
  ext i
  rw [hx.coe_equivRangeGram_apply_apply, opAnalysisLinearMap_apply_apply]

/-- The inverse map of `hx.equivRangeGram` sends `u` to `opSynthesisLinearMap A x u.val`. -/
theorem _root_.CStarModule.IsParsevalFrame.equivRangeGram_symm_eq
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [Module Aᵐᵒᵖ E']
    [CStarModule Aᵐᵒᵖ E'] {x : ι → E'} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (u : LinearMap.range (mulVecLinearMap (CStarMatrix.gram A x))) :
    hx.equivRangeGram.symm u = opSynthesisLinearMap A x u.val := by
  rw [hx.equivRangeGram_symm_apply, opSynthesisLinearMap_apply]

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
      _ = unop (inner Aᵐᵒᵖ (e i) (mulVecCLM p.conjTranspose (U z).val)) :=
          congrArg unop
            ((CStarMatrix.isAdjointPair_mulVecCLM_conjTranspose p).inner_eq_cstarModule _ _)
      _ = unop (inner Aᵐᵒᵖ (e i) (U z).val) := by
          rw [← CStarMatrix.star_eq_conjTranspose, hp.isSelfAdjoint.star_eq,
            ← CStarMatrix.coe_mulVecLinearMap, hUz]
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
    (TauCeti.CStarMatrix.algebraMap_le_gram_iff (splittingFamily f g)).mpr fun w ↦ ?_
  rw [inv_smul_le_iff_of_pos hC]
  have hw_sum : ∑ i, op (w i) • splittingFamily f g i = splittingMap f g w := by
    simp_rw [splittingFamily, ← map_smul, ← map_sum, stdBasis,
      WithCStarModule.sum_op_smul_single_one]
  rw [hw_sum, splittingMap_apply f g w, WithCStarModule.prod_inner, WithCStarModule.equiv_symm_fst,
    WithCStarModule.equiv_symm_snd, unop_add]
  have hg_le : unop (inner Aᵐᵒᵖ (g (f w)) (g (f w))) ≤
      ‖gL‖ ^ 2 • unop (inner Aᵐᵒᵖ (f w) (f w)) :=
    gL.unop_inner_map_map_le_norm_sq_smul (fun b z ↦ g.map_smul (op b) z) (f w)
  simpa only [add_sub_cancel] using unop_inner_add_self_le_of_le_smul (A := A) (g (f w))
    (w - g (f w)) (unop_nonneg.mpr CStarModule.inner_self_nonneg) (sq_nonneg ‖gL‖) hg_le

/-- Any complete right Hilbert `A`-module `E` that splits as a right `A`-linear retract of
`C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` (`f ∘ₗ g = LinearMap.id`) admits an `ι`-indexed Parseval frame. -/
theorem exists_isParsevalFrame_of_comp_eq_id {ι : Type*} [Fintype ι]
    (f : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) →ₗ[Aᵐᵒᵖ] E) (g : E →ₗ[Aᵐᵒᵖ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))
    (hfg : f ∘ₗ g = LinearMap.id) : ∃ x : ι → E, IsParsevalFrame Aᵐᵒᵖ x := by
  classical
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  have hsp : IsStrictlyPositive (CStarMatrix.gram A (splittingFamily f g)) :=
    isStrictlyPositive_gram_splitting f g hfg
  let B := CFC.sqrt (Ring.inverse (CStarMatrix.gram A (splittingFamily f g)))
  let S := CFC.sqrt (CStarMatrix.gram A (splittingFamily f g))
  have hgram_η : CStarMatrix.gram A (fun j ↦ ∑ k, op (B k j) • splittingFamily f g k) = 1 :=
    TauCeti.CStarMatrix.gram_sum_op_smul_sqrt_ringInverse hsp
  let η : ι → C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
    fun j ↦ ∑ k, op (B k j) • splittingFamily f g k
  let x : ι → E := fun j ↦ ∑ k, op (B k j) • f (stdBasis A ι k)
  let π_fst := _root_.WithCStarModule.fstLinearMap Aᵐᵒᵖ Aᵐᵒᵖ E C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)
  have hη_fst (j : ι) : (η j).fst = x j := by
    rw [← _root_.WithCStarModule.fstLinearMap_apply Aᵐᵒᵖ Aᵐᵒᵖ, map_sum]
    simp [splittingFamily, splittingMap_apply, x]
  refine ⟨x, isParsevalFrame_iff.mpr fun z ↦ ?_⟩
  let u₀ : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, E × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) := (WithCStarModule.equiv Aᵐᵒᵖ _).symm (z, 0)
  have hfgz : f (g z) = z := LinearMap.congr_fun hfg z
  have hu₀_eq : splittingMap f g (g z) = u₀ := by
    rw [splittingMap_apply, hfgz, sub_self]
  have hη_sum (k : ι) : ∑ j, op (S j k) • η j = splittingFamily f g k :=
    TauCeti.CStarMatrix.sum_op_smul_sqrt_gram hsp k
  have hu₀_span : ∃ c : ι → A, ∑ j, op (c j) • η j = u₀ := ⟨fun j ↦ ∑ k, S j k * g z k, by
    calc ∑ j, op (∑ k, S j k * g z k) • η j
        = ∑ k, op (g z k) • ∑ j, op (S j k) • η j := by
            simp_rw [Finset.op_sum, Finset.sum_smul, op_mul, mul_smul, Finset.smul_sum]
            exact Finset.sum_comm
      _ = splittingMap f g (∑ k, op (g z k) • stdBasis A ι k) := by
            simp_rw [hη_sum, splittingFamily, ← map_smul, ← map_sum]
      _ = u₀ := by
            simp_rw [stdBasis]
            rw [WithCStarModule.sum_op_smul_single_one, hu₀_eq]⟩
  have hu₀_rec : ∑ i, inner Aᵐᵒᵖ (η i) u₀ • η i = u₀ :=
    TauCeti.CStarMatrix.sum_inner_smul_of_gram_eq_one hgram_η hu₀_span
  have hinner_x (i : ι) : inner Aᵐᵒᵖ (x i) z = inner Aᵐᵒᵖ (η i) u₀ := by
    rw [WithCStarModule.prod_inner]; simp [u₀, hη_fst]
  calc ∑ i, inner Aᵐᵒᵖ (x i) z • x i
      = π_fst (∑ i, inner Aᵐᵒᵖ (η i) u₀ • η i) := by
          dsimp only [π_fst]
          simp_rw [hinner_x, map_sum, map_smul, _root_.WithCStarModule.fstLinearMap_apply, hη_fst]
    _ = z := by
          dsimp only [π_fst]
          rw [hu₀_rec, _root_.WithCStarModule.fstLinearMap_apply, WithCStarModule.equiv_symm_fst]

end LinearMap
