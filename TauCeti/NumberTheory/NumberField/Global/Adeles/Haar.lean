/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.BorelSpace
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Haar
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Haar
import TauCeti.NumberTheory.LocalField.Haar.AdicCompletion

/-!
# Change of variables over the adeles

An invertible adelic matrix scales additive Haar measure on column vectors by the idele norm
of its determinant. The formula holds for every number field and every Haar normalization.
It is the change of variables used in adelic geometry of numbers.

The infinite and finite components are separated by an additive homeomorphism. The infinite
component factors over the archimedean completions; the finite component uses the restricted
product formula `GeneralLinearGroup.distribHaarChar_pi_finiteAdeleRing_eq_distribHaarChar_det`.

## References

* A. Weil, *Basic Number Theory*, Chapter I, §2.
* The corresponding adelic formulas are `New.volume_map_mulVec_adele` and
  `New.volume_map_mul_mul_adele` in `src/Lib/Adelic/Adeles/IdeleModulus.lean` of
  [ShortProof], https://github.com/lsernau/grh-lean at
  `72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0). No code is copied.
-/

public noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix
open scoped NumberField.AdeleRing NNReal ENNReal Pointwise

namespace Matrix.GeneralLinearGroup

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]

/-- The Haar character of an invertible matrix over the infinite adeles is the product of
the normalized absolute values of its local determinants. -/
@[simp]
theorem distribHaarChar_pi_infiniteAdeleRing (g : GL ι K∞) :
    distribHaarChar (ι → K∞) g = ∏ w : InfinitePlace K,
      ‖((det g : K∞) w)‖₊ ^ w.mult := by
  have (w : InfinitePlace K) : SecondCountableTopology w.Completion := by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph
        |>.secondCountableTopology
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph
        |>.secondCountableTopology
  let f (w : InfinitePlace K) : GL ι K∞ →* GL ι w.Completion :=
    GeneralLinearGroup.map (Pi.evalRingHom (fun w : InfinitePlace K ↦ w.Completion) w)
  let (w : InfinitePlace K) : DistribMulAction (GL ι K∞) (ι → w.Completion) :=
    DistribMulAction.compHom _ (f w)
  let (w : InfinitePlace K) : ContinuousConstSMul (GL ι K∞) (ι → w.Completion) :=
    ⟨fun h ↦ continuous_const_smul (f w h)⟩
  -- `K∞` is the product of its completions; transpose the two finite coordinate indices.
  let e : (ι → K∞) ≃ₜ+ (∀ w : InfinitePlace K, ι → w.Completion) :=
    { toEquiv := Equiv.piComm (fun (_ : ι) (w : InfinitePlace K) ↦ w.Completion)
      map_add' := fun _ _ ↦ rfl
      continuous_toFun := continuous_pi fun w ↦ continuous_pi fun i ↦
        (continuous_apply w).comp (continuous_apply i)
      continuous_invFun := continuous_pi fun i ↦ continuous_pi fun w ↦
        (continuous_apply i).comp (continuous_apply w) }
  have he (v : ι → K∞) : e (g • v) = g • e v := by
    ext w i
    exact (Pi.evalRingHom (fun w : InfinitePlace K ↦ w.Completion) w).map_mulVec
      (g : Matrix ι ι K∞) v i
  rw [e.distribHaarChar_eq g g he, distribHaarChar_pi]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  -- The action pulled back through `f w` is the local matrix action by construction.
  have hlocal : distribHaarChar (ι → w.Completion) g =
      distribHaarChar (ι → w.Completion) (f w g) :=
    (ContinuousAddEquiv.refl _).distribHaarChar_eq g (f w g) (fun _ ↦ rfl)
  rw [hlocal, distribHaarChar_eq_distribHaarChar_det, InfinitePlace.distribHaarChar_completion]
  have hdet : (det (f w g) : w.Completion) = (det g : K∞) w :=
    congrArg Units.val (GeneralLinearGroup.map_det _ g)
  rw [hdet]

/-- The Haar character of an adelic matrix is the idele norm of its determinant. -/
@[simp]
theorem distribHaarChar_pi_adeleRing (g : GL ι 𝔸[K]) :
    distribHaarChar (ι → 𝔸[K]) g = (TauCeti.GlobalNumberFields.ideleNorm (det g) : ℝ≥0) := by
  let fi : GL ι 𝔸[K] →* GL ι K∞ := GeneralLinearGroup.map (RingHom.fst _ _)
  let ff : GL ι 𝔸[K] →* GL ι 𝔸ᶠ[K] := GeneralLinearGroup.map (RingHom.snd _ _)
  let : DistribMulAction (GL ι 𝔸[K]) (ι → K∞) := DistribMulAction.compHom _ fi
  let : DistribMulAction (GL ι 𝔸[K]) (ι → 𝔸ᶠ[K]) := DistribMulAction.compHom _ ff
  let : ContinuousConstSMul (GL ι 𝔸[K]) (ι → K∞) :=
    ⟨fun h ↦ continuous_const_smul (fi h)⟩
  let : ContinuousConstSMul (GL ι 𝔸[K]) (ι → 𝔸ᶠ[K]) :=
    ⟨fun h ↦ continuous_const_smul (ff h)⟩
  -- An adelic vector is a pair of vectors over the infinite and finite adele rings.
  let e : (ι → 𝔸[K]) ≃ₜ+ (ι → K∞) × (ι → 𝔸ᶠ[K]) :=
    { toEquiv := Equiv.arrowProdEquivProdArrow ι (fun _ ↦ K∞) (fun _ ↦ 𝔸ᶠ[K])
      map_add' := fun _ _ ↦ rfl
      continuous_toFun := (continuous_pi fun i ↦ continuous_fst.comp (continuous_apply i)).prodMk
        (continuous_pi fun i ↦ continuous_snd.comp (continuous_apply i))
      continuous_invFun := continuous_pi fun i ↦
        ((continuous_apply i).comp continuous_fst).prodMk
          ((continuous_apply i).comp continuous_snd) }
  have he (v : ι → 𝔸[K]) : e (g • v) = g • e v := by
    apply Prod.ext <;> apply funext <;> intro i
    · exact (RingHom.fst K∞ 𝔸ᶠ[K]).map_mulVec (g : Matrix ι ι 𝔸[K]) v i
    · exact (RingHom.snd K∞ 𝔸ᶠ[K]).map_mulVec (g : Matrix ι ι 𝔸[K]) v i
  -- These actions were pulled back through `fi` and `ff`, respectively.
  have hi : distribHaarChar (ι → K∞) g = distribHaarChar (ι → K∞) (fi g) :=
    (ContinuousAddEquiv.refl _).distribHaarChar_eq g (fi g) (fun _ ↦ rfl)
  have hf : distribHaarChar (ι → 𝔸ᶠ[K]) g = distribHaarChar (ι → 𝔸ᶠ[K]) (ff g) :=
    (ContinuousAddEquiv.refl _).distribHaarChar_eq g (ff g) (fun _ ↦ rfl)
  rw [e.distribHaarChar_eq g g he, distribHaarChar_prod, hi, hf]
  rw [distribHaarChar_pi_infiniteAdeleRing,
    distribHaarChar_pi_finiteAdeleRing_eq_distribHaarChar_det,
    FiniteAdeleRing.distribHaarChar_eq_finprod]
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_prod, TauCeti.GlobalNumberFields.coe_ideleNorm]
  congr 1
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    have hdet : (det (fi g) : K∞) = (det g : 𝔸[K]).1 :=
      congrArg Units.val (GeneralLinearGroup.map_det _ g)
    rw [NNReal.coe_pow, coe_nnNorm, hdet, InfinitePlace.completionNormalizedAbsValue_apply,
      InfinitePlace.coe_ideleInfiniteCoord]
  · refine (NNReal.toRealHom.toMonoidHom.map_finprod_of_injective
      NNReal.coe_injective _).trans ?_
    refine finprod_congr fun v ↦ ?_
    have hdet : (det (ff g) : 𝔸ᶠ[K]) = (det g : 𝔸[K]).2 :=
      congrArg Units.val (GeneralLinearGroup.map_det _ g)
    rw [v.normalizedAbsoluteValue_adicCompletion_eq_nnnorm,
      HeightOneSpectrum.coe_ideleFiniteCoord]
    -- `toRealHom` evaluates by the usual coercion from nonnegative reals.
    exact congrArg (fun a : 𝔸ᶠ[K] ↦ ‖a v‖) hdet

end Matrix.GeneralLinearGroup

namespace MeasureTheory.Measure

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]

/-- An invertible adelic matrix multiplies the measure of every image set by the idele norm
of its determinant, independently of the normalization of Haar measure. -/
theorem addHaar_smul_adeleRing (μ : Measure (ι → 𝔸[K])) [μ.IsAddHaarMeasure]
    (g : GL ι 𝔸[K]) (s : Set (ι → 𝔸[K])) :
    μ (g • s) = (TauCeti.GlobalNumberFields.ideleNorm (GeneralLinearGroup.det g) : ℝ≥0) * μ s := by
  obtain ⟨L⟩ : Nonempty (TopologicalSpace.PositiveCompacts (ι → 𝔸[K])) := inferInstance
  have : μ.Regular := Measure.regular_of_isAddLeftInvariant L.isCompact
    L.interior_nonempty L.isCompact.measure_ne_top
  rw [← distribHaarChar_mul, GeneralLinearGroup.distribHaarChar_pi_adeleRing]

/-- Pushing Haar measure forward by an invertible adelic matrix divides it by the idele
norm of the determinant. -/
theorem map_mulVec_adeleRing (μ : Measure (ι → 𝔸[K])) [μ.IsAddHaarMeasure]
    (g : GL ι 𝔸[K]) :
    μ.map ((g : Matrix ι ι 𝔸[K]) *ᵥ ·) =
      (TauCeti.GlobalNumberFields.ideleNorm (GeneralLinearGroup.det g) : ℝ≥0)⁻¹ • μ := by
  obtain ⟨L⟩ : Nonempty (TopologicalSpace.PositiveCompacts (ι → 𝔸[K])) := inferInstance
  have : μ.Regular := Measure.regular_of_isAddLeftInvariant L.isCompact
    L.interior_nonempty L.isCompact.measure_ne_top
  rw [← GeneralLinearGroup.distribHaarChar_pi_adeleRing, ← map_smul_eq_inv_distribHaarChar_smul]
  -- The standard `GL` action on columns is matrix multiplication.
  rfl

/-- For column vectors, left multiplication by `g` followed by scalar multiplication by `b`
has image-set scaling factor `|b ^ #ι * det g|`. Since the adele ring is commutative, this
also gives the factor for right multiplication of a one-column matrix by `b`. -/
theorem addHaar_image_mulVec_smul_adeleRing (μ : Measure (ι → 𝔸[K])) [μ.IsAddHaarMeasure]
    (g : GL ι 𝔸[K]) (b : 𝔸[K]ˣ) (s : Set (ι → 𝔸[K])) :
    μ ((fun v ↦ (g : Matrix ι ι 𝔸[K]) *ᵥ (b • v)) '' s) =
      (TauCeti.GlobalNumberFields.ideleNorm
        (b ^ Fintype.card ι * GeneralLinearGroup.det g) : ℝ≥0) * μ s := by
  let h : GL ι 𝔸[K] := g * TauCeti.diagGL (fun _ : ι ↦ b)
  have hh (v : ι → 𝔸[K]) : (h : Matrix ι ι 𝔸[K]) *ᵥ v =
      (g : Matrix ι ι 𝔸[K]) *ᵥ (b • v) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, TauCeti.diagGL_coe]
    apply congrArg ((g : Matrix ι ι 𝔸[K]) *ᵥ ·)
    -- The unit action of `b` is multiplication by its value in each coordinate.
    exact funext fun i ↦ Matrix.mulVec_diagonal _ _ i
  have hd : GeneralLinearGroup.det h = b ^ Fintype.card ι * GeneralLinearGroup.det g := by
    simp only [h, map_mul, TauCeti.det_diagGL, Finset.prod_const, Finset.card_univ, mul_comm]
  have himage : h • s = (fun v ↦ (g : Matrix ι ι 𝔸[K]) *ᵥ (b • v)) '' s := by
    rw [← Set.image_smul]
    exact congrArg (· '' s) (funext hh)
  rw [← himage, addHaar_smul_adeleRing, hd]

end MeasureTheory.Measure
