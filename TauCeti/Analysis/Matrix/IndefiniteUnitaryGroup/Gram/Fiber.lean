/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
public import TauCeti.MeasureTheory.Measure.FiberMeasure
public import TauCeti.MeasureTheory.Measure.Haar.Matrix.Complex

/-!
# Appending columns in Gram fibers

The map `Matrix.IsHermitian.gram` takes a matrix of columns to its Hermitian Gram matrix.
`Matrix.unitaryGroupOf.isLeFiberMeasure_gramBlocks_mconv` gives a lower bound for the
combined Gram fiber using convolution when the second measure fixes the initial columns.
The proof uses the two-step fiber rule `TauCeti.IsLeFiberMeasure.trans` and the Lebesgue
change of variables for complex matrix multiplication.

See Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, no. 6,
and `New.LeGramFibre.append` in grh-lean, commit `72fead1`
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open MeasureTheory Filter TauCeti
open scoped Matrix

namespace Matrix

variable {n m k : Type*} [Fintype n]

/-- The Gram matrix associated with a Hermitian form, as a point of the Hermitian subspace. -/
def IsHermitian.gram {J : Matrix n n ℂ} (hJ : J.IsHermitian) (X : Matrix n m ℂ) :
    selfAdjoint.submodule ℝ (Matrix m m ℂ) :=
  ⟨Xᴴ * J * X, isHermitian_conjTranspose_mul_mul X hJ⟩

/-- The coercion to matrices is the rectangular Gram product, so it can be rewritten without
unfolding the Hermitian-subspace construction. -/
@[simp] theorem IsHermitian.coe_gram {J : Matrix n n ℂ} (hJ : J.IsHermitian)
    (X : Matrix n m ℂ) : (hJ.gram X : Matrix m m ℂ) = Xᴴ * J * X := (rfl)

/-- The Hermitian Gram map is continuous. -/
@[fun_prop] theorem IsHermitian.continuous_gram {J : Matrix n n ℂ} (hJ : J.IsHermitian) :
    Continuous (hJ.gram : Matrix n m ℂ → _) := by
  apply Continuous.subtype_mk
  fun_prop

namespace unitaryGroupOf

variable [DecidableEq n]

/-- Left multiplication by an isometry of an invertible form preserves Lebesgue measure
on rectangular complex matrices. -/
theorem measurePreserving_mul_left_volume [Fintype k] {J : Matrix n n ℂ}
    (g : unitaryGroupOf J) (hJ : IsUnit J) :
    MeasurePreserving (fun X : Matrix n k ℂ ↦ (g.val : Matrix n n ℂ) * X) volume volume := by
  classical
  let A : Matrix n n ℂ := g.val
  have h := det_mem_unitary_of_mem_unitaryGroupOf hJ g.property
  have hnorm := congrArg norm (Unitary.mem_iff_star_mul_self.mp h)
  simp only [norm_mul, norm_star, norm_one] at hnorm
  have hd : ‖A.det‖ = 1 := by nlinarith [norm_nonneg A.det]
  have hm : Measurable (fun X : Matrix n k ℂ ↦ A * X) :=
    (continuous_const.matrix_mul continuous_id).measurable
  refine ⟨hm, Measure.ext fun S hS ↦ ?_⟩
  have hd₀ : A.det ≠ 0 := norm_pos_iff.mp (hd.symm ▸ Real.zero_lt_one)
  have hi := lintegral_eq_enorm_det_pow_mul_enorm_det_pow_mul_lintegral_comp_matrix_mul_mul
    (Q := (1 : Matrix k k ℂ)) hd₀ (by simp) (S.indicator fun _ ↦ (1 : ENNReal))
  have he : ‖A.det‖ₑ = 1 := by rw [← ofReal_norm, hd]; simp
  have hcomp : (∫⁻ Y : Matrix n k ℂ, S.indicator (fun _ ↦ (1 : ENNReal)) (A * Y)) =
      ∫⁻ Y : Matrix n k ℂ, S.indicator (fun _ ↦ (1 : ENNReal)) Y := by
    simpa only [he, det_one, eNorm_one, one_pow, mul_one, one_mul, Matrix.mul_one] using hi.symm
  rw [← setLIntegral_one, ← lintegral_indicator hS,
    lintegral_map (measurable_const.indicator hS) hm, hcomp,
    lintegral_indicator hS, setLIntegral_one]

/-- The simultaneous action of an isometry on two matrices preserves their mixed Gram block. -/
theorem conjTranspose_mul_mul_eq {J : Matrix n n ℂ} (g : unitaryGroupOf J)
    (X : Matrix n m ℂ) (Y : Matrix n k ℂ) :
    ((g.val : Matrix n n ℂ) * X)ᴴ * J * ((g.val : Matrix n n ℂ) * Y) = Xᴴ * J * Y := by
  have hg : (g.val : Matrix n n ℂ)ᴴ * J * g.val = J :=
    mem_unitaryGroupOf_iff.mp g.property
  rw [conjTranspose_mul]
  calc
    Xᴴ * (g.val : Matrix n n ℂ)ᴴ * J * ((g.val : Matrix n n ℂ) * Y) =
        Xᴴ * ((g.val : Matrix n n ℂ)ᴴ * J * (g.val : Matrix n n ℂ)) * Y := by
      simp only [Matrix.mul_assoc]
    _ = Xᴴ * J * Y := by rw [hg]

/-- Multiplication by an isometry preserves the Hermitian Gram matrix. -/
@[simp] theorem gram_mul {J : Matrix n n ℂ} (g : unitaryGroupOf J) (hJ : J.IsHermitian)
    (X : Matrix n m ℂ) : hJ.gram ((g.val : Matrix n n ℂ) * X) = hJ.gram X := by
  apply Subtype.ext
  simpa only [IsHermitian.coe_gram] using conjTranspose_mul_mul_eq g X X

/-- Appending columns in Gram block coordinates. If the law of `g E₁` under `μ` lies below
the first Gram fiber, and the law of `g E₂` under `η` lies below the mixed and final Gram
fiber with `E₁` fixed, then the law of the combined columns under `μ ∗ₘ η` lies below the
combined Gram fiber. The second measure must fix `E₁` almost everywhere. -/
theorem isLeFiberMeasure_gramBlocks_mconv [Fintype m] [Fintype k]
    {J : Matrix n n ℂ} (hJ : J.IsHermitian)
    (hJu : IsUnit J) (E₁ : Matrix n m ℂ) (E₂ : Matrix n k ℂ)
    [MeasurableSpace (unitaryGroupOf J)] [BorelSpace (unitaryGroupOf J)]
    {μ η : Measure (unitaryGroupOf J)} [SFinite μ] [SFinite η]
    {ν₁ : Measure (selfAdjoint.submodule ℝ (Matrix m m ℂ))}
    {ν₂ : Measure (Matrix m k ℂ × selfAdjoint.submodule ℝ (Matrix k k ℂ))} [SFinite ν₂]
    (h₁ : IsLeFiberMeasure volume ν₁ hJ.gram (hJ.gram E₁)
      (μ.map fun g ↦ (g.val : Matrix n n ℂ) * E₁))
    (h₂ : IsLeFiberMeasure volume ν₂ (fun Y ↦ (E₁ᴴ * J * Y, hJ.gram Y))
      (E₁ᴴ * J * E₂, hJ.gram E₂) (η.map fun g ↦ (g.val : Matrix n n ℂ) * E₂))
    (hfix : ∀ᵐ g ∂η, (g.val : Matrix n n ℂ) * E₁ = E₁) :
    IsLeFiberMeasure (volume.prod volume) (ν₁.prod ν₂)
      (fun XY : Matrix n m ℂ × Matrix n k ℂ ↦
        (hJ.gram XY.1, XY.1ᴴ * J * XY.2, hJ.gram XY.2))
      (hJ.gram E₁, E₁ᴴ * J * E₂, hJ.gram E₂)
      ((μ ∗ₘ η).map fun g ↦ ((g.val : Matrix n n ℂ) * E₁, (g.val : Matrix n n ℂ) * E₂)) := by
  let act₁ (g : unitaryGroupOf J) := (g.val : Matrix n n ℂ) * E₁
  let act₂ (g : unitaryGroupOf J) := (g.val : Matrix n n ℂ) * E₂
  let append (p : unitaryGroupOf J × Matrix n k ℂ) :=
    (act₁ p.1, (p.1.val : Matrix n n ℂ) * p.2)
  let block (p : Matrix n m ℂ × Matrix n k ℂ) := (p.1ᴴ * J * p.2, hJ.gram p.2)
  have hval : Continuous fun g : unitaryGroupOf J ↦ (g.val : Matrix n n ℂ) :=
    Units.continuous_val.comp continuous_subtypeVal
  have ha₁ : Measurable act₁ := (hval.matrix_mul continuous_const).measurable
  have ha₂ : Measurable act₂ := (hval.matrix_mul continuous_const).measurable
  have hact : Measurable (fun p : unitaryGroupOf J × Matrix n k ℂ ↦
      (p.1.val : Matrix n n ℂ) * p.2) :=
    ((hval.comp continuous_fst).matrix_mul continuous_snd).measurable
  have happ : Measurable append := (ha₁.comp measurable_fst).prodMk hact
  have hblock : Continuous block := by dsimp only [block]; fun_prop
  have heq (g : unitaryGroupOf J) (Y : Matrix n k ℂ) :
      block (append (g, Y)) = (E₁ᴴ * J * Y, hJ.gram Y) :=
    Prod.ext (conjTranspose_mul_mul_eq g E₁ Y) (gram_mul g hJ Y)
  have hpush : (μ.prod (volume : Measure (Matrix n k ℂ))).map append =
      (μ.map act₁).prod volume :=
    (MeasurePreserving.skew_product ⟨ha₁, rfl⟩ hact
      (Eventually.of_forall fun g ↦ (measurePreserving_mul_left_volume g hJu).map_eq)).map_eq
  have hsecond := h₂.map_prod (ρ := μ) happ
    (Eventually.of_forall fun g ↦ by
      dsimp only [append]
      exact continuous_const.prodMk
        ((continuous_const (y := (g.val : Matrix n n ℂ))).matrix_mul continuous_id))
    hblock.measurable heq
  rw [hpush] at hsecond
  have hconv : (μ.prod (η.map act₂)).map append =
      (μ ∗ₘ η).map (fun g ↦ (act₁ g, act₂ g)) := by
    let : SecondCountableTopology (unitaryGroupOf J) :=
      (isClosedEmbedding_val hJu).isEmbedding.secondCountableTopology
    have hmul : Measurable (fun z : unitaryGroupOf J × unitaryGroupOf J ↦ z.1 * z.2) := by
      apply Continuous.measurable
      apply (isClosedEmbedding_val hJu).isInducing.continuous_iff.mpr
      simpa only [Function.comp_def, Subgroup.coe_mul, Units.val_mul] using
        hval.fst'.matrix_mul hval.snd'
    have hprod : (μ.prod η).map (Prod.map id act₂) = μ.prod (η.map act₂) := by
      simpa only [Measure.map_id] using (Measure.map_prod_map μ η measurable_id ha₂).symm
    rw [Measure.mconv, Measure.map_map (ha₁.prodMk ha₂) hmul, ← hprod,
      Measure.map_map happ (measurable_id.prodMap ha₂)]
    apply Measure.map_congr
    apply (Measure.ae_prod_iff_ae_ae ?_).2
    · exact Eventually.of_forall fun g ↦ hfix.mono fun u hu ↦ by
        simp only [Function.comp_apply, Prod.map_apply, id_eq, append, act₁, act₂,
          Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hu]
    · exact measurableSet_eq_fun (happ.comp (measurable_id.prodMap ha₂))
        ((ha₁.prodMk ha₂).comp hmul)
  rw [hconv] at hsecond
  exact (h₁.prod_right hJ.continuous_gram.measurable).trans hsecond hblock

end unitaryGroupOf
end Matrix
