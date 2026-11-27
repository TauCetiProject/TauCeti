/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.IndefiniteUnitaryGroup
public import TauCeti.MeasureTheory.Group.Convolution.Action
public import TauCeti.MeasureTheory.Measure.FiberMeasure
public import TauCeti.MeasureTheory.Measure.Haar.Matrix.Complex
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Group.Units

/-!
# Appending columns in Gram fibers

`Matrix.IsHermitian.gram` takes a matrix of columns to its Hermitian Gram matrix.
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

/-- The underlying matrix of the Hermitian Gram map is the rectangular Gram product. -/
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
  have hd : ‖A.det‖ = 1 :=
    CStarRing.norm_of_mem_unitary (det_mem_unitary_of_mem_unitaryGroupOf hJ g.property)
  have hm : Measurable (fun X : Matrix n k ℂ ↦ A * X) :=
    (continuous_const.matrix_mul continuous_id).measurable
  refine ⟨hm, Measure.ext_of_lintegral _ fun f hf ↦ ?_⟩
  rw [lintegral_map hf hm]
  have hd₀ : A.det ≠ 0 := norm_pos_iff.mp (hd.symm ▸ Real.zero_lt_one)
  have hi := lintegral_eq_enorm_det_pow_mul_enorm_det_pow_mul_lintegral_comp_matrix_mul_mul
    (Q := (1 : Matrix k k ℂ)) hd₀ (by simp) f
  simpa only [← ofReal_norm, hd, ENNReal.ofReal_one, det_one, norm_one,
    one_pow, mul_one, one_mul, Matrix.mul_one] using hi.symm

/-- Multiplication by an isometry preserves the Hermitian Gram matrix. -/
@[simp] theorem gram_mul {J : Matrix n n ℂ} (g : unitaryGroupOf J) (hJ : J.IsHermitian)
    (X : Matrix n m ℂ) : hJ.gram ((g.val : Matrix n n ℂ) * X) = hJ.gram X := by
  apply Subtype.ext
  simpa only [IsHermitian.coe_gram] using
    conjTranspose_mul_mul_mul_of_star_mul_mul_eq (R := ℂ) (mem_unitaryGroupOf_iff.mp g.property) X X

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
  let append (p : unitaryGroupOf J × Matrix n k ℂ) :=
    (act₁ p.1, (p.1.val : Matrix n n ℂ) * p.2)
  let block (p : Matrix n m ℂ × Matrix n k ℂ) := (p.1ᴴ * J * p.2, hJ.gram p.2)
  have hval : Continuous fun g : unitaryGroupOf J ↦ (g.val : Matrix n n ℂ) :=
    Units.continuous_val.comp continuous_subtypeVal
  have ha₁ : Measurable act₁ := (hval.matrix_mul continuous_const).measurable
  have hact : Measurable (fun p : unitaryGroupOf J × Matrix n k ℂ ↦
      (p.1.val : Matrix n n ℂ) * p.2) :=
    ((hval.comp continuous_fst).matrix_mul continuous_snd).measurable
  have happ : Measurable append := (ha₁.comp measurable_fst).prodMk hact
  have hblock : Continuous block := by dsimp only [block]; fun_prop
  have heq (g : unitaryGroupOf J) (Y : Matrix n k ℂ) :
      block (append (g, Y)) = (E₁ᴴ * J * Y, hJ.gram Y) :=
    Prod.ext
      (conjTranspose_mul_mul_mul_of_star_mul_mul_eq (R := ℂ)
        (mem_unitaryGroupOf_iff.mp g.property) E₁ Y)
      (gram_mul g hJ Y)
  have hpush : (μ.prod (volume : Measure (Matrix n k ℂ))).map append =
      (μ.map act₁).prod volume :=
    (MeasurePreserving.skew_product ⟨ha₁, rfl⟩ hact
      (Eventually.of_forall fun g ↦ (measurePreserving_mul_left_volume g hJu).map_eq)).map_eq
  have hsecond := h₂.map_prod (ρ := μ) happ
    (Eventually.of_forall fun g ↦ by
      dsimp only [append, act₁]
      fun_prop)
    hblock.measurable heq
  rw [hpush] at hsecond
  let : SecondCountableTopology (unitaryGroupOf J) :=
    (isClosedEmbedding_val hJu).isEmbedding.secondCountableTopology
  let : MeasurableMul₂ (unitaryGroupOf J) := ⟨continuous_mul.measurable⟩
  have hconv := Measure.map_mconv_smul_prod_of_ae_smul_eq μ (x := E₁) (y := E₂) ha₁ hact hfix
  simp only [Subgroup.smul_def, GeneralLinearGroup.smul_def] at hconv
  rw [← hconv] at hsecond
  exact (h₁.prod_right hJ.continuous_gram.measurable).trans hsecond hblock

end unitaryGroupOf
end Matrix
