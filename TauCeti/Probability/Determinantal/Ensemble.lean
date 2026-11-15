/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Determinant.Andreief
public import TauCeti.Probability.Determinantal.Kernel
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
import TauCeti.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Finite determinantal ensembles

For a finite orthonormal family `φ`, the density `|det [φᵢ(xⱼ)]|² / n!` with respect to
the product reference measure defines a probability law on labelled particles. Andréief's
identity evaluates its multiplicative statistics as finite determinants. No finiteness of
the reference measure is assumed, and both real and complex functions are allowed.

The normalization is for labelled particles on the full product space. No ordering chamber
or distinctness convention is built into the definition. The empty family gives the unique
probability law on the one-point space of empty configurations.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), Lemmas 3.2.2 and 3.2.3.
-/

public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ENNReal NNReal

namespace TauCeti

variable {ι E 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The real density of a labelled finite determinantal ensemble. -/
def determinantalDensity (φ : ι → E → 𝕜) (x : ι → E) : ℝ :=
  ‖det (Matrix.of fun i j ↦ φ i (x j))‖ ^ 2 / (Fintype.card ι).factorial

/-- A determinantal density is nonnegative. -/
theorem determinantalDensity_nonneg (φ : ι → E → 𝕜) (x : ι → E) :
    0 ≤ determinantalDensity φ x := by
  unfold determinantalDensity
  positivity

/-- Continuous generators give a continuous density on the space of labelled particles. -/
theorem continuous_determinantalDensity [TopologicalSpace E] {φ : ι → E → 𝕜}
    (hφ : ∀ i, Continuous (φ i)) : Continuous (determinantalDensity φ) := by
  unfold determinantalDensity
  fun_prop

/-- Measurable generators give a measurable determinantal density. -/
theorem measurable_determinantalDensity [MeasurableSpace E] {φ : ι → E → 𝕜}
    (hφ : ∀ i, Measurable (φ i)) : Measurable (determinantalDensity φ) := by
  unfold determinantalDensity
  fun_prop

/-- Coincident particles have zero determinantal density, even for an atomic reference law. -/
theorem determinantalDensity_eq_zero_of_eq (φ : ι → E → 𝕜) {x : ι → E}
    {i j : ι} (hij : i ≠ j) (hx : x i = x j) : determinantalDensity φ x = 0 := by
  have hd : det (Matrix.of fun k l ↦ φ k (x l)) = 0 :=
    Matrix.det_zero_of_column_eq hij (fun k ↦ by simp [hx])
  simp [determinantalDensity, hd]

/-- The density can be read from the kernel, independently of the choice of generators. -/
theorem determinantalDensity_eq_det_finiteRankKernel (φ : ι → E → 𝕜) (x : ι → E) :
    determinantalDensity φ x =
      RCLike.re (det (Matrix.of fun i j ↦ finiteRankKernel φ (x i) (x j))) /
        (Fintype.card ι).factorial := by
  rw [det_finiteRankKernel, RCLike.ofReal_re]
  rfl

/-- The density is invariant under relabelling particles. -/
theorem determinantalDensity_comp_perm (φ : ι → E → 𝕜) (σ : Equiv.Perm ι) (x : ι → E) :
    determinantalDensity φ (x ∘ σ) = determinantalDensity φ x := by
  simp only [determinantalDensity_eq_det_finiteRankKernel, Function.comp_apply]
  have h := Matrix.det_submatrix_equiv_self σ
    (Matrix.of fun i j ↦ finiteRankKernel φ (x i) (x j))
  simpa only [Matrix.submatrix, Matrix.of_apply] using
    congrArg (fun z ↦ RCLike.re z / (Fintype.card ι).factorial) h

section Measure

variable [MeasurableSpace E] {μ : Measure E} [SigmaFinite μ] {φ : ι → E → 𝕜}

/-- The labelled ensemble measure. Orthonormal square-integrable generators make it a
probability measure; without orthonormality this definition is still the same density. -/
def determinantalEnsemble (μ : Measure E) (φ : ι → E → 𝕜) : Measure (ι → E) :=
  (Measure.pi fun _ : ι ↦ μ).withDensity (fun x ↦ ENNReal.ofReal (determinantalDensity φ x))

/-- The defining density, in the form used by measure transport. -/
theorem determinantalEnsemble_def (μ : Measure E) (φ : ι → E → 𝕜) :
    determinantalEnsemble μ φ = (Measure.pi fun _ : ι ↦ μ).withDensity
      (fun x ↦ ENNReal.ofReal (determinantalDensity φ x)) := (rfl)

omit [SigmaFinite μ] in
/-- Evaluate the ensemble on a measurable set of labelled configurations. -/
theorem determinantalEnsemble_apply {s : Set (ι → E)} (hs : MeasurableSet s) :
    determinantalEnsemble μ φ s =
      ∫⁻ x in s, ENNReal.ofReal (determinantalDensity φ x) ∂Measure.pi (fun _ ↦ μ) := by
  rw [determinantalEnsemble_def, withDensity_apply _ hs]

omit [SigmaFinite μ] in
/-- Equal finite rank kernels define the same labelled ensemble law. -/
theorem determinantalEnsemble_eq_of_finiteRankKernel_eq {ψ : ι → E → 𝕜}
    (h : ∀ x y, finiteRankKernel φ x y = finiteRankKernel ψ x y) :
    determinantalEnsemble μ φ = determinantalEnsemble μ ψ := by
  simp_rw [determinantalEnsemble_def, determinantalDensity_eq_det_finiteRankKernel, h]

/-- The real determinantal density is integrable. -/
theorem integrable_determinantalDensity (hφ : ∀ i, MemLp (φ i) 2 μ) :
    Integrable (determinantalDensity φ) (Measure.pi fun _ ↦ μ) :=
  (integrable_norm_det_sq hφ).div_const _

/-- The labelled ensemble has distinct particles almost surely, even when the reference
measure has atoms. Coincident coordinates force the density to vanish. -/
theorem ae_injective_determinantalEnsemble (hφ : ∀ i, MemLp (φ i) 2 μ) :
    ∀ᵐ x ∂determinantalEnsemble μ φ, Function.Injective x := by
  rw [determinantalEnsemble_def, ae_withDensity_iff'
    (integrable_determinantalDensity hφ).aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  filter_upwards [] with x hx
  intro i j hij
  by_contra hne
  have hd := determinantalDensity_eq_zero_of_eq φ hne hij
  simp [hd] at hx

/-- **Exchangeability** of the labelled determinantal ensemble. Any permutation of the
particle coordinates preserves its measure. No normalization is needed. -/
theorem measurePreserving_comp_perm_determinantalEnsemble (μ : Measure E) [SigmaFinite μ]
    (φ : ι → E → 𝕜) (σ : Equiv.Perm ι) :
    MeasurePreserving (fun x : ι → E ↦ x ∘ σ) (determinantalEnsemble μ φ)
      (determinantalEnsemble μ φ) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : ι ↦ E) σ.symm
  have he : (e : (ι → E) → (ι → E)) = (fun x ↦ x ∘ σ) := by
    funext x i
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hp := measurePreserving_piCongrLeft (fun _ : ι ↦ μ) σ.symm
  refine ⟨he ▸ e.measurable, ?_⟩
  rw [← he, determinantalEnsemble_def, e.map_withDensity, hp.map_eq]
  congr 1
  funext x
  congr 1
  have hs : e.symm x = x ∘ σ.symm := by
    apply e.injective
    simp only [MeasurableEquiv.apply_symm_apply, he]
    funext i
    simp
  rw [hs, determinantalDensity_comp_perm]

/-- The labelled determinantal density integrates to one, including an empty family. -/
theorem integral_determinantalDensity (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0) :
    ∫ x, determinantalDensity φ x ∂Measure.pi (fun _ ↦ μ) = 1 := by
  simp only [determinantalDensity, integral_div, integral_norm_det_sq hφ horth]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- **Existence of the determinantal probability law** associated to an orthonormal family. -/
theorem isProbabilityMeasure_determinantalEnsemble (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0) :
    IsProbabilityMeasure (determinantalEnsemble μ φ) := by
  constructor
  rw [determinantalEnsemble_def, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal
      (integrable_determinantalDensity hφ) (.of_forall (determinantalDensity_nonneg φ)),
    integral_determinantalDensity hφ horth, ENNReal.ofReal_one]

/-- Integration against an ensemble is integration against its explicit real density. -/
theorem integral_determinantalEnsemble {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hφ : ∀ i, MemLp (φ i) 2 μ) (f : (ι → E) → F) :
    ∫ x, f x ∂determinantalEnsemble μ φ =
      ∫ x, determinantalDensity φ x • f x ∂Measure.pi (fun _ ↦ μ) := by
  rw [determinantalEnsemble_def, integral_withDensity_eq_integral_toReal_smul₀
    (integrable_determinantalDensity hφ).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (determinantalDensity_nonneg _ _)]

/-- Integrability for the ensemble is integrability after multiplication by its density. -/
theorem integrable_determinantalEnsemble_iff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hφ : ∀ i, MemLp (φ i) 2 μ) {f : (ι → E) → F} :
    Integrable f (determinantalEnsemble μ φ) ↔
      Integrable (fun x ↦ determinantalDensity φ x • f x) (Measure.pi fun _ ↦ μ) := by
  rw [determinantalEnsemble_def, integrable_withDensity_iff_integrable_smul₀'
    (integrable_determinantalDensity hφ).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (determinantalDensity_nonneg _ _)]

omit [MeasurableSpace E] in
private theorem density_mul_prod (φ : ι → E → 𝕜) (u : E → 𝕜) (x : ι → E) :
    determinantalDensity φ x • (∏ j, u (x j)) =
      ((Fintype.card ι).factorial : 𝕜)⁻¹ *
        ((∏ j, u (x j)) * (‖det (Matrix.of fun i j ↦ φ i (x j))‖ ^ 2 : ℝ)) := by
  rw [determinantalDensity, RCLike.real_smul_eq_coe_mul,
    RCLike.ofReal_div, RCLike.ofReal_natCast]
  ring

/-- Multiplicative statistics are integrable whenever all their weighted pairwise products
are integrable. Bounded measurable multipliers satisfy this condition for `L²` generators. -/
theorem integrable_prod_determinantalEnsemble (hφ : ∀ i, MemLp (φ i) 2 μ) {u : E → 𝕜}
    (hu : ∀ i j, Integrable (fun x ↦ φ i x * (u x * star (φ j x))) μ) :
    Integrable (fun x : ι → E ↦ ∏ j, u (x j)) (determinantalEnsemble μ φ) := by
  rw [integrable_determinantalEnsemble_iff hφ]
  simp_rw [density_mul_prod]
  exact (integrable_prod_mul_norm_det_sq hu).const_mul _

/-- **The multiplicative generating functional** of a finite determinantal ensemble.
The multiplier need not be positive, real, or bounded: weighted pairwise integrability suffices.
For an orthonormal family and `u = 1 + g`, the right side is `det (I + [∫ φᵢ g φⱼ*])`. -/
theorem integral_prod_determinantalEnsemble (hφ : ∀ i, MemLp (φ i) 2 μ) {u : E → 𝕜}
    (hu : ∀ i j, Integrable (fun x ↦ φ i x * (u x * star (φ j x))) μ) :
    ∫ x : ι → E, ∏ j, u (x j) ∂determinantalEnsemble μ φ =
      det (Matrix.of fun i j ↦ ∫ x, φ i x * (u x * star (φ j x)) ∂μ) := by
  rw [integral_determinantalEnsemble hφ]
  simp_rw [density_mul_prod]
  rw [integral_const_mul, integral_prod_mul_norm_det_sq hu, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_mul]

/-- Orthonormality puts the multiplicative generating functional in perturbation form. -/
theorem integral_prod_one_add_determinantalEnsemble (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, ∫ x, φ i x * star (φ j x) ∂μ = if i = j then 1 else 0)
    {g : E → 𝕜} (hg : ∀ i j, Integrable (fun x ↦ φ i x * (g x * star (φ j x))) μ) :
    ∫ x : ι → E, ∏ j, (1 + g (x j)) ∂determinantalEnsemble μ φ =
      det (1 + Matrix.of fun i j ↦ ∫ x, φ i x * (g x * star (φ j x)) ∂μ) := by
  have hsplit (i j : ι) (x : E) :
      φ i x * ((1 + g x) * star (φ j x)) =
        φ i x * star (φ j x) + φ i x * (g x * star (φ j x)) := by ring
  have hi (i j : ι) : Integrable (fun x ↦ φ i x * star (φ j x)) μ :=
    (hφ i).integrable_mul (hφ j).star
  have hint (i j : ι) : Integrable (fun x ↦ φ i x * ((1 + g x) * star (φ j x))) μ := by
    simp_rw [hsplit]
    exact (hi i j).add (hg i j)
  rw [integral_prod_determinantalEnsemble hφ hint]
  congr 1
  ext i j
  simp only [Matrix.of_apply, hsplit, integral_add (hi i j) (hg i j), horth,
    Matrix.add_apply, Matrix.one_apply]

end Measure

end TauCeti
