/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.UnitQuotient
public import TauCeti.NumberTheory.LFunctions.Theta.Mellin.Pair
public import TauCeti.NumberTheory.LFunctions.Theta.UnitCone
public import TauCeti.RingTheory.DedekindDomain.Different.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Meromorphic.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral
import TauCeti.RingTheory.ClassGroup.Basic
import TauCeti.RingTheory.FractionalIdeal.Norm
import TauCeti.Topology.ContinuousOn.PuncturedNhds

/-!
# Completed partial zeta functions of ideal classes

For an invertible fractional ideal `I` of a number field `K`, let `𝔎` be the ideal class of `I⁻¹`.
On `Re s > 1`, the completed partial zeta function attached to `I` is

`Z(I, s) = |d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 ∈ 𝔎} N(𝔟) ^ (-s)`,

where the sum runs over the nonzero integral ideals `𝔟` of `𝓞 K` in the class of `I⁻¹` — that is,
the nonzero integral ideals `𝔟` such that `𝔟 I` is principal. We define
`TauCeti.LFunctions.completedPartialZeta I` globally on `ℂ` as the canonical meromorphic normal-form
continuation (`TauCeti.meromorphicContinuation 1`) from `Re s > 1`.

Following Hecke (Neukirch, Chapter VII, §5), we unfold the integral of the norm-weighted reduced
theta series `N(y) ^ (s / 2) (θ_{σ(I)}(y) - 1)` over the cone `unitCone D` above any unit
fundamental domain `D ⊆ S`. Grouping the nonzero points of the ideal lattice `σ(I)` into orbits
under `(𝓞 K)ˣ` matches the orbits with the integral ideals `𝔟` of class `[I]⁻¹`; each orbit sums
over `(𝓞 K)ˣ` (with torsion multiplicity `w = #μ(K)`) to a full archimedean Gaussian integral over
`realSpace K`, evaluated by `integral_archGaussian_mul_archNorm_cpow`. Rescaling by the covolume
`V_{σ(I)} = N(I) 2 ^ (-r₂) √|d_K|` identifies `completedPartialZeta I` on `Re s > 1` with the
Mellin transform at `s / 2` of `mellinKernel D (idealLattice K I) - mellinConstant K`, and hence
globally with the normal form of `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`.

From `mellinKernelFEPair` and the trace-dual kernel identity `mellinKernel_mixedDual_idealLattice`
we deduce meromorphic continuation to `ℂ`, analyticity away from simple poles at `s = 0` and
`s = 1` with residues `-2 a₀` and `2 a₀` (`a₀ = mellinConstant K = 2 ^ (r - 1) R / w`), and
Hecke's functional equation `Z(I, 1 - s) = Z(I^∨, s)` against the trace dual
`FractionalIdeal.dualEquiv ℤ ℚ I`.

## Main definitions

* `TauCeti.LFunctions.completedPartialZeta`: the completed partial zeta function of `I` in
  meromorphic normal form on `ℂ`.

## Main results

* `TauCeti.LFunctions.summable_setIntegral_norm_archGaussian_mul_archNorm_rpow_unitCone`: absolute
  convergence of the lattice-point Gaussian integrals over `unitCone D` for `σ > 1`.
* `TauCeti.LFunctions.completedPartialZeta_eq_toMeromorphicNFOn`: identification of
  `completedPartialZeta I` with the normal form of
  `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`.
* `TauCeti.LFunctions.completedPartialZeta_eq_tsum`,
  `TauCeti.LFunctions.completedPartialZeta_eq_tsum_spanSingleton`,
  `TauCeti.LFunctions.completedPartialZeta_eq_tsum_fundamentalCone`,
  `TauCeti.LFunctions.completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one`: representations on
  `Re s > 1` over ideals in `[I]⁻¹`, principal products, fundamental-cone lattice points, and the
  trivial-modulus ray-class Dirichlet series.
* `TauCeti.LFunctions.completedPartialZeta_eq_integral_unitCone`,
  `TauCeti.LFunctions.hasMellin_mellinKernel_idealLattice_sub_mellinConstant`,
  `TauCeti.LFunctions.completedPartialZeta_eq_mellin`: cone-integral and Mellin-transform
  representations on `Re s > 1` (Neukirch VII (5.5)).
* `TauCeti.LFunctions.analyticAt_completedPartialZeta_iff`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedPartialZeta`,
  `TauCeti.LFunctions.tendsto_mul_completedPartialZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_one`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedPartialZeta_zero`: regularity, simple poles at
  `0` and `1`, and their residues.
* `TauCeti.LFunctions.completedPartialZeta_one_sub`: Hecke's functional equation
  `completedPartialZeta I (1 - s) = completedPartialZeta (FractionalIdeal.dualEquiv ℤ ℚ I) s`
  (Neukirch VII (5.9)).

## References

* E. Hecke, *Über die Zetafunktion beliebiger algebraischer Zahlkörper*, Nachr. Ges. Wiss.
  Göttingen (1917), 77–89.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.3)–(5.9).
-/

public section
noncomputable section

open Complex Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone Set Submodule TauCeti.GlobalNumberFields
  TauCeti.NumberField.mixedEmbedding
open scoped ENNReal nonZeroDivisors Pointwise Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Definition and class invariance -/

/-- **The completed partial zeta function** attached to an invertible fractional ideal `I` of `K`,
Neukirch VII (5.4) and (5.9): the canonical whole-plane meromorphic normal-form continuation from
`Re s > 1` of `|d_K| ^ (s / 2) Γ_ℝ(s) ^ r₁ Γ_ℂ(s) ^ r₂ ∑_{𝔟 ∈ [I]⁻¹} N(𝔟) ^ (-s)`. -/
def completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)

/-- Defining equation of `TauCeti.LFunctions.completedPartialZeta`. -/
theorem completedPartialZeta_def (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I = meromorphicContinuation 1 fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) :=
  (rfl)

/-- `completedPartialZeta I` is in meromorphic normal form on `ℂ`. -/
theorem meromorphicNFOn_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    MeromorphicNFOn (completedPartialZeta I) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

/-- `completedPartialZeta I` is meromorphic on `ℂ`. -/
@[fun_prop]
theorem meromorphic_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (completedPartialZeta I) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedPartialZeta I).meromorphicOn

/-- `completedPartialZeta I` depends on `I` only through its ideal class in `ClassGroup (𝓞 K)`. -/
theorem completedPartialZeta_congr_class {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    completedPartialZeta I = completedPartialZeta J := by
  rw [completedPartialZeta_def, completedPartialZeta_def, h]

/-! ### Unfolding over the unit cone -/

section Unfolding

private abbrev InvClassIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type _ :=
  {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹}

/-- Sum over `(𝓞 K)ˣ` of the complex weighted Gaussian cone integrals along one ideal orbit. -/
private theorem tsum_unit_setIntegral_archGaussian {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : InvClassIdeal I) {s : ℂ} (hs0 : 0 < s.re) :
    (∑' u : (𝓞 K)ˣ, ∫ y in unitCone D,
        (archNorm y : ℂ) ^ (s / 2) *
          archGaussian y (idealLatticeNeZeroEquiv I (𝔟, u) : mixedSpace K) ∂archHaar K) =
      ((Units.torsionOrder K : ℂ) *
        (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K) *
        ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s)) *
        (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hI_nonneg : 0 ≤ (FractionalIdeal.absNorm I.1 : ℝ) :=
    Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg I.1)
  set x₀ := mixedEmbedding K (coneGen I 𝔟)
  have hx₀ : mixedEmbedding.norm x₀ ≠ 0 :=
    (norm_pos_of_mem (mixedEmbedding_coneGen_mem I 𝔟)).ne'
  have hint₀ := integrable_archGaussian_mul_archNorm_cpow hx₀ hs0
  have hu_eq (u : (𝓞 K)ˣ) :
      (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
          archGaussian y (idealLatticeNeZeroEquiv I (𝔟, u) : mixedSpace K) ∂archHaar K) =
        ∫ y in unitCone D, archGaussian (unitScale u y) x₀ *
          (archNorm (unitScale u y) : ℂ) ^ (s / 2) ∂archHaar K :=
    setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y _ ↦ by
      simp only [x₀, coe_idealLatticeNeZeroEquiv, archGaussian_unit_smul, archNorm_unitScale,
        mul_comm]
  simp_rw [hu_eq]
  rw [← torsionOrder_smul_integral_archHaar_eq_tsum_unitCone hD hint₀, nsmul_eq_mul,
    integral_archGaussian_mul_archNorm_cpow hx₀ hs0, norm_mixedEmbedding_coneGen, ofReal_mul,
    mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) hI_nonneg, ofReal_natCast, ofReal_ratCast]
  ring

/-- Sum over `(𝓞 K)ˣ` of the norm-weighted real Gaussian cone integrals along one ideal orbit. -/
private theorem tsum_unit_setIntegral_norm_archGaussian {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (𝔟 : InvClassIdeal I) {σ : ℝ} (hσ_pos : 0 < σ) :
    (∑' u : (𝓞 K)ˣ, ∫ y in unitCone D,
        ‖archGaussian y (idealLatticeNeZeroEquiv I (𝔟, u) : mixedSpace K)‖ *
          archNorm y ^ (σ / 2) ∂archHaar K) =
      ((Units.torsionOrder K : ℝ) *
        ‖Gammaℝ σ ^ nrRealPlaces K * Gammaℝ (2 * σ) ^ nrComplexPlaces K‖ *
        (FractionalIdeal.absNorm I.1 : ℝ) ^ (-σ)) *
        (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) := by
  have hσ0 : (0 : ℝ) < (σ : ℂ).re := by simpa using hσ_pos
  have hI_pos : 0 < (FractionalIdeal.absNorm I.1 : ℝ) :=
    Rat.cast_pos.mpr (FractionalIdeal.absNorm_pos I.ne_zero)
  let g : (𝓞 K)ˣ → ℝ := fun u ↦ ∫ y in unitCone D,
    ‖archGaussian y (idealLatticeNeZeroEquiv I (𝔟, u) : mixedSpace K)‖ *
      archNorm y ^ (σ / 2) ∂archHaar K
  have hg_nonneg (u : (𝓞 K)ˣ) : 0 ≤ g u :=
    setIntegral_nonneg (measurableSet_unitCone hD.measurableSet) fun y hy ↦
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos (mem_unitCone.mp hy).1).le _)
  have hg_coe (u : (𝓞 K)ˣ) : (g u : ℂ) = ∫ y in unitCone D,
      (archNorm y : ℂ) ^ ((σ : ℂ) / 2) *
        archGaussian y (idealLatticeNeZeroEquiv I (𝔟, u) : mixedSpace K) ∂archHaar K := by
    dsimp only [g]
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    have hpow : (archNorm y : ℂ) ^ ((σ : ℂ) / 2) = ((archNorm y ^ (σ / 2) : ℝ) : ℂ) := by
      rw [← ofReal_ofNat, ← ofReal_div, ofReal_cpow (archNorm_pos (mem_unitCone.mp hy).1).le]
    rw [hpow, archGaussian_apply, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      ofReal_mul, mul_comm]
  have htsum : ((∑' u, g u : ℝ) : ℂ) =
      ((Units.torsionOrder K : ℂ) *
        (Gammaℝ σ ^ nrRealPlaces K * Gammaℝ (2 * σ) ^ nrComplexPlaces K) *
        ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-(σ : ℂ))) *
        (Ideal.absNorm (𝔟.1 : Ideal (𝓞 K)) : ℂ) ^ (-(σ : ℂ)) := by
    rw [ofReal_tsum]
    simp_rw [hg_coe]
    exact tsum_unit_setIntegral_archGaussian hD I 𝔟 hσ0
  have hnorm := congrArg Norm.norm htsum
  rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg hg_nonneg), norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast, ← ofReal_ratCast, norm_cpow_eq_rpow_re_of_pos hI_pos,
    Complex.norm_natCast_cpow_of_pos (Ideal.absNorm_pos_of_nonZeroDivisors 𝔟.1),
    neg_re, ofReal_re] at hnorm
  exact hnorm

/-- **Absolute convergence of the lattice-point Gaussian integrals over `unitCone D`.** For `σ > 1`
and any unit fundamental domain `D`, the integrals over `unitCone D` of
`‖archGaussian y x‖ * archNorm y ^ (σ / 2)` are summable over all nonzero `x ∈ σ(I)`. -/
theorem summable_setIntegral_norm_archGaussian_mul_archNorm_rpow_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D, ‖archGaussian y (x : mixedSpace K)‖ * archNorm y ^ (σ / 2)
        ∂archHaar K := by
  have hσ_pos : 0 < σ := zero_lt_one.trans hσ
  have hσ0 : (0 : ℝ) < (σ : ℂ).re := by simpa using hσ_pos
  rw [← (idealLatticeNeZeroEquiv I).summable_iff]
  refine (summable_prod_of_nonneg fun p ↦ setIntegral_nonneg
    (measurableSet_unitCone hD.measurableSet) fun y hy ↦
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (archNorm_pos (mem_unitCone.mp hy).1).le _)).mpr
    ⟨fun 𝔟 ↦ ?_, ?_⟩
  · have hx : mixedEmbedding.norm (mixedEmbedding K (coneGen I 𝔟)) ≠ 0 :=
      (norm_pos_of_mem (mixedEmbedding_coneGen_mem I 𝔟)).ne'
    refine (summable_setIntegral_norm_unitCone hD
      (integrable_archGaussian_mul_archNorm_cpow hx hσ0)).congr fun u ↦ ?_
    refine setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    rw [coe_idealLatticeNeZeroEquiv, archGaussian_unit_smul, ← archNorm_unitScale u y, norm_mul,
      norm_cpow_eq_rpow_re_of_pos (archNorm_pos fun w ↦ unitScale_pos ((mem_unitCone.mp hy).1 w) u),
      div_ofNat_re, ofReal_re]
  · refine (((TauCeti.summable_absNorm_rpow_ideal_iff (K := K)).mpr hσ).subtype _
      |>.mul_left _).congr fun 𝔟 ↦ (tsum_unit_setIntegral_norm_archGaussian hD I 𝔟 hσ_pos).symm

/-- Each nonzero lattice point gives an integrable weighted Gaussian on `unitCone D` for
`Re s > 0`. -/
private theorem integrableOn_unitCone_archNorm_cpow_mul_archGaussian (D : Set (realSpace K))
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y x)
      (unitCone D) (archHaar K) := by
  simpa only [mul_comm] using
    (integrable_archGaussian_mul_archNorm_cpow hx hs).integrableOn

/-- Summability of the cone integrals of `‖(archNorm y) ^ (s / 2) * archGaussian y x‖` over
nonzero `x ∈ σ(I)` for `Re s > 1`. -/
private theorem summable_setIntegral_norm_archNorm_cpow_mul_archGaussian {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    Summable fun x : {x : idealLattice K I // x ≠ 0} ↦
      ∫ y in unitCone D, ‖(archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)‖
        ∂archHaar K :=
  (summable_setIntegral_norm_archGaussian_mul_archNorm_rpow_unitCone hD I hs).congr fun _ ↦
    setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun _ hy ↦ by
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (archNorm_pos (mem_unitCone.mp hy).1), div_ofNat_re,
        mul_comm]

/-- **Integrability of the norm-weighted reduced theta series on `unitCone D`** for `Re s > 1`. -/
theorem integrableOn_archNorm_cpow_mul_latticeTheta_sub_one {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) *
        (latticeTheta (idealLattice K I) y - 1)) (unitCone D) (archHaar K) := by
  classical
  let μ := (archHaar K).restrict (unitCone D)
  let F : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)
  have hF_int (x : {x : idealLattice K I // x ≠ 0}) : Integrable (F x) μ :=
    integrableOn_unitCone_archNorm_cpow_mul_archGaussian D (norm_coe_idealLattice_ne_zero x.2)
      (zero_lt_one.trans hs)
  have hsum : Summable fun x ↦ ∫ y, ‖F x y‖ ∂μ :=
    summable_setIntegral_norm_archNorm_cpow_mul_archGaussian hD I hs
  have hcont : ContinuousOn (fun y ↦ (archNorm y : ℂ) ^ (s / 2) *
      (latticeTheta (idealLattice K I) y - 1)) (unitCone D) := by
    refine ContinuousOn.mul ?_ (ContinuousOn.sub (fun y hy ↦
      (continuousAt_latticeTheta _ (mem_unitCone.mp hy).1).continuousWithinAt) continuousOn_const)
    refine ContinuousOn.cpow (ofRealCLM.continuous.comp continuous_archNorm).continuousOn
      continuousOn_const fun y hy ↦ Or.inl ?_
    simpa using archNorm_pos (mem_unitCone.mp hy).1
  refine ⟨hcont.aestronglyMeasurable (measurableSet_unitCone hD.measurableSet), ?_⟩
  have hle : ∫⁻ y, ‖(archNorm y : ℂ) ^ (s / 2) * (latticeTheta (idealLattice K I) y - 1)‖ₑ ∂μ ≤
      ∑' x, ∫⁻ y, ‖F x y‖ₑ ∂μ := by
    rw [← lintegral_tsum fun x ↦ (hF_int x).1.eNorm]
    refine setLIntegral_mono' (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_
    rw [latticeTheta_eq_one_add _ y (mem_unitCone.mp hy).1, add_sub_cancel_left, ← tsum_mul_left]
    exact eNorm_tsum_le_tsum_eNorm
  simp_rw [← ofReal_integral_norm_eq_lintegral_eNorm (hF_int _)] at hle
  exact hle.trans_lt hsum.tsum_ofReal_lt_top

open scoped Classical in
/-- Complex power `(V_{σ(I)} ^ 2) ^ (s / 2)` expanded in terms of `N(I)`, `2 ^ (-r₂)`, and
`|d_K|`. -/
private theorem covolume_sq_idealLattice_cpow (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) =
      ((FractionalIdeal.absNorm I.1 : ℝ) : ℂ) ^ s *
        (((2⁻¹ : ℝ) : ℂ) ^ s) ^ nrComplexPlaces K *
        (((|discr K| : ℤ) : ℂ)) ^ (s / 2) := by
  set N_I : ℝ := (FractionalIdeal.absNorm I.1 : ℝ)
  set D_K : ℝ := ((|discr K| : ℤ) : ℝ)
  have hNI_pos : 0 < N_I := Rat.cast_pos.mpr (FractionalIdeal.absNorm_pos I.ne_zero)
  have hDK_pos : 0 < D_K := Int.cast_pos.mpr (abs_pos.mpr (discr_ne_zero K))
  have hV_pos : 0 < ZLattice.covolume (idealLattice K I) := ZLattice.covolume_pos (idealLattice K I)
  have h1 : (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) =
      (ZLattice.covolume (idealLattice K I) : ℂ) ^ s := by
    rw [TauCeti.ofReal_pow_cpow hV_pos.le 2 (s / 2), Nat.cast_ofNat,
      mul_div_cancel₀ _ two_ne_zero]
  have hcov : ZLattice.covolume (idealLattice K I) = N_I * 2⁻¹ ^ nrComplexPlaces K * √D_K := by
    rw [covolume_idealLattice]
    simp [N_I, D_K]
  rw [h1, hcov, ofReal_mul,
    mul_cpow_ofReal_nonneg (mul_nonneg hNI_pos.le (by positivity)) (Real.sqrt_nonneg _),
    ofReal_mul, mul_cpow_ofReal_nonneg hNI_pos.le (by positivity), ofReal_pow,
    TauCeti.ofReal_pow_cpow (by positivity) (nrComplexPlaces K) s, cpow_nat_mul,
    Real.sqrt_eq_rpow, ← cpow_mul_ofReal_nonneg hDK_pos.le, ofReal_intCast |discr K|]
  congr 2
  push_cast
  ring

open scoped Classical in
/-- Covolume-rescaled normalization algebra converting the unfolded Gaussian sum into the
archimedean factor times the ideal sum. -/
private theorem covolume_gamma_mul_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        ((Units.torsionOrder K : ℂ) *
          (Gammaℝ s ^ nrRealPlaces K * Gammaℝ (2 * s) ^ nrComplexPlaces K) *
          ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s)) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K := by
  set r₁ := nrRealPlaces K
  set r₂ := nrComplexPlaces K
  set N_I : ℝ := (FractionalIdeal.absNorm I.1 : ℝ)
  have hNI_pos : 0 < N_I := Rat.cast_pos.mpr (FractionalIdeal.absNorm_pos I.ne_zero)
  have hw : (Units.torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Units.torsionOrder_ne_zero K)
  have h2gamma : (2 : ℂ) ^ r₂ * Gammaℝ (2 * s) ^ r₂ = ((2 : ℂ) ^ s) ^ r₂ * Gammaℂ s ^ r₂ := by
    rw [← mul_pow, two_mul_Gammaℝ_two_mul, mul_pow]
  have h2cancel : (((2⁻¹ : ℝ) : ℂ) ^ s) ^ r₂ * ((2 : ℂ) ^ s) ^ r₂ = 1 := by
    rw [← ofReal_ofNat, ← mul_pow, ← mul_cpow_ofReal_nonneg (by positivity) (by positivity)]
    norm_num
  have hNI_cancel : (N_I : ℂ) ^ s * ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s) = 1 := by
    rw [← ofReal_ratCast, ← cpow_add _ _ (ofReal_ne_zero.mpr hNI_pos.ne'), add_neg_cancel,
      cpow_zero]
  rw [covolume_sq_idealLattice_cpow]
  calc (2 : ℂ) ^ r₂ / (Units.torsionOrder K : ℂ) *
          ((N_I : ℂ) ^ s * (((2⁻¹ : ℝ) : ℂ) ^ s) ^ r₂ * ((|discr K| : ℤ) : ℂ) ^ (s / 2)) *
          ((Units.torsionOrder K : ℂ) * (Gammaℝ s ^ r₁ * Gammaℝ (2 * s) ^ r₂) *
            ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s))
      = (((Units.torsionOrder K : ℂ) / (Units.torsionOrder K : ℂ)) *
          ((N_I : ℂ) ^ s * ((FractionalIdeal.absNorm I.1 : ℚ) : ℂ) ^ (-s)) *
          ((((2⁻¹ : ℝ) : ℂ) ^ s) ^ r₂ * ((2 : ℂ) ^ r₂ * Gammaℝ (2 * s) ^ r₂)) *
          (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁)) := by ring
    _ = ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂ := by
        rw [div_self hw, hNI_cancel, h2gamma]
        linear_combination
          (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ * Gammaℂ s ^ r₂) * h2cancel

open scoped Classical in
/-- **Evaluation of Hecke's cone integral on `Re s > 1`.** Over any unit fundamental domain `D`,
the covolume-rescaled cone integral of `(archNorm y) ^ (s / 2) * (θ_{σ(I)}(y) - 1)` equals the
completed partial zeta series. -/
private theorem unitCone_integral_eq_tsum {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
          (latticeTheta (idealLattice K I) y - 1) ∂archHaar K) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  let μ := (archHaar K).restrict (unitCone D)
  let F : {x : idealLattice K I // x ≠ 0} → realSpace K → ℂ :=
    fun x y ↦ (archNorm y : ℂ) ^ (s / 2) * archGaussian y (x : mixedSpace K)
  have hF_int (x : {x : idealLattice K I // x ≠ 0}) : Integrable (F x) μ :=
    integrableOn_unitCone_archNorm_cpow_mul_archGaussian D (norm_coe_idealLattice_ne_zero x.2) hs0
  have hF_sum : Summable fun x ↦ ∫ y, ‖F x y‖ ∂μ :=
    summable_setIntegral_norm_archNorm_cpow_mul_archGaussian hD I hs
  have hint_eq : (∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
        (latticeTheta (idealLattice K I) y - 1) ∂archHaar K) =
      ∑' x, ∫ y, F x y ∂μ := by
    refine (setIntegral_congr_fun (measurableSet_unitCone hD.measurableSet) fun y hy ↦ ?_).trans
      (integral_tsum_of_summable_integral_norm hF_int hF_sum).symm
    rw [latticeTheta_eq_one_add _ y (mem_unitCone.mp hy).1, add_sub_cancel_left, ← tsum_mul_left]
  have hint_sum : Summable fun x ↦ ∫ y, F x y ∂μ :=
    hF_sum.of_norm_bounded fun x ↦ norm_integral_le_integral_norm (F x)
  have hprod_sum : Summable fun p : InvClassIdeal I × (𝓞 K)ˣ ↦
      ∫ y, F (idealLatticeNeZeroEquiv I p) y ∂μ :=
    (idealLatticeNeZeroEquiv I).summable_iff.mpr hint_sum
  rw [hint_eq, ← (idealLatticeNeZeroEquiv I).tsum_eq, hprod_sum.tsum_prod'
    fun 𝔟 ↦ hprod_sum.comp_injective (Prod.mk_right_injective 𝔟)]
  simp_rw [F, μ, tsum_unit_setIntegral_archGaussian hD I _ hs0, tsum_mul_left]
  rw [← mul_assoc _ _ (∑' 𝔟 : InvClassIdeal I, _), covolume_gamma_mul_eq]

end Unfolding

/-! ### Identification with the Mellin functional-equation pair -/

/-- On `Re s > 1`, `mellinKernel D (idealLattice K I) - mellinConstant K` has Mellin transform at
`s / 2` equal to the completed partial zeta series of `I`. -/
private theorem hasMellin_mellinKernel_idealLattice_sub_mellinConstant_tsum
    {D : Set (realSpace K)} (hD : IsUnitFundamentalDomain K D)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  have hm := hasMellin_mellinKernel_sub hD.measurableSet hD.isBounded (idealLattice K I) s
    (integrableOn_archNorm_cpow_mul_latticeTheta_sub_one hD I hs)
  have hconst : (mellinConstant K : ℂ) = (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
      ((surfaceHaar K).real (Subtype.val ⁻¹' D) : ℂ) := by
    rw [mellinConstant_eq_mul_surfaceHaar_real hD]
    push_cast
    rfl
  rwa [← hconst, unitCone_integral_eq_tsum hD I hs] at hm

/-- On `Re s > 1`, `(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` equals the completed
partial zeta series of `I`. -/
theorem mellinKernelFEPair_Λ_div_two_eq_tsum {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hs2 : 1 / 2 < (s / 2).re := by
    rw [div_ofNat_re]
    linarith
  exact (hasMellin_mellinKernel_sub_mellinConstant hD (idealLattice K I) hs2).2.symm.trans
    (hasMellin_mellinKernel_idealLattice_sub_mellinConstant_tsum hD I hs).2

/-- `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` is meromorphic on `ℂ`. -/
private theorem meromorphic_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) :=
  fun z ↦ ((mellinKernelFEPair hD (idealLattice K I)).meromorphic_Λ (z / 2)).comp_analyticAt
    (g := fun w : ℂ ↦ w / 2) (analyticAt_id.div_const (c := (2 : ℂ)))

/-- Away from `0` and `1`, `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` is analytic
at `s`. -/
private theorem analyticAt_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)) s := by
  have h0' : s / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have h1' : s / 2 ≠ ((mellinKernelFEPair hD (idealLattice K I)).k : ℂ) := by
    simp only [mellinKernelFEPair_k, ofReal_div, ofReal_one, ofReal_ofNat]
    exact fun h ↦ h1 (by linear_combination 2 * h)
  have han : AnalyticAt ℂ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) :=
    ((mellinKernelFEPair hD (idealLattice K I)).analyticAt_Λ_iff (s / 2)).mpr ⟨.inl h0', .inl h1'⟩
  exact han.comp (f := fun w : ℂ ↦ w / 2) (analyticAt_id.div_const (c := (2 : ℂ)))

/-- On `{s | 1 < s.re}`, `s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)` is analytic. -/
private theorem analyticOnNhd_mellinKernelFEPair_Λ_div_two {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    AnalyticOnNhd ℂ (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2))
      {s | 1 < s.re} :=
  fun s (hs : 1 < s.re) ↦ analyticAt_mellinKernelFEPair_Λ_div_two hD I
    (fun h ↦ by linarith [h ▸ hs, zero_re]) (fun h ↦ by linarith [h ▸ hs, one_re])

/-- **Global identification with Hecke's Mellin pair.** Over any unit fundamental domain `D`,
`completedPartialZeta I` is the whole-plane meromorphic normal form of
`s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_toMeromorphicNFOn {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I =
      toMeromorphicNFOn (fun s ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)) univ :=
  meromorphicContinuation_eq_toMeromorphicNFOn (meromorphic_mellinKernelFEPair_Λ_div_two hD I)
    (analyticOnNhd_mellinKernelFEPair_Λ_div_two hD I)
    fun _ hs ↦ mellinKernelFEPair_Λ_div_two_eq_tsum hD I hs

/-- At every point `s : ℂ` (poles included), `completedPartialZeta I` has the same punctured germ
as `z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2)`. -/
theorem completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I =ᶠ[𝓝[≠] s]
      fun z ↦ (mellinKernelFEPair hD (idealLattice K I)).Λ (z / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I]
  exact (meromorphic_mellinKernelFEPair_Λ_div_two hD I).meromorphicOn
    |>.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)

/-- Off the poles `0` and `1`, `completedPartialZeta I s` agrees pointwise with
`(mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2)`. -/
theorem completedPartialZeta_eq_mellinKernelFEPair_Λ {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedPartialZeta I s = (mellinKernelFEPair hD (idealLattice K I)).Λ (s / 2) := by
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I]
  exact toMeromorphicNFOn_apply_of_analyticAt (meromorphic_mellinKernelFEPair_Λ_div_two hD I)
    (analyticAt_mellinKernelFEPair_Λ_div_two hD I h0 h1)

/-! ### Half-plane and integral representations -/

/-- **Ideal-sum representation on `Re s > 1`**, Neukirch VII (5.4). -/
theorem completedPartialZeta_eq_tsum (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I,
    toMeromorphicNFOn_apply_of_analyticAt (meromorphic_mellinKernelFEPair_Λ_div_two hD I)
      (analyticOnNhd_mellinKernelFEPair_Λ_div_two hD I s hs),
    mellinKernelFEPair_Λ_div_two_eq_tsum hD I hs]

/-- **Principal-product ideal-sum representation on `Re s > 1`**: the sum runs over nonzero
integral ideals `𝔟` such that `𝔟 I = (x)` for some `x : Kˣ`. -/
theorem completedPartialZeta_eq_tsum_spanSingleton (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ∑' 𝔟 : {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ ⊥ ∧ ∃ x : Kˣ,
            (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
              FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)},
          (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  rw [completedPartialZeta_eq_tsum I hs]
  congr 1
  let e : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} ≃
      {𝔟 : Ideal (𝓞 K) // 𝔟 ≠ ⊥ ∧ ∃ x : Kˣ,
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)} :=
    (Equiv.subtypeEquivRight fun 𝔟 ↦ ClassGroup.mk0_eq_inv_mk_iff I 𝔟).trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun 𝔟 : Ideal (𝓞 K) ↦ 𝔟 ∈ (Ideal (𝓞 K))⁰)
        (fun 𝔟 : Ideal (𝓞 K) ↦ ∃ x : Kˣ,
          (𝔟 : FractionalIdeal (𝓞 K)⁰ K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))).trans <|
        Equiv.subtypeEquivRight fun 𝔟 ↦ and_congr_left' (mem_nonZeroDivisors_iff_ne_zero (x := 𝔟))
  rw [← e.tsum_eq fun 𝔟 ↦ (Ideal.absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)]
  simp [e]

/-- **Fundamental-cone lattice-sum representation on `Re s > 1`**, Neukirch VII (5.3)–(5.4):
each ideal of class `[I]⁻¹` contributes `w = #μ(K)` generators in `fundamentalCone K`. -/
theorem completedPartialZeta_eq_tsum_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s /
        (Units.torsionOrder K : ℂ) *
        ∑' x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  rw [completedPartialZeta_eq_tsum I hs,
    tsum_absNorm_cpow_eq_mul_tsum_idealLattice_fundamentalCone I hs]
  ring

/-- **Relation to the ray-class Dirichlet series at the trivial modulus**: on `Re s > 1`,
`completedPartialZeta I s` is the archimedean factor times the trivial-modulus ray-class Dirichlet
series at `oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹`. -/
theorem completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    completedPartialZeta I s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K)
          (oneEquivClassGroup.symm (ClassGroup.mk K I)⁻¹))) s := by
  rw [completedPartialZeta_eq_tsum I hs,
    LSeries_rayClassCoeff_one_eq_tsum_oneEquivClassGroup _ hs, MulEquiv.apply_symm_apply]

open scoped Classical in
/-- **Cone-integral representation on `Re s > 1`**, Neukirch VII (5.5): over any unit fundamental
domain `D`, `completedPartialZeta I s` is `(2 ^ r₂ / w) V_{σ(I)} ^ s` times the cone integral of
`N(y) ^ (s / 2) (θ_{σ(I)}(y) - 1)`. -/
theorem completedPartialZeta_eq_integral_unitCone {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      (2 : ℂ) ^ nrComplexPlaces K / (Units.torsionOrder K : ℂ) *
        (ZLattice.covolume (idealLattice K I) ^ 2 : ℂ) ^ (s / 2) *
        ∫ y in unitCone D, (archNorm y : ℂ) ^ (s / 2) *
          (latticeTheta (idealLattice K I) y - 1) ∂archHaar K := by
  rw [completedPartialZeta_eq_tsum I hs, unitCone_integral_eq_tsum hD I hs]

/-- **Mellin-transform representation on `Re s > 1` (`HasMellin` form)**, Neukirch VII (5.5):
`completedPartialZeta I s` is the Mellin transform at `s / 2` of
`mellinKernel D (idealLattice K I) - mellinConstant K`. -/
theorem hasMellin_mellinKernel_idealLattice_sub_mellinConstant {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    HasMellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2)
      (completedPartialZeta I s) := by
  rw [completedPartialZeta_eq_tsum I hs]
  exact hasMellin_mellinKernel_idealLattice_sub_mellinConstant_tsum hD I hs

/-- **Mellin-transform representation on `Re s > 1` (`mellin` form)**, Neukirch VII (5.5). -/
theorem completedPartialZeta_eq_mellin {D : Set (realSpace K)}
    (hD : IsUnitFundamentalDomain K D) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    completedPartialZeta I s =
      mellin (fun u ↦ mellinKernel D (idealLattice K I) u - mellinConstant K) (s / 2) :=
  (hasMellin_mellinKernel_idealLattice_sub_mellinConstant hD I hs).2.symm

/-! ### Regularity, poles, and residues -/

/-- `completedPartialZeta I` is analytic away from `s = 0` and `s = 1`. -/
@[fun_prop]
theorem analyticAt_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedPartialZeta I) s := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  rw [completedPartialZeta_eq_toMeromorphicNFOn hD I,
    ← (meromorphicNFOn_toMeromorphicNFOn _ univ
      (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt,
    meromorphicOrderAt_toMeromorphicNFOn
      (meromorphic_mellinKernelFEPair_Λ_div_two hD I).meromorphicOn (mem_univ s)]
  exact (analyticAt_mellinKernelFEPair_Λ_div_two hD I h0 h1).meromorphicOrderAt_nonneg

/-- **Residue of `completedPartialZeta I` at `s = 1`**, Neukirch VII (5.9):
`lim_{s → 1} (s - 1) Z(I, s) = 2 a₀ = 2 ^ r R / w`. -/
theorem tendsto_sub_one_mul_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedPartialZeta I s) (𝓝[≠] 1)
      (𝓝 (2 * mellinConstant K : ℂ)) := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let P := mellinKernelFEPair hD (idealLattice K I)
  have hhalf : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 1) (𝓝[≠] ((1 / 2 : ℝ) : ℂ)) := by
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using
      ((continuous_id'.div_const (2 : ℂ)).continuousAt (x := 1)).tendsto_nhdsNE
        fun _ _ ↦ (div_left_inj₀ two_ne_zero).mp
  have hres := P.Λ_residue_k
  simp only [P, mellinKernelFEPair_k, mellinKernelFEPair_ε, mellinKernelFEPair_N,
    mellinKernelFEPair_g₀, ofReal_one, one_cpow, mul_one, smul_eq_mul, one_mul] at hres
  refine ((hres.comp hhalf).const_mul 2).congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 1] with s hs
  rw [Function.comp_apply, hs]
  push_cast
  ring

/-- **Residue of `completedPartialZeta I` at `s = 0`**, Neukirch VII (5.9):
`lim_{s → 0} s Z(I, s) = -2 a₀ = -2 ^ r R / w`. -/
theorem tendsto_mul_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Tendsto (fun s : ℂ ↦ s * completedPartialZeta I s) (𝓝[≠] 0)
      (𝓝 (-(2 * mellinConstant K : ℂ))) := by
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let P := mellinKernelFEPair hD (idealLattice K I)
  have hhalf : Tendsto (fun s : ℂ ↦ s / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    simpa only [zero_div] using
      ((continuous_id'.div_const (2 : ℂ)).continuousAt (x := 0)).tendsto_nhdsNE
        fun _ _ ↦ (div_left_inj₀ two_ne_zero).mp
  have hres := P.Λ_residue_zero
  simp only [P, mellinKernelFEPair_f₀, smul_eq_mul] at hres
  have hmul := (hres.comp hhalf).const_mul 2
  rw [mul_neg] at hmul
  refine hmul.congr' ?_
  filter_upwards [completedPartialZeta_eventuallyEq_mellinKernelFEPair_Λ hD I 0] with s hs
  rw [Function.comp_apply, hs]
  ring

/-- `completedPartialZeta I` has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 1 = (-1 : ℤ) := by
  have ha : (2 * mellinConstant K : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K))
  exact (meromorphic_completedPartialZeta I 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul ha
    (tendsto_sub_one_mul_completedPartialZeta I)

/-- `completedPartialZeta I` has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    meromorphicOrderAt (completedPartialZeta I) 0 = (-1 : ℤ) := by
  have ha : -(2 * mellinConstant K : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr (mellinConstant_ne_zero K)))
  refine (meromorphic_completedPartialZeta I 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul ha
    ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedPartialZeta_zero I

/-- `completedPartialZeta I` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedPartialZeta_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} :
    AnalyticAt ℂ (completedPartialZeta I) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun han ↦ ⟨?_, ?_⟩, fun ⟨h0, h1⟩ ↦ analyticAt_completedPartialZeta I h0 h1⟩
  · rintro rfl
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_zero] at hnonneg
    exact absurd hnonneg (by decide)
  · rintro rfl
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedPartialZeta_one] at hnonneg
    exact absurd hnonneg (by decide)

/-- As a meromorphic normal form, `completedPartialZeta I` takes the canonical value `0` at its
pole `s = 0`. -/
@[simp]
theorem completedPartialZeta_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I 0 = 0 :=
  not_not.mp <| (meromorphicNFOn_completedPartialZeta I (mem_univ 0))
    |>.meromorphicOrderAt_eq_zero_iff.not.mp
    (by simp [meromorphicOrderAt_completedPartialZeta_zero])

/-- As a meromorphic normal form, `completedPartialZeta I` takes the canonical value `0` at its
pole `s = 1`. -/
@[simp]
theorem completedPartialZeta_one (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    completedPartialZeta I 1 = 0 :=
  not_not.mp <| (meromorphicNFOn_completedPartialZeta I (mem_univ 1))
    |>.meromorphicOrderAt_eq_zero_iff.not.mp
    (by simp [meromorphicOrderAt_completedPartialZeta_one])

/-! ### Functional equation -/

/-- **Hecke's functional equation for completed partial zeta functions**, Neukirch VII (5.9):
`Z(I, 1 - s) = Z(I^∨, s)` for every `s : ℂ` (at the poles `0` and `1` both sides take the
normal-form value `0`). -/
theorem completedPartialZeta_one_sub (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    completedPartialZeta I (1 - s) =
      completedPartialZeta (FractionalIdeal.dualEquiv ℤ ℚ I) s := by
  by_cases h0 : s = 0
  · subst h0
    simp
  by_cases h1 : s = 1
  · subst h1
    simp
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1s1 : 1 - s ≠ 1 := fun h ↦ h0 (sub_eq_self.mp h)
  let hD := isUnitFundamentalDomain_unitFundamentalDomain (K := K)
  let hD' := hD.inv.mul (traceShift_mem_normOneSurface (K := K))
  rw [completedPartialZeta_eq_mellinKernelFEPair_Λ hD I h1s0 h1s1,
    completedPartialZeta_eq_mellinKernelFEPair_Λ hD' (FractionalIdeal.dualEquiv ℤ ℚ I) h0 h1]
  have hs0 : (1 - s) / 2 ≠ 0 := div_ne_zero h1s0 two_ne_zero
  have hs1 : (1 - s) / 2 ≠ 1 / 2 := fun h ↦ h0 (by linear_combination -2 * h)
  have hsub : (1 / 2 : ℂ) - (1 - s) / 2 = s / 2 := by ring
  rw [mellinKernelFEPair_Λ_eq hD (idealLattice K I) hs0 hs1, hsub]
  have hcongr : (mellinKernelFEPair hD.inv (mixedDual K (idealLattice K I))).Λ =
      (mellinKernelFEPair hD' (idealLattice K (FractionalIdeal.dualEquiv ℤ ℚ I))).Λ := by
    rw [← FEPairWithLevel.toWeakFEPair_Λ, ← FEPairWithLevel.toWeakFEPair_Λ]
    refine WeakFEPair.Λ_congr (fun u (hu : 0 < u) ↦ ?_) (by simp) (by simp) (by simp) (by simp)
    simp only [FEPairWithLevel.toWeakFEPair_f, mellinKernelFEPair_f,
      indicator_of_mem (mem_Ioi.mpr hu)]
    exact mellinKernel_mixedDual_idealLattice (FractionalIdeal.coe_dualEquiv ℤ ℚ I) _ u
  exact congrFun hcongr (s / 2)

end TauCeti.LFunctions
