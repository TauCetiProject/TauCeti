/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.JohnNirenberg
public import TauCeti.MeasureTheory.Integral.SharpMaximalFunction

/-!
# Functions of bounded and of vanishing mean oscillation

Let `μ` be a measure on a pseudometric space `X`. The **BMO seminorm** of `f : X → F` is the
supremum of its mean oscillations over all open balls,

`‖f‖_{BMO} = sup_B ⨍_B ‖f - f_B‖`, where `f_B = ⨍_B f`,

taken in `ℝ≥0∞` (`TauCeti.bmoSeminorm`). A locally integrable `f` has **bounded mean
oscillation** (`TauCeti.MemBMO`) when this is finite. The seminorm is the supremum of the sharp
maximal function `f^#` (`TauCeti.bmoSeminorm_eq_iSup_sharpMaximalFunction`), it ignores
constants, is subadditive and homogeneous, and vanishes exactly on the a.e. constant functions
(`TauCeti.bmoSeminorm_eq_zero_iff`). Bounded functions have bounded mean oscillation, with
`‖f‖_{BMO} ≤ 2 ‖f‖_∞` (`TauCeti.bmoSeminorm_le_two_mul_eLpNorm_top`). On a seminormed group
with a right-invariant measure the seminorm is invariant under translation, and on a
finite-dimensional real normed space with an additive Haar measure it is invariant under dilation
(`TauCeti.bmoSeminorm_comp_add_right`, `TauCeti.bmoSeminorm_comp_smul`). On `ℝⁿ` the
John–Nirenberg inequality makes a function of bounded mean oscillation exponentially integrable
on every ball, at a rate controlled by its seminorm
(`TauCeti.exists_setLIntegral_exp_mul_norm_sub_setAverage_ball_le_of_bmoSeminorm_le`).

The **VMO modulus** of `f` is the supremum of its mean oscillations over the balls of radius at
most `r`,

`η_f(r) = sup_{B = B(c, s), s ≤ r} ⨍_B ‖f - f_B‖`

(`TauCeti.vmoModulus`). It is monotone in `r` and its supremum over all `r` is `‖f‖_{BMO}`. A
function of bounded mean oscillation has **vanishing mean oscillation** (`TauCeti.MemVMO`) when
`η_f(r) → 0` as `r → 0`. On `ℝⁿ` with Lebesgue measure the ball of radius `r` has measure
`ωₙ rⁿ`, so this agrees with Sarason's definition through the measure of the balls. The modulus
is the quantity in which perturbation arguments for equations whose coefficients have vanishing
mean oscillation are carried out: on balls of radius at most `r` such a coefficient is close in
mean to a constant, with error `η(r)`.

Functions of vanishing mean oscillation form a subspace of the functions of bounded mean
oscillation that is closed for the BMO seminorm (`TauCeti.memVMO_of_tendsto_bmoSeminorm`) and
contains every uniformly continuous function of bounded mean oscillation
(`UniformContinuous.memVMO`), in particular every continuous function with compact support
(`Continuous.memVMO_of_hasCompactSupport`). Hence the BMO-closure of the uniformly continuous
functions of bounded mean oscillation consists of functions of vanishing mean oscillation, the
easy half of Sarason's characterization.

## Main declarations

* `TauCeti.bmoSeminorm`, `TauCeti.MemBMO`: the BMO seminorm and the space of functions of
  bounded mean oscillation.
* `TauCeti.bmoSeminorm_eq_iSup_sharpMaximalFunction`: the seminorm is the supremum of `f^#`.
* `TauCeti.bmoSeminorm_le_two_mul_eLpNorm_top` and `MeasureTheory.MemLp.memBMO`: `L^∞ ⊆ BMO`.
* `TauCeti.bmoSeminorm_eq_zero_iff`: the seminorm vanishes exactly on a.e. constant functions.
* `TauCeti.bmoSeminorm_comp_add_right`, `TauCeti.bmoSeminorm_comp_smul`: translation and
  dilation invariance.
* `TauCeti.exists_setLIntegral_exp_mul_norm_sub_setAverage_ball_le_of_bmoSeminorm_le`: the
  John–Nirenberg inequality for functions of bounded mean oscillation on `ℝⁿ`.
* `TauCeti.vmoModulus`, `TauCeti.MemVMO`: the VMO modulus and the space of functions of
  vanishing mean oscillation.
* `TauCeti.memVMO_of_tendsto_bmoSeminorm`: VMO is closed in BMO.
* `UniformContinuous.memVMO`, `Continuous.memVMO_of_hasCompactSupport`: uniformly continuous
  functions of bounded mean oscillation, and continuous functions with compact support, have
  vanishing mean oscillation.

## References

* F. John and L. Nirenberg, *On functions of bounded mean oscillation*, Comm. Pure Appl. Math.
  **14** (1961), 415–426.
* D. Sarason, *Functions of vanishing mean oscillation*, Trans. Amer. Math. Soc. **207** (1975),
  391–405.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 3.1.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

section PseudoMetricSpace

variable {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {μ : Measure X} {f g : X → F} {a : ℝ≥0∞} {r : ℝ}

/-! ### The BMO seminorm -/

/-- The **BMO seminorm** of `f` with respect to `μ`: the supremum, over all open balls `B`, of the
mean oscillation `⨍_B ‖f - f_B‖ₑ` of `f` on `B` about its average `f_B = ⨍_B f`.

It takes values in `ℝ≥0∞`, so it is defined for every `f`; balls of radius `r ≤ 0` are empty and
contribute `0`. -/
noncomputable def bmoSeminorm (f : X → F) (μ : Measure X) : ℝ≥0∞ :=
  ⨆ (c : X) (r : ℝ), ⨍⁻ y in ball c r, ‖f y - ⨍ z in ball c r, f z ∂μ‖ₑ ∂μ

/-- The mean oscillation of `f` on any open ball is at most its BMO seminorm. -/
theorem setLAverage_enorm_sub_setAverage_le_bmoSeminorm (f : X → F) (μ : Measure X) (c : X)
    (r : ℝ) : ⨍⁻ y in ball c r, ‖f y - ⨍ z in ball c r, f z ∂μ‖ₑ ∂μ ≤ bmoSeminorm f μ :=
  le_iSup₂_of_le c r le_rfl

/-- The BMO seminorm is at most `a` exactly when the mean oscillation of `f` on every open ball
is. -/
theorem bmoSeminorm_le_iff :
    bmoSeminorm f μ ≤ a ↔ ∀ c r, ⨍⁻ y in ball c r, ‖f y - ⨍ z in ball c r, f z ∂μ‖ₑ ∂μ ≤ a :=
  iSup₂_le_iff

/-- A bound on the mean oscillation of `f` on every open ball bounds its BMO seminorm. -/
theorem bmoSeminorm_le
    (h : ∀ c r, ⨍⁻ y in ball c r, ‖f y - ⨍ z in ball c r, f z ∂μ‖ₑ ∂μ ≤ a) :
    bmoSeminorm f μ ≤ a :=
  bmoSeminorm_le_iff.2 h

/-- The BMO seminorm is the supremum of the sharp maximal function. -/
theorem bmoSeminorm_eq_iSup_sharpMaximalFunction (f : X → F) (μ : Measure X) :
    bmoSeminorm f μ = ⨆ x, sharpMaximalFunction μ f x := by
  refine le_antisymm (bmoSeminorm_le fun c r => ?_)
    (iSup_le fun x => sharpMaximalFunction_le fun c r _ =>
      setLAverage_enorm_sub_setAverage_le_bmoSeminorm f μ c r)
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  · exact le_iSup_of_le c
      (setLAverage_enorm_sub_setAverage_le_sharpMaximalFunction μ f (mem_ball_self hr))

/-- The sharp maximal function is bounded by the BMO seminorm. -/
theorem sharpMaximalFunction_le_bmoSeminorm (f : X → F) (μ : Measure X) (x : X) :
    sharpMaximalFunction μ f x ≤ bmoSeminorm f μ :=
  bmoSeminorm_eq_iSup_sharpMaximalFunction f μ ▸ le_iSup (sharpMaximalFunction μ f) x

/-- The BMO seminorm of a constant with values in a Banach space vanishes. -/
@[simp]
theorem bmoSeminorm_const [CompleteSpace F] (b : F) : bmoSeminorm (fun _ : X => b) μ = 0 := by
  simp [bmoSeminorm_eq_iSup_sharpMaximalFunction]

/-- The BMO seminorm of the zero function vanishes. -/
@[simp]
theorem bmoSeminorm_zero : bmoSeminorm (0 : X → F) μ = 0 := by
  simp [bmoSeminorm_eq_iSup_sharpMaximalFunction]

/-- The BMO seminorm depends only on the a.e. class of `f`. -/
theorem bmoSeminorm_congr_ae (h : f =ᵐ[μ] g) : bmoSeminorm f μ = bmoSeminorm g μ := by
  simp only [bmoSeminorm_eq_iSup_sharpMaximalFunction, sharpMaximalFunction_congr_ae h]

/-- Adding a constant to an a.e. strongly measurable `f` does not change its BMO seminorm. -/
@[simp]
theorem bmoSeminorm_add_const [CompleteSpace F] (hf : AEStronglyMeasurable f μ) (b : F) :
    bmoSeminorm (fun y => f y + b) μ = bmoSeminorm f μ := by
  simp only [bmoSeminorm_eq_iSup_sharpMaximalFunction, sharpMaximalFunction_add_const hf]

/-- The BMO seminorm is homogeneous: `‖k • f‖_{BMO} = ‖k‖ₑ ‖f‖_{BMO}`. -/
@[simp]
theorem bmoSeminorm_const_smul {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [SMulCommClass ℝ 𝕜 F] (k : 𝕜) :
    bmoSeminorm (k • f) μ = ‖k‖ₑ * bmoSeminorm f μ := by
  simp only [bmoSeminorm_eq_iSup_sharpMaximalFunction, sharpMaximalFunction_const_smul,
    ENNReal.mul_iSup]

/-- The BMO seminorm of `-f` is that of `f`. -/
@[simp]
theorem bmoSeminorm_neg : bmoSeminorm (-f) μ = bmoSeminorm f μ := by
  simpa using bmoSeminorm_const_smul (μ := μ) (f := f) (-1 : ℝ)

/-- The BMO seminorm is subadditive on a.e. strongly measurable functions. -/
theorem bmoSeminorm_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    bmoSeminorm (f + g) μ ≤ bmoSeminorm f μ + bmoSeminorm g μ := by
  rw [bmoSeminorm_eq_iSup_sharpMaximalFunction]
  exact iSup_le fun x => (sharpMaximalFunction_add_le hf hg x).trans
    (add_le_add (sharpMaximalFunction_le_bmoSeminorm f μ x)
      (sharpMaximalFunction_le_bmoSeminorm g μ x))

/-- The BMO seminorm of a difference of a.e. strongly measurable functions is at most the sum of
their BMO seminorms. -/
theorem bmoSeminorm_sub_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    bmoSeminorm (f - g) μ ≤ bmoSeminorm f μ + bmoSeminorm g μ := by
  simpa [sub_eq_add_neg] using bmoSeminorm_add_le hf hg.neg

/-- **Bounded functions have bounded mean oscillation**: `‖f‖_{BMO} ≤ 2 ‖f‖_∞`. -/
theorem bmoSeminorm_le_two_mul_eLpNorm_top (f : X → F) (μ : Measure X) :
    bmoSeminorm f μ ≤ 2 * eLpNorm f ∞ μ := by
  refine bmoSeminorm_le fun c r => ?_
  have hae : ∀ᵐ y ∂μ.restrict (ball c r), ‖f y‖ₑ ≤ eLpNorm f ∞ μ :=
    ae_restrict_of_ae (ae_le_eLpNormEssSup.mono fun _ hy => hy.trans eLpNormEssSup_le_eLpNorm_top)
  have havg : ‖⨍ z in ball c r, f z ∂μ‖ₑ ≤ eLpNorm f ∞ μ :=
    (enorm_setAverage_le_setLAverage μ f _).trans
      ((laverage_le_essSup _).trans (essSup_le_of_ae_le _ hae))
  refine (laverage_le_essSup _).trans (essSup_le_of_ae_le _ (hae.mono fun y hy => ?_))
  rw [two_mul]
  exact enorm_sub_le.trans (add_le_add hy havg)

/-! ### Functions of bounded mean oscillation -/

/-- A function `f` has **bounded mean oscillation** with respect to `μ` if it is locally
integrable and its BMO seminorm is finite. -/
def MemBMO (f : X → F) (μ : Measure X) : Prop :=
  LocallyIntegrable f μ ∧ bmoSeminorm f μ < ∞

theorem MemBMO.locallyIntegrable (hf : MemBMO f μ) : LocallyIntegrable f μ :=
  hf.1

theorem MemBMO.bmoSeminorm_lt_top (hf : MemBMO f μ) : bmoSeminorm f μ < ∞ :=
  hf.2

theorem MemBMO.bmoSeminorm_ne_top (hf : MemBMO f μ) : bmoSeminorm f μ ≠ ∞ :=
  hf.2.ne

theorem MemBMO.congr_ae (hf : MemBMO f μ) (h : f =ᵐ[μ] g) : MemBMO g μ :=
  ⟨hf.1.congr h, bmoSeminorm_congr_ae h ▸ hf.2⟩

theorem memBMO_const [IsLocallyFiniteMeasure μ] [CompleteSpace F] (b : F) :
    MemBMO (fun _ : X => b) μ :=
  ⟨locallyIntegrable_const b, by simp⟩

theorem memBMO_zero : MemBMO (0 : X → F) μ :=
  ⟨locallyIntegrable_zero, by simp⟩

theorem MemBMO.const_smul {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (hf : MemBMO f μ) (k : 𝕜) : MemBMO (k • f) μ :=
  ⟨hf.1.smul k, by rw [bmoSeminorm_const_smul]; exact ENNReal.mul_lt_top enorm_lt_top hf.2⟩

theorem MemBMO.neg (hf : MemBMO f μ) : MemBMO (-f) μ :=
  ⟨hf.1.neg, by rw [bmoSeminorm_neg]; exact hf.2⟩

theorem MemBMO.add [SecondCountableTopology X] (hf : MemBMO f μ) (hg : MemBMO g μ) :
    MemBMO (f + g) μ :=
  ⟨hf.1.add hg.1, (bmoSeminorm_add_le hf.1.aestronglyMeasurable hg.1.aestronglyMeasurable).trans_lt
    (ENNReal.add_lt_top.2 ⟨hf.2, hg.2⟩)⟩

theorem MemBMO.sub [SecondCountableTopology X] (hf : MemBMO f μ) (hg : MemBMO g μ) :
    MemBMO (f - g) μ := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- Essentially bounded functions have bounded mean oscillation. -/
theorem _root_.MeasureTheory.MemLp.memBMO [IsLocallyFiniteMeasure μ] (hf : MemLp f ∞ μ) :
    MemBMO f μ :=
  ⟨hf.locallyIntegrable le_top, (bmoSeminorm_le_two_mul_eLpNorm_top f μ).trans_lt
    (ENNReal.mul_lt_top (by simp) hf.eLpNorm_lt_top)⟩

/-! ### Functions with vanishing BMO seminorm -/

/-- On a proper space with a measure finite on compact sets, the BMO seminorm of a locally
integrable function vanishes exactly when the function is a.e. constant. -/
theorem bmoSeminorm_eq_zero_iff [ProperSpace X] [IsFiniteMeasureOnCompacts μ] [CompleteSpace F]
    (hf : LocallyIntegrable f μ) : bmoSeminorm f μ = 0 ↔ ∃ b : F, f =ᵐ[μ] fun _ => b := by
  refine ⟨fun h => ?_, fun ⟨b, hb⟩ => by rw [bmoSeminorm_congr_ae hb, bmoSeminorm_const]⟩
  have hball (c : X) (r : ℝ) :=
    ae_restrict_eq_setAverage_of_setLAverage_enorm_sub_setAverage_eq_zero
      ((hf.integrableOn_isCompact (isCompact_closedBall c r)).mono_set
        ball_subset_closedBall).aestronglyMeasurable measure_ball_lt_top.ne
      (le_antisymm (h ▸ setLAverage_enorm_sub_setAverage_le_bmoSeminorm f μ c r) zero_le)
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact ⟨0, .of_forall fun x => isEmptyElim x⟩
  by_cases hpos : ∃ m : ℕ, μ (ball x₀ m) ≠ 0
  swap
  · simp only [not_exists, not_not] at hpos
    have hμ : μ = 0 := by
      rw [← Measure.measure_univ_eq_zero, ← iUnion_ball_nat x₀]
      exact measure_iUnion_null hpos
    exact ⟨0, by rw [hμ, ae_zero]; exact eventually_bot⟩
  obtain ⟨m, hm⟩ := hpos
  set b := ⨍ z in ball x₀ m, f z ∂μ
  refine ⟨b, ?_⟩
  -- On each ball `B(x₀, n)`, `f` is a.e. equal to its average over the larger ball
  -- `B(x₀, max n m)`, which is also its average over `B(x₀, m)`, a set of positive measure.
  have hn (n : ℕ) : ∀ᵐ y ∂μ.restrict (ball x₀ n), f y = b := by
    have hsub : ball x₀ (n : ℝ) ⊆ ball x₀ (max n m : ℕ) :=
      ball_subset_ball (by exact_mod_cast le_max_left n m)
    have hmsub : ball x₀ (m : ℝ) ⊆ ball x₀ (max n m : ℕ) :=
      ball_subset_ball (by exact_mod_cast le_max_right n m)
    have : NeBot (ae (μ.restrict (ball x₀ m))) := ae_neBot.2 (by simpa using hm)
    obtain ⟨y, hy₁, hy₂⟩ :=
      ((ae_restrict_of_ae_restrict_of_subset hmsub (hball x₀ (max n m : ℕ))).and
        (hball x₀ m)).exists
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hball x₀ (max n m : ℕ))] with z hz
    rw [hz, ← hy₁, hy₂]
  have h := (ae_restrict_iUnion_iff (fun n : ℕ => ball x₀ n) (fun y => f y = b)).2 hn
  rwa [iUnion_ball_nat, Measure.restrict_univ] at h

/-! ### The VMO modulus -/

/-- The **VMO modulus** of `f` with respect to `μ`: the supremum of the mean oscillations of `f`
over the open balls of radius at most `r`. It vanishes for `r ≤ 0`. -/
noncomputable def vmoModulus (f : X → F) (μ : Measure X) (r : ℝ) : ℝ≥0∞ :=
  ⨆ (c : X) (s : ℝ) (_ : s ≤ r), ⨍⁻ y in ball c s, ‖f y - ⨍ z in ball c s, f z ∂μ‖ₑ ∂μ

/-- The mean oscillation of `f` on a ball of radius at most `r` is at most `η_f(r)`. -/
theorem setLAverage_enorm_sub_setAverage_le_vmoModulus (f : X → F) (μ : Measure X) (c : X)
    {s : ℝ} (hs : s ≤ r) :
    ⨍⁻ y in ball c s, ‖f y - ⨍ z in ball c s, f z ∂μ‖ₑ ∂μ ≤ vmoModulus f μ r :=
  le_iSup₂_of_le c s (le_iSup_of_le hs le_rfl)

/-- `η_f(r) ≤ a` exactly when the mean oscillation of `f` on every ball of radius at most `r`
is at most `a`. -/
theorem vmoModulus_le_iff : vmoModulus f μ r ≤ a ↔
    ∀ c s, s ≤ r → ⨍⁻ y in ball c s, ‖f y - ⨍ z in ball c s, f z ∂μ‖ₑ ∂μ ≤ a := by
  simp only [vmoModulus, iSup_le_iff]

/-- A bound on the mean oscillation of `f` on every ball of radius at most `r` bounds `η_f(r)`. -/
theorem vmoModulus_le
    (h : ∀ c s, s ≤ r → ⨍⁻ y in ball c s, ‖f y - ⨍ z in ball c s, f z ∂μ‖ₑ ∂μ ≤ a) :
    vmoModulus f μ r ≤ a :=
  vmoModulus_le_iff.2 h

theorem vmoModulus_of_nonpos (hr : r ≤ 0) : vmoModulus f μ r = 0 :=
  nonpos_iff_eq_zero.1 <| vmoModulus_le fun c s hs => by
    simp [ball_eq_empty.2 (hs.trans hr)]

theorem monotone_vmoModulus (f : X → F) (μ : Measure X) : Monotone (vmoModulus f μ) :=
  fun _ _ hrr' => vmoModulus_le fun c _ hs =>
    setLAverage_enorm_sub_setAverage_le_vmoModulus f μ c (hs.trans hrr')

theorem vmoModulus_le_bmoSeminorm (f : X → F) (μ : Measure X) (r : ℝ) :
    vmoModulus f μ r ≤ bmoSeminorm f μ :=
  vmoModulus_le fun c s _ => setLAverage_enorm_sub_setAverage_le_bmoSeminorm f μ c s

/-- The BMO seminorm is the supremum of the VMO modulus over all radii. -/
theorem iSup_vmoModulus (f : X → F) (μ : Measure X) : ⨆ r, vmoModulus f μ r = bmoSeminorm f μ :=
  le_antisymm (iSup_le (vmoModulus_le_bmoSeminorm f μ)) <| bmoSeminorm_le fun c r =>
    le_iSup_of_le r (setLAverage_enorm_sub_setAverage_le_vmoModulus f μ c le_rfl)

theorem vmoModulus_congr_ae (h : f =ᵐ[μ] g) (r : ℝ) : vmoModulus f μ r = vmoModulus g μ r := by
  simp only [vmoModulus, setLAverage_enorm_sub_setAverage_congr_ae h]

@[simp]
theorem vmoModulus_const [CompleteSpace F] (b : F) (r : ℝ) :
    vmoModulus (fun _ : X => b) μ r = 0 :=
  nonpos_iff_eq_zero.1 <| (vmoModulus_le_bmoSeminorm _ μ r).trans_eq (bmoSeminorm_const b)

/-- The VMO modulus is homogeneous: `η_{k • f} = ‖k‖ₑ η_f`. -/
@[simp]
theorem vmoModulus_const_smul {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [SMulCommClass ℝ 𝕜 F] (k : 𝕜) (r : ℝ) :
    vmoModulus (k • f) μ r = ‖k‖ₑ * vmoModulus f μ r := by
  simp only [vmoModulus, Pi.smul_apply, setLAverage_enorm_const_smul_sub_setAverage,
    ENNReal.mul_iSup]

/-- The VMO modulus is subadditive on a.e. strongly measurable functions. -/
theorem vmoModulus_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (r : ℝ) : vmoModulus (f + g) μ r ≤ vmoModulus f μ r + vmoModulus g μ r :=
  vmoModulus_le fun c _ hs => (setLAverage_enorm_add_sub_le hf.restrict hg.restrict).trans
    (add_le_add (setLAverage_enorm_sub_setAverage_le_vmoModulus f μ c hs)
      (setLAverage_enorm_sub_setAverage_le_vmoModulus g μ c hs))

/-- If `f` varies by at most `ε` between points at distance less than `2 r`, then its mean
oscillation on every ball of radius at most `r` is at most `2 ε`. -/
theorem vmoModulus_le_of_forall_dist_lt [OpensMeasurableSpace X] [CompleteSpace F]
    (hf : AEStronglyMeasurable f μ) {ε : ℝ} (hε : ∀ x y, dist x y < 2 * r → ‖f x - f y‖ ≤ ε) :
    vmoModulus f μ r ≤ 2 * ENNReal.ofReal ε := by
  refine vmoModulus_le fun c s hs => ?_
  rcases eq_or_ne (μ (ball c s)) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  rcases eq_or_ne (μ (ball c s)) ∞ with htop | htop
  · simp [setLAverage_eq, htop]
  obtain ⟨y₀, hy₀⟩ := nonempty_of_measure_ne_zero h0
  have hbound : ∀ y ∈ ball c s, ‖f y - f y₀‖ ≤ ε := fun y hy => hε y y₀ <|
    calc dist y y₀ ≤ dist y c + dist y₀ c := dist_triangle_right y y₀ c
      _ < s + s := add_lt_add hy hy₀
      _ ≤ 2 * r := by linarith
  have hint : IntegrableOn f (ball c s) μ := Measure.integrableOn_of_bounded htop hf
    (M := ‖f y₀‖ + ε) <| (ae_restrict_mem measurableSet_ball).mono fun y hy => by
      have h1 : ‖f y‖ ≤ ‖f y₀‖ + ‖f y - f y₀‖ := by
        simpa using norm_add_le (f y₀) (f y - f y₀)
      linarith [hbound y hy]
  refine (setLAverage_enorm_sub_setAverage_le hint (f y₀)).trans ?_
  gcongr
  refine (laverage_le_essSup _).trans (essSup_le_of_ae_le _ ?_)
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hbound y hy)

/-! ### Functions of vanishing mean oscillation -/

/-- A function `f` has **vanishing mean oscillation** with respect to `μ` if it has bounded mean
oscillation and its VMO modulus `η_f(r)` tends to `0` as `r → 0`. -/
def MemVMO (f : X → F) (μ : Measure X) : Prop :=
  MemBMO f μ ∧ Tendsto (vmoModulus f μ) (𝓝[>] 0) (𝓝 0)

theorem MemVMO.memBMO (hf : MemVMO f μ) : MemBMO f μ :=
  hf.1

theorem MemVMO.tendsto_vmoModulus (hf : MemVMO f μ) :
    Tendsto (vmoModulus f μ) (𝓝[>] 0) (𝓝 0) :=
  hf.2

/-- A function of bounded mean oscillation has vanishing mean oscillation exactly when for every
`ε > 0` its mean oscillation on all sufficiently small balls is at most `ε`. -/
theorem memVMO_iff : MemVMO f μ ↔ MemBMO f μ ∧ ∀ ε > 0, ∃ δ > 0, vmoModulus f μ δ ≤ ε := by
  refine and_congr_right fun _ => ?_
  rw [ENNReal.tendsto_nhds_zero]
  refine forall₂_congr fun ε _ => ⟨fun h => ?_, fun ⟨δ, hδ, h⟩ => ?_⟩
  · obtain ⟨δ, hδ, h⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 h
    exact ⟨δ / 2, half_pos hδ, h ⟨half_pos hδ, half_lt_self hδ⟩⟩
  · exact (nhdsGT_basis (0 : ℝ)).eventually_iff.2
      ⟨δ, hδ, fun r hr => (monotone_vmoModulus f μ hr.2.le).trans h⟩

theorem MemVMO.congr_ae (hf : MemVMO f μ) (h : f =ᵐ[μ] g) : MemVMO g μ :=
  ⟨hf.1.congr_ae h, funext (vmoModulus_congr_ae h) ▸ hf.2⟩

theorem memVMO_const [IsLocallyFiniteMeasure μ] [CompleteSpace F] (b : F) :
    MemVMO (fun _ : X => b) μ :=
  ⟨memBMO_const b, by
    rw [show vmoModulus (fun _ : X => b) μ = fun _ => 0 from funext (vmoModulus_const b)]
    exact tendsto_const_nhds⟩

theorem MemVMO.const_smul {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (hf : MemVMO f μ) (k : 𝕜) : MemVMO (k • f) μ := by
  refine ⟨hf.1.const_smul k, ?_⟩
  have h := ENNReal.Tendsto.const_mul hf.2 (Or.inr (show ‖k‖ₑ ≠ ∞ from enorm_ne_top))
  rw [mul_zero] at h
  rwa [show vmoModulus (k • f) μ = fun r => ‖k‖ₑ * vmoModulus f μ r from
    funext (vmoModulus_const_smul k)]

theorem MemVMO.neg (hf : MemVMO f μ) : MemVMO (-f) μ := by
  simpa using hf.const_smul (-1 : ℝ)

theorem MemVMO.add [SecondCountableTopology X] (hf : MemVMO f μ) (hg : MemVMO g μ) :
    MemVMO (f + g) μ := by
  refine ⟨hf.1.add hg.1, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hf.2.add hg.2) (fun _ => zero_le) fun r => ?_⟩
  exact vmoModulus_add_le hf.1.1.aestronglyMeasurable hg.1.1.aestronglyMeasurable r

theorem MemVMO.sub [SecondCountableTopology X] (hf : MemVMO f μ) (hg : MemVMO g μ) :
    MemVMO (f - g) μ := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- **VMO is closed in BMO.** A locally integrable function that is a limit, in the BMO seminorm,
of functions of vanishing mean oscillation has vanishing mean oscillation. -/
theorem memVMO_of_tendsto_bmoSeminorm [SecondCountableTopology X] {ι : Type*} {l : Filter ι}
    [l.NeBot] {g : ι → X → F} (hf : LocallyIntegrable f μ) (hg : ∀ i, MemVMO (g i) μ)
    (h : Tendsto (fun i => bmoSeminorm (f - g i) μ) l (𝓝 0)) : MemVMO f μ := by
  have hsplit (i : ι) : f = (f - g i) + g i := (sub_add_cancel f (g i)).symm
  have hmeas (i : ι) := (hf.sub (hg i).1.1).aestronglyMeasurable
  obtain ⟨i₀, hi₀⟩ := (ENNReal.tendsto_nhds_zero.1 h 1 one_pos).exists
  refine memVMO_iff.2 ⟨⟨hf, ?_⟩, fun ε hε => ?_⟩
  · rw [hsplit i₀]
    exact (bmoSeminorm_add_le (hmeas i₀) (hg i₀).1.1.aestronglyMeasurable).trans_lt
      (ENNReal.add_lt_top.2 ⟨hi₀.trans_lt ENNReal.one_lt_top, (hg i₀).1.2⟩)
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨i, hi⟩ := (ENNReal.tendsto_nhds_zero.1 h _ hε2).exists
  obtain ⟨δ, hδ, hgδ⟩ := (memVMO_iff.1 (hg i)).2 _ hε2
  refine ⟨δ, hδ, ?_⟩
  rw [hsplit i]
  calc vmoModulus (f - g i + g i) μ δ ≤ vmoModulus (f - g i) μ δ + vmoModulus (g i) μ δ :=
        vmoModulus_add_le (hmeas i) (hg i).1.1.aestronglyMeasurable δ
    _ ≤ ε / 2 + ε / 2 := add_le_add ((vmoModulus_le_bmoSeminorm _ μ δ).trans hi) hgδ
    _ = ε := ENNReal.add_halves ε

/-- **Uniformly continuous functions of bounded mean oscillation have vanishing mean
oscillation.** -/
theorem _root_.UniformContinuous.memVMO [SecondCountableTopology X] [OpensMeasurableSpace X]
    [CompleteSpace F]
    (hf : UniformContinuous f) (hb : MemBMO f μ) : MemVMO f μ := by
  refine memVMO_iff.2 ⟨hb, fun ε hε => ?_⟩
  obtain ⟨η, hη, hηε⟩ : ∃ η : ℝ, 0 < η ∧ 2 * ENNReal.ofReal η ≤ ε := by
    rcases eq_or_ne ε ∞ with rfl | hε'
    · exact ⟨1, one_pos, le_top⟩
    refine ⟨ε.toReal / 2, by positivity [ENNReal.toReal_pos hε.ne' hε'], ?_⟩
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_toReal hε', ENNReal.ofReal_ofNat,
      ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1 hf η hη
  refine ⟨δ / 2, half_pos hδ, (vmoModulus_le_of_forall_dist_lt hb.1.aestronglyMeasurable
    fun x y hxy => ?_).trans hηε⟩
  rw [← dist_eq_norm]
  exact (hfδ (by linarith)).le

/-- Continuous functions with compact support have vanishing mean oscillation. -/
theorem _root_.Continuous.memVMO_of_hasCompactSupport [SecondCountableTopology X]
    [OpensMeasurableSpace X] [IsLocallyFiniteMeasure μ] [CompleteSpace F] (hf : Continuous f)
    (hfc : HasCompactSupport f) : MemVMO f μ :=
  (hfc.uniformContinuous_of_continuous hf).memVMO (hf.memLp_top_of_hasCompactSupport hfc μ).memBMO

end PseudoMetricSpace

/-! ### Translation and dilation invariance -/

section Invariance

variable {X Y F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [PseudoMetricSpace Y]
  [MeasurableSpace Y] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure X} {ν : Measure Y}
  {a : ℝ≥0∞}

/-- The BMO seminorm is invariant under a measurable equivalence `e` that pushes `μ` forward to a
positive finite multiple of `ν` and induces a bijection between the open balls of `X` and of
`Y` by preimage. -/
private theorem bmoSeminorm_comp_of_map_eq_smul {e : X ≃ᵐ Y} (he : μ.map e = a • ν) (ha : a ≠ 0)
    (ha' : a ≠ ∞) (hball : ∀ c r, ∃ c' r', ball c r = e ⁻¹' ball c' r')
    (hball' : ∀ c' r', ∃ c r, ball c r = e ⁻¹' ball c' r') (f : Y → F) :
    bmoSeminorm (f ∘ e) μ = bmoSeminorm f ν := by
  refine le_antisymm (bmoSeminorm_le fun c r => ?_) (bmoSeminorm_le fun c' r' => ?_)
  · obtain ⟨c', r', h⟩ := hball c r
    simp only [Function.comp_apply, h,
      setLAverage_enorm_sub_setAverage_comp_preimage_of_map_eq_smul he ha ha']
    exact setLAverage_enorm_sub_setAverage_le_bmoSeminorm f ν c' r'
  · obtain ⟨c, r, h⟩ := hball' c' r'
    have := setLAverage_enorm_sub_setAverage_le_bmoSeminorm (f ∘ e) μ c r
    simp only [Function.comp_apply, h,
      setLAverage_enorm_sub_setAverage_comp_preimage_of_map_eq_smul he ha ha'] at this
    exact this

/-- The BMO seminorm is invariant under translation for a right-invariant measure. -/
@[simp]
theorem bmoSeminorm_comp_add_right {G : Type*} [SeminormedAddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] {μ : Measure G} [μ.IsAddRightInvariant] (f : G → F) (b : G) :
    bmoSeminorm (fun x => f (x + b)) μ = bmoSeminorm f μ :=
  bmoSeminorm_comp_of_map_eq_smul (e := MeasurableEquiv.addRight b) (a := 1)
    (by simpa using map_add_right_eq_self μ b) one_ne_zero ENNReal.one_ne_top
    (fun c r => ⟨c + b, r, by simp [preimage_add_right_ball]⟩)
    (fun c' r' => ⟨c' - b, r', by simp [preimage_add_right_ball]⟩) f

/-- The BMO seminorm is invariant under dilation `x ↦ t • x`, `t ≠ 0`, for an additive Haar
measure on a finite-dimensional real normed space. -/
@[simp]
theorem bmoSeminorm_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
    [μ.IsAddHaarMeasure] (f : E → F) {t : ℝ} (ht : t ≠ 0) :
    bmoSeminorm (fun x => f (t • x)) μ = bmoSeminorm f μ := by
  have hpre (c : E) (r : ℝ) : (fun x => t • x) ⁻¹' ball c r = ball (t⁻¹ • c) (‖t⁻¹‖ * r) := by
    rw [Set.preimage_smul₀ ht, smul_ball (inv_ne_zero ht)]
  refine bmoSeminorm_comp_of_map_eq_smul (e := MeasurableEquiv.smul₀ t ht)
    (Measure.map_addHaar_smul μ ht) (by simp [ht]) ENNReal.ofReal_ne_top
    (fun c r => ⟨t • c, ‖t‖ * r, ?_⟩) (fun c' r' => ⟨t⁻¹ • c', ‖t⁻¹‖ * r', (hpre c' r').symm⟩) f
  simp only [MeasurableEquiv.coe_smul₀, hpre, inv_smul_smul₀ ht, ← mul_assoc, norm_inv,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 ht), one_mul]

end Invariance

/-! ### The John–Nirenberg inequality for functions of bounded mean oscillation -/

section JohnNirenberg

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **The John–Nirenberg inequality for functions of bounded mean oscillation.** There are
constants `A > 0` and `C`, depending only on the dimension `n ≥ 1`, such that the following holds
for every additive Haar measure `μ` on `ℝⁿ = EuclideanSpace ℝ ι`. If `f : ℝⁿ → E` is locally
integrable with `‖f‖_{BMO} ≤ M` and `σ M ≤ A`, then on every ball `B`,

`∫_B exp (σ ‖f - f_B‖) ≤ C |B|`. -/
theorem exists_setLIntegral_exp_mul_norm_sub_setAverage_ball_le_of_bmoSeminorm_le :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ≥0, ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
      {f : EuclideanSpace ℝ ι → E} {M : ℝ≥0} {σ : ℝ},
      LocallyIntegrable f μ → bmoSeminorm f μ ≤ M → σ * M ≤ A →
      ∀ (x₀ : EuclideanSpace ℝ ι) (r : ℝ),
        ∫⁻ x in ball x₀ r, ENNReal.ofReal (Real.exp (σ * ‖f x - ⨍ y in ball x₀ r, f y ∂μ‖)) ∂μ ≤
          C * μ (ball x₀ r) := by
  obtain ⟨A, hA, C, h⟩ := exists_setLIntegral_exp_mul_norm_sub_setAverage_ball_le (ι := ι)
  refine ⟨A, hA, C, fun {E} _ _ _ μ _ f M σ hf hM hσ x₀ r => ?_⟩
  have hn : 0 < 2 * √(Fintype.card ι : ℝ) := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    positivity
  have hR : 2 * √(Fintype.card ι : ℝ) * r / (2 * √(Fintype.card ι : ℝ)) = r := by
    field_simp
  have := h (x₀ := x₀) (R := 2 * √(Fintype.card ι : ℝ) * r)
    ((hf.integrableOn_isCompact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall)
    (fun y s _ => (setLAverage_enorm_sub_setAverage_le_bmoSeminorm f μ y s).trans hM) hσ
  rwa [hR] at this

end JohnNirenberg

end TauCeti
