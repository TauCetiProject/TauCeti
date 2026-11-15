/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Uniform
public import TauCeti.Analysis.Pseudodifferential.L2
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Measure
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# All-order Sobolev mapping of uniform pseudodifferential operators

For a uniform symbol `a : Symbol n V W m` (`TauCeti.Symbol.IsUniform`) without compact spatial
support, its Kohn–Nirenberg quantization `Op(a)` extends from Schwartz space to a bounded linear
operator `H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)` for every real `s`. Conjugating `Op(a)` by Mathlib's
Bessel multipliers in the uniform composition calculus (`TauCeti.Symbol.uniformSharp`) produces the
uniform order-zero symbol `a.besselConjugate ha s` built from
`⟨ξ / 2π⟩ ^ (s - m) # (a ∘ ⟨ξ / 2π⟩ ^ (-s))`, intertwining `J^s` and `J^{s - m}`; the
Calderón–Vaillancourt `L²` bound on `a.besselConjugate ha s` gives `‖Op(a) u‖_{H^{s - m}} ≤ C
‖u‖_{H^s}`.

## Main declarations

* `TauCeti.Symbol.besselConjugate`, `TauCeti.Symbol.IsUniform.besselConjugate`,
  `TauCeti.Symbol.quantizeUniformCLM_besselConjugate_fourierMultiplierCLM`: Bessel conjugation of
  `Op(a)` to a uniform symbol of order `0`.
* `TauCeti.Symbol.quantizeUniformSobolev`, `TauCeti.Symbol.exists_quantizeUniformSobolev`: the
  bounded extension `H^s →L[ℂ] H^{s - m}` for Hilbert and finite-dimensional normed fibres, agreeing
  with `quantizeSobolev` and `quantizeUniformOrderZero`.
* `TauCeti.Symbol.quantizeUniformSobolev_uniformSharp`,
  `TauCeti.Symbol.quantizeUniformSobolev_const`,
  `TauCeti.Symbol.quantizeUniformSobolev_besselPotential`: Sobolev composition and explicit actions
  of constant symbols and Bessel potentials.
* `TauCeti.Symbol.not_hasCompactSpatialSupport_const`,
  `TauCeti.Symbol.not_exists_eLpNorm_quantizeSchwartzValue_ofSpatial_smul_le`: non-compactness of
  nonzero constant symbols and failure of `L²` boundedness for `x_j T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
* M. Taylor, *Pseudodifferential Operators*, Princeton University Press, 1981, Chapter II, §6.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ}

/-! ### Conjugation to order zero by Bessel multipliers -/

section BesselConjugate

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Bessel conjugation of a uniform symbol.** For uniform `a : Symbol n V W m` and `s : ℝ`, the
symbol `⟨ξ / 2π⟩ ^ (s - m) # (a ∘ ⟨ξ / 2π⟩ ^ (-s))` viewed at order `0`, quantizing on Schwartz
space to `J^{s - m} ∘ Op(a) ∘ J^{-s}` (`quantizeUniformCLM_besselConjugate`). -/
def besselConjugate (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) : Symbol n V W 0 :=
  inclusion (by linarith)
    ((besselPotential (s - m) : Symbol n W W (s - m)).uniformSharp
      (a.comp (besselPotential (-s))) (ha.comp (isUniform_besselPotential (-s))))

theorem IsUniform.besselConjugate {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    (a.besselConjugate ha s).IsUniform :=
  ((isUniform_besselPotential (s - m)).uniformSharp
    (ha.comp (isUniform_besselPotential (-s)))).inclusion (by linarith)

variable [CompleteSpace V] [CompleteSpace W]

/-- On Schwartz functions, `Op(a.besselConjugate ha s) = J^{s - m} ∘ Op(a) ∘ J^{-s}`. -/
theorem quantizeUniformCLM_besselConjugate {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ)
    (v : 𝓢(CoordinateSpace n, V)) :
    quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s) v =
      SchwartzMap.fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ))
        (quantizeUniformCLM a ha
          (SchwartzMap.fourierMultiplierCLM V
            (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) v)) := by
  have hcomp : quantizeUniformCLM (a.comp (besselPotential (-s)))
      (ha.comp (isUniform_besselPotential (-s))) v =
      quantizeUniformCLM a ha (SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) v) := by
    have heq := a.uniformSharp_besselPotential (-s)
    ext x
    rw [quantizeUniformCLM_apply, ← heq, quantizeSchwartzValue_uniformSharp,
      quantizeUniformCLM_apply]
    congr 1; ext y; rw [quantizeUniformCLM_apply]
    exact quantizeSchwartzValue_besselPotential (-s) v y
  have hc := (isUniform_besselPotential (s - m)).uniformSharp
    (ha.comp (isUniform_besselPotential (-s)))
  ext x
  rw [quantizeUniformCLM_apply, besselConjugate, coefficient_inclusion,
    ← quantizeUniformCLM_apply _ hc, quantizeUniformCLM_besselPotential_uniformSharp,
    ContinuousLinearMap.comp_apply, hcomp]

/-- **Intertwining with Bessel multipliers**: `Op(a.besselConjugate ha s) (J^s u) = J^{s - m}
(Op(a) u)`. -/
theorem quantizeUniformCLM_besselConjugate_fourierMultiplierCLM {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s)
        (SchwartzMap.fourierMultiplierCLM V
          (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u) =
      SchwartzMap.fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ))
        (quantizeUniformCLM a ha u) := by
  rw [quantizeUniformCLM_besselConjugate]
  have hinv := SchwartzMap.fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg (-s) u
  simpa only [neg_neg] using congrArg
    (fun w ↦ SchwartzMap.fourierMultiplierCLM W
      (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ))
      (quantizeUniformCLM a ha w)) hinv

private theorem norm_toBesselPotentialSpaceCLM_eq_eLpNorm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (s : ℝ) (u : 𝓢(CoordinateSpace n, F)) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ =
      (eLpNorm (SchwartzMap.fourierMultiplierCLM F
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u) 2 volume).toReal := by
  rw [← BesselPotentialSpace.norm_toLp_eq, SchwartzMap.toLp_toBesselPotentialSpaceCLM,
    SchwartzMap.norm_toLp]

private theorem norm_quantizeUniformCLM_le_of_besselConjugate {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (a.besselConjugate ha s).coefficient v) 2 volume ≤
        ENNReal.ofReal C * eLpNorm v 2 volume) (u : 𝓢(CoordinateSpace n, V)) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
      C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  set v := SchwartzMap.fourierMultiplierCLM V
    (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u
  rw [norm_toBesselPotentialSpaceCLM_eq_eLpNorm, norm_toBesselPotentialSpaceCLM_eq_eLpNorm,
    ← quantizeUniformCLM_besselConjugate_fourierMultiplierCLM ha s u, coe_quantizeUniformCLM,
    ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (v.memLp 2).eLpNorm_ne_top) (hC v)

/-- **Sobolev estimate on Schwartz functions** for finite-dimensional complex normed fibres. -/
theorem IsUniform.exists_norm_quantizeUniformCLM_le_of_finiteDimensional
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    (ha.besselConjugate s).exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional
  exact ⟨C, hC0, norm_quantizeUniformCLM_le_of_besselConjugate ha s hC0 hC⟩

end BesselConjugate

/-! ### Bounded extension between Bessel-potential spaces -/

section Sobolev

variable {V W U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]

/-- **Sobolev estimate on Schwartz functions**: `‖Op(a) u‖_{H^{s - m}} ≤ C ‖u‖_{H^s}`. -/
theorem IsUniform.exists_norm_quantizeUniformCLM_le {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨C, hC0, hC⟩ := (ha.besselConjugate s).exists_eLpNorm_quantizeSchwartzValue_le
  exact ⟨C, hC0, norm_quantizeUniformCLM_le_of_besselConjugate ha s hC0 hC⟩

/-- **All-order Sobolev extension of a uniform pseudodifferential operator**, extending `Op(a)`
uniquely from Schwartz space to `H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)`. -/
def quantizeUniformSobolev (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W) :=
  ((SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) (s - m) 2).comp
      (quantizeUniformCLM a ha)).toLinearMap.extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap

@[simp]
theorem quantizeUniformSobolev_toBesselPotentialSpaceCLM {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) :=
  LinearMap.extendOfNorm_eq
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top)
    (let ⟨C, _, hC⟩ := ha.exists_norm_quantizeUniformCLM_le s; ⟨C, hC⟩) u

theorem toDistr_quantizeUniformSobolev_toBesselPotentialSpaceCLM_apply {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeUniformSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  simp

theorem norm_quantizeUniformSobolev_le {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖) :
    ‖a.quantizeUniformSobolev ha s‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top) hC0 hC

/-- **Agreement with `Symbol.quantizeSobolev`** when `a` has compact spatial support. -/
theorem quantizeUniformSobolev_eq_quantizeSobolev {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    a.quantizeUniformSobolev ha.isUniform s = a.quantizeSobolev ha s :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦
    BesselPotentialSpace.ext (by ext φ; simp)

/-- **Agreement with `Symbol.quantizeUniformOrderZero`** at `m = 0` and `s = 0`. -/
theorem inclusion_comp_quantizeUniformSobolev_zero (a : Symbol n V W 0) (ha : a.IsUniform) :
    BesselPotentialSpace.inclusion (sub_zero (0 : ℝ)).ge ∘L a.quantizeUniformSobolev ha 0 =
      a.quantizeUniformOrderZero ha := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  simp [quantizeUniformOrderZero_toBesselPotentialSpaceCLM ha
    ha.exists_eLpNorm_quantizeSchwartzValue_le]

private theorem quantizeUniformSobolev_congr {a b : Symbol n V W m} (hab : a = b)
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    a.quantizeUniformSobolev ha s = b.quantizeUniformSobolev hb s := by subst hab; rfl

theorem quantizeUniformSobolev_add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform)
    (s : ℝ) :
    (a + b).quantizeUniformSobolev (ha.add hb) s =
      a.quantizeUniformSobolev ha s + b.quantizeUniformSobolev hb s :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦ by
    simp [quantizeUniformCLM_add ha hb]

theorem quantizeUniformSobolev_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) (s : ℝ) :
    (c • a).quantizeUniformSobolev (ha.smul c) s = c • a.quantizeUniformSobolev ha s :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦ by
    simp [quantizeUniformCLM_smul ha c]

@[simp]
theorem quantizeUniformSobolev_zero (h : (0 : Symbol n V W m).IsUniform) (s : ℝ) :
    (0 : Symbol n V W m).quantizeUniformSobolev h s = 0 :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦ by simp

theorem quantizeUniformSobolev_neg {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    (-a).quantizeUniformSobolev ha.neg s = -a.quantizeUniformSobolev ha s := by
  rw [quantizeUniformSobolev_congr (neg_one_smul ℂ a).symm ha.neg (ha.smul (-1)) s,
    quantizeUniformSobolev_smul ha, neg_one_smul]

theorem quantizeUniformSobolev_sub {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform)
    (s : ℝ) :
    (a - b).quantizeUniformSobolev (ha.sub hb) s =
      a.quantizeUniformSobolev ha s - b.quantizeUniformSobolev hb s := by
  rw [eq_sub_iff_add_eq, ← quantizeUniformSobolev_add (ha.sub hb) hb s]
  exact quantizeUniformSobolev_congr (sub_add_cancel a b) _ ha s

/-- Viewing `a` at a higher order `m' ≥ m` composes with `H^{s - m} ⊆ H^{s - m'}`. -/
theorem quantizeUniformSobolev_inclusion {a : Symbol n V W m} (h : m ≤ m') (ha : a.IsUniform)
    (s : ℝ) :
    (inclusion h a).quantizeUniformSobolev (ha.inclusion h) s =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeUniformSobolev ha s :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦ by
    simp [quantizeUniformCLM_inclusion ha h]

/-- `Op(a) : H^s → H^{s - m}` commutes with the Sobolev inclusions `H^s ⊆ H^r`. -/
theorem quantizeUniformSobolev_comp_inclusion {a : Symbol n V W m} (ha : a.IsUniform) {r s : ℝ}
    (h : r ≤ s) :
    a.quantizeUniformSobolev ha r ∘L BesselPotentialSpace.inclusion h =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeUniformSobolev ha s :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦ by simp

private theorem toDistr_quantizeUniformSobolev_inclusion {a : Symbol n V W m}
    {b : Symbol n V W m'} (hab : a.coefficient = b.coefficient) (ha : a.IsUniform)
    (hb : b.IsUniform) {s t : ℝ} (hts : t ≤ s) (u : H^{s}(CoordinateSpace n, V)) :
    (a.quantizeUniformSobolev ha s u).toDistr =
      (b.quantizeUniformSobolev hb t (BesselPotentialSpace.inclusion hts u)).toDistr := by
  have key : BesselPotentialSpace.inclusion (min_le_left (s - m) (t - m')) ∘L
        a.quantizeUniformSobolev ha s =
      BesselPotentialSpace.inclusion (min_le_right (s - m) (t - m')) ∘L
        b.quantizeUniformSobolev hb t ∘L BesselPotentialSpace.inclusion hts :=
    BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦
      BesselPotentialSpace.ext (by ext φ; simp [hab])
  simpa using congrArg (fun T ↦ (T u).toDistr) key

/-- **Compatibility across symbol and Sobolev orders.** -/
theorem toDistr_quantizeUniformSobolev_congr {a : Symbol n V W m} {b : Symbol n V W m'}
    (hab : a.coefficient = b.coefficient) (ha : a.IsUniform) (hb : b.IsUniform) {s t : ℝ}
    {u : H^{s}(CoordinateSpace n, V)} {v : H^{t}(CoordinateSpace n, V)}
    (huv : u.toDistr = v.toDistr) :
    (a.quantizeUniformSobolev ha s u).toDistr = (b.quantizeUniformSobolev hb t v).toDistr := by
  rcases le_total t s with h | h
  · rw [toDistr_quantizeUniformSobolev_inclusion hab ha hb h u]
    congr 2; exact BesselPotentialSpace.ext (by rw [BesselPotentialSpace.toDistr_inclusion, huv])
  · rw [toDistr_quantizeUniformSobolev_inclusion hab.symm hb ha h v]
    congr 2; exact BesselPotentialSpace.ext (by rw [BesselPotentialSpace.toDistr_inclusion, huv])

/-- **Composition on Bessel-potential spaces**: `Op(a # b) = Op(a) ∘ Op(b)`. -/
theorem quantizeUniformSobolev_uniformSharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    BesselPotentialSpace.inclusion (le_of_eq (by ring) : s - m - m' ≤ s - (m' + m)) ∘L
        (a.uniformSharp b hb).quantizeUniformSobolev (ha.uniformSharp hb) s =
      a.quantizeUniformSobolev ha (s - m) ∘L b.quantizeUniformSobolev hb s :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦ by
    simp [quantizeUniformCLM_uniformSharp ha hb]

theorem toDistr_quantizeUniformSobolev_uniformSharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    ((a.uniformSharp b hb).quantizeUniformSobolev (ha.uniformSharp hb) s u).toDistr =
      (a.quantizeUniformSobolev ha (s - m) (b.quantizeUniformSobolev hb s u)).toDistr := by
  simpa using congrArg (fun T ↦ (T u).toDistr) (quantizeUniformSobolev_uniformSharp ha hb s)

/-- **Uniform smoothing operators map every `H^r` boundedly into every `H^s`.** -/
theorem exists_continuousLinearMap_toDistr_quantizeUniformSobolev_eq {a : Symbol n V W m}
    (ha : a.IsUniform)
    (hsm : ∀ k : ℝ, ∃ b : Symbol n V W k, b.IsUniform ∧ b.coefficient = a.coefficient) (r s : ℝ) :
    ∃ T : H^{r}(CoordinateSpace n, V) →L[ℂ] H^{s}(CoordinateSpace n, W),
      ∀ {t : ℝ} {v : H^{t}(CoordinateSpace n, V)} {u : H^{r}(CoordinateSpace n, V)},
        v.toDistr = u.toDistr → (a.quantizeUniformSobolev ha t v).toDistr = (T u).toDistr := by
  obtain ⟨b, hb, hba⟩ := hsm (r - s)
  refine ⟨BesselPotentialSpace.inclusion (by rw [sub_sub_cancel]) ∘L
    b.quantizeUniformSobolev hb r, fun huv ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion]
  exact toDistr_quantizeUniformSobolev_congr hba.symm ha hb huv

theorem memSobolev_toDistr_quantizeUniformSobolev {a : Symbol n V W m} (ha : a.IsUniform)
    (hsm : ∀ k : ℝ, ∃ b : Symbol n V W k, b.IsUniform ∧ b.coefficient = a.coefficient)
    (s t : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    MemSobolev t 2 (a.quantizeUniformSobolev ha s u).toDistr := by
  obtain ⟨b, hb, hba⟩ := hsm (s - t)
  rw [toDistr_quantizeUniformSobolev_congr hba.symm ha hb (v := u) rfl]
  simpa only [sub_sub_cancel] using (b.quantizeUniformSobolev hb s u).memSobolev_toDistr

/-- A constant symbol `T : V →L[ℂ] W` quantizes on `H^s` to `BesselPotentialSpace.postcomp`. -/
theorem quantizeUniformSobolev_const (T : V →L[ℂ] W) (s : ℝ) :
    (const T : Symbol n V W 0).quantizeUniformSobolev (isUniform_const T) s =
      BesselPotentialSpace.inclusion (sub_zero s).le ∘L
        BesselPotentialSpace.postcomp (CoordinateSpace n) s 2 T :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦
    BesselPotentialSpace.ext (by
      ext φ; simp [quantizeUniformCLM_const, SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM])

/-- **Sobolev action of `Symbol.besselPotential`** as the canonical isomorphism `H^s → H^{s - m}`.
-/
theorem quantizeUniformSobolev_besselPotential (m s : ℝ) :
    (besselPotential m : Symbol n V V m).quantizeUniformSobolev (isUniform_besselPotential m) s =
      ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V (s - m) 2).symm.toContinuousLinearEquiv :
          Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ]
            H^{s - m}(CoordinateSpace n, V)) ∘L
        ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V s 2).toContinuousLinearEquiv :
          H^{s}(CoordinateSpace n, V) →L[ℂ] Lp V 2 (volume : Measure (CoordinateSpace n))) := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  have hq : quantizeUniformCLM (besselPotential m : Symbol n V V m)
      (isUniform_besselPotential m) u = SchwartzMap.fourierMultiplierCLM V
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (m / 2) : ℝ) : ℂ)) u := by
    ext x; rw [quantizeUniformCLM_apply]; exact quantizeSchwartzValue_besselPotential m u x
  rw [quantizeUniformSobolev_toBesselPotentialSpaceCLM, hq,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    ← besselPotential_toTemperedDistributionCLM_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    BesselPotentialSpace.toLpₗᵢ_apply, BesselPotentialSpace.toLpₗᵢ_symm_apply,
    ← (SchwartzMap.toBesselPotentialSpaceCLM s 2 u).bessel_toDistr_eq_toLp,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, besselPotential_besselPotential_apply]
  congr 2; ring

/-- On tempered distributions, `Op(⟨ξ / 2π⟩ ^ m)` acts on `H^s` as
`TemperedDistribution.besselPotential`. -/
theorem toDistr_quantizeUniformSobolev_besselPotential (m s : ℝ)
    (u : H^{s}(CoordinateSpace n, V)) :
    ((besselPotential m : Symbol n V V m).quantizeUniformSobolev
        (isUniform_besselPotential m) s u).toDistr =
      TemperedDistribution.besselPotential (CoordinateSpace n) V m u.toDistr := by
  rw [quantizeUniformSobolev_besselPotential, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    BesselPotentialSpace.toLpₗᵢ_apply, BesselPotentialSpace.toLpₗᵢ_symm_apply,
    ← u.bessel_toDistr_eq_toLp, besselPotential_besselPotential_apply]
  congr 2; ring

end Sobolev

/-! ### Finite-dimensional normed fibres -/

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **All-order Sobolev mapping of uniform pseudodifferential operators** between
finite-dimensional complex normed spaces. -/
theorem exists_quantizeUniformSobolev (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  exact ⟨_, toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply a e₁ e₂
    (toDistr_quantizeUniformSobolev_toBesselPotentialSpaceCLM_apply (ha.map _) s)⟩

end FiniteDimensional

/-! ### Constant symbols on `L²` and non-uniform counterexample -/

section OrderZeroAndCounterexample

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- A constant symbol `T : V →L[ℂ] W` quantizes on `H^0 = L²` to `BesselPotentialSpace.postcomp`. -/
theorem quantizeUniformOrderZero_const (T : V →L[ℂ] W) :
    (const T : Symbol n V W 0).quantizeUniformOrderZero (isUniform_const T) =
      BesselPotentialSpace.postcomp (CoordinateSpace n) 0 2 T := by
  have hC : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (const T : Symbol n V W 0).coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
    refine ⟨‖T‖, norm_nonneg T, fun u ↦ ?_⟩
    rw [← coe_quantizeUniformCLM _ (isUniform_const T), quantizeUniformCLM_const]
    refine (eLpNorm_mono (g := ‖T‖ • (u : CoordinateSpace n → V))
      (u.postcompCLM T).continuous.aestronglyMeasurable fun x ↦ ?_).trans_eq ?_
    · simpa [norm_smul, abs_of_nonneg (norm_nonneg T)] using T.le_opNorm (u x)
    · rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal (norm_nonneg T)]
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [quantizeUniformOrderZero_toBesselPotentialSpaceCLM (isUniform_const T) hC,
    quantizeUniformCLM_const, SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM]

@[simp]
theorem quantizeUniformOrderZero_const_id :
    (const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniformOrderZero
        (isUniform_const _) =
      ContinuousLinearMap.id ℂ H^{0}(CoordinateSpace n, V) := by
  rw [quantizeUniformOrderZero_const]
  exact BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦
    by ext φ; simp

theorem norm_quantizeUniformOrderZero_const_id [Nontrivial V] :
    ‖(const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).quantizeUniformOrderZero
        (isUniform_const _)‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let s₀ : Set (CoordinateSpace n) := Metric.ball 0 1
  have hpos : 0 < (volume : Measure (CoordinateSpace n)).real s₀ :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_lt_top.ne
  let w := (BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V 0 2).symm
    (indicatorConstLp 2 (s := s₀) measurableSet_ball measure_ball_lt_top.ne v)
  have hw : ‖w‖ ≠ 0 := by
    rw [LinearIsometryEquiv.norm_map, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top]
    exact mul_ne_zero (norm_ne_zero_iff.mpr hv) (by positivity)
  rw [quantizeUniformOrderZero_const_id]
  refine le_antisymm ContinuousLinearMap.norm_id_le ?_
  simpa [hw] using (ContinuousLinearMap.id ℂ H^{0}(CoordinateSpace n, V)).ratio_le_opNorm w

omit [CompleteSpace V] [CompleteSpace W] in
/-- In positive dimension, a nonzero constant symbol does not have compact spatial support. -/
theorem not_hasCompactSpatialSupport_const [Nonempty (Fin n)] {T : V →L[ℂ] W} (hT : T ≠ 0) :
    ¬ (const T : Symbol n V W 0).HasCompactSpatialSupport := by
  intro h
  obtain ⟨K, hK, hKT⟩ := hasCompactSpatialSupport_iff.mp h
  obtain ⟨j⟩ := ‹Nonempty (Fin n)›
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set x : CoordinateSpace n := (max R 0 + 1) • EuclideanSpace.single j (1 : ℝ)
  have hx : x ∈ K := by_contra fun hx ↦ hT (by simpa using hKT x hx 0)
  have hnorm : ‖x‖ = max R 0 + 1 := by
    simp [x, norm_smul, abs_of_pos (by positivity : 0 < max R 0 + 1)]
  linarith [mem_closedBall_zero_iff.mp (hR hx), le_max_left R 0]

omit [CompleteSpace V] [CompleteSpace W] in
private lemma exists_schwartz_unit_ball_pos_eLpNorm_postcomp {T : V →L[ℂ] W} (hT : T ≠ 0) :
    ∃ u₀ : 𝓢(CoordinateSpace n, V), (∀ y, u₀ y ≠ 0 → ‖y‖ ≤ 1) ∧
      0 < (eLpNorm (u₀.postcompCLM T) 2 volume).toReal := by
  obtain ⟨v, hv⟩ : ∃ v : V, T v ≠ 0 := by by_contra! h; exact hT (ContinuousLinearMap.ext h)
  let b : ContDiffBump (0 : CoordinateSpace n) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hcs : HasCompactSupport (fun x ↦ b x • v) := b.hasCompactSupport.smul_right
  have hs : ContDiff ℝ ∞ (fun x ↦ b x • v) := b.contDiff.smul contDiff_const
  let u₀ : 𝓢(CoordinateSpace n, V) := hcs.toSchwartzMap hs
  have hu₀ (x : CoordinateSpace n) : u₀ x = b x • v :=
    HasCompactSupport.toSchwartzMap_toFun hcs hs x
  refine ⟨u₀, fun y hy ↦ by
      simpa [b.tsupport_eq] using subset_tsupport b fun hb0 ↦ hy (by simp [hu₀, hb0]),
    ENNReal.toReal_pos (fun h0 ↦ ?_) ((u₀.postcompCLM T).memLp 2).eLpNorm_ne_top⟩
  have hae := (eLpNorm_eq_zero_iff two_ne_zero).mp h0
  have h0' := congrFun (Measure.eq_of_ae_eq hae (u₀.postcompCLM T).continuous continuous_zero) 0
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))
  simp only [SchwartzMap.postcompCLM_apply, hu₀, hb0, one_smul, Pi.zero_apply] at h0'
  exact hv h0'

private theorem le_norm_quantizeSchwartzValue_ofSpatial_smul (j : Fin n) {T : V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ x j • T) {u₀ : 𝓢(CoordinateSpace n, V)}
    (hu₀_supp : ∀ y, u₀ y ≠ 0 → ‖y‖ ≤ 1) {t : ℝ} (ht1 : 1 ≤ t) (x : CoordinateSpace n) :
    ‖(t - 1) • ((u₀.postcompCLM T).compSubConstCLM ℂ (t • EuclideanSpace.single j (1 : ℝ))) x‖ ≤
      ‖quantizeSchwartzValue (ofSpatial _ hf).coefficient
        (u₀.compSubConstCLM ℂ (t • EuclideanSpace.single j (1 : ℝ))) x‖ := by
  set eⱼ := EuclideanSpace.single j (1 : ℝ)
  set ut := u₀.compSubConstCLM ℂ (t • eⱼ)
  have hq : quantizeSchwartzValue (ofSpatial _ hf).coefficient ut x = x j • T (ut x) := by
    rw [funext (coefficient_ofSpatial _ hf),
      quantizeSchwartzValue_comp_fst (fun y : CoordinateSpace n ↦ y j • T) ut x, smul_apply]
  rw [hq, SchwartzMap.compSubConstCLM_apply, SchwartzMap.postcompCLM_apply,
    SchwartzMap.compSubConstCLM_apply, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  by_cases hbx : T (u₀ (x - t • eⱼ)) = 0
  · simp [hbx]
  · have hu : u₀ (x - t • eⱼ) ≠ 0 := fun h0 ↦ hbx (by simp [h0])
    have hxj : |x j - t| ≤ 1 := by
      simpa [eⱼ] using (PiLp.norm_apply_le (x - t • eⱼ) j).trans (hu₀_supp _ hu)
    exact mul_le_mul_of_nonneg_right (by linarith [abs_le.mp hxj, le_abs_self (x j)])
      (norm_nonneg _)

/-- **Necessity of spatial uniformity for `L²` boundedness.** For `j : Fin n` and `T ≠ 0`, the
non-uniform order-zero symbol `x ↦ x_j • T` has no `L² → L²` bound over Schwartz functions. -/
theorem not_exists_eLpNorm_quantizeSchwartzValue_ofSpatial_smul_le (j : Fin n) {T : V →L[ℂ] W}
    (hT : T ≠ 0) (hf : ContDiff ℝ ∞ fun x : CoordinateSpace n ↦ x j • T) :
    ¬ ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (ofSpatial _ hf).coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  rintro ⟨C, hC⟩
  obtain ⟨u₀, hu₀_supp, hB0⟩ := exists_schwartz_unit_ball_pos_eLpNorm_postcomp (n := n) hT
  set A := (eLpNorm u₀ 2 volume).toReal
  set B := (eLpNorm (u₀.postcompCLM T) 2 volume).toReal
  set t : ℝ := max 2 (max C 0 * A / B + 2)
  set eⱼ := EuclideanSpace.single j (1 : ℝ)
  have hmp := measurePreserving_sub_right (volume : Measure (CoordinateSpace n)) (t • eⱼ)
  have ht1 : 1 ≤ t := by linarith [le_max_left 2 (max C 0 * A / B + 2)]
  have hpt := le_norm_quantizeSchwartzValue_ofSpatial_smul j hf hu₀_supp ht1
  set w : 𝓢(CoordinateSpace n, W) := (u₀.postcompCLM T).compSubConstCLM ℂ (t • eⱼ)
  have hlow : ENNReal.ofReal (t - 1) * eLpNorm (u₀.postcompCLM T) 2 volume ≤
      ENNReal.ofReal C * eLpNorm u₀ 2 volume := by
    have hw_eq : (w : CoordinateSpace n → W) = (u₀.postcompCLM T) ∘ fun x ↦ x - t • eⱼ :=
      funext (SchwartzMap.compSubConstCLM_apply _ _)
    rw [← eLpNorm_comp_measurePreserving (u₀.postcompCLM T).continuous.aestronglyMeasurable hmp,
      ← hw_eq, ← eLpNorm_comp_measurePreserving u₀.continuous.aestronglyMeasurable hmp]
    refine (le_of_eq ?_).trans
      ((eLpNorm_mono (w.continuous.const_smul (t - 1)).aestronglyMeasurable hpt).trans (hC _))
    rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal (by linarith)]
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (u₀.memLp 2).eLpNorm_ne_top) hlow
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal'] at hreal
  have hmul : (max C 0 * A / B + 1) * B ≤ (t - 1) * B :=
    mul_le_mul_of_nonneg_right (by linarith [le_max_right 2 (max C 0 * A / B + 2)]) hB0.le
  rw [add_mul, div_mul_cancel₀ _ hB0.ne', one_mul] at hmul
  linarith [hreal]

end OrderZeroAndCounterexample

end Symbol

end TauCeti
