/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Uniform
public import TauCeti.Analysis.Pseudodifferential.L2
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# All-order Sobolev mapping of uniform pseudodifferential operators

For a uniform symbol `a : Symbol n V W m` (`TauCeti.Symbol.IsUniform`) without compact spatial
support, its Kohn–Nirenberg quantization `Op(a)` extends from Schwartz space to a bounded linear
operator `H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)` between Bessel-potential spaces for every real `s`
when the fibres `V` and `W` are complex Hilbert spaces or finite-dimensional complex normed spaces.
Conjugating `Op(a)` by Mathlib's Bessel multipliers in the uniform composition calculus
(`TauCeti.Symbol.uniformSharp`) produces the uniform order-zero symbol `a.besselConjugate ha s`
built from `⟨ξ / 2π⟩ ^ (s - m) # (a ∘ ⟨ξ / 2π⟩ ^ (-s))`, intertwining `J^s` and `J^{s - m}`; the
Calderón–Vaillancourt `L²` bound on `a.besselConjugate ha s` gives
`‖Op(a) u‖_{H^{s - m}} ≤ C ‖u‖_{H^s}`. As in `TauCeti.Analysis.Pseudodifferential.L2`, the bundled
extension `TauCeti.Symbol.quantizeUniformSobolev` is defined for complete normed fibres via
`LinearMap.extendOfNorm` and agrees with `Op(a)` on Schwartz space whenever such a bound holds.

## Main declarations

* `TauCeti.Symbol.besselConjugate`, `TauCeti.Symbol.besselConjugate_def`,
  `TauCeti.Symbol.IsUniform.besselConjugate`,
  `TauCeti.Symbol.quantizeUniformCLM_besselConjugate_fourierMultiplierCLM`: Bessel conjugation of
  `Op(a)` to a uniform symbol of order `0`, together with symbol linearity
  (`besselConjugate_add`, `besselConjugate_smul`, `besselConjugate_zero`, `besselConjugate_neg`,
  `besselConjugate_sub`).
* `TauCeti.Symbol.IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le`,
  `IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional`,
  `TauCeti.Symbol.quantizeUniformSobolev`, `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM`,
  `TauCeti.Symbol.hasSobolevExtension_quantizeUniformCLM_zero`,
  `TauCeti.Symbol.exists_quantizeUniformSobolevHilbert`,
  `TauCeti.Symbol.exists_quantizeUniformSobolev`: the bounded extension `H^s →L[ℂ] H^{s - m}` for
  complex Hilbert and finite-dimensional complex normed fibres, and agreement with
  `quantizeSobolev` and `quantizeUniformOrderZero`.
* `TauCeti.Symbol.quantizeUniformSobolev_uniformSharp`,
  `TauCeti.Symbol.quantizeUniformSobolev_const`,
  `TauCeti.Symbol.quantizeUniformSobolev_besselPotential`,
  `IsUniformlySmoothing.exists_continuousLinearMap_toDistr_quantizeUniformSobolev_eq`,
  `IsUniformlySmoothing.memSobolev_toDistr_quantizeUniformSobolev`: Sobolev composition, explicit
  actions of constant symbols and Bessel potentials, and arbitrary Sobolev gain for uniformly
  smoothing symbols.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
* M. Taylor, *Pseudodifferential Operators*, Princeton University Press, 1981, Chapter II, §6.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

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

/-- Defining formula for `Symbol.besselConjugate`. -/
theorem besselConjugate_def (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    a.besselConjugate ha s =
      inclusion (by linarith)
        ((besselPotential (s - m) : Symbol n W W (s - m)).uniformSharp
          (a.comp (besselPotential (-s))) (ha.comp (isUniform_besselPotential (-s)))) :=
  (rfl)

theorem IsUniform.besselConjugate {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    (a.besselConjugate ha s).IsUniform :=
  ((isUniform_besselPotential (s - m)).uniformSharp
    (ha.comp (isUniform_besselPotential (-s)))).inclusion (by linarith)

private theorem besselConjugate_congr {a b : Symbol n V W m} (hab : a = b) (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) :
    a.besselConjugate ha s = b.besselConjugate hb s := by subst hab; rfl

theorem besselConjugate_add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    (a + b).besselConjugate (ha.add hb) s = a.besselConjugate ha s + b.besselConjugate hb s := by
  ext1
  rw [besselConjugate_def, besselConjugate_def, besselConjugate_def, ← map_add,
    coefficient_inclusion, coefficient_inclusion, ← uniformSharp_add]
  exact coefficient_uniformSharp_congr _ _ rfl (congrArg Symbol.coefficient (add_comp a b _))

theorem besselConjugate_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) (s : ℝ) :
    (c • a).besselConjugate (ha.smul c) s = c • a.besselConjugate ha s := by
  ext1
  rw [besselConjugate_def, besselConjugate_def, ← map_smul, coefficient_inclusion,
    coefficient_inclusion, ← uniformSharp_smul]
  exact coefficient_uniformSharp_congr _ _ rfl (congrArg Symbol.coefficient (smul_comp c a _))

@[simp]
theorem besselConjugate_zero (h : (0 : Symbol n V W m).IsUniform) (s : ℝ) :
    (0 : Symbol n V W m).besselConjugate h s = 0 := by
  rw [besselConjugate_congr (zero_smul ℂ (0 : Symbol n V W m)).symm h (h.smul 0) s,
    besselConjugate_smul h 0 s, zero_smul]

theorem besselConjugate_neg {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    (-a).besselConjugate ha.neg s = -a.besselConjugate ha s := by
  rw [besselConjugate_congr (neg_one_smul ℂ a).symm ha.neg (ha.smul (-1)) s,
    besselConjugate_smul ha (-1) s, neg_one_smul]

theorem besselConjugate_sub {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    (a - b).besselConjugate (ha.sub hb) s = a.besselConjugate ha s - b.besselConjugate hb s := by
  rw [eq_sub_iff_add_eq, ← besselConjugate_add (ha.sub hb) hb s]
  exact besselConjugate_congr (sub_add_cancel a b) _ ha s

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
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun T ↦ T v) (quantizeUniformCLM_comp_besselMultiplier a ha (-s)).symm
  have hc := (isUniform_besselPotential (s - m)).uniformSharp
    (ha.comp (isUniform_besselPotential (-s)))
  ext x
  rw [quantizeUniformCLM_apply, besselConjugate_def, coefficient_inclusion,
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

private theorem norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConjugate
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (a.besselConjugate ha s).coefficient v) 2 volume ≤
        ENNReal.ofReal C * eLpNorm v 2 volume) (u : 𝓢(CoordinateSpace n, V)) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
      C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  set v := SchwartzMap.fourierMultiplierCLM V
    (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u
  rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_eq_eLpNorm,
    SchwartzMap.norm_toBesselPotentialSpaceCLM_eq_eLpNorm,
    ← quantizeUniformCLM_besselConjugate_fourierMultiplierCLM ha s u, coe_quantizeUniformCLM,
    ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (v.memLp 2).eLpNorm_ne_top) (hC v)

/-- **Sobolev estimate on Schwartz functions** for finite-dimensional complex normed fibres:
`‖Op(a) u‖_{H^{s - m}} ≤ C ‖u‖_{H^s}`. -/
theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    (ha.besselConjugate s).exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional
  exact ⟨C, hC0,
    norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConjugate ha s hC0 hC⟩

end BesselConjugate

/-! ### Bounded extension between Bessel-potential spaces -/

section NormedSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- **All-order Sobolev extension of a uniform pseudodifferential operator**, defined on complete
complex normed fibres via `LinearMap.extendOfNorm`. When `Op(a)` satisfies an
`H^s → H^{s - m}` bound on Schwartz functions—in particular for complex Hilbert fibres
(`IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le`) or finite-dimensional
complex normed fibres
(`IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional`)—it
extends `Op(a)` uniquely from Schwartz space to `H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)`; without such
an estimate it is `0`. -/
def quantizeUniformSobolev (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W) :=
  ((SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) (s - m) 2).comp
      (quantizeUniformCLM a ha)).toLinearMap.extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap

private theorem quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_norm_le {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ)
    (hC : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) :=
  LinearMap.extendOfNorm_eq
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top) hC u

private theorem quantizeUniformSobolev_congr {a b : Symbol n V W m} (hab : a = b)
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    a.quantizeUniformSobolev ha s = b.quantizeUniformSobolev hb s := by subst hab; rfl

private theorem quantizeUniformSobolev_add_of_norm_le {a b : Symbol n V W m} (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ)
    (hCa : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖)
    (hCb : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM b hb u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖) :
    (a + b).quantizeUniformSobolev (ha.add hb) s =
      a.quantizeUniformSobolev ha s + b.quantizeUniformSobolev hb s := by
  obtain ⟨Ca, hCa⟩ := hCa
  obtain ⟨Cb, hCb⟩ := hCb
  have hCab : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          (quantizeUniformCLM (a + b) (ha.add hb) u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
    refine ⟨Ca + Cb, fun u ↦ ?_⟩
    rw [quantizeUniformCLM_add ha hb, add_apply, map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hCa u) (hCb u))
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [add_apply, quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_norm_le (ha.add hb) s hCab,
    quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_norm_le ha s ⟨Ca, hCa⟩,
    quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_norm_le hb s ⟨Cb, hCb⟩,
    quantizeUniformCLM_add ha hb, add_apply, map_add]

private theorem quantizeUniformSobolev_smul_of_norm_le {a : Symbol n V W m} (ha : a.IsUniform)
    (c : ℂ) (s : ℝ)
    (hC : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖) :
    (c • a).quantizeUniformSobolev (ha.smul c) s = c • a.quantizeUniformSobolev ha s := by
  obtain ⟨C, hC⟩ := hC
  have hCc : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          (quantizeUniformCLM (c • a) (ha.smul c) u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
    refine ⟨‖c‖ * C, fun u ↦ ?_⟩
    rw [quantizeUniformCLM_smul ha c, smul_apply, map_smul, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg c)
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [smul_apply, quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_norm_le (ha.smul c) s hCc,
    quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_norm_le ha s ⟨C, hC⟩,
    quantizeUniformCLM_smul ha c, smul_apply, map_smul]

/-- Operator-norm bound for `Symbol.quantizeUniformSobolev` from a Schwartz-space estimate. -/
theorem norm_quantizeUniformSobolev_le {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖) :
    ‖a.quantizeUniformSobolev ha s‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top) hC0 hC

@[simp]
theorem quantizeUniformSobolev_zero (h : (0 : Symbol n V W m).IsUniform) (s : ℝ) :
    (0 : Symbol n V W m).quantizeUniformSobolev h s = 0 :=
  norm_le_zero_iff.mp (norm_quantizeUniformSobolev_le h s le_rfl fun _ ↦ by simp)

/-- **Sobolev action of `Symbol.besselPotential`** as the canonical isomorphism `H^s → H^{s - m}`.
-/
theorem quantizeUniformSobolev_besselPotential (m s : ℝ) :
    (besselPotential m : Symbol n V V m).quantizeUniformSobolev (isUniform_besselPotential m) s =
      ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V (s - m) 2).symm.toContinuousLinearEquiv :
          Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ]
            H^{s - m}(CoordinateSpace n, V)) ∘L
        ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V s 2).toContinuousLinearEquiv :
          H^{s}(CoordinateSpace n, V) →L[ℂ] Lp V 2 (volume : Measure (CoordinateSpace n))) := by
  set R :=
    ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V (s - m) 2).symm.toContinuousLinearEquiv :
        Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ]
          H^{s - m}(CoordinateSpace n, V)) ∘L
      ((BesselPotentialSpace.toLpₗᵢ (CoordinateSpace n) V s 2).toContinuousLinearEquiv :
        H^{s}(CoordinateSpace n, V) →L[ℂ] Lp V 2 (volume : Measure (CoordinateSpace n)))
  have hR (u : 𝓢(CoordinateSpace n, V)) :
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          (quantizeUniformCLM (besselPotential m : Symbol n V V m)
            (isUniform_besselPotential m) u) =
        R (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) := by
    refine BesselPotentialSpace.ext ?_
    have hq : quantizeUniformCLM (besselPotential m : Symbol n V V m)
        (isUniform_besselPotential m) u = SchwartzMap.fourierMultiplierCLM V
          (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (m / 2) : ℝ) : ℂ)) u := by
      ext x; rw [quantizeUniformCLM_apply]; exact quantizeSchwartzValue_besselPotential m u x
    rw [hq, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
      ← besselPotential_toTemperedDistributionCLM_eq, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      BesselPotentialSpace.toLpₗᵢ_apply, BesselPotentialSpace.toLpₗᵢ_symm_apply,
      ← (SchwartzMap.toBesselPotentialSpaceCLM s 2 u).bessel_toDistr_eq_toLp,
      SchwartzMap.toDistr_toBesselPotentialSpaceCLM, besselPotential_besselPotential_apply]
    congr 2; ring
  have hbound : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2
          (quantizeUniformCLM (besselPotential m : Symbol n V V m)
            (isUniform_besselPotential m) u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ :=
    ⟨‖R‖, fun u ↦ by rw [hR u]; exact R.le_opNorm _⟩
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_norm_le _ s hbound u, hR u]

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

end NormedSobolev

/-! ### Complex Hilbert fibres -/

section Sobolev

variable {V W U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]

/-- **Sobolev estimate on Schwartz functions** for complex Hilbert fibres:
`‖Op(a) u‖_{H^{s - m}} ≤ C ‖u‖_{H^s}`. -/
theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨C, hC0, hC⟩ := (ha.besselConjugate s).exists_eLpNorm_quantizeSchwartzValue_le
  exact ⟨C, hC0,
    norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConjugate ha s hC0 hC⟩

@[simp]
theorem quantizeUniformSobolev_toBesselPotentialSpaceCLM {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) :=
  quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_norm_le ha s
    (let ⟨C, _, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s; ⟨C, hC⟩) u

theorem toDistr_quantizeUniformSobolev_toBesselPotentialSpaceCLM_apply {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeUniformSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  simp

/-- Uniform symbols of order `m` between complex Hilbert fibres quantize to bounded operators
`H^s → H^{s - m}` for every real `s`, in the composable `SchwartzMap.HasSobolevExtension` form. -/
theorem hasSobolevExtension_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) :=
  SchwartzMap.hasSobolevExtension_iff.mpr ⟨a.quantizeUniformSobolev ha s,
    ContinuousLinearMap.ext (quantizeUniformSobolev_toBesselPotentialSpaceCLM ha s)⟩

/-- **Calderón–Vaillancourt.** The quantization of a uniform symbol of order at most `0` between
complex Hilbert fibres extends to a bounded operator on `H⁰ = L²`. -/
theorem hasSobolevExtension_quantizeUniformCLM_zero {b : Symbol n V W m}
    (hb : b.IsUniform) (hm : m ≤ 0) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) 0 0 :=
  (hasSobolevExtension_quantizeUniformCLM b hb 0).mono (by linarith)

/-- **All-order Sobolev mapping of uniform symbols**, for complex Hilbert fibres. Let `a` be a
symbol of order `m` whose estimates are uniform in the position. For every real `s`, the
quantization `Op(a)` extends from Schwartz functions to a bounded operator
`H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`. -/
theorem exists_quantizeUniformSobolevHilbert (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x :=
  ⟨a.quantizeUniformSobolev ha s,
    toDistr_quantizeUniformSobolev_toBesselPotentialSpaceCLM_apply ha s⟩

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

theorem quantizeUniformSobolev_add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform)
    (s : ℝ) :
    (a + b).quantizeUniformSobolev (ha.add hb) s =
      a.quantizeUniformSobolev ha s + b.quantizeUniformSobolev hb s :=
  quantizeUniformSobolev_add_of_norm_le ha hb s
    (let ⟨C, _, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s; ⟨C, hC⟩)
    (let ⟨C, _, hC⟩ := hb.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s; ⟨C, hC⟩)

theorem quantizeUniformSobolev_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) (s : ℝ) :
    (c • a).quantizeUniformSobolev (ha.smul c) s = c • a.quantizeUniformSobolev ha s :=
  quantizeUniformSobolev_smul_of_norm_le ha c s
    (let ⟨C, _, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s; ⟨C, hC⟩)

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
    (a.uniformSharp b hb).quantizeUniformSobolev (ha.uniformSharp hb) s =
      BesselPotentialSpace.inclusion (le_of_eq (by ring) : s - (m' + m) ≤ s - m - m') ∘L
        (a.quantizeUniformSobolev ha (s - m) ∘L b.quantizeUniformSobolev hb s) :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦ by
    simp [quantizeUniformCLM_uniformSharp ha hb]

theorem toDistr_quantizeUniformSobolev_uniformSharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    ((a.uniformSharp b hb).quantizeUniformSobolev (ha.uniformSharp hb) s u).toDistr =
      (a.quantizeUniformSobolev ha (s - m) (b.quantizeUniformSobolev hb s u)).toDistr := by
  simpa using congrArg (fun T ↦ (T u).toDistr) (quantizeUniformSobolev_uniformSharp ha hb s)

/-- **Uniformly smoothing operators gain every number of derivatives.** A uniformly smoothing
symbol `a` between complex Hilbert fibres quantizes to a bounded operator `T : H^r →L[ℂ] H^s` for
arbitrary real orders `r` and `s`: for every `v ∈ H^t` and `u ∈ H^r` with the same tempered
distribution, `Op(a) v` and `T u` have the same tempered distribution. -/
theorem IsUniformlySmoothing.exists_continuousLinearMap_toDistr_quantizeUniformSobolev_eq
    {a : Symbol n V W m} (ha : a.IsUniformlySmoothing) (r s : ℝ) :
    ∃ T : H^{r}(CoordinateSpace n, V) →L[ℂ] H^{s}(CoordinateSpace n, W),
      ∀ {t : ℝ} {v : H^{t}(CoordinateSpace n, V)} {u : H^{r}(CoordinateSpace n, V)},
        v.toDistr = u.toDistr →
          (a.quantizeUniformSobolev ha.isUniform t v).toDistr = (T u).toDistr := by
  obtain ⟨b, hb, hba⟩ := isUniformlySmoothing_iff.mp ha (r - s)
  refine ⟨BesselPotentialSpace.inclusion (by rw [sub_sub_cancel]) ∘L
    b.quantizeUniformSobolev hb r, fun huv ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion]
  exact toDistr_quantizeUniformSobolev_congr hba.symm ha.isUniform hb huv

/-- **Uniformly smoothing operators gain every order of regularity.** If `a` is uniformly smoothing
between complex Hilbert fibres, then for every `u ∈ H^s` and every real `t` the tempered
distribution `(a.quantizeUniformSobolev ha.isUniform s u).toDistr` belongs to `H^t`
(`MemSobolev t 2`). -/
theorem IsUniformlySmoothing.memSobolev_toDistr_quantizeUniformSobolev {a : Symbol n V W m}
    (ha : a.IsUniformlySmoothing) (s t : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    MemSobolev t 2 (a.quantizeUniformSobolev ha.isUniform s u).toDistr := by
  obtain ⟨b, hb, hba⟩ := isUniformlySmoothing_iff.mp ha (s - t)
  rw [toDistr_quantizeUniformSobolev_congr hba.symm ha.isUniform hb (v := u) rfl]
  simpa only [sub_sub_cancel] using (b.quantizeUniformSobolev hb s u).memSobolev_toDistr

/-- A constant symbol `T : V →L[ℂ] W` quantizes on `H^s` to `BesselPotentialSpace.postcomp`. -/
theorem quantizeUniformSobolev_const (T : V →L[ℂ] W) (s : ℝ) :
    (const T : Symbol n V W 0).quantizeUniformSobolev (isUniform_const T) s =
      BesselPotentialSpace.inclusion (sub_zero s).le ∘L
        BesselPotentialSpace.postcomp (CoordinateSpace n) s 2 T :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦
    BesselPotentialSpace.ext (by
      ext φ; simp [quantizeUniformCLM_const, SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM])

end Sobolev

/-! ### Finite-dimensional normed fibres -/

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- On Schwartz functions, `Symbol.quantizeUniformSobolev` agrees with `Op(a)` for
finite-dimensional complex normed fibres. -/
theorem quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_finiteDimensional
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) :=
  quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_norm_le ha s
    (let ⟨C, _, hC⟩ :=
      ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional s;
      ⟨C, hC⟩) u

/-- On Schwartz functions, `Symbol.quantizeUniformSobolev` represents the function `Op(a) u` as a
tempered distribution for finite-dimensional complex normed fibres. -/
theorem toDistr_quantizeUniformSobolev_toBesselPotentialSpaceCLM_apply_of_finiteDimensional
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeUniformSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  rw [quantizeUniformSobolev_toBesselPotentialSpaceCLM_of_finiteDimensional ha s u,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply, coe_quantizeUniformCLM]

theorem quantizeUniformSobolev_add_of_finiteDimensional {a b : Symbol n V W m} (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) :
    (a + b).quantizeUniformSobolev (ha.add hb) s =
      a.quantizeUniformSobolev ha s + b.quantizeUniformSobolev hb s :=
  quantizeUniformSobolev_add_of_norm_le ha hb s
    (let ⟨C, _, hC⟩ :=
      ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional s;
      ⟨C, hC⟩)
    (let ⟨C, _, hC⟩ :=
      hb.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional s;
      ⟨C, hC⟩)

theorem quantizeUniformSobolev_smul_of_finiteDimensional {a : Symbol n V W m} (ha : a.IsUniform)
    (c : ℂ) (s : ℝ) :
    (c • a).quantizeUniformSobolev (ha.smul c) s = c • a.quantizeUniformSobolev ha s :=
  quantizeUniformSobolev_smul_of_norm_le ha c s
    (let ⟨C, _, hC⟩ :=
      ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional s;
      ⟨C, hC⟩)

theorem quantizeUniformSobolev_neg_of_finiteDimensional {a : Symbol n V W m} (ha : a.IsUniform)
    (s : ℝ) :
    (-a).quantizeUniformSobolev ha.neg s = -a.quantizeUniformSobolev ha s := by
  rw [quantizeUniformSobolev_congr (neg_one_smul ℂ a).symm ha.neg (ha.smul (-1)) s,
    quantizeUniformSobolev_smul_of_finiteDimensional ha, neg_one_smul]

theorem quantizeUniformSobolev_sub_of_finiteDimensional {a b : Symbol n V W m} (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) :
    (a - b).quantizeUniformSobolev (ha.sub hb) s =
      a.quantizeUniformSobolev ha s - b.quantizeUniformSobolev hb s := by
  rw [eq_sub_iff_add_eq, ← quantizeUniformSobolev_add_of_finiteDimensional (ha.sub hb) hb s]
  exact quantizeUniformSobolev_congr (sub_add_cancel a b) _ ha s

/-- **All-order Sobolev mapping of uniform pseudodifferential operators** between
finite-dimensional complex normed spaces. -/
theorem exists_quantizeUniformSobolev (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x :=
  ⟨a.quantizeUniformSobolev ha s,
    toDistr_quantizeUniformSobolev_toBesselPotentialSpaceCLM_apply_of_finiteDimensional ha s⟩

end FiniteDimensional

end Symbol

end TauCeti
