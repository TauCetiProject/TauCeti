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

For a uniform symbol `a : Symbol n V W m` (`IsUniform`), conjugating `Op(a)` by Mathlib's Bessel
multipliers in `uniformSharp` yields the uniform order-zero symbol `a.besselConjugate ha s` built
from `⟨ξ / 2π⟩ ^ (s - m) # (a ∘ ⟨ξ / 2π⟩ ^ (-s))`, so `Op(a)` extends to `H^s → H^{s - m}` iff
`a.besselConjugate ha s` extends on `H^0 = L²`. Calderón–Vaillancourt then yields bounded
extensions `H^s(ℝⁿ; V) →L[ℂ] H^{s - m}(ℝⁿ; W)` for complex Hilbert and finite-dimensional complex
normed fibres.

`quantizeUniformSobolev` is defined over arbitrary complete complex normed fibres via
`SchwartzMap.extendBesselPotentialSpace`. Structural properties (Schwartz agreement, linearity,
inclusions, `uniformSharp`, and arbitrary gain for `IsUniformlySmoothing`) are stated once over
complete complex normed fibres assuming `HasSobolevExtension` (or order-zero `L²` boundedness for
uniformly smoothing symbols); agreement with `quantizeUniformOrderZero`, constants, and Bessel
potentials hold unconditionally.

## Main results

* `besselConjugate`, `besselConjugate_def`, `IsUniform.besselConjugate`,
  `quantizeUniformCLM_besselConjugate`, `quantizeUniformCLM_besselConjugate_fourierMultiplierCLM`,
  `hasSobolevExtension_quantizeUniformCLM_iff_besselConjugate`,
  `besselConjugate_{add,smul,zero,neg,sub}`.
* `quantizeUniformSobolev`, `quantizeUniformSobolev_def`, normed-fibre structural theorems,
  `quantizeUniformSobolev_{const,besselPotential}`, `inclusion_comp_quantizeUniformSobolev_zero`,
  and arbitrary gain for `IsUniformlySmoothing`.
* Hilbert fibres: `IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le`,
  `hasSobolevExtension_quantizeUniformCLM`, `hasSobolevExtension_quantizeUniformCLM_zero`,
  `exists_quantizeUniformSobolevHilbert`, `quantizeUniformSobolev_eq_quantizeSobolev`.
* Finite-dimensional fibres:
  `IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional`,
  `hasSobolevExtension_quantizeUniformCLM_of_finiteDimensional`, `exists_quantizeUniformSobolev`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
* M. Taylor, *Pseudodifferential Operators*, Princeton University Press, 1981, Chapter II, §6.
-/

public section
noncomputable section

open MeasureTheory
open TemperedDistribution (MemSobolev besselPotential_besselPotential_apply
  besselPotential_toTemperedDistributionCLM_eq)
open ContinuousLinearMap (comp_apply)
open BesselPotentialSpace (continuousLinearMap_ext toDistr_inclusion toLpₗᵢ)
open SchwartzMap (HasSobolevExtension toBesselPotentialSpaceCLM extendBesselPotentialSpace
  extendBesselPotentialSpace_eq_of_forall norm_extendBesselPotentialSpace_le
  hasSobolevExtension_iff_exists_norm_le hasSobolevExtension_besselMultiplier fourierMultiplierCLM
  toDistr_toBesselPotentialSpaceCLM norm_toBesselPotentialSpaceCLM_eq_eLpNorm
  toBesselPotentialSpaceCLM_postcompCLM
  fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg)
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
  inclusion (by linarith) ((besselPotential (s - m) : Symbol n W W (s - m)).uniformSharp
    (a.comp (besselPotential (-s))) (ha.comp (isUniform_besselPotential (-s))))

/-- Defining formula for `Symbol.besselConjugate`. -/
theorem besselConjugate_def (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    a.besselConjugate ha s = inclusion (by linarith)
      ((besselPotential (s - m) : Symbol n W W (s - m)).uniformSharp
        (a.comp (besselPotential (-s))) (ha.comp (isUniform_besselPotential (-s)))) := (rfl)

theorem IsUniform.besselConjugate {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    (a.besselConjugate ha s).IsUniform :=
  ((isUniform_besselPotential (s - m)).uniformSharp
    (ha.comp (isUniform_besselPotential (-s)))).inclusion (by linarith)

private theorem besselConjugate_congr {a b : Symbol n V W m} (h : a = b) (ha : a.IsUniform)
    (hb : b.IsUniform) (s : ℝ) : a.besselConjugate ha s = b.besselConjugate hb s := by subst h; rfl

theorem besselConjugate_add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    (a + b).besselConjugate (ha.add hb) s = a.besselConjugate ha s + b.besselConjugate hb s := by
  ext1; rw [besselConjugate_def, besselConjugate_def, besselConjugate_def, ← map_add,
    coefficient_inclusion, coefficient_inclusion, ← uniformSharp_add]
  exact coefficient_uniformSharp_congr _ _ rfl (congrArg Symbol.coefficient (add_comp a b _))

theorem besselConjugate_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) (s : ℝ) :
    (c • a).besselConjugate (ha.smul c) s = c • a.besselConjugate ha s := by
  ext1; rw [besselConjugate_def, besselConjugate_def, ← map_smul, coefficient_inclusion,
    coefficient_inclusion, ← uniformSharp_smul]
  exact coefficient_uniformSharp_congr _ _ rfl (congrArg Symbol.coefficient (smul_comp c a _))

@[simp] theorem besselConjugate_zero (h : (0 : Symbol n V W m).IsUniform) (s : ℝ) :
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
      fourierMultiplierCLM W (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ))
        (quantizeUniformCLM a ha (fourierMultiplierCLM V
          (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)) v)) := by
  have hcomp := congrArg (fun T ↦ T v) (quantizeUniformCLM_comp_besselMultiplier a ha (-s)).symm
  have hc := (isUniform_besselPotential (s - m)).uniformSharp
    (ha.comp (isUniform_besselPotential (-s)))
  ext x; rw [quantizeUniformCLM_apply, besselConjugate_def, coefficient_inclusion,
    ← quantizeUniformCLM_apply _ hc, quantizeUniformCLM_besselPotential_uniformSharp,
    comp_apply, hcomp, comp_apply]

/-- **Intertwining with Bessel multipliers**: `Op(a.besselConjugate ha s) (J^s u) = J^{s - m}
(Op(a) u)`. -/
theorem quantizeUniformCLM_besselConjugate_fourierMultiplierCLM {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s)
        (fourierMultiplierCLM V (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
          u) = fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ))
        (quantizeUniformCLM a ha u) := by
  have hinv := fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg (-s) u
  rw [neg_neg] at hinv; rw [quantizeUniformCLM_besselConjugate, hinv]

/-- Over arbitrary complete complex normed fibres, `Op(a)` extends to `H^s → H^{s - m}` if and only
if its Bessel conjugate `a.besselConjugate ha s` extends on `H^0 = L²`. -/
theorem hasSobolevExtension_quantizeUniformCLM_iff_besselConjugate {a : Symbol n V W m}
    (ha : a.IsUniform) (s : ℝ) : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) ↔
      HasSobolevExtension
        (quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s)) 0 0 := by
  let f (t : ℝ) (ζ : CoordinateSpace n) : ℂ := ((1 + ‖ζ‖ ^ 2) ^ (t / 2) : ℝ)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have heq : quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s) =
        fourierMultiplierCLM W (f (s - m)) ∘L quantizeUniformCLM a ha ∘L
          fourierMultiplierCLM V (f (-s)) :=
      ContinuousLinearMap.ext (quantizeUniformCLM_besselConjugate ha s)
    rw [heq]; exact ((hasSobolevExtension_besselMultiplier (s - m) (by ring)).comp h).comp
      (hasSobolevExtension_besselMultiplier (-s) (by ring))
  · have heq : quantizeUniformCLM a ha = fourierMultiplierCLM W (f (-(s - m))) ∘L
        quantizeUniformCLM (a.besselConjugate ha s) (ha.besselConjugate s) ∘L
          fourierMultiplierCLM V (f s) := by
      ext1 u; simp only [comp_apply, f,
        quantizeUniformCLM_besselConjugate_fourierMultiplierCLM ha s u]
      simpa only [neg_neg] using (fourierMultiplierCLM_one_add_norm_sq_rpow_fourierMultiplierCLM_neg
        (-(s - m)) (quantizeUniformCLM a ha u)).symm
    rw [heq]; exact ((hasSobolevExtension_besselMultiplier (-(s - m)) (by ring)).comp h).comp
      (hasSobolevExtension_besselMultiplier s (by ring))

private theorem norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConjugate
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue (a.besselConjugate ha s).coefficient v) 2 volume ≤
        ENNReal.ofReal C * eLpNorm v 2 volume) (u : 𝓢(CoordinateSpace n, V)) :
    ‖toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
      C * ‖toBesselPotentialSpaceCLM s 2 u‖ := by
  set v := fourierMultiplierCLM V
    (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) u
  rw [norm_toBesselPotentialSpaceCLM_eq_eLpNorm, norm_toBesselPotentialSpaceCLM_eq_eLpNorm,
    ← quantizeUniformCLM_besselConjugate_fourierMultiplierCLM ha s u, coe_quantizeUniformCLM,
    ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (v.memLp 2).eLpNorm_ne_top) (hC v)

end BesselConjugate

/-! ### Bounded extension between Bessel-potential spaces -/

section NormedSobolev

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U]

/-- **All-order Sobolev extension of a uniform pseudodifferential operator**, via
`SchwartzMap.extendBesselPotentialSpace`. When `Op(a)` admits a Sobolev extension `H^s → H^{s - m}`
(`HasSobolevExtension`)—e.g. for Hilbert (`hasSobolevExtension_quantizeUniformCLM`) or
finite-dimensional (`hasSobolevExtension_quantizeUniformCLM_of_finiteDimensional`) fibres—it is the
unique extension from Schwartz space; otherwise `0`. -/
def quantizeUniformSobolev (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W) :=
  extendBesselPotentialSpace (quantizeUniformCLM a ha) s (s - m) 2

/-- Defining formula for `Symbol.quantizeUniformSobolev`. -/
theorem quantizeUniformSobolev_def (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    a.quantizeUniformSobolev ha s =
      extendBesselPotentialSpace (quantizeUniformCLM a ha) s (s - m) 2 := (rfl)

private theorem quantizeUniformSobolev_congr {a b : Symbol n V W m} (hab : a = b)
    (ha : a.IsUniform) (hb : b.IsUniform) (s : ℝ) :
    a.quantizeUniformSobolev ha s = b.quantizeUniformSobolev hb s := by subst hab; rfl

/-- On Schwartz functions, `quantizeUniformSobolev` agrees with `Op(a)` whenever `Op(a)` extends
boundedly from `H^s` to `H^{s - m}`. -/
@[simp] theorem quantizeUniformSobolev_toBesselPotentialSpaceCLM {a : Symbol n V W m}
    (ha : a.IsUniform) {s : ℝ} (hE : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m))
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformSobolev ha s (toBesselPotentialSpaceCLM s 2 u) =
      toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u) :=
  hE.extendBesselPotentialSpace_toBesselPotentialSpaceCLM u

/-- On Schwartz functions, `quantizeUniformSobolev` represents `Op(a) u` as a tempered distribution
whenever `Op(a)` extends boundedly from `H^s` to `H^{s - m}`. -/
theorem toDistr_quantizeUniformSobolev_toBesselPotentialSpaceCLM_apply {a : Symbol n V W m}
    (ha : a.IsUniform) {s : ℝ} (hE : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m))
    (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeUniformSobolev ha s (toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  rw [quantizeUniformSobolev_toBesselPotentialSpaceCLM ha hE u, toDistr_toBesselPotentialSpaceCLM,
    SchwartzMap.coe_apply, coe_quantizeUniformCLM]

/-- Operator-norm bound for `Symbol.quantizeUniformSobolev` from a Schwartz-space estimate. -/
theorem norm_quantizeUniformSobolev_le {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ u : 𝓢(CoordinateSpace n, V),
      ‖toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖toBesselPotentialSpaceCLM s 2 u‖) : ‖a.quantizeUniformSobolev ha s‖ ≤ C :=
  norm_extendBesselPotentialSpace_le ENNReal.ofNat_ne_top hC0 hC

@[simp] theorem quantizeUniformSobolev_zero (h : (0 : Symbol n V W m).IsUniform) (s : ℝ) :
    (0 : Symbol n V W m).quantizeUniformSobolev h s = 0 := by
  simp [quantizeUniformSobolev, quantizeUniformCLM_zero]

theorem quantizeUniformSobolev_add {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform)
    {s : ℝ} (hEa : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m))
    (hEb : HasSobolevExtension (quantizeUniformCLM b hb) s (s - m)) :
    (a + b).quantizeUniformSobolev (ha.add hb) s =
      a.quantizeUniformSobolev ha s + b.quantizeUniformSobolev hb s :=
  extendBesselPotentialSpace_eq_of_forall ENNReal.ofNat_ne_top fun u ↦ by
    simp [quantizeUniformSobolev_toBesselPotentialSpaceCLM ha hEa u,
      quantizeUniformSobolev_toBesselPotentialSpaceCLM hb hEb u, quantizeUniformCLM_add ha hb]

theorem quantizeUniformSobolev_smul {a : Symbol n V W m} (ha : a.IsUniform) (c : ℂ) {s : ℝ}
    (hE : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m)) :
    (c • a).quantizeUniformSobolev (ha.smul c) s = c • a.quantizeUniformSobolev ha s :=
  extendBesselPotentialSpace_eq_of_forall ENNReal.ofNat_ne_top fun u ↦ by
    simp [quantizeUniformSobolev_toBesselPotentialSpaceCLM ha hE u, quantizeUniformCLM_smul ha c]

theorem quantizeUniformSobolev_neg {a : Symbol n V W m} (ha : a.IsUniform) {s : ℝ}
    (hE : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m)) :
    (-a).quantizeUniformSobolev ha.neg s = -a.quantizeUniformSobolev ha s := by
  rw [quantizeUniformSobolev_congr (neg_one_smul ℂ a).symm ha.neg (ha.smul (-1)) s,
    quantizeUniformSobolev_smul ha (-1) hE, neg_one_smul]

theorem quantizeUniformSobolev_sub {a b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform)
    {s : ℝ} (hEa : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m))
    (hEb : HasSobolevExtension (quantizeUniformCLM b hb) s (s - m)) :
    (a - b).quantizeUniformSobolev (ha.sub hb) s =
      a.quantizeUniformSobolev ha s - b.quantizeUniformSobolev hb s := by
  have hsub : quantizeUniformCLM (a - b) (ha.sub hb) =
      quantizeUniformCLM a ha - quantizeUniformCLM b hb := by
    rw [eq_sub_iff_add_eq, ← quantizeUniformCLM_add (ha.sub hb) hb]
    exact quantizeUniformCLM_congr _ _ (by simp)
  exact extendBesselPotentialSpace_eq_of_forall ENNReal.ofNat_ne_top fun u ↦ by
    simp [quantizeUniformSobolev_toBesselPotentialSpaceCLM ha hEa u,
      quantizeUniformSobolev_toBesselPotentialSpaceCLM hb hEb u, hsub]

/-- **Agreement with `Symbol.quantizeUniformOrderZero`** at `m = 0` and `s = 0`, unconditionally
over arbitrary complete complex normed fibres. -/
theorem inclusion_comp_quantizeUniformSobolev_zero (a : Symbol n V W 0) (ha : a.IsUniform) :
    BesselPotentialSpace.inclusion (sub_zero (0 : ℝ)).ge ∘L a.quantizeUniformSobolev ha 0 =
      a.quantizeUniformOrderZero ha := by
  rw [quantizeUniformOrderZero_def]
  exact SchwartzMap.inclusion_comp_extendBesselPotentialSpace_of_eq (sub_zero 0) 2

/-- Viewing `a` at a higher order `m' ≥ m` composes with `H^{s - m} ⊆ H^{s - m'}`. -/
theorem quantizeUniformSobolev_inclusion {a : Symbol n V W m} (h : m ≤ m') (ha : a.IsUniform)
    {s : ℝ} (hE : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m)) :
    (inclusion h a).quantizeUniformSobolev (ha.inclusion h) s =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeUniformSobolev ha s :=
  extendBesselPotentialSpace_eq_of_forall ENNReal.ofNat_ne_top fun u ↦ by
    simp [quantizeUniformSobolev_toBesselPotentialSpaceCLM ha hE u,
      quantizeUniformCLM_inclusion ha h]

/-- `Op(a) : H^s → H^{s - m}` commutes with the Sobolev inclusions `H^s ⊆ H^r`. -/
theorem quantizeUniformSobolev_comp_inclusion {a : Symbol n V W m} (ha : a.IsUniform) {r s : ℝ}
    (h : r ≤ s) (hEr : HasSobolevExtension (quantizeUniformCLM a ha) r (r - m))
    (hEs : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m)) :
    a.quantizeUniformSobolev ha r ∘L BesselPotentialSpace.inclusion h =
      BesselPotentialSpace.inclusion (by linarith) ∘L a.quantizeUniformSobolev ha s :=
  continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦ by
    simp [quantizeUniformSobolev_toBesselPotentialSpaceCLM ha hEr,
      quantizeUniformSobolev_toBesselPotentialSpaceCLM ha hEs]

private theorem toDistr_quantizeUniformSobolev_inclusion {a : Symbol n V W m}
    {b : Symbol n V W m'} (hab : a.coefficient = b.coefficient) (ha : a.IsUniform)
    (hb : b.IsUniform) {s t : ℝ} (hts : t ≤ s)
    (hEa : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m))
    (hEb : HasSobolevExtension (quantizeUniformCLM b hb) t (t - m'))
    (u : H^{s}(CoordinateSpace n, V)) :
    (a.quantizeUniformSobolev ha s u).toDistr =
      (b.quantizeUniformSobolev hb t (BesselPotentialSpace.inclusion hts u)).toDistr := by
  have key : BesselPotentialSpace.inclusion (min_le_left (s - m) (t - m')) ∘L
        a.quantizeUniformSobolev ha s = BesselPotentialSpace.inclusion (min_le_right _ _) ∘L
        b.quantizeUniformSobolev hb t ∘L BesselPotentialSpace.inclusion hts :=
    continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦ BesselPotentialSpace.ext
      (by ext φ; simp [quantizeUniformSobolev_toBesselPotentialSpaceCLM ha hEa,
        quantizeUniformSobolev_toBesselPotentialSpaceCLM hb hEb, hab])
  simpa using congrArg (fun T ↦ (T u).toDistr) key

/-- **Compatibility across symbol and Sobolev orders.** -/
theorem toDistr_quantizeUniformSobolev_congr {a : Symbol n V W m} {b : Symbol n V W m'}
    (hab : a.coefficient = b.coefficient) (ha : a.IsUniform) (hb : b.IsUniform) {s t : ℝ}
    (hEa : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m))
    (hEb : HasSobolevExtension (quantizeUniformCLM b hb) t (t - m'))
    {u : H^{s}(CoordinateSpace n, V)} {v : H^{t}(CoordinateSpace n, V)}
    (huv : u.toDistr = v.toDistr) :
    (a.quantizeUniformSobolev ha s u).toDistr = (b.quantizeUniformSobolev hb t v).toDistr := by
  rcases le_total t s with h | h
  · rw [toDistr_quantizeUniformSobolev_inclusion hab ha hb h hEa hEb u]
    congr 2; exact BesselPotentialSpace.ext (by rw [toDistr_inclusion, huv])
  · rw [toDistr_quantizeUniformSobolev_inclusion hab.symm hb ha h hEb hEa v]
    congr 2; exact BesselPotentialSpace.ext (by rw [toDistr_inclusion, huv])

/-- **Composition on Bessel-potential spaces**: `Op(a # b) = Op(a) ∘ Op(b)`. -/
theorem quantizeUniformSobolev_uniformSharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.IsUniform) (hb : b.IsUniform) {s : ℝ}
    (hEa : HasSobolevExtension (quantizeUniformCLM a ha) (s - m) (s - m - m'))
    (hEb : HasSobolevExtension (quantizeUniformCLM b hb) s (s - m)) :
    (a.uniformSharp b hb).quantizeUniformSobolev (ha.uniformSharp hb) s =
      BesselPotentialSpace.inclusion (le_of_eq (by ring) : s - (m' + m) ≤ s - m - m') ∘L
        (a.quantizeUniformSobolev ha (s - m) ∘L b.quantizeUniformSobolev hb s) :=
  extendBesselPotentialSpace_eq_of_forall ENNReal.ofNat_ne_top fun u ↦ by
    simp [quantizeUniformSobolev_toBesselPotentialSpaceCLM hb hEb u,
      quantizeUniformSobolev_toBesselPotentialSpaceCLM ha hEa,
      quantizeUniformCLM_uniformSharp ha hb]

theorem toDistr_quantizeUniformSobolev_uniformSharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.IsUniform) (hb : b.IsUniform) {s : ℝ}
    (hEa : HasSobolevExtension (quantizeUniformCLM a ha) (s - m) (s - m - m'))
    (hEb : HasSobolevExtension (quantizeUniformCLM b hb) s (s - m))
    (u : H^{s}(CoordinateSpace n, V)) :
    ((a.uniformSharp b hb).quantizeUniformSobolev (ha.uniformSharp hb) s u).toDistr =
      (a.quantizeUniformSobolev ha (s - m) (b.quantizeUniformSobolev hb s u)).toDistr := by
  simpa using congrArg (fun T ↦ (T u).toDistr) (quantizeUniformSobolev_uniformSharp ha hb hEa hEb)

/-- A constant symbol `T : V →L[ℂ] W` quantizes on `H^s` to `BesselPotentialSpace.postcomp`,
unconditionally over arbitrary complete complex normed fibres. -/
theorem quantizeUniformSobolev_const (T : V →L[ℂ] W) (s : ℝ) :
    (const T : Symbol n V W 0).quantizeUniformSobolev (isUniform_const T) s =
      BesselPotentialSpace.inclusion (sub_zero s).le ∘L
        BesselPotentialSpace.postcomp (CoordinateSpace n) s 2 T :=
  extendBesselPotentialSpace_eq_of_forall ENNReal.ofNat_ne_top fun u ↦ by
    rw [comp_apply, ← toBesselPotentialSpaceCLM_postcompCLM,
      BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM, quantizeUniformCLM_const]

private theorem toDistr_toLpₗᵢ_symm {s r : ℝ} (u : H^{s}(CoordinateSpace n, V)) :
    (((toLpₗᵢ (CoordinateSpace n) V r 2).symm.toContinuousLinearEquiv :
        Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ] H^{r}(CoordinateSpace n, V))
      (((toLpₗᵢ (CoordinateSpace n) V s 2).toContinuousLinearEquiv :
        H^{s}(CoordinateSpace n, V) →L[ℂ] Lp V 2 (volume : Measure (CoordinateSpace n))) u)).toDistr
      = TemperedDistribution.besselPotential (CoordinateSpace n) V (s - r) u.toDistr := by
  simp [← u.bessel_toDistr_eq_toLp, besselPotential_besselPotential_apply, ← sub_eq_add_neg]

/-- **Sobolev action of `Symbol.besselPotential`** as the canonical isomorphism `H^s → H^{s - m}`,
unconditionally over arbitrary complete complex normed fibres. -/
theorem quantizeUniformSobolev_besselPotential (m s : ℝ) :
    (besselPotential m : Symbol n V V m).quantizeUniformSobolev (isUniform_besselPotential m) s =
      ((toLpₗᵢ (CoordinateSpace n) V (s - m) 2).symm.toContinuousLinearEquiv :
          Lp V 2 (volume : Measure (CoordinateSpace n)) →L[ℂ] H^{s - m}(CoordinateSpace n, V)) ∘L
        ((toLpₗᵢ (CoordinateSpace n) V s 2).toContinuousLinearEquiv :
          H^{s}(CoordinateSpace n, V) →L[ℂ] Lp V 2 (volume : Measure (CoordinateSpace n))) :=
  extendBesselPotentialSpace_eq_of_forall ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext <| by
      have hq : quantizeUniformCLM (besselPotential m : Symbol n V V m)
          (isUniform_besselPotential m) u = fourierMultiplierCLM V
            (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (m / 2) : ℝ) : ℂ)) u := by
        ext x; rw [quantizeUniformCLM_apply]; exact quantizeSchwartzValue_besselPotential m u x
      rw [comp_apply, toDistr_toLpₗᵢ_symm, sub_sub_cancel, toDistr_toBesselPotentialSpaceCLM,
        hq, toDistr_toBesselPotentialSpaceCLM, ← besselPotential_toTemperedDistributionCLM_eq]

/-- On tempered distributions, `Op(⟨ξ / 2π⟩ ^ m)` acts on `H^s` as
`TemperedDistribution.besselPotential`. -/
theorem toDistr_quantizeUniformSobolev_besselPotential (m s : ℝ) (u : H^{s}(CoordinateSpace n, V)) :
    ((besselPotential m : Symbol n V V m).quantizeUniformSobolev
        (isUniform_besselPotential m) s u).toDistr =
      TemperedDistribution.besselPotential (CoordinateSpace n) V m u.toDistr := by
  rw [quantizeUniformSobolev_besselPotential, comp_apply, toDistr_toLpₗᵢ_symm, sub_sub_cancel]

/-- **Uniformly smoothing operators gain every number of derivatives.** Assuming uniform order-zero
symbols extend on `H^0 = L²`, a uniformly smoothing `a` quantizes to `T : H^r →L[ℂ] H^s` agreeing
with `Op(a)` on tempered distributions across all orders `t`. -/
theorem IsUniformlySmoothing.exists_continuousLinearMap_toDistr_quantizeUniformSobolev_eq
    {a : Symbol n V W m} (ha : a.IsUniformlySmoothing) (r s : ℝ)
    (hL2 : ∀ (c : Symbol n V W 0) (hc : c.IsUniform),
      HasSobolevExtension (quantizeUniformCLM c hc) 0 0) :
    ∃ T : H^{r}(CoordinateSpace n, V) →L[ℂ] H^{s}(CoordinateSpace n, W),
      ∀ {t : ℝ} {v : H^{t}(CoordinateSpace n, V)} {u : H^{r}(CoordinateSpace n, V)},
        v.toDistr = u.toDistr →
          (a.quantizeUniformSobolev ha.isUniform t v).toDistr = (T u).toDistr := by
  obtain ⟨b, hb, hba⟩ := isUniformlySmoothing_iff.mp ha (r - s)
  refine ⟨BesselPotentialSpace.inclusion (by rw [sub_sub_cancel]) ∘L
    b.quantizeUniformSobolev hb r, fun {t _ _} huv ↦ ?_⟩
  rw [comp_apply, toDistr_inclusion]
  exact toDistr_quantizeUniformSobolev_congr hba.symm ha.isUniform hb
    ((hasSobolevExtension_quantizeUniformCLM_iff_besselConjugate ha.isUniform t).mpr (hL2 _ _))
    ((hasSobolevExtension_quantizeUniformCLM_iff_besselConjugate hb r).mpr (hL2 _ _)) huv

/-- **Uniformly smoothing operators gain every order of regularity.** Assuming uniform order-zero
symbols extend on `H^0 = L²`, `(a.quantizeUniformSobolev ha.isUniform s u).toDistr` belongs to
`H^t` (`MemSobolev t 2`). -/
theorem IsUniformlySmoothing.memSobolev_toDistr_quantizeUniformSobolev {a : Symbol n V W m}
    (ha : a.IsUniformlySmoothing) (s t : ℝ)
    (hL2 : ∀ (c : Symbol n V W 0) (hc : c.IsUniform),
      HasSobolevExtension (quantizeUniformCLM c hc) 0 0) (u : H^{s}(CoordinateSpace n, V)) :
    MemSobolev t 2 (a.quantizeUniformSobolev ha.isUniform s u).toDistr := by
  obtain ⟨b, hb, hba⟩ := isUniformlySmoothing_iff.mp ha (s - t)
  rw [toDistr_quantizeUniformSobolev_congr hba.symm ha.isUniform hb
    ((hasSobolevExtension_quantizeUniformCLM_iff_besselConjugate ha.isUniform s).mpr (hL2 _ _))
    ((hasSobolevExtension_quantizeUniformCLM_iff_besselConjugate hb s).mpr (hL2 _ _)) (v := u) rfl]
  simpa only [sub_sub_cancel] using (b.quantizeUniformSobolev hb s u).memSobolev_toDistr

end NormedSobolev

/-! ### Complex Hilbert fibres -/

section Hilbert

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **Sobolev estimate on Schwartz functions** for complex Hilbert fibres:
`‖Op(a) u‖_{H^{s - m}} ≤ C ‖u‖_{H^s}`. -/
theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖toBesselPotentialSpaceCLM s 2 u‖ :=
  let ⟨C, hC0, hC⟩ := (ha.besselConjugate s).exists_eLpNorm_quantizeSchwartzValue_le
  ⟨C, hC0, norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConjugate ha s hC0 hC⟩

/-- **Sobolev mapping of uniform symbols**, in composable form. Let `a` be a symbol of order `m`
whose estimates are uniform in the position, between complex Hilbert spaces. For every real `s`,
the quantization `Op(a)` extends to a bounded operator `H^s → H^{s - m}`. -/
theorem hasSobolevExtension_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) :=
  hasSobolevExtension_iff_exists_norm_le.mpr
    (ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le s)

/-- **Calderón–Vaillancourt.** The quantization of a uniform symbol of order at most `0` extends
to a bounded operator on `H⁰ = L²`. -/
theorem hasSobolevExtension_quantizeUniformCLM_zero {b : Symbol n V W m}
    (hb : b.IsUniform) (hm : m ≤ 0) :
    SchwartzMap.HasSobolevExtension (quantizeUniformCLM b hb) 0 0 :=
  (hasSobolevExtension_quantizeUniformCLM b hb 0).mono (by linarith)

/-- **Sobolev mapping of uniform symbols**, for complex Hilbert fibres. Let `a` be a symbol of
order `m` whose estimates are uniform in the position. For every real `s`, the quantization
`Op(a)` extends from Schwartz functions to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`.
No compact spatial support and no finite dimension is needed. -/
theorem exists_quantizeUniformSobolevHilbert (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x :=
  ⟨a.quantizeUniformSobolev ha s,
    toDistr_quantizeUniformSobolev_toBesselPotentialSpaceCLM_apply ha
      (hasSobolevExtension_quantizeUniformCLM a ha s)⟩

/-- **Agreement with `Symbol.quantizeSobolev`** when `a` has compact spatial support. -/
theorem quantizeUniformSobolev_eq_quantizeSobolev {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    a.quantizeUniformSobolev ha.isUniform s = a.quantizeSobolev ha s :=
  continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun _ ↦
    BesselPotentialSpace.ext (by ext φ; simp [quantizeUniformSobolev_toBesselPotentialSpaceCLM
      ha.isUniform (hasSobolevExtension_quantizeUniformCLM a ha.isUniform s)])

end Hilbert

/-! ### Finite-dimensional normed fibres -/

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Sobolev estimate on Schwartz functions** for finite-dimensional complex normed fibres:
`‖Op(a) u‖_{H^{s - m}} ≤ C ‖u‖_{H^s}`. -/
theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖toBesselPotentialSpaceCLM (s - m) 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖toBesselPotentialSpaceCLM s 2 u‖ :=
  let ⟨C, hC0, hC⟩ :=
    (ha.besselConjugate s).exists_eLpNorm_quantizeSchwartzValue_le_of_finiteDimensional
  ⟨C, hC0, norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_besselConjugate ha s hC0 hC⟩

/-- Uniform symbols of order `m` between finite-dimensional complex normed fibres quantize to
bounded operators `H^s → H^{s - m}` (`HasSobolevExtension`). -/
theorem hasSobolevExtension_quantizeUniformCLM_of_finiteDimensional (a : Symbol n V W m)
    (ha : a.IsUniform) (s : ℝ) : HasSobolevExtension (quantizeUniformCLM a ha) s (s - m) :=
  hasSobolevExtension_iff_exists_norm_le.mpr
    (ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le_of_finiteDimensional s)

/-- **Sobolev mapping of uniform symbols.** Let `a` be a symbol of order `m` whose estimates are
uniform in the position, between finite-dimensional complex normed spaces. For every real `s`,
the quantization `Op(a)` extends from Schwartz functions to a bounded operator
`H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`. No compact spatial support is needed. -/
theorem exists_quantizeUniformSobolev (a : Symbol n V W m) (ha : a.IsUniform) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x :=
  ⟨a.quantizeUniformSobolev ha s,
    toDistr_quantizeUniformSobolev_toBesselPotentialSpaceCLM_apply ha
      (hasSobolevExtension_quantizeUniformCLM_of_finiteDimensional a ha s)⟩

end FiniteDimensional
end Symbol
end TauCeti
