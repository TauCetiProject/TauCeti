/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# The one-sided Laplace transform

This file defines the ordinary one-sided Laplace transform of a vector-valued function on `ℝ` at a
complex frequency parameter `s : ℂ`, bundling Bochner integrability with the value of the integral,
and develops its algebraic, analytic, special-function, and calculus API.

## Main definitions

* `TauCeti.LaplaceConvergent f s μ`: `t ↦ Complex.exp (-s * t) • f t` is Bochner integrable with
  respect to `μ` (defaulting to `volume.restrict (Set.Ioi 0)`).
* `TauCeti.laplace f s μ`: the Bochner integral `∫ t, Complex.exp (-s * t) • f t ∂μ`.
* `TauCeti.HasLaplace f s z μ`: `t ↦ Complex.exp (-s * t) • f t` is integrable with respect to `μ`
  and its Bochner integral equals `z`.

## Main results

* Algebraic, congruence, shift, and dilation API: `TauCeti.HasLaplace.unique`,
  `TauCeti.HasLaplace.congr`, `TauCeti.hasLaplace_restrict_Ici_iff`, `TauCeti.hasLaplace_zero`,
  `TauCeti.HasLaplace.add`, `TauCeti.HasLaplace.sub`, `TauCeti.HasLaplace.const_smul`,
  `TauCeti.hasLaplace_cexp_smul_iff`, and `TauCeti.HasLaplace.comp_mul_left`.
* Half-plane convergence and complex parameter differentiation: `TauCeti.LaplaceConvergent.mono_re`,
  `TauCeti.LaplaceConvergent.hasDerivAt_laplace`, `TauCeti.hasDerivAt_of_hasLaplace_of_re_gt`,
  `TauCeti.hasLaplace_neg_ofReal_smul_of_hasLaplace_of_re_gt`, `TauCeti.differentiableOn_laplace`,
  and `TauCeti.analyticOnNhd_laplace`.
* Concrete transforms, negative controls, and integer Gamma–Laplace model:
  `TauCeti.hasLaplace_const`, `TauCeti.laplaceConvergent_const_iff`,
  `TauCeti.not_hasLaplace_one_zero`, `TauCeti.hasLaplace_cexp_mul`, `TauCeti.hasLaplace_cpow`,
  `TauCeti.hasLaplace_pow`, `TauCeti.hasLaplace_rexp_mul_pow`, and
  `TauCeti.hasLaplace_div_factorial_mul_rexp_mul_pow`.
* Transform of a primitive and of a derivative: `TauCeti.hasLaplace_deriv_of_primitive` and
  `TauCeti.hasLaplace_deriv`, valid under integrability hypotheses alone without exponential-order
  bounds or sign conditions on `s.re`.

## Implementation notes

Because the Bochner integral of a non-integrable function is `0` by convention, an unbundled
equation `∫ t in Ioi 0, Complex.exp (-s * t) • f t = z` spuriously holds at `z = 0` for divergent
integrals (such as `f = 1` at `s = 0`). Following `HasSum` and `HasMellin`, `TauCeti.HasLaplace`
bundles integrability with the value of the integral. Results needing real/complex scalar
compatibility assume `[NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]`, which synthesizes
automatically from `[NormedSpace ℂ E]` and avoids diamond issues at `E = ℂ`.

## References

* Dennj Osele, *The Laplace transform* (2026), `github.com/dennj/mathlib4`,
  `Mathlib/Analysis/LaplaceTransform.lean` at commit `90482cd37e85e423459de2ed103cea2f4d98cb20`,
  declarations `LaplaceConvergent`, `laplace`, and `HasLaplace` (for the predicate shape, argument
  order, default measure, and scalar-action hypotheses; all proofs here are written from scratch).
* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242.
* J. Lebl, *Notes on Diffy Qs: Differential Equations for Engineers*, version 6.11 (2026), §6.2.1,
  p. 300.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace TauCeti

/-! ### Core definitions and basic characterization -/

section Defs

variable {E : Type*} [NormedAddCommGroup E]

section Convergent

variable [SMul ℂ E] {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ}

/-- `LaplaceConvergent f s μ` means that `t ↦ Complex.exp (-s * t) • f t` is Bochner integrable
with respect to `μ` (defaulting to Lebesgue measure restricted to `(0, ∞)`). -/
def LaplaceConvergent (f : ℝ → E) (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) : Prop :=
  Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ

/-- Unfolding characterization of `LaplaceConvergent`. -/
theorem laplaceConvergent_def :
    LaplaceConvergent f s μ ↔ Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ := Iff.rfl

/-- Unpack `LaplaceConvergent` to `MeasureTheory.Integrable`. -/
theorem LaplaceConvergent.integrable (h : LaplaceConvergent f s μ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ := h

/-- Almost-everywhere congruence preserves `LaplaceConvergent`. -/
theorem LaplaceConvergent.congr (hf : LaplaceConvergent f s μ) (hfg : f =ᵐ[μ] g) :
    LaplaceConvergent g s μ :=
  Integrable.congr hf (hfg.mono fun _ ht ↦ by simp [ht])

/-- `LaplaceConvergent` depends only on the `μ`-almost-everywhere class of `f`. -/
theorem laplaceConvergent_congr (hfg : f =ᵐ[μ] g) :
    LaplaceConvergent f s μ ↔ LaplaceConvergent g s μ :=
  ⟨fun h ↦ h.congr hfg, fun h ↦ h.congr hfg.symm⟩

/-- Pointwise agreement on `(0, ∞)` preserves `LaplaceConvergent` for the default measure. -/
theorem LaplaceConvergent.congr_Ioi (hf : LaplaceConvergent f s) (hfg : EqOn f g (Ioi 0)) :
    LaplaceConvergent g s :=
  hf.congr ((ae_restrict_mem measurableSet_Ioi).mono hfg)

/-- On the default measure, `LaplaceConvergent` depends only on the values of `f` on `(0, ∞)`. -/
theorem laplaceConvergent_congr_Ioi (hfg : EqOn f g (Ioi 0)) :
    LaplaceConvergent f s ↔ LaplaceConvergent g s :=
  ⟨fun h ↦ h.congr_Ioi hfg, fun h ↦ h.congr_Ioi hfg.symm⟩

/-- Restricting Lebesgue measure to `[0, ∞)` or `(0, ∞)` gives the same `LaplaceConvergent`. -/
@[simp, grind =]
theorem laplaceConvergent_restrict_Ici_iff (f : ℝ → E) (s : ℂ) :
    LaplaceConvergent f s (volume.restrict (Ici 0)) ↔ LaplaceConvergent f s := by
  rw [laplaceConvergent_def, laplaceConvergent_def, restrict_Ioi_eq_restrict_Ici]

end Convergent

section Integral

variable [NormedSpace ℝ E] [SMul ℂ E] {f g : ℝ → E} {s : ℂ} {z z' : E} {μ : Measure ℝ}

/-- The one-sided Laplace transform `∫ t, Complex.exp (-s * t) • f t ∂μ`, with `μ` defaulting to
Lebesgue measure restricted to `(0, ∞)`. -/
noncomputable def laplace (f : ℝ → E) (s : ℂ) (μ : Measure ℝ := volume.restrict (Ioi 0)) : E :=
  ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ

/-- Unfolding characterization of `laplace`, whose body is not exposed across module boundaries. -/
theorem laplace_def : laplace f s μ = ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ := (rfl)

/-- `HasLaplace f s z μ` states that `t ↦ Complex.exp (-s * t) • f t` is integrable with respect to
`μ` and its Bochner integral equals `z`. With the default measure `volume.restrict (Ioi 0)` this is
the ordinary one-sided Laplace transform of `f` at the complex frequency `s`. -/
def HasLaplace (f : ℝ → E) (s : ℂ) (z : E) (μ : Measure ℝ := volume.restrict (Ioi 0)) : Prop :=
  Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ∧
    ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z

/-- Unfolding characterization of `HasLaplace`. -/
theorem hasLaplace_def :
    HasLaplace f s z μ ↔
      Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ ∧
        ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z := Iff.rfl

/-- Characterization of `HasLaplace` in terms of `LaplaceConvergent` and `laplace`. -/
@[grind =]
theorem hasLaplace_iff : HasLaplace f s z μ ↔ LaplaceConvergent f s μ ∧ laplace f s μ = z :=
  Iff.rfl

/-- If `f` is `LaplaceConvergent` at `s`, then `f` has Laplace transform `laplace f s μ`. -/
theorem LaplaceConvergent.hasLaplace (h : LaplaceConvergent f s μ) :
    HasLaplace f s (laplace f s μ) μ := ⟨h, rfl⟩

/-- Extract `LaplaceConvergent` from `HasLaplace`. -/
theorem HasLaplace.laplaceConvergent (h : HasLaplace f s z μ) : LaplaceConvergent f s μ := h.1

/-- Extract Bochner integrability of the damped integrand from `HasLaplace`. -/
theorem HasLaplace.integrable (h : HasLaplace f s z μ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f t) μ := h.1

/-- Extract the Bochner integral identity from `HasLaplace`. -/
theorem HasLaplace.integral_eq (h : HasLaplace f s z μ) :
    ∫ t : ℝ, Complex.exp (-s * t) • f t ∂μ = z := h.2

/-- Extract `laplace f s μ = z` from `HasLaplace f s z μ`. -/
theorem HasLaplace.laplace_eq (h : HasLaplace f s z μ) : laplace f s μ = z := h.2

/-- Uniqueness of the Laplace transform at a given frequency and measure. -/
theorem HasLaplace.unique (hz : HasLaplace f s z μ) (hz' : HasLaplace f s z' μ) : z = z' :=
  hz.2.symm.trans hz'.2

/-- When `f` is not `LaplaceConvergent` at `s`, the totalized `laplace` value is `0`. -/
@[grind =]
theorem laplace_of_not_laplaceConvergent (h : ¬ LaplaceConvergent f s μ) : laplace f s μ = 0 :=
  integral_undef h

/-- `laplace` depends only on the `μ`-almost-everywhere class of `f`. -/
theorem laplace_congr (hfg : f =ᵐ[μ] g) : laplace f s μ = laplace g s μ :=
  integral_congr_ae (hfg.mono fun _ ht ↦ by simp [ht])

/-- Almost-everywhere congruence preserves `HasLaplace`. -/
theorem HasLaplace.congr (hf : HasLaplace f s z μ) (hfg : f =ᵐ[μ] g) : HasLaplace g s z μ :=
  ⟨hf.laplaceConvergent.congr hfg, (laplace_congr hfg.symm).trans hf.laplace_eq⟩

/-- `HasLaplace` depends only on the `μ`-almost-everywhere class of `f`. -/
theorem hasLaplace_congr (hfg : f =ᵐ[μ] g) : HasLaplace f s z μ ↔ HasLaplace g s z μ :=
  ⟨fun h ↦ h.congr hfg, fun h ↦ h.congr hfg.symm⟩

/-- On the default measure, `laplace` depends only on the values of `f` on `(0, ∞)`. -/
theorem laplace_congr_Ioi (hfg : EqOn f g (Ioi 0)) : laplace f s = laplace g s :=
  laplace_congr ((ae_restrict_mem measurableSet_Ioi).mono hfg)

/-- Pointwise agreement on `(0, ∞)` preserves `HasLaplace` for the default measure. -/
theorem HasLaplace.congr_Ioi (hf : HasLaplace f s z) (hfg : EqOn f g (Ioi 0)) : HasLaplace g s z :=
  hf.congr ((ae_restrict_mem measurableSet_Ioi).mono hfg)

/-- On the default measure, `HasLaplace` depends only on the values of `f` on `(0, ∞)`. -/
theorem hasLaplace_congr_Ioi (hfg : EqOn f g (Ioi 0)) : HasLaplace f s z ↔ HasLaplace g s z :=
  ⟨fun h ↦ h.congr_Ioi hfg, fun h ↦ h.congr_Ioi hfg.symm⟩

/-- Restricting Lebesgue measure to `[0, ∞)` or `(0, ∞)` gives the same `laplace` value. -/
@[simp, grind =]
theorem laplace_restrict_Ici (f : ℝ → E) (s : ℂ) :
    laplace f s (volume.restrict (Ici 0)) = laplace f s := by
  rw [laplace_def, laplace_def, restrict_Ioi_eq_restrict_Ici]

/-- Restricting Lebesgue measure to `[0, ∞)` or `(0, ∞)` gives the same `HasLaplace` predicate. -/
@[simp, grind =]
theorem hasLaplace_restrict_Ici_iff (f : ℝ → E) (s : ℂ) (z : E) :
    HasLaplace f s z (volume.restrict (Ici 0)) ↔ HasLaplace f s z := by
  rw [hasLaplace_iff, hasLaplace_iff, laplaceConvergent_restrict_Ici_iff, laplace_restrict_Ici]

end Integral

end Defs

/-! ### Algebraic operations, frequency shift, and positive dilation -/

section Algebra

variable {E : Type*} [NormedAddCommGroup E]

section Zero

/-- The zero function is `LaplaceConvergent` whenever the complex action preserves zero. -/
@[to_fun (attr := simp) laplaceConvergent_fun_zero]
theorem laplaceConvergent_zero [SMulZeroClass ℂ E] (s : ℂ) {μ : Measure ℝ} :
    LaplaceConvergent (0 : ℝ → E) s μ := by simp [LaplaceConvergent]

/-- The Laplace integral of the zero function is `0`. -/
@[to_fun (attr := simp) laplace_fun_zero]
theorem laplace_zero [NormedSpace ℝ E] [SMulZeroClass ℂ E] (s : ℂ) {μ : Measure ℝ} :
    laplace (0 : ℝ → E) s μ = 0 := by simp [laplace]

/-- The zero function has Laplace transform `0` at every complex `s` and measure `μ`. -/
@[to_fun (attr := simp) hasLaplace_fun_zero]
theorem hasLaplace_zero [NormedSpace ℝ E] [SMulZeroClass ℂ E] (s : ℂ) {μ : Measure ℝ} :
    HasLaplace (0 : ℝ → E) s 0 μ :=
  hasLaplace_iff.mpr ⟨laplaceConvergent_zero s, laplace_zero s⟩

end Zero

section DistribSMul

variable [DistribSMul ℂ E] {f g : ℝ → E} {s : ℂ} {μ : Measure ℝ}

/-- Negation preserves `LaplaceConvergent`. -/
@[to_fun]
theorem LaplaceConvergent.neg (hf : LaplaceConvergent f s μ) : LaplaceConvergent (-f) s μ :=
  hf.integrable.neg.congr (ae_of_all _ fun _ ↦ (smul_neg _ _).symm)

/-- `LaplaceConvergent` is invariant under negation. -/
@[grind =, to_fun (attr := simp) laplaceConvergent_fun_neg_iff]
theorem laplaceConvergent_neg_iff : LaplaceConvergent (-f) s μ ↔ LaplaceConvergent f s μ :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, LaplaceConvergent.neg⟩

/-- Addition of functions preserves `LaplaceConvergent`. -/
@[to_fun]
theorem LaplaceConvergent.add (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    LaplaceConvergent (f + g) s μ :=
  (hf.integrable.add hg.integrable).congr (ae_of_all _ fun _ ↦ (smul_add _ _ _).symm)

/-- Subtraction of functions preserves `LaplaceConvergent`. -/
@[to_fun]
theorem LaplaceConvergent.sub (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    LaplaceConvergent (f - g) s μ :=
  (hf.integrable.sub hg.integrable).congr (ae_of_all _ fun _ ↦ (smul_sub _ _ _).symm)

/-- Finite sums preserve `LaplaceConvergent`. -/
@[to_fun laplaceConvergent_fun_finsetSum]
theorem laplaceConvergent_finsetSum {ι : Type*} {f : ι → ℝ → E} (S : Finset ι)
    (hf : ∀ i ∈ S, LaplaceConvergent (f i) s μ) :
    LaplaceConvergent (∑ i ∈ S, f i) s μ :=
  (integrable_finsetSum S fun i hi ↦ (hf i hi).integrable).congr
    (ae_of_all _ fun _ ↦ by simp [Finset.smul_sum])

section NormedSpaceReal

variable [NormedSpace ℝ E] {z w : E}

/-- Negation commutes with `laplace`. -/
@[to_fun laplace_fun_neg]
theorem laplace_neg (f : ℝ → E) (s : ℂ) {μ : Measure ℝ} :
    laplace (-f) s μ = -laplace f s μ := by simp [laplace, smul_neg, integral_neg]

/-- Negation negates the Laplace transform. -/
@[to_fun]
theorem HasLaplace.neg (hf : HasLaplace f s z μ) : HasLaplace (-f) s (-z) μ :=
  hasLaplace_iff.mpr ⟨hf.laplaceConvergent.neg, by rw [laplace_neg, hf.laplace_eq]⟩

/-- `HasLaplace` for `-f` is equivalent to `HasLaplace` for `f` with negated value. -/
@[grind =, to_fun (attr := simp) hasLaplace_fun_neg_iff]
theorem hasLaplace_neg_iff : HasLaplace (-f) s (-z) μ ↔ HasLaplace f s z μ :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, HasLaplace.neg⟩

/-- Linearity of `laplace` on sums of `LaplaceConvergent` functions. -/
@[to_fun laplace_fun_add]
theorem laplace_add (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    laplace (f + g) s μ = laplace f s μ + laplace g s μ := by
  simpa only [laplace, Pi.add_apply, smul_add] using integral_add hf.integrable hg.integrable

/-- Additivity of `HasLaplace` on `f + g`. -/
@[to_fun]
theorem HasLaplace.add (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (f + g) s (z + w) μ :=
  hasLaplace_iff.mpr ⟨hf.laplaceConvergent.add hg.laplaceConvergent,
    by rw [laplace_add hf.laplaceConvergent hg.laplaceConvergent, hf.laplace_eq, hg.laplace_eq]⟩

/-- Linearity of `laplace` on differences of `LaplaceConvergent` functions. -/
@[to_fun laplace_fun_sub]
theorem laplace_sub (hf : LaplaceConvergent f s μ) (hg : LaplaceConvergent g s μ) :
    laplace (f - g) s μ = laplace f s μ - laplace g s μ := by
  simpa only [laplace, Pi.sub_apply, smul_sub] using integral_sub hf.integrable hg.integrable

/-- Subtraction of Laplace transforms on `f - g`. -/
@[to_fun]
theorem HasLaplace.sub (hf : HasLaplace f s z μ) (hg : HasLaplace g s w μ) :
    HasLaplace (f - g) s (z - w) μ :=
  hasLaplace_iff.mpr ⟨hf.laplaceConvergent.sub hg.laplaceConvergent,
    by rw [laplace_sub hf.laplaceConvergent hg.laplaceConvergent, hf.laplace_eq, hg.laplace_eq]⟩

/-- Finite sums commute with `laplace` when each summand is `LaplaceConvergent`. -/
@[to_fun laplace_fun_finsetSum]
theorem laplace_finsetSum {ι : Type*} {f : ι → ℝ → E} (S : Finset ι)
    (hf : ∀ i ∈ S, LaplaceConvergent (f i) s μ) :
    laplace (∑ i ∈ S, f i) s μ = ∑ i ∈ S, laplace (f i) s μ := by
  simp_rw [laplace_def, Finset.sum_apply, Finset.smul_sum]
  exact integral_finsetSum S fun i hi ↦ (hf i hi).integrable

/-- Finite sums of `HasLaplace` predicates. -/
@[to_fun hasLaplace_fun_finsetSum]
theorem hasLaplace_finsetSum {ι : Type*} {f : ι → ℝ → E} {z : ι → E} (S : Finset ι)
    (hf : ∀ i ∈ S, HasLaplace (f i) s (z i) μ) :
    HasLaplace (∑ i ∈ S, f i) s (∑ i ∈ S, z i) μ :=
  hasLaplace_iff.mpr ⟨laplaceConvergent_finsetSum S fun i hi ↦ (hf i hi).laplaceConvergent,
    (laplace_finsetSum S fun i hi ↦ (hf i hi).laplaceConvergent).trans
      (Finset.sum_congr rfl fun i hi ↦ (hf i hi).laplace_eq)⟩

end NormedSpaceReal

end DistribSMul

section SMul

/-- Bounded scalar multiplication commuting with `ℂ` preserves `LaplaceConvergent`. -/
@[to_fun]
theorem LaplaceConvergent.const_smul [SMul ℂ E] {f : ℝ → E} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
    [IsBoundedSMul 𝕜 E] [SMulCommClass ℂ 𝕜 E] (c : 𝕜) :
    LaplaceConvergent (c • f) s μ :=
  (hf.integrable.smul c).congr (ae_of_all _ fun _ ↦ (smul_comm _ c _).symm)

/-- Scalar multiplication by a normed division ring commuting with `ℝ` and `ℂ` on `laplace`. -/
@[to_fun laplace_fun_const_smul]
theorem laplace_const_smul [NormedSpace ℝ E] [SMul ℂ E] (f : ℝ → E) (s : ℂ)
    {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] [SMulCommClass ℂ 𝕜 E] (c : 𝕜) {μ : Measure ℝ} :
    laplace (c • f) s μ = c • laplace f s μ := by
  rw [laplace_def, laplace_def, ← integral_smul]
  exact integral_congr_ae (ae_of_all _ fun _ ↦ smul_comm _ c _)

/-- Bounded scalar multiplication on `HasLaplace` by a normed ring commuting with `ℝ` and `ℂ`. -/
@[to_fun]
theorem HasLaplace.const_smul [NormedSpace ℝ E] [SMul ℂ E] {f : ℝ → E} {s : ℂ} {z : E}
    {μ : Measure ℝ} (hf : HasLaplace f s z μ) {R : Type*} [NormedRing R] [Module R E]
    [IsBoundedSMul R E] [SMulCommClass ℝ R E] [SMulCommClass ℂ R E] (c : R) :
    HasLaplace (c • f) s (c • z) μ :=
  ⟨hf.laplaceConvergent.const_smul c,
    (integral_congr_ae (ae_of_all _ fun _ ↦ smul_comm _ c _)).trans
      (hf.integrable.integral_smul c |>.trans (congrArg (c • ·) hf.integral_eq))⟩

/-- Scalar multiplication of `v : E` by `f : ℝ → ℂ` preserves `LaplaceConvergent`. -/
theorem LaplaceConvergent.smul_const [NormedSpace ℂ E] {f : ℝ → ℂ} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (v : E) :
    LaplaceConvergent (fun t ↦ f t • v) s μ :=
  (hf.integrable.smul_const v).congr (ae_of_all _ fun _ ↦ by simp [smul_eq_mul, mul_smul])

/-- `laplace` of `t ↦ f t • v` equals `laplace f s μ • v` in a complete space. -/
theorem laplace_smul_const [NormedSpace ℝ E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℝ → ℂ) (s : ℂ) (v : E) {μ : Measure ℝ} :
    laplace (fun t ↦ f t • v) s μ = laplace f s μ • v := by
  simpa only [laplace_def, smul_eq_mul, mul_smul] using
    integral_smul_const (μ := μ) (fun t : ℝ ↦ Complex.exp (-s * t) * f t) v

/-- If `f : ℝ → ℂ` has Laplace transform `z`, then `t ↦ f t • v` has Laplace transform `z • v`. -/
theorem HasLaplace.smul_const [NormedSpace ℝ E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℝ → ℂ} {s z : ℂ} {μ : Measure ℝ} (hf : HasLaplace f s z μ) (v : E) :
    HasLaplace (fun t ↦ f t • v) s (z • v) μ :=
  hasLaplace_iff.mpr ⟨hf.laplaceConvergent.smul_const v, by rw [laplace_smul_const, hf.laplace_eq]⟩

/-- Dividing a complex-valued function by a constant preserves `LaplaceConvergent`. -/
theorem LaplaceConvergent.div_const {f : ℝ → ℂ} {s : ℂ} {μ : Measure ℝ}
    (hf : LaplaceConvergent f s μ) (c : ℂ) :
    LaplaceConvergent (fun t ↦ f t / c) s μ :=
  (hf.integrable.div_const c).congr (ae_of_all _ fun _ ↦ mul_div_assoc _ _ _)

/-- `laplace` commutes with division by a complex constant. -/
theorem laplace_div_const (f : ℝ → ℂ) (s c : ℂ) {μ : Measure ℝ} :
    laplace (fun t ↦ f t / c) s μ = laplace f s μ / c := by
  simp_rw [laplace_def, smul_eq_mul, ← mul_div_assoc, integral_div]

/-- Dividing `f : ℝ → ℂ` by `c : ℂ` divides its Laplace transform by `c`. -/
theorem HasLaplace.div_const {f : ℝ → ℂ} {s z : ℂ} {μ : Measure ℝ}
    (hf : HasLaplace f s z μ) (c : ℂ) :
    HasLaplace (fun t ↦ f t / c) s (z / c) μ :=
  hasLaplace_iff.mpr ⟨hf.laplaceConvergent.div_const c, by rw [laplace_div_const, hf.laplace_eq]⟩

end SMul

section ShiftAndDilation

/-- Frequency shift for `LaplaceConvergent`: multiplying `f t` by `exp (a * t)` shifts `s` to
`s - a`. -/
theorem laplaceConvergent_cexp_smul [MulAction ℂ E] (f : ℝ → E) (a s : ℂ) {μ : Measure ℝ} :
    LaplaceConvergent (fun t : ℝ ↦ Complex.exp (a * t) • f t) s μ ↔
      LaplaceConvergent f (s - a) μ := by
  rw [laplaceConvergent_def, laplaceConvergent_def]
  refine integrable_congr (ae_of_all μ fun t ↦ ?_)
  dsimp only; rw [← mul_smul, ← Complex.exp_add]; congr 2; ring

/-- Frequency shift for `laplace`: multiplying `f t` by `exp (a * t)` shifts `s` to `s - a`. -/
theorem laplace_cexp_smul [NormedSpace ℝ E] [MulAction ℂ E] (f : ℝ → E) (a s : ℂ) {μ : Measure ℝ} :
    laplace (fun t : ℝ ↦ Complex.exp (a * t) • f t) s μ = laplace f (s - a) μ := by
  rw [laplace_def, laplace_def]
  refine integral_congr_ae (ae_of_all μ fun t ↦ ?_)
  dsimp only; rw [← mul_smul, ← Complex.exp_add]; congr 2; ring

/-- Frequency-shift equivalence for `HasLaplace`. -/
theorem hasLaplace_cexp_smul_iff [NormedSpace ℝ E] [MulAction ℂ E] (f : ℝ → E) (a s : ℂ) (z : E)
    {μ : Measure ℝ} :
    HasLaplace (fun t : ℝ ↦ Complex.exp (a * t) • f t) s z μ ↔ HasLaplace f (s - a) z μ := by
  rw [hasLaplace_iff, hasLaplace_iff, laplaceConvergent_cexp_smul, laplace_cexp_smul]

/-- Forward frequency-shift rule for `HasLaplace`. -/
theorem HasLaplace.cexp_smul [NormedSpace ℝ E] [MulAction ℂ E] {f : ℝ → E} {a s : ℂ} {z : E}
    {μ : Measure ℝ} (hf : HasLaplace f (s - a) z μ) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (a * t) • f t) s z μ :=
  (hasLaplace_cexp_smul_iff f a s z).mpr hf

/-- Real exponential shift for `LaplaceConvergent`: multiplying `f t` by `Real.exp (a * t)` shifts
`s` to `s - a`. -/
theorem laplaceConvergent_rexp_smul [SMul ℝ E] [MulAction ℂ E] [IsScalarTower ℝ ℂ E]
    (f : ℝ → E) (a : ℝ) (s : ℂ) {μ : Measure ℝ} :
    LaplaceConvergent (fun t : ℝ ↦ Real.exp (a * t) • f t) s μ ↔
      LaplaceConvergent f (s - a) μ := by
  rw [← laplaceConvergent_cexp_smul]
  congr! 2 with t
  simp [← IsScalarTower.algebraMap_smul ℂ, Complex.ofReal_exp]

/-- Real exponential shift for `laplace`: multiplying `f t` by `Real.exp (a * t)` shifts `s` to
`s - a`. -/
theorem laplace_rexp_smul [NormedSpace ℝ E] [MulAction ℂ E] [IsScalarTower ℝ ℂ E]
    (f : ℝ → E) (a : ℝ) (s : ℂ) {μ : Measure ℝ} :
    laplace (fun t : ℝ ↦ Real.exp (a * t) • f t) s μ = laplace f (s - a) μ := by
  rw [← laplace_cexp_smul]
  congr! 2 with t
  simp [← IsScalarTower.algebraMap_smul ℂ, Complex.ofReal_exp]

/-- Real exponential shift equivalence for `HasLaplace`. -/
theorem hasLaplace_rexp_smul_iff [NormedSpace ℝ E] [MulAction ℂ E] [IsScalarTower ℝ ℂ E]
    (f : ℝ → E) (a : ℝ) (s : ℂ) (z : E) {μ : Measure ℝ} :
    HasLaplace (fun t : ℝ ↦ Real.exp (a * t) • f t) s z μ ↔ HasLaplace f (s - a) z μ := by
  rw [hasLaplace_iff, hasLaplace_iff, laplaceConvergent_rexp_smul, laplace_rexp_smul]

/-- Forward real exponential shift rule for `HasLaplace`. -/
theorem HasLaplace.rexp_smul [NormedSpace ℝ E] [MulAction ℂ E] [IsScalarTower ℝ ℂ E]
    {f : ℝ → E} {a : ℝ} {s : ℂ} {z : E} {μ : Measure ℝ} (hf : HasLaplace f (s - a) z μ) :
    HasLaplace (fun t : ℝ ↦ Real.exp (a * t) • f t) s z μ :=
  (hasLaplace_rexp_smul_iff f a s z).mpr hf

/-- Positive time dilation for `LaplaceConvergent` on `(0, ∞)`. -/
theorem laplaceConvergent_comp_mul_left [SMul ℂ E] (f : ℝ → E) (s : ℂ) {c : ℝ} (hc : 0 < c) :
    LaplaceConvergent (fun t : ℝ ↦ f (c * t)) s ↔ LaplaceConvergent f (s / c) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hfun : (fun t : ℝ ↦ Complex.exp (-s * t) • f (c * t)) =
      fun t : ℝ ↦ (fun u : ℝ ↦ Complex.exp (-(s / c) * u) • f u) (c * t) := by
    ext t; simp only [Complex.ofReal_mul]; congr 2; field_simp
  rw [laplaceConvergent_def, laplaceConvergent_def, hfun]
  simpa only [IntegrableOn, mul_zero] using
    integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ ↦ Complex.exp (-(s / c) * u) • f u) 0 hc

/-- Positive time dilation for `laplace` on `(0, ∞)`. -/
theorem laplace_comp_mul_left [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (f : ℝ → E) (s : ℂ) {c : ℝ} (hc : 0 < c) :
    laplace (fun t : ℝ ↦ f (c * t)) s = (c : ℂ)⁻¹ • laplace f (s / c) := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hfun : (fun t : ℝ ↦ Complex.exp (-s * t) • f (c * t)) =
      fun t : ℝ ↦ (fun u : ℝ ↦ Complex.exp (-(s / c) * u) • f u) (c * t) := by
    ext t; simp only [Complex.ofReal_mul]; congr 2; field_simp
  rw [laplace_def, laplace_def, hfun,
    integral_comp_mul_left_Ioi (fun u : ℝ ↦ Complex.exp (-(s / c) * u) • f u) 0 hc,
    mul_zero, ← algebraMap_smul ℂ c⁻¹]
  simp

/-- Positive time dilation for `HasLaplace`: if `0 < c` and `f` has Laplace transform `z` at
`s / c`, then `t ↦ f (c * t)` has Laplace transform `(c : ℂ)⁻¹ • z` at `s`. -/
theorem HasLaplace.comp_mul_left [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {f : ℝ → E} {s : ℂ} {z : E} {c : ℝ} (hc : 0 < c) (hf : HasLaplace f (s / c) z) :
    HasLaplace (fun t : ℝ ↦ f (c * t)) s ((c : ℂ)⁻¹ • z) :=
  hasLaplace_iff.mpr ⟨(laplaceConvergent_comp_mul_left f s hc).mpr hf.laplaceConvergent,
    by rw [laplace_comp_mul_left f s hc, hf.laplace_eq]⟩

/-- Equivalence form of positive time dilation for `HasLaplace`. -/
theorem hasLaplace_comp_mul_left_iff [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (f : ℝ → E) (s : ℂ) (z : E) {c : ℝ} (hc : 0 < c) :
    HasLaplace (fun t : ℝ ↦ f (c * t)) s ((c : ℂ)⁻¹ • z) ↔ HasLaplace f (s / c) z := by
  have hc' : (c : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne')
  rw [hasLaplace_iff, hasLaplace_iff, laplaceConvergent_comp_mul_left f s hc,
    laplace_comp_mul_left f s hc, smul_right_inj hc']

end ShiftAndDilation

end Algebra

/-! ### Local integrability, half-plane convergence, and complex parameter differentiation -/

section Analytic

/-- Pointwise domination of the `s`-derivative of the Laplace integrand by the integrand at `s₀`
on the shifted half-plane `s₀.re + δ ≤ w.re`. -/
private theorem norm_neg_mul_cexp_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) {s₀ w : ℂ} {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (hw : s₀.re + δ ≤ w.re) :
    ‖(-(t : ℂ) * Complex.exp (-w * t)) • f t‖ ≤ δ⁻¹ * ‖Complex.exp (-s₀ * t) • f t‖ := by
  have hrew_eq : (-(t : ℂ) * Complex.exp (-w * t)) • f t =
      (-(t : ℂ) * Complex.exp (-(w - s₀) * t)) • (Complex.exp (-s₀ * t) • f t) := by
    rw [← mul_smul, mul_assoc, ← Complex.exp_add]
    congr 1; congr 1; congr 1; ring
  rw [hrew_eq, norm_smul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht,
    Complex.norm_exp]
  gcongr
  have hre : (-(w - s₀) * (t : ℂ)).re ≤ -δ * t := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  calc
    t * Real.exp ((-(w - s₀) * (t : ℂ)).re) ≤ t * Real.exp (-δ * t) := by gcongr
    _ = δ⁻¹ * ((δ * t) * Real.exp (-δ * t)) := by field_simp
    _ ≤ δ⁻¹ * (Real.exp (δ * t) * Real.exp (-δ * t)) := by
      gcongr; linarith [Real.add_one_le_exp (δ * t)]
    _ = δ⁻¹ := by rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one]

section HalfPlane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If `f` is `LaplaceConvergent` at `s`, then `f` is integrable on every bounded `(0, T]`. -/
theorem LaplaceConvergent.integrableOn_Ioc {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s) (T : ℝ) : IntegrableOn f (Ioc 0 T) := by
  refine ((IntegrableOn.mono_set hf.integrable Ioc_subset_Ioi_self).continuousOn_smul_of_subset
    (Continuous.continuousOn (by fun_prop : Continuous fun t : ℝ ↦ Complex.exp (s * t)))
    isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self).congr (ae_of_all _ fun t ↦ ?_)
  dsimp only
  rw [← mul_smul, ← Complex.exp_add, neg_mul, add_neg_cancel, Complex.exp_zero, one_smul]

/-- If `f` is `LaplaceConvergent` at `s`, then `f` is interval-integrable on `0..T` for `0 ≤ T`. -/
theorem LaplaceConvergent.intervalIntegrable {f : ℝ → E} {s : ℂ}
    (hf : LaplaceConvergent f s) {T : ℝ} (hT : 0 ≤ T) : IntervalIntegrable f volume 0 T :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hf.integrableOn_Ioc T)

/-- Monotonicity of `LaplaceConvergent` on right half-planes: `s₀.re ≤ s.re` preserves
convergence. -/
theorem LaplaceConvergent.mono_re {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀) (hs : s₀.re ≤ s.re) : LaplaceConvergent f s := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ Complex.exp (-(s - s₀) * t))
      (volume.restrict (Ioi 0)) := Continuous.aestronglyMeasurable (by fun_prop)
  have hbdd : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0), ‖Complex.exp (-(s - s₀) * t)‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [Complex.norm_exp, ← Real.exp_zero, Real.exp_le_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  refine (hf.integrable.bdd_smul 1 hmeas hbdd).congr (ae_of_all _ fun t ↦ ?_)
  rw [Pi.smul_apply', ← mul_smul, ← Complex.exp_add]; congr 2; ring

/-- `LaplaceConvergent` depends only on `s.re` for every measure `μ` on `ℝ`. -/
theorem laplaceConvergent_congr_re {f : ℝ → E} {s₁ s₂ : ℂ} {μ : Measure ℝ} (hs : s₁.re = s₂.re) :
    LaplaceConvergent f s₁ μ ↔ LaplaceConvergent f s₂ μ := by
  suffices ∀ {w₁ w₂ : ℂ}, w₁.re = w₂.re → LaplaceConvergent f w₁ μ → LaplaceConvergent f w₂ μ from
    ⟨this hs, this hs.symm⟩
  intro w₁ w₂ hw hf
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ Complex.exp (-(w₂ - w₁) * t)) μ :=
    Continuous.aestronglyMeasurable (by fun_prop)
  have hbdd : ∀ᵐ (t : ℝ) ∂μ, ‖Complex.exp (-(w₂ - w₁) * t)‖ ≤ 1 :=
    ae_of_all _ fun t ↦ by simp [Complex.norm_exp, hw]
  refine (hf.integrable.bdd_smul 1 hmeas hbdd).congr (ae_of_all _ fun t ↦ ?_)
  rw [Pi.smul_apply', ← mul_smul, ← Complex.exp_add]; congr 2; ring

/-- Strictly inside the half-plane of convergence (`s₀.re < s.re`), multiplying `f t` by `t`
preserves `LaplaceConvergent`. -/
theorem LaplaceConvergent.ofReal_smul_of_re_lt {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀) (hs : s₀.re < s.re) :
    LaplaceConvergent (fun t : ℝ ↦ (t : ℂ) • f t) s := by
  set δ : ℝ := s.re - s₀.re
  have hδ : 0 < δ := sub_pos.mpr hs
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ (t : ℂ) * Complex.exp (-(s - s₀) * t))
      (volume.restrict (Ioi 0)) := Continuous.aestronglyMeasurable (by fun_prop)
  have hbdd : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0),
      ‖(t : ℂ) * Complex.exp (-(s - s₀) * t)‖ ≤ δ⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa using norm_neg_mul_cexp_smul_le (fun _ ↦ (1 : ℂ)) (s₀ := 0) (w := s - s₀) hδ
      (mem_Ioi.mp ht).le (by simp [δ])
  refine (hf.integrable.bdd_smul δ⁻¹ hmeas hbdd).congr (ae_of_all _ fun t ↦ ?_)
  dsimp only
  rw [Pi.smul_apply', ← mul_smul, ← mul_smul]
  congr 1
  have hexp : -(s - s₀) * (t : ℂ) + -s₀ * (t : ℂ) = -s * (t : ℂ) := by ring
  rw [mul_assoc, ← Complex.exp_add, hexp, mul_comm]

end HalfPlane

section Differentiation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

/-- Complex differentiation under the Laplace integral: if `f` is `LaplaceConvergent` at `s₀` and
`s₀.re < s.re`, then `w ↦ laplace f w` has complex derivative
`-laplace (fun t ↦ (t : ℂ) • f t) s` at `s`. -/
theorem LaplaceConvergent.hasDerivAt_laplace {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀) (hs : s₀.re < s.re) :
    HasDerivAt (fun w : ℂ ↦ laplace f w) (-laplace (fun t : ℝ ↦ (t : ℂ) • f t) s) s := by
  set δ : ℝ := (s.re - s₀.re) / 2 with hδ_def
  have hδ : 0 < δ := half_pos (sub_pos.mpr hs)
  set F : ℂ → ℝ → E := fun w t ↦ Complex.exp (-w * t) • f t
  set F' : ℂ → ℝ → E := fun w t ↦ (-(t : ℂ) * Complex.exp (-w * t)) • f t
  have hball : Metric.ball s δ ∈ 𝓝 s := Metric.ball_mem_nhds s hδ
  have hre : ∀ w ∈ Metric.ball s δ, s₀.re + δ < w.re := fun w hw ↦ by
    have h1 := (Complex.abs_re_le_norm (w - s)).trans_lt (mem_ball_iff_norm.mp hw)
    rw [Complex.sub_re] at h1; linarith [(abs_lt.mp h1).1, hδ_def]
  have hF_meas : ∀ᶠ w in 𝓝 s, AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    filter_upwards [hball] with w hw
    exact (hf.mono_re (by linarith [hre w hw])).integrable.aestronglyMeasurable
  have hF's_eq : ∀ t : ℝ, F' s t = Complex.exp (-s * t) • (-(fun u : ℝ ↦ (u : ℂ) • f u)) t := by
    intro t; dsimp only [F', Pi.neg_apply]
    rw [neg_mul, neg_smul, mul_comm (t : ℂ), mul_smul, smul_neg]
  have hF's_meas : AEStronglyMeasurable (F' s) (volume.restrict (Ioi 0)) :=
    (hf.ofReal_smul_of_re_lt hs).neg.integrable.aestronglyMeasurable.congr
      (ae_of_all _ fun t ↦ (hF's_eq t).symm)
  have h_bound : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball s δ, ‖F' w t‖ ≤ δ⁻¹ * ‖Complex.exp (-s₀ * t) • f t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    exact norm_neg_mul_cexp_smul_le f hδ (mem_Ioi.mp ht).le (hre w hw).le
  have h_diff : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball s δ, HasDerivAt (fun z ↦ F z t) (F' w t) w :=
    ae_of_all _ fun t w _ ↦
      (by simpa [mul_comm] using ((hasDerivAt_id w).neg.mul_const (t : ℂ)).cexp :
        HasDerivAt (fun z : ℂ ↦ Complex.exp (-z * t)) (-(t : ℂ) * Complex.exp (-w * t)) w
      ).smul_const (f t)
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hF_meas
    (hf.mono_re hs.le).integrable hF's_meas h_bound (hf.integrable.norm.const_mul δ⁻¹) h_diff).2
  rwa [integral_congr_ae (ae_of_all _ hF's_eq), ← laplace_def, laplace_neg] at hmain

/-- If `f` has Laplace transform `F w` on the open half-plane `a < w.re`, then at any `s` with
`a < s.re`, `F` has complex derivative `-laplace (fun t ↦ (t : ℂ) • f t) s` at `s`. -/
theorem hasDerivAt_of_hasLaplace_of_re_gt {f : ℝ → E} {F : ℂ → E} {a : ℝ} {s : ℂ}
    (hF : ∀ w : ℂ, a < w.re → HasLaplace f w (F w)) (hs : a < s.re) :
    HasDerivAt F (-laplace (fun t : ℝ ↦ (t : ℂ) • f t) s) s := by
  obtain ⟨σ, haσ, hσs⟩ := exists_between hs
  have heq : F =ᶠ[𝓝 s] fun w : ℂ ↦ laplace f w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact ((hF w hw).laplace_eq).symm
  exact ((hF σ haσ).laplaceConvergent.hasDerivAt_laplace (by simpa using hσs)).congr_of_eventuallyEq
    heq

/-- If `f` has Laplace transform `F w` on the open half-plane `a < w.re`, then at any `s` with
`a < s.re`, `t ↦ -((t : ℂ) • f t)` has Laplace transform `deriv F s` at `s`. -/
theorem hasLaplace_neg_ofReal_smul_of_hasLaplace_of_re_gt {f : ℝ → E} {F : ℂ → E} {a : ℝ} {s : ℂ}
    (hF : ∀ w : ℂ, a < w.re → HasLaplace f w (F w)) (hs : a < s.re) :
    HasLaplace (fun t : ℝ ↦ -((t : ℂ) • f t)) s (deriv F s) := by
  obtain ⟨σ, haσ, hσs⟩ := exists_between hs
  exact (hasDerivAt_of_hasLaplace_of_re_gt hF hs).deriv ▸
    ((hF σ haσ).laplaceConvergent.ofReal_smul_of_re_lt (by simpa using hσs)).hasLaplace.fun_neg

/-- Differentiability of `laplace f` at any point strictly inside the half-plane of convergence. -/
theorem LaplaceConvergent.differentiableAt_laplace {f : ℝ → E} {s₀ s : ℂ}
    (hf : LaplaceConvergent f s₀) (hs : s₀.re < s.re) :
    DifferentiableAt ℂ (fun w : ℂ ↦ laplace f w) s :=
  (hf.hasDerivAt_laplace hs).differentiableAt

/-- If `f` is `LaplaceConvergent` for every real `σ > a`, then `laplace f` is complex-differentiable
on `{w : ℂ | a < w.re}`. -/
theorem differentiableOn_laplace {f : ℝ → E} {a : ℝ}
    (hf : ∀ σ : ℝ, a < σ → LaplaceConvergent f σ) :
    DifferentiableOn ℂ (fun w : ℂ ↦ laplace f w) {w : ℂ | a < w.re} := by
  intro w hw
  obtain ⟨σ, haσ, hσw⟩ := exists_between hw
  exact ((hf σ haσ).differentiableAt_laplace (by simpa using hσw)).differentiableWithinAt

/-- If `f` is `LaplaceConvergent` for every real `σ > a`, then `laplace f` is holomorphic
(`AnalyticOnNhd ℂ`) on `{w : ℂ | a < w.re}`. -/
theorem analyticOnNhd_laplace {f : ℝ → E} {a : ℝ}
    (hf : ∀ σ : ℝ, a < σ → LaplaceConvergent f σ) :
    AnalyticOnNhd ℂ (fun w : ℂ ↦ laplace f w) {w : ℂ | a < w.re} := by
  by_cases hE : CompleteSpace E
  · exact (Complex.analyticOnNhd_iff_differentiableOn
      (isOpen_lt continuous_const Complex.continuous_re)).mpr (differentiableOn_laplace hf)
  · convert analyticOnNhd_const (v := (0 : E)) with w
    exact integral_of_not_completeSpace hE

end Differentiation

end Analytic

/-! ### Special functions, negative controls, and integer Gamma–Laplace model -/

section SpecialFunctions

section Const

variable {E : Type*} [NormedAddCommGroup E]

/-- A constant vector is `LaplaceConvergent` at `s` whenever `0 < s.re`. -/
theorem laplaceConvergent_const_of_re_pos [NormedSpace ℂ E] {s : ℂ} (hs : 0 < s.re) (c : E) :
    LaplaceConvergent (fun _ : ℝ ↦ c) s :=
  (integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0).smul_const c

/-- Sharp convergence characterization for a nonzero constant vector: `0 < s.re`. -/
theorem laplaceConvergent_const_iff [NormedSpace ℂ E] {c : E} (hc : c ≠ 0) {s : ℂ} :
    LaplaceConvergent (fun _ : ℝ ↦ c) s ↔ 0 < s.re := by
  have hnorm : (fun t : ℝ ↦ ‖Complex.exp (-s * t)‖) = fun t : ℝ ↦ Real.exp (-s.re * t) := by
    ext t; simp [Complex.norm_exp]
  rw [laplaceConvergent_def, integrable_smul_const hc,
    ← integrable_norm_iff (Continuous.aestronglyMeasurable (by fun_prop)), hnorm]
  exact TauCeti.integrableOn_exp_mul_Ioi_iff.trans neg_lt_zero

/-- Negative control: a nonzero constant vector is NOT `LaplaceConvergent` when `s.re ≤ 0`. -/
theorem not_laplaceConvergent_const_of_re_nonpos [NormedSpace ℂ E] {c : E} (hc : c ≠ 0)
    {s : ℂ} (hs : s.re ≤ 0) : ¬ LaplaceConvergent (fun _ : ℝ ↦ c) s :=
  mt (laplaceConvergent_const_iff hc).mp hs.not_gt

/-- Negative control: a nonzero constant vector has no Laplace transform when `s.re ≤ 0`. -/
theorem not_hasLaplace_const_of_re_nonpos [NormedSpace ℝ E] [NormedSpace ℂ E] {c : E} (hc : c ≠ 0)
    {s : ℂ} (hs : s.re ≤ 0) (z : E) : ¬ HasLaplace (fun _ : ℝ ↦ c) s z :=
  fun h ↦ not_laplaceConvergent_const_of_re_nonpos hc hs h.laplaceConvergent

/-- For `0 < s.re`, the constant function `c : E` has Laplace transform `s⁻¹ • c`. -/
theorem hasLaplace_const [NormedSpace ℝ E] [NormedSpace ℂ E] [CompleteSpace E] {s : ℂ}
    (hs : 0 < s.re) (c : E) : HasLaplace (fun _ : ℝ ↦ c) s (s⁻¹ • c) := by
  refine ⟨laplaceConvergent_const_of_re_pos hs c, ?_⟩
  rw [integral_smul_const, integral_exp_mul_complex_Ioi (a := -s) (by simpa using hs) 0]
  simp

end Const

/-- For `0 < s.re`, the constant function `1 : ℝ → ℂ` has Laplace transform `s⁻¹`. -/
@[to_fun hasLaplace_fun_one]
theorem hasLaplace_one {s : ℂ} (hs : 0 < s.re) : HasLaplace (1 : ℝ → ℂ) s s⁻¹ := by
  have h := hasLaplace_const hs (1 : ℂ)
  rwa [smul_eq_mul, mul_one] at h

/-- Negative control: `HasLaplace (1 : ℝ → ℂ) 0 0` is false, certifying rejection of
divergent integrals whose totalized Bochner integral is `0`. -/
@[to_fun not_hasLaplace_fun_one_zero]
theorem not_hasLaplace_one_zero : ¬ HasLaplace (1 : ℝ → ℂ) 0 0 :=
  not_hasLaplace_const_of_re_nonpos one_ne_zero (by simp) 0

/-- For `a.re < s.re`, `t ↦ Complex.exp (a * t)` has Laplace transform `(s - a)⁻¹`. -/
theorem hasLaplace_cexp_mul {a s : ℂ} (hs : a.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (a * t)) s (s - a)⁻¹ := by
  simpa using (hasLaplace_one (s := s - a) (by simpa using sub_pos.mpr hs)).cexp_smul (a := a)

/-- For real `a < s.re`, `t ↦ (Real.exp (a * t) : ℂ)` has Laplace transform `(s - a)⁻¹`. -/
theorem hasLaplace_rexp_mul {a : ℝ} {s : ℂ} (hs : a < s.re) :
    HasLaplace (fun t : ℝ ↦ (Real.exp (a * t) : ℂ)) s (s - a)⁻¹ :=
  (hasLaplace_cexp_mul (a := (a : ℂ)) (s := s) (by simpa using hs)).congr_Ioi fun _ _ ↦ by
    simp [Complex.ofReal_exp]

/-- Complex Gamma–Laplace transform in `w - 1` form: for `0 < w.re` and `0 < s.re`,
`t ↦ (t : ℂ) ^ (w - 1)` has Laplace transform `Complex.Gamma w * s ^ (-w)`. -/
theorem hasLaplace_cpow_sub_one {w s : ℂ} (hw : 0 < w.re) (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ ↦ (t : ℂ) ^ (w - 1)) s (Complex.Gamma w * s ^ (-w)) := by
  have hfun : (fun t : ℝ ↦ Complex.exp (-s * t) • (t : ℂ) ^ (w - 1)) =
      fun t : ℝ ↦ (t : ℂ) ^ (w - 1) * Complex.exp (-(s * t)) := by
    ext t; rw [smul_eq_mul, neg_mul, mul_comm]
  rw [hasLaplace_def, hfun]
  exact ⟨Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hw hs,
    Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hw hs⟩

/-- Complex Gamma–Laplace transform: for `-1 < w.re` and `0 < s.re`, `t ↦ (t : ℂ) ^ w` has Laplace
transform `Complex.Gamma (w + 1) * s ^ (-(w + 1))`. -/
theorem hasLaplace_cpow {w s : ℂ} (hw : -1 < w.re) (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ ↦ (t : ℂ) ^ w) s (Complex.Gamma (w + 1) * s ^ (-(w + 1))) := by
  have hw' : 0 < (w + 1).re := by simp [Complex.add_re]; linarith
  simpa [add_sub_cancel_right] using hasLaplace_cpow_sub_one hw' hs

/-- Integer power Laplace transform: for `k : ℕ` and `0 < s.re`, `t ↦ (t : ℂ) ^ k` has Laplace
transform `(k.factorial : ℂ) / s ^ (k + 1)`. -/
theorem hasLaplace_pow (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ ↦ (t : ℂ) ^ k) s ((k.factorial : ℂ) / s ^ (k + 1)) := by
  have hk : -1 < (k : ℂ).re := by simp; linarith [Nat.cast_nonneg (α := ℝ) k]
  have h := (hasLaplace_cpow hk hs).congr_Ioi fun t _ ↦ Complex.cpow_natCast (t : ℂ) k
  rwa [Complex.Gamma_nat_eq_factorial k, Complex.cpow_neg, ← Nat.cast_add_one,
    Complex.cpow_natCast, ← div_eq_mul_inv] at h

/-- Shifted integer power Laplace transform with complex rate: for `k : ℕ` and `a.re < s.re`,
`t ↦ Complex.exp (a * t) * (t : ℂ) ^ k` has transform `(k.factorial : ℂ) / (s - a) ^ (k + 1)`. -/
theorem hasLaplace_cexp_mul_pow (k : ℕ) {a s : ℂ} (hs : a.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (a * t) * (t : ℂ) ^ k) s
      ((k.factorial : ℂ) / (s - a) ^ (k + 1)) := by
  have hpow := hasLaplace_pow k (s := s - a) (by simpa using sub_pos.mpr hs)
  simpa [smul_eq_mul] using hpow.cexp_smul

/-- Integer Gamma–Laplace model for real exponential rate: for `k : ℕ`, `a : ℝ`, and `a < s.re`,
`t ↦ ((Real.exp (a * t) * t ^ k : ℝ) : ℂ)` has transform `(k.factorial : ℂ) / (s - a) ^ (k + 1)`
(Delange 1954, Lemma 4, §5.1.2, p. 233). -/
theorem hasLaplace_rexp_mul_pow (k : ℕ) {a : ℝ} {s : ℂ} (hs : a < s.re) :
    HasLaplace (fun t : ℝ ↦ ((Real.exp (a * t) * t ^ k : ℝ) : ℂ)) s
      ((k.factorial : ℂ) / (s - a) ^ (k + 1)) :=
  (hasLaplace_cexp_mul_pow k (a := (a : ℂ)) (s := s) (by simpa using hs)).congr_Ioi
    fun _ _ ↦ by push_cast; rfl

/-- Normalized integer Gamma–Laplace model: for `A a : ℝ`, `k : ℕ`, and `a < s.re`, the cast of
`t ↦ A / k! * Real.exp (a * t) * t ^ k` to `ℂ` has transform `(A : ℂ) / (s - a) ^ (k + 1)`. -/
theorem hasLaplace_div_factorial_mul_rexp_mul_pow (A a : ℝ) (k : ℕ) {s : ℂ} (hs : a < s.re) :
    HasLaplace (fun t : ℝ ↦ ((A / (k.factorial : ℝ) * Real.exp (a * t) * t ^ k : ℝ) : ℂ)) s
      ((A : ℂ) / (s - a) ^ (k + 1)) := by
  have h := (hasLaplace_rexp_mul_pow k hs).const_smul ((A / (k.factorial : ℝ) : ℝ) : ℂ)
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [smul_eq_mul, Complex.ofReal_div, Complex.ofReal_natCast, div_mul_div_cancel₀ hfac] at h
  exact h.congr_Ioi fun _ _ ↦ by simp [smul_eq_mul, mul_assoc]

end SpecialFunctions

/-! ### The Laplace transform of a primitive and of a derivative -/

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- Left-hand iterated integral on `0 < u ≤ r ≤ T` for the Fubini primitive identity (`s ≠ 0`). -/
private theorem integral_triangle_lhs {f g : ℝ → E} {s : ℂ} (hs : s ≠ 0) {T : ℝ} (hT : 0 ≤ T)
    (hfg : ∀ t ∈ Ici (0 : ℝ), f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hf_int : IntervalIntegrable (fun r : ℝ ↦ Complex.exp (-s * r) • f r) volume 0 T) :
    ∫ r in Ioc 0 T, (∫ u in Ioc 0 T,
        if u ≤ r then (s * Complex.exp (-s * r)) • g u else 0) =
      s • (∫ r in (0 : ℝ)..T, Complex.exp (-s * r) • f r) -
        (1 - Complex.exp (-s * T)) • f 0 := by
  have hinner : ∀ r ∈ Ioc 0 T,
      (∫ u in Ioc 0 T, if u ≤ r then (s * Complex.exp (-s * r)) • g u else 0) =
        (s * Complex.exp (-s * r)) • (f r - f 0) := fun r hr ↦ by
    have hind : (fun u : ℝ ↦ if u ≤ r then (s * Complex.exp (-s * r)) • g u else 0) =
        (Iic r).indicator (fun u : ℝ ↦ (s * Complex.exp (-s * r)) • g u) := by
      ext u; by_cases hur : u ≤ r <;> simp [hur]
    rw [hind, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioc_of_le hr.2, integral_smul, ← intervalIntegral.integral_of_le hr.1.le,
      eq_sub_of_add_eq' (hfg r hr.1.le).symm]
  rw [setIntegral_congr_fun measurableSet_Ioc hinner]
  have h1 : IntegrableOn (fun r : ℝ ↦ s * Complex.exp (-s * r)) (Ioc 0 T) :=
    Continuous.integrableOn_Ioc (by fun_prop)
  have hsub1 : IntegrableOn (fun r : ℝ ↦ s • (Complex.exp (-s * r) • f r)) (Ioc 0 T) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hf_int).smul s
  have hsub2 : IntegrableOn (fun r : ℝ ↦ (s * Complex.exp (-s * r)) • f 0) (Ioc 0 T) :=
    h1.smul_const (f 0)
  have hcongr : (fun r : ℝ ↦ (s * Complex.exp (-s * r)) • (f r - f 0)) =
      fun r : ℝ ↦ s • (Complex.exp (-s * r) • f r) - (s * Complex.exp (-s * r)) • f 0 := by
    ext r; rw [smul_sub, mul_smul]
  rw [hcongr, integral_sub hsub1 hsub2, integral_smul, integral_smul_const,
    ← intervalIntegral.integral_of_le hT, ← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_const_mul, integral_exp_mul_complex (neg_ne_zero.mpr hs)]
  congr 1; congr 1
  field_simp; simp

/-- Right-hand iterated integral on `0 < u ≤ r ≤ T` for the Fubini primitive identity (`s ≠ 0`). -/
private theorem integral_triangle_rhs {f g : ℝ → E} {s : ℂ} (hs : s ≠ 0) {T : ℝ} (hT : 0 ≤ T)
    (hfg : ∀ t ∈ Ici (0 : ℝ), f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hg_int : IntegrableOn g (Ioc 0 T)) :
    ∫ u in Ioc 0 T, (∫ r in Ioc 0 T,
        if u ≤ r then (s * Complex.exp (-s * r)) • g u else 0) =
      (∫ u in (0 : ℝ)..T, Complex.exp (-s * u) • g u) -
        Complex.exp (-s * T) • (f T - f 0) := by
  have hexp : ∀ u : ℝ, ∫ r : ℝ in u..T, s * Complex.exp (-s * r) =
      Complex.exp (-s * u) - Complex.exp (-s * T) := fun u ↦ by
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex (neg_ne_zero.mpr hs)]
    field_simp; ring
  have hinner : ∀ u ∈ Ioc 0 T,
      (∫ r in Ioc 0 T, if u ≤ r then (s * Complex.exp (-s * r)) • g u else 0) =
        Complex.exp (-s * u) • g u - Complex.exp (-s * T) • g u := fun u hu ↦ by
    have hind : (fun r : ℝ ↦ if u ≤ r then (s * Complex.exp (-s * r)) • g u else 0) =
        (Ici u).indicator (fun r : ℝ ↦ (s * Complex.exp (-s * r)) • g u) := by
      ext r; by_cases hur : u ≤ r <;> simp [hur]
    have hset : Ici u ∩ Ioc 0 T =ᵐ[volume] Ioc u T := by
      have heq : Ici u ∩ Ioc 0 T = Icc u T := Set.ext fun r ↦
        ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hu.1.trans_le h.1, h.2⟩⟩
      exact heq ▸ Ioc_ae_eq_Icc.symm
    rw [hind, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      setIntegral_congr_set hset, integral_smul_const, ← intervalIntegral.integral_of_le hu.2,
      hexp, sub_smul]
  rw [setIntegral_congr_fun measurableSet_Ioc hinner]
  have hug1 : IntegrableOn (fun u : ℝ ↦ Complex.exp (-s * u) • g u) (Ioc 0 T) :=
    hg_int.continuousOn_smul_of_subset
      (Continuous.continuousOn (by fun_prop : Continuous fun u : ℝ ↦ Complex.exp (-s * u)))
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
  have hug2 : IntegrableOn (fun u : ℝ ↦ Complex.exp (-s * T) • g u) (Ioc 0 T) :=
    hg_int.smul (Complex.exp (-s * T))
  rw [integral_sub hug1 hug2, integral_smul, ← intervalIntegral.integral_of_le hT,
    ← intervalIntegral.integral_of_le hT, eq_sub_of_add_eq' (hfg T hT).symm]

/-- Finite-interval integration-by-parts identity on `[0, T]` for a primitive `f` of `g`, valid
for all `s : ℂ`. -/
private theorem cexp_smul_primitive_eq_intervalIntegral {f g : ℝ → E} (s : ℂ) {T : ℝ}
    (hT : 0 ≤ T) (hfg : ∀ t ∈ Ici (0 : ℝ), f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hf_int : IntervalIntegrable (fun r : ℝ ↦ Complex.exp (-s * r) • f r) volume 0 T)
    (hg_int : IntegrableOn g (Ioc 0 T)) :
    Complex.exp (-s * T) • f T =
      f 0 + (∫ u in (0 : ℝ)..T, Complex.exp (-s * u) • g u) -
        s • (∫ r in (0 : ℝ)..T, Complex.exp (-s * r) • f r) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simpa using hfg T hT
  · set μT : Measure ℝ := volume.restrict (Ioc 0 T)
    set G : ℝ → ℝ → E := fun r u ↦ if u ≤ r then (s * Complex.exp (-s * r)) • g u else 0
    have hΔ : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
      (isClosed_le continuous_snd continuous_fst).measurableSet
    have h1 : Integrable (fun r : ℝ ↦ s * Complex.exp (-s * r)) μT :=
      Continuous.integrableOn_Ioc (by fun_prop)
    have hprod : Integrable (Function.uncurry G) (μT.prod μT) := by
      refine ((h1.smul_prod hg_int).indicator hΔ).congr (ae_of_all _ fun p ↦ ?_)
      by_cases hp : p.2 ≤ p.1 <;> simp [Function.uncurry, G, hp]
    have hswap := MeasureTheory.integral_integral_swap hprod
    rw [integral_triangle_lhs hs hT hfg hf_int, integral_triangle_rhs hs hT hfg hg_int,
      sub_smul, one_smul, smul_sub] at hswap
    have h0 := sub_eq_zero.mpr hswap
    exact sub_eq_zero.mp (by convert h0 using 1; abel)

/-- **Laplace transform of a derivative, primitive form**: if `f` is a primitive of `g` on `[0, ∞)`,
`f` has Laplace transform `z` at `s`, and `t ↦ Complex.exp (-s * t) • g t` is integrable on
`(0, ∞)`, then `g` has Laplace transform `s • z - f 0` at `s`.

Unlike the textbook rule under exponential order (compare Lebl, *Notes on Diffy Qs*, version 6.11,
§6.2.1, p. 300), no growth bound on `f` and no sign condition on `s.re` are required: the two
integrability hypotheses alone suffice at every complex `s`. -/
theorem hasLaplace_deriv_of_primitive {f g : ℝ → E} {s : ℂ} {z : E}
    (hfg : ∀ t ∈ Ici (0 : ℝ), f t = f 0 + ∫ u in (0 : ℝ)..t, g u)
    (hf : HasLaplace f s z)
    (hg : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • g t) (volume.restrict (Ioi 0))) :
    HasLaplace g s (s • z - f 0) := by
  refine ⟨hg, ?_⟩
  set w : E := ∫ u : ℝ in Ioi 0, Complex.exp (-s * u) • g u
  have hg_tendsto : Tendsto (fun T : ℝ ↦ ∫ u in (0 : ℝ)..T, Complex.exp (-s * u) • g u)
      atTop (𝓝 w) := intervalIntegral_tendsto_integral_Ioi 0 hg tendsto_id
  have hf_tendsto : Tendsto (fun T : ℝ ↦ ∫ r in (0 : ℝ)..T, Complex.exp (-s * r) • f r)
      atTop (𝓝 z) :=
    hf.integral_eq ▸ intervalIntegral_tendsto_integral_Ioi 0 hf.integrable tendsto_id
  have hlim_bdy : Tendsto (fun T : ℝ ↦ Complex.exp (-s * T) • f T)
      atTop (𝓝 (f 0 + w - s • z)) := by
    refine ((tendsto_const_nhds.add hg_tendsto).sub (hf_tendsto.const_smul s)).congr' ?_
    filter_upwards [Ici_mem_atTop (0 : ℝ)] with T hT
    have hf_int : IntervalIntegrable (fun r : ℝ ↦ Complex.exp (-s * r) • f r) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
        (hf.integrable.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl))
    exact (cexp_smul_primitive_eq_intervalIntegral s hT hfg hf_int
      (LaplaceConvergent.integrableOn_Ioc hg T)).symm
  have hbdy_int : IntegrableAtFilter (fun T : ℝ ↦ Complex.exp (-s * T) • f T) atTop volume :=
    ⟨Ioi 0, Ioi_mem_atTop 0, hf.integrable⟩
  have hatTop_inf : ∀ S ∈ (atTop : Filter ℝ), volume S = ∞ := fun S hS ↦ by
    obtain ⟨R, hR⟩ := mem_atTop_sets.mp hS
    exact top_unique (Real.volume_Ici (a := R) ▸ measure_mono hR)
  have hzero : f 0 + w - s • z = 0 := hbdy_int.eq_zero_of_tendsto hatTop_inf hlim_bdy
  exact eq_sub_iff_add_eq.mpr (eq_of_sub_eq_zero (by abel_nf at hzero ⊢; exact hzero))

/-- **Laplace transform of a derivative**: if `f` is right-continuous at `0`
(`ContinuousWithinAt f (Ici 0) 0`), has derivative `f' t` at every `t > 0`, has Laplace transform
`z` at `s`, and `t ↦ Complex.exp (-s * t) • f' t` is integrable on `(0, ∞)`, then `f'` has Laplace
transform `s • z - f 0` at `s` (compare Lebl, *Notes on Diffy Qs*, version 6.11, §6.2.1, p. 300). -/
theorem hasLaplace_deriv {f f' : ℝ → E} {s : ℂ} {z : E}
    (hf0 : ContinuousWithinAt f (Ici 0) 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf : HasLaplace f s z)
    (hf' : Integrable (fun t : ℝ ↦ Complex.exp (-s * t) • f' t) (volume.restrict (Ioi 0))) :
    HasLaplace f' s (s • z - f 0) := by
  refine hasLaplace_deriv_of_primitive (fun t ht ↦ ?_) hf hf'
  rcases eq_or_lt_of_le (mem_Ici.mp ht) with rfl | ht_pos
  · simp
  · have hcont : ContinuousOn f (Icc 0 t) := fun x hx ↦ by
      rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
      · exact hf0.mono Icc_subset_Ici_self
      · exact (hderiv x hx_pos).continuousAt.continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht_pos.le hcont
      (fun x hx ↦ hderiv x hx.1) (LaplaceConvergent.intervalIntegrable hf' ht_pos.le)]
    abel

end Deriv

end TauCeti
