/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Basic

/-!
# Classical derivatives of smooth Sobolev representatives

A smooth representative of a weak Sobolev function has classical derivatives equal almost
everywhere to its recorded weak derivatives. The nested iterated-gradient fields have exactly
the same pointwise norms as Mathlib's multilinear derivatives. Consequently smooth Sobolev
representatives satisfy the integrability hypotheses of classical higher-order cutoff estimates.

The weak-to-classical identification uses `TauCeti.HasWeakFDerivOn.ae_eq_fderiv`; the norm
comparison uses Mathlib's `norm_iteratedFDeriv_fderiv` and the Riesz isometry. These are the
identifications used in smooth approximation in Evans, *Partial Differential Equations*, §5.3.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ENNReal ContDiff

section Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Taking `i` further derivatives of the `k`th iterated-gradient field has the same norm as
taking `i + k + 1` derivatives of the original scalar function. No smoothness is needed. -/
theorem norm_iteratedFDeriv_iteratedGradientChain (f : E → ℝ) (i k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (iteratedGradientChain f k) x‖ =
      ‖iteratedFDeriv ℝ (i + k + 1) f x‖ := by
  induction k generalizing i with
  | zero =>
      rw [iteratedGradientChain_zero]
      -- The gradient is the inverse Riesz isometry applied to the Fréchet derivative.
      exact ((InnerProductSpace.toDual ℝ E).symm.norm_iteratedFDeriv_comp_left
        (fderiv ℝ f) x i).trans norm_iteratedFDeriv_fderiv
  | succ k ih =>
      rw [iteratedGradientChain_succ, norm_iteratedFDeriv_fderiv]
      exact (ih (i + 1)).trans (congrArg
        (fun j => ‖iteratedFDeriv ℝ (j + 1) f x‖) (by omega))

/-- The nested iterated-gradient field has the same norm as the corresponding multilinear
derivative of the scalar function. -/
@[simp]
theorem norm_iteratedGradientChain (f : E → ℝ) (k : ℕ) (x : E) :
    ‖iteratedGradientChain f k x‖ = ‖iteratedFDeriv ℝ (k + 1) f x‖ :=
  (norm_iteratedFDeriv_zero (f := iteratedGradientChain f k) (x := x)).symm.trans
    ((norm_iteratedFDeriv_iteratedGradientChain f 0 k x).trans
      (congrArg (fun j => ‖iteratedFDeriv ℝ (j + 1) f x‖) (Nat.zero_add k)))

/-- Iterated-gradient fields preserve subtraction of smooth scalar functions. -/
@[simp]
theorem iteratedGradientChain_sub {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedGradientChain (f - g) k =
      iteratedGradientChain f k - iteratedGradientChain g k := by
  induction k with
  | zero =>
      simp only [iteratedGradientChain_zero]
      funext x
      simp only [Pi.sub_apply, gradient,
        fderiv_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x), map_sub]
  | succ k ih =>
      simp only [iteratedGradientChain_succ, ih]
      funext x
      exact fderiv_sub ((contDiff_iteratedGradientChain hf k).differentiable (by simp) x)
        ((contDiff_iteratedGradientChain hg k).differentiable (by simp) x)

/-- The difference of two smooth iterated-gradient fields has the same norm as the difference
of their multilinear derivatives. This identifies the error seminorms in smooth approximation. -/
theorem norm_iteratedGradientChain_sub {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) (x : E) :
    ‖iteratedGradientChain f k x - iteratedGradientChain g k x‖ =
      ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) g x‖ := by
  rw [← Pi.sub_apply, ← iteratedGradientChain_sub hf hg, norm_iteratedGradientChain]
  exact congrArg norm (fun_iteratedFDeriv_sub_apply
    (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt)

end Classical

section Sobolev

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The highest recorded weak derivative of a smooth Sobolev representative is its classical
iterated-gradient field almost everywhere on the domain. -/
theorem Wkp.iteratedGradient_ae_eq_of_contDiff (k : ℕ) (u : Wkp mu Omega p (k + 1))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hu : (value (k + 1) u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (iteratedGradient k u : E → IteratedGradient E k) =ᵐ[mu.restrict Omega]
      iteratedGradientChain f k := by
  induction k with
  | zero =>
      have hd := ((hasWeakFDerivOn_value u).congr_ae hu).ae_eq_fderiv
        (((contDiff_infty_iff_fderiv.mp hf).2.continuous.locallyIntegrable
          (μ := mu)).locallyIntegrableOn (Omega : Set E))
        (fun x _ => hf.differentiable (by simp) x)
      filter_upwards [hd] with x hx
      exact (InnerProductSpace.toDual ℝ E).injective (by
        -- `innerSL` is the continuous-linear-map view of the Riesz isometry.
        ext y
        simpa only [iteratedGradientChain_zero, gradient,
          LinearIsometryEquiv.apply_symm_apply, InnerProductSpace.toDual_apply_apply,
          innerSL_apply_apply] using congrArg (fun l : E →L[ℝ] ℝ => l y) hx)
  | succ k ih =>
      have hprev : (value (k + 1) (lowerOrder (k + 1) u) : E → ℝ) =ᵐ[mu.restrict Omega] f := by
        simpa only [value_succ] using hu
      have hs := contDiff_iteratedGradientChain hf k
      have hc := (contDiff_infty_iff_fderiv.mp hs).2.continuous
      have hd := ((hasWeakFDerivOn_iteratedGradient k u).congr_ae (ih _ hprev)).ae_eq_fderiv
        ((hc.locallyIntegrable (μ := mu)).locallyIntegrableOn (Omega : Set E))
        (fun x _ => hs.differentiable (by simp) x)
      simpa only [iteratedGradientChain_succ] using hd

/-- Every classical derivative through order `k` of a smooth `W^{k,p}` representative belongs
to `Lᵖ` on the domain. -/
theorem Wkp.memLp_iteratedFDeriv_of_contDiff (k : ℕ) (u : Wkp mu Omega p k)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) p (mu.restrict Omega) := by
  induction k with
  | zero =>
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      refine (MemLp.ae_eq hu (Lp.memLp (value 0 u))).congr_norm
        (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable ?_
      exact .of_forall fun x => (norm_iteratedFDeriv_zero (f := f) (x := x)).symm
  | succ k ih =>
      intro i hi
      by_cases hik : i ≤ k
      · exact ih (lowerOrder k u) (by simpa only [value_succ] using hu) i hik
      · have hi' : i = k + 1 := by omega
        subst i
        have hchain := MemLp.ae_eq (iteratedGradient_ae_eq_of_contDiff k u hf hu)
          (Lp.memLp (iteratedGradient k u))
        refine hchain.congr_norm
          (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable ?_
        exact .of_forall fun x => norm_iteratedGradientChain f k x

end Sobolev

end TauCeti
