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

The classical derivative norm comparisons are adapted from Tau Ceti contribution
[#12418](https://github.com/TauCetiProject/TauCeti/pull/12418),
*Bound smooth multiplication in higher-order zero-boundary Sobolev spaces*.
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

/-- Iterated-gradient fields through order `k + 1` preserve subtraction of scalar functions
that are `C^{k+1}` at the point of evaluation. -/
@[simp]
theorem iteratedGradientChain_sub {f g : E → ℝ} {x : E}
    (k : ℕ) (hf : ContDiffAt ℝ (k + 1) f x) (hg : ContDiffAt ℝ (k + 1) g x) :
    iteratedGradientChain (f - g) k x =
      iteratedGradientChain f k x - iteratedGradientChain g k x := by
  induction k generalizing x with
  | zero =>
      simp only [iteratedGradientChain_zero, gradient,
        fderiv_sub (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp)), map_sub]
  | succ k ih =>
      simp only [iteratedGradientChain_succ]
      have heq : iteratedGradientChain (f - g) k =ᶠ[nhds x]
          iteratedGradientChain f k - iteratedGradientChain g k := by
        filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
        exact ih (hfy.of_le (by simp)) (hgy.of_le (by simp))
      rw [heq.fderiv_eq]
      have hfs := contDiffAt_iteratedGradientChain hf k (m := 1)
        (by simp [add_comm, add_left_comm])
      have hgs := contDiffAt_iteratedGradientChain hg k (m := 1)
        (by simp [add_comm, add_left_comm])
      exact fderiv_sub (hfs.differentiableAt (by simp)) (hgs.differentiableAt (by simp))

/-- The order-`k + 1` iterated-gradient fields of two scalar functions that are `C^{k+1}` at
a point have the same difference norm there as their multilinear derivatives. This identifies
the error seminorms in smooth approximation. -/
theorem norm_iteratedGradientChain_sub {f g : E → ℝ} {x : E}
    (k : ℕ) (hf : ContDiffAt ℝ (k + 1) f x) (hg : ContDiffAt ℝ (k + 1) g x) :
    ‖iteratedGradientChain f k x - iteratedGradientChain g k x‖ =
      ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) g x‖ := by
  rw [← iteratedGradientChain_sub k hf hg, norm_iteratedGradientChain]
  exact congrArg norm (fun_iteratedFDeriv_sub_apply
    (hf.of_le (by simp)) (hg.of_le (by simp)))

end Classical

section Sobolev

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The highest recorded weak derivative of a Sobolev representative that is `C^{k+1}` on the
domain is its classical iterated-gradient field almost everywhere there. -/
theorem Wkp.iteratedGradient_ae_eq_of_contDiffOn (k : ℕ) (u : Wkp mu Omega p (k + 1))
    {f : E → ℝ} (hf : ContDiffOn ℝ (k + 1) f Omega)
    (hu : (value (k + 1) u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (iteratedGradient k u : E → IteratedGradient E k) =ᵐ[mu.restrict Omega]
      iteratedGradientChain f k := by
  induction k with
  | zero =>
      have hd := ((hasWeakFDerivOn_value u).congr_ae hu).ae_eq_fderiv
        ((hf.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)).locallyIntegrableOn
          Omega.isOpen.measurableSet)
        (fun x hx => (hf.contDiffAt (Omega.isOpen.mem_nhds hx)).differentiableAt (by simp))
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
      have hs : ContDiffOn ℝ 1 (iteratedGradientChain f k) Omega := fun x hx =>
        (contDiffAt_iteratedGradientChain (hf.contDiffAt (Omega.isOpen.mem_nhds hx)) k
          (by simp [add_comm, add_left_comm])).contDiffWithinAt
      have hc := hs.continuousOn_fderiv_of_isOpen Omega.isOpen (by simp)
      have hd := ((hasWeakFDerivOn_iteratedGradient k u).congr_ae
        (ih _ (hf.of_le (by simp)) hprev)).ae_eq_fderiv
        (hc.locallyIntegrableOn Omega.isOpen.measurableSet)
        (fun x hx => (hs.contDiffAt (Omega.isOpen.mem_nhds hx)).differentiableAt (by simp))
      simpa only [iteratedGradientChain_succ] using hd

/-- The `Lᵖ` norm of the highest weak derivative agrees with the classical derivative
seminorm for a representative that is `C^{k+1}` on the domain. -/
theorem Wkp.norm_iteratedGradient_eq_lpNorm_of_contDiffOn (k : ℕ)
    (u : Wkp mu Omega p (k + 1)) {f : E → ℝ}
    (hf : ContDiffOn ℝ (k + 1) f Omega)
    (hu : (value (k + 1) u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    ‖iteratedGradient k u‖ = lpNorm (iteratedFDeriv ℝ (k + 1) f) p (mu.restrict Omega) := by
  rw [Lp.norm_def, lpNorm]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
    ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen (by simp)).aestronglyMeasurable
      Omega.isOpen.measurableSet) ?_
  filter_upwards [iteratedGradient_ae_eq_of_contDiffOn k u hf hu] with x hx
  rw [hx, norm_iteratedGradientChain]

/-- The full Sobolev norm controls the `Lᵖ` seminorm of each classical derivative through
order `k` of a representative that is `C^k` on the domain. -/
theorem Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn (k : ℕ) (u : Wkp mu Omega p k)
    {f : E → ℝ} (hf : ContDiffOn ℝ k f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    ∀ i ≤ k, lpNorm (iteratedFDeriv ℝ i f) p (mu.restrict Omega) ≤ ‖u‖ := by
  induction k with
  | zero =>
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      have he : eLpNorm (iteratedFDeriv ℝ 0 f) p (mu.restrict Omega) =
          eLpNorm (value 0 u) p (mu.restrict Omega) := by
        refine eLpNorm_congr_norm_ae
          ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen (by simp)).aestronglyMeasurable
            Omega.isOpen.measurableSet) (Lp.aestronglyMeasurable _) ?_
        filter_upwards [hu] with x hx
        rw [norm_iteratedFDeriv_zero, hx]
      simpa only [lpNorm, he, ← Lp.norm_def, value_zero] using le_rfl (a := ‖u‖)
  | succ k ih =>
      intro i hi
      by_cases hik : i ≤ k
      · exact (ih (lowerOrder k u) (hf.of_le (by simp))
          (by simpa only [value_succ] using hu) i hik).trans (norm_lowerOrder_le k u)
      · have hi' : i = k + 1 := by omega
        subst i
        rw [← norm_iteratedGradient_eq_lpNorm_of_contDiffOn k u hf hu]
        exact norm_iteratedGradient_le k u

/-- Every classical derivative through order `k` of a `W^{k,p}` representative that is `C^k`
on the domain belongs to `Lᵖ` there. -/
theorem Wkp.memLp_iteratedFDeriv_of_contDiffOn (k : ℕ) (u : Wkp mu Omega p k)
    {f : E → ℝ} (hf : ContDiffOn ℝ k f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) p (mu.restrict Omega) := by
  induction k with
  | zero =>
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      refine (MemLp.ae_eq hu (Lp.memLp (value 0 u))).congr_norm
        ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen
          (by simp)).aestronglyMeasurable Omega.isOpen.measurableSet) ?_
      exact .of_forall fun x => (norm_iteratedFDeriv_zero (f := f) (x := x)).symm
  | succ k ih =>
      intro i hi
      by_cases hik : i ≤ k
      · exact ih (lowerOrder k u) (hf.of_le (by simp)) (by simpa only [value_succ] using hu) i hik
      · have hi' : i = k + 1 := by omega
        subst i
        have hchain := MemLp.ae_eq (iteratedGradient_ae_eq_of_contDiffOn k u hf hu)
          (Lp.memLp (iteratedGradient k u))
        refine hchain.congr_norm
          ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen
            (by simp)).aestronglyMeasurable Omega.isOpen.measurableSet) ?_
        exact .of_forall fun x => norm_iteratedGradientChain f k x

end Sobolev

end TauCeti
