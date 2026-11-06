/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.TateAlgebra
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Analytic substitution of univariate series

`PowerSeries.analyticSubst g f` has coefficients `∑' k, fₖ * coeff n (g ^ k)`.
For restricted `f` and `g` with the appropriate Gauss-norm bound this is evaluation of `f`
in the complete restricted algebra containing `g`. In particular, the result is independent
of the radius used to perform the evaluation. The constant coefficient of `g` need not vanish.
This radius-independent coefficient description permits substitution on open discs.

The coefficient sums have a junk value when they do not converge; the restrictedness and
norm hypotheses in the theorems below guarantee convergence. Under the formal substitution
hypotheses, analytic and formal substitution agree.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.
-/

public section

namespace PowerSeries

section Definition

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- Analytic substitution, defined by coefficient sums. The sums are meaningful under the
restrictedness and radius bounds in `IsRestricted.hasSum_coeff_analyticSubst`. -/
noncomputable def analyticSubst (g f : R⟦X⟧) : R⟦X⟧ :=
  mk fun n ↦ ∑' k, coeff k f * coeff n (g ^ k)

/-- The coefficient sum defining analytic substitution. -/
@[simp]
theorem coeff_analyticSubst (g f : R⟦X⟧) (n : ℕ) :
    coeff n (analyticSubst g f) = ∑' k, coeff k f * coeff n (g ^ k) := by
  simp [analyticSubst]

/-- Substituting into a constant series gives that constant. -/
@[simp]
theorem analyticSubst_C (g : R⟦X⟧) (a : R) : analyticSubst g (C a) = C a := by
  ext n
  simp [coeff_analyticSubst, coeff_C, ite_mul]

/-- Substitution sends zero to zero. -/
@[simp]
theorem analyticSubst_zero (g : R⟦X⟧) : analyticSubst g 0 = 0 := by
  simpa using analyticSubst_C g 0

/-- Substitution sends one to one. -/
@[simp]
theorem analyticSubst_one (g : R⟦X⟧) : analyticSubst g 1 = 1 := by
  simpa using analyticSubst_C g 1

/-- Substituting into the variable gives the inner series. -/
@[simp]
theorem analyticSubst_X (g : R⟦X⟧) : analyticSubst g X = g := by
  ext n
  simp [coeff_analyticSubst, coeff_X, ite_mul]

/-- Substitution by the variable is the identity. -/
@[simp]
theorem X_analyticSubst (f : R⟦X⟧) : analyticSubst X f = f := by
  ext n
  simp [coeff_analyticSubst, coeff_X_pow, mul_ite]

end Definition

section Formal

variable {R : Type*} [CommRing R] [TopologicalSpace R] {f g : R⟦X⟧}

/-- Whenever formal substitution is defined, it agrees with the analytic coefficient sums. -/
theorem analyticSubst_eq_subst (hg : HasSubst g) : analyticSubst g f = f.subst g := by
  ext n
  rw [coeff_analyticSubst, coeff_subst' hg,
    ← tsum_eq_finsum (L := .unconditional _) (coeff_subst_finite' hg f n)]
  simp only [smul_eq_mul]

end Formal

section Restricted

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {r s : ℝ} [Fact (0 < s)] {f h g : R⟦X⟧}

/-- The coefficients of evaluation in a restricted algebra are the convergent coefficient
sums defining analytic substitution. -/
theorem IsRestricted.hasSum_coeff_analyticSubst (hf : f.IsRestricted r)
    (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) (n : ℕ) :
    HasSum (fun k ↦ coeff k f * coeff n (g ^ k)) (coeff n (analyticSubst g f)) := by
  let G : IsRestricted.subring (R := R) s := ⟨g, hg⟩
  have hG : ‖G‖ ≤ r := by
    simpa only [TauCeti.PowerSeries.norm_eq_gaussNorm] using hgr
  have H := (hf.hasSum_evalAt hG).map
    ((coeff n).toAddMonoidHom.comp (IsRestricted.subring (R := R) s).subtype.toAddMonoidHom)
    (TauCeti.PowerSeries.uniformContinuous_coeff n).continuous
  have H' : Summable (fun k ↦ coeff k f * coeff n (g ^ k)) := by
    simpa [G, Function.comp_def, TauCeti.PowerSeries.coe_smul_isRestrictedSubring] using H.summable
  simpa only [coeff_analyticSubst] using H'.hasSum

/-- Analytic substitution is evaluation in any restricted algebra in which the inner series
has sufficiently small Gauss norm. Thus it does not depend on the chosen radius. -/
theorem IsRestricted.analyticSubst_eq_evalAt (hf : f.IsRestricted r)
    (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) :
    analyticSubst g f =
      (evalAt (A := IsRestricted.subring s) f ⟨g, hg⟩ : R⟦X⟧) := by
  ext n
  have hG : ‖(⟨g, hg⟩ : IsRestricted.subring s)‖ ≤ r := by
    rwa [TauCeti.PowerSeries.norm_eq_gaussNorm]
  have H := (hf.hasSum_evalAt hG).map
    ((coeff n).toAddMonoidHom.comp (IsRestricted.subring (R := R) s).subtype.toAddMonoidHom)
    (TauCeti.PowerSeries.uniformContinuous_coeff n).continuous
  exact (hf.hasSum_coeff_analyticSubst hg hgr n).unique (by
    simpa [Function.comp_def, TauCeti.PowerSeries.coe_smul_isRestrictedSubring] using H)

/-- Substitution into a series restricted at `s` preserves restrictedness at `s`, provided
its Gauss norm is at most a radius of restriction of the outer series. -/
theorem IsRestricted.analyticSubst (hf : f.IsRestricted r)
    (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) :
    (analyticSubst g f).IsRestricted s := by
  rw [hf.analyticSubst_eq_evalAt hg hgr]
  exact (evalAt (A := IsRestricted.subring s) f ⟨g, hg⟩).property

/-- Analytic substitution is additive in the outer series. -/
theorem IsRestricted.analyticSubst_add (hf : f.IsRestricted r) (hh : h.IsRestricted r)
    (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) :
    PowerSeries.analyticSubst g (f + h) =
      PowerSeries.analyticSubst g f + PowerSeries.analyticSubst g h := by
  have hG : ‖(⟨g, hg⟩ : IsRestricted.subring s)‖ ≤ r := by
    rwa [TauCeti.PowerSeries.norm_eq_gaussNorm]
  rw [IsRestricted.analyticSubst_eq_evalAt (hf.add hh) hg hgr,
    hf.analyticSubst_eq_evalAt hg hgr, hh.analyticSubst_eq_evalAt hg hgr,
    hf.evalAt_add hh hG,
    Subring.coe_add]

/-- Analytic substitution is multiplicative in the outer series. -/
theorem IsRestricted.analyticSubst_mul (hf : f.IsRestricted r) (hh : h.IsRestricted r)
    (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) :
    PowerSeries.analyticSubst g (f * h) =
      PowerSeries.analyticSubst g f * PowerSeries.analyticSubst g h := by
  have hG : ‖(⟨g, hg⟩ : IsRestricted.subring s)‖ ≤ r := by
    rwa [TauCeti.PowerSeries.norm_eq_gaussNorm]
  rw [IsRestricted.analyticSubst_eq_evalAt (hf.mul hh) hg hgr,
    hf.analyticSubst_eq_evalAt hg hgr, hh.analyticSubst_eq_evalAt hg hgr,
    hf.evalAt_mul hh hG,
    Subring.coe_mul]

/-- Analytic substitution does not increase the Gauss norm, measured at the respective
source and target radii. This does not require a multiplicative or normalized coefficient norm. -/
theorem IsRestricted.gaussNorm_analyticSubst_le (hf : f.IsRestricted r)
    (hg : g.IsRestricted s) (hgr : g.gaussNorm norm s ≤ r) :
    (PowerSeries.analyticSubst g f).gaussNorm norm s ≤ f.gaussNorm norm r := by
  let G : IsRestricted.subring (R := R) s := ⟨g, hg⟩
  have hG : ‖G‖ ≤ r := by
    simpa only [TauCeti.PowerSeries.norm_eq_gaussNorm] using hgr
  rw [hf.analyticSubst_eq_evalAt hg hgr, ← TauCeti.PowerSeries.norm_eq_gaussNorm, evalAt_def]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (gaussNorm_nonneg _ _ _ norm_nonneg) fun n ↦ ?_
  cases n with
  | zero =>
    have hC : algebraMap R (IsRestricted.subring (R := R) s) (coeff 0 f) =
        ⟨C (coeff 0 f), isRestricted_C s _⟩ := Subtype.ext (by simp)
    rw [pow_zero, Algebra.smul_def, mul_one, hC, TauCeti.PowerSeries.norm_C]
    simpa using le_gaussNorm norm r f (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf) 0
  | succ n =>
    calc
      ‖coeff (n + 1) f • G ^ (n + 1)‖ ≤ ‖coeff (n + 1) f‖ * ‖G‖ ^ (n + 1) :=
        (norm_smul_le _ _).trans
          (mul_le_mul_of_nonneg_left (norm_pow_le' G n.succ_pos) (norm_nonneg _))
      _ ≤ ‖coeff (n + 1) f‖ * r ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg G) hG _) (norm_nonneg _)
      _ ≤ f.gaussNorm norm r :=
        le_gaussNorm norm r f (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf) _

end Restricted

end PowerSeries
