/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.OpenDisc.Eval

/-!
# Analytic substitution on open discs

Let `g` be a series on the open disc of radius `S₀`. Suppose that its Gauss norm on every
smaller closed disc is strictly less than `R₀`. Substitution by `g` then defines a continuous
ring homomorphism from series on the open disc of radius `R₀` to those on the open disc of
radius `S₀`. It is the convergent sum `∑ aₙ gⁿ`, not formal substitution: the constant
coefficient of `g` need not vanish.

Restriction to any smaller closed disc identifies this sum with evaluation in the corresponding
Banach algebra. This gives the local Gauss bounds and compatibility with point evaluation.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {R₀ S₀ : ℝ} [Fact (0 < S₀)]

attribute [local instance] radius_pos

-- A fixed smaller disc suffices for the injectivity arguments below.
private noncomputable def substRadius : Set.Ioo (0 : ℝ) S₀ :=
  ⟨S₀ / 2, half_pos Fact.out, half_lt_self Fact.out⟩

private theorem summable_subst (g : OnOpenDisc.subring R S₀)
    (hg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s g‖ < R₀)
    (f : OnOpenDisc.subring R R₀) :
    Summable (fun n ↦ OnOpenDisc.polynomialHom (Polynomial.C (coeff n (f : R⟦X⟧))) * g ^ n) := by
  rw [summable_iff_cauchySeq_finset]
  apply isUniformInducing_restrictFamily.cauchy_map_iff.mp
  rw [cauchy_pi_iff']
  intro s
  have hrestricted : Summable (fun n ↦
      restrict s (OnOpenDisc.polynomialHom (Polynomial.C (coeff n (f : R⟦X⟧))) * g ^ n)) := by
    simpa only [map_mul, map_pow, restrict_polynomialHom_C, Algebra.smul_def] using
      ((OnOpenDisc.mem_subring.mp f.2).hasSum_evalAt (hg s)).summable
  have hsum (t : Finset ℕ) :
      (restrictFamily (∑ n ∈ t,
        OnOpenDisc.polynomialHom (Polynomial.C (coeff n (f : R⟦X⟧))) * g ^ n)) s =
      ∑ n ∈ t, restrict s
        (OnOpenDisc.polynomialHom (Polynomial.C (coeff n (f : R⟦X⟧))) * g ^ n) := by
    simp only [map_sum, restrictFamily_apply]
  simp only [Filter.map_map, Function.comp_def, Function.eval]
  rw [Filter.map_congr (Filter.Eventually.of_forall hsum)]
  exact summable_iff_cauchySeq_finset.mp hrestricted

private theorem restrict_tsum_subst (g : OnOpenDisc.subring R S₀)
    (hg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s g‖ < R₀)
    (f : OnOpenDisc.subring R R₀) (s : Set.Ioo (0 : ℝ) S₀) :
    restrict s (∑' n, OnOpenDisc.polynomialHom (Polynomial.C (coeff n (f : R⟦X⟧))) * g ^ n) =
      (f : R⟦X⟧).evalAt (restrict s g) := by
  have h := ((summable_subst g hg f).hasSum.map (restrict s)
    (uniformContinuous_restrict s).continuous).tsum_eq
  simpa only [Function.comp_def, map_mul, map_pow, restrict_polynomialHom_C,
    ← Algebra.smul_def, ← evalAt_def] using h.symm

/-- Substitution by an open-disc series whose Gauss norm on each smaller closed disc is
strictly less than the source radius. It is defined by a convergent sum and permits a nonzero
constant coefficient in the inner series. -/
noncomputable def analyticSubst (g : OnOpenDisc.subring R S₀)
    (hg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s g‖ < R₀) :
    OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S₀ where
  toFun f := ∑' n, OnOpenDisc.polynomialHom (Polynomial.C (coeff n (f : R⟦X⟧))) * g ^ n
  map_one' := by
    apply restrict_injective substRadius
    rw [restrict_tsum_subst g hg 1]
    simp
  map_mul' f h := by
    let s : Set.Ioo (0 : ℝ) S₀ := substRadius
    apply restrict_injective s
    rw [restrict_tsum_subst g hg (f * h), map_mul,
      restrict_tsum_subst g hg f, restrict_tsum_subst g hg h, Subring.coe_mul]
    exact (OnOpenDisc.mem_subring.mp f.2).evalAt_mul (OnOpenDisc.mem_subring.mp h.2) (hg s)
  map_zero' := by
    apply restrict_injective substRadius
    rw [restrict_tsum_subst g hg 0]
    simp
  map_add' f h := by
    let s : Set.Ioo (0 : ℝ) S₀ := substRadius
    apply restrict_injective s
    rw [restrict_tsum_subst g hg (f + h), map_add,
      restrict_tsum_subst g hg f, restrict_tsum_subst g hg h, Subring.coe_add]
    exact (OnOpenDisc.mem_subring.mp f.2).evalAt_add (OnOpenDisc.mem_subring.mp h.2) (hg s)

variable (g : OnOpenDisc.subring R S₀)
  (hg : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s g‖ < R₀)

/-- The defining sum for analytic substitution converges in every smaller-radius Gauss norm. -/
theorem hasSum_analyticSubst (f : OnOpenDisc.subring R R₀) :
    HasSum (fun n ↦ OnOpenDisc.polynomialHom (Polynomial.C (coeff n (f : R⟦X⟧))) * g ^ n)
      (analyticSubst g hg f) :=
  (summable_subst g hg f).hasSum

/-- On a smaller closed disc, analytic substitution is evaluation in its restricted algebra. -/
@[simp]
theorem restrict_analyticSubst (f : OnOpenDisc.subring R R₀) (s : Set.Ioo (0 : ℝ) S₀) :
    restrict s (analyticSubst g hg f) = (f : R⟦X⟧).evalAt (restrict s g) :=
  restrict_tsum_subst g hg f s

/-- Analytic substitution is continuous for the topologies of all smaller-radius Gauss norms. -/
theorem continuous_analyticSubst : Continuous (analyticSubst g hg) := by
  rw [continuous_iff]
  intro s
  exact (continuous_evalAtHom (R := R) (hg s)).congr fun f ↦ by
    rw [OnOpenDisc.evalAtHom_apply, restrict_analyticSubst]

/-- The Gauss norm after substitution is bounded by any source Gauss norm whose radius bounds
the Gauss norm of the inner series on the chosen target closed disc. -/
theorem norm_restrict_analyticSubst_le [NormOneClass R] (f : OnOpenDisc.subring R R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (hgr : ‖restrict s g‖ ≤ r) :
    ‖restrict s (analyticSubst g hg f)‖ ≤ ‖restrict r f‖ := by
  rw [restrict_analyticSubst, norm_eq_gaussNorm (restrict r f), coe_restrict]
  exact norm_evalAt_le_gaussNorm
    (hasGaussNorm_of_isRestricted (mem_subring_iff_forall_isRestricted.mp f.2 r)) hgr

/-- Constants are fixed by analytic substitution. -/
@[simp]
theorem analyticSubst_C (a : R) :
    analyticSubst g hg (OnOpenDisc.polynomialHom (Polynomial.C a)) =
      OnOpenDisc.polynomialHom (Polynomial.C a) := by
  apply restrict_injective substRadius
  rw [restrict_analyticSubst, OnOpenDisc.coe_polynomialHom, Polynomial.coe_C, evalAt_C,
    restrict_polynomialHom_C]

/-- The source variable is sent to the inner series. -/
@[simp]
theorem analyticSubst_X :
    analyticSubst g hg (OnOpenDisc.polynomialHom Polynomial.X) = g := by
  apply restrict_injective substRadius
  rw [restrict_analyticSubst, OnOpenDisc.coe_polynomialHom, Polynomial.coe_X, evalAt_X]

/-- Coefficients of analytic substitution are convergent sums, including contributions from
all powers of an inner series with nonzero constant term. -/
theorem hasSum_coeff_analyticSubst (f : OnOpenDisc.subring R R₀) (m : ℕ) :
    HasSum (fun n ↦ coeff n (f : R⟦X⟧) * coeff m ((g : R⟦X⟧) ^ n))
      (coeff m (analyticSubst g hg f : R⟦X⟧)) := by
  have h := (hasSum_analyticSubst g hg f).map
    ((coeff m).toAddMonoidHom.comp (OnOpenDisc.subring R S₀).subtype.toAddMonoidHom)
    (uniformContinuous_coeff m).continuous
  simpa [Function.comp_def, coeff_C_mul] using h

/-- The coefficient formula for analytic substitution. -/
theorem coeff_analyticSubst (f : OnOpenDisc.subring R R₀) (m : ℕ) :
    coeff m (analyticSubst g hg f : R⟦X⟧) =
      ∑' n, coeff n (f : R⟦X⟧) * coeff m ((g : R⟦X⟧) ^ n) :=
  (hasSum_coeff_analyticSubst g hg f m).tsum_eq.symm

/-- On polynomials analytic substitution is polynomial evaluation. -/
@[simp low]
theorem analyticSubst_polynomialHom (p : Polynomial R) :
    analyticSubst g hg (OnOpenDisc.polynomialHom p) =
      Polynomial.eval₂RingHom (OnOpenDisc.polynomialHom.comp Polynomial.C) g p := by
  exact RingHom.congr_fun (Polynomial.ringHom_ext
    (fun a ↦ by simp) (by simp) :
    (analyticSubst g hg).comp OnOpenDisc.polynomialHom =
      Polynomial.eval₂RingHom (OnOpenDisc.polynomialHom.comp Polynomial.C) g) p

/-- A continuous ring homomorphism fixing coefficients and sending the variable to `g` is
analytic substitution by `g`. -/
theorem eq_analyticSubst (φ : OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S₀)
    (hφ : Continuous φ)
    (hC : ∀ a, φ (OnOpenDisc.polynomialHom (Polynomial.C a)) =
      OnOpenDisc.polynomialHom (Polynomial.C a))
    (hX : φ (OnOpenDisc.polynomialHom Polynomial.X) = g) : φ = analyticSubst g hg := by
  exact ringHom_ext hφ (continuous_analyticSubst g hg)
    (fun a ↦ by simpa using hC a) (by simpa using hX)

/-- A uniform strict bound for the source closed-disc norms also bounds every target
closed-disc norm after substitution. -/
theorem norm_restrict_analyticSubst_lt [NormOneClass R] (f : OnOpenDisc.subring R R₀)
    {M : ℝ} (hf : ∀ r : Set.Ioo (0 : ℝ) R₀, ‖restrict r f‖ < M)
    (s : Set.Ioo (0 : ℝ) S₀) : ‖restrict s (analyticSubst g hg f)‖ < M := by
  obtain ⟨r, hgr, hrR⟩ := exists_between (hg s)
  let r' : Set.Ioo (0 : ℝ) R₀ := ⟨r, (norm_nonneg _).trans_lt hgr, hrR⟩
  exact (norm_restrict_analyticSubst_le g hg f s r' hgr.le).trans_lt (hf r')

section Evaluation

variable {A : Type*} [NormedRing A] [Algebra R A] [IsBoundedSMul R A]
  [CompleteSpace A] [IsUltrametricDist A] [NormOneClass A] {b : A}

include hg in
omit [CompleteSpace R] [Fact (0 < S₀)] [CompleteSpace A] in
/-- The inner series takes points of the target open disc into the source open disc. -/
theorem norm_evalAt_lt (hb : ‖b‖ < S₀) : ‖(g : R⟦X⟧).evalAt b‖ < R₀ := by
  obtain ⟨s, hbs, hsS⟩ := exists_between hb
  let s' : Set.Ioo (0 : ℝ) S₀ := ⟨s, (norm_nonneg _).trans_lt hbs, hsS⟩
  -- Reduction to the real witness s hides its interval subtype from instance search.
  have : Fact (0 < (s' : ℝ)) := ⟨s'.2.1⟩
  have hf := hasGaussNorm_of_isRestricted (mem_subring_iff_forall_isRestricted.mp g.2 s')
  calc ‖(g : R⟦X⟧).evalAt b‖ ≤ (g : R⟦X⟧).gaussNorm norm s :=
      norm_evalAt_le_gaussNorm hf hbs.le
    _ = ‖restrict s' g‖ := by rw [norm_eq_gaussNorm, coe_restrict]
    _ < R₀ := hg s'

/-- Point evaluation commutes with analytic substitution, also in noncommutative complete
normed coefficient algebras. -/
theorem evalAt_analyticSubst (hb : ‖b‖ < S₀) (f : OnOpenDisc.subring R R₀) :
    (analyticSubst g hg f : R⟦X⟧).evalAt b =
      (f : R⟦X⟧).evalAt ((g : R⟦X⟧).evalAt b) := by
  have heq : (OnOpenDisc.evalAtHom R hb).comp (analyticSubst g hg) =
      OnOpenDisc.evalAtHom R (norm_evalAt_lt g hg hb) := by
    apply ringHom_ext
    · exact (continuous_evalAtHom hb).comp (continuous_analyticSubst g hg)
    · exact continuous_evalAtHom _
    · intro a
      simp [OnOpenDisc.evalAtHom_apply]
    · simp [OnOpenDisc.evalAtHom_apply]
  simpa only [RingHom.comp_apply, OnOpenDisc.evalAtHom_apply] using RingHom.congr_fun heq f

end Evaluation

variable {T₀ : ℝ} [Fact (0 < T₀)]

/-- Analytic substitutions compose, with the strict radius condition supplied by the
closed-disc Gauss estimates. -/
theorem analyticSubst_comp_analyticSubst [NormOneClass R] (h : OnOpenDisc.subring R T₀)
    (hh : ∀ t : Set.Ioo (0 : ℝ) T₀, ‖restrict t h‖ < S₀) :
    (analyticSubst h hh).comp (analyticSubst g hg) =
      analyticSubst (analyticSubst h hh g) (norm_restrict_analyticSubst_lt h hh g hg) := by
  apply eq_analyticSubst
  · exact (continuous_analyticSubst h hh).comp (continuous_analyticSubst g hg)
  · intro a
    simp
  · simp

/-- Substituting the variable itself is the identity. -/
@[simp]
theorem analyticSubst_self [NormOneClass R] (f : OnOpenDisc.subring R S₀) :
    analyticSubst (OnOpenDisc.polynomialHom Polynomial.X : OnOpenDisc.subring R S₀)
      (fun s ↦ by simpa only [norm_restrict_X] using s.2.2) f = f := by
  have heq := eq_analyticSubst
    (OnOpenDisc.polynomialHom Polynomial.X : OnOpenDisc.subring R S₀)
    (fun s ↦ by simpa only [norm_restrict_X] using s.2.2)
    (RingHom.id _) continuous_id (fun _ ↦ rfl) rfl
  exact (RingHom.congr_fun heq f).symm

end TauCeti.PowerSeries.OnOpenDisc
