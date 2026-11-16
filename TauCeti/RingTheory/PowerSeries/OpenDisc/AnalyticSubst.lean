/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.Algebra.Order.GroupWithZero.Basic
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Taylor
import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# Analytic substitution on open discs

Let `g` be a series on the open disc of radius `S₀`. Suppose that its Gauss norm on every
smaller closed disc is strictly less than `R₀`. Substitution by `g` then defines a continuous
ring homomorphism from series on the open disc of radius `R₀` to those on the open disc of
radius `S₀`. It is the convergent sum `∑ aₙ gⁿ`, not formal substitution: the constant
coefficient of `g` need not vanish. Whenever Mathlib's formal substitution `PowerSeries.subst`
is defined on `g` (for instance when the constant coefficient of `g` is nilpotent), the two
substitutions agree (`TauCeti.PowerSeries.OnOpenDisc.coe_analyticSubst_eq_subst`).

Restriction to any smaller closed disc identifies this sum with evaluation in the corresponding
Banach algebra. This gives the local Gauss bounds and compatibility with point evaluation.
Rescaling `f(X) ↦ f(uX)` (`TauCeti.PowerSeries.OnOpenDisc.rescaleHom`) and affine coordinate
changes `f(X) ↦ f(a + uX)` (`TauCeti.PowerSeries.OnOpenDisc.affineHom`) for `‖a‖ < R₀` and
`‖u‖ * S₀ ≤ R₀` are continuous ring homomorphisms between open-disc algebras and agree with the
corresponding analytic substitutions.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.analyticSubst`: substitution `f ↦ f(g(X))` between open-disc
  series when `g` maps every smaller closed disc strictly inside the source open disc.
* `TauCeti.PowerSeries.OnOpenDisc.rescaleHom` and `TauCeti.PowerSeries.OnOpenDisc.affineHom`:
  rescaling `f(X) ↦ f(uX)` and affine pullback `f(X) ↦ f(a + uX)` as ring homomorphisms between
  open-disc subrings.

## Main results

* `TauCeti.PowerSeries.OnOpenDisc.continuous_analyticSubst`,
  `TauCeti.PowerSeries.OnOpenDisc.evalAt_analyticSubst`, and
  `TauCeti.PowerSeries.OnOpenDisc.analyticSubst_comp_analyticSubst`: continuity, compatibility with
  point evaluation, and composition of analytic substitutions.
* `TauCeti.PowerSeries.OnOpenDisc.coe_analyticSubst_eq_subst`: agreement with formal substitution
  `PowerSeries.subst` whenever `PowerSeries.HasSubst` holds.
* `TauCeti.PowerSeries.OnOpenDisc.rescaleHom_eq_analyticSubst`,
  `TauCeti.PowerSeries.OnOpenDisc.taylorHom_eq_analyticSubst`, and
  `TauCeti.PowerSeries.OnOpenDisc.affineHom_eq_analyticSubst`: rescaling, Taylor translation, and
  affine pullbacks are special cases of analytic substitution.
* `TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_affineHom`,
  `TauCeti.PowerSeries.OnOpenDisc.affineHom_comp`, and
  `TauCeti.PowerSeries.OnOpenDisc.evalAtHom_comp_affineHom`: uniform continuity, composition, and
  compatibility of affine pullbacks with algebra-valued point evaluation.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace TauCeti.PowerSeries.OnOpenDisc

section AnalyticSubst

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {R₀ S₀ : ℝ} [Fact (0 < S₀)]

attribute [local instance] radius_pos

-- A fixed smaller disc suffices for the injectivity arguments below.
private noncomputable def substRadius : Set.Ioo (0 : ℝ) S₀ :=
  ⟨S₀ / 2, half_pos Fact.out, half_lt_self Fact.out⟩

omit [Fact (0 < S₀)] in
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

omit [Fact (0 < S₀)] in
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

/-- Whenever formal substitution by `g` is defined, analytic substitution has the same
underlying formal power series. -/
theorem coe_analyticSubst_eq_subst (hsub : PowerSeries.HasSubst (g : R⟦X⟧))
    (f : OnOpenDisc.subring R R₀) :
    (analyticSubst g hg f : R⟦X⟧) = (f : R⟦X⟧).subst (g : R⟦X⟧) := by
  ext m
  rw [coeff_analyticSubst, coeff_subst' hsub]
  have hfin : (fun n ↦ coeff n (f : R⟦X⟧) * coeff m ((g : R⟦X⟧) ^ n)).HasFiniteSupport := by
    simpa only [smul_eq_mul] using coeff_subst_finite' hsub (f : R⟦X⟧) m
  simpa only [smul_eq_mul] using tsum_eq_finsum hfin

/-- Substituting the zero series extracts the constant coefficient as a constant series. -/
@[simp]
theorem analyticSubst_zero
    (hg0 : ∀ s : Set.Ioo (0 : ℝ) S₀, ‖restrict s (0 : OnOpenDisc.subring R S₀)‖ < R₀)
    (f : OnOpenDisc.subring R R₀) :
    analyticSubst 0 hg0 f =
      OnOpenDisc.polynomialHom (Polynomial.C (constantCoeff (f : R⟦X⟧))) := by
  apply restrict_injective substRadius
  rw [restrict_analyticSubst, map_zero, evalAt_at_zero, restrict_polynomialHom_C]

section Composition

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

end Composition

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

end AnalyticSubst

section PolynomialBounds

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {R₀ S₀ : ℝ}

attribute [local instance] radius_pos

/-- An affine linear polynomial `a + uX` has closed-disc Gauss norm `max ‖a‖ (‖u‖ * s)`. -/
theorem norm_restrict_C_add_C_mul_X (a u : R) (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X))‖ =
      max ‖a‖ (‖u‖ * (s : ℝ)) := by
  refine le_antisymm (norm_le_iff.mpr fun n ↦ ?_) (max_le ?_ ?_)
  · rw [coe_restrict, OnOpenDisc.coe_polynomialHom]
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      have h0 : coeff (n + 2)
          ((Polynomial.C a + Polynomial.C u * Polynomial.X : Polynomial R) : R⟦X⟧) = 0 := by
        simp
      rw [h0, norm_zero, zero_mul]
      positivity
  · convert norm_coeff_mul_pow_le
      (restrict s (OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X))) 0
      using 1
    simp
  · convert norm_coeff_mul_pow_le
      (restrict s (OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X))) 1
      using 1
    simp

/-- The linear polynomial `a + uX` maps smaller closed discs strictly inside the source open disc
whenever `‖a‖ < R₀` and `‖u‖ * S₀ ≤ R₀`. -/
theorem norm_restrict_C_add_C_mul_X_lt {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X))‖ <
      R₀ :=
  (norm_restrict_C_add_C_mul_X a u s).trans_lt <| max_lt ha <|
    TauCeti.mul_lt_of_mul_le_of_nonneg_left hu s.2.2 (norm_nonneg u) ((norm_nonneg a).trans_lt ha)

/-- The monomial `uX` maps smaller closed discs strictly inside the source open disc when
`0 < R₀` and `‖u‖ * S₀ ≤ R₀`. -/
theorem norm_restrict_C_mul_X_lt [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) :
    ‖restrict s (OnOpenDisc.polynomialHom (Polynomial.C u * Polynomial.X))‖ < R₀ := by
  simpa using norm_restrict_C_add_C_mul_X_lt (a := 0) (by simpa using (Fact.out : 0 < R₀)) hu s

/-- The translated variable `X + a` maps smaller closed discs strictly inside the open disc when
`‖a‖ < R₀` and `‖(1 : R)‖ = 1`. -/
theorem norm_restrict_X_add_C_lt [NormOneClass R] {a : R} (ha : ‖a‖ < R₀)
    (s : Set.Ioo (0 : ℝ) R₀) :
    ‖restrict s (OnOpenDisc.polynomialHom (Polynomial.X + Polynomial.C a))‖ < R₀ := by
  have h := norm_restrict_C_add_C_mul_X_lt (S₀ := R₀) ha (u := 1) (by simp) s
  simpa [add_comm] using h

end PolynomialBounds

section Rescale

variable {R : Type*} [NormedCommRing R] {R₀ S₀ : ℝ}

/-- Rescaling `f(X) ↦ f(uX)` as a ring homomorphism from series on the open disc of radius `R₀`
to series on the open disc of radius `S₀`, whenever `‖u‖ * S₀ ≤ R₀`. -/
noncomputable def rescaleHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S₀ :=
  ((PowerSeries.rescale u).comp (OnOpenDisc.subring R R₀).subtype).codRestrict _ fun f ↦
    OnOpenDisc.mem_subring.mpr (((OnOpenDisc.mem_subring.mp f.2).mono hu).rescale)

/-- Rescaling acts as `PowerSeries.rescale` on the underlying formal power series. -/
@[simp]
theorem coe_rescaleHom {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    (rescaleHom hu f : R⟦X⟧) = PowerSeries.rescale u (f : R⟦X⟧) :=
  (rfl)

/-- Rescaling fixes constant series. -/
@[simp]
theorem rescaleHom_C {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (a : R) :
    rescaleHom hu (OnOpenDisc.polynomialHom (Polynomial.C a)) =
      OnOpenDisc.polynomialHom (Polynomial.C a) :=
  Subtype.ext (by simp)

/-- Rescaling sends the variable `X` to `uX`. -/
@[simp]
theorem rescaleHom_X {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    rescaleHom hu (OnOpenDisc.polynomialHom Polynomial.X) =
      OnOpenDisc.polynomialHom (Polynomial.C u * Polynomial.X) :=
  Subtype.ext (by simp)

/-- Rescaling fixes scalars from a base algebra. -/
@[simp]
theorem rescaleHom_algebraMap {A : Type*} [CommSemiring A] [Algebra A R]
    {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (s : A) :
    rescaleHom hu (algebraMap A (OnOpenDisc.subring R R₀) s) =
      algebraMap A (OnOpenDisc.subring R S₀) s := by
  rw [← polynomialHom_C_algebraMap, rescaleHom_C, polynomialHom_C_algebraMap]

/-- Rescaling commutes with scalar multiplication from a scalar tower. -/
@[simp]
theorem rescaleHom_smul {A : Type*} [Semiring A] [Module A R] [IsScalarTower A R R]
    {u : R} (hu : ‖u‖ * S₀ ≤ R₀) (s : A) (f : OnOpenDisc.subring R R₀) :
    rescaleHom hu (s • f) = s • rescaleHom hu f := by
  apply Subtype.ext
  ext n
  simp [smul_mul_assoc, mul_comm (u ^ n)]

/-- Rescaling by `1` is the identity. -/
@[simp]
theorem rescaleHom_one (h1 : ‖(1 : R)‖ * R₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    rescaleHom h1 f = f :=
  Subtype.ext (by simp)

/-- Rescalings compose by multiplying their factors. -/
theorem rescaleHom_rescaleHom {T₀ : ℝ} {u v : R} (hu : ‖u‖ * S₀ ≤ R₀) (hv : ‖v‖ * T₀ ≤ S₀)
    (huv : ‖u * v‖ * T₀ ≤ R₀) (f : OnOpenDisc.subring R R₀) :
    rescaleHom hv (rescaleHom hu f) = rescaleHom huv f :=
  Subtype.ext (by simp [PowerSeries.rescale_rescale])

section Ultrametric

variable [IsUltrametricDist R]

attribute [local instance] radius_pos

/-- Rescaling on a target closed disc of radius `s` is controlled by any source closed disc of
radius `r` with `‖u‖ * s ≤ r`. -/
theorem norm_restrict_rescaleHom_le {u : R} (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (hus : ‖u‖ * (s : ℝ) ≤ r)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (rescaleHom hu f)‖ ≤ ‖restrict r f‖ := by
  have hs : 0 < (s : ℝ) := s.2.1
  refine norm_le_iff.mpr fun n ↦ (?_ : _ ≤ ‖coeff n (f : R⟦X⟧)‖ * (r : ℝ) ^ n).trans
    (by simpa only [coe_restrict] using norm_coeff_mul_pow_le (restrict r f) n)
  rw [coe_restrict, coe_rescaleHom]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_rescale]
    calc ‖u ^ (n + 1) * coeff (n + 1) (f : R⟦X⟧)‖ * (s : ℝ) ^ (n + 1)
        ≤ (‖u‖ ^ (n + 1) * ‖coeff (n + 1) (f : R⟦X⟧)‖) * (s : ℝ) ^ (n + 1) :=
          mul_le_mul_of_nonneg_right
            ((norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_pow_le' u (Nat.succ_pos n)) (norm_nonneg _)))
            (pow_nonneg hs.le _)
      _ = ‖coeff (n + 1) (f : R⟦X⟧)‖ * (‖u‖ * (s : ℝ)) ^ (n + 1) := by rw [mul_pow]; ring
      _ ≤ ‖coeff (n + 1) (f : R⟦X⟧)‖ * (r : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hus _) (norm_nonneg _)

/-- Rescaling is uniformly continuous for the open-disc Gauss uniformities when the source radius
is positive. -/
theorem uniformContinuous_rescaleHom [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    UniformContinuous (rescaleHom hu) :=
  uniformContinuous_of_norm_restrict_le _ fun s ↦ by
    have hus_lt : ‖u‖ * (s : ℝ) < R₀ :=
      TauCeti.mul_lt_of_mul_le_of_nonneg_left hu s.2.2 (norm_nonneg u) Fact.out
    obtain ⟨r, hr1, hr2⟩ := exists_between hus_lt
    exact ⟨⟨r, (mul_nonneg (norm_nonneg u) s.2.1.le).trans_lt hr1, hr2⟩, 1, fun f ↦ by
      simpa only [one_mul] using norm_restrict_rescaleHom_le hu s _ hr1.le f⟩

/-- Rescaling is continuous for the open-disc Gauss topologies when the source radius is
positive. -/
@[continuity]
theorem continuous_rescaleHom [Fact (0 < R₀)] {u : R} (hu : ‖u‖ * S₀ ≤ R₀) :
    Continuous (rescaleHom hu) :=
  (uniformContinuous_rescaleHom hu).continuous

/-- Rescaling agrees with analytic substitution by `uX`. -/
theorem rescaleHom_eq_analyticSubst [CompleteSpace R] [Fact (0 < R₀)] [Fact (0 < S₀)] {u : R}
    (hu : ‖u‖ * S₀ ≤ R₀) :
    rescaleHom hu =
      analyticSubst (OnOpenDisc.polynomialHom (Polynomial.C u * Polynomial.X))
        (norm_restrict_C_mul_X_lt hu) :=
  eq_analyticSubst _ _ _ (continuous_rescaleHom hu) (rescaleHom_C hu) (rescaleHom_X hu)

end Ultrametric

end Rescale

section Affine

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R] {R₀ S₀ : ℝ}

attribute [local instance] radius_pos

/-- Taylor translation agrees with analytic substitution by `X + a`. -/
theorem taylorHom_eq_analyticSubst [NormOneClass R] [Fact (0 < R₀)] {a : R} (ha : ‖a‖ < R₀) :
    taylorHom ha =
      analyticSubst (OnOpenDisc.polynomialHom (Polynomial.X + Polynomial.C a))
        (norm_restrict_X_add_C_lt ha) :=
  eq_analyticSubst _ _ _ (continuous_taylorHom ha) (fun c ↦ by simp) (by simp)

/-- Affine change of coordinates `f(X) ↦ f(a + uX)` as a ring homomorphism from series on the open
disc of radius `R₀` to series on the open disc of radius `S₀`, for `‖a‖ < R₀` and
`‖u‖ * S₀ ≤ R₀`. -/
noncomputable def affineHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R S₀ :=
  (rescaleHom hu).comp (taylorHom ha)

/-- Affine pullback is Taylor translation followed by rescaling. -/
theorem affineHom_apply {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    affineHom ha hu f = rescaleHom hu (taylorHom ha f) :=
  (rfl)

/-- On formal power series, `affineHom` rescales the Taylor translate. -/
@[simp]
theorem coe_affineHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (f : OnOpenDisc.subring R R₀) :
    (affineHom ha hu f : R⟦X⟧) = PowerSeries.rescale u (PowerSeries.taylor a (f : R⟦X⟧)) := by
  rw [affineHom_apply, coe_rescaleHom, coe_taylorHom]

/-- Affine coordinate change fixes constant series. -/
@[simp]
theorem affineHom_C {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) (c : R) :
    affineHom ha hu (OnOpenDisc.polynomialHom (Polynomial.C c)) =
      OnOpenDisc.polynomialHom (Polynomial.C c) := by
  simp [affineHom_apply]

/-- Affine coordinate change sends `X` to `a + uX`. -/
@[simp]
theorem affineHom_X {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    affineHom ha hu (OnOpenDisc.polynomialHom Polynomial.X) =
      OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X) := by
  rw [affineHom_apply, taylorHom_polynomialHom, Polynomial.taylor_X, map_add, map_add,
    rescaleHom_X, rescaleHom_C, ← map_add, add_comm]

/-- Affine coordinate change fixes scalars from a base algebra. -/
@[simp]
theorem affineHom_algebraMap {A : Type*} [CommSemiring A] [Algebra A R]
    {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) (s : A) :
    affineHom ha hu (algebraMap A (OnOpenDisc.subring R R₀) s) =
      algebraMap A (OnOpenDisc.subring R S₀) s := by
  rw [← polynomialHom_C_algebraMap, affineHom_C, polynomialHom_C_algebraMap]

/-- Affine coordinate change commutes with scalar multiplication from a scalar tower. -/
@[simp]
theorem affineHom_smul {A : Type*} [Semiring A] [Module A R] [IsScalarTower A R R]
    {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) (s : A) (f : OnOpenDisc.subring R R₀) :
    affineHom ha hu (s • f) = s • affineHom ha hu f := by
  have ht : taylorHom ha (s • f) = s • taylorHom ha f := by
    have hs : s • f = (s • (1 : R)) • f := by rw [smul_assoc, one_smul]
    have hst : s • taylorHom ha f = (s • (1 : R)) • taylorHom ha f := by
      rw [smul_assoc, one_smul]
    rw [hs, hst]
    apply Subtype.ext
    rw [coe_taylorHom, coe_smul_subring, coe_smul_subring, coe_taylorHom]
    exact (OnOpenDisc.mem_subring.mp f.2).taylor_smul (s • (1 : R)) ha
  rw [affineHom_apply, affineHom_apply, ht, rescaleHom_smul]

/-- Affine coordinate change with zero centre is rescaling. -/
@[simp]
theorem affineHom_zero_left {u : R} (h0 : ‖(0 : R)‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    affineHom h0 hu = rescaleHom hu := by
  have : Fact (0 < R₀) := ⟨by simpa using h0⟩
  ext f
  simp [affineHom_apply]

/-- Affine coordinate change with unit scaling is Taylor translation. -/
@[simp]
theorem affineHom_one_right {a : R} (ha : ‖a‖ < R₀) (h1 : ‖(1 : R)‖ * R₀ ≤ R₀) :
    affineHom ha h1 = taylorHom ha := by
  ext f
  simp [affineHom_apply]

/-- Affine pullback on a target closed disc of radius `s` is controlled by any source closed disc
of radius `r` containing `a` with `‖u‖ * s ≤ r`. -/
theorem norm_restrict_affineHom_le {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (s : Set.Ioo (0 : ℝ) S₀) (r : Set.Ioo (0 : ℝ) R₀) (hus : ‖u‖ * (s : ℝ) ≤ r) (har : ‖a‖ ≤ r)
    (f : OnOpenDisc.subring R R₀) :
    ‖restrict s (affineHom ha hu f)‖ ≤ ‖restrict r f‖ := by
  rw [affineHom_apply]
  exact (norm_restrict_rescaleHom_le hu s r hus (taylorHom ha f)).trans_eq
    (norm_restrict_taylorHom ha r har f)

/-- Affine coordinate change is uniformly continuous for the open-disc Gauss uniformities. -/
theorem uniformContinuous_affineHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    UniformContinuous (affineHom ha hu) :=
  uniformContinuous_of_norm_restrict_le _ fun s ↦ by
    have hR₀ : 0 < R₀ := (norm_nonneg a).trans_lt ha
    have hlt : max ‖a‖ (‖u‖ * (s : ℝ)) < R₀ :=
      max_lt ha (TauCeti.mul_lt_of_mul_le_of_nonneg_left hu s.2.2 (norm_nonneg u) hR₀)
    obtain ⟨r, hr1, hr2⟩ := exists_between hlt
    have hr0 : 0 < r := (le_max_of_le_left (norm_nonneg a)).trans_lt hr1
    exact ⟨⟨r, hr0, hr2⟩, 1, fun f ↦ by
      simpa only [one_mul] using norm_restrict_affineHom_le ha hu s ⟨r, hr0, hr2⟩
        ((le_max_right _ _).trans hr1.le) ((le_max_left _ _).trans hr1.le) f⟩

/-- Affine coordinate change is continuous for the open-disc Gauss topologies. -/
@[continuity]
theorem continuous_affineHom {a u : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) :
    Continuous (affineHom ha hu) :=
  (uniformContinuous_affineHom ha hu).continuous

/-- Affine coordinate changes compose via `(a, u) ∘ (b, v) = (a + u * b, u * v)`. -/
theorem affineHom_comp {T₀ : ℝ} {a u b v : R} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀)
    (hb : ‖b‖ < S₀) (hv : ‖v‖ * T₀ ≤ S₀) :
    (affineHom hb hv).comp (affineHom ha hu) =
      affineHom (a := a + u * b) (u := u * v)
        ((IsUltrametricDist.norm_add_le_max a (u * b)).trans_lt <| max_lt ha <|
          (norm_mul_le u b).trans_lt <|
            TauCeti.mul_lt_of_mul_le_of_nonneg_left hu hb (norm_nonneg u)
              ((norm_nonneg a).trans_lt ha))
        (by
          rcases le_total 0 T₀ with hT | hT
          · exact (mul_le_mul_of_nonneg_right (norm_mul_le u v) hT).trans <| by
              rw [mul_assoc]
              exact (mul_le_mul_of_nonneg_left hv (norm_nonneg u)).trans hu
          · exact (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hT).trans
              ((norm_nonneg a).trans_lt ha).le) := by
  have : Fact (0 < S₀) := ⟨(norm_nonneg b).trans_lt hb⟩
  have hab : ‖a + u * b‖ < R₀ :=
    (IsUltrametricDist.norm_add_le_max a (u * b)).trans_lt <| max_lt ha <|
      (norm_mul_le u b).trans_lt <|
        TauCeti.mul_lt_of_mul_le_of_nonneg_left hu hb (norm_nonneg u)
          ((norm_nonneg a).trans_lt ha)
  have hstep : (taylorHom hb).comp (affineHom ha hu) = affineHom hab hu := by
    apply ringHom_ext
    · exact (continuous_taylorHom hb).comp (continuous_affineHom ha hu)
    · exact continuous_affineHom hab hu
    · intro c
      simp
    · simp only [RingHom.comp_apply, affineHom_X, taylorHom_polynomialHom]
      congr 1
      simp only [map_add, Polynomial.taylor_mul, Polynomial.taylor_C, Polynomial.taylor_X, map_mul]
      ring
  ext f
  have hf := RingHom.congr_fun hstep f
  simp only [RingHom.comp_apply] at hf ⊢
  rw [affineHom_apply, hf, affineHom_apply, affineHom_apply, rescaleHom_rescaleHom]

/-- Evaluating an affine pullback `f(a + uX)` at an algebra point `b` in the target open disc
agrees with evaluating `f` at `u • b + algebraMap R A a` whenever that point lies in the source
open disc. -/
theorem evalAtHom_comp_affineHom {A : Type*} [NormedRing A] [Algebra R A] [IsBoundedSMul R A]
    [CompleteSpace A] {a u : R} {b : A} (ha : ‖a‖ < R₀) (hu : ‖u‖ * S₀ ≤ R₀) (hb : ‖b‖ < S₀)
    (hab : ‖u • b + algebraMap R A a‖ < R₀) :
    (OnOpenDisc.evalAtHom R hb).comp (affineHom ha hu) = OnOpenDisc.evalAtHom R hab := by
  have : Fact (0 < R₀) := ⟨(norm_nonneg a).trans_lt ha⟩
  apply ringHom_ext
  · exact (continuous_evalAtHom hb).comp (continuous_affineHom ha hu)
  · exact continuous_evalAtHom hab
  · intro c
    simp [OnOpenDisc.evalAtHom_apply]
  · rw [RingHom.comp_apply, affineHom_X, OnOpenDisc.evalAtHom_apply, OnOpenDisc.coe_polynomialHom,
      evalAt_coe]
    simp [OnOpenDisc.evalAtHom_apply, Algebra.smul_def, add_comm]

/-- Affine coordinate change agrees with analytic substitution by `a + uX`. -/
theorem affineHom_eq_analyticSubst [Fact (0 < S₀)] {a u : R} (ha : ‖a‖ < R₀)
    (hu : ‖u‖ * S₀ ≤ R₀) :
    affineHom ha hu =
      analyticSubst
        (OnOpenDisc.polynomialHom (Polynomial.C a + Polynomial.C u * Polynomial.X))
        (norm_restrict_C_add_C_mul_X_lt ha hu) :=
  eq_analyticSubst _ _ _ (continuous_affineHom ha hu) (affineHom_C ha hu) (affineHom_X ha hu)

end Affine

end TauCeti.PowerSeries.OnOpenDisc
