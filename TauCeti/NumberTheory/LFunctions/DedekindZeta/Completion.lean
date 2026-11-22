/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.CompletedPartialZeta
import TauCeti.Analysis.Meromorphic.NormalForm
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
import TauCeti.NumberTheory.NumberField.Units.Regulator.Basic
import TauCeti.RingTheory.ClassGroup.Basic

/-!
# The completed Dedekind zeta function and analytic continuation of `dedekindZetaC`

For a number field `K`, this file constructs the completed Dedekind zeta function
`TauCeti.LFunctions.completedDedekindZeta` from the completed partial zeta functions
`TauCeti.LFunctions.completedPartialZeta`, establishes Hecke's functional equation, reflection
symmetry, and simple-pole residues at `s = 0` and `s = 1`, and deduces the full meromorphic
continuation, residue at `s = 1`, and leading-term expansion at `s = 0` of
`TauCeti.LFunctions.dedekindZetaC K` (Neukirch, Chapter VII, §5, (5.5)–(5.11)). Over `ℚ`, it also
identifies `completedDedekindZeta ℚ` with Mathlib's `completedRiemannZeta`.

## Main definitions

* `TauCeti.LFunctions.completedDedekindZeta`: the canonical meromorphic continuation from
  `Re s > 1` of `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`.

## Main results

* `TauCeti.LFunctions.completedDedekindZeta_eq_sum_completedPartialZeta`: the completed Dedekind
  zeta function is the sum of the completed partial zeta functions over the ideal classes.
* `TauCeti.LFunctions.completedDedekindZeta_one_sub`,
  `TauCeti.LFunctions.completedDedekindZeta_one_sub_eventuallyEq`,
  `TauCeti.LFunctions.completedDedekindZeta_conj`: the functional equation `Λ_K(1 - s) = Λ_K(s)`
  (pointwise and as punctured germs) and reflection symmetry `Λ_K(conj s) = conj (Λ_K(s))`.
* `TauCeti.LFunctions.analyticAt_completedDedekindZeta`,
  `TauCeti.LFunctions.analyticAt_completedDedekindZeta_iff`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_zero`,
  `TauCeti.LFunctions.meromorphicOrderAt_completedDedekindZeta_one`,
  `TauCeti.LFunctions.tendsto_mul_completedDedekindZeta_zero`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_completedDedekindZeta`: analyticity off `{0, 1}` and
  simple poles of `Λ_K` at `0` and `1` with residues `∓ 2^(r₁ + r₂) h R / w`.
* `TauCeti.LFunctions.analyticAt_dedekindZetaC`,
  `TauCeti.LFunctions.analyticAt_dedekindZetaC_iff`,
  `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_one`,
  `TauCeti.LFunctions.dedekindZetaC_one`,
  `TauCeti.LFunctions.tendsto_sub_one_mul_dedekindZetaC`: meromorphic continuation of
  `dedekindZetaC K`, analytic away from its simple pole at `s = 1` with residue
  `dedekindZeta_residue K`.
* `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_zero`,
  `TauCeti.LFunctions.tendsto_dedekindZetaC_div_pow_rank_zero`,
  `TauCeti.LFunctions.dedekindZetaC_zero_of_rank_eq_zero`,
  `TauCeti.LFunctions.dedekindZetaC_zero_of_rank_pos`: at `s = 0`, `dedekindZetaC K`
  vanishes to order `Units.rank K` with leading coefficient `-h R / w` (Neukirch VII (5.11)),
  so its value at `0` is `-h / w` in rank zero and `0` in positive rank.
* `TauCeti.LFunctions.completedDedekindZeta_rat_eq_toMeromorphicNFOn`,
  `TauCeti.LFunctions.completedDedekindZeta_rat_eq`: comparison over `ℚ` with
  `completedRiemannZeta`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, (5.5)–(5.11).
-/

public section
noncomputable section

open Complex ComplexConjugate Filter NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.Units Set TauCeti.GlobalNumberFields
  TauCeti.NumberField.mixedEmbedding
open scoped nonZeroDivisors Pointwise Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The completed Dedekind zeta function -/

variable (K) in
/-- **The completed Dedekind zeta function** of a number field `K`: the canonical meromorphic
continuation from `Re s > 1` of `|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`. -/
def completedDedekindZeta : ℂ → ℂ :=
  meromorphicContinuation 1 fun s ↦
    ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
      Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s

variable (K) in
/-- Defining equation of `TauCeti.LFunctions.completedDedekindZeta`. -/
theorem completedDedekindZeta_def :
    completedDedekindZeta K = meromorphicContinuation 1 (fun s ↦
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s) := (rfl)

variable (K) in
/-- The completed Dedekind zeta function is in meromorphic normal form on the plane. -/
theorem meromorphicNFOn_completedDedekindZeta :
    MeromorphicNFOn (completedDedekindZeta K) univ :=
  meromorphicNFOn_meromorphicContinuation _ _

variable (K) in
/-- The completed Dedekind zeta function is meromorphic on `ℂ`. -/
theorem meromorphic_completedDedekindZeta : Meromorphic (completedDedekindZeta K) :=
  meromorphicOn_univ.mp (meromorphicNFOn_completedDedekindZeta K).meromorphicOn

private theorem meromorphic_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Meromorphic fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z :=
  fun z ↦ MeromorphicAt.fun_sum fun c _ ↦ meromorphic_completedPartialZeta (rep c) z

private theorem analyticOnNhd_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    AnalyticOnNhd ℂ (fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z)
      {z | 1 < z.re} := by
  intro z (hz : 1 < z.re)
  have h0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have h1 : z ≠ 1 := by rintro rfl; norm_num at hz
  exact Finset.analyticAt_fun_sum _ fun c _ ↦ analyticAt_completedPartialZeta (rep c) h0 h1

private theorem sum_completedPartialZeta_eqOn
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) :
    EqOn (fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z)
      (fun z ↦ ((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
        Gammaℂ z ^ nrComplexPlaces K * dedekindZeta K z) {z | 1 < z.re} := by
  intro z (hz : 1 < z.re)
  simp_rw [completedPartialZeta_eq_mul_LSeries_rayClassCoeff_one _ hz, hrep, ← Finset.mul_sum,
    sum_LSeries_rayClassCoeff_classGroup hz]

/-- **Decomposition into completed partial zeta functions, as germs.** For any system of ideal-class
representatives `rep`, `completedDedekindZeta K` has the punctured germ of
`∑ c, completedPartialZeta (rep c)` at every point of `ℂ`. -/
private theorem completedDedekindZeta_eventuallyEq_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) (s : ℂ) :
    completedDedekindZeta K =ᶠ[𝓝[≠] s]
      fun z ↦ ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) z := by
  rw [completedDedekindZeta_def]
  exact meromorphicContinuation_eventuallyEq (meromorphic_sum_completedPartialZeta rep)
    (analyticOnNhd_sum_completedPartialZeta rep) (sum_completedPartialZeta_eqOn rep hrep) s

/-- The completed Dedekind zeta function is analytic away from `0` and `1`. -/
theorem analyticAt_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    AnalyticAt ℂ (completedDedekindZeta K) s := by
  have hev := completedDedekindZeta_eventuallyEq_sum_completedPartialZeta
    (ClassGroup.rep K) ClassGroup.mk_rep s
  have ha : AnalyticAt ℂ (fun z ↦ ∑ c : ClassGroup (𝓞 K),
      completedPartialZeta (ClassGroup.rep K c) z) s :=
    Finset.analyticAt_fun_sum _ fun c _ ↦
      analyticAt_completedPartialZeta (ClassGroup.rep K c) h0 h1
  refine (meromorphicNFOn_completedDedekindZeta K
      (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
  rw [meromorphicOrderAt_congr hev]
  exact ha.meromorphicOrderAt_nonneg

/-- Lifting a common normalized residue limit of all `completedPartialZeta I` to
`completedDedekindZeta K`. -/
private theorem tendsto_sub_mul_completedDedekindZeta {s₀ L : ℂ}
    (hL : ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      Tendsto (fun s : ℂ ↦ (s - s₀) * completedPartialZeta I s) (𝓝[≠] s₀) (𝓝 L)) :
    Tendsto (fun s : ℂ ↦ (s - s₀) * completedDedekindZeta K s) (𝓝[≠] s₀)
      (𝓝 ((classNumber K : ℂ) * L)) := by
  have hsum : Tendsto
      (fun s : ℂ ↦ ∑ c : ClassGroup (𝓞 K), (s - s₀) * completedPartialZeta (ClassGroup.rep K c) s)
      (𝓝[≠] s₀) (𝓝 (∑ _c : ClassGroup (𝓞 K), L)) :=
    tendsto_finsetSum _ fun c _ ↦ hL (ClassGroup.rep K c)
  have hval : (∑ _c : ClassGroup (𝓞 K), L) = (classNumber K : ℂ) * L := by
    simp [NumberField.classNumber]
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [completedDedekindZeta_eventuallyEq_sum_completedPartialZeta
    (ClassGroup.rep K) ClassGroup.mk_rep s₀] with s hs
  rw [hs, Finset.mul_sum]

variable (K) in
/-- **Residue of the completed Dedekind zeta function at `s = 0`**:
`s * completedDedekindZeta K s → -(classNumber K * (2 * mellinConstant K))`
as `s → 0`, `s ≠ 0`. -/
theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s : ℂ ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))))) := by
  simpa only [sub_zero, mul_neg] using
    tendsto_sub_mul_completedDedekindZeta (K := K) (s₀ := 0)
      (L := -(2 * mellinConstant K : ℂ)) fun I ↦ by
        simpa only [sub_zero] using tendsto_mul_completedPartialZeta_zero I

variable (K) in
/-- **Residue of the completed Dedekind zeta function at `s = 1`**:
`(s - 1) * completedDedekindZeta K s → classNumber K * (2 * mellinConstant K)` as `s → 1`,
`s ≠ 1`. -/
theorem tendsto_sub_one_mul_completedDedekindZeta :
    Tendsto (fun s : ℂ ↦ (s - 1) * completedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 ((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)))) :=
  tendsto_sub_mul_completedDedekindZeta tendsto_sub_one_mul_completedPartialZeta

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at `s = 0`. -/
theorem meromorphicOrderAt_completedDedekindZeta_zero :
    meromorphicOrderAt (completedDedekindZeta K) 0 = (-1 : ℤ) := by
  have hL : -((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))) ≠ 0 := by
    simp [classNumber_ne_zero, mellinConstant_ne_zero]
  refine (meromorphic_completedDedekindZeta K 0).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    hL ?_
  simpa only [sub_zero, smul_eq_mul] using tendsto_mul_completedDedekindZeta_zero K

variable (K) in
/-- The completed Dedekind zeta function has a simple pole at `s = 1`. -/
theorem meromorphicOrderAt_completedDedekindZeta_one :
    meromorphicOrderAt (completedDedekindZeta K) 1 = (-1 : ℤ) := by
  have hL : (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) ≠ 0 := by
    simp [classNumber_ne_zero, mellinConstant_ne_zero]
  exact (meromorphic_completedDedekindZeta K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul
    hL (by simpa only [smul_eq_mul] using tendsto_sub_one_mul_completedDedekindZeta K)

/-- `completedDedekindZeta K` is analytic at `s` if and only if `s ≠ 0` and `s ≠ 1`. -/
@[simp]
theorem analyticAt_completedDedekindZeta_iff {s : ℂ} :
    AnalyticAt ℂ (completedDedekindZeta K) s ↔ s ≠ 0 ∧ s ≠ 1 := by
  refine ⟨fun han ↦ ⟨?_, ?_⟩, fun ⟨h0, h1⟩ ↦ analyticAt_completedDedekindZeta h0 h1⟩
  · rintro rfl
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedDedekindZeta_zero] at hnonneg
    exact absurd hnonneg (by decide)
  · rintro rfl
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_completedDedekindZeta_one] at hnonneg
    exact absurd hnonneg (by decide)

variable (K) in
/-- As a meromorphic normal form, `completedDedekindZeta K` takes the canonical value `0` at its
pole `s = 0`. -/
@[simp]
theorem completedDedekindZeta_zero : completedDedekindZeta K 0 = 0 :=
  (meromorphicNFOn_completedDedekindZeta K (mem_univ 0)).apply_eq_zero_of_order_ne_zero
    (by simp [meromorphicOrderAt_completedDedekindZeta_zero])

variable (K) in
/-- As a meromorphic normal form, `completedDedekindZeta K` takes the canonical value `0` at its
pole `s = 1`. -/
@[simp]
theorem completedDedekindZeta_one : completedDedekindZeta K 1 = 0 :=
  (meromorphicNFOn_completedDedekindZeta K (mem_univ 1)).apply_eq_zero_of_order_ne_zero
    (by simp [meromorphicOrderAt_completedDedekindZeta_one])

/-- **Decomposition into completed partial zeta functions.** For any system of ideal-class
representatives `rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ` with
`ClassGroup.mk K (rep c) = c`, the completed Dedekind zeta function is the sum of the completed
partial zeta functions at every `s : ℂ`. -/
theorem completedDedekindZeta_eq_sum_completedPartialZeta
    (rep : ClassGroup (𝓞 K) → (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hrep : ∀ c, ClassGroup.mk K (rep c) = c) (s : ℂ) :
    completedDedekindZeta K s = ∑ c : ClassGroup (𝓞 K), completedPartialZeta (rep c) s := by
  by_cases h0 : s = 0
  · subst h0; simp
  by_cases h1 : s = 1
  · subst h1; simp
  rw [completedDedekindZeta_def]
  exact meromorphicContinuation_apply (meromorphic_sum_completedPartialZeta rep)
    (analyticOnNhd_sum_completedPartialZeta rep) (sum_completedPartialZeta_eqOn rep hrep)
    (Finset.analyticAt_fun_sum _ fun c _ ↦ analyticAt_completedPartialZeta (rep c) h0 h1)

/-- On `Re s > 1`, `completedDedekindZeta K` equals
`|d_K|^(s/2) Γ_ℝ(s)^r₁ Γ_ℂ(s)^r₂ ζ_K(s)`. -/
theorem completedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    completedDedekindZeta K s =
      ((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
        Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s := by
  rw [completedDedekindZeta_eq_sum_completedPartialZeta (ClassGroup.rep K) ClassGroup.mk_rep s]
  exact sum_completedPartialZeta_eqOn (ClassGroup.rep K) ClassGroup.mk_rep hs

variable (K) in
/-- **Functional equation of the completed Dedekind zeta function** (Neukirch VII (5.10)):
`completedDedekindZeta K (1 - s) = completedDedekindZeta K s` for all `s : ℂ`. -/
theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  rw [completedDedekindZeta_eq_sum_completedPartialZeta
      (ClassGroup.rep K) ClassGroup.mk_rep (1 - s),
    completedDedekindZeta_eq_sum_completedPartialZeta (ClassGroup.rep K) ClassGroup.mk_rep s]
  simp_rw [completedPartialZeta_one_sub]
  let δ : ClassGroup (𝓞 K) :=
    ClassGroup.mk K (FractionalIdeal.dualEquiv ℤ ℚ (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))
  let e : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
    (Equiv.inv (ClassGroup (𝓞 K))).trans (Equiv.mulLeft δ)
  have he (c : ClassGroup (𝓞 K)) : e c = δ * c⁻¹ := by
    simp [e]
  refine Fintype.sum_equiv e _ _ fun c ↦ ?_
  refine congrFun (completedPartialZeta_congr_class ?_) s
  rw [he, FractionalIdeal.dualEquiv_eq_mul_inv, map_mul, map_inv,
    ClassGroup.mk_rep, ClassGroup.mk_rep, mul_comm]

variable (K) in
/-- **Functional equation of the completed Dedekind zeta function, as germs:**
`completedDedekindZeta K (1 - z) = completedDedekindZeta K z` on a punctured neighborhood of
every `s : ℂ` (including the poles `0` and `1`). -/
theorem completedDedekindZeta_one_sub_eventuallyEq (s : ℂ) :
    (fun z ↦ completedDedekindZeta K (1 - z)) =ᶠ[𝓝[≠] s] completedDedekindZeta K :=
  Eventually.of_forall (completedDedekindZeta_one_sub K)

variable (K) in
/-- Reflection symmetry of the completed Dedekind zeta function across the real axis. -/
@[simp]
theorem completedDedekindZeta_conj (s : ℂ) :
    completedDedekindZeta K (conj s) = conj (completedDedekindZeta K s) := by
  rw [completedDedekindZeta_eq_sum_completedPartialZeta
      (ClassGroup.rep K) ClassGroup.mk_rep (conj s),
    completedDedekindZeta_eq_sum_completedPartialZeta (ClassGroup.rep K) ClassGroup.mk_rep s,
    map_sum]
  exact Finset.sum_congr rfl fun c _ ↦ completedPartialZeta_conj (ClassGroup.rep K c) s

variable (K) in
/-- The residue of `completedDedekindZeta K` at `s = 1` matches the completed form of
`dedekindZeta_residue K`:
`|d_K|^(1/2) Γ_ℝ(1)^r₁ Γ_ℂ(1)^r₂ ρ_K = classNumber K * (2 * mellinConstant K)`. -/
theorem completedDedekindZeta_residue_eq :
    ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) * Gammaℝ 1 ^ nrRealPlaces K *
        Gammaℂ 1 ^ nrComplexPlaces K * (dedekindZeta_residue K : ℂ) =
      (classNumber K : ℂ) * (2 * (mellinConstant K : ℂ)) := by
  have hdiscr_pos : (0 : ℝ) < (|discr K| : ℤ) :=
    Int.cast_pos.mpr (abs_pos.mpr (discr_ne_zero K))
  have hsqrt :
      ((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) = (Real.sqrt |(discr K : ℝ)| : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (abs_nonneg _),
      ← Int.cast_abs (R := ℝ) (a := discr K)]
    simp only [Complex.ofReal_intCast, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hsqrt_ne : Real.sqrt |(discr K : ℝ)| ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hdiscr_pos)).ne'
  rw [hsqrt, Gammaℝ_one, one_pow, mul_one, Gammaℂ_one, dedekindZeta_residue_def]
  have hreal :
      Real.sqrt |(discr K : ℝ)| * (Real.pi : ℝ)⁻¹ ^ nrComplexPlaces K *
          ((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * regulator K * classNumber K) /
            (torsionOrder K * Real.sqrt |(discr K : ℝ)|)) =
        (classNumber K : ℝ) * (2 * mellinConstant K) := by
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hpipow : (1 / Real.pi) ^ nrComplexPlaces K * Real.pi ^ nrComplexPlaces K = 1 := by
      rw [← mul_pow, one_div_mul_cancel hpi, one_pow]
    rw [two_mul_mellinConstant]
    calc
      Real.sqrt |(discr K : ℝ)| * (Real.pi : ℝ)⁻¹ ^ nrComplexPlaces K *
          ((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * regulator K * classNumber K) /
            (torsionOrder K * Real.sqrt |(discr K : ℝ)|))
          = (Real.sqrt |(discr K : ℝ)| / Real.sqrt |(discr K : ℝ)|) *
              ((1 / Real.pi) ^ nrComplexPlaces K * Real.pi ^ nrComplexPlaces K) *
              ((classNumber K : ℝ) *
                (2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K * regulator K / torsionOrder K)) := by
            rw [mul_pow, one_div]; ring
      _ = (classNumber K : ℝ) *
            (2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K * regulator K / torsionOrder K) := by
            rw [div_self hsqrt_ne, hpipow, one_mul, one_mul]
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_one, one_div] using
    congrArg (fun x : ℝ ↦ (x : ℂ)) hreal

/-! ### Continuation, residue, and leading term at `0` of `dedekindZetaC` -/

/-- The inverse completion factor `|d_K|^(-z/2) Γ_ℝ(z)^(-r₁) Γ_ℂ(z)^(-r₂)`. -/
private def invCompletionFactor (K : Type*) [Field K] [NumberField K] (z : ℂ) : ℂ :=
  ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
    (Gammaℂ z)⁻¹ ^ nrComplexPlaces K

private theorem analyticAt_discr_inv_cpow (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) s := by
  have hmem : ((|discr K| : ℤ) : ℂ) ∈ slitPlane :=
    Or.inl (by norm_cast; exact abs_pos.mpr (discr_ne_zero K))
  exact analyticAt_const.cpow (by fun_prop) hmem

private theorem analyticAt_invCompletionFactor (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    AnalyticAt ℂ (invCompletionFactor K) s :=
  ((analyticAt_discr_inv_cpow K s).mul
    ((differentiable_Gammaℝ_inv.analyticAt s).pow _)).mul
    ((differentiable_Gammaℂ_inv.analyticAt s).pow _)

/-- On `Re z > 0`, multiplying by `invCompletionFactor K z` cancels the completion factor
`|d_K|^(z/2) Γ_ℝ(z)^r₁ Γ_ℂ(z)^r₂`. -/
private theorem invCompletionFactor_mul_cancel (K : Type*) [Field K] [NumberField K]
    {z : ℂ} (hz : 0 < z.re) (w : ℂ) :
    invCompletionFactor K z *
        (((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
          Gammaℂ z ^ nrComplexPlaces K * w) = w := by
  have hdiscr_ne : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mpr (discr_ne_zero K)).ne'
  have hGℝ : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos hz
  have hGℂ : Gammaℂ z ≠ 0 := Gammaℂ_ne_zero_of_re_pos hz
  dsimp only [invCompletionFactor]
  calc
    ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K *
        (((|discr K| : ℤ) : ℂ) ^ (z / 2) * Gammaℝ z ^ nrRealPlaces K *
          Gammaℂ z ^ nrComplexPlaces K * w)
        = (((|discr K| : ℤ) : ℂ) ^ (-z / 2) * ((|discr K| : ℤ) : ℂ) ^ (z / 2)) *
            ((Gammaℝ z)⁻¹ ^ nrRealPlaces K * Gammaℝ z ^ nrRealPlaces K) *
            ((Gammaℂ z)⁻¹ ^ nrComplexPlaces K * Gammaℂ z ^ nrComplexPlaces K) * w := by ring
    _ = ((|discr K| : ℤ) : ℂ) ^ (-z / 2 + z / 2) *
            ((Gammaℝ z)⁻¹ * Gammaℝ z) ^ nrRealPlaces K *
            ((Gammaℂ z)⁻¹ * Gammaℂ z) ^ nrComplexPlaces K * w := by
          rw [← Complex.cpow_add _ _ hdiscr_ne, ← mul_pow, ← mul_pow]
    _ = w := by
          have hadd : -z / 2 + z / 2 = 0 := by ring
          simp [hadd, inv_mul_cancel₀ hGℝ, inv_mul_cancel₀ hGℂ]

private theorem meromorphicOrderAt_invCompletionFactor_zero (K : Type*) [Field K] [NumberField K] :
    meromorphicOrderAt (invCompletionFactor K) 0 =
      (nrRealPlaces K : ℤ) + (nrComplexPlaces K : ℤ) := by
  have hdiscr_ord :
      meromorphicOrderAt (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) 0 = 0 := by
    have ha := analyticAt_discr_inv_cpow K 0
    rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr (by simp)]
    rfl
  have hGℝ_an : AnalyticAt ℂ (fun z : ℂ ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 :=
    (differentiable_Gammaℝ_inv.analyticAt 0).pow _
  have hGℂ_an : AnalyticAt ℂ (fun z : ℂ ↦ (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 :=
    (differentiable_Gammaℂ_inv.analyticAt 0).pow _
  have hGℝ_ord : meromorphicOrderAt (fun z : ℂ ↦ (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 =
      (nrRealPlaces K : ℤ) := by
    rw [fun_meromorphicOrderAt_pow (differentiable_Gammaℝ_inv.analyticAt 0).meromorphicAt,
      fun_meromorphicOrderAt_inv, (meromorphicOrderAt_Gammaℝ_eq_neg_one_iff 0).mpr ⟨0, by simp⟩]
    simp
  have hGℂ_ord : meromorphicOrderAt (fun z : ℂ ↦ (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) 0 =
      (nrComplexPlaces K : ℤ) := by
    rw [fun_meromorphicOrderAt_pow (differentiable_Gammaℂ_inv.analyticAt 0).meromorphicAt,
      fun_meromorphicOrderAt_inv, (meromorphicOrderAt_Gammaℂ_eq_neg_one_iff 0).mpr ⟨0, by simp⟩]
    simp
  have hprod1 : AnalyticAt ℂ (fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K) 0 :=
    (analyticAt_discr_inv_cpow K 0).mul hGℝ_an
  unfold invCompletionFactor
  rw [fun_meromorphicOrderAt_mul hprod1.meromorphicAt hGℂ_an.meromorphicAt,
    fun_meromorphicOrderAt_mul (analyticAt_discr_inv_cpow K 0).meromorphicAt hGℝ_an.meromorphicAt,
    hdiscr_ord, hGℝ_ord, hGℂ_ord, zero_add]

private theorem meromorphicOrderAt_invCompletionFactor_one (K : Type*) [Field K] [NumberField K] :
    meromorphicOrderAt (invCompletionFactor K) 1 = 0 := by
  have hdiscr_ne : ((|discr K| : ℤ) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mpr (discr_ne_zero K)).ne'
  have hne : invCompletionFactor K 1 ≠ 0 := by
    simp [invCompletionFactor, Complex.cpow_eq_zero_iff, hdiscr_ne, Real.pi_ne_zero]
  have ha := analyticAt_invCompletionFactor K 1
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hne]
  rfl

private theorem meromorphic_invCompletionFactor_mul_completedDedekindZeta
    (K : Type*) [Field K] [NumberField K] :
    Meromorphic fun z ↦ invCompletionFactor K z * completedDedekindZeta K z :=
  fun z ↦ (analyticAt_invCompletionFactor K z).meromorphicAt.mul
    (meromorphic_completedDedekindZeta K z)

private theorem analyticOnNhd_invCompletionFactor_mul_completedDedekindZeta
    (K : Type*) [Field K] [NumberField K] :
    AnalyticOnNhd ℂ (fun z ↦ invCompletionFactor K z * completedDedekindZeta K z)
      {z | 1 < z.re} :=
  fun z hz ↦ (analyticAt_invCompletionFactor K z).mul
    (analyticAt_completedDedekindZeta (by rintro rfl; norm_num at hz)
      (by rintro rfl; norm_num at hz))

private theorem invCompletionFactor_mul_completedDedekindZeta_eqOn
    (K : Type*) [Field K] [NumberField K] :
    EqOn (fun z ↦ invCompletionFactor K z * completedDedekindZeta K z)
      (dedekindZeta K) {z | 1 < z.re} := by
  intro z (hz : 1 < z.re)
  dsimp only
  rw [completedDedekindZeta_eq hz]
  exact invCompletionFactor_mul_cancel K (by linarith) _

private theorem dedekindZetaC_eventuallyEq_invCompletionFactor_mul (K : Type*)
    [Field K] [NumberField K] (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s] fun z ↦ invCompletionFactor K z * completedDedekindZeta K z := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_eventuallyEq
    (meromorphic_invCompletionFactor_mul_completedDedekindZeta K)
    (analyticOnNhd_invCompletionFactor_mul_completedDedekindZeta K)
    (invCompletionFactor_mul_completedDedekindZeta_eqOn K) s

variable (K) in
/-- **Relation between `dedekindZetaC` and `completedDedekindZeta`, as germs.** At every complex
number `s` (including `0` and `1`), `dedekindZetaC K` has the punctured germ of
`|d_K|^(-z/2) Γ_ℝ(z)^(-r₁) Γ_ℂ(z)^(-r₂) completedDedekindZeta K z`. -/
theorem dedekindZetaC_eventuallyEq_completedDedekindZeta_mul (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s] fun z ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) * (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K z := by
  simpa only [invCompletionFactor] using dedekindZetaC_eventuallyEq_invCompletionFactor_mul K s

private theorem meromorphicOrderAt_dedekindZetaC_eq_add (K : Type*) [Field K] [NumberField K]
    (s : ℂ) :
    meromorphicOrderAt (dedekindZetaC K) s =
      meromorphicOrderAt (invCompletionFactor K) s +
        meromorphicOrderAt (completedDedekindZeta K) s := by
  rw [meromorphicOrderAt_congr (dedekindZetaC_eventuallyEq_invCompletionFactor_mul K s)]
  exact fun_meromorphicOrderAt_mul (analyticAt_invCompletionFactor K s).meromorphicAt
    (meromorphic_completedDedekindZeta K s)

variable (K) in
/-- **Order of vanishing of `dedekindZetaC K` at `s = 0`** (Neukirch VII (5.11)):
`meromorphicOrderAt (dedekindZetaC K) 0 = Units.rank K = r₁ + r₂ - 1`. -/
theorem meromorphicOrderAt_dedekindZetaC_zero :
    meromorphicOrderAt (dedekindZetaC K) 0 = (Units.rank K : ℤ) := by
  have hrank := Units.rank_add_one K
  rw [meromorphicOrderAt_dedekindZetaC_eq_add, meromorphicOrderAt_invCompletionFactor_zero,
    meromorphicOrderAt_completedDedekindZeta_zero]
  norm_cast
  omega

variable (K) in
/-- **Simple pole of `dedekindZetaC K` at `s = 1`**:
`meromorphicOrderAt (dedekindZetaC K) 1 = -1`. -/
theorem meromorphicOrderAt_dedekindZetaC_one :
    meromorphicOrderAt (dedekindZetaC K) 1 = (-1 : ℤ) := by
  rw [meromorphicOrderAt_dedekindZetaC_eq_add, meromorphicOrderAt_invCompletionFactor_one,
    meromorphicOrderAt_completedDedekindZeta_one, zero_add]

variable (K) in
/-- As a meromorphic normal form, `dedekindZetaC K` takes the canonical value `0` at its pole
`s = 1`. -/
@[simp]
theorem dedekindZetaC_one : dedekindZetaC K 1 = 0 :=
  (meromorphicNFOn_dedekindZetaC K (mem_univ 1)).apply_eq_zero_of_order_ne_zero
    (by simp [meromorphicOrderAt_dedekindZetaC_one])

/-- **Holomorphy of `dedekindZetaC K` away from `s = 1`** (including at `s = 0`). -/
theorem analyticAt_dedekindZetaC {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (dedekindZetaC K) s := by
  rcases eq_or_ne s 0 with rfl | h0
  · refine (meromorphicNFOn_dedekindZetaC K
        (mem_univ (0 : ℂ))).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_dedekindZetaC_zero K]
    exact WithTop.coe_nonneg.mpr (Nat.cast_nonneg _)
  · refine (meromorphicNFOn_dedekindZetaC K
        (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_congr (dedekindZetaC_eventuallyEq_invCompletionFactor_mul K s)]
    exact ((analyticAt_invCompletionFactor K s).mul
      (analyticAt_completedDedekindZeta h0 hs)).meromorphicOrderAt_nonneg

/-- `dedekindZetaC K` is analytic at `s` if and only if `s ≠ 1`. -/
@[simp]
theorem analyticAt_dedekindZetaC_iff {s : ℂ} :
    AnalyticAt ℂ (dedekindZetaC K) s ↔ s ≠ 1 := by
  refine ⟨fun han h1 ↦ ?_, analyticAt_dedekindZetaC⟩
  subst h1
  have hnonneg := han.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_dedekindZetaC_one] at hnonneg
  exact absurd hnonneg (by decide)

private theorem dedekindZetaC_eq_invCompletionFactor_mul (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    dedekindZetaC K s = invCompletionFactor K s * completedDedekindZeta K s := by
  rw [dedekindZetaC_def]
  exact meromorphicContinuation_apply
    (meromorphic_invCompletionFactor_mul_completedDedekindZeta K)
    (analyticOnNhd_invCompletionFactor_mul_completedDedekindZeta K)
    (invCompletionFactor_mul_completedDedekindZeta_eqOn K)
    ((analyticAt_invCompletionFactor K s).mul (analyticAt_completedDedekindZeta h0 h1))

/-- Away from `0` and `1` (including at all negative integers), `dedekindZetaC K s` equals
`|d_K|^(-s/2) Γ_ℝ(s)^(-r₁) Γ_ℂ(s)^(-r₂) completedDedekindZeta K s`. -/
theorem dedekindZetaC_eq_completedDedekindZeta_mul {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    dedekindZetaC K s =
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s := by
  simpa only [invCompletionFactor] using dedekindZetaC_eq_invCompletionFactor_mul K h0 h1

/-- On `Re s > 1`, `dedekindZetaC K` agrees with Mathlib's `NumberField.dedekindZeta K`. -/
theorem dedekindZetaC_eq {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaC K s = dedekindZeta K s := by
  rw [dedekindZetaC_def]
  exact (meromorphicContinuation_apply
    (meromorphic_invCompletionFactor_mul_completedDedekindZeta K)
    (analyticOnNhd_invCompletionFactor_mul_completedDedekindZeta K)
    (invCompletionFactor_mul_completedDedekindZeta_eqOn K)
    (analyticOnNhd_invCompletionFactor_mul_completedDedekindZeta K s hs)).trans
    (invCompletionFactor_mul_completedDedekindZeta_eqOn K hs)

variable (K) in
/-- **Analytic class number formula for `dedekindZetaC K`**:
`(s - 1) * dedekindZetaC K s → dedekindZeta_residue K` as `s → 1`, `s ≠ 1`. -/
theorem tendsto_sub_one_mul_dedekindZetaC :
    Tendsto (fun s : ℂ ↦ (s - 1) * dedekindZetaC K s) (𝓝[≠] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) := by
  have h1 : Tendsto (invCompletionFactor K) (𝓝[≠] 1) (𝓝 (invCompletionFactor K 1)) :=
    (analyticAt_invCompletionFactor K 1).continuousAt.mono_left nhdsWithin_le_nhds
  have hmul := h1.mul (tendsto_sub_one_mul_completedDedekindZeta K)
  have hlim :
      invCompletionFactor K 1 * ((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))) =
        (dedekindZeta_residue K : ℂ) := by
    rw [← completedDedekindZeta_residue_eq K]
    exact invCompletionFactor_mul_cancel K (by simp) _
  rw [hlim] at hmul
  refine hmul.congr' ?_
  filter_upwards [dedekindZetaC_eventuallyEq_invCompletionFactor_mul K 1] with z hz
  rw [hz]
  ring

private theorem dedekindZetaC_zero_limit_coeff (K : Type*) [Field K] [NumberField K] :
    -((classNumber K : ℂ) * (2 * (mellinConstant K : ℂ))) * 1 *
        ((2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K) =
      (-((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ) := by
  have h2cancel :
      (2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K : ℝ) *
        ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (2 : ℝ)⁻¹ ^ nrComplexPlaces K) = 1 := by
    calc
      (2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K : ℝ) *
          ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (2 : ℝ)⁻¹ ^ nrComplexPlaces K)
          = ((2 : ℝ) ^ nrRealPlaces K * (2 : ℝ)⁻¹ ^ nrRealPlaces K) *
            ((2 : ℝ) ^ nrComplexPlaces K * (2 : ℝ)⁻¹ ^ nrComplexPlaces K) := by ring
      _ = (2 * (2 : ℝ)⁻¹) ^ nrRealPlaces K * (2 * (2 : ℝ)⁻¹) ^ nrComplexPlaces K := by
            rw [← mul_pow, ← mul_pow]
      _ = 1 := by simp
  have hreal :
      -((classNumber K : ℝ) * (2 * mellinConstant K)) * 1 *
          ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (2 : ℝ)⁻¹ ^ nrComplexPlaces K) =
        -((classNumber K : ℝ) * regulator K / torsionOrder K) := by
    rw [two_mul_mellinConstant]
    calc
      -((classNumber K : ℝ) *
          (2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K * regulator K / torsionOrder K)) * 1 *
          ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (2 : ℝ)⁻¹ ^ nrComplexPlaces K)
          = -((2 ^ nrRealPlaces K * 2 ^ nrComplexPlaces K : ℝ) *
              ((2 : ℝ)⁻¹ ^ nrRealPlaces K * (2 : ℝ)⁻¹ ^ nrComplexPlaces K) *
              ((classNumber K : ℝ) * regulator K / torsionOrder K)) := by ring
      _ = -((classNumber K : ℝ) * regulator K / torsionOrder K) := by rw [h2cancel, one_mul]
  simpa only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_one] using
    congrArg (fun x : ℝ ↦ (x : ℂ)) hreal

private theorem dedekindZetaC_zero_factor_identity {z : ℂ} (hz0 : z ≠ 0)
    (hz : dedekindZetaC K z = invCompletionFactor K z * completedDedekindZeta K z) :
    z * completedDedekindZeta K z * ((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
        ((z * Gammaℝ z)⁻¹ ^ nrRealPlaces K * (z * Gammaℂ z)⁻¹ ^ nrComplexPlaces K) =
      dedekindZetaC K z / z ^ Units.rank K := by
  have hmul : (z * Gammaℝ z)⁻¹ ^ nrRealPlaces K * (z * Gammaℂ z)⁻¹ ^ nrComplexPlaces K =
      z⁻¹ ^ (Units.rank K + 1) *
        ((Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K) := by
    simp_rw [mul_inv, mul_pow]
    rw [Units.rank_add_one K, pow_add]
    ring
  rw [hz, hmul, pow_succ', inv_pow]
  have hzinv : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  dsimp only [invCompletionFactor]
  calc
    z * completedDedekindZeta K z * ((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
        (z⁻¹ * (z ^ Units.rank K)⁻¹ *
          ((Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K))
        = (z * z⁻¹) * (((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
            (Gammaℝ z)⁻¹ ^ nrRealPlaces K *
            (Gammaℂ z)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K z *
            (z ^ Units.rank K)⁻¹) := by ring
    _ = _ := by rw [hzinv, one_mul, ← div_eq_mul_inv]

variable (K) in
/-- **Leading term of `dedekindZetaC K` at `s = 0`** (Neukirch VII (5.11)):
`dedekindZetaC K s / s ^ Units.rank K → -(classNumber K * regulator K / torsionOrder K)`
as `s → 0`, `s ≠ 0`. -/
theorem tendsto_dedekindZetaC_div_pow_rank_zero :
    Tendsto (fun s : ℂ ↦ dedekindZetaC K s / s ^ Units.rank K) (𝓝[≠] 0)
      (𝓝 (-((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ)) := by
  have hdiscr :
      Tendsto (fun z : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-z / 2)) (𝓝[≠] 0) (𝓝 1) := by
    simpa using (analyticAt_discr_inv_cpow K 0).continuousAt.mono_left nhdsWithin_le_nhds
  have hGℝ : Tendsto (fun z : ℂ ↦ (z * Gammaℝ z)⁻¹ ^ nrRealPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrRealPlaces K)) :=
    (Gammaℝ_residue_zero.inv₀ two_ne_zero).pow _
  have hGℂ : Tendsto (fun z : ℂ ↦ (z * Gammaℂ z)⁻¹ ^ nrComplexPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrComplexPlaces K)) :=
    (Gammaℂ_residue_zero.inv₀ two_ne_zero).pow _
  have hprod :=
    ((tendsto_mul_completedDedekindZeta_zero K).mul hdiscr).mul (hGℝ.mul hGℂ)
  rw [dedekindZetaC_zero_limit_coeff K] at hprod
  refine hprod.congr' ?_
  filter_upwards [dedekindZetaC_eventuallyEq_invCompletionFactor_mul K 0, self_mem_nhdsWithin]
    with z hz (hz0 : z ≠ 0)
  exact dedekindZetaC_zero_factor_identity hz0 hz

variable (K) in
/-- **Value of `dedekindZetaC K` at `s = 0` in unit rank zero** (such as `ℚ` and imaginary
quadratic fields): `ζ_K(0) = -h / w`. -/
theorem dedekindZetaC_zero_of_rank_eq_zero (hr : Units.rank K = 0) :
    dedekindZetaC K 0 = (-((classNumber K : ℝ) / torsionOrder K : ℝ) : ℂ) := by
  have hlim : Tendsto (dedekindZetaC K) (𝓝[≠] 0)
      (𝓝 (-((classNumber K : ℝ) / torsionOrder K : ℝ) : ℂ)) := by
    simpa [hr, Units.regulator_eq_one_of_rank_eq_zero K hr] using
      tendsto_dedekindZetaC_div_pow_rank_zero K
  have hcont : Tendsto (dedekindZetaC K) (𝓝[≠] 0) (𝓝 (dedekindZetaC K 0)) :=
    (analyticAt_dedekindZetaC (K := K) zero_ne_one).continuousAt.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hcont hlim

variable (K) in
/-- **Value of `dedekindZetaC K` at `s = 0` in positive unit rank**: `ζ_K(0) = 0`. -/
theorem dedekindZetaC_zero_of_rank_pos (hr : 0 < Units.rank K) :
    dedekindZetaC K 0 = 0 :=
  (meromorphicNFOn_dedekindZetaC K (mem_univ 0)).apply_eq_zero_of_order_ne_zero (by
    rw [meromorphicOrderAt_dedekindZetaC_zero]
    exact_mod_cast hr.ne')

/-! ### Comparison over `ℚ` with the Riemann zeta function -/

/-- Over `ℚ`, `completedDedekindZeta ℚ` is the meromorphic normal form of
`completedRiemannZeta`. -/
theorem completedDedekindZeta_rat_eq_toMeromorphicNFOn :
    completedDedekindZeta ℚ = toMeromorphicNFOn completedRiemannZeta univ := by
  refine eq_of_meromorphicNFOn_of_eqOn_halfPlane (meromorphicNFOn_completedDedekindZeta ℚ)
    (meromorphicNFOn_toMeromorphicNFOn _ _) fun s (hs : 1 < s.re) ↦ ?_
  have h0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hGℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [toMeromorphicNFOn_apply_of_analyticAt meromorphic_completedRiemannZeta
      (analyticAt_completedRiemannZeta h0 h1),
    completedDedekindZeta_eq hs, discr_rat,
    nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
    nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
    dedekindZeta_rat_eq_riemannZeta hs, riemannZeta_def_of_ne_zero h0]
  simp [field]

/-- Over `ℚ`, `completedDedekindZeta ℚ` agrees with Mathlib's `completedRiemannZeta` away from
its poles `0` and `1`. -/
theorem completedDedekindZeta_rat_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedDedekindZeta ℚ s = completedRiemannZeta s := by
  rw [completedDedekindZeta_rat_eq_toMeromorphicNFOn]
  exact toMeromorphicNFOn_apply_of_analyticAt meromorphic_completedRiemannZeta
    (analyticAt_completedRiemannZeta h0 h1)

end TauCeti.LFunctions
