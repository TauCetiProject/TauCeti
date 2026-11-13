/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Bases
import TauCeti.Analysis.InnerProductSpace.ExtremalRpow
import TauCeti.Analysis.Normed.Module.RCLike.Rpow
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.StronglyMeasurable.SpanningSets
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Norming `Lᵖ` functions by test functions

For Hölder conjugate exponents `1 / q + 1 / q' = 1`, the `L^q` norm of a function `h` is the
supremum of the pairings `|∫ h g|` over simple functions `g` of `L^{q'}` norm at most one. This
file proves the half of that duality which is used to bound a norm: if
`‖∫ h g‖ ≤ C ‖g‖_{q'}` for every simple `g ∈ L^{q'}`, then `‖h‖_q ≤ C`.

For `q < ∞` this holds for every `h ∈ L^q`, on any measure space. The test function is the
extremal one `conj g * |g| ^ (q - 2)` of a simple approximation `g` of `h`. For `q = ∞` it needs the
measure to be σ-finite (on a measure with an atom of infinite measure every integrable `g`
vanishes on the atom), and it reduces to the case `q = 1` on a set of finite positive measure
where `‖h‖` is close to its essential supremum.

Testing against simple functions only, rather than against all of `L^{q'}`, is what makes the
statement usable when the pairings can only be computed on simple functions, as in the
Riesz–Thorin theorem. Together with Hölder's inequality, the duality bound shows that the
integral pairing `g ↦ (f ↦ ∫ g f dμ)` is a linear isometry from `L^q(μ)` to the continuous dual
of `L^q'(μ)` on a σ-finite measure space.

For functions with values in an inner product space, paired by `∫ ⟪h, g⟫`, the file also proves
a version for `q < ∞` that does not assume `h ∈ L^q` in advance: the test functions are bounded
and vanish off a set of finite measure, and the extremal function `|h| ^ (q - 2) h` is truncated
where `h` is large and outside a spanning set of a σ-finite measure. This is the form needed to
prove that an operator defined on `L²` maps `L² ∩ Lᵖ` into `L^q` by duality. For `h ∈ L²` and
every `1 ≤ q ≤ ∞`, the `L^q` norm of `h` is then the supremum of the real parts of the `L²`
pairings `⟪h, g⟫` over the `g ∈ L²` in the unit ball of `L^{q'}`, the form used to norm mixed
norms `L^p_t L^q_x`.

The integral Hölder bounds apply to arbitrary functions, using the convention that `eLpNorm`
is `∞` outside the almost everywhere strongly measurable functions.

## Main declarations

* `TauCeti.enorm_integral_mul_le`: Hölder's inequality `‖∫ u v‖ ≤ ‖u‖_p ‖v‖_q` for an integral.
* `MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top`: the duality bound
  for `q < ∞`.
* `MeasureTheory.AEStronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le`: the duality
  bound for `q = ∞` on a σ-finite measure space, without assuming `h ∈ L^∞` in advance.
* `MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le`: the duality bound for every
  `1 ≤ q ≤ ∞` on a σ-finite measure space.
* `MeasureTheory.Lp.enorm_integral_mul_le_of_apply_eq`: a continuous linear functional on
  `L^q'` that is integration against `h` satisfies the hypothesis of these duality bounds.
* `MeasureTheory.Lp.toDual`: on a σ-finite measure space, the integral pairing is a linear
  isometry `L^q(μ) → L^q'(μ)*`.
* `MeasureTheory.Lp.toDual_indicatorConstLp`: the value of the pairing at an indicator function.
* `TauCeti.enorm_integral_inner_le`: Hölder's inequality `‖∫ ⟪u, v⟫‖ ≤ ‖u‖_p ‖v‖_q`.
* `MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`: the duality
  bound for `q < ∞` for inner product space valued functions, against bounded test functions of
  finite-measure support, without assuming `h ∈ L^q`.
* `MeasureTheory.Lp.exists_eLpNorm_le_one_and_lt_re_inner`: for `1 ≤ q ≤ ∞` on a σ-finite
  measure space, the `L^q` norm of `h ∈ L²`, finite or not, is the supremum of `re ⟪h, g⟫` over the
  `g ∈ L²` in the unit ball of `L^{q'}`.
* `TopologicalSpace.IsSeparable.exists_seq_eLpNorm_eq_iSup_ofReal_re_inner`: a countable family
  of such `g` norms every element of a separable subset of `L²` in `L^q`.

## References

* G. B. Folland, *Real Analysis*, second edition, Theorem 6.14.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

namespace TauCeti

variable {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- **Hölder's inequality** for the integral of a product: `‖∫ u v‖ ≤ ‖u‖_p ‖v‖_q` for Hölder
conjugate exponents `p` and `q`. -/
theorem enorm_integral_mul_le {𝕜 : Type*} [NonUnitalNormedRing 𝕜] [NormedSpace ℝ 𝕜]
    {p q : ℝ≥0∞} [p.HolderConjugate q] {u v : α → 𝕜} :
    ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm u p μ * eLpNorm v q μ := by
  simpa only [smul_eq_mul] using enorm_integral_smul_le (μ := μ) (p := p) (a := u) (f := v)

/-- **Hölder's inequality** for the integral of an inner product: `‖∫ ⟪u, v⟫‖ ≤ ‖u‖_p ‖v‖_q` for
Hölder conjugate exponents `p` and `q`. -/
theorem enorm_integral_inner_le {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {p q : ℝ≥0∞} [p.HolderConjugate q] {u v : α → H} :
    ‖∫ x, ⟪u x, v x⟫_𝕜 ∂μ‖ₑ ≤ eLpNorm u p μ * eLpNorm v q μ := by
  calc ‖∫ x, ⟪u x, v x⟫_𝕜 ∂μ‖ₑ ≤ eLpNorm (fun x => ⟪u x, v x⟫_𝕜) 1 μ :=
        (eNorm_integral_le_lintegral_eNorm _).trans lintegral_eNorm_le_eLpNorm_one
    _ ≤ eLpNorm u p μ * eLpNorm v q μ := by
        simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm_of_pos (fun a b => ⟪a, b⟫_𝕜) 1
          continuous_inner (ae_of_all _ fun x => by simpa using norm_inner_le_norm (u x) (v x))
          zero_lt_one

end TauCeti

namespace MeasureTheory

variable {α 𝕜 : Type*} {mα : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]

open TauCeti

/-- **Norming by simple functions, `q < ∞`.** Let `q < ∞` and `q'` be Hölder conjugate. If
`h ∈ L^q` satisfies `‖∫ h g‖ ≤ C ‖g‖_{q'}` for every simple function `g ∈ L^{q'}`, then
`‖h‖_q ≤ C`. -/
theorem MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top {q q' : ℝ≥0∞}
    [hqq : q.HolderConjugate q'] {h : α → 𝕜} (hh : MemLp h q μ) (hq : q ≠ ∞) {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α 𝕜, MemLp g q' μ → ‖∫ x, h x * g x ∂μ‖ₑ ≤ C * eLpNorm g q' μ) :
    eLpNorm h q μ ≤ C := by
  have hq1 : 1 ≤ q := hqq.one_le
  have hq0 : q ≠ 0 := hqq.ne_zero
  set r := q.toReal
  have hr1 : 1 ≤ r := by simpa using ENNReal.toReal_mono hq hq1
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (ε : ℝ≥0∞) / 2 ≠ 0 := by simp [hε.ne']
  -- Approximate `h` by a simple function `φ` and test against the extremal function of `φ`.
  obtain ⟨φ, hφ, hφmem⟩ := hh.exists_simpleFunc_eLpNorm_sub_lt hq hε2
  set g : SimpleFunc α 𝕜 := φ.map fun c => ((‖conj c‖ ^ (r - 2) : ℝ) : 𝕜) • conj c with hg_def
  have hg_norm : ∀ x, ‖g x‖ ≤ ‖φ x‖ ^ (r - 1) := fun x => by
    simpa [hg_def] using norm_ofReal_rpow_sub_two_smul_le (𝕜 := 𝕜) r (conj (φ x))
  have hφg : ∀ x, φ x * g x = ((‖φ x‖ ^ r : ℝ) : 𝕜) := fun x => by
    rw [mul_comm]
    simpa [hg_def, RCLike.inner_apply] using
      inner_ofReal_rpow_sub_two_smul (𝕜 := 𝕜) (by linarith : r ≠ 0) (conj (φ x))
  set X := eLpNorm φ q μ
  have hX : X ≠ ∞ := hφmem.eLpNorm_lt_top.ne
  have hgX : eLpNorm g q' μ ≤ X ^ (r - 1) :=
    eLpNorm_le_eLpNorm_rpow_toReal_sub_one hq g.aestronglyMeasurable (ae_of_all _ hg_norm)
  have hgmem : MemLp g q' μ :=
    memLp_iff.2 (hgX.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by linarith) hX))
  -- The pairing of `φ` with its extremal function is `‖φ‖_q ^ q`.
  have hXr : X ^ r ≤ ‖∫ x, φ x * g x ∂μ‖ₑ := by
    simp_rw [hφg]
    exact (hφmem.eLpNorm_rpow_toReal_eq_enorm_integral (𝕜 := 𝕜) hq0 hq).le
  -- Replacing `φ` by `h` costs at most `‖h - φ‖_q ‖g‖_{q'}`.
  have hsplit : ‖∫ x, φ x * g x ∂μ‖ₑ ≤ (C + ε / 2) * X ^ (r - 1) := by
    have hint₁ : Integrable (fun x => h x * g x) μ := hh.integrable_mul hgmem
    have hint₂ : Integrable (fun x => (h x - φ x) * g x) μ :=
      (hh.sub hφmem).integrable_mul hgmem
    have heq : ∫ x, φ x * g x ∂μ = ∫ x, h x * g x ∂μ - ∫ x, (h x - φ x) * g x ∂μ := by
      rw [← integral_sub hint₁ hint₂]
      congr 1 with x
      ring
    calc ‖∫ x, φ x * g x ∂μ‖ₑ
        ≤ ‖∫ x, h x * g x ∂μ‖ₑ + ‖∫ x, (h x - φ x) * g x ∂μ‖ₑ := by
          rw [heq]
          exact eNorm_sub_le
      _ ≤ C * eLpNorm g q' μ + eLpNorm (h - ⇑φ) q μ * eLpNorm g q' μ := by
          gcongr
          · exact hC g hgmem
          · exact enorm_integral_mul_le
      _ ≤ (C + ε / 2) * X ^ (r - 1) := by
          rw [← add_mul]
          gcongr
  -- Hence `‖φ‖_q ≤ C + ε / 2`, and `‖h‖_q ≤ ‖φ‖_q + ε / 2`.
  have hXle : X ≤ C + ε / 2 := ENNReal.le_of_rpow_le_mul_rpow_sub_one hX (hXr.trans hsplit)
  calc eLpNorm h q μ = eLpNorm ((h - ⇑φ) + ⇑φ) q μ := by simp
    _ ≤ eLpNorm (h - ⇑φ) q μ + X := eLpNorm_add_le hq1
    _ ≤ ε / 2 + (C + ε / 2) := by gcongr
    _ = C + ε := by rw [add_comm, add_assoc, ENNReal.add_halves]

/-- **Norming by simple functions, `q = ∞`.** On a σ-finite measure space, let `h` be almost
everywhere strongly measurable. If `h` satisfies
`‖∫ h g‖ ≤ C ‖g‖₁` for every simple function `g ∈ L¹`, then `‖h‖_∞ ≤ C`. In particular `h ∈ L^∞`
as soon as `C < ∞`. -/
theorem AEStronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le [SigmaFinite μ]
    {h : α → 𝕜} (hmeas : AEStronglyMeasurable h μ)
    {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α 𝕜, MemLp g 1 μ → ‖∫ x, h x * g x ∂μ‖ₑ ≤ C * eLpNorm g 1 μ) :
    eLpNorm h ∞ μ ≤ C := by
  by_contra! hlt
  obtain ⟨t, hCt, htN⟩ := exists_between hlt
  set h' := hmeas.mk h
  have hhh' : h =ᵐ[μ] h' := hmeas.ae_eq_mk
  -- The set `{t < ‖h‖}` has positive measure, so by σ-finiteness it contains a set of finite
  -- positive measure; we first cut it down to a set on which `h` is bounded.
  have hE : MeasurableSet {x | t < ‖h' x‖ₑ} :=
    measurableSet_lt measurable_const hmeas.stronglyMeasurable_mk.measurable.eNorm
  have hG (N : ℕ) : MeasurableSet {x | ‖h' x‖ₑ ≤ N} :=
    measurableSet_le hmeas.stronglyMeasurable_mk.measurable.eNorm measurable_const
  have hpos : 0 < μ {x | t < ‖h' x‖ₑ} := by
    refine pos_iff_ne_zero.2 fun hnull => htN.not_ge ?_
    rw [eLpNorm_exponent_top hmeas]
    refine eLpNormEssSup_le_of_ae_eNorm_bound ?_
    filter_upwards [hhh', measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hx'
    rw [hx]
    simpa using hx'
  -- some bounded slice `{t < ‖h' x‖ₑ} ∩ {‖h' x‖ₑ ≤ N}` has positive measure
  have hcover : {x | t < ‖h' x‖ₑ} ⊆ ⋃ N : ℕ, {x | t < ‖h' x‖ₑ} ∩ {x | ‖h' x‖ₑ ≤ N} := fun x hx ↦ by
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (eNorm_ne_top (x := h' x))
    exact Set.mem_iUnion.2 ⟨N, hx, hN.le⟩
  obtain ⟨N, hNpos⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (hpos.trans_le (measure_mono hcover)).ne'
  obtain ⟨F, hFm, hFE, hFpos, hFtop⟩ :=
    Measure.exists_subset_measure_lt_top (hE.inter (hG N)) hNpos
  -- The case `q = 1`, applied to `1_F h`, bounds `∫_F ‖h‖` by `C μ(F)`.
  have hk : MemLp (F.indicator h) 1 μ := by
    rw [memLp_indicator_iff_restrict hFm.nullMeasurableSet, memLp_one_iff_integrable]
    refine Measure.integrableOn_of_bounded (M := N) hFtop.ne hmeas ?_
    filter_upwards [ae_restrict_of_ae hhh', ae_restrict_mem hFm] with x hx hxF
    have h2 : ‖h' x‖ₑ ≤ (N : ℝ≥0∞) := (hFE hxF).2
    rw [hx]
    simpa [← ofReal_norm] using h2
  have hkC : eLpNorm (F.indicator h) 1 μ ≤ C * μ F := by
    refine hk.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top (q' := ∞) ENNReal.one_ne_top
      fun g _ => ?_
    have hgF : eLpNorm (g.restrict F) 1 μ ≤ μ F * eLpNorm g ∞ μ := by
      rw [SimpleFunc.coe_restrict _ hFm,
        eLpNorm_indicator_eq_eLpNorm_restrict hFm.nullMeasurableSet]
      calc eLpNorm g 1 (μ.restrict F)
          ≤ eLpNorm g ∞ (μ.restrict F) * μ.restrict F Set.univ ^ (1 / (1 : ℝ≥0∞).toReal -
              1 / (∞ : ℝ≥0∞).toReal) :=
            eLpNorm_le_eLpNorm_mul_rpow_measure_univ le_top g.aestronglyMeasurable
        _ ≤ eLpNorm g ∞ μ * μ F := by
            simp only [ENNReal.toReal_one, ENNReal.toReal_top, div_zero, sub_zero, div_one,
              ENNReal.rpow_one, Measure.restrict_apply_univ]
            gcongr
            exact Measure.restrict_le_self
        _ = μ F * eLpNorm g ∞ μ := mul_comm _ _
    have hgmem : MemLp (g.restrict F) 1 μ :=
      memLp_iff.2 (hgF.trans_lt (ENNReal.mul_lt_top hFtop (g.memLp_top μ).eLpNorm_lt_top))
    calc ‖∫ x, F.indicator h x * g x ∂μ‖ₑ = ‖∫ x, h x * g.restrict F x ∂μ‖ₑ := by
          congr 2 with x
          rw [SimpleFunc.restrict_apply _ hFm]
          by_cases hx : x ∈ F <;> simp [hx]
      _ ≤ C * eLpNorm (g.restrict F) 1 μ := hC _ hgmem
      _ ≤ C * (μ F * eLpNorm g ∞ μ) := by gcongr
      _ = C * μ F * eLpNorm g ∞ μ := (mul_assoc _ _ _).symm
  -- On the other hand `‖h‖ > t` on `F`, so `t μ(F) ≤ C μ(F)`, contradicting `C < t`.
  have hlow : t * μ F ≤ eLpNorm (F.indicator h) 1 μ := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hFm.nullMeasurableSet,
      eLpNorm_one_eq_lintegral_eNorm hmeas.restrict, ← setLIntegral_const]
    refine setLIntegral_mono_ae hmeas.eNorm.restrict ?_
    filter_upwards [hhh'] with x hx hxF
    rw [hx]
    exact (hFE hxF).1.le
  exact ((ENNReal.mul_le_mul_iff_left hFpos.ne' hFtop.ne).1 (hlow.trans hkC)).not_gt hCt

/-- **Norming by simple functions.** On a σ-finite measure space, let `q` and `q'` be Hölder
conjugate. If `h ∈ L^q` satisfies `‖∫ h g‖ ≤ C ‖g‖_{q'}` for every simple function
`g ∈ L^{q'}`, then `‖h‖_q ≤ C`. -/
theorem MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le [SigmaFinite μ] {q q' : ℝ≥0∞}
    [q.HolderConjugate q'] {h : α → 𝕜} (hh : MemLp h q μ) {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α 𝕜, MemLp g q' μ → ‖∫ x, h x * g x ∂μ‖ₑ ≤ C * eLpNorm g q' μ) :
    eLpNorm h q μ ≤ C := by
  rcases eq_or_ne q ∞ with rfl | hq
  · obtain rfl : q' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q').1 rfl
    exact hh.aestronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le hC
  · exact hh.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top hq hC

/-- If a continuous linear functional `Λ` on `L^q'(μ)` is integration against `h` at the class of
`σ`, then `‖∫ h σ‖ ≤ ‖Λ‖ ‖σ‖_q'`. This is the hypothesis of the norming lemmas above. -/
theorem Lp.enorm_integral_mul_le_of_apply_eq {q' : ℝ≥0∞} [Fact (1 ≤ q')]
    (Λ : StrongDual 𝕜 (Lp 𝕜 q' μ)) {h σ : α → 𝕜} (hσ : MemLp σ q' μ)
    (hΛ : Λ (hσ.toLp σ) = ∫ x, h x * hσ.toLp σ x ∂μ) :
    ‖∫ x, h x * σ x ∂μ‖ₑ ≤ ‖Λ‖ₑ * eLpNorm σ q' μ :=
  calc ‖∫ x, h x * σ x ∂μ‖ₑ = ‖Λ (hσ.toLp σ)‖ₑ := by
        rw [hΛ]
        congr 1
        exact integral_congr_ae (by filter_upwards [hσ.coeFn_toLp] with x hx; rw [hx])
    _ ≤ ‖Λ‖ₑ * ‖hσ.toLp σ‖ₑ := Λ.le_opENorm _
    _ = ‖Λ‖ₑ * eLpNorm σ q' μ := by rw [Lp.eNorm_def, eLpNorm_congr_ae hσ.coeFn_toLp]

/-- The truncation of `h` to a spanning set where `‖h‖ ≤ N` has `L^q` norm at most `C`, by testing
`h` against the extremal function of the truncation. -/
private theorem eLpNorm_indicator_spanningSets_inter_norm_le_of_forall_enorm_integral_inner_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [SigmaFinite μ] {q q' : ℝ≥0∞}
    [hqq : q.HolderConjugate q'] (hq : q ≠ ∞) {h h' : α → H} (hae : h =ᵐ[μ] h')
    (hh' : StronglyMeasurable h') {C : ℝ≥0∞}
    (hC : ∀ (g : α → H) (s : Set α), μ s ≠ ∞ → (∀ x, x ∉ s → g x = 0) → MemLp g ∞ μ →
      ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ ≤ C * eLpNorm g q' μ) (N : ℕ) :
    eLpNorm ((spanningSets μ N ∩ {x | ‖h' x‖ ≤ N}).indicator h') q μ ≤ C := by
  have hq0 : q ≠ 0 := hqq.ne_zero
  have hr1 : 1 ≤ q.toReal := by simpa using ENNReal.toReal_mono hq hqq.one_le
  set r := q.toReal
  set S := spanningSets μ N ∩ {x | ‖h' x‖ ≤ N}
  have hSm : MeasurableSet S := measurableSet_spanningSets_inter_norm_le hh' N
  -- Test the truncation `u = 1_S h` against its extremal function `g = |u| ^ (q - 2) u`.
  set u := S.indicator h' with hu_def
  set g : α → H := S.indicator fun x => ((‖h' x‖ ^ (r - 2) : ℝ) : 𝕜) • h' x with hg_def
  have hu_le : ∀ x, ‖u x‖ ≤ N := fun x => by
    by_cases hx : x ∈ S
    · simpa [hu_def, Set.indicator_of_mem hx] using hx.2
    · simp [hu_def, Set.indicator_of_notMem hx]
  have hg_norm : ∀ x, ‖g x‖ ≤ ‖u x‖ ^ (r - 1) := fun x => by
    by_cases hx : x ∈ S
    · simpa [hg_def, hu_def, Set.indicator_of_mem hx] using
        norm_ofReal_rpow_sub_two_smul_le (𝕜 := 𝕜) r (h' x)
    · simp [hg_def, Set.indicator_of_notMem hx, Real.rpow_nonneg]
  have hinner : ∀ x, ⟪h' x, g x⟫_𝕜 = ((‖u x‖ ^ r : ℝ) : 𝕜) := fun x => by
    by_cases hx : x ∈ S
    · simpa [hg_def, hu_def, Set.indicator_of_mem hx] using
        inner_ofReal_rpow_sub_two_smul (𝕜 := 𝕜) (by linarith : r ≠ 0) (h' x)
    · simp [hg_def, hu_def, Set.indicator_of_notMem hx, Real.zero_rpow (by linarith : r ≠ 0)]
  have hg_supp : ∀ x, x ∉ spanningSets μ N → g x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => hx (Set.mem_of_mem_inter_left h)) _
  have hum : StronglyMeasurable u := hh'.indicator hSm
  have hgm : AEStronglyMeasurable g μ := by
    refine (StronglyMeasurable.indicator ?_ hSm).aestronglyMeasurable
    exact (RCLike.continuous_ofReal.comp_stronglyMeasurable
      (hh'.norm.measurable.pow_const _).stronglyMeasurable).smul hh'
  have huLq : MemLp u q μ :=
    (memLp_top_of_bound hum.aestronglyMeasurable N
      (ae_of_all _ hu_le)).mono_exponent_of_measure_support_ne_top
      (fun x hx => Set.indicator_of_notMem (fun h => hx (Set.mem_of_mem_inter_left h)) _)
      (measure_spanningSets_lt_top μ N).ne le_top
  set X := eLpNorm u q μ with hX_def
  have hX : X ≠ ∞ := huLq.eLpNorm_lt_top.ne
  have hgX : eLpNorm g q' μ ≤ X ^ (r - 1) :=
    eLpNorm_le_eLpNorm_rpow_toReal_sub_one hq hgm (ae_of_all _ hg_norm)
  have hgtop : MemLp g ∞ μ := by
    refine memLp_top_of_bound hgm ((N : ℝ) ^ (r - 1)) (ae_of_all _ fun x => ?_)
    exact (hg_norm x).trans (Real.rpow_le_rpow (norm_nonneg _) (hu_le x) (by linarith))
  -- The pairing of `h` with `g` is `‖u‖_q ^ q`.
  have hXr : X ^ r = ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ := by
    have hcongr : ∀ᵐ x ∂μ, ((‖u x‖ ^ r : ℝ) : 𝕜) = ⟪h x, g x⟫_𝕜 :=
      hae.mono fun x hx => by rw [hx, hinner]
    rw [hX_def, huLq.eLpNorm_rpow_toReal_eq_enorm_integral (𝕜 := 𝕜) hq0 hq,
      integral_congr_ae hcongr]
  refine ENNReal.le_of_rpow_le_mul_rpow_sub_one (r := r) hX ?_
  calc X ^ r = ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ := hXr
    _ ≤ C * eLpNorm g q' μ :=
        hC g (spanningSets μ N) (measure_spanningSets_lt_top μ N).ne hg_supp hgtop
    _ ≤ C * X ^ (r - 1) := by gcongr

/-- **Norming by bounded functions of finite-measure support.** On a σ-finite measure space, let
`q < ∞` and `q'` be Hölder conjugate. If an almost everywhere strongly measurable `h` with values
in an inner product space satisfies `‖∫ ⟪h, g⟫‖ ≤ C ‖g‖_{q'}` for every bounded `g` vanishing off a
set of finite measure, then `‖h‖_q ≤ C`.

Unlike `MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top`, `h` is not assumed to lie in
`L^q`: when `C < ∞`, membership in `L^q` follows from the conclusion. The test functions lie in
every `Lˢ`, so the hypothesis only involves pairings that are defined, for instance, for every
`h ∈ L²`. -/
theorem AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [SigmaFinite μ] {q q' : ℝ≥0∞}
    [hqq : q.HolderConjugate q'] (hq : q ≠ ∞) {h : α → H} (hh : AEStronglyMeasurable h μ)
    {C : ℝ≥0∞}
    (hC : ∀ (g : α → H) (s : Set α), μ s ≠ ∞ → (∀ x, x ∉ s → g x = 0) → MemLp g ∞ μ →
      ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ ≤ C * eLpNorm g q' μ) :
    eLpNorm h q μ ≤ C := by
  set h' := hh.mk h
  have hh' : StronglyMeasurable h' := hh.stronglyMeasurable_mk
  rw [eLpNorm_congr_ae hh.ae_eq_mk]
  refine Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop)
    (f := fun N => (spanningSets μ N ∩ {x | ‖h' x‖ ≤ N}).indicator h')
    (Filter.Eventually.of_forall fun N =>
      eLpNorm_indicator_spanningSets_inter_norm_le_of_forall_enorm_integral_inner_le hq
        hh.ae_eq_mk hh' hC N)
    (fun N => (hh'.indicator (measurableSet_spanningSets_inter_norm_le hh' N)).aestronglyMeasurable)
    hh'.aestronglyMeasurable
    (ae_of_all _ fun x => tendsto_indicator_spanningSets_inter_norm_le h' x)

/-- Under a bound `re ⟪h, g⟫ ≤ c` on the pairings of `h ∈ L²` with the functions `g ∈ L²` of
`L^{q'}` norm at most one, every `g ∈ L²` of finite `L^{q'}` norm satisfies
`‖⟪h, g⟫‖ ≤ c ‖g‖_{q'}`: rescale `g` to norm one and rotate the pairing onto the real axis. -/
private theorem Lp.enorm_inner_le_of_forall_re_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {q' : ℝ≥0∞} (hq' : q' ≠ 0) {h : Lp E 2 μ} {c : ℝ} (hc : 0 ≤ c)
    (H : ∀ g : Lp E 2 μ, eLpNorm g q' μ ≤ 1 → RCLike.re ⟪h, g⟫_𝕜 ≤ c) (g : Lp E 2 μ)
    (hg : eLpNorm g q' μ ≠ ∞) :
    ‖⟪h, g⟫_𝕜‖ₑ ≤ ENNReal.ofReal c * eLpNorm g q' μ := by
  set a := eLpNorm g q' μ
  rcases eq_or_ne a 0 with ha0 | ha0
  · have hg0 : g = 0 := Lp.ext ((eLpNorm_eq_zero_iff hq').1 ha0
      |>.trans (Lp.coeFn_zero E 2 μ).symm)
    simp [hg0]
  set z := ⟪h, g⟫_𝕜
  rcases eq_or_ne z 0 with hz0 | hz0
  · simp [hz0]
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha0 hg
  have : 0 < ‖z‖ := norm_pos_iff.2 hz0
  -- The rescaled and rotated test function `k • g` has norm one and pairing `‖z‖ / ‖g‖_{q'}`.
  set k : 𝕜 := ((a.toReal⁻¹ * ‖z‖⁻¹ : ℝ) : 𝕜) * (starRingEnd 𝕜) z
  have hk : ‖k‖ = a.toReal⁻¹ := by
    rw [norm_mul, RCLike.norm_ofReal, RCLike.norm_conj, abs_of_pos (by positivity)]
    field_simp
  have hkg : eLpNorm (k • g) q' μ ≤ 1 := by
    have ha : ENNReal.ofReal a.toReal = a := ENNReal.ofReal_toReal hg
    rw [eLpNorm_congr_ae (Lp.coeFn_smul k g), eLpNorm_const_smul, ← ofReal_norm, hk]
    calc ENNReal.ofReal a.toReal⁻¹ * a = ENNReal.ofReal a.toReal⁻¹ * ENNReal.ofReal a.toReal := by
          rw [ha]
      _ = 1 := by
          rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hapos.ne', ENNReal.ofReal_one]
      _ ≤ 1 := le_rfl
  have hre : RCLike.re ⟪h, k • g⟫_𝕜 = ‖z‖ / a.toReal := by
    rw [inner_smul_right, mul_assoc, RCLike.conj_mul, RCLike.re_ofReal_mul]
    norm_cast
    field_simp
  have hle : ‖z‖ ≤ c * a.toReal := by
    have := H _ hkg
    rw [hre, div_le_iff₀ hapos] at this
    exact this
  calc ‖z‖ₑ = ENNReal.ofReal ‖z‖ := (ofReal_norm z).symm
    _ ≤ ENNReal.ofReal (c * a.toReal) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal c * a := by rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hg]

/-- Under the bound of `Lp.enorm_inner_le_of_forall_re_inner_le`, every bounded `g` vanishing off
a set of finite measure satisfies `‖∫ ⟪h, g⟫‖ ≤ c ‖g‖_{q'}`: such a `g` is square integrable, and
the integral is its pairing with `h` in `L²`. -/
private theorem Lp.enorm_integral_inner_le_of_forall_re_inner_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {q' : ℝ≥0∞} (hq' : q' ≠ 0) {h : Lp E 2 μ}
    {c : ℝ} (hc : 0 ≤ c) (H : ∀ g : Lp E 2 μ, eLpNorm g q' μ ≤ 1 → RCLike.re ⟪h, g⟫_𝕜 ≤ c)
    {g : α → E} {s : Set α} (hs : μ s ≠ ∞) (hgs : ∀ x, x ∉ s → g x = 0) (hg : MemLp g ∞ μ) :
    ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ ≤ ENNReal.ofReal c * eLpNorm g q' μ := by
  have hg2 : MemLp g 2 μ := hg.mono_exponent_of_measure_support_ne_top hgs hs le_top
  have hnorm : eLpNorm (hg2.toLp g) q' μ = eLpNorm g q' μ := eLpNorm_congr_ae hg2.coeFn_toLp
  rw [← L2.inner_toLp h hg2, ← hnorm]
  exact Lp.enorm_inner_le_of_forall_re_inner_le hq' hc H _
    (hnorm ▸ (hg.mono_exponent_of_measure_support_ne_top hgs hs le_top).eLpNorm_ne_top)

/-- The case `q = ∞` of `Lp.exists_eLpNorm_le_one_and_lt_re_inner`: if `re ⟪h, g⟫ ≤ c` for every
`g ∈ L²` in the unit ball of `L¹`, then `‖h‖_∞ ≤ c`. Test `‖h‖` against simple functions `g ∈ L¹`
through `g • (h / ‖h‖)`. -/
private theorem Lp.eLpNorm_top_le_of_forall_re_inner_le [SigmaFinite μ] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {h : Lp E 2 μ} {c : ℝ} (hc : 0 ≤ c)
    (H : ∀ g : Lp E 2 μ, eLpNorm g 1 μ ≤ 1 → RCLike.re ⟪h, g⟫_𝕜 ≤ c) :
    eLpNorm h ∞ μ ≤ ENNReal.ofReal c := by
  have hn : AEStronglyMeasurable (fun x ↦ ((‖h x‖ : ℝ) : 𝕜)) μ :=
    (RCLike.continuous_ofReal.comp continuous_norm).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable h)
  rw [← eLpNorm_congr_norm_ae hn (Lp.aestronglyMeasurable h)
    (ae_of_all _ fun x ↦ by simp)]
  refine hn.eLpNorm_top_le_of_forall_enorm_integral_mul_le fun g hg ↦ ?_
  set g₁ : α → E := fun x ↦ g x • ((‖h x‖⁻¹ : ℝ) : 𝕜) • h x
  -- `‖h x‖⁻¹ • h x` is the extremal vector `‖h x‖ ^ (r - 2) • h x` of the case `r = 1`.
  have hext : ∀ x, ((‖h x‖⁻¹ : ℝ) : 𝕜) • h x = ((‖h x‖ ^ ((1 : ℝ) - 2) : ℝ) : 𝕜) • h x :=
    fun x ↦ by norm_num [Real.rpow_neg_one]
  have hg₁ : ∀ x, ‖g₁ x‖ ≤ ‖g x‖ := fun x ↦ by
    dsimp only [g₁]
    rw [norm_smul, hext]
    refine mul_le_of_le_one_right (norm_nonneg _)
      ((norm_ofReal_rpow_sub_two_smul_le (𝕜 := 𝕜) 1 (h x)).trans ?_)
    norm_num
  have hinv : AEStronglyMeasurable (fun x ↦ ((‖h x‖⁻¹ : ℝ) : 𝕜)) μ :=
    (RCLike.continuous_ofReal.measurable.comp_aemeasurable
      (Lp.aestronglyMeasurable h).norm.aemeasurable.inv).aestronglyMeasurable
  have hg₁m : AEStronglyMeasurable g₁ μ :=
    g.aestronglyMeasurable.smul (hinv.smul (Lp.aestronglyMeasurable h))
  have hint : ∫ x, ⟪h x, g₁ x⟫_𝕜 ∂μ = ∫ x, ((‖h x‖ : ℝ) : 𝕜) * g x ∂μ := by
    congr 1 with x
    dsimp only [g₁]
    rw [hext, inner_smul_right, inner_ofReal_rpow_sub_two_smul one_ne_zero, Real.rpow_one,
      mul_comm]
  calc ‖∫ x, ((‖h x‖ : ℝ) : 𝕜) * g x ∂μ‖ₑ = ‖∫ x, ⟪h x, g₁ x⟫_𝕜 ∂μ‖ₑ := by rw [hint]
    _ ≤ ENNReal.ofReal c * eLpNorm g₁ 1 μ :=
        Lp.enorm_integral_inner_le_of_forall_re_inner_le one_ne_zero hc H
          (g.measure_support_lt_top_of_memLp hg one_ne_zero ENNReal.one_ne_top).ne
          (fun x hx ↦ by simp [g₁, Function.notMem_support.1 hx])
          ((g.memLp_top μ).of_le hg₁m (ae_of_all _ hg₁))
    _ ≤ ENNReal.ofReal c * eLpNorm g 1 μ := by gcongr; exact eLpNorm_mono hg₁m hg₁

/-- **Norming `Lᵠ` norms by square-integrable functions.** On a σ-finite measure space, let `q`
and `q'` be Hölder conjugate, `1 ≤ q ≤ ∞`. For every `h ∈ L²`, the `L^q` norm of `h`, finite or
not, is the supremum of `re ⟪h, g⟫` over the functions `g ∈ L²` in the unit ball of `L^{q'}`:
below every `c` with `c < ‖h‖_q` there is such a `g` with `c < re ⟪h, g⟫`. The converse bound
`re ⟪h, g⟫ ≤ ‖h‖_q ‖g‖_{q'}` is Hölder's inequality (`TauCeti.enorm_integral_inner_le`). -/
theorem Lp.exists_eLpNorm_le_one_and_lt_re_inner [SigmaFinite μ] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {q q' : ℝ≥0∞} [hqq : q.HolderConjugate q']
    (h : Lp E 2 μ) {c : ℝ} (hc : ENNReal.ofReal c < eLpNorm h q μ) :
    ∃ g : Lp E 2 μ, eLpNorm g q' μ ≤ 1 ∧ c < RCLike.re ⟪h, g⟫_𝕜 := by
  rcases lt_or_ge c 0 with hc0 | hc0
  · exact ⟨0, Lp.eLpNorm_coeFn_zero.trans_le zero_le_one, by simpa using hc0⟩
  by_contra! H
  refine hc.not_ge ?_
  rcases eq_or_ne q ∞ with rfl | hq
  · obtain rfl : q' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q').1 rfl
    exact Lp.eLpNorm_top_le_of_forall_re_inner_le hc0 H
  · exact (Lp.aestronglyMeasurable h).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := 𝕜)
      (q' := q') hq fun g s hs hgs hg ↦
        Lp.enorm_integral_inner_le_of_forall_re_inner_le hqq.symm.ne_zero hc0 H hs hgs hg

end MeasureTheory

namespace TopologicalSpace.IsSeparable

variable {X 𝕜 E : Type*} [RCLike 𝕜] {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Countable norming families.** On a σ-finite measure space, let `q` and `q'` be Hölder
conjugate. For every separable set `S` of square-integrable functions there is a sequence `gₙ` of
square-integrable functions in the unit ball of `L^{q'}` which norms every element of `S` in
`L^q`:

`‖h‖_q = supₙ re ⟪h, gₙ⟫` for every `h ∈ S`,

whether `‖h‖_q` is finite or not. -/
theorem exists_seq_eLpNorm_eq_iSup_ofReal_re_inner [SigmaFinite μ] {q q' : ℝ≥0∞}
    [hqq : q.HolderConjugate q'] {S : Set (Lp E 2 μ)} (hS : IsSeparable S) :
    ∃ g : ℕ → Lp E 2 μ, (∀ n, eLpNorm (g n) q' μ ≤ 1) ∧
      ∀ h ∈ S, eLpNorm h q μ = ⨆ n, ENNReal.ofReal (RCLike.re ⟪h, g n⟫_𝕜) := by
  have := hS.separableSpace
  set Γ := {g : Lp E 2 μ // eLpNorm g q' μ ≤ 1}
  -- For each rational level `c`, countably many test functions cover `{h ∈ S | c < ‖h‖_q}`.
  have hcount : ∀ c : ℚ, ∃ D : Set Γ, D.Countable ∧
      ⋃ g ∈ D, {h : S | (c : ℝ) < RCLike.re ⟪(h : Lp E 2 μ), (g : Lp E 2 μ)⟫_𝕜} =
        ⋃ g : Γ, {h : S | (c : ℝ) < RCLike.re ⟪(h : Lp E 2 μ), (g : Lp E 2 μ)⟫_𝕜} := by
    intro c
    refine isOpen_iUnion_countable _ fun g ↦ isOpen_lt continuous_const ?_
    exact RCLike.continuous_re.comp ((continuous_subtype_val).inner continuous_const)
  choose D hDc hD using hcount
  set D' : Set (Lp E 2 μ) := insert 0 (⋃ c : ℚ, Subtype.val '' D c)
  have hD'c : D'.Countable :=
    (Set.countable_iUnion fun c ↦ (hDc c).image _).insert 0
  obtain ⟨g, hg⟩ := hD'c.exists_eq_range (Set.insert_nonempty _ _)
  have hgΓ : ∀ n, eLpNorm (g n) q' μ ≤ 1 := by
    intro n
    have hn : g n ∈ D' := hg ▸ Set.mem_range_self n
    rcases hn with hn | hn
    · exact hn ▸ Lp.eLpNorm_coeFn_zero.trans_le zero_le_one
    · obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hn
      obtain ⟨γ, -, hγ⟩ := hc
      exact hγ ▸ γ.2
  refine ⟨g, hgΓ, fun h hh ↦ le_antisymm ?_ (iSup_le fun n ↦ ?_)⟩
  · -- Below `‖h‖_q`, a rational level is exceeded by the pairing with some `gₙ`.
    refine le_of_forall_lt fun b hb ↦ ?_
    obtain ⟨c, hc0, hbc, hch⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hb
    obtain ⟨γ, hγ, hcγ⟩ := Lp.exists_eLpNorm_le_one_and_lt_re_inner (𝕜 := 𝕜) (q' := q') h
      (c := c) hch
    have hmem : (⟨h, hh⟩ : S) ∈ ⋃ γ : Γ,
        {h : S | (c : ℝ) < RCLike.re ⟪(h : Lp E 2 μ), (γ : Lp E 2 μ)⟫_𝕜} :=
      Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hcγ⟩
    rw [← hD c] at hmem
    obtain ⟨γ', hγ'D, hγ'⟩ := Set.mem_iUnion₂.1 hmem
    have hγ'mem : (γ' : Lp E 2 μ) ∈ Set.range g :=
      hg ▸ Set.mem_insert_of_mem _ (Set.mem_iUnion.2 ⟨c, γ', hγ'D, rfl⟩)
    obtain ⟨n, hn⟩ := hγ'mem
    refine lt_iSup_iff.2 ⟨n, hbc.trans ?_⟩
    rw [hn]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by exact_mod_cast hc0)).2 hγ'
  · -- Hölder's inequality bounds each pairing.
    calc ENNReal.ofReal (RCLike.re ⟪h, g n⟫_𝕜) ≤ ‖⟪h, g n⟫_𝕜‖ₑ := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm _)
      _ ≤ eLpNorm h q μ * eLpNorm (g n) q' μ := by
          rw [L2.inner_def]
          exact TauCeti.enorm_integral_inner_le
      _ ≤ eLpNorm h q μ := mul_le_of_le_one_right' (hgΓ n)

end TopologicalSpace.IsSeparable

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {μ : Measure α}

section toDual

variable {q q' : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ q')] [q.HolderConjugate q']

variable (𝕜 μ q q') in
/-- On a σ-finite measure space, for Hölder conjugate exponents `q` and `q'`, the integral pairing
`g ↦ (f ↦ ∫ g f dμ)` is a linear isometry from `L^q(μ)` to the continuous dual of `L^q'(μ)`:
integration against `g` is a continuous linear functional on `L^q'(μ)` of norm `‖g‖_q`. -/
noncomputable def toDual [SigmaFinite μ] : Lp 𝕜 q μ →ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 q' μ) where
  toLinearMap := ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ q q' :
    Lp 𝕜 q μ →ₗ[𝕜] StrongDual 𝕜 (Lp 𝕜 q' μ))
  norm_map' g := by
    set Λ := (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ q q' g
    -- Both norms are the real parts of the extended norms, so it suffices to compare those.
    rw [ContinuousLinearMap.coe_coe, ← toReal_eNorm, ← toReal_eNorm]
    congr 1
    -- Hölder's inequality gives `‖Λ‖ ≤ ‖g‖_q`; testing `Λ` on simple functions gives the converse.
    refine le_antisymm (Λ.opENorm_le_bound fun f => ?_) ?_
    · rw [ContinuousLinearMap.lpPairing_mul_eq_integral, Lp.eNorm_def, Lp.eNorm_def]
      exact TauCeti.enorm_integral_mul_le
    · rw [Lp.eNorm_def]
      exact (Lp.memLp g).eLpNorm_le_of_forall_enorm_integral_mul_le fun σ hσ =>
        enorm_integral_mul_le_of_apply_eq Λ hσ
          (ContinuousLinearMap.lpPairing_mul_eq_integral g _)

@[simp]
theorem toDual_apply [SigmaFinite μ] (g : Lp 𝕜 q μ) (f : Lp 𝕜 q' μ) :
    toDual 𝕜 μ q q' g f = ∫ x, g x * f x ∂μ := by
  rw [toDual, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.lpPairing_mul_eq_integral]

/-- Pairing `g ∈ L^q(μ)` with the indicator function of a set `s` of finite measure, scaled by
`c`, gives `c` times the integral of `g` over `s`. -/
-- High priority, so that `simp` uses this lemma before unfolding the pairing by `toDual_apply`.
@[simp high]
theorem toDual_indicatorConstLp [SigmaFinite μ] (g : Lp 𝕜 q μ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : 𝕜) :
    toDual 𝕜 μ q q' g (indicatorConstLp q' hs hμs c) = (∫ x in s, g x ∂μ) * c := by
  rw [toDual_apply, ← integral_mul_const, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := q') (hs := hs) (hμs := hμs) (c := c)] with x hx
  by_cases hxs : x ∈ s <;> simp [hx, hxs]

end toDual

end MeasureTheory.Lp
