/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.InnerProductSpace.ExtremalRpow
import TauCeti.Analysis.Normed.Module.RCLike.Rpow
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.StronglyMeasurable.SpanningSets
import TauCeti.MeasureTheory.Function.Holder

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
prove that an operator defined on `L²` maps `L² ∩ Lᵖ` into `L^q` by duality.

The integral Hölder bounds apply to arbitrary functions, using the convention that `eLpNorm`
is `∞` outside the almost everywhere strongly measurable functions.

## Main declarations

* `TauCeti.eLpNorm_le_eLpNorm_rpow`: if `‖u‖ ≤ ‖f‖ ^ r`, then `‖u‖_s ≤ ‖f‖_p ^ r` when
  `1 / s = r / p`.
* `TauCeti.enorm_integral_mul_le`: Hölder's inequality `‖∫ u v‖ ≤ ‖u‖_p ‖v‖_q` for an integral.
* `MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top`: the duality bound
  for `q < ∞`.
* `MeasureTheory.AEStronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le` and
  `MeasureTheory.MemLp.eLpNorm_top_le_of_forall_enorm_integral_mul_le`: the duality bound for
  `q = ∞` on a σ-finite measure space, the first without assuming `h ∈ L^∞` in advance.
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

## References

* G. B. Folland, *Real Analysis*, second edition, Theorem 6.14.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

namespace TauCeti

variable {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- If `‖u‖ ≤ ‖f‖ ^ r` almost everywhere with `r ≥ 0`, then `‖u‖_s ≤ ‖f‖_p ^ r` for the exponent
`1 / s = r / p`. For `r = 0` this reads `‖u‖_∞ ≤ 1`. -/
theorem eLpNorm_le_eLpNorm_rpow {f : α → E} {u : α → F} {p s : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r)
    (hf : AEStronglyMeasurable f μ) (hu : AEStronglyMeasurable u μ)
    (hs : s⁻¹ = ENNReal.ofReal r * p⁻¹) (hle : ∀ᵐ x ∂μ, ‖u x‖ ≤ ‖f x‖ ^ r) :
    eLpNorm u s μ ≤ eLpNorm f p μ ^ r := by
  rcases hr.eq_or_lt with rfl | hr
  · have hs : s = ∞ := by simpa using hs
    subst hs
    rw [ENNReal.rpow_zero, eLpNorm_exponent_top hu]
    simpa using eLpNormEssSup_le_of_ae_bound (C := 1) (by simpa using hle)
  · calc eLpNorm u s μ ≤ eLpNorm (fun x => ‖f x‖ ^ r) s μ := eLpNorm_mono_ae_real hu hle
      _ = eLpNorm f (s * ENNReal.ofReal r) μ ^ r := eLpNorm_norm_rpow f hf hr
      _ = eLpNorm f p μ ^ r := by
        congr 2
        have h0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
        rw [← inv_inv s, hs, ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top), inv_inv,
          mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top, one_mul]

/-- **Hölder's inequality** for the integral of a product: `‖∫ u v‖ ≤ ‖u‖_p ‖v‖_q` for Hölder
conjugate exponents `p` and `q`. -/
theorem enorm_integral_mul_le {𝕜 : Type*} [NonUnitalNormedRing 𝕜] [NormedSpace ℝ 𝕜]
    {p q : ℝ≥0∞} [p.HolderConjugate q] {u v : α → 𝕜} :
    ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm u p μ * eLpNorm v q μ := by
  calc ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm (fun x => u x * v x) 1 μ :=
        (enorm_integral_le_lintegral_enorm _).trans lintegral_enorm_le_eLpNorm_one
    _ ≤ eLpNorm u p μ * eLpNorm v q μ := by
        simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm_of_pos (· * ·) 1 continuous_mul
          (ae_of_all _ fun x => by simpa using norm_mul_le (u x) (v x)) zero_lt_one

/-- **Hölder's inequality** for the integral of an inner product: `‖∫ ⟪u, v⟫‖ ≤ ‖u‖_p ‖v‖_q` for
Hölder conjugate exponents `p` and `q`. -/
theorem enorm_integral_inner_le {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {p q : ℝ≥0∞} [p.HolderConjugate q] {u v : α → H} :
    ‖∫ x, ⟪u x, v x⟫_𝕜 ∂μ‖ₑ ≤ eLpNorm u p μ * eLpNorm v q μ := by
  calc ‖∫ x, ⟪u x, v x⟫_𝕜 ∂μ‖ₑ ≤ eLpNorm (fun x => ⟪u x, v x⟫_𝕜) 1 μ :=
        (enorm_integral_le_lintegral_enorm _).trans lintegral_enorm_le_eLpNorm_one
    _ ≤ eLpNorm u p μ * eLpNorm v q μ := by
        simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm_of_pos (fun a b => ⟪a, b⟫_𝕜) 1
          continuous_inner (ae_of_all _ fun x => by simpa using norm_inner_le_norm (u x) (v x))
          zero_lt_one

/-- If `‖g‖ ≤ ‖f‖ ^ (q - 1)` almost everywhere, then `‖g‖_{q'} ≤ ‖f‖_q ^ (q - 1)` for Hölder
conjugate exponents `q < ∞` and `q'`. -/
theorem eLpNorm_le_eLpNorm_rpow_toReal_sub_one {q q' : ℝ≥0∞} [hqq : q.HolderConjugate q']
    (hq : q ≠ ∞) {f : α → E} {g : α → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hle : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖ ^ (q.toReal - 1)) :
    eLpNorm g q' μ ≤ eLpNorm f q μ ^ (q.toReal - 1) := by
  have hr1 : 1 ≤ q.toReal := by simpa using ENNReal.toReal_mono hq hqq.one_le
  refine eLpNorm_le_eLpNorm_rpow (by linarith) hf hg ?_ hle
  rw [← ENNReal.HolderConjugate.sub_one_mul_inv q q' hq, ENNReal.ofReal_sub _ zero_le_one,
    ENNReal.ofReal_toReal hq, ENNReal.ofReal_one]

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
    eLpNorm_le_eLpNorm_rpow_toReal_sub_one hq φ.aestronglyMeasurable g.aestronglyMeasurable
      (ae_of_all _ hg_norm)
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
          exact enorm_sub_le
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
everywhere strongly measurable and integrable on every set of finite measure. If `h` satisfies
`‖∫ h g‖ ≤ C ‖g‖₁` for every simple function `g ∈ L¹`, then `‖h‖_∞ ≤ C`. In particular `h ∈ L^∞`
as soon as `C < ∞`. -/
theorem AEStronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le [SigmaFinite μ]
    {h : α → 𝕜} (hmeas : AEStronglyMeasurable h μ)
    (hint : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn h s μ) {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α 𝕜, MemLp g 1 μ → ‖∫ x, h x * g x ∂μ‖ₑ ≤ C * eLpNorm g 1 μ) :
    eLpNorm h ∞ μ ≤ C := by
  by_contra! hlt
  obtain ⟨t, hCt, htN⟩ := exists_between hlt
  set h' := hmeas.mk h
  have hhh' : h =ᵐ[μ] h' := hmeas.ae_eq_mk
  -- The set `{t < ‖h‖}` has positive measure, so by σ-finiteness it contains a set `F` of
  -- finite positive measure.
  have hE : MeasurableSet {x | t < ‖h' x‖ₑ} :=
    measurableSet_lt measurable_const hmeas.stronglyMeasurable_mk.measurable.enorm
  have hEpos : 0 < μ {x | t < ‖h' x‖ₑ} := by
    refine pos_iff_ne_zero.2 fun h0 => htN.not_ge ?_
    rw [eLpNorm_exponent_top hmeas]
    refine eLpNormEssSup_le_of_ae_enorm_bound ?_
    filter_upwards [hhh', measure_eq_zero_iff_ae_notMem.1 h0] with x hx hx'
    rw [hx]
    simpa using hx'
  obtain ⟨F, hFm, hFE, hFpos, hFtop⟩ := Measure.exists_subset_measure_lt_top hE hEpos
  -- The case `q = 1`, applied to `1_F h`, bounds `∫_F ‖h‖` by `C μ(F)`.
  have hk : MemLp (F.indicator h) 1 μ := by
    rw [memLp_indicator_iff_restrict hFm.nullMeasurableSet, memLp_one_iff_integrable]
    exact hint F hFm hFtop
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
      eLpNorm_one_eq_lintegral_enorm hmeas.restrict, ← setLIntegral_const]
    refine setLIntegral_mono_ae hmeas.enorm.restrict ?_
    filter_upwards [hhh'] with x hx hxF
    rw [hx]
    exact (hFE hxF).le
  exact ((ENNReal.mul_le_mul_iff_left hFpos.ne' hFtop.ne).1 (hlow.trans hkC)).not_gt hCt

/-- **Norming by simple functions, `q = ∞`.** On a σ-finite measure space, if `h ∈ L^∞`
satisfies `‖∫ h g‖ ≤ C ‖g‖₁` for every simple function `g ∈ L¹`, then `‖h‖_∞ ≤ C`. -/
theorem MemLp.eLpNorm_top_le_of_forall_enorm_integral_mul_le [SigmaFinite μ] {h : α → 𝕜}
    (hh : MemLp h ∞ μ) {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α 𝕜, MemLp g 1 μ → ‖∫ x, h x * g x ∂μ‖ₑ ≤ C * eLpNorm g 1 μ) :
    eLpNorm h ∞ μ ≤ C :=
  hh.aestronglyMeasurable.eLpNorm_top_le_of_forall_enorm_integral_mul_le
    (fun s _ hs => have : Fact (μ s < ∞) := ⟨hs⟩; (hh.restrict s).integrable le_top) hC

/-- **Norming by simple functions.** On a σ-finite measure space, let `q` and `q'` be Hölder
conjugate. If `h ∈ L^q` satisfies `‖∫ h g‖ ≤ C ‖g‖_{q'}` for every simple function
`g ∈ L^{q'}`, then `‖h‖_q ≤ C`. -/
theorem MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le [SigmaFinite μ] {q q' : ℝ≥0∞}
    [q.HolderConjugate q'] {h : α → 𝕜} (hh : MemLp h q μ) {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α 𝕜, MemLp g q' μ → ‖∫ x, h x * g x ∂μ‖ₑ ≤ C * eLpNorm g q' μ) :
    eLpNorm h q μ ≤ C := by
  rcases eq_or_ne q ∞ with rfl | hq
  · obtain rfl : q' = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q').1 rfl
    exact hh.eLpNorm_top_le_of_forall_enorm_integral_mul_le hC
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
    _ = ‖Λ‖ₑ * eLpNorm σ q' μ := by rw [Lp.enorm_def, eLpNorm_congr_ae hσ.coeFn_toLp]

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
    eLpNorm_le_eLpNorm_rpow_toReal_sub_one hq hum.aestronglyMeasurable hgm (ae_of_all _ hg_norm)
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

end MeasureTheory

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
    rw [ContinuousLinearMap.coe_coe, ← toReal_enorm, ← toReal_enorm]
    congr 1
    -- Hölder's inequality gives `‖Λ‖ ≤ ‖g‖_q`; testing `Λ` on simple functions gives the converse.
    refine le_antisymm (Λ.opENorm_le_bound fun f => ?_) ?_
    · rw [ContinuousLinearMap.lpPairing_mul_eq_integral, Lp.enorm_def, Lp.enorm_def]
      exact TauCeti.enorm_integral_mul_le
    · rw [Lp.enorm_def]
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
