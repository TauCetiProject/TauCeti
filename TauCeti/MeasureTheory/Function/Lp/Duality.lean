/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

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
Riesz–Thorin theorem.

For functions with values in an inner product space, paired by `∫ ⟪h, g⟫`, the file also proves
a version for `q < ∞` that does not assume `h ∈ L^q` in advance: the test functions are bounded
and vanish off a set of finite measure, and the extremal function `|h| ^ (q - 2) h` is truncated
where `h` is large and outside a spanning set of a σ-finite measure. This is the form needed to
prove that an operator defined on `L²` maps `L² ∩ Lᵖ` into `L^q` by duality.

## Main declarations

* `TauCeti.eLpNorm_le_eLpNorm_rpow`: if `‖u‖ ≤ ‖f‖ ^ r`, then `‖u‖_s ≤ ‖f‖_p ^ r` when
  `1 / s = r / p`.
* `TauCeti.enorm_integral_mul_le`: Hölder's inequality `‖∫ u v‖ ≤ ‖u‖_p ‖v‖_q` for an integral.
* `MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top`: the duality bound
  for `q < ∞`.
* `MeasureTheory.MemLp.eLpNorm_top_le_of_forall_enorm_integral_mul_le`: the duality bound for
  `q = ∞` on a σ-finite measure space.
* `MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le`: the duality bound for every
  `1 ≤ q ≤ ∞` on a σ-finite measure space.
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
theorem enorm_integral_mul_le {𝕜 : Type*} [NormedRing 𝕜] [NormedSpace ℝ 𝕜] {p q : ℝ≥0∞}
    [p.HolderConjugate q] {u v : α → 𝕜} (hu : AEStronglyMeasurable u μ)
    (hv : AEStronglyMeasurable v μ) :
    ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm u p μ * eLpNorm v q μ := by
  calc ‖∫ x, u x * v x ∂μ‖ₑ ≤ ∫⁻ x, ‖u x * v x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => u x * v x) 1 μ := (eLpNorm_one_eq_lintegral_enorm (hu.mul hv)).symm
    _ ≤ (1 : ℝ≥0) * eLpNorm u p μ * eLpNorm v q μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (· * ·) 1 continuous_mul hu hv
          (ae_of_all _ fun x => by simpa using norm_mul_le (u x) (v x))
    _ = eLpNorm u p μ * eLpNorm v q μ := by simp

/-- **Hölder's inequality** for the integral of an inner product: `‖∫ ⟪u, v⟫‖ ≤ ‖u‖_p ‖v‖_q` for
Hölder conjugate exponents `p` and `q`. -/
theorem enorm_integral_inner_le {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] {p q : ℝ≥0∞} [p.HolderConjugate q] {u v : α → H}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) :
    ‖∫ x, ⟪u x, v x⟫_𝕜 ∂μ‖ₑ ≤ eLpNorm u p μ * eLpNorm v q μ := by
  calc ‖∫ x, ⟪u x, v x⟫_𝕜 ∂μ‖ₑ ≤ ∫⁻ x, ‖⟪u x, v x⟫_𝕜‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => ⟪u x, v x⟫_𝕜) 1 μ := (eLpNorm_one_eq_lintegral_enorm (hu.inner hv)).symm
    _ ≤ (1 : ℝ≥0) * eLpNorm u p μ * eLpNorm v q μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (fun a b => ⟪a, b⟫_𝕜) 1 continuous_inner hu hv
          (ae_of_all _ fun x => by simpa using norm_inner_le_norm (u x) (v x))
    _ = eLpNorm u p μ * eLpNorm v q μ := by simp

end TauCeti

namespace MeasureTheory

variable {α 𝕜 : Type*} {mα : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]

open TauCeti

/-- If `X ^ r ≤ C X ^ (r - 1)` for a finite `X` and `r ≥ 1`, then `X ≤ C`: the last step of every
norming argument, where `X` is a norm and `X ^ r` its pairing with the extremal function. -/
private theorem le_of_rpow_le_mul_rpow_sub_one {X C : ℝ≥0∞} {r : ℝ} (hr : 1 ≤ r) (hX : X ≠ ∞)
    (h : X ^ r ≤ C * X ^ (r - 1)) : X ≤ C := by
  rcases eq_or_ne X 0 with hX0 | hX0
  · simp [hX0]
  have hXr : X ^ r = X ^ (r - 1) * X := by
    conv_lhs => rw [show r = (r - 1) + 1 by ring]
    rw [ENNReal.rpow_add _ _ hX0 hX, ENNReal.rpow_one]
  have hpow0 : X ^ (r - 1) ≠ 0 := by simp [ENNReal.rpow_eq_zero_iff, hX0, hX]
  have hpowtop : X ^ (r - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hX
  rw [hXr, mul_comm C] at h
  exact (ENNReal.mul_le_mul_iff_right hpow0 hpowtop).1 h

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
  set g : SimpleFunc α 𝕜 := φ.map fun c => conj c * ((‖c‖ ^ (r - 2) : ℝ) : 𝕜) with hg_def
  have hg_norm : ∀ x, ‖g x‖ ≤ ‖φ x‖ ^ (r - 1) := fun x => by
    rcases eq_or_ne (φ x) 0 with h0 | h0
    · simp [hg_def, h0, Real.rpow_nonneg]
    · have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 h0
      simp only [hg_def, SimpleFunc.map_apply, norm_mul, RCLike.norm_conj, RCLike.norm_ofReal,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      rw [show r - 1 = 1 + (r - 2) by ring, Real.rpow_add hpos, Real.rpow_one]
  have hφg : ∀ x, φ x * g x = ((‖φ x‖ ^ r : ℝ) : 𝕜) := fun x => by
    rcases eq_or_ne (φ x) 0 with h0 | h0
    · simp [hg_def, h0, Real.zero_rpow (by linarith : r ≠ 0)]
    · have hpos : 0 < ‖φ x‖ := norm_pos_iff.2 h0
      simp only [hg_def, SimpleFunc.map_apply, ← mul_assoc, RCLike.mul_conj]
      rw [show r = 2 + (r - 2) by ring, Real.rpow_add hpos, Real.rpow_two]
      push_cast
      ring_nf
  set X := eLpNorm φ q μ with hX_def
  have hX : X ≠ ∞ := hφmem.eLpNorm_lt_top.ne
  have hgX : eLpNorm g q' μ ≤ X ^ (r - 1) := by
    refine eLpNorm_le_eLpNorm_rpow (by linarith) φ.aestronglyMeasurable g.aestronglyMeasurable
      ?_ (ae_of_all _ hg_norm)
    rw [← ENNReal.HolderConjugate.sub_one_mul_inv q q' hq, ENNReal.ofReal_sub _ zero_le_one,
      ENNReal.ofReal_toReal hq, ENNReal.ofReal_one]
  have hgmem : MemLp g q' μ :=
    memLp_iff.2 (hgX.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by linarith) hX))
  -- The pairing of `φ` with its extremal function is `‖φ‖_q ^ q`.
  have hXr : X ^ r ≤ ‖∫ x, φ x * g x ∂μ‖ₑ := by
    have hI : 0 ≤ ∫ x, ‖φ x‖ ^ r ∂μ :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    rw [hX_def, hφmem.eLpNorm_eq_integral_rpow_norm hq0 hq, ENNReal.ofReal_rpow_of_nonneg
      (Real.rpow_nonneg hI _) (by linarith), Real.rpow_inv_rpow hI (by linarith)]
    have heq : ∫ x, φ x * g x ∂μ = ((∫ x, ‖φ x‖ ^ r ∂μ : ℝ) : 𝕜) := by
      simp_rw [hφg]
      exact integral_ofReal
    rw [heq, ← ofReal_norm, RCLike.norm_ofReal, abs_of_nonneg hI]
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
          · exact enorm_integral_mul_le (hh.aestronglyMeasurable.sub φ.aestronglyMeasurable)
              g.aestronglyMeasurable
      _ ≤ (C + ε / 2) * X ^ (r - 1) := by
          rw [← add_mul]
          gcongr
  -- Hence `‖φ‖_q ≤ C + ε / 2`, and `‖h‖_q ≤ ‖φ‖_q + ε / 2`.
  have hXle : X ≤ C + ε / 2 := le_of_rpow_le_mul_rpow_sub_one hr1 hX (hXr.trans hsplit)
  calc eLpNorm h q μ = eLpNorm ((h - ⇑φ) + ⇑φ) q μ := by simp
    _ ≤ eLpNorm (h - ⇑φ) q μ + X := eLpNorm_add_le hq1
    _ ≤ ε / 2 + (C + ε / 2) := by gcongr
    _ = C + ε := by rw [add_comm, add_assoc, ENNReal.add_halves]

/-- **Norming by simple functions, `q = ∞`.** On a σ-finite measure space, if `h ∈ L^∞`
satisfies `‖∫ h g‖ ≤ C ‖g‖₁` for every simple function `g ∈ L¹`, then `‖h‖_∞ ≤ C`. -/
theorem MemLp.eLpNorm_top_le_of_forall_enorm_integral_mul_le [SigmaFinite μ] {h : α → 𝕜}
    (hh : MemLp h ∞ μ) {C : ℝ≥0∞}
    (hC : ∀ g : SimpleFunc α 𝕜, MemLp g 1 μ → ‖∫ x, h x * g x ∂μ‖ₑ ≤ C * eLpNorm g 1 μ) :
    eLpNorm h ∞ μ ≤ C := by
  by_contra! hlt
  obtain ⟨t, hCt, htN⟩ := exists_between hlt
  have hmeas := hh.aestronglyMeasurable
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
  have : IsFiniteMeasure (μ.restrict F) := isFiniteMeasure_restrict.2 hFtop.ne
  -- The case `q = 1`, applied to `1_F h`, bounds `∫_F ‖h‖` by `C μ(F)`.
  have hk : MemLp (F.indicator h) 1 μ := by
    rw [memLp_indicator_iff_restrict hFm.nullMeasurableSet]
    exact (hh.restrict F).mono_exponent le_top
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

/-- **Norming by bounded functions of finite-measure support.** On a σ-finite measure space, let
`q < ∞` and `q'` be Hölder conjugate. If an almost everywhere strongly measurable `h` with values
in an inner product space satisfies `‖∫ ⟪h, g⟫‖ ≤ C ‖g‖_{q'}` for every bounded `g` vanishing off a
set of finite measure, then `‖h‖_q ≤ C`.

Unlike `MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top`, `h` is not assumed to lie in
`L^q`: membership is part of the conclusion. The test functions lie in every `Lˢ`, so the
hypothesis only involves pairings that are defined, for instance, for every `h ∈ L²`. -/
theorem AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [SigmaFinite μ] {q q' : ℝ≥0∞}
    [hqq : q.HolderConjugate q'] (hq : q ≠ ∞) {h : α → H} (hh : AEStronglyMeasurable h μ)
    {C : ℝ≥0∞}
    (hC : ∀ (g : α → H) (s : Set α), μ s ≠ ∞ → (∀ x, x ∉ s → g x = 0) → MemLp g ∞ μ →
      ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ ≤ C * eLpNorm g q' μ) :
    eLpNorm h q μ ≤ C := by
  have hq1 : 1 ≤ q := hqq.one_le
  have hq0 : q ≠ 0 := hqq.ne_zero
  set r := q.toReal
  have hr1 : 1 ≤ r := by simpa using ENNReal.toReal_mono hq hq1
  set h' := hh.mk h
  have hh' : StronglyMeasurable h' := hh.stronglyMeasurable_mk
  -- Truncate `h` to the sets `S N` where it is bounded by `N` and inside the `N`-th spanning set.
  set S : ℕ → Set α := fun N => spanningSets μ N ∩ {x | ‖h' x‖ ≤ N} with hS_def
  have hSm : ∀ N, MeasurableSet (S N) := fun N =>
    (measurableSet_spanningSets μ N).inter (measurableSet_le hh'.norm.measurable measurable_const)
  rw [eLpNorm_congr_ae hh.ae_eq_mk]
  refine Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop) (f := fun N => (S N).indicator h')
    (Filter.Eventually.of_forall fun N => ?_)
    (fun N => (hh'.indicator (hSm N)).aestronglyMeasurable) hh'.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  swap
  · -- Every point eventually lies in `S N`.
    have h1 : ∀ᶠ N in Filter.atTop, x ∈ spanningSets μ N := Filter.eventually_atTop.2
      ⟨spanningSetsIndex μ x, fun N hN => monotone_spanningSets μ hN (mem_spanningSetsIndex μ x)⟩
    have h2 : ∀ᶠ N : ℕ in Filter.atTop, ‖h' x‖ ≤ N :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [h1, h2] with N hN1 hN2
    exact (Set.indicator_of_mem (show x ∈ S N from ⟨hN1, hN2⟩) h').symm
  -- Test the truncation `u = 1_{S N} h` against its extremal function `g = |u| ^ (q - 2) u`.
  set u := (S N).indicator h' with hu_def
  set g : α → H := (S N).indicator fun x => ((‖h' x‖ ^ (r - 2) : ℝ) : 𝕜) • h' x with hg_def
  have hu_le : ∀ x, ‖u x‖ ≤ N := fun x => by
    by_cases hx : x ∈ S N
    · simpa [hu_def, Set.indicator_of_mem hx] using hx.2
    · simp [hu_def, Set.indicator_of_notMem hx]
  have hg_norm : ∀ x, ‖g x‖ ≤ ‖u x‖ ^ (r - 1) := fun x => by
    by_cases hx : x ∈ S N
    · rw [hg_def, hu_def, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      rcases eq_or_ne (h' x) 0 with h0 | h0
      · simp [h0, Real.rpow_nonneg]
      · have hpos : 0 < ‖h' x‖ := norm_pos_iff.2 h0
        rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
          show r - 1 = (r - 2) + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
    · simp [hg_def, Set.indicator_of_notMem hx, Real.rpow_nonneg]
  have hinner : ∀ x, ⟪h' x, g x⟫_𝕜 = ((‖u x‖ ^ r : ℝ) : 𝕜) := fun x => by
    by_cases hx : x ∈ S N
    · rw [hg_def, hu_def, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      rcases eq_or_ne (h' x) 0 with h0 | h0
      · simp [h0, Real.zero_rpow (by linarith : r ≠ 0)]
      · have hpos : 0 < ‖h' x‖ := norm_pos_iff.2 h0
        rw [inner_smul_right, inner_self_eq_norm_sq_to_K, show r = (r - 2) + 2 by ring,
          Real.rpow_add hpos, Real.rpow_two]
        push_cast
        ring_nf
    · simp [hg_def, hu_def, Set.indicator_of_notMem hx, Real.zero_rpow (by linarith : r ≠ 0)]
  have hu_supp : ∀ x, x ∉ spanningSets μ N → u x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => hx h.1) _
  have hg_supp : ∀ x, x ∉ spanningSets μ N → g x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => hx h.1) _
  have hum : StronglyMeasurable u := hh'.indicator (hSm N)
  have hgm : AEStronglyMeasurable g μ := by
    refine (StronglyMeasurable.indicator ?_ (hSm N)).aestronglyMeasurable
    exact (RCLike.continuous_ofReal.comp_stronglyMeasurable
      (hh'.norm.measurable.pow_const _).stronglyMeasurable).smul hh'
  have huLq : MemLp u q μ :=
    (memLp_top_of_bound hum.aestronglyMeasurable N
      (ae_of_all _ hu_le)).mono_exponent_of_measure_support_ne_top hu_supp
      (measure_spanningSets_lt_top μ N).ne le_top
  set X := eLpNorm u q μ with hX_def
  have hX : X ≠ ∞ := huLq.eLpNorm_lt_top.ne
  have hgX : eLpNorm g q' μ ≤ X ^ (r - 1) := by
    refine eLpNorm_le_eLpNorm_rpow (by linarith) hum.aestronglyMeasurable hgm ?_
      (ae_of_all _ hg_norm)
    rw [← ENNReal.HolderConjugate.sub_one_mul_inv q q' hq, ENNReal.ofReal_sub _ zero_le_one,
      ENNReal.ofReal_toReal hq, ENNReal.ofReal_one]
  have hgtop : MemLp g ∞ μ := by
    refine memLp_top_of_bound hgm ((N : ℝ) ^ (r - 1)) (ae_of_all _ fun x => ?_)
    exact (hg_norm x).trans (Real.rpow_le_rpow (norm_nonneg _) (hu_le x) (by linarith))
  -- The pairing of `h` with `g` is `‖u‖_q ^ q`.
  have hXr : X ^ r = ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ := by
    have hI : 0 ≤ ∫ x, ‖u x‖ ^ r ∂μ :=
      integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    rw [hX_def, huLq.eLpNorm_eq_integral_rpow_norm hq0 hq, ENNReal.ofReal_rpow_of_nonneg
      (Real.rpow_nonneg hI _) (by linarith), Real.rpow_inv_rpow hI (by linarith)]
    have heq : ∫ x, ⟪h x, g x⟫_𝕜 ∂μ = ((∫ x, ‖u x‖ ^ r ∂μ : ℝ) : 𝕜) := by
      rw [← integral_ofReal]
      refine integral_congr_ae ?_
      filter_upwards [hh.ae_eq_mk] with x hx
      rw [hx, hinner]
    rw [heq, ← ofReal_norm, RCLike.norm_ofReal, abs_of_nonneg hI]
  refine le_of_rpow_le_mul_rpow_sub_one hr1 hX ?_
  calc X ^ r = ‖∫ x, ⟪h x, g x⟫_𝕜 ∂μ‖ₑ := hXr
    _ ≤ C * eLpNorm g q' μ :=
        hC g (spanningSets μ N) (measure_spanningSets_lt_top μ N).ne hg_supp hgtop
    _ ≤ C * X ^ (r - 1) := by gcongr

end MeasureTheory
