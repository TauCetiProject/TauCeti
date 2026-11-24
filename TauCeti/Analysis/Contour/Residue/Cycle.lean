/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Basic
public import TauCeti.Analysis.Contour.PolarPart.Decomposition
import TauCeti.Analysis.Contour.HigherOrder.Asymptotics
import TauCeti.Analysis.Contour.Winding.Number.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Cycle.Circle
import TauCeti.Analysis.Contour.Cycle.HomologyCauchy
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# The classical residue theorem for an arbitrary null-homologous cycle

Let `U` be open, `S` a finite set and `f` complex differentiable on `U ∖ S`. For a contour cycle `C`
in `U`, **null-homologous** there, whose trace **avoids** `S`,

`Cycle.integral f C = 2πi · ∑_{s ∈ S} n_s(C) · Res_s f`,

and in particular, for one **closed, null-homologous** absolutely continuous curve `γ` in `U` that
avoids `S`,

`∫ t in a..b, γ' t • f (γ t) = 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`,

where `n_s` is the generalized winding number about `s`. The points of `S` in `U` are isolated
singularities of `f` of any kind (removable, poles or essential), and `Res_s f` is the order-`(−1)`
Laurent coefficient `TauCeti.Contour.residue f s`; nothing is asked of `f` at the points of `S`
outside `U`. This is the general arbitrary-cycle form of the classical residue theorem, and it
generalizes the circle theorem (`Contour.classicalResidueTheorem_circle`): the contour is an
arbitrary absolutely continuous loop, or a cycle of them, rather than a round circle, and each
singularity is weighted by its winding number rather than by `1`. Null-homology is not decoration —
on a general holomorphy domain `Ω`, a loop that merely avoids the singularities need not integrate
to the residue sum (a loop around a hole of `Ω` sees the function's behaviour there), so
`n_w(γ) = 0` for every `w ∉ Ω` is exactly the hypothesis that rules this out. Its `S = ∅` case is
the homology Cauchy theorem.

Absolute continuity is the natural regularity for the contour integral
`∫ t in a..b, γ' t • f (γ t)`: it makes `γ'` exist almost everywhere and be interval-integrable,
and makes `γ` the integral of `γ'`. Every piecewise-`C¹` curve is absolutely continuous
(`TauCeti.IsPiecewiseC1On.absolutelyContinuousOnInterval`).

The proof compares `C` with the cycle `∑_s n_s(C) · C(s, r)` of small circles about the points of
`S` in `U`. Both cycles are null-homologous in `U` and wind equally about every point of `S`, so
the homology Cauchy theorem on `U ∖ S` gives them the same integral
(`TauCeti.Contour.Cycle.integral_eq_of_windingNumber_eq`), and the integral around each small
circle is `2πi` times the residue (`TauCeti.Contour.residue_eq_circleIntegral`). The single-curve
theorem is the case of the one-generator cycle.

The file also integrates a polar-part decomposition along a closed curve. The decomposition
(`Contour.PolarPartDecomposition.ofMeromorphic`) writes `f = g + ∑_{s ∈ S} P_s` on `U ∖ S` for `f`
meromorphic at the points of `S`, with `g` differentiable on all of `U` and `P_s` the finite
Laurent tail at `s`. In each Laurent tail the simple-pole coefficient integrates to
`2πi · n_s(γ) · Res_s f`, by the very definition of the winding number (the principal value
collapses to an ordinary integral because `γ` misses `s`), while every coefficient of order `≥ 2`
integrates to zero around the closed curve, having the primitive `−(k−1)⁻¹(z − s)^{−(k−1)}`
(`Contour.integral_pow_inv_mul_deriv_eq_zero_of_closed`).

Unlike the Hungerbühler–Wasem generalized residue theorem
(`Contour.hungerbuhlerWasem_residueTheorem`), whose singularities may lie *on* the curve, nothing
here needs an immersion, a principal value, or the conditions (A′)/(B): with the singularities off
the contour every integral in sight is an ordinary interval integral. Conversely this statement is
*not* a specialization of the HW theorem, which asks for the strictly stronger
`Contour.IsPwC1ImmersionOn` regularity, so an absolutely continuous loop that is not a
piecewise-`C¹` immersion — one with a zero-speed seam, say — is covered here and not there.

## Main results

* `TauCeti.Contour.PolarPartDecomposition.intervalIntegral_deriv_smul_polarPart` — the contour
  integral of a polar part around such a curve is `2πi · n_s(γ) · Res_s f`.
* `PolarPartDecomposition.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum` — the residue
  sum splits off the contour integral without any null-homology hypothesis, the analytic
  remainder's integral being left standing.
* `PolarPartDecomposition.intervalIntegral_deriv_smul_eq_sum_windingNumber_mul_residue` — the
  residue theorem for a fixed decomposition, assuming nothing about `f` beyond it.
* `TauCeti.Contour.Cycle.classicalResidueTheorem_nullHomologous` — the residue theorem for a
  null-homologous cycle avoiding the singularities.
* `TauCeti.Contour.classicalResidueTheorem_nullHomologous` — the residue theorem for an arbitrary
  null-homologous closed curve avoiding the singularities.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), §3.
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI (the homology form of the residue theorem).
* J. B. Conway, *Functions of One Complex Variable I*, Chapter V, §2 (the residue theorem for
  isolated singularities).

## Provenance

No formal source is vendored: the statements are assembled here from the repository's homology
Cauchy theorem for cycles, circle Laurent coefficients, polar-part decomposition and antiderivative
lemma for higher-order Laurent terms, the last two migrated from the AINTLIB `LeanModularForms`
development.
-/
public section

open MeasureTheory Set Metric

open scoped Interval

namespace TauCeti.Contour

namespace PolarPartDecomposition

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- **The contour integral of a polar part is the winding-weighted residue.** Around a closed
absolutely continuous curve missing the pole `s`, the finite Laurent tail of `f` at `s` integrates
to `2πi · n_s(γ) · Res_s f`. -/
theorem intervalIntegral_deriv_smul_polarPart (decomp : PolarPartDecomposition f S U) (s : S)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (h_ne : ∀ t ∈ uIcc a b, γ t ≠ (s : ℂ)) :
    ∫ t in a..b, deriv γ t • decomp.polarPart s (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s * residue f s := by
  classical
  have hcont : ContinuousOn γ (uIcc a b) := hγ.continuousOn
  have hderiv : IntervalIntegrable (fun t => deriv γ t) volume a b :=
    hγ.intervalIntegrable_deriv_of_finiteDimensional
  have hne' : ∀ t ∈ uIcc a b, γ t - (s : ℂ) ≠ 0 := fun t ht => sub_ne_zero.mpr (h_ne t ht)
  -- The simple-pole coefficient contributes the index integral, `2πi` times the winding number;
  -- every higher-order coefficient contributes zero.
  have hindex : ∫ t in a..b, (γ t - (s : ℂ))⁻¹ * deriv γ t
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s := by
    rw [hγ.windingNumber_eq_integral fun ⟨t, ht, h⟩ ↦ h_ne t ht h,
      mul_inv_cancel_left₀ Complex.two_pi_I_ne_zero]
  have hterm : ∀ k : Fin (decomp.order s), IntervalIntegrable
      (fun t => decomp.coeff s k / (γ t - (s : ℂ)) ^ (k.val + 1) * deriv γ t) volume a b :=
    fun k => hderiv.continuousOn_mul (continuousOn_const.div
      ((hcont.sub continuousOn_const).pow _) fun t ht => pow_ne_zero _ (hne' t ht))
  have hsplit : ∫ t in a..b, deriv γ t • decomp.polarPart s (γ t)
      = ∑ k : Fin (decomp.order s),
          ∫ t in a..b, decomp.coeff s k / (γ t - (s : ℂ)) ^ (k.val + 1) * deriv γ t := by
    rw [← intervalIntegral.integral_finsetSum fun k _ => hterm k]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [smul_eq_mul, mul_comm, decomp.polarPart_eq s (γ t), Finset.sum_mul]
  have hval : ∀ k : Fin (decomp.order s),
      (∫ t in a..b, decomp.coeff s k / (γ t - (s : ℂ)) ^ (k.val + 1) * deriv γ t)
        = if k.val = 0 then
            decomp.coeff s k * (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s)
          else 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k.val with hk0 | hk_pos
    · rw [ite_eq_left hk0, ← hindex, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hk0]
      ring
    · rw [ite_eq_right (Nat.pos_iff_ne_zero.mp hk_pos)]
      exact integral_pow_inv_mul_deriv_eq_zero_of_closed (by omega) _ hγ hclosed h_ne
  rw [hsplit, Finset.sum_congr rfl fun k _ => hval k, decomp.sum_ite_coeff_eq_residue_mul s]
  ring

/-- **Splitting the contour integral off the residue sum.** Once `f` is presented on `U` as an
analytic remainder plus finite Laurent tails at the points of `S`, a closed absolutely continuous
curve in `U` avoiding `S` integrates to the remainder's integral plus the winding-weighted residue
sum.

No null-homology is assumed here, so the remainder's integral is left standing; discharging it is
what `intervalIntegral_deriv_smul_eq_sum_windingNumber_mul_residue` does for a null-homologous
curve. Keeping the two steps apart lets a cycle whose *generators* need not be null-homologous —
only the cycle as a whole — sum this identity over its support
(`TauCeti.Contour.Cycle.integral_eq_analyticRemainder_add_sum`).

Nothing is assumed about `f` beyond the decomposition itself: no differentiability or meromorphy
hypothesis appears, a decomposition already carrying everything the argument uses. When `decomp`
is obtained from `ofMeromorphic`, those hypotheses were consumed there. -/
theorem intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum
    (decomp : PolarPartDecomposition f S U) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hclosed : γ a = γ b) (hoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) :
    ∫ t in a..b, deriv γ t • f (γ t)
      = (∫ t in a..b, deriv γ t • decomp.analyticRemainder (γ t))
        + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s := by
  classical
  have hcont : ContinuousOn γ (uIcc a b) := hγ.continuousOn
  have hderiv : IntervalIntegrable (fun t => deriv γ t) volume a b :=
    hγ.intervalIntegrable_deriv_of_finiteDimensional
  have hne : ∀ s : S, ∀ t ∈ uIcc a b, γ t ≠ (s : ℂ) := fun s t ht h_eq =>
    hoff t ht (h_eq ▸ Finset.mem_coe.mpr s.property)
  have hpol_cont : ∀ s : S, ContinuousOn (fun t => decomp.polarPart s (γ t)) (uIcc a b) :=
    fun s => ContinuousOn.congr
      (continuousOn_finsetSum Finset.univ fun k _ => continuousOn_const.div
        ((hcont.sub continuousOn_const).pow (k.val + 1))
        fun t ht => pow_ne_zero _ (sub_ne_zero.mpr (hne s t ht)))
      fun t _ => decomp.polarPart_eq s (γ t)
  have hrem_int : IntervalIntegrable
      (fun t => deriv γ t • decomp.analyticRemainder (γ t)) volume a b :=
    hderiv.smul_continuousOn
      (decomp.analyticRemainder_differentiableOn.continuousOn.comp hcont hγU)
  have hpol_int : ∀ s ∈ S.attach, IntervalIntegrable
      (fun t => deriv γ t • decomp.polarPart s (γ t)) volume a b :=
    fun s _ => hderiv.smul_continuousOn (hpol_cont s)
  have hsum_int : IntervalIntegrable
      (fun t => ∑ s ∈ S.attach, deriv γ t • decomp.polarPart s (γ t)) volume a b := by
    have h := IntervalIntegrable.sum S.attach hpol_int
    rwa [Finset.sum_fn] at h
  have hf_eq : EqOn (fun t => deriv γ t • f (γ t))
      (fun t => deriv γ t • decomp.analyticRemainder (γ t)
        + ∑ s ∈ S.attach, deriv γ t • decomp.polarPart s (γ t)) (uIcc a b) := fun t ht => by
    simp only
    rw [decomp.f_eq (γ t) ⟨hγU t ht, hoff t ht⟩, smul_add, Finset.smul_sum]
  rw [intervalIntegral.integral_congr hf_eq, intervalIntegral.integral_add hrem_int hsum_int,
    intervalIntegral.integral_finsetSum hpol_int,
    Finset.sum_congr rfl fun s _ =>
      decomp.intervalIntegral_deriv_smul_polarPart s hγ hclosed (hne s),
    Finset.mul_sum, ← Finset.sum_attach S
      fun s => 2 * (Real.pi : ℂ) * Complex.I * (windingNumber γ a b s * residue f s)]
  exact congrArg _ (Finset.sum_congr rfl fun s _ => by ring)

/-- **The residue theorem for a fixed polar-part decomposition.** Once `f` is presented on `U` as
an analytic remainder plus finite Laurent tails at the points of `S`, a closed null-homologous
absolutely continuous curve in `U` avoiding `S` integrates to the winding-weighted residue sum. -/
theorem intervalIntegral_deriv_smul_eq_sum_windingNumber_mul_residue
    (decomp : PolarPartDecomposition f S U) (hU : IsOpen U) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hclosed : γ a = γ b) (hoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ))
    (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s := by
  rw [decomp.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum hγ hγU hclosed hoff,
    decomp.intervalIntegral_deriv_smul_analyticRemainder_eq_zero hU hγ hγU hclosed hnull, zero_add]

end PolarPartDecomposition

namespace Cycle

/-- **The residue theorem for a null-homologous cycle.** Let `U` be open, `S` a finite set and `f`,
with values in a complex normed space, differentiable on `U ∖ S`, and let `C` be a cycle in `U`,
**null-homologous** there, whose trace **avoids** `S`. Then

`Cycle.integral f C = 2πi · ∑_{s ∈ S} n_s(C) · Res_s f`,

each point weighted by the winding number of the cycle about it. Each point of `S` in `U` is an
isolated singularity of `f` of any kind (removable, a pole or essential), with its residue
`TauCeti.Contour.residue f s`; nothing is asked of `f` at the points of `S` outside `U`, whose
winding numbers vanish by null-homology. Its `S = ∅` case is the scalar homology Cauchy theorem
(`TauCeti.Contour.Cycle.homologyCauchyTheorem`). -/
theorem classicalResidueTheorem_nullHomologous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {S : Finset ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ))) {C : Cycle} (hCU : IsIn C U)
    (hoff : ∀ s ∈ S, s ∉ trace C) (hnull : IsNullHomologous C U) :
    integral f C = (2 * (Real.pi : ℂ) * Complex.I) • ∑ s ∈ S, windingNumber s C • residue f s := by
  classical
  -- Only the points of `S` in `U` count: the others have winding number `0`.
  set T := S.filter (· ∈ U)
  have hsum : ∑ s ∈ S, windingNumber s C • residue f s
      = ∑ s ∈ T, windingNumber s C • residue f s :=
    (Finset.sum_filter_of_ne fun s _ hs ↦ not_not.mp fun hsU ↦
      hs (by rw [isNullHomologous_iff.mp hnull s hsU, zero_smul])).symm
  have hTS : ∀ s ∈ T, s ∈ S := fun s hs ↦ (Finset.mem_filter.mp hs).1
  have hfT : DifferentiableOn ℂ f (U \ (↑T : Set ℂ)) := hf.mono fun z hz ↦
    ⟨hz.1, fun hzS ↦ hz.2 (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hzS, hz.1⟩))⟩
  -- Closed discs of a common radius `r` about the points of `T`, inside `U` and far apart.
  obtain ⟨r, hr, hrU, hsep⟩ := exists_pos_closedBall_subset_and_lt_dist (T := T)
    (U := fun _ ↦ U) fun w hw ↦ hU.mem_nhds (Finset.mem_filter.mp hw).2
  have hball : ∀ s ∈ T, closedBall s r ∩ (↑T : Set ℂ) ⊆ {s} := fun s hs z hz ↦
    eq_of_mem_closedBall_of_lt_dist (hsep z (Finset.mem_coe.mp hz.2) s hs) hz.1
  have hdisc : ∀ s ∈ T, closedBall s r \ {s} ⊆ U \ (↑T : Set ℂ) := fun s hs z hz ↦
    ⟨hrU s hs hz.1, fun hzT ↦ hz.2 (hball s hs ⟨hz.1, hzT⟩)⟩
  -- The winding numbers of `C` about the points of `T` are integers.
  choose! n hn using fun s (hs : s ∈ T) ↦
    exists_int_windingNumber_of_not_mem_trace C (hoff s (hTS s hs))
  -- `C` and the cycle `∑_{s ∈ T} n_s • C(s, r)` wind equally about every point of `T`.
  set D : Cycle := ∑ s ∈ T, n s • circleCycle s r
  have hcircle : ∀ s ∈ T, IsIn (circleCycle s r) (U \ (↑T : Set ℂ)) := fun s hs ↦ by
    rw [isIn_iff, trace_circleCycle, abs_of_pos hr]
    exact fun z hz ↦ hdisc s hs ⟨sphere_subset_closedBall hz, ne_of_mem_sphere hz hr.ne'⟩
  have hD : IsIn D (U \ (↑T : Set ℂ)) :=
    Finset.sum_induction _ (IsIn · _) (fun _ _ ↦ IsIn.add) (IsIn.zero _)
      fun s hs ↦ (hcircle s hs).zsmul _
  have hDU : IsNullHomologous D U :=
    Finset.sum_induction _ (IsNullHomologous · U) (fun _ _ ↦ IsNullHomologous.add)
      (IsNullHomologous.zero _) fun s hs ↦ IsNullHomologous.zsmul (isNullHomologous_iff.mpr
        fun z hz ↦ windingNumber_circleCycle_eq_zero_of_lt_dist hr.le (not_le.mp fun h ↦
          hz (hrU s hs (mem_closedBall.mpr h)))) _
  have hCD : ∀ z ∈ (↑T : Set ℂ), windingNumber z C = windingNumber z D := fun z hz ↦ by
    rw [windingNumber_sum_zsmul_circleCycle hr
      (fun w hw w' hw' hne ↦ (lt_two_mul_self hr).trans (hsep w hw w' hw' hne)) hz, hn z hz]
  have hC : IsIn C (U \ (↑T : Set ℂ)) := isIn_iff.mpr fun z hz ↦
    ⟨isIn_iff.mp hCU hz, fun hzT ↦ hoff z (hTS z hzT) hz⟩
  rw [integral_eq_of_windingNumber_eq hU T.finite_toSet.isClosed hfT hC hD hnull hDU hCD,
    map_sum, hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  -- Each circle integral is `2πi` times the residue.
  have hres := residue_eq_circleIntegral hr (hfT.mono (hdisc s hs))
  rw [map_zsmul, integral_circleCycle, hn s hs, hres]
  match_scalars
  field_simp

end Cycle

/-- **The classical residue theorem for an arbitrary null-homologous cycle.** Let `U` be open,
`S` a finite set and `f`, with values in a complex normed space, differentiable on `U ∖ S`, and let
`γ` be a closed absolutely continuous curve in `U`, **null-homologous** in `U`, that **avoids** `S`.
Then

`∫ t in a..b, γ' t • f (γ t) = 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`,

each point weighted by the generalized winding number of `γ` about it. Each point of `S` in `U` is
an isolated singularity of `f` of any kind, removable, a pole or essential; nothing at all is asked
of `f` at the points of `S` outside `U`, whose winding numbers vanish by null-homology. Likewise
`S` may list regular points of `f`, whose residues are `0`.

It is the one-generator case of the residue theorem for cycles
(`TauCeti.Contour.Cycle.classicalResidueTheorem_nullHomologous`). Its `S = ∅` case is the homology
Cauchy theorem (`Contour.homologyCauchyTheorem`); the round-circle case with the poles inside is
`Contour.classicalResidueTheorem_circle`, and the version admitting poles *on* the curve is the
Hungerbühler–Wasem theorem `Contour.hungerbuhlerWasem_residueTheorem`. -/
theorem classicalResidueTheorem_nullHomologous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {S : Finset ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ))) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • f (γ t)
      = (2 * (Real.pi : ℂ) * Complex.I) • ∑ s ∈ S, windingNumber γ a b s • residue f s := by
  have h := Cycle.classicalResidueTheorem_nullHomologous hU hf
    ((Cycle.isIn_of_raw_iff γ hγ hclosed U).mpr hγU)
    (fun s hs ↦ by
      rw [Cycle.trace_of_raw]
      rintro ⟨t, ht, rfl⟩
      exact hoff t ht (Finset.mem_coe.mpr hs))
    ((Cycle.isNullHomologous_of_raw_iff γ hγ hclosed U).mpr hnull)
  simpa only [Cycle.integral_of_raw, Cycle.windingNumber_of_raw] using h

end TauCeti.Contour

end
