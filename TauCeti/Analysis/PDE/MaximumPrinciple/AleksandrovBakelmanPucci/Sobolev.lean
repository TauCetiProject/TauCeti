/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# The Aleksandrov–Bakelman–Pucci estimate for strong solutions

Let `Ω` be a bounded open subset of `ℝⁿ = EuclideanSpace ℝ ι`, `n ≥ 1`, and let `u ∈ W^{2,n}(Ω)`
(the Sobolev space `TauCeti.Wkp` on all of `Ω`) have a representative `v` that is continuous on
`closure Ω`. Write `D²u` for the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`, so that
`(D²u eⱼ)ᵢ` is the weak derivative `∂ᵢ∂ⱼu`. Let `a` be a field of positive definite matrices on
`Ω` with `D* = (det a)^{1/n}`, and let `f` satisfy

`f ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu` almost everywhere in `Ω`,

so that `u` is a strong subsolution. If `m` bounds `v` on `frontier Ω`, the
Aleksandrov–Bakelman–Pucci estimate bounds `v` on `Ω` by

`v ≤ m + diam Ω / (n ωₙ^{1/n}) ‖f⁻ / D*‖_{Lⁿ(Γ⁺)}`,

where `Γ⁺` is the upper contact set of `v` on `Ω` and `ωₙ` is the volume of the unit ball
(Gilbarg–Trudinger, Theorem 9.1 without drift, for functions in `W^{2,n}(Ω)`). The coefficients
are assumed measurable, with `∑ᵢⱼ |aⁱʲ| ≤ K D*` on `Ω` for some constant `K`. This holds with
`K = n² Λ / λ` when `λ ‖ξ‖² ≤ ξ · a ξ` and `|aⁱʲ| ≤ Λ`, since then `det a ≥ λⁿ`; the constant `K`
does not enter the estimate. The measure form
`TauCeti.PDE.volume_ball_le_setLIntegral_upperContactSet_of_wkp` needs no integrability of `f`.

This is the maximum principle behind the Krylov–Safonov theory of non-divergence equations with
measurable coefficients, whose solutions are strong rather than classical.

## The approximation

The classical estimate `TauCeti.PDE.volume_ball_le_setLIntegral_upperContactSet` applies to
`C²` functions. Mollify `u` at radius `δₖ → 0` and apply it on the open sets
`Vₖ = {y | 2 δₖ < infDist y Ωᶜ}`, where the mollification `uₖ` is smooth with Hessian the
mollified weak Hessian (`TauCeti.Wkp.fderiv_gradient_smoothField_value`). Since `v` is uniformly
continuous on `closure Ω`, the `uₖ` converge to `v` uniformly on `Vₖ`, and on `frontier Vₖ` they
are at most `m` plus a small error. The right-hand sides converge as well:

* the principal parts `Fₖ = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼuₖ` differ from `F = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu` by at most
  `K D* ‖D²uₖ - D²u‖`, and `D²uₖ → D²u` in `Lⁿ`, so `‖Fₖ⁻ / D*‖_{Lⁿ(Γₖ)}` is at most
  `‖F⁻ / D*‖_{Lⁿ(Γₖ)}` plus a vanishing error, where `Γₖ` is the upper contact set of `uₖ` on
  `Vₖ`;
* a point lying in infinitely many `Γₖ` lies in the upper contact set of `v` on `Ω`
  (`TauCeti.PDE.mem_upperContactSet_of_frequently`), so by the reverse Fatou lemma
  (`TauCeti.limsup_eLpNorm_restrict_le`) the limit superior of `‖F⁻ / D*‖_{Lⁿ(Γₖ)}` is at most
  `‖F⁻ / D*‖_{Lⁿ(Γ⁺)}`.

Finally `F⁻ ≤ f⁻` almost everywhere. Neither the area formula nor the almost everywhere twice
differentiability of `W^{2,n}` functions is used.

## Main declarations

* `TauCeti.PDE.volume_ball_le_setLIntegral_upperContactSet_of_wkp`: the measure form
  `|B(0, (v x - m) / diam Ω)| ≤ ∫_{Γ⁺} (f⁻ / n)ⁿ / det a`.
* `TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow_of_wkp`: **the Aleksandrov–Bakelman–Pucci
  estimate** for strong subsolutions in `W^{2,n}(Ω) ∩ C(closure Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.1 (Lemmas 9.2 and 9.3, Theorem 9.1).
-/

public section

noncomputable section

open Filter Matrix Metric MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal Gradient RealInnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The principal part `∑ᵢⱼ Aᵢⱼ (T eⱼ)ᵢ` is at most `(∑ᵢⱼ |Aᵢⱼ|) ‖T‖` in absolute value. -/
private theorem abs_sum_mul_apply_single_le (A : Matrix ι ι ℝ)
    (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    |∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i| ≤ (∑ i, ∑ j, |A i j|) * ‖T‖ := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |T (EuclideanSpace.single j 1) i| ≤ ‖T (EuclideanSpace.single j 1)‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (T (EuclideanSpace.single j 1)) i
    _ ≤ ‖T‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := T.le_opNorm _
    _ = ‖T‖ := by simp

/-- The principal part `y ↦ ∑ᵢⱼ aⁱʲ(y) (T(y) eⱼ)ᵢ` of a measurable field of operators is
measurable. -/
private theorem aestronglyMeasurable_sum_mul_apply_single {μ : Measure (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    (ha : AEStronglyMeasurable a μ) (hT : AEStronglyMeasurable T μ) :
    AEStronglyMeasurable (fun y => ∑ i, ∑ j, a y i j * T y (EuclideanSpace.single j 1) i) μ := by
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  refine ((continuous_apply j).comp_aestronglyMeasurable
    ((continuous_apply i).comp_aestronglyMeasurable ha)).mul ?_
  exact ((EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous.comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ ι)
      (EuclideanSpace.single j (1 : ℝ))).continuous).comp_aestronglyMeasurable hT

/-- The quotient `F⁻ / (det a)^{1/n}` of measurable functions is measurable. -/
private theorem aestronglyMeasurable_negPart_div_det_rpow {μ : Measure (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {F : EuclideanSpace ℝ ι → ℝ}
    (ha : AEStronglyMeasurable a μ) (hF : AEStronglyMeasurable F μ) :
    AEStronglyMeasurable (fun y => (F y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) μ := by
  refine (continuous_negPart.comp_aestronglyMeasurable hF).aemeasurable.div ?_
    |>.aestronglyMeasurable
  exact ((Real.continuous_rpow_const (by positivity)).comp
    (continuous_id.matrix_det)).comp_aestronglyMeasurable ha |>.aemeasurable

/-- **The principal part under perturbation of the Hessian.** If `a` is positive definite with
`∑ᵢⱼ |aⁱʲ| ≤ K D*`, `D* = (det a)^{1/n}`, then replacing the operator `S` by `T` in the principal
part `P(S) = ∑ᵢⱼ aⁱʲ (S eⱼ)ᵢ` changes `P⁻ / D*` by at most `K ‖T - S‖`. -/
private theorem negPart_div_det_rpow_le {A : Matrix ι ι ℝ} (hA : A.PosDef) {K : ℝ}
    (hK : ∑ i, ∑ j, |A i j| ≤ K * A.det ^ (Fintype.card ι : ℝ)⁻¹)
    (T S : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    (∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i)⁻ / A.det ^ (Fintype.card ι : ℝ)⁻¹ ≤
      (∑ i, ∑ j, A i j * S (EuclideanSpace.single j 1) i)⁻ / A.det ^ (Fintype.card ι : ℝ)⁻¹ +
        K * ‖T - S‖ := by
  set PT := ∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i
  set PS := ∑ i, ∑ j, A i j * S (EuclideanSpace.single j 1) i
  set D := A.det ^ (Fintype.card ι : ℝ)⁻¹
  have hD : 0 < D := Real.rpow_pos_of_pos hA.det_pos _
  have hsub : PT - PS = ∑ i, ∑ j, A i j * (T - S) (EuclideanSpace.single j 1) i := by
    simp [PT, PS, ← Finset.sum_sub_distrib, mul_sub]
  have habs : |PT - PS| ≤ K * D * ‖T - S‖ := hsub ▸ (abs_sum_mul_apply_single_le A (T - S)).trans
    (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  have hneg : PT⁻ ≤ PS⁻ + K * D * ‖T - S‖ := by
    rw [negPart_def, negPart_def]
    exact max_le (by linarith [le_max_left (-PS) 0, neg_le_abs (PT - PS)])
      (by linarith [le_max_right (-PS) 0, abs_nonneg (PT - PS)])
  calc PT⁻ / D ≤ (PS⁻ + K * D * ‖T - S‖) / D := div_le_div_of_nonneg_right hneg hD.le
    _ = PS⁻ / D + K * ‖T - S‖ := by field_simp

/-! ### The approximating sequence -/

section Sequence

omit [DecidableEq ι]

/-- The radius `1 / (k + 1)` of the `k`th mollifier. -/
private def abpRadius (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

private theorem abpRadius_pos (k : ℕ) : 0 < abpRadius k := by
  unfold abpRadius
  positivity

private theorem tendsto_abpRadius : Tendsto abpRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The `k`th mollifier, a normalized bump of outer radius `abpRadius k`. -/
private def abpBump (k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ ι) :=
  ⟨abpRadius k / 2, abpRadius k, half_pos (abpRadius_pos k), half_lt_self (abpRadius_pos k)⟩

omit [Fintype ι] in
private theorem abpBump_rOut (k : ℕ) : (abpBump (ι := ι) k).rOut = abpRadius k :=
  rfl

/-- The open set of points at distance more than `2 abpRadius k` from the complement of `Ω`, on
which the `k`th mollification is compared with the classical estimate. -/
private def abpDomain (Ω : Set (EuclideanSpace ℝ ι)) (k : ℕ) : Set (EuclideanSpace ℝ ι) :=
  {y | 2 * abpRadius k < infDist y Ωᶜ}

private theorem isOpen_abpDomain (Ω : Set (EuclideanSpace ℝ ι)) (k : ℕ) :
    IsOpen (abpDomain Ω k) :=
  isOpen_lt continuous_const (continuous_infDist_pt _)

/-- At distance at least `2 abpRadius k` from `Ωᶜ`, the ball of radius `abpRadius k` lies in
`Ω`. -/
private theorem ball_subset_of_two_mul_abpRadius_le {Ω : Set (EuclideanSpace ℝ ι)} {k : ℕ}
    {y : EuclideanSpace ℝ ι} (hy : 2 * abpRadius k ≤ infDist y Ωᶜ) :
    ball y (abpRadius k) ⊆ Ω :=
  (ball_subset_ball (by linarith [abpRadius_pos k])).trans ball_infDist_compl_subset

private theorem closedBall_subset_of_mem_abpDomain {Ω : Set (EuclideanSpace ℝ ι)} {k : ℕ}
    {y : EuclideanSpace ℝ ι} (hy : y ∈ abpDomain Ω k) :
    closedBall y (abpBump (ι := ι) k).rOut ⊆ Ω :=
  (closedBall_subset_ball (by rw [abpBump_rOut]; linarith [abpRadius_pos k, hy.out])).trans
    ball_infDist_compl_subset

private theorem abpDomain_subset (Ω : Set (EuclideanSpace ℝ ι)) (k : ℕ) : abpDomain Ω k ⊆ Ω :=
  fun _ hy => closedBall_subset_of_mem_abpDomain hy
    (mem_closedBall_self (abpBump (ι := ι) k).rOut_pos.le)

/-- Every point of an open set `Ω` with nonempty complement lies in all but finitely many of the
sets `abpDomain Ω k`. -/
private theorem eventually_lt_infDist {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : IsOpen Ω)
    (hΩc : Ωᶜ.Nonempty) {y : EuclideanSpace ℝ ι} (hy : y ∈ Ω) (c : ℝ) :
    ∀ᶠ k in atTop, c * abpRadius k < infDist y Ωᶜ := by
  have hpos : 0 < infDist y Ωᶜ := (infDist_pos_iff_notMem_closure hΩc).1
    (by rwa [hΩ.isClosed_compl.closure_eq, notMem_compl_iff])
  exact (tendsto_abpRadius.const_mul c).eventually (gt_mem_nhds (by rwa [mul_zero]))

end Sequence

omit [DecidableEq ι] in
/-- The exponent `n = card ι` of the `Lⁿ` spaces is at least `1`, so `ι` is nonempty. -/
private theorem nonempty_of_one_le_card [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] : Nonempty ι :=
  Fintype.card_pos_iff.1 (by exact_mod_cast
    (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι)))

section Mollification

variable [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] {Ω : Opens (EuclideanSpace ℝ ι)}
  (u : Wkp volume Ω (Fintype.card ι) 2) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

/-- Where every bump centred near `y` stays in `Ω`, the classical principal part of the
mollification of `u` is the principal part of the mollified weak Hessian. -/
private theorem sum_mul_fderiv_fderiv_smoothField (phi : ContDiffBump (0 : EuclideanSpace ℝ ι))
    {y : EuclideanSpace ℝ ι} (hy : ∀ᶠ z in 𝓝 y, closedBall z phi.rOut ⊆ Ω) (A : Matrix ι ι ℝ) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ (Wkp.smoothField phi (Wkp.value 2 u))) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      ∑ i, ∑ j, A i j *
        Wkp.smoothField phi (Wkp.iteratedGradient 1 u) y (EuclideanSpace.single j 1) i := by
  have hc : ContDiffAt ℝ 2 (Wkp.smoothField phi (Wkp.value 2 u)) y :=
    (Wkp.contDiff_smoothField phi _).contDiffAt.of_le (by simp)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hc.isSymmSndFDerivAt (by simp), ← inner_hessianOperator_left, ← fderiv_gradient,
    Wkp.fderiv_gradient_smoothField_value u phi hy, EuclideanSpace.inner_single_right]
  simp

/-- **The classical estimate for a mollification.** Let `V` be open, with the bump `phi` centred at
any point of `V` contained in `Ω`. Then the classical Aleksandrov–Bakelman–Pucci measure estimate
holds on `V` for the mollification `uφ` of `u`, with right-hand side
`n⁻ⁿ ‖Fφ⁻ / D*‖ⁿ_{Lⁿ(Γ)}`, where `Fφ = ∑ᵢⱼ aⁱʲ (D²u)φ eⱼ · eᵢ` is the principal part of the
mollified weak Hessian and `Γ` is the upper contact set of `uφ` on `V`. -/
private theorem volume_ball_le_eLpNorm_smoothField
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (phi : ContDiffBump (0 : EuclideanSpace ℝ ι)) {V : Set (EuclideanSpace ℝ ι)}
    (hV : IsOpen V) (hVΩ : ∀ y ∈ V, closedBall y phi.rOut ⊆ Ω)
    (ha : ∀ y ∈ Ω, (a y).PosDef) (hmeas : AEStronglyMeasurable a (volume.restrict Ω)) {m : ℝ}
    (hm : ∀ z ∈ frontier V, Wkp.smoothField phi (Wkp.value 2 u) z ≤ m)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ V) :
    volume (ball (0 : EuclideanSpace ℝ ι)
        ((Wkp.smoothField phi (Wkp.value 2 u) x - m) / diam V)) ≤
      ENNReal.ofReal (((Fintype.card ι : ℝ) ^ Fintype.card ι)⁻¹) *
        eLpNorm (fun y => (∑ i, ∑ j, a y i j *
          Wkp.smoothField phi (Wkp.iteratedGradient 1 u) y (EuclideanSpace.single j 1) i)⁻ /
            (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
          (volume.restrict (upperContactSet (Wkp.smoothField phi (Wkp.value 2 u)) V)) ^
        Fintype.card ι := by
  have := nonempty_of_one_le_card (ι := ι)
  set w := Wkp.smoothField phi (Wkp.value 2 u)
  set G := Wkp.smoothField phi (Wkp.iteratedGradient 1 u)
  have hVsub : V ⊆ Ω := fun y hy => hVΩ y hy (mem_closedBall_self phi.rOut_pos.le)
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := Wkp.contDiff_smoothField phi _
  have hΓΩ : upperContactSet w V ⊆ Ω := (upperContactSet_subset).trans hVsub
  have hkey := volume_ball_le_setLIntegral_upperContactSet (hΩb.subset hVsub) hV
    hw.continuous.continuousOn (hw.contDiffOn.of_le (by simp))
    (a := a) (f := fun y => ∑ i, ∑ j, a y i j * G y (EuclideanSpace.single j 1) i)
    (fun y hy => ha y (hΓΩ hy))
    (fun y hy => (sum_mul_fderiv_fderiv_smoothField u phi
      (by filter_upwards [hV.mem_nhds (upperContactSet_subset hy)] using hVΩ) (a y)).ge)
    hm hx
  rwa [setLIntegral_ofReal_negPart_div_card_pow_div_det_eq
    ((ae_restrict_mem (measurableSet_upperContactSet hV (hw.contDiffOn.of_le
      (by simp)))).mono fun y hy => ha y (hΓΩ hy))
    (aestronglyMeasurable_negPart_div_det_rpow (hmeas.mono_measure
      (Measure.restrict_mono hΓΩ le_rfl))
      (aestronglyMeasurable_sum_mul_apply_single (hmeas.mono_measure
        (Measure.restrict_mono hΓΩ le_rfl))
        (Wkp.contDiff_smoothField phi _).continuous.aestronglyMeasurable))] at hkey

omit [DecidableEq ι] in
/-- **Uniform convergence of the mollifications.** If the value of `u` agrees on `Ω` with a
function `v` continuous on the compact set `closure Ω`, then for every `ε > 0` and all large `k`,
the `k`th mollification of `u` is within `ε` of `v` at every point at distance at least
`2 abpRadius k` from `Ωᶜ`. -/
private theorem eventually_dist_smoothField_le
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    {v : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn v (closure Ω))
    (hv : Wkp.value 2 u =ᵐ[volume.restrict Ω] v) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ y, 2 * abpRadius k ≤ infDist y (Ω : Set (EuclideanSpace ℝ ι))ᶜ →
      dist (Wkp.smoothField (abpBump k) (Wkp.value 2 u) y) (v y) ≤ ε := by
  obtain ⟨η, hη, hvη⟩ := Metric.uniformContinuousOn_iff.1
    (hΩb.isCompact_closure.uniformContinuousOn_of_continuous hcont) ε hε
  filter_upwards [tendsto_abpRadius.eventually (gt_mem_nhds hη)] with k hk y hy
  have hball := ball_subset_of_two_mul_abpRadius_le hy
  have hyΩ : y ∈ (Ω : Set (EuclideanSpace ℝ ι)) := hball (mem_ball_self (abpRadius_pos k))
  refine Wkp.dist_smoothField_le (abpBump k) hv (by rwa [abpBump_rOut]) fun z hz => ?_
  rw [abpBump_rOut] at hz
  exact (hvη z (subset_closure (hball hz)) y (subset_closure hyΩ)
    ((mem_ball.1 hz).trans hk)).le

omit [DecidableEq ι] in
/-- **The limit of the contact sets.** A point lying in the upper contact set of the `k`th
mollification on `abpDomain Ω k` for infinitely many `k` lies in the upper contact set of `v` on
`Ω`. -/
private theorem mem_upperContactSet_of_frequently_smoothField
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (hΩc : (Ω : Set (EuclideanSpace ℝ ι))ᶜ.Nonempty)
    {v : EuclideanSpace ℝ ι → ℝ} (hcont : ContinuousOn v (closure Ω))
    (hv : Wkp.value 2 u =ᵐ[volume.restrict Ω] v) {y : EuclideanSpace ℝ ι}
    (hy : ∃ᶠ k in atTop,
      y ∈ upperContactSet (Wkp.smoothField (abpBump k) (Wkp.value 2 u)) (abpDomain Ω k)) :
    y ∈ upperContactSet v Ω := by
  set w := fun k => Wkp.smoothField (abpBump k) (Wkp.value 2 u)
  have hyΩ : y ∈ (Ω : Set (EuclideanSpace ℝ ι)) :=
    hy.exists.elim fun k hk => abpDomain_subset _ k (upperContactSet_subset hk)
  obtain ⟨M, hM⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn hcont
  -- Pointwise convergence at the points of `Ω`.
  have hconv (z : EuclideanSpace ℝ ι) (hz : z ∈ (Ω : Set (EuclideanSpace ℝ ι))) :
      Tendsto (fun k => w k z) atTop (𝓝 (v z)) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [eventually_dist_smoothField_le u hΩb hcont hv (half_pos hε),
      eventually_lt_infDist Ω.isOpen hΩc hz 2] with k hk hkz
    exact (hk z hkz.le).trans_lt (half_lt_self hε)
  have hr : 0 < infDist y (Ω : Set (EuclideanSpace ℝ ι))ᶜ / 2 := by
    have := eventually_lt_infDist Ω.isOpen hΩc hyΩ 0
    simp only [zero_mul, eventually_const] at this
    positivity
  refine mem_upperContactSet_of_frequently (M := M + 1) hr ?_ (fun z hz => ?_) ?_ hconv hyΩ hy
  · filter_upwards [eventually_lt_infDist Ω.isOpen hΩc hyΩ 4] with k hk z hz
    have h := infDist_le_infDist_add_dist (x := y) (y := z) (s := (Ω : Set (EuclideanSpace ℝ ι))ᶜ)
    rw [mem_ball, dist_comm] at hz
    rw [abpDomain, mem_ofPred_eq]
    linarith
  · filter_upwards [eventually_lt_infDist Ω.isOpen hΩc hz 2] with k hk using hk
  · filter_upwards [eventually_dist_smoothField_le u hΩb hcont hv one_pos] with k hk z hz
    have h1 := hk z hz.out.le
    have h2 := hM z (subset_closure (abpDomain_subset _ k hz))
    rw [Real.dist_eq] at h1
    rw [Real.norm_eq_abs] at h2
    exact (abs_le.2 ⟨by linarith [abs_le.1 h1, abs_le.1 h2], by
      linarith [abs_le.1 h1, abs_le.1 h2]⟩ : |w k z| ≤ M + 1)

/-- **Comparison of the right-hand sides.** On every subset `S` of `Ω`, the `Lⁿ(S)` norm of
`Fφ⁻ / D*`, for the principal part `Fφ` of the mollified weak Hessian, exceeds that of `F⁻ / D*`,
for the principal part `F` of the weak Hessian, by at most `K` times the `Lⁿ` distance between
the mollified weak Hessian and the weak Hessian. -/
private theorem eLpNorm_negPart_smoothField_le (ha : ∀ y ∈ Ω, (a y).PosDef)
    (hmeas : AEStronglyMeasurable a (volume.restrict Ω)) {K : ℝ}
    (hK : ∀ y ∈ Ω, ∑ i, ∑ j, |a y i j| ≤ K * (a y).det ^ (Fintype.card ι : ℝ)⁻¹)
    (phi : ContDiffBump (0 : EuclideanSpace ℝ ι)) {S : Set (EuclideanSpace ℝ ι)}
    (hS : S ⊆ Ω) :
    eLpNorm (fun y => (∑ i, ∑ j, a y i j *
          Wkp.smoothField phi (Wkp.iteratedGradient 1 u) y (EuclideanSpace.single j 1) i)⁻ /
            (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι) (volume.restrict S) ≤
      eLpNorm (fun y => (∑ i, ∑ j, a y i j *
          Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)⁻ /
            (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι) (volume.restrict S) +
        ‖K‖ₑ * eLpNorm (Wkp.smoothField phi (Wkp.iteratedGradient 1 u) -
          (Ω : Set (EuclideanSpace ℝ ι)).indicator (Wkp.iteratedGradient 1 u))
          (Fintype.card ι) volume := by
  set D := Wkp.iteratedGradient 1 u
  set G := Wkp.smoothField phi D
  have hSΩ : ∀ᵐ y ∂(volume.restrict S), y ∈ (Ω : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_of_ae_restrict_of_subset hS (ae_restrict_mem Ω.isOpen.measurableSet)
  have hle : volume.restrict S ≤ volume.restrict Ω := Measure.restrict_mono hS le_rfl
  have hmS := hmeas.mono_measure hle
  have hDS : AEStronglyMeasurable (fun y => (D y : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι))
      (volume.restrict S) := (Lp.aestronglyMeasurable D).mono_measure hle
  calc _ ≤ eLpNorm (fun y => (∑ i, ∑ j, a y i j * D y (EuclideanSpace.single j 1) i)⁻ /
          (a y).det ^ (Fintype.card ι : ℝ)⁻¹ + K * ‖G y - D y‖) (Fintype.card ι)
          (volume.restrict S) := by
        refine eLpNorm_mono_ae_real (aestronglyMeasurable_negPart_div_det_rpow hmS
          (aestronglyMeasurable_sum_mul_apply_single hmS
            (Wkp.contDiff_smoothField phi D).continuous.aestronglyMeasurable)) ?_
        filter_upwards [hSΩ] with y hy
        rw [Real.norm_of_nonneg (div_nonneg (negPart_nonneg _)
          (Real.rpow_nonneg (ha y hy).det_pos.le _))]
        exact negPart_div_det_rpow_le (ha y hy) (hK y hy) (G y) (D y)
    _ ≤ _ := eLpNorm_add_le (Fact.out : (1 : ℝ≥0∞) ≤ Fintype.card ι)
    _ ≤ _ := by
        gcongr
        have hK' : (fun y => K * ‖G y - D y‖) = K • fun y => ‖G y - D y‖ := rfl
        rw [hK', eLpNorm_const_smul,
          eLpNorm_norm (fun y => G y - D y)
            ((Wkp.contDiff_smoothField phi D).continuous.aestronglyMeasurable.sub hDS)]
        gcongr
        refine (eLpNorm_congr_ae ?_).trans_le (eLpNorm_mono_measure _ Measure.restrict_le_self)
        filter_upwards [hSΩ] with y hy
        simp [Set.indicator_of_mem hy]

omit [DecidableEq ι] in
/-- **The right-hand sides on the contact sets.** If `g ∈ Lⁿ(Ω)`, then for every `c` above the
`Lⁿ` norm of `g` on the upper contact set of `v`, the `Lⁿ` norm of `g` on the upper contact set of
the `k`th mollification on `abpDomain Ω k` is below `c` for all large `k`. -/
private theorem eventually_eLpNorm_upperContactSet_lt
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (hΩc : (Ω : Set (EuclideanSpace ℝ ι))ᶜ.Nonempty) {v : EuclideanSpace ℝ ι → ℝ}
    (hcont : ContinuousOn v (closure Ω)) (hv : Wkp.value 2 u =ᵐ[volume.restrict Ω] v)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : MemLp g (Fintype.card ι) (volume.restrict Ω)) {c : ℝ≥0∞}
    (hc : eLpNorm g (Fintype.card ι) (volume.restrict (upperContactSet v Ω)) < c) :
    ∀ᶠ k in atTop, eLpNorm g (Fintype.card ι) (volume.restrict
      (upperContactSet (Wkp.smoothField (abpBump k) (Wkp.value 2 u)) (abpDomain Ω k))) < c := by
  have hsub : limsup (fun k => upperContactSet (Wkp.smoothField (abpBump k) (Wkp.value 2 u))
      (abpDomain Ω k)) atTop ⊆ upperContactSet v Ω := fun y hy =>
    mem_upperContactSet_of_frequently_smoothField u hΩb hΩc hcont hv
      (Filter.mem_limsup_iff_frequently_mem.1 hy)
  refine eventually_lt_of_limsup_lt ((limsup_eLpNorm_restrict_le
    (zero_lt_one.trans_le Fact.out).ne' (ENNReal.natCast_ne_top _) hg
    (fun k => measurableSet_upperContactSet (isOpen_abpDomain _ k)
      ((Wkp.contDiff_smoothField _ _).contDiffOn.of_le (by simp)))
    fun k => upperContactSet_subset.trans (abpDomain_subset _ k)).trans_lt ?_)
  exact (eLpNorm_mono_measure g (Measure.restrict_mono hsub le_rfl)).trans_lt hc

omit [DecidableEq ι] in
/-- The mollified weak Hessians converge to the extension by zero of the weak Hessian in `Lⁿ`. -/
private theorem tendsto_eLpNorm_smoothField_iteratedGradient_sub :
    Tendsto (fun k => eLpNorm (Wkp.smoothField (abpBump k) (Wkp.iteratedGradient 1 u) -
      (Ω : Set (EuclideanSpace ℝ ι)).indicator (Wkp.iteratedGradient 1 u)) (Fintype.card ι)
        volume) atTop (𝓝 0) := by
  simpa only [Wkp.smoothField_def] using tendsto_eLpNorm_normed_convolution_sub
    (ENNReal.natCast_ne_top _) (phi := abpBump)
    (by simpa only [abpBump_rOut] using tendsto_abpRadius)
    ((memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).2
      (Lp.memLp (Wkp.iteratedGradient 1 u)))

omit [DecidableEq ι] in
/-- **The boundary values of the mollifications.** If `v ≤ m` on `frontier Ω`, the mollification
is within `ε` of `v` at distance `2 abpRadius k` from `Ωᶜ`, and `v` varies by less than `ε` over
distances below `η > 2 abpRadius k` in `closure Ω`, then the mollification is at most `m + 2ε` on
`frontier (abpDomain Ω k)`. -/
private theorem smoothField_le_of_mem_frontier_abpDomain
    (hΩc : (Ω : Set (EuclideanSpace ℝ ι))ᶜ.Nonempty) {v : EuclideanSpace ℝ ι → ℝ} {m ε η : ℝ}
    (hm : ∀ z ∈ frontier (Ω : Set (EuclideanSpace ℝ ι)), v z ≤ m)
    (hvη : ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ ι)), ∀ z ∈ closure (Ω : Set _),
      dist y z < η → dist (v y) (v z) < ε) {k : ℕ} (hkη : 2 * abpRadius k < η)
    (hkU : ∀ y, 2 * abpRadius k ≤ infDist y (Ω : Set (EuclideanSpace ℝ ι))ᶜ →
      dist (Wkp.smoothField (abpBump k) (Wkp.value 2 u) y) (v y) ≤ ε)
    {z : EuclideanSpace ℝ ι} (hz : z ∈ frontier (abpDomain Ω k)) :
    Wkp.smoothField (abpBump k) (Wkp.value 2 u) z ≤ m + 2 * ε := by
  have hz' : 2 * abpRadius k = infDist z (Ω : Set (EuclideanSpace ℝ ι))ᶜ :=
    frontier_lt_subset_eq continuous_const (continuous_infDist_pt _) hz
  have hzΩ : z ∈ (Ω : Set (EuclideanSpace ℝ ι)) :=
    ball_subset_of_two_mul_abpRadius_le hz'.le (mem_ball_self (abpRadius_pos k))
  -- The nearest point of `Ωᶜ` lies on `frontier Ω`, where `v ≤ m`.
  obtain ⟨q, hq, hqd⟩ := exists_mem_frontier_infDist_compl_eq_dist hzΩ (nonempty_compl.1 hΩc)
  have h1 := hvη z (subset_closure hzΩ) q (frontier_subset_closure hq) (by
    rw [← hqd, ← hz']; exact hkη)
  have h2 := hkU z hz'.le
  rw [Real.dist_eq] at h1 h2
  linarith [abs_le.1 h1.le, abs_le.1 h2, hm q hq]

omit [DecidableEq ι] [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] in
/-- A nonempty bounded open set in a nontrivial normed space has positive diameter. -/
private theorem diam_pos_of_isOpen {s : Set (EuclideanSpace ℝ ι)} [Nonempty ι] (hs : IsOpen s)
    (hb : Bornology.IsBounded s) {x : EuclideanSpace ℝ ι} (hx : x ∈ s) : 0 < diam s := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hs x hx
  calc 0 < 2 * r := by positivity
    _ = diam (ball x r) := (diam_ball_eq x hr.le).symm
    _ ≤ diam s := diam_mono hball hb

/-- **The estimate up to `ε`.** With `F` the principal part of the weak Hessian and `Γ⁺` the upper
contact set of `v` on `Ω`, for every `ε > 0`,
`|B(0, (v x - m - 3ε) / diam Ω)| ≤ n⁻ⁿ (‖F⁻ / D*‖_{Lⁿ(Γ⁺)} + 2ε)ⁿ`. It is the classical estimate
for a mollification of `u` with a small enough radius. -/
private theorem volume_ball_le_add_of_wkp
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (hΩc : (Ω : Set (EuclideanSpace ℝ ι))ᶜ.Nonempty) {v : EuclideanSpace ℝ ι → ℝ}
    (hcont : ContinuousOn v (closure Ω)) (hv : Wkp.value 2 u =ᵐ[volume.restrict Ω] v)
    (ha : ∀ y ∈ Ω, (a y).PosDef) (hmeas : AEStronglyMeasurable a (volume.restrict Ω)) {K : ℝ}
    (hK : ∀ y ∈ Ω, ∑ i, ∑ j, |a y i j| ≤ K * (a y).det ^ (Fintype.card ι : ℝ)⁻¹)
    (hgΩ : MemLp (fun y => (∑ i, ∑ j, a y i j *
          Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)⁻ /
            (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι) (volume.restrict Ω))
    {m : ℝ} (hm : ∀ z ∈ frontier (Ω : Set (EuclideanSpace ℝ ι)), v z ≤ m)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ Ω) {ε : ℝ} (hε : 0 < ε) :
    volume (ball (0 : EuclideanSpace ℝ ι)
        ((v x - m - 3 * ε) / diam (Ω : Set (EuclideanSpace ℝ ι)))) ≤
      ENNReal.ofReal (((Fintype.card ι : ℝ) ^ Fintype.card ι)⁻¹) *
        (eLpNorm (fun y => (∑ i, ∑ j, a y i j *
          Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)⁻ /
            (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
          (volume.restrict (upperContactSet v Ω)) + ENNReal.ofReal (2 * ε)) ^
        Fintype.card ι := by
  have := nonempty_of_one_le_card (ι := ι)
  set w := fun k => Wkp.smoothField (abpBump k) (Wkp.value 2 u)
  set A := eLpNorm (fun y => (∑ i, ∑ j, a y i j *
    Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)⁻ /
      (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι) (volume.restrict (upperContactSet v Ω))
  have hA : A ≠ ∞ := ((eLpNorm_mono_measure _ (Measure.restrict_mono upperContactSet_subset
    le_rfl)).trans_lt hgΩ.eLpNorm_lt_top).ne
  have hE5 := ENNReal.Tendsto.const_mul (tendsto_eLpNorm_smoothField_iteratedGradient_sub u)
    (Or.inr (enorm_ne_top : ‖K‖ₑ ≠ ∞))
  rw [mul_zero] at hE5
  obtain ⟨η, hη, hvη⟩ := Metric.uniformContinuousOn_iff.1
    (hΩb.isCompact_closure.uniformContinuousOn_of_continuous hcont) ε hε
  -- Choose `k` large enough for all the approximations at once.
  obtain ⟨k, hk4, hk5, hkU, hkx, hkη⟩ :=
    ((eventually_eLpNorm_upperContactSet_lt u hΩb hΩc hcont hv hgΩ
      (ENNReal.lt_add_right hA (ENNReal.ofReal_pos.2 hε).ne')).and
    ((hE5.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).and
    ((eventually_dist_smoothField_le u hΩb hcont hv hε).and
    ((eventually_lt_infDist Ω.isOpen hΩc hx 2).and
    ((tendsto_abpRadius.const_mul 2).eventually
      (gt_mem_nhds (by rwa [mul_zero] : (2 : ℝ) * 0 < η))))))).exists
  have hxV : x ∈ abpDomain Ω k := hkx
  have hstep := volume_ball_le_eLpNorm_smoothField u hΩb (abpBump k) (isOpen_abpDomain _ k)
    (fun y hy => closedBall_subset_of_mem_abpDomain hy) ha hmeas
    (fun z hz => smoothField_le_of_mem_frontier_abpDomain u hΩc hm hvη hkη hkU hz) hxV
  refine (measure_mono ?_).trans (hstep.trans ?_)
  · -- Compare the radii: `v x - m - 3ε ≤ w x - (m + 2ε)` and `diam V ≤ diam Ω`.
    have hwx := hkU x hkx.le
    rw [Real.dist_eq] at hwx
    have hnum : v x - m - 3 * ε ≤ w k x - (m + 2 * ε) := by linarith [abs_le.1 hwx]
    rcases le_or_gt (v x - m - 3 * ε) 0 with hneg | hpos
    · rw [ball_eq_empty.2 (div_nonpos_of_nonpos_of_nonneg hneg diam_nonneg)]
      exact empty_subset _
    have hVΩ := abpDomain_subset (Ω : Set (EuclideanSpace ℝ ι)) k
    refine ball_subset_ball ((div_le_div_of_nonneg_right hnum diam_nonneg).trans
      (div_le_div_of_nonneg_left (by linarith) (diam_pos_of_isOpen (isOpen_abpDomain _ k)
        (hΩb.subset hVΩ) hxV) (diam_mono hVΩ hΩb)))
  · gcongr
    calc _ ≤ _ := eLpNorm_negPart_smoothField_le u ha hmeas hK (abpBump k)
          (S := upperContactSet (w k) (abpDomain Ω k))
          (upperContactSet_subset.trans (abpDomain_subset _ k))
      _ ≤ A + ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add hk4.le hk5.le
      _ = A + ENNReal.ofReal (2 * ε) := by
          rw [add_assoc, ← ENNReal.ofReal_add hε.le hε.le, two_mul]

/-- On `Ω`, `F⁻ / D* ≤ K ‖D²u‖` for the principal part `F` of the weak Hessian, so
`F⁻ / D* ∈ Lⁿ(Ω)`. -/
private theorem memLp_negPart_div_det_rpow (ha : ∀ y ∈ Ω, (a y).PosDef)
    (hmeas : AEStronglyMeasurable a (volume.restrict Ω)) {K : ℝ}
    (hK : ∀ y ∈ Ω, ∑ i, ∑ j, |a y i j| ≤ K * (a y).det ^ (Fintype.card ι : ℝ)⁻¹) :
    MemLp (fun y => (∑ i, ∑ j, a y i j *
      Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)⁻ /
        (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι) (volume.restrict Ω) := by
  set D := Wkp.iteratedGradient 1 u
  refine MemLp.of_le ((Lp.memLp D).norm.const_mul K) (aestronglyMeasurable_negPart_div_det_rpow
    hmeas (aestronglyMeasurable_sum_mul_apply_single hmeas (Lp.aestronglyMeasurable D))) ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
  have h := negPart_div_det_rpow_le (ha y hy) (hK y hy) (D y) 0
  simp only [_root_.zero_apply, PiLp.zero_apply, mul_zero, Finset.sum_const_zero,
    negPart_zero, zero_div, zero_add, sub_zero] at h
  rw [Real.norm_of_nonneg (div_nonneg (negPart_nonneg _)
    (Real.rpow_nonneg (ha y hy).det_pos.le _)), Real.norm_eq_abs]
  exact h.trans (le_abs_self _)

/-- On a subset `Γ` of `Ω`, the right-hand side `n⁻ⁿ ‖F⁻ / D*‖ⁿ_{Lⁿ(Γ)}` written with the principal
part `F` of the weak Hessian is at most `∫_Γ (f⁻ / n)ⁿ / det a` for every `f ≤ F`. -/
private theorem mul_eLpNorm_pow_le_setLIntegral (ha : ∀ y ∈ Ω, (a y).PosDef)
    (hmeas : AEStronglyMeasurable a (volume.restrict Ω)) {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ᵐ y ∂(volume.restrict Ω),
      f y ≤ ∑ i, ∑ j, a y i j * Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)
    {Γ : Set (EuclideanSpace ℝ ι)} (hΓ : Γ ⊆ Ω) :
    ENNReal.ofReal (((Fintype.card ι : ℝ) ^ Fintype.card ι)⁻¹) *
        eLpNorm (fun y => (∑ i, ∑ j, a y i j *
          Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)⁻ /
            (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι) (volume.restrict Γ) ^
          Fintype.card ι ≤
      ∫⁻ y in Γ, ENNReal.ofReal (((f y)⁻ / Fintype.card ι) ^ Fintype.card ι / (a y).det) := by
  have := nonempty_of_one_le_card (ι := ι)
  have hle : volume.restrict Γ ≤ volume.restrict Ω := Measure.restrict_mono hΓ le_rfl
  rw [← setLIntegral_ofReal_negPart_div_card_pow_div_det_eq
    (ae_restrict_of_ae_restrict_of_subset hΓ
      ((ae_restrict_mem Ω.isOpen.measurableSet).mono ha))
    (aestronglyMeasurable_negPart_div_det_rpow (hmeas.mono_measure hle)
      (aestronglyMeasurable_sum_mul_apply_single (hmeas.mono_measure hle)
        ((Lp.aestronglyMeasurable _).mono_measure hle)))]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hΓ hf] with y hy
  rcases le_or_gt (a y).det 0 with hd | hd
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonneg_of_nonpos
      (pow_nonneg (div_nonneg (negPart_nonneg _) (Nat.cast_nonneg _)) _) hd)]
    exact zero_le
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hd.le)
  refine pow_le_pow_left₀ (div_nonneg (negPart_nonneg _) (Nat.cast_nonneg _))
    (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) _
  rw [negPart_def, negPart_def]
  exact max_le_max (neg_le_neg hy) le_rfl

omit [DecidableEq ι] [Fact (1 ≤ (Fintype.card ι : ℝ≥0∞))] in
/-- **Letting `ε → 0`.** If `0 < t / d` with `d > 0` and
`|B(0, (t - 3ε) / d)| ≤ C (A + 2ε)ⁿ` for every `ε > 0`, then `|B(0, t / d)| ≤ C Aⁿ`. -/
private theorem volume_ball_le_of_forall_pos {t d : ℝ} (hR : 0 < t / d) {C A : ℝ≥0∞}
    (hC : C ≠ ∞) (h : ∀ ε : ℝ, 0 < ε → volume (ball (0 : EuclideanSpace ℝ ι) ((t - 3 * ε) / d)) ≤
      C * (A + ENNReal.ofReal (2 * ε)) ^ Fintype.card ι) :
    volume (ball (0 : EuclideanSpace ℝ ι) (t / d)) ≤ C * A ^ Fintype.card ι := by
  have hrad : Tendsto (fun ε : ℝ => (t - 3 * ε) / d) (𝓝 0) (𝓝 (t / d)) := by
    have hc : Continuous fun ε : ℝ => (t - 3 * ε) / d := by fun_prop
    simpa using hc.tendsto 0
  -- For small `ε` the radius is positive, and the volume is `((t - 3ε) / d)ⁿ ωₙ`.
  have hL : Tendsto (fun ε : ℝ => volume (ball (0 : EuclideanSpace ℝ ι) ((t - 3 * ε) / d)))
      (𝓝[>] 0) (𝓝 (volume (ball (0 : EuclideanSpace ℝ ι) (t / d)))) := by
    rw [Measure.addHaar_ball_of_pos _ _ hR]
    refine Tendsto.congr' ?_ ((ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (hrad.pow _))
      (Or.inr measure_ball_lt_top.ne)).mono_left nhdsWithin_le_nhds)
    filter_upwards [(hrad.eventually (lt_mem_nhds hR)).filter_mono nhdsWithin_le_nhds]
      with ε hε
    rw [Measure.addHaar_ball_of_pos _ _ hε]
  have hRt : Tendsto (fun ε : ℝ => C * (A + ENNReal.ofReal (2 * ε)) ^ Fintype.card ι)
      (𝓝[>] 0) (𝓝 (C * A ^ Fintype.card ι)) := by
    have hc : Continuous fun ε : ℝ => ENNReal.ofReal (2 * ε) :=
      ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
    have h1 : Tendsto (fun ε : ℝ => A + ENNReal.ofReal (2 * ε)) (𝓝 0) (𝓝 A) := by
      simpa using tendsto_const_nhds.add (hc.tendsto 0)
    exact (ENNReal.Tendsto.const_mul (((ENNReal.continuous_pow _).tendsto A).comp h1)
      (Or.inr hC)).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hL hRt (eventually_nhdsWithin_of_forall h)

/-! ### The estimate -/

/-- **The Aleksandrov–Bakelman–Pucci estimate for strong subsolutions, measure form**
(Gilbarg–Trudinger, Lemma 9.3 for `W^{2,n}` functions, without drift). Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be
bounded and open, let `u ∈ W^{2,n}(Ω)` agree almost everywhere on `Ω` with a function `v`
continuous on `closure Ω`, and let `m` bound `v` on `frontier Ω`. Let `a` be measurable on `Ω`,
with `a y` positive definite and `∑ᵢⱼ |aⁱʲ(y)| ≤ K (det a(y))^{1/n}` at every `y ∈ Ω`, and let
`f ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu` almost everywhere on `Ω`. Then for `x ∈ Ω`,
`|B(0, (v x - m) / diam Ω)| ≤ ∫_{Γ⁺} (f⁻ / n)ⁿ / det a`, where `Γ⁺` is the upper contact set of
`v` on `Ω`. -/
theorem volume_ball_le_setLIntegral_upperContactSet_of_wkp
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) {v : EuclideanSpace ℝ ι → ℝ}
    (hcont : ContinuousOn v (closure Ω)) (hv : Wkp.value 2 u =ᵐ[volume.restrict Ω] v)
    (ha : ∀ y ∈ Ω, (a y).PosDef) (hmeas : AEStronglyMeasurable a (volume.restrict Ω)) {K : ℝ}
    (hK : ∀ y ∈ Ω, ∑ i, ∑ j, |a y i j| ≤ K * (a y).det ^ (Fintype.card ι : ℝ)⁻¹)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : ∀ᵐ y ∂(volume.restrict Ω),
      f y ≤ ∑ i, ∑ j, a y i j * Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)
    {m : ℝ} (hm : ∀ z ∈ frontier (Ω : Set (EuclideanSpace ℝ ι)), v z ≤ m)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ Ω) :
    volume (ball (0 : EuclideanSpace ℝ ι) ((v x - m) / diam (Ω : Set (EuclideanSpace ℝ ι)))) ≤
      ∫⁻ y in upperContactSet v Ω,
        ENNReal.ofReal (((f y)⁻ / Fintype.card ι) ^ Fintype.card ι / (a y).det) := by
  have := nonempty_of_one_le_card (ι := ι)
  have hΩc : (Ω : Set (EuclideanSpace ℝ ι))ᶜ.Nonempty := nonempty_compl.2 fun h =>
    NormedSpace.unbounded_univ ℝ (EuclideanSpace ℝ ι) (h ▸ hΩb)
  refine le_trans ?_ (mul_eLpNorm_pow_le_setLIntegral u ha hmeas hf upperContactSet_subset)
  rcases le_or_gt (v x) m with hvm | hvm
  · rw [ball_eq_empty.2 (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hvm) diam_nonneg),
      measure_empty]
    exact zero_le
  exact volume_ball_le_of_forall_pos (div_pos (sub_pos.2 hvm)
    (diam_pos_of_isOpen Ω.isOpen hΩb hx)) ENNReal.ofReal_ne_top fun ε hε =>
      volume_ball_le_add_of_wkp u hΩb hΩc hcont hv ha hmeas hK
        (memLp_negPart_div_det_rpow u ha hmeas hK) hm hx hε

/-- **The Aleksandrov–Bakelman–Pucci estimate for strong subsolutions** (Gilbarg–Trudinger,
Theorem 9.1 for `W^{2,n}` functions, without drift). Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be bounded and open,
let `u ∈ W^{2,n}(Ω)` agree almost everywhere on `Ω` with a function `v` continuous on
`closure Ω`, and let `m` bound `v` on `frontier Ω`. Let `a` be measurable on `Ω`, with `a y`
positive definite and `∑ᵢⱼ |aⁱʲ(y)| ≤ K D*(y)` at every `y ∈ Ω`, where `D* = (det a)^{1/n}`, and
let `f ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu` almost everywhere on `Ω`, with `f⁻ / D* ∈ Lⁿ(Γ⁺)` on the upper contact
set `Γ⁺` of `v`. Then on `Ω`, `v ≤ m + diam Ω / (n ωₙ^{1/n}) ‖f⁻ / D*‖_{Lⁿ(Γ⁺)}`, where `ωₙ`
is the volume of the unit ball. -/
theorem le_add_mul_eLpNorm_negPart_div_det_rpow_of_wkp
    (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) {v : EuclideanSpace ℝ ι → ℝ}
    (hcont : ContinuousOn v (closure Ω)) (hv : Wkp.value 2 u =ᵐ[volume.restrict Ω] v)
    (ha : ∀ y ∈ Ω, (a y).PosDef) (hmeas : AEStronglyMeasurable a (volume.restrict Ω)) {K : ℝ}
    (hK : ∀ y ∈ Ω, ∑ i, ∑ j, |a y i j| ≤ K * (a y).det ^ (Fintype.card ι : ℝ)⁻¹)
    {f : EuclideanSpace ℝ ι → ℝ} (hf : ∀ᵐ y ∂(volume.restrict Ω),
      f y ≤ ∑ i, ∑ j, a y i j * Wkp.iteratedGradient 1 u y (EuclideanSpace.single j 1) i)
    (hg : MemLp (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
      (volume.restrict (upperContactSet v Ω)))
    {m : ℝ} (hm : ∀ z ∈ frontier (Ω : Set (EuclideanSpace ℝ ι)), v z ≤ m)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ Ω) :
    v x ≤ m + diam (Ω : Set (EuclideanSpace ℝ ι)) / (Fintype.card ι *
        (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (Fintype.card ι : ℝ)⁻¹) *
      (eLpNorm (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
        (volume.restrict (upperContactSet v Ω))).toReal := by
  have := nonempty_of_one_le_card (ι := ι)
  exact le_add_mul_eLpNorm_negPart_div_det_rpow_of_volume_ball_le hΩb Ω.isOpen hx
    (ae_restrict_of_ae_restrict_of_subset upperContactSet_subset
      ((ae_restrict_mem Ω.isOpen.measurableSet).mono ha)) hg
    (volume_ball_le_setLIntegral_upperContactSet_of_wkp u hΩb hcont hv ha hmeas hK hf hm hx)

end Mollification

end PDE

end TauCeti
