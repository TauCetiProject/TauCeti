/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Prod
import Mathlib.Analysis.Asymptotics.Completion
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Calculus.FDeriv.Add
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Strip
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.MeasureTheory.Integral.IntervalIntegral.CauchySchwarz
import TauCeti.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip
import TauCeti.Topology.Connected.MetricSpace
import TauCeti.Topology.Connected.TotallyDisconnected
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.OmegaLimit
import TauCeti.Topology.UniformSpace.UniformConvergence.Bounded
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# Loops with square-integrable defect accumulate at, and converge to, periodic orbits

Let `X : ℝ → V → V` be a continuous time-dependent vector field on a real normed space,
`1`-periodic in time, and let `u : ℝ × ℝ → V` be a `C¹` map on the half-cylinder `s > a`
whose loops `t ↦ u(s, t)` are `1`-periodic and stay in a compact set. Measure how far the loop at
`s` is from solving `x' = X(t, x)` by the *defect* `∂_t u(s, t) - X(t, u(s, t))`. If the square of
its norm has finite integral over the half-cylinder `(a, ∞) × [0, 1]`, then:

* there are `s_n → ∞` along which the `L²` norm of the defect over the loop tends to `0`
  (`TauCeti.exists_tendsto_integral_norm_sq_sliceDefect`);
* along any such sequence, a subsequence of the loops `t ↦ u(s_n, t)` converges uniformly to a
  `1`-periodic solution of `x' = X(t, x)`
  (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral`).

Together these give a periodic solution and a sequence `s_n → ∞` along which the loops converge
to it uniformly (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top`).
The second statement holds as well for any sequence of `C¹`, `1`-periodic loops `γ_n` in `K`, not
necessarily the loops of one map, whose defects `γ_n' - X(t, γ_n)` tend to `0` in `L²`
(`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral_deriv_sub`).
The same results apply on a half-cylinder `s < a` through the reflected map `(s, t) ↦ u(-s, t)`,
which has the same loops and the same squared defect integral
(`TauCeti.setLIntegral_norm_sq_sliceDefect_comp_neg_fst`).

The convergence of a subsequence of loops, and the passage of the integral equation to the limit
behind it, hold more generally for a sequence of maps `u n`, each `C¹` on its own half-cylinder
`s > a n`, with loops at times `s_n`. This is the form needed for a sequence of Floer cylinders,
whose loops are taken in the necks of the different cylinders. To locate a loop of small defect in
a window `[σ, τ]`, `TauCeti.exists_mem_Icc_integral_norm_sq_sliceDefect_lt` finds one whose squared
defect integral is below the average over the window; so if the squared defect integrals over
windows `[σ k, σ k + ℓ]` tend to `0`, there are loops in the windows whose `L²` defects tend to `0`
(`TauCeti.exists_mem_Icc_tendsto_integral_norm_sq_sliceDefect`).

The second statement is an application of the Arzelà–Ascoli theorem, in the form for periodic
loops with a common modulus of continuity
(`TauCeti.exists_tendstoUniformly_subseq_of_periodic_of_modulus`): by the Cauchy–Schwarz
inequality (`TauCeti.integral_le_sqrt_mul_sqrt_integral_sq`), once the squared defect integrals
are at most `1` the loops have the common modulus of continuity `B h + √h`, where `B` bounds `X`
on the compact set, and the integral equation `x(t) - x(0) = ∫₀ᵗ X(τ, x(τ)) dτ` passes to the limit
because the integral of the defect tends to `0`
(`TauCeti.sub_eq_integral_of_tendsto_integral_norm_sq_sliceDefect`, which, like
`TauCeti.sub_eq_integral_add_integral_sliceDefect`, requires `V` to be complete). The periodic-orbit
theorems below do not assume completeness of `V`: their proofs apply the same argument to the
integrals after composing with the embedding of `V` into its completion, through private helpers.

This is the step of the asymptotic analysis of Floer trajectories that produces the periodic orbit
at an end: for a solution of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on a
cylindrical end, the defect is `J ∂_s u`, and its square integral is controlled by the energy.
No regularity beyond `C¹`, and no bound on the derivative of `u`, is assumed for these statements.

If the derivative of `u` is bounded by `C` — for which a bound on `(a, ∞) × [0, 1]` suffices when
the loops are `1`-periodic (`TauCeti.norm_fderiv_le_of_periodic`) — the loops depend `C`-Lipschitz
continuously on `s` in the uniform distance and form a compact family by the Arzelà–Ascoli theorem.
For every `ε > 0` and every late `s` some loop at a time in `[s, s + ε]` has squared defect
integral below `ε` (`TauCeti.eventually_exists_mem_Icc_integral_norm_sq_sliceDefect_lt`), so every
cluster point of the loops in the topology of uniform convergence is approached by loops at
`σ_n → ∞` with defect tending to zero (`TauCeti.exists_tendstoUniformly_of_mapClusterPt`) and is a
`1`-periodic solution (`TauCeti.periodic_and_hasDerivAt_of_mapClusterPt`). These cluster points form
the ω-limit set of a continuous curve in a compact set, which is preconnected. If the `1`-periodic
solutions in `K` that arise as uniform cluster points of the loops are isolated from each other in
the uniform distance, it is therefore a single solution `x`, and the loops converge uniformly to
`x` as `s → ∞` (`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_mapClusterPt` and
`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atTop`). This is how nondegeneracy of the
periodic orbits in the end's homotopy sector turns the accumulation along a sequence into
convergence along the whole end.

The defect does not see the direction of `s`, so reflecting `(s, t) ↦ (-s, t)` gives the same
statements on a half-cylinder `s < a` at the negative end `s → -∞`
(`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_Iio_ne_top` and
`TauCeti.exists_periodic_hasDerivAt_tendstoUniformly_atBot`). For the Floer equation this is the
output end of a Floer trajectory or of a pair of pants.

The same compactness gives estimates that are uniform in the loops and in the length of the
cylinder, as needed along the necks of a breaking sequence of Floer cylinders:

* every `C¹` periodic loop in `K` with small enough defect is uniformly close to a periodic
  solution in `K` (`TauCeti.exists_pos_forall_exists_periodic_hasDerivAt_dist_lt`);
* if the periodic solutions in `K` are isolated, they are uniformly separated: two of them that are
  uniformly close coincide (`TauCeti.exists_pos_forall_eq_of_forall_dist_lt`);
* hence, for loops with derivative bounded by `C`, if the squared defect integrates to less than a
  constant `δ` over a strip `(a, b) × [0, 1]`, then all loops at `s ∈ [a + η, b - η]` are uniformly
  close to one single periodic solution, with `δ` and the margin `η` independent of the map and of
  `b - a` (`TauCeti.exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt`).

Conversely, at an end along which the loops of `u` converge uniformly to a continuous loop `x`
and the defect tends uniformly to zero, the slice velocity `∂_t u` converges uniformly to
`t ↦ X(t, x(t))` (`TauCeti.tendstoUniformlyOn_fderiv_apply_of_sliceDefect`), so `u` and `∂_t u`
are bounded on the strip when this holds at both ends
(`TauCeti.exists_forall_norm_le_and_norm_fderiv_apply_le_of_sliceDefect`). Both conditions pass
from two `C¹` maps to every point `u + μ (u' - u)` of the segment between them
(`TauCeti.tendstoUniformlyOn_add_smul_sub_and_sliceDefect`), and the defect condition passes to
every continuous vector field that agrees with `X` along `x`
(`TauCeti.tendstoUniformlyOn_sliceDefect_of_apply_eq`). These are the asymptotics along which the
linearized Floer operator is deformed.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, the convergence of finite-energy Floer trajectories to periodic
  orbits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology.
-/

public section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal UniformConvergence

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {X : ℝ → V → V} {u : ℝ × ℝ → V} {a : ℝ}

/-- If a map is continuous on a set `U` containing the line `{s} × ℝ`, its loop `t ↦ f(s, t)` is
continuous. -/
theorem continuous_slice_of_continuousOn {Y : Type*} [TopologicalSpace Y] {f : ℝ × ℝ → Y}
    {U : Set (ℝ × ℝ)} (hf : ContinuousOn f U) {s : ℝ} (hsU : ∀ t, (s, t) ∈ U) :
    Continuous fun t ↦ f (s, t) :=
  hf.comp_continuous (continuous_const.prodMk continuous_id) hsU

/-- The defect `∂_t u(z) - X(t, u(z))` of a map `u` from solving the time-dependent equation
`x' = X(t, x)` along its `t`-slices, at `z = (s, t)`. -/
noncomputable def sliceDefect (X : ℝ → V → V) (u : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  fderiv ℝ u z (0, 1) - X z.2 (u z)

theorem sliceDefect_def (X : ℝ → V → V) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    sliceDefect X u z = fderiv ℝ u z (0, 1) - X z.2 (u z) :=
  (rfl)

/-- The map `(s, t) ↦ x(t)` constant in `s` along a solution of `x' = X(t, x)` has vanishing
defect. -/
theorem sliceDefect_comp_snd_eq_zero {x : ℝ → V} (hx : ∀ t, HasDerivAt x (X t (x t)) t) :
    sliceDefect X (fun w : ℝ × ℝ ↦ x w.2) = 0 := by
  funext z
  obtain ⟨s, t⟩ := z
  have h : HasFDerivAt (fun w : ℝ × ℝ ↦ x w.2)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (X t (x t))).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) (s, t) :=
    (hx t).hasFDerivAt.comp (s, t) (hasFDerivAt_snd (p := (s, t)))
  simp [sliceDefect_def, h.fderiv]

/-- The defect of a map that is `C¹` on an open set `U` is continuous on `U`, for a continuous
vector field. -/
theorem continuousOn_sliceDefect {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U)
    (hX : Continuous (uncurry X)) : ContinuousOn (sliceDefect X u) U :=
  ((hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).sub <|
    hX.comp_continuousOn (continuousOn_snd.prodMk hu.continuousOn)

/-- The defect along the loop at `s` of a map that is `C¹` on an open set containing the line
`{s} × ℝ` is continuous in `t`. -/
theorem continuous_sliceDefect_slice {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U)
    (hX : Continuous (uncurry X)) {s : ℝ} (hsU : ∀ t, (s, t) ∈ U) :
    Continuous fun t ↦ sliceDefect X u (s, t) :=
  continuous_slice_of_continuousOn (continuousOn_sliceDefect hU hu hX) hsU

/-- The squared norm of the defect along the loop at `s` of a map that is `C¹` on an open set
containing the line `{s} × ℝ` is continuous in `t`. -/
theorem continuous_norm_sliceDefect_sq {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hX : Continuous (uncurry X)) {s : ℝ} (hsU : ∀ t, (s, t) ∈ U) :
    Continuous fun t ↦ ‖sliceDefect X u (s, t)‖ ^ 2 :=
  (continuous_sliceDefect_slice hU hu hX hsU).norm.pow 2

/-- Along the loop at `s > a`, a map differentiable on the half-cylinder has `t`-derivative
`X(t, u(s, t))` plus the defect. -/
theorem hasDerivAt_slice_add_sliceDefect (hu : DifferentiableOn ℝ u (Ioi a ×ˢ univ)) {s : ℝ}
    (hs : a < s) (t : ℝ) :
    HasDerivAt (fun t ↦ u (s, t)) (X t (u (s, t)) + sliceDefect X u (s, t)) t := by
  rw [sliceDefect_def, add_sub_cancel]
  have hmem : (s, t) ∈ Ioi a ×ˢ (univ : Set ℝ) := ⟨hs, mem_univ t⟩
  exact hasDerivAt_slice_right (hu.differentiableAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem))

/-- Where `u` is differentiable, the defect is the derivative of the loop `t ↦ u(s, t)` minus the
vector field along it. -/
theorem sliceDefect_eq_deriv_sub {s t : ℝ} (hu : DifferentiableAt ℝ u (s, t)) :
    sliceDefect X u (s, t) = deriv (fun t ↦ u (s, t)) t - X t (u (s, t)) := by
  rw [sliceDefect_def, (hasDerivAt_slice_right hu).deriv]

/-- **The loops solve the integral equation up to the defect.** Along the loop at `s > a` of a
`C¹` map, `u(s, t₂) - u(s, t₁) = ∫_{t₁}^{t₂} X(t, u(s, t)) dt + ∫_{t₁}^{t₂} (∂_t u - X(t, u))`
after applying a continuous linear map `L` into a Banach space. When `V` is complete, `L` can be
the identity; in general, take the embedding of `V` into its completion. -/
private theorem sub_eq_integral_add_integral_sliceDefect_map {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W] (L : V →L[ℝ] W) (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s) (t₁ t₂ : ℝ) :
    L (u (s, t₂)) - L (u (s, t₁)) =
      (∫ t in t₁..t₂, L (X t (u (s, t)))) + ∫ t in t₁..t₂, L (sliceDefect X u (s, t)) := by
  have hXc : Continuous fun t ↦ L (X t (u (s, t))) :=
    L.continuous.comp
      (hX.comp (continuous_id.prodMk
        (continuous_slice_of_continuousOn hu.continuousOn fun t ↦ ⟨hs, mem_univ t⟩)))
  have hd : Continuous fun t ↦ L (sliceDefect X u (s, t)) :=
    L.continuous.comp (continuous_sliceDefect_slice (isOpen_Ioi.prod isOpen_univ) hu hX
      fun t ↦ ⟨hs, mem_univ t⟩)
  rw [← intervalIntegral.integral_add (hXc.intervalIntegrable _ _) (hd.intervalIntegrable _ _)]
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t ↦ L (u (s, t)))
    (fun t _ ↦ ?_) ((hXc.add hd).intervalIntegrable _ _)).symm
  simpa only [Pi.add_apply, map_add, Function.comp_def] using L.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_slice_add_sliceDefect (hu.differentiableOn one_ne_zero) hs t)

/-- **The loops solve the integral equation up to the defect.** Along the loop at `s > a` of a
`C¹` map into a Banach space, `u(s, t₂) - u(s, t₁) = ∫_{t₁}^{t₂} X(t, u(s, t)) dt +
∫_{t₁}^{t₂} (∂_t u - X(t, u))`. -/
theorem sub_eq_integral_add_integral_sliceDefect [CompleteSpace V]
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s)
    (t₁ t₂ : ℝ) :
    u (s, t₂) - u (s, t₁) =
      (∫ t in t₁..t₂, X t (u (s, t))) + ∫ t in t₁..t₂, sliceDefect X u (s, t) := by
  simpa using
    sub_eq_integral_add_integral_sliceDefect_map (ContinuousLinearMap.id ℝ V) hu hX hs t₁ t₂

section Reflection

open LinearIsometryEquiv (negFst)

/-- The derivative of the reflected map `(s, t) ↦ u(-s, t)` at `z` is the derivative of `u` at
`(-z.1, z.2)` precomposed with the reflection. -/
theorem fderiv_comp_neg_fst {z : ℝ × ℝ} :
    fderiv ℝ (fun w ↦ u (-w.1, w.2)) z =
      (fderiv ℝ u (-z.1, z.2)).comp
        ((negFst ℝ ℝ ℝ).toContinuousLinearEquiv : ℝ × ℝ →L[ℝ] ℝ × ℝ) := by
  have h : (fun w ↦ u (-w.1, w.2)) = u ∘ (negFst ℝ ℝ ℝ).toContinuousLinearEquiv := by
    funext w
    simp
  rw [h, ContinuousLinearEquiv.comp_right_fderiv]
  simp

/-- A map `C^n` on the half-cylinder `(-∞, a) × T` reflects to a map `C^n` on
`(-a, ∞) × T`. -/
theorem contDiffOn_comp_neg_fst {n : WithTop ℕ∞} {T : Set ℝ} (hu : ContDiffOn ℝ n u (Iio a ×ˢ T)) :
    ContDiffOn ℝ n (fun w ↦ u (-w.1, w.2)) (Ioi (-a) ×ˢ T) :=
  hu.comp ((negFst ℝ ℝ ℝ).contDiff.contDiffOn.congr fun w _ ↦
    (LinearIsometryEquiv.negFst_apply ℝ ℝ ℝ w).symm) fun _ hw ↦ ⟨neg_lt.1 hw.1, hw.2⟩

/-- Reflecting the `s`-coordinate does not change the `t`-slices: the defect of
`(s, t) ↦ u(-s, t)` at `z` is the defect of `u` at `(-z.1, z.2)`. -/
@[simp]
theorem sliceDefect_comp_neg_fst {z : ℝ × ℝ} :
    sliceDefect X (fun w ↦ u (-w.1, w.2)) z = sliceDefect X u (-z.1, z.2) := by
  simp [sliceDefect_def, fderiv_comp_neg_fst]

/-- **The defect at the negative end.** Reflecting the `s`-coordinate turns the half-cylinder
`(-∞, a) × [0, 1]` into `(-a, ∞) × [0, 1]` and preserves the squared defect integral, so the
results on the half-cylinder `s > a` apply at the negative end of `u` through the reflected map
`(s, t) ↦ u(-s, t)`. -/
theorem setLIntegral_norm_sq_sliceDefect_comp_neg_fst :
    ∫⁻ z in Ioi (-a) ×ˢ Icc 0 1,
        ENNReal.ofReal (‖sliceDefect X (fun w ↦ u (-w.1, w.2)) z‖ ^ 2) =
      ∫⁻ z in Iio a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) := by
  -- The reflection preserves Lebesgue measure and carries `(-a, ∞) × [0, 1]` onto
  -- `(-∞, a) × [0, 1]`.
  have hmp : MeasurePreserving (negFst ℝ ℝ ℝ) := by
    rw [LinearIsometryEquiv.coe_negFst, Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id (volume : Measure ℝ))
  have hpre : negFst ℝ ℝ ℝ ⁻¹' (Iio a ×ˢ Icc 0 1) = Ioi (-a) ×ˢ Icc 0 1 := by
    ext z
    simp [neg_lt]
  simp_rw [sliceDefect_comp_neg_fst, ← LinearIsometryEquiv.negFst_apply ℝ]
  rw [← hpre]
  exact hmp.setLIntegral_comp_preimage_emb (negFst ℝ ℝ ℝ).toHomeomorph.measurableEmbedding
    (fun z ↦ ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2)) _

end Reflection

section Selection

/-- Along the loop at `s > a`, the lower integral of the squared defect over `[0, 1]` is its
integral. -/
private theorem setLIntegral_ofReal_norm_sq_sliceDefect (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s) :
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (‖sliceDefect X u (s, t)‖ ^ 2) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, ‖sliceDefect X u (s, t)‖ ^ 2) := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal
      ((continuous_norm_sliceDefect_sq (isOpen_Ioi.prod isOpen_univ) hu hX
        fun t ↦ ⟨hs, mem_univ t⟩).integrableOn_Icc)
      (Eventually.of_forall fun t ↦ sq_nonneg _)]

/-- **Loops with small defect.** If the squared defect has finite integral over the half-cylinder
`(a, ∞) × [0, 1]`, then there are `s_n → ∞`, with `s_n > a`, along which the `L²` norm of the
defect over the loop at `s_n` tends to `0`. -/
theorem exists_tendsto_integral_norm_sq_sliceDefect
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hX : Continuous (uncurry X))
    (hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤) :
    ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
      Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ n, t)‖ ^ 2) atTop (𝓝 0) := by
  set f : ℝ × ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2)
  -- Tonelli: the integral over the half-cylinder is the iterated integral.
  have hmeas :
      AEMeasurable f ((volume.restrict (Ioi a)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    refine (ENNReal.continuous_ofReal.comp_continuousOn
      (((continuousOn_sliceDefect (isOpen_Ioi.prod isOpen_univ) hu hX).norm.pow 2).mono
        ?_)).aemeasurable
      (measurableSet_Ioi.prod measurableSet_Icc)
    exact prod_mono le_rfl (subset_univ _)
  have hiter : ∫⁻ s in Ioi a, ∫⁻ t in Icc (0 : ℝ) 1, f (s, t) ≠ ⊤ := by
    rwa [← lintegral_prod f hmeas, Measure.prod_restrict, ← Measure.volume_eq_prod]
  -- The inner integral is the real integral of the squared defect over the loop.
  have hinner : ∀ s, a < s → ∫⁻ t in Icc (0 : ℝ) 1, f (s, t) =
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, ‖sliceDefect X u (s, t)‖ ^ 2) := fun _ hs ↦
    setLIntegral_ofReal_norm_sq_sliceDefect hu hX hs
  -- For every `S` and `ε > 0` some loop beyond `S` has squared defect integral below `ε`.
  have hsel : ∀ (S ε : ℝ), 0 < ε → ∃ s, S < s ∧ a < s ∧
      ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (s, t)‖ ^ 2 < ε := by
    intro S ε hε
    by_contra! h
    refine hiter (eq_top_iff.2 ?_)
    calc (⊤ : ℝ≥0∞) = ∫⁻ _ in Ioi (max S a), ENNReal.ofReal ε := by
          rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top (by simpa using hε)]
      _ ≤ ∫⁻ s in Ioi (max S a), ∫⁻ t in Icc (0 : ℝ) 1, f (s, t) := by
          refine setLIntegral_mono' measurableSet_Ioi fun s hs ↦ ?_
          have hs' : S < s ∧ a < s := max_lt_iff.1 hs
          rw [hinner s hs'.2]
          exact ENNReal.ofReal_le_ofReal (h s hs'.1 hs'.2)
      _ ≤ ∫⁻ s in Ioi a, ∫⁻ t in Icc (0 : ℝ) 1, f (s, t) :=
          lintegral_mono_set (Ioi_subset_Ioi (le_max_right S a))
  choose φ hφS hφa hφε using fun n : ℕ ↦ hsel n (1 / (n + 1)) Nat.one_div_pos_of_nat
  refine ⟨φ, hφa, tendsto_atTop_mono (fun n ↦ (hφS n).le) tendsto_natCast_atTop_atTop, ?_⟩
  refine squeeze_zero (fun n ↦ intervalIntegral.integral_nonneg zero_le_one
    fun t _ ↦ sq_nonneg _) (fun n ↦ (hφε n).le) tendsto_one_div_add_atTop_nhds_zero_nat

/-- **A loop with small defect in a window.** On a window `[σ, τ]` with `a < σ ≤ τ`, if the
integral of the squared defect over `[σ, τ] × [0, 1]` is less than `r (τ - σ)`, then some loop at
a time `s ∈ [σ, τ]` has squared defect integral less than `r`: the defect of the loops is below
its average somewhere in the window. -/
theorem exists_mem_Icc_integral_norm_sq_sliceDefect_lt (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hX : Continuous (uncurry X)) {σ τ r : ℝ} (haσ : a < σ) (hστ : σ ≤ τ)
    (hlt : ∫⁻ z in Icc σ τ ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) <
      ENNReal.ofReal (r * (τ - σ))) :
    ∃ s ∈ Icc σ τ, ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (s, t)‖ ^ 2 < r := by
  set f : ℝ × ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2)
  by_contra! h
  refine hlt.not_ge ?_
  have hsub : Icc σ τ ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ univ :=
    prod_mono (fun s hs ↦ haσ.trans_le hs.1) (subset_univ _)
  have hmeas : AEMeasurable f (volume.restrict (Icc σ τ ×ˢ Icc (0 : ℝ) 1)) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (((continuousOn_sliceDefect (isOpen_Ioi.prod isOpen_univ) hu hX).norm.pow 2).mono
        hsub)).aemeasurable
      (measurableSet_Icc.prod measurableSet_Icc)
  rw [Measure.volume_eq_prod, setLIntegral_prod f (by rwa [← Measure.volume_eq_prod])]
  -- Every loop in the window has squared defect integral at least `r`, so the integral over the
  -- window is at least `r (τ - σ)`.
  rcases lt_or_ge r 0 with hr | hr
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hr.le (sub_nonneg.2 hστ))]
    exact bot_le
  calc ENNReal.ofReal (r * (τ - σ)) = ∫⁻ _ in Icc σ τ, ENNReal.ofReal r := by
        rw [setLIntegral_const, Real.volume_Icc, ENNReal.ofReal_mul hr]
    _ ≤ ∫⁻ s in Icc σ τ, ∫⁻ t in Icc (0 : ℝ) 1, f (s, t) := by
        refine setLIntegral_mono' measurableSet_Icc fun s hs ↦ ?_
        rw [setLIntegral_ofReal_norm_sq_sliceDefect hu hX (haσ.trans_le hs.1)]
        exact ENNReal.ofReal_le_ofReal (h s hs)

/-- **Loops with small defect in windows of small defect.** Let `u k` be `C¹` on the
half-cylinders `s > a k` and fix windows `[σ k, σ k + ℓ]` with `ℓ > 0` and `a k < σ k`. If the
integrals of the squared defects of the `u k` over `[σ k, σ k + ℓ] × [0, 1]` tend to `0`, then
there are times `s k` in the windows along which the `L²` norms of the defects over the loops of
`u k` tend to `0`. -/
theorem exists_mem_Icc_tendsto_integral_norm_sq_sliceDefect {u : ℕ → ℝ × ℝ → V} {a σ : ℕ → ℝ}
    {ℓ : ℝ} (hℓ : 0 < ℓ) (haσ : ∀ k, a k < σ k)
    (hu : ∀ k, ContDiffOn ℝ 1 (u k) (Ioi (a k) ×ˢ univ)) (hX : Continuous (uncurry X))
    (hD : Tendsto (fun k ↦ ∫⁻ z in Icc (σ k) (σ k + ℓ) ×ˢ Icc 0 1,
      ENNReal.ofReal (‖sliceDefect X (u k) z‖ ^ 2)) atTop (𝓝 0)) :
    ∃ s : ℕ → ℝ, (∀ k, s k ∈ Icc (σ k) (σ k + ℓ)) ∧
      Tendsto (fun k ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X (u k) (s k, t)‖ ^ 2) atTop (𝓝 0) := by
  set D : ℕ → ℝ≥0∞ := fun k ↦ ∫⁻ z in Icc (σ k) (σ k + ℓ) ×ˢ Icc 0 1,
    ENNReal.ofReal (‖sliceDefect X (u k) z‖ ^ 2)
  -- In each window with a finite defect integral, some loop has squared defect integral at most
  -- the average over the window, up to `1 / (k + 1)`.
  have hsel (k : ℕ) : ∃ s ∈ Icc (σ k) (σ k + ℓ), D k ≠ ⊤ →
      ∫ t in (0 : ℝ)..1, ‖sliceDefect X (u k) (s, t)‖ ^ 2 < ((D k).toReal + 1 / (k + 1)) / ℓ := by
    by_cases hk : D k = ⊤
    · exact ⟨σ k, ⟨le_rfl, le_add_of_nonneg_right hℓ.le⟩, fun h ↦ (h hk).elim⟩
    obtain ⟨s, hs, hlt⟩ := exists_mem_Icc_integral_norm_sq_sliceDefect_lt (hu k) hX (haσ k)
      (le_add_of_nonneg_right hℓ.le) (r := ((D k).toReal + 1 / (k + 1)) / ℓ) <| by
        rw [add_sub_cancel_left, div_mul_cancel₀ _ hℓ.ne']
        calc D k = ENNReal.ofReal (D k).toReal := (ENNReal.ofReal_toReal hk).symm
          _ < ENNReal.ofReal ((D k).toReal + 1 / (k + 1)) :=
              (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
                (lt_add_of_pos_right _ Nat.one_div_pos_of_nat)
    exact ⟨s, hs, fun _ ↦ hlt⟩
  choose s hs hsD using hsel
  refine ⟨s, hs, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (Eventually.of_forall fun k ↦ intervalIntegral.integral_nonneg zero_le_one
      fun t _ ↦ sq_nonneg _)
    ((hD.eventually (gt_mem_nhds ENNReal.zero_lt_top)).mono fun k hk ↦ (hsD k hk.ne).le)⟩
  -- The bounds tend to `0`, since the defect integrals over the windows do.
  have hD' : Tendsto (fun k ↦ (D k).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hD
    rw [ENNReal.toReal_zero] at h
    exact h
  simpa using (hD'.add tendsto_one_div_add_atTop_nhds_zero_nat).div_const ℓ

end Selection

section Modulus

/-- **A modulus of continuity for loops with small defect.** If `X` is bounded by `B` along the
loop at `s` on `[t₁, t₂]`, then
`‖u(s, t₂) - u(s, t₁)‖ ≤ B (t₂ - t₁) + √(t₂ - t₁) √(∫_{t₁}^{t₂} ‖∂_t u - X(t, u)‖²)`. -/
theorem norm_sub_le_add_sqrt_mul_sqrt_integral_sliceDefect
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s)
    {B t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (hB : ∀ t ∈ Icc t₁ t₂, ‖X t (u (s, t))‖ ≤ B) :
    ‖u (s, t₂) - u (s, t₁)‖ ≤
      B * (t₂ - t₁) + √(t₂ - t₁) * √(∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ ^ 2) := by
  have hd := continuous_sliceDefect_slice (isOpen_Ioi.prod isOpen_univ) hu hX
    fun t ↦ ⟨hs, mem_univ t⟩
  have hder : ∀ t, HasDerivAt (fun t ↦ u (s, t)) (X t (u (s, t)) + sliceDefect X u (s, t)) t :=
    hasDerivAt_slice_add_sliceDefect (hu.differentiableOn one_ne_zero) hs
  have hBi : IntervalIntegrable (fun t ↦ B + ‖sliceDefect X u (s, t)‖) volume t₁ t₂ :=
    (continuous_const.add hd.norm).intervalIntegrable _ _
  calc ‖u (s, t₂) - u (s, t₁)‖
      ≤ ∫ t in t₁..t₂, (B + ‖sliceDefect X u (s, t)‖) :=
        norm_sub_le_integral_of_norm_deriv_le_of_le (f := fun t ↦ u (s, t)) ht
          (continuous_slice_of_continuousOn hu.continuousOn fun t ↦ ⟨hs, mem_univ t⟩).continuousOn
          (fun t _ ↦ (hder t).differentiableAt.differentiableWithinAt)
          (Eventually.of_forall fun t htm ↦ by
            rw [(hder t).deriv]
            exact (norm_add_le _ _).trans (add_le_add (hB t (Ioo_subset_Icc_self htm)) le_rfl))
          hBi
    _ = B * (t₂ - t₁) + ∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hd.norm.intervalIntegrable _ _),
          intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    _ ≤ B * (t₂ - t₁) + √(t₂ - t₁) * √(∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ ^ 2) :=
        add_le_add le_rfl (integral_le_sqrt_mul_sqrt_integral_sq ht
          ((hd.norm.pow 2).intervalIntegrable _ _))

/-- **The defect integral is controlled by its `L²` norm.** Over a subinterval `[t₁, t₂]` of
`[0, 1]`, the integral of the norm of the defect along the loop at `s > a` is at most the `L²` norm
of the defect over `[0, 1]`. -/
theorem integral_norm_sliceDefect_le_sqrt (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hX : Continuous (uncurry X)) {s : ℝ} (hs : a < s) {t₁ t₂ : ℝ} (h₀ : 0 ≤ t₁) (ht : t₁ ≤ t₂)
    (h₁ : t₂ ≤ 1) :
    ∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ ≤
      √(∫ t in (0 : ℝ)..1, ‖sliceDefect X u (s, t)‖ ^ 2) := by
  have hd := continuous_norm_sliceDefect_sq (isOpen_Ioi.prod isOpen_univ) hu hX
    fun t ↦ ⟨hs, mem_univ t⟩
  calc ∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖
      ≤ √(t₂ - t₁) * √(∫ t in t₁..t₂, ‖sliceDefect X u (s, t)‖ ^ 2) :=
        integral_le_sqrt_mul_sqrt_integral_sq ht
          (hd.intervalIntegrable _ _)
    _ ≤ 1 * √(∫ t in (0 : ℝ)..1, ‖sliceDefect X u (s, t)‖ ^ 2) := by
        gcongr
        · exact Real.sqrt_le_one.mpr (by linarith)
        · exact intervalIntegral.integral_mono_interval h₀ ht h₁
            (Eventually.of_forall fun t ↦ sq_nonneg _) (hd.intervalIntegrable _ _)
    _ = _ := one_mul _

/-- **Vanishing defect integrals.** Let `u i` be `C¹` on the half-cylinders `s > a i`. If the `L²`
norms of the defects along the loops of `u i` at `s_i > a i` tend to `0`, then so do the integrals
of the norms of the defects over any subinterval `[t₁, t₂]` of `[0, 1]`. The maps may be one map
`u`, with loops at varying `s_i`, or a sequence of maps such as Floer solutions. -/
theorem tendsto_integral_norm_sliceDefect_of_tendsto_integral_norm_sq {ι : Type*}
    {u : ι → ℝ × ℝ → V} {a : ι → ℝ} (hu : ∀ i, ContDiffOn ℝ 1 (u i) (Ioi (a i) ×ˢ univ))
    (hX : Continuous (uncurry X)) {l : Filter ι} {φ : ι → ℝ} (hφa : ∀ i, a i < φ i)
    (hφ : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X (u i) (φ i, t)‖ ^ 2) l (𝓝 0))
    {t₁ t₂ : ℝ} (h₀ : 0 ≤ t₁) (ht : t₁ ≤ t₂) (h₁ : t₂ ≤ 1) :
    Tendsto (fun i ↦ ∫ t in t₁..t₂, ‖sliceDefect X (u i) (φ i, t)‖) l (𝓝 0) := by
  have hsq : Tendsto (fun i ↦
      √(∫ t in (0 : ℝ)..1, ‖sliceDefect X (u i) (φ i, t)‖ ^ 2)) l (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hφ
    rw [Real.sqrt_zero] at h
    exact h
  exact squeeze_zero (fun i ↦ intervalIntegral.integral_nonneg ht fun t _ ↦ norm_nonneg _)
    (fun i ↦ integral_norm_sliceDefect_le_sqrt (hu i) hX (hφa i) h₀ ht h₁) hsq

end Modulus

section Limit

/-- **The integral equation passes to the limit.** Let `X` be continuous and let `u i` be `C¹` on
the half-cylinders `s > a i`. If the loops of `u i` at `s_i > a i` lie in a compact set `K`,
converge pointwise to `x` and the `L²` norms of their defects tend to `0`, then
`x(t) - x(0) = ∫₀ᵗ X(τ, x(τ)) dτ` for `t ∈ [0, 1]`, after applying a continuous linear map `L` into
a Banach space. When `V` is complete, `L` can be the identity; in general, take the embedding of `V`
into its completion. -/
private theorem sub_eq_integral_of_tendsto_integral_norm_sq_sliceDefect_map {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] (L : V →L[ℝ] W) {ι : Type*}
    {u : ι → ℝ × ℝ → V} {a : ι → ℝ} (hu : ∀ i, ContDiffOn ℝ 1 (u i) (Ioi (a i) ×ˢ univ))
    (hX : Continuous (uncurry X)) {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {φ : ι → ℝ}
    (hφa : ∀ i, a i < φ i) {K : Set V} (hK : IsCompact K) (huK : ∀ i t, u i (φ i, t) ∈ K)
    (hφ : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X (u i) (φ i, t)‖ ^ 2) l (𝓝 0))
    {x : ℝ → V} (hx : ∀ t, Tendsto (fun i ↦ u i (φ i, t)) l (𝓝 (x t))) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    L (x t) - L (x 0) = ∫ τ in (0 : ℝ)..t, L (X τ (x τ)) := by
  have hloop : ∀ i, Continuous fun τ ↦ u i (φ i, τ) := fun i ↦
    continuous_slice_of_continuousOn (hu i).continuousOn fun t ↦ ⟨hφa i, mem_univ t⟩
  -- Along the sequence, `u(s, t) - u(s, 0) = ∫₀ᵗ X(τ, u(s, τ)) dτ + ∫₀ᵗ (defect)`.
  have hsplit : ∀ i, L (u i (φ i, t)) - L (u i (φ i, 0)) =
      (∫ τ in (0 : ℝ)..t, L (X τ (u i (φ i, τ)))) +
        ∫ τ in (0 : ℝ)..t, L (sliceDefect X (u i) (φ i, τ)) :=
    fun i ↦ sub_eq_integral_add_integral_sliceDefect_map L (hu i) hX (hφa i) 0 t
  -- The first integral converges by dominated convergence.
  have hA : Tendsto (fun i ↦ ∫ τ in (0 : ℝ)..t, L (X τ (u i (φ i, τ)))) l
      (𝓝 (∫ τ in (0 : ℝ)..t, L (X τ (x τ)))) :=
    tendsto_intervalIntegral_comp_of_tendsto (Φ := L ∘ uncurry X) (y := fun i τ ↦ u i (φ i, τ))
      (L.continuous.comp hX) hK (fun i ↦ (hloop i).continuousOn)
      (fun i τ _ ↦ huK i τ) fun τ _ ↦ hx τ
  -- The second integral tends to `0` by the Cauchy–Schwarz inequality.
  have hD : Tendsto (fun i ↦ ∫ τ in (0 : ℝ)..t, L (sliceDefect X (u i) (φ i, τ))) l (𝓝 0) := by
    have h := (tendsto_integral_norm_sliceDefect_of_tendsto_integral_norm_sq hu hX hφa hφ le_rfl
      ht.1 ht.2).const_mul ‖L‖
    rw [mul_zero] at h
    refine squeeze_zero_norm (fun i ↦ ?_) h
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.norm_integral_le_of_norm_le ht.1
      (Eventually.of_forall fun τ _ ↦ L.le_opNorm _)
      ((continuous_const.mul (continuous_sliceDefect_slice (isOpen_Ioi.prod isOpen_univ)
        (hu i) hX fun t ↦ ⟨hφa i, mem_univ t⟩).norm).intervalIntegrable _ _)
  have hL : Tendsto (fun i ↦ L (u i (φ i, t)) - L (u i (φ i, 0))) l (𝓝 (L (x t) - L (x 0))) :=
    ((L.continuous.tendsto _).comp (hx t)).sub ((L.continuous.tendsto _).comp (hx 0))
  simp_rw [hsplit] at hL
  simpa using (tendsto_nhds_unique (hA.add hD) hL).symm

/-- **The integral equation passes to the limit.** Let `X` be continuous and let `u i` be `C¹` on
the half-cylinders `s > a i`, in a Banach space. If the loops of `u i` at `s_i > a i` lie in a
compact set `K`, converge pointwise to `x` and the `L²` norms of their defects tend to `0`, then
`x(t) - x(0) = ∫₀ᵗ X(τ, x(τ)) dτ` for `t ∈ [0, 1]`. -/
theorem sub_eq_integral_of_tendsto_integral_norm_sq_sliceDefect [CompleteSpace V] {ι : Type*}
    {u : ι → ℝ × ℝ → V} {a : ι → ℝ} (hu : ∀ i, ContDiffOn ℝ 1 (u i) (Ioi (a i) ×ˢ univ))
    (hX : Continuous (uncurry X)) {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {φ : ι → ℝ}
    (hφa : ∀ i, a i < φ i) {K : Set V} (hK : IsCompact K) (huK : ∀ i t, u i (φ i, t) ∈ K)
    (hφ : Tendsto (fun i ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X (u i) (φ i, t)‖ ^ 2) l (𝓝 0))
    {x : ℝ → V} (hx : ∀ t, Tendsto (fun i ↦ u i (φ i, t)) l (𝓝 (x t))) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    x t - x 0 = ∫ τ in (0 : ℝ)..t, X τ (x τ) := by
  simpa using sub_eq_integral_of_tendsto_integral_norm_sq_sliceDefect_map
    (ContinuousLinearMap.id ℝ V) hu hX hφa hK huK hφ hx ht

/-- **Loops with small defect converge to periodic orbits.** Let `X` be a continuous,
`1`-periodic time-dependent vector field and let `u n` be `C¹` on the half-cylinders `s > a n`.
Let `s_n > a n` be times at which the loops `t ↦ u n (s_n, t)` are `1`-periodic and lie in a
compact set `K`. If the `L²` norm of the defect `∂_t u n - X(t, u n)` over the loop of `u n` at
`s_n` tends to `0`, then a subsequence of the loops `t ↦ u n (s_n, t)` converges uniformly to a
`1`-periodic solution `x` of `x' = X(t, x)`. The maps may be one map `u`, as at the end of a single
half-cylinder, or a sequence of maps, as along the necks of a sequence of Floer cylinders. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral {u : ℕ → ℝ × ℝ → V}
    {a : ℕ → ℝ} (hu : ∀ n, ContDiffOn ℝ 1 (u n) (Ioi (a n) ×ˢ univ))
    (hX : Continuous (uncurry X)) (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    {φ : ℕ → ℝ} (hφa : ∀ n, a n < φ n) (hper : ∀ n, Periodic (fun t ↦ u n (φ n, t)) 1)
    {K : Set V} (hK : IsCompact K) (huK : ∀ n t, u n (φ n, t) ∈ K)
    (hφ : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X (u n) (φ n, t)‖ ^ 2) atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧
      TendstoUniformly (fun n t ↦ u (ψ n) (φ (ψ n), t)) x atTop := by
  -- A bound for `X` on `[0, 1] × K`.
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hX.continuousOn
  have hBu : ∀ n, ∀ t ∈ Icc (0 : ℝ) 1, ‖X t (u n (φ n, t))‖ ≤ B :=
    fun n t ht ↦ hB (t, u n (φ n, t)) ⟨ht, huK n t⟩
  -- Pass to the tail of the sequence on which the squared defect integral is at most `1`.
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hφ.eventually (gt_mem_nhds zero_lt_one))
  set y : ℕ → ℝ → V := fun n t ↦ u (N + n) (φ (N + n), t)
  -- The loops share the modulus of continuity `h ↦ B h + √h` on `[0, 1]`.
  have hmod : ∀ n, ∀ t₁ ∈ Icc (0 : ℝ) 1, ∀ t₂ ∈ Icc (0 : ℝ) 1, t₁ ≤ t₂ →
      dist (y n t₂) (y n t₁) ≤ B * (t₂ - t₁) + √(t₂ - t₁) := by
    intro n t₁ ht₁ t₂ ht₂ ht
    have hs := hφa (N + n)
    rw [dist_eq_norm]
    refine (norm_sub_le_add_sqrt_mul_sqrt_integral_sliceDefect (hu _) hX hs ht
      fun t htI ↦ hBu _ t ⟨ht₁.1.trans htI.1, htI.2.trans ht₂.2⟩).trans ?_
    have hle : ∫ t in t₁..t₂, ‖sliceDefect X (u (N + n)) (φ (N + n), t)‖ ^ 2 ≤ 1 :=
      (intervalIntegral.integral_mono_interval ht₁.1 ht ht₂.2
        (Eventually.of_forall fun t ↦ sq_nonneg _)
        ((continuous_norm_sliceDefect_sq (isOpen_Ioi.prod isOpen_univ) (hu _) hX
          fun t ↦ ⟨hs, mem_univ t⟩).intervalIntegrable _ _)).trans
        (hN _ (Nat.le_add_right N n)).le
    exact add_le_add le_rfl (mul_le_of_le_one_right (Real.sqrt_nonneg _)
      (Real.sqrt_le_one.mpr hle))
  have hρ : Tendsto (fun h : ℝ ↦ B * h + √h) (𝓝 0) (𝓝 0) := by
    have hb : Continuous fun h : ℝ ↦ B * h + √h :=
      (continuous_const.mul continuous_id).add Real.continuous_sqrt
    simpa using hb.tendsto 0
  obtain ⟨ψ', hψ', x, hxper, hxcont, hux'⟩ :=
    exists_tendstoUniformly_subseq_of_periodic_of_modulus hK
      (fun n ↦ continuous_slice_of_continuousOn (hu _).continuousOn
        fun t ↦ ⟨hφa (N + n), mem_univ t⟩)
      (fun n ↦ hper (N + n)) (fun n ↦ huK (N + n)) hρ hmod
  set ψ : ℕ → ℕ := fun n ↦ N + ψ' n
  have hψ : StrictMono ψ := fun m n h ↦ Nat.add_lt_add_left (hψ' h) N
  have hux : TendstoUniformly (fun n t ↦ u (ψ n) (φ (ψ n), t)) x atTop := hux'
  have hdef : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X (u (ψ n)) (φ (ψ n), t)‖ ^ 2)
      atTop (𝓝 0) :=
    hφ.comp (tendsto_atTop_mono (fun n ↦ Nat.le_add_left _ N) hψ'.tendsto_atTop)
  -- In the completion `ι : V → V̂`, the limit solves the integral equation on `[0, 1]`, hence
  -- `(ι ∘ x)' = ι (X(t, x))` by periodicity; as `ι` is isometric, `x' = X(t, x)`.
  set ι : V →L[ℝ] UniformSpace.Completion V := UniformSpace.Completion.toComplL
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, ι (x t) - ι (x 0) = ∫ τ in (0 : ℝ)..t, ι (X τ (x τ)) :=
    fun t ht ↦ sub_eq_integral_of_tendsto_integral_norm_sq_sliceDefect_map ι
      (fun n ↦ hu (ψ n)) hX (fun n ↦ hφa (ψ n)) hK (fun n ↦ huK (ψ n)) hdef hux.tendsto_at ht
  refine ⟨ψ, hψ, x, hxper, fun t ↦ ?_, hux⟩
  have h := hasDerivAt_of_periodic_of_sub_eq_integral (x := fun τ ↦ ι (x τ))
    (Y := fun τ ↦ ι (X τ (x τ))) one_pos (hxper.comp ι)
    (ι.continuous.comp (hX.comp (continuous_id.prodMk hxcont)))
    (fun t ↦ by simp only [hxper t, hXper (x t) t]) hint t
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  rw [← Asymptotics.isLittleO_completion_left]
  simpa [ι, UniformSpace.Completion.coe_sub] using h

/-- **Loops with small defect converge to periodic orbits**, for a sequence of loops. Let `X` be
a continuous, `1`-periodic time-dependent vector field, and let `γ n` be `C¹`, `1`-periodic loops
in a compact set `K`. If the `L²` norm of the defect `γ n' - X(t, γ n)` over `[0, 1]` tends to
`0`, then a subsequence of the loops converges uniformly to a `1`-periodic solution `x` of
`x' = X(t, x)` with values in `K`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral_deriv_sub
    {γ : ℕ → ℝ → V} (hγ : ∀ n, ContDiff ℝ 1 (γ n)) (hper : ∀ n, Periodic (γ n) 1)
    {K : Set V} (hK : IsCompact K) (hγK : ∀ n t, γ n t ∈ K)
    (hX : Continuous (uncurry X)) (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    (hγX : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖deriv (γ n) t - X t (γ n t)‖ ^ 2) atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧
      (∀ t, x t ∈ K) ∧ TendstoUniformly (fun n ↦ γ (ψ n)) x atTop := by
  -- The loops are those of the maps `(s, t) ↦ γ n t`, which do not depend on `s`.
  have hdef (n : ℕ) (s t : ℝ) :
      sliceDefect X (fun w ↦ γ n w.2) (s, t) = deriv (γ n) t - X t (γ n t) :=
    sliceDefect_eq_deriv_sub
      (((hγ n).differentiable one_ne_zero t).comp (s, t) differentiableAt_snd)
  obtain ⟨ψ, hψ, x, hxper, hx, hux⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral (a := fun _ ↦ 0)
      (u := fun n w ↦ γ n w.2) (fun n ↦ ((hγ n).comp contDiff_snd).contDiffOn) hX hXper
      (φ := fun _ ↦ 1) (fun _ ↦ one_pos) hper hK hγK (by simpa only [hdef] using hγX)
  exact ⟨ψ, hψ, x, hxper, hx, fun t ↦ hK.isClosed.mem_of_tendsto (hux.tendsto_at t)
    (Eventually.of_forall fun n ↦ hγK _ t), hux⟩

/-- **Loops with square-integrable defect accumulate at periodic orbits.** Let `X` be a
continuous, `1`-periodic time-dependent vector field and let `u` be `C¹` on the half-cylinder
`s > a`, with `1`-periodic loops `t ↦ u(s, t)` in a compact set. If the squared norm of the defect
`∂_t u - X(t, u)` has finite integral over `(a, ∞) × [0, 1]`, then there are a `1`-periodic
solution `x` of `x' = X(t, x)` and `s_n → ∞`, with `s_n > a`, such that the loops
`t ↦ u(s_n, t)` converge uniformly to `x` and the `L²` norms of the defect over them tend to
`0`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    {K : Set V} (hK : IsCompact K) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K)
    (hX : Continuous (uncurry X)) (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    (hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧
      ∃ φ : ℕ → ℝ, (∀ n, a < φ n) ∧ Tendsto φ atTop atTop ∧
        TendstoUniformly (fun n t ↦ u (φ n, t)) x atTop ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ n, t)‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨φ, hφa, hφ, hdef⟩ := exists_tendsto_integral_norm_sq_sliceDefect hu hX hfin
  obtain ⟨ψ, hψ, x, hxper, hx, hux⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral (fun _ ↦ hu) hX hXper hφa
      (fun n ↦ hper _ (hφa n)) hK (fun n ↦ huK _ (hφa n)) hdef
  exact ⟨x, hxper, hx, φ ∘ ψ, fun n ↦ hφa (ψ n), hφ.comp hψ.tendsto_atTop, hux,
    hdef.comp hψ.tendsto_atTop⟩

end Limit

section Convergence

variable {K : Set V} {C : ℝ}

/-- On the strip `(a, b) × ℝ` where `u` is `C¹`, the loop at `s ∈ (a, b)` is `C¹` and its defect is
the defect of `u`. -/
private theorem contDiff_slice_and_sliceDefect_eq {b : ℝ} (hu : ContDiffOn ℝ 1 u (Ioo a b ×ˢ univ))
    {s : ℝ} (hs : s ∈ Ioo a b) :
    ContDiff ℝ 1 (fun t ↦ u (s, t)) ∧
      ∀ t, sliceDefect X u (s, t) = deriv (fun t ↦ u (s, t)) t - X t (u (s, t)) :=
  ⟨hu.comp_contDiff (contDiff_const.prodMk contDiff_id) fun t ↦ ⟨hs, mem_univ t⟩,
    fun t ↦ sliceDefect_eq_deriv_sub ((hu.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs, mem_univ t⟩))⟩

/-- If the squared defect of a map, `C¹` on the strip `(a, b) × ℝ`, integrates to less than `h δ`
over a rectangle `[s, s + h] × [0, 1]` inside the strip, then some loop at a time `σ ∈ [s, s + h]`
has squared defect integral below `δ`. -/
private theorem exists_mem_Icc_integral_norm_sq_sliceDefect_lt_of_setLIntegral_lt {b : ℝ}
    (hu : ContDiffOn ℝ 1 u (Ioo a b ×ˢ univ)) (hX : Continuous (uncurry X)) {s h δ : ℝ}
    (hh : 0 < h) (hs : Icc s (s + h) ⊆ Ioo a b)
    (hE : ∫⁻ z in Icc s (s + h) ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) <
      ENNReal.ofReal (h * δ)) :
    ∃ σ ∈ Icc s (s + h), ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (σ, t)‖ ^ 2 < δ := by
  by_contra! hge
  refine hE.not_ge ?_
  set f : ℝ × ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2)
  have hmeas : AEMeasurable f (volume.restrict (Icc s (s + h) ×ˢ Icc (0 : ℝ) 1)) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (((continuousOn_sliceDefect (isOpen_Ioo.prod isOpen_univ) hu hX).norm.pow 2).mono
        (prod_mono hs (subset_univ _)))).aemeasurable
      (measurableSet_Icc.prod measurableSet_Icc)
  rw [Measure.volume_eq_prod, setLIntegral_prod f (by rwa [← Measure.volume_eq_prod])]
  calc ENNReal.ofReal (h * δ) = ∫⁻ _ in Icc s (s + h), ENNReal.ofReal δ := by
        rw [setLIntegral_const, Real.volume_Icc, add_sub_cancel_left, ENNReal.ofReal_mul hh.le,
          mul_comm]
    _ ≤ ∫⁻ σ in Icc s (s + h), ∫⁻ t in Icc (0 : ℝ) 1, f (σ, t) := by
        refine setLIntegral_mono' measurableSet_Icc fun σ hσ ↦ ?_
        have heq : ∫⁻ t in Icc (0 : ℝ) 1, f (σ, t) =
            ENNReal.ofReal (∫ t in (0 : ℝ)..1, ‖sliceDefect X u (σ, t)‖ ^ 2) := by
          rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
            ofReal_integral_eq_lintegral_ofReal
              ((continuous_norm_sliceDefect_sq (isOpen_Ioo.prod isOpen_univ) hu hX
                fun t ↦ ⟨hs hσ, mem_univ t⟩).integrableOn_Icc)
              (Eventually.of_forall fun t ↦ sq_nonneg _)]
        rw [heq]
        exact ENNReal.ofReal_le_ofReal (hge σ hσ)

/-- **A loop with small defect near every late time.** If the squared defect has finite integral
over `(a, ∞) × [0, 1]`, then for every `ε > 0` and every large enough `s`, some loop at a time
`σ ∈ [s, s + ε]` has squared defect integral less than `ε`. -/
theorem eventually_exists_mem_Icc_integral_norm_sq_sliceDefect_lt
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hX : Continuous (uncurry X))
    (hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in atTop, ∃ σ ∈ Icc s (s + ε),
      ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (σ, t)‖ ^ 2 < ε := by
  set f : ℝ × ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2)
  -- The integrals over the rectangles `[s, s + ε] × [0, 1]` tend to `0`.
  have htail : Tendsto (fun s ↦ ∫⁻ z in Icc s (s + ε) ×ˢ Icc (0 : ℝ) 1, f z) atTop (𝓝 0) := by
    refine tendsto_setLIntegral_of_eventually_subset hfin fun R ↦ ?_
    filter_upwards [eventually_gt_atTop a, eventually_ge_atTop R] with s has hRs
    rintro z ⟨hz₁, hz₂⟩
    exact ⟨⟨has.trans_le hz₁.1, hz₂⟩, hRs.trans (hz₁.1.trans (le_abs_self _))⟩
  filter_upwards [eventually_gt_atTop a,
    htail.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (mul_pos hε hε)))] with s has hs
  exact exists_mem_Icc_integral_norm_sq_sliceDefect_lt hu hX has (le_add_of_nonneg_right hε.le)
    (by rwa [add_sub_cancel_left])

/-- Near a cluster point `y` of the loops in the topology of uniform convergence there are loops
with arbitrarily small defect: some loops at `σ_n → ∞`, with `σ_n > a`, converge uniformly to `y`
while their squared defect integrals tend to `0`. -/
theorem exists_tendstoUniformly_of_mapClusterPt (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hX : Continuous (uncurry X))
    (hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C) {y : ℝ →ᵤ V}
    (hy : MapClusterPt y atTop fun s ↦ UniformFun.ofFun fun t ↦ u (s, t)) :
    ∃ σ : ℕ → ℝ, (∀ n, a < σ n) ∧ Tendsto σ atTop atTop ∧
      Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (σ n, t)‖ ^ 2) atTop (𝓝 0) ∧
      TendstoUniformly (fun n t ↦ u (σ n, t)) (UniformFun.toFun y) atTop := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (a + 1, 0) ⟨lt_add_one a, trivial⟩)
  -- By the mean value inequality on the convex half-cylinder, `u` is `C`-Lipschitz, and so is
  -- each of its slices `s ↦ u (s, t)`.
  have hL : LipschitzOnWith C.toNNReal u (Ioi a ×ˢ univ) :=
    ((convex_Ioi a).prod convex_univ).lipschitzOnWith_of_nnNorm_fderiv_le
      (fun z hz ↦ (hu.differentiableOn one_ne_zero).differentiableAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds hz))
      fun z hz ↦ (Real.le_toNNReal_iff_coe_le hC0).2 (hC z hz)
  have hLs (t : ℝ) : LipschitzOnWith C.toNNReal (fun s ↦ u (s, t)) (Ioi a) := by
    simpa [Function.comp_def] using
      hL.comp (LipschitzWith.prodMk_right t).lipschitzOnWith fun s hs ↦ ⟨hs, trivial⟩
  -- For each `n`, a late loop uniformly `1 / (n + 1)`-close to `y`, and a loop with small defect
  -- at most `1 / (n + 1)` later.
  have hsel : ∀ n : ℕ, ∃ s σ : ℝ, a < s ∧ (n : ℝ) ≤ s ∧ σ ∈ Icc s (s + 1 / (n + 1)) ∧
      (∀ t, dist (u (s, t)) (UniformFun.toFun y t) < 1 / (n + 1)) ∧
      ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (σ, t)‖ ^ 2 < 1 / (n + 1) := by
    intro n
    have hε : (0 : ℝ) < 1 / (n + 1) := Nat.one_div_pos_of_nat
    obtain ⟨S, hS⟩ := eventually_atTop.1
      (eventually_exists_mem_Icc_integral_norm_sq_sliceDefect_lt hu hX hfin hε)
    obtain ⟨s, hs, hsy⟩ := frequently_atTop.1 (mapClusterPt_iff_frequently.1 hy _
      (Metric.eball_mem_nhds y (ENNReal.ofReal_pos.2 hε))) (max (max S (a + 1)) n)
    have hsSa : max S (a + 1) ≤ s := (le_max_left _ _).trans hs
    obtain ⟨σ, hσ, hσd⟩ := hS s ((le_max_left _ _).trans hsSa)
    refine ⟨s, σ, (lt_add_one a).trans_le ((le_max_right _ _).trans hsSa),
      (le_max_right _ _).trans hs, hσ, fun t ↦ ?_, hσd⟩
    rw [Metric.mem_eball] at hsy
    exact edist_lt_ofReal.1 ((UniformFun.edist_le.1 le_rfl t).trans_lt hsy)
  choose s σ has hns hσ hsy hσd using hsel
  have hσa : ∀ n, a < σ n := fun n ↦ (has n).trans_le (hσ n).1
  refine ⟨σ, hσa, tendsto_atTop_mono (fun n ↦ (hns n).trans (hσ n).1) tendsto_natCast_atTop_atTop,
    squeeze_zero (fun n ↦ intervalIntegral.integral_nonneg zero_le_one
      fun t _ ↦ sq_nonneg _) (fun n ↦ (hσd n).le) tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  -- The loops at `σ n` are within `(C + 1) / (n + 1)` of `y`.
  refine Metric.tendstoUniformly_iff.2 fun δ hδ ↦ ?_
  have hlim : Tendsto (fun n : ℕ ↦ (C + 1) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (C + 1)
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn t
  have hσs : |σ n - s n| ≤ 1 / (n + 1) := by
    rw [abs_of_nonneg (sub_nonneg.2 (hσ n).1)]
    linarith [(hσ n).2]
  calc dist (UniformFun.toFun y t) (u (σ n, t))
      ≤ dist (u (σ n, t)) (u (s n, t)) + dist (u (s n, t)) (UniformFun.toFun y t) := by
        rw [dist_comm]; exact dist_triangle _ _ _
    _ ≤ C * (1 / (n + 1)) + 1 / (n + 1) :=
        add_le_add (((hLs t).dist_le_mul _ (hσa n) _ (has n)).trans <| by
          rw [Real.coe_toNNReal C hC0, Real.dist_eq]
          exact mul_le_mul_of_nonneg_left hσs hC0) (hsy n t).le
    _ = (C + 1) * (1 / (n + 1)) := by ring
    _ < δ := hn

/-- **The ω-limit loops are periodic solutions.** Let `X` be a continuous, `1`-periodic
time-dependent vector field and let `u` be `C¹` on the half-cylinder `s > a`, with derivative
bounded by `C` and with `1`-periodic loops `t ↦ u(s, t)` in a compact set `K`. If the squared norm
of the defect `∂_t u - X(t, u)` has finite integral over `(a, ∞) × [0, 1]`, then every cluster point
of the loops as `s → ∞`, in the topology of uniform convergence, is a `1`-periodic solution of
`x' = X(t, x)`. -/
theorem periodic_and_hasDerivAt_of_mapClusterPt (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (hK : IsCompact K)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K) (hX : Continuous (uncurry X))
    (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    (hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C) {y : ℝ →ᵤ V}
    (hy : MapClusterPt y atTop fun s ↦ UniformFun.ofFun fun t ↦ u (s, t)) :
    Periodic (UniformFun.toFun y) 1 ∧
      ∀ t, HasDerivAt (UniformFun.toFun y) (X t (UniformFun.toFun y t)) t := by
  obtain ⟨σ, hσa, -, hdef, hσy⟩ := exists_tendstoUniformly_of_mapClusterPt hu hX hfin hC hy
  -- A subsequence converges uniformly to a periodic solution, which is then `y`.
  obtain ⟨ψ, hψ, x, hxper, hx, hux⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral (fun _ ↦ hu) hX hXper hσa
      (fun n ↦ hper _ (hσa n)) hK (fun n ↦ huK _ (hσa n)) hdef
  have hyx : UniformFun.toFun y = x := funext fun t ↦ tendsto_nhds_unique
    ((hσy.tendsto_at t).comp hψ.tendsto_atTop) (hux.tendsto_at t)
  exact hyx ▸ ⟨hxper, hx⟩

/-- A derivative bound on the strip `(a, ∞) × [0, 1]` extends to the half-cylinder `(a, ∞) × ℝ`
when the slices `t ↦ u(s, t)` are `1`-periodic. -/
theorem norm_fderiv_le_of_periodic (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hC : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ‖fderiv ℝ u z‖ ≤ C) {z : ℝ × ℝ}
    (hz : z ∈ Ioi a ×ˢ (univ : Set ℝ)) : ‖fderiv ℝ u z‖ ≤ C := by
  set n : ℤ := ⌊z.2⌋
  have heq : (fun w : ℝ × ℝ ↦ u (w + (0, -(n : ℝ)))) =ᶠ[𝓝 z] u := by
    filter_upwards [(isOpen_Ioi.prod isOpen_univ).mem_nhds hz] with ⟨s, t⟩ hw
    simpa only [Prod.mk_add_mk, add_zero, ← sub_eq_add_neg, mul_one] using
      (hper s hw.1).sub_int_mul_eq n
  rw [← heq.fderiv_eq, fderiv_comp_add_right]
  refine hC _ ⟨by simpa only [Prod.fst_add, add_zero] using hz.1, ?_, ?_⟩ <;>
    simp only [Prod.snd_add] <;> linarith [Int.floor_le z.2, Int.lt_floor_add_one z.2]

/-- **Convergence of the loops when uniform cluster-point orbits are isolated.** Let `X` be a
continuous, `1`-periodic time-dependent vector field and let `u` be `C¹` on the half-cylinder
`s > a`, with derivative bounded by `C` and with `1`-periodic loops `t ↦ u(s, t)` in a compact set
`K`. Suppose that the squared norm of the defect `∂_t u - X(t, u)` has finite integral over
`(a, ∞) × [0, 1]`, and that the `1`-periodic solutions of `x' = X(t, x)` in `K` that are uniform
cluster points of the loops as `s → ∞` are isolated from each other: each has a uniform
neighbourhood containing no other such cluster point. Then the loops converge uniformly, as
`s → ∞`, to a single `1`-periodic solution `x`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_mapClusterPt
    (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hK : IsCompact K) (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K) (hX : Continuous (uncurry X))
    (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    (hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C)
    (hiso : ∀ x : ℝ → V, Periodic x 1 → (∀ t, HasDerivAt x (X t (x t)) t) → (∀ t, x t ∈ K) →
      MapClusterPt (UniformFun.ofFun x) atTop (fun s ↦ UniformFun.ofFun fun t ↦ u (s, t)) →
      ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 → (∀ t, HasDerivAt y (X t (y t)) t) →
        (∀ t, y t ∈ K) →
        MapClusterPt (UniformFun.ofFun y) atTop (fun s ↦ UniformFun.ofFun fun t ↦ u (s, t)) →
        (∀ t, dist (y t) (x t) < ε) → y = x) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧
      TendstoUniformly (fun s t ↦ u (s, t)) x atTop := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (a + 1, 0) ⟨lt_add_one a, trivial⟩)
  -- By the mean value inequality on the convex half-cylinder, `u` is `C`-Lipschitz.
  have hL : LipschitzOnWith C.toNNReal u (Ioi a ×ˢ univ) :=
    ((convex_Ioi a).prod convex_univ).lipschitzOnWith_of_nnNorm_fderiv_le
      (fun z hz ↦ (hu.differentiableOn one_ne_zero).differentiableAt
        ((isOpen_Ioi.prod isOpen_univ).mem_nhds hz))
      fun z hz ↦ (Real.le_toNNReal_iff_coe_le hC0).2 (hC z hz)
  set ℓ : ℝ → ℝ →ᵤ V := fun s ↦ UniformFun.ofFun fun t ↦ u (s, t)
  -- The loops lie in the set `S` of `1`-periodic, `C`-Lipschitz loops in `K`, which is compact by
  -- the Arzelà–Ascoli theorem.
  set S : Set (ℝ →ᵤ V) := {f | Periodic (UniformFun.toFun f) 1 ∧ (∀ t, UniformFun.toFun f t ∈ K) ∧
    LipschitzWith C.toNNReal (UniformFun.toFun f)}
  have hScpt : IsCompact S := isCompact_setOf_periodic_lipschitzWith hK C.toNNReal
  have hmaps : MapsTo ℓ (Ici (a + 1)) S := fun s hs ↦
    have has : a < s := (lt_add_one a).trans_le hs
    ⟨hper s has, huK s has, by
      have h := hL.comp (LipschitzWith.prodMk_left s).lipschitzOnWith
        fun t (_ : t ∈ univ) ↦ ⟨has, trivial⟩
      rw [lipschitzOnWith_univ, mul_one] at h
      exact h⟩
  -- The loops depend `C`-Lipschitz continuously on `s`.
  have hcont : ContinuousOn ℓ (Ici (a + 1)) := by
    refine LipschitzOnWith.continuousOn (K := C.toNNReal) fun s hs s' hs' ↦
      UniformFun.edist_le.2 fun t ↦ ?_
    have hLs : LipschitzOnWith C.toNNReal (fun s ↦ u (s, t)) (Ioi a) := by
      simpa [Function.comp_def] using
        hL.comp (LipschitzWith.prodMk_right t).lipschitzOnWith fun s hs ↦ ⟨hs, trivial⟩
    exact hLs ((lt_add_one a).trans_le hs) ((lt_add_one a).trans_le hs')
  -- Its ω-limit points are periodic solutions in `K`, and these are isolated from each other.
  set O : Set (ℝ →ᵤ V) := {f | MapClusterPt f atTop ℓ}
  have hO : ∀ f ∈ O, Periodic (UniformFun.toFun f) 1 ∧
      (∀ t, HasDerivAt (UniformFun.toFun f) (X t (UniformFun.toFun f t)) t) ∧
      ∀ t, UniformFun.toFun f t ∈ K := by
    intro f hf
    have hfS : f ∈ S := by
      have h := (setOf_mapClusterPt_atTop_eq_iInter ℓ (a + 1)).subset hf
      exact closure_minimal hmaps.image_subset hScpt.isClosed
        (mem_iInter.1 h ⟨a + 1, mem_Ici.2 le_rfl⟩)
    obtain ⟨hfper, hf'⟩ :=
      periodic_and_hasDerivAt_of_mapClusterPt hu hper hK huK hX hXper hfin hC hf
    exact ⟨hfper, hf', hfS.2.1⟩
  have hdisc : IsDiscrete O := by
    refine isDiscrete_iff_forall_mem_exists_isOpen.2 fun x hx ↦ ?_
    obtain ⟨hxper, hx', hxK⟩ := hO x hx
    obtain ⟨ε, hε, hxε⟩ := hiso _ hxper hx' hxK hx
    refine ⟨Metric.eball x (ENNReal.ofReal ε), Metric.isOpen_eball, ?_⟩
    refine Subset.antisymm (fun y ⟨hyx, hy⟩ ↦ ?_) ?_
    · obtain ⟨hyper, hy', hyK⟩ := hO y hy
      exact hxε _ hyper hy' hyK hy fun t ↦
        edist_lt_ofReal.1 ((UniformFun.edist_le.1 le_rfl t).trans_lt hyx)
    · rintro y rfl
      exact ⟨Metric.mem_eball_self (ENNReal.ofReal_pos.2 hε), hx⟩
  obtain ⟨x, hxO, hx⟩ := exists_tendsto_atTop_of_setOf_mapClusterPt_subset_of_isTotallyDisconnected
    hScpt hcont hmaps hdisc.isTotallyDisconnected Subset.rfl
  obtain ⟨hxper, hx', _⟩ := hO x hxO
  exact ⟨UniformFun.toFun x, hxper, hx', UniformFun.tendsto_iff_tendstoUniformly.1 hx⟩

/-- **Convergence of the loops to an isolated periodic solution.** Let `X` be a continuous,
`1`-periodic time-dependent vector field and let `u` be `C¹` on the half-cylinder `s > a`, with
derivative bounded by `C` and with `1`-periodic loops `t ↦ u(s, t)` in a compact set `K`. Suppose
that the squared norm of the defect `∂_t u - X(t, u)` has finite integral over `(a, ∞) × [0, 1]`,
and that the `1`-periodic solutions of `x' = X(t, x)` in `K` are isolated: each has a uniform
neighbourhood containing no other. Then the loops converge uniformly, as `s → ∞`, to a single
`1`-periodic solution `x`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atTop (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1) (hK : IsCompact K)
    (huK : ∀ s, a < s → ∀ t, u (s, t) ∈ K) (hX : Continuous (uncurry X))
    (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    (hfin : ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤)
    (hC : ∀ z ∈ Ioi a ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C)
    (hiso : ∀ x : ℝ → V, Periodic x 1 → (∀ t, HasDerivAt x (X t (x t)) t) → (∀ t, x t ∈ K) →
      ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 → (∀ t, HasDerivAt y (X t (y t)) t) →
        (∀ t, y t ∈ K) → (∀ t, dist (y t) (x t) < ε) → y = x) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧
      TendstoUniformly (fun s t ↦ u (s, t)) x atTop :=
  exists_periodic_hasDerivAt_tendstoUniformly_atTop_of_mapClusterPt hu hper hK huK hX hXper hfin
    hC fun x hxper hx hxK _ ↦ (hiso x hxper hx hxK).imp fun _ ⟨hε, h⟩ ↦
      ⟨hε, fun y hyper hy hyK _ ↦ h y hyper hy hyK⟩

end Convergence

section NegativeEnd

open LinearIsometryEquiv (negFst)

/-! ### Negative ends

The defect only involves the `t`-derivative of `u`, so it is unchanged by the reflection
`(s, t) ↦ (-s, t)` of the cylinder. The loops of `u` on the half-cylinder `s < a` are the loops of
the reflected map `(s, t) ↦ u(-s, t)` on the half-cylinder `s > -a`, with the same defects, and the
results above transfer to the negative end `s → -∞`. -/

/-- **Loops with square-integrable defect accumulate at periodic orbits at the negative end.** Let
`X` be a continuous, `1`-periodic time-dependent vector field and let `u` be `C¹` on the
half-cylinder `s < a`, with `1`-periodic loops `t ↦ u(s, t)` in a compact set. If the squared norm
of the defect `∂_t u - X(t, u)` has finite integral over `(-∞, a) × [0, 1]`, then there are a
`1`-periodic solution `x` of `x' = X(t, x)` and `s_n → -∞`, with `s_n < a`, such that the loops
`t ↦ u(s_n, t)` converge uniformly to `x` and the `L²` norms of the defect over them tend to
`0`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_Iio_ne_top
    (hu : ContDiffOn ℝ 1 u (Iio a ×ˢ univ)) (hper : ∀ s, s < a → Periodic (fun t ↦ u (s, t)) 1)
    {K : Set V} (hK : IsCompact K) (huK : ∀ s, s < a → ∀ t, u (s, t) ∈ K)
    (hX : Continuous (uncurry X)) (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    (hfin : ∫⁻ z in Iio a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧
      ∃ φ : ℕ → ℝ, (∀ n, φ n < a) ∧ Tendsto φ atTop atBot ∧
        TendstoUniformly (fun n t ↦ u (φ n, t)) x atTop ∧
        Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, ‖sliceDefect X u (φ n, t)‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨x, hxper, hx, φ, hφa, hφ, hux, hdef⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_lintegral_ne_top (contDiffOn_comp_neg_fst hu)
      (fun s hs ↦ hper (-s) (neg_lt.1 hs)) hK (fun s hs ↦ huK (-s) (neg_lt.1 hs)) hX hXper
      (by rwa [setLIntegral_norm_sq_sliceDefect_comp_neg_fst])
  refine ⟨x, hxper, hx, fun n ↦ -φ n, fun n ↦ neg_lt.2 (hφa n),
    tendsto_neg_atTop_atBot.comp hφ, hux, ?_⟩
  simpa using hdef

/-- **Convergence of the loops to an isolated periodic solution at the negative end.** Let `X` be
a continuous, `1`-periodic time-dependent vector field and let `u` be `C¹` on the half-cylinder
`s < a`, with derivative bounded by `C` and with `1`-periodic loops `t ↦ u(s, t)` in a compact set
`K`. Suppose that the squared norm of the defect `∂_t u - X(t, u)` has finite integral over
`(-∞, a) × [0, 1]`, and that the `1`-periodic solutions of `x' = X(t, x)` in `K` are isolated: each
has a uniform neighbourhood containing no other. Then the loops converge uniformly, as `s → -∞`,
to a single `1`-periodic solution `x`. -/
theorem exists_periodic_hasDerivAt_tendstoUniformly_atBot {K : Set V} {C : ℝ}
    (hu : ContDiffOn ℝ 1 u (Iio a ×ˢ univ)) (hper : ∀ s, s < a → Periodic (fun t ↦ u (s, t)) 1)
    (hK : IsCompact K) (huK : ∀ s, s < a → ∀ t, u (s, t) ∈ K) (hX : Continuous (uncurry X))
    (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    (hfin : ∫⁻ z in Iio a ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) ≠ ⊤)
    (hC : ∀ z ∈ Iio a ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C)
    (hiso : ∀ x : ℝ → V, Periodic x 1 → (∀ t, HasDerivAt x (X t (x t)) t) → (∀ t, x t ∈ K) →
      ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 → (∀ t, HasDerivAt y (X t (y t)) t) →
        (∀ t, y t ∈ K) → (∀ t, dist (y t) (x t) < ε) → y = x) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧
      TendstoUniformly (fun s t ↦ u (s, t)) x atBot := by
  -- The reflection is an isometry of `ℝ × ℝ`, so it preserves the bound on the derivative.
  have hC' : ∀ z ∈ Ioi (-a) ×ˢ univ, ‖fderiv ℝ (fun z ↦ u (-z.1, z.2)) z‖ ≤ C := by
    intro z hz
    rw [fderiv_comp_neg_fst]
    exact (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ (negFst ℝ ℝ ℝ)).trans_le
      (hC _ ⟨neg_lt.1 hz.1, trivial⟩)
  obtain ⟨x, hxper, hx, hux⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_atTop (contDiffOn_comp_neg_fst hu)
      (fun s hs ↦ hper (-s) (neg_lt.1 hs)) hK (fun s hs ↦ huK (-s) (neg_lt.1 hs)) hX hXper
      (by rwa [setLIntegral_norm_sq_sliceDefect_comp_neg_fst]) hC' hiso
  refine ⟨x, hxper, hx, Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_⟩
  simpa only [Function.comp_apply, neg_neg] using
    tendsto_neg_atBot_atTop.eventually (Metric.tendstoUniformly_iff.1 hux ε hε)

end NegativeEnd

section Neck

variable {K : Set V}

/-- **Loops with small defect are close to periodic solutions.** Let `X` be a continuous,
`1`-periodic time-dependent vector field and `K` a compact set. For every `ε > 0` there is `δ > 0`
such that every `C¹`, `1`-periodic loop `γ` in `K` whose defect `γ' - X(t, γ)` has squared `L²` norm
below `δ` over `[0, 1]` is uniformly within `ε` of a `1`-periodic solution of `x' = X(t, x)` with
values in `K`. -/
theorem exists_pos_forall_exists_periodic_hasDerivAt_dist_lt (hK : IsCompact K)
    (hX : Continuous (uncurry X)) (hXper : ∀ v, Periodic (fun t ↦ X t v) 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ γ : ℝ → V, ContDiff ℝ 1 γ → Periodic γ 1 → (∀ t, γ t ∈ K) →
      ∫ t in (0 : ℝ)..1, ‖deriv γ t - X t (γ t)‖ ^ 2 < δ →
      ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧ (∀ t, x t ∈ K) ∧
        ∀ t, dist (γ t) (x t) < ε := by
  by_contra! h
  -- Loops with squared defect integrals below `1 / (n + 1)`, each uniformly `ε`-far from every
  -- periodic solution in `K`, have a subsequence converging to such a solution.
  choose γ hγ hper hγK hγX hfar using fun n : ℕ ↦ h (1 / (n + 1)) Nat.one_div_pos_of_nat
  obtain ⟨ψ, -, x, hxper, hx, hxK, hux⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral_deriv_sub hγ hper hK hγK hX
      hXper (squeeze_zero (fun n ↦ intervalIntegral.integral_nonneg zero_le_one
        fun t _ ↦ sq_nonneg _) (fun n ↦ (hγX n).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.1 hux ε hε).exists
  obtain ⟨t, ht⟩ := hfar (ψ n) x hxper hx hxK
  exact ht.not_gt (by rw [dist_comm]; exact hn t)

/-- **Isolated periodic solutions are uniformly separated.** Let `X` be a continuous, `1`-periodic
time-dependent vector field and `K` a compact set. If the `1`-periodic solutions of `x' = X(t, x)`
in `K` are isolated, each having a uniform neighbourhood containing no other, then there is
`ε > 0` such that two of them that are uniformly within `ε` of each other coincide. -/
theorem exists_pos_forall_eq_of_forall_dist_lt (hK : IsCompact K) (hX : Continuous (uncurry X))
    (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    (hiso : ∀ x : ℝ → V, Periodic x 1 → (∀ t, HasDerivAt x (X t (x t)) t) → (∀ t, x t ∈ K) →
      ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 → (∀ t, HasDerivAt y (X t (y t)) t) →
        (∀ t, y t ∈ K) → (∀ t, dist (y t) (x t) < ε) → y = x) :
    ∃ ε > 0, ∀ x y : ℝ → V, Periodic x 1 → (∀ t, HasDerivAt x (X t (x t)) t) →
      (∀ t, x t ∈ K) → Periodic y 1 → (∀ t, HasDerivAt y (X t (y t)) t) → (∀ t, y t ∈ K) →
      (∀ t, dist (x t) (y t) < ε) → x = y := by
  by_contra! h
  choose x y hxper hx hxK hyper hy hyK hxy hne using
    fun n : ℕ ↦ h (1 / (n + 1)) Nat.one_div_pos_of_nat
  -- Periodic solutions are `C¹` loops with vanishing defect, so a subsequence of the `x n`
  -- converges uniformly to a periodic solution `z` in `K`.
  have hderiv (n : ℕ) : deriv (x n) = fun t ↦ X t (x n t) := funext fun t ↦ (hx n t).deriv
  have hC1 (n : ℕ) : ContDiff ℝ 1 (x n) := by
    refine contDiff_one_iff_deriv.2 ⟨fun t ↦ (hx n t).differentiableAt, ?_⟩
    rw [hderiv]
    exact hX.comp (continuous_id.prodMk
      (continuous_iff_continuousAt.2 fun t ↦ (hx n t).continuousAt))
  obtain ⟨ψ, hψ, z, hzper, hz, hzK, hxz⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_of_tendsto_integral_deriv_sub hC1 hxper hK hxK hX
      hXper (by simp [hderiv])
  obtain ⟨ε, hε, hzε⟩ := hiso z hzper hz hzK
  -- Eventually both `x (ψ n)` and `y (ψ n)` lie in the uniform `ε`-neighbourhood of `z`.
  obtain ⟨n, hxn, hn⟩ := ((Metric.tendstoUniformly_iff.1 hxz (ε / 2) (half_pos hε)).and
    (hψ.tendsto_atTop.eventually ((tendsto_one_div_add_atTop_nhds_zero_nat).eventually
      (gt_mem_nhds (half_pos hε))))).exists
  have hxzn : x (ψ n) = z := hzε _ (hxper _) (hx _) (hxK _) fun t ↦ by
    rw [dist_comm]; exact (hxn t).trans (half_lt_self hε)
  have hyzn : y (ψ n) = z := hzε _ (hyper _) (hy _) (hyK _) fun t ↦
    calc dist (y (ψ n) t) (z t) ≤ dist (x (ψ n) t) (y (ψ n) t) + dist (z t) (x (ψ n) t) := by
          rw [dist_comm (x (ψ n) t)]; exact dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add ((hxy _ t).trans hn) (hxn t)
      _ = ε := add_halves ε
  exact hne _ (hxzn.trans hyzn.symm)

/-- Let every `C¹`, `1`-periodic loop in `K` with squared defect integral below `δ` be within
`e / 2` of a periodic solution in `K`. Let `u` be `C¹` on a strip `(a, b) × ℝ`, with derivative
bounded by `C ≥ 0` and `1`-periodic loops in `K`, and let `[s, s + h]` lie in `(a, b)`, where
`C h ≤ e / 2`. If the squared defect integrates to less than `h δ` over `(a, b) × [0, 1]`, then
the loop at `s` is within `e` of a periodic solution in `K`. -/
private theorem exists_periodic_hasDerivAt_forall_dist_lt_of_Icc_subset {b C δ e h s : ℝ}
    (hclose : ∀ γ : ℝ → V, ContDiff ℝ 1 γ → Periodic γ 1 → (∀ t, γ t ∈ K) →
      ∫ t in (0 : ℝ)..1, ‖deriv γ t - X t (γ t)‖ ^ 2 < δ →
      ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧ (∀ t, x t ∈ K) ∧
        ∀ t, dist (γ t) (x t) < e / 2)
    (hX : Continuous (uncurry X)) (hC₀ : 0 ≤ C) (hh : 0 < h) (hCh : C * h ≤ e / 2)
    (hu : ContDiffOn ℝ 1 u (Ioo a b ×ˢ univ)) (hper : ∀ s ∈ Ioo a b, Periodic (fun t ↦ u (s, t)) 1)
    (huK : ∀ s ∈ Ioo a b, ∀ t, u (s, t) ∈ K) (hC : ∀ z ∈ Ioo a b ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C)
    (hs : Icc s (s + h) ⊆ Ioo a b)
    (hE : ∫⁻ z in Ioo a b ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) <
      ENNReal.ofReal (h * δ)) :
    ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧ (∀ t, x t ∈ K) ∧
      ∀ t, dist (u (s, t)) (x t) < e := by
  -- Some loop at most `h` later has small defect, so it is within `e / 2` of a solution.
  obtain ⟨σ, hσ, hσδ⟩ := exists_mem_Icc_integral_norm_sq_sliceDefect_lt_of_setLIntegral_lt hu hX
    hh hs ((lintegral_mono_set (prod_mono hs le_rfl)).trans_lt hE)
  obtain ⟨hγ, hdef⟩ := contDiff_slice_and_sliceDefect_eq (X := X) hu (hs hσ)
  obtain ⟨x, hxper, hx, hxK, hxd⟩ := hclose _ hγ (hper σ (hs hσ)) (huK σ (hs hσ))
    (by simpa only [hdef] using hσδ)
  refine ⟨x, hxper, hx, hxK, fun t ↦ ?_⟩
  have hsσ : |s - σ| ≤ h := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hσ.1])]
    linarith [hσ.2]
  calc dist (u (s, t)) (x t) ≤ dist (u (s, t)) (u (σ, t)) + dist (u (σ, t)) (x t) :=
        dist_triangle _ _ _
    _ < e / 2 + e / 2 := add_lt_add_of_le_of_lt ((dist_le_mul_abs_sub_of_norm_fderiv_le
        (hu.differentiableOn one_ne_zero) hC
        (hs ⟨le_rfl, by linarith⟩) (hs hσ) t).trans ((mul_le_mul_of_nonneg_left hsσ hC₀).trans
          hCh)) (hxd t)
    _ = e := add_halves e

/-- **A long cylinder with small defect stays near a single periodic solution.** Let `X` be a
continuous, `1`-periodic time-dependent vector field and `K` a compact set in which the
`1`-periodic solutions of `x' = X(t, x)` are isolated, each having a uniform neighbourhood
containing no other. For every bound `C` and every `ε > 0` there are `δ > 0` and a margin `η > 0`
with the following property, uniformly in the length of the strip. Let `u` be `C¹` on a strip
`(a, b) × ℝ` with `a + η ≤ b - η`, with derivative bounded by `C` and `1`-periodic loops
`t ↦ u(s, t)` in `K`. If the squared defect `‖∂_t u - X(t, u)‖²` integrates to less than `δ` over
`(a, b) × [0, 1]`, then there is a single `1`-periodic solution `x` in `K` such that every loop at
`s ∈ [a + η, b - η]` is uniformly within `ε` of `x`.

Each loop with small defect is close to some periodic solution
(`TauCeti.exists_pos_forall_exists_periodic_hasDerivAt_dist_lt`); the loops vary continuously
in `s`, and distinct periodic solutions are uniformly separated
(`TauCeti.exists_pos_forall_eq_of_forall_dist_lt`), so by connectedness of `[a + η, b - η]` the
solution does not change along the strip. -/
theorem exists_pos_forall_exists_periodic_hasDerivAt_forall_dist_lt (hK : IsCompact K)
    (hX : Continuous (uncurry X)) (hXper : ∀ v, Periodic (fun t ↦ X t v) 1)
    (hiso : ∀ x : ℝ → V, Periodic x 1 → (∀ t, HasDerivAt x (X t (x t)) t) → (∀ t, x t ∈ K) →
      ∃ ε > 0, ∀ y : ℝ → V, Periodic y 1 → (∀ t, HasDerivAt y (X t (y t)) t) →
        (∀ t, y t ∈ K) → (∀ t, dist (y t) (x t) < ε) → y = x)
    (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ η > 0, ∀ ⦃u : ℝ × ℝ → V⦄ ⦃a b : ℝ⦄, a + η ≤ b - η →
      ContDiffOn ℝ 1 u (Ioo a b ×ˢ univ) → (∀ s ∈ Ioo a b, Periodic (fun t ↦ u (s, t)) 1) →
      (∀ s ∈ Ioo a b, ∀ t, u (s, t) ∈ K) → (∀ z ∈ Ioo a b ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C) →
      ∫⁻ z in Ioo a b ×ˢ Icc 0 1, ENNReal.ofReal (‖sliceDefect X u z‖ ^ 2) <
        ENNReal.ofReal δ →
      ∃ x : ℝ → V, Periodic x 1 ∧ (∀ t, HasDerivAt x (X t (x t)) t) ∧ (∀ t, x t ∈ K) ∧
        ∀ s ∈ Icc (a + η) (b - η), ∀ t, dist (u (s, t)) (x t) < ε := by
  obtain ⟨ε₀, hε₀, hsep⟩ := exists_pos_forall_eq_of_forall_dist_lt hK hX hXper hiso
  -- Work at the scale `e ≤ ε` with `3 e ≤ ε₀`, and with a margin `η` such that `C η < e / 2`.
  set e := min ε (ε₀ / 3)
  have he : 0 < e := lt_min hε (by positivity)
  obtain ⟨δ₁, hδ₁, hclose⟩ :=
    exists_pos_forall_exists_periodic_hasDerivAt_dist_lt hK hX hXper (half_pos he)
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  set η := e / (2 * (C' + 1))
  have hη : 0 < η := by positivity
  have hCη : C' * η < e / 2 := by
    rw [show C' * η = e / 2 * (C' / (C' + 1)) by simp only [η]; field_simp]
    exact mul_lt_of_lt_one_right (half_pos he) ((div_lt_one (by positivity)).2 (lt_add_one C'))
  refine ⟨η / 2 * δ₁, by positivity, η, hη, fun u a b hab hu hper huK hC hE ↦ ?_⟩
  have hC'u : ∀ z ∈ Ioo a b ×ˢ univ, ‖fderiv ℝ u z‖ ≤ C' := fun z hz ↦
    (hC z hz).trans (le_max_left _ _)
  have hIsub : Icc (a + η) (b - η) ⊆ Ioo a b := fun s hs ↦
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- Every loop of the window is within `e` of a periodic solution.
  have hnear (s : ℝ) (hs : s ∈ Icc (a + η) (b - η)) :=
    exists_periodic_hasDerivAt_forall_dist_lt_of_Icc_subset hclose hX hC' (half_pos hη)
      (by nlinarith) hu hper huK hC'u
      (fun σ hσ ↦ ⟨by linarith [hs.1, hσ.1], by linarith [hs.2, hσ.2]⟩) hE
  -- Periodic solutions within `e` of loops at times at most `η` apart are within `5 e / 2` of each
  -- other, hence coincide.
  have hsame : ∀ s ∈ Icc (a + η) (b - η), ∀ s' ∈ Icc (a + η) (b - η), |s - s'| ≤ η →
      ∀ x x' : ℝ → V, Periodic x 1 → (∀ t, HasDerivAt x (X t (x t)) t) → (∀ t, x t ∈ K) →
      Periodic x' 1 → (∀ t, HasDerivAt x' (X t (x' t)) t) → (∀ t, x' t ∈ K) →
      (∀ t, dist (u (s, t)) (x t) < e) → (∀ t, dist (u (s', t)) (x' t) < e) → x = x' := by
    intro s hs s' hs' hss' x x' hxper hx hxK hx'per hx' hx'K hxd hx'd
    refine hsep x x' hxper hx hxK hx'per hx' hx'K fun t ↦ ?_
    calc dist (x t) (x' t) ≤ dist (x t) (u (s, t)) + dist (u (s, t)) (u (s', t)) +
          dist (u (s', t)) (x' t) := dist_triangle4 _ _ _ _
      _ < e + e / 2 + e := by
          gcongr
          · rw [dist_comm]; exact hxd t
          · exact (dist_le_mul_abs_sub_of_norm_fderiv_le (hu.differentiableOn one_ne_zero) hC'u
              (hIsub hs) (hIsub hs') t).trans_lt
              ((mul_le_mul_of_nonneg_left hss' hC').trans_lt hCη)
          · exact hx'd t
      _ ≤ ε₀ := by linarith [min_le_right ε (ε₀ / 3)]
  -- The solution near the first loop of the window is near every loop of it.
  obtain ⟨x, hxper, hx, hxK, hxd⟩ := hnear (a + η) ⟨le_rfl, hab⟩
  refine ⟨x, hxper, hx, hxK, fun s hs t ↦ ?_⟩
  refine (forall_dist_lt_of_forall_exists_dist_lt
    (P := fun y ↦ Periodic y 1 ∧ (∀ t, HasDerivAt y (X t (y t)) t) ∧ ∀ t, y t ∈ K) hη
    (fun s hs ↦ ?_) (fun s hs s' hs' hss' y y' hy hy' ↦ hsame s hs s' hs' hss' y y' hy.1 hy.2.1
      hy.2.2 hy'.1 hy'.2.1 hy'.2.2) ⟨hxper, hx, hxK⟩ hxd s hs t).trans_le (min_le_left _ _)
  obtain ⟨y, hyper, hy, hyK, hyd⟩ := hnear s hs
  exact ⟨y, ⟨hyper, hy, hyK⟩, hyd⟩

end Neck

section Segment

/-! ### Uniform asymptotics at an end, along a segment of maps -/

variable {x : ℝ → V} {l : Filter ℝ}

/-- If the loops of `u` converge uniformly to a continuous loop `x` and the slice defect
`∂t u - X_t(u)` tends uniformly to zero, then `∂t u` converges uniformly to `t ↦ X_t(x t)`. -/
theorem tendstoUniformlyOn_fderiv_apply_of_sliceDefect [ProperSpace V] (hX : Continuous (uncurry X))
    (hx : Continuous x) (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect X u (s, t)) 0 l (Icc 0 1)) :
    TendstoUniformlyOn (fun s t ↦ fderiv ℝ u (s, t) (0, 1)) (fun t ↦ X t (x t)) l (Icc 0 1) := by
  refine ((hδ.fun_add (isCompact_Icc.tendstoUniformlyOn_comp_prodMk_of_continuous hX
    hx.continuousOn hux)).congr (.of_forall fun s t _ ↦ ?_)).congr_right fun t _ ↦ ?_
  · simp only [sliceDefect_def, uncurry_apply_pair, sub_add_cancel]
  · simp only [Pi.zero_apply, uncurry_apply_pair, zero_add]

/-- If the loops of `u` converge uniformly to a continuous loop `x` and the slice defect
`∂t u - X_t(u)` tends uniformly to zero, then so does the slice defect `∂t u - Y_t(u)` for every
continuous time-dependent vector field `Y` that agrees with `X` along `x`. -/
theorem tendstoUniformlyOn_sliceDefect_of_apply_eq [ProperSpace V] {Y : ℝ → V → V}
    (hX : Continuous (uncurry X)) (hY : Continuous (uncurry Y)) (hx : Continuous x)
    (hXY : ∀ t, Y t (x t) = X t (x t))
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect X u (s, t)) 0 l (Icc 0 1)) :
    TendstoUniformlyOn (fun s t ↦ sliceDefect Y u (s, t)) 0 l (Icc 0 1) := by
  refine ((tendstoUniformlyOn_fderiv_apply_of_sliceDefect hX hx hux hδ).fun_sub
    (isCompact_Icc.tendstoUniformlyOn_comp_prodMk_of_continuous hY hx.continuousOn hux)).congr
      (.of_forall fun s t _ ↦ ?_) |>.congr_right fun t _ ↦ ?_
  · simp only [sliceDefect_def, uncurry_apply_pair]
  · simp only [Pi.zero_apply, uncurry_apply_pair, hXY, sub_self]

/-- A `C¹` map of the cylinder and its derivative in `t` are bounded on the strip `ℝ × [0, 1]`
when its loops converge uniformly to continuous loops at both ends and its slice defects for
continuous vector fields tend uniformly to zero there. -/
theorem exists_forall_norm_le_and_norm_fderiv_apply_le_of_sliceDefect [ProperSpace V]
    {Y : ℝ → V → V} (hX : Continuous (uncurry X)) (hY : Continuous (uncurry Y))
    (hu : ContDiff ℝ 1 u) {xm xp : ℝ → V} (hxm : Continuous xm) (hxp : Continuous xp)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn (fun s t ↦ sliceDefect X u (s, t)) 0 atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn (fun s t ↦ sliceDefect Y u (s, t)) 0 atTop (Icc 0 1)) :
    ∃ C, ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t)‖ ≤ C ∧ ‖fderiv ℝ u (s, t) (0, 1)‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := exists_forall_norm_le_of_tendstoUniformlyOn isCompact_Icc
    hu.continuous.continuousOn huxm huxp
  obtain ⟨C₂, hC₂⟩ := exists_forall_norm_le_of_tendstoUniformlyOn isCompact_Icc
    (f := fun z ↦ fderiv ℝ u z (0, 1))
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
    (tendstoUniformlyOn_fderiv_apply_of_sliceDefect hX hxm huxm hδm)
    (tendstoUniformlyOn_fderiv_apply_of_sliceDefect hY hxp huxp hδp)
  exact ⟨max C₁ C₂, fun s t ht ↦
    ⟨(hC₁ s t ht).trans (le_max_left _ _), (hC₂ s t ht).trans (le_max_right _ _)⟩⟩

/-- If two differentiable maps have loops converging uniformly to the same continuous loop `x` at
an end, with slice defects tending uniformly to zero there, then so does every point
`u + μ (u' - u)` of the segment between them. -/
theorem tendstoUniformlyOn_add_smul_sub_and_sliceDefect [ProperSpace V]
    (hX : Continuous (uncurry X))
    {u' : ℝ × ℝ → V} (hu : Differentiable ℝ u) (hu' : Differentiable ℝ u') (hx : Continuous x)
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect X u (s, t)) 0 l (Icc 0 1))
    (hu'x : TendstoUniformlyOn (fun s t ↦ u' (s, t)) x l (Icc 0 1))
    (hδ' : TendstoUniformlyOn (fun s t ↦ sliceDefect X u' (s, t)) 0 l (Icc 0 1)) (μ : ℝ) :
    TendstoUniformlyOn (fun s t ↦ (u + μ • (u' - u)) (s, t)) x l (Icc 0 1) ∧
      TendstoUniformlyOn (fun s t ↦ sliceDefect X (u + μ • (u' - u)) (s, t)) 0 l
        (Icc 0 1) := by
  have hv : TendstoUniformlyOn (fun s t ↦ (u + μ • (u' - u)) (s, t)) x l (Icc 0 1) :=
    (hux.fun_add ((hu'x.fun_sub hux).const_smul μ)).congr_right fun t _ ↦ by simp
  refine ⟨hv, ?_⟩
  have hd := tendstoUniformlyOn_fderiv_apply_of_sliceDefect hX hx hux hδ
  have hd' := tendstoUniformlyOn_fderiv_apply_of_sliceDefect hX hx hu'x hδ'
  refine (((hd.fun_add ((hd'.fun_sub hd).const_smul μ)).fun_sub
    (isCompact_Icc.tendstoUniformlyOn_comp_prodMk_of_continuous hX hx.continuousOn hv)).congr
      (.of_forall fun s t _ ↦ ?_)).congr_right fun t _ ↦ ?_
  · simp [sliceDefect_def, fderiv_add_smul_sub_apply (hu _) (hu' _)]
  · simp

end Segment

end TauCeti
