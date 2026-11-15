/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Topology.Compactness.Compact
public import TauCeti.Topology.Compactness.Normed
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Compact-parameter integration

This file develops regularity of weighted integrals over compact parameter spaces, using
Mathlib's continuity and differentiation theorems for integrals. Continuous differentiability
is preserved at every finite or infinite order and with independent domain and codomain universes.
These results supply the analytic regularity used by smooth Hadamard factorization, differential
forms and kernel integrals.

The file also differentiates a parametrized interval integral `x ↦ ∫ t in a..b, G (x, t)` in a
real parameter `x` at a point `x₀`, assuming only that `G` is `C¹` on an open set containing the
compact segment `{x₀} × [a, b]`: the derivative is the integral of the partial derivative of `G`
in `x`.

Iterated derivatives also pass under an interval integral `x ↦ ∫ s in a..b, u s x` of a family of
`C^N` functions, provided each derivative `D^k (u s) x`, `k ≤ N`, is measurable in `s` and bounded
uniformly in `x` by an integrable function of `s`
(`TauCeti.iteratedFDeriv_intervalIntegral`, `TauCeti.contDiff_intervalIntegral`). No joint
regularity in `(s, x)` is needed, and the bounds may blow up at the ends of the interval. This is
the form needed for time integrals of heat-kernel convolutions, whose derivatives are singular at
the final time.

For a compact parameter space `α` mapped continuously into a topological space `P` by `ι`, an
integrable weight `g` on `α` preserves integrability and continuity of the integrand in a
topological parameter space `E`. No countability assumption on these spaces is needed.

When `E` and `P` are normed spaces and `F` is `C^n` on an open set `W ⊆ E × P`, the integral
`x ↦ ∫ y, g y • F (x, ι y) ∂μ` is `C^n` on every set `U` with `U × ι(α) ⊆ W`
(`TauCeti.contDiffOn_integral_smul_of_contDiffOn`), with derivative the integral of the partial
derivatives of `F` in `x` (`TauCeti.hasFDerivAt_integral_smul_of_contDiffOn`).  The weight need
not be continuous; this is the regularity of kernel integrals such as the Poisson integral of
integrable boundary data on a sphere.

The parameter space `α` itself need carry no differentiable structure. If `F (x, y)` is `C^n` in
`x` on an open set `U` for each `y`, and its partial derivatives in `x` of every order `k ≤ n`
are jointly continuous on `U × α`, then `x ↦ ∫ y, g y • F (x, y) ∂μ` is `C^n` on `U`
(`TauCeti.contDiffOn_integral_smul_of_continuousOn_iteratedFDeriv`), with derivative the integral
of the partial derivatives (`TauCeti.hasFDerivAt_integral_smul_of_continuousOn_fderiv`). This is
the form needed for averages over a compact group acting smoothly. A `C^n` integrand on an open
subset of `E × P`, for a normed space `P`, has jointly continuous partial derivatives in `x`
(`ContDiffOn.continuousOn_iteratedFDeriv_partial`, in
`TauCeti.Analysis.Calculus.IteratedFDeriv.Prod`).

If `F` is only `C^n` on a set `W ⊇ s × ι(α)` with unique derivatives, not necessarily open, for a
convex set `s` with unique derivatives, the integral is `C^n` on `s`
(`Convex.contDiffOn_integral_smul_of_contDiffOn`), with derivative within `s` the integral of the
partial derivatives within `s` (`Convex.hasFDerivWithinAt_integral_smul_of_contDiffOn`). This
is the regularity of the Poincaré homotopy operator on a closed half-ball.

For a family `f : Y → E → F` with compact topological parameter `Y`, smooth slices on an
open set and jointly continuous spatial jets, integration preserves smoothness
(`TauCeti.contDiffOn_integral_of_continuous_jets`) and has the integrated spatial Taylor series
(`TauCeti.hasFTaylorSeriesUpToOn_integral_of_continuous_jets`). All iterated spatial derivatives
commute with integration (`TauCeti.iteratedFDeriv_integral_of_continuous_jets`).

## References

* Lean-Atiyah-Singer, `AtiyahSinger/Analysis/CompactJetIntegral.lean`:
  the source formalization of continuous-jet integration.
  <https://github.com/alpha-squared-labs/Lean-Atiyah-Singer>.
* Mathlib, `hasFDerivAt_integral_of_continuousOn_fderiv`:
  differentiation of compact-parameter integrals.
* H. B. Lawson, Jr. and M.-L. Michelsohn, *Spin Geometry*, Chapter III,
  proof of Theorem 9.7, p. 214: compact-group averaging of operator homotopies.
  The continuous-jet integral lemmas are supplementary analytic inputs in the
  source formalization.
  <https://doi.org/10.1515/9781400883912>.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff Interval

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace TauCeti

/-- **Differentiation under a parametrized interval integral.** If `G` is `C¹` on an open set
containing the segment `{x₀} × [a, b]`, then the partial derivative of `G` in the first variable
is interval integrable along that segment, and `x ↦ ∫ t in a..b, G (x, t)` is differentiable at
`x₀` with derivative the integral of this partial derivative. -/
theorem hasDerivAt_intervalIntegral_of_contDiffOn {G : ℝ × ℝ → F}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) {x₀ a b : ℝ}
    (hsub : {x₀} ×ˢ Set.uIcc a b ⊆ U) :
    IntervalIntegrable (fun t ↦ fderiv ℝ G (x₀, t) (1, 0)) volume a b ∧
      HasDerivAt (fun x ↦ ∫ t in a..b, G (x, t))
        (∫ t in a..b, fderiv ℝ G (x₀, t) (1, 0)) x₀ := by
  obtain ⟨u, v, huo, _, hu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_uIcc hU hsub
  have hx₀u : x₀ ∈ u := hu (Set.mem_singleton x₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (huo.mem_nhds hx₀u)
  have hK : Metric.closedBall x₀ (ε / 2) ×ˢ Set.uIcc a b ⊆ U := fun z hz ↦
    huv ⟨hball (Metric.closedBall_subset_ball (half_lt_self hε) hz.1), hv hz.2⟩
  -- the partial derivative in the first variable, continuous on `U`
  set G' : ℝ × ℝ → F := fun z ↦ fderiv ℝ G z (1, 0)
  have hG'cont : ContinuousOn G' U :=
    (hG.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ (ε / 2)).prod isCompact_uIcc)
    |>.exists_bound_of_continuousOn (hG'cont.mono hK)
  have hslice : ∀ {x : ℝ}, x ∈ u → ∀ {W : ℝ × ℝ → F}, ContinuousOn W U →
      ContinuousOn (fun t ↦ W (x, t)) (Set.uIcc a b) := by
    intro x hx W hW
    exact hW.comp
      (continuous_const.prodMk continuous_id : Continuous fun t : ℝ ↦ (x, t)).continuousOn
      fun t ht ↦ huv ⟨hx, hv ht⟩
  have hdiff : ∀ t ∈ Ι a b, ∀ x ∈ Metric.closedBall x₀ (ε / 2),
      HasDerivAt (fun x ↦ G (x, t)) (G' (x, t)) x := by
    intro t ht x hx
    have hz : (x, t) ∈ U := hK ⟨hx, Set.uIoc_subset_uIcc ht⟩
    have hGz : HasFDerivAt G (fderiv ℝ G (x, t)) (x, t) :=
      ((hG.differentiableOn one_ne_zero (x, t) hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    exact hGz.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x t))
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun x t ↦ G (x, t)) (F' := fun x t ↦ G' (x, t))
    (bound := fun _ ↦ C) (Metric.closedBall_mem_nhds x₀ (half_pos hε)) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_)
  · filter_upwards [huo.mem_nhds hx₀u] with x hx
    exact ((hslice hx hG.continuousOn).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · exact (hslice hx₀u hG.continuousOn).intervalIntegrable
  · exact ((hslice hx₀u hG'cont).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc
  · exact Filter.Eventually.of_forall fun t ht x hx ↦
      hC (x, t) ⟨hx, Set.uIoc_subset_uIcc ht⟩
  · exact Filter.Eventually.of_forall fun t ht x hx ↦ hdiff t ht x hx

/-! ### Iterated derivatives under an interval integral -/

section IteratedFDeriv

variable [CompleteSpace F] {μ : Measure ℝ} {a b : ℝ} {u : ℝ → E → F}

/-- **Differentiating an iterated derivative under an interval integral.** Let `u s` be `C^(m+1)`
for almost every `s ∈ Ι a b`, with `m`-th and `(m+1)`-st derivatives measurable in `s` and bounded
uniformly in `x` by integrable functions of `s`. Then `x ↦ ∫ s in a..b, D^m (u s) x` has derivative
`∫ s in a..b, D^(m+1) (u s) x`, curried in its first variable. -/
theorem hasFDerivAt_intervalIntegral_iteratedFDeriv {m : ℕ}
    (hu : ∀ᵐ s ∂μ.restrict (Ι a b), ContDiff ℝ (m + 1) (u s))
    (hmeas₀ : ∀ x,
      AEStronglyMeasurable (fun s ↦ iteratedFDeriv ℝ m (u s) x) (μ.restrict (Ι a b)))
    (hmeas : ∀ x,
      AEStronglyMeasurable (fun s ↦ iteratedFDeriv ℝ (m + 1) (u s) x) (μ.restrict (Ι a b)))
    {bound₀ bound : ℝ → ℝ} (hb₀ : IntervalIntegrable bound₀ μ a b)
    (hb : IntervalIntegrable bound μ a b)
    (hub₀ : ∀ᵐ s ∂μ.restrict (Ι a b), ∀ x, ‖iteratedFDeriv ℝ m (u s) x‖ ≤ bound₀ s)
    (hub : ∀ᵐ s ∂μ.restrict (Ι a b), ∀ x, ‖iteratedFDeriv ℝ (m + 1) (u s) x‖ ≤ bound s)
    (x : E) :
    HasFDerivAt (fun x ↦ ∫ s in a..b, iteratedFDeriv ℝ m (u s) x ∂μ)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F
        (∫ s in a..b, iteratedFDeriv ℝ (m + 1) (u s) x ∂μ)) x := by
  set e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F
  have hcomm : e (∫ s in a..b, iteratedFDeriv ℝ (m + 1) (u s) x ∂μ) =
      ∫ s in a..b, e (iteratedFDeriv ℝ (m + 1) (u s) x) ∂μ := by
    -- The spaces are named explicitly: with `Fin`-indexed multilinear maps, unification does
    -- not otherwise match the two normed-group instances on the domain of `e`.
    have := LinearIsometry.intervalIntegral_comp_comm (𝕜 := ℝ) (μ := μ) (a := a) (b := b)
      (E := ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) ↦ E) F)
      (F := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F)
      e.toLinearIsometry fun s ↦ iteratedFDeriv ℝ (m + 1) (u s) x
    exact this.symm
  rw [ae_restrict_iff' measurableSet_uIoc] at hu hub
  rw [hcomm]
  -- The derivative of `D^m (u s)` is `D^(m+1) (u s)` up to the currying isometry `e`.
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ)
    (F' := fun y s ↦ e (iteratedFDeriv ℝ (m + 1) (u s) y)) Filter.univ_mem
    (Filter.Eventually.of_forall hmeas₀) (hb₀.mono_fun' (hmeas₀ x) (hub₀.mono fun s hs ↦ hs x))
    (e.continuous.comp_aestronglyMeasurable (hmeas x)) ?_ hb ?_
  · filter_upwards [hub] with s hs hsI y _
    rw [LinearIsometryEquiv.norm_map]
    exact hs hsI y
  · filter_upwards [hu] with s hs hsI y _
    exact ((hs hsI).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self m)
      y).hasFDerivAt

omit [CompleteSpace F] in
/-- **Continuity of an interval integral of iterated derivatives.** If `u s` is `C^k` for almost
every `s ∈ Ι a b` and `D^k (u s) x` is measurable in `s` and bounded uniformly in `x` by an
integrable function of `s`, then `x ↦ ∫ s in a..b, D^k (u s) x` is continuous. -/
theorem continuous_intervalIntegral_iteratedFDeriv {k : ℕ}
    (hu : ∀ᵐ s ∂μ.restrict (Ι a b), ContDiff ℝ k (u s))
    (hmeas : ∀ x,
      AEStronglyMeasurable (fun s ↦ iteratedFDeriv ℝ k (u s) x) (μ.restrict (Ι a b)))
    {bound : ℝ → ℝ} (hb : IntervalIntegrable bound μ a b)
    (hub : ∀ᵐ s ∂μ.restrict (Ι a b), ∀ x, ‖iteratedFDeriv ℝ k (u s) x‖ ≤ bound s) :
    Continuous fun x ↦ ∫ s in a..b, iteratedFDeriv ℝ k (u s) x ∂μ := by
  rw [ae_restrict_iff' measurableSet_uIoc] at hu hub
  refine intervalIntegral.continuous_of_dominated_interval hmeas (fun x ↦ ?_) hb ?_
  · filter_upwards [hub] with s hs hsI using hs hsI x
  · filter_upwards [hu] with s hs hsI using (hs hsI).continuous_iteratedFDeriv le_rfl

/-- **Iterated derivatives under an interval integral.** If, for almost every `s ∈ Ι a b`, `u s`
is `C^N` and each derivative `D^k (u s) x` with `k ≤ N` is measurable in `s` and bounded uniformly
in `x` by an integrable function of `s`, then for `k ≤ N` the `k`-th derivative of
`x ↦ ∫ s in a..b, u s x` is `x ↦ ∫ s in a..b, D^k (u s) x`. -/
theorem iteratedFDeriv_intervalIntegral {N : ℕ}
    (hu : ∀ᵐ s ∂μ.restrict (Ι a b), ContDiff ℝ N (u s))
    (hmeas : ∀ k ≤ N, ∀ x,
      AEStronglyMeasurable (fun s ↦ iteratedFDeriv ℝ k (u s) x) (μ.restrict (Ι a b)))
    {bound : ℕ → ℝ → ℝ} (hb : ∀ k ≤ N, IntervalIntegrable (bound k) μ a b)
    (hub : ∀ k ≤ N, ∀ᵐ s ∂μ.restrict (Ι a b), ∀ x, ‖iteratedFDeriv ℝ k (u s) x‖ ≤ bound k s)
    {k : ℕ} (hk : k ≤ N) :
    iteratedFDeriv ℝ k (fun x ↦ ∫ s in a..b, u s x ∂μ) =
      fun x ↦ ∫ s in a..b, iteratedFDeriv ℝ k (u s) x ∂μ := by
  induction k with
  | zero =>
    funext x
    simp_rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.intervalIntegral_comp_comm
      _).symm
  | succ k ih =>
    funext x
    have hu' : ∀ᵐ s ∂μ.restrict (Ι a b), ContDiff ℝ (k + 1) (u s) :=
      hu.mono fun s hs ↦ hs.of_le (by exact_mod_cast hk)
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih (by omega),
      (hasFDerivAt_intervalIntegral_iteratedFDeriv hu' (hmeas k (by omega)) (hmeas (k + 1) hk)
        (hb k (by omega)) (hb (k + 1) hk) (hub k (by omega)) (hub (k + 1) hk) x).fderiv,
      LinearIsometryEquiv.symm_apply_apply]

/-- **Smoothness of an interval integral of a smooth family.** If, for almost every `s ∈ Ι a b`,
`u s` is `C^N` and each derivative `D^k (u s) x` with `k ≤ N` is measurable in `s` and bounded
uniformly in `x` by an integrable function of `s`, then `x ↦ ∫ s in a..b, u s x` is `C^N`. The
bounds may blow up at the ends of the interval, as long as they stay integrable. -/
theorem contDiff_intervalIntegral {N : ℕ}
    (hu : ∀ᵐ s ∂μ.restrict (Ι a b), ContDiff ℝ N (u s))
    (hmeas : ∀ k ≤ N, ∀ x,
      AEStronglyMeasurable (fun s ↦ iteratedFDeriv ℝ k (u s) x) (μ.restrict (Ι a b)))
    {bound : ℕ → ℝ → ℝ} (hb : ∀ k ≤ N, IntervalIntegrable (bound k) μ a b)
    (hub : ∀ k ≤ N, ∀ᵐ s ∂μ.restrict (Ι a b), ∀ x, ‖iteratedFDeriv ℝ k (u s) x‖ ≤ bound k s) :
    ContDiff ℝ N fun x ↦ ∫ s in a..b, u s x ∂μ := by
  refine contDiff_iff_continuous_differentiable.2 ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · have hk' : k ≤ N := by exact_mod_cast hk
    rw [iteratedFDeriv_intervalIntegral hu hmeas hb hub hk']
    exact continuous_intervalIntegral_iteratedFDeriv
      (hu.mono fun s hs ↦ hs.of_le (by exact_mod_cast hk')) (hmeas k hk') (hb k hk') (hub k hk')
  · have hk' : k + 1 ≤ N := by exact_mod_cast Order.add_one_le_of_lt hk
    rw [iteratedFDeriv_intervalIntegral hu hmeas hb hub (by omega)]
    exact fun x ↦ (hasFDerivAt_intervalIntegral_iteratedFDeriv
      (hu.mono fun s hs ↦ hs.of_le (by exact_mod_cast hk')) (hmeas k (by omega))
      (hmeas (k + 1) hk') (hb k (by omega)) (hb (k + 1) hk') (hub k (by omega)) (hub (k + 1) hk')
      x).differentiableAt

end IteratedFDeriv

/-! ### Integration against a weight over a compact parameter space -/

section CompactParameter

open Filter Set
open scoped Topology

variable {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [OpensMeasurableSpace α] {μ : Measure α} {g : α → ℝ}

section Topological

variable {E P : Type*} [TopologicalSpace E] [TopologicalSpace P] {ι : α → P} {W : Set (E × P)}

/-- An integrable weight on a compact space times a function continuous along `{x} × ι(α)` is
integrable. -/
theorem integrable_smul_of_continuousOn {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : E × P → H} (hg : Integrable g μ) (hι : Continuous ι) (hF : ContinuousOn F W) {x : E}
    (hx : ∀ y, (x, ι y) ∈ W) :
    Integrable (fun y ↦ g y • F (x, ι y)) μ := by
  have hφ : Continuous fun y ↦ F (x, ι y) := hF.comp_continuous (continuous_const.prodMk hι) hx
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  have hm := hφ.stronglyMeasurable_of_support_subset_isCompact isCompact_univ (subset_univ _)
  exact hg.smul_bdd C hm.aestronglyMeasurable (ae_of_all _ fun y ↦ hC y (mem_univ y))

/-- Integration against an integrable weight over a compact parameter space is continuous in a
parameter `x` of the integrand, at any `x₀` with `{x₀} × ι(α)` inside the open set where the
integrand is continuous. -/
theorem continuousAt_integral_smul_of_continuousOn {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι) (hW : IsOpen W)
    (hF : ContinuousOn F W) {x₀ : E} (hx₀ : ∀ y, (x₀, ι y) ∈ W) :
    ContinuousAt (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) x₀ := by
  have hc : ContinuousOn (fun p : E × α ↦ F (p.1, ι p.2))
      ({x : E | ∀ y, (x, ι y) ∈ W} ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn fun p hp ↦ hp.1 p.2
  have hi := continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
    (ContinuousLinearMap.lsmul ℝ ℝ) isCompact_univ (f := fun x y ↦ F (x, ι y)) hc
    (fun _ _ _ h ↦ absurd (mem_univ _) h) hg.integrableOn
  exact hi.continuousAt ((isOpen_forall_prodMk_mem hι hW).mem_nhds hx₀)

end Topological

/-! ### Parameters with continuous partial derivatives

The parameter space `α` carries no differentiable structure. The integrand is only required to
be `C^n` in `x` for each fixed parameter, with its partial derivatives in `x` of every order up to
`n` jointly continuous in `(x, y)`. This is the setting of an average over a compact group, which
is a manifold but not an open subset of a normed space. The results for a `C^n` integrand on an
open subset of `E × P` below are the special case of the integrand `(x, y) ↦ F (x, ι y)`. -/

section PartialDerivatives

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}

/-- **Differentiation under the integral sign with continuous partial derivatives.** If `F` is
continuous on `U × α`, differentiable in `x` on the open set `U` for every parameter `y`, and its
partial derivative in `x` is continuous on `U × α`, then integrating `F (x, y)` against an
integrable weight `g` over the compact space `α` is differentiable on `U`, with derivative the
integral of the partial derivatives. -/
theorem hasFDerivAt_integral_smul_of_continuousOn_fderiv {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : E × α → G} (hg : Integrable g μ) (hU : IsOpen U)
    (hF : ContinuousOn F (U ×ˢ univ)) (hdiff : ∀ y, DifferentiableOn ℝ (fun x ↦ F (x, y)) U)
    (hD : ContinuousOn (fun p : E × α ↦ fderiv ℝ (fun x ↦ F (x, p.2)) p.1) (U ×ˢ univ))
    {x₀ : E} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x ↦ ∫ y, g y • F (x, y) ∂μ)
      (∫ y, g y • fderiv ℝ (fun x ↦ F (x, y)) x₀ ∂μ) x₀ := by
  set D : E × α → E →L[ℝ] G := fun p ↦ fderiv ℝ (fun x ↦ F (x, p.2)) p.1
  have hW : IsOpen (U ×ˢ (univ : Set α)) := hU.prod isOpen_univ
  have hmem : ∀ y, (x₀, id y) ∈ U ×ˢ (univ : Set α) := fun y ↦ ⟨hx₀, mem_univ y⟩
  have hderiv : ∀ p ∈ U ×ˢ (univ : Set α), HasFDerivAt (fun x ↦ F (x, p.2)) (D p) p.1 :=
    fun p hp ↦ ((hdiff p.2).differentiableAt (hU.mem_nhds hp.1)).hasFDerivAt
  obtain ⟨C, hC⟩ := isCompact_univ.exists_eventually_norm_le hW
    (fun y _ ↦ hD.continuousAt (hW.mem_nhds (hmem y))) (fun y _ ↦ hmem y)
  simp only [mem_univ, forall_const] at hC
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun x y ↦ g y • D (x, y))
    (bound := fun y ↦ ‖g y‖ * C) hC ?_
    (integrable_smul_of_continuousOn hg continuous_id hF hmem)
    (integrable_smul_of_continuousOn hg continuous_id hD hmem).aestronglyMeasurable ?_
    (hg.norm.mul_const C) ?_
  · filter_upwards [hC] with x hx
    exact (integrable_smul_of_continuousOn hg continuous_id hF
      fun y ↦ (hx y).1).aestronglyMeasurable
  · refine ae_of_all _ fun y x hx ↦ ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hx y).2 (norm_nonneg _)
  · exact ae_of_all _ fun y x hx ↦ (hderiv (x, y) (hx y).1).const_smul (g y)

/-- **Smoothness of integrals with continuous partial derivatives.** Let `F` be `C^n` in `x` on
the open set `U` for every parameter `y` of the compact space `α`, with partial derivatives in `x`
of every order `k ≤ n` jointly continuous on `U × α`. Then integrating `F (x, y)` against an
integrable weight `g` is `C^n` in `x` on `U`. -/
theorem contDiffOn_integral_smul_of_continuousOn_iteratedFDeriv {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ∞} {F : E × α → G} (hg : Integrable g μ)
    (hU : IsOpen U) (hF : ∀ y, ContDiffOn ℝ n (fun x ↦ F (x, y)) U)
    (hcont : ∀ k : ℕ, (k : ℕ∞) ≤ n → ContinuousOn
      (fun p : E × α ↦ iteratedFDeriv ℝ k (fun x ↦ F (x, p.2)) p.1) (U ×ˢ univ)) :
    ContDiffOn ℝ n (fun x ↦ ∫ y, g y • F (x, y) ∂μ) U := by
  rw [contDiffOn_iff_forall_nat_le]
  intro m hm
  have hkn : ∀ k ≤ m, (k : ℕ∞) ≤ n := fun k hk ↦ (Nat.cast_le.mpr hk).trans hm
  refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ ↦ ?_
  -- Near `x₀`, the partial derivatives of every order `k ≤ m` are bounded uniformly in `y`.
  have hW : IsOpen (U ×ˢ (univ : Set α)) := hU.prod isOpen_univ
  have hmem : ∀ y, (x₀, id y) ∈ U ×ˢ (univ : Set α) := fun y ↦ ⟨hx₀, mem_univ y⟩
  choose C hC using fun k : Iic m ↦ isCompact_univ.exists_eventually_norm_le hW
    (fun y _ ↦ (hcont k (hkn k k.2)).continuousAt (hW.mem_nhds (hmem y))) (fun y _ ↦ hmem y)
  obtain ⟨V, hV, hVo, hx₀V⟩ := mem_nhds_iff.1 (eventually_all.2 hC)
  refine ⟨V, hVo, hx₀V, ?_⟩
  have hs : IsOpen (U ∩ V) := hU.inter hVo
  have hUV : ∀ x ∈ U ∩ V, ∀ y, (x, id y) ∈ U ×ˢ (univ : Set α) := fun x hx y ↦ ⟨hx.1, mem_univ y⟩
  -- The weighted Taylor series of the integrand, in the form required by Mathlib.
  have hT (y : α) : HasFTaylorSeriesUpToOn m (fun x ↦ g y • F (x, y))
      (fun x k ↦ g y • iteratedFDeriv ℝ k (fun x ↦ F (x, y)) x) (U ∩ V) :=
    ((((hF y).of_le (by exact_mod_cast hm)).mono inter_subset_left).ftaylorSeriesWithin
      hs.uniqueDiffOn |>.continuousLinearMap_comp (g y • ContinuousLinearMap.id ℝ G)).congr_series
      fun k _ x hx ↦ by
        ext v
        simp [ftaylorSeriesWithin, iteratedFDerivWithin_of_isOpen k hs hx]
  have hInt := hasFTaylorSeriesUpToOn_integral_of_le_bound (μ := μ) (n := (m : ℕ∞))
    (bound := fun k y ↦ ‖g y‖ * if hk : k ≤ m then C ⟨k, hk⟩ else 0) hs
    (fun x hx k hk ↦ (integrable_smul_of_continuousOn (F := fun p : E × α ↦
      iteratedFDeriv ℝ k (fun x ↦ F (x, p.2)) p.1) hg continuous_id
      (hcont k (hkn k (by exact_mod_cast hk))) (hUV x hx)).aestronglyMeasurable)
    (ae_of_all _ fun y x hx k hk ↦ ?_) (fun k _ ↦ hg.norm.mul_const _) (ae_of_all _ hT)
  · exact hInt.contDiffOn
  · have hk' : k ≤ m := by exact_mod_cast hk
    simp only [norm_smul, hk', ↓reduceDIte]
    exact mul_le_mul_of_nonneg_left ((hV hx.2 ⟨k, hk'⟩ y (mem_univ y)).2) (norm_nonneg _)

end PartialDerivatives

variable {E : Type u} {P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] {ι : α → P} {W : Set (E × P)}

/-- **Differentiation under the integral sign over a compact parameter space.** If `F` is `C¹`
on an open set `W ⊆ E × P` containing `{x₀} × ι(α)`, then integrating `F (x, ι y)` against an
integrable weight `g` is differentiable at `x₀`, with derivative the integral of the partial
derivative of `F` in `x`. -/
theorem hasFDerivAt_integral_smul_of_contDiffOn {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι) (hW : IsOpen W)
    (hF : ContDiffOn ℝ 1 F W) {x₀ : E} (hx₀ : ∀ y, (x₀, ι y) ∈ W) :
    HasFDerivAt (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ)
      (∫ y, g y • fderiv ℝ (fun x ↦ F (x, ι y)) x₀ ∂μ) x₀ := by
  -- `{x₀} × ι(α)` has an open neighbourhood `U × ι(α)` inside `W`, by compactness of `α`.
  let U : Set E := {x | ∀ y, (x, ι y) ∈ W}
  have hc : Continuous fun p : E × α ↦ (p.1, ι p.2) :=
    continuous_fst.prodMk (hι.comp continuous_snd)
  have hU : IsOpen U := isOpen_forall_prodMk_mem hι hW
  have hUW : ∀ p ∈ U ×ˢ (univ : Set α), (p.1, ι p.2) ∈ W := fun p hp ↦ hp.1 p.2
  have hFy (y : α) : ContDiffOn ℝ 1 (fun x ↦ F (x, ι y)) U :=
    hF.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx ↦ hx y
  exact hasFDerivAt_integral_smul_of_continuousOn_fderiv (F := fun p ↦ F (p.1, ι p.2)) hg hU
    (hF.continuousOn.comp hc.continuousOn hUW) (fun y ↦ (hFy y).differentiableOn one_ne_zero)
    ((ContDiffOn.fderiv_partial_of_isOpen (m := 0) (by simpa using hF) hW).continuousOn.comp
      hc.continuousOn hUW) hx₀

/-- **Smoothness of integrals over a compact parameter space.** If `F` is `C^n` on an open set
`W ⊆ E × P` and `{x} × ι(α) ⊆ W` for every `x` in a set `U`, then integrating `F (x, ι y)`
against an integrable weight `g` is `C^n` in `x` on `U`. -/
theorem contDiffOn_integral_smul_of_contDiffOn {G : Type v} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {n : ℕ∞} {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hW : IsOpen W) (hF : ContDiffOn ℝ n F W) {U : Set E}
    (hUW : ∀ x ∈ U, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ n (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) U := by
  set U' : Set E := {x : E | ∀ y, (x, ι y) ∈ W}
  refine ContDiffOn.mono (s := U') ?_ hUW
  have hFy (y : α) : ContDiffOn ℝ n (fun x ↦ F (x, ι y)) U' :=
    hF.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx ↦ hx y
  exact contDiffOn_integral_smul_of_continuousOn_iteratedFDeriv (F := fun p ↦ F (p.1, ι p.2)) hg
    (isOpen_forall_prodMk_mem hι hW) hFy fun k hk ↦
      (hF.continuousOn_iteratedFDeriv_partial hW (by exact_mod_cast hk)).comp
        (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn fun p hp ↦ hp.1 p.2

/-- The first-order remainder of an integral against a weight over a compact parameter space is
the integral of the pointwise remainder: if `F` and a candidate partial derivative `D` are
continuous along `{x} × ι(α)` and `{x₀} × ι(α)`, then the integral of
`g y • F (x, ι y)`, minus that of `g y • F (x₀, ι y)`, minus the integral of
`g y • D (x₀, ι y)` applied to `x - x₀`, is the integral of the pointwise remainder. -/
theorem integral_smul_sub_sub_apply {P : Type*} [TopologicalSpace P] {ι : α → P}
    {W : Set (E × P)} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E × P → G} {D : E × P → E →L[ℝ] G} (hg : Integrable g μ) (hι : Continuous ι)
    (hF : ContinuousOn F W) (hD : ContinuousOn D W) {x x₀ : E} (hx : ∀ y, (x, ι y) ∈ W)
    (hx₀ : ∀ y, (x₀, ι y) ∈ W) :
    (∫ y, g y • F (x, ι y) ∂μ) - (∫ y, g y • F (x₀, ι y) ∂μ) -
        (∫ y, g y • D (x₀, ι y) ∂μ) (x - x₀) =
      ∫ y, g y • (F (x, ι y) - F (x₀, ι y) - D (x₀, ι y) (x - x₀)) ∂μ := by
  have hFx := integrable_smul_of_continuousOn hg hι hF hx
  have hFx₀ := integrable_smul_of_continuousOn hg hι hF hx₀
  have hDx : ContinuousOn (fun p ↦ D p (x - x₀)) W :=
    (ContinuousLinearMap.apply ℝ G (x - x₀)).continuous.comp_continuousOn hD
  rw [ContinuousLinearMap.integral_apply (integrable_smul_of_continuousOn hg hι hD hx₀)]
  simp only [smul_apply, smul_sub]
  rw [integral_sub (by exact hFx.sub hFx₀ :
      Integrable (fun y ↦ g y • F (x, ι y) - g y • F (x₀, ι y)) μ)
    (integrable_smul_of_continuousOn hg hι hDx hx₀), integral_sub hFx hFx₀]

/-! ### Parameters in a convex set

The parameter `x` now ranges over a convex set `s`, which need not be open, and the integrand is
only assumed to be `C^n` on a set `W ⊇ s × ι(α)` with unique derivatives. Derivatives are taken
within `s`. This is the setting of a closed half-ball, the image of a boundary chart. -/

section Convex

variable {s : Set E}

/-- **Differentiation under the integral sign within a convex set.** If `F` is `C¹` on a set
`W ⊆ E × P` with unique derivatives, `s` is convex, and `s × ι(α) ⊆ W`, then integrating
`F (x, ι y)` against an integrable weight `g` is differentiable within `s` at every point `x₀` of
`s` at which `s` has unique derivatives, with derivative the integral of the partial derivatives
of `F` in `x` within `s`. -/
theorem _root_.Convex.hasFDerivWithinAt_integral_smul_of_contDiffOn {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hs : Convex ℝ s) (hW : UniqueDiffOn ℝ W) (hF : ContDiffOn ℝ 1 F W)
    (hsW : ∀ x ∈ s, ∀ y, (x, ι y) ∈ W) {x₀ : E} (hx₀ : x₀ ∈ s)
    (hsu : UniqueDiffWithinAt ℝ s x₀) :
    HasFDerivWithinAt (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ)
      (∫ y, g y • fderivWithin ℝ (fun x ↦ F (x, ι y)) s x₀ ∂μ) s x₀ := by
  -- the partial derivative in `x`, continuous on `W`
  set D : E × P → E →L[ℝ] G := fun p ↦ (fderivWithin ℝ F W p).comp (.inl ℝ E P)
  have hD : ContinuousOn D W :=
    (ContinuousLinearMap.precomp G (.inl ℝ E P)).continuous.comp_continuousOn
      (hF.continuousOn_fderivWithin hW le_rfl)
  have hderiv (x : E) (hx : x ∈ s) (y : α) :
      HasFDerivWithinAt (fun x ↦ F (x, ι y)) (D (x, ι y)) s x :=
    (hF.differentiableOn one_ne_zero _ (hsW x hx y)).hasFDerivWithinAt.comp x
      (hasFDerivAt_prodMk_left x (ι y)).hasFDerivWithinAt fun x' hx' ↦ hsW x' hx' y
  -- the partial derivative is uniformly close to its value at `x₀` for `x` near `x₀` in `s`
  have hunif (ε : ℝ) (hε : 0 < ε) :
      ∃ v ∈ 𝓝[s] x₀, ∀ x ∈ v, ∀ y ∈ univ, dist (D (x, ι y)) (D (x₀, ι y)) < ε :=
    isCompact_univ.mem_uniformity_of_prod (f := fun x y ↦ D (x, ι y))
      (hD.comp (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn
        fun p hp ↦ hsW _ hp.1 _) hx₀ (Metric.dist_mem_uniformity hε)
  have hD₀ : (∫ y, g y • fderivWithin ℝ (fun x ↦ F (x, ι y)) s x₀ ∂μ) =
      ∫ y, g y • D (x₀, ι y) ∂μ :=
    integral_congr_ae (ae_of_all _ fun y ↦ by
      dsimp only
      rw [(hderiv x₀ hx₀ y).fderivWithin hsu])
  rw [hD₀, hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set ε := c / ((∫ y, ‖g y‖ ∂μ) + 1)
  have hgn : 0 ≤ ∫ y, ‖g y‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  have hε : 0 < ε := div_pos hc (by linarith)
  obtain ⟨v, hv, hvD⟩ := hunif ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hv
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hδ)]
    with x hx hxδ
  -- the mean value inequality on the convex set `s ∩ ball x₀ δ`, for each parameter `y`
  have hsδ : Convex ℝ (s ∩ Metric.ball x₀ δ) := hs.inter (convex_ball x₀ δ)
  have hpt (y : α) : ‖F (x, ι y) - F (x₀, ι y) - D (x₀, ι y) (x - x₀)‖ ≤ ε * ‖x - x₀‖ :=
    hsδ.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun z ↦ F (z, ι y))
      (f' := fun z ↦ D (z, ι y))
      (fun z (hz : z ∈ s ∩ Metric.ball x₀ δ) ↦ (hderiv z hz.1 y).mono inter_subset_left)
      (fun z hz ↦ by
        simpa only [dist_eq_norm] using (hvD z (hball ⟨hz.2, hz.1⟩) y (mem_univ y)).le)
      ⟨hx₀, Metric.mem_ball_self hδ⟩ ⟨hx, hxδ⟩
  calc ‖(∫ y, g y • F (x, ι y) ∂μ) - (∫ y, g y • F (x₀, ι y) ∂μ) -
        (∫ y, g y • D (x₀, ι y) ∂μ) (x - x₀)‖
      = ‖∫ y, g y • (F (x, ι y) - F (x₀, ι y) - D (x₀, ι y) (x - x₀)) ∂μ‖ :=
        congrArg norm (integral_smul_sub_sub_apply hg hι hF.continuousOn hD (hsW x hx)
          (hsW x₀ hx₀))
    _ ≤ ∫ y, ‖g y‖ * (ε * ‖x - x₀‖) ∂μ := by
        refine norm_integral_le_of_norm_le ((hg.norm.mul_const _)) (ae_of_all _ fun y ↦ ?_)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hpt y) (norm_nonneg _)
    _ = (∫ y, ‖g y‖ ∂μ) * ε * ‖x - x₀‖ := by rw [integral_mul_const, mul_assoc]
    _ ≤ c * ‖x - x₀‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

private theorem _root_.Convex.contDiffOn_integral_smul_nat {G : Type max u v}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (m : ℕ) {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) (hW : UniqueDiffOn ℝ W)
    (hF : ContDiffOn ℝ m F W) (hsW : ∀ x ∈ s, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ m (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) s := by
  induction m generalizing G with
  | zero =>
      have hc : ContinuousOn (fun p : E × α ↦ F (p.1, ι p.2)) (s ×ˢ univ) :=
        hF.continuousOn.comp (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn
          fun p hp ↦ hsW _ hp.1 _
      refine contDiffOn_zero.2 <|
        (continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
          (ContinuousLinearMap.lsmul ℝ ℝ) isCompact_univ (f := fun x y ↦ F (x, ι y)) hc
          (fun _ _ _ h ↦ absurd (mem_univ _) h) hg.integrableOn).congr fun x _ ↦ by simp
  | succ m ih =>
      have hF' : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1) F W := by exact_mod_cast hF
      have hderiv := fun x hx ↦ hs.hasFDerivWithinAt_integral_smul_of_contDiffOn hg hι hW
        (hF'.of_le le_add_self) hsW hx (hsu x hx)
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderivWithin hsu]
      refine ⟨fun x hx ↦ (hderiv x hx).differentiableWithinAt, fun h ↦ absurd h (by simp), ?_⟩
      refine (ih (F := fun p ↦ (fderivWithin ℝ F W p).comp (.inl ℝ E P))
        (((ContinuousLinearMap.precomp G (.inl ℝ E P)).contDiff.comp_contDiffOn
          (hF'.fderivWithin hW le_rfl)).congr fun _ _ ↦ by simp)).congr fun x hx ↦ ?_
      rw [(hderiv x hx).fderivWithin (hsu x hx)]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      have hpart : HasFDerivWithinAt (fun x ↦ F (x, ι y))
          ((fderivWithin ℝ F W (x, ι y)).comp (.inl ℝ E P)) s x :=
        ((hF'.of_le le_add_self).differentiableOn one_ne_zero _
          (hsW x hx y)).hasFDerivWithinAt.comp x
            (hasFDerivAt_prodMk_left x (ι y)).hasFDerivWithinAt fun x' hx' ↦ hsW x' hx' y
      dsimp only
      rw [hpart.fderivWithin (hsu x hx)]

/-- **Smoothness of integrals over a compact parameter space, within a convex set.** If `F` is
`C^n` on a set `W ⊆ E × P` with unique derivatives, `s` is convex with unique derivatives, and
`s × ι(α) ⊆ W`, then integrating `F (x, ι y)` against an integrable weight `g` is `C^n` in `x`
on `s`. -/
theorem _root_.Convex.contDiffOn_integral_smul_of_contDiffOn {G : Type v} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {n : ℕ∞} {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι)
    (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) (hW : UniqueDiffOn ℝ W) (hF : ContDiffOn ℝ n F W)
    (hsW : ∀ x ∈ s, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ n (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) s := by
  let eG : Type max u v := ULift.{u} G
  let isoG : eG ≃L[ℝ] G := ContinuousLinearEquiv.ulift
  have he : ContDiffOn ℝ n (fun x ↦ ∫ y, g y • isoG.symm (F (x, ι y)) ∂μ) s := by
    rw [contDiffOn_iff_forall_nat_le]
    intro m hm
    exact hs.contDiffOn_integral_smul_nat m hg hι hsu hW
      (isoG.symm.contDiff.comp_contDiffOn (hF.of_le (by exact_mod_cast hm))) hsW
  refine (isoG.contDiff.comp_contDiffOn he).congr fun x _ ↦ ?_
  have hsmul : ∀ y, g y • isoG.symm (F (x, ι y)) = isoG.symm (g y • F (x, ι y)) :=
    fun y ↦ (map_smul _ _ _).symm
  simp only [Function.comp_apply, hsmul, ContinuousLinearEquiv.integral_comp_comm,
    ContinuousLinearEquiv.apply_symm_apply]

end Convex

end CompactParameter

/-! ### Integrals of continuous spatial jets

The compact parameter space in this section has only a topology. Joint continuity of
every spatial derivative and smoothness of each slice allow differentiation under
the integral at every order.
-/

section ContinuousJets

open Filter Set Topology

variable {Y H F : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure Y} [IsFiniteMeasure μ]
  {f : Y → H → F} {s : Set H} (hs : IsOpen s)
  (hf : ∀ y, ContDiffOn ℝ ∞ (f y) s)
  (hjets : ∀ k : ℕ,
    ContinuousOn (fun p : Y × H ↦ iteratedFDeriv ℝ k (f p.1) p.2) (univ ×ˢ s))

include hs hf hjets

/-- The spatial Taylor series of a compact continuous-jet integral consists of the integrated
spatial jets. -/
theorem hasFTaylorSeriesUpToOn_integral_of_continuous_jets :
    HasFTaylorSeriesUpToOn ∞ (fun x ↦ ∫ y, f y x ∂μ)
      (fun x k ↦ ∫ y, iteratedFDeriv ℝ k (f y) x ∂μ) s := by
  have hjet (k : ℕ) (y : Y) (x : H) (hx : x ∈ s) :
      HasFDerivAt (iteratedFDeriv ℝ k (f y))
        (iteratedFDeriv ℝ (k + 1) (f y) x).curryLeft x :=
    ((hf y x hx).contDiffAt (hs.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k) |>.hasFDerivAt
  have hderiv (k : ℕ) (x : H) (hx : x ∈ s) :
      HasFDerivAt (fun z ↦ ∫ y, iteratedFDeriv ℝ k (f y) z ∂μ)
        (∫ y, iteratedFDeriv ℝ (k + 1) (f y) x ∂μ).curryLeft x := by
    let C := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (k + 1) ↦ H) F).toContinuousLinearEquiv
    have hcurry (g : H [×k + 1]→L[ℝ] F) : C g = g.curryLeft := by
      ext v w
      simp only [C, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        continuousMultilinearCurryLeftEquiv_apply, ContinuousMultilinearMap.curryLeft_apply]
    have hvalue : ContinuousOn (fun p : H × Y ↦ iteratedFDeriv ℝ k (f p.2) p.1)
        (s ×ˢ univ) :=
      (hjets k).comp continuous_swap.continuousOn (fun _ hp ↦ ⟨hp.2, hp.1⟩)
    have hnext : ContinuousOn (fun p : H × Y ↦ C (iteratedFDeriv ℝ (k + 1) (f p.2) p.1))
        (s ×ˢ univ) :=
      C.continuous.comp_continuousOn ((hjets (k + 1)).comp continuous_swap.continuousOn
        (fun _ hp ↦ ⟨hp.2, hp.1⟩))
    have hdiff : ContinuousOn (fun p : H × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f p.2)) p.1)
        (s ×ˢ univ) := hnext.congr (fun p hp ↦
          (hcurry _).trans (hjet k p.2 p.1 hp.1).fderiv.symm)
    have hD := hasFDerivAt_integral_of_continuousOn_fderiv (𝕜 := ℝ) (μ := μ)
      (F := fun z y ↦ iteratedFDeriv ℝ k (f y) z)
      (hs.mem_nhds hx) isCompact_univ MeasurableSet.univ (measure_ne_top _ _) Subset.rfl
      hvalue (fun y _ z hz ↦ (hjet k y z hz).differentiableAt.differentiableWithinAt) hdiff
    simp only [setIntegral_univ] at hD
    have heq : (fun y ↦ fderiv ℝ (iteratedFDeriv ℝ k (f y)) x) =
        (fun y ↦ C (iteratedFDeriv ℝ (k + 1) (f y) x)) :=
      funext fun y ↦ (hjet k y x hx).fderiv.trans (hcurry _).symm
    rw [heq] at hD
    -- Commute the integral with the equivalence, then identify its value by left currying.
    have hcomm := ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := μ)
      (E := H [×k + 1]→L[ℝ] F) (F := H →L[ℝ] H [×k]→L[ℝ] F)
      C (fun y ↦ iteratedFDeriv ℝ (k + 1) (f y) x)
    rwa [hcomm, hcurry] at hD
  constructor
  · intro x _
    let C := (continuousMultilinearCurryFin0 ℝ H F).toContinuousLinearEquiv
    have hcomm := ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := μ)
      (E := H [×0]→L[ℝ] F) (F := F) C
      (fun y ↦ iteratedFDeriv ℝ 0 (f y) x)
    -- At degree zero, the currying equivalence evaluates a zero-argument multilinear map.
    simpa only [C, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply,
      ContinuousMultilinearMap.curry0_apply] using hcomm.symm
  · intro k _ x hx
    exact (hderiv k x hx).hasFDerivWithinAt
  · intro k _
    apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
    · exact (hjets k).comp continuous_swap.continuousOn
        (fun _ hp ↦ ⟨mem_univ _, hp.1⟩)
    · intro x y _ hy
      exact (hy (mem_univ y)).elim

/-- A compact family with jointly continuous spatial jets has a smooth integral. -/
theorem contDiffOn_integral_of_continuous_jets :
    ContDiffOn ℝ ∞ (fun x ↦ ∫ y, f y x ∂μ) s :=
  (hasFTaylorSeriesUpToOn_integral_of_continuous_jets (μ := μ) hs hf hjets).contDiffOn

/-- Every spatial derivative of a compact continuous jet integral is the integral of that jet. -/
theorem iteratedFDeriv_integral_of_continuous_jets (k : ℕ) {x : H} (hx : x ∈ s) :
    iteratedFDeriv ℝ k (fun z ↦ ∫ y, f y z ∂μ) x =
      ∫ y, iteratedFDeriv ℝ k (f y) x ∂μ := by
  have hseries := hasFTaylorSeriesUpToOn_integral_of_continuous_jets (μ := μ) hs hf hjets
  have hsmooth := hseries.contDiffOn
  have heq := hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := k)
    (by simp) hs.uniqueDiffOn hx
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn
    (((hsmooth x hx).contDiffAt (hs.mem_nhds hx)).of_le (by simp)) hx] at heq
  exact heq.symm

end ContinuousJets

end TauCeti
