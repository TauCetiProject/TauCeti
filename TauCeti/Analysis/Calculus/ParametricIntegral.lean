/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Topology.Compactness.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Analysis.Convex.Topology

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
the final time. As an application, for a continuous bilinear map `L` and a compactly supported
`C^i` factor `V`, the spatial iterated derivatives of the radial integrand
`y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)` (`t ∈ [0, 1]`) are bounded pointwise
(`TauCeti.norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le`) and uniformly across `[0, 1] × E`
(`TauCeti.exists_norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le`), yielding a linear seminorm
bound on `y ↦ ∫ t in 0..1, t ^ k • L (f (lineMap x₀ y t)) (V y)` along segments from `x₀`
(`TauCeti.exists_norm_iteratedFDeriv_intervalIntegral_pow_smul_clm_apply_lineMap_le`).

For a compact parameter space `α` mapped continuously into a topological space `P` by `ι`, an
integrable weight `g` on `α` preserves integrability and continuity of the integrand in a
topological parameter space `E`. No countability assumption on these spaces is needed.

When `E` and `P` are normed spaces and `F` is `C^n` on an open set `W ⊆ E × P`, the integral
`x ↦ ∫ y, g y • F (x, ι y) ∂μ` is `C^n` on every open set `U` with `U × ι(α) ⊆ W`
(`TauCeti.contDiffOn_integral_smul_of_contDiffOn`), with derivative the integral of the partial
derivatives of `F` in `x` (`TauCeti.hasFDerivAt_integral_smul_of_contDiffOn`).  The weight need
not be continuous; this is the regularity of kernel integrals such as the Poisson integral of
integrable boundary data on a sphere.

The parameter may also range over a convex set `s` with unique derivatives that need not be open:
if `F` is `C^n` on a set `W ⊇ s × ι(α)` with unique derivatives, the integral is `C^n` on `s`
(`Convex.contDiffOn_integral_smul_of_contDiffOn`), with derivative within `s` the integral of the
partial derivatives within `s` (`Convex.hasFDerivWithinAt_integral_smul_of_contDiffOn`). This
is the regularity of the Poincaré homotopy operator on a closed half-ball.
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

/-! ### Spatial derivatives of radial bilinear integrands -/

section RadialBilinear

open AffineMap Filter Set

/-- Pointwise `m`-th spatial derivative bound for a radial bilinear integrand
`z ↦ t ^ k • L (f (lineMap x₀ z t)) (V z)` with `t ∈ [0, 1]`. -/
theorem norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le
    {G E' H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x₀ : E) (k : ℕ) (L : G →L[ℝ] E' →L[ℝ] H)
    {V : E → E'} {m : ℕ} (hV : ContDiff ℝ m V) {M : ℕ → ℝ} {y : E}
    (hM : ∀ j ≤ m, ‖iteratedFDeriv ℝ j V y‖ ≤ M j)
    {f : E → G} (hf : ContDiff ℝ m f) {D : ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hD : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f (lineMap x₀ y t)‖ ≤ D) :
    ‖iteratedFDeriv ℝ m (fun z ↦ t ^ k • L (f (lineMap x₀ z t)) (V z)) y‖ ≤
      (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (‖L‖ * M (m - j))) * D := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 (Nat.zero_le _))
  have ht_id : ‖t • ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_right ht.1 ContinuousLinearMap.norm_id_le).trans ht.2
  have htk_id : ‖(t ^ k) • ContinuousLinearMap.id ℝ H‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg ht.1 _)]
    exact (mul_le_of_le_one_right (pow_nonneg ht.1 _) ContinuousLinearMap.norm_id_le).trans
      (pow_le_one₀ ht.1 ht.2)
  have hray_cont : ContDiff ℝ m (fun z ↦ f (lineMap x₀ z t)) := by
    simp only [lineMap_apply_module']
    exact hf.comp (((contDiff_id.sub contDiff_const).const_smul t).add contDiff_const)
  -- Bound the derivatives of `z ↦ L (f (lineMap x₀ z t))` using `0 ≤ t ≤ 1`.
  have hray_norm {j : ℕ} (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j (fun z ↦ L (f (lineMap x₀ z t))) y‖ ≤ ‖L‖ * D := by
    have hj' : (j : WithTop ℕ∞) ≤ m := by exact_mod_cast hj
    have hcompL : (fun z ↦ L (f (lineMap x₀ z t))) = L ∘ (fun z ↦ f (lineMap x₀ z t)) := rfl
    rw [hcompL]
    refine (L.norm_iteratedFDeriv_comp_left hray_cont.contDiffAt hj').trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg L)
    have hshift : ContDiff ℝ m (fun z ↦ f (z + (1 - t) • x₀)) :=
      hf.comp (contDiff_id.add contDiff_const)
    have hline : (fun z ↦ f (lineMap x₀ z t)) =
        (fun z ↦ f (z + (1 - t) • x₀)) ∘ (t • ContinuousLinearMap.id ℝ E) := by
      funext z
      simp [lineMap_apply_module, add_comm]
    have hpt : (t • ContinuousLinearMap.id ℝ E) y + (1 - t) • x₀ = lineMap x₀ y t := by
      simp [lineMap_apply_module, add_comm]
    rw [hline, (t • ContinuousLinearMap.id ℝ E).iteratedFDeriv_comp_right hshift y hj',
      iteratedFDeriv_comp_add_right, hpt]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (hD j hj)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) ht_id
  -- Apply the Leibniz bound to `z ↦ L (f (lineMap x₀ z t)) (V z)` and absorb `t ^ k`.
  have hu_eq : (fun z ↦ t ^ k • L (f (lineMap x₀ z t)) (V z)) =
      ((t ^ k) • ContinuousLinearMap.id ℝ H) ∘ fun z ↦ L (f (lineMap x₀ z t)) (V z) := rfl
  have hclm_cont : ContDiff ℝ m (fun z ↦ L (f (lineMap x₀ z t)) (V z)) :=
    (L.contDiff.comp hray_cont).clm_apply hV
  rw [hu_eq]
  refine (((t ^ k) • ContinuousLinearMap.id ℝ H).norm_iteratedFDeriv_comp_left
    hclm_cont.contDiffAt le_rfl).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _) htk_id).trans ?_
  refine (norm_iteratedFDeriv_clm_apply (L.contDiff.comp hray_cont) hV y le_rfl).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj ↦ ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hMj : 0 ≤ M (m - j) := (norm_nonneg _).trans (hM (m - j) (Nat.sub_le m j))
  calc (m.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun z ↦ L (f (lineMap x₀ z t))) y‖ *
        ‖iteratedFDeriv ℝ (m - j) V y‖
      ≤ (m.choose j : ℝ) * (‖L‖ * D) * M (m - j) := by
        gcongr
        exacts [hray_norm hjm, hM (m - j) (Nat.sub_le m j)]
    _ = (m.choose j : ℝ) * (‖L‖ * M (m - j)) * D := by ring

/-- **Global derivative domination for a compactly supported radial bilinear integrand.** If `V`
is `C^i` with compact support and `f` is `C^i`, then the spatial derivatives of
`y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)` of order at most `i` are bounded uniformly in
`t ∈ [0, 1]` and `z : E`. -/
theorem exists_norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le
    {G E' H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x₀ : E) (k : ℕ) (L : G →L[ℝ] E' →L[ℝ] H)
    {V : E → E'} {i : ℕ} (hV : ContDiff ℝ i V) (hVc : HasCompactSupport V)
    {f : E → G} (hf : ContDiff ℝ i f) :
    ∃ C : ℝ, ∀ m ≤ i, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z,
      ‖iteratedFDeriv ℝ m (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) z‖ ≤ C := by
  -- Bound the derivatives of the compactly supported factor `V` globally on `E`.
  have hVbd : ∀ m ≤ i, ∃ M : ℝ, ∀ y, ‖iteratedFDeriv ℝ m V y‖ ≤ M := fun m hm ↦
    Continuous.bounded_above_of_compact_support
      (hV.continuous_iteratedFDeriv (by exact_mod_cast hm)) (hVc.iteratedFDeriv m)
  choose! M hM using hVbd
  have hM0 {m : ℕ} (hm : m ≤ i) : 0 ≤ M m := (norm_nonneg _).trans (hM m hm x₀)
  -- Bound the derivatives of `f` on the compact cone over `tsupport V`.
  let K' : Set E := ⋃ y ∈ tsupport V, segment ℝ x₀ y
  have hK' : IsCompact K' := hVc.biUnion_segment x₀
  have hfbd : ∀ j ≤ i, ∃ Cf : ℝ, ∀ z ∈ K', ‖iteratedFDeriv ℝ j f z‖ ≤ Cf := fun j hj ↦
    hK'.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn
  choose! Cf hCf using hfbd
  let Df : ℝ := ∑ j ∈ Finset.range (i + 1), |Cf j|
  have hDf0 : 0 ≤ Df := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hDf {j : ℕ} (hj : j ≤ i) {z : E} (hz : z ∈ K') : ‖iteratedFDeriv ℝ j f z‖ ≤ Df :=
    (hCf j hj z hz).trans <| (le_abs_self _).trans <|
      Finset.single_le_sum (f := fun j ↦ |Cf j|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  let A (m : ℕ) : ℝ := ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (‖L‖ * M (m - j))
  have hA0 {m : ℕ} (hm : m ≤ i) : 0 ≤ A m :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (norm_nonneg L) (hM0 ((Nat.sub_le m j).trans hm)))
  refine ⟨∑ m ∈ Finset.range (i + 1), A m * Df, fun m hm t ht z ↦ ?_⟩
  have hm_le : A m * Df ≤ ∑ n ∈ Finset.range (i + 1), A n * Df :=
    Finset.single_le_sum
      (fun n hn ↦ mul_nonneg (hA0 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))) hDf0)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hm))
  by_cases hz : z ∈ tsupport V
  · exact (norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le x₀ k L
      (hV.of_le (by exact_mod_cast hm)) (fun j hj ↦ hM j (hj.trans hm) z)
      (hf.of_le (by exact_mod_cast hm)) ht
      (fun j hj ↦ hDf (hj.trans hm) (mem_biUnion hz (lineMap_mem_segment ℝ x₀ z ht)))).trans hm_le
  · -- Off `tsupport V`, the integrand vanishes in a neighbourhood of `z`, so its derivatives do.
    have hu_tsup : tsupport (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) ⊆ tsupport V :=
      closure_minimal (Function.support_subset_iff'.2 fun w hw ↦ by
        simp [image_eq_zero_of_notMem_tsupport hw]) (isClosed_tsupport V)
    have hu0 : iteratedFDeriv ℝ m (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) z = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem ↦
        hz (hu_tsup (tsupport_iteratedFDeriv_subset m hmem))
    rw [hu0, norm_zero]
    exact (mul_nonneg (hA0 hm) hDf0).trans hm_le

/-- **Spatial derivative bound for a compactly supported radial bilinear interval integral.**
If `V` is `C^i` with compact support, there exists `A ≥ 0` such that for every `C^i` map `f` whose
derivatives of order at most `i` are bounded by `B` along `[x₀, x]`, the `i`-th derivative of
`y ↦ ∫ t in 0..1, t ^ k • L (f (lineMap x₀ y t)) (V y)` at `x` has norm at most `A * B`. -/
theorem exists_norm_iteratedFDeriv_intervalIntegral_pow_smul_clm_apply_lineMap_le
    {G E' H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (x₀ : E) (k : ℕ) (L : G →L[ℝ] E' →L[ℝ] H)
    {V : E → E'} {i : ℕ} (hV : ContDiff ℝ i V) (hVc : HasCompactSupport V) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {f : E → G}, ContDiff ℝ i f →
        ∀ {x : E} {B : ℝ},
          (∀ j ≤ i, ∀ z ∈ segment ℝ x₀ x, ‖iteratedFDeriv ℝ j f z‖ ≤ B) →
          ‖iteratedFDeriv ℝ i
            (fun y ↦ ∫ t in (0 : ℝ)..1, t ^ k • L (f (lineMap x₀ y t)) (V y)) x‖ ≤
            A * B := by
  have hVbd : ∀ j ≤ i, ∃ M : ℝ, ∀ y, ‖iteratedFDeriv ℝ j V y‖ ≤ M := fun j hj ↦
    Continuous.bounded_above_of_compact_support
      (hV.continuous_iteratedFDeriv (by exact_mod_cast hj)) (hVc.iteratedFDeriv j)
  choose! M hM using hVbd
  have hM0 {j : ℕ} (hj : j ≤ i) : 0 ≤ M j := (norm_nonneg _).trans (hM j hj x₀)
  let A : ℝ := ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (‖L‖ * M (i - j))
  have hA0 : 0 ≤ A :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (norm_nonneg L) (hM0 (Nat.sub_le i j)))
  refine ⟨A, hA0, fun {f} hf {x B} hB ↦ ?_⟩
  -- Joint smoothness and global derivative domination justify differentiating under the integral.
  have hG : ContDiff ℝ i (fun p : ℝ × E ↦ p.1 ^ k • L (f (lineMap x₀ p.2 p.1)) (V p.2)) := by
    have hline_p : ContDiff ℝ i (fun p : ℝ × E ↦ lineMap x₀ p.2 p.1) := by
      simp only [lineMap_apply_module']
      exact (contDiff_fst.smul (contDiff_snd.sub contDiff_const)).add contDiff_const
    exact (contDiff_fst.pow k).smul ((L.contDiff.comp (hf.comp hline_p)).clm_apply
      (hV.comp contDiff_snd))
  have hcont {m : ℕ} (hm : m ≤ i) (z : E) :
      Continuous fun t : ℝ ↦
        iteratedFDeriv ℝ m (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) z :=
    (_root_.ContDiff.continuous_iteratedFDeriv_prod_right hG m (by exact_mod_cast hm)).comp
      (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le x₀ k L hV hVc hf
  have hub (m : ℕ) (hm : m ≤ i) :
      ∀ᵐ t ∂volume.restrict (uIoc (0 : ℝ) 1), ∀ z,
        ‖iteratedFDeriv ℝ m (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) z‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_uIoc, uIoc_of_le zero_le_one]
    exact Eventually.of_forall fun t ht z ↦ hC m hm t (Ioc_subset_Icc_self ht) z
  rw [iteratedFDeriv_intervalIntegral (μ := volume) (a := 0) (b := 1)
    (u := fun t y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) (N := i)
    (Eventually.of_forall fun t ↦ hG.comp (contDiff_const.prodMk contDiff_id))
    (fun m hm z ↦ (hcont hm z).aestronglyMeasurable)
    (bound := fun _ _ ↦ C) (fun _ _ ↦ intervalIntegrable_const) hub le_rfl]
  -- Apply the sharp pointwise derivative bound at `x` along `[x₀, x]`.
  have hle : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ i (fun y ↦ t ^ k • L (f (lineMap x₀ y t)) (V y)) x‖ ≤ A * B :=
    fun t ht ↦ by
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
      exact norm_iteratedFDeriv_pow_smul_clm_apply_lineMap_le x₀ k L hV (fun j hj ↦ hM j hj x)
        hf ht' (fun j hj ↦ hB j hj _ (lineMap_mem_segment ℝ x₀ x ht'))
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hle

end RadialBilinear

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
  have hmem : {x₀} ×ˢ range ι ⊆ W := by
    rintro ⟨x, p⟩ ⟨hx, y, rfl⟩
    rcases mem_singleton_iff.mp hx with rfl
    exact hx₀ y
  obtain ⟨u, v, hu, _, hxu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_range hι) hW hmem
  have hc : ContinuousOn (fun p : E × α ↦ F (p.1, ι p.2)) (u ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn
      fun p hp ↦ huv ⟨hp.1, hv (mem_range_self p.2)⟩
  have hi := continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
    (ContinuousLinearMap.lsmul ℝ ℝ) isCompact_univ (f := fun x y ↦ F (x, ι y)) hc
    (fun _ _ _ h ↦ absurd (mem_univ _) h) hg.integrableOn
  exact hi.continuousAt (hu.mem_nhds (hxu (mem_singleton x₀)))

end Topological

variable {E : Type u} {P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] {ι : α → P} {W : Set (E × P)}

/-- **Partial derivatives in the first variable.** If `F` is `C^(m+1)` on an open set
`W ⊆ E × P`, then the derivative of `x ↦ F (x, p.2)` at `p.1` is `C^m` in `p` on `W`. -/
theorem _root_.ContDiffOn.fderiv_partial_of_isOpen {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : E × P → G} {m : WithTop ℕ∞} (hF : ContDiffOn ℝ (m + 1) F W)
    (hW : IsOpen W) :
    ContDiffOn ℝ m (fun p : E × P ↦ fderiv ℝ (fun x ↦ F (x, p.2)) p.1) W := by
  intro p hp
  have hFp : ContDiffAt ℝ (m + 1) (fun q : (E × P) × E ↦ F (q.2, q.1.2)) (p, p.1) :=
    (hF.contDiffAt (hW.mem_nhds hp)).comp (p, p.1) (by fun_prop)
  exact (ContDiffAt.fderiv (f := fun (q : E × P) (x : E) ↦ F (x, q.2)) hFp contDiffAt_fst
    le_rfl).contDiffWithinAt

/-- **Differentiation under the integral sign over a compact parameter space.** If `F` is `C¹`
on an open set `W ⊆ E × P` containing `{x₀} × ι(α)`, then integrating `F (x, ι y)` against an
integrable weight `g` is differentiable at `x₀`, with derivative the integral of the partial
derivative of `F` in `x`. -/
theorem hasFDerivAt_integral_smul_of_contDiffOn {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι) (hW : IsOpen W)
    (hF : ContDiffOn ℝ 1 F W) {x₀ : E} (hx₀ : ∀ y, (x₀, ι y) ∈ W) :
    HasFDerivAt (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ)
      (∫ y, g y • fderiv ℝ (fun x ↦ F (x, ι y)) x₀ ∂μ) x₀ := by
  set D : E × P → E →L[ℝ] G := fun p ↦ fderiv ℝ (fun x ↦ F (x, p.2)) p.1
  have hD : ContinuousOn D W :=
    (ContDiffOn.fderiv_partial_of_isOpen (m := 0) (by simpa using hF) hW).continuousOn
  have hdiff : ∀ p ∈ W, HasFDerivAt (fun x ↦ F (x, p.2)) (D p) p.1 := fun p hp ↦
    (((hF.contDiffAt (hW.mem_nhds hp)).differentiableAt one_ne_zero).comp p.1
      (differentiableAt_id.prodMk (differentiableAt_const p.2))).hasFDerivAt
  have hmem : ∀ y ∈ Set.range ι, (x₀, y) ∈ W := Set.forall_mem_range.mpr hx₀
  obtain ⟨C, hC⟩ := (isCompact_range hι).exists_eventually_norm_le hW
    (fun y hy ↦ hD.continuousAt (hW.mem_nhds (hmem y hy))) hmem
  simp only [Set.forall_mem_range] at hC
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun x y ↦ g y • D (x, ι y))
    (bound := fun y ↦ ‖g y‖ * C) hC ?_
    (integrable_smul_of_continuousOn hg hι hF.continuousOn hx₀)
    (integrable_smul_of_continuousOn hg hι hD hx₀).aestronglyMeasurable ?_
    (hg.norm.mul_const C) ?_
  · filter_upwards [hC] with x hx
    exact (integrable_smul_of_continuousOn hg hι hF.continuousOn
      fun y ↦ (hx y).1).aestronglyMeasurable
  · refine ae_of_all _ fun y x hx ↦ ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hx y).2 (norm_nonneg _)
  · exact ae_of_all _ fun y x hx ↦ (hdiff (x, ι y) (hx y).1).const_smul (g y)

private theorem contDiffOn_integral_smul_nat {G : Type max u v} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (m : ℕ) {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι)
    (hW : IsOpen W) (hF : ContDiffOn ℝ m F W) {U : Set E} (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ m (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) U := by
  induction m generalizing G with
  | zero =>
      exact contDiffOn_zero.2 fun x hx ↦
        (continuousAt_integral_smul_of_continuousOn hg hι hW hF.continuousOn
          (hUW x hx)).continuousWithinAt
  | succ m ih =>
      have hF' : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1) F W := by exact_mod_cast hF
      have hderiv := fun x hx ↦ hasFDerivAt_integral_smul_of_contDiffOn hg hι hW
        (hF'.of_le le_add_self) (hUW x hx)
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun x hx ↦ (hderiv x hx).differentiableAt.differentiableWithinAt,
        fun h ↦ absurd h (by simp), ?_⟩
      exact (ih (hF'.fderiv_partial_of_isOpen hW)).congr fun x hx ↦ (hderiv x hx).fderiv

/-- **Smoothness of integrals over a compact parameter space.** If `F` is `C^n` on an open set
`W ⊆ E × P` and `{x} × ι(α) ⊆ W` for every `x` in an open set `U`, then integrating `F (x, ι y)`
against an integrable weight `g` is `C^n` in `x` on `U`. -/
theorem contDiffOn_integral_smul_of_contDiffOn {G : Type v} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {n : ℕ∞} {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hW : IsOpen W) (hF : ContDiffOn ℝ n F W) {U : Set E} (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ n (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) U := by
  let eG : Type max u v := ULift.{u} G
  let isoG : eG ≃L[ℝ] G := ContinuousLinearEquiv.ulift
  have he : ContDiffOn ℝ n (fun x ↦ ∫ y, g y • isoG.symm (F (x, ι y)) ∂μ) U := by
    rw [contDiffOn_iff_forall_nat_le]
    intro m hm
    exact contDiffOn_integral_smul_nat m hg hι hW
      (isoG.symm.contDiff.comp_contDiffOn (hF.of_le (by exact_mod_cast hm))) hU hUW
  refine (isoG.contDiff.comp_contDiffOn he).congr fun x _ ↦ ?_
  have hsmul : ∀ y, g y • isoG.symm (F (x, ι y)) = isoG.symm (g y • F (x, ι y)) :=
    fun y ↦ (map_smul _ _ _).symm
  simp only [Function.comp_apply, hsmul, ContinuousLinearEquiv.integral_comp_comm,
    ContinuousLinearEquiv.apply_symm_apply]

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
  have hvD' (z : E) (hz : z ∈ s ∩ Metric.ball x₀ δ) (y : α) :
      ‖D (z, ι y) - D (x₀, ι y)‖ < ε := by
    simpa only [dist_eq_norm] using hvD z (hball ⟨hz.2, hz.1⟩) y (mem_univ y)
  have hpt (y : α) : ‖F (x, ι y) - F (x₀, ι y) - D (x₀, ι y) (x - x₀)‖ ≤ ε * ‖x - x₀‖ :=
    hsδ.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun z ↦ F (z, ι y))
      (f' := fun z ↦ D (z, ι y))
      (fun z (hz : z ∈ s ∩ Metric.ball x₀ δ) ↦ (hderiv z hz.1 y).mono inter_subset_left)
      (fun z hz ↦ (hvD' z hz y).le)
      ⟨hx₀, Metric.mem_ball_self hδ⟩ ⟨hx, hxδ⟩
  have hDx : ContinuousOn (fun p ↦ D p (x - x₀)) W :=
    (ContinuousLinearMap.apply ℝ G (x - x₀)).continuous.comp_continuousOn hD
  calc ‖(∫ y, g y • F (x, ι y) ∂μ) - (∫ y, g y • F (x₀, ι y) ∂μ) -
        (∫ y, g y • D (x₀, ι y) ∂μ) (x - x₀)‖
      = ‖∫ y, g y • (F (x, ι y) - F (x₀, ι y) - D (x₀, ι y) (x - x₀)) ∂μ‖ := by
        have hFx := integrable_smul_of_continuousOn hg hι hF.continuousOn (hsW x hx)
        have hFx₀ := integrable_smul_of_continuousOn hg hι hF.continuousOn (hsW x₀ hx₀)
        rw [ContinuousLinearMap.integral_apply
          (integrable_smul_of_continuousOn hg hι hD (hsW x₀ hx₀))]
        simp only [smul_apply, smul_sub]
        rw [integral_sub (by exact hFx.sub hFx₀ :
            Integrable (fun y ↦ g y • F (x, ι y) - g y • F (x₀, ι y)) μ)
          (integrable_smul_of_continuousOn hg hι hDx (hsW x₀ hx₀)), integral_sub hFx hFx₀]
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

end TauCeti
