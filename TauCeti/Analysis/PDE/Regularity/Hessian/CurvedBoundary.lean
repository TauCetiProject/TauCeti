/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.ContinuousCoefficient
public import TauCeti.Analysis.PDE.Regularity.Hessian.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Flattening
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure

/-!
# The Calderón–Zygmund estimate up to a `C²` boundary for continuous coefficients

Let `E` be a finite-dimensional real inner product space, `1 < p < ∞`, and let `Ω ⊆ ℝ × E` be open.
This file proves the `W^{2,p}` estimate up to the boundary for strong solutions of the
non-divergence-form equation

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` in `Ω`, `u = 0` on `∂Ω`,

whose principal coefficients are continuous up to the boundary and elliptic there, and whose
lower-order coefficients are bounded, on domains with `C²` boundary:

* near a boundary portion which, in rigid coordinates, is the graph of a `C²` function, the
  estimate `‖D²u‖_{Lᵖ(Ω ∩ V)} ≤ C (‖f‖ + ‖∇u‖ + ‖u‖)` holds on a neighbourhood `V` of each of its
  points (`TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph`);
* on a bounded open set with `C²` boundary, `‖D²u‖_{Lᵖ(Ω)} ≤ C (‖f‖ + ‖∇u‖ + ‖u‖)` for every
  `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` solving the equation
  (`TauCeti.exists_norm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph`).

Norms without a subscript are those of `Lᵖ(Ω)`. The constants depend on the domain, the
coefficients and `p`, not on `u` or `f`. The global estimate is Gilbarg–Trudinger's
Theorem 9.13 with the gradient term still on the right; an interpolation inequality for `‖∇u‖`
removes it, and it is the a priori estimate behind the solvability of the Dirichlet problem in
`W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` (Gilbarg–Trudinger, Theorem 9.15). The boundary of `Ω` is described
as in Evans, Appendix C.1, by a height function of class `C²`; the estimate itself only uses
that the flattening chart is a change of variables of order two.

## The argument

The estimate near a flat boundary portion is
`TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_normalHalfSpace`. Near a
curved boundary point the boundary is flattened, as in Gilbarg–Trudinger's proof of Theorem 9.13.

* **Flattening.** In rigid coordinates `e` the map `Φ = e⁻¹ ∘ G⁻¹`, with `G` graph flattening by
  the height function, carries a neighbourhood of `0` in the half-space `{0 < x.fst}` onto `Ω`
  near the boundary point; `Φ` and its inverse `Ψ = G ∘ e` are changes of variables of order two
  (`TauCeti.exists_isChangeOfVariables_normalHalfSpace_of_contDiff`).
* **The transformed equation.** `v = u ∘ Φ` solves an equation of the same form on the flat side
  (`TauCeti.PDE.ae_traceCLM_nondivPullbackPrincipal_comp_add_inner_nondivPullbackDrift_add_mul_eq`),
  with principal coefficient `DΨ ∘ A ∘ DΨ†` composed with `Φ`, which is again continuous and
  elliptic since `DΨ` is continuous and invertible, a drift picking up the second derivatives of
  `Ψ`, which stays bounded since `A` is bounded near the boundary point, and right-hand side
  `f ∘ Φ`. Zero boundary values are carried along by
  `TauCeti.Wkp.IsChangeOfVariables.exists_w1p0_value_ae_eq_mul_value_w1pCompL`.
* **Pushing back.** On a smaller neighbourhood `u = v ∘ Ψ`, so the norm bound of precomposition
  with `Ψ` (`TauCeti.Wkp.norm_compL_le`) bounds `D²u` by `D²v` and the first-order part of `v`,
  and the latter is bounded by `‖u‖ + ‖∇u‖` through precomposition with `Φ`.
* **Covering.** Interior points are handled by the same flat estimate on a ball inside `Ω` and
  inside a half-space. Finitely many of the neighbourhoods cover the compact closure of `Ω`, and
  the `Lᵖ` norm on `Ω` is at most the sum of those on the pieces.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (straightening the boundary) and Theorem 9.13 with its proof.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.1 (`C²` boundaries).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Metric InnerProductSpace
open scoped ENNReal NNReal Gradient ContDiff

namespace TauCeti

section Pullback

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {U' U : Opens G} {Φ Ψ : G → G} {L₁ c₁ L₂ c₂ : ℝ}

omit [FiniteDimensional ℝ G] in
/-- A closed ball about `y₀ ∈ U'` which `Φ` maps into `W`, and on whose image the norm of `A`
stays below `‖A(Φ y₀)‖ + 1` at the points of `Ω`, by the continuity of `A` within `Ω` at
`Φ y₀`. -/
private theorem exists_closedBall_subset_of_continuousWithinAt {U' W : Opens G} {Ω : Set G}
    (hΦc : Continuous Φ) {y₀ : G} (hy₀ : y₀ ∈ U') (hy₀W : Φ y₀ ∈ W) {A : G → G →L[ℝ] G}
    (hA : ContinuousWithinAt A Ω (Φ y₀)) :
    ∃ r > 0, closedBall y₀ r ⊆ (U' : Set G) ∩
      (Φ ⁻¹' W ∩ Φ ⁻¹' {y | y ∈ Ω → ‖A y‖ < ‖A (Φ y₀)‖ + 1}) := by
  have hAbd : ∀ᶠ y in nhds (Φ y₀), y ∈ Ω → ‖A y‖ < ‖A (Φ y₀)‖ + 1 := by
    have h : ContinuousWithinAt (fun y => ‖A y‖) Ω (Φ y₀) := ContinuousWithinAt.norm (f := A) hA
    exact eventually_nhdsWithin_iff.1 (h.eventually (gt_mem_nhds (lt_add_one _)))
  exact nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (U'.isOpen.mem_nhds hy₀)
    (Filter.inter_mem (hΦc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds hy₀W))
      (hΦc.continuousAt.preimage_mem_nhds hAbd)))

omit [FiniteDimensional ℝ G] in
open Wkp in
/-- **Restricting the charts to a ball.** Let `Φ` and `Ψ` be changes of variables of order two
between `U'` and `U` with `Ψ ∘ Φ = id`, such that `Φ` maps `H ∩ U'` onto `Ω ∩ U`, and let
`B(y₀, s) ⊆ U'`. Then `Φ` maps `B(y₀, s)` into `O = U ∩ Ψ⁻¹ B(y₀, s)`, and `Φ` and `Ψ` restrict to
changes of variables between `H ∩ B(y₀, s)` and `Ω ∩ O`. -/
private theorem isChangeOfVariables_inf_ball {H Omega : Opens G}
    (hΦ : IsChangeOfVariables 2 U' U Φ L₁ c₁) (hΨ : IsChangeOfVariables 2 U U' Ψ L₂ c₂)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΨc : Continuous Ψ)
    (himage : Φ '' ((H : Set G) ∩ U') = (Omega : Set G) ∩ U) {y₀ : G} {s : ℝ}
    (hs : ball y₀ s ⊆ U') :
    MapsTo Φ (⟨ball y₀ s, isOpen_ball⟩ : Opens G)
        (⟨U ∩ Ψ ⁻¹' ball y₀ s, hΨc.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball⟩ :
          Opens G) ∧
      IsChangeOfVariables 2 (H ⊓ ⟨ball y₀ s, isOpen_ball⟩)
        (Omega ⊓ ⟨U ∩ Ψ ⁻¹' ball y₀ s, hΨc.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball⟩)
        Φ L₁ c₁ ∧
      IsChangeOfVariables 2
        (Omega ⊓ ⟨U ∩ Ψ ⁻¹' ball y₀ s, hΨc.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball⟩)
        (H ⊓ ⟨ball y₀ s, isOpen_ball⟩) Ψ L₂ c₂ := by
  have hBO : MapsTo Φ (ball y₀ s) (U ∩ Ψ ⁻¹' ball y₀ s) := fun x hx =>
    ⟨hΦ.mapsTo (hs hx), by rw [mem_preimage, hΨΦ]; exact hx⟩
  refine ⟨fun x hx => Opens.mem_mk.2 (hBO (Opens.mem_mk.1 hx)),
    hΦ.mono_set (fun x hx => hs (Opens.mem_mk.1 (Opens.mem_inf.1 hx).2)) fun x hx => ?_,
    hΨ.mono_set (fun y hy => (Opens.mem_mk.1 (Opens.mem_inf.1 hy).2).1) fun y hy => ?_⟩
  · simp only [SetLike.mem_coe, Opens.mem_inf, Opens.mem_mk] at hx ⊢
    have hmem : Φ x ∈ (Omega : Set G) ∩ U := himage ▸ mem_image_of_mem _ ⟨hx.1, hs hx.2⟩
    exact ⟨hmem.1, hBO hx.2⟩
  · simp only [SetLike.mem_coe, Opens.mem_inf, Opens.mem_mk] at hy ⊢
    obtain ⟨x, ⟨hxH, -⟩, rfl⟩ := himage.symm.subset ⟨hy.1, hy.2.1⟩
    exact ⟨by rw [hΨΦ]; exact hxH, hy.2.2⟩

variable [MeasurableSpace G] [BorelSpace G] {mu : Measure G} [mu.IsAddHaarMeasure]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

open Wkp in
/-- The first-order part of `u ∘ Φ` is controlled by the `Lᵖ` norms of `u` and of its gradient. -/
private theorem norm_lowerOrder_compL_restrictL_le {Omega D Ω' : Opens G}
    (hD : D ≤ Omega) (hΦ : IsChangeOfVariables 2 Ω' D Φ L₁ c₁) (u : Wkp mu Omega p 2) :
    ‖lowerOrder 1 (compL hΦ (restrictL hD 2 u))‖ ≤
      compLBound p 1 L₁ c₁ * (‖value 2 u‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖) := by
  rw [lowerOrder_compL, lowerOrder_restrictL]
  refine (norm_compL_le _ _).trans (mul_le_mul_of_nonneg_left ?_
    (compLBound_nonneg p 1 L₁ hΦ.pos))
  refine (norm_restrictL_le hD 1 _).trans
    ((norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 (lowerOrder 1 u)).trans_eq ?_)
  rw [value_succ, value_succ, value_zero]

open Wkp in
/-- **Pushing the Hessian bound forward along `Ψ`.** Let `Φ` be a change of variables of order two
from `Ω'` into `D ⊆ Ω`, and `Ψ` one from `Ω ∩ V ⊆ D` into `Ω'' ⊆ Ω'` with `Φ ∘ Ψ = id` on
`Ω ∩ V`. Then the Hessian of `u` on `Ω ∩ V` is controlled by the first-order part of
`v = u ∘ Φ` and the Hessian of `v` on `Ω''`. -/
private theorem lpNorm_iteratedGradient_inter_le_of_compL {Omega D V Ω' Ω'' : Opens G}
    (hD : D ≤ Omega) (hVD : Omega ⊓ V ≤ D) (hΩ'' : Ω'' ≤ Ω')
    (hΦ : IsChangeOfVariables 2 Ω' D Φ L₁ c₁) (hΨ : IsChangeOfVariables 2 (Omega ⊓ V) Ω'' Ψ L₂ c₂)
    (hΦΨ : RightInvOn Ψ Φ (Omega ⊓ V : Opens G)) (u : Wkp mu Omega p 2) :
    lpNorm (iteratedGradient 1 u) p (mu.restrict ((Omega ⊓ V : Opens G) : Set G)) ≤
      compLBound p 2 L₂ c₂ * (‖lowerOrder 1 (compL hΦ (restrictL hD 2 u))‖ +
        lpNorm (iteratedGradient 1 (compL hΦ (restrictL hD 2 u))) p
          (mu.restrict (Ω'' : Set G))) := by
  have hw : compL hΨ (restrictL hΩ'' 2 (compL hΦ (restrictL hD 2 u))) =
      restrictL (inf_le_left : Omega ⊓ V ≤ Omega) 2 u := by
    rw [compL_eq_iff]
    have hsub : ((Ω'' : Opens G) : Set G) ⊆ Ω' := hΩ''
    filter_upwards [value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) 2 u,
      hΨ.ae_comp (value_restrictL_ae hΩ'' 2 (compL hΦ (restrictL hD 2 u))),
      hΨ.ae_comp (ae_restrict_of_ae_restrict_of_subset hsub (value_compL_ae hΦ (restrictL hD 2 u))),
      ae_restrict_of_ae_restrict_of_subset hVD (value_restrictL_ae hD 2 u),
      ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with y h1 h2 h3 h4 hy
    rw [h1, h2, h3, hΦΨ hy, h4]
  have hB := compLBound_nonneg p 2 L₂ hΨ.pos
  have h1 : lpNorm (iteratedGradient 1 u) p (mu.restrict ((Omega ⊓ V : Opens G) : Set G)) =
      ‖iteratedGradient 1 (restrictL (inf_le_left : Omega ⊓ V ≤ Omega) 2 u)‖ :=
    (Lp.norm_eq_lpNorm_of_ae_eq (iteratedGradient_restrictL_ae _ 1 u)).symm
  have h2 := norm_compL_le hΨ (restrictL hΩ'' 2 (compL hΦ (restrictL hD 2 u)))
  rw [hw] at h2
  have h3 := norm_le_norm_lowerOrder_add_norm_iteratedGradient 1
    (restrictL hΩ'' 2 (compL hΦ (restrictL hD 2 u)))
  rw [lowerOrder_restrictL] at h3
  have h4 := norm_restrictL_le hΩ'' 1 (lowerOrder 1 (compL hΦ (restrictL hD 2 u)))
  have h5 := (Lp.norm_eq_lpNorm_of_ae_eq
    (iteratedGradient_restrictL_ae hΩ'' 1 (compL hΦ (restrictL hD 2 u))))
  rw [h1]
  refine (norm_iteratedGradient_le 1 _).trans (h2.trans (mul_le_mul_of_nonneg_left ?_ hB))
  rw [← h5]
  linarith

open Wkp in
/-- **Zero boundary values along a flattening chart.** If `u` vanishes on `∂Ω ∩ W` and `Φ` maps
`B` into `O ⊆ W`, then `v = u ∘ Φ` vanishes on `∂Ω' ∩ B`: `ψ v ∈ W^{1,p}_0(Ω')` for every smooth
`ψ` compactly supported in `B`. -/
private theorem exists_w1p0_value_ae_eq_mul_value_compL_restrictL (hp : p ≠ ⊤)
    {Omega O W Ω' B : Opens G} {L₁ c₁ L₂ c₂ : ℝ}
    (hΦ : IsChangeOfVariables 2 Ω' (Omega ⊓ O) Φ L₁ c₁)
    (hΨ : IsChangeOfVariables 2 (Omega ⊓ O) Ω' Ψ L₂ c₂) (hΨΦ : ∀ x, Ψ (Φ x) = x)
    (hΦc : Continuous Φ) (hΨc : Continuous Ψ) (hOW : (O : Set G) ⊆ W) (hBO : MapsTo Φ B O)
    {u : Wkp mu Omega p 2}
    (hu0 : ∀ ψ : G → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∃ v : W1p0 mu Omega p,
        W1p.value (v : W1p mu Omega p) =ᵐ[mu.restrict Omega] fun x => ψ x * value 2 u x)
    (ψ : G → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ B) :
    ∃ w : W1p0 mu Ω' p, W1p.value (w : W1p mu Ω' p) =ᵐ[mu.restrict Ω']
      fun x => ψ x * value 2 (compL hΦ (restrictL (inf_le_left : Omega ⊓ O ≤ Omega) 2 u)) x := by
  have hD : Omega ⊓ O ≤ Omega := inf_le_left
  obtain ⟨w, hw⟩ := (hΦ.mono one_le_two).exists_w1p0_value_ae_eq_mul_value_w1pCompL hp
    hΦc.continuousOn hΨc.continuousOn hΨ.mapsTo (fun x _ => hΨΦ x) hBO
    (u := firstOrder 1 u) (fun χ hχ hχc hχs => by
      simpa only [value_firstOrder] using hu0 χ hχ hχc (hχs.trans hOW)) ψ hψ hψc hψs
  refine ⟨w, ?_⟩
  filter_upwards [hw, (hΦ.mono one_le_two).value_w1pCompL_ae hp (W1p.restrictL hD _),
    value_compL_ae hΦ (restrictL hD 2 u),
    hΦ.ae_comp (W1p.value_restrictL_ae hD (firstOrder 1 u)),
    hΦ.ae_comp (value_restrictL_ae hD 2 u)] with x h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4, h5, value_firstOrder]

open Wkp in
/-- **The equation along a flattening chart.** If `u` solves `tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f`
on `Ω`, then `v = u ∘ Φ` solves the pulled-back equation on `Ω'` with right-hand side `f ∘ Φ`,
as an element of `Lᵖ(Ω')`. -/
private theorem ae_pullback_eq_compL_restrictL (hp : p ≠ ⊤) {Omega O Ω' : Opens G}
    {L₁ c₁ L₂ c₂ : ℝ} (hΦ : IsChangeOfVariables 2 Ω' (Omega ⊓ O) Φ L₁ c₁)
    (hΨ : IsChangeOfVariables 2 (Omega ⊓ O) Ω' Ψ L₂ c₂) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    {A : G → G →L[ℝ] G} {b : G → G} {c : G → ℝ} (u : Wkp mu Omega p 2)
    (f : Lp ℝ p (mu.restrict Omega))
    (heq : ∀ᵐ x ∂mu.restrict Omega, traceCLM ℝ G (A x ∘L iteratedGradient 1 u x) +
      ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) :
    ∀ᵐ x ∂mu.restrict Ω', traceCLM ℝ G (PDE.nondivPullbackPrincipal Φ Ψ A x ∘L
        iteratedGradient 1 (compL hΦ (restrictL (inf_le_left : Omega ⊓ O ≤ Omega) 2 u)) x) +
      ⟪PDE.nondivPullbackDrift Φ Ψ A b x, iteratedGradient 0
        (lowerOrder 1 (compL hΦ (restrictL (inf_le_left : Omega ⊓ O ≤ Omega) 2 u))) x⟫_ℝ +
      c (Φ x) * value 2 (compL hΦ (restrictL (inf_le_left : Omega ⊓ O ≤ Omega) 2 u)) x =
        compL (hΦ.mono (Nat.zero_le 2)) (restrictL (inf_le_left : Omega ⊓ O ≤ Omega) 0 f) x := by
  have hD : Omega ⊓ O ≤ Omega := inf_le_left
  have hDs : ((Omega ⊓ O : Opens G) : Set G) ⊆ Omega := hD
  have huD : ∀ᵐ y ∂mu.restrict (Omega ⊓ O : Opens G),
      traceCLM ℝ G (A y ∘L iteratedGradient 1 (restrictL hD 2 u) y) +
        ⟪b y, iteratedGradient 0 (lowerOrder 1 (restrictL hD 2 u)) y⟫_ℝ +
          c y * value 2 (restrictL hD 2 u) y = f y := by
    rw [lowerOrder_restrictL]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hDs heq,
      iteratedGradient_restrictL_ae hD 1 u, iteratedGradient_restrictL_ae hD 0 (lowerOrder 1 u),
      value_restrictL_ae hD 2 u] with y h1 h2 h3 h4
    rw [h2, h3, h4, h1]
  have hpull :=
    PDE.ae_traceCLM_nondivPullbackPrincipal_comp_add_inner_nondivPullbackDrift_add_mul_eq hΦ hΨ
      (fun y _ => hΦΨ y) hp _ huD
  filter_upwards [hpull,
    value_compL_ae (hΦ.mono (Nat.zero_le 2)) (restrictL hD 0 f),
    hΦ.ae_comp (value_restrictL_ae hD 0 f)] with x h1 h2 h3
  rw [h1, ← value_zero (compL (hΦ.mono (Nat.zero_le 2)) (restrictL hD 0 f)), h2, h3, value_zero]

open Wkp in
/-- **The estimate through a flattening chart, for one solution.** Let `Φ` and `Ψ` be mutually
inverse changes of variables of order two between `Ω'` and `Ω ∩ O`, with `O ⊆ W`, and let `Ψ`
also map `Ω ∩ V ⊆ Ω ∩ O` into `Ω'' ⊆ Ω' ∩ K`. Suppose the pulled-back equation on `Ω'` satisfies
the `W^{2,p}` estimate on `Ω' ∩ K` with constant `C₁` for functions vanishing on the part of the
boundary in `B`, where `Φ B ⊆ O`. Then every `u ∈ W^{2,p}(Ω)` vanishing on `∂Ω ∩ W` and solving
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` satisfies the `W^{2,p}` estimate on `Ω ∩ V`, with a constant
depending only on `C₁`, `p` and the constants of the changes of variables. -/
private theorem lpNorm_iteratedGradient_le_of_pullback (hp : p ≠ ⊤)
    {Omega O W Ω' B V Ω'' : Opens G} {L₁ c₁ L₂ c₂ : ℝ}
    (hΦ : IsChangeOfVariables 2 Ω' (Omega ⊓ O) Φ L₁ c₁)
    (hΨ : IsChangeOfVariables 2 (Omega ⊓ O) Ω' Ψ L₂ c₂)
    (hΨ'' : IsChangeOfVariables 2 (Omega ⊓ V) Ω'' Ψ L₂ c₂)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y) (hΦc : Continuous Φ) (hΨc : Continuous Ψ)
    (hOW : (O : Set G) ⊆ W) (hBO : MapsTo Φ B O) (hVO : Omega ⊓ V ≤ Omega ⊓ O)
    (hΩ'' : Ω'' ≤ Ω') {K : Set G} (hΩ''K : (Ω'' : Set G) ⊆ (Ω' : Set G) ∩ K)
    {A : G → G →L[ℝ] G} {b : G → G} {c : G → ℝ} {C₁ : ℝ}
    (hC₁ : ∀ (v : Wkp mu Ω' p 2) (g : Lp ℝ p (mu.restrict Ω')),
      (∀ ψ : G → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ B →
        ∃ w : W1p0 mu Ω' p,
          W1p.value (w : W1p mu Ω' p) =ᵐ[mu.restrict Ω'] fun x => ψ x * value 2 v x) →
      (∀ᵐ x ∂mu.restrict Ω',
        traceCLM ℝ G (PDE.nondivPullbackPrincipal Φ Ψ A x ∘L iteratedGradient 1 v x) +
          ⟪PDE.nondivPullbackDrift Φ Ψ A b x, iteratedGradient 0 (lowerOrder 1 v) x⟫_ℝ +
            c (Φ x) * value 2 v x = g x) →
      lpNorm (iteratedGradient 1 v) p (mu.restrict ((Ω' : Set G) ∩ K)) ≤
        C₁ * (‖g‖ + ‖iteratedGradient 0 (lowerOrder 1 v)‖ + ‖value 2 v‖))
    (u : Wkp mu Omega p 2) (f : Lp ℝ p (mu.restrict Omega))
    (hu0 : ∀ ψ : G → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∃ v : W1p0 mu Omega p,
        W1p.value (v : W1p mu Omega p) =ᵐ[mu.restrict Omega] fun x => ψ x * value 2 u x)
    (heq : ∀ᵐ x ∂mu.restrict Omega, traceCLM ℝ G (A x ∘L iteratedGradient 1 u x) +
      ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) :
    lpNorm (iteratedGradient 1 u) p (mu.restrict ((Omega ⊓ V : Opens G) : Set G)) ≤
      compLBound p 2 L₂ c₂ * (max C₁ 0 * compLBound p 0 L₁ c₁ +
        (1 + 2 * max C₁ 0) * compLBound p 1 L₁ c₁) *
        (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) := by
  have hD : Omega ⊓ O ≤ Omega := inf_le_left
  set v := compL hΦ (restrictL hD 2 u) with hv
  set g := compL (hΦ.mono (Nat.zero_le 2)) (restrictL hD 0 f)
  have hv0 := exists_w1p0_value_ae_eq_mul_value_compL_restrictL hp hΦ hΨ hΨΦ hΦc hΨc hOW hBO hu0
  have hveq := ae_pullback_eq_compL_restrictL hp hΦ hΨ hΦΨ u f heq
  -- The estimates of the norms of `g` and of the first-order part of `v`.
  have hg : ‖g‖ ≤ compLBound p 0 L₁ c₁ * ‖f‖ :=
    (norm_compL_le _ _).trans (mul_le_mul_of_nonneg_left (norm_restrictL_le hD 0 f)
      (compLBound_nonneg p 0 L₁ hΦ.pos))
  have hlow := norm_lowerOrder_compL_restrictL_le hD hΦ u
  have hvlow : ‖iteratedGradient 0 (lowerOrder 1 v)‖ + ‖value 2 v‖ ≤ 2 * ‖lowerOrder 1 v‖ := by
    have h1 := norm_iteratedGradient_le 0 (lowerOrder 1 v)
    have h2 := norm_value_le 1 (lowerOrder 1 v)
    rw [← value_succ] at h2
    linarith
  -- The flat estimate, on `Ω''`.
  have hflat : lpNorm (iteratedGradient 1 v) p (mu.restrict (Ω'' : Set G)) ≤
      max C₁ 0 * (compLBound p 0 L₁ c₁ * ‖f‖ + 2 * ‖lowerOrder 1 v‖) := by
    have hmem : MemLp (iteratedGradient 1 v) p (mu.restrict ((Ω' : Set G) ∩ K)) :=
      (Lp.memLp _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    refine (lpNorm_mono_measure hmem (Measure.restrict_mono hΩ''K le_rfl)).trans
        (((hC₁ v g hv0 hveq).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (by positivity))).trans (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)))
    linarith
  have hpush := lpNorm_iteratedGradient_inter_le_of_compL hD hVO hΩ'' hΦ hΨ''
    (fun y _ => hΦΨ y) u
  rw [← hv] at hpush
  have hB₂ := compLBound_nonneg p 2 L₂ hΨ.pos
  have hB₁ := compLBound_nonneg p 1 L₁ hΦ.pos
  have hB₀ := compLBound_nonneg p 0 L₁ hΦ.pos
  refine hpush.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hB₂
  have hext : 0 ≤ max C₁ 0 * compLBound p 0 L₁ c₁ * (‖iteratedGradient 0 (lowerOrder 1 u)‖ +
      ‖value 2 u‖) + (1 + 2 * max C₁ 0) * compLBound p 1 L₁ c₁ * ‖f‖ := by positivity
  have hℓ : (1 + 2 * max C₁ 0) * ‖lowerOrder 1 v‖ ≤ (1 + 2 * max C₁ 0) *
      (compLBound p 1 L₁ c₁ * (‖value 2 u‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖)) :=
    mul_le_mul_of_nonneg_left hlow (by positivity)
  linarith

end Pullback

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

open Wkp in
/-- **The estimate on the flat side.** Let `Φ` and `Ψ` be mutually inverse changes of variables
of order two between `U'` and `U`, and let `Φ` map the open set `Ω'`, which agrees with the
half-space `H = {0 < x.fst}` inside the open set `B`, into `Ω ∩ U`. Let `K ⊆ B ∩ U'` be compact
with `Φ K ⊆ W`. If `A` is continuous within `Ω` and elliptic at the points of `W` in the closure of
`Ω`, and `A ∘ Φ`, `b ∘ Φ`, `c ∘ Φ` are bounded and measurable on `Ω'`, then the `W^{2,p}` estimate
on `Ω' ∩ K` holds for the pulled-back equation. -/
private theorem exists_lpNorm_iteratedGradient_le_of_pullback (hp : 1 < p) (hp_top : p ≠ ⊤)
    {U' U W Omega Ω' B : Opens (WithLp 2 (ℝ × E))}
    {Φ Ψ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {L₁ c₁ L₂ c₂ : ℝ}
    (hΦ : IsChangeOfVariables 2 U' U Φ L₁ c₁) (hΨ : IsChangeOfVariables 2 U U' Ψ L₂ c₂)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y) (hΦc : Continuous Φ)
    (hΩ'B : (Ω' : Set (WithLp 2 (ℝ × E))) ∩ B =
      (normalHalfSpace (E := E) 0 : Set (WithLp 2 (ℝ × E))) ∩ B)
    (hΦmaps : MapsTo Φ Ω' ((Omega : Set (WithLp 2 (ℝ × E))) ∩ U))
    {K : Set (WithLp 2 (ℝ × E))} (hK : IsCompact K) (hKB : K ⊆ B) (hKU' : K ⊆ U')
    (hKW : MapsTo Φ K W) {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hAΦ : AEStronglyMeasurable (fun x => A (Φ x))
      (volume.restrict (Ω' : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ x ∈ W, ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ W, x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {Λ : ℝ} (hAΛ : ∀ x ∈ (Ω' : Set (WithLp 2 (ℝ × E))), ‖A (Φ x)‖ ≤ Λ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hbΦ : AEStronglyMeasurable (fun x => b (Φ x))
      (volume.restrict (Ω' : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Ω' : Set (WithLp 2 (ℝ × E))), ‖b (Φ x)‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hcΦ : AEStronglyMeasurable (fun x => c (Φ x))
      (volume.restrict (Ω' : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Ω' : Set (WithLp 2 (ℝ × E))), |c (Φ x)| ≤ γ) :
    ∃ C : ℝ, ∀ (v : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Ω' p 2)
      (g : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Ω')),
      (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ B →
        ∃ w : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Ω' p,
          W1p.value (w : W1p volume Ω' p) =ᵐ[volume.restrict (Ω' : Set (WithLp 2 (ℝ × E)))]
            fun x => ψ x * value 2 v x) →
      (∀ᵐ x ∂volume.restrict (Ω' : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E))
            (PDE.nondivPullbackPrincipal Φ Ψ A x ∘L iteratedGradient 1 v x) +
          ⟪PDE.nondivPullbackDrift Φ Ψ A b x, iteratedGradient 0 (lowerOrder 1 v) x⟫_ℝ +
            c (Φ x) * value 2 v x = g x) →
      lpNorm (iteratedGradient 1 v) p
          (volume.restrict ((Ω' : Set (WithLp 2 (ℝ × E))) ∩ K)) ≤
        C * (‖g‖ + ‖iteratedGradient 0 (lowerOrder 1 v)‖ + ‖value 2 v‖) := by
  have hΦΩ : MapsTo Φ Ω' Omega := hΦmaps.mono_right inter_subset_left
  have hm := PDE.aestronglyMeasurable_nondivPullbackPrincipal_and_nondivPullbackDrift hΨ
    hΦc.continuousOn Ω'.isOpen.measurableSet (fun x hx => (hΦmaps hx).2) hAΦ hbΦ
  refine exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_normalHalfSpace hp hp_top 0
    hΩ'B hK hKB hm.1 (fun x hx => PDE.continuousWithinAt_nondivPullbackPrincipal hΨ
      hΦc.continuousAt hΦΩ (hΦ.mapsTo (hKU' hx)) (hcont _ (hKW hx))) (fun x hx hxcl => ?_) hm.2
    (β := L₂ * β + Module.finrank ℝ (WithLp 2 (ℝ × E)) * (L₂ * Λ)) ?_ hcΦ hcγ
  · obtain ⟨lam, hlam, hA⟩ := hell (Φ x) (hKW hx) (map_mem_closure hΦc hxcl hΦΩ)
    exact ⟨_, PDE.nondivPullbackPrincipal_elliptic hΦ hΨ (fun y _ => hΨΦ y) (fun y _ => hΦΨ y)
      (hKU' hx) hlam hA⟩
  · filter_upwards [hbβ, ae_restrict_mem Ω'.isOpen.measurableSet] with x hx hxΩ'
    exact PDE.norm_nondivPullbackDrift_le hΨ (hΦmaps hxΩ').2 hx (hAΛ x hxΩ')

open Wkp in
/-- **The estimate near a straightened boundary portion.** Let `Φ` and `Ψ` be mutually inverse
changes of variables of order two between open sets `U'` and `U` such that `Φ` maps the part of
`U'` in the half-space `H = {0 < x.fst}` onto `Ω ∩ U`, and let `y₀ ∈ U'` with `Φ y₀ ∈ W`. Under the
hypotheses of `TauCeti.exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph`,
the `W^{2,p}` estimate holds on `Ω ∩ V` for an open neighbourhood `V` of `Φ y₀`. -/
private theorem exists_lpNorm_iteratedGradient_le_of_isChangeOfVariables (hp : 1 < p)
    (hp_top : p ≠ ⊤) {U' U W Omega : Opens (WithLp 2 (ℝ × E))}
    {Φ Ψ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {L₁ c₁ L₂ c₂ : ℝ}
    (hΦ : IsChangeOfVariables 2 U' U Φ L₁ c₁) (hΨ : IsChangeOfVariables 2 U U' Ψ L₂ c₂)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y) (hΦc : Continuous Φ) (hΨc : Continuous Ψ)
    (himage : Φ '' ((normalHalfSpace (E := E) 0 : Set (WithLp 2 (ℝ × E))) ∩ U') =
      (Omega : Set (WithLp 2 (ℝ × E))) ∩ U)
    {y₀ : WithLp 2 (ℝ × E)} (hy₀ : y₀ ∈ U') (hy₀W : Φ y₀ ∈ W)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ x ∈ W, ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ W, x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ V : Opens (WithLp 2 (ℝ × E)), Φ y₀ ∈ V ∧ ∃ C : ℝ,
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
          ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
            W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
              fun x => ψ x * value 2 u x) →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
            ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
        lpNorm (iteratedGradient 1 u) p
            (volume.restrict ((Omega ⊓ V : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E)))) ≤
          C * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) := by
  -- A closed ball about `y₀` in `U'` which `Φ` maps into `W`, where `A` stays bounded.
  obtain ⟨r, hr, hrB⟩ := exists_closedBall_subset_of_continuousWithinAt hΦc hy₀ hy₀W (hcont _ hy₀W)
  -- The flat domain `Ω' = H ∩ B(y₀, r)` and the curved one `Ω ∩ O`, `O = U ∩ Ψ⁻¹ B(y₀, r)`.
  let B : Opens (WithLp 2 (ℝ × E)) := ⟨ball y₀ r, isOpen_ball⟩
  let Ω' : Opens (WithLp 2 (ℝ × E)) := normalHalfSpace 0 ⊓ B
  let O : Opens (WithLp 2 (ℝ × E)) := ⟨U ∩ Ψ ⁻¹' ball y₀ r,
    hΨc.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball⟩
  obtain ⟨hBO, hΦ', hΨ'⟩ := isChangeOfVariables_inf_ball hΦ hΨ hΨΦ hΨc himage
    (ball_subset_closedBall.trans (hrB.trans inter_subset_left))
  have hOW : (O : Set (WithLp 2 (ℝ × E))) ⊆ W := fun y hy => by
    simpa [hΦΨ] using (hrB (ball_subset_closedBall (Opens.mem_mk.1 hy).2)).2.1
  -- The coefficients composed with `Φ` are measurable and bounded on `Ω'`.
  have hDs : ((Omega ⊓ O : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) ⊆ Omega :=
    SetLike.coe_subset_coe.2 inf_le_left
  have hac : (volume.restrict (Ω' : Set (WithLp 2 (ℝ × E)))).map Φ ≪
      volume.restrict (Omega : Set (WithLp 2 (ℝ × E))) :=
    (Measure.absolutelyContinuous_of_le_smul (hΦ'.map_restrict_le volume)).trans
      (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hDs le_rfl))
  have hAΛ : ∀ x ∈ (Ω' : Set (WithLp 2 (ℝ × E))), ‖A (Φ x)‖ ≤ ‖A (Φ y₀)‖ + 1 := fun x hx =>
    ((hrB (ball_subset_closedBall (Opens.mem_mk.1 (Opens.mem_inf.1 hx).2))).2.2
      (hDs (hΦ'.mapsTo hx))).le
  -- The estimate on the flat side, on `Ω' ∩ K` with `K = closedBall y₀ (r / 2)`.
  obtain ⟨C₁, hC₁⟩ := exists_lpNorm_iteratedGradient_le_of_pullback hp hp_top hΦ hΨ hΨΦ hΦΨ hΦc
    (Ω' := Ω') (B := B) (by rw [Opens.coe_inf, inter_assoc, inter_self])
    (fun x hx => ⟨hDs (hΦ'.mapsTo hx), (Opens.mem_mk.1 (Opens.mem_inf.1 (hΦ'.mapsTo hx)).2).1⟩)
    (isCompact_closedBall y₀ (r / 2)) (closedBall_subset_ball (half_lt_self hr))
    ((closedBall_subset_closedBall (half_le_self hr.le)).trans (hrB.trans inter_subset_left))
    (fun x hx => (hrB (closedBall_subset_closedBall (half_le_self hr.le) hx)).2.1)
    ((hA.mono_ac hac).comp_aemeasurable hΦ'.aemeasurable) hcont hell hAΛ
    ((hb.mono_ac hac).comp_aemeasurable hΦ'.aemeasurable)
    (hΦ'.ae_comp (ae_restrict_of_ae_restrict_of_subset hDs hbβ))
    ((hc.mono_ac hac).comp_aemeasurable hΦ'.aemeasurable)
    (hΦ'.ae_comp (ae_restrict_of_ae_restrict_of_subset hDs hcγ))
  -- Push forward to `Ω ∩ V` with `V = U ∩ Ψ⁻¹(B(y₀, r / 2))`, which `Ψ` maps to `H ∩ B(y₀, r / 2)`.
  have hhalf : ball y₀ (r / 2) ⊆ ball y₀ r := ball_subset_ball (half_le_self hr.le)
  obtain ⟨-, -, hΨ''⟩ := isChangeOfVariables_inf_ball (H := normalHalfSpace 0) hΦ hΨ hΨΦ hΨc
    himage (hhalf.trans (ball_subset_closedBall.trans (hrB.trans inter_subset_left)))
  have hΩ'' : normalHalfSpace 0 ⊓ ⟨ball y₀ (r / 2), isOpen_ball⟩ ≤ Ω' :=
    inf_le_inf_left _ fun x hx => Opens.mem_mk.2 (hhalf (Opens.mem_mk.1 hx))
  let V : Opens (WithLp 2 (ℝ × E)) := ⟨U ∩ Ψ ⁻¹' ball y₀ (r / 2),
    hΨc.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball⟩
  refine ⟨V, Opens.mem_mk.2 ⟨hΦ.mapsTo hy₀, by
    rw [mem_preimage, hΨΦ]; exact mem_ball_self (half_pos hr)⟩, _, fun u f hu0 heq =>
    lpNorm_iteratedGradient_le_of_pullback hp_top hΦ' hΨ' hΨ'' hΨΦ hΦΨ hΦc hΨc hOW hBO
      (inf_le_inf_left _ fun y hy => Opens.mem_mk.2
        ⟨(Opens.mem_mk.1 hy).1, hhalf (Opens.mem_mk.1 hy).2⟩) hΩ''
      (fun x hx => ⟨hΩ'' hx, ball_subset_closedBall (Opens.mem_mk.1 (Opens.mem_inf.1 hx).2)⟩)
      hC₁ u f hu0 heq⟩

open Wkp in
/-- **The Calderón–Zygmund estimate near a `C²` boundary portion for continuous coefficients.**
Let `1 < p < ∞` and let `Ω ⊆ ℝ × E` be open. Suppose that, in rigid coordinates `e` centred at
`x₀ = e⁻¹ 0`, inside the normal cylinder of half-height `h₀` and radius `r₀`, `Ω` is the region
above the graph of a `C²` function `φ : E → ℝ` with `φ 0 = 0`. Let `W` be an open neighbourhood of
`x₀`. Let `A` be a field of endomorphisms of `ℝ × E`, measurable on `Ω` and continuous within `Ω`
at every point of `W`, such that `A x` is elliptic at every `x ∈ W` in the closure of `Ω`, that is,
`λₓ ‖ξ‖² ≤ ⟪A x ξ, ξ⟫` for some `λₓ > 0`, and let `b` and `c` be measurable with `‖b x‖ ≤ β` and
`|c x| ≤ γ` for almost every `x ∈ Ω`. Then there are an open neighbourhood `V` of `x₀` and a
constant `C`, independent of `u` and `f`, such that every `u ∈ W^{2,p}(Ω)` which vanishes on
`∂Ω ∩ W`, in the sense that `ψ u ∈ W^{1,p}_0(Ω)` for every smooth `ψ` with compact support in `W`,
and solves `tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ(Ω)` almost everywhere on `Ω`, satisfies

`‖D²u‖_{Lᵖ(Ω ∩ V)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖∇u‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`. -/
theorem exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph (hp : 1 < p)
    (hp_top : p ≠ ⊤) {Omega W : Opens (WithLp 2 (ℝ × E))}
    {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {φ : E → ℝ} {h₀ r₀ : ℝ} (hh₀ : 0 < h₀)
    (hr₀ : 0 < r₀) (hφ0 : φ 0 = 0) (hφ : ContDiff ℝ 2 φ)
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    (hW : e.symm 0 ∈ W) {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ x ∈ W, ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ W, x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))) →
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ V : Opens (WithLp 2 (ℝ × E)), e.symm 0 ∈ V ∧ ∃ C : ℝ,
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
          ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
            W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
              fun x => ψ x * value 2 u x) →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
            ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
        lpNorm (iteratedGradient 1 u) p
            (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ V)) ≤
          C * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) := by
  -- Flatten the boundary by `Φ = e⁻¹ ∘ G⁻¹`, `G` graph flattening by `φ`, with inverse `G ∘ e`.
  obtain ⟨U', U, L, h0, -, hΦ, hΨ, himage⟩ :=
    exists_isChangeOfVariables_normalHalfSpace_of_contDiff one_le_two hh₀ hr₀ hφ0 hφ hgraph
  set G := graphFlattening φ hφ.continuous
  have hΨΦ (y : WithLp 2 (ℝ × E)) : (G ∘ e) ((e.symm ∘ G.symm) y) = y := by simp
  have hΦΨ (x : WithLp 2 (ℝ × E)) : (e.symm ∘ G.symm) ((G ∘ e) x) = x := by simp
  have hΦ0 : (e.symm ∘ G.symm) 0 = e.symm 0 := by simp [G, hφ0]
  obtain ⟨V, hV, C, hC⟩ := exists_lpNorm_iteratedGradient_le_of_isChangeOfVariables hp hp_top hΦ
    hΨ hΨΦ hΦΨ (e.symm.continuous.comp G.symm.continuous) (G.continuous.comp e.continuous)
    himage h0 (hΦ0 ▸ hW) hA hcont hell hb hbβ hc hcγ
  refine ⟨V, hΦ0 ▸ hV, C, fun u f hu0 heq => ?_⟩
  simpa only [Opens.coe_inf] using hC u f hu0 heq

open Wkp in
/-- **The estimate near an interior point.** For `x ∈ Ω`, the `W^{2,p}` estimate holds on `Ω ∩ V`
for a ball `V` about `x`. This is the half-space estimate on a ball inside `Ω` and inside a
half-space, where no boundary condition is needed. -/
private theorem exists_lpNorm_iteratedGradient_le_of_mem (hp : 1 < p) (hp_top : p ≠ ⊤)
    {Omega : Opens (WithLp 2 (ℝ × E))} {x : WithLp 2 (ℝ × E)}
    (hx : x ∈ (Omega : Set (WithLp 2 (ℝ × E))))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ y, ContinuousWithinAt A Omega y)
    (hell : ∀ y ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A y ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ V : Opens (WithLp 2 (ℝ × E)), x ∈ V ∧ ∃ C : ℝ,
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        (∀ ψ : WithLp 2 (ℝ × E) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
          ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
            W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
              fun x => ψ x * value 2 u x) →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
            ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
        lpNorm (iteratedGradient 1 u) p
            (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ V)) ≤
          C * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) := by
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 Omega.isOpen x hx
  -- Inside `B(x, ρ) ⊆ Ω`, the domain agrees with the half-space `{x.fst - ρ < y.fst}`.
  let B : Opens (WithLp 2 (ℝ × E)) := ⟨ball x ρ, isOpen_ball⟩
  have hBH : (B : Set (WithLp 2 (ℝ × E))) ⊆ normalHalfSpace (E := E) (x.fst - ρ) := fun y hy => by
    have h := (WithLp.norm_fst_le _ (y - x)).trans_lt (mem_ball_iff_norm.1 hy)
    rw [Real.norm_eq_abs, WithLp.sub_fst] at h
    rw [SetLike.mem_coe, mem_normalHalfSpace]
    linarith [abs_lt.1 h]
  have hΩB : (Omega : Set (WithLp 2 (ℝ × E))) ∩ B =
      (normalHalfSpace (E := E) (x.fst - ρ) : Set (WithLp 2 (ℝ × E))) ∩ B := by
    have hBΩ : (B : Set (WithLp 2 (ℝ × E))) ⊆ Omega := hρΩ
    rw [inter_eq_right.2 hBΩ, inter_eq_right.2 hBH]
  obtain ⟨C, hC⟩ := exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_normalHalfSpace hp
    hp_top (x.fst - ρ) hΩB (isCompact_closedBall x (ρ / 2))
    (closedBall_subset_ball (half_lt_self hρ)) hA (fun y _ => hcont y) (fun y _ hy => hell y hy)
    hb hbβ hc hcγ
  refine ⟨⟨ball x (ρ / 2), isOpen_ball⟩, mem_ball_self (half_pos hρ), C, fun u f hu0 heq => ?_⟩
  have hmem : MemLp (iteratedGradient 1 u) p
      (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ closedBall x (ρ / 2))) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  exact (lpNorm_mono_measure hmem
    (Measure.restrict_mono (inter_subset_inter_right _ ball_subset_closedBall) le_rfl)).trans
      (hC u f (fun ψ hψ hψc _ => hu0 ψ hψ hψc) heq)

open Wkp in
/-- **The estimate near a point of the closure.** Under the hypotheses of
`TauCeti.exists_norm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph`, with `A`
continuous within `Ω` everywhere, every point `x` of the closure of `Ω` has an open neighbourhood
`V` on whose part in `Ω` the `W^{2,p}` estimate holds for solutions in `W^{1,p}_0(Ω)`: by the
interior estimate at points of `Ω`, by flattening the boundary at points of `∂Ω`. -/
private theorem exists_lpNorm_iteratedGradient_le_of_mem_closure (hp : 1 < p) (hp_top : p ≠ ⊤)
    {Omega : Opens (WithLp 2 (ℝ × E))}
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont' : ∀ x, ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    {x : WithLp 2 (ℝ × E)} (hx : x ∈ closure (Omega : Set (WithLp 2 (ℝ × E)))) :
    ∃ V : Opens (WithLp 2 (ℝ × E)), x ∈ V ∧ ∃ C : ℝ,
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        firstOrder 1 u ∈ w1p0Submodule volume Omega p →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
            ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
        lpNorm (iteratedGradient 1 u) p
            (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ V)) ≤
          C * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) := by
  -- Zero boundary values give `ψ u ∈ W^{1,p}_0(Ω)` for every smooth compactly supported `ψ`.
  have hu0 : ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2),
      firstOrder 1 u ∈ w1p0Submodule volume Omega p → ∀ ψ : WithLp 2 (ℝ × E) → ℝ,
        ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        ∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
          W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
            fun x => ψ x * value 2 u x := fun u hu ψ hψ hψc => by
    simpa only [value_firstOrder] using
      W1p.exists_w1p0_value_ae_eq_mul_of_mem_w1p0Submodule hψ hψc hu
  by_cases hxΩ : x ∈ (Omega : Set (WithLp 2 (ℝ × E)))
  · obtain ⟨V, hV, C, hC⟩ := exists_lpNorm_iteratedGradient_le_of_mem hp hp_top hxΩ hA hcont'
      hell hb hbβ hc hcγ
    exact ⟨V, hV, C, fun u f hu heq => hC u f (hu0 u hu) heq⟩
  · obtain ⟨e, φ, h₀, r₀, hex, hh₀, hr₀, hφ0, hφ, hgraph⟩ :=
      hbdry x ⟨hx, by rwa [Omega.isOpen.interior_eq]⟩
    have hx₀ : e.symm 0 = x := by rw [← hex, e.symm_apply_apply]
    obtain ⟨V, hV, C, hC⟩ :=
      exists_lpNorm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph hp hp_top
        (W := ⊤) hh₀ hr₀ hφ0 hφ hgraph trivial hA (fun y _ => hcont' y)
        (fun y _ hy => hell y hy) hb hbβ hc hcγ
    exact ⟨V, hx₀ ▸ hV, C, fun u f hu heq => hC u f (fun ψ hψ hψc _ => hu0 u hu ψ hψ hψc) heq⟩

open Wkp in
/-- **The global Calderón–Zygmund estimate on a bounded `C²` domain for continuous coefficients.**
Let `1 < p < ∞` and let `Ω ⊆ ℝ × E` be a bounded open set with `C²` boundary: at every boundary
point `x`, in rigid coordinates `e` with `e x = 0`, inside a normal cylinder, `Ω` is the region
above the graph of a `C²` function `φ` with `φ 0 = 0`. Let `A` be a field of endomorphisms of
`ℝ × E`, measurable on `Ω` and continuous within `Ω` at every point of the closure of `Ω`, with
`A x` elliptic at every such point: `λₓ ‖ξ‖² ≤ ⟪A x ξ, ξ⟫` for some `λₓ > 0`. Let `b` and `c` be
measurable with `‖b x‖ ≤ β` and `|c x| ≤ γ` for almost every `x ∈ Ω`. Then there is a constant `C`,
independent of `u` and `f`, such that every `u ∈ W^{2,p}(Ω)` with `u ∈ W^{1,p}_0(Ω)` solving
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ(Ω)` almost everywhere on `Ω` satisfies

`‖D²u‖_{Lᵖ(Ω)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖∇u‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`.

This is Gilbarg–Trudinger's Theorem 9.13 with the gradient term still on the right; an
interpolation inequality removes it. -/
theorem exists_norm_iteratedGradient_le_of_continuousWithinAt_of_contDiff_graph (hp : 1 < p)
    (hp_top : p ≠ ⊤) {Omega : Opens (WithLp 2 (ℝ × E))}
    (hΩ : Bornology.IsBounded (Omega : Set (WithLp 2 (ℝ × E))))
    (hbdry : ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst))
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hA : AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcont : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))), ContinuousWithinAt A Omega x)
    (hell : ∀ x ∈ closure (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {b : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hbβ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), ‖b x‖ ≤ β)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
      firstOrder 1 u ∈ w1p0Submodule volume Omega p →
      (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) +
          ⟪b x, iteratedGradient 0 (lowerOrder 1 u) x⟫_ℝ + c x * value 2 u x = f x) →
      ‖iteratedGradient 1 u‖ ≤ C * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) := by
  -- Continuity within `Ω` is automatic away from the closure of `Ω`.
  have hcont' : ∀ x, ContinuousWithinAt A Omega x := fun x => by
    by_cases hx : x ∈ closure (Omega : Set (WithLp 2 (ℝ × E)))
    · exact hcont x hx
    · exact continuousWithinAt_of_notMem_closure hx
  -- Every point of the closure of `Ω` has a neighbourhood `V` on whose part in `Ω` the estimate
  -- holds.
  have hloc := fun x hx => exists_lpNorm_iteratedGradient_le_of_mem_closure hp hp_top hbdry hA
    hcont' hell hb hbβ hc hcγ (x := x) hx
  -- Finitely many such neighbourhoods cover the compact closure of `Ω`; sum the estimates.
  choose! V hxV C hC using hloc
  obtain ⟨t, htΩ, hcover⟩ := hΩ.isCompact_closure.elim_nhds_subcover (fun x => (V x : Set _))
    fun x hx => (V x).isOpen.mem_nhds (hxV x hx)
  refine ⟨∑ x ∈ t, C x, fun u f hu heq => ?_⟩
  have hcoverΩ : (Omega : Set (WithLp 2 (ℝ × E))) ⊆
      ⋃ x ∈ t, (Omega : Set (WithLp 2 (ℝ × E))) ∩ V x := fun y hy => by
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover (subset_closure hy))
    exact mem_iUnion₂.2 ⟨x, hxt, hy, hyx⟩
  calc ‖iteratedGradient 1 u‖
      = lpNorm (iteratedGradient 1 u) p (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) :=
        Lp.norm_eq_lpNorm_of_ae_eq (Filter.EventuallyEq.refl _ _)
    _ ≤ ∑ x ∈ t, lpNorm (iteratedGradient 1 u) p
          (volume.restrict ((Omega : Set (WithLp 2 (ℝ × E))) ∩ V x)) :=
        lpNorm_restrict_le_sum_of_subset_biUnion hp.le hcoverΩ fun x _ =>
          (Lp.memLp _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    _ ≤ ∑ x ∈ t, C x * (‖f‖ + ‖iteratedGradient 0 (lowerOrder 1 u)‖ + ‖value 2 u‖) :=
        Finset.sum_le_sum fun x hxt => hC x (htΩ x hxt) u f hu heq
    _ = _ := (Finset.sum_mul _ _ _).symm

end TauCeti
