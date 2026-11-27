/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Dirichlet.Existence
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Ball.Basic
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Hessian
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# The `W^{2,p}` Dirichlet problem on balls

Let `1 < p < ∞`. This file applies the `W^{2,p}` theory of the Dirichlet problem on bounded
domains with `C²` boundary to balls `B(x₀, r) ⊆ ℝ × E`, whose boundary charts are given by
`TauCeti.exists_affineIsometryEquiv_contDiff_ball_iff`.

* **Solvability**
  (`TauCeti.existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_add_mul_eq_of_eq_ball`).
  For `A` continuous and elliptic on the closed ball and `c ≤ 0` bounded, the problem
  `tr (A ∘ D²u) + c u = f` in `B(x₀, r)`, `u ∈ W^{2,p} ∩ W^{1,p}_0`, has exactly one solution for
  every `f ∈ Lᵖ`.
* **A uniform estimate for constant coefficients**
  (`TauCeti.exists_norm_iteratedGradient_le_of_traceCLM_comp_iteratedGradient_eq_of_eq_ball`). For
  `0 < λ` and `Λ` there is a constant `C` such that

  `‖D²u‖_{Lᵖ(B(x₀, r))} ≤ C ‖tr (A ∘ D²u)‖_{Lᵖ(B(x₀, r))}`

  for every constant coefficient `A` with `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `‖A‖ ≤ Λ`, every ball `B(x₀, r)`
  and every `u ∈ W^{2,p}(B(x₀, r)) ∩ W^{1,p}_0(B(x₀, r))`. The constant depends neither on the
  ball nor on `A` beyond `λ` and `Λ`.

The second statement is the comparison step in the mean oscillation estimates for the Hessian with
coefficients of small mean oscillation: on each ball the coefficient is frozen at a matrix `A`
that varies with the ball, and a solution of the frozen equation with `Lᵖ` datum is split into a
solution of the homogeneous equation, whose mean oscillation decays
(`TauCeti.PDE.setIntegral_ball_norm_iteratedGradient_sub_setAverage_le_of_sum_mul_inner_eq_zero`),
and the solution of the Dirichlet problem with the same datum, controlled by this estimate. For
exponents `1 < p < 2`, where the solutions need not have square integrable second derivatives, the
`L²` comparison behind the estimates for `p > 2` is not available.

## The argument

On the unit ball, the a priori estimate of the Dirichlet problem
(`TauCeti.exists_norm_le_of_traceCLM_comp_iteratedGradient_add_mul_eq`, Gilbarg–Trudinger,
Lemma 9.17) holds for each `A` with some constant. The operators `u ↦ tr (A ∘ D²u)` depend
continuously, indeed linearly, on `A`, and the admissible `A` form a compact set, so one constant
serves for all of them (`IsCompact.exists_forall_norm_le_mul_eLpNorm_of_traceCLM_comp`). A
general ball is the image of the unit ball under `y ↦ x₀ + r y`. Precomposing with this map
(`TauCeti.Wkp.compL`) multiplies the Hessian by `r²`, preserves zero boundary values, and changes
`Lᵖ` norms by the factors `r^{∓n/p}`, `n = dim (ℝ × E)`, coming from the Jacobian. These factors
cancel in the estimate, which is therefore scale invariant.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.15 and Lemma 9.17.
* H. Dong, D. Kim, *On the `Lₚ`-solvability of higher order parabolic and elliptic systems with
  BMO coefficients*, Arch. Ration. Mech. Anal. 199 (2011), 889–941 (the comparison with the frozen
  problem in `L^q`).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Metric InnerProductSpace Filter Module
open scoped ENNReal NNReal Topology ContDiff

namespace TauCeti

open Wkp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The boundary charts of a ball, in the form taken by the `W^{2,p}` theory of the Dirichlet
problem. -/
private theorem exists_chart_of_mem_frontier {Omega : Opens (WithLp 2 (ℝ × E))}
    {x₀ : WithLp 2 (ℝ × E)} {r : ℝ} (hr : 0 < r)
    (hΩ : (Omega : Set (WithLp 2 (ℝ × E))) = ball x₀ r) :
    ∀ x ∈ frontier (Omega : Set (WithLp 2 (ℝ × E))),
      ∃ (e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (φ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ φ 0 = 0 ∧ ContDiff ℝ 2 φ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ φ z.snd < z.fst) := by
  intro x hx
  rw [hΩ] at hx
  obtain ⟨e, φ, h₀, r₀, h1, h2, h3, h4, h5, -, h6⟩ :=
    exists_affineIsometryEquiv_contDiff_ball_iff x₀ hr hx
  refine ⟨e, φ, h₀, r₀, h1, h2, h3, h4, h5.of_le (by simp), fun z hz => ?_⟩
  rw [← SetLike.mem_coe, hΩ]
  exact h6 z hz

/-- **The Dirichlet problem in `W^{2,p}` on a ball** (Gilbarg–Trudinger, Theorem 9.15). Let
`1 < p < ∞` and let `Ω = B(x₀, r) ⊆ ℝ × E`. Let `A` be continuous within `Ω` and elliptic at every
point of the closed ball, and let `c` be measurable, bounded and `c ≤ 0` almost everywhere. Then
for every `f ∈ Lᵖ(Ω)` there is exactly one `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` with
`tr (A ∘ D²u) + c u = f` almost everywhere on `Ω`. -/
theorem existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_add_mul_eq_of_eq_ball
    (hp : 1 < p) (hp_top : p ≠ ⊤) {Omega : Opens (WithLp 2 (ℝ × E))} {x₀ : WithLp 2 (ℝ × E)}
    {r : ℝ} (hr : 0 < r) (hΩ : (Omega : Set (WithLp 2 (ℝ × E))) = ball x₀ r)
    {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
    (hcont : ∀ x ∈ closedBall x₀ r, ContinuousWithinAt A (ball x₀ r) x)
    (hell : ∀ x ∈ closedBall x₀ r, ∃ lam : ℝ, 0 < lam ∧ ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {c : WithLp 2 (ℝ × E) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))
    (hcγ : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), |c x| ≤ γ)
    (hc0 : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), c x ≤ 0)
    (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)) :
    ∃! u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2,
      firstOrder 1 u ∈ w1p0Submodule volume Omega p ∧
      ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L iteratedGradient 1 u x) + c x * value 2 u x =
          f x := by
  have hcl : closure (Omega : Set (WithLp 2 (ℝ × E))) = closedBall x₀ r := by
    rw [hΩ, closure_ball x₀ hr.ne']
  exact existsUnique_firstOrder_mem_w1p0Submodule_and_traceCLM_comp_iteratedGradient_add_mul_eq hp
    hp_top (by rw [hΩ]; exact isBounded_ball) (exists_chart_of_mem_frontier hr hΩ)
    (fun x hx => hΩ ▸ hcont x (hcl ▸ hx)) (fun x hx => hell x (hcl ▸ hx)) hc hcγ hc0 f

/-- The a priori estimate for constant coefficients on the unit ball, with one constant for all
coefficients `A` with `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and `‖A‖ ≤ Λ`. The datum enters as any function `g` equal
to `tr (A ∘ D²u)` almost everywhere. -/
private theorem exists_norm_le_mul_eLpNorm_of_eq_ball_zero_one (hp : 1 < p) (hp_top : p ≠ ⊤)
    {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) {V : Opens (WithLp 2 (ℝ × E))}
    (hV : (V : Set (WithLp 2 (ℝ × E))) = ball 0 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E),
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) → ‖A‖ ≤ Lam →
      ∀ u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) V p 2,
        firstOrder 1 u ∈ w1p0Submodule volume V p →
      ∀ g : WithLp 2 (ℝ × E) → ℝ, (∀ᵐ x ∂volume.restrict (V : Set (WithLp 2 (ℝ × E))),
        traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L iteratedGradient 1 u x) = g x) →
      ‖u‖ ≤ C * (eLpNorm g p (volume.restrict (V : Set (WithLp 2 (ℝ × E))))).toReal := by
  -- The admissible coefficients form a compact set.
  have hK : IsCompact ({A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) | ‖A‖ ≤ Lam} ∩
      ⋂ ξ, {A | lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ}) := by
    have : ProperSpace (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) := by
      simpa +instances using FiniteDimensional.proper ℝ (WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E))
    have hξ : ∀ ξ : WithLp 2 (ℝ × E), IsClosed {A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E) |
        lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ} := fun ξ =>
      isClosed_le continuous_const
        ((continuous_id.clm_apply continuous_const).inner continuous_const)
    -- The closed ball is compact in the metric topology, in which `‖·‖` is continuous.
    exact (isCompact_closedBall (0 : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) Lam
      |>.of_isClosed_subset ((isClosed_le continuous_norm continuous_const).inter
        (isClosed_iInter hξ)) fun A hA => mem_closedBall_zero_iff.2 hA.1)
  -- The Banach space `M = W^{2,p}(V) ∩ W^{1,p}_0(V)`.
  set M : Submodule ℝ (Wkp (volume : Measure (WithLp 2 (ℝ × E))) V p 2) :=
    (w1p0Submodule volume V p).toSubmodule.comap (firstOrderL 1).toLinearMap
  have hM : ∀ u, u ∈ M ↔ firstOrder 1 u ∈ w1p0Submodule volume V p := fun u => by
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, firstOrderL_apply,
      ClosedSubmodule.mem_toSubmodule_iff]
  -- For each admissible `A`, Gilbarg–Trudinger's Lemma 9.17 on the unit ball.
  obtain ⟨C, hC0, hC⟩ := hK.exists_forall_norm_le_mul_eLpNorm_of_traceCLM_comp
    ((iteratedGradientL 1).comp M.subtypeL) fun A hA => by
      obtain ⟨C, hC⟩ := exists_norm_le_of_traceCLM_comp_iteratedGradient_add_mul_eq hp hp_top
        (Omega := V) (by rw [hV]; exact isBounded_ball) (exists_chart_of_mem_frontier one_pos hV)
        (A := fun _ => A) (fun _ _ => continuousWithinAt_const)
        (fun _ _ => ⟨lam, hlam, mem_iInter.1 hA.2⟩) (c := 0) (γ := 0) aestronglyMeasurable_const
        (ae_of_all _ fun _ => by simp) (ae_of_all _ fun _ => le_rfl)
      exact ⟨C, fun m f hf => hC m f ((hM m).1 m.property) (by
        filter_upwards [hf] with x hx
        rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, iteratedGradientL_apply] at hx
        simpa using hx)⟩
  refine ⟨C, hC0, fun A hA hAΛ u hu g hg => ?_⟩
  have h := hC A ⟨hAΛ, mem_iInter.2 hA⟩ ⟨u, (hM u).2 hu⟩ g (by
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [iteratedGradientL_apply]
    exact hg)
  simpa using h


omit [MeasurableSpace E] [BorelSpace E] in
/-- The affine map `Ψ y = x₀ + r y` is a change of variables of order two from the unit ball onto
`B(x₀, r)`, and its inverse `Φ x = r⁻¹ (x - x₀)` is one from `B(x₀, r)` onto the unit ball. The
lower bounds `c` and `c'` of their Jacobians, the Jacobians themselves, multiply to one. -/
private theorem exists_isChangeOfVariables_smul_add {V Omega : Opens (WithLp 2 (ℝ × E))}
    (hV : (V : Set (WithLp 2 (ℝ × E))) = ball 0 1) {x₀ : WithLp 2 (ℝ × E)} {r : ℝ} (hr : 0 < r)
    (hΩ : (Omega : Set (WithLp 2 (ℝ × E))) = ball x₀ r) :
    ∃ L c L' c' : ℝ, Wkp.IsChangeOfVariables 2 V Omega (fun y => x₀ + r • y) L c ∧
      Wkp.IsChangeOfVariables 2 Omega V (fun x => r⁻¹ • (x - x₀)) L' c' ∧ c' * c = 1 := by
  -- `Ψ = τ ∘ D` and `Φ = D⁻¹ ∘ τ⁻¹`, through the ball `W = B(0, r)`, for the dilation `D y = r y`
  -- and the translation `τ y = x₀ + y`.
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨ball 0 r, isOpen_ball⟩
  let D : WithLp 2 (ℝ × E) ≃L[ℝ] WithLp 2 (ℝ × E) :=
    (LinearEquiv.smulOfNeZero ℝ _ r hr.ne').toContinuousLinearEquiv
  let τ : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E) :=
    AffineIsometryEquiv.constVAdd ℝ (WithLp 2 (ℝ × E)) x₀
  have hD : ∀ y, D y = r • y := fun y => rfl
  have hD' : ∀ y, D.symm y = r⁻¹ • y := fun y =>
    D.symm_apply_eq.2 (by rw [hD, smul_smul, mul_inv_cancel₀ hr.ne', one_smul])
  have hτ' : ∀ y, τ.symm y = y - x₀ := fun y => by
    rw [AffineIsometryEquiv.symm_apply_eq]
    exact (add_sub_cancel _ _).symm
  have hΨ := (Wkp.IsChangeOfVariables.continuousLinearEquiv (k := 2) (U := V) (V := W) D
    fun y hy => by
      rw [SetLike.mem_coe, ← SetLike.mem_coe, hV, mem_ball_zero_iff] at hy
      simpa [hD, W, norm_smul, abs_of_pos hr] using mul_lt_of_lt_one_right hr hy
    ).affineIsometryEquiv_comp (V' := Omega) τ fun y hy => by
      rw [hΩ]
      simpa [W, τ, dist_eq_norm] using hy
  have hΦ := (Wkp.IsChangeOfVariables.continuousLinearEquiv (k := 2) (U := W) (V := V) D.symm
    fun y hy => by
      have : r⁻¹ * ‖y‖ < 1 := by rwa [inv_mul_lt_one₀ hr, ← mem_ball_zero_iff]
      rw [hV]
      simpa [hD', norm_smul, abs_of_pos hr] using this).affineIsometryEquiv_comp_comp
    (U' := Omega) (V' := V) τ.symm (AffineIsometryEquiv.refl ℝ _) (fun x hx => by
      rw [SetLike.mem_coe, ← SetLike.mem_coe, hΩ, mem_ball, dist_eq_norm] at hx
      simpa [W, hτ'] using hx) fun _ hy => hy
  have hΨfun : (⇑τ ∘ ⇑D) = fun y => x₀ + r • y := rfl
  have hΦfun : (⇑(AffineIsometryEquiv.refl ℝ _) ∘ ⇑D.symm ∘ ⇑τ.symm) =
      fun x => r⁻¹ • (x - x₀) := funext fun x => by simp [hD', hτ']
  refine ⟨_, _, _, _, hΨfun ▸ hΨ, hΦfun ▸ hΦ, ?_⟩
  rw [← abs_mul, ContinuousLinearEquiv.det_coe_symm, inv_mul_cancel₀ (abs_pos.1 hΨ.pos), abs_one]

/-- The weak Hessian of `u ∘ Ψ` for the affine map `Ψ y = x₀ + r y` is `r² D²u ∘ Ψ`. -/
private theorem iteratedGradient_compL_smul_add_ae (hp_top : p ≠ ⊤)
    {U V : Opens (WithLp 2 (ℝ × E))} {x₀ : WithLp 2 (ℝ × E)} {r L c : ℝ}
    (h : Wkp.IsChangeOfVariables 2 V U (fun y => x₀ + r • y) L c)
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) U p 2) :
    ∀ᵐ y ∂volume.restrict (V : Set (WithLp 2 (ℝ × E))),
      (iteratedGradient 1 (Wkp.compL h u) y : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)) =
        (r ^ 2) • iteratedGradient 1 u (x₀ + r • y) := by
  have hfd : fderiv ℝ (fun y : WithLp 2 (ℝ × E) => x₀ + r • y) =
      fun _ => r • ContinuousLinearMap.id ℝ (WithLp 2 (ℝ × E)) :=
    funext fun y => (((hasFDerivAt_id y).const_smul r).const_add x₀).fderiv
  filter_upwards [Wkp.inner_iteratedGradient_compL_ae h hp_top u] with y hy
  ext a
  refine ext_inner_right ℝ fun b => ?_
  rw [hy a b, hfd, fderiv_const_apply]
  simp only [smul_apply, ContinuousLinearMap.id_apply, map_smul, zero_apply, inner_zero_right,
    add_zero, real_inner_smul_left, real_inner_smul_right]
  ring

omit [Fact (1 ≤ p)] in
/-- Precomposing with a change of variables `Φ` and multiplying by `k` changes `Lᵖ` norms by at
most the factor `|k| c^{-1/p}`, where `c` bounds the Jacobian of `Φ` from below. -/
private theorem eLpNorm_const_mul_comp_le {U V : Opens (WithLp 2 (ℝ × E))}
    {Φ : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)} {L c : ℝ} (h : Wkp.IsChangeOfVariables 2 U V Φ L c)
    (k : ℝ) (g : WithLp 2 (ℝ × E) → ℝ) :
    eLpNorm (fun x => k * g (Φ x)) p (volume.restrict (U : Set (WithLp 2 (ℝ × E)))) ≤
      ‖k‖ₑ * ((ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal *
        eLpNorm g p (volume.restrict (V : Set (WithLp 2 (ℝ × E))))) := by
  have hfun : (fun x => k * g (Φ x)) = k • (g ∘ Φ) := rfl
  rw [hfun, eLpNorm_const_smul]
  gcongr
  exact eLpNorm_comp_le_of_map_le_smul h.aemeasurable (h.map_restrict_le volume) p

/-- For the affine map `Ψ y = x₀ + r y` with inverse `Φ x = r⁻¹ (x - x₀)`, the `Lᵖ` norm of the
weak Hessian of `u` is at most `r⁻² c'^{-1/p}` times that of `u ∘ Ψ`, where `c'` bounds the
Jacobian of `Φ` from below. -/
private theorem eLpNorm_iteratedGradient_le_of_compL_smul_add (hp_top : p ≠ ⊤)
    {U V : Opens (WithLp 2 (ℝ × E))} {x₀ : WithLp 2 (ℝ × E)} {r L c L' c' : ℝ} (hr : 0 < r)
    (hΨ : Wkp.IsChangeOfVariables 2 V U (fun y => x₀ + r • y) L c)
    (hΦ : Wkp.IsChangeOfVariables 2 U V (fun x => r⁻¹ • (x - x₀)) L' c')
    (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) U p 2) :
    eLpNorm (iteratedGradient 1 u) p (volume.restrict (U : Set (WithLp 2 (ℝ × E)))) ≤
      ‖(r ^ 2)⁻¹‖ₑ * ((ENNReal.ofReal c')⁻¹ ^ (1 / p).toReal *
        eLpNorm (iteratedGradient 1 (Wkp.compL hΨ u)) p
          (volume.restrict (V : Set (WithLp 2 (ℝ × E))))) := by
  rw [← eLpNorm_norm _ (Lp.aestronglyMeasurable (iteratedGradient 1 u)),
    eLpNorm_congr_ae (g := fun x => (r ^ 2)⁻¹ *
      ‖iteratedGradient 1 (Wkp.compL hΨ u) (r⁻¹ • (x - x₀))‖) ?_,
    ← eLpNorm_norm _ (Lp.aestronglyMeasurable (iteratedGradient 1 (Wkp.compL hΨ u)))]
  · exact eLpNorm_const_mul_comp_le (p := p) hΦ ((r ^ 2)⁻¹)
      fun y => ‖iteratedGradient 1 (Wkp.compL hΨ u) y‖
  filter_upwards [hΦ.ae_comp (mu := volume) (iteratedGradient_compL_smul_add_ae hp_top hΨ u)]
    with x hx
  rw [hx, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel, norm_smul,
    Real.norm_of_nonneg (by positivity), inv_mul_cancel_left₀ (by positivity)]

/-- **The uniform estimate for constant coefficients on balls.** Let `1 < p < ∞`, `0 < λ` and `Λ`.
There is a constant `C` such that for every `A : ℝ × E →L ℝ × E` with `λ ‖ξ‖² ≤ ⟪A ξ, ξ⟫` and
`‖A‖ ≤ Λ`, every ball `Ω = B(x₀, r)` and every `u ∈ W^{2,p}(Ω) ∩ W^{1,p}_0(Ω)` with
`tr (A ∘ D²u) = f` almost everywhere on `Ω`,

`‖D²u‖_{Lᵖ(Ω)} ≤ C ‖f‖_{Lᵖ(Ω)}`.

The constant depends neither on the ball nor on `A` beyond `λ` and `Λ`. -/
theorem exists_norm_iteratedGradient_le_of_traceCLM_comp_iteratedGradient_eq_of_eq_ball
    (hp : 1 < p) (hp_top : p ≠ ⊤) {lam : ℝ} (hlam : 0 < lam) (Lam : ℝ) :
    ∃ C : ℝ, ∀ A : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E),
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A ξ, ξ⟫_ℝ) → ‖A‖ ≤ Lam →
      ∀ {Omega : Opens (WithLp 2 (ℝ × E))} {x₀ : WithLp 2 (ℝ × E)} {r : ℝ}, 0 < r →
        (Omega : Set (WithLp 2 (ℝ × E))) = ball x₀ r →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        firstOrder 1 u ∈ w1p0Submodule volume Omega p →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A ∘L iteratedGradient 1 u x) = f x) →
        ‖iteratedGradient 1 u‖ ≤ C * ‖f‖ := by
  let V : Opens (WithLp 2 (ℝ × E)) := ⟨ball 0 1, isOpen_ball⟩
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_mul_eLpNorm_of_eq_ball_zero_one hp hp_top hlam Lam
    (V := V) rfl
  refine ⟨C, fun A hA hAΛ Omega x₀ r hr hΩ u f hu heq => ?_⟩
  obtain ⟨L, c, L', c', hΨ, hΦ, hcc⟩ := exists_isChangeOfVariables_smul_add (V := V) rfl hr hΩ
  -- `w = u ∘ Ψ` lies in `W^{2,p}(V) ∩ W^{1,p}_0(V)` and solves `tr (A ∘ D²w) = r² f ∘ Ψ`.
  set w := Wkp.compL (mu := volume) (p := p) hΨ u
  have hw0 : firstOrder 1 w ∈ w1p0Submodule volume V p := by
    rw [Wkp.firstOrder_compL hΨ hp_top u]
    refine hΨ.w1pCompL_mem_w1p0Submodule_of_leftInvOn hp_top hΦ.differentiableOn.continuousOn
      hΦ.mapsTo (fun y _ => ?_) hu
    simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hhess := iteratedGradient_compL_smul_add_ae hp_top hΨ u
  have hw := hC A hA hAΛ w hw0 (fun y => r ^ 2 * f (x₀ + r • y)) (by
    filter_upwards [hhess, hΨ.ae_comp (mu := volume) heq] with y h1 h2
    rw [h1, ContinuousLinearMap.comp_smul, map_smul, h2, smul_eq_mul])
  -- The `Lᵖ` norms of the datum and of the Hessian change by the Jacobian factors `c^{-1/p}` and
  -- `c'^{-1/p}`, whose product is one, and by `r^{±2}`.
  have hg := eLpNorm_const_mul_comp_le (p := p) hΨ (r ^ 2) f
  have hu2 := eLpNorm_iteratedGradient_le_of_compL_smul_add hp_top hr hΨ hΦ u
  -- Combining the three estimates.
  have hw2 := ENNReal.ofReal_le_ofReal ((norm_iteratedGradient_le 1 w).trans hw)
  have hgfin := hg.trans_lt (ENNReal.mul_lt_top eNorm_lt_top (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hΨ.pos).ne')) (Lp.eLpNorm_lt_top f)))
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), ENNReal.ofReal_mul hC0,
    ENNReal.ofReal_toReal hgfin.ne] at hw2
  have hjac :
      (ENNReal.ofReal c')⁻¹ ^ (1 / p).toReal * (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
      ← ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr (ENNReal.ofReal_pos.2 hΨ.pos).ne'),
      ← ENNReal.ofReal_mul hΦ.pos.le, hcc, ENNReal.ofReal_one, inv_one, ENNReal.one_rpow]
  have hr2 : ‖(r ^ 2)⁻¹‖ₑ * ‖r ^ 2‖ₑ = 1 := by
    rw [← eNorm_mul, inv_mul_cancel₀ (by positivity), eNorm_one]
  have hmain := calc
    eLpNorm (iteratedGradient 1 u) p (volume.restrict (Omega : Set (WithLp 2 (ℝ × E))))
      ≤ ‖(r ^ 2)⁻¹‖ₑ * ((ENNReal.ofReal c')⁻¹ ^ (1 / p).toReal * (ENNReal.ofReal C *
          (‖r ^ 2‖ₑ * ((ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal *
            eLpNorm f p (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))))))) :=
        hu2.trans (by gcongr; exact hw2.trans (by gcongr))
    _ = ENNReal.ofReal C * eLpNorm f p (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) *
        ((‖(r ^ 2)⁻¹‖ₑ * ‖r ^ 2‖ₑ) * ((ENNReal.ofReal c')⁻¹ ^ (1 / p).toReal *
          (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal)) := by ring
    _ = ENNReal.ofReal C * eLpNorm f p (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) := by
        rw [hr2, hjac, one_mul, mul_one]
  rw [Lp.norm_def, Lp.norm_def f, ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (by finiteness) hmain

end TauCeti
