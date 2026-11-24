/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
import TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction
import TauCeti.Analysis.Calculus.ContDiff.UniformOn
import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution

/-!
# Smooth families of compactly supported functions in `H^s`

Let `X` be a finite-dimensional real normed space of parameters and `F : X → E → ℂ` a family of
functions on a finite-dimensional real inner product space `E`, jointly smooth in the parameter and
the point, and supported in one closed ball `‖x‖ ≤ R` for every parameter. Then `c ↦ F c` is a
smooth map into every Bessel-potential space `H^s(E)`, `s ≥ 0`
(`BesselPotentialSpace.exists_contDiff_inclusionLp_ae_eq_of_hasCompactSupport`).

This is how families built from a fixed cutoff and smooth coefficients, such as the core of a
family of plane vortices over a window of divisors, enter Sobolev-space arguments.

The proof is by induction on the integer order. In `L²` the family factors through the bounded
continuous functions: `c ↦ F c` is a superposition `f ↦ G ∘ f` applied to the affine family
`c ↦ (x ↦ (c, ρ x))`, where `ρ` is the radial retraction onto the ball, and superposition operators
are smooth for the sup norm (`BoundedContinuousFunction.contDiffAt_of_forall_apply_eq`).
Restriction to the ball is a bounded operator from the bounded continuous functions to `L²`. The
derivatives `x ↦ ∂_v F c x` form a family of the same kind, so a family that is smooth in `H^k`
together with its first derivatives is smooth in `H^(k+1)`
(`BesselPotentialSpace.exists_contDiff_inclusion_eq_of_lineDerivOp_eq`).
-/

public section

noncomputable section

open MeasureTheory Module Filter Metric Set TemperedDistribution
open scoped ContDiff BesselPotentialSpace BoundedContinuousFunction Topology LineDeriv ENNReal

namespace BesselPotentialSpace

/-! ### The radial retraction onto a ball -/

section Retract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction `x ↦ (R / max R ‖x‖) • x` onto the closed ball of radius `R`. -/
private def retract (R : ℝ) (x : E) : E :=
  (R * (max R ‖x‖)⁻¹) • x

private theorem continuous_retract {R : ℝ} (hR : 0 < R) : Continuous (retract (E := E) R) :=
  (continuous_const.mul ((continuous_const.max continuous_norm).inv₀ fun _ ↦
    (hR.trans_le (le_max_left _ _)).ne')).smul continuous_id

private theorem norm_retract_le {R : ℝ} (hR : 0 < R) (x : E) : ‖retract R x‖ ≤ R := by
  have hm : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  rw [retract, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
  calc R * ((max R ‖x‖)⁻¹ * ‖x‖) ≤ R * 1 := by
        gcongr
        exact inv_mul_le_one_of_le₀ (le_max_right _ _) hm.le
    _ = R := mul_one R

/-- A function vanishing outside the ball of radius `R` does not see the retraction. -/
private theorem apply_retract {R : ℝ} (hR : 0 < R) {f : E → ℂ} (hf : ∀ x, R ≤ ‖x‖ → f x = 0)
    (x : E) : f (retract R x) = f x := by
  rcases le_or_gt ‖x‖ R with hx | hx
  · rw [retract, max_eq_left hx, mul_inv_cancel₀ hR.ne', one_smul]
  · rw [hf x hx.le, hf]
    rw [retract, max_eq_right hx.le, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), mul_assoc, inv_mul_cancel₀ (hR.trans hx).ne', mul_one]

/-! ### Families of bounded continuous functions -/

variable [FiniteDimensional ℝ E] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
/-- A jointly continuous family, read through the retraction onto a ball, is a family of bounded
continuous functions. -/
private theorem exists_boundedContinuousFunction {G : X × E → ℂ} (hG : Continuous G) {R : ℝ}
    (hR : 0 < R) : ∃ Ψ : X → E →ᵇ ℂ, ∀ c x, Ψ c x = G (c, retract R x) := by
  have hc (c : X) : Continuous fun x : E ↦ G (c, retract R x) :=
    hG.comp (continuous_const.prodMk (continuous_retract hR))
  have hb (c : X) : ∃ C, ∀ x : E, ‖G (c, retract R x)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
      (hG.comp (continuous_const.prodMk continuous_id)).continuousOn
    exact ⟨C, fun x ↦ hC _ (mem_closedBall_zero_iff.2 (norm_retract_le hR x))⟩
  choose C hC using hb
  exact ⟨fun c ↦ .ofNormedAddCommGroup _ (hc c) (C c) (hC c), fun _ _ ↦ rfl⟩

/-- **The family of bounded continuous functions is smooth.** For `G` jointly smooth, the family
`c ↦ (x ↦ G (c, ρ x))`, with `ρ` the retraction onto a ball, is smooth for the sup norm: it is a
superposition operator applied to an affine family. -/
private theorem contDiff_of_forall_apply_eq {G : X × E → ℂ} (hG : ContDiff ℝ ∞ G) {R : ℝ}
    (hR : 0 < R) {Ψ : X → E →ᵇ ℂ} (hΨ : ∀ c x, Ψ c x = G (c, retract R x)) :
    ContDiff ℝ ∞ Ψ := by
  refine contDiff_infty.2 fun n ↦ contDiff_iff_contDiffAt.2 fun c₀ ↦ ?_
  set s : Set (X × E) := closedBall c₀ 1 ×ˢ closedBall 0 (R + 1)
  have hs : IsCompact s := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hGs : TauCeti.UniformContDiffOn ℝ n G s :=
    ContDiffOn.uniformContDiffOn isOpen_univ (subset_univ _) hs
      (hG.contDiffOn.of_le (by exact_mod_cast le_top))
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hG.continuous.continuousOn
  -- The superposition by `G`, on the functions with values in `s`.
  classical
  set Θ : (E →ᵇ X × E) → E →ᵇ ℂ := fun f ↦
    if h : ∀ x, f x ∈ s then .ofNormedAddCommGroup (G ∘ f) (hG.continuous.comp f.continuous) C
      fun x ↦ hC _ (h x)
    else 0
  set f₀ : E →ᵇ X × E := .ofNormedAddCommGroup (fun x ↦ (c₀, retract R x))
    (continuous_const.prodMk (continuous_retract hR)) (max ‖c₀‖ R) fun x ↦
      max_le_max le_rfl (norm_retract_le hR x)
  have hf₀ (x : E) : ball (f₀ x) (1 / 2) ⊆ s := fun p hp ↦ by
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hp
    refine ⟨mem_closedBall.2 (hp.1.le.trans (by norm_num)), mem_closedBall_zero_iff.2 ?_⟩
    have h := norm_le_norm_add_norm_sub' p.2 (retract R x)
    rw [← dist_eq_norm] at h
    have := norm_retract_le hR x
    simp only [f₀, BoundedContinuousFunction.coe_ofNormedAddCommGroup] at hp
    linarith [hp.2]
  have hΘ : ∀ f ∈ ball f₀ (1 / 2), ∀ x, Θ f x = G (f x) := fun f hf x ↦ by
    have h : ∀ x, f x ∈ s := fun x ↦
      hf₀ x ((BoundedContinuousFunction.dist_coe_le_dist x).trans_lt (mem_ball.1 hf))
    simp [Θ, h]
  have hΘc := BoundedContinuousFunction.contDiffAt_of_forall_apply_eq hGs (by norm_num) hf₀ hΘ
  -- The affine family `c ↦ (x ↦ (c, ρ x))`.
  set L : X →L[ℝ] E →ᵇ X × E := LinearMap.mkContinuous
    { toFun := fun c ↦ BoundedContinuousFunction.const E ((c, 0) : X × E)
      map_add' := fun _ _ ↦ by ext <;> simp
      map_smul' := fun _ _ ↦ by ext <;> simp } 1 fun c ↦ by
        simp
  set ι : X → E →ᵇ X × E := fun c ↦ f₀ + L (c - c₀)
  have hι : ContDiff ℝ ∞ ι := contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const))
  have hι₀ : ι c₀ = f₀ := by simp [ι]
  refine ((hι₀ ▸ hΘc).comp c₀
    (hι.contDiffAt.of_le (by exact_mod_cast le_top))).congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds c₀ (by norm_num : (0 : ℝ) < 1 / 2)] with c hc
  have hιc : ι c ∈ ball f₀ (1 / 2) := by
    rw [mem_ball, dist_eq_norm]
    simp only [ι, add_sub_cancel_left]
    calc ‖L (c - c₀)‖ ≤ 1 * ‖c - c₀‖ := L.le_of_opNorm_le (LinearMap.mkContinuous_norm_le _
          zero_le_one _) _
      _ < 1 / 2 := by rw [one_mul, ← dist_eq_norm]; exact mem_ball.1 hc
  ext x
  rw [Function.comp_apply, hΘ _ hιc x, hΨ]
  simp [ι, L, f₀]

end Retract

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-! ### Square integrability -/

private theorem memLp_indicator_closedBall (R : ℝ) (g : E →ᵇ ℂ) :
    MemLp ((closedBall (0 : E) R).indicator g) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_closedBall.nullMeasurableSet]
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : E) R)) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall _ _).measure_lt_top.ne
  exact .of_bound g.continuous.aestronglyMeasurable ‖g‖ (.of_forall g.norm_coe_le_norm)

/-- Restriction to the closed ball of radius `R`, as a bounded operator from the bounded continuous
functions to `L²`. -/
private def restrictLp (R : ℝ) : (E →ᵇ ℂ) →L[ℝ] Lp ℂ 2 (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := fun g ↦ (memLp_indicator_closedBall R g).toLp _
      map_add' := fun f g ↦ by
        refine Lp.ext ?_
        filter_upwards [(memLp_indicator_closedBall R (f + g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_indicator_closedBall R f).toLp _)
            ((memLp_indicator_closedBall R g).toLp _),
          (memLp_indicator_closedBall R f).coeFn_toLp,
          (memLp_indicator_closedBall R g).coeFn_toLp] with x h₁ h₂ h₃ h₄
        rw [h₁, h₂, Pi.add_apply, h₃, h₄, FunLike.coe_add, indicator_add', Pi.add_apply]
      map_smul' := fun a g ↦ by
        refine Lp.ext ?_
        filter_upwards [(memLp_indicator_closedBall R (a • g)).coeFn_toLp,
          Lp.coeFn_smul a ((memLp_indicator_closedBall R g).toLp _),
          (memLp_indicator_closedBall R g).coeFn_toLp] with x h₁ h₂ h₃
        rw [h₁, RingHom.id_apply, h₂, Pi.smul_apply, h₃, FunLike.coe_smul]
        by_cases hx : x ∈ closedBall (0 : E) R <;> simp [hx] }
    ((volume (closedBall (0 : E) R) ^ (2 : ℝ≥0∞).toReal⁻¹).toReal) fun g ↦ by
      have hB : volume (closedBall (0 : E) R) ^ (2 : ℝ≥0∞).toReal⁻¹ ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by norm_num) (isCompact_closedBall _ _).measure_lt_top.ne
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp _ (memLp_indicator_closedBall R g), eLpNorm_indicator_eq_eLpNorm_restrict
        measurableSet_closedBall.nullMeasurableSet, ← ENNReal.toReal_ofReal (norm_nonneg g),
        ← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono (ENNReal.mul_ne_top hB ENNReal.ofReal_ne_top) ?_
      have h := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict (closedBall (0 : E) R))
        g.continuous.aestronglyMeasurable (.of_forall g.norm_coe_le_norm)
      rwa [Measure.restrict_apply_univ] at h

private theorem restrictLp_ae_eq (R : ℝ) (g : E →ᵇ ℂ) :
    restrictLp R g =ᵐ[volume] (closedBall (0 : E) R).indicator g :=
  (memLp_indicator_closedBall R g).coeFn_toLp

/-- **The case `L²`.** A jointly smooth family of functions vanishing outside a fixed ball is a
smooth map into `H⁰(E) = L²(E)`. -/
private theorem exists_contDiff_inclusionLp_zero {F : X → E → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) {R : ℝ} (hR : ∀ c x, R ≤ ‖x‖ → F c x = 0) :
    ∃ Φ : X → H^{((0 : ℕ) : ℝ)}(E), ContDiff ℝ ∞ Φ ∧
      ∀ c, ⇑(inclusionLp (Nat.cast_nonneg 0) (Φ c)) =ᵐ[volume] F c := by
  set R' := max R 1
  have hR' : 0 < R' := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨Ψ, hΨ⟩ := exists_boundedContinuousFunction (E := E) hF.continuous hR'
  have hΨc := contDiff_of_forall_apply_eq hF hR' hΨ
  -- `L²` is `H⁰(E)`.
  set J : Lp ℂ 2 (volume : Measure E) →L[ℂ] H^{((0 : ℕ) : ℝ)}(E) :=
    (inclusion (by simp)).comp (toLpₗᵢ E ℂ 0 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hJ (g : Lp ℂ 2 (volume : Measure E)) : inclusionLp (Nat.cast_nonneg 0) (J g) = g := by
    simp only [J, ContinuousLinearMap.comp_apply, inclusionLp_inclusion, inclusionLp_zero]
    exact (toLpₗᵢ_apply _).symm.trans ((toLpₗᵢ E ℂ 0 2).apply_symm_apply g)
  refine ⟨fun c ↦ J (restrictLp R' (Ψ c)),
    ((J.restrictScalars ℝ).comp (restrictLp R')).contDiff.comp hΨc, fun c ↦ ?_⟩
  rw [hJ]
  filter_upwards [restrictLp_ae_eq R' (Ψ c)] with x hx
  rw [hx]
  by_cases hxB : x ∈ closedBall (0 : E) R'
  · rw [indicator_of_mem hxB, hΨ, Function.uncurry_apply_pair, apply_retract hR' fun y hy ↦
      hR c y ((le_max_left _ _).trans hy)]
  · have hxR : R' < ‖x‖ := by simpa using hxB
    rw [indicator_of_notMem hxB, hR c x ((le_max_left _ _).trans hxR.le)]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The derivatives of a family vanishing outside a ball vanish outside a slightly larger ball. -/
private theorem fderiv_eq_zero_of_forall_le_norm {f : E → ℂ} {R : ℝ} (hf : ∀ x, R ≤ ‖x‖ → f x = 0)
    {x : E} (hx : R + 1 ≤ ‖x‖) : fderiv ℝ f x = 0 := by
  have hev : f =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [ball_mem_nhds x one_pos] with y hy
    refine hf y ?_
    have := norm_sub_norm_le x y
    rw [← dist_eq_norm, dist_comm] at this
    linarith [mem_ball.1 hy]
  rw [hev.fderiv_eq, fderiv_const_apply]

/-- **The case of an integer order.** -/
private theorem exists_contDiff_inclusionLp_natCast (k : ℕ) {F : X → E → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) {R : ℝ} (hR : ∀ c x, R ≤ ‖x‖ → F c x = 0) :
    ∃ Φ : X → H^{(k : ℝ)}(E), ContDiff ℝ ∞ Φ ∧
      ∀ c, ⇑(inclusionLp k.cast_nonneg (Φ c)) =ᵐ[volume] F c := by
  induction k generalizing F R with
  | zero => exact exists_contDiff_inclusionLp_zero hF hR
  | succ k ih =>
    set b := stdOrthonormalBasis ℝ E
    have hFc (c : X) : ContDiff ℝ ∞ (F c) := hF.comp (contDiff_const.prodMk contDiff_id)
    -- The derivatives `x ↦ ∂_{b i} F c x` form a family of the same kind.
    have hF' (i : Fin (finrank ℝ E)) :
        ContDiff ℝ ∞ (Function.uncurry fun c x ↦ fderiv ℝ (F c) x (b i)) := by
      have h : ContDiff ℝ ∞ fun p : X × E ↦ fderiv ℝ (F p.1) p.2 :=
        ContDiff.fderiv (f := fun p : X × E ↦ F p.1)
          (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by simp)
      exact h.clm_apply contDiff_const
    obtain ⟨Φ, hΦ, hΦF⟩ := ih hF hR
    choose Φ' hΦ' hΦ'F using fun i ↦ ih (hF' i) (R := R + 1) fun c x hx ↦ by
      simp [fderiv_eq_zero_of_forall_le_norm (hR c) hx]
    obtain ⟨u, hu, huΦ⟩ := exists_contDiff_inclusion_eq_of_lineDerivOp_eq b hΦ hΦ' fun c i ↦ by
      rw [← toTemperedDistribution_inclusionLp k.cast_nonneg,
        ← toTemperedDistribution_inclusionLp k.cast_nonneg]
      exact TauCeti.lineDerivOp_toTemperedDistribution_eq_of_contDiff ((hFc c).of_le (by simp))
        (hΦF c) (hΦ'F i c)
    have hle : ((k + 1 : ℕ) : ℝ) ≤ k + 1 := by push_cast; rfl
    refine ⟨fun c ↦ inclusion hle (u c), ((inclusion hle).restrictScalars ℝ).contDiff.comp hu,
      fun c ↦ ?_⟩
    rw [inclusionLp_inclusion, ← inclusionLp_inclusion (by linarith : (k : ℝ) ≤ k + 1)
      k.cast_nonneg, huΦ]
    exact hΦF c

/-- **Compactly supported smooth families are smooth in every `H^s`.** Let `F : X → E → ℂ` be
jointly smooth in the parameter `c ∈ X` and the point `x ∈ E`, and let every `F c` vanish outside
the closed ball of radius `R`. Then for every `s ≥ 0` there is a smooth map `Φ : X → H^s(E)` whose
`L²` function at `c` is `F c`. -/
theorem exists_contDiff_inclusionLp_ae_eq_of_forall_le_norm {F : X → E → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) {R : ℝ} (hR : ∀ c x, R ≤ ‖x‖ → F c x = 0) {s : ℝ}
    (hs : 0 ≤ s) :
    ∃ Φ : X → H^{s}(E), ContDiff ℝ ∞ Φ ∧ ∀ c, ⇑(inclusionLp hs (Φ c)) =ᵐ[volume] F c := by
  obtain ⟨Φ, hΦ, hΦF⟩ := exists_contDiff_inclusionLp_natCast ⌈s⌉₊ hF hR
  refine ⟨fun c ↦ inclusion (Nat.le_ceil s) (Φ c),
    ((inclusion (Nat.le_ceil s)).restrictScalars ℝ).contDiff.comp hΦ, fun c ↦ ?_⟩
  rw [inclusionLp_inclusion]
  exact hΦF c

end BesselPotentialSpace
