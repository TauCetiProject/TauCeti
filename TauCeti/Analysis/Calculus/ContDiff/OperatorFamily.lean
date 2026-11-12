/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Partial
import TauCeti.Analysis.Calculus.MeanValue

/-!
# Families of operators that are smooth pointwise with bounded derivatives

Let `Φ : E → Λ →L[𝕜] F` be a family of continuous linear maps on a normed space `Λ`, and `U` an
open subset of `E`. Suppose that for every `f : Λ` the function `y ↦ Φ y f` is `C^k` on `U`, and
that its derivatives of order at most `k` are bounded by `C * ‖f‖` near each point of `U`, with a
constant `C` independent of `f`. Such a family need not be `C^k` as a map into the operator space
`Λ →L[𝕜] F`, but it loses at most one derivative, and none at all once the operator is applied:

* `TauCeti.contDiffOn_of_forall_norm_iteratedFDeriv_le`: if the hypotheses hold to order `k + 1`,
  then `Φ` is `C^k` on `U` for the operator norm;
* `TauCeti.contDiffOn_apply_of_forall_norm_iteratedFDeriv_le`: if they hold to order `k`, then
  `(f, y) ↦ Φ y f` is `C^k` on `Λ × U`.

The motivating example is the evaluation map of a Banach space `Λ` of `C^k` functions, with
`Φ y f = f y`: for the `C^k` norm, `y ↦ (f ↦ f y)` is in general only `C^(k - 1)` into the dual
space, since the `k`th derivatives of the unit ball of `Λ` are not equicontinuous, yet the
evaluation map `(f, y) ↦ f y` is jointly `C^k`. This is the regularity of evaluation used to make
universal sections over spaces of `C^k` maps, such as `(f, x) ↦ df_x` on a compact manifold,
smooth enough for the Sard–Smale theorem.

Both statements are proved by induction on `k`, the second using the first. The derivatives of
the maps `y ↦ Φ y f` form a family of the same kind, with one derivative fewer. Joint
differentiability comes from the criterion of continuous partial derivatives,
`hasStrictFDerivAt_uncurry_coprod`: the partial derivative in `f` is `Φ y`, which is continuous
for the operator norm by the first statement one order lower, and the partial derivative in `y`
is the derivative family, jointly continuous by the second statement applied to it.
Operator-norm estimates come from the mean value inequality applied to each `y ↦ Φ y f`
separately (`Convex.norm_sub_sub_flip_le_of_norm_hasFDerivWithin_sub_le`).

## References

* R. Abraham and J. Robbin, *Transversal mappings and flows*, W. A. Benjamin, 1967, Chapter II
  (the evaluation map of a space of `C^k` maps is `C^k`).
-/

public section

open Filter Set Topology
open scoped ContDiff

namespace TauCeti

universe u v w

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped Classical in
/-- The derivatives `fderiv 𝕜 (fun z ↦ Φ z f) y`, as a continuous linear map of `f`, when each of
them exists and they are bounded by a multiple of `‖f‖`; otherwise `0`. -/
private noncomputable def derivFamily (Φ : E → Λ →L[𝕜] F) (y : E) : Λ →L[𝕜] E →L[𝕜] F :=
  if h : (∀ f, DifferentiableAt 𝕜 (fun z ↦ Φ z f) y) ∧
      ∃ C, ∀ f, ‖fderiv 𝕜 (fun z ↦ Φ z f) y‖ ≤ C * ‖f‖ then
    LinearMap.mkContinuousOfExistsBound
      { toFun := fun f ↦ fderiv 𝕜 (fun z ↦ Φ z f) y
        map_add' := fun f g ↦ by
          simp only [map_add]
          exact fderiv_add (h.1 f) (h.1 g)
        map_smul' := fun a f ↦ by
          simp only [map_smul, RingHom.id_apply]
          exact fderiv_const_smul (h.1 f) a } h.2
  else 0

private theorem derivFamily_apply {Φ : E → Λ →L[𝕜] F} {y : E}
    (hd : ∀ f, DifferentiableAt 𝕜 (fun z ↦ Φ z f) y)
    (hb : ∃ C, ∀ f, ‖fderiv 𝕜 (fun z ↦ Φ z f) y‖ ≤ C * ‖f‖) (f : Λ) :
    derivFamily Φ y f = fderiv 𝕜 (fun z ↦ Φ z f) y := by
  unfold derivFamily
  split_ifs with h
  · exact LinearMap.mkContinuousOfExistsBound_apply _ h.2 f
  · exact absurd ⟨hd, hb⟩ h

/-- The hypotheses of the main theorems at order `k`: every `y ↦ Φ y f` is `C^k` on `U`, and its
derivatives of order at most `k` are bounded by `C * ‖f‖` near each point of `U`. -/
private def PointwiseContDiffOn (k : ℕ) (U : Set E) (Φ : E → Λ →L[𝕜] F) : Prop :=
  (∀ f, ContDiffOn 𝕜 k (fun y ↦ Φ y f) U) ∧
    ∀ m ≤ k, ∀ y ∈ U, ∃ C, ∀ᶠ z in 𝓝 y, ∀ f,
      ‖iteratedFDeriv 𝕜 m (fun y ↦ Φ y f) z‖ ≤ C * ‖f‖

private theorem PointwiseContDiffOn.mono {k l : ℕ} {U : Set E} {Φ : E → Λ →L[𝕜] F}
    (h : PointwiseContDiffOn k U Φ) (hlk : l ≤ k) : PointwiseContDiffOn l U Φ :=
  ⟨fun f ↦ (h.1 f).of_le (by exact_mod_cast hlk), fun m hm ↦ h.2 m (hm.trans hlk)⟩

/-- At a point of `U`, each `y ↦ Φ y f` has the derivative family as its derivative. -/
private theorem PointwiseContDiffOn.hasFDerivAt {k : ℕ} {U : Set E} {Φ : E → Λ →L[𝕜] F}
    (h : PointwiseContDiffOn (k + 1) U Φ) (hU : IsOpen U) {y : E} (hy : y ∈ U) (f : Λ) :
    HasFDerivAt (fun z ↦ Φ z f) (derivFamily Φ y f) y := by
  have hd : ∀ f, DifferentiableAt 𝕜 (fun z ↦ Φ z f) y := fun f ↦
    ((h.1 f).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
  obtain ⟨C, hC⟩ := h.2 1 (Nat.le_add_left 1 k) y hy
  refine derivFamily_apply hd ⟨C, fun g ↦ ?_⟩ f ▸ (hd f).hasFDerivAt
  exact norm_iteratedFDeriv_one (𝕜 := 𝕜) (fun z ↦ Φ z g) ▸ hC.self_of_nhds g

/-- The derivative family of a family satisfying the hypotheses at order `k + 1` satisfies them
at order `k`. -/
private theorem PointwiseContDiffOn.deriv {k : ℕ} {U : Set E} {Φ : E → Λ →L[𝕜] F}
    (h : PointwiseContDiffOn (k + 1) U Φ) (hU : IsOpen U) :
    PointwiseContDiffOn k U (derivFamily Φ) := by
  refine ⟨fun f ↦ ((h.1 f).fderiv_of_isOpen hU (by norm_cast)).congr fun y hy ↦
    (h.hasFDerivAt hU hy f).fderiv.symm, fun m hm y hy ↦ ?_⟩
  obtain ⟨C, hC⟩ := h.2 (m + 1) (by omega) y hy
  refine ⟨C, ?_⟩
  filter_upwards [hC, hU.mem_nhds hy] with z hz hzU f
  have heq : (fun w ↦ derivFamily Φ w f) =ᶠ[𝓝 z] fderiv 𝕜 (fun w ↦ Φ w f) :=
    eventually_of_mem (hU.mem_nhds hzU) fun w hw ↦ (h.hasFDerivAt hU hw f).fderiv.symm
  rw [(heq.iteratedFDeriv (𝕜 := 𝕜) m).self_of_nhds, norm_iteratedFDeriv_fderiv]
  exact hz f

/-- Order zero of `contDiffOn_apply_of_forall_norm_iteratedFDeriv_le`: the map `(f, y) ↦ Φ y f`
is continuous. -/
private theorem PointwiseContDiffOn.continuousOn_apply {U : Set E} {Φ : E → Λ →L[𝕜] F}
    (h : PointwiseContDiffOn 0 U Φ) (hU : IsOpen U) :
    ContinuousOn (fun p : Λ × E ↦ Φ p.2 p.1) (univ ×ˢ U) := by
  rintro ⟨f₀, y₀⟩ ⟨-, hy₀⟩
  refine ContinuousAt.continuousWithinAt ?_
  -- Split `Φ y f - Φ y₀ f₀` as `Φ y (f - f₀) + (Φ y f₀ - Φ y₀ f₀)`.
  obtain ⟨C, hC⟩ := h.2 0 le_rfl y₀ hy₀
  have hcont : ContinuousAt (fun y ↦ Φ y f₀) y₀ :=
    ((h.1 f₀).continuousOn.continuousAt (hU.mem_nhds hy₀))
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (g := fun p : Λ × E ↦ C * ‖p.1 - f₀‖ + ‖Φ p.2 f₀ - Φ y₀ f₀‖) ?_ ?_
  · filter_upwards [continuousAt_snd.preimage_mem_nhds hC] with p hp
    have hp' := hp (p.1 - f₀)
    rw [norm_iteratedFDeriv_zero] at hp'
    calc ‖Φ p.2 p.1 - Φ y₀ f₀‖ = ‖Φ p.2 (p.1 - f₀) + (Φ p.2 f₀ - Φ y₀ f₀)‖ := by
          rw [map_sub]; abel_nf
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add_left hp' _)
  · have h₁ : Tendsto (fun p : Λ × E ↦ C * ‖p.1 - f₀‖) (𝓝 (f₀, y₀)) (𝓝 0) := by
      simpa using ((tendsto_norm_sub_self f₀).comp (continuousAt_fst (p := (f₀, y₀)))).const_mul C
    have h₂ : Tendsto (fun p : Λ × E ↦ ‖Φ p.2 f₀ - Φ y₀ f₀‖) (𝓝 (f₀, y₀)) (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.1 hcont).comp continuousAt_snd
    simpa using h₁.add h₂

variable [IsRCLikeNormedField 𝕜]

/-- Order zero of `contDiffOn_of_forall_norm_iteratedFDeriv_le`: the family is continuous for the
operator norm. -/
private theorem PointwiseContDiffOn.continuousOn {U : Set E} {Φ : E → Λ →L[𝕜] F}
    (h : PointwiseContDiffOn 1 U Φ) (hU : IsOpen U) : ContinuousOn Φ U := by
  intro y hy
  refine (ContinuousAt.continuousWithinAt ?_)
  -- Near `y`, the derivative family is bounded, so `Φ` is Lipschitz for the operator norm.
  obtain ⟨C, hC⟩ := h.2 1 le_rfl y hy
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hC.and (hU.eventually_mem hy))
  have hD : ∀ w ∈ Metric.ball y r, ‖derivFamily Φ w‖ ≤ max C 0 := fun w hw ↦
    ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun f ↦ by
      rw [(h.hasFDerivAt (k := 0) hU (hball w hw).2 f).fderiv.symm,
        ← norm_iteratedFDeriv_one]
      exact ((hball w hw).1 f).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (norm_nonneg f))
  have hlip : ∀ z ∈ Metric.ball y r, ‖Φ z - Φ y‖ ≤ max C 0 * ‖z - y‖ := fun z hz ↦ by
    let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
    let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
    simpa using (convex_ball y r).norm_sub_sub_flip_le_of_norm_hasFDerivWithin_sub_le (L := 0)
      (fun w hw f ↦ (h.hasFDerivAt (k := 0) hU (hball w hw).2 f).hasFDerivWithinAt)
      (by simpa using hD) (Metric.mem_ball_self hr) hz
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (eventually_of_mem (Metric.ball_mem_nhds y hr) hlip) ?_
  simpa using (tendsto_norm_sub_self y).const_mul (max C 0)

/-! The two inductions replace the target `G` by `E →L[𝕜] G`, so they are stated for a target in
a universe that absorbs that of `E`. The main theorems lift an arbitrary target with `ULift`. -/

private theorem PointwiseContDiffOn.contDiffOn {k : ℕ} {U : Set E}
    {G : Type (max u w)} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {Φ : E → Λ →L[𝕜] G}
    (h : PointwiseContDiffOn (k + 1) U Φ) (hU : IsOpen U) : ContDiffOn 𝕜 k Φ U := by
  induction k generalizing G Φ with
  | zero => exact contDiffOn_zero.2 (h.continuousOn hU)
  | succ k ih =>
    -- The derivative of `Φ` is the derivative family, with its two arguments exchanged.
    have hΨ := h.deriv hU
    have hΨc := (hΨ.mono (Nat.le_add_left 1 k)).continuousOn hU
    have hderiv : ∀ y ∈ U, HasFDerivAt Φ (derivFamily Φ y).flip y := by
      intro y hy
      rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
      intro ε hε
      -- Near `y`, the derivative family stays within `ε` of its value at `y`.
      have hnear : ∀ᶠ w in 𝓝 y, w ∈ U ∧ ‖derivFamily Φ w - derivFamily Φ y‖ ≤ ε :=
        (hU.eventually_mem hy).and ((tendsto_iff_norm_sub_tendsto_zero.1
          ((hΨc y hy).continuousAt (hU.mem_nhds hy))).eventually (ge_mem_nhds hε))
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnear
      filter_upwards [Metric.ball_mem_nhds y hr] with z hz
      let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
      let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
      exact (convex_ball y r).norm_sub_sub_flip_le_of_norm_hasFDerivWithin_sub_le
        (fun w hw f ↦ (h.hasFDerivAt hU (hball w hw).1 f).hasFDerivWithinAt)
        (fun w hw ↦ (hball w hw).2) (Metric.mem_ball_self hr) hz
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun y hy ↦ (hderiv y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine ((ContinuousLinearMap.flipₗᵢ 𝕜 Λ E G).contDiff.comp_contDiffOn (ih hΨ)).congr
      fun y hy ↦ ?_
    rw [(hderiv y hy).fderiv, Function.comp_apply, ContinuousLinearMap.coe_flipₗᵢ]

private theorem PointwiseContDiffOn.contDiffOn_apply {k : ℕ} {U : Set E}
    {G : Type (max u w)} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {Φ : E → Λ →L[𝕜] G}
    (h : PointwiseContDiffOn k U Φ) (hU : IsOpen U) :
    ContDiffOn 𝕜 k (fun p : Λ × E ↦ Φ p.2 p.1) (univ ×ˢ U) := by
  induction k generalizing G Φ with
  | zero => exact contDiffOn_zero.2 (h.continuousOn_apply hU)
  | succ k ih =>
    have hUp : IsOpen (univ ×ˢ U : Set (Λ × E)) := isOpen_univ.prod hU
    have hΦc : ContDiffOn 𝕜 k Φ U := h.contDiffOn hU
    have hΨ : ContDiffOn 𝕜 k (fun p : Λ × E ↦ derivFamily Φ p.2 p.1) (univ ×ˢ U) :=
      ih (h.deriv hU)
    -- The partial derivatives are `Φ y` in `f` and the derivative family in `y`, both continuous.
    have hstrict : ∀ p ∈ (univ ×ˢ U : Set (Λ × E)), HasStrictFDerivAt
        (fun p : Λ × E ↦ Φ p.2 p.1) ((Φ p.2).coprod (derivFamily Φ p.2 p.1)) p := by
      intro p hp
      exact hasStrictFDerivAt_uncurry_coprod (f := fun f y ↦ Φ y f) (f₁ := fun _ y ↦ Φ y)
        (f₂ := fun f y ↦ derivFamily Φ y f) (Eventually.of_forall fun v ↦ (Φ v.2).hasFDerivAt)
        (eventually_of_mem (hUp.mem_nhds hp) fun v hv ↦ h.hasFDerivAt hU hv.2 v.1)
        ((hΦc.continuousOn.continuousAt (hU.mem_nhds hp.2)).comp continuousAt_snd)
        (hΨ.continuousOn.continuousAt (hUp.mem_nhds hp))
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hUp]
    refine ⟨fun p hp ↦ (hstrict p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine ((ContinuousLinearMap.coprodEquivL (S := 𝕜)).contDiff.comp_contDiffOn
      ((hΦc.comp (contDiffOn_snd (s := univ ×ˢ U)) fun p hp ↦ hp.2).prodMk hΨ)).congr fun p hp ↦ ?_
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp [(hstrict p hp).hasFDerivAt.fderiv]

/-- **Operator-norm regularity of a pointwise smooth family.** Let `Φ y : Λ →L[𝕜] F` be a family
of continuous linear maps on an open set `U`. If every `y ↦ Φ y f` is `C^(k + 1)` on `U`, and near
each point of `U` its derivatives of order at most `k + 1` are bounded by `C * ‖f‖` for a constant
`C` independent of `f`, then `Φ` is `C^k` on `U` for the operator norm. -/
theorem contDiffOn_of_forall_norm_iteratedFDeriv_le {Φ : E → Λ →L[𝕜] F} {U : Set E}
    (hU : IsOpen U) {k : ℕ} (hΦ : ∀ f, ContDiffOn 𝕜 (k + 1) (fun y ↦ Φ y f) U)
    (hbd : ∀ m ≤ k + 1, ∀ y ∈ U, ∃ C, ∀ᶠ z in 𝓝 y, ∀ f,
      ‖iteratedFDeriv 𝕜 m (fun y ↦ Φ y f) z‖ ≤ C * ‖f‖) :
    ContDiffOn 𝕜 k Φ U := by
  -- Lift the target to a universe absorbing that of `E`.
  let e := (LinearIsometryEquiv.ulift 𝕜 F).symm
  have h : PointwiseContDiffOn (k + 1) U fun y ↦ (e : F →L[𝕜] ULift.{u} F).comp (Φ y) :=
    ⟨fun f ↦ e.toContinuousLinearEquiv.comp_contDiffOn_iff.2 (by exact_mod_cast hΦ f),
      fun m hm y hy ↦ (hbd m hm y hy).imp fun C hC ↦ hC.mono fun z hz f ↦
        (e.norm_iteratedFDeriv_comp_left (fun y ↦ Φ y f) z m).trans_le (hz f)⟩
  refine ((ContinuousLinearMap.compL 𝕜 Λ _ F (e.symm : ULift.{u} F →L[𝕜] F)).contDiff
    |>.comp_contDiffOn (h.contDiffOn hU)).congr fun y _ ↦ ?_
  ext f
  simp

/-- **Joint regularity of a pointwise smooth family of operators.** Let `Φ y : Λ →L[𝕜] F` be a
family of continuous linear maps on an open set `U`. If every `y ↦ Φ y f` is `C^k` on `U`, and near
each point of `U` its derivatives of order at most `k` are bounded by `C * ‖f‖` for a constant `C`
independent of `f`, then `(f, y) ↦ Φ y f` is `C^k` on `Λ × U`.

For the evaluation map of a space of `C^k` functions, `Φ y f = f y`, this says that evaluation is
jointly `C^k`, although `y ↦ Φ y` is in general only `C^(k - 1)` for the operator norm. -/
theorem contDiffOn_apply_of_forall_norm_iteratedFDeriv_le {Φ : E → Λ →L[𝕜] F} {U : Set E}
    (hU : IsOpen U) {k : ℕ} (hΦ : ∀ f, ContDiffOn 𝕜 k (fun y ↦ Φ y f) U)
    (hbd : ∀ m ≤ k, ∀ y ∈ U, ∃ C, ∀ᶠ z in 𝓝 y, ∀ f,
      ‖iteratedFDeriv 𝕜 m (fun y ↦ Φ y f) z‖ ≤ C * ‖f‖) :
    ContDiffOn 𝕜 k (fun p : Λ × E ↦ Φ p.2 p.1) (univ ×ˢ U) := by
  -- Lift the target to a universe absorbing that of `E`.
  let e := (LinearIsometryEquiv.ulift 𝕜 F).symm
  have h : PointwiseContDiffOn k U fun y ↦ (e : F →L[𝕜] ULift.{u} F).comp (Φ y) :=
    ⟨fun f ↦ e.toContinuousLinearEquiv.comp_contDiffOn_iff.2 (hΦ f),
      fun m hm y hy ↦ (hbd m hm y hy).imp fun C hC ↦ hC.mono fun z hz f ↦
        (e.norm_iteratedFDeriv_comp_left (fun y ↦ Φ y f) z m).trans_le (hz f)⟩
  exact e.toContinuousLinearEquiv.comp_contDiffOn_iff.1 (h.contDiffOn_apply hU)

end TauCeti
