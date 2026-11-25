/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.Boundary.SmoothMap
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The polar collar of the closed unit ball

The closed unit ball of a real inner product space `E` of dimension `n + 1` is a manifold with
boundary whose boundary is the unit sphere (`TauCeti.boundary_closedBall`). This file builds its
*polar collar* `TauCeti.SmoothCollar.closedBall`, the smooth collar

`(x, t) ↦ (1 - t) x`, for `x` in the boundary sphere and `t ∈ [0, 1)`.

Its image is the punctured closed ball `0 < ‖z‖ ≤ 1`, open in the ball
(`TauCeti.SmoothCollar.range_closedBall`), and its inverse there is `z ↦ (z / ‖z‖, 1 - ‖z‖)`.
For the closed unit disc of `ℂ` this is the polar collar `(θ, t) ↦ (1 - t) e^{iθ}`
(`TauCeti.SmoothCollar.closedBall_complex_polar`).
-/

public section

noncomputable section

open Set Function Metric Topology Module
open scoped Manifold ContDiff

namespace TauCeti

open _root_.TauCeti.EuclideanHalfSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n + 1)]

local notation "B" => ModelWithCorners.boundary (I := 𝓡∂ (n + 1)) (closedBall (0 : E) 1)
local notation "D" => normalIioOpens 1

/-- The normal coordinate `t ∈ [0, 1)` of a point of `normalIioOpens 1`. -/
private theorem normal_mem_Ico (t : D) : (t : EuclideanHalfSpace 1).val 0 ∈ Ico (0 : ℝ) 1 :=
  ⟨(t : EuclideanHalfSpace 1).property, mem_normalIioOpens.1 t.property⟩

/-- A boundary point of the closed unit ball has norm one. -/
private theorem norm_boundary (x : B) : ‖((x : closedBall (0 : E) 1) : E)‖ = 1 :=
  isBoundaryPoint_closedBall_iff.1 x.property

private theorem polar_mem_closedBall (x : B) (t : D) :
    (1 - (t : EuclideanHalfSpace 1).val 0) • ((x : closedBall (0 : E) 1) : E) ∈
      closedBall (0 : E) 1 := by
  obtain ⟨h0, h1⟩ := normal_mem_Ico t
  rw [mem_closedBall_zero_iff, norm_smul, norm_boundary, mul_one, Real.norm_eq_abs,
    abs_of_pos (by linarith)]
  linarith

/-- The underlying map of the polar collar of the closed unit ball: `(x, t) ↦ (1 - t) x`. -/
def closedBallCollarFun (p : B × D) : closedBall (0 : E) 1 :=
  ⟨(1 - (p.2 : EuclideanHalfSpace 1).val 0) • ((p.1 : closedBall (0 : E) 1) : E),
    polar_mem_closedBall p.1 p.2⟩

/-- The polar collar reads as `(1 - t) x` in `E`. -/
@[simp]
theorem coe_closedBallCollarFun (p : B × D) :
    (closedBallCollarFun p : E) =
      (1 - (p.2 : EuclideanHalfSpace 1).val 0) • ((p.1 : closedBall (0 : E) 1) : E) :=
  (rfl)

/-- The polar collar has norm `1 - t`. -/
private theorem norm_closedBallCollarFun (p : B × D) :
    ‖(closedBallCollarFun p : E)‖ = 1 - (p.2 : EuclideanHalfSpace 1).val 0 := by
  obtain ⟨-, h1⟩ := normal_mem_Ico p.2
  rw [coe_closedBallCollarFun, norm_smul, norm_boundary, mul_one, Real.norm_eq_abs,
    abs_of_pos (by linarith)]

/-- The polar collar misses the centre of the ball. -/
private theorem closedBallCollarFun_ne_zero (p : B × D) : (closedBallCollarFun p : E) ≠ 0 := by
  have h := norm_closedBallCollarFun p
  obtain ⟨-, h1⟩ := normal_mem_Ico p.2
  intro h0
  rw [h0, norm_zero] at h
  linarith

/-- The polar collar is analytic. -/
theorem contMDiff_closedBallCollarFun {k : ℕ∞ω} :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (closedBallCollarFun (n := n) (E := E)) := by
  have hx : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) k
      (fun x : B ↦ ((x : closedBall (0 : E) 1) : E)) :=
    (contMDiff_subtypeVal_closedBall (n := n + 1)).comp
      (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k) (closedBall (0 : E) 1)).contMDiff
  have ht : ContMDiff (𝓡∂ 1) 𝓘(ℝ) k (fun t : D ↦ (t : EuclideanHalfSpace 1).val 0) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
      (𝓡∂ 1).contMDiff).comp (contMDiff_subtypeVal (U := D))
  have hxp : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod (𝓡∂ 1)) 𝓘(ℝ, E) k
      (fun p : B × D ↦ ((p.1 : closedBall (0 : E) 1) : E)) := hx.comp contMDiff_fst
  have htp : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod (𝓡∂ 1)) 𝓘(ℝ) k
      (fun p : B × D ↦ (p.2 : EuclideanHalfSpace 1).val 0) := ht.comp contMDiff_snd
  exact contMDiff_iff_comp_subtypeVal_closedBall.2 ((contMDiff_const.sub htp).smul hxp)

/-! ### The inverse on the punctured ball -/

/-- The boundary sphere of the closed unit ball is nonempty. -/
private theorem nonempty_boundary : Nonempty B := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [Fact.out (p := finrank ℝ E = n + 1)]
    exact Nat.succ_pos n)
  obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
  exact ⟨⟨⟨x, mem_closedBall_zero_iff.2 hx.le⟩, isBoundaryPoint_closedBall_iff.2 hx⟩⟩

/-- The unit vector `z / ‖z‖` of a nonzero point of the closed ball, a boundary point. -/
private theorem normalize_mem_boundary {z : closedBall (0 : E) 1} (hz : (z : E) ≠ 0) :
    (⟨‖(z : E)‖⁻¹ • (z : E), by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]⟩ : closedBall (0 : E) 1) ∈ B :=
  isBoundaryPoint_closedBall_iff.2 (by
    simp only [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)])

open Classical in
/-- The angular part `z / ‖z‖` of a point of the punctured closed ball, a boundary point. -/
private def unitPoint (z : closedBall (0 : E) 1) : B :=
  if hz : (z : E) = 0 then (nonempty_boundary (n := n) (E := E)).some
  else ⟨_, normalize_mem_boundary hz⟩

private theorem coe_unitPoint {z : closedBall (0 : E) 1} (hz : (z : E) ≠ 0) :
    ((unitPoint (n := n) z : closedBall (0 : E) 1) : E) = ‖(z : E)‖⁻¹ • (z : E) := by
  simp [unitPoint, hz]

/-- The radial coordinate `1 - ‖z‖` of a point `z` of the closed ball, as a vector of the ambient
space of the half-line model. -/
private def radialVec (z : closedBall (0 : E) 1) : EuclideanSpace ℝ (Fin 1) :=
  (1 - ‖(z : E)‖) • EuclideanSpace.single 0 1

omit [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)] in
private theorem radialVec_apply_zero (z : closedBall (0 : E) 1) :
    radialVec z 0 = 1 - ‖(z : E)‖ := by
  simp [radialVec]

omit [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)] in
private theorem radialVec_mem_range (z : closedBall (0 : E) 1) : radialVec z ∈ range (𝓡∂ 1) := by
  rw [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq, radialVec_apply_zero, sub_nonneg]
  exact mem_closedBall_zero_iff.1 z.property

/-- The point of the half-line model with normal coordinate `1 - ‖z‖`. -/
private def radialPoint (z : closedBall (0 : E) 1) : EuclideanHalfSpace 1 :=
  (𝓡∂ 1).symm (radialVec z)

omit [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)] in
private theorem radialPoint_apply_zero (z : closedBall (0 : E) 1) :
    (radialPoint z).val 0 = 1 - ‖(z : E)‖ := by
  have h := radialVec_mem_range z
  rw [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] at h
  rw [radialPoint, modelWithCornersEuclideanHalfSpace_symm_apply_of_le h, radialVec_apply_zero]

omit [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)] in
private theorem radialPoint_mem {z : closedBall (0 : E) 1} (hz : (z : E) ≠ 0) :
    radialPoint z ∈ D := by
  rw [mem_normalIioOpens, radialPoint_apply_zero]
  linarith [norm_pos_iff.2 hz]

open Classical in
/-- The inverse of the polar collar on the punctured closed ball: `z ↦ (z / ‖z‖, 1 - ‖z‖)`. -/
private def closedBallCollarInv (z : closedBall (0 : E) 1) : B × D :=
  (unitPoint z, if hz : (z : E) = 0 then normalIioOpensZero one_pos
    else ⟨radialPoint z, radialPoint_mem hz⟩)

/-- A map into `normalIioOpens 1` is `C^k` at a point when its composition with the inclusion
is. -/
private theorem contMDiffAt_of_subtypeVal_comp {k : ℕ∞ω} {f : closedBall (0 : E) 1 → D}
    {z : closedBall (0 : E) 1} (h : ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ 1) k (Subtype.val ∘ f) z) :
    ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ 1) k f z :=
  (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).1 h

private theorem contMDiffAt_closedBallCollarInv {k : ℕ∞ω} {z : closedBall (0 : E) 1}
    (hz : (z : E) ≠ 0) :
    ContMDiffAt (𝓡∂ (n + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod (𝓡∂ 1)) k
      (closedBallCollarInv (n := n) (E := E)) z := by
  have hU : {w : closedBall (0 : E) 1 | (w : E) ≠ 0} ∈ 𝓝 z :=
    (isOpen_ne_fun continuous_subtypeVal continuous_const).mem_nhds hz
  have hval : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, E) k (Subtype.val : closedBall (0 : E) 1 → E) z :=
    contMDiff_subtypeVal_closedBall z
  refine ContMDiffAt.prodMk ?_ (contMDiffAt_of_subtypeVal_comp ?_)
  · rw [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_comp_subtypeVal_boundary,
      contMDiffWithinAt_univ, contMDiffAt_iff_comp_subtypeVal_closedBall]
    have hn : ContDiffAt ℝ k (fun w : E ↦ ‖w‖⁻¹ • w) (z : E) :=
      ((contDiffAt_norm ℝ hz).inv (norm_ne_zero_iff.2 hz)).smul contDiffAt_id
    refine (hn.contMDiffAt.comp z hval).congr_of_eventuallyEq ?_
    filter_upwards [hU] with w hw
    exact coe_unitPoint hw
  · have hr : ContMDiffAt (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) k radialVec z := by
      have hc : ContDiffAt ℝ k (fun w : E ↦ (1 - ‖w‖) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
          (z : E) :=
        (contDiffAt_const.sub (contDiffAt_norm ℝ hz)).smul contDiffAt_const
      exact hc.contMDiffAt.comp z hval
    have hp : ContMDiffAt (𝓡∂ (n + 1)) (𝓡∂ 1) k radialPoint z := by
      rw [← contMDiffWithinAt_univ] at hr ⊢
      exact ((𝓡∂ 1).contMDiffOn_symm _ (radialVec_mem_range z)).comp z hr
        fun w _ ↦ radialVec_mem_range w
    refine hp.congr_of_eventuallyEq ?_
    filter_upwards [hU] with w hw
    simp [hw]

/-- The polar collar as a partial diffeomorphism onto the punctured closed ball. -/
private def closedBallCollarPartialDiffeomorph (k : ℕ∞ω) :
    PartialDiffeomorph (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) (B × D)
      (closedBall (0 : E) 1) k where
  toFun := closedBallCollarFun
  invFun := closedBallCollarInv
  source := univ
  target := {z | (z : E) ≠ 0}
  map_source' p _ := closedBallCollarFun_ne_zero p
  map_target' _ _ := mem_univ _
  left_inv' p _ := by
    have hz := closedBallCollarFun_ne_zero p
    have hnorm := norm_closedBallCollarFun p
    obtain ⟨-, h1⟩ := normal_mem_Ico p.2
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext (Subtype.ext ?_))
    · rw [closedBallCollarInv, coe_unitPoint hz, hnorm, coe_closedBallCollarFun, smul_smul,
        inv_mul_cancel₀ (by linarith), one_smul]
    · simp only [closedBallCollarInv, hz, ↓reduceDIte]
      ext i
      rw [Subsingleton.elim i 0, radialPoint_apply_zero, hnorm, sub_sub_cancel]
  right_inv' z hz := by
    have hz' : (z : E) ≠ 0 := hz
    apply Subtype.ext
    simp only [closedBallCollarInv, hz', ↓reduceDIte, coe_closedBallCollarFun,
      radialPoint_apply_zero, coe_unitPoint hz', sub_sub_cancel, smul_smul]
    rw [mul_inv_cancel₀ (norm_ne_zero_iff.2 hz'), one_smul]
  open_source := isOpen_univ
  open_target := isOpen_ne_fun continuous_subtypeVal continuous_const
  contMDiffOn_toFun := contMDiff_closedBallCollarFun.contMDiffOn
  contMDiffOn_invFun z hz := (contMDiffAt_closedBallCollarInv hz).contMDiffWithinAt

/-! ### The polar collar -/

/-- The polar collar is a local diffeomorphism. -/
theorem isLocalDiffeomorph_closedBallCollarFun {k : ℕ∞ω} :
    IsLocalDiffeomorph (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (closedBallCollarFun (n := n) (E := E)) := fun p ↦
  isLocalDiffeomorphAt_of_eqOn (Φ := closedBallCollarPartialDiffeomorph k) (mem_univ p)
    fun _ _ ↦ rfl

/-- The polar collar is injective. -/
theorem injective_closedBallCollarFun : Injective (closedBallCollarFun (n := n) (E := E)) :=
  fun p q h ↦ by
    rw [← (closedBallCollarPartialDiffeomorph (n := n) (E := E) ⊤).left_inv (mem_univ p),
      ← (closedBallCollarPartialDiffeomorph (n := n) (E := E) ⊤).left_inv (mem_univ q)]
    exact congrArg _ h

/-- The polar collar sends the zero slice to the boundary sphere. -/
theorem closedBallCollarFun_zero (x : B) :
    closedBallCollarFun (x, normalIioOpensZero one_pos) = x := by
  apply Subtype.ext
  simp

variable (n E) in
/-- The **polar collar** of the closed unit ball: the smooth collar `(x, t) ↦ (1 - t) x`, for `x`
in the boundary sphere and `t ∈ [0, 1)`. -/
def SmoothCollar.closedBall (k : ℕ∞ω) : SmoothCollar n k (Metric.closedBall (0 : E) 1) where
  toFun := closedBallCollarFun
  isLocalDiffeomorph' := isLocalDiffeomorph_closedBallCollarFun
  injective' := injective_closedBallCollarFun
  apply_zero' := closedBallCollarFun_zero

/-- The polar collar of the closed unit ball is `(x, t) ↦ (1 - t) x`. -/
@[simp]
theorem SmoothCollar.coe_closedBall_apply {k : ℕ∞ω} (p : B × D) :
    (SmoothCollar.closedBall n E k p : E) =
      (1 - (p.2 : EuclideanHalfSpace 1).val 0) • ((p.1 : Metric.closedBall (0 : E) 1) : E) :=
  (rfl)

/-- The image of the polar collar of the closed unit ball is the punctured closed ball
`0 < ‖z‖ ≤ 1`, an open subset of the ball. -/
theorem SmoothCollar.range_closedBall {k : ℕ∞ω} :
    range (SmoothCollar.closedBall n E k) = {z : Metric.closedBall (0 : E) 1 | (z : E) ≠ 0} := by
  ext z
  refine ⟨?_, fun hz ↦ ⟨closedBallCollarInv z,
    (closedBallCollarPartialDiffeomorph (n := n) (E := E) k).right_inv hz⟩⟩
  rintro ⟨p, rfl⟩
  exact closedBallCollarFun_ne_zero p

/-! ### The closed unit disc -/

section Disc

/-- The real dimension of `ℂ`, written as the successor `1 + 1` used by the boundary
constructions. -/
local instance instFactFinrankComplexOneAddOne : Fact (finrank ℝ ℂ = 1 + 1) :=
  ⟨Complex.finrank_real_complex⟩

/-- **The polar collar of the closed unit disc** is `(θ, t) ↦ (1 - t) e^{iθ}`: for every angle
`θ` and depth `t ∈ [0, 1)`, the boundary point `e^{iθ}` at depth `t` is sent to
`(1 - t) e^{iθ}`. -/
theorem SmoothCollar.closedBall_complex_polar {k : ℕ∞ω} (θ : ℝ) (t : D) :
    ∃ x : ModelWithCorners.boundary (I := 𝓡∂ (1 + 1)) (Metric.closedBall (0 : ℂ) 1),
      ((x : Metric.closedBall (0 : ℂ) 1) : ℂ) = Complex.exp (θ * Complex.I) ∧
      (SmoothCollar.closedBall 1 ℂ k (x, t) : ℂ) =
        (1 - (t : EuclideanHalfSpace 1).val 0) * Complex.exp (θ * Complex.I) := by
  have hn : ‖Complex.exp (θ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  refine ⟨⟨⟨Complex.exp (θ * Complex.I), mem_closedBall_zero_iff.2 hn.le⟩,
    isBoundaryPoint_closedBall_iff.2 hn⟩, rfl, ?_⟩
  rw [SmoothCollar.coe_closedBall_apply, Complex.real_smul]
  push_cast
  rfl

end Disc

end TauCeti
