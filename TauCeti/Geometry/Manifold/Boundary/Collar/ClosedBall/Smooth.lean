/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Boundary
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Collar
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The polar collar of the closed unit ball

The closed unit ball of a real inner product space `E` of dimension `n + 1` is a manifold with
boundary whose boundary is the unit sphere (`TauCeti.boundary_closedBall`). This file builds its
*polar collar* `TauCeti.SmoothCollar.closedBall`, the smooth collar

`(x, t) ↦ (1 - t) x`, for `x` in the boundary sphere and `t ∈ [0, 1)`.

Its image is the punctured closed ball `0 < ‖z‖ ≤ 1`, open in the ball
(`TauCeti.SmoothCollar.range_closedBall`, `TauCeti.SmoothCollar.opensRange_closedBall`), and its
inverse there is `z ↦ (z / ‖z‖, 1 - ‖z‖)`
(`TauCeti.SmoothCollar.coe_diffeomorphOpensRange_closedBall_symm_apply_fst`,
`TauCeti.SmoothCollar.diffeomorphOpensRange_closedBall_symm_apply_snd_coe_apply`).
For the closed unit disc of `ℂ` this is the polar collar `(θ, t) ↦ (1 - t) e^{iθ}`
(`TauCeti.SmoothCollar.exists_closedBall_complex_apply_eq_mul_exp`).
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

/-- The radial factor `1 - t` of a point of `normalIioOpens 1` is positive. -/
private theorem one_sub_normal_pos (t : D) : 0 < 1 - (t : EuclideanHalfSpace 1).val 0 :=
  sub_pos.2 (normal_mem_Ico t).2

/-- A boundary point of the closed unit ball has norm one. -/
private theorem norm_boundary (x : B) : ‖((x : closedBall (0 : E) 1) : E)‖ = 1 :=
  isBoundaryPoint_closedBall_iff.1 x.property

/-- The point `(1 - t) x` has norm `1 - t`. -/
private theorem norm_sub_smul_boundary (x : B) (t : D) :
    ‖(1 - (t : EuclideanHalfSpace 1).val 0) • ((x : closedBall (0 : E) 1) : E)‖ =
      1 - (t : EuclideanHalfSpace 1).val 0 := by
  rw [norm_smul, norm_boundary, mul_one, Real.norm_eq_abs, abs_of_pos (one_sub_normal_pos t)]

private theorem polar_mem_closedBall (x : B) (t : D) :
    (1 - (t : EuclideanHalfSpace 1).val 0) • ((x : closedBall (0 : E) 1) : E) ∈
      closedBall (0 : E) 1 := by
  rw [mem_closedBall_zero_iff, norm_sub_smul_boundary]
  linarith [(normal_mem_Ico t).1]

/-- The underlying map of the polar collar of the closed unit ball: `(x, t) ↦ (1 - t) x`. -/
private def closedBallCollarFun (p : B × D) : closedBall (0 : E) 1 :=
  ⟨(1 - (p.2 : EuclideanHalfSpace 1).val 0) • ((p.1 : closedBall (0 : E) 1) : E),
    polar_mem_closedBall p.1 p.2⟩

/-- The polar collar reads as `(1 - t) x` in `E`. -/
private theorem coe_closedBallCollarFun (p : B × D) :
    (closedBallCollarFun p : E) =
      (1 - (p.2 : EuclideanHalfSpace 1).val 0) • ((p.1 : closedBall (0 : E) 1) : E) :=
  (rfl)

/-- The polar collar has norm `1 - t`. -/
private theorem norm_closedBallCollarFun (p : B × D) :
    ‖(closedBallCollarFun p : E)‖ = 1 - (p.2 : EuclideanHalfSpace 1).val 0 :=
  norm_sub_smul_boundary p.1 p.2

/-- The polar collar misses the centre of the ball. -/
private theorem closedBallCollarFun_ne_zero (p : B × D) : (closedBallCollarFun p : E) ≠ 0 :=
  norm_ne_zero_iff.1 ((norm_closedBallCollarFun p).trans_ne (one_sub_normal_pos p.2).ne')

/-- Normalising the polar collar recovers its boundary point. -/
private theorem inv_norm_smul_closedBallCollarFun (p : B × D) :
    ‖(closedBallCollarFun p : E)‖⁻¹ • (closedBallCollarFun p : E) =
      ((p.1 : closedBall (0 : E) 1) : E) := by
  rw [norm_closedBallCollarFun, coe_closedBallCollarFun,
    inv_smul_smul₀ (one_sub_normal_pos p.2).ne']

/-- The polar collar is analytic. -/
private theorem contMDiff_closedBallCollarFun {k : ℕ∞ω} :
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

omit [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)] in
/-- The radial coordinate `1 - ‖z‖` of a nonzero point of the closed ball lies in `[0, 1)`. -/
private theorem normalRay_mem {z : closedBall (0 : E) 1} (hz : (z : E) ≠ 0) :
    normalRay (1 - ‖(z : E)‖) ∈ D := by
  rw [mem_normalIioOpens, normalRay_coe_apply]
  exact max_lt (by linarith [norm_pos_iff.2 hz]) one_pos

open Classical in
/-- The inverse of the polar collar on the punctured closed ball: `z ↦ (z / ‖z‖, 1 - ‖z‖)`. -/
private def closedBallCollarInv (z : closedBall (0 : E) 1) : B × D :=
  if hz : (z : E) = 0 then (Classical.arbitrary B, normalIioOpensZero one_pos)
  else (sphereDiffeomorphBoundaryClosedBall (ballCollarInv z hz).1, ⟨_, normalRay_mem hz⟩)

/-- Off the centre, the inverse is the sphere point of `TauCeti.ballCollarInv` and the normal
ray at `1 - ‖z‖`. -/
private theorem closedBallCollarInv_of_ne_zero {z : closedBall (0 : E) 1} (hz : (z : E) ≠ 0) :
    closedBallCollarInv (n := n) z =
      (sphereDiffeomorphBoundaryClosedBall (ballCollarInv z hz).1, ⟨_, normalRay_mem hz⟩) :=
  dite_eq_right hz

/-- The angular part of the inverse is `z / ‖z‖`. -/
private theorem coe_closedBallCollarInv_fst {z : closedBall (0 : E) 1} (hz : (z : E) ≠ 0) :
    (((closedBallCollarInv (n := n) z).1 : closedBall (0 : E) 1) : E) = ‖(z : E)‖⁻¹ • (z : E) := by
  rw [closedBallCollarInv_of_ne_zero hz, sphereDiffeomorphBoundaryClosedBall_apply_coe,
    coe_ballCollarInv_fst]

/-- The normal coordinate of the inverse is `1 - ‖z‖`. -/
private theorem closedBallCollarInv_snd_apply_zero {z : closedBall (0 : E) 1} (hz : (z : E) ≠ 0) :
    ((closedBallCollarInv (n := n) z).2 : EuclideanHalfSpace 1).val 0 = 1 - ‖(z : E)‖ := by
  rw [closedBallCollarInv_of_ne_zero hz, normalRay_coe_apply]
  exact max_eq_left (sub_nonneg.2 (mem_closedBall_zero_iff.1 z.property))

/-- The inverse of the polar collar is analytic on the punctured closed ball. -/
private theorem contMDiff_closedBallCollarInv {k : ℕ∞ω} :
    ContMDiff (𝓡∂ (n + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod (𝓡∂ 1)) k
      (fun y : puncturedClosedBall E ↦
        closedBallCollarInv (n := n) (E := E) (y : closedBall (0 : E) 1)) := by
  have hy : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, E) k
      (fun y : puncturedClosedBall E ↦ ((y : closedBall (0 : E) 1) : E)) :=
    contMDiff_subtypeVal_closedBall.comp contMDiff_subtypeVal
  have heq : (fun y : puncturedClosedBall E ↦
      closedBallCollarInv (n := n) (E := E) (y : closedBall (0 : E) 1)) =
      fun y : puncturedClosedBall E ↦
        (sphereDiffeomorphBoundaryClosedBall (ballCollarInv (y : closedBall (0 : E) 1)
          (mem_puncturedClosedBall.1 y.property)).1,
          ⟨_, normalRay_mem (mem_puncturedClosedBall.1 y.property)⟩) :=
    funext fun y ↦ closedBallCollarInv_of_ne_zero _
  rw [heq]
  refine ContMDiff.prodMk
    (((sphereDiffeomorphBoundaryClosedBall (n := n) (E := E)).contMDiff.of_le le_top).comp
      (contMDiff_ballCollarInv (n := n)).fst) ((TauCeti.ContMDiff.subtypeVal_comp_iff D _).1 ?_)
  exact ContMDiff.normalRay (fun y ↦ contMDiffAt_const.sub
      ((contDiffAt_norm ℝ (mem_puncturedClosedBall.1 y.property)).comp_contMDiffAt
        (f := fun y : puncturedClosedBall E ↦ ((y : closedBall (0 : E) 1) : E)) hy.contMDiffAt))
    fun y ↦ sub_nonneg.2 (mem_closedBall_zero_iff.1 y.val.property)

/-- The polar collar as a partial diffeomorphism onto the punctured closed ball. -/
private def closedBallCollarPartialDiffeomorph (k : ℕ∞ω) :
    PartialDiffeomorph (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) (B × D)
      (closedBall (0 : E) 1) k where
  toFun := closedBallCollarFun
  invFun := closedBallCollarInv
  source := univ
  target := puncturedClosedBall E
  map_source' p _ := mem_puncturedClosedBall.2 (closedBallCollarFun_ne_zero p)
  map_target' _ _ := mem_univ _
  left_inv' p _ := by
    have hz := closedBallCollarFun_ne_zero p
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext (Subtype.ext ?_))
    · rw [coe_closedBallCollarInv_fst hz, inv_norm_smul_closedBallCollarFun]
    · ext i
      rw [Subsingleton.elim i 0, closedBallCollarInv_snd_apply_zero hz, norm_closedBallCollarFun,
        sub_sub_cancel]
  right_inv' z hz := by
    have hz' : (z : E) ≠ 0 := mem_puncturedClosedBall.1 hz
    apply Subtype.ext
    rw [coe_closedBallCollarFun, closedBallCollarInv_snd_apply_zero hz',
      coe_closedBallCollarInv_fst hz', sub_sub_cancel, smul_inv_smul₀ (norm_ne_zero_iff.2 hz')]
  open_source := isOpen_univ
  open_target := (puncturedClosedBall E).isOpen
  contMDiffOn_toFun := contMDiff_closedBallCollarFun.contMDiffOn
  contMDiffOn_invFun z hz :=
    (contMDiffAt_subtype_iff (U := puncturedClosedBall E) (x := ⟨z, hz⟩).1
      (contMDiff_closedBallCollarInv _)).contMDiffWithinAt

/-! ### The polar collar -/

/-- The polar collar is a local diffeomorphism. -/
private theorem isLocalDiffeomorph_closedBallCollarFun {k : ℕ∞ω} :
    IsLocalDiffeomorph (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) k
      (closedBallCollarFun (n := n) (E := E)) := fun p ↦
  isLocalDiffeomorphAt_of_eqOn (Φ := closedBallCollarPartialDiffeomorph k) (mem_univ p)
    fun _ _ ↦ rfl

/-- The polar collar is injective. -/
private theorem injective_closedBallCollarFun : Injective (closedBallCollarFun (n := n) (E := E)) :=
  fun p q h ↦ by
    rw [← (closedBallCollarPartialDiffeomorph (n := n) (E := E) ⊤).left_inv (mem_univ p),
      ← (closedBallCollarPartialDiffeomorph (n := n) (E := E) ⊤).left_inv (mem_univ q)]
    exact congrArg _ h

/-- The polar collar sends the zero slice to the boundary sphere. -/
private theorem closedBallCollarFun_zero (x : B) :
    closedBallCollarFun (x, normalIioOpensZero one_pos) = x := by
  apply Subtype.ext
  simp [coe_closedBallCollarFun]

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
@[simp]
theorem SmoothCollar.range_closedBall {k : ℕ∞ω} :
    range (SmoothCollar.closedBall n E k) = puncturedClosedBall E := by
  ext z
  refine ⟨?_, fun hz ↦ ⟨closedBallCollarInv z,
    (closedBallCollarPartialDiffeomorph (n := n) (E := E) k).right_inv hz⟩⟩
  rintro ⟨p, rfl⟩
  exact mem_puncturedClosedBall.2 (closedBallCollarFun_ne_zero p)

/-- The image of the polar collar of the closed unit ball, as an open subset of the ball, is the
punctured closed ball. -/
@[simp]
theorem SmoothCollar.opensRange_closedBall {k : ℕ∞ω} :
    (SmoothCollar.closedBall n E k).opensRange = puncturedClosedBall E :=
  SetLike.coe_injective ((coe_opensRange _).trans range_closedBall)

/-- The polar collar of the closed unit ball sends depth `t` to norm `1 - t`. -/
theorem SmoothCollar.norm_closedBall_apply {k : ℕ∞ω} (p : B × D) :
    ‖(SmoothCollar.closedBall n E k p : E)‖ = 1 - (p.2 : EuclideanHalfSpace 1).val 0 := by
  rw [SmoothCollar.coe_closedBall_apply, norm_sub_smul_boundary]

/-- The inverse of the polar collar of the closed unit ball is `closedBallCollarInv`. -/
private theorem diffeomorphOpensRange_closedBall_symm {k : ℕ∞ω}
    (z : (SmoothCollar.closedBall n E k).opensRange) :
    (SmoothCollar.closedBall n E k).diffeomorphOpensRange.symm z = closedBallCollarInv z := by
  have hz : (z : closedBall (0 : E) 1) ∈ puncturedClosedBall E := by
    simpa only [SmoothCollar.opensRange_closedBall] using z.property
  rw [← (SmoothCollar.closedBall n E k).diffeomorphOpensRange.symm_apply_apply
    (closedBallCollarInv z)]
  refine congrArg _ (Subtype.ext ?_)
  rw [SmoothCollar.coe_diffeomorphOpensRange_apply]
  exact ((closedBallCollarPartialDiffeomorph (n := n) (E := E) k).right_inv hz).symm

/-- A point of the image of the polar collar of the closed unit ball is nonzero. -/
private theorem coe_opensRange_closedBall_ne_zero {k : ℕ∞ω}
    (z : (SmoothCollar.closedBall n E k).opensRange) :
    ((z : Metric.closedBall (0 : E) 1) : E) ≠ 0 := by
  rw [← mem_puncturedClosedBall, ← SmoothCollar.opensRange_closedBall (n := n) (k := k)]
  exact z.property

/-- The inverse of the polar collar of the closed unit ball sends `z` to the boundary point
`z / ‖z‖`. -/
@[simp]
theorem SmoothCollar.coe_diffeomorphOpensRange_closedBall_symm_apply_fst {k : ℕ∞ω}
    (z : (SmoothCollar.closedBall n E k).opensRange) :
    ((((SmoothCollar.closedBall n E k).diffeomorphOpensRange.symm z).1 :
        Metric.closedBall (0 : E) 1) : E) =
      ‖((z : Metric.closedBall (0 : E) 1) : E)‖⁻¹ • ((z : Metric.closedBall (0 : E) 1) : E) := by
  rw [diffeomorphOpensRange_closedBall_symm,
    coe_closedBallCollarInv_fst (coe_opensRange_closedBall_ne_zero z)]

/-- The inverse of the polar collar of the closed unit ball sends `z` to depth `1 - ‖z‖`. -/
@[simp]
theorem SmoothCollar.diffeomorphOpensRange_closedBall_symm_apply_snd_coe_apply {k : ℕ∞ω}
    (z : (SmoothCollar.closedBall n E k).opensRange) :
    (((SmoothCollar.closedBall n E k).diffeomorphOpensRange.symm z).2 :
        EuclideanHalfSpace 1).val 0 = 1 - ‖((z : Metric.closedBall (0 : E) 1) : E)‖ := by
  rw [diffeomorphOpensRange_closedBall_symm,
    closedBallCollarInv_snd_apply_zero (coe_opensRange_closedBall_ne_zero z)]

/-! ### The closed unit disc -/

section Disc

attribute [local instance] finrank_real_complex_fact'

/-- **The polar collar of the closed unit disc** is `(θ, t) ↦ (1 - t) e^{iθ}`: for every angle
`θ` and depth `t ∈ [0, 1)`, the boundary point `e^{iθ}` at depth `t` is sent to
`(1 - t) e^{iθ}`. -/
theorem SmoothCollar.exists_closedBall_complex_apply_eq_mul_exp {k : ℕ∞ω} (θ : ℝ) (t : D) :
    ∃ x : ModelWithCorners.boundary (I := 𝓡∂ (1 + 1)) (Metric.closedBall (0 : ℂ) 1),
      ((x : Metric.closedBall (0 : ℂ) 1) : ℂ) = Complex.exp (θ * Complex.I) ∧
      (SmoothCollar.closedBall 1 ℂ k (x, t) : ℂ) =
        (1 - (t : EuclideanHalfSpace 1).val 0) * Complex.exp (θ * Complex.I) := by
  have hx : ((circleHomeomorphBoundaryClosedBall (Circle.exp θ)).val : ℂ) =
      Complex.exp (θ * Complex.I) := by
    rw [circleHomeomorphBoundaryClosedBall_apply_coe, Circle.coe_exp]
  refine ⟨circleHomeomorphBoundaryClosedBall (Circle.exp θ), hx, ?_⟩
  rw [SmoothCollar.coe_closedBall_apply, Complex.real_smul, hx, Complex.ofReal_sub,
    Complex.ofReal_one]

end Disc

end TauCeti
