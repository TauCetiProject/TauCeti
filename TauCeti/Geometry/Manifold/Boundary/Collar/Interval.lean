/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.Boundary.Charts
public import Mathlib.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Orientation.Interval
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The interval collar of `[0, 1]`

The unit interval `[0, 1]` is a manifold with boundary whose boundary consists of its two
endpoints. This file builds its *interval collar* `TauCeti.SmoothCollar.unitInterval`, the smooth
collar

`(0, t) ↦ t / 2`, `(1, t) ↦ 1 - t / 2`, for `t ∈ [0, 1)`,

written uniformly as `(x, t) ↦ x + (1 - 2 x) t / 2` for an endpoint `x ∈ {0, 1}`. Its image is
`[0, 1/2) ∪ (1/2, 1]`, the interval without its midpoint
(`TauCeti.SmoothCollar.range_unitInterval`). The factor `1/2` is needed: the map
`(x, t) ↦ x + (1 - 2 x) t` without it sends `(0, 1/2)` and `(1, 1/2)` to the same point
(`TauCeti.not_injective_add_sign_mul_normal`).

Near each endpoint `x` the collar is a partial diffeomorphism from `{x} × [0, 1)` onto the half of
the interval at distance less than `1/2` from `x`, with inverse `z ↦ (x, 2 |z - x|)`; this is what
makes it a local diffeomorphism.

The boundary of `[0, 1]` is zero-dimensional, so its charts and the interval charts are written
with the model dimension `0 + 1` used by the boundary constructions.
-/

public section

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace TauCeti

open Fact.Manifold
open _root_.TauCeti.EuclideanHalfSpace

attribute [local instance] intervalBoundaryChartedSpace

local notation "B" => ModelWithCorners.boundary (I := 𝓡∂ (0 + 1)) (Icc (0 : ℝ) 1)
local notation "D" => normalIioOpens 1

/-- An endpoint of `[0, 1]` is `0` or `1`. -/
private theorem boundary_coe_eq (x : B) : ((x : Icc (0 : ℝ) 1) : ℝ) = 0 ∨
    ((x : Icc (0 : ℝ) 1) : ℝ) = 1 := by
  have hx : (x : Icc (0 : ℝ) 1) ∈ ({⊥, ⊤} : Set (Icc (0 : ℝ) 1)) :=
    (Set.ext_iff.1 boundary_Icc _).1 x.property
  rcases hx with hx | hx
  · left; rw [hx, Icc.coe_bot]
  · right; rw [Set.mem_singleton_iff.1 hx, Icc.coe_top]

/-- The value `x + (1 - 2 x) t / 2` of the interval collar at an endpoint `x` and normal
coordinate `t ∈ [0, 1)` lies in `[0, 1]`. -/
private theorem collar_mem_Icc (x : B) (t : D) :
    ((x : Icc (0 : ℝ) 1) : ℝ) + (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) *
      ((t : EuclideanHalfSpace 1).val 0 / 2) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := (homeomorphNormalIioOpens 1 t).property
  rw [coe_homeomorphNormalIioOpens] at h0 h1
  rcases boundary_coe_eq x with hx | hx <;> rw [hx] <;> constructor <;> linarith

/-- The underlying map of the interval collar of `[0, 1]`:
`(x, t) ↦ x + (1 - 2 x) t / 2`, that is `(0, t) ↦ t / 2` and `(1, t) ↦ 1 - t / 2`. -/
private def unitIntervalCollarFun (p : B × D) : Icc (0 : ℝ) 1 :=
  ⟨((p.1 : Icc (0 : ℝ) 1) : ℝ) + (1 - 2 * ((p.1 : Icc (0 : ℝ) 1) : ℝ)) *
      ((p.2 : EuclideanHalfSpace 1).val 0 / 2), collar_mem_Icc p.1 p.2⟩

/-- The interval collar reads as `x + (1 - 2 x) t / 2` in `ℝ`. -/
@[simp]
private theorem coe_unitIntervalCollarFun (p : B × D) :
    (unitIntervalCollarFun p : ℝ) = ((p.1 : Icc (0 : ℝ) 1) : ℝ) +
      (1 - 2 * ((p.1 : Icc (0 : ℝ) 1) : ℝ)) * ((p.2 : EuclideanHalfSpace 1).val 0 / 2) :=
  (rfl)

/-- The interval collar is analytic. -/
private theorem contMDiff_unitIntervalCollarFun {k : ℕ∞ω} :
    ContMDiff ((𝓡 0).prod (𝓡∂ 1)) (𝓡∂ (0 + 1)) k unitIntervalCollarFun := by
  have hx : ContMDiff (𝓡 0) 𝓘(ℝ) k (fun x : B ↦ ((x : Icc (0 : ℝ) 1) : ℝ)) :=
    contMDiff_subtypeVal_Icc.comp
      (isSmoothEmbedding_subtypeVal_boundary (n := 0) (k := k) (Icc (0 : ℝ) 1)).contMDiff
  have ht : ContMDiff (𝓡∂ 1) 𝓘(ℝ) k (fun t : D ↦ (t : EuclideanHalfSpace 1).val 0) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 1) 0).contDiff.contMDiff.comp
      (𝓡∂ 1).contMDiff).comp (contMDiff_subtypeVal (U := D))
  have hxp : ContMDiff ((𝓡 0).prod (𝓡∂ 1)) 𝓘(ℝ) k
      (fun p : B × D ↦ ((p.1 : Icc (0 : ℝ) 1) : ℝ)) := hx.comp contMDiff_fst
  have htp : ContMDiff ((𝓡 0).prod (𝓡∂ 1)) 𝓘(ℝ) k
      (fun p : B × D ↦ (p.2 : EuclideanHalfSpace 1).val 0) := ht.comp contMDiff_snd
  have hg : ContDiff ℝ k (fun q : ℝ × ℝ ↦ q.1 + (1 - 2 * q.1) * (q.2 / 2)) := by fun_prop
  have h := hg.contMDiff.comp (hxp.prodMk_space htp)
  exact contMDiff_iff_comp_subtypeVal_Icc.2 ⟨continuous_induced_rng.2 h.continuous, h⟩

/-! ### The local inverses near the endpoints -/

/-- The sign `1 - 2 x` of an endpoint `x ∈ {0, 1}` squares to one. -/
private theorem sign_mul_self (x : B) :
    (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) * (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) = 1 := by
  rcases boundary_coe_eq x with hx | hx <;> rw [hx] <;> norm_num

/-- The sign `1 - 2 x` of an endpoint `x ∈ {0, 1}` has absolute value one. -/
private theorem abs_sign (x : B) : |1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)| = 1 :=
  (mul_self_eq_one_iff.1 ((abs_mul_abs_self _).trans (sign_mul_self x))).resolve_right
    fun h ↦ by linarith [abs_nonneg (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ))]

/-- A point `z` of `[0, 1]` lies on the inward side of the endpoint `x`: `(1 - 2 x) (z - x) ≥ 0`. -/
private theorem sign_mul_sub_nonneg (x : B) (z : Icc (0 : ℝ) 1) :
    0 ≤ (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) * ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)) := by
  obtain ⟨h0, h1⟩ := z.property
  rcases boundary_coe_eq x with hx | hx <;> rw [hx] <;> nlinarith

/-- The point of the half-line model with normal coordinate `2 (1 - 2 x) (z - x)`: the normal
coordinate of a point `z` of `[0, 1]` seen from the endpoint `x`. -/
private def normalPoint (x : B) (z : Icc (0 : ℝ) 1) : EuclideanHalfSpace 1 :=
  normalRay (2 * (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) * ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)))

private theorem normalPoint_apply_zero (x : B) (z : Icc (0 : ℝ) 1) :
    (normalPoint x z).val 0 =
      2 * (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) * ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)) := by
  rw [normalPoint, normalRay_coe_apply, max_eq_left]
  rw [mul_assoc]
  exact mul_nonneg zero_le_two (sign_mul_sub_nonneg x z)

private theorem contMDiff_normalPoint {k : ℕ∞ω} (x : B) :
    ContMDiff (𝓡∂ (0 + 1)) (𝓡∂ 1) k (normalPoint x) := by
  let e := (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).symm
  have hv : ContMDiff (𝓡∂ (0 + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) k (fun z : Icc (0 : ℝ) 1 ↦
      e (2 * (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) * ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)))) := by
    have hc : ContDiff ℝ k (fun r : ℝ ↦ e (2 * (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) *
        (r - ((x : Icc (0 : ℝ) 1) : ℝ)))) :=
      e.contDiff.comp (by fun_prop)
    exact hc.contMDiff.comp contMDiff_subtypeVal_Icc
  have h := (𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hv fun z ↦ by
    rw [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq, mul_assoc]
    exact mul_nonneg zero_le_two (sign_mul_sub_nonneg x z)
  exact h.congr fun z ↦ normalRay_eq_symm _

/-- Two endpoints at distance less than `1` are equal. -/
private theorem eq_of_abs_sub_lt {x y : B}
    (h : |((y : Icc (0 : ℝ) 1) : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)| < 1) : y = x := by
  refine Subtype.ext (Subtype.ext ?_)
  rcases boundary_coe_eq x with hx | hx <;> rcases boundary_coe_eq y with hy | hy <;>
    simp only [hx, hy] at h ⊢ <;> norm_num at h

/-- The points of `[0, 1]` at distance less than `1/2` from the endpoint `x`. -/
private def nearEnd (x : B) : Set (Icc (0 : ℝ) 1) :=
  {z | |(z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)| < 1 / 2}

/-- The interval collar stays within distance `1/2` of its endpoint. -/
private theorem unitIntervalCollarFun_mem_nearEnd (p : B × D) :
    unitIntervalCollarFun p ∈ nearEnd p.1 := by
  simp only [nearEnd, mem_ofPred_eq]
  obtain ⟨h0, h1⟩ := (homeomorphNormalIioOpens 1 p.2).property
  rw [coe_homeomorphNormalIioOpens] at h0 h1
  rw [coe_unitIntervalCollarFun, add_sub_cancel_left, abs_mul, abs_sign, one_mul,
    abs_of_nonneg (by linarith)]
  linarith

/-- The regions near the two endpoints are disjoint: a point near both `x` and `y` forces
`x = y`. -/
private theorem eq_of_mem_nearEnd {x y : B} {z : Icc (0 : ℝ) 1} (hx : z ∈ nearEnd x)
    (hy : z ∈ nearEnd y) : x = y := by
  refine eq_of_abs_sub_lt ?_
  calc |((x : Icc (0 : ℝ) 1) : ℝ) - ((y : Icc (0 : ℝ) 1) : ℝ)|
      ≤ |((x : Icc (0 : ℝ) 1) : ℝ) - (z : ℝ)| + |(z : ℝ) - ((y : Icc (0 : ℝ) 1) : ℝ)| :=
        abs_sub_le _ _ _
    _ < 1 / 2 + 1 / 2 := add_lt_add (by rwa [abs_sub_comm]) hy
    _ = 1 := by norm_num

/-- A point of `[0, 1]` other than its midpoint is near one of the endpoints. -/
private theorem exists_mem_nearEnd {z : Icc (0 : ℝ) 1} (hz : (z : ℝ) ≠ 1 / 2) :
    ∃ x : B, z ∈ nearEnd x := by
  obtain ⟨h0, h1⟩ := z.property
  rcases lt_or_gt_of_ne hz with h | h
  · refine ⟨⟨⊥, Icc_isBoundaryPoint_bot⟩, ?_⟩
    simp only [nearEnd, mem_ofPred_eq, Icc.coe_bot, abs_lt]
    constructor <;> linarith
  · refine ⟨⟨⊤, Icc_isBoundaryPoint_top⟩, ?_⟩
    simp only [nearEnd, mem_ofPred_eq, Icc.coe_top, abs_lt]
    constructor <;> linarith

private theorem isOpen_nearEnd (x : B) : IsOpen (nearEnd x) :=
  isOpen_lt (by fun_prop) continuous_const

private theorem normalPoint_mem (x : B) {z : Icc (0 : ℝ) 1} (hz : z ∈ nearEnd x) :
    normalPoint x z ∈ D := by
  rw [mem_normalIioOpens, normalPoint_apply_zero, mul_assoc]
  have h := sign_mul_sub_nonneg x z
  have habs : |(1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) *
      ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ))| < 1 / 2 := by
    rwa [abs_mul, abs_sign, one_mul]
  rw [abs_of_nonneg h] at habs
  linarith

open Classical in
/-- The local inverse of the interval collar near the endpoint `x`: `z ↦ (x, 2 |z - x|)`, on the
points at distance less than `1/2` from `x`. -/
private def localInv (x : B) (z : Icc (0 : ℝ) 1) : B × D :=
  (x, if hz : z ∈ nearEnd x then ⟨normalPoint x z, normalPoint_mem x hz⟩
    else normalIioOpensZero one_pos)

/-- The interval collar near the endpoint `x`, as a partial diffeomorphism from `{x} × [0, 1)` onto
the points at distance less than `1/2` from `x`. -/
private def localCollar (k : ℕ∞ω) (x : B) :
    PartialDiffeomorph ((𝓡 0).prod (𝓡∂ 1)) (𝓡∂ (0 + 1)) (B × D) (Icc (0 : ℝ) 1) k where
  toFun := unitIntervalCollarFun
  invFun := localInv x
  source := {p | |((p.1 : Icc (0 : ℝ) 1) : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)| < 1 / 2}
  target := nearEnd x
  map_source' p hp :=
    eq_of_abs_sub_lt (hp.trans (by norm_num)) ▸ unitIntervalCollarFun_mem_nearEnd p
  map_target' z _ := by simp [localInv]
  left_inv' p hp := by
    have hx := eq_of_abs_sub_lt (hp.trans (by norm_num))
    have hz : unitIntervalCollarFun p ∈ nearEnd x := hx ▸ unitIntervalCollarFun_mem_nearEnd p
    refine Prod.ext hx.symm (Subtype.ext (Subtype.ext ?_))
    simp only [localInv, hz, ↓reduceDIte]
    ext i
    rw [Subsingleton.elim i 0, normalPoint_apply_zero, coe_unitIntervalCollarFun, hx,
      add_sub_cancel_left]
    linear_combination (p.2 : EuclideanHalfSpace 1).val 0 * sign_mul_self x
  right_inv' z hz := by
    apply Subtype.ext
    simp only [localInv, hz, ↓reduceDIte, coe_unitIntervalCollarFun, normalPoint_apply_zero]
    linear_combination ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)) * sign_mul_self x
  open_source := isOpen_lt (by fun_prop) continuous_const
  open_target := isOpen_nearEnd x
  contMDiffOn_toFun := contMDiff_unitIntervalCollarFun.contMDiffOn
  contMDiffOn_invFun z hz := by
    have h : ContMDiffAt (𝓡∂ (0 + 1)) (𝓡∂ 1) k (fun w ↦ (localInv x w).2) z := by
      refine (TauCeti.ContMDiffAt.subtypeVal_comp_iff D _ z).1 ?_
      refine ((contMDiff_normalPoint x) z).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_nearEnd x).mem_nhds hz] with w hw
      simp [localInv, hw]
    exact (contMDiffAt_const.prodMk h).contMDiffWithinAt

/-- The map of `localCollar k x` is the interval collar. -/
private theorem localCollar_apply (k : ℕ∞ω) (x : B) (p : B × D) :
    (localCollar k x).toPartialEquiv p = unitIntervalCollarFun p :=
  rfl

/-- The inverse of `localCollar k x` is `localInv x`. -/
private theorem localCollar_symm_apply (k : ℕ∞ω) (x : B) (z : Icc (0 : ℝ) 1) :
    (localCollar k x).toPartialEquiv.symm z = localInv x z :=
  rfl

/-- The interval collar is a local diffeomorphism. -/
private theorem isLocalDiffeomorph_unitIntervalCollarFun {k : ℕ∞ω} :
    IsLocalDiffeomorph ((𝓡 0).prod (𝓡∂ 1)) (𝓡∂ (0 + 1)) k unitIntervalCollarFun := fun p ↦
  isLocalDiffeomorphAt_of_eqOn (Φ := localCollar k p.1) (by simp [localCollar])
    fun _ _ ↦ rfl

/-- The interval collar is injective. -/
private theorem injective_unitIntervalCollarFun : Injective unitIntervalCollarFun := by
  intro p q h
  have hx : q.1 = p.1 :=
    eq_of_mem_nearEnd (unitIntervalCollarFun_mem_nearEnd q)
      (h ▸ unitIntervalCollarFun_mem_nearEnd p)
  have hp : p ∈ (localCollar ⊤ p.1).source := by simp [localCollar]
  have hq : q ∈ (localCollar ⊤ p.1).source := by simp [localCollar, hx]
  rw [← (localCollar ⊤ p.1).left_inv hp, ← (localCollar ⊤ p.1).left_inv hq]
  exact congrArg _ h

/-- The interval collar sends the zero slice to the endpoints. -/
private theorem unitIntervalCollarFun_zero (x : B) :
    unitIntervalCollarFun (x, normalIioOpensZero one_pos) = x := by
  apply Subtype.ext
  simp

variable (k : ℕ∞ω) in
/-- The **interval collar** of `[0, 1]`: the smooth collar `(0, t) ↦ t / 2`, `(1, t) ↦ 1 - t / 2`,
for `t ∈ [0, 1)`. -/
def SmoothCollar.unitInterval : SmoothCollar 0 k (Icc (0 : ℝ) 1) where
  toFun := unitIntervalCollarFun
  isLocalDiffeomorph' := isLocalDiffeomorph_unitIntervalCollarFun
  injective' := injective_unitIntervalCollarFun
  apply_zero' := unitIntervalCollarFun_zero

/-- The interval collar of `[0, 1]` is `(x, t) ↦ x + (1 - 2 x) t / 2`. -/
@[simp]
theorem SmoothCollar.coe_unitInterval_apply {k : ℕ∞ω} (p : B × D) :
    (SmoothCollar.unitInterval k p : ℝ) = ((p.1 : Icc (0 : ℝ) 1) : ℝ) +
      (1 - 2 * ((p.1 : Icc (0 : ℝ) 1) : ℝ)) * ((p.2 : EuclideanHalfSpace 1).val 0 / 2) :=
  (rfl)

/-- The image of the interval collar of `[0, 1]` is `[0, 1/2) ∪ (1/2, 1]`, the interval without
its midpoint. -/
theorem SmoothCollar.range_unitInterval {k : ℕ∞ω} :
    range (SmoothCollar.unitInterval k) = {z : Icc (0 : ℝ) 1 | (z : ℝ) ≠ 1 / 2} := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    have h := unitIntervalCollarFun_mem_nearEnd p
    simp only [nearEnd, mem_ofPred_eq, coe_unitIntervalCollarFun] at h
    simp only [mem_ofPred_eq, SmoothCollar.coe_unitInterval_apply]
    intro he
    rw [he] at h
    rcases boundary_coe_eq p.1 with hx | hx <;> rw [hx] at h <;> norm_num at h
  · intro hz
    obtain ⟨x, hx⟩ := exists_mem_nearEnd hz
    refine ⟨localInv x z, ?_⟩
    rw [SmoothCollar.unitInterval, SmoothCollar.coe_mk, ← localCollar_symm_apply k,
      ← localCollar_apply k x]
    exact (localCollar k x).right_inv hx

/-- **The factor `1/2` is needed.** Without it, the map `(x, t) ↦ x + (1 - 2 x) t`, which moves an
endpoint `x` of `[0, 1]` by `t` in the direction of the sign `1 - 2 x = ±1` of its inward normal,
that is `(0, t) ↦ t` and `(1, t) ↦ 1 - t`, sends `(0, 1/2)` and `(1, 1/2)` to the same point. -/
theorem not_injective_add_sign_mul_normal :
    ¬Injective (fun p : B × D ↦ ((p.1 : Icc (0 : ℝ) 1) : ℝ) +
      (1 - 2 * ((p.1 : Icc (0 : ℝ) 1) : ℝ)) * (p.2 : EuclideanHalfSpace 1).val 0) := by
  intro h
  let t : D := (homeomorphNormalIioOpens 1).symm ⟨1 / 2, by norm_num⟩
  have ht : (t : EuclideanHalfSpace 1).val 0 = 1 / 2 := by
    rw [coe_homeomorphNormalIioOpens_symm, normalRay_coe_apply]
    norm_num
  have he := congrArg (fun p : B × D ↦ ((p.1 : Icc (0 : ℝ) 1) : ℝ))
    (h (a₁ := (⟨⊥, Icc_isBoundaryPoint_bot⟩, t)) (a₂ := (⟨⊤, Icc_isBoundaryPoint_top⟩, t))
      (by simp only [ht]; norm_num))
  norm_num at he

end TauCeti
