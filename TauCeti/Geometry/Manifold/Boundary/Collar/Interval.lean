/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Smooth
public import TauCeti.Geometry.Manifold.Boundary.Charts
public import Mathlib.Geometry.Manifold.Instances.Icc

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
(`TauCeti.not_injective_unitIntervalCollarFun_double`).

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

/-- The interval charts of `[0, 1]`, with the model dimension written as the successor `0 + 1`
used by the boundary constructions. -/
@[reducible] local instance instChartedSpaceUnitIntervalZeroAddOne :
    ChartedSpace (EuclideanHalfSpace (0 + 1)) (Icc (0 : ℝ) 1) :=
  instIccChartedSpace 0 1

/-- The zero-dimensional charts of the two endpoints of `[0, 1]`. -/
@[reducible] local instance instChartedSpaceUnitIntervalBoundary :
    ChartedSpace (EuclideanSpace ℝ (Fin 0)) ((𝓡∂ (0 + 1)).boundary (Icc (0 : ℝ) 1)) :=
  boundaryChartedSpace (n := 0)

/-- The interval `[0, 1]` is an analytic manifold for the charts
`instChartedSpaceUnitIntervalZeroAddOne`. -/
local instance instIsManifoldUnitIntervalZeroAddOne {k : ℕ∞ω} :
    IsManifold (𝓡∂ (0 + 1)) k (Icc (0 : ℝ) 1) :=
  instIsManifoldIcc 0 1

local notation "B" => ModelWithCorners.boundary (I := 𝓡∂ (0 + 1)) (Icc (0 : ℝ) 1)
local notation "D" => normalIioOpens 1

/-- The normal coordinate `t ∈ [0, 1)` of a point of `normalIioOpens 1`. -/
private theorem normal_mem_Ico (t : D) : (t : EuclideanHalfSpace 1).val 0 ∈ Ico (0 : ℝ) 1 :=
  ⟨(t : EuclideanHalfSpace 1).property, mem_normalIioOpens.1 t.property⟩

/-- An endpoint of `[0, 1]` is `0` or `1`. -/
private theorem boundary_coe_eq (x : B) : ((x : Icc (0 : ℝ) 1) : ℝ) = 0 ∨
    ((x : Icc (0 : ℝ) 1) : ℝ) = 1 := by
  have hx : (x : Icc (0 : ℝ) 1) ∈ ({⊥, ⊤} : Set (Icc (0 : ℝ) 1)) :=
    (Set.ext_iff.1 boundary_Icc _).1 x.property
  rcases hx with hx | hx
  · left; rw [hx]; rfl
  · right; rw [Set.mem_singleton_iff.1 hx]; rfl

/-- The real value `x + (1 - 2 x) t / 2` of the interval collar at the endpoint `x` and normal
coordinate `t`. -/
private theorem collar_mem_Icc (x : B) (t : D) :
    ((x : Icc (0 : ℝ) 1) : ℝ) + (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) *
      ((t : EuclideanHalfSpace 1).val 0 / 2) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := normal_mem_Ico t
  rcases boundary_coe_eq x with hx | hx <;> rw [hx] <;> constructor <;> linarith

/-- The underlying map of the interval collar of `[0, 1]`:
`(x, t) ↦ x + (1 - 2 x) t / 2`, that is `(0, t) ↦ t / 2` and `(1, t) ↦ 1 - t / 2`. -/
def unitIntervalCollarFun (p : B × D) : Icc (0 : ℝ) 1 :=
  ⟨((p.1 : Icc (0 : ℝ) 1) : ℝ) + (1 - 2 * ((p.1 : Icc (0 : ℝ) 1) : ℝ)) *
      ((p.2 : EuclideanHalfSpace 1).val 0 / 2), collar_mem_Icc p.1 p.2⟩

/-- The interval collar reads as `x + (1 - 2 x) t / 2` in `ℝ`. -/
@[simp]
theorem coe_unitIntervalCollarFun (p : B × D) :
    (unitIntervalCollarFun p : ℝ) = ((p.1 : Icc (0 : ℝ) 1) : ℝ) +
      (1 - 2 * ((p.1 : Icc (0 : ℝ) 1) : ℝ)) * ((p.2 : EuclideanHalfSpace 1).val 0 / 2) :=
  (rfl)

/-- The interval collar is analytic. -/
theorem contMDiff_unitIntervalCollarFun {k : ℕ∞ω} :
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

/-- A point `z` of `[0, 1]` lies on the inward side of the endpoint `x`: `(1 - 2 x) (z - x) ≥ 0`. -/
private theorem sign_mul_sub_nonneg (x : B) (z : Icc (0 : ℝ) 1) :
    0 ≤ (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) * ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)) := by
  obtain ⟨h0, h1⟩ := z.property
  rcases boundary_coe_eq x with hx | hx <;> rw [hx] <;> nlinarith

/-- The normal coordinate `2 (1 - 2 x) (z - x)` of a point `z` of `[0, 1]` seen from the endpoint
`x`, as a vector of the ambient space of the half-line model. -/
private def normalVec (x : B) (z : Icc (0 : ℝ) 1) : EuclideanSpace ℝ (Fin 1) :=
  (2 * (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) * ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ))) •
    EuclideanSpace.single 0 1

private theorem normalVec_apply_zero (x : B) (z : Icc (0 : ℝ) 1) : normalVec x z 0 =
    2 * (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) * ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)) := by
  simp [normalVec]

/-- The point of the half-line model with normal coordinate `2 (1 - 2 x) (z - x)`. -/
private def normalPoint (x : B) (z : Icc (0 : ℝ) 1) : EuclideanHalfSpace 1 :=
  (𝓡∂ 1).symm (normalVec x z)

private theorem normalPoint_apply_zero (x : B) (z : Icc (0 : ℝ) 1) :
    (normalPoint x z).val 0 =
      2 * (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) * ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)) := by
  have h : 0 ≤ normalVec x z 0 := by
    rw [normalVec_apply_zero, mul_assoc]
    exact mul_nonneg zero_le_two (sign_mul_sub_nonneg x z)
  rw [normalPoint, modelWithCornersEuclideanHalfSpace_symm_apply_of_le h, normalVec_apply_zero]

private theorem contMDiff_normalPoint {k : ℕ∞ω} (x : B) :
    ContMDiff (𝓡∂ (0 + 1)) (𝓡∂ 1) k (normalPoint x) := by
  have hv : ContMDiff (𝓡∂ (0 + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) k (normalVec x) := by
    have hc : ContDiff ℝ k (fun r : ℝ ↦ (2 * (1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) *
        (r - ((x : Icc (0 : ℝ) 1) : ℝ))) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := by
      fun_prop
    exact hc.contMDiff.comp contMDiff_subtypeVal_Icc
  refine (𝓡∂ 1).contMDiffOn_symm.comp_contMDiff hv fun z ↦ ?_
  rw [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq, normalVec_apply_zero, mul_assoc]
  exact mul_nonneg zero_le_two (sign_mul_sub_nonneg x z)

/-- Two endpoints at distance less than `1/2` are equal. -/
private theorem eq_of_abs_sub_lt {x y : B}
    (h : |((y : Icc (0 : ℝ) 1) : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)| < 1 / 2) : y = x := by
  refine Subtype.ext (Subtype.ext ?_)
  rcases boundary_coe_eq x with hx | hx <;> rcases boundary_coe_eq y with hy | hy <;>
    simp only [hx, hy] at h ⊢ <;> norm_num at h

/-- The interval collar stays within distance `1/2` of its endpoint. -/
private theorem abs_unitIntervalCollarFun_sub_lt (p : B × D) :
    |(unitIntervalCollarFun p : ℝ) - ((p.1 : Icc (0 : ℝ) 1) : ℝ)| < 1 / 2 := by
  obtain ⟨h0, h1⟩ := normal_mem_Ico p.2
  rw [coe_unitIntervalCollarFun, add_sub_cancel_left]
  rcases boundary_coe_eq p.1 with hx | hx <;> rw [hx] <;> norm_num <;>
    rw [abs_of_nonneg (by linarith)] <;> linarith

/-- A map into `normalIioOpens 1` is `C^k` at a point when its composition with the inclusion
is. -/
private theorem contMDiffAt_of_subtypeVal_comp {k : ℕ∞ω} {f : Icc (0 : ℝ) 1 → D}
    {z : Icc (0 : ℝ) 1} (h : ContMDiffAt (𝓡∂ (0 + 1)) (𝓡∂ 1) k (Subtype.val ∘ f) z) :
    ContMDiffAt (𝓡∂ (0 + 1)) (𝓡∂ 1) k f z :=
  (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).1 h

/-- The points of `[0, 1]` at distance less than `1/2` from the endpoint `x`. -/
private def nearEnd (x : B) : Set (Icc (0 : ℝ) 1) :=
  {z | |(z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ)| < 1 / 2}

private theorem isOpen_nearEnd (x : B) : IsOpen (nearEnd x) :=
  isOpen_lt (by fun_prop) continuous_const

private theorem normalPoint_mem (x : B) {z : Icc (0 : ℝ) 1} (hz : z ∈ nearEnd x) :
    normalPoint x z ∈ D := by
  rw [mem_normalIioOpens, normalPoint_apply_zero, mul_assoc]
  have h := sign_mul_sub_nonneg x z
  have habs : |(1 - 2 * ((x : Icc (0 : ℝ) 1) : ℝ)) *
      ((z : ℝ) - ((x : Icc (0 : ℝ) 1) : ℝ))| < 1 / 2 := by
    rcases boundary_coe_eq x with hx | hx <;> simp only [nearEnd, mem_ofPred_eq] at hz <;>
      rw [hx] at hz ⊢ <;> norm_num <;> simpa [abs_sub_comm] using hz
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
  map_source' p hp := by
    have hx := eq_of_abs_sub_lt hp
    have h := abs_unitIntervalCollarFun_sub_lt p
    rwa [hx] at h
  map_target' z _ := by simp [localInv]
  left_inv' p hp := by
    have hx := eq_of_abs_sub_lt hp
    have hz : unitIntervalCollarFun p ∈ nearEnd x := by
      have h := abs_unitIntervalCollarFun_sub_lt p
      rwa [hx] at h
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
    refine (contMDiffAt_const.prodMk (contMDiffAt_of_subtypeVal_comp ?_)).contMDiffWithinAt
    refine ((contMDiff_normalPoint x) z).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_nearEnd x).mem_nhds hz] with w hw
    simp [hw]

/-- The interval collar is a local diffeomorphism. -/
theorem isLocalDiffeomorph_unitIntervalCollarFun {k : ℕ∞ω} :
    IsLocalDiffeomorph ((𝓡 0).prod (𝓡∂ 1)) (𝓡∂ (0 + 1)) k unitIntervalCollarFun := fun p ↦
  isLocalDiffeomorphAt_of_eqOn (Φ := localCollar k p.1) (by simp [localCollar])
    fun _ _ ↦ rfl

/-- The interval collar is injective. -/
theorem injective_unitIntervalCollarFun : Injective unitIntervalCollarFun := by
  intro p q h
  have hx : q.1 = p.1 := by
    apply eq_of_abs_sub_lt
    have hp := abs_unitIntervalCollarFun_sub_lt p
    have hq := abs_unitIntervalCollarFun_sub_lt q
    rw [h] at hp
    rcases boundary_coe_eq p.1 with h₁ | h₁ <;> rcases boundary_coe_eq q.1 with h₂ | h₂ <;>
      rw [h₁] at hp <;> rw [h₂] at hq <;> rw [h₁, h₂] <;> norm_num <;>
      rw [abs_lt] at hp hq <;> linarith [hp.1, hp.2, hq.1, hq.2]
  have hp : p ∈ (localCollar ⊤ p.1).source := by simp [localCollar]
  have hq : q ∈ (localCollar ⊤ p.1).source := by simp [localCollar, hx]
  rw [← (localCollar ⊤ p.1).left_inv hp, ← (localCollar ⊤ p.1).left_inv hq]
  exact congrArg _ h

/-- The interval collar sends the zero slice to the endpoints. -/
theorem unitIntervalCollarFun_zero (x : B) :
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
    have h := abs_unitIntervalCollarFun_sub_lt p
    change (unitIntervalCollarFun p : ℝ) ≠ 1 / 2
    intro he
    rw [he] at h
    rcases boundary_coe_eq p.1 with hx | hx <;> rw [hx] at h <;> norm_num at h
  · intro hz
    obtain ⟨h0, h1⟩ := z.property
    have hz' : (z : ℝ) ≠ 1 / 2 := hz
    obtain ⟨x, hx⟩ : ∃ x : B, z ∈ nearEnd x := by
      rcases lt_or_gt_of_ne hz' with h | h
      · refine ⟨⟨⊥, Icc_isBoundaryPoint_bot⟩, ?_⟩
        simp only [nearEnd, mem_ofPred_eq]
        rw [abs_lt]
        constructor <;> simp <;> linarith
      · refine ⟨⟨⊤, Icc_isBoundaryPoint_top⟩, ?_⟩
        simp only [nearEnd, mem_ofPred_eq]
        rw [abs_lt]
        constructor <;> simp <;> linarith
    exact ⟨localInv x z, (localCollar k x).right_inv hx⟩

/-- **The factor `1/2` is needed.** Without it, the map `(x, t) ↦ x + (1 - 2 x) t`, that is
`(0, t) ↦ t` and `(1, t) ↦ 1 - t`, sends `(0, 1/2)` and `(1, 1/2)` to the same point. -/
theorem not_injective_unitIntervalCollarFun_double :
    ¬Injective (fun p : B × D ↦ ((p.1 : Icc (0 : ℝ) 1) : ℝ) +
      (1 - 2 * ((p.1 : Icc (0 : ℝ) 1) : ℝ)) * (p.2 : EuclideanHalfSpace 1).val 0) := by
  intro h
  let t : D := ⟨(𝓡∂ 1).symm (EuclideanSpace.single 0 (1 / 2)), by
    rw [mem_normalIioOpens, modelWithCornersEuclideanHalfSpace_symm_apply_of_le (by simp)]
    norm_num⟩
  have ht : (t : EuclideanHalfSpace 1).val 0 = 1 / 2 := by
    change ((𝓡∂ 1).symm (EuclideanSpace.single 0 (1 / 2))).val 0 = 1 / 2
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (by simp)]
    simp
  have he := congrArg (fun p : B × D ↦ ((p.1 : Icc (0 : ℝ) 1) : ℝ))
    (h (a₁ := (⟨⊥, Icc_isBoundaryPoint_bot⟩, t)) (a₂ := (⟨⊤, Icc_isBoundaryPoint_top⟩, t))
      (by simp only [ht]; norm_num))
  norm_num at he

end TauCeti
