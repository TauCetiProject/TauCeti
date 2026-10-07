/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Ray
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Segment

/-!
# Geodesic segments, rays and lines between points of `ℍ ∪ ∂ℍ`

For points `p`, `q` of `ℍ ∪ ∂ℍ`, modelled as `ℍ ⊕ OnePoint ℝ`, `extGeodesicSegment p q` is the
closed piece of the geodesic through `p` and `q` lying between them, as a set of points of `ℍ`:
the segment `geodesicSegment z w` between two points of `ℍ`, the ray from a point of `ℍ` towards
an ideal point, and the whole geodesic line between two distinct ideal points. Between an ideal
point and itself it is empty. The piece does not depend on the order of `p` and `q`
(`extGeodesicSegment_comm`), contains the endpoints that lie in `ℍ`, lies on every geodesic
line running from `p` to `q` (`extGeodesicSegment_subset_range_geodesicLine`), and is
equivariant under `PSL(2, ℝ)` (`smul_extGeodesicSegment`).

Closed half-planes are convex in this extended sense: if `p` and `q` are weakly to the left of
`geodesicLine k` (`extClosedLeftHalfPlane k`), then so is the piece between them
(`extGeodesicSegment_subset_closure_leftHalfPlane`), and in particular a geodesic ray or line
whose endpoints are weakly to the left of `geodesicLine k` lies in its closed left half-plane
(`geodesicLine_image_Ici_subset_closure_leftHalfPlane`,
`range_geodesicLine_subset_closure_leftHalfPlane`). Away from finite endpoints, this containment
is strict unless the supporting lines coincide
(`mem_leftHalfPlane_of_mem_extGeodesicSegment`).

## Main declarations

* `TauCeti.UpperHalfPlane.extGeodesicSegment p q`: the closed geodesic piece between two
  points of `ℍ ∪ ∂ℍ`.
* `TauCeti.UpperHalfPlane.extGeodesicSegment_comm`,
  `TauCeti.UpperHalfPlane.smul_extGeodesicSegment`: symmetry and equivariance.
* `TauCeti.UpperHalfPlane.extGeodesicSegment_subset_closure_leftHalfPlane`: closed
  half-planes are convex.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §7.1 (for
`z, w ∈ ℍ ∪ ∂ℍ`, the part `[z, w]` of the unique geodesic through `z` and `w` lying between them;
the sides of a polygon with vertices in `ℍ ∪ ∂ℍ`) and Solution 14.1 (half-planes are convex).
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint

namespace TauCeti.UpperHalfPlane

open Matrix.ProjectiveSpecialLinearGroup (mk_smul_zero_eq_infty_iff mk_smul_infty_eq_infty_iff
  mk_smul_zero_eq_coe_iff mk_smul_infty_eq_coe_iff)

/-! ### The geodesic piece between two points of `ℍ ∪ ∂ℍ` -/

open scoped Classical in
/-- The closed piece of the geodesic through `p` and `q` lying between them, for points `p`, `q`
of `ℍ ∪ ∂ℍ`: the segment `geodesicSegment z w` for `z, w ∈ ℍ` (the point `{z}` if `z = w`), the
ray from `z ∈ ℍ` towards an ideal point `ξ` (in either order of `p` and `q`), and the whole
geodesic line between two distinct ideal points. Between an ideal point and itself it is `∅`. -/
def extGeodesicSegment : ℍ ⊕ OnePoint ℝ → ℍ ⊕ OnePoint ℝ → Set ℍ
  | .inl z, .inl w => geodesicSegment z w
  | .inl z, .inr η => geodesicLine (rayToward z (.inr η)) '' Set.Ici 0
  | .inr ξ, .inl w => geodesicLine (rayToward w (.inr ξ)) '' Set.Ici 0
  | .inr ξ, .inr η =>
    if ξ = η then ∅ else Set.range (geodesicLine (geodesicFromTo (.inr ξ) (.inr η)))

-- The body of `extGeodesicSegment` is not `@[expose]`d, so downstream modules rewrite with
-- the following case lemmas.
/-- Between two points of `ℍ`, the piece is the geodesic segment. -/
@[simp]
theorem extGeodesicSegment_inl_inl (z w : ℍ) :
    extGeodesicSegment (.inl z) (.inl w) = geodesicSegment z w := by
  rfl

/-- Between a point `z` of `ℍ` and an ideal point `η`, the piece is the ray from `z` to `η`. -/
@[simp]
theorem extGeodesicSegment_inl_inr (z : ℍ) (η : OnePoint ℝ) :
    extGeodesicSegment (.inl z) (.inr η) = geodesicLine (rayToward z (.inr η)) '' Set.Ici 0 := by
  rfl

/-- Between an ideal point `ξ` and a point `w` of `ℍ`, the piece is the ray from `w` to `ξ`. -/
@[simp]
theorem extGeodesicSegment_inr_inl (ξ : OnePoint ℝ) (w : ℍ) :
    extGeodesicSegment (.inr ξ) (.inl w) = geodesicLine (rayToward w (.inr ξ)) '' Set.Ici 0 := by
  rfl

/-- Between an ideal point and itself, the piece is empty. -/
@[simp]
theorem extGeodesicSegment_inr_self (ξ : OnePoint ℝ) :
    extGeodesicSegment (.inr ξ) (.inr ξ) = ∅ := by
  simp [extGeodesicSegment]

/-- Between two distinct ideal points, the piece is the whole geodesic line joining them. -/
theorem extGeodesicSegment_inr_inr {ξ η : OnePoint ℝ} (h : ξ ≠ η) :
    extGeodesicSegment (.inr ξ) (.inr η) =
      Set.range (geodesicLine (geodesicFromTo (.inr ξ) (.inr η))) := by
  simp [extGeodesicSegment, h]

/-- The piece does not depend on the order of its endpoints. -/
theorem extGeodesicSegment_comm (p q : ℍ ⊕ OnePoint ℝ) :
    extGeodesicSegment q p = extGeodesicSegment p q := by
  rcases p with z | ξ <;> rcases q with w | η
  · simp only [extGeodesicSegment_inl_inl, geodesicSegment_comm]
  · rfl
  · rfl
  obtain rfl | hξη := eq_or_ne ξ η
  · rfl
  have hg := isGeodesicFromTo_geodesicFromTo (Sum.inr_injective.ne hξη)
  rw [extGeodesicSegment_inr_inr hξη, extGeodesicSegment_inr_inr hξη.symm]
  exact ((isGeodesicFromTo_mul_pslS_iff.2 hg).range_geodesicLine_eq
    (isGeodesicFromTo_geodesicFromTo (Sum.inr_injective.ne hξη.symm))).trans
    (range_geodesicLine_mul_pslS _)

/-- A starting point in `ℍ` lies on the piece. -/
@[simp]
theorem left_mem_extGeodesicSegment (z : ℍ) (q : ℍ ⊕ OnePoint ℝ) :
    z ∈ extGeodesicSegment (.inl z) q := by
  rcases q with w | η
  · exact left_mem_geodesicSegment z w
  · exact ⟨0, Set.mem_Ici.2 le_rfl, geodesicLine_rayToward_zero z _⟩

/-- An end point in `ℍ` lies on the piece. -/
@[simp]
theorem right_mem_extGeodesicSegment (p : ℍ ⊕ OnePoint ℝ) (w : ℍ) :
    w ∈ extGeodesicSegment p (.inl w) := by
  rw [extGeodesicSegment_comm]
  exact left_mem_extGeodesicSegment w p

/-- The piece between `p` and `q` lies on every geodesic line running from `p` to `q`. -/
theorem extGeodesicSegment_subset_range_geodesicLine {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) : extGeodesicSegment p q ⊆ Set.range (geodesicLine g) := by
  rcases p with z | ξ <;> rcases q with w | η
  · rw [extGeodesicSegment_inl_inl,
      (isGeodesicFromTo_geodesicBetween fun h ↦ hg.ne (congrArg _ h)).range_geodesicLine_eq hg]
    exact geodesicSegment_subset_range_geodesicLine z w
  · rw [extGeodesicSegment_inl_inr,
      (isGeodesicFromTo_rayToward Sum.inl_ne_inr).range_geodesicLine_eq hg]
    exact Set.image_subset_range _ _
  · rw [extGeodesicSegment_inr_inl, ← range_geodesicLine_mul_pslS,
      (isGeodesicFromTo_rayToward Sum.inl_ne_inr).range_geodesicLine_eq
        (isGeodesicFromTo_mul_pslS_iff.2 hg)]
    exact Set.image_subset_range _ _
  · have hξη : ξ ≠ η := fun h ↦ hg.ne (congrArg _ h)
    rw [extGeodesicSegment_inr_inr hξη,
      (isGeodesicFromTo_geodesicFromTo (Sum.inr_injective.ne hξη)).range_geodesicLine_eq hg]

/-- Translating a ray from a point of `ℍ` towards an ideal point gives the ray between the
translated points. -/
private theorem smul_image_rayToward (h : PSL(2, ℝ)) (z : ℍ) (ξ : OnePoint ℝ) :
    h • (geodesicLine (rayToward z (.inr ξ)) '' Set.Ici 0) =
      geodesicLine (rayToward (h • z) (.inr (h • ξ))) '' Set.Ici 0 := by
  rw [← Sum.smul_inr, rayToward_smul h Sum.inl_ne_inr, ← Set.image_smul, Set.image_image]
  simp only [smul_geodesicLine]

/-- The piece transforms naturally under the action. -/
@[simp]
theorem smul_extGeodesicSegment (h : PSL(2, ℝ)) (p q : ℍ ⊕ OnePoint ℝ) :
    h • extGeodesicSegment p q = extGeodesicSegment (h • p) (h • q) := by
  rcases p with z | ξ <;> rcases q with w | η <;> simp only [Sum.smul_inl, Sum.smul_inr]
  · rw [extGeodesicSegment_inl_inl, extGeodesicSegment_inl_inl, smul_geodesicSegment]
  · rw [extGeodesicSegment_inl_inr, extGeodesicSegment_inl_inr, smul_image_rayToward]
  · rw [extGeodesicSegment_inr_inl, extGeodesicSegment_inr_inl, smul_image_rayToward]
  obtain rfl | hξη := eq_or_ne ξ η
  · rw [extGeodesicSegment_inr_self, extGeodesicSegment_inr_self, Set.smul_set_empty]
  have hg := isGeodesicFromTo_geodesicFromTo (Sum.inr_injective.ne hξη)
  have hξη' : h • ξ ≠ h • η := (MulAction.injective h).ne hξη
  rw [extGeodesicSegment_inr_inr hξη, extGeodesicSegment_inr_inr hξη',
    smul_range_geodesicLine]
  exact (isGeodesicFromTo_geodesicFromTo (Sum.inr_injective.ne hξη')).range_geodesicLine_eq
    (hg.smul h)

/-! ### Closed half-planes are convex -/

/-- Moving a point of the geodesic line of `g` onto the imaginary axis by `g⁻¹`. -/
private theorem geodesicLine_mem_closure_leftHalfPlane_iff (g k : PSL(2, ℝ)) (t : ℝ) :
    geodesicLine g t ∈ closure (leftHalfPlane k) ↔
      geodesicLine 1 t ∈ closure (leftHalfPlane (g⁻¹ * k)) := by
  rw [← smul_leftHalfPlane, closure_smul, Set.mem_smul_set_iff_inv_smul_mem, inv_inv,
    smul_geodesicLine, mul_one]

/-- Moving an ideal point by `g⁻¹`. -/
private theorem inr_smul_mem_extClosedLeftHalfPlane_iff (g k : PSL(2, ℝ)) (ξ : OnePoint ℝ) :
    Sum.inr (g • ξ) ∈ extClosedLeftHalfPlane k ↔
      Sum.inr ξ ∈ extClosedLeftHalfPlane (g⁻¹ * k) := by
  rw [← smul_extClosedLeftHalfPlane, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Sum.smul_inr]

/-- The side form of the class of `A` along the imaginary axis is `-c d e^{2t} - a b`. -/
private theorem sideForm_mk_geodesicLine_one (A : SL(2, ℝ)) (t : ℝ) :
    sideForm (A : PSL(2, ℝ)) (geodesicLine 1 t) =
      -(A 1 0 * A 1 1) * Real.exp t ^ 2 - A 0 0 * A 0 1 := by
  rw [sideForm_mk, geodesicLine_one_apply, UpperHalfPlane.coe_mk]
  simp only [Complex.normSq_mk]
  ring

/-- If `∞` is weakly to the left of the geodesic line of the class of `A`, then `0 ≤ c d`. -/
private theorem mul_nonneg_of_inr_infty_mem {A : SL(2, ℝ)}
    (h : Sum.inr ∞ ∈ extClosedLeftHalfPlane (A : PSL(2, ℝ))) : 0 ≤ A 1 0 * A 1 1 := by
  rcases inr_mem_extClosedLeftHalfPlane_iff.1 h with h₀ | h₁ | h
  · rw [(mk_smul_zero_eq_infty_iff A).1 h₀.symm, mul_zero]
  · rw [(mk_smul_infty_eq_infty_iff A).1 h₁.symm, zero_mul]
  -- both endpoints are real, `e₀ < e₁`, and `(e₁ - e₀) c d = a d - b c = 1`
  have h₀ : (A : PSL(2, ℝ)) • ((0 : ℝ) : OnePoint ℝ) ≠ ∞ := fun h₀ ↦
    smul_zero_notMem_boundaryLeftHalfPlane _ (by rwa [h₀])
  have h₁ : (A : PSL(2, ℝ)) • (∞ : OnePoint ℝ) ≠ ∞ := fun h₁ ↦
    smul_infty_notMem_boundaryLeftHalfPlane _ (by rwa [h₁])
  obtain ⟨e₀, he₀⟩ := OnePoint.ne_infty_iff_exists.1 h₀
  obtain ⟨e₁, he₁⟩ := OnePoint.ne_infty_iff_exists.1 h₁
  have he := (infty_mem_boundaryLeftHalfPlane_iff he₀.symm he₁.symm).1 h
  have hb := (mk_smul_zero_eq_coe_iff.1 he₀.symm).2
  have ha := (mk_smul_infty_eq_coe_iff.1 he₁.symm).2
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact A.det_coe
  have hcd : (e₁ - e₀) * (A 1 0 * A 1 1) = 1 := by
    linear_combination hdet - A 1 1 * ha + A 1 0 * hb
  exact ((pos_iff_pos_of_mul_pos (hcd.symm ▸ one_pos)).1 (sub_pos.2 he)).le

/-- If `0` is weakly to the left of the geodesic line of the class of `A`, then `0 ≤ a b`. -/
private theorem mul_nonneg_of_inr_zero_mem {A : SL(2, ℝ)}
    (h : Sum.inr ((0 : ℝ) : OnePoint ℝ) ∈ extClosedLeftHalfPlane (A : PSL(2, ℝ))) :
    0 ≤ A 0 0 * A 0 1 := by
  have h₀ := sideForm_toComplex_nonpos_of_mem_extClosedLeftHalfPlane
    (Sum.inr_injective.ne (OnePoint.coe_ne_infty 0)) h
  rw [toComplex_inr_coe, sideForm_mk_ofReal] at h₀
  linarith

/-- A geodesic line whose two ideal endpoints are weakly to the left of `geodesicLine k` lies in
the closed left half-plane of `k`. -/
theorem range_geodesicLine_subset_closure_leftHalfPlane {g k : PSL(2, ℝ)}
    (h₀ : Sum.inr (g • ((0 : ℝ) : OnePoint ℝ)) ∈ extClosedLeftHalfPlane k)
    (h₁ : Sum.inr (g • (∞ : OnePoint ℝ)) ∈ extClosedLeftHalfPlane k) :
    Set.range (geodesicLine g) ⊆ closure (leftHalfPlane k) := by
  rintro _ ⟨t, rfl⟩
  rw [geodesicLine_mem_closure_leftHalfPlane_iff]
  rw [inr_smul_mem_extClosedLeftHalfPlane_iff] at h₀ h₁
  generalize g⁻¹ * k = m at h₀ h₁ ⊢
  induction m using QuotientGroup.induction_on with | H A => ?_
  have hcd := mul_nonneg_of_inr_infty_mem h₁
  have hab := mul_nonneg_of_inr_zero_mem h₀
  rw [mem_closure_leftHalfPlane_iff_sideForm_nonpos, sideForm_mk_geodesicLine_one]
  nlinarith [mul_nonneg hcd (sq_nonneg (Real.exp t))]

/-- A geodesic ray `geodesicLine g '' [0, ∞)` starting in the closed left half-plane of `k`,
whose forward endpoint `g • ∞` is weakly to the left of `geodesicLine k`, lies in the closed
left half-plane of `k`. -/
theorem geodesicLine_image_Ici_subset_closure_leftHalfPlane {g k : PSL(2, ℝ)}
    (h₀ : geodesicLine g 0 ∈ closure (leftHalfPlane k))
    (h₁ : Sum.inr (g • (∞ : OnePoint ℝ)) ∈ extClosedLeftHalfPlane k) :
    geodesicLine g '' Set.Ici 0 ⊆ closure (leftHalfPlane k) := by
  rintro _ ⟨t, ht, rfl⟩
  rw [geodesicLine_mem_closure_leftHalfPlane_iff] at h₀ ⊢
  rw [inr_smul_mem_extClosedLeftHalfPlane_iff] at h₁
  generalize g⁻¹ * k = m at h₀ h₁ ⊢
  induction m using QuotientGroup.induction_on with | H A => ?_
  have hcd := mul_nonneg_of_inr_infty_mem h₁
  rw [mem_closure_leftHalfPlane_iff_sideForm_nonpos, sideForm_mk_geodesicLine_one] at h₀ ⊢
  rw [Real.exp_zero, one_pow] at h₀
  have hexp : 1 ≤ Real.exp t ^ 2 := one_le_pow₀ (Real.one_le_exp ht)
  nlinarith [mul_nonneg hcd (sub_nonneg.2 hexp)]

/-- Closed half-planes are convex: the piece between two points of `ℍ ∪ ∂ℍ` weakly to the left of
`geodesicLine k` lies in the closed left half-plane of `k`. -/
theorem extGeodesicSegment_subset_closure_leftHalfPlane {k : PSL(2, ℝ)}
    {p q : ℍ ⊕ OnePoint ℝ} (hp : p ∈ extClosedLeftHalfPlane k)
    (hq : q ∈ extClosedLeftHalfPlane k) :
    extGeodesicSegment p q ⊆ closure (leftHalfPlane k) := by
  rcases p with z | ξ <;> rcases q with w | η
  · rw [extGeodesicSegment_inl_inl]
    exact geodesicSegment_subset_closure_leftHalfPlane (inl_mem_extClosedLeftHalfPlane_iff.1 hp)
      (inl_mem_extClosedLeftHalfPlane_iff.1 hq)
  · rw [extGeodesicSegment_inl_inr]
    exact geodesicLine_image_Ici_subset_closure_leftHalfPlane
      (by rwa [geodesicLine_rayToward_zero, ← inl_mem_extClosedLeftHalfPlane_iff])
      (by rwa [rayToward_inr_smul_infty])
  · rw [extGeodesicSegment_inr_inl]
    exact geodesicLine_image_Ici_subset_closure_leftHalfPlane
      (by rwa [geodesicLine_rayToward_zero, ← inl_mem_extClosedLeftHalfPlane_iff])
      (by rwa [rayToward_inr_smul_infty])
  obtain rfl | hξη := eq_or_ne ξ η
  · rw [extGeodesicSegment_inr_self]
    exact Set.empty_subset _
  have hg := isGeodesicFromTo_geodesicFromTo (Sum.inr_injective.ne hξη)
  rw [extGeodesicSegment_inr_inr hξη]
  exact range_geodesicLine_subset_closure_leftHalfPlane (by rwa [hg.smul_zero_eq])
    (by rwa [hg.smul_infty_eq])

/-- Away from its finite endpoints, a geodesic piece in a closed half-plane lies in the open
half-plane, provided its supporting line is distinct from the boundary line. This includes
segments, rays and lines with ideal endpoints. -/
theorem mem_leftHalfPlane_of_mem_extGeodesicSegment {g k : PSL(2, ℝ)}
    {p q : ℍ ⊕ OnePoint ℝ} {z : ℍ} (hg : IsGeodesicFromTo g p q)
    (hp : p ∈ extClosedLeftHalfPlane k) (hq : q ∈ extClosedLeftHalfPlane k)
    (hne : Set.range (geodesicLine g) ≠ Set.range (geodesicLine k))
    (hz : z ∈ extGeodesicSegment p q) (hzp : p ≠ .inl z) (hzq : q ≠ .inl z) :
    z ∈ leftHalfPlane k := by
  -- Treat the two orientations of a ray together, then reduce each endpoint configuration
  -- to an interior parameter of an interval in the closed half-plane.
  have ray_case {w : ℍ} {ξ : OnePoint ℝ}
      (hw : w ∈ closure (leftHalfPlane k))
      (hξ : Sum.inr ξ ∈ extClosedLeftHalfPlane k)
      (hr : Set.range (geodesicLine (rayToward w (.inr ξ))) ≠
        Set.range (geodesicLine k))
      (hz : z ∈ geodesicLine (rayToward w (.inr ξ)) '' Set.Ici 0) (hwz : w ≠ z) :
      z ∈ leftHalfPlane k := by
    obtain ⟨t, ht, rfl⟩ := hz
    have htpos : 0 < t := lt_of_le_of_ne ht (by
      intro heq
      apply hwz
      rw [← heq, geodesicLine_rayToward_zero])
    have hstart : geodesicLine (rayToward w (.inr ξ)) 0 ∈ closure (leftHalfPlane k) := by
      rwa [geodesicLine_rayToward_zero]
    have hclosed := geodesicLine_image_Ici_subset_closure_leftHalfPlane hstart
      (by rwa [rayToward_inr_smul_infty])
    exact geodesicLine_mem_leftHalfPlane_of_mem_closure htpos (lt_add_one t)
      hstart (hclosed ⟨t + 1, Set.mem_Ici.2 (by linarith), rfl⟩) hr
  rcases p with v | ξ <;> rcases q with w | η
  · obtain ⟨s, t, hst, rfl, rfl⟩ := isGeodesicFromTo_inl_inl.1 hg
    rw [extGeodesicSegment_inl_inl, geodesicSegment_geodesicLine, Set.uIcc_of_le hst.le] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have hsu : s < u := lt_of_le_of_ne hu.1 (fun heq ↦ hzp (by rw [heq]))
    have hut : u < t := lt_of_le_of_ne hu.2 (fun heq ↦ hzq (by rw [heq]))
    exact geodesicLine_mem_leftHalfPlane_of_mem_closure hsu hut
      (inl_mem_extClosedLeftHalfPlane_iff.1 hp) (inl_mem_extClosedLeftHalfPlane_iff.1 hq) hne
  · rw [extGeodesicSegment_inl_inr] at hz
    apply ray_case (inl_mem_extClosedLeftHalfPlane_iff.1 hp) hq
      (by rwa [← (isGeodesicFromTo_rayToward Sum.inl_ne_inr).range_geodesicLine_eq hg]) hz
    exact fun heq ↦ hzp (congrArg Sum.inl heq)
  · rw [extGeodesicSegment_inr_inl] at hz
    apply ray_case (inl_mem_extClosedLeftHalfPlane_iff.1 hq) hp
      (by rw [← (isGeodesicFromTo_rayToward Sum.inl_ne_inr).range_geodesicLine_eq
          (isGeodesicFromTo_mul_pslS_iff.2 hg), range_geodesicLine_mul_pslS]; exact hne) hz
    exact fun heq ↦ hzq (congrArg Sum.inl heq)
  · -- With two ideal endpoints, the piece is the whole line, so bracket the point by `t ± 1`.
    have hξη : ξ ≠ η := fun heq ↦ hg.ne (congrArg Sum.inr heq)
    have hpiece : extGeodesicSegment (.inr ξ) (.inr η) = Set.range (geodesicLine g) := by
      rw [extGeodesicSegment_inr_inr hξη]
      exact hg.range_geodesicLine_eq (isGeodesicFromTo_geodesicFromTo hg.ne)
    rw [hpiece] at hz
    obtain ⟨t, rfl⟩ := hz
    have hclosed := extGeodesicSegment_subset_closure_leftHalfPlane hp hq
    rw [hpiece] at hclosed
    exact geodesicLine_mem_leftHalfPlane_of_mem_closure (sub_one_lt t) (lt_add_one t)
      (hclosed ⟨t - 1, rfl⟩) (hclosed ⟨t + 1, rfl⟩) hne

end TauCeti.UpperHalfPlane
