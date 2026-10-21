/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Order.Minimal
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Orientation
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.GaussBonnet
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Height
import TauCeti.Topology.Order.Interval

/-!
# Polygons cut out by finitely many half-planes

A finite intersection `K` of closed geodesic half-planes of `ℍ` with nonempty interior is the
carrier of a convex polygon, possibly with ideal vertices, as soon as removing finitely many open
horodiscs from `K` leaves a bounded set
(`exists_convexPolygon_carrier_eq_iInter_closure_leftHalfPlane`). Each side of the polygon lies on
the boundary line of one of the half-planes, with the polygon on the left, and is exactly the face
of `K` along that line; each ideal vertex is the centre of one of the horodiscs. With no horodiscs,
a bounded intersection is a compact convex polygon
(`exists_compactConvexPolygon_carrier_eq_iInter_closure_leftHalfPlane`). This converts finite
half-plane descriptions, such as those of Dirichlet domains truncated at their cusps, into polygons
with enumerated vertices and sides.

## Proof

First discard redundant half-planes: in a minimal subfamily with the same intersection `K`, each
line `L` carries a point strictly inside all the other half-planes, found by crossing `L` on the
segment from an interior point to a point violating only the half-plane of `L`. The face `K ∩ L`
is then an extended geodesic segment with two distinct endpoints in `ℍ ∪ ∂ℍ`, traversed with `K`
on its left. Following faces from their ends to their starts is a permutation of the lines, and
one of its cycles lists the vertices of a convex polygon. Its carrier contains `K` and, by the hull
property `ConvexPolygon.carrier_subset_closure_leftHalfPlane_of_forall`, lies in `K`.

* An end in `ℍ` lies on some other line `L'`, as otherwise `K` would continue along `L`. It is not
  inside the face of `L'`, since `L` would then cross into the open right side of `L'`. It is not
  the end of that face either, since the two faces would then reach it from opposite sides, which
  the signs of the oriented angles there exclude. So it is the start of the face on `L'`.
* At an ideal end, move it to `∞`. Two lines of the family never run to the same ideal point, nor
  from the same ideal point, since each carries a point strictly to the left of the other; one
  line may run to the ideal point another runs from, as two sides meeting at an ideal vertex do.
  As `K` has points arbitrarily high up, every semicircle has `∞` on its left, so a vertical line
  of the family has all its high points in `K`: the vertical constraints only see the real part,
  and the line meets `K`. If no line ran down from `∞`, `K` would contain every point far enough
  to the left, and the points of a small fixed height escaping to the left would leave every
  horodisc while staying in `K`. So some line runs down from `∞`, and its face starts there. If
  no horodisc were centred at `∞`, the points of `K` high up would leave every horodisc in the
  same way.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §9.4 (sides and vertices of convex polygons).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§3.2 and 4.2 (Dirichlet regions and their cusps).
-/

public section

open Set UpperHalfPlane Filter
open scoped MatrixGroups OnePoint Topology Pointwise

namespace TauCeti.UpperHalfPlane

/-! ### Discarding redundant half-planes -/

section Essential

variable {ι : Type*} {t : Finset ι} {L : ι → PSL(2, ℝ)}

/-- A finite family of half-planes containing a common point in all its open half-planes has a
subfamily with the same closed intersection in which every line carries a point strictly inside
all the other half-planes. -/
private theorem exists_subset_iInter_eq_and_essential {p : ℍ}
    (hp : ∀ j ∈ t, p ∈ leftHalfPlane (L j)) :
    ∃ s ⊆ t, ⋂ j ∈ s, closure (leftHalfPlane (L j)) = ⋂ j ∈ t, closure (leftHalfPlane (L j)) ∧
      ∀ k ∈ s, ∃ u : ℝ, ∀ j ∈ s, j ≠ k → geodesicLine (L k) u ∈ leftHalfPlane (L j) := by
  classical
  obtain ⟨s, hst, hs, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun s : Finset ι ↦ ⋂ j ∈ s, closure (leftHalfPlane (L j)) =
      ⋂ j ∈ t, closure (leftHalfPlane (L j))) t rfl
  refine ⟨s, hst, hs, fun k hk ↦ ?_⟩
  -- removing `k` strictly enlarges the intersection, by minimality
  have hsub : ⋂ j ∈ s, closure (leftHalfPlane (L j)) ⊆
      ⋂ j ∈ s.erase k, closure (leftHalfPlane (L j)) :=
    biInter_mono (Finset.erase_subset k s) fun _ _ ↦ Subset.rfl
  obtain ⟨x, hx, hxs⟩ := exists_of_ssubset (hsub.ssubset_of_ne fun heq ↦
    Finset.notMem_erase k s (hmin (heq.symm.trans hs) (Finset.erase_subset k s) hk))
  refine exists_geodesicLine_mem_leftHalfPlane_of_notMem (t := s) (fun j hj ↦ hp j (hst hj)) hk
    (fun j hj hjk ↦ mem_iInter₂.1 hx j (Finset.mem_erase.2 ⟨hjk, hj⟩)) fun hxk ↦ hxs ?_
  refine mem_iInter₂.2 fun j hj ↦ ?_
  by_cases hjk : j = k
  · exact hjk ▸ hxk
  · exact mem_iInter₂.1 hx j (Finset.mem_erase.2 ⟨hjk, hj⟩)

end Essential

/-! ### The endpoints of a face

For a geodesic line `g` and a set `K ⊆ ℍ`, the face of `K` along the line is the set of points
`geodesicLine g t` in `K`. When `K` is an intersection of closed half-planes, its parameters
`geodesicLine g ⁻¹' K` form a closed interval, and the face is an extended geodesic segment between
the two points of `ℍ ∪ ∂ℍ` below. -/

section FaceEndpoints

variable (g : PSL(2, ℝ)) (K : Set ℍ)

open scoped Classical in
/-- The point of `ℍ ∪ ∂ℍ` at which the face of `K` along `geodesicLine g` starts: its point of
least parameter, or the backward endpoint `g • 0` if the parameters are unbounded below. -/
private noncomputable def faceStart : ℍ ⊕ OnePoint ℝ :=
  if BddBelow (geodesicLine g ⁻¹' K) then .inl (geodesicLine g (sInf (geodesicLine g ⁻¹' K)))
  else .inr (g • ((0 : ℝ) : OnePoint ℝ))

open scoped Classical in
/-- The point of `ℍ ∪ ∂ℍ` at which the face of `K` along `geodesicLine g` ends: its point of
greatest parameter, or the forward endpoint `g • ∞` if the parameters are unbounded above. -/
private noncomputable def faceEnd : ℍ ⊕ OnePoint ℝ :=
  if BddAbove (geodesicLine g ⁻¹' K) then .inl (geodesicLine g (sSup (geodesicLine g ⁻¹' K)))
  else .inr (g • (∞ : OnePoint ℝ))

variable {g K}

private theorem faceStart_eq_inl {τ : ℝ} (hτ : geodesicLine g τ ∈ K)
    (hle : ∀ σ, geodesicLine g σ ∈ K → τ ≤ σ) : faceStart g K = .inl (geodesicLine g τ) := by
  have h : IsLeast (geodesicLine g ⁻¹' K) τ := ⟨hτ, hle⟩
  rw [faceStart, ite_eq_left h.bddBelow, h.csInf_eq]

private theorem faceEnd_eq_inl {τ : ℝ} (hτ : geodesicLine g τ ∈ K)
    (hle : ∀ σ, geodesicLine g σ ∈ K → σ ≤ τ) : faceEnd g K = .inl (geodesicLine g τ) := by
  have h : IsGreatest (geodesicLine g ⁻¹' K) τ := ⟨hτ, hle⟩
  rw [faceEnd, ite_eq_left h.bddAbove, h.csSup_eq]

private theorem faceStart_eq_inr (h : ¬BddBelow (geodesicLine g ⁻¹' K)) :
    faceStart g K = .inr (g • ((0 : ℝ) : OnePoint ℝ)) :=
  ite_eq_right h

private theorem faceEnd_eq_inr (h : ¬BddAbove (geodesicLine g ⁻¹' K)) :
    faceEnd g K = .inr (g • (∞ : OnePoint ℝ)) :=
  ite_eq_right h

private theorem exists_of_faceStart_eq_inl (hS : IsClosed (geodesicLine g ⁻¹' K))
    (hne : (geodesicLine g ⁻¹' K).Nonempty) {z : ℍ} (h : faceStart g K = .inl z) :
    ∃ a, geodesicLine g a ∈ K ∧ geodesicLine g a = z ∧ ∀ σ, geodesicLine g σ ∈ K → a ≤ σ := by
  by_cases hb : BddBelow (geodesicLine g ⁻¹' K)
  · rw [faceStart, ite_eq_left hb, Sum.inl.injEq] at h
    exact ⟨_, hS.csInf_mem hne hb, h, fun σ hσ ↦ csInf_le hb hσ⟩
  · rw [faceStart_eq_inr hb] at h
    exact absurd h Sum.inr_ne_inl

private theorem exists_of_faceEnd_eq_inl (hS : IsClosed (geodesicLine g ⁻¹' K))
    (hne : (geodesicLine g ⁻¹' K).Nonempty) {w : ℍ} (h : faceEnd g K = .inl w) :
    ∃ b, geodesicLine g b ∈ K ∧ geodesicLine g b = w ∧ ∀ σ, geodesicLine g σ ∈ K → σ ≤ b := by
  by_cases hb : BddAbove (geodesicLine g ⁻¹' K)
  · rw [faceEnd, ite_eq_left hb, Sum.inl.injEq] at h
    exact ⟨_, hS.csSup_mem hne hb, h, fun σ hσ ↦ le_csSup hb hσ⟩
  · rw [faceEnd_eq_inr hb] at h
    exact absurd h Sum.inr_ne_inl

private theorem of_faceStart_eq_inr {ξ : OnePoint ℝ} (h : faceStart g K = .inr ξ) :
    g • ((0 : ℝ) : OnePoint ℝ) = ξ ∧ ¬BddBelow (geodesicLine g ⁻¹' K) := by
  by_cases hb : BddBelow (geodesicLine g ⁻¹' K)
  · rw [faceStart, ite_eq_left hb] at h
    exact absurd h Sum.inl_ne_inr
  · rw [faceStart_eq_inr hb, Sum.inr.injEq] at h
    exact ⟨h, hb⟩

private theorem of_faceEnd_eq_inr {η : OnePoint ℝ} (h : faceEnd g K = .inr η) :
    g • (∞ : OnePoint ℝ) = η ∧ ¬BddAbove (geodesicLine g ⁻¹' K) := by
  by_cases hb : BddAbove (geodesicLine g ⁻¹' K)
  · rw [faceEnd, ite_eq_left hb] at h
    exact absurd h Sum.inl_ne_inr
  · rw [faceEnd_eq_inr hb, Sum.inr.injEq] at h
    exact ⟨h, hb⟩

/-- A point of a face is its start, its end, or lies strictly between two other points of it. -/
private theorem faceStart_eq_or_faceEnd_eq_or_exists {τ : ℝ} (hτ : geodesicLine g τ ∈ K) :
    faceStart g K = .inl (geodesicLine g τ) ∨ faceEnd g K = .inl (geodesicLine g τ) ∨
      ∃ σ₁ σ₂, σ₁ < τ ∧ τ < σ₂ ∧ geodesicLine g σ₁ ∈ K ∧ geodesicLine g σ₂ ∈ K := by
  by_cases h₁ : ∃ σ₁, σ₁ < τ ∧ geodesicLine g σ₁ ∈ K
  · by_cases h₂ : ∃ σ₂, τ < σ₂ ∧ geodesicLine g σ₂ ∈ K
    · obtain ⟨σ₁, hσ₁, h₁⟩ := h₁
      obtain ⟨σ₂, hσ₂, h₂⟩ := h₂
      exact Or.inr (Or.inr ⟨σ₁, σ₂, hσ₁, hσ₂, h₁, h₂⟩)
    · push Not at h₂
      exact Or.inr (Or.inl (faceEnd_eq_inl hτ fun σ hσ ↦ le_of_not_gt fun h ↦ h₂ σ h hσ))
  · push Not at h₁
    exact Or.inl (faceStart_eq_inl hτ fun σ hσ ↦ le_of_not_gt fun h ↦ h₁ σ h hσ)

/-- A face with two distinct points runs from its start to its end. -/
private theorem isGeodesicFromTo_faceStart_faceEnd {σ₁ σ₂ : ℝ} (h₁ : geodesicLine g σ₁ ∈ K)
    (h₂ : geodesicLine g σ₂ ∈ K) (h₁₂ : σ₁ < σ₂) :
    IsGeodesicFromTo g (faceStart g K) (faceEnd g K) := by
  by_cases hb : BddBelow (geodesicLine g ⁻¹' K) <;> by_cases hb' : BddAbove (geodesicLine g ⁻¹' K)
  · rw [faceStart, ite_eq_left hb, faceEnd, ite_eq_left hb']
    exact isGeodesicFromTo_inl_inl.2
      ⟨_, _, ((csInf_le hb h₁).trans_lt h₁₂).trans_le (le_csSup hb' h₂), rfl, rfl⟩
  · rw [faceStart, ite_eq_left hb, faceEnd_eq_inr hb']
    exact isGeodesicFromTo_inl_inr.2 ⟨mem_range_self _, rfl⟩
  · rw [faceStart_eq_inr hb, faceEnd, ite_eq_left hb']
    exact isGeodesicFromTo_inr_inl.2 ⟨rfl, mem_range_self _⟩
  · rw [faceStart_eq_inr hb, faceEnd_eq_inr hb']
    exact isGeodesicFromTo_inr_inr.2 ⟨rfl, rfl⟩

/-- A nonempty face with closed order-connected parameters is the extended geodesic segment from
its start to its end. -/
private theorem inter_range_eq_extGeodesicSegment (hS : IsClosed (geodesicLine g ⁻¹' K))
    (hoc : (geodesicLine g ⁻¹' K).OrdConnected) (hne : (geodesicLine g ⁻¹' K).Nonempty) :
    K ∩ range (geodesicLine g) = extGeodesicSegment (faceStart g K) (faceEnd g K) := by
  rw [← image_preimage_eq_inter_range]
  by_cases hb : BddBelow (geodesicLine g ⁻¹' K) ∧ BddAbove (geodesicLine g ⁻¹' K)
  · obtain ⟨a, ha⟩ := hne
    rw [faceStart, ite_eq_left hb.1, faceEnd, ite_eq_left hb.2, extGeodesicSegment_inl_inl,
      geodesicSegment_geodesicLine, uIcc_of_le ((csInf_le hb.1 ha).trans (le_csSup hb.2 ha))]
    congr 1
    exact Subset.antisymm (fun σ hσ ↦ ⟨csInf_le hb.1 hσ, le_csSup hb.2 hσ⟩)
      (hoc.out (hS.csInf_mem ⟨a, ha⟩ hb.1) (hS.csSup_mem ⟨a, ha⟩ hb.2))
  rcases hoc.eq_Ici_or_eq_Iic_or_eq_univ hne hS hb with ⟨a, h⟩ | ⟨b, h⟩ | h
  · rw [faceStart, faceEnd, h, ite_eq_left bddBelow_Ici, ite_eq_right (not_bddAbove_Ici a),
      csInf_Ici, geodesicLine_image_Ici]
  · rw [faceStart, faceEnd, h, ite_eq_right (not_bddBelow_Iic b), ite_eq_left bddAbove_Iic,
      csSup_Iic, geodesicLine_image_Iic]
  · rw [faceStart, faceEnd, h, ite_eq_right not_bddBelow_univ, ite_eq_right not_bddAbove_univ,
      image_univ, range_geodesicLine_eq_extGeodesicSegment]

private theorem faceStart_mul_smul (h : PSL(2, ℝ)) :
    faceStart (h * g) (h • K) = h • faceStart g K := by
  have hS : geodesicLine (h * g) ⁻¹' (h • K) = geodesicLine g ⁻¹' K := by
    ext t
    rw [mem_preimage, mem_preimage, ← smul_geodesicLine, smul_mem_smul_set_iff]
  by_cases hb : BddBelow (geodesicLine g ⁻¹' K)
  · rw [faceStart, faceStart, hS, ite_eq_left hb, ite_eq_left hb, Sum.smul_inl,
      smul_geodesicLine]
  · rw [faceStart_eq_inr (hS ▸ hb), faceStart_eq_inr hb, Sum.smul_inr, mul_smul]

private theorem faceEnd_mul_smul (h : PSL(2, ℝ)) :
    faceEnd (h * g) (h • K) = h • faceEnd g K := by
  have hS : geodesicLine (h * g) ⁻¹' (h • K) = geodesicLine g ⁻¹' K := by
    ext t
    rw [mem_preimage, mem_preimage, ← smul_geodesicLine, smul_mem_smul_set_iff]
  by_cases hb : BddAbove (geodesicLine g ⁻¹' K)
  · rw [faceEnd, faceEnd, hS, ite_eq_left hb, ite_eq_left hb, Sum.smul_inl, smul_geodesicLine]
  · rw [faceEnd_eq_inr (hS ▸ hb), faceEnd_eq_inr hb, Sum.smul_inr, mul_smul]

end FaceEndpoints

/-! ### Geodesic lines seen from `∞` -/

section Infinity

/-- Seen from `∞`, a geodesic line is a vertical line running down from `∞` or up to `∞`, or a
semicircle with `∞` on its left, or a semicircle whose right half-plane contains all sufficiently
high points. -/
private theorem smul_eq_infty_or_or_eventually (g : PSL(2, ℝ)) :
    g • ((0 : ℝ) : OnePoint ℝ) = ∞ ∨ g • (∞ : OnePoint ℝ) = ∞ ∨
      (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane g ∨ ∀ᶠ z in atImInfty, z ∈ rightHalfPlane g := by
  by_cases h₀ : g • ((0 : ℝ) : OnePoint ℝ) = ∞
  · exact Or.inl h₀
  by_cases h₁ : g • (∞ : OnePoint ℝ) = ∞
  · exact Or.inr (Or.inl h₁)
  obtain ⟨e₀, he₀⟩ := OnePoint.ne_infty_iff_exists.1 h₀
  obtain ⟨e₁, he₁⟩ := OnePoint.ne_infty_iff_exists.1 h₁
  have hne : e₀ ≠ e₁ := fun h ↦ OnePoint.coe_ne_infty (0 : ℝ)
    (MulAction.injective g (show g • ((0 : ℝ) : OnePoint ℝ) = g • ∞ by rw [← he₀, ← he₁, h]))
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr (Or.inr (Or.inl ((infty_mem_boundaryLeftHalfPlane_iff he₀.symm he₁.symm).2 h)))
  -- reversing the orientation puts `∞` on the left
  refine Or.inr (Or.inr (Or.inr ?_))
  rw [← leftHalfPlane_mul_pslS]
  refine eventually_mem_leftHalfPlane_of_infty_mem_boundaryLeftHalfPlane
    ((infty_mem_boundaryLeftHalfPlane_iff (e₀ := e₁) (e₁ := e₀) ?_ ?_).2 h)
  · rw [mul_smul, pslS_smul_zero, he₁]
  · rw [mul_smul, pslS_smul_infty, he₀]

/-- A geodesic line running up to `∞` is a vertical line with side form `Re z - e`. -/
private theorem exists_sideForm_eq_re_sub {g : PSL(2, ℝ)} (hg : g • (∞ : OnePoint ℝ) = ∞) :
    ∃ e : ℝ, ∀ z : ℂ, sideForm g z = z.re - e := by
  obtain ⟨e, he⟩ := OnePoint.ne_infty_iff_exists.1 fun h₀ : g • ((0 : ℝ) : OnePoint ℝ) = ∞ ↦
    OnePoint.coe_ne_infty (0 : ℝ) (MulAction.injective g (h₀.trans hg.symm))
  exact ⟨e, sideForm_eq_of_smul_infty_eq_infty he.symm hg⟩

/-- A geodesic line running down from `∞` is a vertical line with side form `e - Re z`. -/
private theorem exists_sideForm_eq_sub_re {g : PSL(2, ℝ)}
    (hg : g • ((0 : ℝ) : OnePoint ℝ) = ∞) : ∃ e : ℝ, ∀ z : ℂ, sideForm g z = e - z.re := by
  obtain ⟨e, he⟩ := OnePoint.ne_infty_iff_exists.1 fun h₁ : g • (∞ : OnePoint ℝ) = ∞ ↦
    OnePoint.coe_ne_infty (0 : ℝ) (MulAction.injective g (hg.trans h₁.symm))
  exact ⟨e, sideForm_eq_of_smul_zero_eq_infty hg he.symm⟩

/-- The side form of a vertical geodesic line depends only on the real part. -/
private theorem sideForm_eq_of_re_eq {g : PSL(2, ℝ)}
    (hg : g • ((0 : ℝ) : OnePoint ℝ) = ∞ ∨ g • (∞ : OnePoint ℝ) = ∞) {z w : ℂ}
    (h : z.re = w.re) : sideForm g z = sideForm g w := by
  rcases hg with h₀ | h₁
  · obtain ⟨e, he⟩ := exists_sideForm_eq_sub_re h₀
    rw [he, he, h]
  · obtain ⟨e, he⟩ := exists_sideForm_eq_re_sub h₁
    rw [he, he, h]

/-- The points of a vertical geodesic line have the same real part. -/
private theorem re_eq_of_mem_range {g : PSL(2, ℝ)}
    (hg : g • ((0 : ℝ) : OnePoint ℝ) = ∞ ∨ g • (∞ : OnePoint ℝ) = ∞) {z w : ℍ}
    (hz : z ∈ range (geodesicLine g)) (hw : w ∈ range (geodesicLine g)) : z.re = w.re := by
  rw [mem_range_geodesicLine_iff_sideForm_eq_zero] at hz hw
  rcases hg with h₀ | h₁
  · obtain ⟨e, he⟩ := exists_sideForm_eq_sub_re h₀
    rw [he, coe_re] at hz hw
    linarith
  · obtain ⟨e, he⟩ := exists_sideForm_eq_re_sub h₁
    rw [he, coe_re] at hz hw
    linarith

variable {κ : Type*} {L : κ → PSL(2, ℝ)} {K : Set ℍ}

/-- If an intersection `K` of closed half-planes has points arbitrarily high up, then every
sufficiently high point satisfying the constraints of the vertical lines lies in `K`: the
semicircles all have `∞` on their left. -/
private theorem eventually_mem_of_frequently [Finite κ]
    (hK : K = ⋂ j, closure (leftHalfPlane (L j))) (hfreq : ∃ᶠ z in atImInfty, z ∈ K) :
    ∀ᶠ z : ℍ in atImInfty, (∀ m, (L m • ((0 : ℝ) : OnePoint ℝ) = ∞ ∨
      L m • (∞ : OnePoint ℝ) = ∞) → sideForm (L m) z ≤ 0) → z ∈ K := by
  have hm (m : κ) : ∀ᶠ z : ℍ in atImInfty, ((L m • ((0 : ℝ) : OnePoint ℝ) = ∞ ∨
      L m • (∞ : OnePoint ℝ) = ∞) → sideForm (L m) z ≤ 0) →
        z ∈ closure (leftHalfPlane (L m)) := by
    rcases smul_eq_infty_or_or_eventually (L m) with h | h | h | h
    · exact Eventually.of_forall fun z hz ↦
        (mem_closure_leftHalfPlane_iff_sideForm_nonpos _ _).2 (hz (Or.inl h))
    · exact Eventually.of_forall fun z hz ↦
        (mem_closure_leftHalfPlane_iff_sideForm_nonpos _ _).2 (hz (Or.inr h))
    · filter_upwards [eventually_mem_leftHalfPlane_of_infty_mem_boundaryLeftHalfPlane h]
        with z hz _ using subset_closure hz
    · -- a semicircle with the high points on its right would exclude them from `K`
      exfalso
      obtain ⟨z, hzK, hzr⟩ := (hfreq.and_eventually h).exists
      rw [hK] at hzK
      exact (disjoint_rightHalfPlane_closure_leftHalfPlane _).le_bot ⟨hzr, mem_iInter.1 hzK m⟩
  filter_upwards [eventually_all.2 hm] with z hz hv
  rw [hK, mem_iInter]
  exact fun m ↦ hz m (hv m)

/-- If `K` has points arbitrarily high up, then a vertical line of one of its half-planes, meeting
`K`, has all its sufficiently high points in `K`. -/
private theorem eventually_map_geodesicLine_mem [Finite κ]
    (hK : K = ⋂ j, closure (leftHalfPlane (L j))) (hfreq : ∃ᶠ z in atImInfty, z ∈ K) {k : κ}
    (hk : L k • ((0 : ℝ) : OnePoint ℝ) = ∞ ∨ L k • (∞ : OnePoint ℝ) = ∞) {z₀ : ℍ}
    (hz₀ : z₀ ∈ K) (hz₀k : z₀ ∈ range (geodesicLine (L k))) :
    ∀ᶠ z in atImInfty, z ∈ range (geodesicLine (L k)) → z ∈ K := by
  filter_upwards [eventually_mem_of_frequently hK hfreq] with z hz hzk
  refine hz fun m hm ↦ ?_
  have hz₀m : z₀ ∈ closure (leftHalfPlane (L m)) := by
    rw [hK] at hz₀
    exact mem_iInter.1 hz₀ m
  rw [mem_closure_leftHalfPlane_iff_sideForm_nonpos] at hz₀m
  rwa [sideForm_eq_of_re_eq (w := z₀) hm
    (by rw [coe_re, coe_re]; exact re_eq_of_mem_range hk hzk hz₀k)]

variable {ι : Type*} [Finite ι]

/-- An intersection `K` of closed half-planes with points arbitrarily high up, none of whose lines
runs down from `∞`, does not stay bounded after removing finitely many horodiscs: it contains
every point far enough to the left, and the points of a small fixed height escape the horodiscs
towards the left. -/
private theorem false_of_forall_smul_zero_ne_infty [Finite κ]
    (hK : K = ⋂ j, closure (leftHalfPlane (L j))) (hfreq : ∃ᶠ z in atImInfty, z ∈ K)
    (hdown : ∀ m, L m • ((0 : ℝ) : OnePoint ℝ) ≠ ∞) (g : ι → PSL(2, ℝ)) {A : ι → ℝ}
    (hA : ∀ i, 0 < A i) (hb : Bornology.IsBounded (K \ ⋃ i, {z : ℍ | A i < (g i • z).im})) :
    False := by
  -- every point sufficiently far to the left lies in `K`
  have hleft (m : κ) : ∀ᶠ x in atBot, ∀ z : ℍ, z.re ≤ x →
      z ∈ closure (leftHalfPlane (L m)) := by
    rcases smul_eq_infty_or_or_eventually (L m) with h | h | h | h
    · exact absurd h (hdown m)
    · obtain ⟨e, he⟩ := OnePoint.ne_infty_iff_exists.1 (hdown m)
      filter_upwards [eventually_le_atBot e] with x hx z hz
      rw [mem_closure_leftHalfPlane_iff_sideForm_nonpos,
        sideForm_eq_of_smul_infty_eq_infty he.symm h, coe_re]
      linarith
    · obtain ⟨c, ρ, κ', hρ, hκ', hform⟩ := exists_sideForm_eq_of_infty_mem_boundaryLeftHalfPlane h
      filter_upwards [eventually_le_atBot (c - ρ)] with x hx z hz
      rw [mem_closure_leftHalfPlane_iff_sideForm_nonpos, hform]
      have hρz : ρ ^ 2 ≤ Complex.normSq ((z : ℂ) - c) := by
        rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, coe_re, Complex.ofReal_re,
          Complex.ofReal_im]
        nlinarith [mul_self_nonneg ((z : ℂ).im - 0)]
      exact mul_nonpos_of_nonneg_of_nonpos hκ'.le (by linarith)
    · exfalso
      obtain ⟨z, hzK, hzr⟩ := (hfreq.and_eventually h).exists
      rw [hK] at hzK
      exact (disjoint_rightHalfPlane_closure_leftHalfPlane _).le_bot ⟨hzr, mem_iInter.1 hzK m⟩
  have hcore : ∀ᶠ x in atBot, ∀ z : ℍ, z.re ≤ x → z ∈ K := by
    filter_upwards [eventually_all.2 hleft] with x hx z hz
    rw [hK, mem_iInter]
    exact fun m ↦ hx m z hz
  -- a common small height at which the points far to the left avoid every horodisc
  choose b hb₀ hbA using fun i ↦ exists_pos_eventually_im_smul_le (g i) (hA i)
  obtain ⟨h, hhb, hh⟩ := ((eventually_all.2 fun i ↦ Ioo_mem_nhdsGT (hb₀ i)).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hout : ∀ᶠ x in atBot, ∀ i, ∀ z : ℍ, z.re = x → z.im = h → (g i • z).im ≤ A i :=
    eventually_all.2 fun i ↦ hbA i h (hhb i).2.le
  obtain ⟨X, hX⟩ := eventually_atBot.1 (hcore.and hout)
  -- the points `x + h i` for `x ≤ X` lie in the bounded truncation, a contradiction
  refine not_isBounded_of_forall_re_le (S := K \ ⋃ i, {z : ℍ | A i < (g i • z).im}) hh
    (fun z hzX hzh ↦ ⟨(hX _ hzX).1 z le_rfl, ?_⟩) hb
  simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt]
  exact fun i ↦ (hX _ hzX).2 i z rfl hzh

end Infinity


/-! ### The faces of an irredundant intersection

Throughout, `K` is the intersection of the closed left half-planes of finitely many geodesic lines
`L k`, and each line `L k` carries the point `geodesicLine (L k) (u k)` strictly inside all the
other half-planes. -/

section Faces

variable {κ : Type*} {L : κ → PSL(2, ℝ)} {K : Set ℍ} {u : κ → ℝ}

/-- A point of `K` lies in each of the closed half-planes. -/
private theorem mem_closure_leftHalfPlane_of_mem (hK : K = ⋂ j, closure (leftHalfPlane (L j)))
    {z : ℍ} (hz : z ∈ K) (k : κ) : z ∈ closure (leftHalfPlane (L k)) := by
  rw [hK] at hz
  exact mem_iInter.1 hz k

/-- A point of the line of `L k` strictly inside all the other half-planes lies in `K`, together
with the points of the line near it. -/
private theorem exists_pos_ball_subset [Finite κ] (hK : K = ⋂ j, closure (leftHalfPlane (L j)))
    {k : κ} {v : ℝ} (hv : ∀ j, j ≠ k → geodesicLine (L k) v ∈ leftHalfPlane (L j)) :
    ∃ ε > 0, ∀ τ ∈ Metric.ball v ε, geodesicLine (L k) τ ∈ K := by
  have hU : IsOpen (geodesicLine (L k) ⁻¹' ⋂ j, ⋂ (_ : j ≠ k), leftHalfPlane (L j)) :=
    (isOpen_iInter_of_finite fun _ ↦ isOpen_iInter_of_finite fun _ ↦
      isOpen_leftHalfPlane _).preimage (isometry_geodesicLine _).continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU v (mem_iInter₂.2 hv)
  refine ⟨ε, hε, fun τ hτ ↦ ?_⟩
  -- on the line, the half-plane of `L k` itself holds automatically
  rw [hK, mem_iInter]
  intro j
  by_cases hjk : j = k
  · rw [hjk, closure_leftHalfPlane]
    exact Or.inr (mem_range_self τ)
  · exact subset_closure (mem_iInter₂.1 (hball hτ) j hjk)

variable (hK : K = ⋂ j, closure (leftHalfPlane (L j)))
  (hu : ∀ k j, j ≠ k → geodesicLine (L k) (u k) ∈ leftHalfPlane (L j))

include hK in
private theorem isClosed_preimage_geodesicLine (k : κ) : IsClosed (geodesicLine (L k) ⁻¹' K) :=
  (hK ▸ isClosed_iInter fun _ ↦ isClosed_closure).preimage (isometry_geodesicLine _).continuous

include hK in
private theorem ordConnected_preimage_geodesicLine (k : κ) :
    (geodesicLine (L k) ⁻¹' K).OrdConnected := by
  simp only [hK, preimage_iInter]
  exact ordConnected_iInter fun j ↦ ordConnected_preimage_geodesicLine_closure_leftHalfPlane _ _

include hu in
/-- Distinct indices have distinct lines. -/
private theorem range_geodesicLine_ne {j k : κ} (hjk : j ≠ k) :
    range (geodesicLine (L j)) ≠ range (geodesicLine (L k)) := fun h ↦
  notMem_range_geodesicLine_of_mem_leftHalfPlane (hu k j hjk) (by rw [h]; exact mem_range_self _)

include hK hu in
/-- Each face contains two points. -/
private theorem exists_lt_and_mem [Finite κ] (k : κ) :
    ∃ σ₁ σ₂, σ₁ < σ₂ ∧ geodesicLine (L k) σ₁ ∈ K ∧ geodesicLine (L k) σ₂ ∈ K := by
  obtain ⟨ε, hε, hball⟩ := exists_pos_ball_subset hK (hu k)
  refine ⟨u k, u k + ε / 2, by linarith, hball _ (Metric.mem_ball_self hε), hball _ ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
  exact half_lt_self hε

include hK hu in
private theorem isGeodesicFromTo_face [Finite κ] (k : κ) :
    IsGeodesicFromTo (L k) (faceStart (L k) K) (faceEnd (L k) K) := by
  obtain ⟨σ₁, σ₂, h, h₁, h₂⟩ := exists_lt_and_mem hK hu k
  exact isGeodesicFromTo_faceStart_faceEnd h₁ h₂ h

include hK hu in
private theorem inter_range_eq_face [Finite κ] (k : κ) :
    K ∩ range (geodesicLine (L k)) = extGeodesicSegment (faceStart (L k) K) (faceEnd (L k) K) :=
  inter_range_eq_extGeodesicSegment (isClosed_preimage_geodesicLine hK k)
    (ordConnected_preimage_geodesicLine hK k)
    ⟨u k, (exists_pos_ball_subset hK (hu k)).choose_spec.2 _
      (Metric.mem_ball_self (exists_pos_ball_subset hK (hu k)).choose_spec.1)⟩

include hK hu in
private theorem nonempty_preimage_geodesicLine [Finite κ] (k : κ) :
    (geodesicLine (L k) ⁻¹' K).Nonempty :=
  let ⟨σ₁, _, _, h₁, _⟩ := exists_lt_and_mem hK hu k
  ⟨σ₁, h₁⟩

include hK hu in
/-- A finite end of a face is preceded by another point of the face. -/
private theorem exists_lt_of_faceEnd_eq_inl [Finite κ] {k : κ} {w : ℍ}
    (h : faceEnd (L k) K = .inl w) :
    ∃ s b, s < b ∧ geodesicLine (L k) s ∈ K ∧ geodesicLine (L k) b ∈ K ∧
      geodesicLine (L k) b = w ∧ ∀ σ, geodesicLine (L k) σ ∈ K → σ ≤ b := by
  obtain ⟨b, hbK, hb, hle⟩ := exists_of_faceEnd_eq_inl (isClosed_preimage_geodesicLine hK k)
    (nonempty_preimage_geodesicLine hK hu k) h
  obtain ⟨σ₁, σ₂, h₁₂, h₁, h₂⟩ := exists_lt_and_mem hK hu k
  exact ⟨σ₁, b, h₁₂.trans_le (hle σ₂ h₂), h₁, hbK, hb, hle⟩

include hK hu in
/-- A finite start of a face is followed by another point of the face. -/
private theorem exists_lt_of_faceStart_eq_inl [Finite κ] {k : κ} {z : ℍ}
    (h : faceStart (L k) K = .inl z) :
    ∃ a t, a < t ∧ geodesicLine (L k) t ∈ K ∧ geodesicLine (L k) a ∈ K ∧
      geodesicLine (L k) a = z ∧ ∀ σ, geodesicLine (L k) σ ∈ K → a ≤ σ := by
  obtain ⟨a, haK, ha, hle⟩ := exists_of_faceStart_eq_inl (isClosed_preimage_geodesicLine hK k)
    (nonempty_preimage_geodesicLine hK hu k) h
  obtain ⟨σ₁, σ₂, h₁₂, h₁, h₂⟩ := exists_lt_and_mem hK hu k
  exact ⟨a, σ₂, (hle σ₁ h₁).trans_lt h₁₂, h₂, haK, ha, hle⟩

include hK hu in
/-- A point of `K` on the line `L j` lies strictly to the left of another line `L k` meeting `L j`
at a different point. -/
private theorem mem_leftHalfPlane_of_mem_of_ne {j k : κ} (hjk : j ≠ k) {z w : ℍ} (hz : z ∈ K)
    (hzj : z ∈ range (geodesicLine (L j))) (hwj : w ∈ range (geodesicLine (L j)))
    (hwk : w ∈ range (geodesicLine (L k))) (hzw : z ≠ w) : z ∈ leftHalfPlane (L k) := by
  have hz' := mem_closure_leftHalfPlane_of_mem hK hz k
  rw [closure_leftHalfPlane] at hz'
  exact hz'.resolve_right fun hzk ↦
    range_geodesicLine_ne hu hjk (range_geodesicLine_eq_of_mem hzw hzj hwj hzk hwk)

include hK hu in
/-- The relative interior of a face does not meet another line. -/
private theorem geodesicLine_notMem_range_of_lt_of_lt {j k : κ} (hjk : j ≠ k) {σ₁ τ σ₂ : ℝ}
    (h₁ : σ₁ < τ) (h₂ : τ < σ₂) (hσ₁ : geodesicLine (L j) σ₁ ∈ K)
    (hσ₂ : geodesicLine (L j) σ₂ ∈ K) : geodesicLine (L j) τ ∉ range (geodesicLine (L k)) :=
  notMem_range_geodesicLine_of_mem_leftHalfPlane
    (geodesicLine_mem_leftHalfPlane_of_mem_closure h₁ h₂ (mem_closure_leftHalfPlane_of_mem hK hσ₁ k)
      (mem_closure_leftHalfPlane_of_mem hK hσ₂ k) (range_geodesicLine_ne hu hjk))

include hK hu in
/-- A point of `K` on two of the lines is an endpoint of the face of each. -/
private theorem faceStart_eq_or_faceEnd_eq_of_mem_range {j k : κ} (hjk : j ≠ k) {z : ℍ}
    (hz : z ∈ K) (hzj : z ∈ range (geodesicLine (L j))) (hzk : z ∈ range (geodesicLine (L k))) :
    faceStart (L j) K = .inl z ∨ faceEnd (L j) K = .inl z := by
  obtain ⟨τ, rfl⟩ := hzj
  rcases faceStart_eq_or_faceEnd_eq_or_exists hz with h | h | ⟨σ₁, σ₂, h₁, h₂, hσ₁, hσ₂⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hzk (geodesicLine_notMem_range_of_lt_of_lt hK hu hjk h₁ h₂ hσ₁ hσ₂)

include hK hu in
/-- The finite end of a face lies on another line: otherwise `K` would continue along the line
beyond it. -/
private theorem exists_ne_mem_range_of_faceEnd_eq_inl [Finite κ] {k : κ} {w : ℍ}
    (h : faceEnd (L k) K = .inl w) : ∃ j, j ≠ k ∧ w ∈ range (geodesicLine (L j)) := by
  obtain ⟨-, b, -, -, hb, rfl, hle⟩ := exists_lt_of_faceEnd_eq_inl hK hu h
  by_contra! hno
  -- otherwise the end is strictly inside the other half-planes, so `K` continues
  have hv : ∀ j, j ≠ k → geodesicLine (L k) b ∈ leftHalfPlane (L j) := fun j hjk ↦ by
    have h' := mem_closure_leftHalfPlane_of_mem hK hb j
    rw [closure_leftHalfPlane] at h'
    exact h'.resolve_right (hno j hjk)
  obtain ⟨ε, hε, hball⟩ := exists_pos_ball_subset hK hv
  have := hle (b + ε / 2) (hball _ (by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    exact half_lt_self hε))
  linarith

include hK hu in
/-- Two faces do not end at the same point of `ℍ`. -/
private theorem eq_of_faceEnd_eq_inl [Finite κ] {j k : κ} {w : ℍ} (hj : faceEnd (L j) K = .inl w)
    (hk : faceEnd (L k) K = .inl w) : j = k := by
  by_contra hjk
  obtain ⟨sj, bj, hsbj, hsj, -, hbj, -⟩ := exists_lt_of_faceEnd_eq_inl hK hu hj
  obtain ⟨sk, bk, hsbk, hsk, -, hbk, -⟩ := exists_lt_of_faceEnd_eq_inl hK hu hk
  have hv : geodesicLine (L j) bj = geodesicLine (L k) bk := hbj.trans hbk.symm
  have hkab : geodesicLine (L k) sk ≠ geodesicLine (L k) bk :=
    (geodesicLine_injective _).ne hsbk.ne
  have hjab : geodesicLine (L j) sj ≠ geodesicLine (L j) bj :=
    (geodesicLine_injective _).ne hsbj.ne
  have hx := mem_leftHalfPlane_of_mem_of_ne hK hu (Ne.symm hjk) hsk (mem_range_self _)
    (mem_range_self bk) ⟨bj, hv⟩ hkab
  have hy := mem_leftHalfPlane_of_mem_of_ne hK hu hjk hsj (mem_range_self _)
    (mem_range_self bj) ⟨bk, hv.symm⟩ hjab
  -- both faces arrive at the common point, so each is on the right of the other seen from it
  rw [← leftHalfPlane_geodesicBetween_geodesicLine_of_lt _ hsbk,
    leftHalfPlane_geodesicBetween_swap hkab.symm] at hy
  rw [← leftHalfPlane_geodesicBetween_geodesicLine_of_lt _ hsbj,
    leftHalfPlane_geodesicBetween_swap hjab.symm, hv] at hx
  exact notMem_rightHalfPlane_geodesicBetween_of_mem_rightHalfPlane hkab.symm (hv ▸ hjab.symm) hy
    hx

include hK hu in
/-- Two faces do not start at the same point of `ℍ`. -/
private theorem eq_of_faceStart_eq_inl [Finite κ] {j k : κ} {z : ℍ}
    (hj : faceStart (L j) K = .inl z) (hk : faceStart (L k) K = .inl z) : j = k := by
  by_contra hjk
  obtain ⟨aj, tj, hatj, htj, -, haj, -⟩ := exists_lt_of_faceStart_eq_inl hK hu hj
  obtain ⟨ak, tk, hatk, htk, -, hak, -⟩ := exists_lt_of_faceStart_eq_inl hK hu hk
  have hv : geodesicLine (L j) aj = geodesicLine (L k) ak := haj.trans hak.symm
  have hkab : geodesicLine (L k) ak ≠ geodesicLine (L k) tk :=
    (geodesicLine_injective _).ne hatk.ne
  have hjab : geodesicLine (L j) aj ≠ geodesicLine (L j) tj :=
    (geodesicLine_injective _).ne hatj.ne
  have hx := mem_leftHalfPlane_of_mem_of_ne hK hu (Ne.symm hjk) htk (mem_range_self _)
    (mem_range_self ak) ⟨aj, hv⟩ hkab.symm
  have hy := mem_leftHalfPlane_of_mem_of_ne hK hu hjk htj (mem_range_self _)
    (mem_range_self aj) ⟨ak, hv.symm⟩ hjab.symm
  -- both faces leave the common point, so each is on the left of the other seen from it
  rw [← leftHalfPlane_geodesicBetween_geodesicLine_of_lt _ hatk] at hy
  rw [← leftHalfPlane_geodesicBetween_geodesicLine_of_lt _ hatj, hv] at hx
  exact notMem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane hkab (hv ▸ hjab) hy hx

include hK hu in
/-- The finite end of each face is the start of the face of another line. -/
private theorem exists_ne_faceStart_eq_of_faceEnd_eq_inl [Finite κ] {k : κ} {w : ℍ}
    (h : faceEnd (L k) K = .inl w) : ∃ j, j ≠ k ∧ faceStart (L j) K = .inl w := by
  obtain ⟨j, hjk, hwj⟩ := exists_ne_mem_range_of_faceEnd_eq_inl hK hu h
  obtain ⟨-, b, -, -, hb, rfl, -⟩ := exists_lt_of_faceEnd_eq_inl hK hu h
  rcases faceStart_eq_or_faceEnd_eq_of_mem_range hK hu hjk hb hwj (mem_range_self b) with h' | h'
  · exact ⟨j, hjk, h'⟩
  · exact absurd (eq_of_faceEnd_eq_inl hK hu h' h) hjk

include hK hu in
/-- A finite start of a face lies strictly to the left of every other line, unless it is an
endpoint of that line's face. -/
private theorem mem_extLeftHalfPlane_or_of_faceStart_eq_inl [Finite κ] {j k : κ} (hjk : j ≠ k)
    {z : ℍ} (h : faceStart (L j) K = .inl z) :
    Sum.inl z ∈ extLeftHalfPlane (L k) ∨ faceStart (L k) K = .inl z ∨
      faceEnd (L k) K = .inl z := by
  obtain ⟨a, -, -, -, ha, rfl, -⟩ := exists_lt_of_faceStart_eq_inl hK hu h
  have h' := mem_closure_leftHalfPlane_of_mem hK ha k
  rw [closure_leftHalfPlane] at h'
  rcases h' with h' | h'
  · exact Or.inl (inl_mem_extLeftHalfPlane_iff.2 h')
  · exact Or.inr (faceStart_eq_or_faceEnd_eq_of_mem_range hK hu (Ne.symm hjk) ha h'
      (mem_range_self a))

/-! #### Ideal endpoints -/

include hK hu in
private theorem geodesicLine_mem [Finite κ] (k : κ) : geodesicLine (L k) (u k) ∈ K :=
  (exists_pos_ball_subset hK (hu k)).choose_spec.2 _
    (Metric.mem_ball_self (exists_pos_ball_subset hK (hu k)).choose_spec.1)

include hK hu in
/-- A face ending at `∞` gives points of `K` arbitrarily high up. -/
private theorem frequently_mem_of_faceEnd_eq [Finite κ] {k : κ}
    (h : faceEnd (L k) K = .inr ∞) : ∃ᶠ z in atImInfty, z ∈ K := by
  obtain ⟨hk, hb⟩ := of_faceEnd_eq_inr h
  refine (tendsto_geodesicLine_atTop_atImInfty hk).frequently (Eventually.frequently
    (eventually_atTop.2 ⟨u k, fun t ht ↦ ?_⟩))
  obtain ⟨σ, hσ, htσ⟩ := not_bddAbove_iff.1 hb t
  exact (ordConnected_preimage_geodesicLine hK k).out (geodesicLine_mem hK hu k) hσ ⟨ht, htσ.le⟩

include hK hu in
/-- A face starting at `∞` gives points of `K` arbitrarily high up. -/
private theorem frequently_mem_of_faceStart_eq [Finite κ] {k : κ}
    (h : faceStart (L k) K = .inr ∞) : ∃ᶠ z in atImInfty, z ∈ K := by
  obtain ⟨hk, hb⟩ := of_faceStart_eq_inr h
  refine (tendsto_geodesicLine_atBot_atImInfty hk).frequently (Eventually.frequently
    (eventually_atBot.2 ⟨u k, fun t ht ↦ ?_⟩))
  obtain ⟨σ, hσ, hσt⟩ := not_bddBelow_iff.1 hb t
  exact (ordConnected_preimage_geodesicLine hK k).out hσ (geodesicLine_mem hK hu k) ⟨hσt.le, ht⟩

include hK hu in
/-- If `K` has points arbitrarily high up, the face of a line running up to `∞` ends there. -/
private theorem faceEnd_eq_inr_of_frequently [Finite κ] (hfreq : ∃ᶠ z in atImInfty, z ∈ K)
    {k : κ} (hk : L k • (∞ : OnePoint ℝ) = ∞) : faceEnd (L k) K = .inr ∞ := by
  obtain ⟨a, ha⟩ := eventually_atTop.1 ((tendsto_geodesicLine_atTop_atImInfty hk).eventually
    (eventually_map_geodesicLine_mem hK hfreq (Or.inr hk) (geodesicLine_mem hK hu k)
      (mem_range_self _)))
  rw [faceEnd_eq_inr fun hbdd ↦
    not_bddAbove_Ici a (hbdd.mono fun t ht ↦ ha t ht (mem_range_self t)), hk]

include hK hu in
/-- If `K` has points arbitrarily high up, the face of a line running down from `∞` starts
there. -/
private theorem faceStart_eq_inr_of_frequently [Finite κ] (hfreq : ∃ᶠ z in atImInfty, z ∈ K)
    {k : κ} (hk : L k • ((0 : ℝ) : OnePoint ℝ) = ∞) : faceStart (L k) K = .inr ∞ := by
  obtain ⟨a, ha⟩ := eventually_atBot.1 ((tendsto_geodesicLine_atBot_atImInfty hk).eventually
    (eventually_map_geodesicLine_mem hK hfreq (Or.inl hk) (geodesicLine_mem hK hu k)
      (mem_range_self _)))
  rw [faceStart_eq_inr fun hbdd ↦
    not_bddBelow_Iic a (hbdd.mono fun t ht ↦ ha t ht (mem_range_self t)), hk]

include hu in
/-- Two different lines do not both run up to `∞`: each would carry a point strictly to the
left of the other. -/
private theorem eq_of_smul_infty_eq_infty {j k : κ} (hj : L j • (∞ : OnePoint ℝ) = ∞)
    (hk : L k • (∞ : OnePoint ℝ) = ∞) : j = k := by
  by_contra hjk
  obtain ⟨ej, hej⟩ := exists_sideForm_eq_re_sub hj
  obtain ⟨ek, hek⟩ := exists_sideForm_eq_re_sub hk
  have h₁ := (mem_leftHalfPlane_iff_sideForm_neg _ _).1 (hu k j hjk)
  have h₂ := (mem_leftHalfPlane_iff_sideForm_neg _ _).1 (hu j k (Ne.symm hjk))
  have h₃ := (mem_range_geodesicLine_iff_sideForm_eq_zero _ _).1
    (mem_range_self (f := geodesicLine (L k)) (u k))
  have h₄ := (mem_range_geodesicLine_iff_sideForm_eq_zero _ _).1
    (mem_range_self (f := geodesicLine (L j)) (u j))
  rw [hej] at h₁ h₄
  rw [hek] at h₂ h₃
  linarith

include hu in
/-- Two different lines do not both run down from `∞`. -/
private theorem eq_of_smul_zero_eq_infty {j k : κ} (hj : L j • ((0 : ℝ) : OnePoint ℝ) = ∞)
    (hk : L k • ((0 : ℝ) : OnePoint ℝ) = ∞) : j = k := by
  by_contra hjk
  obtain ⟨ej, hej⟩ := exists_sideForm_eq_sub_re hj
  obtain ⟨ek, hek⟩ := exists_sideForm_eq_sub_re hk
  have h₁ := (mem_leftHalfPlane_iff_sideForm_neg _ _).1 (hu k j hjk)
  have h₂ := (mem_leftHalfPlane_iff_sideForm_neg _ _).1 (hu j k (Ne.symm hjk))
  have h₃ := (mem_range_geodesicLine_iff_sideForm_eq_zero _ _).1
    (mem_range_self (f := geodesicLine (L k)) (u k))
  have h₄ := (mem_range_geodesicLine_iff_sideForm_eq_zero _ _).1
    (mem_range_self (f := geodesicLine (L j)) (u j))
  rw [hej] at h₁ h₄
  rw [hek] at h₂ h₃
  linarith

include hK hu in
/-- A face starting at `∞` has `∞` strictly to the left of every other line, unless `∞` is an
endpoint of that line's face. -/
private theorem mem_extLeftHalfPlane_or_of_faceStart_eq_infty [Finite κ] {j k : κ} (hjk : j ≠ k)
    (h : faceStart (L j) K = .inr ∞) :
    Sum.inr ∞ ∈ extLeftHalfPlane (L k) ∨ faceStart (L k) K = .inr ∞ ∨
      faceEnd (L k) K = .inr ∞ := by
  have hfreq := frequently_mem_of_faceStart_eq hK hu h
  rcases smul_eq_infty_or_or_eventually (L k) with hk | hk | hk | hk
  · exact absurd (eq_of_smul_zero_eq_infty hu (of_faceStart_eq_inr h).1 hk) hjk
  · exact Or.inr (Or.inr (faceEnd_eq_inr_of_frequently hK hu hfreq hk))
  · exact Or.inl (inr_mem_extLeftHalfPlane_iff.2 hk)
  · obtain ⟨z, hzK, hzr⟩ := (hfreq.and_eventually hk).exists
    exact ((disjoint_rightHalfPlane_closure_leftHalfPlane _).le_bot
      ⟨hzr, mem_closure_leftHalfPlane_of_mem hK hzK k⟩).elim

variable {ι : Type*} [Finite ι]

include hK hu in
/-- If `K` stays bounded after removing finitely many horodiscs, a face ending at `∞` is followed
by a face starting there. -/
private theorem exists_faceStart_eq_of_faceEnd_eq_infty [Finite κ] {k : κ}
    (h : faceEnd (L k) K = .inr ∞) (g : ι → PSL(2, ℝ)) {A : ι → ℝ} (hA : ∀ i, 0 < A i)
    (hb : Bornology.IsBounded (K \ ⋃ i, {z : ℍ | A i < (g i • z).im})) :
    ∃ j, faceStart (L j) K = .inr ∞ := by
  have hfreq := frequently_mem_of_faceEnd_eq hK hu h
  by_cases hdown : ∃ m, L m • ((0 : ℝ) : OnePoint ℝ) = ∞
  · obtain ⟨m, hm⟩ := hdown
    exact ⟨m, faceStart_eq_inr_of_frequently hK hu hfreq hm⟩
  · push Not at hdown
    exact (false_of_forall_smul_zero_ne_infty hK hfreq hdown g hA hb).elim

/-! #### Moving an ideal endpoint to `∞` -/

include hK in
private theorem smul_eq_iInter_closure_leftHalfPlane (h : PSL(2, ℝ)) :
    h • K = ⋂ j, closure (leftHalfPlane (h * L j)) := by
  rw [hK, smul_set_iInter]
  simp_rw [← closure_smul, smul_leftHalfPlane]

include hu in
private theorem geodesicLine_mul_mem_leftHalfPlane (h : PSL(2, ℝ)) (k j : κ) (hjk : j ≠ k) :
    geodesicLine (h * L k) (u k) ∈ leftHalfPlane (h * L j) := by
  rw [← smul_geodesicLine, ← smul_leftHalfPlane]
  exact smul_mem_smul_set (hu k j hjk)

include hu in
/-- Two different lines do not run to the same ideal point. -/
private theorem eq_of_smul_infty_eq {j k : κ} (h : L j • (∞ : OnePoint ℝ) = L k • ∞) : j = k := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ℝ) (L j • (∞ : OnePoint ℝ)) ∞
  exact eq_of_smul_infty_eq_infty (L := fun i ↦ g * L i) (geodesicLine_mul_mem_leftHalfPlane hu g)
    (by rw [mul_smul, hg]) (by rw [mul_smul, ← h, hg])

include hu in
/-- Two different lines do not run from the same ideal point. -/
private theorem eq_of_smul_zero_eq {j k : κ}
    (h : L j • ((0 : ℝ) : OnePoint ℝ) = L k • ((0 : ℝ) : OnePoint ℝ)) : j = k := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ℝ) (L j • ((0 : ℝ) : OnePoint ℝ)) ∞
  exact eq_of_smul_zero_eq_infty (L := fun i ↦ g * L i) (geodesicLine_mul_mem_leftHalfPlane hu g)
    (by rw [mul_smul, hg]) (by rw [mul_smul, ← h, hg])

include hK hu in
/-- Two faces do not end at the same point. -/
private theorem eq_of_faceEnd_eq [Finite κ] {j k : κ} (h : faceEnd (L j) K = faceEnd (L k) K) :
    j = k := by
  cases hj : faceEnd (L j) K with
  | inl w => exact eq_of_faceEnd_eq_inl hK hu hj (h.symm.trans hj)
  | inr η =>
    exact eq_of_smul_infty_eq hu
      ((of_faceEnd_eq_inr hj).1.trans (of_faceEnd_eq_inr (h.symm.trans hj)).1.symm)

include hK hu in
/-- Two faces do not start at the same point. -/
private theorem eq_of_faceStart_eq [Finite κ] {j k : κ}
    (h : faceStart (L j) K = faceStart (L k) K) : j = k := by
  cases hj : faceStart (L j) K with
  | inl z => exact eq_of_faceStart_eq_inl hK hu hj (h.symm.trans hj)
  | inr ξ =>
    exact eq_of_smul_zero_eq hu
      ((of_faceStart_eq_inr hj).1.trans (of_faceStart_eq_inr (h.symm.trans hj)).1.symm)

include hK hu in
/-- The start of a face lies strictly to the left of every other line, unless it is an endpoint of
that line's face. -/
private theorem faceStart_mem_extLeftHalfPlane_or [Finite κ] {j k : κ} (hjk : j ≠ k) :
    faceStart (L j) K ∈ extLeftHalfPlane (L k) ∨ faceStart (L k) K = faceStart (L j) K ∨
      faceEnd (L k) K = faceStart (L j) K := by
  cases hj : faceStart (L j) K with
  | inl z =>
    rcases mem_extLeftHalfPlane_or_of_faceStart_eq_inl hK hu hjk hj with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  | inr ξ =>
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, ℝ) ξ ∞
    have hj' : faceStart (g * L j) (g • K) = .inr ∞ := by
      rw [faceStart_mul_smul, hj, Sum.smul_inr, hg]
    rcases mem_extLeftHalfPlane_or_of_faceStart_eq_infty (smul_eq_iInter_closure_leftHalfPlane hK g)
      (geodesicLine_mul_mem_leftHalfPlane hu g) hjk hj' with h | h | h
    · rw [← smul_extLeftHalfPlane, ← hg, ← Sum.smul_inr, smul_mem_smul_set_iff] at h
      exact Or.inl h
    · refine Or.inr (Or.inl (smul_left_cancel g ?_))
      rw [← faceStart_mul_smul, h, Sum.smul_inr, hg]
    · refine Or.inr (Or.inr (smul_left_cancel g ?_))
      rw [← faceEnd_mul_smul, h, Sum.smul_inr, hg]

include hK hu in
/-- The start of each face is weakly to the left of every line. -/
private theorem faceStart_mem_extClosedLeftHalfPlane [Finite κ] (j k : κ) :
    faceStart (L j) K ∈ extClosedLeftHalfPlane (L k) := by
  by_cases hjk : j = k
  · rw [hjk]
    exact (isGeodesicFromTo_face hK hu k).left_mem_extClosedLeftHalfPlane
  rcases faceStart_mem_extLeftHalfPlane_or hK hu hjk with h | h | h
  · exact extLeftHalfPlane_subset_extClosedLeftHalfPlane _ h
  · exact h ▸ (isGeodesicFromTo_face hK hu k).left_mem_extClosedLeftHalfPlane
  · exact h ▸ (isGeodesicFromTo_face hK hu k).right_mem_extClosedLeftHalfPlane

include hK hu in
/-- If `K` stays bounded after removing finitely many horodiscs, the end of each face is the start
of the face of another line. -/
private theorem exists_ne_faceEnd_eq_faceStart [Finite κ] (g : ι → PSL(2, ℝ)) {A : ι → ℝ}
    (hA : ∀ i, 0 < A i) (hb : Bornology.IsBounded (K \ ⋃ i, {z : ℍ | A i < (g i • z).im}))
    (k : κ) : ∃ j, j ≠ k ∧ faceEnd (L k) K = faceStart (L j) K := by
  cases hk : faceEnd (L k) K with
  | inl w =>
    obtain ⟨j, hjk, hj⟩ := exists_ne_faceStart_eq_of_faceEnd_eq_inl hK hu hk
    exact ⟨j, hjk, hj.symm⟩
  | inr η =>
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq PSL(2, ℝ) η ∞
    have hk' : faceEnd (h * L k) (h • K) = .inr ∞ := by
      rw [faceEnd_mul_smul, hk, Sum.smul_inr, hh]
    obtain ⟨j, hj⟩ := exists_faceStart_eq_of_faceEnd_eq_infty
      (smul_eq_iInter_closure_leftHalfPlane hK h) (geodesicLine_mul_mem_leftHalfPlane hu h) hk'
      (fun i ↦ g i * h⁻¹) hA (isBounded_smul_sdiff h g A hb)
    have hj' : faceStart (L j) K = .inr η := smul_left_cancel h (by
      rw [← faceStart_mul_smul, hj, Sum.smul_inr, hh])
    refine ⟨j, fun hjk ↦ ?_, hj'.symm⟩
    subst hjk
    exact (isGeodesicFromTo_face hK hu j).ne (hj'.trans hk.symm)

include hK hu in
/-- If `K` stays bounded after removing finitely many horodiscs, every ideal start of a face is
the centre of one of them. -/
private theorem exists_smul_eq_infty_of_faceStart_eq [Finite κ] {k : κ} {ξ : OnePoint ℝ}
    (hk : faceStart (L k) K = .inr ξ) (g : ι → PSL(2, ℝ)) {A : ι → ℝ} (hA : ∀ i, 0 < A i)
    (hb : Bornology.IsBounded (K \ ⋃ i, {z : ℍ | A i < (g i • z).im})) :
    ∃ i, g i • ξ = ∞ := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq PSL(2, ℝ) ξ ∞
  have hk' : faceStart (h * L k) (h • K) = .inr ∞ := by
    rw [faceStart_mul_smul, hk, Sum.smul_inr, hh]
  obtain ⟨i, hi⟩ := exists_smul_infty_eq_infty (frequently_mem_of_faceStart_eq
    (smul_eq_iInter_closure_leftHalfPlane hK h) (geodesicLine_mul_mem_leftHalfPlane hu h) hk')
    (fun i ↦ g i * h⁻¹) hA (isBounded_smul_sdiff h g A hb)
  have hξ : h⁻¹ • (∞ : OnePoint ℝ) = ξ := by rw [← hh, inv_smul_smul]
  exact ⟨i, by rwa [mul_smul, hξ] at hi⟩

include hK hu in
/-- A cycle of the successor map on faces has at least three lines: one line would be its own
successor, and two lines would run between the same two points. -/
private theorem three_le_minimalPeriod [Finite κ] {f : κ → κ} (hfk : ∀ k, f k ≠ k)
    (hf : ∀ k, faceEnd (L k) K = faceStart (L (f k)) K) (hinj : f.Injective) (k₀ : κ) :
    3 ≤ Function.minimalPeriod f k₀ := by
  have hn0 := Function.minimalPeriod_pos_of_mem_periodicPts (hinj.mem_periodicPts k₀)
  have hiter (m : ℕ) (hm : Function.minimalPeriod f k₀ = m) : f^[m] k₀ = k₀ := by
    rw [← hm]
    exact Function.iterate_minimalPeriod
  have hn1 : Function.minimalPeriod f k₀ ≠ 1 := fun h ↦ hfk k₀ (hiter 1 h)
  have hn2 : Function.minimalPeriod f k₀ ≠ 2 := fun h ↦ by
    have h2 : f (f k₀) = k₀ := hiter 2 h
    -- the lines of `k₀` and `f k₀` run between the same two points, in opposite directions
    have h₂ := isGeodesicFromTo_face hK hu (f k₀)
    rw [← hf k₀, hf (f k₀), h2] at h₂
    refine range_geodesicLine_ne hu (hfk k₀) ?_
    rw [← range_geodesicLine_mul_pslS (L (f k₀))]
    exact (isGeodesicFromTo_face hK hu k₀).range_geodesicLine_eq
      (isGeodesicFromTo_mul_pslS_iff.2 h₂)
  omega

include hK hu in
/-- Following the faces from ends to starts, one cycle of lines gives a convex polygon whose
carrier is `K` and whose sides are faces. Its ideal vertices are centres of the horodiscs. -/
private theorem exists_convexPolygon_of_faces [Finite κ] [Nonempty κ] (g : ι → PSL(2, ℝ))
    {A : ι → ℝ} (hA : ∀ i, 0 < A i)
    (hb : Bornology.IsBounded (K \ ⋃ i, {z : ℍ | A i < (g i • z).im})) :
    ∃ (n : ℕ) (_ : NeZero n) (P : ConvexPolygon n), P.carrier = K ∧
      (∀ i, ∃ k, leftHalfPlane (P.sideGeodesic i) = leftHalfPlane (L k) ∧
        P.side i = K ∩ range (geodesicLine (L k))) ∧
      ∀ i ξ, P.vertex i = .inr ξ → ∃ j, g j • ξ = ∞ := by
  choose f hfk hf using exists_ne_faceEnd_eq_faceStart hK hu g hA hb
  have hinj : f.Injective := fun k₁ k₂ h ↦ eq_of_faceEnd_eq hK hu (by rw [hf, hf, h])
  obtain ⟨k₀⟩ := ‹Nonempty κ›
  -- the cycle `c 0, c 1, …` of `k₀` under `f` has length `n`
  set n := Function.minimalPeriod f k₀
  let c : ℕ → κ := fun m ↦ f^[m] k₀
  have hcmod (m : ℕ) : c (m % n) = c m := Function.iterate_mod_minimalPeriod_eq
  have hcsucc (m : ℕ) : c (m + 1) = f (c m) := Function.iterate_succ_apply' f m k₀
  have hcinj {m m' : ℕ} (hm : m < n) (hm' : m' < n) (h : c m = c m') : m = m' :=
    Function.iterate_injOn_Iio_minimalPeriod hm hm' h
  have hn3 : 3 ≤ n := three_le_minimalPeriod hK hu hfk hf hinj k₀
  have : NeZero n := ⟨by omega⟩
  have hsucc (i : Fin n) : c ((i + 1 : Fin n) : ℕ) = f (c i) := by
    rw [← hcsucc, ← hcmod (i + 1), Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have hcne {i j : Fin n} (hij : i ≠ j) : c i ≠ c j := fun h ↦ hij (Fin.ext (hcinj i.isLt j.isLt h))
  let P : ConvexPolygon n :=
    { vertex := fun i ↦ faceStart (L (c i)) K
      three_le := hn3
      vertex_ne_vertex_add_one := fun i ↦ by
        rw [hsucc, ← hf]
        exact (isGeodesicFromTo_face hK hu _).ne
      vertex_mem_extLeftHalfPlane := fun i j hji hji' ↦ by
        have hface := isGeodesicFromTo_face hK hu (c i)
        rw [hsucc, ← hf, hface.extLeftHalfPlane_eq (isGeodesicFromTo_geodesicFromTo hface.ne)]
        rcases faceStart_mem_extLeftHalfPlane_or hK hu (hcne hji) with h | h | h
        · exact h
        · exact absurd (eq_of_faceStart_eq hK hu h) (hcne hji).symm
        -- the vertex `j` is not the end of the face of `c i`, the start of `c (i + 1)`
        · rw [hf, ← hsucc] at h
          exact absurd (eq_of_faceStart_eq hK hu h) (hcne fun h' ↦ hji' h'.symm) }
  have hPv (i : Fin n) : P.vertex i = faceStart (L (c i)) K := rfl
  have hPv' (i : Fin n) : P.vertex (i + 1) = faceEnd (L (c i)) K := by
    rw [hPv, hsucc, ← hf]
  have hside (i : Fin n) : leftHalfPlane (P.sideGeodesic i) = leftHalfPlane (L (c i)) := by
    rw [ConvexPolygon.sideGeodesic_def, hPv' i]
    exact (isGeodesicFromTo_face hK hu (c i)).leftHalfPlane_eq
      (isGeodesicFromTo_geodesicFromTo (isGeodesicFromTo_face hK hu (c i)).ne)
  refine ⟨n, inferInstance, P, subset_antisymm ?_ ?_, fun i ↦ ⟨c i, hside i, ?_⟩,
    fun i ξ hi ↦ exists_smul_eq_infty_of_faceStart_eq hK hu hi g hA hb⟩
  · -- the hull property: every vertex is weakly to the left of every line
    rw [hK]
    exact subset_iInter fun k ↦ P.carrier_subset_closure_leftHalfPlane_of_forall fun i ↦
      faceStart_mem_extClosedLeftHalfPlane hK hu (c i) k
  · rw [ConvexPolygon.carrier_def]
    refine subset_iInter fun i ↦ ?_
    rw [hside, hK]
    exact iInter_subset _ _
  · rw [ConvexPolygon.side_def, hPv, hPv', inter_range_eq_face hK hu]

end Faces

/-! ### The polygon -/

/-- **A finite intersection of closed half-planes with a bounded cusp truncation is a convex
polygon.** Let `K` be the intersection of the closed left half-planes of the geodesic lines
`L k`, `k ∈ t`, for a finite set `t`, and suppose that `K` has nonempty interior. Suppose that
removing from `K` finitely many open horodiscs `{z | A i < Im (g i • z)}` with `A i > 0`, centred
at the ideal points carried to `∞` by `g i`, leaves a bounded set. Then `K` is the carrier of a
convex polygon, possibly with ideal vertices. Each side of the polygon is the face `K ∩ L k` of
`K` along the line of some `k ∈ t`, and the polygon lies to the left of that line. Each ideal vertex
is the centre of one of the horodiscs. -/
theorem exists_convexPolygon_carrier_eq_iInter_closure_leftHalfPlane {ι ι' : Type*} [Finite ι']
    (t : Finset ι) (L : ι → PSL(2, ℝ))
    (hint : (interior (⋂ k ∈ t, closure (leftHalfPlane (L k)))).Nonempty)
    (g : ι' → PSL(2, ℝ)) {A : ι' → ℝ} (hA : ∀ i, 0 < A i)
    (hb : Bornology.IsBounded
      ((⋂ k ∈ t, closure (leftHalfPlane (L k))) \ ⋃ i, {z : ℍ | A i < (g i • z).im})) :
    ∃ (n : ℕ) (_ : NeZero n) (P : ConvexPolygon n),
      P.carrier = ⋂ k ∈ t, closure (leftHalfPlane (L k)) ∧
      (∀ i, ∃ k ∈ t, leftHalfPlane (P.sideGeodesic i) = leftHalfPlane (L k) ∧
        P.side i = (⋂ k ∈ t, closure (leftHalfPlane (L k))) ∩ range (geodesicLine (L k))) ∧
      ∀ i ξ, P.vertex i = .inr ξ → ∃ j, g j • ξ = ∞ := by
  obtain ⟨p, hp⟩ := hint
  simp only [Finset.interior_iInter, interior_closure_leftHalfPlane, mem_iInter₂] at hp
  obtain ⟨s, hst, hs, hess⟩ := exists_subset_iInter_eq_and_essential hp
  -- pass to the irredundant subfamily `s`, indexed by its elements
  let L' : s → PSL(2, ℝ) := fun k ↦ L k
  have hK : ⋂ k ∈ t, closure (leftHalfPlane (L k)) = ⋂ k : s, closure (leftHalfPlane (L' k)) := by
    rw [← hs]
    ext z
    simp [L']
  have hess' (k : s) :
      ∃ u : ℝ, ∀ j : s, j ≠ k → geodesicLine (L' k) u ∈ leftHalfPlane (L' j) := by
    obtain ⟨u, hu⟩ := hess k k.2
    exact ⟨u, fun j hj ↦ hu j j.2 (Subtype.coe_injective.ne hj)⟩
  choose u hu using hess'
  -- an empty family would leave all of `ℍ`, which stays unbounded after removing the horodiscs
  have : Nonempty s := by
    by_contra h
    rw [not_nonempty_iff] at h
    refine false_of_forall_smul_zero_ne_infty (L := L') rfl ?_ (fun m ↦ isEmptyElim m) g hA
      (hK ▸ hb)
    rw [iInter_of_empty]
    exact Eventually.frequently (Eventually.of_forall fun _ ↦ mem_univ _)
  obtain ⟨n, _, P, hPK, hPs, hPv⟩ := exists_convexPolygon_of_faces hK hu g hA (hK ▸ hb)
  refine ⟨n, inferInstance, P, hPK, fun i ↦ ?_, hPv⟩
  obtain ⟨k, h₁, h₂⟩ := hPs i
  exact ⟨k, hst k.2, h₁, h₂⟩

/-- **A bounded intersection of finitely many closed half-planes is a compact convex polygon.**
Let `K` be the intersection of the closed left half-planes of the geodesic lines `L k`, `k ∈ t`,
for a finite set `t`. If `K` is bounded with nonempty interior, it is the carrier of a compact
convex polygon. Each side of the polygon is the face `K ∩ L k` of `K` along the line of some
`k ∈ t`, and the polygon lies to the left of that line. -/
theorem exists_compactConvexPolygon_carrier_eq_iInter_closure_leftHalfPlane {ι : Type*}
    (t : Finset ι) (L : ι → PSL(2, ℝ))
    (hint : (interior (⋂ k ∈ t, closure (leftHalfPlane (L k)))).Nonempty)
    (hb : Bornology.IsBounded (⋂ k ∈ t, closure (leftHalfPlane (L k)))) :
    ∃ (n : ℕ) (_ : NeZero n) (P : CompactConvexPolygon n),
      P.carrier = ⋂ k ∈ t, closure (leftHalfPlane (L k)) ∧
      ∀ i, ∃ k ∈ t, leftHalfPlane (geodesicBetween (P.vertex i) (P.vertex (i + 1))) =
          leftHalfPlane (L k) ∧
        P.side i = (⋂ k ∈ t, closure (leftHalfPlane (L k))) ∩ range (geodesicLine (L k)) := by
  -- with no horodiscs to remove, the polygon has no ideal vertices
  obtain ⟨n, _, P, hPK, hPs, hPv⟩ := exists_convexPolygon_carrier_eq_iInter_closure_leftHalfPlane
    t L hint (Empty.elim : Empty → PSL(2, ℝ)) (A := Empty.elim) (fun i ↦ i.elim) (by simpa using hb)
  obtain ⟨Q, rfl⟩ := P.exists_eq_toConvexPolygon fun i ↦ by
    cases hv : P.vertex i with
    | inl z => exact ⟨z, rfl⟩
    | inr ξ => exact (hPv i ξ hv).elim fun j _ ↦ j.elim
  refine ⟨n, inferInstance, Q, by rwa [← Q.carrier_toConvexPolygon], fun i ↦ ?_⟩
  obtain ⟨k, hk, h₁, h₂⟩ := hPs i
  refine ⟨k, hk, ?_, by rwa [← Q.side_toConvexPolygon]⟩
  rwa [ConvexPolygon.sideGeodesic_def, Q.vertex_toConvexPolygon, Q.vertex_toConvexPolygon,
    leftHalfPlane_geodesicFromTo_inl_inl (Q.vertex_ne_vertex_add_one i)] at h₁

end TauCeti.UpperHalfPlane
