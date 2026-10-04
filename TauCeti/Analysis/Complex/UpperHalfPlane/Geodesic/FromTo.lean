/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Between
public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.Order.Hom.Set
public import TauCeti.Analysis.Complex.UpperHalfPlane.Extended
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Endpoint

/-!
# Oriented geodesics between points of `ℍ ∪ ∂ℍ`

Points of `ℍ ∪ ∂ℍ` are modelled as `ℍ ⊕ OnePoint ℝ`: a point of `ℍ` (`Sum.inl`) or an ideal
point (`Sum.inr`), on which `PSL(2, ℝ)` acts componentwise. Any two distinct such points lie on a
unique geodesic (Walkden §7.1). `IsGeodesicFromTo g p q` says that the geodesic line of `g` runs
from `p` to `q`: a point of `ℍ` lies on the line, an ideal point is its backward endpoint `g • 0`
(for `p`) or forward endpoint `g • ∞` (for `q`), and two points of `ℍ` occur in this order.
Such a `g` exists for `p ≠ q` (`exists_isGeodesicFromTo`) and is unique up to reparametrisation
(`IsGeodesicFromTo.exists_eq_mul_dilation`), so `geodesicFromTo p q`, a choice of it, has
well-defined half-planes and ideal arcs.

`extLeftHalfPlane g` is the open left half-plane of `g` together with the open arc of ideal points
on its left, as a subset of `ℍ ⊕ OnePoint ℝ`: the points of `ℍ ∪ ∂ℍ` strictly to the left of the
line. Reading a point of `ℍ ⊕ OnePoint ℝ` other than `∞` as a complex number (`toComplex`, from
`Extended.lean`), the side form `sideForm g` of `HalfPlane.lean` can be evaluated at vertices: it
is negative at points strictly to the left of a line
(`sideForm_toComplex_neg_of_mem_extLeftHalfPlane`), and zero at the two points a line runs between
(`IsGeodesicFromTo.sideForm_toComplex_left`, `IsGeodesicFromTo.sideForm_toComplex_right`).

## Main declarations

* `TauCeti.UpperHalfPlane.IsGeodesicFromTo g p q`: the geodesic line of `g` runs from `p` to `q`.
* `TauCeti.UpperHalfPlane.geodesicFromTo p q`: a geodesic line from `p` to `q`
  (`isGeodesicFromTo_geodesicFromTo`).
* `TauCeti.UpperHalfPlane.extLeftHalfPlane g`: the points of `ℍ ∪ ∂ℍ` strictly to the left of
  `geodesicLine g`.
* `TauCeti.UpperHalfPlane.IsGeodesicFromTo.re_toComplex_lt`: on a geodesic with `∞` on its left,
  points occur from left to right.
* `TauCeti.UpperHalfPlane.IsGeodesicFromTo.re_toComplex_lt_iff`: a geodesic line through two
  points with distinct real parts passes its points in order.

## Source

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §7.1 (for
`z, w ∈ ℍ ∪ ∂ℍ` there is a unique geodesic through both; `[z, w]` is the part between them) and
§4.3 (geodesics are determined by their endpoints; Lemma 4.3.1, a semicircle with endpoints
`ζ₋ < ζ₊`); Katok, *Fuchsian groups, geodesic flows on surfaces of constant negative curvature and
symbolic coding of geodesics*, Clay Math. Proc. 10 (2010), Theorem 3.1 p. 10 (geodesics are
semicircles and vertical lines).
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise OnePoint

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (dilation dilation_add dilation_inv)

/-! ### Geodesic lines running between two points of `ℍ ∪ ∂ℍ` -/

/-- The geodesic line of `g` runs from `p` to `q`, for points `p`, `q` of `ℍ ∪ ∂ℍ`: a point of `ℍ`
lies on the line, an ideal starting point is the backward endpoint `g • 0`, an ideal end point is
the forward endpoint `g • ∞`, and two points of `ℍ` occur in this order along the line. -/
def IsGeodesicFromTo (g : PSL(2, ℝ)) : ℍ ⊕ OnePoint ℝ → ℍ ⊕ OnePoint ℝ → Prop
  | .inl z, .inl w => ∃ s t : ℝ, s < t ∧ geodesicLine g s = z ∧ geodesicLine g t = w
  | .inl z, .inr η => z ∈ Set.range (geodesicLine g) ∧ g • (∞ : OnePoint ℝ) = η
  | .inr ξ, .inl w => g • ((0 : ℝ) : OnePoint ℝ) = ξ ∧ w ∈ Set.range (geodesicLine g)
  | .inr ξ, .inr η => g • ((0 : ℝ) : OnePoint ℝ) = ξ ∧ g • (∞ : OnePoint ℝ) = η

@[simp]
theorem isGeodesicFromTo_inl_inl {g : PSL(2, ℝ)} {z w : ℍ} :
    IsGeodesicFromTo g (.inl z) (.inl w) ↔
      ∃ s t : ℝ, s < t ∧ geodesicLine g s = z ∧ geodesicLine g t = w :=
  Iff.rfl

@[simp]
theorem isGeodesicFromTo_inl_inr {g : PSL(2, ℝ)} {z : ℍ} {η : OnePoint ℝ} :
    IsGeodesicFromTo g (.inl z) (.inr η) ↔
      z ∈ Set.range (geodesicLine g) ∧ g • (∞ : OnePoint ℝ) = η :=
  Iff.rfl

@[simp]
theorem isGeodesicFromTo_inr_inl {g : PSL(2, ℝ)} {ξ : OnePoint ℝ} {w : ℍ} :
    IsGeodesicFromTo g (.inr ξ) (.inl w) ↔
      g • ((0 : ℝ) : OnePoint ℝ) = ξ ∧ w ∈ Set.range (geodesicLine g) :=
  Iff.rfl

@[simp]
theorem isGeodesicFromTo_inr_inr {g : PSL(2, ℝ)} {ξ η : OnePoint ℝ} :
    IsGeodesicFromTo g (.inr ξ) (.inr η) ↔
      g • ((0 : ℝ) : OnePoint ℝ) = ξ ∧ g • (∞ : OnePoint ℝ) = η :=
  Iff.rfl

/-- The two points a geodesic line runs between are distinct. -/
theorem IsGeodesicFromTo.ne {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (h : IsGeodesicFromTo g p q) : p ≠ q := by
  rcases p with z | ξ <;> rcases q with w | η
  · obtain ⟨s, t, hst, rfl, rfl⟩ := h
    exact fun hzw ↦ hst.ne (geodesicLine_injective g (Sum.inl_injective hzw))
  · exact Sum.inl_ne_inr
  · exact Sum.inr_ne_inl
  · obtain ⟨rfl, rfl⟩ := h
    exact fun hξη ↦ OnePoint.coe_ne_infty 0 (MulAction.injective g (Sum.inr_injective hξη))

/-- A point of `ℍ` from which a geodesic line runs lies on the line. -/
theorem IsGeodesicFromTo.left_mem_range {g : PSL(2, ℝ)} {z : ℍ} {q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g (.inl z) q) : z ∈ Set.range (geodesicLine g) := by
  rcases q with w | η
  · obtain ⟨s, -, -, hs, -⟩ := hg
    exact ⟨s, hs⟩
  · exact hg.1

/-- A point of `ℍ` to which a geodesic line runs lies on the line. -/
theorem IsGeodesicFromTo.right_mem_range {g : PSL(2, ℝ)} {p : ℍ ⊕ OnePoint ℝ} {w : ℍ}
    (hg : IsGeodesicFromTo g p (.inl w)) : w ∈ Set.range (geodesicLine g) := by
  rcases p with z | ξ
  · obtain ⟨-, t, -, -, ht⟩ := hg
    exact ⟨t, ht⟩
  · exact hg.2

/-- An ideal point from which a geodesic line runs is its backward endpoint. -/
theorem IsGeodesicFromTo.smul_zero_eq {g : PSL(2, ℝ)} {ξ : OnePoint ℝ} {q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g (.inr ξ) q) : g • ((0 : ℝ) : OnePoint ℝ) = ξ := by
  rcases q with w | η <;> exact hg.1

/-- An ideal point to which a geodesic line runs is its forward endpoint. -/
theorem IsGeodesicFromTo.smul_infty_eq {g : PSL(2, ℝ)} {p : ℍ ⊕ OnePoint ℝ} {η : OnePoint ℝ}
    (hg : IsGeodesicFromTo g p (.inr η)) : g • (∞ : OnePoint ℝ) = η := by
  rcases p with z | ξ <;> exact hg.2

/-- The geodesic from `z` to `w` runs from `z` to `w`. -/
theorem isGeodesicFromTo_geodesicBetween {z w : ℍ} (hzw : z ≠ w) :
    IsGeodesicFromTo (geodesicBetween z w) (.inl z) (.inl w) :=
  ⟨0, dist z w, dist_pos.2 hzw, geodesicLine_geodesicBetween_zero z w,
    geodesicLine_geodesicBetween_dist z w⟩

/-- Translating by `h` carries a geodesic line from `p` to `q` to one from `h • p` to `h • q`. -/
theorem IsGeodesicFromTo.smul {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) (h : PSL(2, ℝ)) :
    IsGeodesicFromTo (h * g) (h • p) (h • q) := by
  rcases p with z | ξ <;> rcases q with w | η <;> simp only [Sum.smul_inl, Sum.smul_inr]
  · obtain ⟨s, t, hst, rfl, rfl⟩ := hg
    exact ⟨s, t, hst, (smul_geodesicLine h g s).symm, (smul_geodesicLine h g t).symm⟩
  · obtain ⟨⟨t, rfl⟩, rfl⟩ := hg
    exact ⟨⟨t, (smul_geodesicLine h g t).symm⟩, mul_smul h g _⟩
  · obtain ⟨rfl, ⟨t, rfl⟩⟩ := hg
    exact ⟨mul_smul h g _, ⟨t, (smul_geodesicLine h g t).symm⟩⟩
  · obtain ⟨rfl, rfl⟩ := hg
    exact ⟨mul_smul h g _, mul_smul h g _⟩

/-- Reparametrising by a dilation does not change the points a geodesic line runs between. -/
theorem IsGeodesicFromTo.mul_dilation {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) (s : ℝ) :
    IsGeodesicFromTo (g * ↑(dilation s)) p q := by
  rcases p with z | ξ <;> rcases q with w | η
  · obtain ⟨s', t', hst, rfl, rfl⟩ := hg
    refine ⟨s' - s, t' - s, sub_lt_sub_right hst s, ?_, ?_⟩ <;>
      rw [geodesicLine_mul_dilation, add_sub_cancel]
  · obtain ⟨hz, rfl⟩ := hg
    exact ⟨range_geodesicLine_mul_dilation g s ▸ hz, by rw [mul_smul, dilation_smul_infty]⟩
  · obtain ⟨rfl, hw⟩ := hg
    exact ⟨by rw [mul_smul, dilation_smul_zero], range_geodesicLine_mul_dilation g s ▸ hw⟩
  · obtain ⟨rfl, rfl⟩ := hg
    exact ⟨by rw [mul_smul, dilation_smul_zero], by rw [mul_smul, dilation_smul_infty]⟩

/-- Reversing the orientation of a geodesic line by `pslS` swaps the points it runs between. -/
theorem isGeodesicFromTo_mul_pslS_iff {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ} :
    IsGeodesicFromTo (g * pslS) p q ↔ IsGeodesicFromTo g q p := by
  rcases p with z | ξ <;> rcases q with w | η
  · simp only [isGeodesicFromTo_inl_inl, geodesicLine_mul_pslS]
    constructor
    · rintro ⟨s, t, hst, hs, ht⟩
      exact ⟨-t, -s, neg_lt_neg hst, ht, hs⟩
    · rintro ⟨s, t, hst, hs, ht⟩
      exact ⟨-t, -s, neg_lt_neg hst, by rwa [neg_neg], by rwa [neg_neg]⟩
  all_goals simp [range_geodesicLine_mul_pslS, mul_smul, and_comm]

/-- Any two distinct points of `ℍ ∪ ∂ℍ` are joined by a geodesic line. -/
theorem exists_isGeodesicFromTo {p q : ℍ ⊕ OnePoint ℝ} (hpq : p ≠ q) :
    ∃ g : PSL(2, ℝ), IsGeodesicFromTo g p q := by
  rcases p with z | ξ <;> rcases q with w | η
  · exact ⟨_, isGeodesicFromTo_geodesicBetween fun hzw ↦ hpq (congrArg _ hzw)⟩
  · obtain ⟨g, hg₀, hg⟩ := exists_geodesicLine_zero_eq_and_smul_infty_eq z η
    exact ⟨g, ⟨0, hg₀⟩, hg⟩
  · obtain ⟨g, hg₀, hg⟩ := exists_geodesicLine_zero_eq_and_smul_infty_eq w ξ
    exact ⟨g * pslS, isGeodesicFromTo_mul_pslS_iff.2 ⟨⟨0, hg₀⟩, hg⟩⟩
  · exact exists_smul_zero_eq_and_smul_infty_eq fun hξη ↦ hpq (congrArg _ hξη)

/-- Two elements whose reparametrisations by dilations agree differ by a dilation. -/
private theorem exists_eq_mul_dilation_of_mul_dilation_eq {g g' : PSL(2, ℝ)} {s s' : ℝ}
    (h : g * ↑(dilation s) = g' * ↑(dilation s')) : ∃ u : ℝ, g' = g * ↑(dilation u) := by
  have hd : (↑(dilation (s - s')) : PSL(2, ℝ)) = ↑(dilation s) * (↑(dilation s'))⁻¹ := by
    rw [sub_eq_add_neg, dilation_add, ← dilation_inv, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  refine ⟨s - s', ?_⟩
  rw [hd, ← mul_assoc, h]
  group

/-- Uniqueness of the geodesic line from a point of `ℍ` to an ideal point. -/
private theorem exists_eq_mul_dilation_inl_inr {g g' : PSL(2, ℝ)} {z : ℍ} {η : OnePoint ℝ}
    (hg : IsGeodesicFromTo g (.inl z) (.inr η)) (hg' : IsGeodesicFromTo g' (.inl z) (.inr η)) :
    ∃ s : ℝ, g' = g * ↑(dilation s) := by
  obtain ⟨⟨s, rfl⟩, rfl⟩ := hg
  obtain ⟨⟨s', hs'⟩, h'⟩ := hg'
  refine exists_eq_mul_dilation_of_mul_dilation_eq (s := s) (s' := s')
    (eq_of_geodesicLine_zero_eq_of_smul_infty_eq ?_ ?_)
  · rw [geodesicLine_mul_dilation, geodesicLine_mul_dilation, add_zero, add_zero, hs']
  · rw [mul_smul, mul_smul, dilation_smul_infty, dilation_smul_infty, h']

/-- **Uniqueness of the geodesic through two points of `ℍ ∪ ∂ℍ`**: two geodesic lines running
from `p` to `q` differ by a reparametrisation. -/
theorem IsGeodesicFromTo.exists_eq_mul_dilation {g g' : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) (hg' : IsGeodesicFromTo g' p q) :
    ∃ s : ℝ, g' = g * ↑(dilation s) := by
  rcases p with z | ξ <;> rcases q with w | η
  · obtain ⟨s, t, hst, rfl, rfl⟩ := hg
    obtain ⟨s', t', hst', hs', ht'⟩ := hg'
    refine exists_eq_mul_dilation_of_mul_dilation_eq (s := s) (s' := s') ?_
    rw [← geodesicBetween_geodesicLine_of_lt g hst, ← geodesicBetween_geodesicLine_of_lt g' hst',
      hs', ht']
  · exact exists_eq_mul_dilation_inl_inr hg hg'
  · -- reverse both lines with `pslS` and use the previous case
    obtain ⟨u, hu⟩ := exists_eq_mul_dilation_inl_inr (isGeodesicFromTo_mul_pslS_iff.2 hg)
      (isGeodesicFromTo_mul_pslS_iff.2 hg')
    refine ⟨-u, ?_⟩
    calc g' = g' * pslS * pslS := by rw [mul_assoc, pslS_mul_self, mul_one]
      _ = g * ↑(dilation (-u)) := by rw [hu, ← pslS_mul_dilation_mul_pslS]; group
  · obtain ⟨rfl, rfl⟩ := hg
    exact exists_eq_mul_dilation_of_smul_zero_eq_of_smul_infty_eq hg'.1.symm hg'.2.symm

/-- Two geodesic lines running from `p` to `q` have the same left half-plane. -/
theorem IsGeodesicFromTo.leftHalfPlane_eq {g g' : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) (hg' : IsGeodesicFromTo g' p q) :
    leftHalfPlane g' = leftHalfPlane g := by
  obtain ⟨s, rfl⟩ := hg.exists_eq_mul_dilation hg'
  exact leftHalfPlane_mul_dilation g s

/-- Two geodesic lines running from `p` to `q` have the same left ideal arc. -/
theorem IsGeodesicFromTo.boundaryLeftHalfPlane_eq {g g' : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) (hg' : IsGeodesicFromTo g' p q) :
    boundaryLeftHalfPlane g' = boundaryLeftHalfPlane g := by
  obtain ⟨s, rfl⟩ := hg.exists_eq_mul_dilation hg'
  exact boundaryLeftHalfPlane_mul_dilation g s

/-! ### The chosen geodesic from `p` to `q` -/

open scoped Classical in
/-- A geodesic line from `p` to `q`, for distinct points `p`, `q` of `ℍ ∪ ∂ℍ`
(`isGeodesicFromTo_geodesicFromTo`); the identity if `p = q`. -/
def geodesicFromTo (p q : ℍ ⊕ OnePoint ℝ) : PSL(2, ℝ) :=
  if h : ∃ g : PSL(2, ℝ), IsGeodesicFromTo g p q then h.choose else 1

/-- The junk value of `geodesicFromTo` on equal points. -/
@[simp]
theorem geodesicFromTo_self (p : ℍ ⊕ OnePoint ℝ) : geodesicFromTo p p = 1 := by
  have h : ¬∃ g : PSL(2, ℝ), IsGeodesicFromTo g p p := fun ⟨_, hg⟩ ↦ hg.ne rfl
  simp only [geodesicFromTo, h, ↓reduceDIte]

/-- `geodesicFromTo p q` runs from `p` to `q`. -/
theorem isGeodesicFromTo_geodesicFromTo {p q : ℍ ⊕ OnePoint ℝ} (hpq : p ≠ q) :
    IsGeodesicFromTo (geodesicFromTo p q) p q := by
  have h := exists_isGeodesicFromTo hpq
  simp only [geodesicFromTo, h, ↓reduceDIte]
  exact h.choose_spec

/-- Between two points of `ℍ`, `geodesicFromTo` has the half-planes of `geodesicBetween`. -/
theorem leftHalfPlane_geodesicFromTo_inl_inl {z w : ℍ} (hzw : z ≠ w) :
    leftHalfPlane (geodesicFromTo (.inl z) (.inl w)) = leftHalfPlane (geodesicBetween z w) :=
  (isGeodesicFromTo_geodesicBetween hzw).leftHalfPlane_eq
    (isGeodesicFromTo_geodesicFromTo (Sum.inl_injective.ne hzw))

/-- The left half-plane of `geodesicFromTo` transforms naturally under the action. -/
theorem leftHalfPlane_geodesicFromTo_smul (h : PSL(2, ℝ)) {p q : ℍ ⊕ OnePoint ℝ} (hpq : p ≠ q) :
    leftHalfPlane (geodesicFromTo (h • p) (h • q)) = h • leftHalfPlane (geodesicFromTo p q) := by
  rw [smul_leftHalfPlane]
  exact ((isGeodesicFromTo_geodesicFromTo hpq).smul h).leftHalfPlane_eq
    (isGeodesicFromTo_geodesicFromTo ((MulAction.injective h).ne hpq))

/-! ### Points of `ℍ ∪ ∂ℍ` strictly to the left of a geodesic line -/

/-- The points of `ℍ ∪ ∂ℍ` strictly to the left of `geodesicLine g`: the open left half-plane
together with the open arc of ideal points on its left. -/
def extLeftHalfPlane (g : PSL(2, ℝ)) : Set (ℍ ⊕ OnePoint ℝ) :=
  Set.sumEquiv.symm (leftHalfPlane g, boundaryLeftHalfPlane g)

@[simp]
theorem inl_mem_extLeftHalfPlane_iff {g : PSL(2, ℝ)} {z : ℍ} :
    Sum.inl z ∈ extLeftHalfPlane g ↔ z ∈ leftHalfPlane g := by
  simp [extLeftHalfPlane, Set.sumEquiv_symm_apply]

@[simp]
theorem inr_mem_extLeftHalfPlane_iff {g : PSL(2, ℝ)} {ξ : OnePoint ℝ} :
    Sum.inr ξ ∈ extLeftHalfPlane g ↔ ξ ∈ boundaryLeftHalfPlane g := by
  simp [extLeftHalfPlane, Set.sumEquiv_symm_apply]

/-- Translating the points strictly to the left of `g` by `h` gives those strictly to the left
of `h * g`. -/
@[simp]
theorem smul_extLeftHalfPlane (h g : PSL(2, ℝ)) :
    h • extLeftHalfPlane g = extLeftHalfPlane (h * g) := by
  rw [extLeftHalfPlane, extLeftHalfPlane, Set.sumEquiv_symm_apply, Set.sumEquiv_symm_apply,
    Set.smul_set_union, ← Set.image_smul_comm _ _ _ fun z ↦ (Sum.smul_inl h z).symm,
    ← Set.image_smul_comm _ _ _ fun ξ ↦ (Sum.smul_inr h ξ).symm, smul_leftHalfPlane,
    smul_boundaryLeftHalfPlane]

/-- Two geodesic lines running from `p` to `q` have the same points strictly on their left. -/
theorem IsGeodesicFromTo.extLeftHalfPlane_eq {g g' : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) (hg' : IsGeodesicFromTo g' p q) :
    extLeftHalfPlane g' = extLeftHalfPlane g := by
  rw [extLeftHalfPlane, extLeftHalfPlane, hg.leftHalfPlane_eq hg',
    hg.boundaryLeftHalfPlane_eq hg']

/-- The points strictly to the left of `geodesicFromTo` transform naturally under the action. -/
theorem extLeftHalfPlane_geodesicFromTo_smul (h : PSL(2, ℝ)) {p q : ℍ ⊕ OnePoint ℝ}
    (hpq : p ≠ q) :
    extLeftHalfPlane (geodesicFromTo (h • p) (h • q)) =
      h • extLeftHalfPlane (geodesicFromTo p q) := by
  rw [smul_extLeftHalfPlane]
  exact ((isGeodesicFromTo_geodesicFromTo hpq).smul h).extLeftHalfPlane_eq
    (isGeodesicFromTo_geodesicFromTo ((MulAction.injective h).ne hpq))

/-- A point strictly to the left of a geodesic line is not one of the two points it runs
between. -/
theorem IsGeodesicFromTo.left_notMem_extLeftHalfPlane {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) : p ∉ extLeftHalfPlane g := by
  rcases p with z | ξ
  · rw [inl_mem_extLeftHalfPlane_iff]
    exact Set.disjoint_right.1 (disjoint_leftHalfPlane_range_geodesicLine g) hg.left_mem_range
  · rw [inr_mem_extLeftHalfPlane_iff, ← hg.smul_zero_eq]
    exact smul_zero_notMem_boundaryLeftHalfPlane g

/-- A point strictly to the left of a geodesic line is not one of the two points it runs
between. -/
theorem IsGeodesicFromTo.right_notMem_extLeftHalfPlane {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) : q ∉ extLeftHalfPlane g := by
  rcases q with w | η
  · rw [inl_mem_extLeftHalfPlane_iff]
    exact Set.disjoint_right.1 (disjoint_leftHalfPlane_range_geodesicLine g) hg.right_mem_range
  · rw [inr_mem_extLeftHalfPlane_iff, ← hg.smul_infty_eq]
    exact smul_infty_notMem_boundaryLeftHalfPlane g

/-! ### The side form at points of `ℍ ∪ ∂ℍ` -/

/-- A point other than `∞` strictly to the left of a geodesic line is where its side form is
negative. -/
theorem sideForm_toComplex_neg_of_mem_extLeftHalfPlane {g : PSL(2, ℝ)} {p : ℍ ⊕ OnePoint ℝ}
    (hp : p ≠ .inr ∞) (h : p ∈ extLeftHalfPlane g) : sideForm g (toComplex p) < 0 := by
  rcases p with z | ξ
  · rw [toComplex_inl]
    exact (mem_leftHalfPlane_iff_sideForm_neg g z).1 (inl_mem_extLeftHalfPlane_iff.1 h)
  · obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun hξ ↦ hp (congrArg _ hξ)
    rw [toComplex_inr_coe]
    exact (coe_mem_boundaryLeftHalfPlane_iff g x).1 (inr_mem_extLeftHalfPlane_iff.1 h)

/-- The side form of a geodesic line vanishes at the point it runs from, unless that point is
`∞`. -/
theorem IsGeodesicFromTo.sideForm_toComplex_left {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) (hp : p ≠ .inr ∞) : sideForm g (toComplex p) = 0 := by
  rcases p with z | ξ
  · rw [toComplex_inl]
    exact (mem_range_geodesicLine_iff_sideForm_eq_zero g z).1 hg.left_mem_range
  · obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun hξ ↦ hp (congrArg _ hξ)
    rw [toComplex_inr_coe]
    exact sideForm_eq_zero_of_smul_zero_eq hg.smul_zero_eq

/-- The side form of a geodesic line vanishes at the point it runs to, unless that point is
`∞`. -/
theorem IsGeodesicFromTo.sideForm_toComplex_right {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) (hq : q ≠ .inr ∞) : sideForm g (toComplex q) = 0 := by
  rcases q with w | η
  · rw [toComplex_inl]
    exact (mem_range_geodesicLine_iff_sideForm_eq_zero g w).1 hg.right_mem_range
  · obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.1 fun hη ↦ hq (congrArg _ hη)
    rw [toComplex_inr_coe]
    exact sideForm_eq_zero_of_smul_infty_eq hg.smul_infty_eq

/-- On a geodesic line with `∞` strictly on its left, the points it runs between occur from left
to right. -/
theorem IsGeodesicFromTo.re_toComplex_lt {g : PSL(2, ℝ)} {p q : ℍ ⊕ OnePoint ℝ}
    (hg : IsGeodesicFromTo g p q) (h : (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane g) :
    (toComplex p).re < (toComplex q).re := by
  -- both endpoints are real, since `∞` is strictly on the left
  have h₀ : g • ((0 : ℝ) : OnePoint ℝ) ≠ ∞ := fun h₀ ↦
    smul_zero_notMem_boundaryLeftHalfPlane g (by rwa [h₀])
  have h₁ : g • (∞ : OnePoint ℝ) ≠ ∞ := fun h₁ ↦
    smul_infty_notMem_boundaryLeftHalfPlane g (by rwa [h₁])
  obtain ⟨e₀, he₀⟩ := OnePoint.ne_infty_iff_exists.1 h₀
  obtain ⟨e₁, he₁⟩ := OnePoint.ne_infty_iff_exists.1 h₁
  have he := (infty_mem_boundaryLeftHalfPlane_iff he₀.symm he₁.symm).1 h
  rcases p with z | ξ <;> rcases q with w | η
  · obtain ⟨s, t, hst, rfl, rfl⟩ := hg
    rw [toComplex_inl, toComplex_inl]
    exact strictMono_re_geodesicLine he₀.symm he₁.symm he hst
  · obtain ⟨⟨t, rfl⟩, rfl⟩ := hg
    rw [← he₁, toComplex_inl, toComplex_inr_coe, coe_re, Complex.ofReal_re]
    exact re_geodesicLine_lt he₀.symm he₁.symm he t
  · obtain ⟨rfl, ⟨t, rfl⟩⟩ := hg
    rw [← he₀, toComplex_inl, toComplex_inr_coe, coe_re, Complex.ofReal_re]
    exact lt_re_geodesicLine he₀.symm he₁.symm he t
  · obtain ⟨rfl, rfl⟩ := hg
    rwa [← he₀, ← he₁, toComplex_inr_coe, toComplex_inr_coe, Complex.ofReal_re,
      Complex.ofReal_re]

/-- For a geodesic line running from `p` to `q` and from `p` to `r`, where `p` and `q` are not `∞`
and have distinct real parts, the real part of `toComplex r` lies on the same side of `Re p` as
`Re q`. -/
theorem IsGeodesicFromTo.re_toComplex_lt_iff {g : PSL(2, ℝ)} {p q r : ℍ ⊕ OnePoint ℝ}
    (hpq : IsGeodesicFromTo g p q) (hpr : IsGeodesicFromTo g p r) (hp : p ≠ .inr ∞)
    (hq : q ≠ .inr ∞) (hre : (toComplex p).re ≠ (toComplex q).re) :
    (toComplex p).re < (toComplex r).re ↔ (toComplex p).re < (toComplex q).re := by
  have hp₀ := hpq.sideForm_toComplex_left hp
  have hq₀ := hpq.sideForm_toComplex_right hq
  -- neither endpoint of the line is `∞`: the line would be vertical, with `Re p = Re q`
  have h₀ : g • ((0 : ℝ) : OnePoint ℝ) ≠ ∞ := fun h₀ ↦ by
    obtain ⟨e, he⟩ := OnePoint.ne_infty_iff_exists.1 fun h₁ : g • (∞ : OnePoint ℝ) = ∞ ↦
      OnePoint.coe_ne_infty (0 : ℝ) (MulAction.injective g (h₀.trans h₁.symm))
    rw [sideForm_eq_of_smul_zero_eq_infty h₀ he.symm] at hp₀ hq₀
    exact hre (by linarith)
  have h₁ : g • (∞ : OnePoint ℝ) ≠ ∞ := fun h₁ ↦ by
    obtain ⟨e, he⟩ := OnePoint.ne_infty_iff_exists.1 fun h₀ : g • ((0 : ℝ) : OnePoint ℝ) = ∞ ↦
      OnePoint.coe_ne_infty (0 : ℝ) (MulAction.injective g (h₀.trans h₁.symm))
    rw [sideForm_eq_of_smul_infty_eq_infty he.symm h₁] at hp₀ hq₀
    exact hre (by linarith)
  obtain ⟨e₀, he₀⟩ := OnePoint.ne_infty_iff_exists.1 h₀
  obtain ⟨e₁, he₁⟩ := OnePoint.ne_infty_iff_exists.1 h₁
  have hne : e₀ ≠ e₁ := fun h ↦ OnePoint.coe_ne_infty (0 : ℝ)
    (MulAction.injective g (he₀.symm.trans ((congrArg _ h).trans he₁)))
  -- `∞` lies strictly on one side of the line; orient the line so that it is on the left
  rcases hne.lt_or_gt with h | h
  · have hinf := (infty_mem_boundaryLeftHalfPlane_iff he₀.symm he₁.symm).2 h
    exact iff_of_true (hpr.re_toComplex_lt hinf) (hpq.re_toComplex_lt hinf)
  · have hinf : (∞ : OnePoint ℝ) ∈ boundaryLeftHalfPlane (g * pslS) :=
      (infty_mem_boundaryLeftHalfPlane_iff (by rw [mul_smul, pslS_smul_zero, he₁])
        (by rw [mul_smul, pslS_smul_infty, he₀])).2 h
    exact iff_of_false (isGeodesicFromTo_mul_pslS_iff.2 hpr |>.re_toComplex_lt hinf).not_gt
      (isGeodesicFromTo_mul_pslS_iff.2 hpq |>.re_toComplex_lt hinf).not_gt

end TauCeti.UpperHalfPlane
