/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import Mathlib.Analysis.Convex.Star
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Homotopy.Basic

/-!
# Milnor's retraction of a handle onto a lower sublevel with a cell attached

Near a nondegenerate critical point of index `λ` with critical value `c`, a Morse function has the
form `f = c - ‖u‖² + ‖v‖²`, where `u ∈ Eᵤ` runs over the `λ` negative directions and `v ∈ Eₛ`
over the positive ones; these are the unstable and stable directions of the negative gradient
flow. Passing the critical level attaches the `λ`-cell `e = {‖u‖² ≤ ε, v = 0}` to the
lower sublevel `{f ≤ c - ε}`. In the quadratic model, the union of the lower sublevel and the cell
is `TauCeti.quadraticSublevelUnionCell ε`, consisting of the points `(u, v)` with
`-‖u‖² + ‖v‖² ≤ -ε` or with `‖u‖² ≤ ε` and `v = 0`. Equivalently, it is the set of points with
`‖v‖ ≤ √(‖u‖² - ε)` (`TauCeti.mem_quadraticSublevelUnionCell_iff_norm_le`), using that the real
square root of a negative number is `0`.

This file constructs Milnor's deformation `r_t` of the quadratic model onto that set. The end map
`TauCeti.quadraticHandleRetraction ε` keeps `u` and retracts `v` radially onto the closed ball of
radius `√(‖u‖² - ε)`; its fixed points are exactly the points of
`TauCeti.quadraticSublevelUnionCell ε`. The homotopy `TauCeti.quadraticHandleDeformation ε` moves
`v` along the segment from this retraction back to `v`, and fixes
`TauCeti.quadraticSublevelUnionCell ε` throughout. In Milnor's three cases: points
with `‖u‖² ≤ ε` move along `(u, t v)` and end on the cell, points with
`ε ≤ ‖u‖² ≤ ‖v‖² + ε` end on the level `-‖u‖² + ‖v‖² = -ε`, and points of the lower sublevel stay
fixed.

At every time the deformation multiplies `v` by a scalar in `[0, 1]`
(`TauCeti.exists_quadraticHandleDeformation_apply_eq_smul`). Hence it preserves every set whose
fibres `{v | (u, v) ∈ X}` are star-shaped about the origin, and
`X ∩ quadraticSublevelUnionCell ε` is a strong deformation retract of each such `X`
(`TauCeti.exists_inter_quadraticSublevelUnionCell_deformation`). Such sets include every sublevel
of a function which, for fixed `u`, does not decrease when `v` is scaled up; Milnor applies the
deformation to the sublevel `{F ≤ c - ε}` of a function `F = f - μ(‖u‖² + 2‖v‖²)` modified near the
critical point; that sublevel is `{f ≤ c - ε}` together with a handle around the cell.

## Main declarations

* `TauCeti.quadraticSublevelUnionCell`: the lower quadratic sublevel together with the cell.
* `TauCeti.quadraticHandleRetraction`: the retraction onto
  `TauCeti.quadraticSublevelUnionCell ε`, with `TauCeti.quadraticHandleRetraction_mem` and
  `TauCeti.quadraticHandleRetraction_eq_self_iff`.
* `TauCeti.quadraticHandleDeformation`: the deformation from the retraction to the identity,
  relative to `TauCeti.quadraticSublevelUnionCell ε`.
* `TauCeti.quadraticHandleDeformation_mem_of_starConvex`: the deformation preserves sets with
  star-shaped fibres.
* `TauCeti.exists_inter_quadraticSublevelUnionCell_deformation`: the strong deformation retraction
  of such a set onto its intersection with `TauCeti.quadraticSublevelUnionCell ε`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 3.2.
-/

public section

open Set unitInterval

noncomputable section

namespace TauCeti

variable {Eᵤ Eₛ : Type*} [NormedAddCommGroup Eᵤ] [NormedAddCommGroup Eₛ] {ε : ℝ}
  {z : Eᵤ × Eₛ}

/-! ### The lower sublevel with the cell attached -/

/-- The lower sublevel `{-‖u‖² + ‖v‖² ≤ -ε}` of the quadratic model `-‖u‖² + ‖v‖²` of a Morse
function at a critical point, together with the cell `{‖u‖² ≤ ε, v = 0}` of radius `√ε` in the
negative directions `u`. -/
def quadraticSublevelUnionCell (ε : ℝ) : Set (Eᵤ × Eₛ) :=
  {z | -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ -ε} ∪ {z | ‖z.1‖ ^ 2 ≤ ε ∧ z.2 = 0}

@[simp]
theorem mem_quadraticSublevelUnionCell :
    z ∈ quadraticSublevelUnionCell ε ↔
      -‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ -ε ∨ ‖z.1‖ ^ 2 ≤ ε ∧ z.2 = 0 :=
  Iff.rfl

/-- A point lies in the lower quadratic sublevel with the cell attached exactly when its positive
component has norm at most `√(‖u‖² - ε)`. -/
theorem mem_quadraticSublevelUnionCell_iff_norm_le :
    z ∈ quadraticSublevelUnionCell ε ↔ ‖z.2‖ ≤ √(‖z.1‖ ^ 2 - ε) := by
  rw [mem_quadraticSublevelUnionCell]
  rcases le_total 0 (‖z.1‖ ^ 2 - ε) with h | h
  · rw [Real.le_sqrt (norm_nonneg _) h]
    constructor
    · rintro (h' | ⟨-, h'⟩)
      · linarith
      · simpa [h'] using h
    · exact fun h' ↦ .inl (by linarith)
  · rw [Real.sqrt_eq_zero'.2 h, norm_le_zero_iff]
    constructor
    · rintro (h' | ⟨-, h'⟩)
      · have h₂ : ‖z.2‖ ^ 2 ≤ 0 := by linarith
        simpa using h₂
      · exact h'
    · exact fun h' ↦ .inr ⟨by linarith, h'⟩

/-! ### The retraction -/

variable [NormedSpace ℝ Eₛ]

/-- **Milnor's retraction** of the quadratic model onto `TauCeti.quadraticSublevelUnionCell ε`:
it keeps `u` and retracts `v` radially onto the closed ball of radius `√(‖u‖² - ε)`. -/
def quadraticHandleRetraction (ε : ℝ) : C(Eᵤ × Eₛ, Eᵤ × Eₛ) where
  toFun z := (z.1, radialRetraction √(‖z.1‖ ^ 2 - ε) z.2)
  continuous_toFun := continuous_fst.prodMk
    ((by fun_prop : Continuous fun z : Eᵤ × Eₛ ↦ √(‖z.1‖ ^ 2 - ε)).radialRetraction
      (fun _ ↦ Real.sqrt_nonneg _) continuous_snd)

@[simp]
theorem quadraticHandleRetraction_apply (ε : ℝ) (z : Eᵤ × Eₛ) :
    quadraticHandleRetraction ε z = (z.1, radialRetraction √(‖z.1‖ ^ 2 - ε) z.2) :=
  (rfl)

/-- The retraction takes values in the lower quadratic sublevel with the cell attached. -/
theorem quadraticHandleRetraction_mem (ε : ℝ) (z : Eᵤ × Eₛ) :
    quadraticHandleRetraction ε z ∈ quadraticSublevelUnionCell ε := by
  rw [mem_quadraticSublevelUnionCell_iff_norm_le, quadraticHandleRetraction_apply,
    norm_radialRetraction (Real.sqrt_nonneg _)]
  exact min_le_right _ _

/-- The fixed points of the retraction are exactly the points of the lower quadratic sublevel with
the cell attached. -/
theorem quadraticHandleRetraction_eq_self_iff :
    quadraticHandleRetraction ε z = z ↔ z ∈ quadraticSublevelUnionCell ε := by
  refine ⟨fun h ↦ h ▸ quadraticHandleRetraction_mem ε z, fun h ↦ ?_⟩
  rw [quadraticHandleRetraction_apply,
    radialRetraction_of_norm_le (mem_quadraticSublevelUnionCell_iff_norm_le.1 h)]

/-! ### The deformation -/

/-- **Milnor's deformation** of the quadratic model onto `TauCeti.quadraticSublevelUnionCell ε`:
at time `t` it keeps `u` and replaces `v` by `(1 - t) r(v) + t v`, where `r(v)` is the radial
retraction of `v` onto the closed ball of radius `√(‖u‖² - ε)`. It is a homotopy from
`TauCeti.quadraticHandleRetraction ε` to the identity which fixes
`TauCeti.quadraticSublevelUnionCell ε`. -/
def quadraticHandleDeformation (ε : ℝ) :
    (quadraticHandleRetraction ε).HomotopyRel (ContinuousMap.id (Eᵤ × Eₛ))
      (quadraticSublevelUnionCell ε) where
  toFun p :=
    (p.2.1, (1 - (p.1 : ℝ)) • radialRetraction √(‖p.2.1‖ ^ 2 - ε) p.2.2 + (p.1 : ℝ) • p.2.2)
  continuous_toFun := by
    have hr : Continuous fun p : I × (Eᵤ × Eₛ) ↦ radialRetraction √(‖p.2.1‖ ^ 2 - ε) p.2.2 :=
      (by fun_prop : Continuous fun p : I × (Eᵤ × Eₛ) ↦ √(‖p.2.1‖ ^ 2 - ε)).radialRetraction
        (fun _ ↦ Real.sqrt_nonneg _) (by fun_prop)
    fun_prop
  map_zero_left z := by simp
  map_one_left z := by simp
  prop' t z hz := by
    rw [mem_quadraticSublevelUnionCell_iff_norm_le] at hz
    simp only [ContinuousMap.coe_mk, quadraticHandleRetraction_apply,
      radialRetraction_of_norm_le hz, ← add_smul, sub_add_cancel, one_smul]

@[simp]
theorem quadraticHandleDeformation_apply (ε : ℝ) (t : I) (z : Eᵤ × Eₛ) :
    quadraticHandleDeformation ε (t, z) =
      (z.1, (1 - (t : ℝ)) • radialRetraction √(‖z.1‖ ^ 2 - ε) z.2 + (t : ℝ) • z.2) :=
  (rfl)

/-- At every time, the deformation keeps `u` and multiplies `v` by a scalar in `[0, 1]`. -/
theorem exists_quadraticHandleDeformation_apply_eq_smul (ε : ℝ) (t : I) (z : Eᵤ × Eₛ) :
    ∃ s ∈ Icc (0 : ℝ) 1, quadraticHandleDeformation ε (t, z) = (z.1, s • z.2) := by
  set a := min 1 (√(‖z.1‖ ^ 2 - ε) / ‖z.2‖)
  have ha₀ : 0 ≤ a := le_min zero_le_one (by positivity)
  have ha₁ : a ≤ 1 := min_le_left _ _
  have ht₀ : (0 : ℝ) ≤ t := nonneg t
  have ht₁ : (t : ℝ) ≤ 1 := le_one t
  refine ⟨(1 - t) * a + t, ⟨by nlinarith, by nlinarith⟩, ?_⟩
  rw [quadraticHandleDeformation_apply, radialRetraction_def, smul_smul, ← add_smul]

/-- The deformation never increases the norm of the positive component `v`. -/
theorem norm_snd_quadraticHandleDeformation_apply_le (ε : ℝ) (t : I) (z : Eᵤ × Eₛ) :
    ‖(quadraticHandleDeformation ε (t, z)).2‖ ≤ ‖z.2‖ := by
  obtain ⟨s, hs, h⟩ := exists_quadraticHandleDeformation_apply_eq_smul ε t z
  rw [h, norm_smul, Real.norm_of_nonneg hs.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hs.2

/-- The deformation preserves every set whose fibres `{v | (u, v) ∈ X}` are star-shaped about the
origin. -/
theorem quadraticHandleDeformation_mem_of_starConvex {X : Set (Eᵤ × Eₛ)}
    (hX : ∀ u, StarConvex ℝ 0 {v | (u, v) ∈ X}) (ε : ℝ) (t : I) (hz : z ∈ X) :
    quadraticHandleDeformation ε (t, z) ∈ X := by
  obtain ⟨s, hs, h⟩ := exists_quadraticHandleDeformation_apply_eq_smul ε t z
  rw [h]
  exact starConvex_zero_iff.1 (hX z.1) (by simpa using hz) hs.1 hs.2

/-- **Milnor's handle retraction.** If every fibre `{v | (u, v) ∈ X}` of `X` is star-shaped about
the origin, then `X ∩ quadraticSublevelUnionCell ε` is a strong deformation retract of `X`: there
is a retraction of `X` onto it, and a homotopy in `X` from this retraction to the identity which
fixes `X ∩ quadraticSublevelUnionCell ε`. Both are restrictions of
`TauCeti.quadraticHandleRetraction ε` and `TauCeti.quadraticHandleDeformation ε`. -/
theorem exists_inter_quadraticSublevelUnionCell_deformation {X : Set (Eᵤ × Eₛ)}
    (hX : ∀ u, StarConvex ℝ 0 {v | (u, v) ∈ X}) (ε : ℝ) :
    ∃ r : C(X, ↥(X ∩ quadraticSublevelUnionCell ε)),
      (∀ x, r (ContinuousMap.inclusion inter_subset_left x) = x) ∧
      Nonempty (((ContinuousMap.inclusion inter_subset_left).comp r).HomotopyRel
        (ContinuousMap.id X) {x | (x : Eᵤ × Eₛ) ∈ quadraticSublevelUnionCell ε}) := by
  have hmem (x : X) : quadraticHandleRetraction ε x ∈ X := by
    simpa using quadraticHandleDeformation_mem_of_starConvex hX ε 0 x.2
  refine ⟨⟨fun x ↦ ⟨quadraticHandleRetraction ε x, hmem x,
      quadraticHandleRetraction_mem ε (x : Eᵤ × Eₛ)⟩, by fun_prop⟩,
    fun x ↦ Subtype.ext (quadraticHandleRetraction_eq_self_iff.2 x.2.2), ⟨?_⟩⟩
  exact
    { toFun p := ⟨quadraticHandleDeformation ε (p.1, p.2),
        quadraticHandleDeformation_mem_of_starConvex hX ε p.1 p.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext ((quadraticHandleDeformation ε).apply_zero (x : Eᵤ × Eₛ))
      map_one_left x := Subtype.ext ((quadraticHandleDeformation ε).apply_one (x : Eᵤ × Eₛ))
      prop' t x hx := Subtype.ext ((quadraticHandleDeformation ε).eq_fst t hx) }

end TauCeti
