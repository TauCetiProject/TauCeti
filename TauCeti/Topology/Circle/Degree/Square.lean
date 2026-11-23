/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Circle.Degree
public import TauCeti.Topology.Homotopy.Cube.Basic

import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# The degree of a circle-valued map around the boundary of the square

Let `Γ` be a map from the square `I^(Fin 2)` to the unit circle that is continuous on the boundary
`∂I² = Cube.boundary (Fin 2)`. Running once counterclockwise around the boundary, starting from
the corner `(0, 0)` (`TauCeti.squareBoundaryLoop`), turns `Γ` into a loop in the circle. Its
degree is `TauCeti.squareBoundaryDegree Γ`. When the square is the sphere `I² / ∂I²` underlying
the second homotopy group, this is the winding number of a clutching function along the boundary
of the disc, which is how the first Chern number of a complex vector bundle over a sphere is read
off.

The degree only sees `Γ` on the boundary (`TauCeti.squareBoundaryDegree_congr`), and it has the
laws of a winding number:

* **products:** for `Γ` and `Γ'` continuous on the boundary,
  `deg (Γ * Γ') = deg Γ + deg Γ'` (`TauCeti.squareBoundaryDegree_mul`), and hence
  `deg (Γ ^ n) = n deg Γ` (`TauCeti.squareBoundaryDegree_pow`);
* **inverses:** `deg Γ⁻¹ = -deg Γ` (`TauCeti.squareBoundaryDegree_inv`);
* **maps defined on the whole square:** if `Γ` is continuous on all of `I²`, its boundary loop is
  null-homotopic, so `deg Γ = 0` (`TauCeti.squareBoundaryDegree_eq_zero_of_continuous`), and
  multiplying any map by `Γ` does not change its degree
  (`TauCeti.squareBoundaryDegree_mul_of_continuous`);
* **homotopy:** a family `H (τ, ·)`, `τ ∈ I`, continuous on `I × ∂I²`, has constant degree
  (`TauCeti.squareBoundaryDegree_eq_of_homotopy`);
* **subdivision:** if `Γ` is also continuous on the vertical segment `s = 1/2`, the degree of `Γ`
  is the sum of the degrees of its two halves, read through the affine maps
  `TauCeti.cubeLeftHalf 0` and `TauCeti.cubeRightHalf 0` of `I²` onto `s ≤ 1/2` and `s ≥ 1/2`
  (`TauCeti.squareBoundaryDegree_eq_add`). This is the subdivision along the first coordinate
  that Mathlib uses to multiply classes of `π₂` (`GenLoop.transAt 0`).

The proofs read the degree as the sum of the angles swept along the four edges
(`Circle.angleChange`): the shared edge `s = 1/2` of the two halves is run once in each
direction and cancels.

The basic map of nonzero degree is the direction `TauCeti.squareCenterDirection` of a point from
the centre of the square, the point `c / ‖c‖` of the circle for its offset
`c = (s - 1/2) + (t - 1/2) i` from the centre (`TauCeti.squareCenterOffset`). Its degree is `1`
(`TauCeti.squareBoundaryDegree_squareCenterDirection`): along each edge the direction sweeps a
quarter turn, as the arguments of the corners `(±1 ± i) / 2` show.

## Main definitions

* `TauCeti.squareBoundaryLoop`: the boundary of the square as a loop based at `(0, 0)`.
* `TauCeti.squareBoundaryDegree`: the degree of a circle-valued map around the boundary.
* `TauCeti.squareCenterOffset`, `TauCeti.squareCenterDirection`: the offset of a point of the
  square from the centre, as a complex number, and its direction.

## Main results

* `TauCeti.squareBoundaryDegree_eq_degree`: the degree is that of the loop `Γ ∘ ∂I²`.
* `TauCeti.squareBoundaryDegree_congr`, `TauCeti.squareBoundaryDegree_mul`,
  `TauCeti.squareBoundaryDegree_pow`, `TauCeti.squareBoundaryDegree_inv`,
  `TauCeti.squareBoundaryDegree_eq_zero_of_continuous`,
  `TauCeti.squareBoundaryDegree_mul_of_continuous`,
  `TauCeti.squareBoundaryDegree_eq_of_homotopy`, `TauCeti.squareBoundaryDegree_eq_add`: the laws
  above.
* `TauCeti.squareBoundaryDegree_squareCenterDirection`: the direction from the centre has
  degree `1`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, Section 1.2 (clutching functions and the winding
  number of a map from the boundary of a disc to the circle).
-/

public section

noncomputable section

open Set Function
open scoped unitInterval Topology.Homotopy

namespace TauCeti

/-! ### The boundary loop -/

/-- The bottom edge `s ↦ (s, 0)` of the square. -/
private def squareBottom : Path (![0, 0] : Fin 2 → I) ![1, 0] where
  toFun s := ![s, 0]
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The right edge `t ↦ (1, t)` of the square. -/
private def squareRight : Path (![1, 0] : Fin 2 → I) ![1, 1] where
  toFun t := ![1, t]
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The top edge `s ↦ (s, 1)` of the square. -/
private def squareTop : Path (![0, 1] : Fin 2 → I) ![1, 1] where
  toFun s := ![s, 1]
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The left edge `t ↦ (0, t)` of the square. -/
private def squareLeft : Path (![0, 0] : Fin 2 → I) ![0, 1] where
  toFun t := ![0, t]
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

private theorem range_squareBottom : range squareBottom ⊆ Cube.boundary (Fin 2) := by
  rintro _ ⟨s, rfl⟩
  exact ⟨1, Or.inl rfl⟩

private theorem range_squareRight : range squareRight ⊆ Cube.boundary (Fin 2) := by
  rintro _ ⟨t, rfl⟩
  exact ⟨0, Or.inr rfl⟩

private theorem range_squareTop : range squareTop ⊆ Cube.boundary (Fin 2) := by
  rintro _ ⟨s, rfl⟩
  exact ⟨1, Or.inr rfl⟩

private theorem range_squareLeft : range squareLeft ⊆ Cube.boundary (Fin 2) := by
  rintro _ ⟨t, rfl⟩
  exact ⟨0, Or.inl rfl⟩

/-- The boundary of the square `I^(Fin 2)` as a loop based at the corner `(0, 0)`, run once
counterclockwise: along the bottom edge, up the right edge, back along the top edge and down the
left edge. -/
def squareBoundaryLoop : Path (![0, 0] : Fin 2 → I) ![0, 0] :=
  squareBottom.trans (squareRight.trans (squareTop.symm.trans squareLeft.symm))

/-- The boundary loop of the square runs in the boundary of the square. -/
theorem range_squareBoundaryLoop_subset : range squareBoundaryLoop ⊆ Cube.boundary (Fin 2) := by
  simp only [squareBoundaryLoop, Path.trans_range, Path.symm_range, union_subset_iff]
  exact ⟨range_squareBottom, range_squareRight, range_squareTop, range_squareLeft⟩

/-! ### The degree around the boundary -/

open Classical in
/-- The **degree of a circle-valued map around the boundary of the square**: the degree of the
loop `t ↦ Γ (∂I² t)` obtained by running once counterclockwise around the boundary of the square
`I^(Fin 2)` (`TauCeti.squareBoundaryLoop`). It is defined when `Γ` is continuous on the boundary,
and is `0` otherwise. -/
def squareBoundaryDegree (Γ : (Fin 2 → I) → Circle) : ℤ :=
  if h : ContinuousOn Γ (Cube.boundary (Fin 2)) then
    Circle.degree (squareBoundaryLoop.map' (h.mono range_squareBoundaryLoop_subset))
  else 0

variable {Γ Γ' : (Fin 2 → I) → Circle}

/-- For a map continuous on the boundary of the square, `TauCeti.squareBoundaryDegree` is the
degree of its boundary loop. -/
theorem squareBoundaryDegree_eq_degree (h : ContinuousOn Γ (Cube.boundary (Fin 2))) :
    squareBoundaryDegree Γ =
      Circle.degree (squareBoundaryLoop.map' (h.mono range_squareBoundaryLoop_subset)) :=
  dite_eq_left h

/-- A map that is not continuous on the boundary of the square is given degree `0`. -/
theorem squareBoundaryDegree_of_not_continuousOn (h : ¬ContinuousOn Γ (Cube.boundary (Fin 2))) :
    squareBoundaryDegree Γ = 0 :=
  dite_eq_right h

/-- The degree around the boundary only depends on the values on the boundary. -/
theorem squareBoundaryDegree_congr (h : EqOn Γ Γ' (Cube.boundary (Fin 2))) :
    squareBoundaryDegree Γ = squareBoundaryDegree Γ' := by
  by_cases hΓ : ContinuousOn Γ (Cube.boundary (Fin 2))
  · have hΓ' : ContinuousOn Γ' (Cube.boundary (Fin 2)) := hΓ.congr h.symm
    rw [squareBoundaryDegree_eq_degree hΓ, squareBoundaryDegree_eq_degree hΓ']
    exact Circle.degree_congr _ _ fun t ↦ h (range_squareBoundaryLoop_subset (mem_range_self t))
  · have hΓ' : ¬ContinuousOn Γ' (Cube.boundary (Fin 2)) := fun hΓ' ↦ hΓ (hΓ'.congr h)
    rw [squareBoundaryDegree_of_not_continuousOn hΓ, squareBoundaryDegree_of_not_continuousOn hΓ']

/-- A constant map has degree `0` around the boundary of the square. -/
@[simp]
theorem squareBoundaryDegree_const (c : Circle) : squareBoundaryDegree (fun _ ↦ c) = 0 := by
  rw [squareBoundaryDegree_eq_degree continuousOn_const, ← Circle.degree_refl c]
  exact Circle.degree_congr _ _ fun _ ↦ rfl

/-- **Products.** The degree around the boundary of the square of a pointwise product of maps
continuous on the boundary is the sum of their degrees. -/
theorem squareBoundaryDegree_mul (hΓ : ContinuousOn Γ (Cube.boundary (Fin 2)))
    (hΓ' : ContinuousOn Γ' (Cube.boundary (Fin 2))) :
    squareBoundaryDegree (Γ * Γ') = squareBoundaryDegree Γ + squareBoundaryDegree Γ' := by
  rw [squareBoundaryDegree_eq_degree (hΓ.mul hΓ'), squareBoundaryDegree_eq_degree hΓ,
    squareBoundaryDegree_eq_degree hΓ', ← Circle.degree_mul]
  exact Circle.degree_congr _ _ fun _ ↦ rfl

/-- **Powers.** The degree around the boundary of the square of the `n`-th power of a map
continuous on the boundary is `n` times its degree. -/
theorem squareBoundaryDegree_pow (hΓ : ContinuousOn Γ (Cube.boundary (Fin 2))) (n : ℕ) :
    squareBoundaryDegree (Γ ^ n) = n * squareBoundaryDegree Γ := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact squareBoundaryDegree_const 1
  | succ n ih =>
    rw [pow_succ, squareBoundaryDegree_mul (hΓ.pow n) hΓ, ih]
    push_cast
    ring

/-- **Inverses.** The degree around the boundary of the square of the pointwise inverse of a map
is the negative of its degree. No continuity is assumed: if `Γ` is not continuous on the boundary,
neither is `Γ⁻¹`, and both degrees are `0`. -/
@[simp]
theorem squareBoundaryDegree_inv : squareBoundaryDegree Γ⁻¹ = -squareBoundaryDegree Γ := by
  by_cases hΓ : ContinuousOn Γ (Cube.boundary (Fin 2))
  · have h := squareBoundaryDegree_mul hΓ hΓ.inv
    rw [mul_inv_cancel, Pi.one_def, squareBoundaryDegree_const] at h
    omega
  · rw [squareBoundaryDegree_of_not_continuousOn hΓ,
      squareBoundaryDegree_of_not_continuousOn fun h ↦ hΓ (by simpa using h.inv), neg_zero]

/-- **Homotopy invariance.** If `H` is continuous on `I × ∂I²`, the maps `H (0, ·)` and
`H (1, ·)` have the same degree around the boundary of the square. -/
theorem squareBoundaryDegree_eq_of_homotopy {H : I × (Fin 2 → I) → Circle}
    (hH : ContinuousOn H (univ ×ˢ Cube.boundary (Fin 2))) :
    squareBoundaryDegree (fun y ↦ H (0, y)) = squareBoundaryDegree (fun y ↦ H (1, y)) := by
  have hslice (τ : I) : ContinuousOn (fun y ↦ H (τ, y)) (Cube.boundary (Fin 2)) :=
    hH.comp (Continuous.prodMk_right τ).continuousOn fun _ hy ↦ ⟨mem_univ _, hy⟩
  rw [squareBoundaryDegree_eq_degree (hslice 0), squareBoundaryDegree_eq_degree (hslice 1)]
  -- The boundary loops of the slices `H (τ, ·)` form a homotopy of loops.
  have hcont : Continuous fun q : I × I ↦ H (q.1, squareBoundaryLoop q.2) :=
    hH.comp_continuous (by fun_prop) fun q ↦
      ⟨mem_univ _, range_squareBoundaryLoop_subset (mem_range_self _)⟩
  exact Circle.degree_eq_of_homotopy _ _ ⟨_, hcont⟩ (fun _ ↦ rfl) (fun _ ↦ rfl)
    fun τ ↦ by simp

/-- **Maps on the whole square.** A map continuous on the whole square has degree `0` around its
boundary: its boundary loop contracts within the image of the square. -/
theorem squareBoundaryDegree_eq_zero_of_continuous (h : Continuous Γ) :
    squareBoundaryDegree Γ = 0 := by
  -- Contract the square onto its corner `0`.
  have hH := squareBoundaryDegree_eq_of_homotopy
    (H := fun q ↦ Γ (cubeContraction (Fin 2) q)) (h.comp (map_continuous _)).continuousOn
  simp only [ContinuousMap.Homotopy.apply_zero, ContinuousMap.Homotopy.apply_one,
    ContinuousMap.const_apply, ContinuousMap.id_apply, squareBoundaryDegree_const] at hH
  exact hH.symm

/-- **Factors defined on the whole square.** Multiplying by a map continuous on the whole square
does not change the degree around the boundary. No continuity of `Γ` is assumed: if `Γ` is not
continuous on the boundary, neither is the product, and both degrees are `0`. -/
theorem squareBoundaryDegree_mul_of_continuous (hΓ' : Continuous Γ') :
    squareBoundaryDegree (Γ * Γ') = squareBoundaryDegree Γ := by
  by_cases hΓ : ContinuousOn Γ (Cube.boundary (Fin 2))
  · rw [squareBoundaryDegree_mul hΓ hΓ'.continuousOn,
      squareBoundaryDegree_eq_zero_of_continuous hΓ', add_zero]
  · refine (squareBoundaryDegree_of_not_continuousOn fun h ↦ hΓ ?_).trans
      (squareBoundaryDegree_of_not_continuousOn hΓ).symm
    simpa using h.mul hΓ'.inv.continuousOn

/-! ### Subdivision along the first coordinate -/

/-- The vertical segment `s = 1/2` along which the square is subdivided. -/
private def squareSeam : Set (Fin 2 → I) := {y | (y 0 : ℝ) = 1 / 2}

/-- Two points of the square agree when their coordinates agree as real numbers. -/
private theorem square_ext {y z : Fin 2 → I} (h₀ : (y 0 : ℝ) = z 0) (h₁ : (y 1 : ℝ) = z 1) :
    y = z := by
  ext i
  fin_cases i
  exacts [h₀, h₁]

private theorem mapsTo_cubeLeftHalf :
    MapsTo (cubeLeftHalf (0 : Fin 2)) (Cube.boundary (Fin 2))
      (Cube.boundary (Fin 2) ∪ squareSeam) := by
  intro y hy
  simp only [Cube.boundary, mem_ofPred_eq, Fin.exists_fin_two] at hy
  rcases hy with (hi | hi) | hi
  · exact Or.inl ⟨0, Or.inl (Subtype.ext (by simp [hi]))⟩
  · exact Or.inr (by simp [squareSeam, hi])
  · exact Or.inl ⟨1, by simpa using hi⟩

private theorem mapsTo_cubeRightHalf :
    MapsTo (cubeRightHalf (0 : Fin 2)) (Cube.boundary (Fin 2))
      (Cube.boundary (Fin 2) ∪ squareSeam) := by
  intro y hy
  simp only [Cube.boundary, mem_ofPred_eq, Fin.exists_fin_two] at hy
  rcases hy with (hi | hi) | hi
  · exact Or.inr (by simp [squareSeam, hi])
  · exact Or.inl ⟨0, Or.inr (Subtype.ext (by norm_num [hi]))⟩
  · exact Or.inl ⟨1, by simpa using hi⟩

/-- The angle swept by a map along a path of the square on which it is continuous, and `0` when it
is not continuous there. -/
private def pathAngle {a b : Fin 2 → I} (γ : Path a b) (Γ : (Fin 2 → I) → Circle) : ℝ :=
  open Classical in
  if h : ContinuousOn Γ (range γ) then Circle.angleChange (γ.map' h) else 0

private theorem pathAngle_eq {a b : Fin 2 → I} (γ : Path a b) (h : ContinuousOn Γ (range γ)) :
    pathAngle γ Γ = Circle.angleChange (γ.map' h) :=
  dite_eq_left h

/-- Two maps that agree along two paths, at corresponding times, sweep the same angle along
them. -/
private theorem pathAngle_congr {a b a' b' : Fin 2 → I} (γ : Path a b) (γ' : Path a' b')
    (h : ContinuousOn Γ (range γ)) (h' : ContinuousOn Γ' (range γ'))
    (hγ : ∀ t, Γ (γ t) = Γ' (γ' t)) : pathAngle γ Γ = pathAngle γ' Γ' := by
  rw [pathAngle_eq γ h, pathAngle_eq γ' h']
  exact Circle.angleChange_congr _ _ hγ

/-- The degree around the boundary of the square is the sum of the angles swept along the bottom
and right edges minus those swept along the top and left edges, over `2π`. -/
private theorem squareBoundaryDegree_mul_two_pi (h : ContinuousOn Γ (Cube.boundary (Fin 2))) :
    (squareBoundaryDegree Γ : ℝ) * (2 * Real.pi) = pathAngle squareBottom Γ +
      pathAngle squareRight Γ - pathAngle squareTop Γ - pathAngle squareLeft Γ := by
  rw [squareBoundaryDegree_eq_degree h, ← Circle.angleChange_eq_degree_mul,
    pathAngle_eq _ (h.mono range_squareBottom), pathAngle_eq _ (h.mono range_squareRight),
    pathAngle_eq _ (h.mono range_squareTop), pathAngle_eq _ (h.mono range_squareLeft),
    Circle.angleChange_congr _ ((squareBottom.map' (h.mono range_squareBottom)).trans
      ((squareRight.map' (h.mono range_squareRight)).trans
        ((squareTop.map' (h.mono range_squareTop)).symm.trans
          (squareLeft.map' (h.mono range_squareLeft)).symm))) fun t ↦ ?_]
  · simp only [Circle.angleChange_trans, Circle.angleChange_symm]
    ring
  · simp only [squareBoundaryLoop, Path.map', Path.trans_apply, Path.symm_apply, Path.coe_mk_mk,
      comp_apply]
    split_ifs <;> rfl

/-- Along a horizontal edge, the angle swept by `Γ` is the sum of the angles swept by its two
halves. -/
private theorem pathAngle_horizontal_eq_add {a b : Fin 2 → I} (γ : Path a b) (c : I)
    (hγ : ∀ s, γ s = ![s, c]) (h : ContinuousOn Γ (Cube.boundary (Fin 2) ∪ squareSeam))
    (hrange : range γ ⊆ Cube.boundary (Fin 2)) :
    pathAngle γ Γ = pathAngle γ (Γ ∘ cubeLeftHalf 0) + pathAngle γ (Γ ∘ cubeRightHalf 0) := by
  have hL : ContinuousOn (Γ ∘ cubeLeftHalf 0) (range γ) :=
    (h.comp (map_continuous _).continuousOn mapsTo_cubeLeftHalf).mono hrange
  have hR : ContinuousOn (Γ ∘ cubeRightHalf 0) (range γ) :=
    (h.comp (map_continuous _).continuousOn mapsTo_cubeRightHalf).mono hrange
  have hΓ : ContinuousOn Γ (range γ) := (h.mono subset_union_left).mono hrange
  rw [pathAngle_eq γ hΓ, pathAngle_eq γ hL, pathAngle_eq γ hR]
  refine Circle.angleChange_eq_add_of_halves _ _ _ (fun s t ht ↦ ?_) fun s t ht ↦ ?_ <;>
    simp only [Path.map', Path.coe_mk_mk, comp_apply, hγ] <;>
    exact congrArg Γ (square_ext (by simp [ht]) (by simp))

/-- An integer is the degree of `Γ` around the boundary of the square once its multiple of `2π`
is the multiple `squareBoundaryDegree Γ * 2π`. -/
private theorem squareBoundaryDegree_eq_of_mul_two_pi {n : ℤ}
    (h : (squareBoundaryDegree Γ : ℝ) * (2 * Real.pi) = n * (2 * Real.pi)) :
    squareBoundaryDegree Γ = n := by
  exact_mod_cast mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) h

/-- **Subdivision.** If `Γ` is continuous on the boundary of the square and on the vertical
segment `s = 1/2`, its degree around the boundary is the sum of the degrees of its restrictions
to the left and right halves of the square. -/
theorem squareBoundaryDegree_eq_add
    (h : ContinuousOn Γ (Cube.boundary (Fin 2) ∪ {y | (y 0 : ℝ) = 1 / 2})) :
    squareBoundaryDegree Γ =
      squareBoundaryDegree (Γ ∘ cubeLeftHalf 0) + squareBoundaryDegree (Γ ∘ cubeRightHalf 0) := by
  have hΓ : ContinuousOn Γ (Cube.boundary (Fin 2)) := h.mono subset_union_left
  have hL : ContinuousOn (Γ ∘ cubeLeftHalf 0) (Cube.boundary (Fin 2)) :=
    h.comp (map_continuous _).continuousOn mapsTo_cubeLeftHalf
  have hR : ContinuousOn (Γ ∘ cubeRightHalf 0) (Cube.boundary (Fin 2)) :=
    h.comp (map_continuous _).continuousOn mapsTo_cubeRightHalf
  -- The horizontal edges split into halves.
  have hbot := pathAngle_horizontal_eq_add squareBottom 0 (fun _ ↦ rfl) h range_squareBottom
  have htop := pathAngle_horizontal_eq_add squareTop 1 (fun _ ↦ rfl) h range_squareTop
  -- The outer vertical edges are those of the halves.
  have hright : pathAngle squareRight Γ = pathAngle squareRight (Γ ∘ cubeRightHalf 0) :=
    pathAngle_congr _ _ (hΓ.mono range_squareRight) (hR.mono range_squareRight) fun t ↦
      congrArg Γ (square_ext (by simp [squareRight]) (by simp [squareRight]))
  have hleft : pathAngle squareLeft Γ = pathAngle squareLeft (Γ ∘ cubeLeftHalf 0) :=
    pathAngle_congr _ _ (hΓ.mono range_squareLeft) (hL.mono range_squareLeft) fun t ↦
      congrArg Γ (square_ext (by simp [squareLeft]) (by simp [squareLeft]))
  -- The inner vertical edges are both the seam `s = 1/2`, and cancel.
  have hseam : pathAngle squareRight (Γ ∘ cubeLeftHalf 0) =
      pathAngle squareLeft (Γ ∘ cubeRightHalf 0) :=
    pathAngle_congr _ _ (hL.mono range_squareRight) (hR.mono range_squareLeft) fun t ↦
      congrArg Γ (square_ext (by simp [squareRight, squareLeft])
        (by simp [squareRight, squareLeft]))
  have key := squareBoundaryDegree_mul_two_pi hΓ
  rw [hbot, htop, hright, hleft] at key
  have hsum : ((squareBoundaryDegree (Γ ∘ cubeLeftHalf 0) +
      squareBoundaryDegree (Γ ∘ cubeRightHalf 0) : ℤ) : ℝ) * (2 * Real.pi) =
      (squareBoundaryDegree Γ : ℝ) * (2 * Real.pi) := by
    rw [Int.cast_add, add_mul, squareBoundaryDegree_mul_two_pi hL,
      squareBoundaryDegree_mul_two_pi hR, key, hseam]
    ring
  exact squareBoundaryDegree_eq_of_mul_two_pi hsum.symm

/-! ### The direction from the centre -/

/-- The position of a point `(s, t)` of the square relative to the centre `(1/2, 1/2)`, as the
complex number `(s - 1/2) + (t - 1/2) i`. -/
def squareCenterOffset (y : Fin 2 → I) : ℂ :=
  ((y 0 : ℝ) - 1 / 2 : ℝ) + ((y 1 : ℝ) - 1 / 2 : ℝ) * Complex.I

/-- The real part of the offset from the centre is `s - 1/2`. -/
@[simp]
theorem re_squareCenterOffset (y : Fin 2 → I) : (squareCenterOffset y).re = (y 0 : ℝ) - 1 / 2 := by
  simp [squareCenterOffset]

/-- The imaginary part of the offset from the centre is `t - 1/2`. -/
@[simp]
theorem im_squareCenterOffset (y : Fin 2 → I) : (squareCenterOffset y).im = (y 1 : ℝ) - 1 / 2 := by
  simp [squareCenterOffset]

@[fun_prop]
theorem continuous_squareCenterOffset : Continuous squareCenterOffset := by
  unfold squareCenterOffset
  fun_prop

/-- The centre of the square is not on its boundary. -/
theorem squareCenterOffset_ne_zero_of_mem {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    squareCenterOffset y ≠ 0 := by
  intro h0
  simp only [Complex.ext_iff, re_squareCenterOffset, im_squareCenterOffset, Complex.zero_re,
    Complex.zero_im, sub_eq_zero] at h0
  obtain ⟨i, hi | hi⟩ := hy <;> fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] at hi <;>
    norm_num [hi] at h0

/-- The direction of a point of the square from its centre, the point `c / ‖c‖` of the circle for
`c = squareCenterOffset y` (`TauCeti.coe_squareCenterDirection`). It is `1` at the centre. -/
def squareCenterDirection (y : Fin 2 → I) : Circle :=
  Circle.exp (Complex.arg (squareCenterOffset y))

/-- Away from the centre, the direction from the centre is `c / ‖c‖` for the offset `c`. -/
theorem coe_squareCenterDirection {y : Fin 2 → I} (hy : squareCenterOffset y ≠ 0) :
    (squareCenterDirection y : ℂ) = squareCenterOffset y / ‖squareCenterOffset y‖ := by
  rw [squareCenterDirection, Circle.coe_exp, Complex.exp_arg_mul_I hy]

/-- The direction from the centre is continuous on the boundary of the square. -/
theorem continuousOn_squareCenterDirection :
    ContinuousOn squareCenterDirection (Cube.boundary (Fin 2)) :=
  (Topology.IsInducing.subtypeVal.continuousOn_iff).2 <|
    (continuous_squareCenterOffset.continuousOn.div
      (Complex.continuous_ofReal.comp continuous_squareCenterOffset.norm).continuousOn
      fun y hy ↦ by simpa using squareCenterOffset_ne_zero_of_mem hy).congr
    fun y hy ↦ coe_squareCenterDirection (squareCenterOffset_ne_zero_of_mem hy)

/-- Along a path of the square, the angle swept by a map is the change of any continuous lift of
it along `Circle.exp`. -/
private theorem pathAngle_eq_sub {a b : Fin 2 → I} (γ : Path a b) (h : ContinuousOn Γ (range γ))
    {θ : I → ℝ} (hθ : Continuous θ) (hθΓ : ∀ t, Circle.exp (θ t) = Γ (γ t)) :
    pathAngle γ Γ = θ 1 - θ 0 := by
  rw [pathAngle_eq γ h]
  exact Circle.angleChange_eq_sub _ hθ hθΓ

/-- Along an edge of the square that avoids the closed negative real axis, as seen from the
centre, the direction from the centre sweeps the angle between the arguments of the ends. -/
private theorem pathAngle_squareCenterDirection_eq_arg_sub {a b : Fin 2 → I} (γ : Path a b)
    (hrange : range γ ⊆ Cube.boundary (Fin 2))
    (hslit : ∀ t, squareCenterOffset (γ t) ∈ Complex.slitPlane) :
    pathAngle γ squareCenterDirection =
      Complex.arg (squareCenterOffset b) - Complex.arg (squareCenterOffset a) := by
  rw [pathAngle_eq_sub γ (continuousOn_squareCenterDirection.mono hrange)
    (continuous_iff_continuousAt.2 fun t ↦ (Complex.continuousAt_arg (hslit t)).comp
      (f := fun s ↦ squareCenterOffset (γ s)) (by fun_prop)) fun t ↦ rfl]
  simp only [comp_apply, Path.source, Path.target]

/-- Along an edge of the square that avoids the closed positive real axis, as seen from the
centre, the direction from the centre sweeps the angle between the arguments of the negated
ends. -/
private theorem pathAngle_squareCenterDirection_eq_arg_neg_sub {a b : Fin 2 → I} (γ : Path a b)
    (hrange : range γ ⊆ Cube.boundary (Fin 2))
    (hslit : ∀ t, -squareCenterOffset (γ t) ∈ Complex.slitPlane) :
    pathAngle γ squareCenterDirection =
      Complex.arg (-squareCenterOffset b) - Complex.arg (-squareCenterOffset a) := by
  have hθ : Continuous fun t ↦ Complex.arg (-squareCenterOffset (γ t)) + Real.pi :=
    (continuous_iff_continuousAt.2 fun t ↦ (Complex.continuousAt_arg (hslit t)).comp
      (f := fun s ↦ -squareCenterOffset (γ s)) (by fun_prop)).add continuous_const
  rw [pathAngle_eq_sub γ (continuousOn_squareCenterDirection.mono hrange) hθ
    fun t ↦ Circle.ext ?_]
  · simp only [Path.source, Path.target]
    ring
  have hne := squareCenterOffset_ne_zero_of_mem (hrange (mem_range_self t))
  rw [Circle.exp_add, Circle.coe_mul, Circle.coe_exp, Complex.exp_arg_mul_I (neg_ne_zero.2 hne),
    coe_squareCenterDirection hne, Circle.coe_exp, Complex.exp_pi_mul_I, norm_neg]
  ring

/-- **The direction from the centre has degree one.** Running once counterclockwise around the
boundary of the square, the direction of the point from the centre of the square turns once
counterclockwise around the circle. -/
theorem squareBoundaryDegree_squareCenterDirection :
    squareBoundaryDegree squareCenterDirection = 1 := by
  -- The four edges, read through the arguments of the corners as seen from the centre.
  have hbot := pathAngle_squareCenterDirection_eq_arg_sub squareBottom range_squareBottom
    fun t ↦ Complex.mem_slitPlane_iff.2 (Or.inr (by norm_num [squareBottom]))
  have hright := pathAngle_squareCenterDirection_eq_arg_sub squareRight range_squareRight
    fun t ↦ Complex.mem_slitPlane_iff.2 (Or.inl (by norm_num [squareRight]))
  have htop := pathAngle_squareCenterDirection_eq_arg_sub squareTop range_squareTop
    fun t ↦ Complex.mem_slitPlane_iff.2 (Or.inr (by norm_num [squareTop]))
  have hleft := pathAngle_squareCenterDirection_eq_arg_neg_sub squareLeft range_squareLeft
    fun t ↦ Complex.mem_slitPlane_iff.2 (Or.inl (by norm_num [squareLeft]))
  -- Every corner is `±z` or `±conj z` for the upper right corner `z = (1 + i) / 2`.
  set z : ℂ := squareCenterOffset ![1, 1]
  have hz : 0 < z.im := by norm_num [z]
  have h00 : squareCenterOffset ![0, 0] = -z := by apply Complex.ext <;> norm_num [z]
  have h10 : squareCenterOffset ![1, 0] = (starRingEnd ℂ) z := by
    apply Complex.ext <;> norm_num [z]
  have h01 : squareCenterOffset ![0, 1] = -(starRingEnd ℂ) z := by
    apply Complex.ext <;> norm_num [z]
  have hconj : Complex.arg ((starRingEnd ℂ) z) = -Complex.arg z := by
    have hπ : Complex.arg z ≠ Real.pi := fun h ↦ hz.ne' (Complex.arg_eq_pi_iff.1 h).2
    simp [Complex.arg_conj, hπ]
  have key := squareBoundaryDegree_mul_two_pi continuousOn_squareCenterDirection
  rw [hbot, hright, htop, hleft, h00, h10, h01, neg_neg, neg_neg,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz,
    Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hz), hconj] at key
  exact squareBoundaryDegree_eq_of_mul_two_pi (by rw [key]; push_cast; ring)

end TauCeti
