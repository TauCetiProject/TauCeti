/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.CompositionOuterApprox
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Algebra.Order.Module.Pi

/-!
# Examples of matched outer approximations

Small real examples for the rows `TauCeti.CompositionLift.componentRow`,
`TauCeti.CompositionLift.outerRow` and `TauCeti.CompositionLift.directRow` and for the outer
approximations `TauCeti.CompositionLift.directOuterApprox`,
`TauCeti.CompositionLift.sharedOuterApprox` and `TauCeti.CompositionLift.sharedOuterApproxOn`.
They compute the approximations exactly, check that the comparison theorems apply, and show which
of their hypotheses matter.

* The squared-coordinate model `g x = (x₀², x₁²)` on the box `[-1, 1]²` with the outer sum
  `h y = y₀ + y₁`. At the anchor `(1, 1)` the rows are `G x = (2 x₀ - 1, 2 x₁ - 1)`,
  `H y = y₀ + y₁` and `C x = 2 x₀ + 2 x₁ - 2 = H (G x)`.
* With the anchor `(1, 1)`, repeated any positive number of times, and budget one, the direct set
  and the projected shared set are both the box cut by `x₀ + x₁ ≤ 3/2`. With the empty height
  domain the shared set is empty although the direct set is not, so the height domain cannot be
  discarded. With no anchors the direct set is the box and the shared set is the box times the
  height domain.
* With the two anchors `(1, 1)` and `(-1, -1)` and budget `1/2`, the direct set is the box cut by
  `|x₀ + x₁| ≤ 5/4` and the projected shared set is the box cut by `|x₀| + |x₁| ≤ 5/4`. The
  objective `-x₀ + x₁` attains `-2`, `-5/4` and `-1` on the direct, shared and original sets, and
  `-1` on the exact lift.
* For `g x = x²`, `h = id` and budget `1/4`, the shared set at the anchor `0` projects onto the
  whole line, while the direct set at the anchor `1` is `x ≤ 5/8`: the comparison theorems need
  the same anchors on both sides.
* For `g x = x`, `h = exp`, the anchor `0` and budget two, both approximations are `x ≤ 1`, while
  the original set is `x ≤ log 2`. On `[0, ∞)` they become `[0, 1]` and `[0, log 2]`, and the
  height `0` above `0` is retained in the shared set.
* For `g x = x`, `h y = y²`, the anchor `-1` and budget one, the outer derivative `v ↦ -2 v` is
  not monotone. The inequality-height shared set projects onto the whole line and is not
  contained in the direct set `[-1, ∞)`. With exact rows on the only coordinate, the shared set
  projects onto `[-1, ∞)`, and the comparison with exact rows applies.
* For `g x = (x, x²)`, `h (u, v) = u² + v`, the anchor `-1`, budget two and exact rows on the
  first coordinate, the outer derivative `(u, v) ↦ -2 u + v` is not monotone but is nonnegative
  on the nonnegative directions `(0, t)`. Both approximations are `[-1, ∞)`, containing the
  original set `[-1, 1]`.
* With no height coordinates and at least one anchor, every row reduces to the scalar condition
  `h 0 ≤ b`, and the shared set retains the membership of the unique height `0` in `E`.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global
  optimization*, Math. Program. 103 (2005), 225–249, §2, Theorem 1.
-/

public section

open Set

namespace TauCeti.CompositionLift

/-! ### The squared-coordinate model -/

/-- The squared coordinates `x ↦ (x₀², x₁²)` of a point of the plane. -/
def sqCoords (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun j => x j ^ 2

/-- The derivative `v ↦ (2 a₀ v₀, 2 a₁ v₁)` of `sqCoords` at `a`. -/
noncomputable def sqCoordsDeriv (a : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ :=
  ContinuousLinearMap.pi fun j => (2 * a j) • ContinuousLinearMap.proj j

/-- The coordinate sum `y ↦ y₀ + y₁`. It is the outer function of the squared-coordinate model
and, being linear, its own derivative everywhere. -/
noncomputable def coordSum : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

@[simp]
theorem sqCoords_apply (x : Fin 2 → ℝ) (j : Fin 2) : sqCoords x j = x j ^ 2 :=
  (rfl)

@[simp]
theorem sqCoordsDeriv_apply (a v : Fin 2 → ℝ) (j : Fin 2) :
    sqCoordsDeriv a v j = 2 * a j * v j := by
  simp [sqCoordsDeriv, mul_assoc]

@[simp]
theorem coordSum_apply (y : Fin 2 → ℝ) : coordSum y = y 0 + y 1 := by
  simp [coordSum]

theorem hasFDerivAt_sqCoords (a : Fin 2 → ℝ) : HasFDerivAt sqCoords (sqCoordsDeriv a) a :=
  hasFDerivAt_pi'' fun j =>
    ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) j a).pow 2).congr_fderiv
      (by ext v; simp)

/-- Each squared coordinate is convex on every convex set. -/
theorem convexOn_sqCoords_apply {D : Set (Fin 2 → ℝ)} (hD : Convex ℝ D) (j : Fin 2) :
    ConvexOn ℝ D fun x => sqCoords x j :=
  ((Even.convexOn_pow even_two).comp_linearMap
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j)).subset (subset_univ _) hD

theorem convexOn_coordSum {E : Set (Fin 2 → ℝ)} (hE : Convex ℝ E) : ConvexOn ℝ E coordSum :=
  coordSum.toLinearMap.convexOn hE

theorem monotone_coordSum : Monotone coordSum := fun y y' hy => by
  simp only [coordSum_apply]
  linarith [hy 0, hy 1]

/-- The component row of the squared coordinates at the anchor `a` is `2 a_j x_j - a_j²`. -/
theorem componentRow_sqCoords_apply (a x : Fin 2 → ℝ) (j : Fin 2) :
    componentRow sqCoords a (sqCoordsDeriv a) x j = 2 * a j * x j - a j ^ 2 := by
  simp [componentRow_def]
  ring

/-- The outer row of the linear outer function `coordSum` is `coordSum` itself, whatever the inner
map and the anchor. -/
theorem outerRow_coordSum {X : Type*} (g : X → Fin 2 → ℝ) (a : X) (y : Fin 2 → ℝ) :
    outerRow g coordSum a coordSum y = y 0 + y 1 := by
  simp [outerRow_def]
  ring

/-- The direct row of the squared-coordinate model at the anchor `a`. -/
theorem directRow_sqCoords_coordSum (a x : Fin 2 → ℝ) :
    directRow sqCoords coordSum a (sqCoordsDeriv a) coordSum x =
      2 * a 0 * x 0 + 2 * a 1 * x 1 - a 0 ^ 2 - a 1 ^ 2 := by
  rw [← outerRow_componentRow, outerRow_coordSum, componentRow_sqCoords_apply,
    componentRow_sqCoords_apply]
  ring

/-! #### Rows at the anchor `(1, 1)` -/

/-- At the anchor `(1, 1)` the component row is `G x = (2 x₀ - 1, 2 x₁ - 1)`. -/
theorem componentRow_sqCoords_one (x : Fin 2 → ℝ) :
    componentRow sqCoords 1 (sqCoordsDeriv 1) x = ![2 * x 0 - 1, 2 * x 1 - 1] := by
  ext j
  fin_cases j <;> simp [componentRow_sqCoords_apply]

/-- At the anchor `(1, 1)` the direct row is `C x = 2 x₀ + 2 x₁ - 2`. -/
theorem directRow_sqCoords_one (x : Fin 2 → ℝ) :
    directRow sqCoords coordSum 1 (sqCoordsDeriv 1) coordSum x = 2 * x 0 + 2 * x 1 - 2 := by
  simp [directRow_sqCoords_coordSum]
  ring

/-- At the origin the component row at `(1, 1)` is `(-1, -1)`. -/
theorem componentRow_sqCoords_one_zero :
    componentRow sqCoords 1 (sqCoordsDeriv 1) 0 = ![-1, -1] := by
  rw [componentRow_sqCoords_one]
  norm_num

/-- At the anchor `(1, 1)` itself the direct row is `h (g a) = 2`. -/
theorem directRow_sqCoords_one_self :
    directRow sqCoords coordSum 1 (sqCoordsDeriv 1) coordSum 1 = 2 := by
  norm_num [directRow_sqCoords_one]

/-- At the origin the direct row at `(1, 1)` is `-2`. -/
theorem directRow_sqCoords_one_zero :
    directRow sqCoords coordSum 1 (sqCoordsDeriv 1) coordSum 0 = -2 := by
  norm_num [directRow_sqCoords_one]

/-- The rows are centred at the anchor: the uncentred expression `h (g a) + (Dh ∘ Dg) x`, that is
`2 x₀ + 2 x₁ + 2`, takes the value `6` at the anchor `(1, 1)` instead of `h (g a) = 2`. -/
theorem coordSum_sqCoords_one_add_comp_sqCoordsDeriv_one :
    coordSum (sqCoords 1) + (coordSum.comp (sqCoordsDeriv 1)) 1 = 6 := by
  norm_num

/-! #### One repeated anchor -/

section OneAnchor

variable {κ : Type*}

/-- With the anchor `(1, 1)`, repeated any positive number of times, and budget one, the direct
set is the box cut by `x₀ + x₁ ≤ 3/2`. -/
theorem directOuterApprox_sqCoords_const_one [Nonempty κ] :
    directOuterApprox (Icc (-1) 1) sqCoords coordSum (fun _ : κ => 1) (fun _ => sqCoordsDeriv 1)
      (fun _ => coordSum) 1 = {x | x ∈ Icc (-1) 1 ∧ x 0 + x 1 ≤ 3 / 2} := by
  ext x
  simp only [mem_directOuterApprox, directRow_sqCoords_one, forall_const, mem_ofPred_eq]
  constructor <;> rintro ⟨hx, h⟩ <;> exact ⟨hx, by linarith⟩

/-- With the anchor `(1, 1)`, repeated any positive number of times, and budget one, the shared
set projects onto the same set as the direct one. -/
theorem fst_image_sharedOuterApprox_sqCoords_const_one [Nonempty κ] :
    Prod.fst '' sharedOuterApprox (Icc (-1) 1) univ sqCoords coordSum (fun _ : κ => 1)
      (fun _ => sqCoordsDeriv 1) (fun _ => coordSum) 1 =
        {x | x ∈ Icc (-1) 1 ∧ x 0 + x 1 ≤ 3 / 2} := by
  ext x
  simp only [mem_image, mem_sharedOuterApprox, mem_univ, true_and, forall_const,
    componentRow_sqCoords_one, outerRow_coordSum, Prod.exists, exists_and_right, exists_eq_right,
    mem_ofPred_eq]
  constructor
  · rintro ⟨y, hx, hy, hb⟩
    have h0 := hy 0
    have h1 := hy 1
    simp at h0 h1
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hb⟩
    refine ⟨![2 * x 0 - 1, 2 * x 1 - 1], hx, le_rfl, ?_⟩
    simp
    linarith

/-- With the empty height domain the shared set is empty, although the direct set computed in
`directOuterApprox_sqCoords_const_one`, which involves no height domain, contains the origin. -/
theorem sharedOuterApprox_sqCoords_const_one_empty :
    sharedOuterApprox (Icc (-1) 1) ∅ sqCoords coordSum (fun _ : κ => 1)
      (fun _ => sqCoordsDeriv 1) (fun _ => coordSum) 1 = ∅ := by
  ext z
  simp

/-- With no anchors the direct set is the box. -/
theorem directOuterApprox_sqCoords_of_isEmpty [IsEmpty κ] (a : κ → Fin 2 → ℝ) (b : ℝ) :
    directOuterApprox (Icc (-1) 1) sqCoords coordSum a (fun i => sqCoordsDeriv (a i))
      (fun _ => coordSum) b = Icc (-1) 1 := by
  ext x
  simp

/-- With no anchors the shared set with exact rows on any `J` is the box times the height domain
`E`: it projects onto the box for `E = univ` and is empty for `E = ∅`. -/
theorem sharedOuterApproxOn_sqCoords_of_isEmpty [IsEmpty κ] (J : Set (Fin 2))
    (E : Set (Fin 2 → ℝ)) (a : κ → Fin 2 → ℝ) (b : ℝ) :
    sharedOuterApproxOn J (Icc (-1) 1) E sqCoords coordSum a (fun i => sqCoordsDeriv (a i))
      (fun _ => coordSum) b = Icc (-1) 1 ×ˢ E := by
  ext z
  simp

/-- For the affine inner map `g = id`, every component row is exact. -/
@[simp]
theorem componentRow_id (a x : Fin 2 → ℝ) :
    componentRow id a (ContinuousLinearMap.id ℝ (Fin 2 → ℝ)) x = x := by
  simp [componentRow_def]

/-- For the affine inner map `g = id` with the outer sum and budget one, the direct set is the box
cut by `x₀ + x₁ ≤ 1`, whatever the nonempty family of anchors. -/
theorem directOuterApprox_id_coordSum [Nonempty κ] (a : κ → Fin 2 → ℝ) :
    directOuterApprox (Icc (-1) 1) id coordSum a (fun _ => ContinuousLinearMap.id ℝ _)
      (fun _ => coordSum) 1 = {x | x ∈ Icc (-1) 1 ∧ x 0 + x 1 ≤ 1} := by
  ext x
  simp only [mem_directOuterApprox, ← outerRow_componentRow, componentRow_id, outerRow_coordSum,
    forall_const, mem_ofPred_eq]

/-- For the affine inner map `g = id` with the outer sum and budget one, the shared set projects
onto the same set as the direct one, whatever the nonempty family of anchors. -/
theorem fst_image_sharedOuterApprox_id_coordSum [Nonempty κ] (a : κ → Fin 2 → ℝ) :
    Prod.fst '' sharedOuterApprox (Icc (-1) 1) univ id coordSum a
      (fun _ => ContinuousLinearMap.id ℝ _) (fun _ => coordSum) 1 =
        {x | x ∈ Icc (-1) 1 ∧ x 0 + x 1 ≤ 1} := by
  ext x
  simp only [mem_image, mem_sharedOuterApprox, mem_univ, true_and, componentRow_id,
    outerRow_coordSum, forall_const, Prod.exists, exists_and_right, exists_eq_right,
    mem_ofPred_eq]
  constructor
  · rintro ⟨y, hx, hxy, hb⟩
    exact ⟨hx, by linarith [hxy 0, hxy 1]⟩
  · rintro ⟨hx, hb⟩
    exact ⟨x, hx, le_rfl, hb⟩

end OneAnchor

/-! #### Two opposite anchors -/

/-- The anchors `(1, 1)` and `(-1, -1)`. -/
def pmOne : Fin 2 → Fin 2 → ℝ := ![1, -1]

@[simp]
theorem pmOne_zero (j : Fin 2) : pmOne 0 j = 1 :=
  (rfl)

@[simp]
theorem pmOne_one (j : Fin 2) : pmOne 1 j = -1 :=
  (rfl)

theorem pmOne_mem_Icc (i : Fin 2) : pmOne i ∈ Icc (-1) 1 := by
  fin_cases i <;> constructor <;> intro j <;> norm_num

/-- With the anchors `(1, 1)` and `(-1, -1)` and budget `1/2`, the direct set is the box cut by
`|x₀ + x₁| ≤ 5/4`. -/
theorem directOuterApprox_sqCoords_pmOne :
    directOuterApprox (Icc (-1) 1) sqCoords coordSum pmOne (fun i => sqCoordsDeriv (pmOne i))
      (fun _ => coordSum) (1 / 2) = {x | x ∈ Icc (-1) 1 ∧ |x 0 + x 1| ≤ 5 / 4} := by
  ext x
  simp only [mem_directOuterApprox, directRow_sqCoords_coordSum, Fin.forall_fin_two, pmOne_zero,
    pmOne_one, mem_ofPred_eq, abs_le]
  refine and_congr_right fun _ => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- With the anchors `(1, 1)` and `(-1, -1)` and budget `1/2`, the shared set projects onto the box
cut by `|x₀| + |x₁| ≤ 5/4`: a common height must dominate the rows of both anchors in each
coordinate, so its coordinates are at least `2 |x_j| - 1`. -/
theorem fst_image_sharedOuterApprox_sqCoords_pmOne :
    Prod.fst '' sharedOuterApprox (Icc (-1) 1) univ sqCoords coordSum pmOne
      (fun i => sqCoordsDeriv (pmOne i)) (fun _ => coordSum) (1 / 2) =
        {x | x ∈ Icc (-1) 1 ∧ |x 0| + |x 1| ≤ 5 / 4} := by
  ext x
  simp only [mem_image, mem_sharedOuterApprox, mem_univ, true_and, outerRow_coordSum,
    Fin.forall_fin_two, Pi.le_def, componentRow_sqCoords_apply, pmOne_zero, pmOne_one,
    Prod.exists, exists_and_right, exists_eq_right, exists_and_left, mem_ofPred_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨y, ⟨⟨h00, h01⟩, hb⟩, ⟨h10, h11⟩, -⟩
    have e0 : |x 0| ≤ (y 0 + 1) / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have e1 : |x 1| ≤ (y 1 + 1) / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  · intro hb
    refine ⟨fun j => 2 * |x j| - 1, ⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      linarith [le_abs_self (x 0), le_abs_self (x 1), neg_abs_le (x 0), neg_abs_le (x 1)]

/-- The squared-coordinate model satisfies the hypotheses of
`originalSet_subset_fst_image_sharedOuterApprox` at the anchors `(1, 1)` and `(-1, -1)`. -/
theorem originalSet_subset_fst_image_sharedOuterApprox_sqCoords_pmOne :
    originalSet (Icc (-1) 1) sqCoords coordSum (1 / 2) ⊆
      Prod.fst '' sharedOuterApprox (Icc (-1) 1) univ sqCoords coordSum pmOne
        (fun i => sqCoordsDeriv (pmOne i)) (fun _ => coordSum) (1 / 2) :=
  originalSet_subset_fst_image_sharedOuterApprox (mapsTo_univ _ _)
    (convexOn_sqCoords_apply (convex_Icc _ _)) (convexOn_coordSum convex_univ) pmOne_mem_Icc
    (fun _ => (hasFDerivAt_sqCoords _).hasFDerivWithinAt)
    (fun _ => coordSum.hasFDerivAt.hasFDerivWithinAt)

/-- The squared-coordinate model satisfies the hypothesis of
`fst_image_sharedOuterApprox_subset_directOuterApprox`: its outer derivative is monotone. -/
theorem fst_image_sharedOuterApprox_subset_directOuterApprox_sqCoords_pmOne :
    Prod.fst '' sharedOuterApprox (Icc (-1) 1) univ sqCoords coordSum pmOne
        (fun i => sqCoordsDeriv (pmOne i)) (fun _ => coordSum) (1 / 2) ⊆
      directOuterApprox (Icc (-1) 1) sqCoords coordSum pmOne (fun i => sqCoordsDeriv (pmOne i))
        (fun _ => coordSum) (1 / 2) :=
  fst_image_sharedOuterApprox_subset_directOuterApprox fun _ => monotone_coordSum

theorem mem_directOuterApprox_sqCoords_pmOne :
    ![1, -1] ∈ directOuterApprox (Icc (-1) 1) sqCoords coordSum pmOne
      (fun i => sqCoordsDeriv (pmOne i)) (fun _ => coordSum) (1 / 2) := by
  rw [directOuterApprox_sqCoords_pmOne]
  refine ⟨⟨fun j => ?_, fun j => ?_⟩, ?_⟩ <;> try fin_cases j
  all_goals norm_num

/-- On the direct set the objective `-x₀ + x₁` attains its minimum `-2` at `(1, -1)`. -/
theorem isMinOn_directOuterApprox_sqCoords_pmOne :
    IsMinOn (fun x : Fin 2 → ℝ => -x 0 + x 1) (directOuterApprox (Icc (-1) 1) sqCoords coordSum
      pmOne (fun i => sqCoordsDeriv (pmOne i)) (fun _ => coordSum) (1 / 2)) ![1, -1] := by
  rw [directOuterApprox_sqCoords_pmOne]
  refine isMinOn_iff.2 fun x ⟨hx, _⟩ => ?_
  have h0 := hx.2 0
  have h1 := hx.1 1
  norm_num at h0 h1 ⊢
  linarith

theorem mem_fst_image_sharedOuterApprox_sqCoords_pmOne :
    ![5 / 8, -5 / 8] ∈ Prod.fst '' sharedOuterApprox (Icc (-1) 1) univ sqCoords coordSum pmOne
      (fun i => sqCoordsDeriv (pmOne i)) (fun _ => coordSum) (1 / 2) := by
  rw [fst_image_sharedOuterApprox_sqCoords_pmOne]
  refine ⟨⟨fun j => ?_, fun j => ?_⟩, ?_⟩ <;> try fin_cases j
  all_goals norm_num [abs_of_pos]

/-- On the projected shared set the objective `-x₀ + x₁` attains its minimum `-5/4` at
`(5/8, -5/8)`. -/
theorem isMinOn_fst_image_sharedOuterApprox_sqCoords_pmOne :
    IsMinOn (fun x : Fin 2 → ℝ => -x 0 + x 1) (Prod.fst '' sharedOuterApprox (Icc (-1) 1) univ
      sqCoords coordSum pmOne (fun i => sqCoordsDeriv (pmOne i)) (fun _ => coordSum) (1 / 2))
      ![5 / 8, -5 / 8] := by
  rw [fst_image_sharedOuterApprox_sqCoords_pmOne]
  refine isMinOn_iff.2 fun x ⟨_, hx⟩ => ?_
  norm_num
  linarith [le_abs_self (x 0), neg_abs_le (x 1)]

theorem mem_originalSet_sqCoords :
    ![1 / 2, -1 / 2] ∈ originalSet (Icc (-1) 1) sqCoords coordSum (1 / 2) := by
  refine mem_originalSet.2 ⟨⟨fun j => ?_, fun j => ?_⟩, ?_⟩ <;> try fin_cases j
  all_goals norm_num

/-- On the original set `x₀² + x₁² ≤ 1/2` the objective `-x₀ + x₁` attains its minimum `-1` at
`(1/2, -1/2)`. -/
theorem isMinOn_originalSet_sqCoords :
    IsMinOn (fun x : Fin 2 → ℝ => -x 0 + x 1) (originalSet (Icc (-1) 1) sqCoords coordSum (1 / 2))
      ![1 / 2, -1 / 2] := by
  refine isMinOn_iff.2 fun x hx => ?_
  have hb : x 0 ^ 2 + x 1 ^ 2 ≤ 1 / 2 := by simpa using (mem_originalSet.1 hx).2
  norm_num
  nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1 - 1)]

theorem mk_mem_liftedSet_sqCoords :
    (![1 / 2, -1 / 2], sqCoords ![1 / 2, -1 / 2]) ∈
      liftedSet (Icc (-1) 1) univ sqCoords coordSum (1 / 2) :=
  mk_mem_liftedSet_of_mem_originalSet (mapsTo_univ _ _) mem_originalSet_sqCoords

/-- The exact lift retains the minimum `-1` of the original problem, attained at the graph point
above `(1/2, -1/2)`. -/
theorem isMinOn_liftedSet_sqCoords :
    IsMinOn ((fun x : Fin 2 → ℝ => -x 0 + x 1) ∘ Prod.fst)
      (liftedSet (Icc (-1) 1) univ sqCoords coordSum (1 / 2))
      (![1 / 2, -1 / 2], sqCoords ![1 / 2, -1 / 2]) :=
  (isMinOn_comp_fst_liftedSet_iff (mapsTo_univ _ _) (monotone_coordSum.monotoneOn _) _ _).2
    isMinOn_originalSet_sqCoords

/-! ### One height coordinate -/

/-- The real line as a map into one height coordinate, `x ↦ (x)`. -/
def lineCoord (x : ℝ) : Fin 1 → ℝ := fun _ => x

/-- The derivative `v ↦ (v)` of `lineCoord`. -/
noncomputable def lineCoordDeriv : ℝ →L[ℝ] Fin 1 → ℝ :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ

/-- The only coordinate `y ↦ y₀` of a height vector with one coordinate. -/
noncomputable def firstCoord : (Fin 1 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0

@[simp]
theorem lineCoord_apply (x : ℝ) (j : Fin 1) : lineCoord x j = x :=
  (rfl)

@[simp]
theorem lineCoordDeriv_apply (v : ℝ) (j : Fin 1) : lineCoordDeriv v j = v :=
  (rfl)

@[simp]
theorem firstCoord_apply (y : Fin 1 → ℝ) : firstCoord y = y 0 :=
  (rfl)

theorem hasFDerivAt_lineCoord (x : ℝ) : HasFDerivAt lineCoord lineCoordDeriv x :=
  hasFDerivAt_pi'' fun _ => hasFDerivAt_id x

/-- The component row of `lineCoord` is exact at every anchor. -/
@[simp]
theorem componentRow_lineCoord (a x : ℝ) :
    componentRow lineCoord a lineCoordDeriv x = lineCoord x := by
  ext j
  simp [componentRow_def]

/-! #### Matched anchors matter -/

/-- The square `x ↦ (x²)` as a map into one height coordinate. -/
def sqLine (x : ℝ) : Fin 1 → ℝ := fun _ => x ^ 2

/-- For `g x = x²` and `h = id`, the direct row at the anchor `1` is `C x = 2 x - 1`. -/
theorem directRow_sqLine_one (x : ℝ) :
    directRow sqLine firstCoord 1 ((2 : ℝ) • lineCoordDeriv) firstCoord x = 2 * x - 1 := by
  simp [directRow_def, sqLine]
  ring

/-- For `g x = x²`, `h = id` and budget `1/4`, the direct set at the anchor `1` is `x ≤ 5/8`. -/
theorem directOuterApprox_sqLine_one :
    directOuterApprox univ sqLine firstCoord (fun _ : Unit => 1)
      (fun _ => (2 : ℝ) • lineCoordDeriv) (fun _ => firstCoord) (1 / 4) = Iic (5 / 8) := by
  ext x
  simp only [mem_directOuterApprox, mem_univ, true_and, forall_const, directRow_sqLine_one,
    mem_Iic]
  constructor <;> intro h <;> linarith

/-- For `g x = x²`, `h = id` and budget `1/4`, the shared set at the anchor `0` projects onto the
whole line. It contains `1`, which the direct set at the anchor `1` excludes, so the comparison
needs the same anchors on both sides. -/
theorem fst_image_sharedOuterApprox_sqLine_zero :
    Prod.fst '' sharedOuterApprox univ univ sqLine firstCoord (fun _ : Unit => 0)
      (fun _ => (0 : ℝ) • lineCoordDeriv) (fun _ => firstCoord) (1 / 4) = univ := by
  refine eq_univ_of_forall fun x => ⟨(x, 0), ?_, rfl⟩
  simp [componentRow_def, outerRow_def, sqLine, Pi.le_def]

/-- Both approximations of `x² ≤ 1/4` contain the original set `[-1/2, 1/2]`. -/
theorem originalSet_sqLine :
    originalSet univ sqLine firstCoord (1 / 4) = Icc (-1 / 2) (1 / 2) := by
  ext x
  simp only [mem_originalSet, mem_univ, true_and, firstCoord_apply, sqLine, mem_Icc]
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith

/-! #### An exponential outer function -/

/-- The outer function `y ↦ exp y₀`. -/
noncomputable def expFirst (y : Fin 1 → ℝ) : ℝ := Real.exp (y 0)

theorem hasFDerivAt_expFirst_zero : HasFDerivAt expFirst firstCoord (lineCoord 0) :=
  ((Real.hasDerivAt_exp _).comp_hasFDerivAt _ firstCoord.hasFDerivAt).congr_fderiv (by simp)

/-- For `g x = x` and `h = exp`, the direct row at the anchor `0` is `C x = 1 + x`. -/
theorem directRow_expFirst (x : ℝ) :
    directRow lineCoord expFirst 0 lineCoordDeriv firstCoord x = 1 + x := by
  simp [directRow_def, expFirst]

/-- For `g x = x`, `h = exp`, the anchor `0` and budget two, the direct row is `1 + x`, so the
direct set is `D ∩ (-∞, 1]`. -/
theorem directOuterApprox_expFirst (D : Set ℝ) :
    directOuterApprox D lineCoord expFirst (fun _ : Unit => 0) (fun _ => lineCoordDeriv)
      (fun _ => firstCoord) 2 = D ∩ Iic 1 := by
  ext x
  simp only [mem_directOuterApprox, forall_const, directRow_expFirst, mem_inter_iff, mem_Iic]
  exact and_congr_right fun _ => by constructor <;> intro h <;> linarith

/-- For `g x = x`, `h = exp`, the anchor `0` and budget two, the shared set on the whole line
projects onto `(-∞, 1]`. -/
theorem fst_image_sharedOuterApprox_expFirst_univ :
    Prod.fst '' sharedOuterApprox univ univ lineCoord expFirst (fun _ : Unit => 0)
      (fun _ => lineCoordDeriv) (fun _ => firstCoord) 2 = Iic 1 := by
  ext x
  simp only [mem_image, mem_sharedOuterApprox, mem_univ, true_and, forall_const,
    componentRow_lineCoord, Prod.exists, exists_and_right, exists_eq_right, mem_Iic]
  simp only [outerRow_def, expFirst, lineCoord_apply, Real.exp_zero, map_sub, firstCoord_apply,
    Pi.le_def, Fin.forall_fin_one]
  constructor
  · rintro ⟨y, hxy, hb⟩
    linarith
  · intro hx
    exact ⟨lineCoord x, le_rfl, by simp; linarith⟩

/-- The original set of `exp x ≤ 2` on `D` is `D ∩ (-∞, log 2]`. -/
theorem originalSet_expFirst (D : Set ℝ) :
    originalSet D lineCoord expFirst 2 = D ∩ Iic (Real.log 2) := by
  ext x
  simp [expFirst, ← Real.le_log_iff_exp_le two_pos]

/-- On `D = E = [0, ∞)` the shared set projects onto `[0, 1]`. -/
theorem fst_image_sharedOuterApprox_expFirst_Ici :
    Prod.fst '' sharedOuterApprox (Ici 0) (Ici 0) lineCoord expFirst (fun _ : Unit => 0)
      (fun _ => lineCoordDeriv) (fun _ => firstCoord) 2 = Icc 0 1 := by
  ext x
  simp only [mem_image, mem_sharedOuterApprox, forall_const, componentRow_lineCoord, Prod.exists,
    exists_and_right, exists_eq_right, mem_Icc, mem_Ici]
  simp only [outerRow_def, expFirst, lineCoord_apply, Real.exp_zero, map_sub, firstCoord_apply,
    Pi.le_def, Fin.forall_fin_one, Pi.zero_apply]
  constructor
  · rintro ⟨y, hx, -, hxy, hb⟩
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hx1⟩
    exact ⟨lineCoord x, hx, by simpa using hx, le_rfl, by simp; linarith⟩

/-- On `D = E = [0, ∞)` the shared set retains the height constraint: the pair `(0, 0)` lies in it
with the height `0 ∈ E`. -/
theorem mk_zero_zero_mem_sharedOuterApprox_expFirst_Ici :
    ((0 : ℝ), (0 : Fin 1 → ℝ)) ∈ sharedOuterApprox (Ici 0) (Ici 0) lineCoord expFirst
      (fun _ : Unit => 0) (fun _ => lineCoordDeriv) (fun _ => firstCoord) 2 := by
  refine mem_sharedOuterApprox.2 ⟨mem_Ici.2 le_rfl, mem_Ici.2 le_rfl, fun _ => ⟨?_, ?_⟩⟩
  · simp [Pi.le_def]
  · norm_num [outerRow_def, expFirst]

/-- On `D = E = [0, ∞)` the exponential model satisfies the hypotheses of
`originalSet_subset_fst_image_sharedOuterApprox`, with derivatives within the restricted
domains. -/
theorem originalSet_subset_fst_image_sharedOuterApprox_expFirst_Ici :
    originalSet (Ici 0) lineCoord expFirst 2 ⊆
      Prod.fst '' sharedOuterApprox (Ici 0) (Ici 0) lineCoord expFirst (fun _ : Unit => 0)
        (fun _ => lineCoordDeriv) (fun _ => firstCoord) 2 :=
  originalSet_subset_fst_image_sharedOuterApprox (fun _ hx _ => hx)
    (fun _ => LinearMap.id.convexOn (convex_Ici 0))
    ((convexOn_exp.comp_linearMap firstCoord.toLinearMap).subset (subset_univ _) (convex_Ici 0))
    (fun _ => mem_Ici.2 le_rfl) (fun _ => (hasFDerivAt_lineCoord 0).hasFDerivWithinAt)
    (fun _ => hasFDerivAt_expFirst_zero.hasFDerivWithinAt)

/-! #### Exact rows on every coordinate -/

/-- The outer function `y ↦ y₀²`. -/
def sqFirst (y : Fin 1 → ℝ) : ℝ := y 0 ^ 2

theorem hasFDerivAt_sqFirst : HasFDerivAt sqFirst ((-2 : ℝ) • firstCoord) (lineCoord (-1)) :=
  (firstCoord.hasFDerivAt.pow 2).congr_fderiv (by ext; simp)

theorem convexOn_sqFirst : ConvexOn ℝ univ sqFirst := by
  have := (Even.convexOn_pow (𝕜 := ℝ) even_two).comp_linearMap firstCoord.toLinearMap
  rwa [preimage_univ] at this

/-- The outer derivative `v ↦ -2 v₀` of `sqFirst` at `-1` is not monotone. -/
theorem not_monotone_neg_two_smul_firstCoord : ¬Monotone ((-2 : ℝ) • firstCoord) := by
  intro h
  have := h (show (0 : Fin 1 → ℝ) ≤ 1 from zero_le_one)
  norm_num at this

/-- For `g x = x`, `h y = y²` and the anchor `-1`, the outer row is `H y = -2 y - 1`. -/
theorem outerRow_sqFirst (y : Fin 1 → ℝ) :
    outerRow lineCoord sqFirst (-1) ((-2 : ℝ) • firstCoord) y = -2 * y 0 - 1 := by
  simp [outerRow_def, sqFirst]
  ring

/-- For `g x = x`, `h y = y²` and the anchor `-1`, the direct row is `C x = -2 x - 1`. -/
theorem directRow_sqFirst (x : ℝ) :
    directRow lineCoord sqFirst (-1) lineCoordDeriv ((-2 : ℝ) • firstCoord) x = -2 * x - 1 := by
  rw [← outerRow_componentRow, componentRow_lineCoord, outerRow_sqFirst, lineCoord_apply]

/-- For `g x = x`, `h y = y²`, the anchor `-1` and budget one, the direct set is `[-1, ∞)`. -/
theorem directOuterApprox_sqFirst :
    directOuterApprox univ lineCoord sqFirst (fun _ : Unit => -1) (fun _ => lineCoordDeriv)
      (fun _ => (-2 : ℝ) • firstCoord) 1 = Ici (-1) := by
  ext x
  simp only [mem_directOuterApprox, mem_univ, true_and, forall_const, directRow_sqFirst, mem_Ici]
  constructor <;> intro h <;> linarith

/-- With inequality heights only, the shared set projects onto the whole line: the height
`max x (-1)` dominates the component row `x` and satisfies the outer row. -/
theorem fst_image_sharedOuterApprox_sqFirst :
    Prod.fst '' sharedOuterApprox univ univ lineCoord sqFirst (fun _ : Unit => -1)
      (fun _ => lineCoordDeriv) (fun _ => (-2 : ℝ) • firstCoord) 1 = univ := by
  refine eq_univ_of_forall fun x => ⟨(x, lineCoord (max x (-1))), ?_, rfl⟩
  refine mem_sharedOuterApprox.2 ⟨mem_univ _, mem_univ _, fun _ => ⟨fun j => ?_, ?_⟩⟩
  · simp
  · dsimp only
    rw [outerRow_sqFirst, lineCoord_apply]
    linarith [le_max_right x (-1)]

/-- Without monotone outer derivatives the projected shared set need not lie in the direct set. -/
theorem not_fst_image_sharedOuterApprox_subset_directOuterApprox_sqFirst :
    ¬Prod.fst '' sharedOuterApprox univ univ lineCoord sqFirst (fun _ : Unit => -1)
        (fun _ => lineCoordDeriv) (fun _ => (-2 : ℝ) • firstCoord) 1 ⊆
      directOuterApprox univ lineCoord sqFirst (fun _ : Unit => -1) (fun _ => lineCoordDeriv)
        (fun _ => (-2 : ℝ) • firstCoord) 1 := by
  rw [fst_image_sharedOuterApprox_sqFirst, directOuterApprox_sqFirst]
  intro h
  have := h (mem_univ (-2 : ℝ))
  norm_num at this

/-- With exact rows on the only coordinate, the shared set projects onto `[-1, ∞)`. -/
theorem fst_image_sharedOuterApproxOn_sqFirst :
    Prod.fst '' sharedOuterApproxOn univ univ univ lineCoord sqFirst (fun _ : Unit => -1)
      (fun _ => lineCoordDeriv) (fun _ => (-2 : ℝ) • firstCoord) 1 = Ici (-1) := by
  ext x
  simp only [mem_image, mem_sharedOuterApproxOn, mem_sharedOuterApprox, mem_univ, true_and,
    forall_const, componentRow_lineCoord, outerRow_sqFirst, Prod.exists, exists_and_right,
    exists_eq_right, mem_Ici, lineCoord_apply]
  constructor
  · rintro ⟨y, ⟨-, hb⟩, hy⟩
    rw [hy 0] at hb
    linarith
  · intro hx
    exact ⟨lineCoord x, ⟨le_rfl, by simp; linarith⟩, fun _ => rfl⟩

/-- The original set of `x² ≤ 1` is `[-1, 1]`. -/
theorem originalSet_sqFirst : originalSet univ lineCoord sqFirst 1 = Icc (-1) 1 := by
  ext x
  simp only [mem_originalSet, mem_univ, true_and, sqFirst, lineCoord_apply, mem_Icc]
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith

/-- With exact rows on every coordinate, `originalSet_subset_fst_image_sharedOuterApproxOn`
applies with no convexity premise on the inner map. -/
theorem originalSet_subset_fst_image_sharedOuterApproxOn_sqFirst :
    originalSet univ lineCoord sqFirst 1 ⊆
      Prod.fst '' sharedOuterApproxOn univ univ univ lineCoord sqFirst (fun _ : Unit => -1)
        (fun _ => lineCoordDeriv) (fun _ => (-2 : ℝ) • firstCoord) 1 :=
  originalSet_subset_fst_image_sharedOuterApproxOn (mapsTo_univ _ _) (by simp)
    (fun j hj => (hj (mem_univ j)).elim) convexOn_sqFirst (fun _ => mem_univ _)
    (fun _ => (hasFDerivAt_lineCoord _).hasFDerivWithinAt)
    (fun _ => hasFDerivAt_sqFirst.hasFDerivWithinAt)

/-- With exact rows on every coordinate, `fst_image_sharedOuterApproxOn_subset_directOuterApprox`
applies to the non-monotone outer derivative `v ↦ -2 v₀`: the only permitted direction is zero. -/
theorem fst_image_sharedOuterApproxOn_subset_directOuterApprox_sqFirst :
    Prod.fst '' sharedOuterApproxOn univ univ univ lineCoord sqFirst (fun _ : Unit => -1)
        (fun _ => lineCoordDeriv) (fun _ => (-2 : ℝ) • firstCoord) 1 ⊆
      directOuterApprox univ lineCoord sqFirst (fun _ : Unit => -1) (fun _ => lineCoordDeriv)
        (fun _ => (-2 : ℝ) • firstCoord) 1 :=
  fst_image_sharedOuterApproxOn_subset_directOuterApprox fun _ => TauCeti.forall_map_nonneg_univ _

/-! #### Exact rows on one of two coordinates -/

/-- The map `x ↦ (x, x²)`. -/
def lineSq (x : ℝ) : Fin 2 → ℝ := ![x, x ^ 2]

/-- The derivative `v ↦ (v, -2 v)` of `lineSq` at `-1`. -/
noncomputable def lineSqDeriv : ℝ →L[ℝ] Fin 2 → ℝ :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.id ℝ ℝ, (-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ]

/-- The outer function `(u, v) ↦ u² + v`. -/
def sqAddSnd (y : Fin 2 → ℝ) : ℝ := y 0 ^ 2 + y 1

/-- The derivative `(u, v) ↦ -2 u + v` of `sqAddSnd` at `lineSq (-1) = (-1, 1)`. -/
noncomputable def sqAddSndDeriv : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (-2 : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

@[simp]
theorem lineSq_apply_zero (x : ℝ) : lineSq x 0 = x :=
  (rfl)

@[simp]
theorem lineSq_apply_one (x : ℝ) : lineSq x 1 = x ^ 2 :=
  (rfl)

@[simp]
theorem lineSqDeriv_apply_zero (v : ℝ) : lineSqDeriv v 0 = v :=
  (rfl)

@[simp]
theorem lineSqDeriv_apply_one (v : ℝ) : lineSqDeriv v 1 = -2 * v :=
  (rfl)

@[simp]
theorem sqAddSndDeriv_apply (y : Fin 2 → ℝ) : sqAddSndDeriv y = -2 * y 0 + y 1 := by
  simp [sqAddSndDeriv]

theorem hasFDerivAt_lineSq : HasFDerivAt lineSq lineSqDeriv (-1) := by
  refine hasFDerivAt_pi'' fun j => ?_
  fin_cases j
  · exact (hasFDerivAt_id (-1 : ℝ)).congr_fderiv (by ext; simp)
  · exact ((hasFDerivAt_id (-1 : ℝ)).pow 2).congr_fderiv (by ext; simp)

theorem hasFDerivAt_sqAddSnd : HasFDerivAt sqAddSnd sqAddSndDeriv (lineSq (-1)) :=
  (((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 _).pow 2).add
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 1 _)).congr_fderiv (by ext; simp)

theorem convexOn_sqAddSnd : ConvexOn ℝ univ sqAddSnd := by
  have h0 := (Even.convexOn_pow (𝕜 := ℝ) even_two).comp_linearMap
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0)
  rw [preimage_univ] at h0
  exact h0.add ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).convexOn convex_univ)

/-- The outer derivative `(u, v) ↦ -2 u + v` is not monotone. -/
theorem not_monotone_sqAddSndDeriv : ¬Monotone sqAddSndDeriv := by
  intro h
  have := h (show (0 : Fin 2 → ℝ) ≤ Pi.single 0 1 from Pi.single_nonneg.2 zero_le_one)
  norm_num at this

/-- At the anchor `-1` the component row of `lineSq` is `G x = (x, -2 x - 1)`. -/
theorem componentRow_lineSq (x : ℝ) :
    componentRow lineSq (-1) lineSqDeriv x = ![x, -2 * x - 1] := by
  ext j
  fin_cases j
  · simp [componentRow_def]
  · simp [componentRow_def]
    ring

/-- At the anchor `-1` the outer row is `H y = -2 y₀ + y₁ - 1`. -/
theorem outerRow_sqAddSnd (y : Fin 2 → ℝ) :
    outerRow lineSq sqAddSnd (-1) sqAddSndDeriv y = -2 * y 0 + y 1 - 1 := by
  simp [outerRow_def, sqAddSnd]
  ring

/-- At the anchor `-1` the direct row is `C x = -4 x - 2`. -/
theorem directRow_sqAddSnd (x : ℝ) :
    directRow lineSq sqAddSnd (-1) lineSqDeriv sqAddSndDeriv x = -4 * x - 2 := by
  rw [← outerRow_componentRow, outerRow_sqAddSnd, componentRow_lineSq]
  simp
  ring

/-- With budget two the direct set is `[-1, ∞)`. -/
theorem directOuterApprox_sqAddSnd :
    directOuterApprox univ lineSq sqAddSnd (fun _ : Unit => -1) (fun _ => lineSqDeriv)
      (fun _ => sqAddSndDeriv) 2 = Ici (-1) := by
  ext x
  simp only [mem_directOuterApprox, mem_univ, true_and, forall_const, directRow_sqAddSnd, mem_Ici]
  constructor <;> intro h <;> linarith

/-- With exact rows on the first coordinate and budget two, the shared set projects onto
`[-1, ∞)`. -/
theorem fst_image_sharedOuterApproxOn_sqAddSnd :
    Prod.fst '' sharedOuterApproxOn {0} univ univ lineSq sqAddSnd (fun _ : Unit => -1)
      (fun _ => lineSqDeriv) (fun _ => sqAddSndDeriv) 2 = Ici (-1) := by
  ext x
  simp only [mem_image, mem_sharedOuterApproxOn, mem_sharedOuterApprox, mem_univ, true_and,
    forall_const, componentRow_lineSq, outerRow_sqAddSnd, Prod.exists, exists_and_right,
    exists_eq_right, mem_Ici, mem_singleton_iff, forall_eq, Pi.le_def, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨y, ⟨⟨-, h1⟩, hb⟩, h0⟩
    rw [h0] at hb
    linarith
  · intro hx
    refine ⟨![x, -2 * x - 1], ⟨⟨le_rfl, le_rfl⟩, ?_⟩, rfl⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith

/-- The original set of `x² + x² ≤ 2` is `[-1, 1]`. -/
theorem originalSet_sqAddSnd : originalSet univ lineSq sqAddSnd 2 = Icc (-1) 1 := by
  ext x
  simp only [mem_originalSet, mem_univ, true_and, sqAddSnd, lineSq_apply_zero, lineSq_apply_one,
    mem_Icc]
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith

/-- The model `lineSq`, `sqAddSnd` satisfies the hypotheses of
`originalSet_subset_fst_image_sharedOuterApproxOn` with exact rows on the first coordinate. -/
theorem originalSet_subset_fst_image_sharedOuterApproxOn_sqAddSnd :
    originalSet univ lineSq sqAddSnd 2 ⊆
      Prod.fst '' sharedOuterApproxOn {0} univ univ lineSq sqAddSnd (fun _ : Unit => -1)
        (fun _ => lineSqDeriv) (fun _ => sqAddSndDeriv) 2 := by
  refine originalSet_subset_fst_image_sharedOuterApproxOn (mapsTo_univ _ _) ?_ (fun j hj => ?_)
    convexOn_sqAddSnd (fun _ => mem_univ _) (fun _ => hasFDerivAt_lineSq.hasFDerivWithinAt)
    (fun _ => hasFDerivAt_sqAddSnd.hasFDerivWithinAt)
  · rintro - x - j rfl
    simp [componentRow_lineSq]
  · obtain rfl : j = 1 := by fin_cases j <;> simp_all
    exact Even.convexOn_pow even_two

/-- The non-monotone outer derivative `(u, v) ↦ -2 u + v` is nonnegative on the nonnegative
directions `(0, t)` vanishing on the first coordinate, so
`fst_image_sharedOuterApproxOn_subset_directOuterApprox` applies. -/
theorem fst_image_sharedOuterApproxOn_subset_directOuterApprox_sqAddSnd :
    Prod.fst '' sharedOuterApproxOn {0} univ univ lineSq sqAddSnd (fun _ : Unit => -1)
        (fun _ => lineSqDeriv) (fun _ => sqAddSndDeriv) 2 ⊆
      directOuterApprox univ lineSq sqAddSnd (fun _ : Unit => -1) (fun _ => lineSqDeriv)
        (fun _ => sqAddSndDeriv) 2 := by
  refine fst_image_sharedOuterApproxOn_subset_directOuterApprox fun _ v hv hJ => ?_
  rw [sqAddSndDeriv_apply, hJ 0 rfl]
  linarith [show (0 : ℝ) ≤ v 1 from hv 1]

/-! ### No height coordinates -/

section NoHeights

variable {κ : Type*} [Nonempty κ] (D : Set ℝ) (E : Set (Fin 0 → ℝ)) (g : ℝ → Fin 0 → ℝ)
  (h : (Fin 0 → ℝ) → ℝ) (a : κ → ℝ) (Dg : κ → ℝ →L[ℝ] Fin 0 → ℝ)
  (Dh : κ → (Fin 0 → ℝ) →L[ℝ] ℝ) (b : ℝ)

/-- With no height coordinates and at least one anchor, every direct row is the scalar `h 0`. -/
theorem directOuterApprox_fin_zero :
    directOuterApprox D g h a Dg Dh b = {x | x ∈ D ∧ h 0 ≤ b} := by
  have hDh : ∀ i v, Dh i v = 0 := fun i v => by rw [Subsingleton.elim v 0, map_zero]
  ext x
  simp [directRow_def, hDh, Subsingleton.elim (g _) 0]

/-- With no height coordinates and at least one anchor, the shared set projects onto the points
of `D` satisfying `h 0 ≤ b`, provided the unique height `0` lies in `E`. -/
theorem fst_image_sharedOuterApprox_fin_zero :
    Prod.fst '' sharedOuterApprox D E g h a Dg Dh b = {x | x ∈ D ∧ 0 ∈ E ∧ h 0 ≤ b} := by
  have hDh : ∀ i v, Dh i v = 0 := fun i v => by rw [Subsingleton.elim v 0, map_zero]
  ext x
  simp only [mem_image, mem_sharedOuterApprox, outerRow_def, hDh, Subsingleton.elim (g _) 0,
    Subsingleton.elim (componentRow g _ _ _) 0, Prod.exists, exists_and_right, exists_eq_right,
    mem_ofPred_eq, add_zero, forall_const]
  constructor
  · rintro ⟨y, hx, hy, -, hb⟩
    exact ⟨hx, Subsingleton.elim y 0 ▸ hy, hb⟩
  · rintro ⟨hx, hE, hb⟩
    exact ⟨0, hx, hE, le_rfl, hb⟩

end NoHeights

end TauCeti.CompositionLift
