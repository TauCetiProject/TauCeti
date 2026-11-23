/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.CompositionOuterApprox
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

/-!
# Examples of matched outer approximations

Small real examples for the rows `TauCeti.CompositionLift.componentRow`,
`TauCeti.CompositionLift.outerRow` and `TauCeti.CompositionLift.directRow` and the outer
approximations `TauCeti.CompositionLift.directOuterApprox`,
`TauCeti.CompositionLift.sharedOuterApprox` and `TauCeti.CompositionLift.sharedOuterApproxOn`.
In the explicitly computed rows, all derivatives are the actual Fréchet derivatives of the inner
and outer functions at the anchors; the empty-height result holds for arbitrary continuous linear
row maps. The shared approximations below use unrestricted heights (every height is admissible),
except where a bullet names another height domain: the empty one of the third bullet and the
half-line `y ≥ 0` of the `exp` bullet. In particular the projected shared sets of the one-anchor,
identity-map and two-anchor bullets are computed with unrestricted heights.

* Squared coordinates `g x = (x_j ^ 2)_j` with outer sum `h y = ∑ j, y j`. At the anchor `(1, 1)`
  the rows are `G x = (2 x₀ - 1, 2 x₁ - 1)`, `H y = y₀ + y₁` and `C x = 2 x₀ + 2 x₁ - 2`, with
  `C (1, 1) = 2` and `C (0, 0) = -2`. On the box `[-1, 1]²` with budget one, any nonempty family of
  copies of this anchor gives `x₀ + x₁ ≤ 3/2` for both the direct set and the projected shared set.
* For the identity inner map and outer sum on an input domain `D`, both sets are the points of `D`
  satisfying `∑ j, x j ≤ b`, for every nonempty family of anchors.
* Without anchors the direct set and the projected shared set are the box when every height is
  admissible. With no admissible heights the shared approximation is empty, whatever the anchors,
  while the direct set of the box with budget one and copies of the anchor `(1, 1)` contains `0`:
  the height domain cannot be discarded.
* On the box `[-1, 1]²`, the two anchors `(1, 1)` and `(-1, -1)` with budget `1/2` give the
  direct set `|x₀ + x₁| ≤ 5/4` and the projected shared set `|x₀| + |x₁| ≤ 5/4`. The objective
  `-x₀ + x₁` attains `-2`, `-5/4` and `-1` on the direct set, the projected shared set and the
  original set, and the exact
  lift of `TauCeti.CompositionLift.liftedSet` retains `-1`.
* For `g x = x ^ 2` and `h = id` with budget `1/4`, the shared heights at the anchor `0` project
  onto the whole line, while the direct row at the anchor `1` is `C x = 2 x - 1`, whose budget
  constraint gives the direct set `x ≤ 5/8`: with different anchors the shared projection need not
  lie in the direct set.
* For `g = id` and `h = exp` at the anchor `0` with budget two, the direct set and the projected
  shared set are `x ≤ 1` on the line and `[0, 1]` on the half-line `x ≥ 0`, where the height
  constraint `y ≥ 0` is retained.
* For `g = id` and `h y = y ^ 2` at the anchor `-1` with budget one, the direct row is
  `C x = -2 x - 1`, whose budget constraint gives the direct set `[-1, ∞)`, while inequality
  heights project onto the whole line. So the first-coordinate projection of the shared set without
  exact rows is not contained in the direct set; the outer derivative `-2` is not monotone. With an
  exact row on the only coordinate the projection is `[-1, ∞)`.
* For `g x = (x, x ^ 2)` and `h (u, v) = u ^ 2 + v` at the anchor `-1` with budget two and an exact
  row on the first coordinate, the projected shared set and the direct set are both `[-1, ∞)`, and
  the original set is `[-1, 1]`; the outer derivative `(-2, 1)` is nonnegative on the nonnegative
  directions vanishing on the first coordinate.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global
  optimization*, Math. Program. 103 (2005), 225–249, §2, Theorem 1.
-/

public section

open Set
open ContinuousLinearMap (mul proj toSpanSingleton)

namespace TauCeti.CompositionLift

/-! ### Squared coordinates with outer sum -/

section SquaredSum

variable {ι : Type*}

/-- The component rows of the squared coordinates: `G x = (2 a_j x_j - a_j ^ 2)_j`. -/
theorem componentRow_sq [Fintype ι] (a x : ι → ℝ) :
    componentRow (fun x j ↦ x j ^ 2) a (mul ℝ _ (2 * a)) x = fun j ↦ 2 * a j * x j - a j ^ 2 := by
  ext j
  simp only [componentRow_def, Pi.add_apply, ContinuousLinearMap.mul_apply', Pi.mul_apply,
    Pi.ofNat_apply, Pi.sub_apply]
  ring

/-- The coordinatewise square has derivative `v ↦ 2 a v` at `a`, by Mathlib's power rule on the
normed ring `ι → ℝ`. -/
example [Fintype ι] (a : ι → ℝ) :
    HasFDerivAt (fun x : ι → ℝ ↦ fun j ↦ x j ^ 2) (mul ℝ _ (2 * a)) a := by
  refine (hasFDerivAt_pow (𝕜 := ℝ) 2 (x := a)).congr_fderiv ?_
  ext v j
  simp

/-- The outer sum is its own derivative, as a continuous linear map. -/
example [Fintype ι] (y : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ ↦ ∑ j, y j) (∑ j, proj j : (ι → ℝ) →L[ℝ] ℝ) y := by
  convert (∑ j, proj j : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt using 1
  ext
  simp

/-- The direct rows of the squared coordinates with outer sum: `C x = ∑ j, (2 a_j x_j - a_j ^ 2)`.
-/
theorem directRow_sq_sum [Fintype ι] (a x : ι → ℝ) :
    directRow (fun x j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) a (mul ℝ _ (2 * a)) (∑ j, proj j) x =
      ∑ j, (2 * a j * x j - a j ^ 2) := by
  simp only [directRow_sum_coord, componentRow_sq]

end SquaredSum

/-- At the anchor `(1, 1)` the component row of the squared coordinates is
`G x = (2 x₀ - 1, 2 x₁ - 1)`. -/
theorem componentRow_sq_one (x : Fin 2 → ℝ) :
    componentRow (fun x j ↦ x j ^ 2) 1 (mul ℝ _ (2 * 1)) x = ![2 * x 0 - 1, 2 * x 1 - 1] := by
  rw [componentRow_sq]
  ext j
  fin_cases j <;> simp

/-- At the anchor `(1, 1)` the direct row of the squared coordinates with outer sum is
`C x = 2 x₀ + 2 x₁ - 2`. -/
theorem directRow_sq_sum_one (x : Fin 2 → ℝ) :
    directRow (fun x j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) 1 (mul ℝ _ (2 * 1)) (∑ j, proj j) x =
      2 * x 0 + 2 * x 1 - 2 := by
  rw [directRow_sq_sum, Fin.sum_univ_two]
  simp only [Pi.one_apply]
  ring

/-- At the anchor `(1, 1)` itself, the component row of the squared coordinates is `(1, 1)`. -/
example : componentRow (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) 1 (mul ℝ _ (2 * 1)) 1 = ![1, 1] := by
  rw [componentRow_self]
  ext j
  fin_cases j <;> simp

/-- At the anchor `(1, 1)` itself, the direct row of the squared coordinates with outer sum is `2`.
-/
example :
    directRow (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) 1 (mul ℝ _ (2 * 1))
      (∑ j, proj j) 1 = 2 := by
  rw [directRow_self]
  norm_num [Fin.sum_univ_two]

/-- At the origin, the component row of the squared coordinates at the anchor `(1, 1)` is
`(-1, -1)`. -/
theorem componentRow_sq_one_zero :
    componentRow (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) 1 (mul ℝ _ (2 * 1)) 0 = ![-1, -1] := by
  rw [componentRow_sq_one]
  norm_num

/-- At the origin, the direct row of the squared coordinates with outer sum at the anchor `(1, 1)`
is `-2`, whereas the expression `h (g a) + Dh (Dg x)`, which measures from `0` instead of the
anchor, is `2` there. -/
theorem directRow_sq_sum_one_zero :
    directRow (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) 1 (mul ℝ _ (2 * 1))
      (∑ j, proj j) 0 = -2 := by
  rw [directRow_sq_sum_one]
  norm_num

/-! ### Outer approximations on the box -/

section Box

variable {κ : Type*}

/-- On the box `[-1, 1]²` with budget one, any nonempty family of copies of the anchor `(1, 1)`
gives the direct set `x₀ + x₁ ≤ 3/2` of the squared coordinates with outer sum. -/
theorem directOuterApprox_sq_sum_one [Nonempty κ] :
    directOuterApprox (Icc (-1) 1) (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j)
      (fun _ : κ ↦ 1) (fun _ ↦ mul ℝ _ (2 * 1)) (fun _ ↦ ∑ j, proj j) 1 =
      Icc (-1) 1 ∩ {x | x 0 + x 1 ≤ 3 / 2} := by
  ext x
  simp only [mem_directOuterApprox, directRow_sq_sum_one, forall_const, mem_inter_iff,
    mem_ofPred_eq]
  constructor <;> rintro ⟨hx, hb⟩ <;> exact ⟨hx, by linarith⟩

/-- On the box `[-1, 1]²` with budget one and all heights admissible, any nonempty family of copies
of the anchor `(1, 1)` gives the projected shared set `x₀ + x₁ ≤ 3/2` of the squared coordinates
with outer sum, the same as the direct set. -/
theorem fst_image_sharedOuterApprox_sq_sum_one [Nonempty κ] :
    Prod.fst '' sharedOuterApprox (Icc (-1) 1) univ (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2)
      (fun y ↦ ∑ j, y j) (fun _ : κ ↦ 1) (fun _ ↦ mul ℝ _ (2 * 1)) (fun _ ↦ ∑ j, proj j) 1 =
      Icc (-1) 1 ∩ {x | x 0 + x 1 ≤ 3 / 2} := by
  rw [← directOuterApprox_sq_sum_one (κ := κ)]
  exact fst_image_sharedOuterApprox_eq_directOuterApprox
    (fun _ _ _ hyz ↦ by simpa using Fintype.sum_mono hyz) (mapsTo_univ _ _) fun _ _ _ ↦ rfl

/-- With no admissible heights the shared approximation is empty, whatever the anchors, rows and
budget (`sharedOuterApprox_empty_heights`). Together with `directOuterApprox_sq_sum_one`, whose
direct set contains `0`, this shows that the height domain cannot be discarded. -/
example (a : κ → Fin 2 → ℝ)
    (Dg : κ → (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ) (Dh : κ → (Fin 2 → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    Prod.fst '' sharedOuterApprox (Icc (-1) 1) ∅ (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2)
      (fun y ↦ ∑ j, y j) a Dg Dh b = ∅ := by
  simp

/-- Without anchors the direct set of the squared coordinates with outer sum is the box
(`directOuterApprox_of_isEmpty`). -/
example [IsEmpty κ] (a : κ → Fin 2 → ℝ)
    (Dg : κ → (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ) (Dh : κ → (Fin 2 → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    directOuterApprox (Icc (-1) 1) (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) a Dg Dh b =
      Icc (-1) 1 := by
  rw [directOuterApprox_of_isEmpty]

/-- Without anchors and with all heights admissible, the projected shared set of the squared
coordinates with outer sum is the box (`fst_image_sharedOuterApprox_of_isEmpty`). -/
example [IsEmpty κ] (a : κ → Fin 2 → ℝ)
    (Dg : κ → (Fin 2 → ℝ) →L[ℝ] Fin 2 → ℝ) (Dh : κ → (Fin 2 → ℝ) →L[ℝ] ℝ) (b : ℝ) :
    Prod.fst '' sharedOuterApprox (Icc (-1) 1) univ (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2)
      (fun y ↦ ∑ j, y j) a Dg Dh b = Icc (-1) 1 :=
  fst_image_sharedOuterApprox_of_isEmpty univ_nonempty

end Box

/-! ### The identity inner map -/

section Affine

variable {ι κ : Type*} [Fintype ι] [Nonempty κ] {D : Set (ι → ℝ)} {b : ℝ}

/-- For the identity inner map with outer sum on the input domain `D`, every nonempty family of
anchors gives as direct set the points of `D` satisfying `∑ j, x j ≤ b`; on the box `[-1, 1]²`
with budget one this is `x₀ + x₁ ≤ 1` for the anchors `(1, 1)` and `(-1, -1)`. -/
theorem directOuterApprox_id_sum (a : κ → ι → ℝ) :
    directOuterApprox D id (fun y ↦ ∑ j, y j) a (fun _ ↦ ContinuousLinearMap.id ℝ _)
      (fun _ ↦ ∑ j, proj j) b = D ∩ {x | ∑ j, x j ≤ b} := by
  ext x
  simp [componentRow_def]

/-- For the identity inner map with outer sum on the input domain `D` and all heights admissible,
every nonempty family of anchors gives as projected shared set the points of `D` satisfying
`∑ j, x j ≤ b`, the same as the direct set. -/
theorem fst_image_sharedOuterApprox_id_sum (a : κ → ι → ℝ) :
    Prod.fst '' sharedOuterApprox D univ id (fun y ↦ ∑ j, y j) a
      (fun _ ↦ ContinuousLinearMap.id ℝ _) (fun _ ↦ ∑ j, proj j) b = D ∩ {x | ∑ j, x j ≤ b} := by
  rw [← directOuterApprox_id_sum a]
  exact fst_image_sharedOuterApprox_eq_directOuterApprox
    (fun _ _ _ hyz ↦ by simpa using Fintype.sum_mono hyz) (mapsTo_univ id _) fun _ _ _ ↦ by
      simpa only [ContinuousLinearMap.coe_id'] using
        (ContinuousLinearMap.id ℝ (ι → ℝ)).componentRow_eq_apply

end Affine

/-! ### Two opposite anchors -/

section TwoAnchors

/-- The component rows of the squared coordinates at the anchors `(1, 1)` and `(-1, -1)`:
`G x = (2 c x_j - 1)_j` for `c = ±1`. -/
private theorem componentRow_sq_one_neg_one (i : Fin 2) (x : Fin 2 → ℝ) (j : Fin 2) :
    componentRow (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (![1, -1] i) (mul ℝ _ (2 * ![1, -1] i)) x j =
      2 * ![1, -1] i * x j - 1 := by
  rw [componentRow_sq]
  fin_cases i <;> simp

/-- The direct rows of the squared coordinates with outer sum at the anchors `(1, 1)` and
`(-1, -1)`: `C x = 2 c (x₀ + x₁) - 2` for `c = ±1`. -/
private theorem directRow_sq_sum_one_neg_one (i : Fin 2) (x : Fin 2 → ℝ) :
    directRow (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) (![1, -1] i)
      (mul ℝ _ (2 * ![1, -1] i)) (∑ j, proj j) x = 2 * ![1, -1] i * (x 0 + x 1) - 2 := by
  rw [directRow_sq_sum, Fin.sum_univ_two]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.one_apply, Pi.neg_apply] <;> ring

/-- At the anchors `(1, 1)` and `(-1, -1)` with budget `1/2`, the direct set of the squared
coordinates with outer sum on the box `[-1, 1]²` is `|x₀ + x₁| ≤ 5/4`. -/
theorem directOuterApprox_sq_sum_one_neg_one :
    directOuterApprox (Icc (-1) 1) (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j)
      ![1, -1] (fun i ↦ mul ℝ _ (2 * ![1, -1] i)) (fun _ ↦ ∑ j, proj j) (1 / 2) =
      Icc (-1) 1 ∩ {x | |x 0 + x 1| ≤ 5 / 4} := by
  ext x
  simp only [mem_directOuterApprox, directRow_sq_sum_one_neg_one, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mem_inter_iff,
    mem_ofPred_eq, abs_le]
  refine and_congr_right fun _ ↦ ⟨fun ⟨_, _⟩ ↦ ⟨?_, ?_⟩, fun ⟨_, _⟩ ↦ ⟨?_, ?_⟩⟩ <;> linarith

/-- At the anchors `(1, 1)` and `(-1, -1)` with budget `1/2` and all heights admissible, the
projected shared set of the squared coordinates with outer sum on the box `[-1, 1]²` is
`|x₀| + |x₁| ≤ 5/4`: one height vector must dominate the rows of both anchors, so each height is at
least `2 |x_j| - 1`. -/
theorem fst_image_sharedOuterApprox_sq_sum_one_neg_one :
    Prod.fst '' sharedOuterApprox (Icc (-1) 1) univ (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2)
      (fun y ↦ ∑ j, y j) ![1, -1] (fun i ↦ mul ℝ _ (2 * ![1, -1] i)) (fun _ ↦ ∑ j, proj j)
      (1 / 2) = Icc (-1) 1 ∩ {x | |x 0| + |x 1| ≤ 5 / 4} := by
  ext x
  constructor
  · rintro ⟨⟨x, y⟩, hz, rfl⟩
    obtain ⟨hx, -, hrow⟩ := mem_sharedOuterApprox.1 hz
    have hb := (hrow 0).2
    rw [outerRow_sum_coord, Fin.sum_univ_two] at hb
    have hy (j : Fin 2) : 2 * |x j| - 1 ≤ y j := by
      have h0 := (hrow 0).1 j
      have h1 := (hrow 1).1 j
      rw [componentRow_sq_one_neg_one] at h0 h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
      have h : |x j| ≤ (y j + 1) / 2 := abs_le.2 ⟨by linarith, by linarith⟩
      linarith
    refine mem_inter_iff _ _ _ |>.2 ⟨hx, ?_⟩
    simp only [mem_ofPred_eq]
    linarith [hy 0, hy 1]
  · intro hx
    obtain ⟨hx, hb⟩ := mem_inter_iff _ _ _ |>.1 hx
    refine ⟨(x, fun j ↦ 2 * |x j| - 1), mem_sharedOuterApprox.2 ⟨hx, mem_univ _, fun i ↦
      ⟨fun j ↦ ?_, ?_⟩⟩, rfl⟩
    · rw [componentRow_sq_one_neg_one]
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
        linarith [le_abs_self (x j), neg_abs_le (x j)]
    · rw [outerRow_sum_coord, Fin.sum_univ_two]
      simp only [mem_ofPred_eq] at hb
      linarith

/-- The objective `-x₀ + x₁` attains its minimum `-2` on the direct set at the anchors `(1, 1)` and
`(-1, -1)` with budget `1/2`, at the corner `(1, -1)`. -/
theorem mem_and_isMinOn_directOuterApprox_sq_sum_one_neg_one :
    ![1, -1] ∈ directOuterApprox (Icc (-1) 1) (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2)
        (fun y ↦ ∑ j, y j) ![1, -1] (fun i ↦ mul ℝ _ (2 * ![1, -1] i)) (fun _ ↦ ∑ j, proj j)
        (1 / 2) ∧
      IsMinOn (fun x : Fin 2 → ℝ ↦ -x 0 + x 1) (directOuterApprox (Icc (-1) 1)
        (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) ![1, -1]
        (fun i ↦ mul ℝ _ (2 * ![1, -1] i)) (fun _ ↦ ∑ j, proj j) (1 / 2)) ![1, -1] := by
  rw [directOuterApprox_sq_sum_one_neg_one]
  refine ⟨mem_inter_iff _ _ _ |>.2 ⟨mem_Icc.2 ⟨fun j ↦ ?_, fun j ↦ ?_⟩, ?_⟩,
    isMinOn_iff.2 fun x hx ↦ ?_⟩
  · fin_cases j <;> norm_num
  · fin_cases j <;> norm_num
  · norm_num
  · obtain ⟨hlo, hhi⟩ := mem_Icc.1 (mem_inter_iff _ _ _ |>.1 hx).1
    have h0 := hhi 0
    have h1 := hlo 1
    simp only [Pi.one_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h0 h1 ⊢
    linarith

/-- The objective `-x₀ + x₁` attains its minimum `-5/4` on the projected shared set at the anchors
`(1, 1)` and `(-1, -1)` with budget `1/2`, at `(5/8, -5/8)`. -/
theorem mem_and_isMinOn_fst_image_sharedOuterApprox_sq_sum_one_neg_one :
    ![5 / 8, -5 / 8] ∈ Prod.fst '' sharedOuterApprox (Icc (-1) 1)
        univ (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) ![1, -1]
        (fun i ↦ mul ℝ _ (2 * ![1, -1] i)) (fun _ ↦ ∑ j, proj j) (1 / 2) ∧
      IsMinOn (fun x : Fin 2 → ℝ ↦ -x 0 + x 1) (Prod.fst '' sharedOuterApprox (Icc (-1) 1)
        univ (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) ![1, -1]
        (fun i ↦ mul ℝ _ (2 * ![1, -1] i)) (fun _ ↦ ∑ j, proj j) (1 / 2)) ![5 / 8, -5 / 8] := by
  rw [fst_image_sharedOuterApprox_sq_sum_one_neg_one]
  refine ⟨mem_inter_iff _ _ _ |>.2 ⟨mem_Icc.2 ⟨fun j ↦ ?_, fun j ↦ ?_⟩, ?_⟩,
    isMinOn_iff.2 fun x hx ↦ ?_⟩
  · fin_cases j <;> norm_num
  · fin_cases j <;> norm_num
  · norm_num [abs_of_pos, abs_of_neg]
  · obtain ⟨-, hb⟩ := mem_inter_iff _ _ _ |>.1 hx
    simp only [mem_ofPred_eq] at hb
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith [le_abs_self (x 0), neg_abs_le (x 1)]

/-- The objective `-x₀ + x₁` attains its minimum `-1` on the original set `x₀ ^ 2 + x₁ ^ 2 ≤ 1/2`
of the box `[-1, 1]²`, at `(1/2, -1/2)`. -/
theorem mem_and_isMinOn_originalSet_sq_sum_half :
    ![1 / 2, -1 / 2] ∈ originalSet (Icc (-1) 1) (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2)
        (fun y ↦ ∑ j, y j) (1 / 2) ∧
      IsMinOn (fun x : Fin 2 → ℝ ↦ -x 0 + x 1) (originalSet (Icc (-1) 1)
        (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) (1 / 2)) ![1 / 2, -1 / 2] := by
  refine ⟨mem_originalSet.2 ⟨mem_Icc.2 ⟨fun j ↦ ?_, fun j ↦ ?_⟩, ?_⟩,
    isMinOn_iff.2 fun x hx ↦ ?_⟩
  · fin_cases j <;> norm_num
  · fin_cases j <;> norm_num
  · norm_num [Fin.sum_univ_two]
  · have hb := (mem_originalSet.1 hx).2
    rw [Fin.sum_univ_two] at hb
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [sq_nonneg (x 0 + x 1)]

/-- The exact lift retains the minimum `-1` of `-x₀ + x₁`: with the monotone outer sum, the graph
point `((1/2, -1/2), (1/4, 1/4))` minimises the objective on the lifted set. -/
theorem mem_and_isMinOn_liftedSet_sq_sum_half :
    (![1 / 2, -1 / 2], ![1 / 4, 1 / 4]) ∈ liftedSet (Icc (-1) 1) univ
        (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) (1 / 2) ∧
      IsMinOn ((fun x : Fin 2 → ℝ ↦ -x 0 + x 1) ∘ Prod.fst) (liftedSet (Icc (-1) 1) univ
        (fun (x : Fin 2 → ℝ) j ↦ x j ^ 2) (fun y ↦ ∑ j, y j) (1 / 2))
        (![1 / 2, -1 / 2], ![1 / 4, 1 / 4]) := by
  have hg : (fun j ↦ (![1 / 2, -1 / 2] : Fin 2 → ℝ) j ^ 2) = ![1 / 4, 1 / 4] := by
    ext j
    fin_cases j <;> norm_num
  obtain ⟨hmem, hmin⟩ := mem_and_isMinOn_originalSet_sq_sum_half
  refine ⟨?_, (isMinOn_comp_fst_liftedSet_iff (mapsTo_univ _ _)
    (Fintype.sum_mono.monotoneOn univ) _ _).2 hmin⟩
  rw [← hg]
  exact mk_mem_liftedSet_of_mem_originalSet (mapsTo_univ _ _) hmem

end TwoAnchors

/-! ### Examples on the line -/

section Line

/-- The derivative of `x ↦ (x ^ 2)` as a map `ℝ → ℝ¹` at `a` is `t ↦ (2 a t)`. -/
theorem hasFDerivAt_sq_line (a : ℝ) :
    HasFDerivAt (fun x : ℝ ↦ fun _ : Fin 1 ↦ x ^ 2) (toSpanSingleton ℝ fun _ ↦ 2 * a) a :=
  (hasDerivAt_pi.2 fun _ ↦ by simpa using hasDerivAt_pow 2 a).hasFDerivAt

/-- The derivative of the identity `x ↦ (x)` as a map `ℝ → ℝ¹` is `t ↦ (t)`, as a continuous
linear map. -/
example (a : ℝ) : HasFDerivAt (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (toSpanSingleton ℝ 1) a := by
  convert (toSpanSingleton ℝ (1 : Fin 1 → ℝ)).hasFDerivAt using 1
  ext
  simp

/-! #### Rows at different anchors -/

/-- The original set of `x ^ 2 ≤ 1/4` on the line is `[-1/2, 1/2]`. -/
theorem originalSet_sq_line_quarter :
    originalSet univ (fun x : ℝ ↦ fun _ : Fin 1 ↦ x ^ 2) (fun y ↦ y 0) (1 / 4) =
      Icc (-1 / 2) (1 / 2) := by
  ext x
  have hq : (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
  simp only [mem_originalSet, mem_univ, true_and, mem_Icc, hq, sq_le_sq,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_le, neg_div]

/-- For `x ^ 2 ≤ 1/4` on the line, the shared heights at the anchor `0` project onto the whole line:
the height `0` dominates the component row `0` and satisfies the outer row. -/
theorem fst_image_sharedOuterApprox_sq_line_zero :
    Prod.fst '' sharedOuterApprox univ univ (fun x : ℝ ↦ fun _ : Fin 1 ↦ x ^ 2) (fun y ↦ y 0)
      (fun _ : Fin 1 ↦ 0) (fun _ ↦ toSpanSingleton ℝ fun _ ↦ 2 * 0) (fun _ ↦ proj 0) (1 / 4) =
      univ := by
  refine eq_univ_of_forall fun x ↦ ⟨(x, 0), mem_sharedOuterApprox.2 ⟨mem_univ _, mem_univ _,
    fun _ ↦ ⟨fun _ ↦ ?_, ?_⟩⟩, rfl⟩
  · simp [componentRow_def]
  · norm_num [outerRow_def]

/-- For `x ^ 2 ≤ 1/4` on the line, the direct row at the anchor `1` is `C x = 2 x - 1`, and the
budget constraint `C x ≤ 1/4` gives the direct set `x ≤ 5/8`. It does not contain `1`, which the
shared heights at the anchor `0` admit: with different anchors the shared projection need not lie in
the direct set. -/
theorem directOuterApprox_sq_line_one :
    directOuterApprox univ (fun x : ℝ ↦ fun _ : Fin 1 ↦ x ^ 2) (fun y ↦ y 0)
      (fun _ : Fin 1 ↦ 1) (fun _ ↦ toSpanSingleton ℝ fun _ ↦ 2 * 1) (fun _ ↦ proj 0) (1 / 4) =
      Iic (5 / 8) := by
  ext x
  simp only [mem_directOuterApprox, directRow_def, mem_univ, true_and, forall_const, mem_Iic,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply,
    smul_eq_mul]
  constructor <;> intro h <;> linarith

/-! #### The exponential outer function -/

/-- The derivative of `y ↦ exp y₀` at `0` is `v ↦ v₀`. -/
theorem hasFDerivAt_exp_proj_zero :
    HasFDerivAt (fun y : Fin 1 → ℝ ↦ Real.exp (y 0)) (proj (R := ℝ) 0) 0 := by
  simpa using (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ ↦ ℝ) (0 : Fin 1) 0).exp

/-- For `exp x ≤ 2` at the anchor `0`, the outer row is `H y = 1 + y₀`. -/
theorem outerRow_exp_zero (y : Fin 1 → ℝ) :
    outerRow (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (fun y ↦ Real.exp (y 0)) 0 (proj 0) y = 1 + y 0 := by
  simp [outerRow_def]

/-- For `exp x ≤ 2` at the anchor `0`, the direct row is `C x = 1 + x`. -/
theorem directRow_exp_zero (x : ℝ) :
    directRow (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (fun y ↦ Real.exp (y 0)) 0 (toSpanSingleton ℝ 1)
      (proj 0) x = 1 + x := by
  simp [directRow_def]

/-- For `exp x ≤ 2` on a domain `D` at the anchor `0`, the direct set is `D ∩ (-∞, 1]`. In
particular it is `x ≤ 1` on the line and `[0, 1]` on the half-line `x ≥ 0`, the same as the
projected shared sets. -/
theorem directOuterApprox_exp_zero (D : Set ℝ) :
    directOuterApprox D (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (fun y ↦ Real.exp (y 0))
      (fun _ : Fin 1 ↦ 0) (fun _ ↦ toSpanSingleton ℝ 1) (fun _ ↦ proj 0) 2 = D ∩ Iic 1 := by
  ext x
  simp only [mem_directOuterApprox, directRow_exp_zero, forall_const, mem_inter_iff, mem_Iic]
  constructor <;> rintro ⟨hx, h⟩ <;> exact ⟨hx, by linarith⟩

/-- On a domain `D` with heights in `E ⊇ {(x) | x ∈ D}`, the projected shared set for `exp x ≤ 2` at
the anchor `0` is `D ∩ (-∞, 1]`. -/
private theorem fst_image_sharedOuterApprox_exp_zero {D : Set ℝ} {E : Set (Fin 1 → ℝ)}
    (hDE : MapsTo (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) D E) :
    Prod.fst '' sharedOuterApprox D E (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (fun y ↦ Real.exp (y 0))
      (fun _ : Fin 1 ↦ 0) (fun _ ↦ toSpanSingleton ℝ 1) (fun _ ↦ proj 0) 2 = D ∩ Iic 1 := by
  rw [← directOuterApprox_exp_zero D]
  exact fst_image_sharedOuterApprox_eq_directOuterApprox (fun _ _ _ h ↦ h 0)
    (hDE.mono_left directOuterApprox_subset) fun _ _ _ ↦ by ext; simp [componentRow_def]

/-- For `exp x ≤ 2` on the line at the anchor `0`, the projected shared set is `x ≤ 1`. -/
theorem fst_image_sharedOuterApprox_exp_zero_univ :
    Prod.fst '' sharedOuterApprox univ univ (fun x : ℝ ↦ fun _ : Fin 1 ↦ x)
      (fun y ↦ Real.exp (y 0)) (fun _ : Fin 1 ↦ 0) (fun _ ↦ toSpanSingleton ℝ 1)
      (fun _ ↦ proj 0) 2 = Iic 1 := by
  rw [fst_image_sharedOuterApprox_exp_zero (mapsTo_univ _ _), univ_inter]

/-- For `exp x ≤ 2` on the half-line `x ≥ 0` with heights `y ≥ 0` at the anchor `0`, the projected
shared set is `[0, 1]`. -/
theorem fst_image_sharedOuterApprox_exp_zero_Ici :
    Prod.fst '' sharedOuterApprox (Ici 0) (Ici 0) (fun x : ℝ ↦ fun _ : Fin 1 ↦ x)
      (fun y ↦ Real.exp (y 0)) (fun _ : Fin 1 ↦ 0) (fun _ ↦ toSpanSingleton ℝ 1)
      (fun _ ↦ proj 0) 2 = Icc 0 1 := by
  rw [fst_image_sharedOuterApprox_exp_zero (E := Ici 0) fun _ hx ↦ mem_Ici.2 fun _ ↦ mem_Ici.1 hx,
    Ici_inter_Iic]

/-- For `exp x ≤ 2` on the half-line `x ≥ 0` with heights `y ≥ 0` at the anchor `0`, the pair
`(0, (0))` lies in the shared set. -/
theorem zero_mem_sharedOuterApprox_exp_zero_Ici :
    ((0 : ℝ), (0 : Fin 1 → ℝ)) ∈ sharedOuterApprox (Ici 0) (Ici 0)
      (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (fun y ↦ Real.exp (y 0)) (fun _ : Fin 1 ↦ 0)
      (fun _ ↦ toSpanSingleton ℝ 1) (fun _ ↦ proj 0) 2 := by
  refine mem_sharedOuterApprox.2 ⟨mem_Ici.2 le_rfl, mem_Ici.2 le_rfl, fun _ ↦ ⟨?_, ?_⟩⟩
  · exact le_of_eq <| by ext; simp
  · rw [outerRow_exp_zero]
    norm_num

/-- For `exp x ≤ 2` on a domain `D`, the original set is `D ∩ (-∞, log 2]`, which lies in
`D ∩ (-∞, 1]` since `log 2 < 1`. -/
theorem originalSet_exp_two (D : Set ℝ) :
    originalSet D (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (fun y ↦ Real.exp (y 0)) 2 =
      D ∩ Iic (Real.log 2) := by
  ext x
  simp [← Real.le_log_iff_exp_le two_pos]

/-! #### Exact rows for an affine coordinate -/

/-- The derivative of `y ↦ y₀ ^ 2` at `(-1)` is `v ↦ -2 v₀`. -/
theorem hasFDerivAt_sq_proj_neg_one :
    HasFDerivAt (fun y : Fin 1 → ℝ ↦ y 0 ^ 2) ((-2 : ℝ) • proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ)
      (fun _ ↦ -1) := by
  refine ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ ↦ ℝ) (0 : Fin 1) fun _ ↦ -1).pow 2).congr_fderiv
    ?_
  ext v
  norm_num

/-- The outer derivative `v ↦ -2 v₀` of `y ↦ y₀ ^ 2` at `(-1)` is not monotone. -/
theorem not_monotone_neg_two_smul_proj :
    ¬Monotone ((-2 : ℝ) • proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ) := by
  intro hm
  have := hm (zero_le_one : (0 : Fin 1 → ℝ) ≤ 1)
  norm_num at this

/-- The outer derivative `v ↦ -2 v₀` is nonnegative on the nonnegative directions vanishing on the
only coordinate, since the only such direction is zero. -/
theorem neg_two_smul_proj_nonneg_of_proj_zero_eq_zero (v : Fin 1 → ℝ)
    (hv : ∀ j ∈ ({0} : Set (Fin 1)), v j = 0) :
    0 ≤ ((-2 : ℝ) • proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ) v := by
  simp [hv 0 (Set.mem_singleton 0)]

/-- For `x ^ 2 ≤ 1` at the anchor `-1`, the outer row is `H y = -2 y₀ - 1`. -/
theorem outerRow_sq_neg_one (y : Fin 1 → ℝ) :
    outerRow (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (fun y ↦ y 0 ^ 2) (-1) ((-2 : ℝ) • proj 0) y =
      -2 * y 0 - 1 := by
  simp only [outerRow_def, smul_apply, ContinuousLinearMap.proj_apply,
    Pi.sub_apply, smul_eq_mul]
  ring

/-- For `x ^ 2 ≤ 1` on the line at the anchor `-1`, inequality heights project onto the whole line:
the height `max x (-1)` dominates the component row `x`, and the outer row `H y = -2 y - 1` stays
within the budget `1` there. -/
theorem fst_image_sharedOuterApprox_sq_neg_one :
    Prod.fst '' sharedOuterApprox univ univ (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (fun y ↦ y 0 ^ 2)
      (fun _ : Fin 1 ↦ -1) (fun _ ↦ toSpanSingleton ℝ 1) (fun _ ↦ (-2 : ℝ) • proj 0) 1 = univ := by
  refine eq_univ_of_forall fun x ↦ ⟨(x, fun _ ↦ max x (-1)), mem_sharedOuterApprox.2
    ⟨mem_univ _, mem_univ _, fun _ ↦ ⟨?_, ?_⟩⟩, rfl⟩
  · exact fun _ ↦ by simp [componentRow_def]
  · rw [outerRow_sq_neg_one]
    linarith [le_max_right x (-1)]

/-- For `x ^ 2 ≤ 1` on the line at the anchor `-1`, the direct row is `C x = -2 x - 1`, and the
budget constraint `C x ≤ 1` gives the direct set `[-1, ∞)`. Since the inequality heights project
onto the whole line, the projected shared set is not contained in the direct set without exact
rows. -/
theorem directOuterApprox_sq_neg_one :
    directOuterApprox univ (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (fun y ↦ y 0 ^ 2)
      (fun _ : Fin 1 ↦ -1) (fun _ ↦ toSpanSingleton ℝ 1) (fun _ ↦ (-2 : ℝ) • proj 0) 1 =
      Ici (-1) := by
  ext x
  simp only [mem_directOuterApprox, ← outerRow_componentRow, outerRow_sq_neg_one, componentRow_def,
    Pi.add_apply, ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, mul_one, mem_univ, true_and, forall_const, mem_Ici]
  constructor <;> intro h <;> linarith

/-- For `x ^ 2 ≤ 1` on the line at the anchor `-1`, the exact row `y₀ = x` on the only coordinate
gives the projected shared set `[-1, ∞)`. -/
theorem fst_image_sharedOuterApproxOn_sq_neg_one :
    Prod.fst '' sharedOuterApproxOn {0} univ univ (fun x : ℝ ↦ fun _ : Fin 1 ↦ x)
      (fun y ↦ y 0 ^ 2) (fun _ : Fin 1 ↦ -1) (fun _ ↦ toSpanSingleton ℝ 1)
      (fun _ ↦ (-2 : ℝ) • proj 0) 1 = Ici (-1) := by
  rw [← directOuterApprox_sq_neg_one]
  exact fst_image_sharedOuterApproxOn_eq_directOuterApprox (r := fun x _ ↦ x)
    (fun _ v _ hv ↦ neg_two_smul_proj_nonneg_of_proj_zero_eq_zero v hv) (mapsTo_univ _ _)
    fun _ _ _ ↦ by ext; simp [componentRow_def]

/-- The original set of `x ^ 2 ≤ 1` on the line is `[-1, 1]`. -/
theorem originalSet_sq_one :
    originalSet univ (fun x : ℝ ↦ fun _ : Fin 1 ↦ x) (fun y ↦ y 0 ^ 2) 1 = Icc (-1) 1 := by
  ext x
  simp [sq_le_one_iff_abs_le_one, abs_le]

/-! #### Exact rows next to a convex coordinate -/

/-- The derivative of `x ↦ (x, x ^ 2)` at `-1` is `t ↦ (t, -2 t)`. -/
theorem hasFDerivAt_id_sq_neg_one :
    HasFDerivAt (fun x : ℝ ↦ ![x, x ^ 2]) (toSpanSingleton ℝ ![1, -2]) (-1) := by
  refine (hasDerivAt_pi.2 fun j ↦ ?_).hasFDerivAt
  fin_cases j
  · simpa using hasDerivAt_id' (-1 : ℝ)
  · simpa using hasDerivAt_pow 2 (-1 : ℝ)

/-- The derivative of `(u, v) ↦ u ^ 2 + v` at `(-1, 1)` is `w ↦ -2 w₀ + w₁`. -/
theorem hasFDerivAt_sq_add_neg_one_one :
    HasFDerivAt (fun y : Fin 2 → ℝ ↦ y 0 ^ 2 + y 1)
      ((-2 : ℝ) • proj 0 + proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) ![-1, 1] := by
  refine (((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ ↦ ℝ) (0 : Fin 2) ![-1, 1]).pow 2).add
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ ↦ ℝ) (1 : Fin 2) ![-1, 1])).congr_fderiv ?_
  ext v
  norm_num

/-- The outer derivative `w ↦ -2 w₀ + w₁` is nonnegative on the nonnegative directions vanishing on
the first coordinate, although it is not monotone. -/
theorem neg_two_smul_proj_add_proj_nonneg_of_nonneg_of_proj_zero_eq_zero (v : Fin 2 → ℝ)
    (hv : 0 ≤ v) (hv0 : ∀ j ∈ ({0} : Set (Fin 2)), v j = 0) :
    0 ≤ ((-2 : ℝ) • proj 0 + proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) v := by
  simpa [hv0 0 (Set.mem_singleton 0)] using hv 1

/-- For `x ^ 2 + x ^ 2 ≤ 2` written as `h (x, x ^ 2)` with `h (u, v) = u ^ 2 + v`, the component row
at the anchor `-1` is `G x = (x, -2 x - 1)`. -/
theorem componentRow_id_sq_neg_one (x : ℝ) :
    componentRow (fun x : ℝ ↦ ![x, x ^ 2]) (-1) (toSpanSingleton ℝ ![1, -2]) x =
      ![x, -2 * x - 1] := by
  ext j
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, componentRow_def, Pi.add_apply,
    ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> ring

/-- For `h (u, v) = u ^ 2 + v` at `(-1, 1)`, the outer row is `H y = -2 y₀ + y₁ - 1`. -/
theorem outerRow_sq_add_neg_one (y : Fin 2 → ℝ) :
    outerRow (fun x : ℝ ↦ ![x, x ^ 2]) (fun y ↦ y 0 ^ 2 + y 1) (-1) ((-2 : ℝ) • proj 0 + proj 1)
      y = -2 * y 0 + y 1 - 1 := by
  simp only [outerRow_def, add_apply, smul_apply, ContinuousLinearMap.proj_apply, Pi.sub_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- For `h (x, x ^ 2) ≤ 2` at the anchor `-1`, the direct row is `C x = -4 x - 2`. -/
theorem directRow_id_sq_neg_one (x : ℝ) :
    directRow (fun x : ℝ ↦ ![x, x ^ 2]) (fun y ↦ y 0 ^ 2 + y 1) (-1) (toSpanSingleton ℝ ![1, -2])
      ((-2 : ℝ) • proj 0 + proj 1) x = -4 * x - 2 := by
  rw [← outerRow_componentRow, outerRow_sq_add_neg_one, componentRow_id_sq_neg_one]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- For `h (x, x ^ 2) ≤ 2` on the line at the anchor `-1`, the direct set is `[-1, ∞)`. -/
theorem directOuterApprox_id_sq_neg_one :
    directOuterApprox univ (fun x : ℝ ↦ ![x, x ^ 2]) (fun y ↦ y 0 ^ 2 + y 1)
      (fun _ : Fin 1 ↦ -1) (fun _ ↦ toSpanSingleton ℝ ![1, -2])
      (fun _ ↦ (-2 : ℝ) • proj 0 + proj 1) 2 = Ici (-1) := by
  ext x
  simp only [mem_directOuterApprox, directRow_id_sq_neg_one, mem_univ, true_and, forall_const,
    mem_Ici]
  constructor <;> intro h <;> linarith

/-- For `h (x, x ^ 2) ≤ 2` on the line at the anchor `-1`, the exact row `y₀ = x` on the first
coordinate gives the projected shared set `[-1, ∞)`, the same as the direct set. -/
theorem fst_image_sharedOuterApproxOn_id_sq_neg_one :
    Prod.fst '' sharedOuterApproxOn {0} univ univ (fun x : ℝ ↦ ![x, x ^ 2])
      (fun y ↦ y 0 ^ 2 + y 1) (fun _ : Fin 1 ↦ -1) (fun _ ↦ toSpanSingleton ℝ ![1, -2])
      (fun _ ↦ (-2 : ℝ) • proj 0 + proj 1) 2 = Ici (-1) := by
  rw [← directOuterApprox_id_sq_neg_one]
  exact fst_image_sharedOuterApproxOn_eq_directOuterApprox
    (fun _ v hv hv0 ↦ neg_two_smul_proj_add_proj_nonneg_of_nonneg_of_proj_zero_eq_zero v hv hv0)
    (mapsTo_univ _ _) fun x _ _ ↦ componentRow_id_sq_neg_one x

/-- The original set of `x ^ 2 + x ^ 2 ≤ 2` on the line is `[-1, 1]`. -/
theorem originalSet_id_sq_two :
    originalSet univ (fun x : ℝ ↦ ![x, x ^ 2]) (fun y ↦ y 0 ^ 2 + y 1) 2 = Icc (-1) 1 := by
  ext x
  have : x ^ 2 + x ^ 2 ≤ 2 ↔ x ^ 2 ≤ 1 := by constructor <;> intro h <;> linarith
  simp [this, sq_le_one_iff_abs_le_one, abs_le]

end Line

end TauCeti.CompositionLift
