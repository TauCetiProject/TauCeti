/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.Binary
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Odd unimodular forms over `ℤ₂`

An odd unimodular symmetric bilinear form over `ℤ₂` has an orthogonal basis whose self-pairings
`u₁, …, uₙ` are units
(`LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self`).
This file proves that such a diagonal form is determined up to isometry by its rank, the square
class of its determinant `u₁ ⋯ uₙ`, and its **oddity** `u₁ + ⋯ + uₙ mod 8`: two diagonal forms with
unit coefficients in the same number of variables are isometric as soon as the products of their
coefficients differ by a square and the sums of their coefficients agree modulo `8`. Isometric
forms always have determinants in the same square class
(`TauCeti.isSquare_prod_mul_prod_of_equivalent`), so this is the sufficiency half of the
classification of odd unimodular `ℤ₂`-lattices by rank, determinant and oddity.

The square class of a unit of `ℤ₂` is its residue modulo `8`, so everything is read on residues
modulo `8`. The proof is an induction on the rank which moves a prescribed coefficient to the front
by binary steps: `⟨x, y⟩ ≅ ⟨z, x y z⟩` whenever `z ≡ y (mod 4)`, because then
`x (2m)² + y t² = z` is solvable with `z - y = 4m`. Binary steps preserve the number of
coefficients congruent to `3` modulo `4`, which is not an isometry invariant: `⟨1, 1, 1, 1⟩` and
`⟨3, 3, 3, 3⟩` are isometric. One quaternary isometry is therefore needed, the explicit
change of variables `⟨1, 1, 1, c⟩ ≅ ⟨3, 2 + c, c (2c + 1), 3 (2c + 1)(c + 2)⟩` of determinant
`3 (2 + c)(2c + 1)`. In rank at least five the same effect is obtained from the induction
hypothesis by tripling four coefficients, which changes neither invariant.

## Main results

* `TauCeti.equivalent_weightedSumSquares_of_isSquare_prod_mul_prod_of_eight_dvd_sum_sub_sum`:
  diagonal quadratic forms over `ℤ₂` with unit coefficients are isometric when the products of
  their coefficients differ by a square and the sums of their coefficients agree modulo `8`.
* `LinearMap.BilinForm.iIsOrtho.equivalent_of_isSquare_prod_mul_prod_of_eight_dvd_sum_sub_sum`: the
  same statement for bilinear forms over `ℤ₂` with orthogonal bases of unit self-pairings.
* `TauCeti.equivalent_weightedSumSquares_of_toZModPow_eq`: diagonal forms over `ℤ₂` whose
  coefficients have equal odd residues modulo `8` are isometric.
* `TauCeti.equivalent_binary_of_four_dvd_sub`: the binary step `⟨x, y⟩ ≅ ⟨z, x y z⟩` over `ℤ₂`
  for units `x, y` and `z ≡ y (mod 4)`.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93, in particular 93:16.
-/

public section

open QuadraticMap PadicInt

namespace TauCeti

/-! ### Residues modulo `8` -/

/-- Diagonal forms over `ℤ₂` whose coefficients have equal odd residues modulo `8` are isometric:
corresponding coefficients differ by the square of a unit. -/
theorem equivalent_weightedSumSquares_of_toZModPow_eq {ι : Type*} [Fintype ι]
    {w v : ι → ℤ_[2]} (hv : ∀ i, toZModPow 3 (v i) * toZModPow 3 (v i) = 1)
    (h : ∀ i, toZModPow 3 (w i) = toZModPow 3 (v i)) :
    (weightedSumSquares ℤ_[2] w).Equivalent (weightedSumSquares ℤ_[2] v) := by
  choose t ht using fun i ↦ exists_eq_mul_sq_of_toZModPow_eq (hv i) (h i)
  exact ⟨QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares t fun i ↦ (ht i).symm⟩

/-- Two odd residues modulo `8` are congruent modulo `4` up to sign. -/
private theorem two_mul_add_eq_zero_of_ne {x y : ZMod (2 ^ 3)} (hx : x * x = 1) (hy : y * y = 1)
    (h : 2 * (x - y) ≠ 0) : 2 * (x + y) = 0 := by
  have key : ∀ x y : ZMod (2 ^ 3), x * x = 1 → y * y = 1 → 2 * (x - y) ≠ 0 → 2 * (x + y) = 0 := by
    decide
  exact key x y hx hy h

/-- The coefficient sum is unchanged by the binary step `⟨x, y⟩ ↦ ⟨z, x y z⟩` with
`z ≡ y (mod 4)`. -/
private theorem add_mul_mul_eq_of_two_mul_sub_eq_zero {x y z : ZMod (2 ^ 3)} (hx : x * x = 1)
    (hy : y * y = 1) (hz : z * z = 1) (h : 2 * (z - y) = 0) : z + x * y * z = x + y := by
  have key : ∀ x y z : ZMod (2 ^ 3), x * x = 1 → y * y = 1 → z * z = 1 → 2 * (z - y) = 0 →
      z + x * y * z = x + y := by
    decide
  exact key x y z hx hy hz h

/-! ### Elementary isometries -/

/-- **The binary step.** If `x` and `y` are units of `ℤ₂` and `z ≡ y (mod 4)`, then
`⟨x, y⟩ ≅ ⟨z, x y z⟩`. Writing `z - y = 4m`, the element `z - 4 x m²` agrees with `y` modulo `8`,
so it is `y t²` for a unit `t`, and `x (2m)² + y t² = z`. -/
theorem equivalent_binary_of_four_dvd_sub {x y z : ℤ_[2]} (hx : IsUnit x) (hy : IsUnit y)
    (h : (4 : ℤ_[2]) ∣ z - y) :
    (weightedSumSquares ℤ_[2] ![x, y]).Equivalent (weightedSumSquares ℤ_[2] ![z, x * y * z]) := by
  rw [isUnit_iff_toZModPow_three_mul_self] at hx hy
  obtain ⟨m, hm⟩ := h
  have key : ∀ a b : ZMod (2 ^ 3), b * b = 1 → 4 * a - 4 * b * a ^ 2 = 0 := by decide
  have hr : toZModPow 3 (z - 4 * x * m ^ 2) = toZModPow 3 y := by
    rw [show z - 4 * x * m ^ 2 = y + 4 * m - 4 * x * m ^ 2 by linear_combination hm]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
    linear_combination key (toZModPow 3 m) (toZModPow 3 x) hx
  -- `z - 4 x m²` is `y` times the square of a unit.
  obtain ⟨t, ht⟩ := exists_eq_mul_sq_of_toZModPow_eq hy hr
  -- `z ≡ y (mod 4)` is a unit.
  have hzu : IsUnit z := by
    have key' : ∀ a b : ZMod (2 ^ 3), b * b = 1 → (b + 4 * a) * (b + 4 * a) = 1 := by decide
    rw [isUnit_iff_toZModPow_three_mul_self, show z = y + 4 * m by linear_combination hm]
    simpa only [map_add, map_mul, map_ofNat] using key' (toZModPow 3 m) _ hy
  have e : (weightedSumSquares ℤ_[2] ![x, y]).Equivalent
      (weightedSumSquares ℤ_[2] ![(hzu.unit : ℤ_[2]), x * y * hzu.unit]) :=
    ⟨(isometryEquivBinaryNormalForm x y (2 * m) t hzu.unit
      (by rw [IsUnit.unit_spec]; linear_combination -ht)).symm⟩
  rwa [IsUnit.unit_spec] at e

/-- **The quaternary step.** The isometry `⟨a, a, a, a c⟩ ≅ ⟨3a, (2 + c)a, c (2c + 1)a,
3 (2c + 1)(c + 2)a⟩`, given by the matrix with columns `(1, 1, 1, 0)`, `(1, -1, 0, 1)`,
`(c, 0, -c, -1)` and `(1 - c, 2c + 1, -(c + 2), 3)`, whose determinant is `3 (2 + c)(2c + 1)`. -/
private theorem equivalent_weightedSumSquares_four (a c : ℤ_[2])
    (hc : IsUnit (3 * (2 + c) * (2 * c + 1))) :
    (weightedSumSquares ℤ_[2] ![a, a, a, a * c]).Equivalent
      (weightedSumSquares ℤ_[2] ![3 * a, (2 + c) * a, c * (2 * c + 1) * a,
        3 * (2 * c + 1) * (c + 2) * a]) := by
  let P : Matrix (Fin 4) (Fin 4) ℤ_[2] :=
    !![1, 1, c, 1 - c; 1, -1, 0, 2 * c + 1; 1, 0, -c, -(c + 2); 0, 1, -1, 3]
  have hdet : P.det = 3 * (2 + c) * (2 * c + 1) := by
    -- The minors produced by the cofactor expansion index rows through `Fin.succAbove`.
    have h1 : Fin.succAbove (1 : Fin 4) 2 = 3 := by decide
    have h2 : Fin.succAbove (2 : Fin 4) 2 = 3 := by decide
    have h3 : Fin.succAbove (3 : Fin 4) 2 = 2 := by decide
    simp [P, Matrix.det_succ_row_zero, Fin.sum_univ_succ, h1, h2, h3]
    ring
  let f : (Fin 4 → ℤ_[2]) ≃ₗ[ℤ_[2]] (Fin 4 → ℤ_[2]) :=
    LinearEquiv.ofIsUnitDet (f := Matrix.toLin' P) (v := Pi.basisFun ℤ_[2] (Fin 4))
      (v' := Pi.basisFun ℤ_[2] (Fin 4))
      (by rwa [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', hdet])
  refine ⟨({ toLinearEquiv := f
             map_app' := fun y ↦ ?_ } : QuadraticMap.IsometryEquiv _ _).symm⟩
  simp only [f, LinearEquiv.coe_ofIsUnitDet, weightedSumSquares_apply, Fin.sum_univ_four,
    smul_eq_mul]
  simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-! ### The induction on the rank -/

/-- The statement proved by induction on the rank `n`: diagonal forms of rank `n` with odd
coefficients whose coefficient products and coefficient sums agree modulo `8` are isometric. -/
private def Classified (n : ℕ) : Prop :=
  ∀ w v : Fin n → ℤ_[2], (∀ i, toZModPow 3 (w i) * toZModPow 3 (w i) = 1) →
    (∀ i, toZModPow 3 (v i) * toZModPow 3 (v i) = 1) →
    toZModPow 3 (∏ i, w i) = toZModPow 3 (∏ i, v i) →
    toZModPow 3 (∑ i, w i) = toZModPow 3 (∑ i, v i) →
    (weightedSumSquares ℤ_[2] w).Equivalent (weightedSumSquares ℤ_[2] v)

/-- **The step of the induction, in coordinates.** If `c ≡ y (mod 4)`, the binary step replaces
`⟨x, y, r⟩` by `⟨c, x y c, r⟩`, and the induction hypothesis identifies `⟨x y c, r⟩` with `t`. -/
private theorem equivalent_cons_cons_of_two_mul_sub_eq_zero {m : ℕ} (ih : Classified (m + 1))
    {x y c : ℤ_[2]} {r : Fin m → ℤ_[2]} {t : Fin (m + 1) → ℤ_[2]}
    (hx : toZModPow 3 x * toZModPow 3 x = 1) (hy : toZModPow 3 y * toZModPow 3 y = 1)
    (hc : toZModPow 3 c * toZModPow 3 c = 1) (hr : ∀ i, toZModPow 3 (r i) * toZModPow 3 (r i) = 1)
    (ht : ∀ i, toZModPow 3 (t i) * toZModPow 3 (t i) = 1)
    (hP : toZModPow 3 (x * (y * ∏ i, r i)) = toZModPow 3 (c * ∏ i, t i))
    (hS : toZModPow 3 (x + (y + ∑ i, r i)) = toZModPow 3 (c + ∑ i, t i))
    (hcy : 2 * (toZModPow 3 c - toZModPow 3 y) = 0) :
    (weightedSumSquares ℤ_[2] (Fin.cons x (Fin.cons y r) : Fin (m + 2) → ℤ_[2])).Equivalent
      (weightedSumSquares ℤ_[2] (Fin.cons c t : Fin (m + 2) → ℤ_[2])) := by
  have hpair := equivalent_binary_of_four_dvd_sub (isUnit_iff_toZModPow_three_mul_self.mpr hx)
    (isUnit_iff_toZModPow_three_mul_self.mpr hy)
    (four_dvd_sub_iff_two_mul_toZModPow_sub_eq_zero.mpr hcy)
  refine (equivalent_weightedSumSquares_of_pair (w := Fin.cons x (Fin.cons y r))
    (w' := Fin.cons c (Fin.cons (x * y * c) r)) (i := 0) (j := 1) zero_ne_one
    (by simpa using hpair) ?_).trans (equivalent_weightedSumSquares_cons c (ih _ _ ?_ ht ?_ ?_))
  · intro k hk0 hk1
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
    · exact absurd rfl hk0
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
    · exact absurd rfl hk1
    simp
  · refine Fin.cases ?_ fun i ↦ ?_
    · simp only [Fin.cons_zero, map_mul]
      linear_combination (toZModPow 3 y * toZModPow 3 y * toZModPow 3 c * toZModPow 3 c) * hx +
        (toZModPow 3 c * toZModPow 3 c) * hy + hc
    · simpa using hr i
  · simp only [Fin.prod_cons, map_mul, map_prod] at hP ⊢
    linear_combination toZModPow 3 c * hP + (∏ i, toZModPow 3 (t i)) * hc
  · simp only [Fin.sum_cons, map_mul, map_add, map_sum] at hS ⊢
    linear_combination hS + add_mul_mul_eq_of_two_mul_sub_eq_zero hx hy hc hcy

/-- **The step of the induction.** Assuming the classification in rank `n`, two diagonal forms of
rank `n + 1` with the same invariants are isometric as soon as the first coefficient of the second
is congruent modulo `4` to some coefficient of the first. -/
private theorem equivalent_of_two_mul_sub_eq_zero {n : ℕ} (ih : Classified n)
    {w v : Fin (n + 1) → ℤ_[2]} (hw : ∀ i, toZModPow 3 (w i) * toZModPow 3 (w i) = 1)
    (hv : ∀ i, toZModPow 3 (v i) * toZModPow 3 (v i) = 1)
    (hP : toZModPow 3 (∏ i, w i) = toZModPow 3 (∏ i, v i))
    (hS : toZModPow 3 (∑ i, w i) = toZModPow 3 (∑ i, v i)) (j : Fin (n + 1))
    (hj : 2 * (toZModPow 3 (v 0) - toZModPow 3 (w j)) = 0) :
    (weightedSumSquares ℤ_[2] w).Equivalent (weightedSumSquares ℤ_[2] v) := by
  rcases n with _ | m
  · -- In rank one the two coefficients agree modulo `8`.
    refine equivalent_weightedSumSquares_of_toZModPow_eq hv fun i ↦ ?_
    rw [Fin.fin_one_eq_zero i]
    simpa using hP
  -- Move `w j` to the second position, then apply the step in coordinates.
  have e₀ := equivalent_weightedSumSquares_comp w (Equiv.swap 1 j)
  set u := w ∘ Equiv.swap 1 j with hu
  have hu' : u = Fin.cons (u 0) (Fin.cons (u 1) fun i ↦ u i.succ.succ) := by
    ext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i) i <;> simp
  have hv' : v = Fin.cons (v 0) fun i ↦ v i.succ := (Fin.cons_self_tail v).symm
  have hPu : toZModPow 3 (u 0 * (u 1 * ∏ i : Fin m, u i.succ.succ)) =
      toZModPow 3 (v 0 * ∏ i : Fin (m + 1), v i.succ) := by
    rw [← Fin.prod_cons, ← Fin.prod_cons, ← hu', ← Fin.prod_cons, ← hv', ← hP]
    exact congrArg _ (Equiv.prod_comp (Equiv.swap 1 j) w)
  have hSu : toZModPow 3 (u 0 + (u 1 + ∑ i : Fin m, u i.succ.succ)) =
      toZModPow 3 (v 0 + ∑ i : Fin (m + 1), v i.succ) := by
    rw [← Fin.sum_cons, ← Fin.sum_cons, ← hu', ← Fin.sum_cons, ← hv', ← hS]
    exact congrArg _ (Equiv.sum_comp (Equiv.swap 1 j) w)
  refine e₀.trans ?_
  rw [hu', hv']
  exact equivalent_cons_cons_of_two_mul_sub_eq_zero ih (hw _) (hw _) (hv 0) (fun i ↦ hw _)
    (fun i ↦ hv _) hPu hSu (by simpa [hu] using hj)

/-- The residue computations behind the quaternary step: if `a, b, c, d` are odd residues modulo
`8`, all congruent modulo `4`, and `k = a (b c a d a)`, then the four coefficients
`3a, (2 + k)a, k (2k + 1)a, 3 (2k + 1)(k + 2)a` and the determinant `3 (2 + k)(2k + 1)` of the
quaternary step are odd, and the coefficient product and sum are those of `⟨a, b, c, d⟩`. -/
private theorem residues_of_rank_four : ∀ a b c d k : ZMod (2 ^ 3), a * a = 1 → b * b = 1 →
    2 * (b - a) = 0 → c * c = 1 → 2 * (c - a) = 0 → d * d = 1 → 2 * (d - a) = 0 →
    k = a * (b * c * a * d * a) →
    (3 * a) * (3 * a) = 1 ∧ ((2 + k) * a) * ((2 + k) * a) = 1 ∧
      (k * (2 * k + 1) * a) * (k * (2 * k + 1) * a) = 1 ∧
      (3 * (2 * k + 1) * (k + 2) * a) * (3 * (2 * k + 1) * (k + 2) * a) = 1 ∧
      (3 * (2 + k) * (2 * k + 1)) * (3 * (2 + k) * (2 * k + 1)) = 1 ∧
      3 * a * ((2 + k) * a) * (k * (2 * k + 1) * a) * (3 * (2 * k + 1) * (k + 2) * a) =
        a * b * c * d ∧
      3 * a + (2 + k) * a + k * (2 * k + 1) * a + 3 * (2 * k + 1) * (k + 2) * a =
        a + b + c + d := by
  decide

/-- **Rank four, all coefficients in one class modulo `4`.** If every coefficient of `w` is
congruent to `w 0` modulo `4` and `v 0` is congruent to `-w 0`, two binary steps bring `w` to the
shape `⟨a, a, a, e⟩`, and the quaternary step produces the first coefficient `3a ≡ v 0`. -/
private theorem equivalent_of_rank_four (ih : Classified 3) {w v : Fin 4 → ℤ_[2]}
    (hw : ∀ i, toZModPow 3 (w i) * toZModPow 3 (w i) = 1)
    (hv : ∀ i, toZModPow 3 (v i) * toZModPow 3 (v i) = 1)
    (hP : toZModPow 3 (∏ i, w i) = toZModPow 3 (∏ i, v i))
    (hS : toZModPow 3 (∑ i, w i) = toZModPow 3 (∑ i, v i))
    (hw' : ∀ j, 2 * (toZModPow 3 (w j) - toZModPow 3 (w 0)) = 0)
    (hv0 : 2 * (toZModPow 3 (v 0) + toZModPow 3 (w 0)) = 0) :
    (weightedSumSquares ℤ_[2] w).Equivalent (weightedSumSquares ℤ_[2] v) := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, w = ![a, b, c, d] :=
    ⟨w 0, w 1, w 2, w 3, by ext i; fin_cases i <;> rfl⟩
  have ha : toZModPow 3 a * toZModPow 3 a = 1 := hw 0
  have hb : toZModPow 3 b * toZModPow 3 b = 1 := hw 1
  have hc : toZModPow 3 c * toZModPow 3 c = 1 := hw 2
  have hd : toZModPow 3 d * toZModPow 3 d = 1 := hw 3
  have hmul {x y : ℤ_[2]} (hx : toZModPow 3 x * toZModPow 3 x = 1)
      (hy : toZModPow 3 y * toZModPow 3 y = 1) : toZModPow 3 (x * y) * toZModPow 3 (x * y) = 1 := by
    rw [map_mul, mul_mul_mul_comm, hx, hy, one_mul]
  have hca : 2 * (toZModPow 3 c - toZModPow 3 a) = 0 := hw' 2
  have hda : 2 * (toZModPow 3 d - toZModPow 3 a) = 0 := hw' 3
  have hbca := hmul (hmul hb hc) ha
  have he := hmul (hmul hbca hd) ha
  have hk := hmul ha he
  obtain ⟨hu₀, hu₁, hu₂, hu₃, hdet, hprod, hsum⟩ :=
    residues_of_rank_four _ _ _ _ _ ha hb (hw' 1) hc hca hd hda rfl
  -- Two binary steps give `⟨a, a, a, e⟩` with `e = (b c a) d a`.
  have e₁ : (weightedSumSquares ℤ_[2] ![a, b, c, d]).Equivalent
      (weightedSumSquares ℤ_[2] ![a, a, b * c * a, d]) := by
    refine equivalent_weightedSumSquares_cons a (equivalent_weightedSumSquares_of_pair
      (w := ![b, c, d]) (w' := ![a, b * c * a, d]) (i := 0) (j := 1) zero_ne_one ?_ ?_)
    · simpa using equivalent_binary_of_four_dvd_sub (isUnit_iff_toZModPow_three_mul_self.mpr hb)
        (isUnit_iff_toZModPow_three_mul_self.mpr hc)
        (four_dvd_sub_iff_two_mul_toZModPow_sub_eq_zero.mpr (by linear_combination -hca))
    · intro k hk0 hk1
      fin_cases k <;> simp_all
  have e₂ : (weightedSumSquares ℤ_[2] ![a, a, b * c * a, d]).Equivalent
      (weightedSumSquares ℤ_[2] ![a, a, a, b * c * a * d * a]) :=
    equivalent_weightedSumSquares_cons a (equivalent_weightedSumSquares_cons a
      (equivalent_binary_of_four_dvd_sub (isUnit_iff_toZModPow_three_mul_self.mpr hbca)
        (isUnit_iff_toZModPow_three_mul_self.mpr hd)
        (four_dvd_sub_iff_two_mul_toZModPow_sub_eq_zero.mpr (by linear_combination -hda))))
  -- Rescale `e` to `a k` with `k = a e`, which has the same residue, and take the quaternary step.
  have e₃ : (weightedSumSquares ℤ_[2] ![a, a, a, b * c * a * d * a]).Equivalent
      (weightedSumSquares ℤ_[2] ![a, a, a, a * (a * (b * c * a * d * a))]) := by
    refine equivalent_weightedSumSquares_of_toZModPow_eq (fun i ↦ ?_) fun i ↦ ?_
    · fin_cases i <;> simp only [Matrix.cons_val, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one]
      exacts [ha, ha, ha, hmul ha hk]
    · fin_cases i <;> simp only [Matrix.cons_val, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one]
      simp only [map_mul]
      linear_combination
        (-(toZModPow 3 b * toZModPow 3 c * toZModPow 3 a * toZModPow 3 d * toZModPow 3 a)) * ha
  have e₄ := equivalent_weightedSumSquares_four a (a * (b * c * a * d * a))
    (isUnit_iff_toZModPow_three_mul_self.mpr (by
      simp only [map_mul, map_add, map_one, map_ofNat]
      exact hdet))
  refine e₁.trans (e₂.trans (e₃.trans (e₄.trans ?_)))
  -- The new first coefficient `3a` is congruent to `v 0` modulo `4`.
  refine equivalent_of_two_mul_sub_eq_zero ih (fun i ↦ ?_) hv ?_ ?_ 0 ?_
  · fin_cases i <;> simp only [Matrix.cons_val, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one,
      map_mul, map_add, map_one, map_ofNat]
    · exact hu₀
    · exact hu₁
    · exact hu₂
    · exact hu₃
  · rw [← hP]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      map_mul, map_add, map_one, map_ofNat]
    linear_combination hprod
  · rw [← hS]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      map_mul, map_add, map_one, map_ofNat]
    linear_combination hsum
  · have h8 : (8 : ZMod (2 ^ 3)) = 0 := by decide
    simp only [Matrix.cons_val_zero, map_mul, map_ofNat] at hv0 ⊢
    linear_combination hv0 - toZModPow 3 a * h8

/-- **Rank at least five, all coefficients in one class modulo `4`.** Tripling four coefficients
of the tail of `w` changes neither the product nor the sum of its coefficients modulo `8`, so the
induction hypothesis identifies the two tails; the new second coefficient `3 (w 1)` is congruent to
`v 0` modulo `4`. -/
private theorem equivalent_of_five_le {k : ℕ} (ih : Classified (k + 4))
    {w v : Fin (k + 5) → ℤ_[2]} (hw : ∀ i, toZModPow 3 (w i) * toZModPow 3 (w i) = 1)
    (hv : ∀ i, toZModPow 3 (v i) * toZModPow 3 (v i) = 1)
    (hP : toZModPow 3 (∏ i, w i) = toZModPow 3 (∏ i, v i))
    (hS : toZModPow 3 (∑ i, w i) = toZModPow 3 (∑ i, v i))
    (hw' : ∀ j, 2 * (toZModPow 3 (w j) - toZModPow 3 (w 0)) = 0)
    (hv0 : 2 * (toZModPow 3 (v 0) + toZModPow 3 (w 0)) = 0) :
    (weightedSumSquares ℤ_[2] w).Equivalent (weightedSumSquares ℤ_[2] v) := by
  obtain ⟨a, b, c, d, e, r, rfl⟩ : ∃ a b c d e r,
      w = Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d (Fin.cons e r)))) :=
    ⟨w 0, Fin.tail w 0, Fin.tail (Fin.tail w) 0, Fin.tail (Fin.tail (Fin.tail w)) 0,
      Fin.tail (Fin.tail (Fin.tail (Fin.tail w))) 0,
      Fin.tail (Fin.tail (Fin.tail (Fin.tail (Fin.tail w)))), by simp only [Fin.cons_self_tail]⟩
  have h8 : (8 : ZMod (2 ^ 3)) = 0 := by decide
  have h80 : (80 : ZMod (2 ^ 3)) = 0 := by decide
  have hodd3 (x : ℤ_[2]) (hx : toZModPow 3 x * toZModPow 3 x = 1) :
      toZModPow 3 (3 * x) * toZModPow 3 (3 * x) = 1 := by
    simp only [map_mul, map_ofNat]
    linear_combination 9 * hx + h8
  have hb := hw' (Fin.succ 0)
  have hc := hw' (Fin.succ (Fin.succ 0))
  have hd := hw' (Fin.succ (Fin.succ (Fin.succ 0)))
  have he := hw' (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
  have hbo := hw (Fin.succ 0)
  have hco := hw (Fin.succ (Fin.succ 0))
  have hdo := hw (Fin.succ (Fin.succ (Fin.succ 0)))
  have heo := hw (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
  have hr : ∀ i, toZModPow 3 (r i) * toZModPow 3 (r i) = 1 := fun i ↦ by
    simpa only [Fin.cons_succ] using hw i.succ.succ.succ.succ.succ
  simp only [Fin.cons_succ, Fin.cons_zero] at hb hc hd he hv0 hbo hco hdo heo
  set t : Fin (k + 4) → ℤ_[2] := Fin.cons b (Fin.cons c (Fin.cons d (Fin.cons e r))) with ht_def
  set t' : Fin (k + 4) → ℤ_[2] :=
    Fin.cons (3 * b) (Fin.cons (3 * c) (Fin.cons (3 * d) (Fin.cons (3 * e) r))) with ht'_def
  have ht : ∀ i, toZModPow 3 (t i) * toZModPow 3 (t i) = 1 := fun i ↦ by
    simpa using hw i.succ
  have ht' : ∀ i, toZModPow 3 (t' i) * toZModPow 3 (t' i) = 1 := by
    simp only [ht'_def, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    exact ⟨hodd3 _ hbo, hodd3 _ hco, hodd3 _ hdo, hodd3 _ heo, hr⟩
  have hPt : toZModPow 3 (∏ i, t i) = toZModPow 3 (∏ i, t' i) := by
    simp only [ht_def, ht'_def, Fin.prod_cons, map_mul, map_ofNat]
    linear_combination (-(toZModPow 3 b * toZModPow 3 c * toZModPow 3 d * toZModPow 3 e *
      toZModPow 3 (∏ i, r i))) * h80
  have hSt : toZModPow 3 (∑ i, t i) = toZModPow 3 (∑ i, t' i) := by
    simp only [ht_def, ht'_def, Fin.sum_cons, map_add, map_mul, map_ofNat]
    linear_combination -(hb + hc + hd + he) - toZModPow 3 a * h8
  rw [Fin.prod_cons, map_mul, hPt] at hP
  rw [Fin.sum_cons, map_add, hSt] at hS
  refine (equivalent_weightedSumSquares_cons a (ih t t' ht ht' hPt hSt)).trans ?_
  refine equivalent_of_two_mul_sub_eq_zero ih (fun i ↦ ?_) hv ?_ ?_ (Fin.succ 0) ?_
  · exact Fin.cases (by simpa using hw 0) ht' i
  · rwa [Fin.prod_cons, map_mul]
  · rwa [Fin.sum_cons, map_add]
  · simp only [ht'_def, Fin.cons_succ, Fin.cons_zero, map_mul, map_ofNat]
    linear_combination hv0 - 3 * hb - toZModPow 3 a * h8

/-- **The classification of diagonal forms by residues modulo `8`**, proved by strong induction on
the rank. If some coefficient of either form is congruent modulo `4` to the first coefficient of the
other, the step `equivalent_of_two_mul_sub_eq_zero` applies. Otherwise the coefficients of each form
lie in one class modulo `4`, and the two classes are opposite. This is impossible in ranks one to
three, and it is handled by the quaternary step in rank four and by tripling four coefficients in
higher rank. -/
private theorem classified (n : ℕ) : Classified n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w v hw hv hP hS
  rcases n with _ | m
  · obtain rfl := Subsingleton.elim w v
    exact .refl _
  have ihm := ih m (Nat.lt_succ_self m)
  by_cases hA : ∃ j, 2 * (toZModPow 3 (v 0) - toZModPow 3 (w j)) = 0
  · obtain ⟨j, hj⟩ := hA
    exact equivalent_of_two_mul_sub_eq_zero ihm hw hv hP hS j hj
  by_cases hA' : ∃ j, 2 * (toZModPow 3 (w 0) - toZModPow 3 (v j)) = 0
  · obtain ⟨j, hj⟩ := hA'
    exact (equivalent_of_two_mul_sub_eq_zero ihm hv hw hP.symm hS.symm j hj).symm
  simp only [not_exists] at hA hA'
  have hv' (j : Fin (m + 1)) : 2 * (toZModPow 3 (v j) + toZModPow 3 (w 0)) = 0 := by
    linear_combination two_mul_add_eq_zero_of_ne (hw 0) (hv j) (hA' j)
  have hw' (j : Fin (m + 1)) : 2 * (toZModPow 3 (w j) - toZModPow 3 (w 0)) = 0 := by
    linear_combination two_mul_add_eq_zero_of_ne (hv 0) (hw j) (hA j) - hv' 0
  have h8 : (8 : ZMod (2 ^ 3)) = 0 := by decide
  have h4 : 4 * toZModPow 3 (w 0) ≠ 0 := by
    have key : ∀ x : ZMod (2 ^ 3), x * x = 1 → 4 * x ≠ 0 := by decide
    exact key _ (hw 0)
  rcases m with _ | _ | _ | _ | k
  · -- Rank one: the coefficients agree modulo `8`, but are opposite modulo `4`.
    refine absurd ?_ h4
    have h1 : toZModPow 3 (w 0) = toZModPow 3 (v 0) := by simpa using hP
    linear_combination hv' 0 + 2 * h1
  · -- Rank two: the coefficient products then cannot agree together with the sums.
    have key : ∀ a b c d : ZMod (2 ^ 3), a * a = 1 → b * b = 1 → 2 * (b - a) = 0 → c * c = 1 →
        2 * (c + a) = 0 → d * d = 1 → 2 * (d + a) = 0 → a * b = c * d → a + b = c + d → False := by
      decide
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Fin.succ_zero_eq_one, mul_one, add_zero, map_mul, map_add] at hP hS
    exact (key _ _ _ _ (hw 0) (hw 1) (hw' 1) (hv 0) (hv' 0) (hv 1) (hv' 1) hP hS).elim
  · -- Rank three: the coefficient sums are opposite modulo `4`.
    refine absurd ?_ h4
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      add_zero, map_add] at hS
    linear_combination 2 * hS - hw' 1 - hw' 2 + hv' 0 + hv' 1 + hv' 2 - toZModPow 3 (w 0) * h8
  · exact equivalent_of_rank_four (ih 3 (by omega)) hw hv hP hS hw' (hv' 0)
  · exact equivalent_of_five_le (ih (k + 4) (by omega)) hw hv hP hS hw' (hv' 0)

/-! ### The classification -/

/-- **Odd unimodular diagonal forms over `ℤ₂`.** Two diagonal quadratic forms over `ℤ₂` with unit
coefficients `w` and `v`, indexed by the same finite type, are isometric when the products of their
coefficients differ by a square and the sums of their coefficients agree modulo `8`.

The first hypothesis is also necessary (`TauCeti.isSquare_prod_mul_prod_of_equivalent`). -/
theorem equivalent_weightedSumSquares_of_isSquare_prod_mul_prod_of_eight_dvd_sum_sub_sum
    {ι : Type*} [Fintype ι] {w v : ι → ℤ_[2]ˣ} (hdet : IsSquare ((∏ i, w i) * ∏ i, v i))
    (hodd : (8 : ℤ_[2]) ∣ ∑ i, (w i : ℤ_[2]) - ∑ i, (v i : ℤ_[2])) :
    (weightedSumSquares ℤ_[2] w).Equivalent (weightedSumSquares ℤ_[2] v) := by
  let e := (Fintype.equivFin ι).symm
  rw [weightedSumSquares_units, weightedSumSquares_units]
  refine (equivalent_weightedSumSquares_comp _ e).trans
    (Equivalent.trans ?_ (equivalent_weightedSumSquares_comp _ e).symm)
  have hpw : ∏ i, ((fun i ↦ (w i : ℤ_[2])) ∘ e) i = ∏ i, (w i : ℤ_[2]) :=
    Equiv.prod_comp e fun i ↦ (w i : ℤ_[2])
  have hpv : ∏ i, ((fun i ↦ (v i : ℤ_[2])) ∘ e) i = ∏ i, (v i : ℤ_[2]) :=
    Equiv.prod_comp e fun i ↦ (v i : ℤ_[2])
  have hsw : ∑ i, ((fun i ↦ (w i : ℤ_[2])) ∘ e) i = ∑ i, (w i : ℤ_[2]) :=
    Equiv.sum_comp e fun i ↦ (w i : ℤ_[2])
  have hsv : ∑ i, ((fun i ↦ (v i : ℤ_[2])) ∘ e) i = ∑ i, (v i : ℤ_[2]) :=
    Equiv.sum_comp e fun i ↦ (v i : ℤ_[2])
  refine classified _ _ _ (fun i ↦ toZModPow_three_mul_self _) (fun i ↦ toZModPow_three_mul_self _)
    ?_ ?_
  · -- Equal residues of the products: both are odd and their product is a square.
    obtain ⟨s, hs⟩ := hdet
    have hs' : toZModPow 3 (∏ i, (w i : ℤ_[2])) * toZModPow 3 (∏ i, (v i : ℤ_[2])) =
        toZModPow 3 (s : ℤ_[2]) * toZModPow 3 (s : ℤ_[2]) := by
      rw [← map_mul, ← map_mul, ← Units.coe_prod, ← Units.coe_prod, ← Units.val_mul, hs,
        Units.val_mul]
    have hv := toZModPow_three_mul_self (∏ i, v i)
    rw [Units.coe_prod] at hv
    rw [hpw, hpv]
    linear_combination -toZModPow 3 (∏ i, (w i : ℤ_[2])) * hv +
      toZModPow 3 (∏ i, (v i : ℤ_[2])) * hs' +
      toZModPow 3 (∏ i, (v i : ℤ_[2])) * toZModPow_three_mul_self s
  · -- Equal residues of the sums.
    rw [hsw, hsv, ← sub_eq_zero, ← map_sub, toZModPow_eq_zero_iff_dvd]
    norm_num
    exact hodd

end TauCeti

namespace LinearMap.BilinForm

open Module QuadraticMap
open LinearMap (BilinForm)

variable {ι M N : Type*} [Fintype ι] [AddCommGroup M] [Module ℤ_[2] M]
  [AddCommGroup N] [Module ℤ_[2] N] {B : BilinForm ℤ_[2] M} {C : BilinForm ℤ_[2] N}
  {b : Basis ι ℤ_[2] M} {c : Basis ι ℤ_[2] N}

/-- **Odd unimodular forms over `ℤ₂`.** Two bilinear forms over `ℤ₂` with orthogonal bases `b`
and `c` of the same index type, all of whose self-pairings are units, are isometric when the
products of their self-pairings differ by a square and the sums of their self-pairings agree
modulo `8`. Odd unimodular symmetric forms have such bases
(`LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self`). -/
theorem iIsOrtho.equivalent_of_isSquare_prod_mul_prod_of_eight_dvd_sum_sub_sum
    (hb : B.iIsOrtho b) (hc : C.iIsOrtho c) (hbu : ∀ i, IsUnit (B (b i) (b i)))
    (hcu : ∀ i, IsUnit (C (c i) (c i)))
    (hdet : IsSquare ((∏ i, B (b i) (b i)) * ∏ i, C (c i) (c i)))
    (hodd : (8 : ℤ_[2]) ∣ ∑ i, B (b i) (b i) - ∑ i, C (c i) (c i)) :
    B.Equivalent C := by
  classical
  -- A form with an orthogonal basis is isometric to the diagonal form of its self-pairings.
  have hB : B.Equivalent (Matrix.toBilin' (Matrix.diagonal fun i ↦ B (b i) (b i))) :=
    ⟨b.isometryEquivOfToMatrixEq (Pi.basisFun ℤ_[2] ι)
      (by rw [hb.toMatrix_eq_diagonal, toMatrix_basisFun, toMatrix'_toBilin'])⟩
  have hC : C.Equivalent (Matrix.toBilin' (Matrix.diagonal fun i ↦ C (c i) (c i))) :=
    ⟨c.isometryEquivOfToMatrixEq (Pi.basisFun ℤ_[2] ι)
      (by rw [hc.toMatrix_eq_diagonal, toMatrix_basisFun, toMatrix'_toBilin'])⟩
  have hquad (u : ι → ℤ_[2]) :
      (Matrix.toBilin' (Matrix.diagonal u)).toQuadraticMap = weightedSumSquares ℤ_[2] u := by
    ext x
    simp [Matrix.toBilin'_apply', Matrix.mulVec_diagonal, dotProduct, weightedSumSquares_apply,
      mul_left_comm]
  have hsymm (u : ι → ℤ_[2]) : (Matrix.toBilin' (Matrix.diagonal u)).IsSymm :=
    Matrix.isSymm_toBilin'_iff_isSymm.mpr (Matrix.isSymm_diagonal _)
  refine hB.trans (Equivalent.trans ?_ hC.symm)
  rw [IsSymm.equivalent_iff_toQuadraticMap_equivalent (hsymm _) (hsymm _)
    (.of_ne_zero two_ne_zero), hquad, hquad]
  have h := TauCeti.equivalent_weightedSumSquares_of_isSquare_prod_mul_prod_of_eight_dvd_sum_sub_sum
    (w := fun i ↦ (hbu i).unit) (v := fun i ↦ (hcu i).unit)
    (by rw [← TauCeti.isSquare_units_val_iff]; simpa using hdet) (by simpa using hodd)
  simpa only [weightedSumSquares_units, IsUnit.unit_spec] using h

end LinearMap.BilinForm
