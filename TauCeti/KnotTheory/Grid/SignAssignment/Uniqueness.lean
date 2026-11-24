/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SignAssignment.Basic
public import TauCeti.KnotTheory.Grid.SignAssignment.Differential
import TauCeti.GroupTheory.Coxeter.Cocycle
import TauCeti.GroupTheory.Perm.Coxeter
import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Geometry
import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Uniqueness of grid sign assignments up to gauge

Any two sign assignments `S` and `T` for size-`n` grid states differ by a gauge transformation:
there is a sign function `f : GridState n → ℤˣ` with `S.gauge f = T`, and `f` is unique up to a
global sign flip `f ↦ -f`. In particular, fixing `f x₀` at a single grid state `x₀` determines the
gauge uniquely, and the signed unblocked grid complexes `(GC⁻, ∂⁻_S)` and `(GC⁻, ∂⁻_T)` are
isomorphic via the diagonal sign change `Finsupp.signEquiv`.

## Proof overview

The pointwise ratio `r ↦ S(r) * T(r)` of two sign assignments satisfies the *unsigned* versions of
the three axioms: equal products on opposite decompositions of a square (commuting or recut), and
product `1` on both vertical and horizontal annuli. For `n ≥ 2`:

1. Restricting the ratio to width-one rectangles between adjacent columns `i` and `i + 1`
   (`0 ≤ i < n - 1`) produces a `ℤˣ`-valued 1-cochain on the right Cayley graph of
   `Equiv.Perm (Fin n)` with its type-`A` Coxeter system `TauCeti.permCoxeterSystem n`. The vertical
   annulus rule gives the involution condition, disjoint commutation gives the distant braid
   relation, and two recuts of a length-three hexagon give the adjacent braid relation.
2. Simply connectedness of the Coxeter Cayley 2-complex
   (`CoxeterSystem.exists_cocycle_eq_inv_mul`) produces a gauge `g` such that `S` and
   `T' = T.gauge g` agree on all adjacent width-one rectangles.
3. Strong induction on cyclic width extends agreement on any set of width-one columns to all empty
   rectangles whose covered columns lie in that set, first giving all non-wrapping empty rectangles.
4. Strong induction on vertical height extends agreement to wrapping width-one rectangles from
   column `n - 1` to column `0`, using the horizontal annulus rule for height `1` and recutting off
   a height-one strip for height `≥ 2`.
5. Applying the same width induction to all columns extends agreement to every empty rectangle,
   giving `S = T.gauge g` and hence `S.gauge g = T`.

## Main results

* `TauCeti.GridSignAssignment.gauge_neg`: negating a gauge leaves the gauged sign assignment
  unchanged.
* `TauCeti.GridSignAssignment.gauge_eq_iff`: two gauges produce the same sign assignment if and only
  if they are equal or opposite.
* `TauCeti.GridSignAssignment.exists_gauge_eq`: any two sign assignments of the same size are
  related by a gauge transformation.
* `TauCeti.GridSignAssignment.existsUnique_gauge_eq`: the gauge relating two sign assignments is
  unique once its value at one grid state is fixed.
* `TauCeti.GridDiagram.exists_signEquiv_signedUnblockedDifferential`: any two sign assignments
  induce conjugate signed unblocked differentials via `Finsupp.signEquiv`.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), Theorem 4.2.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Proposition 15.2.8.
-/

public section

namespace TauCeti

namespace GridSignAssignment

variable {n : ℕ}

/-! ### Auxiliary unit arithmetic and the ratio of two sign assignments -/

private theorem units_eq_of_mul_eq_one {a b : ℤˣ} (h : a * b = 1) : b = a :=
  (eq_inv_of_mul_eq_one_right h).trans (Int.units_inv_eq_self a)

private theorem units_eq_neg_of_mul_eq_neg_one {a b : ℤˣ} (h : a * b = -1) : b = -a := by
  simpa only [← mul_assoc, Int.units_mul_self, one_mul, mul_neg, mul_one] using congrArg (a * ·) h

/-- The pointwise product of two sign assignments on an empty rectangle, equal to `1` exactly where
the two sign assignments agree. -/
private def ratio (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) : ℤˣ :=
  S.sign r hr * T.sign r hr

private theorem ratio_eq_one_iff (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) :
    ratio S T r hr = 1 ↔ S.sign r hr = T.sign r hr :=
  ⟨fun h => (units_eq_of_mul_eq_one h).symm, fun h => by rw [ratio, h, Int.units_mul_self]⟩

private theorem ratio_congr (S T : GridSignAssignment n) {x y x' y' : GridState n}
    {r : GridRectangleBetween x y} {r' : GridRectangleBetween x' y'}
    (hr : r.IsEmpty) (hr' : r'.IsEmpty) (hx : x = x')
    (hl : r.left = r'.left) (hrr : r.right = r'.right) :
    ratio S T r hr = ratio S T r' hr' := by
  subst hx
  have hy : y = y' := by rw [r.target_eq_swapColumns, r'.target_eq_swapColumns, hl, hrr]
  subst hy
  obtain rfl : r = r' := GridRectangleBetween.ext hl hrr
  rfl

private theorem ratio_mul_ratio (S T : GridSignAssignment n) {x₁ y₁ x₂ y₂ : GridState n}
    (r₁ : GridRectangleBetween x₁ y₁) (r₂ : GridRectangleBetween x₂ y₂)
    (h₁ : r₁.IsEmpty) (h₂ : r₂.IsEmpty) :
    ratio S T r₁ h₁ * ratio S T r₂ h₂ =
      (S.sign r₁ h₁ * S.sign r₂ h₂) * (T.sign r₁ h₁ * T.sign r₂ h₂) := by
  unfold ratio; ac_rfl

private theorem ratio_square (S T : GridSignAssignment n) {x z : GridState n}
    (D E : GridRectangleDecomposition x z)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hE₁ : E.first.IsEmpty) (hE₂ : E.second.IsEmpty) (hne : E ≠ D)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.second.toGridRectangle.coveredSquares.val) :
    ratio S T E.first hE₁ * ratio S T E.second hE₂ =
      ratio S T D.first hD₁ * ratio S T D.second hD₂ := by
  rw [ratio_mul_ratio, ratio_mul_ratio,
    S.sign_mul_sign_eq_neg D E hD₁ hD₂ hE₁ hE₂ hne hdomain,
    T.sign_mul_sign_eq_neg D E hD₁ hD₂ hE₁ hE₂ hne hdomain, neg_mul_neg]

private theorem ratio_commute (S T : GridSignAssignment n) {x z : GridState n}
    (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides)
    (h₁ : D.first.IsEmpty) (h₂ : D.second.IsEmpty) :
    ratio S T (D.commute h).first (D.isEmpty_commute_first h h₁ h₂) *
        ratio S T (D.commute h).second (D.isEmpty_commute_second h h₁ h₂) =
      ratio S T D.first h₁ * ratio S T D.second h₂ :=
  ratio_square S T D (D.commute h) h₁ h₂
    (D.isEmpty_commute_first h h₁ h₂) (D.isEmpty_commute_second h h₁ h₂) (D.commute_ne h)
    (by rw [D.commute_first_toGridRectangle h, D.commute_second_toGridRectangle h, add_comm])

private theorem ratio_recut (S T : GridSignAssignment n) {x z : GridState n}
    (D : GridRectangleDecomposition x z) (hone : D.HasOneCommonSide)
    (h₁ : D.first.IsEmpty) (h₂ : D.second.IsEmpty) :
    ratio S T (D.recut hone h₁ h₂).first (D.isRecut_recut hone h₁ h₂).isEmpty_first *
        ratio S T (D.recut hone h₁ h₂).second (D.isRecut_recut hone h₁ h₂).isEmpty_second =
      ratio S T D.first h₁ * ratio S T D.second h₂ :=
  ratio_square S T D (D.recut hone h₁ h₂) h₁ h₂
    (D.isRecut_recut hone h₁ h₂).isEmpty_first (D.isRecut_recut hone h₁ h₂).isEmpty_second
    (D.recut_ne hone h₁ h₂) (D.isRecut_recut hone h₁ h₂).isRepartition.val_add_val_eq

private theorem ratio_vertical_annulus (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (s : GridRectangleBetween y x)
    (hr : r.IsEmpty) (hs : s.IsEmpty) (hleft : s.left = r.left) :
    ratio S T s hs = ratio S T r hr :=
  units_eq_of_mul_eq_one <| by
    rw [ratio_mul_ratio, S.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft,
      T.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft]
    simp

private theorem ratio_horizontal_annulus (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (s : GridRectangleBetween y x)
    (hr : r.IsEmpty) (hs : s.IsEmpty) (hleft : s.left = r.right) :
    ratio S T s hs = ratio S T r hr :=
  units_eq_of_mul_eq_one <| by
    rw [ratio_mul_ratio, S.sign_mul_sign_eq_one_of_left_eq_right r s hr hs hleft,
      T.sign_mul_sign_eq_one_of_left_eq_right r s hr hs hleft, one_mul]

/-! ### Width-one rectangles and the Coxeter 1-cocycle -/

private def widthOneRect (x : GridState n) (a : Fin n) (hn : 1 < n) :
    GridRectangleBetween x (x.swapColumns a (finRotate n a)) :=
  GridRectangleBetween.ofSwapColumns x _ a (finRotate n a) (Grid.finRotate_ne_self hn a).symm rfl

private theorem widthOneRect_left (x : GridState n) (a : Fin n) (hn : 1 < n) :
    (widthOneRect x a hn).left = a := GridRectangleBetween.ofSwapColumns_left ..

private theorem widthOneRect_right (x : GridState n) (a : Fin n) (hn : 1 < n) :
    (widthOneRect x a hn).right = finRotate n a := GridRectangleBetween.ofSwapColumns_right ..

private theorem widthOneRect_bottom (x : GridState n) (a : Fin n) (hn : 1 < n) :
    (widthOneRect x a hn).bottom = x a := GridRectangleBetween.ofSwapColumns_bottom ..

private theorem widthOneRect_top (x : GridState n) (a : Fin n) (hn : 1 < n) :
    (widthOneRect x a hn).top = x (finRotate n a) := GridRectangleBetween.ofSwapColumns_top ..

private theorem widthOneRect_isEmpty (x : GridState n) (a : Fin n) (hn : 1 < n) :
    (widthOneRect x a hn).IsEmpty :=
  GridRectangleBetween.isEmpty_of_right_eq_finRotate _
    (by rw [widthOneRect_left, widthOneRect_right])

private theorem finRotate_strand (i : Fin (n - 1)) :
    finRotate n (BraidGroup.strand i) = BraidGroup.strandSucc i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.isLt; omega⟩
  apply Fin.ext
  rw [coe_finRotate]
  have hne : BraidGroup.strand i ≠ Fin.last m := fun h => by
    have hval := congrArg Fin.val h
    simp only [BraidGroup.val_strand, Fin.val_last] at hval
    have := i.isLt; omega
  simp [hne]

private theorem mk_swapColumns_strand (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (⟨σ⟩ : GridState n).swapColumns (BraidGroup.strand i) (finRotate n (BraidGroup.strand i)) =
      ⟨σ * (permCoxeterSystem n).simple i⟩ := by
  ext c
  rw [GridState.swapColumns_apply, finRotate_strand, permCoxeterSystem_simple,
    BraidGroup.transposition_eq_swap]
  rfl

/-- The `ℤˣ`-valued 1-cochain on the right Cayley graph of `Equiv.Perm (Fin n)` obtained by
evaluating the ratio of `S` and `T` on adjacent width-one rectangles. -/
private def adjCocycle (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) : ℤˣ :=
  ratio S T (widthOneRect ⟨σ⟩ (BraidGroup.strand i) hn) (widthOneRect_isEmpty _ _ hn)

private theorem adjCocycle_inv (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) i = (adjCocycle S T hn σ i)⁻¹ := by
  let r := widthOneRect ⟨σ⟩ (BraidGroup.strand i) hn
  let s : GridRectangleBetween _ ⟨σ⟩ :=
    { left := r.left, right := r.right, left_ne_right := r.left_ne_right
      map_left := r.map_right.symm, map_right := r.map_left.symm
      map_of_ne := fun c hl hr => (r.map_of_ne c hl hr).symm }
  have hs : s.IsEmpty := GridRectangleBetween.isEmpty_of_right_eq_finRotate s
    (by simp [s, r, widthOneRect_left, widthOneRect_right])
  rw [adjCocycle, ratio_congr S T _ hs (mk_swapColumns_strand σ i).symm
      (by simp [s, r, widthOneRect_left]) (by simp [s, r, widthOneRect_right]),
    ratio_vertical_annulus S T r s (widthOneRect_isEmpty _ _ hn) hs rfl, Int.units_inv_eq_self]
  rfl

private theorem adjCocycle_braid_two (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)}
    (hdist : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    adjCocycle S T hn σ i * adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) j =
      adjCocycle S T hn σ j * adjCocycle S T hn (σ * (permCoxeterSystem n).simple j) i := by
  let x : GridState n := ⟨σ⟩
  let a := BraidGroup.strand i
  let b := BraidGroup.strand j
  let y := x.swapColumns a (finRotate n a)
  let D : GridRectangleDecomposition x (y.swapColumns b (finRotate n b)) :=
    { middle := y, first := widthOneRect x a hn, second := widthOneRect y b hn }
  have hdisj : D.HasDisjointSides := by
    rw [D.hasDisjointSides_iff]
    simp only [D, widthOneRect_left, widthOneRect_right, finRotate_strand, a, b, ne_eq,
      Fin.ext_iff, BraidGroup.val_strand, BraidGroup.val_strandSucc]
    omega
  have hD₁ := widthOneRect_isEmpty x a hn
  have hD₂ := widthOneRect_isEmpty y b hn
  have hcomm := ratio_commute S T D hdisj hD₁ hD₂
  rw [ratio_congr S T (D.isEmpty_commute_first hdisj hD₁ hD₂) (widthOneRect_isEmpty x b hn) rfl
      (by simp [D, widthOneRect_left, b]) (by simp [D, widthOneRect_right, b]),
    ratio_congr S T (D.isEmpty_commute_second hdisj hD₁ hD₂)
      (widthOneRect_isEmpty ⟨σ * (permCoxeterSystem n).simple j⟩ a hn)
      (by rw [D.commute_middle hdisj]; simp only [D, widthOneRect_left, widthOneRect_right, b]
          exact mk_swapColumns_strand σ j)
      (by simp [D, widthOneRect_left, a]) (by simp [D, widthOneRect_right, a]),
    ratio_congr S T hD₂ (widthOneRect_isEmpty ⟨σ * (permCoxeterSystem n).simple i⟩ b hn)
      (mk_swapColumns_strand σ i)
      (by simp [widthOneRect_left, b]) (by simp [widthOneRect_right, b])] at hcomm
  exact hcomm.symm

private theorem adjCocycle_braid_three_of_mem_cIoo (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j)
    (hrow : σ (BraidGroup.strandSucc i) ∈
      Grid.cIoo (σ (BraidGroup.strand i)) (σ (BraidGroup.strandSucc j))) :
    adjCocycle S T hn σ i *
        adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) j *
        adjCocycle S T hn
          (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i =
      adjCocycle S T hn σ j *
        adjCocycle S T hn (σ * (permCoxeterSystem n).simple j) i *
        adjCocycle S T hn
          (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j := by
  let x : GridState n := ⟨σ⟩
  let a := BraidGroup.strand i
  let b := BraidGroup.strandSucc i
  let c := BraidGroup.strandSucc j
  let si := (permCoxeterSystem n).simple i
  let sj := (permCoxeterSystem n).simple j
  have hbj : BraidGroup.strand j = b := BraidGroup.strand_eq_strandSucc_of_succ hij
  have hab : finRotate n a = b := finRotate_strand i
  have hbc : finRotate n b = c := hbj ▸ finRotate_strand j
  have hac : a ≠ c := BraidGroup.strand_ne_strandSucc_of_succ hij
  have hbac : b ∈ Grid.cIoo a c := by
    rw [Grid.mem_cIoo]; refine ⟨hac, ?_⟩
    have := BraidGroup.val_strand i; have := BraidGroup.val_strandSucc i
    have := BraidGroup.val_strandSucc j
    rw [ite_eq_left (by omega)]; omega
  -- First recut: `(a, b)` then `(b, c)`.
  let y₁ := x.swapColumns a (finRotate n a)
  let z₁ := y₁.swapColumns (BraidGroup.strand j) (finRotate n (BraidGroup.strand j))
  let D₁ : GridRectangleDecomposition x z₁ :=
    { middle := y₁, first := widthOneRect x a hn
      second := widthOneRect y₁ (BraidGroup.strand j) hn }
  have hD₁_common : D₁.first.right = D₁.second.left := by
    simp only [D₁, widthOneRect_right, widthOneRect_left, hab, hbj]
  have hone₁ := D₁.hasOneCommonSide_of_right_eq_left hD₁_common
    (by simpa only [D₁, widthOneRect_left, widthOneRect_right, hbj, hbc] using hac)
  have hD₁f : D₁.first.IsEmpty := widthOneRect_isEmpty _ _ hn
  have hD₁s : D₁.second.IsEmpty := widthOneRect_isEmpty _ _ hn
  let E₁ := D₁.recut hone₁ hD₁f hD₁s
  have hrec₁ := D₁.isRecut_recut hone₁ hD₁f hD₁s
  have hE₁_sides :
      E₁.first.left = b ∧ E₁.first.right = c ∧ E₁.second.left = a ∧ E₁.second.right = c := by
    rcases D₁.recut_geometry_of_right_eq_left hD₁_common hone₁ hD₁f hD₁s with
      ⟨-, hfl, hfr, hsl, hsr, -⟩ | ⟨hbad, -⟩
    · exact ⟨by simpa only [E₁, D₁, widthOneRect_right, hab] using hfl,
        by simpa only [E₁, D₁, widthOneRect_right, hbj, hbc] using hfr,
        by simpa only [E₁, D₁, widthOneRect_left] using hsl,
        by simpa only [E₁, D₁, widthOneRect_right, hbj, hbc] using hsr⟩
    · have hD₁_stop : D₁.second.top = σ c := by
        rw [show D₁.second.top = y₁ (finRotate n (BraidGroup.strand j)) from
          widthOneRect_top _ _ hn, hbj, hbc]
        change x (Equiv.swap a (finRotate n a) c) = σ c
        rw [hab, Equiv.swap_apply_of_ne_of_ne hac.symm (hbc ▸ Grid.finRotate_ne_self hn b)]
      rw [widthOneRect_bottom, show D₁.first.top = σ b by rw [widthOneRect_top, hab], hD₁_stop]
        at hbad
      exact False.elim (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap (σ a) (σ b)) hbad
        (Grid.mem_cIoo_cyclic_left hrow))
  obtain ⟨hE₁fl, hE₁fr, hE₁sl, hE₁sr⟩ := hE₁_sides
  have hy₁ : y₁ = ⟨σ * si⟩ := mk_swapColumns_strand σ i
  have hz₁ : z₁ = ⟨σ * si * sj⟩ := (by rw [← hy₁] : z₁ = _).trans (mk_swapColumns_strand _ j)
  have hE₁mid : E₁.middle = ⟨σ * sj⟩ := by
    rw [E₁.first.target_eq_swapColumns, hE₁fl, hE₁fr, ← hbc, ← hbj]
    exact mk_swapColumns_strand σ j
  have hstep₁ : adjCocycle S T hn σ j * ratio S T E₁.second hrec₁.isEmpty_second =
      adjCocycle S T hn σ i * adjCocycle S T hn (σ * si) j := by
    have hr₁ := ratio_recut S T D₁ hone₁ hD₁f hD₁s
    rw [ratio_congr S T hrec₁.isEmpty_first (widthOneRect_isEmpty x (BraidGroup.strand j) hn) rfl
        (by rw [hE₁fl, widthOneRect_left, hbj]) (by rw [hE₁fr, widthOneRect_right, hbj, hbc]),
      ratio_congr S T hD₁s (widthOneRect_isEmpty ⟨σ * si⟩ (BraidGroup.strand j) hn) hy₁
        (by simp [D₁, widthOneRect_left]) (by simp [D₁, widthOneRect_right])] at hr₁
    exact hr₁
  -- Second recut: `E₁.second` (sides `(a, c)`) followed by `(a, b)` at `z₁`.
  let D₂ : GridRectangleDecomposition E₁.middle (z₁.swapColumns a (finRotate n a)) :=
    { middle := z₁, first := E₁.second, second := widthOneRect z₁ a hn }
  have hD₂_common : D₂.first.left = D₂.second.left := hE₁sl.trans (widthOneRect_left z₁ a hn).symm
  have hD₂_col : D₂.second.right ∈ Grid.cIoo D₂.first.left D₂.first.right := by
    simpa only [D₂, widthOneRect_right, hE₁sl, hE₁sr, hab] using hbac
  have hone₂ := D₂.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hD₂_common hD₂_col
  have hD₂s : D₂.second.IsEmpty := widthOneRect_isEmpty _ _ hn
  let E₂ := D₂.recut hone₂ hrec₁.isEmpty_second hD₂s
  have hrec₂ := D₂.isRecut_recut hone₂ hrec₁.isEmpty_second hD₂s
  obtain ⟨hE₂fl, hE₂fr, hE₂sl, hE₂sr⟩ :=
    D₂.recut_sides_of_left_eq_left_of_mem_cIoo hD₂_common hD₂_col hrec₁.isEmpty_second hD₂s
  have hD₂sr : D₂.second.right = finRotate n a := widthOneRect_right z₁ a hn
  have hE₂mid : E₂.middle = ⟨σ * sj * si⟩ := by
    rw [E₂.first.target_eq_swapColumns, hE₂fl, hE₂fr, hE₁sl, hD₂sr, hE₁mid]
    exact mk_swapColumns_strand _ i
  have hstep₂ : adjCocycle S T hn (σ * sj) i * adjCocycle S T hn (σ * sj * si) j =
      ratio S T E₁.second hrec₁.isEmpty_second * adjCocycle S T hn (σ * si * sj) i := by
    have hr₂ := ratio_recut S T D₂ hone₂ hrec₁.isEmpty_second hD₂s
    rw [ratio_congr S T hrec₂.isEmpty_first (widthOneRect_isEmpty ⟨σ * sj⟩ a hn) hE₁mid
        (by rw [hE₂fl, hE₁sl, widthOneRect_left]) (by rw [hE₂fr, hD₂sr, widthOneRect_right]),
      ratio_congr S T hrec₂.isEmpty_second
        (widthOneRect_isEmpty ⟨σ * sj * si⟩ (BraidGroup.strand j) hn) hE₂mid
        (by rw [hE₂sl, hD₂sr, hab, widthOneRect_left, hbj])
        (by rw [hE₂sr, hE₁sr, widthOneRect_right, hbj, hbc]),
      ratio_congr S T hD₂s (widthOneRect_isEmpty ⟨σ * si * sj⟩ a hn) hz₁
        (by simp [D₂, widthOneRect_left, a]) (by simp [D₂, widthOneRect_right, a])] at hr₂
    exact hr₂
  change adjCocycle S T hn σ i * adjCocycle S T hn (σ * si) j *
      adjCocycle S T hn (σ * si * sj) i =
    adjCocycle S T hn σ j * adjCocycle S T hn (σ * sj) i * adjCocycle S T hn (σ * sj * si) j
  rw [← hstep₁, mul_assoc, ← hstep₂, ← mul_assoc]

private theorem adjCocycle_braid_three_of_succ (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j) :
    adjCocycle S T hn σ i *
        adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) j *
        adjCocycle S T hn
          (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i =
      adjCocycle S T hn σ j *
        adjCocycle S T hn (σ * (permCoxeterSystem n).simple j) i *
        adjCocycle S T hn
          (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j := by
  let a := BraidGroup.strand i
  let b := BraidGroup.strandSucc i
  let c := BraidGroup.strandSucc j
  by_cases hrow : σ b ∈ Grid.cIoo (σ a) (σ c)
  · exact adjCocycle_braid_three_of_mem_cIoo S T hn σ hij hrow
  · let si := (permCoxeterSystem n).simple i
    let sj := (permCoxeterSystem n).simple j
    let τ : Equiv.Perm (Fin n) := σ * si * sj * si
    have hτ_eq : τ = σ * sj * si * sj := by
      have hbraid : si * sj * si = sj * si * sj := by
        simpa only [si, sj, permCoxeterSystem_simple] using
          BraidGroup.transposition_braid (Or.inl hij)
      simp only [τ, mul_assoc, ← mul_assoc si sj si, hbraid]
    have hbj : BraidGroup.strand j = b := BraidGroup.strand_eq_strandSucc_of_succ hij
    have hab : a ≠ b := BraidGroup.strand_ne_strandSucc i
    have hbc : b ≠ c := hbj ▸ BraidGroup.strand_ne_strandSucc j
    have hac : a ≠ c := BraidGroup.strand_ne_strandSucc_of_succ hij
    have hsi : si = Equiv.swap a b := by
      simp only [si, permCoxeterSystem_simple, BraidGroup.transposition_eq_swap, a, b]
    have hsj : sj = Equiv.swap b c := by
      simp only [sj, permCoxeterSystem_simple, BraidGroup.transposition_eq_swap, hbj, c]
    have hrow' : τ b ∈ Grid.cIoo (τ a) (τ c) := by
      rw [show τ a = σ c by
          simp [τ, Equiv.Perm.mul_apply, hsi, hsj, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm],
        show τ b = σ b by
          simp [τ, Equiv.Perm.mul_apply, hsi, hsj, Equiv.swap_apply_of_ne_of_ne hab hac],
        show τ c = σ a by
          simp [τ, Equiv.Perm.mul_apply, hsi, hsj, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]]
      exact Grid.mem_cIoo_swap_of_notMem (σ.injective.ne hac)
        (σ.injective.ne hab.symm) (σ.injective.ne hbc) hrow
    have hsq : ∀ (w : Equiv.Perm (Fin n)) (k : Fin (n - 1)),
        w * (permCoxeterSystem n).simple k * (permCoxeterSystem n).simple k = w := fun w k => by
      simp [permCoxeterSystem_simple, BraidGroup.mul_transposition_mul_self]
    have hstep : ∀ w k, adjCocycle S T hn (w * (permCoxeterSystem n).simple k) k =
        adjCocycle S T hn w k := fun w k => by rw [adjCocycle_inv, Int.units_inv_eq_self]
    have hmain := adjCocycle_braid_three_of_mem_cIoo S T hn τ hij hrow'
    change adjCocycle S T hn τ i * adjCocycle S T hn (τ * si) j *
        adjCocycle S T hn (τ * si * sj) i =
      adjCocycle S T hn τ j * adjCocycle S T hn (τ * sj) i *
        adjCocycle S T hn (τ * sj * si) j at hmain
    have hL2 : τ * si = σ * si * sj := hsq _ i
    have hL3 : τ * si * sj = σ * si := by rw [hL2, hsq]
    have hR2 : τ * sj = σ * sj * si := by rw [hτ_eq, hsq]
    have hR3 : τ * sj * si = σ * sj := by rw [hR2, hsq]
    rw [hL3, hL2, hR3, hR2, hstep σ i, hstep (σ * si) j, hstep (σ * sj) i, hstep σ j,
      show adjCocycle S T hn τ i = adjCocycle S T hn (σ * si * sj) i from hstep _ i,
      show adjCocycle S T hn τ j = adjCocycle S T hn (σ * sj * si) j by rw [hτ_eq, hstep]] at hmain
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hmain

private theorem adjCocycle_braid (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) (i j : Fin (n - 1)) :
    (permCoxeterSystem n).wordCocycleProd (adjCocycle S T hn) σ
        (CoxeterSystem.braidWord (CoxeterMatrix.A (n - 1)) i j) =
      (permCoxeterSystem n).wordCocycleProd (adjCocycle S T hn) σ
        (CoxeterSystem.braidWord (CoxeterMatrix.A (n - 1)) j i) := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  have hval : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  by_cases hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
  · simp only [CoxeterSystem.braidWord, coxeterMatrixA_eq_three hadj,
      coxeterMatrixA_eq_three hadj.symm, CoxeterSystem.alternatingWord, List.concat_eq_append,
      List.nil_append, List.cons_append, CoxeterSystem.wordCocycleProd_cons,
      CoxeterSystem.wordCocycleProd_nil, mul_one, ← mul_assoc]
    rcases hadj with h | h
    · exact (adjCocycle_braid_three_of_succ S T hn σ h).symm
    · exact adjCocycle_braid_three_of_succ S T hn σ h
  · have hdist : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i := by omega
    simp only [CoxeterSystem.braidWord, coxeterMatrixA_eq_two hdist,
      coxeterMatrixA_eq_two hdist.symm, CoxeterSystem.alternatingWord, List.concat_eq_append,
      List.nil_append, List.cons_append, CoxeterSystem.wordCocycleProd_cons,
      CoxeterSystem.wordCocycleProd_nil, mul_one]
    exact adjCocycle_braid_two S T hn σ hdist

/-! ### Extending agreement from width-one rectangles to all empty rectangles -/

private theorem mem_cIoo_and_card_cIco_finRotate {a b : Fin n} (hn : 1 < n) {w : ℕ}
    (hab : a ≠ b) (hw : (Grid.cIco a b).card = w) (hw1 : w ≠ 1) :
    finRotate n a ∈ Grid.cIoo a b ∧ (Grid.cIco (finRotate n a) b).card = w - 1 := by
  have hge2 : 2 ≤ w := by have := Grid.card_cIco_of_ne hab; omega
  have hne : finRotate n a ≠ b := fun heq => by
    rw [Grid.cIco_eq_singleton_iff.mpr ⟨rfl, heq.symm, hab⟩, Finset.card_singleton] at hw
    omega
  have hmem : finRotate n a ∈ Grid.cIoo a b :=
    Grid.mem_cIoo_cyclic_right (Grid.mem_cIoo_finRotate_left_iff.mpr ⟨hab.symm, hne.symm⟩)
  refine ⟨hmem, ?_⟩
  have hunion := congrArg Finset.card (Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hmem)
  rw [Finset.card_union_of_disjoint (Grid.disjoint_cIco_cIco_of_mem_cIoo hmem), hw,
    Grid.cIco_eq_singleton_iff.mpr ⟨rfl, rfl, (Grid.finRotate_ne_self hn a).symm⟩,
    Finset.card_singleton] at hunion
  omega

/-- Agreement on width-one rectangles at columns satisfying `P` extends by induction on cyclic
width to every empty rectangle whose covered columns all satisfy `P`. -/
private theorem ratio_eq_one_of_forall_cIco (S T : GridSignAssignment n) (hn : 1 < n)
    {P : Fin n → Prop}
    (h1 : ∀ (x : GridState n) (a : Fin n), P a →
      ratio S T (widthOneRect x a hn) (widthOneRect_isEmpty x a hn) = 1) :
    ∀ (w : ℕ) {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      (Grid.cIco r.left r.right).card = w → (∀ c ∈ Grid.cIco r.left r.right, P c) →
      ratio S T r hr = 1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro x y r hr hw hP
    have hPa : P r.left := hP r.left (Grid.left_mem_cIco r.left_ne_right)
    by_cases hw1 : w = 1
    · have hcard_oo : (Grid.cIoo r.left r.right).card = 0 := by
        have := Grid.card_cIco_of_ne r.left_ne_right; omega
      have hright : r.right = finRotate n r.left :=
        (Grid.cIco_eq_singleton_iff.mp (show Grid.cIco r.left r.right = {r.left} by
          simp [Grid.cIco_of_ne r.left_ne_right, Finset.card_eq_zero.mp hcard_oo])).2.1
      rw [ratio_congr S T hr (widthOneRect_isEmpty x r.left hn) rfl
        (widthOneRect_left x r.left hn).symm
        (hright.trans (widthOneRect_right x r.left hn).symm), h1 x r.left hPa]
    · have hge2 : 2 ≤ w := by have := Grid.card_cIco_of_ne r.left_ne_right; omega
      obtain ⟨hb_mem, hcard_b⟩ := mem_cIoo_and_card_cIco_finRotate hn r.left_ne_right hw hw1
      let a := r.left
      let D : GridRectangleDecomposition x (y.swapColumns a (finRotate n a)) :=
        { middle := y, first := r, second := widthOneRect y a hn }
      have hD_common : D.first.left = D.second.left := (widthOneRect_left y a hn).symm
      have hD_col : D.second.right ∈ Grid.cIoo D.first.left D.first.right := by
        simpa only [D, widthOneRect_right] using hb_mem
      have hone := D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hD_common hD_col
      have hDs : D.second.IsEmpty := widthOneRect_isEmpty y a hn
      let E := D.recut hone hr hDs
      have hrec := D.isRecut_recut hone hr hDs
      obtain ⟨hEfl, hEfr, hEsl, hEsr⟩ :=
        D.recut_sides_of_left_eq_left_of_mem_cIoo hD_common hD_col hr hDs
      have hDsr : D.second.right = finRotate n a := widthOneRect_right y a hn
      have hEf : ratio S T E.first hrec.isEmpty_first = 1 := by
        rw [ratio_congr S T hrec.isEmpty_first (widthOneRect_isEmpty x a hn) rfl
          (hEfl.trans (widthOneRect_left x a hn).symm)
          (by rw [hEfr, hDsr, widthOneRect_right]), h1 x a hPa]
      have hEs : ratio S T E.second hrec.isEmpty_second = 1 :=
        ih (w - 1) (by omega) E.second hrec.isEmpty_second
          (by rwa [hEsl, hEsr, hDsr]) fun c hc => by
            rw [hEsl, hEsr, hDsr] at hc
            exact hP c (Grid.cIco_subset_of_mem_cIoo hb_mem hc)
      have hrecut := ratio_recut S T D hone hr hDs
      change ratio S T E.first hrec.isEmpty_first * ratio S T E.second hrec.isEmpty_second =
        ratio S T r hr * ratio S T D.second hDs at hrecut
      rw [hEf, hEs, h1 y a hPa, mul_one, mul_one] at hrecut
      exact hrecut.symm

/-- A wrapping height-one rectangle pairs via a horizontal annulus with a non-wrapping empty
rectangle, so agreement on non-wrapping rectangles forces its ratio to be `1`. -/
private theorem ratio_eq_one_of_cIoo_rows_eq_empty (S T : GridSignAssignment n)
    (hnonwrap : ∀ {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      r.left.val < r.right.val → ratio S T r hr = 1)
    {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty)
    (hrev : r.right.val < r.left.val) (hrows : Grid.cIoo r.bottom r.top = ∅) :
    ratio S T r hr = 1 := by
  let s : GridRectangleBetween y x :=
    { left := r.right, right := r.left, left_ne_right := r.left_ne_right.symm
      map_left := r.map_left.symm, map_right := r.map_right.symm
      map_of_ne := fun c hl hr => (r.map_of_ne c hr hl).symm }
  have hs_empty : s.IsEmpty := by
    rw [s.isEmpty_iff_forall_notMem_cIoo]; intro _ _
    rw [show s.bottom = r.bottom from r.map_right, show s.top = r.top from r.map_left, hrows]
    exact Finset.notMem_empty _
  rw [← ratio_horizontal_annulus S T r s hr hs_empty rfl]
  exact hnonwrap s hs_empty hrev

/-- Agreement on all non-wrapping empty rectangles extends to wrapping width-one rectangles from
column `n - 1` to column `0`, by induction on vertical height. -/
private theorem ratio_eq_one_lastCol (S T : GridSignAssignment n) (hn : 1 < n)
    (hnonwrap : ∀ {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      r.left.val < r.right.val → ratio S T r hr = 1) :
    ∀ (h : ℕ) (x : GridState n),
      (Grid.cIco (x ⟨n - 1, by omega⟩) (x ⟨0, by omega⟩)).card = h →
      ratio S T (widthOneRect x ⟨n - 1, by omega⟩ hn)
        (widthOneRect_isEmpty x ⟨n - 1, by omega⟩ hn) = 1 := by
  let lastCol : Fin n := ⟨n - 1, by omega⟩
  let zeroCol : Fin n := ⟨0, by omega⟩
  have hrot_last : finRotate n lastCol = zeroCol := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact Fin.ext (by rw [coe_finRotate]; simp [lastCol, Fin.last, zeroCol])
  have hlast_ne_zero : lastCol ≠ zeroCol :=
    hrot_last ▸ (Grid.finRotate_ne_self hn lastCol).symm
  intro h
  induction h using Nat.strong_induction_on with
  | ind h ih =>
    intro x hh
    change (Grid.cIco (x lastCol) (x zeroCol)).card = h at hh
    have hne_rows : x lastCol ≠ x zeroCol := x.toPerm.injective.ne hlast_ne_zero
    by_cases hh1 : h = 1
    · exact ratio_eq_one_of_cIoo_rows_eq_empty S T hnonwrap (widthOneRect x lastCol hn)
        (widthOneRect_isEmpty x lastCol hn)
        (by rw [widthOneRect_right, widthOneRect_left, hrot_last]; simp only [zeroCol, lastCol]
            omega)
        (by rw [widthOneRect_bottom, widthOneRect_top, hrot_last]
            exact Finset.card_eq_zero.mp (by have := Grid.card_cIco_of_ne hne_rows; omega))
    · have hge2 : 2 ≤ h := by have := Grid.card_cIco_of_ne hne_rows; omega
      obtain ⟨hr_mid_mem, hcard_mid⟩ := mem_cIoo_and_card_cIco_finRotate hn hne_rows hh hh1
      let r_mid : Fin n := finRotate n (x lastCol)
      let c : Fin n := x.toPerm.symm r_mid
      have hxc : x c = r_mid := x.toPerm.apply_symm_apply r_mid
      have hc_ne_last : c ≠ lastCol := fun heq =>
        Grid.finRotate_ne_self hn (x lastCol) (hxc.symm.trans (congrArg x heq))
      have hc_ne_zero : c ≠ zeroCol := fun heq =>
        Grid.right_notMem_cIoo (x lastCol) (x zeroCol) (by
          rw [show finRotate n (x lastCol) = x zeroCol from hxc.symm.trans (congrArg x heq)]
            at hr_mid_mem
          exact hr_mid_mem)
      have hc_pos : 0 < c.val := Nat.pos_of_ne_zero fun heq => hc_ne_zero (Fin.ext heq)
      have hc_lt : c.val < n - 1 := by
        have := c.isLt; exact lt_of_le_of_ne (by omega) fun heq => hc_ne_last (Fin.ext heq)
      let w := x.swapColumns lastCol c
      let t : GridRectangleBetween x w :=
        GridRectangleBetween.ofSwapColumns x w lastCol c hc_ne_last.symm rfl
      have ht_rows : Grid.cIoo t.bottom t.top = ∅ := by
        rw [show t.bottom = x lastCol from GridRectangleBetween.ofSwapColumns_bottom ..,
          (GridRectangleBetween.ofSwapColumns_top ..).trans hxc, Grid.cIoo_finRotate_eq_empty]
      have ht_empty : t.IsEmpty := by
        rw [t.isEmpty_iff_forall_notMem_cIoo]; intro _ _; rw [ht_rows]; exact Finset.notMem_empty _
      have ht_ratio : ratio S T t ht_empty = 1 :=
        ratio_eq_one_of_cIoo_rows_eq_empty S T hnonwrap t ht_empty
          (by rw [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right]
              exact hc_lt) ht_rows
      let D : GridRectangleDecomposition x (w.swapColumns lastCol (finRotate n lastCol)) :=
        { middle := w, first := t, second := widthOneRect w lastCol hn }
      have hDfl : D.first.left = lastCol := GridRectangleBetween.ofSwapColumns_left ..
      have hDfr : D.first.right = c := GridRectangleBetween.ofSwapColumns_right ..
      have hDsr : D.second.right = zeroCol := (widthOneRect_right w lastCol hn).trans hrot_last
      have hD_common : D.first.left = D.second.left :=
        hDfl.trans (widthOneRect_left w lastCol hn).symm
      have hD_col : D.second.right ∈ Grid.cIoo D.first.left D.first.right := by
        rw [hDfl, hDfr, hDsr, Grid.mem_cIoo]
        refine ⟨hc_ne_last.symm, ?_⟩
        rw [ite_eq_right (by simp [lastCol]; omega)]; exact Or.inr hc_pos
      have hone := D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hD_common hD_col
      have hDs : D.second.IsEmpty := widthOneRect_isEmpty w lastCol hn
      let E := D.recut hone ht_empty hDs
      have hrec := D.isRecut_recut hone ht_empty hDs
      obtain ⟨hEfl, hEfr, hEsl, hEsr⟩ :=
        D.recut_sides_of_left_eq_left_of_mem_cIoo hD_common hD_col ht_empty hDs
      have hD2_height : (Grid.cIco (w lastCol) (w zeroCol)).card = h - 1 := by
        rw [show w lastCol = r_mid by simp [w, hxc],
          show w zeroCol = x zeroCol by
            simp [w, Equiv.swap_apply_of_ne_of_ne hlast_ne_zero.symm hc_ne_zero.symm]]
        exact hcard_mid
      have hrecut := ratio_recut S T D hone ht_empty hDs
      change ratio S T E.first hrec.isEmpty_first * ratio S T E.second hrec.isEmpty_second =
        ratio S T t ht_empty * ratio S T D.second hDs at hrecut
      rw [ratio_congr S T _ (widthOneRect_isEmpty x lastCol hn) rfl
            (by rw [hEfl, hDfl, widthOneRect_left])
            (by rw [hEfr, hDsr, widthOneRect_right, hrot_last]),
          hnonwrap E.second hrec.isEmpty_second (by rw [hEsl, hEsr, hDsr, hDfr]; exact hc_pos),
          ht_ratio, ih (h - 1) (by omega) w hD2_height, mul_one, mul_one] at hrecut
      exact hrecut

/-! ### Main uniqueness theorems -/

/-- Negating a gauge leaves the gauged sign assignment unchanged, since every rectangle carries
both endpoint signs. -/
@[simp]
theorem gauge_neg (S : GridSignAssignment n) (f : GridState n → ℤˣ) :
    S.gauge (-f) = S.gauge f := by
  refine GridSignAssignment.ext fun x y r hr => ?_
  simp only [gauge_sign, Pi.neg_apply, neg_mul_neg]

/-- Two gauges produce the same sign assignment if and only if they agree everywhere or are
opposite everywhere. -/
theorem gauge_eq_iff (S : GridSignAssignment n) (f g : GridState n → ℤˣ) :
    S.gauge f = S.gauge g ↔ f = g ∨ f = -g := by
  constructor
  · intro heq
    let h : GridState n → ℤˣ := fun x => f x * g x
    have hconst : ∀ x : GridState n, h x = h ⟨1⟩ := by
      by_cases hn : 1 < n
      · intro x
        have hstep : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)),
            h ⟨σ * (permCoxeterSystem n).simple i⟩ = h ⟨σ⟩ := fun σ i => by
          have hsign := congrArg (fun A : GridSignAssignment n =>
            A.sign (widthOneRect ⟨σ⟩ (BraidGroup.strand i) hn) (widthOneRect_isEmpty _ _ hn)) heq
          simp only [gauge_sign, mk_swapColumns_strand] at hsign
          refine units_eq_of_mul_eq_one ?_
          rw [show h ⟨σ⟩ * h ⟨σ * (permCoxeterSystem n).simple i⟩ =
              (f ⟨σ⟩ * f ⟨σ * (permCoxeterSystem n).simple i⟩) *
                (g ⟨σ⟩ * g ⟨σ * (permCoxeterSystem n).simple i⟩) by unfold h; ac_rfl,
            mul_right_cancel hsign, Int.units_mul_self]
        exact (permCoxeterSystem n).fun_eq_const_of_mul_simple_eq
          (f := fun σ => h ⟨σ⟩) hstep x.toPerm
      · intro x; rw [show x = ⟨1⟩ by ext c; have := c.isLt; omega]
    rcases Int.units_eq_one_or (h ⟨1⟩) with h1 | h1
    · exact Or.inl (funext fun x => (units_eq_of_mul_eq_one ((hconst x).trans h1)).symm)
    · exact Or.inr (funext fun x => by
        simpa [Pi.neg_apply] using
          (congrArg Neg.neg (units_eq_neg_of_mul_eq_neg_one ((hconst x).trans h1))).symm)
  · rintro (rfl | rfl)
    · rfl
    · exact S.gauge_neg g

/-- **Uniqueness of grid sign assignments up to gauge.** Any two sign assignments on size-`n` grid
states differ by a gauge transformation. -/
theorem exists_gauge_eq (S T : GridSignAssignment n) :
    ∃ f : GridState n → ℤˣ, S.gauge f = T := by
  by_cases hn : 1 < n
  · obtain ⟨f, hf⟩ := (permCoxeterSystem n).exists_cocycle_eq_inv_mul
      (adjCocycle_inv S T hn) (adjCocycle_braid S T hn)
    let g : GridState n → ℤˣ := fun x => f x.toPerm
    let T' : GridSignAssignment n := T.gauge g
    have hadj : ∀ (x : GridState n) (i : Fin (n - 1)),
        ratio S T' (widthOneRect x (BraidGroup.strand i) hn) (widthOneRect_isEmpty x _ hn) = 1 :=
      fun x i => by
        have hbase : ratio S T (widthOneRect x (BraidGroup.strand i) hn)
              (widthOneRect_isEmpty x _ hn) =
            (f x.toPerm)⁻¹ * f (x.toPerm * (permCoxeterSystem n).simple i) := (hf x.toPerm i).symm
        rw [show ratio S T' _ _ = (g x * g (x.swapColumns (BraidGroup.strand i)
                (finRotate n (BraidGroup.strand i)))) * ratio S T _ _ by
              simp only [ratio, T', gauge_sign]; ac_rfl,
          hbase, mk_swapColumns_strand x.toPerm i]
        simp only [g, Int.units_inv_eq_self, Int.units_mul_self]
    have hadj' : ∀ (x : GridState n) (a : Fin n), a.val < n - 1 →
        ratio S T' (widthOneRect x a hn) (widthOneRect_isEmpty x a hn) = 1 := fun x a ha =>
      (Fin.ext (BraidGroup.val_strand ⟨a.val, ha⟩) : BraidGroup.strand ⟨a.val, ha⟩ = a) ▸
        hadj x ⟨a.val, ha⟩
    have hnonwrap : ∀ {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
        r.left.val < r.right.val → ratio S T' r hr = 1 := fun r hr hlt =>
      ratio_eq_one_of_forall_cIco S T' hn (P := fun c => c.val < n - 1) hadj' _ r hr rfl
        fun c hc => by
          rw [Grid.cIco_eq_Ico_of_lt hlt, Finset.mem_Ico] at hc
          have := r.right.isLt; omega
    have hall1 : ∀ (x : GridState n) (a : Fin n), True →
        ratio S T' (widthOneRect x a hn) (widthOneRect_isEmpty x a hn) = 1 := fun x a _ => by
      by_cases ha : a.val < n - 1
      · exact hadj' x a ha
      · rw [show a = ⟨n - 1, by omega⟩ from Fin.ext (by have := a.isLt; dsimp; omega)]
        exact ratio_eq_one_lastCol S T' hn hnonwrap _ x rfl
    have hST' : S = T' := GridSignAssignment.ext fun _ _ r hr =>
      (ratio_eq_one_iff S T' r hr).mp
        (ratio_eq_one_of_forall_cIco S T' hn (P := fun _ => True) hall1 _ r hr rfl fun _ _ =>
          trivial)
    exact ⟨g, hST'.symm ▸ T.gauge_gauge_self g⟩
  · refine ⟨1, GridSignAssignment.ext fun _ _ r _ => ?_⟩
    have := r.left.isLt; have := r.right.isLt
    exact False.elim (r.left_ne_right (Fin.ext (by omega)))

/-- The gauge transforming one sign assignment into another is unique once its value at a single
grid state is specified. -/
theorem existsUnique_gauge_eq (S T : GridSignAssignment n) (x₀ : GridState n) (s₀ : ℤˣ) :
    ∃! f : GridState n → ℤˣ, f x₀ = s₀ ∧ S.gauge f = T := by
  obtain ⟨f₀, hf₀⟩ := exists_gauge_eq S T
  let c : ℤˣ := s₀ * f₀ x₀
  let f : GridState n → ℤˣ := fun x => c * f₀ x
  have hfx₀ : f x₀ = s₀ := by simp only [f, c, mul_assoc, Int.units_mul_self, mul_one]
  have hgauge : S.gauge f = T := by
    rw [← hf₀]
    exact GridSignAssignment.ext fun x y r hr => by
      simp only [gauge_sign, f]; rw [mul_mul_mul_comm, Int.units_mul_self, one_mul]
  refine ⟨f, ⟨hfx₀, hgauge⟩, fun g ⟨hgx₀, hggauge⟩ => ?_⟩
  rcases (S.gauge_eq_iff g f).mp (hggauge.trans hgauge.symm) with rfl | hneg
  · rfl
  · exact False.elim (units_ne_neg_self s₀ (by simpa [hgx₀, hfx₀] using congrFun hneg x₀))

end GridSignAssignment

/-- Any two sign assignments produce conjugate signed unblocked differentials via a diagonal sign
change on the generators of `GC⁻`. -/
theorem GridDiagram.exists_signEquiv_signedUnblockedDifferential {n : ℕ} (G : GridDiagram n)
    (S T : GridSignAssignment n) (R : Type*) [CommRing R] :
    ∃ f : GridState n → ℤˣ,
      G.signedUnblockedDifferential T R =
        (Finsupp.signEquiv (MvPolynomial (Fin n) R) f).toLinearMap ∘ₗ
          G.signedUnblockedDifferential S R ∘ₗ
            (Finsupp.signEquiv (MvPolynomial (Fin n) R) f).toLinearMap := by
  obtain ⟨f, rfl⟩ := GridSignAssignment.exists_gauge_eq S T
  exact ⟨f, G.signedUnblockedDifferential_gauge S R f⟩

end TauCeti
