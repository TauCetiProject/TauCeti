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
3. Strong induction on width extends agreement to all non-wrapping empty rectangles by recutting off
   a width-one strip from the left.
4. Strong induction on vertical height extends agreement to wrapping width-one rectangles from
   column `n - 1` to column `0`, using the horizontal annulus rule for height `1` and recutting off
   a height-one strip for height `≥ 2`.
5. Strong induction on cyclic width extends agreement from all width-one rectangles to every empty
   rectangle, giving `S = T.gauge g` and hence `S.gauge g = T`.

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

/-! ### Auxiliary unit arithmetic -/

private theorem units_eq_of_mul_eq_one {a b : ℤˣ} (h : a * b = 1) : b = a :=
  (eq_inv_of_mul_eq_one_right h).trans (Int.units_inv_eq_self a)

private theorem units_eq_neg_of_mul_eq_neg_one {a b : ℤˣ} (h : a * b = -1) : b = -a := by
  have h1 : a * (a * b) = a * (-1) := congrArg (a * ·) h
  simpa only [← mul_assoc, Int.units_mul_self, one_mul, mul_neg, mul_one] using h1

private theorem units_ne_neg_self (a : ℤˣ) : a ≠ -a := by
  rcases Int.units_eq_one_or a with rfl | rfl <;> decide

/-! ### The ratio of two sign assignments -/

/-- The pointwise product of two sign assignments on an empty rectangle, equal to `1` exactly where
the two sign assignments agree. -/
private def ratio (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) : ℤˣ :=
  S.sign r hr * T.sign r hr

private theorem ratio_eq_one_iff (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) :
    ratio S T r hr = 1 ↔ S.sign r hr = T.sign r hr := by
  constructor
  · intro h
    exact (units_eq_of_mul_eq_one h).symm
  · intro h
    rw [ratio, h, Int.units_mul_self]

private theorem ratio_congr (S T : GridSignAssignment n) {x y x' y' : GridState n}
    {r : GridRectangleBetween x y} {r' : GridRectangleBetween x' y'}
    (hr : r.IsEmpty) (hr' : r'.IsEmpty) (hx : x = x')
    (hl : r.left = r'.left) (hrr : r.right = r'.right) :
    ratio S T r hr = ratio S T r' hr' := by
  subst hx
  have hy : y = y' := by
    rw [r.target_eq_swapColumns, r'.target_eq_swapColumns, hl, hrr]
  subst hy
  have heq : r = r' := GridRectangleBetween.ext hl hrr
  subst heq
  rfl

private theorem ratio_square (S T : GridSignAssignment n) {x z : GridState n}
    (D E : GridRectangleDecomposition x z)
    (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty)
    (hE₁ : E.first.IsEmpty) (hE₂ : E.second.IsEmpty) (hne : E ≠ D)
    (hdomain : E.first.toGridRectangle.coveredSquares.val +
        E.second.toGridRectangle.coveredSquares.val =
      D.first.toGridRectangle.coveredSquares.val + D.second.toGridRectangle.coveredSquares.val) :
    ratio S T E.first hE₁ * ratio S T E.second hE₂ =
      ratio S T D.first hD₁ * ratio S T D.second hD₂ := by
  calc ratio S T E.first hE₁ * ratio S T E.second hE₂
      = (S.sign E.first hE₁ * S.sign E.second hE₂) *
          (T.sign E.first hE₁ * T.sign E.second hE₂) := by unfold ratio; ac_rfl
    _ = (-(S.sign D.first hD₁ * S.sign D.second hD₂)) *
          (-(T.sign D.first hD₁ * T.sign D.second hD₂)) := by
        rw [S.sign_mul_sign_eq_neg D E hD₁ hD₂ hE₁ hE₂ hne hdomain,
          T.sign_mul_sign_eq_neg D E hD₁ hD₂ hE₁ hE₂ hne hdomain]
    _ = ratio S T D.first hD₁ * ratio S T D.second hD₂ := by
        rw [neg_mul_neg]; unfold ratio; ac_rfl

private theorem ratio_commute (S T : GridSignAssignment n) {x z : GridState n}
    (D : GridRectangleDecomposition x z) (h : D.HasDisjointSides)
    (h₁ : D.first.IsEmpty) (h₂ : D.second.IsEmpty) :
    ratio S T (D.commute h).first (D.isEmpty_commute_first h h₁ h₂) *
        ratio S T (D.commute h).second (D.isEmpty_commute_second h h₁ h₂) =
      ratio S T D.first h₁ * ratio S T D.second h₂ := by
  refine ratio_square S T D (D.commute h) h₁ h₂
    (D.isEmpty_commute_first h h₁ h₂) (D.isEmpty_commute_second h h₁ h₂) (D.commute_ne h) ?_
  rw [D.commute_first_toGridRectangle h, D.commute_second_toGridRectangle h, add_comm]

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
    ratio S T s hs = ratio S T r hr := by
  refine units_eq_of_mul_eq_one ?_
  calc ratio S T r hr * ratio S T s hs
      = (S.sign r hr * S.sign s hs) * (T.sign r hr * T.sign s hs) := by unfold ratio; ac_rfl
    _ = (-1) * (-1) := by
        rw [S.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft,
          T.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft]
    _ = 1 := by simp

private theorem ratio_horizontal_annulus (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (s : GridRectangleBetween y x)
    (hr : r.IsEmpty) (hs : s.IsEmpty) (hleft : s.left = r.right) :
    ratio S T s hs = ratio S T r hr := by
  refine units_eq_of_mul_eq_one ?_
  calc ratio S T r hr * ratio S T s hs
      = (S.sign r hr * S.sign s hs) * (T.sign r hr * T.sign s hs) := by unfold ratio; ac_rfl
    _ = 1 * 1 := by
        rw [S.sign_mul_sign_eq_one_of_left_eq_right r s hr hs hleft,
          T.sign_mul_sign_eq_one_of_left_eq_right r s hr hs hleft]
    _ = 1 := one_mul 1

/-! ### Width-one rectangles and the Coxeter 1-cocycle -/

private def widthOneRect (x : GridState n) (a : Fin n) (hn : 1 < n) :
    GridRectangleBetween x (x.swapColumns a (finRotate n a)) :=
  GridRectangleBetween.ofSwapColumns x _ a (finRotate n a) (Grid.finRotate_ne_self hn a).symm rfl

private theorem widthOneRect_left (x : GridState n) (a : Fin n) (hn : 1 < n) :
    (widthOneRect x a hn).left = a :=
  GridRectangleBetween.ofSwapColumns_left x _ a (finRotate n a)
    (Grid.finRotate_ne_self hn a).symm rfl

private theorem widthOneRect_right (x : GridState n) (a : Fin n) (hn : 1 < n) :
    (widthOneRect x a hn).right = finRotate n a :=
  GridRectangleBetween.ofSwapColumns_right x _ a (finRotate n a)
    (Grid.finRotate_ne_self hn a).symm rfl

private theorem widthOneRect_bottom (x : GridState n) (a : Fin n) (hn : 1 < n) :
    (widthOneRect x a hn).bottom = x a :=
  GridRectangleBetween.ofSwapColumns_bottom x _ a (finRotate n a)
    (Grid.finRotate_ne_self hn a).symm rfl

private theorem widthOneRect_top (x : GridState n) (a : Fin n) (hn : 1 < n) :
    (widthOneRect x a hn).top = x (finRotate n a) :=
  GridRectangleBetween.ofSwapColumns_top x _ a (finRotate n a)
    (Grid.finRotate_ne_self hn a).symm rfl

private theorem widthOneRect_isEmpty (x : GridState n) (a : Fin n) (hn : 1 < n) :
    (widthOneRect x a hn).IsEmpty :=
  GridRectangleBetween.isEmpty_of_right_eq_finRotate _
    (by rw [widthOneRect_left, widthOneRect_right])

private theorem finRotate_strand (i : Fin (n - 1)) :
    finRotate n (BraidGroup.strand i) = BraidGroup.strandSucc i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.isLt; omega⟩
  apply Fin.ext
  rw [coe_finRotate]
  have hi := i.isLt
  have hne : BraidGroup.strand i ≠ Fin.last m := by
    intro h
    have hval := congrArg Fin.val h
    simp only [BraidGroup.val_strand, Fin.val_last] at hval
    omega
  simp [hne]

private theorem swapColumns_swapColumns_self (x : GridState n) (a b : Fin n) :
    (x.swapColumns a b).swapColumns a b = x := by
  ext c
  simp

private theorem swapColumns_comm_self (x : GridState n) (a b : Fin n) :
    (x.swapColumns a b).swapColumns b a = x := by
  ext c
  simp [Equiv.swap_comm]

private theorem mk_swapColumns_strand (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (⟨σ⟩ : GridState n).swapColumns (BraidGroup.strand i)
        (finRotate n (BraidGroup.strand i)) =
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
  let a := BraidGroup.strand i
  let r := widthOneRect ⟨σ⟩ a hn
  let y := (⟨σ⟩ : GridState n).swapColumns a (finRotate n a)
  let s : GridRectangleBetween y ⟨σ⟩ :=
    GridRectangleBetween.ofSwapColumns y ⟨σ⟩ a (finRotate n a) (Grid.finRotate_ne_self hn a).symm
      (swapColumns_swapColumns_self ⟨σ⟩ a (finRotate n a)).symm
  have hs : s.IsEmpty :=
    GridRectangleBetween.isEmpty_of_right_eq_finRotate s
      (by simp only [s, GridRectangleBetween.ofSwapColumns_left,
        GridRectangleBetween.ofSwapColumns_right])
  have hcongr : adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) i = ratio S T s hs :=
    ratio_congr S T (widthOneRect_isEmpty _ _ hn) hs (mk_swapColumns_strand σ i).symm
      (by simp only [widthOneRect_left, s, GridRectangleBetween.ofSwapColumns_left, a])
      (by simp only [widthOneRect_right, s, GridRectangleBetween.ofSwapColumns_right, a])
  have hleft : s.left = r.left := by
    simp only [s, r, GridRectangleBetween.ofSwapColumns_left, widthOneRect_left]
  rw [hcongr, ratio_vertical_annulus S T r s (widthOneRect_isEmpty _ _ hn) hs hleft,
    Int.units_inv_eq_self]
  rfl

private theorem adjCocycle_braid_two (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)}
    (hdist : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    adjCocycle S T hn σ i * adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) j =
      adjCocycle S T hn σ j * adjCocycle S T hn (σ * (permCoxeterSystem n).simple j) i := by
  let x : GridState n := ⟨σ⟩
  let a := BraidGroup.strand i
  let b := BraidGroup.strand j
  let r₁ := widthOneRect x a hn
  let y := x.swapColumns a (finRotate n a)
  let r₂ := widthOneRect y b hn
  let D : GridRectangleDecomposition x (y.swapColumns b (finRotate n b)) :=
    { middle := y, first := r₁, second := r₂ }
  have hdisj : D.HasDisjointSides := by
    rw [D.hasDisjointSides_iff]
    simp only [D, r₁, r₂, widthOneRect_left, widthOneRect_right, finRotate_strand, a, b,
      ne_eq, Fin.ext_iff, BraidGroup.val_strand, BraidGroup.val_strandSucc]
    omega
  have hcomm := ratio_commute S T D hdisj (widthOneRect_isEmpty _ _ hn)
    (widthOneRect_isEmpty _ _ hn)
  have hD₁ : ratio S T D.first (widthOneRect_isEmpty _ _ hn) = adjCocycle S T hn σ i := rfl
  have hD₂ : ratio S T D.second (widthOneRect_isEmpty _ _ hn) =
      adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) j :=
    ratio_congr S T _ _ (mk_swapColumns_strand σ i)
      (by simp only [D, r₂, widthOneRect_left, b])
      (by simp only [D, r₂, widthOneRect_right, b])
  have hE₁ : ratio S T (D.commute hdisj).first
      (D.isEmpty_commute_first hdisj (widthOneRect_isEmpty _ _ hn)
        (widthOneRect_isEmpty _ _ hn)) = adjCocycle S T hn σ j :=
    ratio_congr S T _ _ rfl
      (by simp only [D.commute_first_left hdisj, D, r₂, widthOneRect_left, b])
      (by simp only [D.commute_first_right hdisj, D, r₂, widthOneRect_right, b])
  have hE₂ : ratio S T (D.commute hdisj).second
      (D.isEmpty_commute_second hdisj (widthOneRect_isEmpty _ _ hn)
        (widthOneRect_isEmpty _ _ hn)) =
      adjCocycle S T hn (σ * (permCoxeterSystem n).simple j) i :=
    ratio_congr S T _ _
      (by rw [D.commute_middle hdisj]; simp only [D, r₂, widthOneRect_left, widthOneRect_right, b]
          exact mk_swapColumns_strand σ j)
      (by simp only [D.commute_second_left hdisj, D, r₁, widthOneRect_left, a])
      (by simp only [D.commute_second_right hdisj, D, r₁, widthOneRect_right, a])
  rw [hE₁, hE₂, hD₁, hD₂] at hcomm
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
  have hbj : BraidGroup.strand j = b := BraidGroup.strand_eq_strandSucc_of_succ hij
  have hab : finRotate n a = b := finRotate_strand i
  have hbc : finRotate n b = c := by rw [← hbj]; exact finRotate_strand j
  have hac : a ≠ c := BraidGroup.strand_ne_strandSucc_of_succ hij
  have hbac : b ∈ Grid.cIoo a c := by
    rw [Grid.mem_cIoo]
    refine ⟨hac, ?_⟩
    have ha : a.val = i.val := BraidGroup.val_strand i
    have hb : b.val = i.val + 1 := BraidGroup.val_strandSucc i
    have hc : c.val = j.val + 1 := BraidGroup.val_strandSucc j
    rw [ite_eq_left (by omega)]
    omega
  -- First recut: the length-two path `(a, b)` then `(b, c)`.
  let y₁ := x.swapColumns a (finRotate n a)
  let z₁ := y₁.swapColumns (BraidGroup.strand j) (finRotate n (BraidGroup.strand j))
  let D₁ : GridRectangleDecomposition x z₁ :=
    { middle := y₁
      first := widthOneRect x a hn
      second := widthOneRect y₁ (BraidGroup.strand j) hn }
  have hD₁_common : D₁.first.right = D₁.second.left := by
    simp only [D₁, widthOneRect_right, widthOneRect_left, hab, hbj]
  have hD₁_other : D₁.first.left ≠ D₁.second.right := by
    simpa only [D₁, widthOneRect_left, widthOneRect_right, hbj, hbc] using hac
  have hone₁ := D₁.hasOneCommonSide_of_right_eq_left hD₁_common hD₁_other
  have hD₁f : D₁.first.IsEmpty := widthOneRect_isEmpty _ _ hn
  have hD₁s : D₁.second.IsEmpty := widthOneRect_isEmpty _ _ hn
  let E₁ := D₁.recut hone₁ hD₁f hD₁s
  have hrec₁ := D₁.isRecut_recut hone₁ hD₁f hD₁s
  have hD₁_bot : D₁.first.bottom = σ a := widthOneRect_bottom x a hn
  have hD₁_top : D₁.first.top = σ b := by
    rw [show D₁.first.top = x (finRotate n a) from widthOneRect_top x a hn, hab]
  have hD₁_stop : D₁.second.top = σ c := by
    rw [show D₁.second.top = y₁ (finRotate n (BraidGroup.strand j)) from widthOneRect_top _ _ hn,
      hbj, hbc]
    change x (Equiv.swap a (finRotate n a) c) = σ c
    rw [hab, Equiv.swap_apply_of_ne_of_ne hac.symm
      (by rw [← hbc]; exact Grid.finRotate_ne_self hn b)]
  have hgeom₁ := D₁.recut_geometry_of_right_eq_left hD₁_common hone₁ hD₁f hD₁s
  have hE₁_sides :
      E₁.first.left = b ∧ E₁.first.right = c ∧ E₁.second.left = a ∧ E₁.second.right = c := by
    rcases hgeom₁ with ⟨-, hfl, hfr, hsl, hsr, -⟩ | ⟨hbad, -⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [E₁, D₁, widthOneRect_right, hab] using hfl
      · simpa only [E₁, D₁, widthOneRect_right, hbj, hbc] using hfr
      · simpa only [E₁, D₁, widthOneRect_left] using hsl
      · simpa only [E₁, D₁, widthOneRect_right, hbj, hbc] using hsr
    · rw [hD₁_bot, hD₁_top, hD₁_stop] at hbad
      exact False.elim (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap (σ a) (σ b)) hbad
        (Grid.mem_cIoo_cyclic_left hrow))
  obtain ⟨hE₁fl, hE₁fr, hE₁sl, hE₁sr⟩ := hE₁_sides
  have hy₁ : y₁ = ⟨σ * (permCoxeterSystem n).simple i⟩ := mk_swapColumns_strand σ i
  have hz₁ : z₁ = ⟨σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j⟩ := by
    calc z₁ = (⟨σ * (permCoxeterSystem n).simple i⟩ : GridState n).swapColumns
            (BraidGroup.strand j) (finRotate n (BraidGroup.strand j)) := by rw [← hy₁]
      _ = ⟨σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j⟩ :=
          mk_swapColumns_strand _ j
  have hE₁mid : E₁.middle = ⟨σ * (permCoxeterSystem n).simple j⟩ := by
    rw [E₁.first.target_eq_swapColumns, hE₁fl, hE₁fr, ← hbc, ← hbj]
    exact mk_swapColumns_strand σ j
  have hstep₁ : adjCocycle S T hn σ j * ratio S T E₁.second hrec₁.isEmpty_second =
      adjCocycle S T hn σ i * adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) j := by
    have hr₁ := ratio_recut S T D₁ hone₁ hD₁f hD₁s
    have h1 : ratio S T E₁.first hrec₁.isEmpty_first = adjCocycle S T hn σ j :=
      ratio_congr S T _ _ rfl
        (by rw [hE₁fl, widthOneRect_left, hbj])
        (by rw [hE₁fr, widthOneRect_right, hbj, hbc])
    have h2 : ratio S T D₁.first hD₁f = adjCocycle S T hn σ i := rfl
    have h3 : ratio S T D₁.second hD₁s =
        adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) j :=
      ratio_congr S T _ _ hy₁
        (by simp only [D₁, widthOneRect_left])
        (by simp only [D₁, widthOneRect_right])
    simpa only [E₁, h1, h2, h3] using hr₁
  -- Second recut: `E₁.second` (sides `(a, c)`) followed by `(a, b)` at `z₁`.
  let D₂ : GridRectangleDecomposition E₁.middle (z₁.swapColumns a (finRotate n a)) :=
    { middle := z₁
      first := E₁.second
      second := widthOneRect z₁ a hn }
  have hD₂_common : D₂.first.left = D₂.second.left :=
    hE₁sl.trans (widthOneRect_left z₁ a hn).symm
  have hD₂_col : D₂.second.right ∈ Grid.cIoo D₂.first.left D₂.first.right := by
    simpa only [D₂, widthOneRect_right, hE₁sl, hE₁sr, hab] using hbac
  have hone₂ := D₂.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hD₂_common hD₂_col
  have hD₂f : D₂.first.IsEmpty := hrec₁.isEmpty_second
  have hD₂s : D₂.second.IsEmpty := widthOneRect_isEmpty _ _ hn
  let E₂ := D₂.recut hone₂ hD₂f hD₂s
  have hrec₂ := D₂.isRecut_recut hone₂ hD₂f hD₂s
  obtain ⟨hE₂fl, hE₂fr, hE₂sl, hE₂sr⟩ :=
    D₂.recut_sides_of_left_eq_left_of_mem_cIoo hD₂_common hD₂_col hD₂f hD₂s
  have hE₂mid :
      E₂.middle = ⟨σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i⟩ := by
    rw [E₂.first.target_eq_swapColumns, hE₂fl, hE₂fr, hE₁sl,
      show D₂.second.right = finRotate n a from widthOneRect_right z₁ a hn, hE₁mid]
    exact mk_swapColumns_strand _ i
  have hstep₂ :
      adjCocycle S T hn (σ * (permCoxeterSystem n).simple j) i *
          adjCocycle S T hn
            (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j =
        ratio S T E₁.second hrec₁.isEmpty_second *
          adjCocycle S T hn
            (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i := by
    have hr₂ := ratio_recut S T D₂ hone₂ hD₂f hD₂s
    have h1 : ratio S T E₂.first hrec₂.isEmpty_first =
        adjCocycle S T hn (σ * (permCoxeterSystem n).simple j) i :=
      ratio_congr S T _ _ hE₁mid
        (by rw [hE₂fl, hE₁sl, widthOneRect_left])
        (by rw [hE₂fr, show D₂.second.right = finRotate n a from widthOneRect_right z₁ a hn,
          widthOneRect_right])
    have h2 : ratio S T E₂.second hrec₂.isEmpty_second =
        adjCocycle S T hn
          (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j :=
      ratio_congr S T _ _ hE₂mid
        (by rw [hE₂sl, show D₂.second.right = finRotate n a from widthOneRect_right z₁ a hn,
          hab, widthOneRect_left, hbj])
        (by rw [hE₂sr, hE₁sr, widthOneRect_right, hbj, hbc])
    have h3 : ratio S T D₂.second hD₂s =
        adjCocycle S T hn
          (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i :=
      ratio_congr S T _ _ hz₁
        (by simp only [D₂, widthOneRect_left, a])
        (by simp only [D₂, widthOneRect_right, a])
    simpa only [E₂, h1, h2, h3] using hr₂
  calc adjCocycle S T hn σ i *
        adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) j *
        adjCocycle S T hn
          (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i
      = (adjCocycle S T hn σ j * ratio S T E₁.second hrec₁.isEmpty_second) *
          adjCocycle S T hn
            (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i := by
        rw [← hstep₁]
    _ = adjCocycle S T hn σ j *
          (ratio S T E₁.second hrec₁.isEmpty_second *
            adjCocycle S T hn
              (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i) :=
        mul_assoc _ _ _
    _ = adjCocycle S T hn σ j *
          (adjCocycle S T hn (σ * (permCoxeterSystem n).simple j) i *
            adjCocycle S T hn
              (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j) := by
        rw [← hstep₂]
    _ = adjCocycle S T hn σ j *
          adjCocycle S T hn (σ * (permCoxeterSystem n).simple j) i *
          adjCocycle S T hn
            (σ * (permCoxeterSystem n).simple j * (permCoxeterSystem n).simple i) j :=
        (mul_assoc _ _ _).symm

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
  · -- Reverse the hexagon: apply the `hrow` branch at `τ = σ * s_i * s_j * s_i`.
    let si := (permCoxeterSystem n).simple i
    let sj := (permCoxeterSystem n).simple j
    let τ : Equiv.Perm (Fin n) := σ * si * sj * si
    have hbraid : si * sj * si = sj * si * sj := by
      simp only [si, sj, permCoxeterSystem_simple]
      exact BraidGroup.transposition_braid (Or.inl hij)
    have hτ_eq : τ = σ * sj * si * sj := by
      simp only [τ, mul_assoc]
      rw [← mul_assoc si sj si, hbraid, mul_assoc]
    have hbj : BraidGroup.strand j = b := BraidGroup.strand_eq_strandSucc_of_succ hij
    have hab : a ≠ b := BraidGroup.strand_ne_strandSucc i
    have hbc : b ≠ c := hbj ▸ BraidGroup.strand_ne_strandSucc j
    have hac : a ≠ c := BraidGroup.strand_ne_strandSucc_of_succ hij
    have hsi : si = Equiv.swap a b := by
      simp only [si, permCoxeterSystem_simple, BraidGroup.transposition_eq_swap, a, b]
    have hsj : sj = Equiv.swap b c := by
      simp only [sj, permCoxeterSystem_simple, BraidGroup.transposition_eq_swap, hbj, c]
    have hτa : τ a = σ c := by
      simp only [τ, Equiv.Perm.mul_apply, hsi, hsj, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
    have hτb : τ b = σ b := by
      simp only [τ, Equiv.Perm.mul_apply, hsi, hsj, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
    have hτc : τ c = σ a := by
      simp only [τ, Equiv.Perm.mul_apply, hsi, hsj,
        Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm, Equiv.swap_apply_right]
    have hrow' : τ b ∈ Grid.cIoo (τ a) (τ c) := by
      rw [hτa, hτb, hτc]
      exact Grid.mem_cIoo_swap_of_notMem (σ.injective.ne hac)
        (σ.injective.ne hab.symm) (σ.injective.ne hbc) hrow
    have hmain := adjCocycle_braid_three_of_mem_cIoo S T hn τ hij hrow'
    change adjCocycle S T hn τ i * adjCocycle S T hn (τ * si) j *
        adjCocycle S T hn (τ * si * sj) i =
      adjCocycle S T hn τ j * adjCocycle S T hn (τ * sj) i *
        adjCocycle S T hn (τ * sj * si) j at hmain
    have hstep : ∀ w k, adjCocycle S T hn (w * (permCoxeterSystem n).simple k) k =
        adjCocycle S T hn w k := fun w k => by
      rw [adjCocycle_inv, Int.units_inv_eq_self]
    have hL1 : adjCocycle S T hn τ i = adjCocycle S T hn (σ * si * sj) i := hstep _ i
    have hL2 : adjCocycle S T hn (τ * si) j = adjCocycle S T hn (σ * si) j := by
      have : τ * si = σ * si * sj := by
        simp [τ, si, permCoxeterSystem_simple, BraidGroup.mul_transposition_mul_self]
      rw [this, hstep]
    have hL3 : adjCocycle S T hn (τ * si * sj) i = adjCocycle S T hn σ i := by
      have : τ * si * sj = σ * si := by
        simp [τ, si, sj, permCoxeterSystem_simple, BraidGroup.mul_transposition_mul_self]
      rw [this, hstep]
    have hR1 : adjCocycle S T hn τ j = adjCocycle S T hn (σ * sj * si) j := by
      rw [hτ_eq, hstep]
    have hR2 : adjCocycle S T hn (τ * sj) i = adjCocycle S T hn (σ * sj) i := by
      have : τ * sj = σ * sj * si := by
        rw [hτ_eq]
        simp [sj, permCoxeterSystem_simple, BraidGroup.mul_transposition_mul_self]
      rw [this, hstep]
    have hR3 : adjCocycle S T hn (τ * sj * si) j = adjCocycle S T hn σ j := by
      have : τ * sj * si = σ * sj := by
        rw [hτ_eq]
        simp [si, sj, permCoxeterSystem_simple, BraidGroup.mul_transposition_mul_self]
      rw [this, hstep]
    rw [hL1, hL2, hL3, hR1, hR2, hR3] at hmain
    calc adjCocycle S T hn σ i * adjCocycle S T hn (σ * si) j *
          adjCocycle S T hn (σ * si * sj) i
        = adjCocycle S T hn (σ * si * sj) i * adjCocycle S T hn (σ * si) j *
          adjCocycle S T hn σ i := by ac_rfl
      _ = adjCocycle S T hn (σ * sj * si) j * adjCocycle S T hn (σ * sj) i *
          adjCocycle S T hn σ j := hmain
      _ = adjCocycle S T hn σ j * adjCocycle S T hn (σ * sj) i *
          adjCocycle S T hn (σ * sj * si) j := by ac_rfl

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
  · have hMij : CoxeterMatrix.A (n - 1) i j = 3 := coxeterMatrixA_eq_three hadj
    have hMji : CoxeterMatrix.A (n - 1) j i = 3 := coxeterMatrixA_eq_three hadj.symm
    simp only [CoxeterSystem.braidWord, hMij, hMji, CoxeterSystem.alternatingWord,
      List.concat_eq_append, List.nil_append, List.cons_append,
      CoxeterSystem.wordCocycleProd_cons, CoxeterSystem.wordCocycleProd_nil, mul_one, ← mul_assoc]
    rcases hadj with h | h
    · exact (adjCocycle_braid_three_of_succ S T hn σ h).symm
    · exact adjCocycle_braid_three_of_succ S T hn σ h
  · have hdist : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i := by omega
    have hMij : CoxeterMatrix.A (n - 1) i j = 2 := coxeterMatrixA_eq_two hdist
    have hMji : CoxeterMatrix.A (n - 1) j i = 2 := coxeterMatrixA_eq_two hdist.symm
    simp only [CoxeterSystem.braidWord, hMij, hMji, CoxeterSystem.alternatingWord,
      List.concat_eq_append, List.nil_append, List.cons_append,
      CoxeterSystem.wordCocycleProd_cons, CoxeterSystem.wordCocycleProd_nil, mul_one]
    exact adjCocycle_braid_two S T hn σ hdist

/-! ### Extending agreement from adjacent width-one rectangles to all empty rectangles -/

/-- Agreement on adjacent width-one rectangles extends to all non-wrapping empty rectangles by
induction on width. -/
private theorem ratio_eq_one_of_left_lt_right (S T : GridSignAssignment n) (hn : 1 < n)
    (hadj : ∀ (x : GridState n) (i : Fin (n - 1)),
      ratio S T (widthOneRect x (BraidGroup.strand i) hn) (widthOneRect_isEmpty x _ hn) = 1) :
    ∀ (w : ℕ) {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      r.left.val < r.right.val → r.right.val - r.left.val = w → ratio S T r hr = 1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro x y r hr hlt hw
    have ha_lt : r.left.val < n - 1 := by have := r.right.isLt; omega
    let i : Fin (n - 1) := ⟨r.left.val, ha_lt⟩
    have hi : BraidGroup.strand i = r.left := Fin.ext (BraidGroup.val_strand i)
    have hrot_val : (finRotate n r.left).val = r.left.val + 1 := by
      rw [← hi, finRotate_strand, BraidGroup.val_strandSucc, BraidGroup.val_strand]
    by_cases hw1 : w = 1
    · have hright : r.right = finRotate n r.left := Fin.ext (by omega)
      have hcongr : ratio S T r hr =
          ratio S T (widthOneRect x (BraidGroup.strand i) hn) (widthOneRect_isEmpty x _ hn) :=
        ratio_congr S T hr (widthOneRect_isEmpty x _ hn) rfl
          (by rw [widthOneRect_left, hi])
          (by rw [hright, widthOneRect_right, hi])
      rw [hcongr, hadj]
    · let a := r.left
      let b := finRotate n a
      have hba : b ∈ Grid.cIoo a r.right := by
        rw [Grid.mem_cIoo]
        refine ⟨r.left_ne_right, ?_⟩
        rw [ite_eq_left (by omega)]
        change r.left.val < (finRotate n r.left).val ∧ (finRotate n r.left).val < r.right.val
        omega
      let D : GridRectangleDecomposition x (y.swapColumns a b) :=
        { middle := y, first := r, second := widthOneRect y a hn }
      have hD_common : D.first.left = D.second.left := (widthOneRect_left y a hn).symm
      have hD_col : D.second.right ∈ Grid.cIoo D.first.left D.first.right := by
        simpa only [D, widthOneRect_right] using hba
      have hone := D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hD_common hD_col
      have hDs : D.second.IsEmpty := widthOneRect_isEmpty y a hn
      let E := D.recut hone hr hDs
      have hrec := D.isRecut_recut hone hr hDs
      obtain ⟨hEfl, hEfr, hEsl, hEsr⟩ :=
        D.recut_sides_of_left_eq_left_of_mem_cIoo hD_common hD_col hr hDs
      have hEf : ratio S T E.first hrec.isEmpty_first = 1 := by
        have hcongr := ratio_congr S T hrec.isEmpty_first
          (widthOneRect_isEmpty x (BraidGroup.strand i) hn) rfl
          (by rw [hEfl, widthOneRect_left, hi])
          (by rw [hEfr, show D.second.right = b from widthOneRect_right y a hn,
            widthOneRect_right, hi])
        rw [hcongr, hadj]
      have hEs : ratio S T E.second hrec.isEmpty_second = 1 := by
        refine ih (w - 1) (by omega) E.second hrec.isEmpty_second ?_ ?_
        · rw [hEsl, hEsr, show D.second.right = b from widthOneRect_right y a hn]
          change (finRotate n r.left).val < r.right.val
          omega
        · rw [hEsl, hEsr, show D.second.right = b from widthOneRect_right y a hn]
          change r.right.val - (finRotate n r.left).val = w - 1
          omega
      have hD2 : ratio S T D.second hDs = 1 := by
        have hcongr := ratio_congr S T hDs
          (widthOneRect_isEmpty y (BraidGroup.strand i) hn) rfl
          (by rw [show D.second.left = a from widthOneRect_left y a hn, widthOneRect_left, hi])
          (by rw [show D.second.right = b from widthOneRect_right y a hn, widthOneRect_right, hi])
        rw [hcongr, hadj]
      have hrecut := ratio_recut S T D hone hr hDs
      change ratio S T E.first hrec.isEmpty_first * ratio S T E.second hrec.isEmpty_second =
        ratio S T r hr * ratio S T D.second hDs at hrecut
      rw [hEf, hEs, hD2, mul_one, mul_one] at hrecut
      exact hrecut.symm

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
    apply Fin.ext
    rw [coe_finRotate]
    have hlast : lastCol = Fin.last m := Fin.ext (by simp [lastCol])
    simp [hlast, zeroCol]
  have hlast_ne_zero : lastCol ≠ zeroCol := by
    rw [← hrot_last]
    exact (Grid.finRotate_ne_self hn lastCol).symm
  intro h
  induction h using Nat.strong_induction_on with
  | ind h ih =>
    intro x hh
    change (Grid.cIco (x lastCol) (x zeroCol)).card = h at hh
    have hne_rows : x lastCol ≠ x zeroCol := x.toPerm.injective.ne hlast_ne_zero
    by_cases hh1 : h = 1
    · -- Height `1`: the horizontal annulus partner from `0` to `n - 1` is empty and non-wrapping.
      have hcard_oo : (Grid.cIoo (x lastCol) (x zeroCol)).card = 0 := by
        have hc := Grid.card_cIco_of_ne hne_rows
        omega
      have hoo_empty : Grid.cIoo (x lastCol) (x zeroCol) = ∅ := Finset.card_eq_zero.mp hcard_oo
      let r := widthOneRect x lastCol hn
      let y := x.swapColumns lastCol (finRotate n lastCol)
      let s : GridRectangleBetween y x :=
        GridRectangleBetween.ofSwapColumns y x zeroCol lastCol hlast_ne_zero.symm
          (by rw [← hrot_last]; exact (swapColumns_comm_self x lastCol _).symm)
      have hs_empty : s.IsEmpty := by
        rw [s.isEmpty_iff_forall_notMem_cIoo]
        intro c _
        have hbot : s.bottom = x lastCol := by
          rw [show s.bottom = y zeroCol from GridRectangleBetween.ofSwapColumns_bottom ..,
            ← hrot_last]
          simp [y]
        have htop : s.top = x zeroCol := by
          rw [show s.top = y lastCol from GridRectangleBetween.ofSwapColumns_top .., ← hrot_last]
          simp [y]
        rw [hbot, htop, hoo_empty]
        exact Finset.notMem_empty _
      have hs_ratio : ratio S T s hs_empty = 1 :=
        hnonwrap s hs_empty (by
          rw [show s.left = zeroCol from GridRectangleBetween.ofSwapColumns_left ..,
            show s.right = lastCol from GridRectangleBetween.ofSwapColumns_right ..]
          simp only [zeroCol, lastCol]
          omega)
      have hann := ratio_horizontal_annulus S T r s (widthOneRect_isEmpty x lastCol hn) hs_empty
        (by rw [show s.left = zeroCol from GridRectangleBetween.ofSwapColumns_left ..,
          widthOneRect_right, hrot_last])
      rw [← hann, hs_ratio]
    · -- Height `≥ 2`: peel off the row immediately above `x lastCol`.
      have hge2 : 2 ≤ h := by
        have hc := Grid.card_cIco_of_ne hne_rows
        omega
      let r_mid : Fin n := finRotate n (x lastCol)
      have hr_mid_ne_bot : r_mid ≠ x lastCol := Grid.finRotate_ne_self hn (x lastCol)
      have hr_mid_ne_top : r_mid ≠ x zeroCol := by
        intro heq
        have hsing : Grid.cIco (x lastCol) (x zeroCol) = {x lastCol} :=
          Grid.cIco_eq_singleton_iff.mpr ⟨rfl, heq.symm, hne_rows⟩
        rw [hsing, Finset.card_singleton] at hh
        omega
      have hr_mid_mem : r_mid ∈ Grid.cIoo (x lastCol) (x zeroCol) :=
        Grid.mem_cIoo_cyclic_right
          (Grid.mem_cIoo_finRotate_left_iff.mpr ⟨hne_rows.symm, hr_mid_ne_top.symm⟩)
      let c : Fin n := x.toPerm.symm r_mid
      have hxc : x c = r_mid := x.toPerm.apply_symm_apply r_mid
      have hc_ne_last : c ≠ lastCol := fun h => hr_mid_ne_bot (hxc ▸ congrArg x h)
      have hc_ne_zero : c ≠ zeroCol := fun h => hr_mid_ne_top (hxc ▸ congrArg x h)
      have hc_pos : 0 < c.val := by
        have hne : c.val ≠ 0 := fun h => hc_ne_zero (Fin.ext h)
        omega
      have hc_lt : c.val < n - 1 := by
        have hne : c.val ≠ n - 1 := fun h => hc_ne_last (Fin.ext h)
        have := c.isLt
        omega
      have hzero_mem : zeroCol ∈ Grid.cIoo lastCol c := by
        rw [Grid.mem_cIoo]
        refine ⟨hc_ne_last.symm, ?_⟩
        rw [ite_eq_right (by simp [lastCol]; omega)]
        exact Or.inr hc_pos
      let w := x.swapColumns lastCol c
      let t : GridRectangleBetween x w :=
        GridRectangleBetween.ofSwapColumns x w lastCol c hc_ne_last.symm rfl
      have ht_empty : t.IsEmpty := by
        rw [t.isEmpty_iff_forall_notMem_cIoo]
        intro col _
        have hbot : t.bottom = x lastCol := GridRectangleBetween.ofSwapColumns_bottom ..
        have htop : t.top = finRotate n (x lastCol) :=
          (GridRectangleBetween.ofSwapColumns_top ..).trans hxc
        rw [hbot, htop, Grid.cIoo_finRotate_eq_empty]
        exact Finset.notMem_empty _
      let t_ann : GridRectangleBetween w x :=
        GridRectangleBetween.ofSwapColumns w x c lastCol hc_ne_last
          (swapColumns_comm_self x lastCol c).symm
      have ht_ann_empty : t_ann.IsEmpty := by
        rw [t_ann.isEmpty_iff_forall_notMem_cIoo]
        intro col _
        have hbot : t_ann.bottom = x lastCol := by
          rw [show t_ann.bottom = w c from GridRectangleBetween.ofSwapColumns_bottom ..]
          simp only [w, GridState.swapColumns_apply, Equiv.swap_apply_right]
        have htop : t_ann.top = finRotate n (x lastCol) := by
          rw [show t_ann.top = w lastCol from GridRectangleBetween.ofSwapColumns_top ..]
          simp only [w, GridState.swapColumns_apply, Equiv.swap_apply_left, hxc, r_mid]
        rw [hbot, htop, Grid.cIoo_finRotate_eq_empty]
        exact Finset.notMem_empty _
      have ht_ratio : ratio S T t ht_empty = 1 := by
        have ht_ann_ratio : ratio S T t_ann ht_ann_empty = 1 :=
          hnonwrap t_ann ht_ann_empty (by
            rw [show t_ann.left = c from GridRectangleBetween.ofSwapColumns_left ..,
              show t_ann.right = lastCol from GridRectangleBetween.ofSwapColumns_right ..]
            simp only [lastCol]
            exact hc_lt)
        have hann := ratio_horizontal_annulus S T t t_ann ht_empty ht_ann_empty
          (by rw [show t_ann.left = c from GridRectangleBetween.ofSwapColumns_left ..,
            show t.right = c from GridRectangleBetween.ofSwapColumns_right ..])
        rw [← hann, ht_ann_ratio]
      -- Recut `t` followed by the height-reduced width-one rectangle at `w`.
      let D : GridRectangleDecomposition x (w.swapColumns lastCol (finRotate n lastCol)) :=
        { middle := w, first := t, second := widthOneRect w lastCol hn }
      have hD_common : D.first.left = D.second.left :=
        (GridRectangleBetween.ofSwapColumns_left ..).trans (widthOneRect_left w lastCol hn).symm
      have hD_col : D.second.right ∈ Grid.cIoo D.first.left D.first.right := by
        rw [show D.first.left = lastCol from GridRectangleBetween.ofSwapColumns_left ..,
          show D.first.right = c from GridRectangleBetween.ofSwapColumns_right ..,
          show D.second.right = finRotate n lastCol from widthOneRect_right w lastCol hn,
          hrot_last]
        exact hzero_mem
      have hone := D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hD_common hD_col
      have hDs : D.second.IsEmpty := widthOneRect_isEmpty w lastCol hn
      let E := D.recut hone ht_empty hDs
      have hrec := D.isRecut_recut hone ht_empty hDs
      obtain ⟨hEfl, hEfr, hEsl, hEsr⟩ :=
        D.recut_sides_of_left_eq_left_of_mem_cIoo hD_common hD_col ht_empty hDs
      have hD2_height : (Grid.cIco (w lastCol) (w zeroCol)).card = h - 1 := by
        have hw_last : w lastCol = r_mid := by simp [w, hxc]
        have hw_zero : w zeroCol = x zeroCol := by
          simp [w, Equiv.swap_apply_of_ne_of_ne hlast_ne_zero.symm hc_ne_zero.symm]
        rw [hw_last, hw_zero]
        have hunion := congrArg Finset.card (Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hr_mid_mem)
        rw [Finset.card_union_of_disjoint (Grid.disjoint_cIco_cIco_of_mem_cIoo hr_mid_mem), hh]
          at hunion
        have hsing : Grid.cIco (x lastCol) r_mid = {x lastCol} :=
          Grid.cIco_eq_singleton_iff.mpr ⟨rfl, rfl, hr_mid_ne_bot.symm⟩
        rw [hsing, Finset.card_singleton] at hunion
        omega
      have hD2_ratio : ratio S T D.second hDs = 1 := ih (h - 1) (by omega) w hD2_height
      have hEs_ratio : ratio S T E.second hrec.isEmpty_second = 1 :=
        hnonwrap E.second hrec.isEmpty_second (by
          rw [hEsl, hEsr,
            show D.second.right = finRotate n lastCol from widthOneRect_right w lastCol hn,
            show D.first.right = c from GridRectangleBetween.ofSwapColumns_right .., hrot_last]
          exact hc_pos)
      have hEf_congr : ratio S T E.first hrec.isEmpty_first =
          ratio S T (widthOneRect x lastCol hn) (widthOneRect_isEmpty x lastCol hn) :=
        ratio_congr S T _ _ rfl
          (by rw [hEfl, show D.first.left = lastCol from GridRectangleBetween.ofSwapColumns_left ..,
            widthOneRect_left])
          (by rw [hEfr,
            show D.second.right = finRotate n lastCol from widthOneRect_right w lastCol hn,
            widthOneRect_right])
      have hrecut := ratio_recut S T D hone ht_empty hDs
      change ratio S T E.first hrec.isEmpty_first * ratio S T E.second hrec.isEmpty_second =
        ratio S T t ht_empty * ratio S T D.second hDs at hrecut
      rw [hEf_congr, hEs_ratio, ht_ratio, hD2_ratio, mul_one, mul_one] at hrecut
      exact hrecut

/-- Agreement on all width-one rectangles extends to every empty rectangle by induction on cyclic
width. -/
private theorem ratio_eq_one_of_widthOne (S T : GridSignAssignment n) (hn : 1 < n)
    (h1 : ∀ (x : GridState n) (a : Fin n),
      ratio S T (widthOneRect x a hn) (widthOneRect_isEmpty x a hn) = 1) :
    ∀ (w : ℕ) {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      (Grid.cIco r.left r.right).card = w → ratio S T r hr = 1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro x y r hr hw
    by_cases hw1 : w = 1
    · have hcard_oo : (Grid.cIoo r.left r.right).card = 0 := by
        have hc := Grid.card_cIco_of_ne r.left_ne_right
        omega
      have hsing : Grid.cIco r.left r.right = {r.left} := by
        simp [Grid.cIco_of_ne r.left_ne_right, Finset.card_eq_zero.mp hcard_oo]
      have hright : r.right = finRotate n r.left := (Grid.cIco_eq_singleton_iff.mp hsing).2.1
      have hcongr := ratio_congr S T hr (widthOneRect_isEmpty x r.left hn) rfl
        (widthOneRect_left x r.left hn).symm
        (hright.trans (widthOneRect_right x r.left hn).symm)
      rw [hcongr, h1]
    · have hge2 : 2 ≤ w := by
        have hc := Grid.card_cIco_of_ne r.left_ne_right
        omega
      let a := r.left
      let b := finRotate n a
      have hba_ne : b ≠ a := Grid.finRotate_ne_self hn a
      have hbr_ne : b ≠ r.right := by
        intro heq
        have hsing : Grid.cIco a r.right = {a} :=
          Grid.cIco_eq_singleton_iff.mpr ⟨rfl, heq.symm, r.left_ne_right⟩
        rw [hsing, Finset.card_singleton] at hw
        omega
      have hb_mem : b ∈ Grid.cIoo a r.right :=
        Grid.mem_cIoo_cyclic_right
          (Grid.mem_cIoo_finRotate_left_iff.mpr ⟨r.left_ne_right.symm, hbr_ne.symm⟩)
      let D : GridRectangleDecomposition x (y.swapColumns a b) :=
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
      have hcard_es : (Grid.cIco E.second.left E.second.right).card = w - 1 := by
        rw [hEsl, hEsr, show D.second.right = b from widthOneRect_right y a hn]
        change (Grid.cIco b r.right).card = w - 1
        have hunion := congrArg Finset.card (Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hb_mem)
        rw [Finset.card_union_of_disjoint (Grid.disjoint_cIco_cIco_of_mem_cIoo hb_mem), hw]
          at hunion
        have hsing : Grid.cIco a b = {a} :=
          Grid.cIco_eq_singleton_iff.mpr ⟨rfl, rfl, hba_ne.symm⟩
        rw [hsing, Finset.card_singleton] at hunion
        omega
      have hEf : ratio S T E.first hrec.isEmpty_first = 1 := by
        have hcongr := ratio_congr S T hrec.isEmpty_first (widthOneRect_isEmpty x a hn) rfl
          (hEfl.trans (widthOneRect_left x a hn).symm)
          (by rw [hEfr, show D.second.right = b from widthOneRect_right y a hn, widthOneRect_right])
        rw [hcongr, h1]
      have hEs : ratio S T E.second hrec.isEmpty_second = 1 :=
        ih (w - 1) (by omega) E.second hrec.isEmpty_second hcard_es
      have hD2 : ratio S T D.second hDs = 1 := h1 y a
      have hrecut := ratio_recut S T D hone hr hDs
      change ratio S T E.first hrec.isEmpty_first * ratio S T E.second hrec.isEmpty_second =
        ratio S T r hr * ratio S T D.second hDs at hrecut
      rw [hEf, hEs, hD2, mul_one, mul_one] at hrecut
      exact hrecut.symm

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
            h ⟨σ * (permCoxeterSystem n).simple i⟩ = h ⟨σ⟩ := by
          intro σ i
          let r := widthOneRect ⟨σ⟩ (BraidGroup.strand i) hn
          have hr : r.IsEmpty := widthOneRect_isEmpty _ _ hn
          have hsign := congrArg (fun A : GridSignAssignment n => A.sign r hr) heq
          simp only [gauge_sign] at hsign
          have hfg : f ⟨σ⟩ * f ((⟨σ⟩ : GridState n).swapColumns (BraidGroup.strand i)
              (finRotate n (BraidGroup.strand i))) =
            g ⟨σ⟩ * g ((⟨σ⟩ : GridState n).swapColumns (BraidGroup.strand i)
              (finRotate n (BraidGroup.strand i))) := mul_right_cancel hsign
          rw [mk_swapColumns_strand] at hfg
          have hmul : h ⟨σ⟩ * h ⟨σ * (permCoxeterSystem n).simple i⟩ = 1 := by
            calc h ⟨σ⟩ * h ⟨σ * (permCoxeterSystem n).simple i⟩
                = (f ⟨σ⟩ * f ⟨σ * (permCoxeterSystem n).simple i⟩) *
                    (g ⟨σ⟩ * g ⟨σ * (permCoxeterSystem n).simple i⟩) := by unfold h; ac_rfl
              _ = (g ⟨σ⟩ * g ⟨σ * (permCoxeterSystem n).simple i⟩) *
                    (g ⟨σ⟩ * g ⟨σ * (permCoxeterSystem n).simple i⟩) := by rw [hfg]
              _ = 1 := Int.units_mul_self _
          exact units_eq_of_mul_eq_one hmul
        exact (permCoxeterSystem n).fun_eq_const_of_mul_simple_eq
          (f := fun σ => h ⟨σ⟩) hstep x.toPerm
      · intro x
        have hx : x = ⟨1⟩ := by
          ext c
          have := c.isLt
          omega
        rw [hx]
    rcases Int.units_eq_one_or (h ⟨1⟩) with h1 | h1
    · left
      funext x
      exact (units_eq_of_mul_eq_one ((hconst x).trans h1)).symm
    · right
      funext x
      have hx := units_eq_neg_of_mul_eq_neg_one ((hconst x).trans h1)
      simpa [Pi.neg_apply] using congrArg Neg.neg hx |>.symm
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
        ratio S T' (widthOneRect x (BraidGroup.strand i) hn) (widthOneRect_isEmpty x _ hn) = 1 := by
      intro x i
      let r := widthOneRect x (BraidGroup.strand i) hn
      have hr : r.IsEmpty := widthOneRect_isEmpty x _ hn
      have htarget : x.swapColumns (BraidGroup.strand i) (finRotate n (BraidGroup.strand i)) =
          ⟨x.toPerm * (permCoxeterSystem n).simple i⟩ :=
        mk_swapColumns_strand x.toPerm i
      have hbase :
          ratio S T r hr = (f x.toPerm)⁻¹ * f (x.toPerm * (permCoxeterSystem n).simple i) :=
        (hf x.toPerm i).symm
      calc ratio S T' r hr
          = (g x * g (x.swapColumns (BraidGroup.strand i) (finRotate n (BraidGroup.strand i)))) *
              ratio S T r hr := by
            simp only [ratio, T', gauge_sign]
            ac_rfl
        _ = (f x.toPerm * f (x.toPerm * (permCoxeterSystem n).simple i)) *
              ((f x.toPerm)⁻¹ * f (x.toPerm * (permCoxeterSystem n).simple i)) := by
            rw [hbase, htarget]
        _ = (f x.toPerm * (f x.toPerm)⁻¹) *
              (f (x.toPerm * (permCoxeterSystem n).simple i) *
                f (x.toPerm * (permCoxeterSystem n).simple i)) := by ac_rfl
        _ = 1 := by rw [mul_inv_cancel, Int.units_mul_self, mul_one]
    have hnonwrap : ∀ {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
        r.left.val < r.right.val → ratio S T' r hr = 1 := fun r hr hlt =>
      ratio_eq_one_of_left_lt_right S T' hn hadj (r.right.val - r.left.val) r hr hlt rfl
    have hall1 : ∀ (x : GridState n) (a : Fin n),
        ratio S T' (widthOneRect x a hn) (widthOneRect_isEmpty x a hn) = 1 := by
      intro x a
      by_cases ha : a.val < n - 1
      · let i : Fin (n - 1) := ⟨a.val, ha⟩
        have hi : BraidGroup.strand i = a := Fin.ext (BraidGroup.val_strand i)
        have hcongr := ratio_congr S T' (widthOneRect_isEmpty x a hn)
          (widthOneRect_isEmpty x (BraidGroup.strand i) hn) rfl
          (by rw [widthOneRect_left, widthOneRect_left, hi])
          (by rw [widthOneRect_right, widthOneRect_right, hi])
        rw [hcongr, hadj]
      · let lastCol : Fin n := ⟨n - 1, by omega⟩
        have halast : a = lastCol := Fin.ext (by have := a.isLt; simp only [lastCol]; omega)
        rw [halast]
        exact ratio_eq_one_lastCol S T' hn hnonwrap _ x rfl
    have hST' : S = T' := GridSignAssignment.ext fun x y r hr =>
      (ratio_eq_one_iff S T' r hr).mp
        (ratio_eq_one_of_widthOne S T' hn hall1 (Grid.cIco r.left r.right).card r hr rfl)
    refine ⟨g, ?_⟩
    rw [hST']
    exact T.gauge_gauge_self g
  · refine ⟨1, GridSignAssignment.ext fun x y r _ => ?_⟩
    have hl := r.left.isLt
    have hr := r.right.isLt
    exact False.elim (r.left_ne_right (Fin.ext (by omega)))

/-- The gauge transforming one sign assignment into another is unique once its value at a single
grid state is specified. -/
theorem existsUnique_gauge_eq (S T : GridSignAssignment n) (x₀ : GridState n) (s₀ : ℤˣ) :
    ∃! f : GridState n → ℤˣ, f x₀ = s₀ ∧ S.gauge f = T := by
  obtain ⟨f₀, hf₀⟩ := exists_gauge_eq S T
  let c : ℤˣ := s₀ * f₀ x₀
  let f : GridState n → ℤˣ := fun x => c * f₀ x
  have hfx₀ : f x₀ = s₀ := by
    simp only [f, c, mul_assoc, Int.units_mul_self, mul_one]
  have hgauge : S.gauge f = T := by
    rw [← hf₀]
    refine GridSignAssignment.ext fun x y r hr => ?_
    simp only [gauge_sign, f]
    calc c * f₀ x * (c * f₀ y) * S.sign r hr
        = (c * c) * (f₀ x * f₀ y * S.sign r hr) := by ac_rfl
      _ = f₀ x * f₀ y * S.sign r hr := by rw [Int.units_mul_self, one_mul]
  refine ⟨f, ⟨hfx₀, hgauge⟩, ?_⟩
  rintro g ⟨hgx₀, hggauge⟩
  rcases (S.gauge_eq_iff g f).mp (hggauge.trans hgauge.symm) with rfl | hneg
  · rfl
  · exfalso
    have hx := congrFun hneg x₀
    rw [hgx₀, Pi.neg_apply, hfx₀] at hx
    exact units_ne_neg_self s₀ hx

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
