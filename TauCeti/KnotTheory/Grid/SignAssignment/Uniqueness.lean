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
import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Empty
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
  obtain rfl : y = y' := by rw [r.target_eq_swapColumns, r'.target_eq_swapColumns, hl, hrr]
  obtain rfl : r = r' := GridRectangleBetween.ext hl hrr; rfl

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
    {D E : GridRectangleDecomposition x z} (hone : D.HasOneCommonSide)
    (h₁ : D.first.IsEmpty) (h₂ : D.second.IsEmpty) (hE : E = D.recut hone h₁ h₂)
    (hE₁ : E.first.IsEmpty) (hE₂ : E.second.IsEmpty) :
    ratio S T E.first hE₁ * ratio S T E.second hE₂ =
      ratio S T D.first h₁ * ratio S T D.second h₂ := by
  subst hE; exact ratio_square S T D (D.recut hone h₁ h₂) h₁ h₂ hE₁ hE₂
    (D.recut_ne hone h₁ h₂) (D.isRecut_recut hone h₁ h₂).isRepartition.val_add_val_eq

private theorem ratio_vertical_annulus (S T : GridSignAssignment n) {x y : GridState n}
    (r : GridRectangleBetween x y) (s : GridRectangleBetween y x)
    (hr : r.IsEmpty) (hs : s.IsEmpty) (hleft : s.left = r.left) :
    ratio S T s hs = ratio S T r hr :=
  units_eq_of_mul_eq_one <| by
    rw [ratio_mul_ratio, S.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft,
      T.sign_mul_sign_eq_neg_one_of_left_eq_left r s hr hs hleft]; simp

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

private theorem mk_swapColumns_strand (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    (⟨σ⟩ : GridState n).swapColumns (BraidGroup.strand i) (finRotate n (BraidGroup.strand i)) =
      ⟨σ * (permCoxeterSystem n).simple i⟩ := by
  ext c; rw [GridState.swapColumns_apply, BraidGroup.finRotate_strand, permCoxeterSystem_simple,
    BraidGroup.transposition_eq_swap]; rfl

/-- The `ℤˣ`-valued 1-cochain on the right Cayley graph of `Equiv.Perm (Fin n)` obtained by
evaluating the ratio of `S` and `T` on adjacent width-one rectangles. -/
private def adjCocycle (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) : ℤˣ :=
  ratio S T (widthOneRect ⟨σ⟩ (BraidGroup.strand i) hn) (widthOneRect_isEmpty _ _ hn)

private theorem adjCocycle_inv (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) (i : Fin (n - 1)) :
    adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) i = (adjCocycle S T hn σ i)⁻¹ := by
  let r := widthOneRect ⟨σ⟩ (BraidGroup.strand i) hn
  have hs : r.verticalComplement.IsEmpty := (r.isEmpty_and_isEmpty_verticalComplement_iff.mpr
    (by rw [widthOneRect_left, widthOneRect_right])).2
  rw [adjCocycle, ratio_congr S T _ hs (mk_swapColumns_strand σ i).symm
      (by simp [r, widthOneRect_left]) (by simp [r, widthOneRect_right]),
    ratio_vertical_annulus S T r r.verticalComplement (widthOneRect_isEmpty _ _ hn) hs
      r.verticalComplement_left, Int.units_inv_eq_self]; rfl

private theorem adjCocycle_braid_two (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)}
    (hdist : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    adjCocycle S T hn σ i * adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) j =
      adjCocycle S T hn σ j * adjCocycle S T hn (σ * (permCoxeterSystem n).simple j) i := by
  let x : GridState n := ⟨σ⟩; let a := BraidGroup.strand i; let b := BraidGroup.strand j
  let y := x.swapColumns a (finRotate n a)
  let D : GridRectangleDecomposition x (y.swapColumns b (finRotate n b)) :=
    { middle := y, first := widthOneRect x a hn, second := widthOneRect y b hn }
  have hdisj : D.HasDisjointSides := by
    rw [D.hasDisjointSides_iff]
    simp only [D, widthOneRect_left, widthOneRect_right, BraidGroup.finRotate_strand, a, b, ne_eq,
      Fin.ext_iff, BraidGroup.val_strand, BraidGroup.val_strandSucc]; omega
  have hD₁ := widthOneRect_isEmpty x a hn; have hD₂ := widthOneRect_isEmpty y b hn
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

/-- Recutting two consecutive width-one rectangles `(a, b)` then `(b, c)` when
`x b ∈ cIoo (x a) (x c)` yields side columns `(b, c)` followed by `(a, c)`. -/
private theorem recut_sides_of_consecutive_widthOne {x z : GridState n}
    (D : GridRectangleDecomposition x z) {a b c : Fin n}
    (hfl : D.first.left = a) (hfr : D.first.right = b)
    (hsl : D.second.left = b) (hsr : D.second.right = c)
    (hac : a ≠ c) (hbc : b ≠ c) (hrow : x b ∈ Grid.cIoo (x a) (x c))
    (hone : D.HasOneCommonSide) (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    (D.recut hone hD₁ hD₂).first.left = b ∧ (D.recut hone hD₁ hD₂).first.right = c ∧
      (D.recut hone hD₁ hD₂).second.left = a ∧ (D.recut hone hD₁ hD₂).second.right = c := by
  rcases D.recut_geometry_of_right_eq_left (hfr.trans hsl.symm) hone hD₁ hD₂ with
    ⟨-, hEfl, hEfr, hEsl, hEsr, -⟩ | ⟨hbad, -⟩
  · exact ⟨hEfl.trans hfr, hEfr.trans hsr, hEsl.trans hfl, hEsr.trans hsr⟩
  · have hstop : D.second.top = x c := by
      rw [GridRectangleBetween.top_def, hsr, D.first.map_of_ne c (hfl ▸ hac.symm) (hfr ▸ hbc.symm)]
    rw [GridRectangleBetween.bottom_def, hfl, GridRectangleBetween.top_def, hfr, hstop] at hbad
    exact False.elim (Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap (x a) (x b)) hbad
      (Grid.mem_cIoo_cyclic_left hrow))

/-- Recutting an empty rectangle on `(a, c)` followed by an empty rectangle on `(a, b)` with
`b ∈ cIoo a c` yields side columns `(a, b)` followed by `(b, c)`. -/
private theorem recut_sides_of_span_then_left {x z : GridState n}
    (D : GridRectangleDecomposition x z) {a b c : Fin n}
    (hfl : D.first.left = a) (hfr : D.first.right = c)
    (hsl : D.second.left = a) (hsr : D.second.right = b) (hbac : b ∈ Grid.cIoo a c)
    (hone : D.HasOneCommonSide) (hD₁ : D.first.IsEmpty) (hD₂ : D.second.IsEmpty) :
    (D.recut hone hD₁ hD₂).first.left = a ∧ (D.recut hone hD₁ hD₂).first.right = b ∧
      (D.recut hone hD₁ hD₂).second.left = b ∧ (D.recut hone hD₁ hD₂).second.right = c := by
  obtain ⟨hEfl, hEfr, hEsl, hEsr⟩ :=
    D.recut_sides_of_left_eq_left_of_mem_cIoo (hfl.trans hsl.symm) (by rwa [hfl, hfr, hsr]) hD₁ hD₂
  exact ⟨hEfl.trans hfl, hEfr.trans hsr, hEsl.trans hsr, hEsr.trans hfr⟩

private noncomputable abbrev braidThreeProd (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) (i j : Fin (n - 1)) : ℤˣ :=
  adjCocycle S T hn σ i * adjCocycle S T hn (σ * (permCoxeterSystem n).simple i) j *
    adjCocycle S T hn (σ * (permCoxeterSystem n).simple i * (permCoxeterSystem n).simple j) i

private theorem adjCocycle_braid_three_of_mem_cIoo (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j)
    (hrow : σ (BraidGroup.strandSucc i) ∈
      Grid.cIoo (σ (BraidGroup.strand i)) (σ (BraidGroup.strandSucc j))) :
    braidThreeProd S T hn σ i j = braidThreeProd S T hn σ j i := by
  let x : GridState n := ⟨σ⟩
  let a := BraidGroup.strand i; let b := BraidGroup.strandSucc i; let c := BraidGroup.strandSucc j
  set si := (permCoxeterSystem n).simple i; set sj := (permCoxeterSystem n).simple j
  have hbj : BraidGroup.strand j = b := BraidGroup.strand_eq_strandSucc_of_succ hij
  have hab : finRotate n a = b := BraidGroup.finRotate_strand i
  have hbc : finRotate n b = c := hbj ▸ BraidGroup.finRotate_strand j
  have hac : a ≠ c := BraidGroup.strand_ne_strandSucc_of_succ hij
  have hbac : b ∈ Grid.cIoo a c := by
    rw [Grid.mem_cIoo]; refine ⟨hac, ?_⟩
    have := BraidGroup.val_strand i; have := BraidGroup.val_strandSucc i
    have := BraidGroup.val_strandSucc j; rw [ite_eq_left (by omega)]; omega
  -- Step 1: recut `(a, b)` followed by `(b, c)` at `x` into `(b, c)` followed by `(a, c)`.
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
  let E₁ := D₁.recut hone₁ hD₁f hD₁s; have hrec₁ := D₁.isRecut_recut hone₁ hD₁f hD₁s
  obtain ⟨hE₁fl, hE₁fr, hE₁sl, hE₁sr⟩ := recut_sides_of_consecutive_widthOne D₁
    (widthOneRect_left x a hn) ((widthOneRect_right x a hn).trans hab)
    ((widthOneRect_left y₁ (BraidGroup.strand j) hn).trans hbj)
    (by simp only [D₁, widthOneRect_right, hbj, hbc])
    hac (hbj ▸ BraidGroup.strand_ne_strandSucc j) hrow hone₁ hD₁f hD₁s
  have hy₁ : y₁ = ⟨σ * si⟩ := mk_swapColumns_strand σ i
  have hz₁ : z₁ = ⟨σ * si * sj⟩ := (by rw [← hy₁] : z₁ = _).trans (mk_swapColumns_strand _ j)
  have hE₁mid : E₁.middle = ⟨σ * sj⟩ := by
    rw [E₁.first.target_eq_swapColumns, hE₁fl, hE₁fr, ← hbc, ← hbj]; exact mk_swapColumns_strand σ j
  have hstep₁ : adjCocycle S T hn σ j * ratio S T E₁.second hrec₁.isEmpty_second =
      adjCocycle S T hn σ i * adjCocycle S T hn (σ * si) j := by
    have hr₁ := ratio_recut S T hone₁ hD₁f hD₁s rfl hrec₁.isEmpty_first hrec₁.isEmpty_second
    rw [ratio_congr S T hrec₁.isEmpty_first (widthOneRect_isEmpty x (BraidGroup.strand j) hn) rfl
        (by rw [hE₁fl, widthOneRect_left, hbj]) (by rw [hE₁fr, widthOneRect_right, hbj, hbc]),
      ratio_congr S T hD₁s (widthOneRect_isEmpty ⟨σ * si⟩ (BraidGroup.strand j) hn) hy₁
        (by simp [D₁, widthOneRect_left]) (by simp [D₁, widthOneRect_right])] at hr₁; exact hr₁
  -- Step 2: recut `E₁.second` (on `(a, c)`) followed by `(a, b)` at `z₁` into `(a, b)`
  -- followed by `(b, c)`.
  let D₂ : GridRectangleDecomposition E₁.middle (z₁.swapColumns a (finRotate n a)) :=
    { middle := z₁, first := E₁.second, second := widthOneRect z₁ a hn }
  have hD₂_common : D₂.first.left = D₂.second.left := hE₁sl.trans (widthOneRect_left z₁ a hn).symm
  have hD₂_col : D₂.second.right ∈ Grid.cIoo D₂.first.left D₂.first.right := by
    dsimp only [D₂, E₁]; rwa [widthOneRect_right, hE₁sl, hE₁sr, hab]
  have hone₂ := D₂.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hD₂_common hD₂_col
  have hD₂s : D₂.second.IsEmpty := widthOneRect_isEmpty _ _ hn
  let E₂ := D₂.recut hone₂ hrec₁.isEmpty_second hD₂s
  have hrec₂ := D₂.isRecut_recut hone₂ hrec₁.isEmpty_second hD₂s
  obtain ⟨hE₂fl, hE₂fr, hE₂sl, hE₂sr⟩ := recut_sides_of_span_then_left D₂
    hE₁sl hE₁sr (widthOneRect_left z₁ a hn) ((widthOneRect_right z₁ a hn).trans hab) hbac
    hone₂ hrec₁.isEmpty_second hD₂s
  have hE₂mid : E₂.middle = ⟨σ * sj * si⟩ := by
    rw [E₂.first.target_eq_swapColumns, hE₂fl, hE₂fr, ← hab, hE₁mid]
    exact mk_swapColumns_strand _ i
  have hstep₂ : adjCocycle S T hn (σ * sj) i * adjCocycle S T hn (σ * sj * si) j =
      ratio S T E₁.second hrec₁.isEmpty_second * adjCocycle S T hn (σ * si * sj) i := by
    have hr₂ := ratio_recut S T hone₂ hrec₁.isEmpty_second hD₂s rfl
      hrec₂.isEmpty_first hrec₂.isEmpty_second
    rw [ratio_congr S T hrec₂.isEmpty_first (widthOneRect_isEmpty ⟨σ * sj⟩ a hn) hE₁mid
        (by rw [hE₂fl, widthOneRect_left]) (by rw [hE₂fr, ← hab, widthOneRect_right]),
      ratio_congr S T hrec₂.isEmpty_second
        (widthOneRect_isEmpty ⟨σ * sj * si⟩ (BraidGroup.strand j) hn) hE₂mid
        (by rw [hE₂sl, widthOneRect_left, hbj]) (by rw [hE₂sr, widthOneRect_right, hbj, hbc]),
      ratio_congr S T hD₂s (widthOneRect_isEmpty ⟨σ * si * sj⟩ a hn) hz₁
        (by simp [D₂, widthOneRect_left, a]) (by simp [D₂, widthOneRect_right, a])] at hr₂
    exact hr₂
  -- Combine both recut identities across the shared factor `ratio S T E₁.second`.
  rw [braidThreeProd, braidThreeProd, ← hstep₁, mul_assoc, ← hstep₂, ← mul_assoc]

private theorem adjCocycle_braid_three_of_succ (S T : GridSignAssignment n) (hn : 1 < n)
    (σ : Equiv.Perm (Fin n)) {i j : Fin (n - 1)} (hij : (i : ℕ) + 1 = j) :
    braidThreeProd S T hn σ i j = braidThreeProd S T hn σ j i := by
  let a := BraidGroup.strand i; let b := BraidGroup.strandSucc i; let c := BraidGroup.strandSucc j
  by_cases hrow : σ b ∈ Grid.cIoo (σ a) (σ c)
  · exact adjCocycle_braid_three_of_mem_cIoo S T hn σ hij hrow
  · set si := (permCoxeterSystem n).simple i with hsi_def
    set sj := (permCoxeterSystem n).simple j with hsj_def
    let τ : Equiv.Perm (Fin n) := σ * si * sj * si
    have hτ_eq : τ = σ * sj * si * sj := by
      have hbraid : si * sj * si = sj * si * sj := by
        simpa [si, sj, permCoxeterSystem_simple] using BraidGroup.transposition_braid (Or.inl hij)
      simp only [τ, mul_assoc, ← mul_assoc si sj si, hbraid]
    have hbj : BraidGroup.strand j = b := BraidGroup.strand_eq_strandSucc_of_succ hij
    have hab : a ≠ b := BraidGroup.strand_ne_strandSucc i
    have hbc : b ≠ c := hbj ▸ BraidGroup.strand_ne_strandSucc j
    have hac : a ≠ c := BraidGroup.strand_ne_strandSucc_of_succ hij
    have hsi : si = Equiv.swap a b := by
      simp [si, permCoxeterSystem_simple, BraidGroup.transposition_eq_swap, a, b]
    have hsj : sj = Equiv.swap b c := by
      simp [sj, permCoxeterSystem_simple, BraidGroup.transposition_eq_swap, hbj, c]
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
    unfold braidThreeProd at hmain ⊢
    simp only [← hsi_def, ← hsj_def] at hmain ⊢
    have hL2 : τ * si = σ * si * sj := hsi_def ▸ hsq _ i
    have hL3 : τ * si * sj = σ * si := hL2 ▸ hsj_def ▸ hsq _ j
    have hR2 : τ * sj = σ * sj * si := hτ_eq ▸ hsj_def ▸ hsq _ j
    have hR3 : τ * sj * si = σ * sj := hR2 ▸ hsi_def ▸ hsq _ i
    have hstep_i : ∀ w, adjCocycle S T hn (w * si) i = adjCocycle S T hn w i :=
      fun w => hsi_def ▸ hstep w i
    have hstep_j : ∀ w, adjCocycle S T hn (w * sj) j = adjCocycle S T hn w j :=
      fun w => hsj_def ▸ hstep w j
    rw [hL3, hL2, hR3, hR2, hstep_i σ, hstep_j (σ * si), hstep_i (σ * sj), hstep_j σ,
      show adjCocycle S T hn τ i = adjCocycle S T hn (σ * si * sj) i from hstep_i _,
      show adjCocycle S T hn τ j = adjCocycle S T hn (σ * sj * si) j by rw [hτ_eq, hstep_j]]
        at hmain
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
    exact hadj.elim (fun h => (adjCocycle_braid_three_of_succ S T hn σ h).symm)
      (adjCocycle_braid_three_of_succ S T hn σ)
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
    rw [Grid.cIco_eq_singleton_iff.mpr ⟨rfl, heq.symm, hab⟩, Finset.card_singleton] at hw; omega
  have hmem : finRotate n a ∈ Grid.cIoo a b :=
    Grid.mem_cIoo_cyclic_right (Grid.mem_cIoo_finRotate_left_iff.mpr ⟨hab.symm, hne.symm⟩)
  have hunion := congrArg Finset.card (Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hmem)
  rw [Finset.card_union_of_disjoint (Grid.disjoint_cIco_cIco_of_mem_cIoo hmem), hw,
    Grid.cIco_eq_singleton_iff.mpr ⟨rfl, rfl, (Grid.finRotate_ne_self hn a).symm⟩,
    Finset.card_singleton] at hunion
  exact ⟨hmem, by omega⟩

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
      obtain ⟨hEfl, hEfr, hEsl, hEsr⟩ := recut_sides_of_span_then_left D rfl rfl
        (widthOneRect_left y a hn) (widthOneRect_right y a hn) hb_mem hone hr hDs
      have hEf : ratio S T E.first hrec.isEmpty_first = 1 := by
        rw [ratio_congr S T hrec.isEmpty_first (widthOneRect_isEmpty x a hn) rfl
          (hEfl.trans (widthOneRect_left x a hn).symm)
          (hEfr.trans (widthOneRect_right x a hn).symm), h1 x a hPa]
      have hEs : ratio S T E.second hrec.isEmpty_second = 1 :=
        ih (w - 1) (by omega) E.second hrec.isEmpty_second (by rwa [hEsl, hEsr]) fun c hc =>
          hP c (Grid.cIco_subset_of_mem_cIoo hb_mem (by rwa [hEsl, hEsr] at hc))
      have hrecut := ratio_recut S T hone hr hDs rfl hrec.isEmpty_first hrec.isEmpty_second
      rw [hEf, hEs, show ratio S T D.second hDs = 1 from h1 y a hPa, mul_one, mul_one] at hrecut
      exact hrecut.symm

/-- A wrapping height-one rectangle pairs via a horizontal annulus with a non-wrapping empty
rectangle, so agreement on non-wrapping rectangles forces its ratio to be `1`. -/
private theorem ratio_eq_one_of_top_eq_finRotate (S T : GridSignAssignment n)
    (hnonwrap : ∀ {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      r.left.val < r.right.val → ratio S T r hr = 1)
    {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty)
    (hrev : r.right.val < r.left.val) (htop : r.top = finRotate n r.bottom) :
    ratio S T r hr = 1 := by
  have hs_empty : r.horizontalComplement.IsEmpty :=
    (r.isEmpty_and_isEmpty_horizontalComplement_iff.mpr htop).2
  rw [← ratio_horizontal_annulus S T r r.horizontalComplement hr hs_empty
    r.horizontalComplement_left]
  exact hnonwrap r.horizontalComplement hs_empty (by simpa using hrev)

private def lastCol (hn : 1 < n) : Fin n := ⟨n - 1, by omega⟩
private def zeroCol (hn : 1 < n) : Fin n := ⟨0, by omega⟩

private theorem finRotate_lastCol (hn : 1 < n) : finRotate n (lastCol hn) = zeroCol hn := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact Fin.ext (by rw [coe_finRotate]; simp [lastCol, Fin.last, zeroCol])

private theorem lastCol_ne_zeroCol (hn : 1 < n) : lastCol hn ≠ zeroCol hn :=
  finRotate_lastCol hn ▸ (Grid.finRotate_ne_self hn (lastCol hn)).symm

/-- When the row span from `x (lastCol hn)` to `x (zeroCol hn)` has height `h ≠ 1`, the column `c`
at row `finRotate n (x (lastCol hn))` satisfies `0 < c < n - 1`, and swapping `lastCol hn` with `c`
reduces that height to `h - 1`. -/
private theorem exists_cutCol_of_height_ne_one (hn : 1 < n) (x : GridState n) {h : ℕ}
    (hh : (Grid.cIco (x (lastCol hn)) (x (zeroCol hn))).card = h) (hh1 : h ≠ 1) :
    ∃ c : Fin n, x c = finRotate n (x (lastCol hn)) ∧ 0 < c.val ∧ c.val < n - 1 ∧
      (Grid.cIco ((x.swapColumns (lastCol hn) c) (lastCol hn))
        ((x.swapColumns (lastCol hn) c) (zeroCol hn))).card = h - 1 := by
  have hne_rows : x (lastCol hn) ≠ x (zeroCol hn) := x.toPerm.injective.ne (lastCol_ne_zeroCol hn)
  obtain ⟨hr_mid_mem, hcard_mid⟩ := mem_cIoo_and_card_cIco_finRotate hn hne_rows hh hh1
  let r_mid : Fin n := finRotate n (x (lastCol hn))
  let c : Fin n := x.toPerm.symm r_mid
  have hxc : x c = r_mid := x.toPerm.apply_symm_apply r_mid
  have hc_ne_last : c ≠ lastCol hn := fun heq =>
    Grid.finRotate_ne_self hn (x (lastCol hn)) (hxc.symm.trans (congrArg x heq))
  have hc_ne_zero : c ≠ zeroCol hn := fun heq =>
    Grid.right_notMem_cIoo (x (lastCol hn)) (x (zeroCol hn))
      ((hxc.symm.trans (congrArg x heq)) ▸ hr_mid_mem)
  refine ⟨c, hxc, Nat.pos_of_ne_zero fun heq => hc_ne_zero (Fin.ext heq),
    lt_of_le_of_ne (by have := c.isLt; omega) (fun heq => hc_ne_last (Fin.ext heq)), ?_⟩
  simpa only [GridState.swapColumns_apply, Equiv.swap_apply_left, hxc,
    Equiv.swap_apply_of_ne_of_ne (lastCol_ne_zeroCol hn).symm hc_ne_zero.symm] using hcard_mid

/-- The wrapping height-one strip rectangle from `lastCol hn` to an interior column `c < n - 1`. -/
private def heightOneStrip (x : GridState n) (hn : 1 < n) {c : Fin n} (hc_lt : c.val < n - 1) :
    GridRectangleBetween x (x.swapColumns (lastCol hn) c) :=
  GridRectangleBetween.ofSwapColumns x _ (lastCol hn) c
    (fun heq => by have := congrArg Fin.val heq; simp [lastCol] at this; omega) rfl

private theorem heightOneStrip_isEmpty (x : GridState n) (hn : 1 < n) {c : Fin n}
    (hc_lt : c.val < n - 1) (hxc : x c = finRotate n (x (lastCol hn))) :
    (heightOneStrip x hn hc_lt).IsEmpty :=
  ((heightOneStrip x hn hc_lt).isEmpty_and_isEmpty_horizontalComplement_iff.mpr (by
    rw [heightOneStrip, GridRectangleBetween.ofSwapColumns_top,
      GridRectangleBetween.ofSwapColumns_bottom, hxc])).1

private theorem ratio_heightOneStrip (S T : GridSignAssignment n) (hn : 1 < n)
    (hnonwrap : ∀ {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      r.left.val < r.right.val → ratio S T r hr = 1)
    (x : GridState n) {c : Fin n} (hc_lt : c.val < n - 1)
    (hxc : x c = finRotate n (x (lastCol hn))) :
    ratio S T (heightOneStrip x hn hc_lt) (heightOneStrip_isEmpty x hn hc_lt hxc) = 1 :=
  ratio_eq_one_of_top_eq_finRotate S T hnonwrap _ _ (by simpa [heightOneStrip, lastCol] using hc_lt)
    (by rw [heightOneStrip, GridRectangleBetween.ofSwapColumns_top,
          GridRectangleBetween.ofSwapColumns_bottom, hxc])

/-- Agreement on all non-wrapping empty rectangles extends to wrapping width-one rectangles from
column `n - 1` to column `0`, by induction on vertical height. -/
private theorem ratio_eq_one_lastCol (S T : GridSignAssignment n) (hn : 1 < n)
    (hnonwrap : ∀ {x y : GridState n} (r : GridRectangleBetween x y) (hr : r.IsEmpty),
      r.left.val < r.right.val → ratio S T r hr = 1) :
    ∀ (h : ℕ) (x : GridState n),
      (Grid.cIco (x (lastCol hn)) (x (zeroCol hn))).card = h →
      ratio S T (widthOneRect x (lastCol hn) hn) (widthOneRect_isEmpty x (lastCol hn) hn) = 1 := by
  intro h
  induction h using Nat.strong_induction_on with
  | ind h ih =>
    intro x hh
    have hne_rows : x (lastCol hn) ≠ x (zeroCol hn) := x.toPerm.injective.ne (lastCol_ne_zeroCol hn)
    by_cases hh1 : h = 1
    · -- Base case `h = 1`: horizontal annulus pairs `widthOneRect` with a non-wrapping rectangle.
      have hcard_oo : (Grid.cIoo (x (lastCol hn)) (x (zeroCol hn))).card = 0 := by
        have := Grid.card_cIco_of_ne hne_rows; omega
      have htop : x (zeroCol hn) = finRotate n (x (lastCol hn)) :=
        (Grid.cIco_eq_singleton_iff.mp (show Grid.cIco (x (lastCol hn)) (x (zeroCol hn)) =
            {x (lastCol hn)} by
          simp [Grid.cIco_of_ne hne_rows, Finset.card_eq_zero.mp hcard_oo])).2.1
      exact ratio_eq_one_of_top_eq_finRotate S T hnonwrap (widthOneRect x (lastCol hn) hn)
        (widthOneRect_isEmpty x (lastCol hn) hn)
        (by rw [widthOneRect_right, widthOneRect_left, finRotate_lastCol]
            simp only [zeroCol, lastCol]; omega)
        (by rw [widthOneRect_bottom, widthOneRect_top, finRotate_lastCol, htop])
    · -- Inductive step `h ≥ 2`: cut off a height-one strip `t` at column `c` (`0 < c < n - 1`).
      have hge2 : 2 ≤ h := by have := Grid.card_cIco_of_ne hne_rows; omega
      obtain ⟨c, hxc, hc_pos, hc_lt, hD2_height⟩ := exists_cutCol_of_height_ne_one hn x hh hh1
      let w := x.swapColumns (lastCol hn) c
      let t := heightOneStrip x hn hc_lt
      have ht_empty : t.IsEmpty := heightOneStrip_isEmpty x hn hc_lt hxc
      let D : GridRectangleDecomposition x
          (w.swapColumns (lastCol hn) (finRotate n (lastCol hn))) :=
        { middle := w, first := t, second := widthOneRect w (lastCol hn) hn }
      have hDfl : D.first.left = lastCol hn := GridRectangleBetween.ofSwapColumns_left ..
      have hDfr : D.first.right = c := GridRectangleBetween.ofSwapColumns_right ..
      have hDsr : D.second.right = zeroCol hn :=
        (widthOneRect_right w (lastCol hn) hn).trans (finRotate_lastCol hn)
      have hD_common : D.first.left = D.second.left :=
        hDfl.trans (widthOneRect_left w (lastCol hn) hn).symm
      have hbac : zeroCol hn ∈ Grid.cIoo (lastCol hn) c := by
        rw [Grid.mem_cIoo]
        refine ⟨fun heq => by have := congrArg Fin.val heq; simp [lastCol] at this; omega, ?_⟩
        rw [ite_eq_right (by simp [lastCol]; omega)]; exact Or.inr hc_pos
      have hone := D.hasOneCommonSide_of_left_eq_left_of_mem_cIoo hD_common
        (by rwa [hDfl, hDfr, hDsr])
      have hDs : D.second.IsEmpty := widthOneRect_isEmpty w (lastCol hn) hn
      let E := D.recut hone ht_empty hDs
      have hrec := D.isRecut_recut hone ht_empty hDs
      obtain ⟨hEfl, hEfr, hEsl, hEsr⟩ := recut_sides_of_span_then_left D hDfl hDfr
        (widthOneRect_left w (lastCol hn) hn) hDsr hbac hone ht_empty hDs
      have hrecut := ratio_recut S T hone ht_empty hDs rfl hrec.isEmpty_first hrec.isEmpty_second
      rw [ratio_congr S T _ (widthOneRect_isEmpty x (lastCol hn) hn) rfl
            (hEfl.trans (widthOneRect_left x (lastCol hn) hn).symm)
            (by rw [hEfr, widthOneRect_right, finRotate_lastCol]),
          hnonwrap E.second hrec.isEmpty_second (by rw [hEsl, hEsr]; exact hc_pos),
          show ratio S T D.first ht_empty = 1 from ratio_heightOneStrip S T hn hnonwrap x hc_lt hxc,
          show ratio S T D.second hDs = 1 from ih (h - 1) (by omega) w hD2_height,
          mul_one, mul_one] at hrecut
      exact hrecut

/-! ### Main uniqueness theorems -/

/-- Negating a gauge leaves the gauged sign assignment unchanged, since every rectangle carries
both endpoint signs. -/
@[simp]
theorem gauge_neg (S : GridSignAssignment n) (f : GridState n → ℤˣ) :
    S.gauge (-f) = S.gauge f := by
  refine GridSignAssignment.ext fun _ _ _ _ => ?_
  simp only [gauge_sign, Pi.neg_apply, neg_mul_neg]

/-- Two gauges produce the same sign assignment if and only if they agree everywhere or are
opposite everywhere. -/
theorem gauge_eq_iff (S : GridSignAssignment n) (f g : GridState n → ℤˣ) :
    S.gauge f = S.gauge g ↔ f = g ∨ f = -g := by
  refine ⟨fun heq => ?_, fun h => h.elim (fun h => h ▸ rfl) fun h => h ▸ S.gauge_neg g⟩
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
      exact (permCoxeterSystem n).fun_eq_const_of_mul_simple_eq (f := fun σ => h ⟨σ⟩) hstep x.toPerm
    · intro x; rw [show x = ⟨1⟩ by ext c; have := c.isLt; omega]
  rcases Int.units_eq_one_or (h ⟨1⟩) with h1 | h1
  · exact Or.inl (funext fun x => (units_eq_of_mul_eq_one ((hconst x).trans h1)).symm)
  · exact Or.inr (funext fun x => by
      simpa [Pi.neg_apply] using
        (congrArg Neg.neg (units_eq_neg_of_mul_eq_neg_one ((hconst x).trans h1))).symm)

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
        rw [show ratio S T' _ _ = (g x * g (x.swapColumns (BraidGroup.strand i)
                (finRotate n (BraidGroup.strand i)))) * ratio S T _ _ by
              simp only [ratio, T', gauge_sign]; ac_rfl,
          show ratio S T _ _ = (f x.toPerm)⁻¹ * f (x.toPerm * (permCoxeterSystem n).simple i) from
            (hf x.toPerm i).symm,
          mk_swapColumns_strand x.toPerm i]
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
        ratio S T' (widthOneRect x a hn) (widthOneRect_isEmpty x a hn) = 1 := fun x a _ =>
      if ha : a.val < n - 1 then hadj' x a ha
      else (show a = lastCol hn from Fin.ext (by have := a.isLt; simp [lastCol]; omega)) ▸
        ratio_eq_one_lastCol S T' hn hnonwrap _ x rfl
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
  let f : GridState n → ℤˣ := fun x => (s₀ * f₀ x₀) * f₀ x
  have hfx₀ : f x₀ = s₀ := by simp only [f, mul_assoc, Int.units_mul_self, mul_one]
  have hgauge : S.gauge f = T := hf₀ ▸ GridSignAssignment.ext fun _ _ _ _ => by
    simp only [gauge_sign, f]; rw [mul_mul_mul_comm, Int.units_mul_self, one_mul]
  refine ⟨f, ⟨hfx₀, hgauge⟩, fun g ⟨hgx₀, hggauge⟩ => ?_⟩
  exact ((S.gauge_eq_iff g f).mp (hggauge.trans hgauge.symm)).resolve_right fun hneg =>
    units_ne_neg_self s₀ (by simpa [hgx₀, hfx₀] using congrFun hneg x₀)

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
