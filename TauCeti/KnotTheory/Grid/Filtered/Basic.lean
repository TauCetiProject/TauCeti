/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.XHomotopy.Annulus
import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Empty

/-!
# The filtered grid complex

The unblocked grid complex `GC⁻` of `Unblocked.lean` counts the empty rectangles that carry no
`X`-marking. The *filtered* grid complex has the same underlying module, the free module on grid
states over `R[V₀, …, V_{n-1}]`, but its differential

`∂ x = ∑_y ∑_r V^{O(r)} · y`

runs over **all** empty rectangles `r` from `x` to `y`, whatever `X`-markings they cover. The
`X`-markings are not weighted; they are remembered by the Alexander filtration instead, which this
differential respects and whose associated graded complex is `GC⁻`
(`TauCeti.KnotTheory.Grid.Filtered.Alexander`). Ozsváth, Stipsicz and Szabó show that the
filtered chain homotopy type of this complex is a knot invariant; that invariance is not proved
here.

The differential squares to zero in characteristic two, by the juxtaposition argument of the
unblocked complex. Away from the diagonal, the two-step decompositions into empty rectangles pair
off by reordering or recutting, exactly as for `∂⁻`
(`TauCeti.GridRectangleDecomposition.sum_eq_zero_of_pairing`). On the diagonal the count no
longer vanishes term by term: a pair of empty rectangles from `x` back to `x` covers a thin annulus,
and since `X`-markings are allowed every thin annulus is counted. Each thin annulus carries exactly
one `X`-marking, so these are the thin annuli of the `X`-marking homotopies of
`TauCeti.KnotTheory.Grid.XHomotopy.Annulus`. The column annulus of column `c` covers the
`O`-marking of column `c`, and each row annulus covers the `O`-marking of its row, so on a grid of
size at least two the diagonal entry is `2 ∑_c V_c`
(`GridDiagram.sum_filteredCoefficient_mul_filteredCoefficient_self`), which vanishes in
characteristic two.

## Main definitions

* `TauCeti.GridDiagram.filteredCoefficient`: the sum of the weights `V^{O(r)}` of the empty
  rectangles from `x` to `y`.
* `TauCeti.GridDiagram.filteredDifferential`: the filtered grid differential, linear over the
  polynomial ring.

## Main results

* `TauCeti.GridDiagram.filteredCoefficient_eq_unblockedCoefficient_add`: a matrix coefficient of
  the filtered differential is the corresponding coefficient of `∂⁻` plus the weights of the empty
  rectangles covering an `X`-marking.
* `TauCeti.GridDiagram.filteredDifferential_sq_single_apply`: the matrix entries of the square of
  the filtered differential.
* `TauCeti.GridDiagram.sum_filteredCoefficient_mul_filteredCoefficient_self`: on a grid of size at
  least two, every diagonal entry of the square is `2 ∑_c V_c`.
* `TauCeti.GridDiagram.filteredDifferential_comp_self_eq_zero`: in characteristic two the filtered
  differential squares to zero.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 13 (the filtered grid complex) and Chapter 4.6 (the
  juxtaposition argument for `∂² = 0`).
* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), [arXiv:math/0610559](https://arxiv.org/abs/math/0610559), Section 2.
-/

public section

namespace TauCeti

open MvPolynomial GridRectangleBetween GridTwoStepDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-! ### The matrix coefficients -/

/-- The matrix coefficient of the filtered grid differential from `x` to `y`: the sum of the
weights `V^{O(r)}` of all empty rectangles from `x` to `y`, including those covering
`X`-markings. -/
noncomputable def filteredCoefficient (x y : GridState n) : MvPolynomial (Fin n) R :=
  ∑ r ∈ emptyRectangles x y, G.OMonomial R r.toGridRectangle

theorem filteredCoefficient_def (x y : GridState n) :
    G.filteredCoefficient R x y = ∑ r ∈ emptyRectangles x y, G.OMonomial R r.toGridRectangle :=
  (rfl)

/-- The filtered differential has no diagonal matrix coefficient. -/
@[simp]
theorem filteredCoefficient_self (x : GridState n) : G.filteredCoefficient R x x = 0 := by
  rw [filteredCoefficient_def, emptyRectangles_self, Finset.sum_empty]

/-- A matrix coefficient of the filtered differential is the corresponding coefficient of the
unblocked differential `∂⁻`, which counts the empty rectangles covering no `X`-marking, plus the
weights of the empty rectangles covering at least one `X`-marking. -/
theorem filteredCoefficient_eq_unblockedCoefficient_add (x y : GridState n) :
    G.filteredCoefficient R x y = G.unblockedCoefficient R x y +
      ∑ r ∈ (emptyRectangles x y).filter
          (fun r => ¬Disjoint r.toGridRectangle.coveredSquares G.XSet),
        G.OMonomial R r.toGridRectangle := by
  classical
  have h : G.unblockedRectangles x y = (emptyRectangles x y).filter
      (fun r => Disjoint r.toGridRectangle.coveredSquares G.XSet) := by
    ext r
    rw [mem_unblockedRectangles, Finset.mem_filter, mem_emptyRectangles]
  rw [filteredCoefficient_def, unblockedCoefficient_def, h, Finset.sum_filter_add_sum_filter_not]

/-! ### The filtered differential -/

/-- The filtered grid differential, as a linear map on `GC⁻` over the polynomial ring: its matrix
coefficient from `x` to `y` is `TauCeti.GridDiagram.filteredCoefficient`. -/
noncomputable def filteredDifferential :
    GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n :=
  Finsupp.linearCombination (MvPolynomial (Fin n) R) fun x =>
    Finsupp.equivFunOnFinite.symm (G.filteredCoefficient R x)

/-- The matrix coefficients of the filtered differential. -/
@[simp]
theorem filteredDifferential_single_apply (x y : GridState n) (p : MvPolynomial (Fin n) R) :
    G.filteredDifferential R (Finsupp.single x p) y = p * G.filteredCoefficient R x y := by
  simp [filteredDifferential]

/-- The coefficient formula for the filtered differential on an arbitrary chain. -/
theorem filteredDifferential_apply_apply (c : GridChainMinus R n) (y : GridState n) :
    G.filteredDifferential R c y = c.sum fun x p => p * G.filteredCoefficient R x y := by
  simp [filteredDifferential, Finsupp.linearCombination_apply, Finsupp.sum_apply]

/-- The matrix of the square of the filtered differential: its `(x, z)` entry is the sum over
intermediate grid states of the products of the two matrix coefficients. -/
theorem filteredDifferential_sq_single_apply (x z : GridState n) :
    G.filteredDifferential R (G.filteredDifferential R (Finsupp.single x 1)) z =
      ∑ y, G.filteredCoefficient R x y * G.filteredCoefficient R y z := by
  rw [filteredDifferential_apply_apply, Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp

/-! ### The square of the filtered differential -/

/-- An entry of the square of the filtered differential is the sum of the weights of the two-step
decompositions into empty rectangles. -/
private theorem sum_filteredCoefficient_mul_filteredCoefficient (x z : GridState n) :
    ∑ y, G.filteredCoefficient R x y * G.filteredCoefficient R y z =
      ∑ D ∈ decompositionsOf emptyRectangles emptyRectangles x z,
        G.unblockedDecompositionWeight R D := by
  simp only [unblockedDecompositionWeight_def]
  rw [sum_decompositionsOf emptyRectangles emptyRectangles
    fun _ r₁ r₂ => G.OMonomial R r₁.toGridRectangle * G.OMonomial R r₂.toGridRectangle]
  simp only [filteredCoefficient_def, Finset.sum_mul_sum]

/-- Off the diagonal, the two-step decompositions into empty rectangles cancel in pairs in
characteristic two. -/
private theorem sum_decompositionsOf_emptyRectangles_eq_zero [CharP R 2] {x z : GridState n}
    (hzx : z ≠ x) :
    ∑ D ∈ decompositionsOf emptyRectangles emptyRectangles x z,
      G.unblockedDecompositionWeight R D = 0 := by
  refine GridRectangleDecomposition.sum_eq_zero_of_pairing hzx (fun D hD => ?_)
    (fun D hD h => ?_) (fun D _ hone hfirst hsecond => ?_) _
    (fun D _ h => ?_) (fun D _ hone hfirst hsecond => ?_)
  · simpa only [mem_decompositionsOf, mem_emptyRectangles] using hD
  · rw [mem_decompositionsOf, mem_emptyRectangles, mem_emptyRectangles] at hD ⊢
    exact ⟨D.isEmpty_commute_first h hD.1 hD.2, D.isEmpty_commute_second h hD.1 hD.2⟩
  · rw [mem_decompositionsOf, mem_emptyRectangles, mem_emptyRectangles]
    exact ⟨(D.isRecut_recut hone hfirst hsecond).isEmpty_first,
      (D.isRecut_recut hone hfirst hsecond).isEmpty_second⟩
  · rw [G.unblockedDecompositionWeight_commute R D]
    exact CharTwo.add_self_eq_zero _
  · rw [G.unblockedDecompositionWeight_recut R D]
    exact CharTwo.add_self_eq_zero _

/-- A pair of empty rectangles returning to its source covers a thin annulus, which carries exactly
one `X`-marking; so it is counted by `∂⁻ ∘ H_k + H_k ∘ ∂⁻` for the `X`-marking `X_k` of that
annulus. -/
private theorem exists_mem_XHomotopyDecompositions {x : GridState n}
    {D : GridRectangleDecomposition x x} (h₁ : D.first.IsEmpty) (h₂ : D.second.IsEmpty) :
    ∃ k, D ∈ G.XHomotopyDecompositions k x x := by
  have hD := D.first.disjoint_coveredSquares D.second
  rcases (D.first.isEmpty_and_isEmpty_iff D.second).mp ⟨h₁, h₂⟩ with
    ⟨hleft, hright⟩ | ⟨hleft, htop⟩
  · -- a thin column annulus, through the `X`-marking of its column
    refine ⟨D.first.left,
      (G.mem_XHomotopyDecompositions_iff_of_disjoint _ D hD).mpr ⟨h₁, h₂, ?_⟩⟩
    have hcol : D.first.toGridRectangle.coveredColumns = {D.first.left} := by
      rw [GridRectangle.coveredColumns_def, toGridRectangle_left, toGridRectangle_right,
        Grid.cIco_eq_singleton_iff]
      exact ⟨rfl, hright, D.first.left_ne_right⟩
    rw [coveredSquares_union_coveredSquares_of_left_eq_left _ _ hleft, hcol]
    ext p
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
      and_true, mem_XSet, Prod.ext_iff]
    constructor
    · rintro ⟨h, hX⟩
      exact ⟨h, h ▸ hX.symm⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, by rw [h, h']⟩
  · -- a thin row annulus, through the `X`-marking of its row
    refine ⟨G.X.transpose D.first.bottom,
      (G.mem_XHomotopyDecompositions_iff_of_disjoint _ D hD).mpr ⟨h₁, h₂, ?_⟩⟩
    have hrow : D.first.toGridRectangle.coveredRows = {D.first.bottom} := by
      rw [GridRectangle.coveredRows_def, toGridRectangle_bottom, toGridRectangle_top,
        Grid.cIco_eq_singleton_iff]
      exact ⟨rfl, htop, D.first.bottom_ne_top⟩
    rw [coveredSquares_union_coveredSquares_of_left_eq_right _ _ hleft, hrow,
      GridState.apply_transpose_apply]
    ext p
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
      true_and, mem_XSet, Prod.ext_iff]
    constructor
    · rintro ⟨h, hX⟩
      exact ⟨by rw [← h, ← hX, GridState.transpose_apply_apply], h⟩
    · rintro ⟨h, h'⟩
      exact ⟨h', by rw [h, h', GridState.apply_transpose_apply]⟩

/-- A decomposition from `x` back to `x` is counted for at most one `X`-marking homotopy. -/
private theorem disjoint_XHomotopyDecompositions_self {x : GridState n} {k k' : Fin n}
    (h : k ≠ k') :
    Disjoint (G.XHomotopyDecompositions k x x) (G.XHomotopyDecompositions k' x x) := by
  rw [Finset.disjoint_left]
  intro D hk hk'
  have hD := D.first.disjoint_coveredSquares D.second
  have e := ((G.mem_XHomotopyDecompositions_iff_of_disjoint k D hD).mp hk).2.2
  have e' := ((G.mem_XHomotopyDecompositions_iff_of_disjoint k' D hD).mp hk').2.2
  rw [e] at e'
  exact h (Prod.ext_iff.mp (Finset.singleton_injective e')).1

/-- The decompositions from `x` back to `x` into empty rectangles are the thin annuli, sorted by
the `X`-marking each one carries. -/
private theorem decompositionsOf_emptyRectangles_self (x : GridState n) :
    decompositionsOf emptyRectangles emptyRectangles x x =
      Finset.univ.biUnion fun k => G.XHomotopyDecompositions k x x := by
  ext D
  simp only [mem_decompositionsOf, mem_emptyRectangles, Finset.mem_biUnion, Finset.mem_univ,
    true_and]
  exact ⟨fun h => G.exists_mem_XHomotopyDecompositions h.1 h.2,
    fun ⟨_, hk⟩ => G.isEmpty_of_mem_XHomotopyDecompositions hk⟩

/-- **The diagonal of the square of the filtered differential.** On a grid of size at least two,
every diagonal entry of the square of the filtered differential is `2 ∑_c V_c`: the pairs of empty
rectangles from `x` back to `x` are the `n` thin column annuli and the `n` thin row annuli, the
column annulus of column `c` covers the `O`-marking of column `c`, and the row annuli cover the
`O`-markings of all rows. -/
theorem sum_filteredCoefficient_mul_filteredCoefficient_self (hn : 1 < n) (x : GridState n) :
    ∑ y, G.filteredCoefficient R x y * G.filteredCoefficient R y x = 2 * ∑ c, MvPolynomial.X c := by
  rw [G.sum_filteredCoefficient_mul_filteredCoefficient R, G.decompositionsOf_emptyRectangles_self,
    Finset.sum_biUnion fun k _ k' _ h => G.disjoint_XHomotopyDecompositions_self h]
  simp only [G.sum_XHomotopyDecompositions_self R hn, Finset.sum_add_distrib]
  have hrow : ∑ k, (MvPolynomial.X (G.O.transpose (G.X k)) : MvPolynomial (Fin n) R) =
      ∑ c, MvPolynomial.X c :=
    Equiv.sum_comp (G.X.toPerm.trans G.O.transpose.toPerm) fun c => MvPolynomial.X c
  rw [hrow, two_mul]

variable [CharP R 2]

/-- In characteristic two every matrix entry of the square of the filtered differential
vanishes. -/
theorem sum_filteredCoefficient_mul_filteredCoefficient_eq_zero (x z : GridState n) :
    ∑ y, G.filteredCoefficient R x y * G.filteredCoefficient R y z = 0 := by
  rcases eq_or_ne z x with rfl | hzx
  · rcases lt_or_ge 1 n with hn | hn
    · rw [G.sum_filteredCoefficient_mul_filteredCoefficient_self R hn, CharTwo.two_eq_zero,
        zero_mul]
    · -- On a grid of size at most one there are no rectangles at all.
      have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn
      refine Finset.sum_eq_zero fun y _ => ?_
      have : IsEmpty (GridRectangleBetween z y) :=
        ⟨fun r => r.left_ne_right (Subsingleton.elim _ _)⟩
      rw [filteredCoefficient_def, Finset.eq_empty_of_isEmpty (emptyRectangles z y),
        Finset.sum_empty, zero_mul]
  · rw [G.sum_filteredCoefficient_mul_filteredCoefficient R]
    exact G.sum_decompositionsOf_emptyRectangles_eq_zero R hzx

/-- **The filtered grid differential squares to zero** in characteristic two. -/
theorem filteredDifferential_comp_self_eq_zero :
    G.filteredDifferential R ∘ₗ G.filteredDifferential R =
      (0 : GridChainMinus R n →ₗ[MvPolynomial (Fin n) R] GridChainMinus R n) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring (Finsupp.ext fun z => ?_)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
    filteredDifferential_sq_single_apply, G.sum_filteredCoefficient_mul_filteredCoefficient_eq_zero]
  rfl

end GridDiagram

end TauCeti
