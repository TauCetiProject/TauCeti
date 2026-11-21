/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.DirectSum.Module
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.KnotTheory.Grid.Diagram.Components
public import TauCeti.KnotTheory.Grid.Unblocked
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# The Alexander multigrading of a grid diagram

A grid diagram `G` of size `n` presenting an `ℓ`-component link has one Alexander grading for each
link component. For a component `q`, write `𝕏_q` and `𝕆_q` for the `X`- and `O`-markings on `q`
and `n_q` for the number of `O`-markings on `q`. The `q`-th Alexander grading of a grid state `x`
is

`A_q(x) = J(x - ½(𝕏 + 𝕆), 𝕏_q - 𝕆_q) - (n_q - 1) / 2`,

with `J` extended bilinearly to formal sums of grid points and marked squares
(`GridDiagram.componentAlexander`). In the formula, `J(x, 𝕏_q)` pairs the points of `x` with the
centres of the marked squares, which is `GridPoint.JCenter`, while the pairings among markings
compare marked squares with marked squares and so may use their lower-left corners.

The multigrading refines the single Alexander grading `GridDiagram.alexander` of
`Gradings.lean`, but with the link normalization: the sum of the component gradings is

`∑_q A_q(x) = J(x - ½(𝕏 + 𝕆), 𝕏 - 𝕆) - (n - ℓ) / 2 = A(x) + (ℓ - 1) / 2`

(`GridDiagram.sum_componentAlexander`), since `A` carries the knot shift `(n - 1) / 2`. For a knot
there is a single component and `A_q = A` (`GridDiagram.IsKnot.componentAlexander_eq`).

Across a rectangle `r` from `x` to `y` the `q`-th grading changes by the markings of `q` that `r`
covers, `A_q(x) - A_q(y) = #(𝕏_q ∩ r) - #(𝕆_q ∩ r)`
(`GridDiagram.componentAlexander_sub_componentAlexander_eq_card_sub_card`). Each column and each
row carries either no marking of `q` or exactly one `X`-marking and one `O`-marking of `q`,
because the component permutation `c ↦ X⁻¹(O(c))` stays on `q`; so the weight `𝕏_q - 𝕆_q` has
vanishing column and row sums, and `GridRectangleBetween.JWeight_sub_JWeight_eq_sum` applies.

On the unblocked complex `GC⁻`, the variable `V_c` has multidegree `-e_q` for the component `q`
of column `c`, so the monomial `V^e · x` has `q`-th Alexander grading
`A_q(x) - ∑_{c ∈ q} e_c` (`GridDiagram.monomialComponentAlexander`). The unblocked differential
counts rectangles with no `X`-marking and weights each by the variables of the `O`-markings it
covers, so it preserves every component grading
(`GridDiagram.unblockedDifferential_mem_componentAlexanderChainMinusPiece`). The gradings are
rational and, for a link, need not be integers (Manolescu, Ozsváth, Szabó and Thurston place
`A_q` in `ℤ + lk(L_q, L ∖ L_q) / 2`), so the multidegrees are valued in `ℚ` and no integrality is
claimed here.

## Main definitions

* `TauCeti.GridDiagram.componentColumns`, `TauCeti.GridDiagram.componentXSet`,
  `TauCeti.GridDiagram.componentOSet`: the columns and the marked squares of one link component.
* `TauCeti.GridDiagram.componentAlexander`: the Alexander grading `A_q` of a link component `q`.
* `TauCeti.GridDiagram.monomialComponentAlexander`: the Alexander multidegree of a monomial
  `V^e · x` of `GC⁻`.
* `TauCeti.GridDiagram.componentAlexanderChainMinusPiece`: the chains of `GC⁻` homogeneous of a
  given Alexander multidegree.
* `TauCeti.GridDiagram.componentAlexanderChainMinusGrading`: the Alexander multigrading of `GC⁻`
  as an internal grading over the coefficient ring.

## Main results

* `TauCeti.GridDiagram.sum_componentAlexander`: the component gradings sum to the Alexander
  grading plus `(ℓ - 1) / 2`.
* `TauCeti.GridDiagram.IsKnot.componentAlexander_eq`: for a knot the component grading is the
  Alexander grading.
* `TauCeti.GridDiagram.componentAlexander_sub_componentAlexander_eq_card_sub_card`: the change of
  a component grading across a rectangle counts the covered markings of that component.
* `TauCeti.GridDiagram.unblockedDifferential_mem_componentAlexanderChainMinusPiece`: the unblocked
  differential preserves the Alexander multidegree.
* `TauCeti.GridDiagram.X_smul_mem_componentAlexanderChainMinusPiece`: the variable `V_c` lowers
  the grading of the component of `c` by one and preserves the others.
* `TauCeti.GridDiagram.iSup_componentAlexanderChainMinusPiece_eq_top`,
  `TauCeti.GridDiagram.iSupIndep_componentAlexanderChainMinusPiece`: `GC⁻` is the direct sum of its
  multigraded pieces.

## References

* C. Manolescu, P. Ozsváth, Z. Szabó, D. Thurston, *On combinatorial link Floer homology*,
  Geom. Topol. 11 (2007), [arXiv:math/0610559](https://arxiv.org/abs/math/0610559), Section 2:
  the Alexander multigrading `A_i` of a grid state.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 11.1: the Alexander multigrading of the grid complex of a
  link and its relation to the single Alexander grading.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### The columns and markings of one component -/

/-- The columns whose markings lie on the link component `q`. -/
def componentColumns (q : G.Components) : Finset (Fin n) :=
  Finset.univ.filter fun c => G.componentOfColumn c = q

/-- A column lies on a component exactly when its component is that component. -/
@[simp]
theorem mem_componentColumns {q : G.Components} {c : Fin n} :
    c ∈ G.componentColumns q ↔ G.componentOfColumn c = q := by
  simp [componentColumns]

/-- The `X`-marked squares on the link component `q`. -/
def componentXSet (q : G.Components) : Finset (Fin n × Fin n) :=
  G.XSet.filter fun p => G.componentOfColumn p.1 = q

/-- A square is an `X`-marking of a component exactly when it is an `X`-marking whose column lies
on that component. -/
@[simp]
theorem mem_componentXSet {q : G.Components} {p : Fin n × Fin n} :
    p ∈ G.componentXSet q ↔ G.X p.1 = p.2 ∧ G.componentOfColumn p.1 = q := by
  simp [componentXSet]

/-- The `O`-marked squares on the link component `q`. -/
def componentOSet (q : G.Components) : Finset (Fin n × Fin n) :=
  G.OSet.filter fun p => G.componentOfColumn p.1 = q

/-- A square is an `O`-marking of a component exactly when it is an `O`-marking whose column lies
on that component. -/
@[simp]
theorem mem_componentOSet {q : G.Components} {p : Fin n × Fin n} :
    p ∈ G.componentOSet q ↔ G.O p.1 = p.2 ∧ G.componentOfColumn p.1 = q := by
  simp [componentOSet]

/-- The `X`-marking and the `O`-marking of a row lie on the same component: the component
permutation carries the column of the `O`-marking to the column of the `X`-marking. -/
theorem componentOfColumn_X_transpose (r : Fin n) :
    G.componentOfColumn (G.X.transpose r) = G.componentOfColumn (G.O.transpose r) := by
  have h : G.componentPerm (G.O.transpose r) = G.X.transpose r := by
    rw [componentPerm_apply_eq_iff, GridState.apply_transpose_apply,
      GridState.apply_transpose_apply]
  rw [← h, componentOfColumn_eq_iff]
  exact (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- The component grid sizes `n_q` add up to the grid size. -/
theorem sum_card_componentColumns : ∑ q, (G.componentColumns q).card = n := by
  simp only [componentColumns]
  rw [← Finset.card_eq_sum_card_fiberwise (fun c _ => Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]

/-- A pairing that is the sum of its values on the single points of a point set is the sum of its
values on the parts of the point set lying over each component. -/
private theorem sum_filter_componentOfColumn (F : Finset (Fin n × Fin n) → ℚ)
    (hF : ∀ t, F t = ∑ p ∈ t, F {p}) (t : Finset (Fin n × Fin n)) :
    ∑ q, F (t.filter fun p => G.componentOfColumn p.1 = q) = F t := by
  rw [Finset.sum_congr rfl fun q _ => hF _, hF t]
  exact Finset.sum_fiberwise t (fun p => G.componentOfColumn p.1) fun p => F {p}

/-- The `J`-pairing with the `X`-markings is the sum of the pairings with the `X`-markings of each
component. -/
theorem sum_J_componentXSet (s : Finset (Fin n × Fin n)) :
    ∑ q, GridPoint.J s (G.componentXSet q) = GridPoint.J s G.XSet :=
  G.sum_filter_componentOfColumn _ (GridPoint.J_eq_sum_singleton_right s) _

/-- The `J`-pairing with the `O`-markings is the sum of the pairings with the `O`-markings of each
component. -/
theorem sum_J_componentOSet (s : Finset (Fin n × Fin n)) :
    ∑ q, GridPoint.J s (G.componentOSet q) = GridPoint.J s G.OSet :=
  G.sum_filter_componentOfColumn _ (GridPoint.J_eq_sum_singleton_right s) _

/-- The pairing of a point set with the centres of the `X`-markings is the sum of its pairings with
the `X`-markings of each component. -/
theorem sum_JCenter_componentXSet (s : Finset (Fin n × Fin n)) :
    ∑ q, GridPoint.JCenter s (G.componentXSet q) = GridPoint.JCenter s G.XSet :=
  G.sum_filter_componentOfColumn _ (GridPoint.JCenter_eq_sum_singleton_right s) _

/-- The pairing of a point set with the centres of the `O`-markings is the sum of its pairings with
the `O`-markings of each component. -/
theorem sum_JCenter_componentOSet (s : Finset (Fin n × Fin n)) :
    ∑ q, GridPoint.JCenter s (G.componentOSet q) = GridPoint.JCenter s G.OSet :=
  G.sum_filter_componentOfColumn _ (GridPoint.JCenter_eq_sum_singleton_right s) _

/-! ### The component Alexander gradings -/

/-- The Alexander grading of the link component `q`,
`A_q(x) = J(x - ½(𝕏 + 𝕆), 𝕏_q - 𝕆_q) - (n_q - 1) / 2`.

The points of `x` are paired with the centres of the marked squares of `q`
(`GridPoint.JCenter`); the markings are paired with each other through the lower-left corners of
their squares, which gives the same value since both are translated by the same vector. -/
def componentAlexander (q : G.Components) (x : GridState n) : ℚ :=
  GridPoint.JCenter x.pointSet (G.componentXSet q) -
      GridPoint.JCenter x.pointSet (G.componentOSet q) -
    (GridPoint.J G.XSet (G.componentXSet q) - GridPoint.J G.XSet (G.componentOSet q) +
        GridPoint.J G.OSet (G.componentXSet q) - GridPoint.J G.OSet (G.componentOSet q)) / 2 -
    (((G.componentColumns q).card : ℚ) - 1) / 2

/-- The component Alexander grading as its defining formula. -/
theorem componentAlexander_def (q : G.Components) (x : GridState n) :
    G.componentAlexander q x =
      GridPoint.JCenter x.pointSet (G.componentXSet q) -
          GridPoint.JCenter x.pointSet (G.componentOSet q) -
        (GridPoint.J G.XSet (G.componentXSet q) - GridPoint.J G.XSet (G.componentOSet q) +
            GridPoint.J G.OSet (G.componentXSet q) - GridPoint.J G.OSet (G.componentOSet q)) / 2 -
        (((G.componentColumns q).card : ℚ) - 1) / 2 :=
  (rfl)

/-- **The component gradings sum to the Alexander grading with the link normalization.** The sum
of the Alexander gradings of the components is `J(x - ½(𝕏 + 𝕆), 𝕏 - 𝕆) - (n - ℓ) / 2`, which is
the Alexander grading `A(x)`, normalized by the knot shift `(n - 1) / 2`, plus `(ℓ - 1) / 2`. -/
theorem sum_componentAlexander (x : GridState n) :
    ∑ q, G.componentAlexander q x = G.alexander x + ((G.componentCount : ℚ) - 1) / 2 := by
  have hcard : ∑ q, (((G.componentColumns q).card : ℚ) - 1) = (n : ℚ) - G.componentCount := by
    rw [Finset.sum_sub_distrib, ← Nat.cast_sum, sum_card_componentColumns, Finset.sum_const,
      Finset.card_univ, card_components, nsmul_eq_mul, mul_one]
  simp only [componentAlexander_def, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, sum_JCenter_componentXSet, sum_JCenter_componentOSet, sum_J_componentXSet,
    sum_J_componentOSet, hcard]
  rw [alexander_eq, JX_def, JO_def, GridState.J_def, GridState.J_def, ← XSet_def, ← OSet_def,
    GridPoint.J_comm G.XSet G.OSet]
  push_cast
  ring

/-- **For a knot the component grading is the Alexander grading.** A knot grid has a single
component, whose Alexander grading is `A`. -/
theorem IsKnot.componentAlexander_eq {G : GridDiagram n} (hG : G.IsKnot) (q : G.Components)
    (x : GridState n) : G.componentAlexander q x = G.alexander x := by
  have hcard : Fintype.card G.Components = 1 := by
    rw [card_components]
    exact (G.isKnot_def).mp hG
  have : Subsingleton G.Components := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  have h := G.sum_componentAlexander x
  rw [Fintype.sum_subsingleton _ q, (G.isKnot_def).mp hG] at h
  rw [h]
  norm_num

/-! ### The change across a rectangle -/

/-- The weight `𝕏_q - 𝕆_q` of a component on the squares of the grid. -/
private def componentWeight (q : G.Components) (p : Fin n × Fin n) : ℤ :=
  (if p ∈ G.componentXSet q then 1 else 0) - (if p ∈ G.componentOSet q then 1 else 0)

/-- Every column carries the same number of `X`- and `O`-markings of a component. -/
private theorem sum_componentWeight_column (q : G.Components) (c : Fin n) :
    ∑ r, G.componentWeight q (c, r) = 0 := by
  simp [componentWeight, Finset.sum_sub_distrib, ite_and]

/-- Every row carries the same number of `X`- and `O`-markings of a component. -/
private theorem sum_componentWeight_row (q : G.Components) (r : Fin n) :
    ∑ c, G.componentWeight q (c, r) = 0 := by
  have hX (c : Fin n) : G.X c = r ↔ c = G.X.transpose r :=
    ⟨fun h => by rw [← h, GridState.transpose_apply_apply],
      fun h => by rw [h, GridState.apply_transpose_apply]⟩
  have hO (c : Fin n) : G.O c = r ↔ c = G.O.transpose r :=
    ⟨fun h => by rw [← h, GridState.transpose_apply_apply],
      fun h => by rw [h, GridState.apply_transpose_apply]⟩
  have h := G.componentOfColumn_X_transpose r
  simp only [componentWeight, mem_componentXSet, hX, GridState.transpose_apply, ite_and,
    mem_componentOSet, hO, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [GridState.transpose_apply] at h
  rw [h, sub_self]

/-- The pairing of a grid state with the component weight is the difference of its pairings with
the `X`- and `O`-markings of the component. -/
private theorem JWeight_componentWeight (q : G.Components) (x : GridState n) :
    x.JWeight (G.componentWeight q) =
      GridPoint.JCenter x.pointSet (G.componentXSet q) -
        GridPoint.JCenter x.pointSet (G.componentOSet q) := by
  rw [GridState.JWeight_def, GridPoint.JCenter_eq_sum_singleton_right _ (G.componentXSet q),
    GridPoint.JCenter_eq_sum_singleton_right _ (G.componentOSet q)]
  simp only [componentWeight, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter]

/-- **The change of a component grading across a rectangle.** If `r` is a rectangle from `x` to
`y`, then `A_q(x) - A_q(y)` is the number of `X`-markings of `q` that `r` covers minus the number
of `O`-markings of `q` that it covers. -/
theorem componentAlexander_sub_componentAlexander_eq_card_sub_card (q : G.Components)
    {x y : GridState n} (R : GridRectangleBetween x y) :
    G.componentAlexander q x - G.componentAlexander q y =
      ((G.componentXSet q ∩ R.toGridRectangle.coveredSquares).card : ℚ) -
        ((G.componentOSet q ∩ R.toGridRectangle.coveredSquares).card : ℚ) := by
  have h := R.JWeight_sub_JWeight_eq_sum (G.sum_componentWeight_column q)
    (G.sum_componentWeight_row q)
  rw [JWeight_componentWeight, JWeight_componentWeight] at h
  have hsum : ∑ p ∈ R.toGridRectangle.coveredSquares, (G.componentWeight q p : ℚ) =
      ((G.componentXSet q ∩ R.toGridRectangle.coveredSquares).card : ℚ) -
        ((G.componentOSet q ∩ R.toGridRectangle.coveredSquares).card : ℚ) := by
    simp only [componentWeight, Int.cast_sub, Finset.sum_sub_distrib, Int.cast_ite, Int.cast_one,
      Int.cast_zero, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [componentAlexander_def, componentAlexander_def, ← hsum, ← h]
  ring

/-- The `O`-markings of a component covered by a rectangle are indexed by the covered `O`-columns
on that component. -/
theorem card_componentOSet_inter_coveredSquares (q : G.Components) (r : GridRectangle n) :
    (G.componentOSet q ∩ r.coveredSquares).card = (G.componentColumns q ∩ G.OColumns r).card := by
  refine Finset.card_bij (fun p _ => p.1) (fun p hp => ?_) (fun p hp p' hp' h => ?_)
    (fun c hc => ?_)
  · simp only [Finset.mem_inter, mem_componentOSet, mem_componentColumns, mem_OColumns] at hp ⊢
    obtain ⟨⟨hO, hq⟩, hr⟩ := hp
    exact ⟨hq, by rwa [hO]⟩
  · simp only [Finset.mem_inter, mem_componentOSet] at hp hp'
    exact Prod.ext h (by rw [← hp.1.1, ← hp'.1.1, h])
  · simp only [Finset.mem_inter, mem_componentColumns, mem_OColumns] at hc
    exact ⟨(c, G.O c), by simpa [Finset.mem_inter, mem_componentOSet] using hc, rfl⟩

/-- A rectangle with no `X`-marking raises the grading of each component by the number of covered
`O`-markings on it. So, with each variable `V_c` charged `-1` in the grading of the component of
`c`, the term `V^{O(r)} · y` of `∂⁻ x` has the same component gradings as `x`. -/
theorem componentAlexander_sub_card_inter_OColumns_eq (q : G.Components) {x y : GridState n}
    {r : GridRectangleBetween x y} (hr : Disjoint r.toGridRectangle.coveredSquares G.XSet) :
    G.componentAlexander q y -
        ((G.componentColumns q ∩ G.OColumns r.toGridRectangle).card : ℚ) =
      G.componentAlexander q x := by
  have hX : G.componentXSet q ∩ r.toGridRectangle.coveredSquares = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp
      (hr.symm.mono_left (Finset.filter_subset _ _))
  have h := G.componentAlexander_sub_componentAlexander_eq_card_sub_card q r
  rw [hX, Finset.card_empty, Nat.cast_zero, card_componentOSet_inter_coveredSquares] at h
  linarith

/-! ### The Alexander multigrading of `GC⁻` -/

/-- The Alexander multidegree of the monomial `V^e · x` of `GC⁻`: its `q`-th entry is
`A_q(x) - ∑_{c ∈ q} e_c`, so that the variable `V_c` lowers the grading of the component of `c`
by one. -/
def monomialComponentAlexander (x : GridState n) (e : Fin n →₀ ℕ) (q : G.Components) : ℚ :=
  G.componentAlexander q x - ∑ c ∈ G.componentColumns q, (e c : ℚ)

/-- The Alexander multidegree of a monomial as its defining formula. -/
theorem monomialComponentAlexander_apply (x : GridState n) (e : Fin n →₀ ℕ)
    (q : G.Components) :
    G.monomialComponentAlexander x e q =
      G.componentAlexander q x - ∑ c ∈ G.componentColumns q, (e c : ℚ) :=
  (rfl)

/-- A grid state, with the trivial monomial, has multidegree its component gradings. -/
@[simp]
theorem monomialComponentAlexander_zero (x : GridState n) :
    G.monomialComponentAlexander x 0 = fun q => G.componentAlexander q x := by
  funext q
  simp [monomialComponentAlexander_apply]

/-- The entries of the Alexander multidegree of a monomial add up to its Alexander grading
`A(x) - |e|`, plus the link correction `(ℓ - 1) / 2`. -/
theorem sum_monomialComponentAlexander (x : GridState n) (e : Fin n →₀ ℕ) :
    ∑ q, G.monomialComponentAlexander x e q =
      G.alexander x - (e.degree : ℚ) + ((G.componentCount : ℚ) - 1) / 2 := by
  have he : ∑ q, ∑ c ∈ G.componentColumns q, (e c : ℚ) = (e.degree : ℚ) := by
    rw [Finsupp.degree_eq_sum, Nat.cast_sum]
    exact Finset.sum_fiberwise Finset.univ G.componentOfColumn fun c => (e c : ℚ)
  simp only [monomialComponentAlexander_apply, Finset.sum_sub_distrib, sum_componentAlexander, he]
  ring

/-- Multiplying the monomial `V^e · x` by the variable `V_i` lowers the grading of the component
of the column `i` by one and preserves the other entries of the multidegree. -/
theorem monomialComponentAlexander_single_add (x : GridState n) (i : Fin n)
    (e : Fin n →₀ ℕ) :
    G.monomialComponentAlexander x (Finsupp.single i 1 + e) =
      G.monomialComponentAlexander x e - Pi.single (G.componentOfColumn i) 1 := by
  funext q
  simp only [monomialComponentAlexander_apply, Pi.sub_apply, Finsupp.add_apply, Nat.cast_add,
    Finset.sum_add_distrib, Finsupp.single_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_ite_eq, mem_componentColumns, Pi.single_apply]
  by_cases h : q = G.componentOfColumn i
  · subst h
    simp only [ite_true, add_comm (1 : ℚ)]
    ring
  · simp [h, Ne.symm h]

/-- Passing along a rectangle counted by the unblocked differential and multiplying by its weight
`V^{O(r)}` preserves the Alexander multidegree. -/
theorem monomialComponentAlexander_add_of_mem_unblockedRectangles {x y : GridState n}
    {r : GridRectangleBetween x y} (hr : r ∈ G.unblockedRectangles x y) (e : Fin n →₀ ℕ) :
    G.monomialComponentAlexander y
        (e + ∑ c ∈ G.OColumns r.toGridRectangle, Finsupp.single c 1) =
      G.monomialComponentAlexander x e := by
  funext q
  have hA := G.componentAlexander_sub_card_inter_OColumns_eq q
    (G.disjoint_XSet_of_mem_unblockedRectangles hr)
  have hO : ∑ c ∈ G.componentColumns q,
      ((∑ d ∈ G.OColumns r.toGridRectangle, Finsupp.single d 1 : Fin n →₀ ℕ) c : ℚ) =
        ((G.componentColumns q ∩ G.OColumns r.toGridRectangle).card : ℚ) := by
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, Finset.sum_boole, Finset.filter_mem_eq_inter]
  simp only [monomialComponentAlexander_apply, Finsupp.add_apply, Nat.cast_add,
    Finset.sum_add_distrib, hO]
  linarith

/-- The chains of `GC⁻` all of whose monomials have Alexander multidegree in a prescribed set.
Only singletons and complements of singletons are used: the first are the homogeneous pieces, and
comparing against the second makes the pieces independent. -/
private def componentAlexanderChainMinusSupported (R : Type*) [CommSemiring R]
    (S : Set (G.Components → ℚ)) : Submodule R (GridChainMinus R n) where
  carrier := {c | ∀ x : GridState n, ∀ e ∈ (c x).support, G.monomialComponentAlexander x e ∈ S}
  add_mem' {c d} hc hd x e he := by
    classical
    rw [Finsupp.add_apply] at he
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
    · exact hc x e h
    · exact hd x e h
  zero_mem' x e he := by simp at he
  smul_mem' b c hc x e he := by
    rw [Finsupp.smul_apply] at he
    exact hc x e (MvPolynomial.support_smul he)

/-- The chains of `GC⁻` homogeneous of Alexander multidegree `a`: those all of whose monomials
`V^e · x` have multidegree `a`.

The variables move the multidegree, so this is a submodule over the coefficient ring `R` only. -/
def componentAlexanderChainMinusPiece (R : Type*) [CommSemiring R] (a : G.Components → ℚ) :
    Submodule R (GridChainMinus R n) :=
  G.componentAlexanderChainMinusSupported R {a}

/-- A chain of `GC⁻` is homogeneous of Alexander multidegree `a` exactly when every monomial
occurring in it has multidegree `a`. -/
@[simp]
theorem mem_componentAlexanderChainMinusPiece {R : Type*} [CommSemiring R]
    {a : G.Components → ℚ} {c : GridChainMinus R n} :
    c ∈ G.componentAlexanderChainMinusPiece R a ↔
      ∀ x : GridState n, ∀ e ∈ (c x).support, G.monomialComponentAlexander x e = a :=
  Iff.rfl

/-- A single monomial `V^e · x` is homogeneous of its own Alexander multidegree. -/
theorem single_monomial_mem_componentAlexanderChainMinusPiece (R : Type*) [CommSemiring R]
    (x : GridState n) (e : Fin n →₀ ℕ) (b : R) :
    Finsupp.single x (monomial e b) ∈
      G.componentAlexanderChainMinusPiece R (G.monomialComponentAlexander x e) := by
  classical
  intro y f hf
  rw [Finsupp.single_apply] at hf
  split_ifs at hf with h
  · subst h
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hf)]
    exact Set.mem_singleton _
  · simp at hf

/-- **The unblocked grid differential preserves the Alexander multidegree.** -/
theorem unblockedDifferential_mem_componentAlexanderChainMinusPiece {R : Type*} [CommSemiring R]
    {a : G.Components → ℚ} {c : GridChainMinus R n}
    (hc : c ∈ G.componentAlexanderChainMinusPiece R a) :
    G.unblockedDifferential R c ∈ G.componentAlexanderChainMinusPiece R a := by
  classical
  intro z f hf
  rw [unblockedDifferential_apply_apply, Finsupp.sum] at hf
  obtain ⟨w, -, hfw⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hf)
  obtain ⟨e, he, d, hd, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hfw)
  obtain ⟨r, hr, rfl⟩ := G.exists_mem_unblockedRectangles_of_mem_support_unblockedCoefficient R hd
  rw [G.monomialComponentAlexander_add_of_mem_unblockedRectangles hr e]
  exact hc w e he

/-- The unblocked grid differential maps each Alexander multigraded piece of `GC⁻` into itself. -/
theorem map_unblockedDifferential_componentAlexanderChainMinusPiece_le (R : Type*)
    [CommSemiring R] (a : G.Components → ℚ) :
    Submodule.map ((G.unblockedDifferential R).restrictScalars R)
        (G.componentAlexanderChainMinusPiece R a) ≤
      G.componentAlexanderChainMinusPiece R a := by
  rintro _ ⟨c, hc, rfl⟩
  exact G.unblockedDifferential_mem_componentAlexanderChainMinusPiece hc

/-- **The variable `V_i` has multidegree `-e_q`** for the component `q` of the column `i`:
multiplying a homogeneous chain by it lowers the grading of that component by one and preserves
the others. -/
theorem X_smul_mem_componentAlexanderChainMinusPiece {R : Type*} [CommSemiring R] (i : Fin n)
    {a : G.Components → ℚ} {c : GridChainMinus R n}
    (hc : c ∈ G.componentAlexanderChainMinusPiece R a) :
    (MvPolynomial.X i : MvPolynomial (Fin n) R) • c ∈
      G.componentAlexanderChainMinusPiece R (a - Pi.single (G.componentOfColumn i) 1) := by
  classical
  intro z f hf
  rw [Finsupp.smul_apply, smul_eq_mul, MvPolynomial.X] at hf
  obtain ⟨b, hb, e, he, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hf)
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb),
    monomialComponentAlexander_single_add, (G.mem_componentAlexanderChainMinusPiece).mp hc z e he]
  exact Set.mem_singleton _

/-! ### `GC⁻` is the direct sum of its multigraded pieces -/

/-- The multigraded pieces of `GC⁻` span it: every chain is a finite sum of monomial multiples of
grid-state generators. -/
theorem iSup_componentAlexanderChainMinusPiece_eq_top (R : Type*) [CommSemiring R] :
    ⨆ a, G.componentAlexanderChainMinusPiece R a = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro c -
  induction c using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add x p c _ _ ih =>
    refine Submodule.add_mem _ ?_ ih
    have hp : (Finsupp.single x p : GridChainMinus R n) =
        ∑ e ∈ p.support, Finsupp.single x (monomial e (p.coeff e)) := by
      conv_lhs => rw [MvPolynomial.as_sum p]
      exact map_sum (Finsupp.singleAddHom x) _ _
    rw [hp]
    exact Submodule.sum_mem _ fun e _ =>
      Submodule.mem_iSup_of_mem (G.monomialComponentAlexander x e)
        (G.single_monomial_mem_componentAlexanderChainMinusPiece R x e _)

/-- The multigraded pieces of `GC⁻` are independent: every monomial of a chain has exactly one
Alexander multidegree. -/
theorem iSupIndep_componentAlexanderChainMinusPiece (R : Type*) [CommSemiring R] :
    iSupIndep (G.componentAlexanderChainMinusPiece R) := by
  intro a
  rw [Submodule.disjoint_def]
  intro c hc hc'
  rw [mem_componentAlexanderChainMinusPiece] at hc
  have hle (b : G.Components → ℚ) (hb : b ≠ a) :
      G.componentAlexanderChainMinusPiece R b ≤ G.componentAlexanderChainMinusSupported R {a}ᶜ :=
    fun d hd z e he => by
      rw [Set.mem_compl_singleton_iff, (mem_componentAlexanderChainMinusPiece G).mp hd z e he]
      exact hb
  have hcompl : c ∈ G.componentAlexanderChainMinusSupported R {a}ᶜ := iSup₂_le hle hc'
  refine Finsupp.ext fun z => ?_
  rw [Finsupp.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  exact fun e he => hcompl z e he (hc z e he)

/-- **The Alexander multigrading of `GC⁻`**: the unblocked grid chain module is the internal direct
sum of its multigraded pieces, as a module over the coefficient ring `R`. -/
def componentAlexanderChainMinusGrading (R : Type*) [CommRing R] :
    InternalGrading R (GridChainMinus R n) (G.Components → ℚ) where
  piece := G.componentAlexanderChainMinusPiece R
  isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (G.iSupIndep_componentAlexanderChainMinusPiece R)
    (G.iSup_componentAlexanderChainMinusPiece_eq_top R)

/-- The pieces of the Alexander multigrading of `GC⁻` are its multigraded pieces. -/
@[simp]
theorem componentAlexanderChainMinusGrading_piece (R : Type*) [CommRing R]
    (a : G.Components → ℚ) :
    (G.componentAlexanderChainMinusGrading R).piece a = G.componentAlexanderChainMinusPiece R a :=
  (rfl)

/-- The unblocked grid differential is homogeneous of degree zero for the Alexander
multigrading. -/
theorem isHomogeneous_unblockedDifferential_componentAlexanderChainMinusGrading (R : Type*)
    [CommRing R] :
    LinearMap.IsHomogeneous (G.unblockedDifferential R)
      (G.componentAlexanderChainMinusGrading R).piece
      (G.componentAlexanderChainMinusGrading R).piece 0 :=
  LinearMap.isHomogeneous_def.mpr fun a _ hc => by
    simpa using G.unblockedDifferential_mem_componentAlexanderChainMinusPiece hc

end GridDiagram

end TauCeti
