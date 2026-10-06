/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.KnotTheory.Grid.Grading.Parity
public import TauCeti.KnotTheory.Grid.Unblocked
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# The bigrading of the unblocked grid complex `GC⁻`

`Unblocked.lean` builds the unblocked grid complex `GC⁻`, the free module on grid states over
`R[V₀, …, V_{n-1}]`, and records how one rectangle counted by its differential moves the two
gradings of a grid state. This file fixes the bigrading those two records were made for and proves
that the unblocked differential is homogeneous for it.

The convention is the standard one: a variable `V_c` sits in `O`-Maslov degree `-2` and Alexander
degree `-1`, so the basis element `V^e · x` has bidegree

`(M_O(x) - 2 |e|, A(x) - |e|)`

for `|e|` the total degree of the exponent vector `e`. This is
`OddComponentGridDiagram.monomialBidegree`; the Alexander grading is an integer exactly for a
diagram with an odd number of link components, which is why the bigraded statements are made for
`OddComponentGridDiagram`, matching `Grading/Chain.lean`. The underlying grading changes are stated
first for an arbitrary grid diagram, in the integer gradings `GridDiagram.maslovOℤ` and
`GridDiagram.alexanderTwoℤ`, where no hypothesis on the component count is needed; they live here
rather than beside their rational counterparts in `Unblocked.lean` because the integer gradings are
not among that file's dependencies.

With that convention the two records of `Unblocked.lean` say exactly that **the unblocked grid
differential has bidegree `(-1, 0)`**: it drops the `O`-Maslov grading by one and preserves the
Alexander grading. That is the convention the roadmap asks to be fixed once and for all before any
grid homology is stated, and it is what makes `GC⁻` a bigraded complex rather than merely a module
carrying a differential.

The homogeneous piece `OddComponentGridDiagram.bigradedChainMinusPiece` is a submodule over the
coefficient ring `R` only, not over `R[V₀, …, V_{n-1}]`: the variables move the bidegree. It
consists of the chains all of whose monomials have the given bidegree, and these pieces make `GC⁻`
an internal direct sum (`OddComponentGridDiagram.isInternal_bigradedChainMinusPiece`). This is not
the decomposition of `Grading/Chain.lean`, which regroups the basis of grid states of the blocked
chain module `GridChain R n` by bidegree over an arbitrary coefficient ring: over the polynomial
ring a basis element is a monomial *times* a grid state, and its bidegree depends on both, so what
is graded here is `GC⁻` itself and the pieces are submodules of it.

Forgetting the `O`-Maslov component gives the Alexander grading of `GC⁻`
(`OddComponentGridDiagram.alexanderChainMinusGrading`), an internal grading over `R` which `∂⁻`
preserves and in which each variable `V_c` has degree `-1`. This is the grading that descends to
the unblocked grid homology `GH⁻` and in which the concordance invariant `τ` is read off.

## Main definitions

* `TauCeti.OddComponentGridDiagram.monomialBidegree`: the bidegree of the basis element `V^e · x`
  of `GC⁻`.
* `TauCeti.OddComponentGridDiagram.bigradedChainMinusPiece`: the homogeneous piece of `GC⁻` in one
  bidegree.
* `TauCeti.OddComponentGridDiagram.alexanderChainMinusPiece` and
  `TauCeti.OddComponentGridDiagram.alexanderChainMinusGrading`: the Alexander-homogeneous pieces of
  `GC⁻` and the internal grading they form.

## Main results

* `TauCeti.GridDiagram.maslovOℤ_sub_two_mul_card_OColumns` and
  `TauCeti.GridDiagram.alexanderTwoℤ_sub_two_mul_card_OColumns`: the integer forms of the two
  grading changes across a rectangle counted by `∂⁻`.
* `TauCeti.GridDiagram.isWeightedHomogeneous_OMonomial` and
  `TauCeti.GridDiagram.isWeightedHomogeneous_unblockedCoefficient`: with every variable of weight
  `-2`, the weight of an empty rectangle from `x` to `y`, and so each matrix coefficient of `∂⁻`,
  is weighted homogeneous of degree `M_O(x) - 1 - M_O(y)`, for any diagram.
* `TauCeti.OddComponentGridDiagram.monomialBidegree_add_of_mem_unblockedRectangles`: multiplying by
  the weight of a counted rectangle and moving to its target lowers the bidegree by `(1, 0)`.
* `TauCeti.OddComponentGridDiagram.unblockedDifferential_mem_bigradedChainMinusPiece`: the
  unblocked grid differential has bidegree `(-1, 0)`.
* `TauCeti.OddComponentGridDiagram.monomial_smul_mem_bigradedChainMinusPiece` and
  `TauCeti.OddComponentGridDiagram.X_smul_mem_bigradedChainMinusPiece`: the variable `V_c` has
  bidegree `(-2, -1)`, and a monomial `V^d` has bidegree `-|d|` times `(2, 1)`.
* `TauCeti.OddComponentGridDiagram.matrixMap_mem_bigradedChainMinusPiece` and
  `TauCeti.OddComponentGridDiagram.matrixMap_mem_alexanderChainMinusPiece`: a renamed matrix map
  whose weighted transitions preserve bidegree or Alexander degree preserves the corresponding
  homogeneous pieces.
* `TauCeti.OddComponentGridDiagram.isInternal_bigradedChainMinusPiece`: `GC⁻` is the internal
  direct sum of its homogeneous pieces.
* `TauCeti.OddComponentGridDiagram.isHomogeneous_unblockedDifferential_alexanderChainMinusGrading`
  and `TauCeti.OddComponentGridDiagram.X_smul_mem_alexanderChainMinusPiece`: `∂⁻` preserves the
  Alexander grading and each variable `V_c` lowers it by one.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and
`∂² = 0`", whose unblocked complex `GC⁻` this bigrades, and its standing convention "Mind the
bigrading bookkeeping", which asks to "fix once whether differentials drop Maslov by 1 and preserve
Alexander (unblocked)". The conventions follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots
and Links*, Chapter 4.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) {x y : GridState n}

/-! ### The integer grading changes across a counted rectangle -/

/-- The integer form of the `O`-Maslov grading change across an empty rectangle: charging the
weight `V^{O(r)}` with `-2` per variable, a rectangle counted by `∂⁻` lowers the integer `O`-Maslov
grading by exactly one. -/
theorem maslovOℤ_sub_two_mul_card_OColumns {r : GridRectangleBetween x y} (hr : r.IsEmpty) :
    G.maslovOℤ y - 2 * ((G.OColumns r.toGridRectangle).card : ℤ) = G.maslovOℤ x - 1 := by
  have h := G.maslovO_sub_two_mul_card_OColumns_eq_maslovO_sub_one hr
  rw [G.maslovO_eq_intCast, G.maslovO_eq_intCast] at h
  exact_mod_cast h

/-- The integer form of the Alexander grading change across a rectangle carrying no `X`-marking:
charging the weight `V^{O(r)}` with `-1` per variable, a rectangle counted by `∂⁻` preserves the
Alexander grading, here in its doubled integer form. -/
theorem alexanderTwoℤ_sub_two_mul_card_OColumns {r : GridRectangleBetween x y}
    (hr : Disjoint r.toGridRectangle.coveredSquares G.XSet) :
    G.alexanderTwoℤ y - 2 * ((G.OColumns r.toGridRectangle).card : ℤ) = G.alexanderTwoℤ x := by
  have h := G.alexander_sub_card_OColumns_eq_alexander hr
  have hy := G.two_mul_alexander_eq_intCast y
  have hx := G.two_mul_alexander_eq_intCast x
  have hq : (G.alexanderTwoℤ y : ℚ) - 2 * ((G.OColumns r.toGridRectangle).card : ℚ) =
      (G.alexanderTwoℤ x : ℚ) := by
    rw [← hy, ← hx]
    linarith
  exact_mod_cast hq

/-! ### Maslov homogeneity of the rectangle weights -/

variable (R : Type*) [CommSemiring R]

/-- **The weight of an empty rectangle is Maslov homogeneous.** Giving every variable the weight
`-2`, the weight `V^{O(r)}` of an empty rectangle from `x` to `y` is weighted homogeneous of degree
`M_O(x) - 1 - M_O(y)`: the term `V^{O(r)} · y` lies one below `x` in the `O`-Maslov grading. No
condition on the `X`-markings is needed. -/
theorem isWeightedHomogeneous_OMonomial {r : GridRectangleBetween x y} (hr : r.IsEmpty) :
    IsWeightedHomogeneous (fun _ : Fin n ↦ (-2 : ℤ)) (G.OMonomial R r.toGridRectangle)
      (G.maslovOℤ x - 1 - G.maslovOℤ y) := by
  have h := G.maslovOℤ_sub_two_mul_card_OColumns hr
  rw [OMonomial_eq_monomial]
  refine isWeightedHomogeneous_monomial _ _ _ ?_
  simp only [map_sum, Finsupp.weight_single, one_smul, Finset.sum_const, nsmul_eq_mul]
  omega

/-- A sum of weights of empty rectangles from `x` to `y`, such as a matrix coefficient of the
unblocked differential or of an `X`-marking homotopy, is weighted homogeneous of degree
`M_O(x) - 1 - M_O(y)` when every variable has weight `-2`. -/
theorem isWeightedHomogeneous_sum_OMonomial (s : Finset (GridRectangleBetween x y))
    (hs : ∀ r ∈ s, r.IsEmpty) :
    IsWeightedHomogeneous (fun _ : Fin n ↦ (-2 : ℤ)) (∑ r ∈ s, G.OMonomial R r.toGridRectangle)
      (G.maslovOℤ x - 1 - G.maslovOℤ y) :=
  IsWeightedHomogeneous.sum _ _ _ fun r hr ↦ G.isWeightedHomogeneous_OMonomial R (hs r hr)

/-- **The unblocked differential drops the `O`-Maslov grading by one**, in the form of its matrix
coefficients: with every variable of weight `-2`, the coefficient from `x` to `y` is weighted
homogeneous of degree `M_O(x) - 1 - M_O(y)`. Unlike the bigraded statements below, this needs no
hypothesis on the number of link components. -/
theorem isWeightedHomogeneous_unblockedCoefficient (x y : GridState n) :
    IsWeightedHomogeneous (fun _ : Fin n ↦ (-2 : ℤ)) (G.unblockedCoefficient R x y)
      (G.maslovOℤ x - 1 - G.maslovOℤ y) := by
  rw [unblockedCoefficient_def]
  exact G.isWeightedHomogeneous_sum_OMonomial R _ fun _ hr ↦ G.isEmpty_of_mem_unblockedRectangles hr

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) {x y : GridState n}

/-- The integer Alexander grading is unchanged across a rectangle counted by `∂⁻`, once its weight
`V^{O(r)}` is charged `-1` per variable. -/
theorem alexanderℤ_sub_card_OColumns {r : GridRectangleBetween x y}
    (hr : Disjoint r.toGridRectangle.coveredSquares G.1.XSet) :
    G.alexanderℤ y - ((G.1.OColumns r.toGridRectangle).card : ℤ) = G.alexanderℤ x := by
  have h := G.1.alexanderTwoℤ_sub_two_mul_card_OColumns hr
  rw [← G.two_mul_alexanderℤ, ← G.two_mul_alexanderℤ] at h
  omega

/-! ### The bidegree of a monomial generator -/

/-- The bidegree of the basis element `V^e · x` of the unblocked grid chain module `GC⁻`.

Each variable `V_c` sits in `O`-Maslov degree `-2` and Alexander degree `-1`, so the exponent
vector `e` shifts the bidegree of the grid state `x` by `-|e|` times `(2, 1)`, for `|e|` the total
degree of `e`. -/
noncomputable def monomialBidegree (x : GridState n) (e : Fin n →₀ ℕ) : ℤ × ℤ :=
  G.bidegree x - (2 * (e.degree : ℤ), (e.degree : ℤ))

/-- The `O`-Maslov component of the bidegree of `V^e · x`. -/
@[simp]
theorem monomialBidegree_fst (x : GridState n) (e : Fin n →₀ ℕ) :
    (G.monomialBidegree x e).1 = G.1.maslovOℤ x - 2 * (e.degree : ℤ) := by
  rw [monomialBidegree, Prod.fst_sub, bidegree_fst]

/-- The Alexander component of the bidegree of `V^e · x`. -/
@[simp]
theorem monomialBidegree_snd (x : GridState n) (e : Fin n →₀ ℕ) :
    (G.monomialBidegree x e).2 = G.alexanderℤ x - (e.degree : ℤ) := by
  rw [monomialBidegree, Prod.snd_sub, bidegree_snd]

/-- Renaming the input variables and multiplying by a squarefree weight preserves bidegree
when the target state's Maslov and Alexander gradings rise by twice and once the weight's size. -/
theorem monomialBidegree_mapDomain_add_sum (G' : OddComponentGridDiagram n)
    (σ : Equiv.Perm (Fin n)) (d : Fin n →₀ ℕ) (S : Finset (Fin n))
    (hM : G'.1.maslovOℤ y = G.1.maslovOℤ x + 2 * (S.card : ℤ))
    (hA : G'.alexanderℤ y = G.alexanderℤ x + S.card) :
    G'.monomialBidegree y
      (Finsupp.mapDomain σ d + ∑ c ∈ S, Finsupp.single (σ c) 1) =
      G.monomialBidegree x d := by
  have hdeg : ((Finsupp.mapDomain σ d +
      ∑ c ∈ S, Finsupp.single (M := ℕ) (σ c) 1).degree : ℤ) =
      (d.degree : ℤ) + (S.card : ℤ) := by
    rw [map_add, map_sum, Finsupp.degree_mapDomain]
    simp
  refine Prod.ext ?_ ?_
  · simp only [monomialBidegree_fst, hdeg, hM]
    ring
  · simp only [monomialBidegree_snd, hdeg, hA]
    ring

/-- A grid-state generator carries the bidegree of its state. -/
@[simp]
theorem monomialBidegree_zero (x : GridState n) : G.monomialBidegree x 0 = G.bidegree x := by
  rw [monomialBidegree]
  simp

/-- Multiplying the basis element `V^e · x` by the weight of a rectangle counted by `∂⁻` and
passing to the rectangle's target lowers the bidegree by `(1, 0)`. This is the whole content of the
statement that `∂⁻` has bidegree `(-1, 0)`. -/
theorem monomialBidegree_add_of_mem_unblockedRectangles
    {r : GridRectangleBetween x y} (hr : r ∈ G.1.unblockedRectangles x y) (e : Fin n →₀ ℕ) :
    G.monomialBidegree y (e + ∑ c ∈ G.1.OColumns r.toGridRectangle, Finsupp.single c 1) =
      G.monomialBidegree x e - (1, 0) := by
  have hM := G.1.maslovOℤ_sub_two_mul_card_OColumns (G.1.isEmpty_of_mem_unblockedRectangles hr)
  have hA := G.alexanderℤ_sub_card_OColumns (G.1.disjoint_XSet_of_mem_unblockedRectangles hr)
  have hsum : ((e + ∑ c ∈ G.1.OColumns r.toGridRectangle,
      Finsupp.single (M := ℕ) c 1).degree : ℤ) =
      (e.degree : ℤ) + ((G.1.OColumns r.toGridRectangle).card : ℤ) := by
    rw [map_add, map_sum]
    simp
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, monomialBidegree_fst]
    rw [hsum]
    omega
  · simp only [Prod.snd_sub, monomialBidegree_snd]
    rw [hsum]
    omega

/-! ### The homogeneous pieces of `GC⁻` -/

/-- The chains of `GC⁻` all of whose monomials have bidegree in a prescribed set of bidegrees.
Only the singleton and complement-of-singleton cases are used: a homogeneous piece is the first,
and comparing it against the second is what makes the pieces independent. -/
private def bigradedChainMinusSupported (R : Type*) [CommSemiring R] (S : Set (ℤ × ℤ)) :
    Submodule R (GridChainMinus R n) where
  carrier := {c | ∀ x : GridState n, ∀ e ∈ (c x).support, G.monomialBidegree x e ∈ S}
  add_mem' {a b} ha hb x e he := by
    classical
    rw [Finsupp.add_apply] at he
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
    · exact ha x e h
    · exact hb x e h
  zero_mem' x e he := by simp at he
  smul_mem' a b hb x e he := by
    rw [Finsupp.smul_apply] at he
    exact hb x e (MvPolynomial.support_smul he)

private theorem bigradedChainMinusSupported_mono {R : Type*} [CommSemiring R] {S T : Set (ℤ × ℤ)}
    (h : S ⊆ T) : G.bigradedChainMinusSupported R S ≤ G.bigradedChainMinusSupported R T :=
  fun _ hc x e he => h (hc x e he)

/-- The homogeneous piece of the unblocked grid chain module `GC⁻` in bidegree `g`: the chains all
of whose monomials `V^e · x` have bidegree `g`.

The variables move the bidegree, so this is a submodule over the coefficient ring `R` only, not
over `R[V₀, …, V_{n-1}]`. -/
def bigradedChainMinusPiece (R : Type*) [CommSemiring R] (g : ℤ × ℤ) :
    Submodule R (GridChainMinus R n) :=
  G.bigradedChainMinusSupported R {g}

/-- A chain of `GC⁻` is homogeneous of bidegree `g` exactly when every monomial occurring in it
has bidegree `g`. -/
@[simp]
theorem mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R] {g : ℤ × ℤ}
    {c : GridChainMinus R n} :
    c ∈ G.bigradedChainMinusPiece R g ↔
      ∀ x : GridState n, ∀ e ∈ (c x).support, G.monomialBidegree x e = g :=
  Iff.rfl

/-- A monomial multiple of a single grid-state generator is homogeneous of its own bidegree. -/
theorem single_monomial_mem_bigradedChainMinusPiece (R : Type*) [CommSemiring R]
    (x : GridState n) (e : Fin n →₀ ℕ) (a : R) :
    (Finsupp.single x (monomial e a) : GridChainMinus R n) ∈
      G.bigradedChainMinusPiece R (G.monomialBidegree x e) := by
  rw [mem_bigradedChainMinusPiece]
  intro z f hf
  rcases eq_or_ne z x with rfl | hzx
  · rw [Finsupp.single_eq_same] at hf
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hf)]
  · rw [Finsupp.single_eq_of_ne hzx] at hf
    simp at hf

/-- A grid-state generator of `GC⁻` is homogeneous of the bidegree of its state. -/
theorem single_one_mem_bigradedChainMinusPiece (R : Type*) [CommSemiring R] (x : GridState n) :
    (Finsupp.single x 1 : GridChainMinus R n) ∈ G.bigradedChainMinusPiece R (G.bidegree x) := by
  have h := G.single_monomial_mem_bigradedChainMinusPiece R x 0 (1 : R)
  have hone : (monomial (0 : Fin n →₀ ℕ) (1 : R) : MvPolynomial (Fin n) R) = 1 := by
    simp
  rwa [monomialBidegree_zero, hone] at h

/-- The unblocked grid differential lowers the bidegree of every monomial of a chain by `(1, 0)`. -/
private theorem unblockedDifferential_mem_bigradedChainMinusSupported {R : Type*}
    [CommSemiring R] {S T : Set (ℤ × ℤ)} (hST : ∀ g ∈ S, g - (1, 0) ∈ T)
    {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusSupported R S) :
    G.1.unblockedDifferential R c ∈ G.bigradedChainMinusSupported R T := by
  classical
  intro z f hf
  rw [GridDiagram.unblockedDifferential_apply_apply, Finsupp.sum] at hf
  obtain ⟨w, -, hfw⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hf)
  obtain ⟨e, he, d, hd, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hfw)
  obtain ⟨r, hr, rfl⟩ :=
    G.1.exists_mem_unblockedRectangles_of_mem_support_unblockedCoefficient R hd
  rw [G.monomialBidegree_add_of_mem_unblockedRectangles hr e]
  exact hST _ (hc w e he)

/-- **The unblocked grid differential has bidegree `(-1, 0)`**: it drops the `O`-Maslov grading by
one and preserves the Alexander grading. -/
theorem unblockedDifferential_mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R]
    {g : ℤ × ℤ} {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    G.1.unblockedDifferential R c ∈ G.bigradedChainMinusPiece R (g - (1, 0)) :=
  G.unblockedDifferential_mem_bigradedChainMinusSupported (by rintro _ rfl; rfl) hc

/-- The unblocked grid differential maps each homogeneous piece of `GC⁻` into the piece one lower
in the `O`-Maslov grading. -/
theorem map_unblockedDifferential_bigradedChainMinusPiece_le (R : Type*) [CommSemiring R]
    (g : ℤ × ℤ) :
    Submodule.map ((G.1.unblockedDifferential R).restrictScalars R)
        (G.bigradedChainMinusPiece R g) ≤
      G.bigradedChainMinusPiece R (g - (1, 0)) := by
  rintro _ ⟨c, hc, rfl⟩
  exact G.unblockedDifferential_mem_bigradedChainMinusPiece hc

/-- Multiplying the basis element `V^e · x` by `V^d` lowers its bidegree by `|d|` times `(2, 1)`. -/
private theorem monomialBidegree_add_left (x : GridState n) (d e : Fin n →₀ ℕ) :
    G.monomialBidegree x (d + e) =
      G.monomialBidegree x e - (2 * (d.degree : ℤ), (d.degree : ℤ)) := by
  have hdeg : ((d + e).degree : ℤ) = (d.degree : ℤ) + (e.degree : ℤ) := by
    rw [map_add]
    push_cast
    ring
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, monomialBidegree_fst, hdeg]
    ring
  · simp only [Prod.snd_sub, monomialBidegree_snd, hdeg]
    ring

/-- Multiplying by the monomial `V^d` lowers the bidegree of every monomial of a chain by `|d|`
times `(2, 1)`. -/
private theorem monomial_smul_mem_bigradedChainMinusSupported {R : Type*} [CommSemiring R]
    (d : Fin n →₀ ℕ) (a : R) {S T : Set (ℤ × ℤ)}
    (hST : ∀ g ∈ S, g - (2 * (d.degree : ℤ), (d.degree : ℤ)) ∈ T) {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusSupported R S) :
    (monomial d a : MvPolynomial (Fin n) R) • c ∈ G.bigradedChainMinusSupported R T := by
  classical
  intro z f hf
  rw [Finsupp.smul_apply, smul_eq_mul] at hf
  obtain ⟨b, hb, e, he, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hf)
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb),
    G.monomialBidegree_add_left]
  exact hST _ (hc z e he)

/-- **A monomial of the polynomial ring has bidegree `-|d|` times `(2, 1)`**: multiplying a
homogeneous chain of `GC⁻` by `V^d` lowers its `O`-Maslov grading by `2 |d|` and its Alexander
grading by `|d|`. -/
theorem monomial_smul_mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R]
    (d : Fin n →₀ ℕ) (a : R) {g : ℤ × ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.bigradedChainMinusPiece R g) :
    (monomial d a : MvPolynomial (Fin n) R) • c ∈
      G.bigradedChainMinusPiece R (g - (2 * (d.degree : ℤ), (d.degree : ℤ))) :=
  G.monomial_smul_mem_bigradedChainMinusSupported d a (by rintro _ rfl; rfl) hc

/-- **The variable `V_c` has bidegree `(-2, -1)`**: multiplying a homogeneous chain of `GC⁻` by a
polynomial variable lowers its `O`-Maslov grading by two and its Alexander grading by one. -/
theorem X_smul_mem_bigradedChainMinusPiece {R : Type*} [CommSemiring R] (i : Fin n) {g : ℤ × ℤ}
    {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    (X i : MvPolynomial (Fin n) R) • c ∈ G.bigradedChainMinusPiece R (g - (2, 1)) := by
  have h := G.monomial_smul_mem_bigradedChainMinusPiece (Finsupp.single i 1) (1 : R) hc
  rwa [Finsupp.degree_single, Nat.cast_one, mul_one, ← X] at h

/-! ### `GC⁻` is the direct sum of its homogeneous pieces -/

/-- The homogeneous pieces of `GC⁻` span it: every chain is a finite sum of monomial multiples of
grid-state generators. -/
theorem iSup_bigradedChainMinusPiece_eq_top (R : Type*) [CommSemiring R] :
    ⨆ g : ℤ × ℤ, G.bigradedChainMinusPiece R g = ⊤ := by
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
      Submodule.mem_iSup_of_mem (G.monomialBidegree x e)
        (G.single_monomial_mem_bigradedChainMinusPiece R x e _)

/-- The homogeneous pieces of `GC⁻` are independent: every monomial of a chain has exactly one
bidegree. -/
theorem iSupIndep_bigradedChainMinusPiece (R : Type*) [CommSemiring R] :
    iSupIndep (G.bigradedChainMinusPiece R) := by
  intro g
  rw [Submodule.disjoint_def]
  intro c hc hc'
  rw [mem_bigradedChainMinusPiece] at hc
  have hcompl : c ∈ G.bigradedChainMinusSupported R {g}ᶜ :=
    iSup₂_le (fun _ hg => G.bigradedChainMinusSupported_mono
      (Set.singleton_subset_iff.mpr hg)) hc'
  refine Finsupp.ext fun z => ?_
  rw [Finsupp.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  exact fun e he => hcompl z e he (hc z e he)

/-- **The unblocked grid chain module is bigraded**: `GC⁻` is the internal direct sum of its
homogeneous pieces.

The coefficient ring is a `CommRing` here, and not merely a `CommSemiring` as elsewhere in the
file, because independence plus spanning gives an internal direct sum only over a ring
(`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`). The grid coefficient rings of
interest, `ZMod 2` first among them, are rings. -/
theorem isInternal_bigradedChainMinusPiece (R : Type*) [CommRing R] :
    DirectSum.IsInternal (G.bigradedChainMinusPiece R) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (G.iSupIndep_bigradedChainMinusPiece R) (G.iSup_bigradedChainMinusPiece_eq_top R)

/-! ### The Alexander grading of `GC⁻` -/

/-- The Alexander-homogeneous piece of the unblocked grid chain module `GC⁻` in degree `a`: the
chains all of whose monomials `V^e · x` have Alexander grading `A(x) - |e| = a`, whatever their
`O`-Maslov grading. Like the bigraded pieces, it is a submodule over the coefficient ring `R`
only. -/
def alexanderChainMinusPiece (R : Type*) [CommSemiring R] (a : ℤ) :
    Submodule R (GridChainMinus R n) :=
  G.bigradedChainMinusSupported R {g | g.2 = a}

/-- A chain of `GC⁻` is Alexander-homogeneous of degree `a` exactly when every monomial `V^e · x`
occurring in it has Alexander grading `A(x) - |e| = a`. -/
@[simp]
theorem mem_alexanderChainMinusPiece {R : Type*} [CommSemiring R] {a : ℤ}
    {c : GridChainMinus R n} :
    c ∈ G.alexanderChainMinusPiece R a ↔
      ∀ x : GridState n, ∀ e ∈ (c x).support, G.alexanderℤ x - (e.degree : ℤ) = a := by
  simp only [← monomialBidegree_snd]
  rfl

/-- A bigraded piece of `GC⁻` lies in the Alexander piece of its Alexander degree. -/
theorem bigradedChainMinusPiece_le_alexanderChainMinusPiece (R : Type*) [CommSemiring R]
    (m a : ℤ) : G.bigradedChainMinusPiece R (m, a) ≤ G.alexanderChainMinusPiece R a :=
  G.bigradedChainMinusSupported_mono (Set.singleton_subset_iff.mpr rfl)

/-- The unblocked grid differential preserves the Alexander grading. -/
theorem unblockedDifferential_mem_alexanderChainMinusPiece {R : Type*} [CommSemiring R]
    {a : ℤ} {c : GridChainMinus R n} (hc : c ∈ G.alexanderChainMinusPiece R a) :
    G.1.unblockedDifferential R c ∈ G.alexanderChainMinusPiece R a :=
  G.unblockedDifferential_mem_bigradedChainMinusSupported
    (fun g (hg : g.2 = a) ↦ by simpa using hg) hc

/-- **The variable `V_c` has Alexander degree `-1`**: multiplying an Alexander-homogeneous chain
of `GC⁻` by a polynomial variable lowers its Alexander grading by one. -/
theorem X_smul_mem_alexanderChainMinusPiece {R : Type*} [CommSemiring R] (i : Fin n) {a : ℤ}
    {c : GridChainMinus R n} (hc : c ∈ G.alexanderChainMinusPiece R a) :
    (X i : MvPolynomial (Fin n) R) • c ∈ G.alexanderChainMinusPiece R (a - 1) := by
  have h := G.monomial_smul_mem_bigradedChainMinusSupported (Finsupp.single i 1) (1 : R)
    (T := {g | g.2 = a - 1}) (fun g (hg : g.2 = a) ↦ by simp [hg]) hc
  rwa [← X] at h

/-- The Alexander pieces of `GC⁻` span it. -/
theorem iSup_alexanderChainMinusPiece_eq_top (R : Type*) [CommSemiring R] :
    ⨆ a : ℤ, G.alexanderChainMinusPiece R a = ⊤ :=
  eq_top_iff.mpr <| (G.iSup_bigradedChainMinusPiece_eq_top R).ge.trans <| iSup_le fun g ↦
    (G.bigradedChainMinusPiece_le_alexanderChainMinusPiece R g.1 g.2).trans (le_iSup _ g.2)

/-- The Alexander pieces of `GC⁻` are independent: every monomial of a chain has exactly one
Alexander grading. -/
theorem iSupIndep_alexanderChainMinusPiece (R : Type*) [CommSemiring R] :
    iSupIndep (G.alexanderChainMinusPiece R) := by
  intro a
  rw [Submodule.disjoint_def]
  intro c hc hc'
  have hcompl : c ∈ G.bigradedChainMinusSupported R {g | g.2 ≠ a} :=
    iSup₂_le (fun b hb ↦ G.bigradedChainMinusSupported_mono
      fun g (hg : g.2 = b) ↦ by simpa [hg] using hb) hc'
  refine Finsupp.ext fun z ↦ ?_
  rw [Finsupp.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  exact fun e he ↦ hcompl z e he (hc z e he)

/-- **The Alexander grading of `GC⁻`**: the unblocked grid chain module is the internal direct sum
of its Alexander pieces, as a module over the coefficient ring `R`. -/
def alexanderChainMinusGrading (R : Type*) [CommRing R] :
    InternalGrading R (GridChainMinus R n) where
  piece := G.alexanderChainMinusPiece R
  isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (G.iSupIndep_alexanderChainMinusPiece R) (G.iSup_alexanderChainMinusPiece_eq_top R)

/-- The degree-`a` piece of the Alexander grading of `GC⁻` is its Alexander piece. -/
@[simp]
theorem alexanderChainMinusGrading_piece (R : Type*) [CommRing R] (a : ℤ) :
    (G.alexanderChainMinusGrading R).piece a = G.alexanderChainMinusPiece R a :=
  (rfl)

/-- The unblocked grid differential is homogeneous of degree zero for the Alexander grading. -/
theorem isHomogeneous_unblockedDifferential_alexanderChainMinusGrading (R : Type*) [CommRing R] :
    LinearMap.IsHomogeneous (G.1.unblockedDifferential R) (G.alexanderChainMinusGrading R).piece
      (G.alexanderChainMinusGrading R).piece 0 :=
  LinearMap.isHomogeneous_def.mpr fun a _ hc ↦ by
    simpa using G.unblockedDifferential_mem_alexanderChainMinusPiece hc

/-! ### Grading preservation by renamed matrix maps -/

section RenameMatrixMap

variable (R : Type*) [CommSemiring R] (G' : OddComponentGridDiagram n) (σ : Equiv.Perm (Fin n))
  (M : GridState n → GridState n → MvPolynomial (Fin n) R)
  (f : GridChainMinus R n → GridChainMinus R n)
  (hf : ∀ c y, f c y = c.sum fun x p => rename σ p * M x y)
  (hgrade : ∀ x y, ∀ w ∈ (M x y).support, ∀ d : Fin n →₀ ℕ,
    G'.monomialBidegree y (Finsupp.mapDomain σ d + w) = G.monomialBidegree x d)

include hf hgrade

/-- A matrix whose weighted transitions preserve bidegree preserves the bidegree of each
monomial occurring in an arbitrary input chain. -/
private theorem exists_monomialBidegree_eq_of_mem_support_matrixMap
    {c : GridChainMinus R n} {y : GridState n} {e : Fin n →₀ ℕ}
    (he : e ∈ (f c y).support) :
    ∃ x : GridState n, ∃ d ∈ (c x).support,
      G'.monomialBidegree y e = G.monomialBidegree x d := by
  rw [hf] at he
  obtain ⟨x, d, hd, w, hw, rfl⟩ :=
    GridChain.exists_eq_mapDomain_add_of_mem_support_sum_rename_mul R c σ M he
  exact ⟨x, d, hd, hgrade x y w hw d⟩

/-- A renamed matrix map whose weighted transitions preserve bidegree sends a chain homogeneous
for the source diagram `G` to a chain of the same bidegree for the target diagram `G'`. -/
theorem matrixMap_mem_bigradedChainMinusPiece
    {g : ℤ × ℤ} {c : GridChainMinus R n} (hc : c ∈ G.bigradedChainMinusPiece R g) :
    f c ∈ G'.bigradedChainMinusPiece R g := by
  rw [mem_bigradedChainMinusPiece] at hc ⊢
  intro y e he
  obtain ⟨x, d, hd, h⟩ :=
    G.exists_monomialBidegree_eq_of_mem_support_matrixMap R G' σ M f hf hgrade he
  rw [h, hc x d hd]

omit hgrade in
/-- A renamed matrix map whose weighted transitions preserve Alexander degree sends an
Alexander-homogeneous chain for `G` to a chain of the same Alexander degree for `G'`. -/
theorem matrixMap_mem_alexanderChainMinusPiece
    (hAlexander : ∀ x y, ∀ w ∈ (M x y).support, ∀ d : Fin n →₀ ℕ,
      (G'.monomialBidegree y (Finsupp.mapDomain σ d + w)).2 = (G.monomialBidegree x d).2)
    {a : ℤ} {c : GridChainMinus R n} (hc : c ∈ G.alexanderChainMinusPiece R a) :
    f c ∈ G'.alexanderChainMinusPiece R a := by
  rw [mem_alexanderChainMinusPiece] at hc ⊢
  intro y e he
  rw [hf] at he
  obtain ⟨x, d, hd, w, hw, rfl⟩ :=
    GridChain.exists_eq_mapDomain_add_of_mem_support_sum_rename_mul R c σ M he
  rw [← monomialBidegree_snd, hAlexander x y w hw d, monomialBidegree_snd, hc x d hd]

end RenameMatrixMap

end OddComponentGridDiagram

end TauCeti
