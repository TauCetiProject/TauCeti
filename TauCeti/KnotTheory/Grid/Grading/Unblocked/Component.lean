/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Linarith
public import TauCeti.KnotTheory.Grid.Grading.Component
public import TauCeti.KnotTheory.Grid.Grading.Unblocked.MonomialDegree
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# The Alexander multigrading of `GC⁻`

`Grading/Component.lean` gives a grid diagram one Alexander grading `A_q` of grid states for each
link component `q`. This file extends them to the unblocked grid complex `GC⁻`.

The variable `V_c` has multidegree `-e_q` for the component `q` of column `c`, so the monomial
`V^e · x` has `q`-th Alexander grading `A_q(x) - ∑_{c ∈ q} e_c`
(`GridDiagram.monomialComponentAlexander`). The unblocked differential counts rectangles with no
`X`-marking and weights each by the variables of the `O`-markings it covers; such a rectangle
raises `A_q` by the number of covered `O`-markings of `q`, so the differential preserves every
component grading (`GridDiagram.unblockedDifferential_mem_componentAlexanderChainMinusPiece`).
The gradings are rational and, for a link, need not be integers, so the multidegrees are valued in
`ℚ`.

The pieces and the internal grading are the instance `deg = monomialComponentAlexander` of the
grading of `GC⁻` by monomial degrees, `GridChainMinus.monomialDegreeGrading`.

## Main definitions

* `TauCeti.GridDiagram.monomialComponentAlexander`: the Alexander multidegree of a monomial
  `V^e · x` of `GC⁻`.
* `TauCeti.GridDiagram.componentAlexanderChainMinusPiece`: the chains of `GC⁻` homogeneous of a
  given Alexander multidegree.
* `TauCeti.GridDiagram.componentAlexanderChainMinusGrading`: the Alexander multigrading of `GC⁻`
  as an internal grading over the coefficient ring.

## Main results

* `TauCeti.GridDiagram.componentAlexander_sub_card_inter_OColumns_eq`: a rectangle with no
  `X`-marking raises each component grading by the number of covered `O`-markings on it.
* `TauCeti.GridDiagram.sum_monomialComponentAlexander`: the entries of the multidegree of a
  monomial add up to its Alexander grading plus the link correction `(ℓ - 1) / 2`.
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
  the Alexander multigrading of the link grid complex.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 11.1: the Alexander multigrading of the grid complex of a
  link.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### Rectangles counted by the unblocked differential -/

/-- The `O`-markings of a component covered by a rectangle are indexed by the covered `O`-columns
on that component. -/
theorem card_componentOSet_inter_coveredSquares (q : G.Components) (r : GridRectangle n) :
    (G.componentOSet q ∩ r.coveredSquares).card = (G.componentColumns q ∩ G.OColumns r).card := by
  rw [componentOSet_def, Finset.filter_inter, ← Finset.inter_filter, ← card_OColumnsOfSquares]
  congr 1
  ext c
  simp [mem_componentColumns, mem_OColumns, and_comm]

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
      (hr.symm.mono_left (by rw [componentXSet_def]; exact Finset.filter_subset _ _))
  have h := G.componentAlexander_sub_componentAlexander_eq_card_sub_card q r
  rw [hX, Finset.card_empty, Nat.cast_zero, card_componentOSet_inter_coveredSquares] at h
  linarith

/-! ### The Alexander multidegree of a monomial -/

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
    simp only [componentColumns_def]
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

/-- The chains of `GC⁻` homogeneous of Alexander multidegree `a`: those all of whose monomials
`V^e · x` have multidegree `a`.

The variables move the multidegree, so this is a submodule over the coefficient ring `R` only. -/
noncomputable def componentAlexanderChainMinusPiece (R : Type*) [CommSemiring R]
    (a : G.Components → ℚ) : Submodule R (GridChainMinus R n) :=
  GridChainMinus.monomialDegreePiece R G.monomialComponentAlexander a

/-- A chain of `GC⁻` is homogeneous of Alexander multidegree `a` exactly when every monomial
occurring in it has multidegree `a`. -/
@[simp]
theorem mem_componentAlexanderChainMinusPiece {R : Type*} [CommSemiring R]
    {a : G.Components → ℚ} {c : GridChainMinus R n} :
    c ∈ G.componentAlexanderChainMinusPiece R a ↔
      ∀ x : GridState n, ∀ e ∈ (c x).support, G.monomialComponentAlexander x e = a :=
  GridChainMinus.mem_monomialDegreePiece

/-- A single monomial `V^e · x` is homogeneous of its own Alexander multidegree. -/
theorem single_monomial_mem_componentAlexanderChainMinusPiece (R : Type*) [CommSemiring R]
    (x : GridState n) (e : Fin n →₀ ℕ) (b : R) :
    Finsupp.single x (monomial e b) ∈
      G.componentAlexanderChainMinusPiece R (G.monomialComponentAlexander x e) :=
  GridChainMinus.single_monomial_mem_monomialDegreePiece R G.monomialComponentAlexander x e b

/-- **The unblocked grid differential preserves the Alexander multidegree.** -/
theorem unblockedDifferential_mem_componentAlexanderChainMinusPiece {R : Type*} [CommSemiring R]
    {a : G.Components → ℚ} {c : GridChainMinus R n}
    (hc : c ∈ G.componentAlexanderChainMinusPiece R a) :
    G.unblockedDifferential R c ∈ G.componentAlexanderChainMinusPiece R a :=
  G.unblockedDifferential_mem_monomialDegreePiece (φ := id)
    (fun _ _ _ hr e => G.monomialComponentAlexander_add_of_mem_unblockedRectangles hr e) hc

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
  have h := GridChainMinus.monomial_smul_mem_monomialDegreePiece (Finsupp.single i 1) (1 : R)
    (φ := (· - Pi.single (G.componentOfColumn i) 1))
    (fun x e => G.monomialComponentAlexander_single_add x i e) hc
  rwa [← MvPolynomial.X] at h

/-! ### `GC⁻` is the direct sum of its multigraded pieces -/

/-- The multigraded pieces of `GC⁻` span it: every chain is a finite sum of monomial multiples of
grid-state generators. -/
theorem iSup_componentAlexanderChainMinusPiece_eq_top (R : Type*) [CommSemiring R] :
    ⨆ a, G.componentAlexanderChainMinusPiece R a = ⊤ :=
  GridChainMinus.iSup_monomialDegreePiece_eq_top R G.monomialComponentAlexander

/-- The multigraded pieces of `GC⁻` are independent: every monomial of a chain has exactly one
Alexander multidegree. -/
theorem iSupIndep_componentAlexanderChainMinusPiece (R : Type*) [CommSemiring R] :
    iSupIndep (G.componentAlexanderChainMinusPiece R) :=
  GridChainMinus.iSupIndep_monomialDegreePiece R G.monomialComponentAlexander

/-- **The Alexander multigrading of `GC⁻`**: the unblocked grid chain module is the internal direct
sum of its multigraded pieces, as a module over the coefficient ring `R`. -/
noncomputable def componentAlexanderChainMinusGrading (R : Type*) [CommRing R] :
    InternalGrading R (GridChainMinus R n) (G.Components → ℚ) :=
  GridChainMinus.monomialDegreeGrading R G.monomialComponentAlexander

/-- The pieces of the Alexander multigrading of `GC⁻` are its multigraded pieces. -/
@[simp]
theorem componentAlexanderChainMinusGrading_piece (R : Type*) [CommRing R]
    (a : G.Components → ℚ) :
    (G.componentAlexanderChainMinusGrading R).piece a = G.componentAlexanderChainMinusPiece R a :=
  GridChainMinus.monomialDegreeGrading_piece R _ a

/-- The unblocked grid differential is homogeneous of degree zero for the Alexander
multigrading. -/
theorem isHomogeneous_unblockedDifferential_componentAlexanderChainMinusGrading (R : Type*)
    [CommRing R] :
    LinearMap.IsHomogeneous (G.unblockedDifferential R)
      (G.componentAlexanderChainMinusGrading R).piece
      (G.componentAlexanderChainMinusGrading R).piece 0 :=
  LinearMap.isHomogeneous_def.mpr fun a _ hc => by
    rw [componentAlexanderChainMinusGrading_piece] at hc
    simpa using G.unblockedDifferential_mem_componentAlexanderChainMinusPiece hc

end GridDiagram

end TauCeti
