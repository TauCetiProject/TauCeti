/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Filtered.Basic
public import TauCeti.KnotTheory.Grid.Grading.Unblocked.Chain

/-!
# The Alexander filtration of the filtered grid complex

The filtered grid differential (`TauCeti.KnotTheory.Grid.Filtered.Basic`) counts every empty
rectangle, each weighted by the monomial `V^{O(r)}` of the `O`-markings it covers. With the
standard convention of `Grading/Unblocked/Chain.lean`, in which `V_c` has `O`-Maslov degree `-2`
and Alexander degree `-1`, a rectangle `r` from `x` to `y` gives a term `V^{O(r)} · y` of Maslov
grading `M_O(x) - 1` and of Alexander grading `A(x) - #(X ∩ r)`: it lowers the Alexander grading by
the number of `X`-markings it covers.

So the filtered differential still lowers the Maslov grading by exactly one
(`GridDiagram.isWeightedHomogeneous_filteredCoefficient`), but it no longer preserves the
Alexander grading; it only never raises it. The level `F_a` of the *Alexander filtration*
consists of the chains all of whose monomials `V^e · x` have Alexander grading
`A(x) - |e| ≤ a`. It is a submodule over the polynomial ring, since every variable lowers the
Alexander grading, and the filtered differential maps it into itself. The rectangles that preserve
the Alexander grading are exactly those covering no `X`-marking, which are the rectangles of the
unblocked differential `∂⁻`. Hence on `F_a` the filtered differential agrees with `∂⁻` up to terms
in `F_{a-1}`: the associated graded complex of the filtered grid complex is the unblocked grid
complex `GC⁻`. The filtration is exhaustive and separated.

As for the Alexander grading of `GC⁻`, the integer Alexander grading requires a grid diagram with
an odd number of link components, so the filtration is defined for
`TauCeti.OddComponentGridDiagram`.

## Main definitions

* `TauCeti.OddComponentGridDiagram.alexanderFiltration`: the level `F_a` of the Alexander
  filtration, a submodule of `GC⁻` over the polynomial ring.

## Main results

* `TauCeti.GridDiagram.isWeightedHomogeneous_filteredCoefficient`: with every variable of weight
  `-2`, each matrix coefficient of the filtered differential from `x` to `y` is weighted homogeneous
  of degree `M_O(x) - 1 - M_O(y)`.
* `TauCeti.OddComponentGridDiagram.alexanderFiltration_mono`,
  `TauCeti.OddComponentGridDiagram.iSup_alexanderFiltration_eq_top` and
  `TauCeti.OddComponentGridDiagram.iInf_alexanderFiltration_eq_bot`: the levels increase with `a`,
  and the filtration is exhaustive and separated.
* `TauCeti.OddComponentGridDiagram.X_smul_mem_alexanderFiltration`: each variable `V_i` lowers the
  filtration level by one.
* `TauCeti.OddComponentGridDiagram.alexanderChainMinusPiece_le_alexanderFiltration`: the
  Alexander-homogeneous chains of degree `a` lie in `F_a`.
* `TauCeti.OddComponentGridDiagram.filteredDifferential_mem_alexanderFiltration`: the filtered
  differential preserves each level `F_a`.
* `filteredDifferential_sub_unblockedDifferential_mem_alexanderFiltration`:
  on `F_a` the filtered differential differs from `∂⁻` by a chain in `F_{a-1}`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 13 (the Alexander filtration of the grid complex and its
  associated graded complex).
-/

public section

namespace TauCeti

open MvPolynomial GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommSemiring R]

/-- **The filtered differential lowers the `O`-Maslov grading by one**, in the form of its matrix
coefficients: with every variable of weight `-2`, the coefficient from `x` to `y` is weighted
homogeneous of degree `M_O(x) - 1 - M_O(y)`. -/
theorem isWeightedHomogeneous_filteredCoefficient (x y : GridState n) :
    IsWeightedHomogeneous (fun _ : Fin n ↦ (-2 : ℤ)) (G.filteredCoefficient R x y)
      (G.maslovOℤ x - 1 - G.maslovOℤ y) := by
  rw [filteredCoefficient_def]
  exact G.isWeightedHomogeneous_sum_OMonomial R _ fun r hr ↦ (mem_emptyRectangles r).mp hr

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*)

section CommSemiring

variable [CommSemiring R]

/-- The level `F_a` of the Alexander filtration of the grid chain module `GC⁻`: the chains all of
whose monomials `V^e · x` have Alexander grading `A(x) - |e| ≤ a`. Each variable lowers the
Alexander grading, so this is a submodule over the polynomial ring. -/
def alexanderFiltration (a : ℤ) : Submodule (MvPolynomial (Fin n) R) (GridChainMinus R n) where
  carrier := {c | ∀ x : GridState n, ∀ e ∈ (c x).support, G.alexanderℤ x - (e.degree : ℤ) ≤ a}
  add_mem' {c d} hc hd x e he := by
    classical
    rw [Finsupp.add_apply] at he
    rcases Finset.mem_union.mp (MvPolynomial.support_add he) with h | h
    · exact hc x e h
    · exact hd x e h
  zero_mem' x e he := by simp at he
  smul_mem' p c hc x e he := by
    classical
    rw [Finsupp.smul_apply, smul_eq_mul] at he
    obtain ⟨d, -, f, hf, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ he)
    have h := hc x f hf
    rw [map_add, Nat.cast_add]
    omega

variable {G R} in
/-- A chain lies in the level `F_a` of the Alexander filtration exactly when every monomial
`V^e · x` occurring in it has Alexander grading `A(x) - |e| ≤ a`. -/
@[simp]
theorem mem_alexanderFiltration {a : ℤ} {c : GridChainMinus R n} :
    c ∈ G.alexanderFiltration R a ↔
      ∀ x : GridState n, ∀ e ∈ (c x).support, G.alexanderℤ x - (e.degree : ℤ) ≤ a :=
  Iff.rfl

/-- The levels of the Alexander filtration increase with the Alexander grading. -/
theorem alexanderFiltration_mono : Monotone (G.alexanderFiltration R) :=
  fun _ _ hab _ hc x e he ↦ (hc x e he).trans hab

/-- **The variable `V_i` has Alexander degree `-1`**: multiplying a chain in the level `F_a` by a
variable gives a chain in `F_{a-1}`. -/
theorem X_smul_mem_alexanderFiltration (i : Fin n) {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderFiltration R a) :
    (X i : MvPolynomial (Fin n) R) • c ∈ G.alexanderFiltration R (a - 1) := by
  classical
  intro x e he
  rw [Finsupp.smul_apply, smul_eq_mul, X] at he
  obtain ⟨d, hd, f, hf, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ he)
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd), map_add,
    Finsupp.degree_single, Nat.cast_add, Nat.cast_one]
  have h := hc x f hf
  omega

/-- The Alexander-homogeneous chains of degree `a` lie in the level `F_a`. -/
theorem alexanderChainMinusPiece_le_alexanderFiltration (a : ℤ) :
    G.alexanderChainMinusPiece R a ≤ (G.alexanderFiltration R a).restrictScalars R :=
  fun _ hc x e he ↦ (G.mem_alexanderChainMinusPiece.mp hc x e he).le

/-- The Alexander filtration is exhaustive: every chain lies in some level. -/
theorem iSup_alexanderFiltration_eq_top : ⨆ a, G.alexanderFiltration R a = ⊤ := by
  refine eq_top_iff.mpr fun c _ ↦ ?_
  have hc : c ∈ ⨆ a, G.alexanderChainMinusPiece R a := by
    rw [G.iSup_alexanderChainMinusPiece_eq_top R]
    exact Submodule.mem_top
  exact (iSup_le fun a _ hc' ↦ le_iSup (G.alexanderFiltration R) a
    (G.alexanderChainMinusPiece_le_alexanderFiltration R a hc') :
      ⨆ a, G.alexanderChainMinusPiece R a ≤
        (⨆ a, G.alexanderFiltration R a).restrictScalars R) hc

/-- The Alexander filtration is separated: only the zero chain lies in every level. -/
theorem iInf_alexanderFiltration_eq_bot : ⨅ a, G.alexanderFiltration R a = ⊥ := by
  refine eq_bot_iff.mpr fun c hc ↦ (Submodule.mem_bot _).mpr (Finsupp.ext fun x ↦ ?_)
  rw [Finsupp.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro e he
  have h := (Submodule.mem_iInf _).mp hc (G.alexanderℤ x - (e.degree : ℤ) - 1) x e he
  omega

/-- The common estimate behind both filtration statements: if every rectangle of a family covers
at least `k` of the `X`-markings, then the matrix map counting that family with the weights
`V^{O(r)}` sends `F_a` into `F_{a-k}`. -/
private theorem le_of_mem_support_sum_mul_sum_OMonomial {a : ℤ} (k : ℕ)
    (s : ∀ x y : GridState n, Finset (GridRectangleBetween x y))
    (hs : ∀ x y, ∀ r ∈ s x y, k ≤ (G.1.XSet ∩ r.toGridRectangle.coveredSquares).card)
    {c : GridChainMinus R n} (hc : c ∈ G.alexanderFiltration R a) {y : GridState n}
    {e : Fin n →₀ ℕ}
    (he : e ∈ (c.sum fun x p => p * ∑ r ∈ s x y, G.1.OMonomial R r.toGridRectangle).support) :
    G.alexanderℤ y - (e.degree : ℤ) ≤ a - k := by
  classical
  rw [Finsupp.sum] at he
  obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  obtain ⟨d, hd, w, hw, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hx)
  obtain ⟨r, hr, rfl⟩ := G.1.exists_mem_of_mem_support_sum_OMonomial R hw
  have hA := G.alexanderℤ_sub_card_OColumns_eq_sub_card r
  have hdeg : ((d + ∑ c ∈ G.1.OColumns r.toGridRectangle, Finsupp.single c 1).degree : ℤ) =
      (d.degree : ℤ) + ((G.1.OColumns r.toGridRectangle).card : ℤ) := by
    rw [map_add, map_sum]
    simp
  have hx := hc x d hd
  have hk := hs x y r hr
  rw [hdeg]
  omega

/-- **The filtered differential respects the Alexander filtration**: it maps each level `F_a` into
itself, since no rectangle raises the Alexander grading. -/
theorem filteredDifferential_mem_alexanderFiltration {a : ℤ} {c : GridChainMinus R n}
    (hc : c ∈ G.alexanderFiltration R a) :
    G.1.filteredDifferential R c ∈ G.alexanderFiltration R a := by
  intro y e he
  simp only [GridDiagram.filteredDifferential_apply_apply,
    GridDiagram.filteredCoefficient_def] at he
  simpa using G.le_of_mem_support_sum_mul_sum_OMonomial R 0 (fun x y ↦ emptyRectangles x y)
    (fun _ _ _ _ ↦ Nat.zero_le _) hc he

end CommSemiring

variable [CommRing R]

/-- **The associated graded complex of the filtered grid complex is `GC⁻`**: on the level `F_a`
the filtered differential differs from the unblocked differential `∂⁻` by a chain in `F_{a-1}`.
The extra terms come from the rectangles covering an `X`-marking, each of which lowers the
Alexander grading. -/
theorem filteredDifferential_sub_unblockedDifferential_mem_alexanderFiltration {a : ℤ}
    {c : GridChainMinus R n} (hc : c ∈ G.alexanderFiltration R a) :
    G.1.filteredDifferential R c - G.1.unblockedDifferential R c ∈
      G.alexanderFiltration R (a - 1) := by
  classical
  rw [mem_alexanderFiltration]
  intro y e he
  have hy : (G.1.filteredDifferential R c - G.1.unblockedDifferential R c) y =
      c.sum fun x p => p * ∑ r ∈ (emptyRectangles x y).filter
        (fun r => ¬Disjoint r.toGridRectangle.coveredSquares G.1.XSet),
        G.1.OMonomial R r.toGridRectangle := by
    rw [Finsupp.sub_apply, GridDiagram.filteredDifferential_apply_apply,
      GridDiagram.unblockedDifferential_apply_apply, ← Finsupp.sum_sub]
    simp only [GridDiagram.filteredCoefficient_eq_unblockedCoefficient_add, mul_add,
      add_sub_cancel_left]
  rw [hy] at he
  refine G.le_of_mem_support_sum_mul_sum_OMonomial R 1
    (fun x y ↦ (emptyRectangles x y).filter
      fun r ↦ ¬Disjoint r.toGridRectangle.coveredSquares G.1.XSet) (fun x y r hr ↦ ?_) hc he
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.inter_comm,
    ← Finset.disjoint_iff_inter_eq_empty]
  exact (Finset.mem_filter.mp hr).2

end OddComponentGridDiagram

end TauCeti
