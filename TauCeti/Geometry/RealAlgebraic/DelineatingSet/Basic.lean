/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Geometry.RealAlgebraic.Stack.Basic
public import TauCeti.RingTheory.MvPolynomial.OrderAt

/-!
# Delineating sets over a point

Let `f` be a polynomial in the variables `X 0, …, X n`, with `X 0` the distinguished variable,
and let `α` be a point of the base `R ^ n`. The ordinary fibre of `f` over `α` is the univariate
polynomial `t ↦ f(t, α)`, obtained by mapping `MvPolynomial.finSuccEquiv R n f` along evaluation
at `α`. When the fibre is zero, `f` is *nullified* over `α`. Its roots then say nothing about the
order of vanishing of `f` along the line `{α} × R`, which can still vary. For
`X 1 * X 0 + X 2 ^ 2` over the origin of `ℝ ^ 2`, the fibre is zero, but the order is `2` at the
origin of `ℝ ^ 3` and `1` at every other point of the line
(`TauCeti.exists_forall_eval_eq_zero_orderAt_ne`).

The *delineating set* `f.delineatingSet α` repairs this. It consists of the nonzero fibres over
`α` of all iterated partial derivatives of `f`, in all variables, of order at most the total
degree of `f`. By the derivative characterization of the order
(`MvPolynomial.le_orderAt_iff_eval_foldl_pderiv`), the order of `f` at `(t, α)` depends only on
which members of the delineating set vanish at `t`. Hence it is the same at all points `t` that
are roots of no member, and refining the line at the finitely many roots of the delineating set
cuts it into a point for each root and open intervals, on each of which `f` has constant order.
When the fibre itself is nonzero, it belongs to the delineating set, so the refinement also
separates its roots.

This is the treatment of nullification over zero-dimensional cells in McCallum's projection
theory: there the lifting over such a cell refines the fibre at the roots of the delineating set,
so that the order of the nullified polynomial is constant on each cell above it.

## Main definitions

* `MvPolynomial.delineatingSet`: the nonzero fibres over a point of the iterated partial
  derivatives of `f` up to its total degree.

## Main results

* `MvPolynomial.orderAt_cons_eq_of_eval_eq_zero_iff`: the order of `f` at `(t, α)` is determined
  by which members of the delineating set vanish at `t`.
* `MvPolynomial.orderAt_eq_of_mem_stackCells`: over the point `α`, `f` has constant order on each
  cell of any stack whose sections include every root of the delineating set.
* `MvPolynomial.exists_strictMono_orderAt_eq_of_mem_stackCells`: the roots of the delineating set
  define such a finite stack.
* `TauCeti.exists_forall_eval_eq_zero_orderAt_ne`: the ordinary fibre alone does not determine
  the order.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998),
  pp. 242–268.
* C. W. Brown, *The McCallum projection, lifting, and order-invariance*, technical report
  USNA-CS-TR-2005-02, U.S. Naval Academy (2005).
-/

public section

open Polynomial TauCeti

namespace MvPolynomial

variable {R : Type*} [CommRing R] {n : ℕ} {f : MvPolynomial (Fin (n + 1)) R} {α : Fin n → R}

/-- The *delineating set* of `f` over the point `α` of the base: the nonzero fibres over `α` of
the iterated partial derivatives of `f`, in all variables, of order at most the total degree of
`f`. The fibre of `g` over `α` is the univariate polynomial `t ↦ g(t, α)`, that is,
`(finSuccEquiv R n g).map (eval α)`. -/
noncomputable def delineatingSet (f : MvPolynomial (Fin (n + 1)) R) (α : Fin n → R) :
    Finset R[X] := by
  classical
  exact ((Finset.range (f.totalDegree + 1)).biUnion fun k ↦
    Finset.univ.image fun v : Fin k → Fin (n + 1) ↦
      (finSuccEquiv R n ((List.ofFn v).foldl (fun q i ↦ pderiv i q) f)).map (eval α)).erase 0

/-- The members of the delineating set of `f` over `α` are the nonzero fibres over `α` of the
iterated partial derivatives of `f` along lists of at most `f.totalDegree` variables. -/
theorem mem_delineatingSet {q : R[X]} :
    q ∈ f.delineatingSet α ↔ q ≠ 0 ∧ ∃ l : List (Fin (n + 1)), l.length ≤ f.totalDegree ∧
      (finSuccEquiv R n (l.foldl (fun q i ↦ pderiv i q) f)).map (eval α) = q := by
  classical
  simp only [delineatingSet, Finset.mem_erase, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_image, Finset.mem_univ, true_and, Nat.lt_succ_iff]
  refine and_congr_right fun _ ↦ ⟨fun ⟨k, hk, v, hv⟩ ↦ ⟨_, by simpa using hk, hv⟩,
    fun ⟨l, hl, hq⟩ ↦ ⟨l.length, hl, l.get, by rwa [List.ofFn_get]⟩⟩

/-- A nonzero fibre of `f` itself belongs to the delineating set. -/
theorem map_finSuccEquiv_mem_delineatingSet (h : (finSuccEquiv R n f).map (eval α) ≠ 0) :
    (finSuccEquiv R n f).map (eval α) ∈ f.delineatingSet α :=
  mem_delineatingSet.2 ⟨h, [], by simp, rfl⟩

variable [IsAddTorsionFree R]

/-- The order of `f` at the point `(t, α)` depends only on which members of the delineating set
of `f` over `α` vanish at `t`. -/
theorem orderAt_cons_eq_of_eval_eq_zero_iff {t t' : R}
    (h : ∀ q ∈ f.delineatingSet α, q.eval t = 0 ↔ q.eval t' = 0) :
    f.orderAt (Fin.cons t α) = f.orderAt (Fin.cons t' α) := by
  refine orderAt_eq_of_forall_eval_foldl_pderiv_eq_zero_iff fun l hl ↦ ?_
  rw [eval_eq_eval_mv_eval', eval_eq_eval_mv_eval']
  by_cases h0 : (finSuccEquiv R n (l.foldl (fun q i ↦ pderiv i q) f)).map (eval α) = 0
  · simp [h0]
  · exact h _ (mem_delineatingSet.2 ⟨h0, l, hl, rfl⟩)

/-- Away from the roots of the delineating set of `f` over `α`, the order of `f` along the line
over `α` is constant. -/
theorem orderAt_cons_eq_of_not_isRoot {t t' : R}
    (ht : ∀ q ∈ f.delineatingSet α, ¬q.IsRoot t) (ht' : ∀ q ∈ f.delineatingSet α, ¬q.IsRoot t') :
    f.orderAt (Fin.cons t α) = f.orderAt (Fin.cons t' α) :=
  orderAt_cons_eq_of_eval_eq_zero_iff fun q hq ↦ iff_of_false (ht q hq) (ht' q hq)

/-- Over the point `α`, `f` has constant order on each cell of the stack cut out by points
`c i` of the line, provided every root of every member of the delineating set of `f` over `α`
is one of the `c i`. The points `c i` may include further roots, for instance those of other
polynomials of a family. -/
theorem orderAt_eq_of_mem_stackCells [LinearOrder R] {k : ℕ} {c : Fin k → R}
    (hc : ∀ q ∈ f.delineatingSet α, ∀ t, q.IsRoot t → t ∈ Set.range c)
    {E : Set (Fin (n + 1) → R)} (hE : E ∈ stackCells {α} fun i _ ↦ c i)
    {y y' : Fin (n + 1) → R} (hy : y ∈ E) (hy' : y' ∈ E) : f.orderAt y = f.orderAt y' := by
  rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · -- A section over the point `α` is the single point `(c i, α)`.
    obtain ⟨hy, hyi⟩ := mem_image_cylinder.1 hy
    obtain ⟨hy', hyi'⟩ := mem_image_cylinder.1 hy'
    simp only [mem_sectionSet] at hyi hyi'
    rw [← Fin.cons_self_tail y, ← Fin.cons_self_tail y', Set.mem_singleton_iff.1 hy,
      Set.mem_singleton_iff.1 hy', ← hyi, ← hyi']
  · -- A sector over `α` avoids every `c i`, hence every root of the delineating set.
    have key {y : Fin (n + 1) → R} (hy : y ∈ cylinder {α} '' sectorSet (fun i _ ↦ c i) j) :
        y = Fin.cons (y 0) α ∧ ∀ q ∈ f.delineatingSet α, ¬q.IsRoot (y 0) := by
      obtain ⟨hyα, hyj⟩ := mem_image_cylinder.1 hy
      refine ⟨by rw [← Set.mem_singleton_iff.1 hyα, Fin.cons_self_tail], fun q hq hr ↦ ?_⟩
      obtain ⟨i, hi⟩ := hc q hq _ hr
      exact Set.disjoint_left.1 (disjoint_sectionSet_sectorSet _ i j) (mem_sectionSet.2 hi) hyj
    obtain ⟨hy, hr⟩ := key hy
    obtain ⟨hy', hr'⟩ := key hy'
    rw [hy, hy']
    exact orderAt_cons_eq_of_not_isRoot hr hr'

/-- **Refinement of a nullified fibre.** Over a domain, the roots of the members of the
delineating set of `f` over `α` are finitely many points `c₀ < … < cₖ₋₁` of the line, and `f`
has constant order on each cell of the stack over `α` that they cut out: each point `cᵢ`, and
each open interval between consecutive points. -/
theorem exists_strictMono_orderAt_eq_of_mem_stackCells [LinearOrder R] [IsDomain R]
    (f : MvPolynomial (Fin (n + 1)) R) (α : Fin n → R) :
    ∃ (k : ℕ) (c : Fin k → R), StrictMono c ∧
      (∀ i, ∃ q ∈ f.delineatingSet α, q.IsRoot (c i)) ∧
      ∀ E ∈ stackCells {α} (fun i _ ↦ c i), ∀ y ∈ E, ∀ y' ∈ E, f.orderAt y = f.orderAt y' := by
  classical
  set T := (f.delineatingSet α).biUnion fun q ↦ q.roots.toFinset
  have hT {t : R} : t ∈ T ↔ ∃ q ∈ f.delineatingSet α, q.IsRoot t := by
    simp only [T, Finset.mem_biUnion, Multiset.mem_toFinset]
    exact exists_congr fun q ↦ and_congr_right fun hq ↦ mem_roots (mem_delineatingSet.1 hq).1
  refine ⟨T.card, T.orderEmbOfFin rfl, (T.orderEmbOfFin rfl).strictMono,
    fun i ↦ hT.1 (T.orderEmbOfFin_mem rfl i), fun E hE y hy y' hy' ↦
      orderAt_eq_of_mem_stackCells (fun q hq t ht ↦ ?_) hE hy hy'⟩
  rw [Finset.range_orderEmbOfFin]
  exact hT.2 ⟨q, hq, ht⟩

end MvPolynomial

namespace TauCeti

open MvPolynomial

/-- The fibre of a polynomial does not determine its order of vanishing. The polynomial
`X 1 * X 0 + X 2 ^ 2` vanishes on the whole line `{(t, 0, 0)}` over the origin of `ℝ ^ 2`, but its
order is `2` at the origin of `ℝ ^ 3` and `1` at every other point `(t, 0, 0)` of the line. -/
theorem exists_forall_eval_eq_zero_orderAt_ne :
    ∃ f : MvPolynomial (Fin 3) ℝ, (∀ t, eval ![t, 0, 0] f = 0) ∧
      f.orderAt ![0, 0, 0] = 2 ∧ ∀ t ≠ 0, f.orderAt ![t, 0, 0] = 1 := by
  have h0 : pderiv 0 (X 1 * X 0 + X 2 ^ 2 : MvPolynomial (Fin 3) ℝ) = X 1 := by simp [pderiv_X]
  have h1 : pderiv 1 (X 1 * X 0 + X 2 ^ 2 : MvPolynomial (Fin 3) ℝ) = X 0 := by simp [pderiv_X]
  have h2 : pderiv 2 (X 1 * X 0 + X 2 ^ 2 : MvPolynomial (Fin 3) ℝ) = 2 * X 2 := by
    simp [pderiv_X]
  have heq {o : ℕ∞} {m : ℕ} (h : (m : ℕ∞) ≤ o) (h' : ¬((m + 1 : ℕ) : ℕ∞) ≤ o) : o = m := by
    induction o using ENat.recTopCoe
    · simp at h'
    · norm_cast at h h' ⊢
      omega
  refine ⟨X 1 * X 0 + X 2 ^ 2, fun t ↦ by simp, heq ?_ ?_, fun t ht ↦ heq ?_ ?_⟩
  · -- the polynomial and its first partial derivatives vanish at the origin
    norm_num only
    rw [← one_add_one_eq_two (R := ℕ∞), succ_le_orderAt_iff]
    refine ⟨by simp, fun i ↦ ?_⟩
    rw [Order.one_le_iff_pos, orderAt_pos_iff]
    fin_cases i <;> simp [h0, h1, h2]
  · -- the mixed partial derivative along `X 0` and `X 1` is `1`
    rw [le_orderAt_iff_eval_foldl_pderiv]
    intro h
    simpa [h0] using h [0, 1] (by simp)
  · simp [orderAt_pos_iff, Order.one_le_iff_pos]
  · -- the partial derivative along `X 1` is `X 0`, which is `t ≠ 0` at `(t, 0, 0)`
    rw [le_orderAt_iff_eval_foldl_pderiv]
    intro h
    exact ht (by simpa [h1] using h [1] (by simp))

end TauCeti
