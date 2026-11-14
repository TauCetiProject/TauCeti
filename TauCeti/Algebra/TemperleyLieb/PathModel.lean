/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Algebra.TemperleyLieb.Trace.Basic
public import TauCeti.Combinatorics.SimpleGraph.WalkFrom
public import TauCeti.LinearAlgebra.Matrix.ExtendLast
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Field
import TauCeti.Data.Fintype.BigOperators

/-!
# Path models of the Temperley–Lieb algebras

Let `G` be a finite simple graph with a base vertex `v₀`, and let `r` be a weighting of its
vertices by nonzero scalars whose squares satisfy the adjacency eigenvector equation with
eigenvalue `δ`: the squared weights of the neighbours of `v` add up to `δ * r v ^ 2`. When this
holds at every vertex, this file builds a representation of the Temperley–Lieb tower with loop
value `δ` on walks in `G` starting at `v₀`, together with a Markov trace, and proves that the trace
is positive when the weights are self-adjoint. More generally, on `n` strands the generator
relations and Markov trace axioms up to `n` strands only inspect the eigenvector equation at
endpoints of walks from `v₀` of fewer than `n` steps
(`TauCeti.TemperleyLieb.IsPathEigenvectorUpTo`). Combined with bounded uniqueness
(`TauCeti.TemperleyLieb.IsMarkovTraceUpTo.unique`), this proves positivity on `n` strands of every
global Markov trace whenever a finite graph carries positive weights satisfying the recurrence up to
depth `n`—even at loop parameters where no finite graph carries a global positive eigenvector; see
`TauCeti.Algebra.TemperleyLieb.Positivity`.

The algebra on `n` strands acts on functions of vertex sequences `s : Fin (n + 1) → V`, among
which the walks from `v₀` (`SimpleGraph.IsWalkFrom`) are the states of the model. The
generator `e i` acts on the vertex at position `b = i + 1`, between the positions `a = i` and
`c = i + 2`: on a walk `s` with `s a = s c` it is the rank-one matrix
`(r (s a) ^ 2)⁻¹ • w wᵀ` on the vertex at `b`, where `w` is the vector of weights `r x` of the
neighbours `x` of `s a`, and it vanishes on the other rows
(`TauCeti.TemperleyLieb.pathGenerator`). Since `a < n`, `s a` is the endpoint of a prefix walk of
fewer than `n` steps, so the quadratic relation is the bounded eigenvector equation
`wᵀ w = δ * r (s a) ^ 2`; the zigzag relations hold because the walk returns to the vertex it
left; and generators at distant positions move independent vertices. Every generator preserves
the walks and their endpoints, and on rows of walks adding a straight strand acts as
`Matrix.extendLast`.

The trace (`TauCeti.TemperleyLieb.pathTrace`) is the matrix trace weighted by
`(r v / r v₀) ^ 2` on the walks ending at `v`. Extending walks of fewer than `n` steps by one step
multiplies the total weight by `δ`, which gives the normalization and the strand inclusion
compatibility up to `n` strands; capping the last step with the previous one forces the walk to
return to its penultimate vertex, which gives the Markov property. For self-adjoint weights the
generator matrices are self-adjoint, so the representation carries the analytic adjoint to the
conjugate transpose, and the trace of `x⋆ * x` is a sum of absolute squares with nonnegative
weights.

## Main definitions

* `TauCeti.TemperleyLieb.IsPathEigenvectorUpTo`: the squared weights satisfy the adjacency
  eigenvector equation with eigenvalue `δ` at endpoints of walks from `v₀` of fewer than `n` steps.
* `TauCeti.TemperleyLieb.pathGenerator`: the matrix of a generator in the path model.
* `TauCeti.TemperleyLieb.pathRep`: the path representation of the Temperley–Lieb algebra.
* `TauCeti.TemperleyLieb.pathWeight`: the weight of a vertex sequence in the trace.
* `TauCeti.TemperleyLieb.pathTrace`: the trace of the path model.

## Main results

* `TauCeti.TemperleyLieb.pathRep_apply_eq_zero`: the path representation preserves walks and
  their endpoints.
* `TauCeti.TemperleyLieb.pathRep_strandIncl_apply`: on rows of walks, adding a straight strand
  acts by `Matrix.extendLast`.
* `TauCeti.TemperleyLieb.isMarkovTraceUpTo_pathTrace`,
  `TauCeti.TemperleyLieb.isMarkovTrace_pathTrace`: the trace of the path model is a Markov trace up
  to `n` strands (and on the full tower under a global eigenvector).
* `TauCeti.TemperleyLieb.pathRep_star`: for self-adjoint weights, the path representation carries
  the analytic adjoint to the conjugate transpose.
* `TauCeti.TemperleyLieb.pathTrace_star_mul_self_nonneg`: for self-adjoint weights, the trace of
  `x⋆ * x` is nonnegative.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_isPathEigenvectorUpTo`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_of_graph`: positivity of every
  Markov trace on `n` strands from a bounded-depth or global path model.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989 (path algebras of graphs and their Temperley–Lieb
  representations).
* H. Wenzl, *Hecke algebras of type `A_n` and subfactors*, Invent. Math. 92 (1988), 349–383.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, §§4.4–4.5 (the tree basis
  and the paths on `A_(m-1)`).
-/

public section

open Function Matrix
open SimpleGraph (isWalkFrom_iff_init isWalkFrom_snoc isWalkFrom_zero)

namespace TauCeti.TemperleyLieb

variable {K : Type*} [Field K] {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (v₀ : V) (r : V → K)

section EigenvectorUpTo

omit [DecidableEq V]

/-- The squares of `r` satisfy the adjacency eigenvector equation with eigenvalue `δ` at the
endpoints of all walks in `G` from `v₀` with fewer than `n` steps. -/
def IsPathEigenvectorUpTo (δ : K) (n : ℕ) : Prop :=
  ∀ ⦃m : ℕ⦄, m < n → ∀ ⦃s : Fin (m + 1) → V⦄, G.IsWalkFrom v₀ s →
    ∑ u ∈ G.neighborFinset (s (Fin.last m)), r u ^ 2 = δ * r (s (Fin.last m)) ^ 2

variable {G v₀ r}

/-- Unfolded characterization of `IsPathEigenvectorUpTo`. -/
theorem isPathEigenvectorUpTo_iff {δ : K} {n : ℕ} :
    IsPathEigenvectorUpTo G v₀ r δ n ↔
      ∀ ⦃m : ℕ⦄, m < n → ∀ ⦃s : Fin (m + 1) → V⦄, G.IsWalkFrom v₀ s →
        ∑ u ∈ G.neighborFinset (s (Fin.last m)), r u ^ 2 = δ * r (s (Fin.last m)) ^ 2 :=
  (Iff.rfl)

/-- On zero strands there are no walks of fewer than `0` steps, so `IsPathEigenvectorUpTo` holds
vacuously. -/
@[simp]
theorem isPathEigenvectorUpTo_zero (δ : K) : IsPathEigenvectorUpTo G v₀ r δ 0 :=
  fun _ hm ↦ absurd hm (Nat.not_lt_zero _)

/-- Monotonicity of `IsPathEigenvectorUpTo` in the step bound. -/
theorem IsPathEigenvectorUpTo.mono {δ : K} {m n : ℕ} (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (hmn : m ≤ n) : IsPathEigenvectorUpTo G v₀ r δ m :=
  fun _ hk _ hs ↦ hδ (hk.trans_le hmn) hs

/-- A global adjacency eigenvector satisfies `IsPathEigenvectorUpTo` at every depth `n`. -/
theorem IsPathEigenvectorUpTo.of_forall {δ : K}
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) (n : ℕ) :
    IsPathEigenvectorUpTo G v₀ r δ n :=
  fun _ _ _ _ ↦ hδ _

/-- At any position `a` strictly before the end of an `m`-step walk from `v₀`, the bounded
eigenvector hypothesis up to `m` gives the neighbour-square sum at `s a`. -/
theorem IsPathEigenvectorUpTo.apply_of_lt {δ : K} {m : ℕ}
    (hδ : IsPathEigenvectorUpTo G v₀ r δ m) {s : Fin (m + 1) → V} (hs : G.IsWalkFrom v₀ s)
    {a : Fin (m + 1)} (ha : a.val < m) :
    ∑ u ∈ G.neighborFinset (s a), r u ^ 2 = δ * r (s a) ^ 2 := by
  have h := hδ ha (hs.take ha.le)
  rwa [Fin.take_apply, show Fin.castLE _ (Fin.last a.val) = a from Fin.ext (by simp)] at h

end EigenvectorUpTo

section Generator

variable {m : ℕ}

/-- The matrix of a Temperley–Lieb generator in the path model on walks with `m` steps, acting on
the vertex at position `b`, whose neighbouring positions are `a` and `c`. Its entry at `s` and `t`
is `r (s b) * r (t b) / r (s a) ^ 2` when `s` is a walk from `v₀` with `s a = s c`, the
configuration `t` differs from `s` at most at position `b`, and `t b` is a neighbour of `s a`; it
is `0` otherwise. -/
def pathGenerator (a b c : Fin (m + 1)) : Matrix (Fin (m + 1) → V) (Fin (m + 1) → V) K :=
  Matrix.of fun s t ↦
    if G.IsWalkFrom v₀ s ∧ s a = s c ∧ t = update s b (t b) ∧ G.Adj (s a) (t b) then
      r (s b) * r (t b) / r (s a) ^ 2
    else 0

omit [Fintype V] in
theorem pathGenerator_apply (a b c : Fin (m + 1)) (s t : Fin (m + 1) → V) :
    pathGenerator G v₀ r a b c s t =
      if G.IsWalkFrom v₀ s ∧ s a = s c ∧ t = update s b (t b) ∧ G.Adj (s a) (t b) then
        r (s b) * r (t b) / r (s a) ^ 2
      else 0 := (rfl)

variable {G v₀ r}

/-- Left multiplication by a generator matrix: the row `s` of the product is a weighted sum of
the rows of `X` at the walks obtained from `s` by moving the vertex at position `b` to a neighbour
of `s a`. -/
theorem pathGenerator_mul_apply (a b c : Fin (m + 1))
    (X : Matrix (Fin (m + 1) → V) (Fin (m + 1) → V) K) (s u : Fin (m + 1) → V) :
    (pathGenerator G v₀ r a b c * X) s u =
      if G.IsWalkFrom v₀ s ∧ s a = s c then
        ∑ x ∈ G.neighborFinset (s a), r (s b) * r x / r (s a) ^ 2 * X (update s b x) u
      else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with hs
  · have h (t : Fin (m + 1) → V) : pathGenerator G v₀ r a b c s t * X t u =
        if t = update s b (t b) then
          (if G.Adj (s a) (t b) then r (s b) * r (t b) / r (s a) ^ 2 * X t u else 0)
        else 0 := by
      rw [pathGenerator_apply, ← ite_and, ite_mul, zero_mul]
      simp only [hs, true_and]
    simp_rw [h]
    rw [Fintype.sum_ite_eq_update s b, ← Finset.sum_filter]
    simp_rw [update_self]
    congr 1
    ext x
    simp
  · refine Finset.sum_eq_zero fun t _ ↦ ?_
    rw [pathGenerator_apply, ite_eq_right_iff.2 fun h ↦ (hs ⟨h.1, h.2.1⟩).elim, zero_mul]

omit [Fintype V] in
/-- A generator matrix evaluated at a walk whose vertex at position `b` has been moved. -/
theorem pathGenerator_update_apply {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) {s : Fin (m + 1) → V} (hs : G.IsWalkFrom v₀ s) (hac : s a = s c)
    {x : V} (hx : G.Adj (s a) x) (u : Fin (m + 1) → V) :
    pathGenerator G v₀ r a b c (update s b x) u =
      if u = update s b (u b) ∧ G.Adj (s a) (u b) then r x * r (u b) / r (s a) ^ 2 else 0 := by
  have ha : a ≠ b := Fin.ne_of_val_ne (by omega)
  have hc : c ≠ b := Fin.ne_of_val_ne (by omega)
  rw [pathGenerator_apply, update_of_ne ha, update_of_ne hc, update_self, update_idem]
  simp [hs.update hab hbc hac hx, hac]

variable (hr : ∀ v, r v ≠ 0) {δ : K}

include hr in
/-- Closing a loop multiplies a generator matrix by the loop value `δ`. -/
theorem pathGenerator_mul_self (hδ : IsPathEigenvectorUpTo G v₀ r δ m)
    {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) :
    pathGenerator G v₀ r a b c * pathGenerator G v₀ r a b c =
      δ • pathGenerator G v₀ r a b c := by
  ext s u
  rw [pathGenerator_mul_apply, Matrix.smul_apply, pathGenerator_apply, smul_eq_mul]
  split_ifs with hs hu hu
  · rw [Finset.sum_congr rfl fun x hx ↦ by
      rw [pathGenerator_update_apply hab hbc hs.1 hs.2 ((G.mem_neighborFinset _ _).1 hx),
        ite_eq_left ⟨hu.2.2.1, hu.2.2.2⟩]]
    have hsa := hr (s a)
    calc ∑ x ∈ G.neighborFinset (s a), r (s b) * r x / r (s a) ^ 2 * (r x * r (u b) / r (s a) ^ 2)
        = r (s b) * r (u b) / r (s a) ^ 4 * ∑ x ∈ G.neighborFinset (s a), r x ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          field_simp
      _ = _ := by
          rw [hδ.apply_of_lt hs.1 (by omega)]
          field_simp
  · rw [mul_zero]
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    rw [pathGenerator_update_apply hab hbc hs.1 hs.2 ((G.mem_neighborFinset _ _).1 hx),
      ite_eq_right fun h ↦ hu ⟨hs.1, hs.2, h⟩, mul_zero]
  · exact absurd ⟨hu.1, hu.2.1⟩ hs
  · rw [mul_zero]

include hr in
/-- The zigzag relation for the generator matrices at the consecutive positions `b` and `c`, with
the one at `b` outside. -/
theorem pathGenerator_zigzag_left {a b c d : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hcd : c.val + 1 = d.val) :
    pathGenerator G v₀ r a b c * pathGenerator G v₀ r b c d * pathGenerator G v₀ r a b c =
      pathGenerator G v₀ r a b c := by
  have hab' : a ≠ b := Fin.ne_of_val_ne (by omega)
  have hac : a ≠ c := Fin.ne_of_val_ne (by omega)
  have hbd : b ≠ d := Fin.ne_of_val_ne (by omega)
  have hcb : c ≠ b := Fin.ne_of_val_ne (by omega)
  ext s v
  rw [mul_assoc, pathGenerator_mul_apply, pathGenerator_apply]
  by_cases hs : G.IsWalkFrom v₀ s ∧ s a = s c
  · -- Only the move of the vertex at `b` to `s d` survives the middle generator, and then only
    -- the move of the vertex at `c` back to `s a` survives the last one.
    have hdmem : s d ∈ G.neighborFinset (s a) := by
      rw [SimpleGraph.mem_neighborFinset, hs.2]; exact hs.1.adj hcd
    rw [ite_eq_left hs, Finset.sum_eq_single_of_mem (s d) hdmem fun x _ hxd ↦ by
      rw [pathGenerator_mul_apply, update_self, update_of_ne hbd.symm,
        ite_eq_right fun h ↦ hxd h.2, mul_zero]]
    have hwalk := hs.1.update hab hbc hs.2 ((G.mem_neighborFinset _ _).1 hdmem)
    have hamem : s a ∈ G.neighborFinset (s d) := by
      rw [SimpleGraph.mem_neighborFinset, hs.2]; exact (hs.1.adj hcd).symm
    rw [pathGenerator_mul_apply, update_self, update_of_ne hbd.symm, update_of_ne hcb,
      ite_eq_left ⟨hwalk, rfl⟩, Finset.sum_eq_single_of_mem (s a) hamem fun y _ hya ↦ by
        rw [pathGenerator_apply, update_of_ne hac, update_of_ne hab', update_self,
          ite_eq_right fun h ↦ hya h.2.1.symm, mul_zero]]
    rw [show update (update s b (s d)) c (s a) = update s b (s d) by
        rw [hs.2, update_comm hcb.symm, update_eq_self],
      pathGenerator_update_apply hab hbc hs.1 hs.2 ((G.mem_neighborFinset _ _).1 hdmem)]
    simp only [hs, true_and]
    split_ifs
    · rw [← hs.2]
      have := hr (s a)
      have := hr (s d)
      field_simp
    · simp
  · rw [ite_eq_right hs, ite_eq_right fun h ↦ hs ⟨h.1, h.2.1⟩]

include hr in
/-- The zigzag relation for the generator matrices at the consecutive positions `b` and `c`, with
the one at `c` outside. -/
theorem pathGenerator_zigzag_right {a b c d : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (hcd : c.val + 1 = d.val) :
    pathGenerator G v₀ r b c d * pathGenerator G v₀ r a b c * pathGenerator G v₀ r b c d =
      pathGenerator G v₀ r b c d := by
  have hac : a ≠ c := Fin.ne_of_val_ne (by omega)
  have hbc' : b ≠ c := Fin.ne_of_val_ne (by omega)
  have hdc : d ≠ c := Fin.ne_of_val_ne (by omega)
  have hdb : d ≠ b := Fin.ne_of_val_ne (by omega)
  ext s v
  rw [mul_assoc, pathGenerator_mul_apply, pathGenerator_apply]
  by_cases hs : G.IsWalkFrom v₀ s ∧ s b = s d
  · -- Only the move of the vertex at `c` to `s a` survives the middle generator, and then only
    -- the move of the vertex at `b` to `s d` survives the last one.
    have hamem : s a ∈ G.neighborFinset (s b) := by
      rw [SimpleGraph.mem_neighborFinset]; exact (hs.1.adj hab).symm
    rw [ite_eq_left hs, Finset.sum_eq_single_of_mem (s a) hamem fun x _ hxa ↦ by
      rw [pathGenerator_mul_apply, update_self, update_of_ne hac,
        ite_eq_right fun h ↦ hxa h.2.symm, mul_zero]]
    have hwalk := hs.1.update hbc hcd hs.2 ((G.mem_neighborFinset _ _).1 hamem)
    have hdmem : s d ∈ G.neighborFinset (s a) := by
      rw [SimpleGraph.mem_neighborFinset, ← hs.2]; exact hs.1.adj hab
    rw [pathGenerator_mul_apply, update_self, update_of_ne hac, update_of_ne hbc',
      ite_eq_left ⟨hwalk, rfl⟩, Finset.sum_eq_single_of_mem (s d) hdmem fun y _ hyd ↦ by
        rw [pathGenerator_apply, update_self, ite_eq_right fun h ↦ hyd (by
          rw [update_of_ne hdb, update_of_ne hdc] at h; exact h.2.1), mul_zero]]
    rw [show update (update s c (s a)) b (s d) = update s c (s a) from
        update_eq_self_iff.2 (by rw [update_of_ne hbc', hs.2]),
      pathGenerator_update_apply hbc hcd hs.1 hs.2 ((G.mem_neighborFinset _ _).1 hamem)]
    simp only [hs, true_and]
    split_ifs
    · rw [← hs.2]
      have := hr (s a)
      have := hr (s b)
      field_simp
    · simp
  · rw [ite_eq_right hs, ite_eq_right fun h ↦ hs ⟨h.1, h.2.1⟩]

/-- The product of the generator matrices at two positions `b` and `b'` that neither neighbours
nor equals the other, as an explicit matrix: it moves both vertices independently. -/
theorem pathGenerator_mul_pathGenerator_apply {a b c a' b' c' : Fin (m + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (h₁ : b ≠ a') (h₂ : b ≠ b')
    (h₃ : b ≠ c') (s v : Fin (m + 1) → V) :
    (pathGenerator G v₀ r a b c * pathGenerator G v₀ r a' b' c') s v =
      if G.IsWalkFrom v₀ s ∧ s a = s c ∧ s a' = s c' ∧
          v = update (update s b (v b)) b' (v b') ∧ G.Adj (s a) (v b) ∧ G.Adj (s a') (v b') then
        r (s b) * r (v b) / r (s a) ^ 2 * (r (s b') * r (v b') / r (s a') ^ 2)
      else 0 := by
  rw [pathGenerator_mul_apply]
  by_cases hs : G.IsWalkFrom v₀ s ∧ s a = s c
  swap
  · rw [ite_eq_right hs, ite_eq_right fun h ↦ hs ⟨h.1, h.2.1⟩]
  rw [ite_eq_left hs]
  -- Only the move of the vertex at `b` to `v b` contributes.
  have hterm : ∀ x ∈ G.neighborFinset (s a), r (s b) * r x / r (s a) ^ 2 *
      pathGenerator G v₀ r a' b' c' (update s b x) v = if x = v b then
        (if s a' = s c' ∧ v = update (update s b (v b)) b' (v b') ∧ G.Adj (s a') (v b') then
          r (s b) * r (v b) / r (s a) ^ 2 * (r (s b') * r (v b') / r (s a') ^ 2) else 0)
      else 0 := by
    intro x hx
    rw [pathGenerator_apply, update_of_ne h₁.symm, update_of_ne h₃.symm, update_of_ne h₂.symm]
    have hw := hs.1.update hab hbc hs.2 ((G.mem_neighborFinset _ _).1 hx)
    by_cases hxv : x = v b
    · subst hxv
      simp only [hw, true_and, ite_true, mul_ite, mul_zero]
    · rw [ite_eq_right hxv, ite_eq_right fun h ↦ hxv ?_, mul_zero]
      have := congrFun h.2.2.1 b
      rw [update_of_ne h₂, update_self] at this
      exact this.symm
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp only [SimpleGraph.mem_neighborFinset]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- Generator matrices at positions `b` and `b'` that neither neighbour nor equal one another
commute. -/
theorem pathGenerator_mul_pathGenerator_comm {a b c a' b' c' : Fin (m + 1)}
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (hab' : a'.val + 1 = b'.val)
    (hbc' : b'.val + 1 = c'.val) (h₁ : b ≠ a') (h₂ : b ≠ b') (h₃ : b ≠ c') (h₄ : b' ≠ a)
    (h₅ : b' ≠ c) :
    pathGenerator G v₀ r a b c * pathGenerator G v₀ r a' b' c' =
      pathGenerator G v₀ r a' b' c' * pathGenerator G v₀ r a b c := by
  ext s v
  rw [pathGenerator_mul_pathGenerator_apply hab hbc h₁ h₂ h₃,
    pathGenerator_mul_pathGenerator_apply hab' hbc' h₄ h₂.symm h₅, update_comm h₂]
  split_ifs <;> first | ring1 | (exfalso; tauto)

/-- On walks, the generator matrix at positions away from the last one is extended from the
walks with one step fewer. -/
theorem pathGenerator_castSucc_apply {a b c : Fin (m + 1)} {s : Fin (m + 2) → V}
    (hs : G.IsWalkFrom v₀ s) (t : Fin (m + 2) → V) :
    pathGenerator G v₀ r a.castSucc b.castSucc c.castSucc s t =
      extendLast (α := fun _ ↦ V) (pathGenerator G v₀ r a b c) s t := by
  obtain ⟨s, y, rfl⟩ : ∃ s' y, s = Fin.snoc s' y := ⟨_, _, (Fin.snoc_init_self s).symm⟩
  obtain ⟨t, z, rfl⟩ : ∃ t' z, t = Fin.snoc t' z := ⟨_, _, (Fin.snoc_init_self t).symm⟩
  rw [isWalkFrom_snoc] at hs
  rw [pathGenerator_apply, extendLast_apply, pathGenerator_apply]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.init_snoc, ← Fin.snoc_update, Fin.snoc_inj,
    isWalkFrom_snoc, hs, true_and, eq_comm (a := z)]
  split_ifs <;> first | rfl | (exfalso; tauto)

end Generator

variable {G v₀ r}

section Rep

variable (hr : ∀ v, r v ≠ 0) {δ : K} {n : ℕ}

variable (G v₀) in
/-- The **path representation** of the Temperley–Lieb algebra on `n` strands with loop value `δ`,
on functions of the vertex sequences of length `n + 1`: the generator `e i` acts by the generator
matrix at position `i + 1`. The generator matrices are supported on the walks in `G` starting at
`v₀`, so on the functions supported on the other vertex sequences the representation acts through
the character sending every generator to `0`. -/
def pathRep (hδ : IsPathEigenvectorUpTo G v₀ r δ n) :
    TemperleyLieb K δ n →ₐ[K] Matrix (Fin (n + 1) → V) (Fin (n + 1) → V) K :=
  lift (fun i ↦ pathGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩)
    (fun _ ↦ pathGenerator_mul_self hr hδ rfl rfl)
    (fun {i j} h ↦ by
      obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj⟩ := j
      simp only at h
      rcases h with rfl | rfl
      · exact pathGenerator_zigzag_left hr rfl rfl rfl
      · exact pathGenerator_zigzag_right hr rfl rfl rfl)
    (fun {i j} h ↦ pathGenerator_mul_pathGenerator_comm rfl rfl rfl rfl
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega))

/-- The path representation sends the generator `e i` to the generator matrix at position
`i + 1`. -/
@[simp]
theorem pathRep_e (hδ : IsPathEigenvectorUpTo G v₀ r δ n) (i : Fin (n - 1)) :
    pathRep G v₀ hr hδ (e δ i) =
      pathGenerator G v₀ r ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ :=
  lift_e _ _ _ _ i

/-- The path representation preserves walks and their endpoints: its matrix entry at `s` and `t`
vanishes unless `s` and `t` are both walks from `v₀` or both not, and end at the same vertex. -/
theorem pathRep_apply_eq_zero (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x : TemperleyLieb K δ n) {s t : Fin (n + 1) → V}
    (h : ¬((G.IsWalkFrom v₀ s ↔ G.IsWalkFrom v₀ t) ∧ s (Fin.last n) = t (Fin.last n))) :
    pathRep G v₀ hr hδ x s t = 0 := by
  induction x using TemperleyLieb.induction generalizing s t with
  | e i =>
    rw [pathRep_e, pathGenerator_apply, ite_eq_right_iff]
    rintro ⟨hs, hac, hst, hadj⟩
    refine (h ⟨⟨fun _ ↦ ?_, fun _ ↦ hs⟩, ?_⟩).elim
    · rw [hst]
      exact hs.update rfl rfl hac hadj
    · rw [hst, update_of_ne (by simp [Fin.ext_iff]; omega)]
  | algebraMap k =>
    rw [AlgHom.commutes, Matrix.algebraMap_matrix_apply, ite_eq_right_iff]
    rintro rfl
    exact (h ⟨Iff.rfl, rfl⟩).elim
  | add x y hx hy => rw [map_add, Matrix.add_apply, hx h, hy h, add_zero]
  | mul x y hx hy =>
    rw [map_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    by_cases hsu : (G.IsWalkFrom v₀ s ↔ G.IsWalkFrom v₀ u) ∧ s (Fin.last n) = u (Fin.last n)
    · rw [hy fun hut ↦ h ⟨hsu.1.trans hut.1, hsu.2.trans hut.2⟩, mul_zero]
    · rw [hx hsu, zero_mul]

/-- On the rows of walks, adding a straight strand acts on the path representation by extending
walks by one step: the matrix of `strandIncl x` agrees with `extendLast` of the matrix of `x`. -/
theorem pathRep_strandIncl_apply (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2))
    (x : TemperleyLieb K δ (n + 1)) {s : Fin (n + 3) → V}
    (hs : G.IsWalkFrom v₀ s) (t : Fin (n + 3) → V) :
    pathRep G v₀ hr hδ (strandIncl x) s t =
      extendLast (α := fun _ ↦ V) (pathRep G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x) s t := by
  induction x using TemperleyLieb.induction generalizing s t with
  | e i =>
    rw [strandIncl_e, pathRep_e, pathRep_e, ← pathGenerator_castSucc_apply hs]
    simp only [Fin.castSucc_mk, Fin.val_castSucc]
  | algebraMap k => simp only [AlgHom.commutes]
  | add x y hx hy => simp only [map_add, Matrix.add_apply, hx hs, hy hs]
  | mul x y hx hy =>
    rw [map_mul, map_mul, map_mul, map_mul, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [hx hs]
    by_cases hu : G.IsWalkFrom v₀ u
    · rw [hy hu]
    -- A row of a walk has no entry in the column of a non-walk.
    rw [extendLast_apply, ite_eq_right_iff.2 fun hlast ↦
      pathRep_apply_eq_zero hr (hδ.mono (Nat.le_succ (n + 1))) x
        fun h ↦ hu ((isWalkFrom_iff_init u).2 ⟨h.1.1 ((isWalkFrom_iff_init s).1 hs).1, by
          rw [← h.2, ← hlast]; exact ((isWalkFrom_iff_init s).1 hs).2⟩), zero_mul, zero_mul]

end Rep

section Weight

variable (G v₀ r) in
/-- The weight of a vertex sequence in the trace of the path model: `(r v / r v₀) ^ 2` for a walk
from `v₀` ending at the vertex `v`, and `0` for every other sequence. -/
def pathWeight {m : ℕ} (s : Fin (m + 1) → V) : K :=
  if G.IsWalkFrom v₀ s then (r (s (Fin.last m)) / r v₀) ^ 2 else 0

omit [Fintype V] in
theorem pathWeight_def {m : ℕ} (s : Fin (m + 1) → V) :
    pathWeight G v₀ r s = if G.IsWalkFrom v₀ s then (r (s (Fin.last m)) / r v₀) ^ 2 else 0 :=
  (rfl)

/-- Extending walks by one step multiplies the total weight by `δ`: the weights of the neighbours
of the endpoint of an `m`-step walk add up to `δ` times the weight of that endpoint. -/
theorem sum_pathWeight_snoc {δ : K} {m : ℕ} (hδ : IsPathEigenvectorUpTo G v₀ r δ (m + 1))
    (t : Fin (m + 1) → V) :
    ∑ y, pathWeight G v₀ r (Fin.snoc t y : Fin (m + 2) → V) = δ * pathWeight G v₀ r t := by
  simp only [pathWeight_def, isWalkFrom_snoc, Fin.snoc_last, ite_and]
  split_ifs with ht
  · rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter]
    simp_rw [div_pow]
    rw [← Finset.sum_div, hδ (Nat.lt_succ_self m) ht, mul_div_assoc]
  · simp

end Weight

section Trace

variable (hr : ∀ v, r v ≠ 0) {δ : K} {n : ℕ}

variable (G v₀) in
/-- The **trace of the path model** on `n` strands: the trace of the path representation weighted
by `TauCeti.TemperleyLieb.pathWeight`. Given `IsPathEigenvectorUpTo G v₀ r δ n`, its restrictions
form a Markov trace up to `n` strands (`TauCeti.TemperleyLieb.isMarkovTraceUpTo_pathTrace`). -/
def pathTrace (hδ : IsPathEigenvectorUpTo G v₀ r δ n) : TemperleyLieb K δ n →ₗ[K] K :=
  traceLinearMap (Fin (n + 1) → V) K K ∘ₗ LinearMap.mulLeft K (diagonal (pathWeight G v₀ r)) ∘ₗ
    (pathRep G v₀ hr hδ).toLinearMap

/-- The trace of the path model is the weighted trace of the path representation. -/
theorem pathTrace_apply (hδ : IsPathEigenvectorUpTo G v₀ r δ n) (x : TemperleyLieb K δ n) :
    pathTrace G v₀ hr hδ x = trace (diagonal (pathWeight G v₀ r) * pathRep G v₀ hr hδ x) :=
  (rfl)

/-- The trace of the path model of the identity on `n` strands is `δ ^ n`. -/
@[simp]
theorem pathTrace_one (hδ : IsPathEigenvectorUpTo G v₀ r δ n) :
    pathTrace G v₀ hr hδ (1 : TemperleyLieb K δ n) = δ ^ n := by
  rw [pathTrace_apply, map_one, mul_one, trace_diagonal]
  induction n with
  | zero =>
    rw [Fintype.sum_eq_single (fun _ ↦ v₀) fun s hs ↦ ?_, pow_zero, pathWeight_def,
      ite_eq_left ((isWalkFrom_zero (v₀ := v₀) _).2 rfl), div_self (hr v₀), one_pow]
    rw [pathWeight_def, ite_eq_right fun h ↦ hs (funext fun i ↦ by
      rw [Fin.fin_one_eq_zero i]; exact h.apply_zero)]
  | succ n ih =>
    rw [Fintype.sum_fin_snoc, Finset.sum_congr rfl fun t _ ↦ sum_pathWeight_snoc hδ t,
      ← Finset.mul_sum, ih (hδ.mono (Nat.le_succ n)), pow_succ, mul_comm]

/-- The weight matrix of the path model commutes with the path representation, since the latter
preserves walks and their endpoints. -/
theorem commute_diagonal_pathWeight_pathRep (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x : TemperleyLieb K δ n) :
    Commute (diagonal (pathWeight G v₀ r)) (pathRep G v₀ hr hδ x) := by
  ext s t
  rw [diagonal_mul, mul_diagonal]
  by_cases h : (G.IsWalkFrom v₀ s ↔ G.IsWalkFrom v₀ t) ∧ s (Fin.last n) = t (Fin.last n)
  · rw [pathWeight_def, pathWeight_def, if_congr h.1 (by rw [h.2]) rfl, mul_comm]
  · rw [pathRep_apply_eq_zero hr hδ x h, mul_zero, zero_mul]

/-- **The trace property** of the trace of the path model. -/
theorem pathTrace_mul_comm (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x y : TemperleyLieb K δ n) :
    pathTrace G v₀ hr hδ (x * y) = pathTrace G v₀ hr hδ (y * x) := by
  rw [pathTrace_apply, pathTrace_apply, map_mul, map_mul, ← mul_assoc,
    (commute_diagonal_pathWeight_pathRep hr hδ x).eq, mul_assoc, trace_mul_comm, mul_assoc]

/-- On the diagonal weighted by walks, the path representation of `strandIncl x` agrees with
`extendLast` of the path representation of `x`. -/
private theorem pathWeight_mul_pathRep_strandIncl (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2))
    (x : TemperleyLieb K δ (n + 1)) (s t : Fin (n + 3) → V) :
    pathWeight G v₀ r s * pathRep G v₀ hr hδ (strandIncl x) s t =
      pathWeight G v₀ r s *
        extendLast (α := fun _ ↦ V) (pathRep G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x) s t := by
  by_cases hs : G.IsWalkFrom v₀ s
  · rw [pathRep_strandIncl_apply hr hδ x hs]
  · rw [pathWeight_def, ite_eq_right hs, zero_mul, zero_mul]

/-- Adding a straight strand multiplies the trace of the path model by `δ`. -/
@[simp]
theorem pathTrace_strandIncl (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2))
    (x : TemperleyLieb K δ (n + 1)) :
    pathTrace G v₀ hr hδ (strandIncl x) =
      δ * pathTrace G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x := by
  simp only [pathTrace_apply, trace, Matrix.diag_apply, diagonal_mul]
  rw [Finset.sum_congr rfl fun s _ ↦ pathWeight_mul_pathRep_strandIncl hr hδ x s s,
    Fintype.sum_fin_snoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [extendLast_apply, Fin.init_snoc, ite_true]
  rw [← Finset.sum_mul, sum_pathWeight_snoc hδ, mul_assoc]

/-- The weighted partial trace over the last step of walks, against the generator matrix capping
the last step with the previous one, recovers the weighted trace one level down. -/
private theorem trace_pathGenerator_mul_pathRep_strandIncl
    (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2)) (x : TemperleyLieb K δ (n + 1))
    {a b c : Fin (n + 3)} (ha : a.val = n) (hb : b.val = n + 1) (hc : c.val = n + 2) :
    trace (pathGenerator G v₀ r a b c *
        (diagonal (pathWeight G v₀ r) * pathRep G v₀ hr hδ (strandIncl x))) =
      trace (diagonal (pathWeight G v₀ r) *
        pathRep G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x) := by
  obtain ⟨a', rfl, ha'⟩ : ∃ a' : Fin (n + 2), a = a'.castSucc ∧ a'.val = n :=
    ⟨⟨n, by omega⟩, Fin.ext ha, rfl⟩
  obtain rfl : b = (Fin.last (n + 1)).castSucc := Fin.ext hb
  obtain rfl : c = Fin.last (n + 2) := Fin.ext hc
  simp only [trace, Matrix.diag_apply, pathGenerator_mul_apply, diagonal_mul]
  rw [Fintype.sum_fin_snoc]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [Fin.snoc_castSucc, Fin.snoc_last, isWalkFrom_snoc]
  have ha'l : a'.val + 1 = (Fin.last (n + 1)).val := by simp [ha']
  by_cases ht : G.IsWalkFrom v₀ t
  swap
  · -- Neither side sees a sequence that is not a walk.
    rw [Finset.sum_eq_zero fun y _ ↦ by rw [ite_eq_right fun h ↦ ht h.1.1], pathWeight_def,
      ite_eq_right ht, zero_mul]
  have hadj := ht.adj ha'l
  rw [Fintype.sum_eq_single (t a') fun y hy ↦ ite_eq_right fun h ↦ hy h.2.symm,
    ite_eq_left ⟨⟨ht, hadj.symm⟩, rfl⟩]
  -- Only the move of the vertex at the penultimate position back to `t (Fin.last _)` survives.
  rw [Fin.snoc_castSucc]
  rw [Finset.sum_eq_single_of_mem (t (Fin.last (n + 1))) ((G.mem_neighborFinset _ _).2 hadj)
    fun z _ hz ↦ by
      rw [← Fin.snoc_update, pathWeight_mul_pathRep_strandIncl hr hδ x, extendLast_apply,
        Fin.init_snoc, Fin.init_snoc, Fin.snoc_last, Fin.snoc_last, ite_eq_left rfl,
        pathRep_apply_eq_zero hr (hδ.mono (Nat.le_succ (n + 1))) x fun h ↦ hz (by simpa using h.2),
        mul_zero, mul_zero]]
  rw [update_eq_self_iff.2 (Fin.snoc_castSucc ..).symm, pathWeight_mul_pathRep_strandIncl hr hδ x,
    extendLast_apply, ite_eq_left rfl, Fin.init_snoc, pathWeight_def, pathWeight_def,
    ite_eq_left ((isWalkFrom_snoc t _).2 ⟨ht, hadj.symm⟩), ite_eq_left ht, Fin.snoc_last]
  have := hr (t a')
  field_simp

/-- **The Markov property** of the trace of the path model: capping the added last strand with the
previous one does not change the trace. -/
@[simp]
theorem pathTrace_strandIncl_mul_e_last (hδ : IsPathEigenvectorUpTo G v₀ r δ (n + 2))
    (x : TemperleyLieb K δ (n + 1)) :
    pathTrace G v₀ hr hδ (strandIncl x * e δ (Fin.last n)) =
      pathTrace G v₀ hr (hδ.mono (Nat.le_succ (n + 1))) x := by
  rw [pathTrace_apply, pathTrace_apply, map_mul, pathRep_e, ← mul_assoc, trace_mul_comm]
  exact trace_pathGenerator_mul_pathRep_strandIncl hr hδ x rfl rfl rfl

variable (G v₀) in
/-- Given the eigenvector equation up to `n` steps, the trace of the path model is an unnormalized
Markov trace up to `n` strands. -/
theorem isMarkovTraceUpTo_pathTrace (hδ : IsPathEigenvectorUpTo G v₀ r δ n) :
    IsMarkovTraceUpTo K δ n (fun _ hm ↦ pathTrace G v₀ hr (hδ.mono hm)) :=
  ⟨fun _ hm ↦ pathTrace_one hr (hδ.mono hm),
    fun _ hm x y ↦ pathTrace_mul_comm hr (hδ.mono hm) x y,
    fun _ hm x ↦ pathTrace_strandIncl hr (hδ.mono hm) x,
    fun _ hm x ↦ pathTrace_strandIncl_mul_e_last hr (hδ.mono hm) x⟩

variable (G v₀) in
/-- Given the eigenvector equation up to `n` steps, every Markov trace on the full tower agrees on
`m ≤ n` strands with the trace of the path model. -/
theorem IsMarkovTrace.eq_pathTrace_of_isPathEigenvectorUpTo
    {tr : ∀ k : ℕ, TemperleyLieb K δ k →ₗ[K] K} (htr : IsMarkovTrace K δ tr)
    (hδ : IsPathEigenvectorUpTo G v₀ r δ n) {m : ℕ} (hm : m ≤ n) :
    tr m = pathTrace G v₀ hr (hδ.mono hm) :=
  htr.eq_of_isMarkovTraceUpTo (isMarkovTraceUpTo_pathTrace G v₀ hr hδ) hm

variable (G v₀) in
/-- Under a global adjacency eigenvector, the trace of the path model is an unnormalized Markov
trace on the full tower. -/
theorem isMarkovTrace_pathTrace (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) :
    IsMarkovTrace K δ (fun m ↦ pathTrace G v₀ hr (.of_forall hδ m)) :=
  ⟨fun m ↦ pathTrace_one hr (.of_forall hδ m),
    fun m x y ↦ pathTrace_mul_comm hr (.of_forall hδ m) x y,
    fun m x ↦ pathTrace_strandIncl hr (.of_forall hδ (m + 2)) x,
    fun m x ↦ pathTrace_strandIncl_mul_e_last hr (.of_forall hδ (m + 2)) x⟩

variable (G v₀) in
/-- Under a global adjacency eigenvector, every Markov trace at the loop value `δ` is the trace of
the path model, by uniqueness of Markov traces. -/
theorem IsMarkovTrace.eq_pathTrace {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr)
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2) :
    tr = fun m ↦ pathTrace G v₀ hr (.of_forall hδ m) :=
  htr.unique (isMarkovTrace_pathTrace G v₀ hr hδ)

end Trace

section Star

variable [StarRing K]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The defining condition of a nonzero entry of a generator matrix is symmetric in the two
vertex sequences, which then agree at the position `a`. -/
private theorem pathGenerator_cond_symm {m : ℕ} {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) {s t : Fin (m + 1) → V}
    (h : G.IsWalkFrom v₀ s ∧ s a = s c ∧ t = update s b (t b) ∧ G.Adj (s a) (t b)) :
    (G.IsWalkFrom v₀ t ∧ t a = t c ∧ s = update t b (s b) ∧ G.Adj (t a) (s b)) ∧ t a = s a := by
  obtain ⟨hs, hac, hst, hadj⟩ := h
  have ha : t a = s a := by rw [hst, update_of_ne (Fin.ne_of_val_ne (by omega))]
  have hc : t c = s c := by rw [hst, update_of_ne (Fin.ne_of_val_ne (by omega))]
  refine ⟨⟨?_, by rw [ha, hc, hac], ?_, by rw [ha]; exact hs.adj hab⟩, ha⟩
  · rw [hst]
    exact hs.update hab hbc hac hadj
  · rw [hst, update_idem, update_eq_self]

omit [Fintype V] in
/-- For self-adjoint weights `r`, the generator matrices of the path model are self-adjoint. -/
theorem conjTranspose_pathGenerator (hrs : ∀ v, IsSelfAdjoint (r v)) {m : ℕ}
    {a b c : Fin (m + 1)} (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) :
    (pathGenerator G v₀ r a b c)ᴴ = pathGenerator G v₀ r a b c := by
  ext s t
  rw [conjTranspose_apply, pathGenerator_apply, pathGenerator_apply]
  by_cases h : G.IsWalkFrom v₀ s ∧ s a = s c ∧ t = update s b (t b) ∧ G.Adj (s a) (t b)
  · obtain ⟨h', ha⟩ := pathGenerator_cond_symm hab hbc h
    rw [ite_eq_left h', ite_eq_left h, ha]
    simp [(hrs _).star_eq, mul_comm]
  · rw [ite_eq_right h, ite_eq_right fun h' ↦ h (pathGenerator_cond_symm hab hbc h').1,
      star_zero]

variable (hr : ∀ v, r v ≠ 0) (hrs : ∀ v, IsSelfAdjoint (r v)) {δ : K} [Fact (IsSelfAdjoint δ)]
  {n : ℕ}

include hrs in
/-- For self-adjoint weights `r`, the path representation carries the analytic adjoint of the
Temperley–Lieb algebra to the conjugate transpose of matrices. -/
@[simp]
theorem pathRep_star (hδ : IsPathEigenvectorUpTo G v₀ r δ n) (x : TemperleyLieb K δ n) :
    pathRep G v₀ hr hδ (star x) = (pathRep G v₀ hr hδ x)ᴴ := by
  refine (map_star_iff.mpr fun i ↦ ?_) x
  rw [pathRep_e, IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_pathGenerator hrs rfl rfl]

variable [PartialOrder K] [StarOrderedRing K]

omit [Fintype V] in
include hrs in
/-- For self-adjoint weights `r`, every vertex sequence has nonnegative weight. -/
theorem pathWeight_nonneg {m : ℕ} (s : Fin (m + 1) → V) : 0 ≤ pathWeight G v₀ r s := by
  rw [pathWeight_def]
  split_ifs
  · exact ((hrs _).div (hrs _)).sq_nonneg
  · exact le_rfl

include hrs in
/-- **Positivity of the trace of the path model.** For self-adjoint weights `r`, the trace of the
path model is nonnegative on every element of the form `x⋆ * x`. -/
theorem pathTrace_star_mul_self_nonneg (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    (x : TemperleyLieb K δ n) :
    0 ≤ pathTrace G v₀ hr hδ (star x * x) := by
  -- The trace of `D * Aᴴ * A` is the trace of `A * D * Aᴴ`, with `D` a nonnegative diagonal.
  rw [pathTrace_apply, map_mul, pathRep_star hr hrs, ← mul_assoc, trace_mul_comm, ← mul_assoc]
  exact ((posSemidef_diagonal_iff.2 fun s ↦ pathWeight_nonneg hrs s).mul_mul_conjTranspose_same
    _).trace_nonneg

omit [DecidableEq V] in
include hr hrs in
/-- **Bounded-depth positivity of a Markov trace from a path model.** Let `G` be a finite graph
with a base vertex `v₀` and a vertex weighting `r` by nonzero self-adjoint scalars whose squares
satisfy the adjacency eigenvector equation with eigenvalue `δ` at the endpoints of all walks from
`v₀` with fewer than `n` steps. Then on `n` strands every Markov trace at the loop value `δ` is
nonnegative on every element of the form `x⋆ * x`. -/
theorem IsMarkovTrace.map_star_mul_self_nonneg_of_isPathEigenvectorUpTo
    (hδ : IsPathEigenvectorUpTo G v₀ r δ n)
    {tr : ∀ k : ℕ, TemperleyLieb K δ k →ₗ[K] K} (htr : IsMarkovTrace K δ tr)
    (x : TemperleyLieb K δ n) : 0 ≤ tr n (star x * x) := by
  classical
  rw [htr.eq_pathTrace_of_isPathEigenvectorUpTo G v₀ hr hδ le_rfl]
  exact pathTrace_star_mul_self_nonneg hr hrs hδ x

omit [DecidableEq V] in
include hr hrs in
/-- **Positivity of a Markov trace from a path model.** Let `G` be a nonempty finite graph with a
vertex weighting `r` by nonzero self-adjoint scalars whose squares form an eigenvector of the
adjacency matrix with eigenvalue `δ`. Then every Markov trace at the loop value `δ` is nonnegative
on every element of the form `x⋆ * x`. -/
theorem IsMarkovTrace.map_star_mul_self_nonneg_of_graph [Nonempty V]
    (hδ : ∀ v, ∑ u ∈ G.neighborFinset v, r u ^ 2 = δ * r v ^ 2)
    {tr : ∀ k : ℕ, TemperleyLieb K δ k →ₗ[K] K} (htr : IsMarkovTrace K δ tr)
    (x : TemperleyLieb K δ n) : 0 ≤ tr n (star x * x) :=
  htr.map_star_mul_self_nonneg_of_isPathEigenvectorUpTo hr hrs
    (.of_forall (v₀ := Classical.arbitrary V) hδ n) x

end Star

end TauCeti.TemperleyLieb
