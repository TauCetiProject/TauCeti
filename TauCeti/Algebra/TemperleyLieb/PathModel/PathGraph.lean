/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.PathModel
public import TauCeti.QuantumGroups.QuantumInteger.Order
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.StdBasis
import TauCeti.Algebra.TemperleyLieb.Dimension
import TauCeti.Algebra.TemperleyLieb.TypeA
import TauCeti.Combinatorics.SimpleGraph.PathGraph.Counting
import TauCeti.Data.Fintype.BigOperators

/-!
# The image of the path model on a path graph

On the Dynkin graph `A_(k+1)`, realized as `SimpleGraph.pathGraph (k + 1)`, take the end vertex `0`
as base vertex and nonzero vertex weights satisfying the eigenvector equation up to depth `n`
(`TauCeti.TemperleyLieb.IsPathEigenvectorUpTo`). This file proves that the path representation on
walks (`TauCeti.TemperleyLieb.walkRep`) of the Temperley–Lieb algebra on `n` strands maps onto the
*path algebra*: the matrices on the walks from `0` with `n` steps whose entries between walks with
different endpoints vanish, that is, the direct sum over the vertices `v` of the full matrix
algebras on the walks ending at `v`. For self-adjoint weights in a star-ordered field (such as
real weights over `ℂ`), together with `TauCeti.TemperleyLieb.ker_walkRep`, this identifies the
quotient of the Temperley–Lieb algebra by the trace radical with the path algebra.

The proof is an induction on the number of strands. Adding a strand extends walks by one step
(`TauCeti.TemperleyLieb.walkRep_strandIncl_apply`), so a diagonal matrix unit on `n + 1` steps
becomes the projection onto the one-step extensions of a walk. Compressing the last generator
(`TauCeti.TemperleyLieb.walkRep_e_last_apply_snoc_snoc`) by this projection isolates the extension
that turns back. On a path graph every vertex has at most two neighbours, so the other extension is
the difference, and every diagonal matrix unit is in the image. Compressions of strand inclusions
of off-diagonal matrix units then join walks with the same last two vertices. Two walks that end at
`z` from different penultimate vertices arrive from `z - 1` and from `z + 1`, so some walk with one
step fewer ends at `z`, and the last generator joins its two extensions through `z - 1` and `z + 1`.

When the path graph has at least `n + 1` vertices, the walks from `0` with `n` steps never try to
step past the top vertex, so it never restricts them. Their endpoint multiplicities are ballot
numbers, and the pairs of walks with a common endpoint number `catalan n`. So the image has
dimension at least `catalan n`, and the Catalan bound on the Temperley–Lieb algebra makes the path
representation injective. With positive weights
`√[t + 1]`, this shows that the trace radical of every Markov trace on `n` strands vanishes whenever
the quantum integers `[1], …, [n + 1]` are positive, in particular for `δ ≥ 2`.

## Main results

* `TauCeti.TemperleyLieb.mem_range_walkRep_pathGraph_iff`: the image of the path representation on
  walks in the path graph is the path algebra.
* `TauCeti.TemperleyLieb.walkRep_pathGraph_injective`: on a path graph with at least `n + 1`
  vertices, the path representation on walks with `n` steps is injective.
* `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_bot_of_qInt_pos`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_bot_of_two_le`: the trace radical of a
  Markov trace vanishes on `n` strands when `[1], …, [n + 1]` are positive, and on every number of
  strands when `δ ≥ 2`.

## References

* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989 (path algebras of graphs and their Temperley–Lieb
  representations).
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, §4.4 (the tree basis
  (TB1)–(TB7) for `δ ≥ 2`) and §4.5 (paths on `A_(m-1)` at `δ = 2 cos (π / m)`).
* H. Wenzl, *Hecke algebras of type `A_n` and subfactors*, Invent. Math. 92 (1988), 349–383.
-/

public section

open Function Matrix SimpleGraph

namespace TauCeti.TemperleyLieb

variable {k : ℕ}

/-- On the path graph, there is at most one walk from `0` with at most one step. -/
private theorem subsingleton_walk_pathGraph {m : ℕ} (hm : m ≤ 1) :
    Subsingleton {s : Fin (m + 1) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s} := by
  refine ⟨fun u v ↦ Subtype.ext (funext fun i ↦ ?_)⟩
  obtain hi | hi : i = 0 ∨ (0 : Fin (m + 1)).val + 1 = i.val := by
    rw [Fin.ext_iff]; simp only [Fin.val_zero]; omega
  · rw [hi, u.property.apply_zero, v.property.apply_zero]
  · have h₁ := u.property.adj hi
    have h₂ := v.property.adj hi
    rw [u.property.apply_zero, pathGraph_adj] at h₁
    rw [v.property.apply_zero, pathGraph_adj] at h₂
    simp only [Fin.val_zero] at h₁ h₂
    exact Fin.ext (by omega)

section Range

variable {K : Type*} [Field K] {r : Fin (k + 1) → K} (hr : ∀ v, r v ≠ 0) {δ : K} {n : ℕ}

/-- The strand inclusion of an element acting by a matrix unit on the walks with one step fewer
acts by the matrix with entry `1` at the walks extending its two indices by the same vertex. -/
private theorem exists_mem_range_walkRep_apply_eq_of_single_mem
    (hδ : IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ (n + 2))
    {a b : {s : Fin (n + 2) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s}}
    (hab : single a b 1 ∈ (walkRep _ 0 hr (hδ.mono (Nat.le_succ (n + 1)))).range) :
    ∃ M ∈ (walkRep _ 0 hr hδ).range, ∀ u v, M u v =
      if u.val (Fin.last (n + 2)) = v.val (Fin.last (n + 2)) ∧ Fin.init u.val = a.val ∧
        Fin.init v.val = b.val then 1 else 0 := by
  obtain ⟨x, hx⟩ := (AlgHom.mem_range _).1 hab
  refine ⟨_, (AlgHom.mem_range _).2 ⟨strandIncl x, rfl⟩, fun u v ↦ ?_⟩
  rw [walkRep_strandIncl_apply, hx]
  simp only [single_apply, Subtype.ext_iff, eq_comm (a := a.val), eq_comm (a := b.val)]
  split_ifs <;> tauto

/-- The strand inclusion of an element acting by the diagonal matrix unit at a walk `w` with
`n + 1` steps acts by the diagonal projection onto the one-step extensions of `w`. -/
private theorem diagonal_mem_range_walkRep_of_single_mem
    (hδ : IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ (n + 2))
    {w : {s : Fin (n + 2) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s}}
    (hw : single w w 1 ∈ (walkRep _ 0 hr (hδ.mono (Nat.le_succ (n + 1)))).range) :
    (diagonal fun u : {s : Fin (n + 3) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s} ↦
      if Fin.init u.val = w.val then (1 : K) else 0) ∈ (walkRep _ 0 hr hδ).range := by
  obtain ⟨D, hD, hDapp⟩ := exists_mem_range_walkRep_apply_eq_of_single_mem hr hδ hw
  convert hD using 1
  ext u v
  by_cases huv : u = v
  · subst huv
    simp [hDapp]
  · rw [diagonal_apply_ne _ huv, hDapp]
    refine (ite_eq_right_iff.2 fun ⟨hl, hu, hv⟩ ↦ (huv (Subtype.ext ?_)).elim).symm
    rw [← Fin.snoc_init_self u.val, ← Fin.snoc_init_self v.val, hu, hv, hl]

/-- Compressing the last generator by the diagonal projection onto the one-step extensions of the
walk `p a` leaves a nonzero multiple of the diagonal matrix unit at the extension `p a p'` that
turns back to the endpoint `p' = p (Fin.last n)` of `p`. -/
private theorem diagonal_mul_walkRep_e_last_mul_diagonal
    (hδ : IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ (n + 2))
    {p : Fin (n + 1) → Fin (k + 1)} {a : Fin (k + 1)}
    (hs : (pathGraph (k + 1)).IsWalkFrom 0
      (Fin.snoc (Fin.snoc p a : Fin (n + 2) → Fin (k + 1)) (p (Fin.last n)) :
        Fin (n + 3) → Fin (k + 1))) :
    (diagonal fun u : {s : Fin (n + 3) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s} ↦
        if Fin.init u.val = Fin.snoc p a then (1 : K) else 0) *
      walkRep _ 0 hr hδ (e δ (Fin.last n)) *
      (diagonal fun u : {s : Fin (n + 3) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s} ↦
        if Fin.init u.val = Fin.snoc p a then (1 : K) else 0) =
      (r a ^ 2 / r (p (Fin.last n)) ^ 2) • single ⟨_, hs⟩ ⟨_, hs⟩ 1 := by
  ext ⟨u, hu⟩ ⟨v, hv⟩
  induction u using Fin.snocCases with | snoc u d
  induction u using Fin.snocCases with | snoc q c
  induction v using Fin.snocCases with | snoc v d'
  induction v using Fin.snocCases with | snoc q' c'
  rw [mul_diagonal, diagonal_mul, walkRep_e_last_apply_snoc_snoc, Matrix.smul_apply]
  simp only [single_apply, Fin.init_snoc, Fin.snoc_inj, Subtype.mk.injEq, smul_eq_mul]
  split_ifs <;> grind

/-- On the path graph, the one-step extensions of the walk `p a` are the extension `p a b` and the
extension that turns back to the endpoint `p (Fin.last n)` of `p`, when these differ. -/
private theorem single_eq_diagonal_sub_single
    {p : Fin (n + 1) → Fin (k + 1)} {a b : Fin (k + 1)}
    (hs : (pathGraph (k + 1)).IsWalkFrom 0
      (Fin.snoc (Fin.snoc p a : Fin (n + 2) → Fin (k + 1)) b : Fin (n + 3) → Fin (k + 1)))
    (hs' : (pathGraph (k + 1)).IsWalkFrom 0
      (Fin.snoc (Fin.snoc p a : Fin (n + 2) → Fin (k + 1)) (p (Fin.last n)) :
        Fin (n + 3) → Fin (k + 1)))
    (hb : b ≠ p (Fin.last n)) :
    single ⟨_, hs⟩ ⟨_, hs⟩ (1 : K) =
      (diagonal fun u : {s : Fin (n + 3) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s} ↦
        if Fin.init u.val = Fin.snoc p a then (1 : K) else 0) - single ⟨_, hs'⟩ ⟨_, hs'⟩ 1 := by
  ext u v
  by_cases huv : u = v
  · subst huv
    obtain ⟨u, hu⟩ := u
    induction u using Fin.snocCases with | snoc u d
    induction u using Fin.snocCases with | snoc q c
    rw [Matrix.sub_apply, diagonal_apply_eq]
    simp only [single_apply, Fin.init_snoc, Fin.snoc_inj, Subtype.mk.injEq, and_self]
    by_cases hqc : q = p ∧ c = a
    · obtain ⟨rfl, rfl⟩ := hqc
      -- `d`, `b` and the endpoint of `q` are neighbours of `c`, and the last two differ
      have hcd := ((isWalkFrom_snoc _ _).1 hu).2
      have hcb := ((isWalkFrom_snoc _ _).1 hs).2
      have hqc := ((isWalkFrom_snoc _ _).1 ((isWalkFrom_snoc _ _).1 hs).1).2
      simp only [Fin.snoc_last, pathGraph_adj] at hcd hcb hqc
      obtain rfl | rfl : d = b ∨ d = q (Fin.last n) := by
        simp only [Fin.ext_iff] at hb ⊢; omega
      all_goals simp [hb, Ne.symm hb]
    · have hqc' : ¬(p = q ∧ a = c) := fun h ↦ hqc ⟨h.1.symm, h.2.symm⟩
      simp [hqc, hqc']
  · rw [Matrix.sub_apply, diagonal_apply_ne _ huv]
    simp only [single_apply]
    rw [ite_eq_right_iff.2 fun h ↦ (huv (h.1.symm.trans h.2)).elim,
      ite_eq_right_iff.2 fun h ↦ (huv (h.1.symm.trans h.2)).elim, sub_zero]

/-- Every diagonal matrix unit at the walks with `n + 2` steps lies in the image of the path
representation, given the diagonal matrix units at the walks with `n + 1` steps. -/
private theorem single_self_mem_range_walkRep
    (hδ : IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ (n + 2))
    (ih : ∀ a : {s : Fin (n + 2) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s},
      single a a 1 ∈ (walkRep _ 0 hr (hδ.mono (Nat.le_succ (n + 1)))).range)
    (s : {s : Fin (n + 3) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s}) :
    single s s 1 ∈ (walkRep _ 0 hr hδ).range := by
  set A := (walkRep _ 0 hr hδ).range
  obtain ⟨s, hs⟩ := s
  induction s using Fin.snocCases with | snoc s b
  induction s using Fin.snocCases with | snoc p a
  have hw := ((isWalkFrom_snoc _ _).1 hs).1
  -- the walk `p a (p (Fin.last n))`, which turns back in its last step
  have hs' : (pathGraph (k + 1)).IsWalkFrom 0
      (Fin.snoc (Fin.snoc p a : Fin (n + 2) → Fin (k + 1)) (p (Fin.last n)) :
        Fin (n + 3) → Fin (k + 1)) :=
    (isWalkFrom_snoc _ _).2 ⟨hw, by rw [Fin.snoc_last]; exact ((isWalkFrom_snoc _ _).1 hw).2.symm⟩
  have hD := diagonal_mem_range_walkRep_of_single_mem hr hδ (ih ⟨_, hw⟩)
  have hs'mem : single ⟨_, hs'⟩ ⟨_, hs'⟩ 1 ∈ A := by
    have hc : r a ^ 2 / r (p (Fin.last n)) ^ 2 ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (hr a)) (pow_ne_zero _ (hr _))
    have h := A.smul_mem (A.mul_mem (A.mul_mem hD
      ((AlgHom.mem_range _).2 ⟨e δ (Fin.last n), rfl⟩)) hD) (r a ^ 2 / r (p (Fin.last n)) ^ 2)⁻¹
    rwa [diagonal_mul_walkRep_e_last_mul_diagonal hr hδ hs', smul_smul, inv_mul_cancel₀ hc,
      one_smul] at h
  by_cases hb : b = p (Fin.last n)
  · subst hb
    exact hs'mem
  rw [single_eq_diagonal_sub_single hs hs' hb]
  exact A.sub_mem hD hs'mem

/-- Given the matrix units at the walks with `n + 1` steps, the matrix unit between two walks
with `n + 2` steps and the same last two vertices lies in the image of the path representation. -/
private theorem single_mem_range_walkRep_of_apply_eq
    (hδ : IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ (n + 2))
    (ih : ∀ a b : {s : Fin (n + 2) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s},
      a.val (Fin.last (n + 1)) = b.val (Fin.last (n + 1)) →
        single a b 1 ∈ (walkRep _ 0 hr (hδ.mono (Nat.le_succ (n + 1)))).range)
    {u v : {s : Fin (n + 3) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s}}
    (h₁ : u.val (Fin.last (n + 2)) = v.val (Fin.last (n + 2)))
    (h₂ : u.val (Fin.last (n + 1)).castSucc = v.val (Fin.last (n + 1)).castSucc) :
    single u v 1 ∈ (walkRep _ 0 hr hδ).range := by
  set A := (walkRep _ 0 hr hδ).range
  have hdiag := single_self_mem_range_walkRep hr hδ fun a ↦ ih a a rfl
  obtain ⟨M, hM, hMapp⟩ := exists_mem_range_walkRep_apply_eq_of_single_mem hr hδ
    (ih ⟨Fin.init u.val, u.property.init⟩ ⟨Fin.init v.val, v.property.init⟩ h₂)
  have h := A.mul_mem (A.mul_mem (hdiag u) hM) (hdiag v)
  rwa [single_mul_mul_single, hMapp, ite_eq_left ⟨h₁, rfl, rfl⟩, one_mul, mul_one] at h

/-- Given the diagonal matrix units at the walks with `n + 2` steps, the last generator joins the
two extensions `p x z` and `p y z` of a walk `p` with `n` steps ending at `z` through neighbours
`x` and `y` of `z`. -/
private theorem single_snoc_snoc_mem_range_walkRep
    (hδ : IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ (n + 2))
    (hdiag : ∀ s : {s : Fin (n + 3) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s},
      single s s 1 ∈ (walkRep _ 0 hr hδ).range)
    {p : Fin (n + 1) → Fin (k + 1)} {x y z : Fin (k + 1)} (hpz : p (Fin.last n) = z)
    (hx : (pathGraph (k + 1)).IsWalkFrom 0
      (Fin.snoc (Fin.snoc p x : Fin (n + 2) → Fin (k + 1)) z : Fin (n + 3) → Fin (k + 1)))
    (hy : (pathGraph (k + 1)).IsWalkFrom 0
      (Fin.snoc (Fin.snoc p y : Fin (n + 2) → Fin (k + 1)) z : Fin (n + 3) → Fin (k + 1))) :
    single ⟨_, hx⟩ ⟨_, hy⟩ 1 ∈ (walkRep _ 0 hr hδ).range := by
  set A := (walkRep _ 0 hr hδ).range
  have hc : r x * r y / r z ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (hr x) (hr y)) (pow_ne_zero _ (hr z))
  have h := A.smul_mem (A.mul_mem (A.mul_mem (hdiag ⟨_, hx⟩)
    ((AlgHom.mem_range _).2 ⟨e δ (Fin.last n), rfl⟩)) (hdiag ⟨_, hy⟩)) (r x * r y / r z ^ 2)⁻¹
  rwa [single_mul_mul_single, walkRep_e_last_apply_snoc_snoc,
    ite_eq_left ⟨rfl, hpz, rfl⟩, one_mul, mul_one, smul_single, smul_eq_mul,
    inv_mul_cancel₀ hc] at h

/-- The inductive step: if the image of the path representation on `n + 1` strands contains every
matrix unit between walks with a common endpoint, then so does its image on `n + 2` strands. -/
private theorem single_mem_range_walkRep_succ
    (hδ : IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ (n + 2))
    (ih : ∀ a b : {s : Fin (n + 2) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s},
      a.val (Fin.last (n + 1)) = b.val (Fin.last (n + 1)) →
        single a b 1 ∈ (walkRep _ 0 hr (hδ.mono (Nat.le_succ (n + 1)))).range)
    {s t : {s : Fin (n + 3) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s}}
    (hst : s.val (Fin.last (n + 2)) = t.val (Fin.last (n + 2))) :
    single s t 1 ∈ (walkRep _ 0 hr hδ).range := by
  set A := (walkRep _ 0 hr hδ).range
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  simp only at hst
  by_cases hxy : s (Fin.last (n + 1)).castSucc = t (Fin.last (n + 1)).castSucc
  · exact single_mem_range_walkRep_of_apply_eq hr hδ ih hst hxy
  -- otherwise the penultimate vertices `x` and `y` are the two neighbours of the endpoint `z`
  obtain ⟨x, hx⟩ : ∃ x, s (Fin.last (n + 1)).castSucc = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, t (Fin.last (n + 1)).castSucc = y := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, s (Fin.last (n + 2)) = z := ⟨_, rfl⟩
  have hxz : (pathGraph (k + 1)).Adj x z := hx ▸ hz ▸ hs.adj (by simp)
  have hyz : (pathGraph (k + 1)).Adj y z := by
    rw [← hy, ← hz, hst]
    exact ht.adj (by simp)
  -- so some walk with `n` steps ends at `z`
  obtain ⟨p, hp, hpz⟩ : ∃ p : Fin (n + 1) → Fin (k + 1),
      (pathGraph (k + 1)).IsWalkFrom 0 p ∧ p (Fin.last n) = z := by
    rw [hx, hy] at hxy
    rw [pathGraph_adj] at hxz hyz
    by_cases hxz' : x.val = z.val + 1
    · exact hs.init.exists_isWalkFrom_pathGraph_of_val_eq_add_one (by simpa [Fin.init_def, hx])
    · exact ht.init.exists_isWalkFrom_pathGraph_of_val_eq_add_one
        (by simp only [Fin.init_def, hy]; simp only [Fin.ext_iff] at hxy; omega)
  have hq {w : Fin (k + 1)} (hwz : (pathGraph (k + 1)).Adj w z) : (pathGraph (k + 1)).IsWalkFrom 0
      (Fin.snoc (Fin.snoc p w : Fin (n + 2) → Fin (k + 1)) z : Fin (n + 3) → Fin (k + 1)) :=
    (isWalkFrom_snoc _ _).2 ⟨(isWalkFrom_snoc _ _).2 ⟨hp, hpz ▸ hwz.symm⟩,
      by rw [Fin.snoc_last]; exact hwz⟩
  -- `s`, `p x z`, `p y z` and `t` are joined in turn
  have h := A.mul_mem (A.mul_mem
    (single_mem_range_walkRep_of_apply_eq hr hδ ih (u := ⟨s, hs⟩) (v := ⟨_, hq hxz⟩)
      (by simp [hz]) (by simp [hx]))
    (single_snoc_snoc_mem_range_walkRep hr hδ
      (single_self_mem_range_walkRep hr hδ fun a ↦ ih a a rfl) hpz (hq hxz) (hq hyz)))
    (single_mem_range_walkRep_of_apply_eq hr hδ ih (u := ⟨_, hq hyz⟩) (v := ⟨t, ht⟩)
      (by simp [← hst, hz]) (by simp [hy]))
  rwa [single_mul_single_same, single_mul_single_same, one_mul, one_mul] at h

/-- When there is at most one walk with `n` steps, its matrix unit is the identity. -/
private theorem single_mem_range_walkRep_of_subsingleton
    (hδ : IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ n)
    [Subsingleton {s : Fin (n + 1) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s}]
    (s t : {s : Fin (n + 1) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s}) :
    single s t 1 ∈ (walkRep _ 0 hr hδ).range := by
  have h : single s t (1 : K) = 1 := by
    ext u v
    rw [Subsingleton.elim s u, Subsingleton.elim t u, Subsingleton.elim v u, single_apply_same,
      one_apply_eq]
  rw [h]
  exact Subalgebra.one_mem _

/-- Every matrix unit between walks with a common endpoint lies in the image of the path
representation on the path graph. -/
private theorem single_mem_range_walkRep_pathGraph : ∀ {n : ℕ}
    (hδ : IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ n)
    {s t : {s : Fin (n + 1) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s}},
    s.val (Fin.last n) = t.val (Fin.last n) → single s t 1 ∈ (walkRep _ 0 hr hδ).range
  | 0, hδ, s, t, _ =>
    haveI := subsingleton_walk_pathGraph (k := k) (m := 0) zero_le_one
    single_mem_range_walkRep_of_subsingleton hr hδ s t
  | 1, hδ, s, t, _ =>
    haveI := subsingleton_walk_pathGraph (k := k) (m := 1) le_rfl
    single_mem_range_walkRep_of_subsingleton hr hδ s t
  | _ + 2, hδ, _, _, hst =>
    single_mem_range_walkRep_succ hr hδ (fun _ _ hab ↦ single_mem_range_walkRep_pathGraph _ hab) hst

/-- **The image of the path representation on the path graph is the path algebra.** On the walks
from the end vertex `0` of the path graph, a matrix is the image of an element of the
Temperley–Lieb algebra exactly when it preserves endpoints: its entries between walks with
different endpoints vanish. -/
theorem mem_range_walkRep_pathGraph_iff (hδ : IsPathEigenvectorUpTo (pathGraph (k + 1)) 0 r δ n)
    (X : Matrix {s : Fin (n + 1) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s}
      {s : Fin (n + 1) → Fin (k + 1) // (pathGraph (k + 1)).IsWalkFrom 0 s} K) :
    X ∈ (walkRep (pathGraph (k + 1)) 0 hr hδ).range ↔
      ∀ s t, s.val (Fin.last n) ≠ t.val (Fin.last n) → X s t = 0 := by
  refine ⟨fun hX s t h ↦ ?_, fun hX ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := (AlgHom.mem_range _).1 hX
    exact walkRep_apply_eq_zero hr hδ x h
  rw [matrix_eq_sum_single X]
  refine Subalgebra.sum_mem _ fun s _ ↦ Subalgebra.sum_mem _ fun t _ ↦ ?_
  by_cases h : s.val (Fin.last n) = t.val (Fin.last n)
  · rw [← mul_one (X s t), ← smul_eq_mul, ← smul_single]
    exact Subalgebra.smul_mem _ (single_mem_range_walkRep_pathGraph hr hδ h) _
  · rw [hX s t h, single_zero]
    exact Subalgebra.zero_mem _

end Range

/-- **The path representation on a long enough path graph is faithful.** On the path graph with
`N + 1 ≥ n + 1` vertices, the path representation of the Temperley–Lieb algebra on `n` strands
on the walks from `0` is injective, for any nonzero weights satisfying the eigenvector equation up
to depth `n`. Its image contains the `catalan n` matrix units between walks with a common
endpoint. -/
theorem walkRep_pathGraph_injective {K : Type*} [Field K] {δ : K} {n N : ℕ} (hn : n ≤ N)
    {r : Fin (N + 1) → K} (hr : ∀ v, r v ≠ 0)
    (hδ : IsPathEigenvectorUpTo (pathGraph (N + 1)) 0 r δ n) :
    Function.Injective (walkRep (pathGraph (N + 1)) 0 hr hδ) := by
  let ι := {p : {s : Fin (n + 1) → Fin (N + 1) // (pathGraph (N + 1)).IsWalkFrom 0 s} ×
    {s : Fin (n + 1) → Fin (N + 1) // (pathGraph (N + 1)).IsWalkFrom 0 s} //
      p.1.val (Fin.last n) = p.2.val (Fin.last n)}
  -- the matrix units between walks with a common endpoint lie in the image
  let b : ι → LinearMap.range (walkRep (pathGraph (N + 1)) 0 hr hδ).toLinearMap := fun i ↦
    ⟨single i.val.1 i.val.2 1, LinearMap.mem_range.2
      ((AlgHom.mem_range _).1 (single_mem_range_walkRep_pathGraph hr hδ i.property))⟩
  have hb : LinearIndependent K b := by
    refine LinearIndependent.of_comp (LinearMap.range _).subtype ?_
    convert (Matrix.stdBasis K _ _).linearIndependent.comp (fun i : ι ↦ i.val)
      Subtype.val_injective using 1
    funext ⟨⟨s, t⟩, _⟩
    simp [b, Matrix.stdBasis_eq_single]
  -- and there are `catalan n` of them
  have hcard : Fintype.card ι = catalan n := by
    rw [show Fintype.card ι = _ from Fintype.card_subtype_apply_fst_eq_apply_snd
      fun s : {s : Fin (n + 1) → Fin (N + 1) // (pathGraph (N + 1)).IsWalkFrom 0 s} ↦
        s.val (Fin.last n), ← sum_sq_card_walk_length_pathGraph hn]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _
      (fun s : Fin (n + 1) → Fin (N + 1) ↦ s (Fin.last n) = v)),
      card_isWalkFrom_eq_adjMatrix_pow_apply, adjMatrix_pow_apply_eq_card_walk, Nat.cast_id]
  exact injective_of_catalan_le_finrank_range (walkRep _ 0 hr hδ).toLinearMap
    (hcard ▸ hb.fintype_card_le_finrank)

section Radical

open scoped ComplexOrder

variable {δ : ℝ} {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

/-- **The trace radical vanishes when the quantum integers are positive.** If `[1], …, [n + 1]`
are positive at `δ : ℝ`, the trace radical of every Markov trace on `n` strands is zero, so the
Temperley–Lieb algebra on `n` strands embeds in the path algebra of the path graph with `n + 1`
vertices. -/
theorem IsMarkovTrace.traceRadical_eq_bot_of_qInt_pos (htr : IsMarkovTrace ℂ (δ : ℂ) tr) {n : ℕ}
    (hq : ∀ j ∈ Finset.Icc 1 (n + 1), 0 < qInt ℝ δ j) :
    (tr n).traceRadical (htr.map_mul_comm n) = ⊥ := by
  have hpos (t : Fin (n + 1)) : 0 < qInt ℝ δ (t + 1) :=
    hq (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hr (t : Fin (n + 1)) : ((√(qInt ℝ δ (t + 1)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hpos t)).ne'
  have hδ := (isPathEigenvectorUpTo_pathGraph_sqrt_qInt le_rfl (fun t ↦ (hpos t).le)).map
    Complex.ofRealHom
  rw [← htr.ker_walkRep hr (fun t ↦ Complex.conj_ofReal _) hδ]
  exact (RingHom.injective_iff_ker_eq_bot _).1 (walkRep_pathGraph_injective le_rfl hr hδ)

/-- **The trace radical vanishes for `δ ≥ 2`.** For `δ ≥ 2`, the trace radical of every Markov
trace is zero on every number of strands. -/
theorem IsMarkovTrace.traceRadical_eq_bot_of_two_le (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : 2 ≤ δ) (n : ℕ) : (tr n).traceRadical (htr.map_mul_comm n) = ⊥ :=
  htr.traceRadical_eq_bot_of_qInt_pos fun _ hj ↦
    qInt_pos_of_two_le hδ (Finset.mem_Icc.1 hj).1

end Radical

end TauCeti.TemperleyLieb
