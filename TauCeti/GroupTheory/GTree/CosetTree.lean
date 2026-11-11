/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.OfParent
public import TauCeti.GroupTheory.GTree.Basic
public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic.FieldSimp

/-!
# The coset tree of an increasing union of subgroups

Let `G` be the union of an increasing sequence of subgroups `H 0 ≤ H 1 ≤ ⋯`. Serre's coset tree
has the cosets `g H n` of all the `H n` as vertices, and an edge joining `g H n` to
`g H (n + 1)` for every `g` and `n`. The group `G` acts on it by left translation, without
inversions, and the stabilizer of the vertex `a H n` is the conjugate `a (H n) a⁻¹`. Hence every
element of `G` is elliptic, while `G` fixes a vertex only if some `H n` is all of `G`.

Applied to the subgroups `(1 / n!) ℤ` of the additive group of the rational numbers, this gives
an action on a tree in which every element is elliptic and there is no global fixed point. So the
theorem that a finitely generated group of elliptic automorphisms of a tree fixes a vertex
(`TauCeti.GTree.IsEllipticSubgroup.of_fg`) fails without finite generation. In the trichotomy of
Guirardel and Levitt for a group acting on a tree, this is the third case: an infinitely
generated group fixing an end and no vertex.

## Main declarations

* `TauCeti.GTree.cosetTree`: the coset tree of an increasing union of subgroups.
* `TauCeti.GTree.cosetTreeVertexEquiv`, `TauCeti.GTree.mem_stabilizer_cosetTreeVertexEquiv_symm`:
  its vertices and their stabilizers.
* `TauCeti.GTree.cosetTree_isElliptic`: every element is elliptic.
* `TauCeti.GTree.cosetTree_isEllipticSubgroup_top_iff`: the group fixes a vertex exactly when
  the sequence of subgroups reaches the whole group.
* `TauCeti.GTree.ratTree`, `TauCeti.GTree.ratTree_isElliptic`,
  `TauCeti.GTree.not_ratTree_isEllipticSubgroup_top`: the example of the rational numbers.

## References

* J.-P. Serre, *Trees*, Chapter I, §6.1, Theorem 15 and its proof, and §6.5.
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.1,
  Proposition 1.1.
-/

public section

universe w

namespace TauCeti

open SerreGraph _root_.MulAction

namespace GTree

variable {G : Type w} [Group G] (H : ℕ →o Subgroup G)

/-! ### The parent map on cosets -/

/-- The parent of the coset `g H n` is the coset `g H (n + 1)`. -/
def cosetParent (x : Σ n, G ⧸ H n) : Σ n, G ⧸ H n :=
  ⟨x.1 + 1, Subgroup.quotientMapOfLE (H.monotone x.1.le_succ) x.2⟩

@[simp] theorem cosetParent_mk (n : ℕ) (g : G) :
    cosetParent H ⟨n, (g : G ⧸ H n)⟩ = ⟨n + 1, (g : G ⧸ H (n + 1))⟩ := (rfl)

/-- The `k`-th iterated parent of the coset `g H n` is the coset `g H (n + k)`. -/
theorem cosetParent_iterate_mk (k n : ℕ) (g : G) :
    (cosetParent H)^[k] ⟨n, (g : G ⧸ H n)⟩ = ⟨n + k, (g : G ⧸ H (n + k))⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, cosetParent_mk, add_assoc]

/-- Left translation commutes with the parent map. -/
theorem cosetParent_smul (g : G) (x : Σ n, G ⧸ H n) :
    cosetParent H (g • x) = g • cosetParent H x := by
  obtain ⟨n, x⟩ := x
  induction x using QuotientGroup.induction_on
  rfl

/-- Two cosets of members of the sequence are equal when they are cosets of the same subgroup
and their representatives differ by an element of it. -/
private theorem sigma_mk_eq {m n : ℕ} {g h : G} (hmn : m = n) (hgh : g⁻¹ * h ∈ H m) :
    (⟨m, g⟩ : Σ n, G ⧸ H n) = ⟨n, h⟩ := by
  subst hmn
  exact congrArg _ (QuotientGroup.eq.mpr hgh)

/-- No coset is a proper iterated parent of itself. -/
theorem cosetParent_iterate_eq_iterate (x : Σ n, G ⧸ H n) (k l : ℕ)
    (h : (cosetParent H)^[k] x = (cosetParent H)^[l] x) : k = l := by
  obtain ⟨n, x⟩ := x
  induction x using QuotientGroup.induction_on
  simp only [cosetParent_iterate_mk] at h
  exact Nat.add_left_cancel (congrArg Sigma.fst h)

/-- When the subgroups exhaust the group, any two cosets have a common iterated parent. -/
theorem exists_cosetParent_iterate_eq (hH : ∀ g, ∃ n, g ∈ H n) (x y : Σ n, G ⧸ H n) :
    ∃ k l, (cosetParent H)^[k] x = (cosetParent H)^[l] y := by
  obtain ⟨m, x⟩ := x
  obtain ⟨n, y⟩ := y
  induction x using QuotientGroup.induction_on with | _ g
  induction y using QuotientGroup.induction_on with | _ h
  obtain ⟨N, hN⟩ := hH (g⁻¹ * h)
  refine ⟨n + N, m + N, ?_⟩
  rw [cosetParent_iterate_mk, cosetParent_iterate_mk]
  exact sigma_mk_eq H (by omega) (H.monotone (by omega) hN)

/-! ### The coset tree -/

variable (hH : ∀ g, ∃ n, g ∈ H n)

/-- The coset tree of a group `G` which is the union of an increasing sequence of subgroups
`H n`: the vertices are the cosets `g H n`, an edge joins `g H n` to `g H (n + 1)`, and `G` acts
by left translation. -/
@[expose] def cosetTree : GTree.{w, w} G where
  toSerreGraph := ofParent (cosetParent H)
  isTree :=
    ofParent_isTree _ (cosetParent_iterate_eq_iterate H) (exists_cosetParent_iterate_eq H hH)
  action := ofParentAction _ (cosetParent_smul H)
  action_smul_ne_rev := ofParentAction_equivE_ne_rev _

/-- The vertices of the coset tree are the cosets of the subgroups `H n`. -/
def cosetTreeVertexEquiv : (cosetTree H hH).V ≃ Σ n, G ⧸ H n := Equiv.refl _

/-- The group acts on the vertices of the coset tree by left translation of cosets. -/
@[simp] theorem cosetTreeVertexEquiv_smul (g : G) (v : (cosetTree H hH).V) :
    cosetTreeVertexEquiv H hH (g • v) = g • cosetTreeVertexEquiv H hH v :=
  ofParentAction_equivV (cosetParent_smul H) g v

/-- The stabilizer of the vertex `a H n` of the coset tree is the conjugate `a (H n) a⁻¹`. -/
theorem mem_stabilizer_cosetTreeVertexEquiv_symm {g a : G} {n : ℕ} :
    g ∈ stabilizer G ((cosetTreeVertexEquiv H hH).symm ⟨n, (a : G ⧸ H n)⟩) ↔
      a⁻¹ * g * a ∈ H n := by
  rw [mem_stabilizer_iff, ← (cosetTreeVertexEquiv H hH).apply_eq_iff_eq,
    cosetTreeVertexEquiv_smul, Equiv.apply_symm_apply, Sigma.smul_mk, Sigma.mk.injEq, heq_eq_eq,
    eq_self_iff_true, true_and, MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq,
    smul_eq_mul, mul_assoc]

/-- The stabilizer of the vertex `H n` of the coset tree is `H n`. -/
@[simp] theorem stabilizer_cosetTreeVertexEquiv_symm_one (n : ℕ) :
    stabilizer G ((cosetTreeVertexEquiv H hH).symm ⟨n, ((1 : G) : G ⧸ H n)⟩) = H n := by
  ext g
  rw [mem_stabilizer_cosetTreeVertexEquiv_symm, inv_one, one_mul, mul_one]

variable {H hH}

/-- Every element is elliptic in the coset tree: it fixes the vertex `H n` as soon as it lies in
`H n`. -/
theorem cosetTree_isElliptic (g : G) : (cosetTree H hH).IsElliptic g := by
  obtain ⟨n, hn⟩ := hH g
  refine isElliptic_iff.mpr ⟨(cosetTreeVertexEquiv H hH).symm ⟨n, ((1 : G) : G ⧸ H n)⟩,
    mem_stabilizer_iff.mp ?_⟩
  rwa [stabilizer_cosetTreeVertexEquiv_symm_one]

/-- A subgroup fixes a vertex of the coset tree exactly when it lies in a conjugate of some
`H n`. -/
theorem cosetTree_isEllipticSubgroup_iff {K : Subgroup G} :
    (cosetTree H hH).IsEllipticSubgroup K ↔ ∃ n a, ∀ g ∈ K, a⁻¹ * g * a ∈ H n := by
  rw [isEllipticSubgroup_iff]
  refine ⟨fun ⟨v, hv⟩ => ?_, fun ⟨n, a, h⟩ =>
    ⟨(cosetTreeVertexEquiv H hH).symm ⟨n, (a : G ⧸ H n)⟩, fun g hg =>
      (mem_stabilizer_cosetTreeVertexEquiv_symm H hH).mpr (h g hg)⟩⟩
  obtain ⟨⟨n, x⟩, rfl⟩ := (cosetTreeVertexEquiv H hH).symm.surjective v
  induction x using QuotientGroup.induction_on with | _ a
  exact ⟨n, a, fun g hg => (mem_stabilizer_cosetTreeVertexEquiv_symm H hH).mp (hv hg)⟩

/-- The whole group fixes a vertex of the coset tree exactly when some `H n` is the whole
group. -/
theorem cosetTree_isEllipticSubgroup_top_iff :
    (cosetTree H hH).IsEllipticSubgroup ⊤ ↔ ∃ n, H n = ⊤ := by
  rw [cosetTree_isEllipticSubgroup_iff]
  refine ⟨fun ⟨n, a, h⟩ => ⟨n, eq_top_iff.mpr fun g _ => ?_⟩,
    fun ⟨n, hn⟩ => ⟨n, 1, fun g _ => hn ▸ Subgroup.mem_top _⟩⟩
  simpa [mul_assoc] using h (a * g * a⁻¹) (Subgroup.mem_top _)

/-! ### The rational numbers -/

/-- The increasing sequence of the subgroups `(1 / n!) ℤ` of the additive group of the rational
numbers. -/
def ratChain : ℕ →o Subgroup (Multiplicative ℚ) where
  toFun n := Subgroup.zpowers (Multiplicative.ofAdd ((n.factorial : ℚ)⁻¹))
  monotone' := monotone_nat_of_le_succ fun n =>
    Subgroup.zpowers_le.mpr <| Subgroup.mem_zpowers_iff.mpr ⟨(n + 1 : ℕ), by
      rw [← ofAdd_zsmul, zsmul_eq_mul, Nat.factorial_succ]
      push_cast
      field_simp⟩

/-- A rational number lies in `(1 / n!) ℤ` exactly when it is an integer divided by `n!`. -/
theorem mem_ratChain_iff {n : ℕ} {q : Multiplicative ℚ} :
    q ∈ ratChain n ↔ ∃ k : ℤ, (k : ℚ) / n.factorial = q.toAdd := by
  refine Subgroup.mem_zpowers_iff.trans (exists_congr fun k => ?_)
  rw [← ofAdd_zsmul, zsmul_eq_mul, ← div_eq_mul_inv]
  exact (Equiv.eq_symm_apply Multiplicative.ofAdd).symm

/-- Every rational number lies in some `(1 / n!) ℤ`. -/
theorem exists_mem_ratChain (q : Multiplicative ℚ) : ∃ n, q ∈ ratChain n := by
  refine ⟨q.toAdd.den, mem_ratChain_iff.mpr ⟨q.toAdd.num * (q.toAdd.den - 1).factorial, ?_⟩⟩
  have hd : (q.toAdd.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.toAdd.den_pos.ne'
  have hf : (((q.toAdd.den - 1).factorial : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  conv_rhs => rw [← Rat.num_div_den q.toAdd]
  rw [← Nat.mul_factorial_pred q.toAdd.den_pos.ne']
  push_cast
  field_simp

/-- No `(1 / n!) ℤ` contains every rational number. -/
theorem ratChain_ne_top (n : ℕ) : ratChain n ≠ ⊤ := by
  intro h
  obtain ⟨k, hk⟩ := mem_ratChain_iff.mp
    (h ▸ Subgroup.mem_top (Multiplicative.ofAdd ((2 * n.factorial : ℚ)⁻¹)))
  have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [toAdd_ofAdd] at hk
  field_simp at hk
  have hk' : k * 2 = 1 := by exact_mod_cast hk
  omega

/-- The coset tree of the rational numbers, the union of the subgroups `(1 / n!) ℤ`. -/
def ratTree : GTree.{0, 0} (Multiplicative ℚ) :=
  cosetTree ratChain exists_mem_ratChain

theorem ratTree_def : ratTree = cosetTree ratChain exists_mem_ratChain := (rfl)

/-- Every rational number acts on the tree `ratTree` as an elliptic automorphism. -/
theorem ratTree_isElliptic (q : Multiplicative ℚ) : ratTree.IsElliptic q :=
  cosetTree_isElliptic q

/-- The rational numbers have no global fixed point in the tree `ratTree`, although each of them
is elliptic. -/
theorem not_ratTree_isEllipticSubgroup_top : ¬ratTree.IsEllipticSubgroup ⊤ := fun h =>
  let ⟨n, hn⟩ := cosetTree_isEllipticSubgroup_top_iff.mp h
  ratChain_ne_top n hn

end GTree

end TauCeti
