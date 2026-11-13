/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.OfParent
public import TauCeti.GroupTheory.GTree.Basic
public import TauCeti.Data.Rat.ZMultiples
public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

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
* `TauCeti.GTree.cosetTreeVertexEquiv`, `TauCeti.GTree.stabilizer_cosetTreeVertexEquiv_symm`:
  its vertices and their stabilizers.
* `TauCeti.GTree.cosetTreeDartEquiv`, `TauCeti.GTree.cosetTreeVertexEquiv_src`,
  `TauCeti.GTree.mem_stabilizer_cosetTreeDartEquiv_symm`: its darts, their endpoints and their
  stabilizers.
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

theorem cosetParent_def (x : Σ n, G ⧸ H n) :
    cosetParent H x = ⟨x.1 + 1, Subgroup.quotientMapOfLE (H.monotone x.1.le_succ) x.2⟩ := (rfl)

@[simp] theorem cosetParent_fst (x : Σ n, G ⧸ H n) : (cosetParent H x).1 = x.1 + 1 := (rfl)

@[simp] theorem cosetParent_mk (n : ℕ) (g : G) :
    cosetParent H ⟨n, (g : G ⧸ H n)⟩ = ⟨n + 1, (g : G ⧸ H (n + 1))⟩ := by
  rw [cosetParent_def, Subgroup.quotientMapOfLE_apply_mk]

/-- The `k`-th iterated parent of the coset `g H n` is the coset `g H (n + k)`. -/
theorem cosetParent_iterate_mk (k n : ℕ) (g : G) :
    (cosetParent H)^[k] ⟨n, (g : G ⧸ H n)⟩ = ⟨n + k, (g : G ⧸ H (n + k))⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, cosetParent_mk, add_assoc]

/-- Left translation commutes with the parent map. -/
@[simp] theorem cosetParent_smul (g : G) (x : Σ n, G ⧸ H n) :
    cosetParent H (g • x) = g • cosetParent H x := by
  obtain ⟨n, x⟩ := x
  induction x using QuotientGroup.induction_on
  simp only [Sigma.smul_mk, MulAction.Quotient.smul_mk, cosetParent_mk]

/-- No coset is a proper iterated parent of itself. -/
theorem eq_of_cosetParent_iterate_eq (x : Σ n, G ⧸ H n) (k l : ℕ)
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
  rw [cosetParent_iterate_mk, cosetParent_iterate_mk, show m + (n + N) = n + (m + N) by omega]
  exact congrArg _ (QuotientGroup.eq.mpr (H.monotone (by omega) hN))

/-! ### The coset tree -/

variable (hH : ∀ g, ∃ n, g ∈ H n)

-- The body is exposed because the compiler needs the vertex and dart types to compile
-- `cosetTreeVertexEquiv` and `cosetTreeDartEquiv` for importing modules.
/-- The coset tree of a group `G` which is the union of an increasing sequence of subgroups
`H n`: the vertices are the cosets `g H n`, an edge joins `g H n` to `g H (n + 1)`, and `G` acts
by left translation. -/
@[expose] def cosetTree : GTree.{w, w} G where
  toSerreGraph := ofParent (cosetParent H)
  isTree :=
    ofParent_isTree _ (eq_of_cosetParent_iterate_eq H) (exists_cosetParent_iterate_eq H hH)
  action := ofParentAction _ (cosetParent_smul H)
  action_smul_ne_rev := ofParentAction_equivE_ne_rev _

/-- The vertices of the coset tree are the cosets of the subgroups `H n`. -/
def cosetTreeVertexEquiv : (cosetTree H hH).V ≃ Σ n, G ⧸ H n := Equiv.refl _

/-- The darts of the coset tree: `(x, true)` runs from the coset `x` to its parent, and
`(x, false)` runs back. -/
def cosetTreeDartEquiv : (cosetTree H hH).E ≃ (Σ n, G ⧸ H n) × Bool := Equiv.refl _

/-- The dart `(x, true)` of the coset tree starts at the coset `x`, and the dart `(x, false)`
starts at the parent of `x`. -/
@[simp] theorem cosetTreeVertexEquiv_src (e : (cosetTree H hH).E) :
    cosetTreeVertexEquiv H hH ((cosetTree H hH).src e) =
      if (cosetTreeDartEquiv H hH e).2 then (cosetTreeDartEquiv H hH e).1
      else cosetParent H (cosetTreeDartEquiv H hH e).1 := (rfl)

/-- Reversing a dart of the coset tree changes its orientation. -/
@[simp] theorem cosetTreeDartEquiv_rev (e : (cosetTree H hH).E) :
    cosetTreeDartEquiv H hH ((cosetTree H hH).rev e) =
      ((cosetTreeDartEquiv H hH e).1, !(cosetTreeDartEquiv H hH e).2) := (rfl)

/-- The dart `(x, true)` of the coset tree ends at the parent of the coset `x`, and the dart
`(x, false)` ends at `x`. -/
@[simp] theorem cosetTreeVertexEquiv_tgt (e : (cosetTree H hH).E) :
    cosetTreeVertexEquiv H hH ((cosetTree H hH).tgt e) =
      if (cosetTreeDartEquiv H hH e).2 then cosetParent H (cosetTreeDartEquiv H hH e).1
      else (cosetTreeDartEquiv H hH e).1 := by
  rw [tgt_def, cosetTreeVertexEquiv_src, cosetTreeDartEquiv_rev]
  cases (cosetTreeDartEquiv H hH e).2 <;> simp

/-- The group acts on the vertices of the coset tree by left translation of cosets. -/
@[simp] theorem cosetTreeVertexEquiv_smul (g : G) (v : (cosetTree H hH).V) :
    cosetTreeVertexEquiv H hH (g • v) = g • cosetTreeVertexEquiv H hH v :=
  ofParentAction_equivV (cosetParent_smul H) g v

/-- Left translation of cosets moves the corresponding vertices of the coset tree. -/
@[simp] theorem cosetTreeVertexEquiv_symm_smul (g : G) (x : Σ n, G ⧸ H n) :
    (cosetTreeVertexEquiv H hH).symm (g • x) = g • (cosetTreeVertexEquiv H hH).symm x := by
  rw [Equiv.symm_apply_eq, cosetTreeVertexEquiv_smul, Equiv.apply_symm_apply]

/-- The group acts on the darts of the coset tree by left translation, preserving orientations. -/
@[simp] theorem cosetTreeDartEquiv_smul (g : G) (e : (cosetTree H hH).E) :
    cosetTreeDartEquiv H hH (g • e) =
      (g • (cosetTreeDartEquiv H hH e).1, (cosetTreeDartEquiv H hH e).2) :=
  ofParentAction_equivE (cosetParent_smul H) g e

/-- An element `g` fixes the vertex `a H n` of the coset tree exactly when `a⁻¹ g a` lies in
`H n`. -/
theorem mem_stabilizer_cosetTreeVertexEquiv_symm {g a : G} {n : ℕ} :
    g ∈ stabilizer G ((cosetTreeVertexEquiv H hH).symm ⟨n, (a : G ⧸ H n)⟩) ↔
      a⁻¹ * g * a ∈ H n := by
  rw [mem_stabilizer_iff, ← (cosetTreeVertexEquiv H hH).apply_eq_iff_eq,
    cosetTreeVertexEquiv_smul, Equiv.apply_symm_apply, eq_comm]
  simp [QuotientGroup.eq, mul_assoc]

/-- The stabilizer of the vertex `a H n` of the coset tree is the conjugate `a (H n) a⁻¹`. -/
theorem stabilizer_cosetTreeVertexEquiv_symm (n : ℕ) (a : G) :
    stabilizer G ((cosetTreeVertexEquiv H hH).symm ⟨n, (a : G ⧸ H n)⟩) =
      (H n).map (MulAut.conj a).toMonoidHom := by
  ext g
  rw [mem_stabilizer_cosetTreeVertexEquiv_symm, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

/-- The stabilizer of the vertex `H n` of the coset tree is `H n`. -/
@[simp] theorem stabilizer_cosetTreeVertexEquiv_symm_one (n : ℕ) :
    stabilizer G ((cosetTreeVertexEquiv H hH).symm ⟨n, ((1 : G) : G ⧸ H n)⟩) = H n := by
  ext g
  rw [mem_stabilizer_cosetTreeVertexEquiv_symm, inv_one, one_mul, mul_one]

/-- The stabilizer of the vertex `H n` of the coset tree is `H n`, where for normal `H n` the
coset `H n` is the identity of the quotient group. -/
@[simp] theorem stabilizer_cosetTreeVertexEquiv_symm_one_of_normal (n : ℕ) [(H n).Normal] :
    stabilizer G ((cosetTreeVertexEquiv H hH).symm ⟨n, 1⟩) = H n :=
  stabilizer_cosetTreeVertexEquiv_symm_one H hH n

/-- The stabilizer of a dart of the coset tree is the stabilizer of the coset it is attached to:
for the darts joining `a H n` and `a H (n + 1)`, the conjugate `a (H n) a⁻¹`. -/
theorem mem_stabilizer_cosetTreeDartEquiv_symm {g a : G} {n : ℕ} {d : Bool} :
    g ∈ stabilizer G ((cosetTreeDartEquiv H hH).symm (⟨n, (a : G ⧸ H n)⟩, d)) ↔
      a⁻¹ * g * a ∈ H n := by
  rw [← mem_stabilizer_cosetTreeVertexEquiv_symm H hH, mem_stabilizer_iff, mem_stabilizer_iff,
    ← (cosetTreeDartEquiv H hH).apply_eq_iff_eq, ← (cosetTreeVertexEquiv H hH).apply_eq_iff_eq]
  simp

/-- The stabilizer of the darts of the coset tree joining `H n` and `H (n + 1)` is `H n`. -/
@[simp] theorem stabilizer_cosetTreeDartEquiv_symm_one (n : ℕ) (d : Bool) :
    stabilizer G ((cosetTreeDartEquiv H hH).symm (⟨n, ((1 : G) : G ⧸ H n)⟩, d)) = H n := by
  ext g
  rw [mem_stabilizer_cosetTreeDartEquiv_symm, inv_one, one_mul, mul_one]

/-- The stabilizer of the darts of the coset tree joining `H n` and `H (n + 1)` is `H n`, where
for normal `H n` the coset `H n` is the identity of the quotient group. -/
@[simp] theorem stabilizer_cosetTreeDartEquiv_symm_one_of_normal (n : ℕ) [(H n).Normal]
    (d : Bool) : stabilizer G ((cosetTreeDartEquiv H hH).symm (⟨n, 1⟩, d)) = H n :=
  stabilizer_cosetTreeDartEquiv_symm_one H hH n d

variable {H hH}

/-- Every element is elliptic in the coset tree: it fixes the vertex `H n` as soon as it lies in
`H n`. -/
@[simp] theorem cosetTree_isElliptic (g : G) : (cosetTree H hH).IsElliptic g := by
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
@[simp] theorem cosetTree_isEllipticSubgroup_top_iff :
    (cosetTree H hH).IsEllipticSubgroup ⊤ ↔ ∃ n, H n = ⊤ := by
  rw [cosetTree_isEllipticSubgroup_iff]
  refine ⟨fun ⟨n, a, h⟩ => ⟨n, eq_top_iff.mpr fun g _ => ?_⟩,
    fun ⟨n, hn⟩ => ⟨n, 1, fun g _ => hn ▸ Subgroup.mem_top _⟩⟩
  simpa [mul_assoc] using h (a * g * a⁻¹) (Subgroup.mem_top _)

/-! ### The rational numbers -/

/-- The increasing sequence of the subgroups `(1 / n!) ℤ` of the additive group of the rational
numbers. -/
def ratChain : ℕ →o Subgroup (Multiplicative ℚ) where
  toFun n := (AddSubgroup.zmultiples (n.factorial : ℚ)⁻¹).toSubgroup
  monotone' m n h q := by
    simp only [Multiplicative.mem_toSubgroup,
      Rat.mem_zmultiples_inv_natCast_iff (Nat.factorial_ne_zero _)]
    exact fun hq => hq.trans (Nat.factorial_dvd_factorial h)

theorem ratChain_apply (n : ℕ) :
    ratChain n = (AddSubgroup.zmultiples (n.factorial : ℚ)⁻¹).toSubgroup := (rfl)

/-- A rational number lies in `(1 / n!) ℤ` exactly when its denominator divides `n!`. -/
theorem mem_ratChain_iff {n : ℕ} {q : Multiplicative ℚ} :
    q ∈ ratChain n ↔ q.toAdd.den ∣ n.factorial :=
  Rat.mem_zmultiples_inv_natCast_iff n.factorial_ne_zero

/-- Every rational number lies in some `(1 / n!) ℤ`. -/
theorem exists_mem_ratChain (q : Multiplicative ℚ) : ∃ n, q ∈ ratChain n :=
  ⟨q.toAdd.den, mem_ratChain_iff.mpr (Nat.dvd_factorial q.toAdd.den_pos le_rfl)⟩

/-- No `(1 / n!) ℤ` contains every rational number: it misses `1 / (n! + 1)`. -/
@[simp] theorem ratChain_ne_top (n : ℕ) : ratChain n ≠ ⊤ := fun h => by
  have := mem_ratChain_iff.mp (h ▸ Subgroup.mem_top (Multiplicative.ofAdd
    ((n.factorial + 1 : ℕ) : ℚ)⁻¹))
  rw [toAdd_ofAdd, Rat.inv_natCast_den_of_pos n.factorial.succ_pos] at this
  exact absurd (Nat.le_of_dvd n.factorial_pos this) (by omega)

/-- The coset tree of the rational numbers, the union of the subgroups `(1 / n!) ℤ`. -/
def ratTree : GTree.{0, 0} (Multiplicative ℚ) :=
  cosetTree ratChain exists_mem_ratChain

theorem ratTree_def : ratTree = cosetTree ratChain exists_mem_ratChain := (rfl)

/-- Every rational number acts on the tree `ratTree` as an elliptic automorphism. -/
@[simp] theorem ratTree_isElliptic (q : Multiplicative ℚ) : ratTree.IsElliptic q :=
  cosetTree_isElliptic q

/-- The rational numbers have no global fixed point in the tree `ratTree`, although each of them
is elliptic. -/
@[simp] theorem not_ratTree_isEllipticSubgroup_top : ¬ratTree.IsEllipticSubgroup ⊤ := fun h =>
  let ⟨n, hn⟩ := cosetTree_isEllipticSubgroup_top_iff.mp h
  ratChain_ne_top n hn

end GTree

end TauCeti
