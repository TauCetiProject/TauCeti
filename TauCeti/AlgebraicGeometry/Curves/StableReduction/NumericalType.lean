/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Matrix.Symmetric
-- the no-disconnected-cut criterion that discharges the `connected` field of a numerical type
public import TauCeti.LinearAlgebra.Matrix.Connected
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import TauCeti.LinearAlgebra.Matrix.Symmetric

/-!
# Numerical types and their signed genus

A **numerical type** is the combinatorial shadow of the special fibre of a proper regular model
of a curve over a discrete valuation ring: a finite nonempty set of components carrying
multiplicities `mᵢ`, weights `wᵢ` (the degrees of the constant fields of the components over the
residue field) and genera `gᵢ`, together with a symmetric matrix of intersection numbers
`A = (aᵢⱼ)` whose off-diagonal entries are nonnegative, whose associated graph is connected,
which is killed by the multiplicity vector, and whose `i`-th row is divisible by `wᵢ`.

This file introduces that structure, its positivity and connectedness API, its reindexing along
an equivalence of component sets, equivalences of numerical types, and its signed genus

`g(T) = 1 + ∑ᵢ mᵢ (wᵢ (gᵢ - 1) - aᵢᵢ / 2)`.

The arithmetic subtlety in the genus formula is that the individual half-diagonals `aᵢᵢ / 2` need
not be integers, so the halving may only be performed once, on the whole sum. That this is
legitimate is `TauCeti.NumericalType.even_sum_multiplicity_mul_diagonal`: pairing the fibre
relation against the multiplicity vector gives `∑ᵢⱼ mᵢ mⱼ aᵢⱼ = 0`, and for a symmetric integer
matrix that forces `∑ᵢ mᵢ aᵢᵢ` to be even
(`Matrix.IsSymm.even_sum_mul_diag_of_dotProduct_mulVec_eq_zero`).

## Main definitions

* `TauCeti.NumericalType`: the structure described above, following
  [Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z).
* `TauCeti.NumericalType.Adj`: the adjacency relation `i ≠ j ∧ 0 < aᵢⱼ` whose reflexive
  transitive closure the connectedness axiom requires to be total.
* `TauCeti.NumericalType.reindex`: the numerical type obtained by transporting the component set
  along an equivalence.
* `TauCeti.NumericalType.Equiv`: an equivalence of numerical types, a bijection of component sets
  matching all of their data, with its identity, inverse and composite.
* `TauCeti.NumericalType.arithmeticGenus`: the signed genus, valued in `ℤ`.

## Main results

* `TauCeti.NumericalType.even_sum_multiplicity_mul_diagonal`: `∑ᵢ mᵢ aᵢᵢ` is even, which is what
  makes the halving in the genus formula exact, and
  `TauCeti.NumericalType.two_mul_arithmeticGenus`, the resulting division-free form of that
  formula.
* `TauCeti.NumericalType.intersection_self_nonpos` and
  `TauCeti.NumericalType.intersection_self_neg`: self-intersections are nonpositive, and are
  negative as soon as there is more than one component.
* `TauCeti.NumericalType.exists_mem_notMem_adj`: every nonempty proper set of components meets
  its complement, the no-disconnected-cut form in which
  [Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z) states the connectedness
  condition.
* `TauCeti.NumericalType.arithmeticGenus_reindex`: the signed genus does not depend on the chosen
  indexing of the components.
* `TauCeti.NumericalType.nonempty_equiv_iff`: two numerical types are equivalent exactly when
  one is a reindexing of the other, and `TauCeti.NumericalType.Equiv.arithmeticGenus_eq`:
  equivalent numerical types have the same signed genus.

## Implementation notes

Abstract numerical types can have negative genus, so `arithmeticGenus` lands in `ℤ` rather than
`ℕ`; the genus-zero variant of `weightedExample` at the end of the file has genus `-1`. Nor may
the halving be distributed over the sum: `oddDiagonalExample` has odd diagonal entries.

Symmetry of the intersection matrix is recorded through Mathlib's `Matrix.IsSymm` rather than as
a bare pointwise equation, so that a reindexed matrix inherits it from `Matrix.IsSymm.submatrix`.

The no-disconnected-cut criterion in the other direction, which is what discharges the `connected`
field when a numerical type is built, has to be available before the type exists, so it is stated
for a bare matrix:
`Matrix.forall_reflTransGen_ne_and_pos_iff` in `TauCeti.LinearAlgebra.Matrix.Connected`, which
this file re-exports.
-/

-- The `NumericalType` structure, the signed genus and the two worked examples follow the
-- signatures written down in `StableReduction/Suggested.lean` of the Tau Ceti roadmap.

public section

namespace TauCeti

open Finset

universe u v w

/-- A numerical type, in the sense of
[Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z).

`multiplicity i` and `weight i` are the multiplicity of the `i`-th component of the special fibre
of a proper regular model and the degree of its constant field over the residue field, and
`genus i` is its arithmetic genus over that constant field, not the genus of its normalization.
The matrix `intersection` records the intersection numbers of the components. -/
structure NumericalType where
  /-- The finite nonempty index set of components. -/
  Component : Type u
  [componentFintype : Fintype Component]
  [componentDecidableEq : DecidableEq Component]
  [componentNonempty : Nonempty Component]
  /-- The multiplicity of a component in the special fibre. -/
  multiplicity : Component → ℕ+
  /-- The degree of the constant field of a component over the residue field. -/
  weight : Component → ℕ+
  /-- The matrix of intersection numbers of the components. -/
  intersection : Matrix Component Component ℤ
  /-- Intersection numbers are symmetric. -/
  intersection_isSymm : intersection.IsSymm
  /-- Distinct components meet nonnegatively. -/
  offDiagonal_nonneg : ∀ i j, i ≠ j → 0 ≤ intersection i j
  /-- The graph joining components that meet is connected. -/
  connected : ∀ i j, Relation.ReflTransGen
    (fun i j ↦ i ≠ j ∧ 0 < intersection i j) i j
  /-- The whole special fibre meets every component in degree zero. -/
  fiber_relation : ∀ i, ∑ j, (multiplicity j : ℤ) * intersection i j = 0
  /-- The `i`-th row of the intersection matrix is divisible by the weight of the `i`-th
  component. -/
  weight_dvd : ∀ i j, (weight i : ℤ) ∣ intersection i j
  /-- The arithmetic genus of a component over its own constant field. -/
  genus : Component → ℕ

namespace NumericalType

attribute [instance] componentFintype componentDecidableEq componentNonempty

variable (T : NumericalType.{u})

/-- Intersection numbers of a numerical type commute. -/
lemma intersection_comm (i j : T.Component) : T.intersection i j = T.intersection j i :=
  (T.intersection_isSymm.apply i j).symm

/-! ### Connectedness of the intersection graph -/

/-- Two components of a numerical type are adjacent when they are distinct and meet. -/
def Adj (i j : T.Component) : Prop := i ≠ j ∧ 0 < T.intersection i j

/-- Unfolding of `TauCeti.NumericalType.Adj`. -/
@[simp]
lemma adj_iff {i j : T.Component} : T.Adj i j ↔ i ≠ j ∧ 0 < T.intersection i j := Iff.rfl

/-- The connectedness axiom, phrased with `TauCeti.NumericalType.Adj`. -/
lemma reflTransGen_adj (i j : T.Component) : Relation.ReflTransGen T.Adj i j := T.connected i j

variable {T} in
/-- Adjacency is a symmetric relation. -/
lemma Adj.symm {i j : T.Component} (h : T.Adj i j) : T.Adj j i :=
  ⟨h.1.symm, T.intersection_comm i j ▸ h.2⟩

/-- Every nonempty proper set of components of a numerical type meets its complement: this is the
no-disconnected-cut form of the connectedness axiom. -/
lemma exists_mem_notMem_adj (s : Set T.Component) (hne : s.Nonempty) (hs : s ≠ Set.univ) :
    ∃ i ∈ s, ∃ j ∉ s, T.Adj i j :=
  (Relation.forall_reflTransGen_iff T.Adj).1 T.reflTransGen_adj s hne hs

/-! ### Self-intersections -/

private lemma multiplicity_pos (i : T.Component) : (0 : ℤ) < (T.multiplicity i : ℤ) :=
  Int.natCast_pos.mpr (T.multiplicity i).pos

/-- Off the diagonal, multiplicity-weighted intersection numbers are nonnegative. -/
lemma multiplicity_mul_intersection_nonneg {i j : T.Component} (h : i ≠ j) :
    0 ≤ (T.multiplicity j : ℤ) * T.intersection i j :=
  mul_nonneg (T.multiplicity_pos j).le (T.offDiagonal_nonneg i j h)

/-- The fibre relation with the diagonal term isolated. -/
lemma multiplicity_mul_intersection_self (i : T.Component) :
    (T.multiplicity i : ℤ) * T.intersection i i =
      -∑ j ∈ univ.erase i, (T.multiplicity j : ℤ) * T.intersection i j := by
  have h := T.fiber_relation i
  rw [← Finset.add_sum_erase _ _ (mem_univ i)] at h
  linarith

/-- Self-intersections in a numerical type are nonpositive. -/
lemma intersection_self_nonpos (i : T.Component) : T.intersection i i ≤ 0 := by
  have hle : (T.multiplicity i : ℤ) * T.intersection i i ≤ 0 := by
    rw [T.multiplicity_mul_intersection_self i, neg_nonpos]
    exact Finset.sum_nonneg fun _ hj ↦
      T.multiplicity_mul_intersection_nonneg (Finset.ne_of_mem_erase hj).symm
  by_contra hgt
  rw [not_le] at hgt
  exact absurd hle (not_le.2 (mul_pos (T.multiplicity_pos i) hgt))

/-- In a numerical type with more than one component, every component meets some other one. -/
lemma exists_adj (h : 1 < Fintype.card T.Component) (i : T.Component) : ∃ j, T.Adj i j := by
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card h i
  rcases (T.reflTransGen_adj i j).cases_head with rfl | ⟨k, hk, -⟩
  · exact absurd rfl hj
  · exact ⟨k, hk⟩

/-- In a numerical type with more than one component, self-intersections are negative. -/
lemma intersection_self_neg (h : 1 < Fintype.card T.Component) (i : T.Component) :
    T.intersection i i < 0 := by
  obtain ⟨j, hij, hpos⟩ := T.exists_adj h i
  have hmem : j ∈ univ.erase i := mem_erase.2 ⟨hij.symm, mem_univ j⟩
  have hsum : 0 < ∑ k ∈ univ.erase i, (T.multiplicity k : ℤ) * T.intersection i k :=
    lt_of_lt_of_le (mul_pos (T.multiplicity_pos j) hpos)
      (Finset.single_le_sum (fun k hk ↦
        T.multiplicity_mul_intersection_nonneg (Finset.ne_of_mem_erase hk).symm) hmem)
  have hneg : (T.multiplicity i : ℤ) * T.intersection i i < 0 := by
    rw [T.multiplicity_mul_intersection_self i]
    linarith
  by_contra hge
  rw [not_lt] at hge
  exact absurd hneg (not_lt.2 (mul_nonneg (T.multiplicity_pos i).le hge))

/-! ### Integrality of the signed genus -/

/-- The multiplicity-weighted sum of the self-intersections of a numerical type is even.

This is what makes the halving in the genus formula exact; the individual terms `mᵢ aᵢᵢ` need not
be even, as `oddDiagonalExample` shows. The fibre relation says that the intersection matrix kills
the multiplicity vector, so this is an instance of
`Matrix.IsSymm.even_sum_mul_diag_of_dotProduct_mulVec_eq_zero`. -/
lemma even_sum_multiplicity_mul_diagonal :
    Even (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) := by
  have hker : T.intersection.mulVec (fun j ↦ (T.multiplicity j : ℤ)) = 0 := funext fun i ↦ by
    simpa [Matrix.mulVec, dotProduct, mul_comm] using T.fiber_relation i
  exact T.intersection_isSymm.even_sum_mul_diag_of_dotProduct_mulVec_eq_zero
    (by rw [hker, dotProduct_zero])

/-! ### The signed genus -/

/-- The signed genus of a numerical type,
`g(T) = 1 + ∑ᵢ mᵢ (wᵢ (gᵢ - 1) - aᵢᵢ / 2)`
(compare [Stacks, Tag 0C71](https://stacks.math.columbia.edu/tag/0C71)).

The halving is performed once, on the whole sum `∑ᵢ mᵢ aᵢᵢ`, which is even by
`even_sum_multiplicity_mul_diagonal`; the individual half-diagonals need not be integers.
Abstract numerical types can have negative genus, so the value is an integer, not a natural
number. -/
def arithmeticGenus : ℤ :=
  1 + (∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) * ((T.genus i : ℤ) - 1)) -
    (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2

/-- The defining formula of the signed genus, with the halving performed once on the whole sum
`∑ᵢ mᵢ aᵢᵢ`. -/
lemma arithmeticGenus_def :
    T.arithmeticGenus =
      1 + (∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) * ((T.genus i : ℤ) - 1)) -
        (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2 := by
  rw [arithmeticGenus]

/-- The genus formula with the halving cleared, which is the shape in which it is used. -/
lemma two_mul_arithmeticGenus :
    2 * T.arithmeticGenus =
      2 + 2 * (∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) * ((T.genus i : ℤ) - 1)) -
        ∑ i, (T.multiplicity i : ℤ) * T.intersection i i := by
  have h : (2 : ℤ) * ((∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2)
      = ∑ i, (T.multiplicity i : ℤ) * T.intersection i i :=
    Int.mul_ediv_cancel' T.even_sum_multiplicity_mul_diagonal.two_dvd
  rw [arithmeticGenus]
  linarith

/-! ### Reindexing -/

/-- The numerical type obtained by transporting the component set along an equivalence.

The finiteness and decidable equality of the new component set are transported along the
equivalence, so the target needs no instances of its own and may live in any universe. -/
@[expose]
def reindex {C : Type v} (e : T.Component ≃ C) : NumericalType.{v} :=
  letI : Fintype C := Fintype.ofEquiv _ e
  letI : DecidableEq C := e.symm.decidableEq
  { Component := C
    componentNonempty := T.componentNonempty.map e
    multiplicity c := T.multiplicity (e.symm c)
    weight c := T.weight (e.symm c)
    intersection := T.intersection.submatrix e.symm e.symm
    intersection_isSymm := T.intersection_isSymm.submatrix _
    offDiagonal_nonneg _ _ h := T.offDiagonal_nonneg _ _ fun hh ↦ h (e.symm.injective hh)
    connected i j := by
      have key : ∀ a b : T.Component,
          Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < T.intersection x y) a b →
          Relation.ReflTransGen
            (fun x y : C ↦ x ≠ y ∧ 0 < T.intersection.submatrix e.symm e.symm x y) (e a) (e b) := by
        intro a b hab
        induction hab with
        | refl => exact Relation.ReflTransGen.refl
        | @tail c d _ hcd ih =>
          refine ih.tail ⟨fun hh ↦ hcd.1 (e.injective hh), ?_⟩
          simpa using hcd.2
      simpa using key (e.symm i) (e.symm j) (T.connected _ _)
    fiber_relation i :=
      (Fintype.sum_equiv e.symm _
        (fun k ↦ (T.multiplicity k : ℤ) * T.intersection (e.symm i) k) fun _ ↦ rfl).trans
        (T.fiber_relation (e.symm i))
    weight_dvd _ _ := T.weight_dvd _ _
    genus c := T.genus (e.symm c) }

/-- Numerical types are determined by their multiplicity, weight, intersection and genus data:
an equivalence of component sets matching all four identifies the two types. As the component set
is a field rather than a parameter, this is the extensionality principle for numerical types; the
instance fields are subsingletons and the remaining fields are proofs. -/
lemma reindex_eq {T' : NumericalType.{v}} (e : T.Component ≃ T'.Component)
    (hm : ∀ i, T'.multiplicity (e i) = T.multiplicity i)
    (hw : ∀ i, T'.weight (e i) = T.weight i)
    (hA : ∀ i j, T'.intersection (e i) (e j) = T.intersection i j)
    (hg : ∀ i, T'.genus (e i) = T.genus i) :
    T.reindex e = T' := by
  cases T' with
  | mk C' m' w' A' hs ho hc hf hd g' =>
    unfold reindex
    -- `congr 1` leaves the four data fields, the transported `Fintype` and `DecidableEq`
    -- instances, which are subsingletons, and the proof fields, which are irrelevant
    congr 1 <;>
      first
        | exact Subsingleton.elim _ _
        | exact proof_irrel_heq _ _
        | (funext c; simpa using (hm (e.symm c)).symm)
        | (funext c; simpa using (hw (e.symm c)).symm)
        | (funext c; simpa using (hg (e.symm c)).symm)
        | (funext c d; simpa using (hA (e.symm c) (e.symm d)).symm)

variable {C : Type v} (e : T.Component ≃ C)

/-- Multiplicities of a reindexed numerical type. -/
@[simp]
lemma reindex_multiplicity (c : C) :
    (T.reindex e).multiplicity c = T.multiplicity (e.symm c) := rfl

/-- Weights of a reindexed numerical type. -/
@[simp]
lemma reindex_weight (c : C) : (T.reindex e).weight c = T.weight (e.symm c) := rfl

/-- Component genera of a reindexed numerical type. -/
@[simp]
lemma reindex_genus (c : C) : (T.reindex e).genus c = T.genus (e.symm c) := rfl

/-- Intersection numbers of a reindexed numerical type. -/
@[simp]
lemma reindex_intersection (c d : C) :
    (T.reindex e).intersection c d = T.intersection (e.symm c) (e.symm d) := rfl

/-- Reindexing along the identity equivalence changes nothing. -/
@[simp]
lemma reindex_refl : T.reindex (Equiv.refl T.Component) = T :=
  T.reindex_eq _ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) fun _ ↦ rfl

/-- Reindexing twice is reindexing along the composite equivalence. -/
@[simp]
lemma reindex_reindex {D : Type w} (f : C ≃ D) :
    (T.reindex e).reindex f = T.reindex (e.trans f) := by
  -- `reindex_eq` does not apply directly, since `f` has the type it asks for only after
  -- unfolding `reindex`; both sides are the same data on the same component set anyway
  cases T
  unfold reindex
  congr 1 <;> first | exact Subsingleton.elim _ _ | exact proof_irrel_heq _ _

/-- The signed genus does not depend on the chosen indexing of the components. -/
@[simp]
lemma arithmeticGenus_reindex : (T.reindex e).arithmeticGenus = T.arithmeticGenus := by
  -- name the `Fintype C` that `reindex` transported along `e`, so that the two sums below can
  -- be compared with `Fintype.sum_equiv`
  let _ : Fintype C := (T.reindex e).componentFintype
  refine mul_left_cancel₀ (a := (2 : ℤ)) two_ne_zero ?_
  have h1 : ∑ i, ((T.reindex e).multiplicity i : ℤ) * ((T.reindex e).weight i : ℤ) *
      (((T.reindex e).genus i : ℤ) - 1)
      = ∑ k, (T.multiplicity k : ℤ) * (T.weight k : ℤ) * ((T.genus k : ℤ) - 1) :=
    Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl
  have h2 : ∑ i, ((T.reindex e).multiplicity i : ℤ) * (T.reindex e).intersection i i
      = ∑ k, (T.multiplicity k : ℤ) * T.intersection k k :=
    Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl
  rw [(T.reindex e).two_mul_arithmeticGenus, T.two_mul_arithmeticGenus, h1, h2]

/-! ### Equivalence of numerical types -/

/-- An equivalence of numerical types, in the sense of
[Stacks, Tag 0C6Z](https://stacks.math.columbia.edu/tag/0C6Z): a bijection of component sets
matching multiplicities, weights, intersection numbers and genera. Two numerical types are
equivalent when `Nonempty (T.Equiv T')`. -/
structure Equiv (T' : NumericalType.{v}) where
  /-- The underlying bijection of component sets. -/
  toEquiv : T.Component ≃ T'.Component
  /-- The bijection preserves multiplicities. -/
  multiplicity_apply : ∀ i, T'.multiplicity (toEquiv i) = T.multiplicity i
  /-- The bijection preserves weights. -/
  weight_apply : ∀ i, T'.weight (toEquiv i) = T.weight i
  /-- The bijection preserves intersection numbers. -/
  intersection_apply : ∀ i j, T'.intersection (toEquiv i) (toEquiv j) = T.intersection i j
  /-- The bijection preserves the genera of the components. -/
  genus_apply : ∀ i, T'.genus (toEquiv i) = T.genus i

namespace Equiv

variable {T} {T' : NumericalType.{v}} {T'' : NumericalType.{w}}

/-- The identity equivalence of a numerical type. -/
@[expose, simps toEquiv]
def refl : T.Equiv T where
  toEquiv := _root_.Equiv.refl T.Component
  multiplicity_apply _ := rfl
  weight_apply _ := rfl
  intersection_apply _ _ := rfl
  genus_apply _ := rfl

/-- The inverse of an equivalence of numerical types. -/
@[expose, simps toEquiv]
def symm (f : T.Equiv T') : T'.Equiv T where
  toEquiv := f.toEquiv.symm
  multiplicity_apply j := by simpa using (f.multiplicity_apply (f.toEquiv.symm j)).symm
  weight_apply j := by simpa using (f.weight_apply (f.toEquiv.symm j)).symm
  intersection_apply j k := by
    simpa using (f.intersection_apply (f.toEquiv.symm j) (f.toEquiv.symm k)).symm
  genus_apply j := by simpa using (f.genus_apply (f.toEquiv.symm j)).symm

/-- The composite of two equivalences of numerical types. -/
@[expose, simps toEquiv]
def trans (f : T.Equiv T') (g : T'.Equiv T'') : T.Equiv T'' where
  toEquiv := f.toEquiv.trans g.toEquiv
  multiplicity_apply i := (g.multiplicity_apply _).trans (f.multiplicity_apply i)
  weight_apply i := (g.weight_apply _).trans (f.weight_apply i)
  intersection_apply i j := (g.intersection_apply _ _).trans (f.intersection_apply i j)
  genus_apply i := (g.genus_apply _).trans (f.genus_apply i)

/-- An equivalence of numerical types identifies the target with the reindexed source. -/
lemma reindex_eq (f : T.Equiv T') : T.reindex f.toEquiv = T' :=
  T.reindex_eq f.toEquiv f.multiplicity_apply f.weight_apply f.intersection_apply f.genus_apply

/-- Equivalent numerical types have the same signed genus. -/
lemma arithmeticGenus_eq (f : T.Equiv T') : T'.arithmeticGenus = T.arithmeticGenus := by
  rw [← f.reindex_eq, arithmeticGenus_reindex]

end Equiv

/-- A numerical type is equivalent to each of its reindexings, along the reindexing
equivalence. -/
@[expose]
def equivReindex : T.Equiv (T.reindex e) where
  toEquiv := e
  multiplicity_apply i := congrArg T.multiplicity (e.symm_apply_apply i)
  weight_apply i := congrArg T.weight (e.symm_apply_apply i)
  intersection_apply i j := congrArg₂ T.intersection (e.symm_apply_apply i) (e.symm_apply_apply j)
  genus_apply i := congrArg T.genus (e.symm_apply_apply i)

/-- The bijection underlying `TauCeti.NumericalType.equivReindex` is the reindexing equivalence. -/
@[simp]
lemma equivReindex_toEquiv : (T.equivReindex e).toEquiv = e := rfl

/-- Two numerical types are equivalent exactly when one is a reindexing of the other. -/
lemma nonempty_equiv_iff {T' : NumericalType.{v}} :
    Nonempty (T.Equiv T') ↔ ∃ e : T.Component ≃ T'.Component, T.reindex e = T' :=
  ⟨fun ⟨f⟩ ↦ ⟨f.toEquiv, f.reindex_eq⟩, fun ⟨e, he⟩ ↦ he ▸ ⟨T.equivReindex e⟩⟩

/-! ### Worked examples -/

/-- Two components of multiplicity one, weight two and genus one, meeting doubly: a numerical
type of signed genus three. -/
private noncomputable abbrev weightedExample : NumericalType.{0} where
  Component := Fin 2
  multiplicity _ := 1
  weight _ := 2
  intersection := !![-2, 2; 2, -2]
  intersection_isSymm := Matrix.IsSymm.ext fun i j ↦ by fin_cases i <;> fin_cases j <;> rfl
  offDiagonal_nonneg i j h := by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | decide
  connected := by
    have key : ∀ i j : Fin 2, i ≠ j → (0 : ℤ) < !![(-2 : ℤ), 2; 2, -2] i j := by
      intro i j h
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | decide
    intro i j
    rcases eq_or_ne i j with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨h, key i j h⟩
  fiber_relation i := by fin_cases i <;> decide
  weight_dvd i j := by fin_cases i <;> fin_cases j <;> decide
  genus _ := 1

example : weightedExample.arithmeticGenus = 3 := by decide

example : ({ weightedExample with genus := fun _ ↦ 0 } : NumericalType).arithmeticGenus = -1 := by
  decide

/-- Two components of multiplicity and weight one and genus one, meeting transversally. Both
diagonal entries are odd, so the halving in the genus formula cannot be distributed over the
sum. -/
private noncomputable abbrev oddDiagonalExample : NumericalType.{0} where
  Component := Fin 2
  multiplicity _ := 1
  weight _ := 1
  intersection := !![-1, 1; 1, -1]
  intersection_isSymm := Matrix.IsSymm.ext fun i j ↦ by fin_cases i <;> fin_cases j <;> rfl
  offDiagonal_nonneg i j h := by
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | decide
  connected := by
    have key : ∀ i j : Fin 2, i ≠ j → (0 : ℤ) < !![(-1 : ℤ), 1; 1, -1] i j := by
      intro i j h
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | decide
    intro i j
    rcases eq_or_ne i j with rfl | h
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨h, key i j h⟩
  fiber_relation i := by fin_cases i <;> decide
  weight_dvd _ _ := one_dvd _
  genus _ := 1

example : oddDiagonalExample.intersection 0 0 = -1 := by decide

example : oddDiagonalExample.arithmeticGenus = 2 := by decide

end NumericalType

end TauCeti
