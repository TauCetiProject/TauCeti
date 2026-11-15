/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Countable.Defs
public import TauCeti.Algebra.Order.Group.DimensionGroup.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Basic.Countable.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Abel

/-!
# The Effros–Handelman–Shen theorem for countable dimension groups

A countable partially ordered abelian group is a dimension group if and only if it admits a
sequential positive inductive presentation by simplicial groups `(ℤ^{rₙ}, ℕ^{rₙ})`.

The converse direction transfers directedness, unperforation, and Riesz interpolation from the
simplicial stages `Fin (rank n) → ℤ` to the inductive limit `G` using eventual vanishing of
elements mapping to `0` and positive exhaustion of `G⁺`.

The forward direction rests on **Shen's triangle lemma**
(`TauCeti.exists_monotone_factorization_of_map_eq_zero`): given an unperforated partially ordered
abelian group `G` with Riesz interpolation, a monotone homomorphism `f : (Fin r → ℤ) →+ G`, and
`x : Fin r → ℤ` in `ker f`, `f` factors as `β ∘ α` through a simplicial group `Fin s → ℤ` with
`α` and `β` monotone and `α x = 0`. Iterating over finite subsets of `ker f` while adjoining
elements of a countable exhaustion of `G⁺` builds a `SimplicialPresentation G`.

## Main definitions

* `TauCeti.bondIter` : Composite bonding homomorphism from stage `n` to stage `n + k` in a
  sequential system of simplicial groups.
* `TauCeti.SimplicialPresentation G` : Presentation of `G` as a sequential positive inductive
  limit of simplicial groups `Fin (rank n) → ℤ`.

## Main results

* `TauCeti.SimplicialPresentation.isDimensionGroup` and
  `TauCeti.SimplicialPresentation.countable` : Any group admitting a `SimplicialPresentation` is a
  countable dimension group.
* `TauCeti.exists_monotone_factorization_of_map_eq_zero` and
  `TauCeti.exists_monotone_factorization_finset` : Shen's triangle lemma for single elements and
  finite subsets of the kernel of a positive map from `Fin r → ℤ`.
* `TauCeti.IsDimensionGroup.nonempty_simplicialPresentation` : Every countable dimension group
  admits a `SimplicialPresentation`.
* `TauCeti.effros_handelman_shen` : Countable characterization of dimension groups as sequential
  positive inductive limits of simplicial groups.

## References

* E. G. Effros, D. E. Handelman, C.-L. Shen, *Dimension groups and their affine representations*,
  Amer. J. Math. **102** (1980), 385–407, Lemma 2.1 and Theorem 2.2.
* K. R. Goodearl, F. Wehrung, *Representations of distributive semilattices in ideal lattices of
  various algebraic structures*, Algebra Universalis **45** (2001), 71–102 (arXiv:math/0011083),
  Lemma 3.2 and Theorem 3.3.
* M. Rørdam, *Classification of Nuclear C*-Algebras*, Encyclopaedia Math. Sci. **126**,
  Springer, 2002, Theorem 1.4.4.
-/

public section

namespace TauCeti

section Presentation

/-- The composite of the bonding maps of a sequential system of simplicial groups from stage
`n` to stage `n + k`. -/
def bondIter {rank : ℕ → ℕ}
    (bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ)) (n : ℕ) :
    ∀ k : ℕ, (Fin (rank n) → ℤ) →+ (Fin (rank (n + k)) → ℤ)
  | 0 => AddMonoidHom.id _
  | k + 1 => (bond (n + k)).comp (bondIter bond n k)

/-- Zero steps of `bondIter` is the identity homomorphism. -/
@[simp]
theorem bondIter_zero {rank : ℕ → ℕ}
    (bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ)) (n : ℕ) :
    bondIter bond n 0 = AddMonoidHom.id _ :=
  (rfl)

/-- `k + 1` steps of `bondIter` composes the `k`-step iterate with `bond (n + k)`. -/
@[simp]
theorem bondIter_succ {rank : ℕ → ℕ}
    (bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ)) (n k : ℕ) :
    bondIter bond n (k + 1) = (bond (n + k)).comp (bondIter bond n k) :=
  (rfl)

/-- If every bonding map is monotone, so is every composite `bondIter bond n k`. -/
theorem bondIter_mono {rank : ℕ → ℕ}
    {bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ)}
    (hbond : ∀ n, Monotone (bond n)) (n k : ℕ) :
    Monotone (bondIter bond n k) := by
  induction k with
  | zero => exact monotone_id
  | succ k ih => exact (hbond (n + k)).comp ih

/-- Iterating `bond` for `d + l` steps from stage `n` agrees with iterating `d` steps from
stage `n` and then `l` steps from stage `n + d`, up to `Fin.cast` along `Nat.add_assoc`. -/
theorem bondIter_add_apply {rank : ℕ → ℕ}
    (bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ))
    (n d l : ℕ) (u : Fin (rank n) → ℤ) :
    bondIter bond n (d + l) u =
      bondIter bond (n + d) l (bondIter bond n d u) ∘
        Fin.cast (congrArg rank (Nat.add_assoc n d l).symm) := by
  have hstep : ∀ {a b : ℕ} (hab : a = b) (v : Fin (rank a) → ℤ),
      bond b (v ∘ Fin.cast (congrArg rank hab.symm)) =
        bond a v ∘ Fin.cast (congrArg rank (congrArg (· + 1) hab).symm) := by
    rintro a _ rfl v
    rfl
  induction l with
  | zero => simp [AddMonoidHom.id_apply]
  | succ l ih =>
    simp only [Nat.add_succ, bondIter_succ, AddMonoidHom.comp_apply, ih]
    exact hstep (Nat.add_assoc n d l) _

/-- An inequality between `k`-step iterates of monotone bonding maps persists at every later stage
`K ≥ k`. -/
theorem bondIter_le_of_le {rank : ℕ → ℕ}
    {bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ)}
    (hbond : ∀ n, Monotone (bond n)) (n : ℕ) {k K : ℕ} (hkK : k ≤ K)
    {x y : Fin (rank n) → ℤ}
    (hxy : bondIter bond n k x ≤ bondIter bond n k y) :
    bondIter bond n K x ≤ bondIter bond n K y := by
  induction K, hkK using Nat.le_induction with
  | base => exact hxy
  | succ K _ ih =>
    rw [bondIter_succ, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
    exact hbond (n + K) ih

/-- A presentation of a partially ordered abelian group `G` as the sequential positive
inductive limit of simplicial groups `(ℤ^{rₙ}, ℕ^{rₙ})`: positive bonding maps (not required to
be injective), compatible positive maps into `G` whose images exhaust `G` and whose images of
the positive cones exhaust `G⁺`, and whose kernels are the eventual kernels of the system. -/
structure SimplicialPresentation (G : Type*) [AddCommGroup G] [PartialOrder G] where
  /-- The rank of the simplicial group at stage `n`. -/
  rank : ℕ → ℕ
  /-- The bonding map from stage `n` to stage `n + 1`. -/
  bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ)
  bond_mono : ∀ n, Monotone (bond n)
  /-- The map from stage `n` to the limit `G`. -/
  toLimit : ∀ n, (Fin (rank n) → ℤ) →+ G
  toLimit_mono : ∀ n, Monotone (toLimit n)
  toLimit_comp_bond : ∀ n, (toLimit (n + 1)).comp (bond n) = toLimit n
  exhausts : ∀ g : G, ∃ n x, toLimit n x = g
  exhausts_pos : ∀ g : G, 0 ≤ g → ∃ n x, 0 ≤ x ∧ toLimit n x = g
  eventually_zero : ∀ n x, toLimit n x = 0 → ∃ k, bondIter bond n k x = 0

namespace SimplicialPresentation

section Basic

variable {G : Type*} [AddCommGroup G] [PartialOrder G]

/-- Applying `bond n` followed by `toLimit (n + 1)` recovers `toLimit n`. -/
@[simp]
theorem toLimit_bond_apply (P : SimplicialPresentation G) (n : ℕ)
    (x : Fin (P.rank n) → ℤ) :
    P.toLimit (n + 1) (P.bond n x) = P.toLimit n x :=
  DFunLike.congr_fun (P.toLimit_comp_bond n) x

/-- Every composite bonding map of a `SimplicialPresentation` is monotone. -/
theorem bondIter_mono (P : SimplicialPresentation G) (n k : ℕ) :
    Monotone (bondIter P.bond n k) :=
  TauCeti.bondIter_mono P.bond_mono n k

/-- An inequality between `k`-step iterates of `P.bond` persists at every stage `K ≥ k`. -/
theorem bondIter_le_of_le (P : SimplicialPresentation G) (n : ℕ) {k K : ℕ} (hkK : k ≤ K)
    {x y : Fin (P.rank n) → ℤ}
    (hxy : bondIter P.bond n k x ≤ bondIter P.bond n k y) :
    bondIter P.bond n K x ≤ bondIter P.bond n K y :=
  TauCeti.bondIter_le_of_le P.bond_mono n hkK hxy

/-- Composing `toLimit (n + k)` with `bondIter P.bond n k` recovers `toLimit n`. -/
@[simp]
theorem toLimit_comp_bondIter (P : SimplicialPresentation G) (n k : ℕ) :
    (P.toLimit (n + k)).comp (bondIter P.bond n k) = P.toLimit n := by
  induction k with
  | zero => exact AddMonoidHom.comp_id (P.toLimit n)
  | succ k ih =>
    rw [bondIter_succ, ← AddMonoidHom.comp_assoc]
    exact (congrArg (·.comp (bondIter P.bond n k)) (P.toLimit_comp_bond (n + k))).trans ih

/-- Applying `bondIter P.bond n k` followed by `toLimit (n + k)` recovers `toLimit n`. -/
@[simp]
theorem toLimit_bondIter_apply (P : SimplicialPresentation G) (n k : ℕ)
    (x : Fin (P.rank n) → ℤ) :
    P.toLimit (n + k) (bondIter P.bond n k x) = P.toLimit n x :=
  DFunLike.congr_fun (P.toLimit_comp_bondIter n k) x

/-- Any element represented at stage `m` is also represented at every stage `n ≥ m`. -/
theorem exists_toLimit_of_le (P : SimplicialPresentation G) {m n : ℕ} (h : m ≤ n)
    {g : G} (hg : ∃ x, P.toLimit m x = g) :
    ∃ x, P.toLimit n x = g := by
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨bondIter P.bond m d x, P.toLimit_bondIter_apply m d x⟩

/-- Any element represented nonnegatively at stage `m` is also represented nonnegatively at
every stage `n ≥ m`. -/
theorem exists_nonneg_toLimit_of_le (P : SimplicialPresentation G) {m n : ℕ} (h : m ≤ n)
    {g : G} (hg : ∃ x, 0 ≤ x ∧ P.toLimit m x = g) :
    ∃ x, 0 ≤ x ∧ P.toLimit n x = g := by
  obtain ⟨x, hx0, rfl⟩ := hg
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨bondIter P.bond m d x, by simpa using P.bondIter_mono m d hx0,
    P.toLimit_bondIter_apply m d x⟩

/-- Any group admitting a `SimplicialPresentation` is countable. -/
theorem countable (P : SimplicialPresentation G) : Countable G := by
  let f : (Σ n : ℕ, Fin (P.rank n) → ℤ) → G := fun p => P.toLimit p.1 p.2
  have hf : Function.Surjective f := fun g =>
    let ⟨n, x, hx⟩ := P.exhausts g
    ⟨⟨n, x⟩, hx⟩
  exact hf.countable

/-- Every group admitting a `SimplicialPresentation` is directed. -/
theorem isDirected (P : SimplicialPresentation G) : IsDirected G (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨n₁, x₁, hx₁⟩ := P.exhausts a
  obtain ⟨n₂, x₂, hx₂⟩ := P.exhausts b
  obtain ⟨y₁, rfl⟩ := P.exists_toLimit_of_le (le_max_left n₁ n₂) ⟨x₁, hx₁⟩
  obtain ⟨y₂, rfl⟩ := P.exists_toLimit_of_le (le_max_right n₁ n₂) ⟨x₂, hx₂⟩
  exact ⟨P.toLimit (max n₁ n₂) (y₁ ⊔ y₂),
    P.toLimit_mono _ le_sup_left, P.toLimit_mono _ le_sup_right⟩

/-- Every group admitting a `SimplicialPresentation` is unperforated. -/
theorem isUnperforated (P : SimplicialPresentation G) : IsUnperforated G := by
  rw [isUnperforated_def]
  intro m hm g hg
  obtain ⟨n₁, x₁, hx₁⟩ := P.exhausts g
  obtain ⟨n₂, z₁, hz₁0, hz₁⟩ := P.exhausts_pos (m • g) hg
  let N := max n₁ n₂
  obtain ⟨x, hx⟩ := P.exists_toLimit_of_le (n := N) (le_max_left n₁ n₂) ⟨x₁, hx₁⟩
  obtain ⟨z, hz0, hz⟩ :=
    P.exists_nonneg_toLimit_of_le (n := N) (le_max_right n₁ n₂) ⟨z₁, hz₁0, hz₁⟩
  have hker : P.toLimit N (m • x - z) = 0 := by rw [map_sub, map_nsmul, hx, hz, sub_self]
  obtain ⟨k, hk⟩ := P.eventually_zero N _ hker
  rw [map_sub, map_nsmul, sub_eq_zero] at hk
  have hmk : 0 ≤ m • bondIter P.bond N k x := by rw [hk]; simpa using P.bondIter_mono N k hz0
  have hx0 : 0 ≤ bondIter P.bond N k x :=
    (isDimensionGroup_pi_int _).isUnperforated.nonneg_of_nsmul_nonneg hm.ne' hmk
  rw [← hx, ← P.toLimit_bondIter_apply N k x]
  simpa using P.toLimit_mono (N + k) hx0

end Basic

section OrderedGroup

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- Order lifting along a `SimplicialPresentation`: if `P.toLimit n x ≤ P.toLimit n y`, then
`bondIter P.bond n k x ≤ bondIter P.bond n k y` at some later stage `n + k`. -/
theorem exists_bondIter_le (P : SimplicialPresentation G) (n : ℕ)
    {x y : Fin (P.rank n) → ℤ} (hxy : P.toLimit n x ≤ P.toLimit n y) :
    ∃ k : ℕ, bondIter P.bond n k x ≤ bondIter P.bond n k y := by
  have hu : 0 ≤ P.toLimit n (y - x) := by
    rw [map_sub]
    exact sub_nonneg.mpr hxy
  obtain ⟨m, z, hz0, hzm⟩ := P.exhausts_pos (P.toLimit n (y - x)) hu
  suffices ∃ k : ℕ, 0 ≤ bondIter P.bond n k (y - x) by
    obtain ⟨k, hk⟩ := this
    exact ⟨k, sub_nonneg.mp (by rwa [← map_sub])⟩
  rcases le_total n m with hnm | hmn
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hker : P.toLimit (n + d) (bondIter P.bond n d (y - x) - z) = 0 := by
      rw [map_sub, P.toLimit_bondIter_apply, hzm, sub_self]
    obtain ⟨l, hl⟩ := P.eventually_zero (n + d) _ hker
    have hl' : 0 ≤ bondIter P.bond (n + d) l (bondIter P.bond n d (y - x)) := by
      rw [map_sub, sub_eq_zero] at hl
      rw [hl]
      simpa using P.bondIter_mono (n + d) l hz0
    refine ⟨d + l, ?_⟩
    rw [bondIter_add_apply]
    exact fun _ => hl' _
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have hz'0 : 0 ≤ bondIter P.bond m d z := by
      simpa using P.bondIter_mono m d hz0
    have hker : P.toLimit (m + d) ((y - x) - bondIter P.bond m d z) = 0 := by
      rw [map_sub, P.toLimit_bondIter_apply, hzm, sub_self]
    obtain ⟨k, hk⟩ := P.eventually_zero (m + d) _ hker
    refine ⟨k, ?_⟩
    rw [map_sub, sub_eq_zero] at hk
    rw [hk]
    simpa using P.bondIter_mono (m + d) k hz'0

/-- Every group admitting a `SimplicialPresentation` satisfies Riesz interpolation. -/
theorem hasRieszInterpolation (P : SimplicialPresentation G) : HasRieszInterpolation G := by
  rw [hasRieszInterpolation_def]
  intro a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂
  obtain ⟨n₁, x₁₀, hx₁₀⟩ := P.exhausts a₁
  obtain ⟨n₂, x₂₀, hx₂₀⟩ := P.exhausts a₂
  obtain ⟨n₃, y₁₀, hy₁₀⟩ := P.exhausts b₁
  obtain ⟨n₄, y₂₀, hy₂₀⟩ := P.exhausts b₂
  let N := max (max n₁ n₂) (max n₃ n₄)
  obtain ⟨x₁, rfl⟩ :=
    P.exists_toLimit_of_le (n := N) (le_max_of_le_left (le_max_left n₁ n₂)) ⟨x₁₀, hx₁₀⟩
  obtain ⟨x₂, rfl⟩ :=
    P.exists_toLimit_of_le (n := N) (le_max_of_le_left (le_max_right n₁ n₂)) ⟨x₂₀, hx₂₀⟩
  obtain ⟨y₁, rfl⟩ :=
    P.exists_toLimit_of_le (n := N) (le_max_of_le_right (le_max_left n₃ n₄)) ⟨y₁₀, hy₁₀⟩
  obtain ⟨y₂, rfl⟩ :=
    P.exists_toLimit_of_le (n := N) (le_max_of_le_right (le_max_right n₃ n₄)) ⟨y₂₀, hy₂₀⟩
  obtain ⟨k₁₁, hk₁₁⟩ := P.exists_bondIter_le N h₁₁
  obtain ⟨k₁₂, hk₁₂⟩ := P.exists_bondIter_le N h₁₂
  obtain ⟨k₂₁, hk₂₁⟩ := P.exists_bondIter_le N h₂₁
  obtain ⟨k₂₂, hk₂₂⟩ := P.exists_bondIter_le N h₂₂
  let K := max (max k₁₁ k₁₂) (max k₂₁ k₂₂)
  obtain ⟨z, hz₁, hz₂, hz₃, hz₄⟩ :=
    (isDimensionGroup_pi_int (Fin (P.rank (N + K)))).hasRieszInterpolation.exists_between
      (P.bondIter_le_of_le N (K := K) (le_max_of_le_left (le_max_left k₁₁ k₁₂)) hk₁₁)
      (P.bondIter_le_of_le N (K := K) (le_max_of_le_left (le_max_right k₁₁ k₁₂)) hk₁₂)
      (P.bondIter_le_of_le N (K := K) (le_max_of_le_right (le_max_left k₂₁ k₂₂)) hk₂₁)
      (P.bondIter_le_of_le N (K := K) (le_max_of_le_right (le_max_right k₂₁ k₂₂)) hk₂₂)
  exact ⟨P.toLimit (N + K) z,
    (P.toLimit_bondIter_apply N K x₁).symm.trans_le (P.toLimit_mono (N + K) hz₁),
    (P.toLimit_bondIter_apply N K x₂).symm.trans_le (P.toLimit_mono (N + K) hz₂),
    (P.toLimit_mono (N + K) hz₃).trans_eq (P.toLimit_bondIter_apply N K y₁),
    (P.toLimit_mono (N + K) hz₄).trans_eq (P.toLimit_bondIter_apply N K y₂)⟩

/-- Every group admitting a `SimplicialPresentation` is a dimension group. -/
theorem isDimensionGroup (P : SimplicialPresentation G) : IsDimensionGroup G :=
  IsDimensionGroup.mk P.isDirected P.isUnperforated P.hasRieszInterpolation

end OrderedGroup

end SimplicialPresentation

end Presentation

section ShenTriangle

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

private theorem exists_shen_decomp (hu : IsUnperforated G) (hr : HasRieszInterpolation G)
    {r : ℕ} {w : Fin r → G} (hw : ∀ i, 0 ≤ w i) {x : Fin r → ℤ}
    (hsum : ∑ i, x i • w i = 0) {M : ℕ} (hM : 0 < M)
    (hbound : ∀ i, (x i).natAbs ≤ M) {k₀ : Fin r} (hxk₀ : x k₀ = (M : ℤ)) :
    ∃ h : Fin r → G,
      (∀ j ∈ Finset.univ.filter (fun j => x j < 0), 0 ≤ h j ∧ h j ≤ w j) ∧
      ∑ j ∈ Finset.univ.filter (fun j => x j < 0), h j = w k₀ := by
  let Ipos := (Finset.univ.filter fun i : Fin r => 0 ≤ x i).erase k₀
  let Ineg := Finset.univ.filter fun j : Fin r => x j < 0
  have hk₀_mem : k₀ ∈ Finset.univ.filter (fun i : Fin r => 0 ≤ x i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ k₀, by omega⟩
  have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin r => 0 ≤ x i)
    (fun i => x i • w i)).symm
  simp only [not_le] at hsplit
  rw [hsum, ← Finset.add_sum_erase _ _ hk₀_mem, hxk₀] at hsplit
  have hpos : 0 ≤ ∑ i ∈ Ipos, x i • w i :=
    Finset.sum_nonneg fun i hi =>
      zsmul_nonneg (hw i) (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).2
  have heq : (M : ℤ) • w k₀ + ∑ i ∈ Ipos, x i • w i = ∑ j ∈ Ineg, (-x j) • w j := by
    have hneg : ∑ j ∈ Ineg, (-x j) • w j = -∑ j ∈ Ineg, x j • w j := by
      simp [Finset.sum_neg_distrib]
    rw [hneg]
    exact eq_neg_of_add_eq_zero_left hsplit.symm
  have hneg_le : ∑ j ∈ Ineg, (-x j) • w j ≤ (M : ℤ) • ∑ j ∈ Ineg, w j := by
    rw [Finset.smul_sum]
    refine Finset.sum_le_sum fun j _ => zsmul_le_zsmul_left (hw j) ?_
    have := hbound j
    omega
  have hMle : M • w k₀ ≤ M • ∑ j ∈ Ineg, w j := by
    rw [← natCast_zsmul, ← natCast_zsmul]
    exact (le_add_of_nonneg_right hpos).trans (heq.trans_le hneg_le)
  exact hr.exists_finset_sum_eq_of_le_sum (fun j _ => hw j) (hw k₀)
    ((hu.nsmul_le_nsmul_iff_right hM.ne').mp hMle)

private abbrev ShenIndex {r : ℕ} (x : Fin r → ℤ) (k₀ : Fin r) : Type :=
  {i : Fin r // i ∈ (Finset.univ.filter (fun i => 0 ≤ x i)).erase k₀} ⊕
    ({j : Fin r // j ∈ Finset.univ.filter (fun j => x j < 0)} ⊕
      {j : Fin r // j ∈ Finset.univ.filter (fun j => x j < 0)})

private def shenRawHom {r : ℕ} (x : Fin r → ℤ) (k₀ : Fin r) :
    (Fin r → ℤ) →+ (ShenIndex x k₀ → ℤ) where
  toFun y := Sum.elim (fun i => y i.1)
    (Sum.elim (fun j => y k₀ + y j.1) (fun j => y j.1))
  map_zero' := by ext (_ | (_ | _)) <;> simp
  map_add' y₁ y₂ := by ext (_ | (_ | _)) <;> simp; abel

private theorem shenRawHom_mono {r : ℕ} (x : Fin r → ℤ) (k₀ : Fin r) :
    Monotone (shenRawHom x k₀) := by
  rintro y₁ y₂ hy (_ | (_ | _))
  · exact hy _
  · exact add_le_add (hy k₀) (hy _)
  · exact hy _

private def shenRawWeights {r : ℕ} (x : Fin r → ℤ) (k₀ : Fin r)
    (w h : Fin r → G) : ShenIndex x k₀ → G :=
  Sum.elim (fun i => w i.1) (Sum.elim (fun j => h j.1) (fun j => w j.1 - h j.1))

private theorem shenRawWeights_nonneg {r : ℕ} {x : Fin r → ℤ} {k₀ : Fin r}
    {w h : Fin r → G} (hw : ∀ i, 0 ≤ w i)
    (hh : ∀ j ∈ Finset.univ.filter (fun j => x j < 0), 0 ≤ h j ∧ h j ≤ w j) :
    ∀ u, 0 ≤ shenRawWeights x k₀ w h u := by
  rintro (i | (j | j))
  · exact hw i.1
  · exact (hh j.1 j.2).1
  · exact sub_nonneg.mpr (hh j.1 j.2).2

omit [PartialOrder G] [IsOrderedAddMonoid G] in
private theorem shenRawSum_eq {r : ℕ} {x : Fin r → ℤ} {k₀ : Fin r}
    (hk₀ : 0 ≤ x k₀) {w h : Fin r → G}
    (hh_sum : ∑ j ∈ Finset.univ.filter (fun j => x j < 0), h j = w k₀)
    (y : Fin r → ℤ) :
    ∑ u : ShenIndex x k₀, shenRawHom x k₀ y u • shenRawWeights x k₀ w h u =
      ∑ i : Fin r, y i • w i := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_attach, shenRawHom, shenRawWeights, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_attach _ (fun i => y i • w i),
    Finset.sum_attach _ (fun j => (y k₀ + y j) • h j),
    Finset.sum_attach _ (fun j => y j • (w j - h j))]
  have hcombine :
      ∑ j ∈ Finset.univ.filter (fun j => x j < 0), (y k₀ + y j) • h j +
          ∑ j ∈ Finset.univ.filter (fun j => x j < 0), y j • (w j - h j) =
        y k₀ • w k₀ + ∑ j ∈ Finset.univ.filter (fun j => x j < 0), y j • w j := by
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ j, (y k₀ + y j) • h j + y j • (w j - h j) = y k₀ • h j + y j • w j := by
      intro j
      rw [add_zsmul, zsmul_sub]
      abel
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, hh_sum]
  have hk₀_mem : k₀ ∈ Finset.univ.filter (fun i : Fin r => 0 ≤ x i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ k₀, hk₀⟩
  rw [hcombine, ← add_assoc, Finset.sum_erase_add _ _ hk₀_mem]
  simpa only [not_le] using
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin r => 0 ≤ x i) (fun i => y i • w i)

private theorem shenRawHom_natAbs_le {r : ℕ} {x : Fin r → ℤ} {M : ℕ}
    (hbound : ∀ i, (x i).natAbs ≤ M) {k₀ : Fin r} (hxk₀ : x k₀ = (M : ℤ))
    (u : ShenIndex x k₀) :
    (shenRawHom x k₀ x u).natAbs ≤ M := by
  rcases u with i | (j | j)
  · exact hbound i.1
  · have hlt := (Finset.mem_filter.mp j.2).2
    have hb := hbound j.1
    simp only [shenRawHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Sum.elim_inr, Sum.elim_inl, hxk₀]
    omega
  · exact hbound j.1

private theorem shenRawHom_mid_ne {r : ℕ} {x : Fin r → ℤ} {M : ℕ}
    (hbound : ∀ i, (x i).natAbs ≤ M) {k₀ : Fin r} (hxk₀ : x k₀ = (M : ℤ))
    (j : {j : Fin r // j ∈ Finset.univ.filter (fun j => x j < 0)}) :
    (shenRawHom x k₀ x (Sum.inr (Sum.inl j))).natAbs ≠ M := by
  have hlt := (Finset.mem_filter.mp j.2).2
  have hb := hbound j.1
  simp only [shenRawHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Sum.elim_inr, Sum.elim_inl, hxk₀]
  omega

private theorem shenRawCard_lt {r : ℕ} {x : Fin r → ℤ} {M : ℕ}
    (hbound : ∀ i, (x i).natAbs ≤ M) {k₀ : Fin r} (hxk₀ : x k₀ = (M : ℤ)) :
    (Finset.univ.filter fun u : ShenIndex x k₀ => (shenRawHom x k₀ x u).natAbs = M).card <
      (Finset.univ.filter fun i : Fin r => (x i).natAbs = M).card := by
  let Sκ := Finset.univ.filter fun u : ShenIndex x k₀ => (shenRawHom x k₀ x u).natAbs = M
  let Sr := Finset.univ.filter fun i : Fin r => (x i).natAbs = M
  let proj : ShenIndex x k₀ → Fin r :=
    Sum.elim Subtype.val (Sum.elim (fun _ => k₀) Subtype.val)
  have hno_mid : ∀ j, Sum.inr (Sum.inl j) ∉ Sκ := fun j hj =>
    shenRawHom_mid_ne hbound hxk₀ j (Finset.mem_filter.mp hj).2
  have hsep : ∀ (i : {i : Fin r // i ∈ (Finset.univ.filter (fun i => 0 ≤ x i)).erase k₀})
      (j : {j : Fin r // j ∈ Finset.univ.filter (fun j => x j < 0)}),
      proj (Sum.inl i) ≠ proj (Sum.inr (Sum.inr j)) := by
    intro i j hp
    have hi := (Finset.mem_filter.mp (Finset.mem_erase.mp i.2).2).2
    have hj := (Finset.mem_filter.mp j.2).2
    simp only [proj, Sum.elim_inl, Sum.elim_inr] at hp
    rw [hp] at hi
    omega
  have hinj : Set.InjOn proj Sκ := by
    rintro (i₁ | (j₁ | j₁)) hu₁ (i₂ | (j₂ | j₂)) hu₂ hp <;>
      first
      | exact (hno_mid _ ‹_›).elim
      | exact congrArg Sum.inl (Subtype.ext hp)
      | exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext hp)
      | exact (hsep _ _ hp).elim
      | exact (hsep _ _ hp.symm).elim
  have hssub : Sκ.image proj ⊂ Sr := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨k₀, by simp [Sr, hxk₀], fun hk₀_im => ?_⟩
      obtain ⟨i | (j | j), hu, hpu⟩ := Finset.mem_image.mp hk₀_im
      · exact (Finset.mem_erase.mp i.2).1 hpu
      · exact hno_mid j hu
      · have hlt := (Finset.mem_filter.mp j.2).2
        simp only [proj, Sum.elim_inr] at hpu
        rw [hpu] at hlt
        omega
    · rintro z hz
      obtain ⟨i | (j | j), hu, rfl⟩ := Finset.mem_image.mp hz
      · simpa [Sr, proj, shenRawHom] using (Finset.mem_filter.mp hu).2
      · exact (hno_mid j hu).elim
      · simpa [Sr, proj, shenRawHom] using (Finset.mem_filter.mp hu).2
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_lt_card hssub

private theorem shenStepPos (hu : IsUnperforated G) (hr : HasRieszInterpolation G)
    {r : ℕ} {w : Fin r → G} (hw : ∀ i, 0 ≤ w i) {x : Fin r → ℤ}
    (hsum : ∑ i, x i • w i = 0) {M : ℕ} (hM : 0 < M)
    (hbound : ∀ i, (x i).natAbs ≤ M) {k₀ : Fin r} (hxk₀ : x k₀ = (M : ℤ)) :
    ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (w' : Fin s → G),
      Monotone α ∧ (∀ u, 0 ≤ w' u) ∧
      (∀ y, ∑ u, α y u • w' u = ∑ i, y i • w i) ∧
      (∀ u, (α x u).natAbs ≤ M) ∧
      (Finset.univ.filter fun u : Fin s => (α x u).natAbs = M).card <
        (Finset.univ.filter fun i : Fin r => (x i).natAbs = M).card := by
  obtain ⟨h, hh, hh_sum⟩ := exists_shen_decomp hu hr hw hsum hM hbound hxk₀
  have hlt := shenRawCard_lt hbound hxk₀
  let e : ShenIndex x k₀ ≃ Fin (Fintype.card (ShenIndex x k₀)) := Fintype.equivFin _
  let α : (Fin r → ℤ) →+ (Fin (Fintype.card (ShenIndex x k₀)) → ℤ) :=
    { toFun := fun y u => shenRawHom x k₀ y (e.symm u)
      map_zero' := by ext u; simp
      map_add' := fun y₁ y₂ => by ext u; simp }
  refine ⟨Fintype.card (ShenIndex x k₀), α, fun u => shenRawWeights x k₀ w h (e.symm u),
    fun y₁ y₂ hy u => shenRawHom_mono x k₀ hy (e.symm u),
    fun u => shenRawWeights_nonneg hw hh (e.symm u),
    fun y => ?_, fun u => shenRawHom_natAbs_le hbound hxk₀ (e.symm u), ?_⟩
  · simp only [α, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [Equiv.sum_comp e.symm (fun v => shenRawHom x k₀ y v • shenRawWeights x k₀ w h v)]
    exact shenRawSum_eq (by omega) hh_sum y
  · have hcard :
        (Finset.univ.filter fun u => (α x u).natAbs = M).card =
          (Finset.univ.filter fun v : ShenIndex x k₀ => (shenRawHom x k₀ x v).natAbs = M).card := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr (Equiv.subtypeEquiv e.symm fun _ => Iff.rfl)
    exact hcard.trans_lt hlt

private theorem shenStep (hu : IsUnperforated G) (hr : HasRieszInterpolation G)
    {r : ℕ} {w : Fin r → G} (hw : ∀ i, 0 ≤ w i) {x : Fin r → ℤ}
    (hsum : ∑ i, x i • w i = 0) {M : ℕ} (hM : 0 < M)
    (hbound : ∀ i, (x i).natAbs ≤ M) {k₀ : Fin r} (hxk₀ : (x k₀).natAbs = M) :
    ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (w' : Fin s → G),
      Monotone α ∧ (∀ u, 0 ≤ w' u) ∧
      (∀ y, ∑ u, α y u • w' u = ∑ i, y i • w i) ∧
      (∀ u, (α x u).natAbs ≤ M) ∧
      (Finset.univ.filter fun u : Fin s => (α x u).natAbs = M).card <
        (Finset.univ.filter fun i : Fin r => (x i).natAbs = M).card := by
  rcases Int.natAbs_eq (x k₀) with hpos | hneg
  · exact shenStepPos hu hr hw hsum hM hbound (hpos.trans (congrArg Nat.cast hxk₀))
  · have hsum_neg : ∑ i, (-x) i • w i = 0 := by
      simp [Pi.neg_apply, Finset.sum_neg_distrib, hsum]
    have hbound_neg : ∀ i, ((-x) i).natAbs ≤ M := fun i => by simp [hbound i]
    have hxk₀_neg : (-x) k₀ = (M : ℤ) := by
      simp only [Pi.neg_apply]
      rw [hxk₀] at hneg
      omega
    obtain ⟨s, α, w', hα, hw', hαsum, hαb, hαlt⟩ :=
      shenStepPos hu hr hw hsum_neg hM hbound_neg hxk₀_neg
    refine ⟨s, α, w', hα, hw', hαsum, ?_, ?_⟩
    · intro u
      simpa [map_neg] using hαb u
    · simpa [map_neg] using hαlt

private theorem shenReduceCount (hu : IsUnperforated G) (hr : HasRieszInterpolation G)
    {M : ℕ} (hM : 0 < M) (c : ℕ) :
    ∀ {r : ℕ} {w : Fin r → G}, (∀ i, 0 ≤ w i) →
      ∀ {x : Fin r → ℤ}, ∑ i, x i • w i = 0 → (∀ i, (x i).natAbs ≤ M) →
        (Finset.univ.filter fun i : Fin r => (x i).natAbs = M).card ≤ c →
        ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (w' : Fin s → G),
          Monotone α ∧ (∀ u, 0 ≤ w' u) ∧
          (∀ y, ∑ u, α y u • w' u = ∑ i, y i • w i) ∧
          (∀ u, (α x u).natAbs ≤ M - 1) := by
  induction c with
  | zero =>
    intro r w hw x _ hbound hcard
    rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard
    refine ⟨r, AddMonoidHom.id _, w, monotone_id, hw, fun _ => rfl, fun i => ?_⟩
    have hne : (x i).natAbs ≠ M := hcard (Finset.mem_univ i)
    have hle := hbound i
    simp only [AddMonoidHom.id_apply]
    omega
  | succ c ih =>
    intro r w hw x hsum hbound hcard
    rcases (Finset.univ.filter fun i : Fin r => (x i).natAbs = M).eq_empty_or_nonempty with
      hemp | ⟨k₀, hk₀⟩
    · refine ⟨r, AddMonoidHom.id _, w, monotone_id, hw, fun _ => rfl, fun i => ?_⟩
      have hne : (x i).natAbs ≠ M := Finset.filter_eq_empty_iff.mp hemp (Finset.mem_univ i)
      have hle := hbound i
      simp only [AddMonoidHom.id_apply]
      omega
    · obtain ⟨r₁, α₁, w₁, hα₁, hw₁, hsum₁, hb₁, hlt₁⟩ :=
        shenStep hu hr hw hsum hM hbound (Finset.mem_filter.mp hk₀).2
      obtain ⟨s, α₂, w₂, hα₂, hw₂, hsum₂, hb₂⟩ :=
        ih hw₁ ((hsum₁ x).trans hsum) hb₁ (Nat.le_of_lt_succ (hlt₁.trans_le hcard))
      exact ⟨s, α₂.comp α₁, w₂, hα₂.comp hα₁, hw₂,
        fun y => (hsum₂ (α₁ y)).trans (hsum₁ y), hb₂⟩

private theorem shenReduceAll (hu : IsUnperforated G) (hr : HasRieszInterpolation G)
    (M : ℕ) :
    ∀ {r : ℕ} {w : Fin r → G}, (∀ i, 0 ≤ w i) →
      ∀ {x : Fin r → ℤ}, ∑ i, x i • w i = 0 → (∀ i, (x i).natAbs ≤ M) →
        ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (w' : Fin s → G),
          Monotone α ∧ (∀ u, 0 ≤ w' u) ∧
          (∀ y, ∑ u, α y u • w' u = ∑ i, y i • w i) ∧ α x = 0 := by
  induction M with
  | zero =>
    intro r w hw x _ hbound
    refine ⟨r, AddMonoidHom.id _, w, monotone_id, hw, fun _ => rfl, ?_⟩
    ext i
    exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp (hbound i))
  | succ M ih =>
    intro r w hw x hsum hbound
    have hcard :
        (Finset.univ.filter fun i : Fin r => (x i).natAbs = M + 1).card ≤ r :=
      (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin r)
    obtain ⟨r₁, α₁, w₁, hα₁, hw₁, hsum₁, hb₁⟩ :=
      shenReduceCount hu hr (Nat.succ_pos M) r hw hsum hbound hcard
    obtain ⟨s, α₂, w₂, hα₂, hw₂, hsum₂, hzero⟩ :=
      ih hw₁ ((hsum₁ x).trans hsum) hb₁
    exact ⟨s, α₂.comp α₁, w₂, hα₂.comp hα₁, hw₂,
      fun y => (hsum₂ (α₁ y)).trans (hsum₁ y), hzero⟩

/-- **Shen's triangle lemma** (Effros–Handelman–Shen, Lemma 2.1; Goodearl–Wehrung, Lemma 3.2):
if `G` is unperforated with Riesz interpolation, `f : (Fin r → ℤ) →+ G` is monotone, and
`f x = 0`, then `f` factors as `β.comp α` through some `Fin s → ℤ` with `α` and `β` monotone
and `α x = 0`. -/
theorem exists_monotone_factorization_of_map_eq_zero
    (hu : IsUnperforated G) (hr : HasRieszInterpolation G)
    {r : ℕ} (f : (Fin r → ℤ) →+ G) (hf : Monotone f)
    (x : Fin r → ℤ) (hx : f x = 0) :
    ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (β : (Fin s → ℤ) →+ G),
      Monotone α ∧ Monotone β ∧ β.comp α = f ∧ α x = 0 := by
  let w : Fin r → G := fun i => f (Pi.single i 1)
  have hw : ∀ i, 0 ≤ w i := fun i => by
    have h0 : (0 : Fin r → ℤ) ≤ Pi.single i 1 := fun j => by
      rcases eq_or_ne j i with rfl | hji <;> simp [*]
    simpa [w] using hf h0
  have hlin : ∀ y : Fin r → ℤ, ∑ i, y i • w i = f y := fun y => by
    conv_rhs => rw [pi_eq_sum_univ' y, map_sum]
    exact Finset.sum_congr (s₁ := Finset.univ) rfl fun i _ =>
      (map_zsmul f (y i) (Pi.single i 1)).symm
  let M : ℕ := Finset.univ.sup fun i : Fin r => (x i).natAbs
  have hbound : ∀ i : Fin r, (x i).natAbs ≤ M := fun i =>
    Finset.le_sup (f := fun j : Fin r => (x j).natAbs) (Finset.mem_univ i)
  obtain ⟨s, α, w', hα, hw', hsum', hzero⟩ :=
    shenReduceAll hu hr M hw ((hlin x).trans hx) hbound
  refine ⟨s, α, (Fintype.linearCombination ℤ w').toAddMonoidHom, hα,
    fun _ _ hxy => Finset.sum_le_sum (s := Finset.univ)
      fun u _ => zsmul_le_zsmul_left (hw' u) (hxy u), ?_, hzero⟩
  exact DFunLike.ext _ _ fun y => (hsum' y).trans (hlin y)

/-- Finite-subset form of Shen's triangle lemma: for any finite subset `F ⊆ ker f` of a monotone
homomorphism `f : (Fin r → ℤ) →+ G` into an unperforated group with Riesz interpolation, `f`
factors monotonically through some `Fin s → ℤ` annihilating all of `F`. -/
theorem exists_monotone_factorization_finset
    (hu : IsUnperforated G) (hr : HasRieszInterpolation G)
    {r : ℕ} (f : (Fin r → ℤ) →+ G) (hf : Monotone f)
    (F : Finset (Fin r → ℤ)) (hF : ∀ x ∈ F, f x = 0) :
    ∃ (s : ℕ) (α : (Fin r → ℤ) →+ (Fin s → ℤ)) (β : (Fin s → ℤ) →+ G),
      Monotone α ∧ Monotone β ∧ β.comp α = f ∧ ∀ x ∈ F, α x = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨r, AddMonoidHom.id _, f, monotone_id, hf, AddMonoidHom.comp_id f, by simp⟩
  | @insert x₀ F hx₀ ih =>
    obtain ⟨s₁, α₁, β₁, hα₁, hβ₁, hcomp₁, hzero₁⟩ :=
      ih fun x hx => hF x (Finset.mem_insert_of_mem hx)
    have hx₀_zero : β₁ (α₁ x₀) = 0 := by
      rw [← AddMonoidHom.comp_apply, hcomp₁]
      exact hF x₀ (Finset.mem_insert_self x₀ F)
    obtain ⟨s, α₂, β₂, hα₂, hβ₂, hcomp₂, hzero₂⟩ :=
      exists_monotone_factorization_of_map_eq_zero hu hr β₁ hβ₁ (α₁ x₀) hx₀_zero
    refine ⟨s, α₂.comp α₁, β₂, hα₂.comp hα₁, hβ₂,
      by rw [← AddMonoidHom.comp_assoc, hcomp₂, hcomp₁], ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hzero₂
    · simp [hzero₁ x hx']

end ShenTriangle

section InductiveConstruction

variable {G : Type*} [AddCommGroup G] [PartialOrder G]

private structure SimplicialStage (G : Type*) [AddCommGroup G] [PartialOrder G] (n : ℕ) where
  rank : ℕ
  toLimit : (Fin rank → ℤ) →+ G
  toLimit_mono : Monotone toLimit
  seqs : Fin (n + 1) → ℕ → (Fin rank → ℤ)

private noncomputable def stageCandidates {n : ℕ} (S : SimplicialStage G n) :
    Finset (Fin S.rank → ℤ) := by
  classical
  exact (Finset.univ.biUnion fun i : Fin (n + 1) =>
    (Finset.range (n + 1)).image (S.seqs i)).filter fun y => S.toLimit y = 0

private structure NextStage {n : ℕ} (S : SimplicialStage G n) (g : G)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) where
  stage : SimplicialStage G (n + 1)
  bond : (Fin S.rank → ℤ) →+ (Fin stage.rank → ℤ)
  bond_mono : Monotone bond
  toLimit_comp_bond : stage.toLimit.comp bond = S.toLimit
  exists_nonneg_toLimit_eq : ∃ x : Fin stage.rank → ℤ, 0 ≤ x ∧ stage.toLimit x = g
  bond_eq_zero : ∀ y ∈ stageCandidates S, bond y = 0
  seqs_last : stage.seqs (Fin.last (n + 1)) = enumZVec stage.rank
  seqs_castSucc : ∀ (i : Fin (n + 1)) (j : ℕ), stage.seqs (Fin.castSucc i) j = bond (S.seqs i j)

variable [IsOrderedAddMonoid G]

private theorem exists_nextStage (hd : IsDimensionGroup G) {n : ℕ}
    (S : SimplicialStage G n) {g : G} (hg : 0 ≤ g)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) :
    Nonempty (NextStage S g enumZVec) := by
  have hK : ∀ y ∈ stageCandidates S, S.toLimit y = 0 := fun y hy => by
    classical exact (Finset.mem_filter.mp hy).2
  obtain ⟨s, α, β, hα, hβ, hcomp, hzero⟩ := exists_monotone_factorization_finset
    hd.isUnperforated hd.hasRieszInterpolation S.toLimit S.toLimit_mono (stageCandidates S) hK
  let inl : (Fin s → ℤ) →+ (Fin (s + 1) → ℤ) :=
    { toFun := Fin.lastCases 0
      map_zero' := by ext i; cases i using Fin.lastCases <;> simp
      map_add' := fun z₁ z₂ => by ext i; cases i using Fin.lastCases <;> simp }
  have hinl_mono : Monotone inl := fun z₁ z₂ hz i => by
    cases i using Fin.lastCases <;> [simp [inl]; simpa [inl] using hz _]
  let toLim : (Fin (s + 1) → ℤ) →+ G :=
    { toFun := fun w => β (w ∘ Fin.castSucc) + w (Fin.last s) • g
      map_zero' := by simp
      map_add' := fun w₁ w₂ => by
        have hcs : (w₁ + w₂) ∘ Fin.castSucc = w₁ ∘ Fin.castSucc + w₂ ∘ Fin.castSucc := rfl
        rw [hcs, map_add, Pi.add_apply, add_zsmul]; abel }
  have htoLim_mono : Monotone toLim := fun _ _ hw =>
    add_le_add (hβ fun u => hw (Fin.castSucc u)) (zsmul_le_zsmul_left hg (hw (Fin.last s)))
  have htoLim_inl : toLim.comp inl = β := by
    refine DFunLike.ext _ _ fun z => ?_
    have hcs : Fin.lastCases (0 : ℤ) z ∘ Fin.castSucc = z := by ext u; simp
    simp [toLim, inl, hcs]
  have htoLim_last : toLim (Pi.single (Fin.last s) 1) = g := by
    have hcs : (Pi.single (Fin.last s) (1 : ℤ)) ∘ Fin.castSucc = 0 := by
      ext u; exact Pi.single_eq_of_ne (Fin.castSucc_ne_last u) 1
    simp [toLim, hcs]
  refine ⟨{
    stage :=
      { rank := s + 1
        toLimit := toLim
        toLimit_mono := htoLim_mono
        seqs := Fin.lastCases (enumZVec (s + 1)) (fun i j => inl (α (S.seqs i j))) }
    bond := inl.comp α
    bond_mono := hinl_mono.comp hα
    toLimit_comp_bond := by rw [← AddMonoidHom.comp_assoc, htoLim_inl, hcomp]
    exists_nonneg_toLimit_eq := ⟨Pi.single (Fin.last s) 1,
      fun j => by rcases eq_or_ne j (Fin.last s) with rfl | hj <;> simp [*], htoLim_last⟩
    bond_eq_zero := fun y hy => by rw [AddMonoidHom.comp_apply, hzero y hy, map_zero]
    seqs_last := by simp
    seqs_castSucc := fun i j => by simp }⟩

private noncomputable def nextStage (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ))
    (n : ℕ) (S : SimplicialStage G n) : NextStage S (posEnum n) enumZVec :=
  Classical.choice (exists_nextStage hd S (hpos n) enumZVec)

private noncomputable def stageSeq (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) :
    ∀ n : ℕ, SimplicialStage G n
  | 0 =>
    { rank := 0
      toLimit := 0
      toLimit_mono := monotone_const
      seqs := fun _ => enumZVec 0 }
  | n + 1 => (nextStage hd posEnum hpos enumZVec n (stageSeq hd posEnum hpos enumZVec n)).stage

@[simp]
private theorem stageSeq_zero (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) :
    stageSeq hd posEnum hpos enumZVec 0 =
      { rank := 0
        toLimit := 0
        toLimit_mono := monotone_const
        seqs := fun _ => enumZVec 0 } :=
  rfl

@[simp]
private theorem stageSeq_succ (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) (n : ℕ) :
    stageSeq hd posEnum hpos enumZVec (n + 1) =
      (nextStage hd posEnum hpos enumZVec n (stageSeq hd posEnum hpos enumZVec n)).stage :=
  rfl

private noncomputable def stageBond (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) (n : ℕ) :
    (Fin (stageSeq hd posEnum hpos enumZVec n).rank → ℤ) →+
      (Fin (stageSeq hd posEnum hpos enumZVec (n + 1)).rank → ℤ) :=
  (nextStage hd posEnum hpos enumZVec n (stageSeq hd posEnum hpos enumZVec n)).bond

@[simp]
private theorem stageBond_eq (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) (n : ℕ) :
    stageBond hd posEnum hpos enumZVec n =
      (nextStage hd posEnum hpos enumZVec n (stageSeq hd posEnum hpos enumZVec n)).bond :=
  rfl

private theorem stageSeq_succ_seqs_castSucc (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) (n : ℕ) (i : Fin (n + 1)) (j : ℕ) :
    (stageSeq hd posEnum hpos enumZVec (n + 1)).seqs (Fin.castSucc i) j =
      stageBond hd posEnum hpos enumZVec n
        ((stageSeq hd posEnum hpos enumZVec n).seqs i j) := by
  simp only [stageSeq_succ, stageBond_eq]
  exact (nextStage hd posEnum hpos enumZVec n
    (stageSeq hd posEnum hpos enumZVec n)).seqs_castSucc i j

private theorem stageSeq_toLimit_comp_stageBond (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) (n : ℕ) :
    ((stageSeq hd posEnum hpos enumZVec (n + 1)).toLimit).comp
        (stageBond hd posEnum hpos enumZVec n) =
      (stageSeq hd posEnum hpos enumZVec n).toLimit := by
  simp only [stageSeq_succ, stageBond_eq]
  exact (nextStage hd posEnum hpos enumZVec n
    (stageSeq hd posEnum hpos enumZVec n)).toLimit_comp_bond

private theorem stageSeq_seqs (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) (m d j : ℕ) :
    (stageSeq hd posEnum hpos enumZVec (m + d)).seqs
        ⟨m, Nat.lt_succ_of_le (Nat.le_add_right m d)⟩ j =
      bondIter (stageBond hd posEnum hpos enumZVec) m d
        (enumZVec (stageSeq hd posEnum hpos enumZVec m).rank j) := by
  induction d with
  | zero =>
    simp only [Nat.add_zero, bondIter_zero, AddMonoidHom.id_apply]
    have hlast : (⟨m, Nat.lt_succ_of_le (Nat.le_refl m)⟩ : Fin (m + 1)) = Fin.last m :=
      Fin.ext rfl
    rw [hlast]
    cases m with
    | zero => simp
    | succ m =>
      simp [(nextStage hd posEnum hpos enumZVec m
        (stageSeq hd posEnum hpos enumZVec m)).seqs_last]
  | succ d ih =>
    have hcast :
        (⟨m, Nat.lt_succ_of_le (Nat.le_add_right m (d + 1))⟩ : Fin (m + (d + 1) + 1)) =
          Fin.castSucc ⟨m, Nat.lt_succ_of_le (Nat.le_add_right m d)⟩ := Fin.ext rfl
    rw [hcast]
    simp only [Nat.add_succ, bondIter_succ, AddMonoidHom.comp_apply, ← ih,
      stageSeq_succ_seqs_castSucc]

private theorem stageSeq_toLimit_comp_bondIter (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ)) (m k : ℕ) :
    ((stageSeq hd posEnum hpos enumZVec (m + k)).toLimit).comp
        (bondIter (stageBond hd posEnum hpos enumZVec) m k) =
      (stageSeq hd posEnum hpos enumZVec m).toLimit := by
  induction k with
  | zero => exact AddMonoidHom.comp_id _
  | succ k ih =>
    simp only [Nat.add_succ, bondIter_succ, ← AddMonoidHom.comp_assoc,
      stageSeq_toLimit_comp_stageBond, ih]

private theorem stageSeq_eventually_zero (hd : IsDimensionGroup G)
    (posEnum : ℕ → G) (hpos : ∀ n, 0 ≤ posEnum n)
    (enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ))
    (henumZVec : ∀ r : ℕ, Function.Surjective (enumZVec r))
    (m : ℕ) (x : Fin (stageSeq hd posEnum hpos enumZVec m).rank → ℤ)
    (hx : (stageSeq hd posEnum hpos enumZVec m).toLimit x = 0) :
    ∃ k, bondIter (stageBond hd posEnum hpos enumZVec) m k x = 0 := by
  let S := stageSeq hd posEnum hpos enumZVec
  obtain ⟨j, rfl⟩ := henumZVec (S m).rank x
  let d : ℕ := max m j - m
  have hmd : j < m + d + 1 := by omega
  let idx : Fin (m + d + 1) := ⟨m, Nat.lt_succ_of_le (Nat.le_add_right m d)⟩
  have hmem_cand : (S (m + d)).seqs idx j ∈ stageCandidates (S (m + d)) := by
    classical
    simp only [stageCandidates, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ,
      true_and, Finset.mem_image, Finset.mem_range]
    refine ⟨⟨idx, j, hmd, rfl⟩, ?_⟩
    rw [stageSeq_seqs]
    exact (DFunLike.congr_fun
      (stageSeq_toLimit_comp_bondIter hd posEnum hpos enumZVec m d) _).trans hx
  refine ⟨d + 1, ?_⟩
  rw [bondIter_succ, AddMonoidHom.comp_apply, ← stageSeq_seqs, stageBond_eq]
  exact (nextStage hd posEnum hpos enumZVec (m + d) (S (m + d))).bond_eq_zero _ hmem_cand

/-- Every countable dimension group admits a `SimplicialPresentation`. -/
theorem IsDimensionGroup.nonempty_simplicialPresentation (hd : IsDimensionGroup G)
    [Countable G] : Nonempty (SimplicialPresentation G) := by
  classical
  let enumG : ℕ → G := Classical.choose (exists_surjective_nat G)
  have henumG : Function.Surjective enumG := Classical.choose_spec (exists_surjective_nat G)
  let posEnum : ℕ → G := fun n => if 0 ≤ enumG n then enumG n else 0
  have hpos : ∀ n, 0 ≤ posEnum n := fun n => by
    dsimp only [posEnum]; split_ifs with h <;> [exact h; exact le_rfl]
  let enumZVec : ∀ r : ℕ, ℕ → (Fin r → ℤ) := fun r =>
    Classical.choose (exists_surjective_nat (Fin r → ℤ))
  have henumZVec : ∀ r : ℕ, Function.Surjective (enumZVec r) := fun r =>
    Classical.choose_spec (exists_surjective_nat (Fin r → ℤ))
  let S := stageSeq hd posEnum hpos enumZVec
  let step := fun n => nextStage hd posEnum hpos enumZVec n (S n)
  have hexhausts_pos : ∀ g : G, 0 ≤ g → ∃ n x, 0 ≤ x ∧ (S n).toLimit x = g := by
    intro g hg
    obtain ⟨n, rfl⟩ := henumG g
    obtain ⟨x, hx0, hxg⟩ := (step n).exists_nonneg_toLimit_eq
    exact ⟨n + 1, x, hx0, hxg.trans (ite_eq_left hg)⟩
  have hpush : ∀ {m N : ℕ}, m ≤ N → ∀ {v : G}, (∃ x, (S m).toLimit x = v) →
      ∃ y, (S N).toLimit y = v := by
    rintro m N hmN v ⟨x, rfl⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmN
    exact ⟨bondIter (stageBond hd posEnum hpos enumZVec) m k x,
      DFunLike.congr_fun (stageSeq_toLimit_comp_bondIter hd posEnum hpos enumZVec m k) x⟩
  have hexhausts : ∀ g : G, ∃ n x, (S n).toLimit x = g := by
    intro g
    obtain ⟨u, hu0, hgu⟩ := hd.isDirected.directed 0 g
    obtain ⟨n₁, x₁, _, hx₁⟩ := hexhausts_pos u hu0
    obtain ⟨n₂, x₂, _, hx₂⟩ := hexhausts_pos (u - g) (sub_nonneg.mpr hgu)
    obtain ⟨y₁, hy₁⟩ := hpush (le_max_left n₁ n₂) ⟨x₁, hx₁⟩
    obtain ⟨y₂, hy₂⟩ := hpush (le_max_right n₁ n₂) ⟨x₂, hx₂⟩
    exact ⟨max n₁ n₂, y₁ - y₂, by rw [map_sub, hy₁, hy₂, sub_sub_cancel]⟩
  exact ⟨{
    rank := fun n => (S n).rank
    bond := stageBond hd posEnum hpos enumZVec
    bond_mono := fun n => (step n).bond_mono
    toLimit := fun n => (S n).toLimit
    toLimit_mono := fun n => (S n).toLimit_mono
    toLimit_comp_bond := fun n => (step n).toLimit_comp_bond
    exhausts := hexhausts
    exhausts_pos := hexhausts_pos
    eventually_zero := stageSeq_eventually_zero hd posEnum hpos enumZVec henumZVec }⟩

end InductiveConstruction

/-- The Effros–Handelman–Shen theorem in its countable form (Goodearl–Wehrung,
*Representations of distributive semilattices in ideal lattices of various algebraic
structures*, Theorem 3.3, citing Effros–Handelman–Shen, Theorem 2.2): a partially ordered
abelian group is a countable dimension group if and only if it is the sequential positive
inductive limit of simplicial groups. The limit side forces countability, so the statement
carries no separate hypothesis. -/
theorem effros_handelman_shen (G : Type*) [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] :
    (IsDimensionGroup G ∧ Countable G) ↔ Nonempty (SimplicialPresentation G) :=
  ⟨fun ⟨hd, _⟩ => hd.nonempty_simplicialPresentation,
   fun ⟨P⟩ => ⟨P.isDimensionGroup, P.countable⟩⟩

end TauCeti
