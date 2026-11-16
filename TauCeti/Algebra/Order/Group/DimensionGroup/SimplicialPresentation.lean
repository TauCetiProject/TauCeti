/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Group.DimensionGroup.Basic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fintype.Fin

/-!
# Simplicial presentations of ordered abelian groups

A *simplicial presentation* of a partially ordered abelian group `G` exhibits `G` as the
sequential positive inductive limit of the simplicial groups `(Fin (rank n) → ℤ)` along positive
(monotone) bonding homomorphisms, not required to be injective. Compatible positive maps into `G`
exhaust `G` and its positive cone, and their kernels coincide with the eventual kernels of the
bonding maps.

This file defines iterated bonding maps (`TauCeti.bondIter`), `TauCeti.SimplicialPresentation`,
stage-to-stage transition maps (`TauCeti.SimplicialPresentation.transition`), and proves the
limit direction of the Effros–Handelman–Shen theorem: every group admitting a simplicial
presentation is a countable dimension group.

## Main definitions

* `TauCeti.bondIter`: the `k`-step composite bonding homomorphism from stage `n` to stage `n + k`.
* `TauCeti.SimplicialPresentation G`: a sequential positive inductive-limit presentation of `G` by
  simplicial groups `Fin (rank n) → ℤ`.
* `TauCeti.SimplicialPresentation.transition`: the composite bonding map from stage `n` to any
  later stage `m ≥ n`.

## Main results

* `TauCeti.SimplicialPresentation.countable`: every group with a simplicial presentation is
  countable.
* `TauCeti.SimplicialPresentation.isDirectedOrder`,
  `TauCeti.SimplicialPresentation.isUnperforated`,
  `TauCeti.SimplicialPresentation.hasRieszInterpolation`,
  `TauCeti.SimplicialPresentation.isDimensionGroup`: every group with a simplicial presentation is
  a dimension group.

## References

* E. G. Effros, D. E. Handelman and C.-L. Shen, *Dimension groups and their affine
  representations*, American Journal of Mathematics 102 (1980), 385–407, Theorem 2.2.
* K. R. Goodearl and F. Wehrung, *Representations of distributive semilattices in ideal lattices of
  various algebraic structures*, Algebra Universalis 45 (2001), 71–102, §3, Theorem 3.3.
* M. Rørdam, *Classification of nuclear C⋆-algebras*, Encyclopaedia of Mathematical Sciences
  126, Springer, 2002, §1.4, Theorem 1.4.4.
-/

public section

namespace TauCeti

section BondIter

variable {rank : ℕ → ℕ}
  (bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ))

/-- The composite of the bonding maps of a sequential system of simplicial groups from stage `n`
to stage `n + k`. -/
def bondIter (n : ℕ) : ∀ k : ℕ, (Fin (rank n) → ℤ) →+ (Fin (rank (n + k)) → ℤ)
  | 0 => AddMonoidHom.id _
  | k + 1 => (bond (n + k)).comp (bondIter n k)

@[simp]
theorem bondIter_zero (n : ℕ) : bondIter bond n 0 = AddMonoidHom.id _ :=
  (rfl)

@[simp]
theorem bondIter_succ (n k : ℕ) :
    bondIter bond n (k + 1) = (bond (n + k)).comp (bondIter bond n k) :=
  (rfl)

theorem bondIter_succ_apply (n k : ℕ) (x : Fin (rank n) → ℤ) :
    bondIter bond n (k + 1) x = bond (n + k) (bondIter bond n k x) :=
  (rfl)

theorem bondIter_one (n : ℕ) : bondIter bond n 1 = bond n := by
  simp

/-- The iterated bonding map of monotone bonding maps is monotone. -/
theorem bondIter_mono {bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ)}
    (hmono : ∀ n, Monotone (bond n)) (n k : ℕ) : Monotone (bondIter bond n k) := by
  induction k with
  | zero => exact monotone_id
  | succ k ih => exact (hmono (n + k)).comp ih

end BondIter

/-- A presentation of a partially ordered abelian group `G` as the sequential positive inductive
limit of simplicial groups `(Fin (rank n) → ℤ)`: positive bonding maps (not required to be
injective), compatible positive maps into `G` whose images exhaust `G` and whose images of the
positive cones exhaust `G⁺`, and whose kernels are the eventual kernels of the system. -/
structure SimplicialPresentation (G : Type*) [AddCommGroup G] [PartialOrder G] where
  /-- The rank of the simplicial group at stage `n`. -/
  rank : ℕ → ℕ
  /-- The bonding homomorphism from stage `n` to stage `n + 1`. -/
  bond : ∀ n, (Fin (rank n) → ℤ) →+ (Fin (rank (n + 1)) → ℤ)
  /-- Each bonding map is positive (monotone). -/
  bond_mono : ∀ n, Monotone (bond n)
  /-- The compatible homomorphism from stage `n` to `G`. -/
  toLimit : ∀ n, (Fin (rank n) → ℤ) →+ G
  /-- Each stage-to-limit map is positive (monotone). -/
  toLimit_mono : ∀ n, Monotone (toLimit n)
  /-- Compatibility of `toLimit` with the bonding maps. -/
  toLimit_comp_bond : ∀ n, (toLimit (n + 1)).comp (bond n) = toLimit n
  /-- Every element of `G` comes from some stage. -/
  exhausts : ∀ g : G, ∃ n x, toLimit n x = g
  /-- Every nonnegative element of `G` comes from a nonnegative element of some stage. -/
  exhausts_pos : ∀ g : G, 0 ≤ g → ∃ n x, 0 ≤ x ∧ toLimit n x = g
  /-- Every element in the kernel of `toLimit n` maps to `0` after finitely many bonding steps. -/
  eventually_zero : ∀ n x, toLimit n x = 0 → ∃ k, bondIter bond n k x = 0

namespace SimplicialPresentation

section Basic

variable {G : Type*} [AddCommGroup G] [PartialOrder G]

/-- Each iterated bonding map in a simplicial presentation is monotone. -/
theorem bondIter_mono (P : SimplicialPresentation G) (n k : ℕ) :
    Monotone (bondIter P.bond n k) :=
  TauCeti.bondIter_mono P.bond_mono n k

@[simp]
theorem toLimit_bond (P : SimplicialPresentation G) (n : ℕ) (x : Fin (P.rank n) → ℤ) :
    P.toLimit (n + 1) (P.bond n x) = P.toLimit n x :=
  DFunLike.congr_fun (P.toLimit_comp_bond n) x

@[simp]
theorem toLimit_comp_bondIter (P : SimplicialPresentation G) (n k : ℕ) :
    (P.toLimit (n + k)).comp (bondIter P.bond n k) = P.toLimit n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [bondIter_succ, ← AddMonoidHom.comp_assoc]
    have hcomp : (P.toLimit (n + (k + 1))).comp (P.bond (n + k)) = P.toLimit (n + k) :=
      P.toLimit_comp_bond (n + k)
    rw [hcomp, ih]

@[simp]
theorem toLimit_bondIter (P : SimplicialPresentation G) (n k : ℕ) (x : Fin (P.rank n) → ℤ) :
    P.toLimit (n + k) (bondIter P.bond n k x) = P.toLimit n x :=
  DFunLike.congr_fun (P.toLimit_comp_bondIter n k) x

/-- The composite bonding homomorphism from stage `n` to any later stage `m ≥ n`. -/
def transition (P : SimplicialPresentation G) {n : ℕ} :
    ∀ {m : ℕ}, n ≤ m → (Fin (P.rank n) → ℤ) →+ (Fin (P.rank m) → ℤ)
  | 0, h => (Nat.le_zero.mp h).symm ▸ AddMonoidHom.id _
  | m + 1, h =>
    if hEq : n = m + 1 then
      hEq ▸ AddMonoidHom.id _
    else
      (P.bond m).comp (transition P (Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne h hEq)))

@[simp]
theorem transition_refl (P : SimplicialPresentation G) (n : ℕ) :
    P.transition (le_refl n) = AddMonoidHom.id _ := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [transition, dite_eq_left rfl]

theorem transition_step (P : SimplicialPresentation G) {n m : ℕ} (h : n ≤ m) :
    P.transition (Nat.le_succ_of_le h) = (P.bond m).comp (P.transition h) := by
  rw [transition, dite_eq_right (Nat.ne_of_lt (Nat.lt_succ_of_le h))]

theorem transition_step_apply (P : SimplicialPresentation G) {n m : ℕ} (h : n ≤ m)
    (x : Fin (P.rank n) → ℤ) :
    P.transition (Nat.le_succ_of_le h) x = P.bond m (P.transition h x) :=
  DFunLike.congr_fun (P.transition_step h) x

@[simp]
theorem transition_succ (P : SimplicialPresentation G) (n : ℕ) :
    P.transition (Nat.le_succ n) = P.bond n := by
  rw [P.transition_step (le_refl n), P.transition_refl, AddMonoidHom.comp_id]

theorem transition_comp (P : SimplicialPresentation G) {n m l : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ l) :
    (P.transition h₂).comp (P.transition h₁) = P.transition (h₁.trans h₂) := by
  induction l, h₂ using Nat.le_induction with
  | base => simp
  | succ l hml ih =>
    rw [P.transition_step hml, P.transition_step (h₁.trans hml), AddMonoidHom.comp_assoc, ih]

@[simp]
theorem transition_transition (P : SimplicialPresentation G) {n m l : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ l)
    (x : Fin (P.rank n) → ℤ) :
    P.transition h₂ (P.transition h₁ x) = P.transition (h₁.trans h₂) x :=
  DFunLike.congr_fun (P.transition_comp h₁ h₂) x

/-- On stages `n ≤ n + k`, `P.transition` agrees with `bondIter P.bond n k`. -/
theorem transition_add (P : SimplicialPresentation G) (n k : ℕ) :
    P.transition (Nat.le_add_right n k) = bondIter P.bond n k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [P.transition_step (Nat.le_add_right n k), ih, bondIter_succ]

/-- Every transition map is monotone. -/
theorem transition_mono (P : SimplicialPresentation G) {n m : ℕ} (h : n ≤ m) :
    Monotone (P.transition h) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [P.transition_refl]
    exact monotone_id
  | succ m hnm ih =>
    rw [P.transition_step hnm]
    exact (P.bond_mono m).comp ih

@[simp]
theorem toLimit_comp_transition (P : SimplicialPresentation G) {n m : ℕ} (h : n ≤ m) :
    (P.toLimit m).comp (P.transition h) = P.toLimit n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    rw [P.transition_step hnm, ← AddMonoidHom.comp_assoc, P.toLimit_comp_bond, ih]

@[simp]
theorem toLimit_transition (P : SimplicialPresentation G) {n m : ℕ} (h : n ≤ m)
    (x : Fin (P.rank n) → ℤ) :
    P.toLimit m (P.transition h x) = P.toLimit n x :=
  DFunLike.congr_fun (P.toLimit_comp_transition h) x

/-- An element in the kernel of `P.toLimit n` vanishes at some later stage. -/
theorem exists_transition_eq_zero (P : SimplicialPresentation G) {n : ℕ} {x : Fin (P.rank n) → ℤ}
    (hx : P.toLimit n x = 0) :
    ∃ (m : ℕ) (h : n ≤ m), P.transition h x = 0 := by
  obtain ⟨k, hk⟩ := P.eventually_zero n x hx
  exact ⟨n + k, Nat.le_add_right n k, by rwa [P.transition_add]⟩

/-- Two elements from possibly different stages with equal images in `G` become equal at a common
later stage. -/
theorem exists_transition_eq (P : SimplicialPresentation G) {n₁ n₂ : ℕ}
    {x₁ : Fin (P.rank n₁) → ℤ} {x₂ : Fin (P.rank n₂) → ℤ}
    (h : P.toLimit n₁ x₁ = P.toLimit n₂ x₂) :
    ∃ (m : ℕ) (h₁ : n₁ ≤ m) (h₂ : n₂ ≤ m), P.transition h₁ x₁ = P.transition h₂ x₂ := by
  let N := max n₁ n₂
  have h1 : n₁ ≤ N := le_max_left n₁ n₂
  have h2 : n₂ ≤ N := le_max_right n₁ n₂
  have h0 : P.toLimit N (P.transition h1 x₁ - P.transition h2 x₂) = 0 := by
    simp [map_sub, h]
  obtain ⟨m, hNm, hm⟩ := P.exists_transition_eq_zero h0
  refine ⟨m, h1.trans hNm, h2.trans hNm, ?_⟩
  rw [map_sub, P.transition_transition, P.transition_transition, sub_eq_zero] at hm
  exact hm

/-- Any group admitting a simplicial presentation is countable. -/
theorem countable (P : SimplicialPresentation G) : Countable G := by
  have hsurj : Function.Surjective fun p : (n : ℕ) × (Fin (P.rank n) → ℤ) ↦ P.toLimit p.1 p.2 :=
    fun g ↦ by
      obtain ⟨n, x, rfl⟩ := P.exhausts g
      exact ⟨⟨n, x⟩, rfl⟩
  exact hsurj.countable

/-- Any group admitting a simplicial presentation is upward directed. -/
theorem isDirectedOrder (P : SimplicialPresentation G) : IsDirectedOrder G := by
  refine ⟨fun g₁ g₂ ↦ ?_⟩
  obtain ⟨n₁, x₁, rfl⟩ := P.exhausts g₁
  obtain ⟨n₂, x₂, rfl⟩ := P.exhausts g₂
  let N := max n₁ n₂
  let y₁ := P.transition (le_max_left n₁ n₂) x₁
  let y₂ := P.transition (le_max_right n₁ n₂) x₂
  refine ⟨P.toLimit N (y₁ ⊔ y₂), ?_, ?_⟩
  · simpa only [y₁, toLimit_transition] using P.toLimit_mono N (le_sup_left : y₁ ≤ y₁ ⊔ y₂)
  · simpa only [y₂, toLimit_transition] using P.toLimit_mono N (le_sup_right : y₂ ≤ y₁ ⊔ y₂)

/-- Any group admitting a simplicial presentation is unperforated. -/
theorem isUnperforated (P : SimplicialPresentation G) : IsUnperforated G := by
  rw [isUnperforated_iff]
  intro k hk g hg
  obtain ⟨n₁, x, rfl⟩ := P.exhausts g
  obtain ⟨n₂, y, hy, hyeq⟩ := P.exhausts_pos (k • P.toLimit n₁ x) hg
  have hEq : P.toLimit n₁ (k • x) = P.toLimit n₂ y := by
    rw [map_nsmul, hyeq]
  obtain ⟨m, h₁, h₂, hm⟩ := P.exists_transition_eq hEq
  rw [map_nsmul] at hm
  have hmy : 0 ≤ P.transition h₂ y := by
    simpa only [map_zero] using P.transition_mono h₂ hy
  have hmx : 0 ≤ P.transition h₁ x :=
    (IsUnperforated.pi fun _ ↦ IsUnperforated.of_linearOrder).nonneg_of_nsmul_nonneg hk
      (hm.symm ▸ hmy)
  simpa only [map_zero, toLimit_transition] using P.toLimit_mono m hmx

/-- The canonical rank-0 simplicial presentation of a subsingleton (in particular, zero) group. -/
def ofSubsingleton [Subsingleton G] : SimplicialPresentation G where
  rank _ := 0
  bond _ := 0
  bond_mono _ := monotone_const
  toLimit _ := 0
  toLimit_mono _ := monotone_const
  toLimit_comp_bond _ := by ext x; exact Subsingleton.elim _ _
  exhausts _ := ⟨0, 0, Subsingleton.elim _ _⟩
  exhausts_pos _ _ := ⟨0, 0, le_rfl, Subsingleton.elim _ _⟩
  eventually_zero _ _ _ := ⟨0, Subsingleton.elim _ _⟩

@[simp]
theorem ofSubsingleton_rank [Subsingleton G] (n : ℕ) :
    (ofSubsingleton (G := G)).rank n = 0 :=
  (rfl)

@[simp]
theorem ofSubsingleton_bond [Subsingleton G] (n : ℕ) :
    (ofSubsingleton (G := G)).bond n = 0 :=
  (rfl)

@[simp]
theorem ofSubsingleton_toLimit [Subsingleton G] (n : ℕ) :
    (ofSubsingleton (G := G)).toLimit n = 0 :=
  (rfl)

end Basic

section OrderedGroup

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- An inequality in `G` between images of elements from possibly different stages holds at a
common later stage. -/
theorem exists_transition_le (P : SimplicialPresentation G) {n₁ n₂ : ℕ}
    {x₁ : Fin (P.rank n₁) → ℤ} {x₂ : Fin (P.rank n₂) → ℤ}
    (h : P.toLimit n₁ x₁ ≤ P.toLimit n₂ x₂) :
    ∃ (m : ℕ) (h₁ : n₁ ≤ m) (h₂ : n₂ ≤ m), P.transition h₁ x₁ ≤ P.transition h₂ x₂ := by
  let N := max n₁ n₂
  have h1 : n₁ ≤ N := le_max_left n₁ n₂
  have h2 : n₂ ≤ N := le_max_right n₁ n₂
  obtain ⟨n', d, hd, hdeq⟩ := P.exhausts_pos (P.toLimit n₂ x₂ - P.toLimit n₁ x₁) (sub_nonneg.2 h)
  have hEq : P.toLimit N (P.transition h2 x₂ - P.transition h1 x₁) = P.toLimit n' d := by
    simp [map_sub, hdeq]
  obtain ⟨m, hNm, hn'm, hm⟩ := P.exists_transition_eq hEq
  rw [map_sub, P.transition_transition, P.transition_transition] at hm
  refine ⟨m, h1.trans hNm, h2.trans hNm, sub_nonneg.1 ?_⟩
  rw [hm]
  simpa only [map_zero] using P.transition_mono hn'm hd

/-- Any ordered abelian group admitting a simplicial presentation has Riesz interpolation. -/
theorem hasRieszInterpolation (P : SimplicialPresentation G) : HasRieszInterpolation G := by
  rw [hasRieszInterpolation_iff]
  intro a₁ a₂ b₁ b₂ h₁₁ h₁₂ h₂₁ h₂₂
  obtain ⟨na₁, xa₁, rfl⟩ := P.exhausts a₁
  obtain ⟨na₂, xa₂, rfl⟩ := P.exhausts a₂
  obtain ⟨nb₁, xb₁, rfl⟩ := P.exhausts b₁
  obtain ⟨nb₂, xb₂, rfl⟩ := P.exhausts b₂
  obtain ⟨m₁₁, ha₁₁, hb₁₁, l₁₁⟩ := P.exists_transition_le h₁₁
  obtain ⟨m₁₂, ha₁₂, hb₁₂, l₁₂⟩ := P.exists_transition_le h₁₂
  obtain ⟨m₂₁, ha₂₁, hb₂₁, l₂₁⟩ := P.exists_transition_le h₂₁
  obtain ⟨m₂₂, ha₂₂, hb₂₂, l₂₂⟩ := P.exists_transition_le h₂₂
  let M := max (max m₁₁ m₁₂) (max m₂₁ m₂₂)
  have h₁₁M : m₁₁ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have h₁₂M : m₁₂ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have h₂₁M : m₂₁ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have h₂₂M : m₂₂ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  let za₁ := P.transition (ha₁₁.trans h₁₁M) xa₁
  let za₂ := P.transition (ha₂₁.trans h₂₁M) xa₂
  let zb₁ := P.transition (hb₁₁.trans h₁₁M) xb₁
  let zb₂ := P.transition (hb₁₂.trans h₁₂M) xb₂
  have le₁₁ : za₁ ≤ zb₁ := by
    simpa only [za₁, zb₁, transition_transition] using P.transition_mono h₁₁M l₁₁
  have le₁₂ : za₁ ≤ zb₂ := by
    simpa only [za₁, zb₂, transition_transition] using P.transition_mono h₁₂M l₁₂
  have le₂₁ : za₂ ≤ zb₁ := by
    simpa only [za₂, zb₁, transition_transition] using P.transition_mono h₂₁M l₂₁
  have le₂₂ : za₂ ≤ zb₂ := by
    simpa only [za₂, zb₂, transition_transition] using P.transition_mono h₂₂M l₂₂
  refine ⟨P.toLimit M (za₁ ⊔ za₂), ?_, ?_, ?_, ?_⟩
  · simpa only [za₁, toLimit_transition] using P.toLimit_mono M (le_sup_left : za₁ ≤ za₁ ⊔ za₂)
  · simpa only [za₂, toLimit_transition] using P.toLimit_mono M (le_sup_right : za₂ ≤ za₁ ⊔ za₂)
  · simpa only [zb₁, toLimit_transition] using P.toLimit_mono M (sup_le le₁₁ le₂₁)
  · simpa only [zb₂, toLimit_transition] using P.toLimit_mono M (sup_le le₁₂ le₂₂)

/-- Every ordered abelian group admitting a simplicial presentation is a dimension group. -/
theorem isDimensionGroup (P : SimplicialPresentation G) : IsDimensionGroup G where
  isDirectedOrder := P.isDirectedOrder
  isUnperforated := P.isUnperforated
  hasRieszInterpolation := P.hasRieszInterpolation

end OrderedGroup

end SimplicialPresentation

end TauCeti
