/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Basic.Countable.Defs
public import TauCeti.Algebra.Order.Group.DimensionGroup.Basic

import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Basic.Countable.Basic

/-!
# Sequential simplicial inductive presentations of dimension groups

A sequential positive inductive presentation of a partially ordered abelian group `G` expresses `G`
as the direct limit of a sequence of simplicial groups `(ℤ^{rₙ}, ℕ^{rₙ})` with monotone bonding
homomorphisms.

This file defines iterated bonding homomorphisms `bondIter` and the presentation structure
`SimplicialPresentation G`, develops its elimination and universal-property API (`hom_ext`, `lift`,
`existsUnique_lift`, `monotone_lift_iff`, and eventual kernel/order characterizations), and proves
the converse direction of the Effros–Handelman–Shen theorem: every partially ordered abelian group
admitting a `SimplicialPresentation` is a countable dimension group.

## Main definitions

* `TauCeti.bondIter` : Composite bonding homomorphism from stage `n` to stage `n + k` in a
  sequential system of simplicial groups.
* `TauCeti.SimplicialPresentation G` : Presentation of a partially ordered abelian group `G` as a
  sequential positive inductive limit of simplicial groups `Fin (rank n) → ℤ`.
* `TauCeti.SimplicialPresentation.lift` : Homomorphism `G →+ H` induced by a compatible family of
  stage homomorphisms `(Fin (P.rank n) → ℤ) →+ H`.

## Main results

* `TauCeti.SimplicialPresentation.existsUnique_lift` and
  `TauCeti.SimplicialPresentation.monotone_lift_iff` : Universal property of a
  `SimplicialPresentation` as a sequential positive inductive limit.
* `TauCeti.SimplicialPresentation.isDimensionGroup` and
  `TauCeti.SimplicialPresentation.countable` : Any partially ordered abelian group admitting a
  `SimplicialPresentation` is a countable dimension group.

## References

* E. G. Effros, D. E. Handelman, C.-L. Shen, *Dimension groups and their affine representations*,
  Amer. J. Math. **102** (1980), 385–407, Theorem 2.2.
* K. R. Goodearl, F. Wehrung, *Representations of distributive semilattices in ideal lattices of
  various algebraic structures*, Algebra Universalis **45** (2001), 71–102 (arXiv:math/0011083),
  Theorem 3.3.
* M. Rørdam, *Classification of Nuclear C*-Algebras*, Encyclopaedia Math. Sci. **126**,
  Springer, 2002, §1.4.
-/

public section

namespace TauCeti

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
structure SimplicialPresentation (G : Type*) [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] where
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

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]

/-- Applying `bond n` followed by `toLimit (n + 1)` recovers `toLimit n`. -/
@[simp]
theorem toLimit_bond_apply (P : SimplicialPresentation G) (n : ℕ) (x : Fin (P.rank n) → ℤ) :
    P.toLimit (n + 1) (P.bond n x) = P.toLimit n x :=
  DFunLike.congr_fun (P.toLimit_comp_bond n) x

/-- Every composite bonding map of a `SimplicialPresentation` is monotone. -/
theorem bondIter_mono (P : SimplicialPresentation G) (n k : ℕ) :
    Monotone (bondIter P.bond n k) :=
  TauCeti.bondIter_mono P.bond_mono n k

/-- An inequality between `k`-step iterates of `P.bond` persists at every stage `K ≥ k`. -/
theorem bondIter_le_of_le (P : SimplicialPresentation G) (n : ℕ) {k K : ℕ} (hkK : k ≤ K)
    {x y : Fin (P.rank n) → ℤ} (hxy : bondIter P.bond n k x ≤ bondIter P.bond n k y) :
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
theorem exists_toLimit_of_le (P : SimplicialPresentation G) {m n : ℕ} (h : m ≤ n) {g : G}
    (hg : ∃ x, P.toLimit m x = g) : ∃ x, P.toLimit n x = g := by
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨bondIter P.bond m d x, P.toLimit_bondIter_apply m d x⟩

/-- Any element represented nonnegatively at stage `m` is also represented nonnegatively at
every stage `n ≥ m`. -/
theorem exists_nonneg_toLimit_of_le (P : SimplicialPresentation G) {m n : ℕ} (h : m ≤ n) {g : G}
    (hg : ∃ x, 0 ≤ x ∧ P.toLimit m x = g) : ∃ x, 0 ≤ x ∧ P.toLimit n x = g := by
  obtain ⟨x, hx0, rfl⟩ := hg
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨bondIter P.bond m d x, by simpa using P.bondIter_mono m d hx0,
    P.toLimit_bondIter_apply m d x⟩

/-- Every partially ordered abelian group admitting a `SimplicialPresentation` is countable. -/
theorem countable (P : SimplicialPresentation G) : Countable G := by
  have : ∀ n, Finite (Fin (P.rank n)) := fun _ => .intro (Equiv.refl _)
  let f : (Σ n : ℕ, Fin (P.rank n) → ℤ) → G := fun p => P.toLimit p.1 p.2
  have hf : Function.Surjective f := fun g =>
    let ⟨n, x, hx⟩ := P.exhausts g
    ⟨⟨n, x⟩, hx⟩
  exact hf.countable

/-- Every partially ordered abelian group admitting a `SimplicialPresentation` is directed. -/
theorem isDirectedOrder (P : SimplicialPresentation G) : IsDirectedOrder G := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨n₁, x₁, hx₁⟩ := P.exhausts a
  obtain ⟨n₂, x₂, hx₂⟩ := P.exhausts b
  obtain ⟨y₁, rfl⟩ := P.exists_toLimit_of_le (le_max_left n₁ n₂) ⟨x₁, hx₁⟩
  obtain ⟨y₂, rfl⟩ := P.exists_toLimit_of_le (le_max_right n₁ n₂) ⟨x₂, hx₂⟩
  exact ⟨P.toLimit (max n₁ n₂) (y₁ ⊔ y₂),
    P.toLimit_mono _ le_sup_left, P.toLimit_mono _ le_sup_right⟩

/-- Every partially ordered abelian group admitting a `SimplicialPresentation` is unperforated. -/
theorem isUnperforated (P : SimplicialPresentation G) : IsUnperforated G := by
  rw [isUnperforated_iff]
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
    (IsUnperforated.pi fun _ => .of_linearOrder).nonneg_of_nsmul_nonneg hm hmk
  rw [← hx, ← P.toLimit_bondIter_apply N k x]
  simpa using P.toLimit_mono (N + k) hx0

/-- Order lifting along a `SimplicialPresentation`: if `P.toLimit n x ≤ P.toLimit n y`, then
`bondIter P.bond n k x ≤ bondIter P.bond n k y` at some later stage `n + k`. -/
theorem exists_bondIter_le (P : SimplicialPresentation G) (n : ℕ) {x y : Fin (P.rank n) → ℤ}
    (hxy : P.toLimit n x ≤ P.toLimit n y) :
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

/-- Every partially ordered abelian group admitting a `SimplicialPresentation` satisfies Riesz
interpolation. -/
theorem hasRieszInterpolation (P : SimplicialPresentation G) : HasRieszInterpolation G := by
  rw [hasRieszInterpolation_iff]
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
    (HasRieszInterpolation.pi fun _ : Fin (P.rank (N + K)) => .of_semilatticeSup).exists_ge_ge_le_le
      (P.bondIter_le_of_le N (K := K) (le_max_of_le_left (le_max_left k₁₁ k₁₂)) hk₁₁)
      (P.bondIter_le_of_le N (K := K) (le_max_of_le_left (le_max_right k₁₁ k₁₂)) hk₁₂)
      (P.bondIter_le_of_le N (K := K) (le_max_of_le_right (le_max_left k₂₁ k₂₂)) hk₂₁)
      (P.bondIter_le_of_le N (K := K) (le_max_of_le_right (le_max_right k₂₁ k₂₂)) hk₂₂)
  exact ⟨P.toLimit (N + K) z,
    (P.toLimit_bondIter_apply N K x₁).symm.trans_le (P.toLimit_mono (N + K) hz₁),
    (P.toLimit_bondIter_apply N K x₂).symm.trans_le (P.toLimit_mono (N + K) hz₂),
    (P.toLimit_mono (N + K) hz₃).trans_eq (P.toLimit_bondIter_apply N K y₁),
    (P.toLimit_mono (N + K) hz₄).trans_eq (P.toLimit_bondIter_apply N K y₂)⟩

/-- Every partially ordered abelian group admitting a `SimplicialPresentation` is a dimension
group. -/
theorem isDimensionGroup (P : SimplicialPresentation G) : IsDimensionGroup G :=
  ⟨P.isDirectedOrder, P.isUnperforated, P.hasRieszInterpolation⟩

/-- An element of stage `n` maps to `0` in `G` if and only if it maps to `0` at some later stage
`n + k`. -/
theorem toLimit_eq_zero_iff (P : SimplicialPresentation G) (n : ℕ) (x : Fin (P.rank n) → ℤ) :
    P.toLimit n x = 0 ↔ ∃ k : ℕ, bondIter P.bond n k x = 0 :=
  ⟨P.eventually_zero n x, fun ⟨k, hk⟩ => by rw [← P.toLimit_bondIter_apply n k x, hk, map_zero]⟩

/-- Two elements of stage `n` have the same image in `G` if and only if they become equal at some
later stage `n + k`. -/
theorem toLimit_eq_iff (P : SimplicialPresentation G) (n : ℕ) (x y : Fin (P.rank n) → ℤ) :
    P.toLimit n x = P.toLimit n y ↔ ∃ k : ℕ, bondIter P.bond n k x = bondIter P.bond n k y := by
  refine ⟨fun h => ?_, fun ⟨k, hk⟩ => by
    rw [← P.toLimit_bondIter_apply n k x, ← P.toLimit_bondIter_apply n k y, hk]⟩
  obtain ⟨k, hk⟩ := P.eventually_zero n (x - y) (by rw [map_sub, h, sub_self])
  exact ⟨k, sub_eq_zero.mp (by rwa [← map_sub])⟩

/-- Two elements of stage `n` compare in `G` if and only if they compare at some later stage
`n + k`. -/
theorem toLimit_le_iff (P : SimplicialPresentation G) (n : ℕ) (x y : Fin (P.rank n) → ℤ) :
    P.toLimit n x ≤ P.toLimit n y ↔ ∃ k : ℕ, bondIter P.bond n k x ≤ bondIter P.bond n k y :=
  ⟨P.exists_bondIter_le n, fun ⟨k, hk⟩ => by
    simpa only [P.toLimit_bondIter_apply] using P.toLimit_mono (n + k) hk⟩

/-- Two additive homomorphisms out of `G` agree if they agree after composing with every stage
map `P.toLimit n`. -/
theorem hom_ext (P : SimplicialPresentation G) {H : Type*} [AddZero H]
    {φ ψ : G →+ H} (h : ∀ n, φ.comp (P.toLimit n) = ψ.comp (P.toLimit n)) :
    φ = ψ := by
  refine DFunLike.ext _ _ fun g => ?_
  obtain ⟨n, x, rfl⟩ := P.exhausts g
  exact DFunLike.congr_fun (h n) x

private theorem family_eq_of_toLimit_eq (P : SimplicialPresentation G) {H : Type*} [AddZero H]
    (f : ∀ n, (Fin (P.rank n) → ℤ) →+ H) (hf : ∀ n, (f (n + 1)).comp (P.bond n) = f n)
    {n₁ n₂ : ℕ} {x₁ : Fin (P.rank n₁) → ℤ} {x₂ : Fin (P.rank n₂) → ℤ}
    (h : P.toLimit n₁ x₁ = P.toLimit n₂ x₂) : f n₁ x₁ = f n₂ x₂ := by
  have hiter : ∀ (n k : ℕ) (x : Fin (P.rank n) → ℤ),
      f (n + k) (bondIter P.bond n k x) = f n x := by
    intro n k x
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [bondIter_succ, AddMonoidHom.comp_apply]
      exact (DFunLike.congr_fun (hf (n + k)) _).trans ih
  have hle : ∀ {a b : ℕ} {u : Fin (P.rank a) → ℤ} {v : Fin (P.rank b) → ℤ},
      a ≤ b → P.toLimit a u = P.toLimit b v → f a u = f b v := by
    intro a b u v hab huv
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    obtain ⟨k, hk⟩ := (P.toLimit_eq_iff (a + d) _ _).mp ((P.toLimit_bondIter_apply a d u).trans huv)
    calc f a u = f (a + d) (bondIter P.bond a d u) := (hiter a d u).symm
      _ = f (a + d + k) (bondIter P.bond (a + d) k (bondIter P.bond a d u)) := (hiter _ k _).symm
      _ = f (a + d + k) (bondIter P.bond (a + d) k v) := congrArg (f (a + d + k)) hk
      _ = f (a + d) v := hiter (a + d) k v
  rcases le_total n₁ n₂ with h₁₂ | h₂₁
  · exact hle h₁₂ h
  · exact (hle h₂₁ h.symm).symm

/-- The universal-property homomorphism `G →+ H` induced by a compatible family of homomorphisms
`f n : (Fin (P.rank n) → ℤ) →+ H` satisfying `(f (n + 1)).comp (P.bond n) = f n`. -/
noncomputable def lift (P : SimplicialPresentation G) {H : Type*} [AddZero H]
    (f : ∀ n, (Fin (P.rank n) → ℤ) →+ H) (hf : ∀ n, (f (n + 1)).comp (P.bond n) = f n) :
    G →+ H :=
  have heval : ∀ {n : ℕ} {x : Fin (P.rank n) → ℤ} {g : G}, P.toLimit n x = g →
      f (Classical.choose (P.exhausts g))
        (Classical.choose (Classical.choose_spec (P.exhausts g))) = f n x :=
    fun h => P.family_eq_of_toLimit_eq f hf
      ((Classical.choose_spec (Classical.choose_spec (P.exhausts _))).trans h.symm)
  { toFun := fun g =>
      f (Classical.choose (P.exhausts g))
        (Classical.choose (Classical.choose_spec (P.exhausts g)))
    map_zero' := by rw [heval (n := 0) (x := 0) (map_zero (P.toLimit 0)), map_zero]
    map_add' := fun g₁ g₂ => by
      obtain ⟨n₁, x₁, hx₁⟩ := P.exhausts g₁
      obtain ⟨n₂, x₂, hx₂⟩ := P.exhausts g₂
      obtain ⟨y₁, hy₁⟩ := P.exists_toLimit_of_le (le_max_left n₁ n₂) ⟨x₁, hx₁⟩
      obtain ⟨y₂, hy₂⟩ := P.exists_toLimit_of_le (le_max_right n₁ n₂) ⟨x₂, hx₂⟩
      have hadd : P.toLimit (max n₁ n₂) (y₁ + y₂) = g₁ + g₂ := by rw [map_add, hy₁, hy₂]
      rw [heval hadd, map_add, heval hy₁, heval hy₂] }

/-- Evaluating `P.lift f hf` on an element coming from stage `n` recovers `f n`. -/
@[simp]
theorem lift_toLimit (P : SimplicialPresentation G) {H : Type*} [AddZero H]
    (f : ∀ n, (Fin (P.rank n) → ℤ) →+ H) (hf : ∀ n, (f (n + 1)).comp (P.bond n) = f n)
    (n : ℕ) (x : Fin (P.rank n) → ℤ) : P.lift f hf (P.toLimit n x) = f n x :=
  P.family_eq_of_toLimit_eq f hf
    (Classical.choose_spec (Classical.choose_spec (P.exhausts (P.toLimit n x))))

/-- Composing `P.lift f hf` with `P.toLimit n` recovers `f n`. -/
@[simp]
theorem lift_comp_toLimit (P : SimplicialPresentation G) {H : Type*} [AddZero H]
    (f : ∀ n, (Fin (P.rank n) → ℤ) →+ H) (hf : ∀ n, (f (n + 1)).comp (P.bond n) = f n) (n : ℕ) :
    (P.lift f hf).comp (P.toLimit n) = f n :=
  DFunLike.ext _ _ fun x => P.lift_toLimit f hf n x

/-- Lifting the restrictions of a homomorphism `φ : G →+ H` to the stages recovers `φ`. -/
@[simp]
theorem lift_comp_toLimit_self (P : SimplicialPresentation G) {H : Type*} [AddZero H]
    (φ : G →+ H) :
    P.lift (fun n => φ.comp (P.toLimit n))
      (fun n => by rw [AddMonoidHom.comp_assoc, P.toLimit_comp_bond]) = φ :=
  P.hom_ext fun n => P.lift_comp_toLimit _ _ n

/-- Lifting the stage maps `P.toLimit` recovers the identity homomorphism on `G`. -/
@[simp]
theorem lift_toLimit_eq_id (P : SimplicialPresentation G) :
    P.lift P.toLimit P.toLimit_comp_bond = AddMonoidHom.id G :=
  P.hom_ext fun n => by simp

/-- Universal property of a `SimplicialPresentation`: every compatible family of additive
homomorphisms `f n : (Fin (P.rank n) → ℤ) →+ H` descends to a unique additive homomorphism
`G →+ H`. -/
theorem existsUnique_lift (P : SimplicialPresentation G) {H : Type*} [AddZero H]
    (f : ∀ n, (Fin (P.rank n) → ℤ) →+ H) (hf : ∀ n, (f (n + 1)).comp (P.bond n) = f n) :
    ∃! φ : G →+ H, ∀ n, φ.comp (P.toLimit n) = f n :=
  ⟨P.lift f hf, P.lift_comp_toLimit f hf, fun _ hφ =>
    P.hom_ext fun n => (hφ n).trans (P.lift_comp_toLimit f hf n).symm⟩

/-- If every stage map `f n` is monotone, then the induced homomorphism `P.lift f hf` is
monotone. -/
theorem lift_mono (P : SimplicialPresentation G) {H : Type*} [AddZero H] [Preorder H]
    (f : ∀ n, (Fin (P.rank n) → ℤ) →+ H) (hf : ∀ n, (f (n + 1)).comp (P.bond n) = f n)
    (hmono : ∀ n, Monotone (f n)) : Monotone (P.lift f hf) := by
  intro g₁ g₂ hle
  obtain ⟨n₁, x₁, hx₁⟩ := P.exhausts g₁
  obtain ⟨n₂, x₂, hx₂⟩ := P.exhausts g₂
  obtain ⟨y₁, rfl⟩ := P.exists_toLimit_of_le (le_max_left n₁ n₂) ⟨x₁, hx₁⟩
  obtain ⟨y₂, rfl⟩ := P.exists_toLimit_of_le (le_max_right n₁ n₂) ⟨x₂, hx₂⟩
  obtain ⟨k, hk⟩ := P.exists_bondIter_le (max n₁ n₂) hle
  rw [← P.toLimit_bondIter_apply _ k y₁, ← P.toLimit_bondIter_apply _ k y₂,
    P.lift_toLimit, P.lift_toLimit]
  exact hmono (max n₁ n₂ + k) hk

/-- The induced homomorphism `P.lift f hf` is monotone if and only if every stage map `f n` is
monotone. -/
theorem monotone_lift_iff (P : SimplicialPresentation G) {H : Type*} [AddZero H] [Preorder H]
    (f : ∀ n, (Fin (P.rank n) → ℤ) →+ H) (hf : ∀ n, (f (n + 1)).comp (P.bond n) = f n) :
    Monotone (P.lift f hf) ↔ ∀ n, Monotone (f n) :=
  ⟨fun h n _ _ hxy => by simpa only [P.lift_toLimit] using h (P.toLimit_mono n hxy),
    P.lift_mono f hf⟩

end SimplicialPresentation

end TauCeti
