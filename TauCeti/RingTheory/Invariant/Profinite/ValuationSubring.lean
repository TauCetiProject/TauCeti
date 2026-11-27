/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Invariant.Profinite.Frobenius
public import TauCeti.RingTheory.Valuation.LocalizationAtCenter

import TauCeti.RingTheory.Frobenius

/-!
# Frobenius elements at a valuation subring for profinite actions

Let `B` be a commutative ring with fraction field `L`, and let a group `G` act on `B` and `L`
compatibly. Let `A` be a valuation subring of `L` centred at a prime `Q` of `B`
(`ValuationSubring.IsCenteredAt A Q`: `A` contains `B` and `Q` is the set of elements of `B` that
are nonunits of `A`), and assume that the localization `B_Q` is a valuation ring. Tau Ceti's
`TauCeti/RingTheory/Valuation/LocalizationAtCenter.lean` shows that `A` is then `B_Q` realized in
`L`, that the stabilizers of `A` and `Q` in `G` agree, and that `g` raises elements of `B` to the
`q`-th power modulo `Q` exactly when it raises elements of `A` to the `q`-th power modulo the
nonunits of `A`.

This file transports the profinite Frobenius results of
`TauCeti/RingTheory/Invariant/Profinite/Frobenius.lean`, stated for the prime `Q`, to the
valuation subring `A`. In the language of valuation subrings, an element `σ` inducing
`x ↦ x ^ q` on the residue field of `A` is described by the two conditions
`σ ∈ MulAction.stabilizer G A` and `∀ x ∈ A, σ • x - x ^ q ∈ A.nonunits`, with no named predicate.
The first condition follows from the second (`ValuationSubring.IsCenteredAt.mem_stabilizer`), but
results state both, so that they can be quoted as they are used.

The typical setting is `B` the integral closure of a Dedekind domain `R` in an algebraic, possibly
infinite, Galois extension `L` of its fraction field `K`, and `G` a profinite group acting on `L`
over `K` with fixed field `K`, such as `Gal(L/K)`. Then every localization of `B` at a prime is a
valuation ring (Tau Ceti's `IsIntegralClosure.preValuationRing_atPrime`), and every valuation
subring of `L` containing `B` is centred at some prime of `B`.

For a continuous action of a profinite `G` on `L` with the discrete topology, with `B^G = R`
(`Algebra.IsInvariant R B G`):

* an element acting by `x ↦ x ^ q` modulo the nonunits of `A`, with `q = #(R ⧸ Q ∩ R)`, exists as
  soon as `R ⧸ Q ∩ R` is finite;
* such an element and the inertia group of `Q` topologically generate the stabilizer of `A`.

The continuity hypothesis is on `L`, not on `B`: the discrete topology on `B` used by the
prime-level results is introduced inside the proofs.

## Main results

* `ValuationSubring.IsCenteredAt.isArithFrobAt_iff_forall_smul_sub_pow_mem`: `σ` is an
  arithmetic Frobenius at `Q` (Mathlib's `IsArithFrobAt R σ Q`) exactly when it raises elements
  of `A` to the `#(R ⧸ Q ∩ R)`-th power modulo the nonunits of `A`.
* `ValuationSubring.IsCenteredAt.mem_inertia_iff`: the inertia group of `Q` consists of the `g`
  with `g • x - x` a nonunit of `A` for every `x ∈ A`.
* `ValuationSubring.IsCenteredAt.exists_forall_smul_sub_pow_mem_nonunits`: existence of a
  Frobenius element at `A` for a profinite action.
* `ValuationSubring.IsCenteredAt.topologicalClosure_zpowers_mul_inertia_eq_stabilizer` and
  `ValuationSubring.IsCenteredAt.topologicalClosure_zpowers_sup_inertia_eq_stabilizer`: a
  Frobenius element and the inertia group generate the stabilizer of `A`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9 and Chapter II, §9.
* The statements in the form "stabilizes `A` and acts by `x ↦ x ^ q` modulo the nonunits of `A`"
  are those of `New.IsFrob` in the riemann-hypothesis project
  (https://github.com/leanprover-community/riemann-hypothesis, file
  `src/Lib/ClassField/Places/LocalFields.lean` at commit
  e38782a68eb5f6ee793739847c703aa16080ef6c), where existence is proved through completions.
-/

public section

open MulAction Pointwise

/-- If a topological group `G` acts continuously on a field `L` with the discrete topology, and
compatibly on a ring `B` with fraction field `L`, then the action on `B` is continuous for the
discrete topology on `B`. -/
theorem IsFractionRing.continuousSMul_of_discreteTopology (B L : Type*) [CommRing B] [Field L]
    [Algebra B L] [IsFractionRing B L] (G : Type*) [Group G] [MulSemiringAction G B]
    [MulSemiringAction G L] [SMulDistribClass G B L] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace L] [DiscreteTopology L] [ContinuousSMul G L]
    [TopologicalSpace B] [DiscreteTopology B] :
    ContinuousSMul G B := by
  refine continuousSMul_iff_stabilizer_isOpen.mpr fun b ↦ ?_
  have : stabilizer G b = stabilizer G (algebraMap B L b) := by
    ext g
    simp only [mem_stabilizer_iff, ← algebraMap.smul', (IsFractionRing.injective B L).eq_iff]
  rw [this]
  exact stabilizer_isOpen G _

namespace ValuationSubring.IsCenteredAt

variable {B L : Type*} [CommRing B] [Field L] [Algebra B L] [IsFractionRing B L]
  {G : Type*} [Group G] [MulSemiringAction G B] [MulSemiringAction G L] [SMulDistribClass G B L]
  {A : ValuationSubring L} {Q : Ideal B} [Q.IsPrime] [PreValuationRing (Localization.AtPrime Q)]

/-! ### Comparison of the congruence conditions -/

/-- An element raising every element of `A` to the `q`-th power modulo the nonunits of `A`
stabilizes `A`. -/
theorem mem_stabilizer (h : A.IsCenteredAt Q) {g : G} {q : ℕ}
    (hg : ∀ x ∈ A, g • x - x ^ q ∈ A.nonunits) : g ∈ stabilizer G A := by
  rw [h.stabilizer_eq]
  exact Ideal.mem_stabilizer_of_forall_smul_sub_pow_mem (h.smul_sub_pow_mem_of_forall hg)

/-- **Arithmetic Frobenius elements at the centre of a valuation subring.** For a ring `R` below
`B` fixed by `G`, `σ` is an arithmetic Frobenius element at `Q` relative to `R` exactly when it
raises every element of `A` to the `#(R ⧸ Q ∩ R)`-th power modulo the nonunits of `A`. -/
theorem isArithFrobAt_iff_forall_smul_sub_pow_mem (h : A.IsCenteredAt Q) {R : Type*}
    [CommRing R] [Algebra R B] [SMulCommClass G R B] {σ : G} :
    IsArithFrobAt R σ Q ↔ ∀ x ∈ A, σ • x - x ^ Nat.card (R ⧸ Q.under R) ∈ A.nonunits :=
  h.forall_smul_sub_pow_mem_iff

/-- **The inertia group of the centre of a valuation subring.** The inertia group of `Q` in `G`
consists of the `g` such that `g • x - x` is a nonunit of `A` for every `x ∈ A`. -/
theorem mem_inertia_iff (h : A.IsCenteredAt Q) {g : G} :
    g ∈ Q.inertia G ↔ ∀ x ∈ A, g • x - x ∈ A.nonunits := by
  simpa using h.forall_smul_sub_pow_mem_iff (g := g) (q := 1)

/-! ### Profinite actions -/

variable [TopologicalSpace G] [TopologicalSpace L] [DiscreteTopology L] [ContinuousSMul G L]

variable [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
  {R : Type*} [CommRing R] [Algebra R B] [SMulCommClass G R B]

/-- **Frobenius elements exist at a valuation subring.** For a profinite group `G` acting
continuously on `L` with the discrete topology, with `B^G = R`, and a valuation subring `A`
centred at a prime `Q` of `B` with `R ⧸ Q ∩ R` finite, some `σ : G` stabilizes `A` and acts on `A`
by `x ↦ x ^ #(R ⧸ Q ∩ R)` modulo its nonunits. -/
theorem exists_forall_smul_sub_pow_mem_nonunits (h : A.IsCenteredAt Q)
    [Algebra.IsInvariant R B G] [Finite (R ⧸ Q.under R)] :
    ∃ σ : G, σ ∈ stabilizer G A ∧
      ∀ x ∈ A, σ • x - x ^ Nat.card (R ⧸ Q.under R) ∈ A.nonunits := by
  let _ : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have := IsFractionRing.continuousSMul_of_discreteTopology B L G
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant_of_profinite R G Q
  have hσ' := h.isArithFrobAt_iff_forall_smul_sub_pow_mem.mp hσ
  exact ⟨σ, h.mem_stabilizer hσ', hσ'⟩

/-- **A Frobenius element and inertia generate the stabilizer of a valuation subring**, as a
product of subsets: if `σ` acts on `A` by `x ↦ x ^ #(R ⧸ Q ∩ R)` modulo its nonunits, every
element of the stabilizer of `A` is `s * i` with `s` in the closure of the powers of `σ` and `i`
in the inertia group of `Q`, which `ValuationSubring.IsCenteredAt.mem_inertia_iff` describes on
`A`. No invariance hypothesis on `R ⊆ B` is needed. -/
theorem topologicalClosure_zpowers_mul_inertia_eq_stabilizer (h : A.IsCenteredAt Q) {σ : G}
    (hσ : ∀ x ∈ A, σ • x - x ^ Nat.card (R ⧸ Q.under R) ∈ A.nonunits) :
    ((Subgroup.zpowers σ).topologicalClosure : Set G) * Q.inertia G = stabilizer G A := by
  let _ : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have := IsFractionRing.continuousSMul_of_discreteTopology B L G
  rw [h.stabilizer_eq]
  exact Ideal.topologicalClosure_zpowers_mul_inertia_eq_stabilizer_of_isArithFrobAt Q
    (h.isArithFrobAt_iff_forall_smul_sub_pow_mem.mpr hσ)

/-- **A Frobenius element and inertia generate the stabilizer of a valuation subring**: if `σ`
acts on `A` by `x ↦ x ^ #(R ⧸ Q ∩ R)` modulo its nonunits, the stabilizer of `A` is generated by
the closure of `⟨σ⟩` and the inertia group of `Q`. -/
theorem topologicalClosure_zpowers_sup_inertia_eq_stabilizer (h : A.IsCenteredAt Q) {σ : G}
    (hσ : ∀ x ∈ A, σ • x - x ^ Nat.card (R ⧸ Q.under R) ∈ A.nonunits) :
    (Subgroup.zpowers σ).topologicalClosure ⊔ Q.inertia G = stabilizer G A := by
  let _ : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have := IsFractionRing.continuousSMul_of_discreteTopology B L G
  rw [h.stabilizer_eq]
  exact Ideal.topologicalClosure_zpowers_sup_inertia_eq_stabilizer_of_isArithFrobAt Q
    (h.isArithFrobAt_iff_forall_smul_sub_pow_mem.mpr hσ)

end ValuationSubring.IsCenteredAt
