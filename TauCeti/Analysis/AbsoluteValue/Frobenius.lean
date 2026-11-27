/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.ValuationSubring
public import TauCeti.RingTheory.Invariant.Profinite.ValuationSubring

/-!
# Frobenius elements at a nonarchimedean absolute value for profinite actions

Let `w` be a nonarchimedean absolute value on a field `L`, with valuation subring
`A_w = {x | w x ≤ 1}` (`AbsoluteValue.valuationSubring`), and let a group `G` act on `L` by ring
automorphisms. An element `σ : G` inducing `x ↦ x ^ q` on the residue field of `A_w` is described
by the hypothesis `∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1`, with no named predicate.

This file transports the profinite Frobenius results of
`TauCeti/RingTheory/Invariant/Profinite/ValuationSubring.lean` from valuation subrings to
absolute values. The bridge is a ring `B` with fraction field `L` on which `G` also acts, for
instance the integral closure of the ring of integers of a number field `K` in an algebraic
extension `L` of `K`. If `w ≤ 1` on `B` and `Q = {b ∈ B | w b < 1}`, then `A_w` is centred at `Q`
(`AbsoluteValue.isCenteredAt_valuationSubring`), and when the localization `B_Q` is a valuation
ring the conditions on `w` translate into conditions modulo `Q`:

* `σ` is an arithmetic Frobenius at `Q` (Mathlib's `IsArithFrobAt R σ Q`) exactly when it acts on
  `A_w` by `x ↦ x ^ #(R ⧸ Q ∩ R)` modulo `w < 1`;
* the inertia group of `Q` consists of the `g` with `w (g • x - x) < 1` whenever `w x ≤ 1`.

For a compact totally disconnected group `G` acting continuously on `L` with the discrete topology,
with `B^G = R` and `w ≤ 1` on `R` (hence on `B`, which is integral over `R`, by Tau Ceti's
`IsNonarchimedean.apply_le_one_of_isIntegral`), this gives:

* an element of the stabilizer of `A_w` acting on `A_w` by `x ↦ x ^ #(R ⧸ Q ∩ R)` modulo `w < 1`
  exists when `R ⧸ Q ∩ R` is finite;
* any such element and the inertia group generate the stabilizer of `A_w` topologically.

The results are stated with the stabilizer of the valuation subring `A_w`. For places
(`ℚ`-normalised absolute values) this is also the stabilizer of `w`; that comparison is not proved
here.

## Main results

* `AbsoluteValue.isCenteredAt_valuationSubring`: `A_w` is centred at `{b | w b < 1}`.
* `AbsoluteValue.isArithFrobAt_iff_forall_apply_smul_sub_pow_lt_one` and
  `AbsoluteValue.mem_inertia_iff_forall_apply_smul_sub_lt_one`: the Frobenius and inertia
  conditions at `w` are those at its centre.
* `AbsoluteValue.exists_mem_stabilizer_forall_apply_smul_sub_pow_lt_one`: existence of a Frobenius
  element at `w` for a profinite action.
* `AbsoluteValue.topologicalClosure_zpowers_mul_inertia_eq_stabilizer_valuationSubring` and
  `AbsoluteValue.topologicalClosure_zpowers_sup_inertia_eq_stabilizer_valuationSubring`: a
  Frobenius element and inertia generate the stabilizer of `A_w`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §§3 and 9.
* The congruence form `w (σ • x - x ^ q) < 1` is the one of `New.IsFrob` in the riemann-hypothesis
  project (https://github.com/leanprover-community/riemann-hypothesis, file
  `src/Lib/ClassField/Places/LocalFields.lean` at commit
  e38782a68eb5f6ee793739847c703aa16080ef6c), where existence is proved through completions.
-/

public section

open MulAction Pointwise

namespace AbsoluteValue

variable {L S : Type*} [Field L] [Semifield S] [LinearOrder S] [IsStrictOrderedRing S]
  {w : AbsoluteValue L S}

variable {B : Type*} [CommRing B] [Algebra B L] {Q : Ideal B}

/-- **The centre of an absolute value.** If `w ≤ 1` on the image of `B` and `Q` is the ideal of
the `b` with `w b < 1`, the valuation subring of `w` is centred at `Q`. -/
theorem isCenteredAt_valuationSubring (hw : IsNonarchimedean w)
    (hB : ∀ b : B, w (algebraMap B L b) ≤ 1) (hQ : ∀ b : B, b ∈ Q ↔ w (algebraMap B L b) < 1) :
    (w.valuationSubring hw).IsCenteredAt Q where
  algebraMap_mem b := (mem_valuationSubring_iff hw).mpr (hB b)
  algebraMap_mem_nonunits_iff b := by rw [mem_nonunits_valuationSubring_iff, hQ]

/-- The condition "`σ` acts by `x ↦ x ^ q` modulo the nonunits" on the valuation subring of `w`,
read on `w`. -/
theorem forall_mem_valuationSubring_smul_sub_pow_mem_nonunits_iff {G : Type*} [Monoid G]
    [MulSemiringAction G L] (hw : IsNonarchimedean w) {σ : G} {q : ℕ} :
    (∀ x ∈ w.valuationSubring hw, σ • x - x ^ q ∈ (w.valuationSubring hw).nonunits) ↔
      ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1 := by
  simp only [mem_valuationSubring_iff, mem_nonunits_valuationSubring_iff]

variable [IsFractionRing B L] {G : Type*} [Group G] [MulSemiringAction G B]
  [MulSemiringAction G L] [SMulDistribClass G B L] [Q.IsPrime]
  [PreValuationRing (Localization.AtPrime Q)]

/-- **Arithmetic Frobenius elements at the centre of an absolute value.** If `w ≤ 1` on `B`, with
`Q = {b | w b < 1}` and `B_Q` a valuation ring, then for a ring `R` below `B` fixed by `G`, `σ` is
an arithmetic Frobenius at `Q` exactly when `w (σ • x - x ^ #(R ⧸ Q ∩ R)) < 1` whenever
`w x ≤ 1`. -/
theorem isArithFrobAt_iff_forall_apply_smul_sub_pow_lt_one (hw : IsNonarchimedean w)
    (hB : ∀ b : B, w (algebraMap B L b) ≤ 1) (hQ : ∀ b : B, b ∈ Q ↔ w (algebraMap B L b) < 1)
    {R : Type*} [CommRing R] [Algebra R B] [SMulCommClass G R B] {σ : G} :
    IsArithFrobAt R σ Q ↔ ∀ x, w x ≤ 1 → w (σ • x - x ^ Nat.card (R ⧸ Q.under R)) < 1 := by
  rw [(isCenteredAt_valuationSubring hw hB hQ).isArithFrobAt_iff_forall_smul_sub_pow_mem,
    forall_mem_valuationSubring_smul_sub_pow_mem_nonunits_iff]

/-- **The inertia group of the centre of an absolute value.** If `w ≤ 1` on `B`, with
`Q = {b | w b < 1}` and `B_Q` a valuation ring, the inertia group of `Q` in `G` consists of the `g`
with `w (g • x - x) < 1` whenever `w x ≤ 1`. -/
theorem mem_inertia_iff_forall_apply_smul_sub_lt_one (hw : IsNonarchimedean w)
    (hB : ∀ b : B, w (algebraMap B L b) ≤ 1) (hQ : ∀ b : B, b ∈ Q ↔ w (algebraMap B L b) < 1)
    {g : G} : g ∈ Q.inertia G ↔ ∀ x, w x ≤ 1 → w (g • x - x) < 1 := by
  rw [(isCenteredAt_valuationSubring hw hB hQ).mem_inertia_iff]
  simp

variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G]
  [TopologicalSpace L] [DiscreteTopology L] [ContinuousSMul G L]
  {R : Type*} [CommRing R] [Algebra R B] [SMulCommClass G R B]

/-- **Frobenius elements exist at a nonarchimedean absolute value.** Let a profinite group `G` act
continuously on `L` with the discrete topology and on a ring `B` with fraction field `L`, with
`B^G = R`. If `w ≤ 1` on `R`, `Q = {b ∈ B | w b < 1}` has `B_Q` a valuation ring and `R ⧸ Q ∩ R`
is finite, then some `σ : G` stabilizes the valuation subring of `w` and satisfies
`w (σ • x - x ^ #(R ⧸ Q ∩ R)) < 1` whenever `w x ≤ 1`. -/
theorem exists_mem_stabilizer_forall_apply_smul_sub_pow_lt_one (hw : IsNonarchimedean w)
    [Algebra R L] [IsScalarTower R B L] [Algebra.IsInvariant R B G]
    (hR : ∀ r : R, w (algebraMap R L r) ≤ 1) (hQ : ∀ b : B, b ∈ Q ↔ w (algebraMap B L b) < 1)
    [Finite (R ⧸ Q.under R)] :
    ∃ σ : G, σ ∈ stabilizer G (w.valuationSubring hw) ∧
      ∀ x, w x ≤ 1 → w (σ • x - x ^ Nat.card (R ⧸ Q.under R)) < 1 := by
  have hint : Algebra.IsIntegral R B := IsFractionRing.of_continuousSMul_discreteTopology B L G
    (Algebra.IsInvariant.isIntegral_of_profinite (A := R) (B := B) (G := G))
  have hB (b : B) : w (algebraMap B L b) ≤ 1 :=
    hw.apply_le_one_of_isIntegral hR ((hint.isIntegral b).algebraMap)
  simpa only [← forall_mem_valuationSubring_smul_sub_pow_mem_nonunits_iff hw] using
    (isCenteredAt_valuationSubring hw hB hQ).exists_mem_stabilizer_forall_smul_sub_pow_mem_nonunits
      (G := G) (R := R)

/-- **A Frobenius element and inertia generate the stabilizer of the valuation subring of an
absolute value**, as a product of subsets: if `w ≤ 1` on `B`, `Q = {b | w b < 1}` has `B_Q` a
valuation ring, and `σ` satisfies `w (σ • x - x ^ #(R ⧸ Q ∩ R)) < 1` whenever `w x ≤ 1`, then
every element of the stabilizer of the valuation subring of `w` is `s * i` with `s` in the closure
of the powers of `σ` and `i` in the inertia group of `Q`, which
`AbsoluteValue.mem_inertia_iff_forall_apply_smul_sub_lt_one` describes on `w`. -/
theorem topologicalClosure_zpowers_mul_inertia_eq_stabilizer_valuationSubring
    (hw : IsNonarchimedean w) (hB : ∀ b : B, w (algebraMap B L b) ≤ 1)
    (hQ : ∀ b : B, b ∈ Q ↔ w (algebraMap B L b) < 1) {σ : G}
    (hσ : ∀ x, w x ≤ 1 → w (σ • x - x ^ Nat.card (R ⧸ Q.under R)) < 1) :
    ((Subgroup.zpowers σ).topologicalClosure : Set G) * Q.inertia G =
      stabilizer G (w.valuationSubring hw) :=
  (isCenteredAt_valuationSubring hw hB hQ).topologicalClosure_zpowers_mul_inertia_eq_stabilizer
    ((forall_mem_valuationSubring_smul_sub_pow_mem_nonunits_iff hw).mpr hσ)

/-- **A Frobenius element and inertia generate the stabilizer of the valuation subring of an
absolute value**: under the hypotheses of
`AbsoluteValue.topologicalClosure_zpowers_mul_inertia_eq_stabilizer_valuationSubring`, the
stabilizer of the valuation subring of `w` is generated by the closure of `⟨σ⟩` and the inertia
group of `Q`. -/
theorem topologicalClosure_zpowers_sup_inertia_eq_stabilizer_valuationSubring
    (hw : IsNonarchimedean w) (hB : ∀ b : B, w (algebraMap B L b) ≤ 1)
    (hQ : ∀ b : B, b ∈ Q ↔ w (algebraMap B L b) < 1) {σ : G}
    (hσ : ∀ x, w x ≤ 1 → w (σ • x - x ^ Nat.card (R ⧸ Q.under R)) < 1) :
    (Subgroup.zpowers σ).topologicalClosure ⊔ Q.inertia G =
      stabilizer G (w.valuationSubring hw) :=
  (isCenteredAt_valuationSubring hw hB hQ).topologicalClosure_zpowers_sup_inertia_eq_stabilizer
    ((forall_mem_valuationSubring_smul_sub_pow_mem_nonunits_iff hw).mpr hσ)

end AbsoluteValue
