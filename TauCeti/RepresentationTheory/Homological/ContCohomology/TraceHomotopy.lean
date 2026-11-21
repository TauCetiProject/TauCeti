/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.MulAction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

import Mathlib.Algebra.Ring.Action.End

/-!
# The trace homotopy of a finite group with a trace-one weight

Let a finite group `G` act on a semiring `A` by ring automorphisms and semilinearly on an
`A`-module `M`, so that `g • (r • m) = (g • r) • (g • m)`. Suppose that `α : A` has trace one,
`∑ τ, τ • α = 1`. The **trace homotopy** sends a `1`-cochain `a : G → M` to

```text
b = traceHomotopy α a = -∑ τ, (τ • α) • a τ.
```

With `d⁰` and `d¹` the explicit differentials of `TauCeti.ContCohomology`, it satisfies the
defect identity

```text
(d⁰ b) g - a g = -∑ τ, ((g τ) • α) • (d¹ a) (g, τ)    for every g,
```

whatever the cochain `a`, together with `b = m - ∑ τ, τ • (α • m)` when `a = d⁰ m`. In particular
it inverts `d⁰` on `1`-cocycles: every `1`-cocycle `a` equals `d⁰ b`. Both identities are purely
algebraic, and they hold for every finite group, including one whose order is not invertible in
`A`. The weight `α = |G|⁻¹` with the trivial action recovers averaging.

On an ultrametric module with a bounded scalar action, and a weight whose conjugates have norm at
most `‖α‖` (for instance under an isometric action on `A`), the defect identity gives the bounds

```text
‖b‖ ≤ ‖α‖ * B          when ‖a g‖ ≤ B for every g,
‖(d⁰ b) g - a g‖ ≤ ‖α‖ * D    when ‖(d¹ a) (g, h)‖ ≤ D for all g, h.
```

These are the finite-group estimates behind Tate's vanishing of `H¹(H, ℂ_p)` for the absolute
Galois group `H` of a cyclotomic field `K_∞ = K(μ_{p^∞})`. There `G` is a finite quotient of `H`
acting on a finite Galois extension of `K_∞`, `a` is an algebraic approximation of a continuous
cocycle, and `α` is an almost integral element of trace one, with `‖α‖` below any prescribed
constant greater than `1`; dividing by `|G|` instead would lose a factor `‖(|G| : K_∞)‖⁻¹`, which
is unbounded as `G` grows.

## Main results

* `TauCeti.ContCohomology.traceHomotopy`: the trace homotopy `a ↦ -∑ τ, (τ • α) • a τ`.
* `TauCeti.ContCohomology.d0_traceHomotopy_apply_sub`: the defect identity.
* `TauCeti.ContCohomology.d0_traceHomotopy_of_isCocycle₁`: a `1`-cocycle is `d⁰` of its trace
  homotopy.
* `TauCeti.ContCohomology.traceHomotopy_d0`: the trace homotopy of `d⁰ m` is
  `m - ∑ τ, τ • (α • m)`.
* `TauCeti.ContCohomology.norm_traceHomotopy_le` and
  `TauCeti.ContCohomology.norm_d0_traceHomotopy_apply_sub_le`: the ultrametric bounds.
* `TauCeti.ContCohomology.subsingleton_H1_of_sum_smul_eq_one`: a finite group with a trace-one
  weight has vanishing continuous `H¹`.
* `TauCeti.ContCohomology.subsingleton_H1_of_isUnit_natCard`: continuous `H¹` vanishes when the
  order of `G` is a unit in a semiring acting linearly on the coefficients; for instance for a
  finite group acting continuously and linearly on a topological vector space over a field of
  characteristic zero.

## References

* O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory*, §14.1, Lemma 14.1.3,
  and §14.3, Lemma 14.3.1 and its proof, for the trace homotopy and its estimates.
* J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (Driebergen, 1966),
  Springer, 1967, §3.
-/

public section

open groupCohomology

namespace TauCeti.ContCohomology

section Algebraic

variable {G A M : Type*} [Group G] [Fintype G] [Semiring A] [MulSemiringAction G A]
  [AddCommGroup M] [Module A M]

/-- The **trace homotopy** of a weight `α : A`, sending a `1`-cochain `a : G → M` of the finite
group `G` to `-∑ τ, (τ • α) • a τ`. When the conjugates of `α` sum to `1`, it inverts `d⁰` on
`1`-cocycles (`TauCeti.ContCohomology.d0_traceHomotopy_of_isCocycle₁`), with the defect on an
arbitrary cochain controlled by its `d¹` (`TauCeti.ContCohomology.d0_traceHomotopy_apply_sub`). -/
def traceHomotopy (α : A) : (G → M) →+ M where
  toFun a := -∑ τ, (τ • α) • a τ
  map_zero' := by simp
  map_add' a a' := by simp [smul_add, Finset.sum_add_distrib, add_comm]

/-- The defining formula for the trace homotopy. -/
@[simp]
theorem traceHomotopy_apply (α : A) (a : G → M) :
    traceHomotopy α a = -∑ τ, (τ • α) • a τ := (rfl)

/-- The left translates of the conjugates of a trace-one weight still sum to `1`. -/
private theorem sum_mul_smul_eq_one {α : A} (hα : ∑ τ : G, τ • α = 1) (g : G) :
    ∑ τ : G, (g * τ) • α = 1 := by
  simp_rw [mul_smul, ← Finset.smul_sum, hα, smul_one]

variable [DistribMulAction G M] [SMulDistribClass G A M]

/-- **The defect identity of the trace homotopy.** For a trace-one weight `α` and any `1`-cochain
`a`, the trace homotopy `b` of `a` satisfies `(d⁰ b) g - a g = -∑ τ, ((g τ) • α) • (d¹ a) (g, τ)`.
In particular `d⁰ b` approximates `a` as well as `a` approximates a cocycle. -/
theorem d0_traceHomotopy_apply_sub {α : A} (hα : ∑ τ : G, τ • α = 1) (a : G → M) (g : G) :
    d0 G M (traceHomotopy α a) g - a g = -∑ τ, ((g * τ) • α) • d1 G M a (g, τ) := by
  -- Reindex the sum defining `b` by `τ ↦ g τ`, and sum the constant face `a g` against the
  -- translated weights, which add up to `1`.
  have hshift : ∑ τ : G, ((g * τ) • α) • a (g * τ) = ∑ τ : G, (τ • α) • a τ :=
    Equiv.sum_comp (Equiv.mulLeft g) fun τ ↦ (τ • α) • a τ
  have hone : ∑ τ : G, ((g * τ) • α) • a g = a g := by
    rw [← Finset.sum_smul, sum_mul_smul_eq_one hα g, one_smul]
  simp only [d0_apply, d1_apply, traceHomotopy_apply, smul_neg, Finset.smul_sum,
    smul_distrib_smul, ← mul_smul, smul_add, smul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hone, hshift]
  abel

/-- **The trace homotopy inverts `d⁰` on `1`-cocycles.** For a trace-one weight `α`, every
`1`-cocycle `a` is the coboundary of its trace homotopy. -/
theorem d0_traceHomotopy_of_isCocycle₁ {α : A} (hα : ∑ τ : G, τ • α = 1) {a : G → M}
    (ha : IsCocycle₁ a) : d0 G M (traceHomotopy α a) = a := by
  have hd : d1 G M a = 0 := d1_apply_eq_zero_iff.2 ha
  funext g
  have h := d0_traceHomotopy_apply_sub hα a g
  rw [hd] at h
  simpa [sub_eq_zero] using h

/-- **The trace homotopy of a coboundary.** For a trace-one weight `α`, the trace homotopy of
`d⁰ m` is `m` minus the trace `∑ τ, τ • (α • m)`, which is invariant under `G`. -/
theorem traceHomotopy_d0 {α : A} (hα : ∑ τ : G, τ • α = 1) (m : M) :
    traceHomotopy α (d0 G M m) = m - ∑ τ : G, τ • (α • m) := by
  simp only [traceHomotopy_apply, d0_apply, smul_sub, Finset.sum_sub_distrib,
    ← smul_distrib_smul, ← Finset.sum_smul, hα, one_smul]
  abel

end Algebraic

section Norm

variable {G A M : Type*} [Group G] [Fintype G] [SeminormedRing A] [MulSemiringAction G A]
  [SeminormedAddCommGroup M] [IsUltrametricDist M] [Module A M] [IsBoundedSMul A M]

/-- **The trace homotopy is bounded by the weight.** On an ultrametric module, if the conjugates of
`α` have norm at most `‖α‖` and `a` is bounded by `B`, then its trace homotopy is bounded by
`‖α‖ * B`. No trace condition is needed. -/
theorem norm_traceHomotopy_le {α : A} (hnorm : ∀ τ : G, ‖τ • α‖ ≤ ‖α‖) {a : G → M} {B : ℝ}
    (ha : ∀ g, ‖a g‖ ≤ B) : ‖traceHomotopy α a‖ ≤ ‖α‖ * B := by
  rw [traceHomotopy_apply, norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty Finset.univ_nonempty
    fun τ _ ↦ ?_
  exact (norm_smul_le _ _).trans (mul_le_mul (hnorm τ) (ha τ) (norm_nonneg _) (norm_nonneg _))

/-- **The defect of the trace homotopy is bounded by the cocycle defect.** On an ultrametric
module, for a trace-one weight `α` whose conjugates have norm at most `‖α‖`, if `d¹ a` is bounded
by `D`, then `d⁰` of the trace homotopy of `a` differs from `a` by at most `‖α‖ * D`. -/
theorem norm_d0_traceHomotopy_apply_sub_le [DistribMulAction G M] [SMulDistribClass G A M]
    {α : A} (hα : ∑ τ : G, τ • α = 1) (hnorm : ∀ τ : G, ‖τ • α‖ ≤ ‖α‖) {a : G → M} {D : ℝ}
    (hda : ∀ g h, ‖d1 G M a (g, h)‖ ≤ D) (g : G) :
    ‖d0 G M (traceHomotopy α a) g - a g‖ ≤ ‖α‖ * D := by
  rw [d0_traceHomotopy_apply_sub hα, norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty Finset.univ_nonempty
    fun τ _ ↦ ?_
  exact (norm_smul_le _ _).trans
    (mul_le_mul (hnorm _) (hda g τ) (norm_nonneg _) (norm_nonneg _))

end Norm

section Cohomology

variable {G M : Type*} [Group G] [TopologicalSpace G] [AddCommGroup M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]

/-- **A finite group with a trace-one weight has vanishing `H¹`.** If a finite group `G` acts on a
semiring `A` by ring automorphisms and semilinearly on the topological `A`-module `M`, and some
`α : A` has trace one, then every continuous `1`-cocycle is a coboundary, so `H¹(G, M) = 0`. -/
theorem subsingleton_H1_of_sum_smul_eq_one [Fintype G] {A : Type*} [Semiring A]
    [MulSemiringAction G A] [Module A M] [SMulDistribClass G A M] {α : A}
    (hα : ∑ τ : G, τ • α = 1) : Subsingleton (H1 G M) := by
  suffices h : ∀ x : H1 G M, x = 0 from ⟨fun x y ↦ (h x).trans (h y).symm⟩
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    rw [H1pi_eq_zero_iff, ← d0_traceHomotopy_of_isCocycle₁ hα (mem_Z1_iff.1 f.2).2]
    exact d0_mem_B1 _

/-- **`H¹` vanishes when the order of the group is invertible on the coefficients.** If `M` is a
module over a semiring `k` on which `G` acts `k`-linearly, and `Nat.card G` is a unit of `k`,
then `H¹(G, M) = 0`. This covers a finite group acting continuously and linearly on a topological
vector space over a field of characteristic zero. An infinite `G` has `Nat.card G = 0`, which is a
unit only of the zero ring. The algebraic counterpart for `Rep k G`, in every positive degree, is
`groupCohomology.subsingleton_of_isUnit_natCard`; here the coefficients carry an arbitrary
topology and the classes are those of continuous cocycles. -/
theorem subsingleton_H1_of_isUnit_natCard {k : Type*} [Semiring k] [Module k M]
    [SMulCommClass G k M] (hG : IsUnit (Nat.card G : k)) : Subsingleton (H1 G M) := by
  cases finite_or_infinite G with
  | inl _ =>
    cases nonempty_fintype G
    -- Let `G` act trivially on `k`; the weight `|G|⁻¹` then has trace one.
    let : MulSemiringAction G k := MulSemiringAction.compHom k (1 : G →* RingAut k)
    have hsmul (g : G) (r : k) : g • r = r := rfl
    have : SMulDistribClass G k M := ⟨fun g r m ↦ by rw [hsmul, smul_comm]⟩
    refine subsingleton_H1_of_sum_smul_eq_one (A := k) (α := ↑hG.unit⁻¹) ?_
    simp only [hsmul, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      nsmul_eq_mul, IsUnit.mul_val_inv]
  | inr _ =>
    rw [Nat.card_eq_zero_of_infinite, Nat.cast_zero, isUnit_zero_iff] at hG
    have : Subsingleton k := subsingleton_of_zero_eq_one hG
    have : Subsingleton M := Module.subsingleton k M
    infer_instance

end Cohomology

end TauCeti.ContCohomology
