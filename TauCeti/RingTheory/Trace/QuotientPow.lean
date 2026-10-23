/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.LinearAlgebra.Trace.Exact
import TauCeti.RingTheory.DedekindDomain.Ideal.QuotientPow

/-!
# The trace of a quotient by a power of a prime

Let `B` be a Dedekind domain over a commutative ring `A`, let `p` be a maximal ideal of `A` with
residue field `κ = A ⧸ p`, and let `P` be a maximal ideal of `B` with `p · B ⊆ P ^ n`, so that
`B ⧸ P ^ n` is a `κ`-algebra.  This file computes the trace of that algebra:

`Tr_{(B ⧸ P ^ n) / κ} (z) = n · Tr_{(B ⧸ P) / κ} (z)`.

The `P`-adic filtration of `B ⧸ P ^ n` has `n` graded pieces, each of them a copy of the residue
field `B ⧸ P` on which multiplication by `z` acts as multiplication by the residue of `z`; the
trace of an endomorphism of a filtered vector space is the sum of the traces on the pieces, so the
`n` copies contribute `n` equal summands.  The induction runs over one step of the filtration at a
time, through the short exact sequence

`0 → B ⧸ P --· a--> B ⧸ P ^ (n + 1) → B ⧸ P ^ n → 0`,

where `a` is any element of `P ^ n` not in `P ^ (n + 1)`; injectivity of multiplication by `a`
(`Ideal.mapQ_mulLeft_pow_succ_injective`) and exactness in the middle
(`Ideal.exact_mapQ_mulLeft_pow_succ`) are proved in
`TauCeti.RingTheory.DedekindDomain.Ideal.QuotientPow`, and the trace identity is
`LinearMap.trace_eq_add_of_exact`.

The formula is what makes the tame case of Dedekind's different theorem work: it produces an
element of `B ⧸ P ^ e` with nonzero trace as soon as the residue extension is separable and the
characteristic of `κ` does not divide `e` (see
`TauCeti.RingTheory.DedekindDomain.Different`, where it is combined with Mathlib's trace
computation for `B ⧸ p · B`, `Algebra.trace_quotient_eq_of_isDedekindDomain`).

## Main results

* `Algebra.trace_quotient_pow_mk`: the trace formula `Tr_{B ⧸ P ^ n} = n · Tr_{B ⧸ P}`.
-/

public section

open Module

namespace Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsDedekindDomain B]
variable {p : Ideal A} [p.IsMaximal] {P : Ideal B} [P.IsMaximal]

attribute [local instance] Ideal.Quotient.field

/-- One step of the `P`-adic filtration: for `P ≠ ⊥`, the trace over `A ⧸ p` of the residue of `z`
in `B ⧸ P ^ (n + 1)` is the sum of its traces over `A ⧸ p` in `B ⧸ P` and in `B ⧸ P ^ n`, for any
`A ⧸ p`-algebra structures on these quotients compatible with `A`. -/
private theorem trace_quotient_pow_succ_mk [Module.Finite A B] (hP : P ≠ ⊥) (n : ℕ)
    [Algebra (A ⧸ p) (B ⧸ P ^ (n + 1))] [IsScalarTower A (A ⧸ p) (B ⧸ P ^ (n + 1))]
    [Algebra (A ⧸ p) (B ⧸ P ^ n)] [IsScalarTower A (A ⧸ p) (B ⧸ P ^ n)]
    [Algebra (A ⧸ p) (B ⧸ P)] [IsScalarTower A (A ⧸ p) (B ⧸ P)] (z : B) :
    Algebra.trace (A ⧸ p) (B ⧸ P ^ (n + 1)) (Ideal.Quotient.mk _ z) =
      Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ z) +
        Algebra.trace (A ⧸ p) (B ⧸ P ^ n) (Ideal.Quotient.mk _ z) := by
  have := Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ P ^ (n + 1))
  obtain ⟨a, ha, ha'⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hP Ideal.IsPrime.ne_top' n
  have hsurj : Function.Surjective (algebraMap A (A ⧸ p)) :=
    Ideal.Quotient.algebraMap_eq p ▸ Ideal.Quotient.mk_surjective
  -- the `B`-linear maps of `0 → B ⧸ P → B ⧸ P ^ (n + 1) → B ⧸ P ^ n → 0`, made `A ⧸ p`-linear
  let g := Submodule.mapQ P (P ^ (n + 1)) (LinearMap.mulLeft B a)
    (Ideal.le_comap_mulLeft_pow_succ ha)
  let π := Submodule.factor (Ideal.pow_le_pow_right (I := P) (n.le_add_right 1))
  let i := (g.restrictScalars A).extendScalarsOfSurjective hsurj
  let pi := (π.restrictScalars A).extendScalarsOfSurjective hsurj
  have hi : ⇑i = g := funext fun _ ↦ by
    rw [LinearMap.extendScalarsOfSurjective_apply, LinearMap.restrictScalars_apply]
  have hpi : ⇑pi = π := funext fun _ ↦ by
    rw [LinearMap.extendScalarsOfSurjective_apply, LinearMap.restrictScalars_apply]
  simp only [Algebra.trace_apply]
  refine LinearMap.trace_eq_add_of_exact (i := i) (π := pi) ?_ ?_ ?_ ?_ ?_
  · rw [hi]; exact Ideal.mapQ_mulLeft_pow_succ_injective ha ha'
  · rw [hpi]; exact Submodule.factor_surjective _
  · rw [hi, hpi]; exact Ideal.exact_mapQ_mulLeft_pow_succ hP ha ha'
  -- multiplication by the residue of `z` is the action of `z ∈ B`, which `B`-linear maps respect
  all_goals simp only [LinearMap.ext_iff, LinearMap.comp_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply', hi, hpi, ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def, map_smul,
    implies_true]

/-- **The trace of a quotient by a prime power.** For `P` a maximal ideal of a Dedekind domain `B`
that is module-finite over `A`, and `p` a maximal ideal of `A` making both `B ⧸ P ^ n` and `B ⧸ P`
algebras over the residue field `A ⧸ p`, the trace of the residue of `z` in `B ⧸ P ^ n` is `n`
times its trace in the residue field `B ⧸ P`.

The two `IsScalarTower` hypotheses pin the algebra structures to the ones induced by `A → B`;
they are what `Ideal.Quotient.algebraQuotientOfLEComap` provides, and they hold for `B ⧸ P ^ n`
exactly when `p · B ⊆ P ^ n`. -/
theorem trace_quotient_pow_mk [Module.Finite A B] (hP : P ≠ ⊥) (n : ℕ)
    [instA : Algebra (A ⧸ p) (B ⧸ P ^ n)] [instT : IsScalarTower A (A ⧸ p) (B ⧸ P ^ n)]
    [Algebra (A ⧸ p) (B ⧸ P)] [IsScalarTower A (A ⧸ p) (B ⧸ P)] (z : B) :
    Algebra.trace (A ⧸ p) (B ⧸ P ^ n) (Ideal.Quotient.mk _ z) =
      n • Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk _ z) := by
  induction n generalizing instA instT with
  | zero =>
      have hz : z ∈ P ^ 0 := by simp
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hz]
  | succ n ih =>
      have : Nontrivial (B ⧸ P ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr <|
        ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.pow_le_self n.succ_ne_zero)
      -- the base ideal is the contraction of `P ^ (n + 1)`, hence lies in that of `P ^ n`
      have hcomap : p ≤ Ideal.comap (algebraMap A B) (P ^ n) :=
        (Ideal.comap_eq_of_scalar_tower_quotient (algebraMap (A ⧸ p) _).injective).ge.trans
          (Ideal.comap_mono (Ideal.pow_le_pow_right n.le_succ))
      let _ : Algebra (A ⧸ p) (B ⧸ P ^ n) := Ideal.Quotient.algebraQuotientOfLEComap hcomap
      -- the structure map of `algebraQuotientOfLEComap` is `Ideal.quotientMap` by definition
      have _ : IsScalarTower A (A ⧸ p) (B ⧸ P ^ n) := .of_algebraMap_eq fun x ↦ by
        rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.algebraMap_eq]
        exact Ideal.quotientMap_mk.symm
      rw [trace_quotient_pow_succ_mk hP n z, ih, succ_nsmul']

end Algebra
