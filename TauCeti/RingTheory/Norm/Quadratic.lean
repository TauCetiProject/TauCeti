/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic
public import TauCeti.FieldTheory.Galois.Basic

/-!
# Trace and norm in a separable quadratic extension

For a separable quadratic extension `L/K` the trace and norm are the two elementary symmetric
functions of the pair `{x, σx}`, where `σ` is the nontrivial automorphism: `tr x = x + σx` and
`N x = x · σx` (`algebraMap_trace_eq_add`, `algebraMap_norm_eq_mul`). Everything else here is a
consequence, except `trace_algebraMap_add_algebraMap_mul`, which needs no separability at all —
`K`-linearity of the trace and `tr(b) = [L : K]·b = 2b` suffice:

* `trace_algebraMap_add_algebraMap_mul` (no separability) and
  `norm_algebraMap_add_algebraMap_mul` evaluate the trace and norm of `b + aθ`, which is how a
  statement about one generator transfers to another;
* `discrim_ne_zero`: for `θ` outside `K`, the discriminant `t² - 4n` of its minimal polynomial
  `X² - tX + n` is nonzero, since it equals `(θ - σθ)²` and `σ` moves `θ`.

In characteristic two `discrim_ne_zero` says `t ≠ 0`, reflecting that a separable quadratic
extension is then Artin–Schreier rather than Kummer.

These are consumed by the extension quadratic twist in
`TauCeti/AlgebraicGeometry/EllipticCurve/QuadraticTwist.lean`, which advances
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists): `discrim_ne_zero` is exactly what
makes the twist by a generator elliptic.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/RingTheory/Norm/Quadratic.lean` at the roadmap's pin `bc2fe8ff7396`, FLT PR #1088,
Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`; following this
repository's convention for adapted material, the upstream authorship is credited here rather
than in the copyright header. Ported with the source's `@[expose]` dropped, and with the two
square-root lemmas left to the PR that consumes them.
-/

public section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L]

namespace Algebra.IsQuadraticExtension

/-- The trace of `b + aθ` in a quadratic extension is `a·tr(θ) + 2b`. Separability is not
needed: this is `K`-linearity of the trace together with `tr(b) = [L : K]·b = 2b`. -/
theorem trace_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.trace K L (algebraMap K L b + algebraMap K L a * θ)
      = a * Algebra.trace K L θ + 2 * b := by
  rw [map_add, Algebra.trace_algebraMap, ← Algebra.smul_def, map_smul,
    Algebra.IsQuadraticExtension.finrank_eq_two]
  simp [nsmul_eq_mul]
  ring

variable [Algebra.IsSeparable K L]

/-- In a separable quadratic extension, the trace of `x` is `x + σx`, where `σ` is the
nontrivial automorphism. -/
theorem algebraMap_trace_eq_add {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (x : L) :
    algebraMap K L (Algebra.trace K L x) = x + σ x := by
  classical
  rw [trace_eq_sum_automorphisms, univ_algEquiv K L hσ, Finset.sum_pair (Ne.symm hσ)]
  simp

/-- In a separable quadratic extension, the norm of `x` is `x * σx`, where `σ` is the
nontrivial automorphism. -/
theorem algebraMap_norm_eq_mul {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1) (x : L) :
    algebraMap K L (Algebra.norm K x) = x * σ x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_algEquiv K L hσ, Finset.prod_pair (Ne.symm hσ)]
  simp

/-- The norm of `b + aθ` in a separable quadratic extension is `b² + ab·tr(θ) + a²·N(θ)`. -/
theorem norm_algebraMap_add_algebraMap_mul (a b : K) (θ : L) :
    Algebra.norm K (algebraMap K L b + algebraMap K L a * θ)
      = b ^ 2 + a * b * Algebra.trace K L θ + a ^ 2 * Algebra.norm K θ := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  apply FaithfulSMul.algebraMap_injective K L
  simp only [map_add, map_mul, map_pow, algebraMap_trace_eq_add K L hσ,
    algebraMap_norm_eq_mul K L hσ, AlgEquiv.commutes]
  ring

/-- If `θ` generates a separable quadratic extension of `K` — that is, lies outside `K` — and
`t`, `n` denote its trace and norm, so that `θ² = tθ - n`, then the discriminant `t² - 4n` of
the minimal polynomial of `θ` is nonzero: over the nontrivial automorphism `σ` it equals
`(θ - σθ)²`, and `σθ ≠ θ`. -/
theorem discrim_ne_zero {θ : L} (hθ : θ ∉ Set.range (algebraMap K L)) :
    Algebra.trace K L θ ^ 2 - 4 * Algebra.norm K θ ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_ne_one K L
  intro h0
  have h1 : (θ - σ θ) ^ 2 = 0 := by
    have h2 := congrArg (algebraMap K L) h0
    simp only [map_sub, map_pow, map_mul, map_zero, map_ofNat,
      algebraMap_trace_eq_add K L hσ, algebraMap_norm_eq_mul K L hσ] at h2
    linear_combination h2
  exact hθ (mem_range_algebraMap_of_apply_eq K L hσ
    (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)).symm)

end Algebra.IsQuadraticExtension

end
