/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Evaluating a multivariate power series at arguments from an adic ideal

Let `S` carry the `I`-adic topology for an ideal `I`, and let `f` be a multivariate power series
evaluated at a family `a : σ → S` through a continuous coefficient map `φ`. This file bounds the
value `eval₂ φ a f` by a power of `I`, in the three forms the estimate is used in: the value is
confined to `I ^ k` as soon as the arguments are and `φ` sends the constant term there, and the
confinement improves when its coefficient images vanish in low total degree or when `φ` sends every
coefficient into a power of `I`.

Three further results serve the same arguments from either side. Over finitely many variables a
pointwise topologically nilpotent family admits evaluation; arguments drawn from `I` satisfy
`MvPowerSeries.HasEval` in the first place, so that the value is defined at all; and the value is
congruent to the image of the constant term modulo `I`.

They are proved differently. `hasEval_of_finite_of_isTopologicallyNilpotent` does not use the
estimates above at all: over
finitely many variables the decay condition at infinity is vacuous, so topological nilpotence
of each argument is the whole content. `hasEval_of_mem` is its corollary, obtained by supplying
that nilpotence from membership in `I` through `IsAdic.isTopologicallyNilpotent_of_mem`.
`eval₂_sub_constantCoeff_mem` is the one that reduces to them — subtracting the constant term
kills the constant monomial and every surviving monomial carries an argument, so the difference
is the `k = 1` case of `eval₂_mem_pow` applied to `f - C (constantCoeff f)`.

The three bounds have the same one-line mechanism. `MvPowerSeries.hasSum_eval₂` writes the value
as the sum of its monomial values `φ (coeff d f) * ∏ s, a s ^ d s`; each such monomial is checked
to lie in the relevant power of `I`; and the sum of a family inside `I ^ n` stays inside `I ^ n`
because `I ^ n` is closed (`IsAdic.isClosed_pow`) and `tsum_mem` applies. The three statements
differ only in which power the monomial estimate produces.

Three hypotheses of the source turn out to be unnecessary. Nothing asks for `I` to be maximal or
for `S` to be local, only that the topology be `I`-adic, so the results are stated for an
arbitrary ideal; the coefficient map is an arbitrary continuous `φ : R →+* S` rather than the
identity, since `MvPowerSeries.hasSum_eval₂` is already stated at that generality; and the index
type need not be finite, because the summation argument uses only the `Tendsto a cofinite (𝓝 0)`
already carried by `HasEval`. Taking `I` to be `IsLocalRing.maximalIdeal S` and `φ` to be
`RingHom.id S` recovers the source statements.

Finiteness of `σ` survives in `hasEval_of_finite_of_isTopologicallyNilpotent`, where it is what
makes the decay condition of
`HasEval` vacuous; that is the one place the hypothesis does work, and `hasEval_of_mem` inherits
it from there.

## Main results

* `MvPowerSeries.eval₂_mem_pow` : arguments in `I ^ k`, and a constant term whose image under
  `φ` lies in `I ^ k`, confine the value to `I ^ k`.
* `MvPowerSeries.eval₂_mem_pow_mul` : if the coefficient images vanish below total degree `c`,
  evaluation at arguments in `I ^ j` takes values in `I ^ (c * j)`.
* `MvPowerSeries.eval₂_mem_pow_add_mul` : if moreover `φ` sends every coefficient into `I ^ k`,
  the value lies in `I ^ (k + c * j)`.
* `MvPowerSeries.hasEval_of_finite_of_isTopologicallyNilpotent` : finitely many topologically
  nilpotent arguments are an
  admissible evaluation point.
* `MvPowerSeries.hasEval_of_mem` : a family of finitely many arguments drawn from `I` is an
  admissible evaluation point.
* `MvPowerSeries.eval₂_sub_constantCoeff_mem` : the value and the image of the constant term
  differ by an element of `I`.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` (`github.com/MichaelStollBayreuth/EllipticCurves`,
Apache-2.0) at commit `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, file
`EllipticCurves/WeierstrassFormalGroup/Eval.lean`, where the three bounds are
`ChabautyColeman.MvPSeries.eval_mem_maximalIdeal_pow`, `..._pow_mul` and `..._pow_add_mul`, and
`EllipticCurves/Mathlib/Chabauty/MvPSeries.lean`, where `hasEval_of_mem` carries the same name and
`eval₂_sub_constantCoeff_mem` is `ChabautyColeman.MvPSeries.eval_sub_constantCoeff_mem`. That
development evaluates through its own `ChabautyColeman.MvPSeries.eval`, which is by definition
`MvPowerSeries.eval₂ (RingHom.id _)`; the wrapper is dropped here and the statements are made
directly about Mathlib's `MvPowerSeries.eval₂`, as are the generalisations noted above. The
monomial estimates and the closed-ideal summation argument are the source's, as is the
`HasEval` construction. The congruence modulo `I` is not: the source proves it from the
`hasSum` expansion directly, whereas here it is the `k = 1` case of `eval₂_mem_pow` applied to
`f - C (constantCoeff f)`, which is shorter and needs no finiteness of `σ`.
-/

public section

namespace MvPowerSeries

section Eval

variable {σ : Type*}
variable {R : Type*} [CommRing R] [UniformSpace R] [IsTopologicalSemiring R] [IsUniformAddGroup R]
variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S]
    [T2Space S] [IsTopologicalRing S] [IsLinearTopology S S]
variable {φ : R →+* S} {a : σ → S} {I : Ideal S}

/-- **The value lies in `I ^ k` when the arguments do and `φ` sends the constant term there.**
Every monomial of positive degree already carries an argument, hence a factor from `I ^ k`; the
constant monomial is covered by the hypothesis on the image of the constant term. -/
theorem eval₂_mem_pow (hφ : Continuous φ) (ha : HasEval a) (hI : IsAdic I) {k : ℕ}
    (hmem : ∀ i, a i ∈ I ^ k) (f : MvPowerSeries σ R)
    (hcc : φ (constantCoeff f) ∈ I ^ k) :
    eval₂ φ a f ∈ I ^ k := by
  classical
  have htot := hasSum_eval₂ hφ ha f
  have hval : ∀ d : σ →₀ ℕ, φ (coeff d f) * d.prod (fun s e ↦ a s ^ e) ∈ I ^ k := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simpa using hcc
    · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
      rw [Finsupp.prod, ← Finset.prod_erase_mul _ _ hi]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (hmem i) _
          (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))))
  have hsum := tsum_mem (hI.isClosed_pow k) hval
  rwa [htot.tsum_eq] at hsum

/-- **Small coefficient images improve the bound.** If `φ` kills the coefficients below total degree
`c` and sends every coefficient of `f` into `I ^ k`, evaluation at arguments of `I ^ j` lies in
`I ^ (k + c * j)`. -/
theorem eval₂_mem_pow_add_mul (hφ : Continuous φ) (ha : HasEval a) (hI : IsAdic I) {j c k : ℕ}
    (hmem : ∀ i, a i ∈ I ^ j) (f : MvPowerSeries σ R)
    (hcoeff : ∀ d : σ →₀ ℕ, φ (coeff d f) ∈ I ^ k)
    (hlow : ∀ d : σ →₀ ℕ, d.degree < c → φ (coeff d f) = 0) :
    eval₂ φ a f ∈ I ^ (k + c * j) := by
  classical
  have htot := hasSum_eval₂ hφ ha f
  have hval : ∀ d : σ →₀ ℕ, φ (coeff d f) * d.prod (fun s e ↦ a s ^ e) ∈ I ^ (k + c * j) := by
    intro d
    rcases lt_or_ge d.degree c with hlt | hge
    · rw [hlow d hlt, zero_mul]
      exact zero_mem _
    · rw [pow_add]
      apply Ideal.mul_mem_mul (hcoeff d)
      apply Ideal.pow_le_pow_right (Nat.mul_le_mul_right j hge)
      simpa only [Finsupp.prod, Finsupp.degree_apply,
        Finset.prod_pow_eq_pow_sum, ← pow_mul, Nat.mul_comm, Finset.mul_sum] using
        (Ideal.prod_mem_prod fun s (_ : s ∈ d.support) ↦ Ideal.pow_mem_pow (hmem s) (d s))
  have hsum := tsum_mem (hI.isClosed_pow (k + c * j)) hval
  rwa [htot.tsum_eq] at hsum

/-- **If the coefficient images vanish below total degree `c`, evaluation at arguments of
`I ^ j` takes values in `I ^ (c * j)`.** -/
theorem eval₂_mem_pow_mul (hφ : Continuous φ) (ha : HasEval a) (hI : IsAdic I) {j c : ℕ}
    (hmem : ∀ i, a i ∈ I ^ j) (f : MvPowerSeries σ R)
    (hcoeff : ∀ d : σ →₀ ℕ, d.degree < c → φ (coeff d f) = 0) :
    eval₂ φ a f ∈ I ^ (c * j) := by
  simpa using eval₂_mem_pow_add_mul (k := 0) hφ ha hI hmem f (fun _ ↦ by simp) hcoeff

/-- **The value differs from the image of the constant term by an element of `I`.** Equivalently,
for arguments drawn from `I` the value of `f` is congruent to the image of its constant term
modulo `I`. -/
theorem eval₂_sub_constantCoeff_mem (hφ : Continuous φ) (ha : HasEval a)
    (hI : IsAdic I) (hmem : ∀ i, a i ∈ I) (f : MvPowerSeries σ R) :
    eval₂ φ a f - φ (constantCoeff f) ∈ I := by
  have key := eval₂_mem_pow (k := 1) hφ ha hI (by simpa using hmem)
    (f - C (constantCoeff f)) (by simp)
  rw [pow_one] at key
  -- `eval₂ φ a` is not syntactically a bundled hom, so additivity is taken through `eval₂Hom`.
  have hsplit : eval₂ φ a (f - C (constantCoeff f)) = eval₂ φ a f - φ (constantCoeff f) := by
    rw [← coe_eval₂Hom hφ ha, map_sub, coe_eval₂Hom hφ ha, eval₂_C]
  rwa [hsplit] at key

end Eval

section HasEval

-- Neither result below needs the uniform structure the evaluation bounds require: `HasEval` is
-- a condition on a topological ring alone.
variable {σ : Type*} {S : Type*} [CommRing S] [TopologicalSpace S] {a : σ → S} {I : Ideal S}

/-- **Finitely many topologically nilpotent arguments can be substituted into a power series.**
Over finitely many variables the decay condition `HasEval` asks for at infinity is vacuous, so
pointwise topological nilpotence is the whole of it. -/
theorem hasEval_of_finite_of_isTopologicallyNilpotent [Finite σ]
    (h : ∀ i, IsTopologicallyNilpotent (a i)) : HasEval a where
  hpow := h
  tendsto_zero := by simp [Filter.cofinite_eq_bot]

/-- **A family drawn from an adic ideal can be substituted into a power series.** For an index
type with finitely many variables, lying in `I` is the only condition the arguments need: it
already gives them the `HasEval` property that evaluation requires. -/
theorem hasEval_of_mem [Finite σ] (hI : IsAdic I) (hmem : ∀ i, a i ∈ I) : HasEval a :=
  hasEval_of_finite_of_isTopologicallyNilpotent fun s ↦ hI.isTopologicallyNilpotent_of_mem (hmem s)

end HasEval

end MvPowerSeries
