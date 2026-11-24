/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Defect
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.Analysis.Real.Sqrt

/-!
# Asymptotic multiplicative domains of nets of c.p.c. maps into matrices

Let `(φᵢ)` be a family of completely positive contractions `φᵢ : A → M_{kᵢ}` from a possibly
nonunital C⋆-algebra into matrix algebras of varying sizes, indexed along a filter `l` (for
instance a net). Its *asymptotic 2-norm multiplicative domain* `D₂` consists of the `a ∈ A` with
`d₂(φᵢ, a) → 0` and `d₂(φᵢ, a⋆) → 0`, and its *asymptotic norm multiplicative domain* `D_∞` is
defined in the same way with the norm defect `d_∞` (see
`TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Defect`).

Both are closed nonunital star subalgebras of `A`, that is, C⋆-subalgebras. The square roots of
the defects are subadditive, satisfy the product rule
`d(φ, ab)^{1/2} ≤ ‖b‖ d(φ, a)^{1/2} + ‖a‖ d(φ, b)^{1/2}` and are `1`-Lipschitz, which gives
closure under sums, products and limits, and they are homogeneous, `d(φ, c • a) = |c|² d(φ, a)`
(`CompletelyPositiveMap.twoNormDefect_smul`, `CompletelyPositiveMap.normDefect_smul`).
By the product estimates, the net is asymptotically multiplicative against an element of the
domain on either side: for `a ∈ D₂` and every `b ∈ A`, `‖φᵢ(ab) - φᵢ(a)φᵢ(b)‖₂ → 0` and
`‖φᵢ(ba) - φᵢ(b)φᵢ(a)‖₂ → 0`, and in norm for `D_∞`.

Since `d₂(φ, s) ≤ ‖φ(s⋆s) - φ(s⋆)φ(s)‖₂`, asymptotic multiplicativity on the pairs `(s⋆, s)` and
`(s, s⋆)` puts `s` in `D₂`. Hence if this holds for every `s` in a set `S` generating `A` as a
C⋆-algebra, then `D₂ = A` and the net is asymptotically multiplicative on all pairs. This is the
generating-set criterion, for instance for a spanning set of unitaries.

## Main definitions

* `TauCeti.asymptoticTwoNormDomain`: the C⋆-subalgebra `D₂`.
* `TauCeti.asymptoticNormDomain`: the C⋆-subalgebra `D_∞`.

## Main results

* `TauCeti.isClosed_asymptoticTwoNormDomain`,
  `TauCeti.isClosed_asymptoticNormDomain`: both domains are closed.
* `TauCeti.tendsto_normalizedTwoNorm_map_mul_sub_of_mem` and its `'` version:
  two-sided asymptotic multiplicativity on `D₂`, and the norm versions for `D_∞`.
* `TauCeti.tendsto_normalizedTwoNorm_map_mul_sub_of_adjoin`,
  `TauCeti.tendsto_norm_map_mul_sub_of_adjoin`: the generating-set criterion.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), proof of Theorem 3.1.6.
-/

public section

noncomputable section

open Filter Topology
open scoped ComplexOrder CStarAlgebra

namespace TauCeti

open CompletelyPositiveMap CStarMatrix

variable {A : Type*} [NonUnitalCStarAlgebra A]

section Domain

/-! ### A C⋆-subalgebra from a family of seminorm-like defects -/

variable {ι : Type*} (l : Filter ι)

/-- The elements `a` with `s i a → 0` and `s i a⋆ → 0` along `l`, for a family `s` of nonnegative,
subadditive, homogeneous functions satisfying the product rule. -/
private def domainOf (s : ι → A → ℝ) (hs0 : ∀ i a, 0 ≤ s i a)
    (hadd : ∀ i a b, s i (a + b) ≤ s i a + s i b)
    (hmul : ∀ i a b, s i (a * b) ≤ ‖b‖ * s i a + ‖a‖ * s i b)
    (hsmul : ∀ i (c : ℂ) a, s i (c • a) = ‖c‖ * s i a) : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | Tendsto (s · a) l (𝓝 0) ∧ Tendsto (s · (star a)) l (𝓝 0)}
  zero_mem' := by
    have h (i : ι) : s i 0 = 0 := by simpa using hsmul i 0 0
    simp [h, tendsto_const_nhds]
  add_mem' {a b} ha hb := by
    refine ⟨squeeze_zero (hs0 · _) (hadd · a b) (by simpa using ha.1.add hb.1), ?_⟩
    rw [star_add]
    exact squeeze_zero (hs0 · _) (hadd · _ _) (by simpa using ha.2.add hb.2)
  mul_mem' {a b} ha hb := by
    refine ⟨squeeze_zero (hs0 · _) (hmul · a b) ?_, ?_⟩
    · simpa using (ha.1.const_mul ‖b‖).add (hb.1.const_mul ‖a‖)
    · rw [star_mul]
      exact squeeze_zero (hs0 · _) (hmul · _ _)
        (by simpa using (hb.2.const_mul ‖star a‖).add (ha.2.const_mul ‖star b‖))
  smul_mem' c a ha := by
    refine ⟨?_, ?_⟩
    · simpa [hsmul] using ha.1.const_mul ‖c‖
    · simpa [star_smul, hsmul] using ha.2.const_mul ‖star c‖
  star_mem' {a} ha := ⟨by simpa using ha.2, by simpa using ha.1⟩

private theorem mem_domainOf_iff {s : ι → A → ℝ} {hs0 hadd hmul hsmul} {a : A} :
    a ∈ domainOf l s hs0 hadd hmul hsmul ↔
      Tendsto (s · a) l (𝓝 0) ∧ Tendsto (s · (star a)) l (𝓝 0) :=
  Iff.rfl

private theorem isClosed_domainOf {s : ι → A → ℝ} {hs0 hadd hmul hsmul}
    (hlip : ∀ i, LipschitzWith 1 (s i)) :
    IsClosed (domainOf l s hs0 hadd hmul hsmul : Set A) := by
  have hc := (LipschitzWith.uniformEquicontinuous s 1 hlip).equicontinuous
    |>.isClosed_setOfPred_tendsto (l := l) (continuous_const (y := (0 : ℝ)))
  exact hc.inter (hc.preimage continuous_star)

/-! ### The two asymptotic multiplicative domains -/

variable {l} [PartialOrder A] [StarOrderedRing A] {n : ι → Type*} [∀ i, Fintype (n i)]
  {φ : ∀ i, A →CP CStarMatrix (n i) (n i) ℂ}

/-- The **asymptotic 2-norm multiplicative domain** `D₂` of a family of completely positive
contractions `φᵢ : A → M_{kᵢ}` along a filter `l`: the C⋆-subalgebra of the `a` with
`d₂(φᵢ, a) → 0` and `d₂(φᵢ, a⋆) → 0` (`TauCeti.mem_asymptoticTwoNormDomain_iff`). -/
def asymptoticTwoNormDomain (l : Filter ι) (φ : ∀ i, A →CP CStarMatrix (n i) (n i) ℂ)
    (hφ : ∀ i a, ‖φ i a‖ ≤ ‖a‖) : NonUnitalStarSubalgebra ℂ A :=
  domainOf l (fun i a ↦ √((φ i).twoNormDefect a)) (fun _ _ ↦ Real.sqrt_nonneg _)
    (fun i ↦ sqrt_twoNormDefect_add_le (hφ i)) (fun i ↦ sqrt_twoNormDefect_mul_le (hφ i))
    (fun i c a ↦ by
      rw [twoNormDefect_smul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg c)])

/-- The **asymptotic norm multiplicative domain** `D_∞` of a family of completely positive
contractions `φᵢ : A → M_{kᵢ}` along a filter `l`: the C⋆-subalgebra of the `a` with
`d_∞(φᵢ, a) → 0` and `d_∞(φᵢ, a⋆) → 0` (`TauCeti.mem_asymptoticNormDomain_iff`). -/
def asymptoticNormDomain (l : Filter ι) (φ : ∀ i, A →CP CStarMatrix (n i) (n i) ℂ)
    (hφ : ∀ i a, ‖φ i a‖ ≤ ‖a‖) : NonUnitalStarSubalgebra ℂ A :=
  domainOf l (fun i a ↦ √((φ i).normDefect a)) (fun _ _ ↦ Real.sqrt_nonneg _)
    (fun i ↦ sqrt_normDefect_add_le (hφ i)) (fun i ↦ sqrt_normDefect_mul_le (hφ i))
    (fun i c a ↦ by
      rw [normDefect_smul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg c)])

variable (hφ : ∀ i a, ‖φ i a‖ ≤ ‖a‖)
include hφ

/-- Membership in the asymptotic 2-norm multiplicative domain. -/
@[simp]
theorem mem_asymptoticTwoNormDomain_iff {a : A} :
    a ∈ asymptoticTwoNormDomain l φ hφ ↔
      Tendsto (fun i ↦ (φ i).twoNormDefect a) l (𝓝 0) ∧
        Tendsto (fun i ↦ (φ i).twoNormDefect (star a)) l (𝓝 0) := by
  rw [asymptoticTwoNormDomain, mem_domainOf_iff,
    Real.tendsto_sqrt_nhds_zero_iff (.of_forall fun i ↦ twoNormDefect_nonneg (hφ i) a),
    Real.tendsto_sqrt_nhds_zero_iff (.of_forall fun i ↦ twoNormDefect_nonneg (hφ i) (star a))]

/-- Membership in the asymptotic norm multiplicative domain. -/
@[simp]
theorem mem_asymptoticNormDomain_iff {a : A} :
    a ∈ asymptoticNormDomain l φ hφ ↔
      Tendsto (fun i ↦ (φ i).normDefect a) l (𝓝 0) ∧
        Tendsto (fun i ↦ (φ i).normDefect (star a)) l (𝓝 0) := by
  rw [asymptoticNormDomain, mem_domainOf_iff,
    Real.tendsto_sqrt_nhds_zero_iff (.of_forall fun i ↦ normDefect_nonneg (φ i) a),
    Real.tendsto_sqrt_nhds_zero_iff (.of_forall fun i ↦ normDefect_nonneg (φ i) (star a))]

/-- The asymptotic 2-norm multiplicative domain is closed, so it is a C⋆-subalgebra. -/
theorem isClosed_asymptoticTwoNormDomain :
    IsClosed (asymptoticTwoNormDomain l φ hφ : Set A) :=
  isClosed_domainOf l fun i ↦ .of_le_add fun a b ↦ by
    linarith [abs_le.1 (abs_sqrt_twoNormDefect_sub_le (hφ i) a b), dist_eq_norm a b]

/-- The asymptotic norm multiplicative domain is closed, so it is a C⋆-subalgebra. -/
theorem isClosed_asymptoticNormDomain : IsClosed (asymptoticNormDomain l φ hφ : Set A) :=
  isClosed_domainOf l fun i ↦ .of_le_add fun a b ↦ by
    linarith [abs_le.1 (abs_sqrt_normDefect_sub_le (hφ i) a b), dist_eq_norm a b]

/-- The norm multiplicative domain is contained in the 2-norm multiplicative domain. -/
theorem asymptoticNormDomain_le_asymptoticTwoNormDomain :
    asymptoticNormDomain l φ hφ ≤ asymptoticTwoNormDomain l φ hφ := fun a ha ↦ by
  rw [mem_asymptoticNormDomain_iff] at ha
  rw [mem_asymptoticTwoNormDomain_iff]
  exact ⟨squeeze_zero (fun i ↦ twoNormDefect_nonneg (hφ i) a)
      (fun i ↦ (φ i).twoNormDefect_le_normDefect a) ha.1,
    squeeze_zero (fun i ↦ twoNormDefect_nonneg (hφ i) (star a))
      (fun i ↦ (φ i).twoNormDefect_le_normDefect (star a)) ha.2⟩

/-- **Asymptotic multiplicativity on the 2-norm domain, on the left.** For `a ∈ D₂` and every
`b`, `‖φᵢ(ab) - φᵢ(a)φᵢ(b)‖₂ → 0`. -/
theorem tendsto_normalizedTwoNorm_map_mul_sub_of_mem {a : A}
    (ha : a ∈ asymptoticTwoNormDomain l φ hφ) (b : A) :
    Tendsto (fun i ↦ normalizedTwoNorm (φ i (a * b) - φ i a * φ i b)) l (𝓝 0) :=
  squeeze_zero (fun _ ↦ normalizedTwoNorm_nonneg _)
    (fun i ↦ normalizedTwoNorm_map_mul_sub_le' (hφ i) a b)
    (by simpa using ((mem_asymptoticTwoNormDomain_iff hφ).1 ha).2.sqrt.mul_const ‖b‖)

/-- **Asymptotic multiplicativity on the 2-norm domain, on the right.** For `a ∈ D₂` and every
`b`, `‖φᵢ(ba) - φᵢ(b)φᵢ(a)‖₂ → 0`. -/
theorem tendsto_normalizedTwoNorm_map_mul_sub_of_mem' {a : A}
    (ha : a ∈ asymptoticTwoNormDomain l φ hφ) (b : A) :
    Tendsto (fun i ↦ normalizedTwoNorm (φ i (b * a) - φ i b * φ i a)) l (𝓝 0) :=
  squeeze_zero (fun _ ↦ normalizedTwoNorm_nonneg _)
    (fun i ↦ normalizedTwoNorm_map_mul_sub_le (hφ i) b a)
    (by simpa using ((mem_asymptoticTwoNormDomain_iff hφ).1 ha).1.sqrt.const_mul ‖b‖)

/-- **Asymptotic multiplicativity on the norm domain, on the left.** For `a ∈ D_∞` and every
`b`, `‖φᵢ(ab) - φᵢ(a)φᵢ(b)‖ → 0`. -/
theorem tendsto_norm_map_mul_sub_of_mem {a : A} (ha : a ∈ asymptoticNormDomain l φ hφ) (b : A) :
    Tendsto (fun i ↦ ‖φ i (a * b) - φ i a * φ i b‖) l (𝓝 0) :=
  squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ norm_map_mul_sub_le' (hφ i) a b)
    (by simpa using ((mem_asymptoticNormDomain_iff hφ).1 ha).2.sqrt.mul_const ‖b‖)

/-- **Asymptotic multiplicativity on the norm domain, on the right.** For `a ∈ D_∞` and every
`b`, `‖φᵢ(ba) - φᵢ(b)φᵢ(a)‖ → 0`. -/
theorem tendsto_norm_map_mul_sub_of_mem' {a : A} (ha : a ∈ asymptoticNormDomain l φ hφ) (b : A) :
    Tendsto (fun i ↦ ‖φ i (b * a) - φ i b * φ i a‖) l (𝓝 0) :=
  squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ norm_map_mul_sub_le (hφ i) b a)
    (by simpa using ((mem_asymptoticNormDomain_iff hφ).1 ha).1.sqrt.const_mul ‖b‖)

/-- **The generating-set criterion in 2-norm.** If `‖φᵢ(s⋆s) - φᵢ(s⋆)φᵢ(s)‖₂ → 0` and
`‖φᵢ(ss⋆) - φᵢ(s)φᵢ(s⋆)‖₂ → 0` for every `s` in a set `S` generating `A` as a C⋆-algebra, then
`‖φᵢ(ab) - φᵢ(a)φᵢ(b)‖₂ → 0` for all `a, b ∈ A`. -/
theorem tendsto_normalizedTwoNorm_map_mul_sub_of_adjoin {S : Set A}
    (hS : (NonUnitalStarAlgebra.adjoin ℂ S).topologicalClosure = ⊤)
    (hS₁ : ∀ s ∈ S,
      Tendsto (fun i ↦ normalizedTwoNorm (φ i (star s * s) - φ i (star s) * φ i s)) l (𝓝 0))
    (hS₂ : ∀ s ∈ S,
      Tendsto (fun i ↦ normalizedTwoNorm (φ i (s * star s) - φ i s * φ i (star s))) l (𝓝 0))
    (a b : A) :
    Tendsto (fun i ↦ normalizedTwoNorm (φ i (a * b) - φ i a * φ i b)) l (𝓝 0) := by
  refine tendsto_normalizedTwoNorm_map_mul_sub_of_mem hφ ?_ b
  have hle : (NonUnitalStarAlgebra.adjoin ℂ S).topologicalClosure ≤
      asymptoticTwoNormDomain l φ hφ := by
    refine NonUnitalStarSubalgebra.topologicalClosure_minimal _ (NonUnitalStarAlgebra.adjoin_le
      fun s hs ↦ ?_) (isClosed_asymptoticTwoNormDomain hφ)
    rw [SetLike.mem_coe, mem_asymptoticTwoNormDomain_iff]
    refine ⟨squeeze_zero (fun i ↦ twoNormDefect_nonneg (hφ i) s)
        (fun i ↦ (φ i).twoNormDefect_le_normalizedTwoNorm s) (hS₁ s hs),
      squeeze_zero (fun i ↦ twoNormDefect_nonneg (hφ i) (star s))
        (fun i ↦ (φ i).twoNormDefect_le_normalizedTwoNorm (star s)) ?_⟩
    simpa using hS₂ s hs
  exact hle (by rw [hS]; exact NonUnitalStarAlgebra.mem_top)

/-- **The generating-set criterion in norm.** If `‖φᵢ(s⋆s) - φᵢ(s⋆)φᵢ(s)‖ → 0` and
`‖φᵢ(ss⋆) - φᵢ(s)φᵢ(s⋆)‖ → 0` for every `s` in a set `S` generating `A` as a C⋆-algebra, then
`‖φᵢ(ab) - φᵢ(a)φᵢ(b)‖ → 0` for all `a, b ∈ A`. -/
theorem tendsto_norm_map_mul_sub_of_adjoin {S : Set A}
    (hS : (NonUnitalStarAlgebra.adjoin ℂ S).topologicalClosure = ⊤)
    (hS₁ : ∀ s ∈ S, Tendsto (fun i ↦ ‖φ i (star s * s) - φ i (star s) * φ i s‖) l (𝓝 0))
    (hS₂ : ∀ s ∈ S, Tendsto (fun i ↦ ‖φ i (s * star s) - φ i s * φ i (star s)‖) l (𝓝 0))
    (a b : A) :
    Tendsto (fun i ↦ ‖φ i (a * b) - φ i a * φ i b‖) l (𝓝 0) := by
  refine tendsto_norm_map_mul_sub_of_mem hφ ?_ b
  have hle : (NonUnitalStarAlgebra.adjoin ℂ S).topologicalClosure ≤
      asymptoticNormDomain l φ hφ := by
    refine NonUnitalStarSubalgebra.topologicalClosure_minimal _ (NonUnitalStarAlgebra.adjoin_le
      fun s hs ↦ ?_) (isClosed_asymptoticNormDomain hφ)
    rw [SetLike.mem_coe, mem_asymptoticNormDomain_iff]
    refine ⟨by simpa [normDefect_eq_norm_map_star] using hS₁ s hs, ?_⟩
    simpa [normDefect_eq_norm_map_star] using hS₂ s hs
  exact hle (by rw [hS]; exact NonUnitalStarAlgebra.mem_top)

end Domain

end TauCeti
