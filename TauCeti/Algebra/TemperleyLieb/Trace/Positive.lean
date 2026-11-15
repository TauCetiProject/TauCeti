/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import TauCeti.RingTheory.TraceFunctional.Positive

/-!
# Positive Markov traces, Jones quotients, and the pullback criterion

At a real loop parameter `δ`, `TauCeti.Algebra.TemperleyLieb.Positivity` determines when the
Hermitian forms `H_n(x, y) = tr n (x⋆ * y)` of a Markov trace on `TemperleyLieb ℂ (δ : ℂ) n` are
positive semidefinite: on all numbers of strands for `δ ∈ jonesLoopParameters`, and below the
first bad level `n < ⌊π / arccos (δ / 2)⌋` for any real `δ`. This file bundles admissible Markov
traces as `TauCeti.StarPositiveFunctional`s and develops the normalized faithful traces on the
positive Jones quotients together with the pullback criteria for star representations into operator
or tower algebras:

1. **Positive trace functionals.** For `δ ∈ jonesLoopParameters`,
   `IsMarkovTrace.starPositiveFunctional` packages `tr n` as a `TauCeti.StarPositiveFunctional`,
   making the generic trace-radical and unnormalized quotient-trace API of
   `TauCeti.RingTheory.TraceFunctional.Positive` directly available (in particular
   `StarPositiveFunctional.mem_traceRadical_iff_apply_star_mul_self_eq_zero` and
   `(htr.starPositiveFunctional hδ n).quotientTrace (htr.map_mul_comm n)`).
2. **Normalized positive traces on the Jones quotients.** For `δ ∈ jonesLoopParameters`, the
   quotient `Q_n = TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical` carries the normalized
   faithful positive trace `normalizedPositiveQuotientTrace` (`= δ⁻ⁿ • quotientTrace`), which is
   preserved on the nose by the injective `⋆`-homomorphisms `quotientStrandInclStarAlgHom` and
   satisfies the normalized Markov identity with factor `(δ ^ 2)⁻¹` on
   `δ⁻¹ • e (Fin.last n)`.
3. **Pullback criteria and representation kernels.** If `δ > 0` and compatible `⋆`-homomorphisms
   `ρ_n : TemperleyLieb ℂ (δ : ℂ) n →⋆ₐ[ℂ] B_n` pull positive functionals `σ_n` back to
   `δ⁻ⁿ • tr n` (or satisfy the normalized tower Markov identities directly, without assuming an
   ambient `tr` or injectivity of `ρ_n`), then `δ ∈ jonesLoopParameters`. For any nonzero
   self-adjoint `δ : ℂ`, when `σ` has trivial GNS null space, `RingHom.ker ρ` equals the trace
   radical `(tr n).traceRadical`.

## Main definitions

* `TauCeti.TemperleyLieb.IsMarkovTrace.starPositiveFunctional`: `tr n` bundled as a
  `StarPositiveFunctional` at an admissible loop parameter `δ ∈ jonesLoopParameters`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.normalizedPositiveQuotientTrace`: the normalized faithful
  positive trace `δ⁻ⁿ • tr n` on the Jones quotients `TemperleyLieb ℂ (δ : ℂ) n ⧸ R_n`.

## Main results

* `TauCeti.TemperleyLieb.IsMarkovTrace.normalizedPositiveQuotientTrace_quotientStrandIncl`,
  `IsMarkovTrace.normalizedPositiveQuotientTrace_quotientStrandIncl_mul_mk_inv_smul_e_last`:
  strand invariance and the `(δ ^ 2)⁻¹` Markov formula on the positive Jones quotients.
* `TauCeti.TemperleyLieb.IsMarkovTrace.mem_jonesLoopParameters_of_pullback`,
  `TauCeti.TemperleyLieb.mem_jonesLoopParameters_of_tower_pullback`: the pullback criteria forcing
  `δ ∈ jonesLoopParameters` without injectivity of `ρ_n`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.ker_eq_traceRadical_of_pullback`: `ker ρ = R_n` for a
  nonzero self-adjoint loop parameter and a faithful target functional.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones and V. S. Sunder, *Introduction to Subfactors*, LMS Lecture Note Series 234,
  Cambridge University Press, 1997, Theorem 2.3.8.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, §§4.3–4.5.
-/

public section

noncomputable section

open Real
open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

section PositiveForm

variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
  {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

namespace IsMarkovTrace

/-- At an admissible loop parameter `δ ∈ jonesLoopParameters`, the Markov trace on `n` strands as
a `TauCeti.StarPositiveFunctional`. -/
-- `@[expose]` lets downstream consumers apply `StarPositiveFunctional.quotientTrace` and
-- `StarPositiveFunctional.mem_traceRadical_iff_apply_star_mul_self_eq_zero` directly on
-- `(tr n).traceRadical (htr.map_mul_comm n)` without a dependent-type mismatch on `toLinearMap`.
@[expose]
def starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters)
    (n : ℕ) : StarPositiveFunctional (TemperleyLieb ℂ (δ : ℂ) n) where
  toLinearMap := tr n
  square_nonneg x :=
    (htr.forall_map_star_mul_self_nonneg_iff (pos_of_mem_jonesLoopParameters hδ)).2 hδ n x

/-- Evaluating `starPositiveFunctional` gives `tr n`. -/
@[simp]
theorem starPositiveFunctional_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.starPositiveFunctional hδ n x = tr n x :=
  (rfl)

/-- Forgetting positivity recovers `tr n`. -/
@[simp]
theorem toLinearMap_starPositiveFunctional (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) :
    (htr.starPositiveFunctional hδ n).toLinearMap = tr n :=
  (rfl)

section Quotient

/-- At an admissible loop parameter, the normalized faithful positive trace `δ⁻ⁿ • tr n` on the
Jones quotient `TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical`. Unlike the unnormalized trace
`(htr.starPositiveFunctional hδ n).quotientTrace (htr.map_mul_comm n)`, it takes the value `1` at
the identity and is preserved on the nose by strand inclusion. -/
def normalizedPositiveQuotientTrace (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    StarPositiveFunctional
      (TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) where
  toLinearMap := ((δ : ℂ)⁻¹ ^ n) • (tr n).quotientTrace (htr.map_mul_comm n)
  square_nonneg x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hδ0 : 0 ≤ (((δ⁻¹) ^ n : ℝ) : ℂ) :=
      Complex.zero_le_real.2 (pow_nonneg (inv_nonneg.2 (pos_of_mem_jonesLoopParameters hδ).le) n)
    have hcast : ((δ : ℂ)⁻¹) ^ n = (((δ⁻¹) ^ n : ℝ) : ℂ) := by simp
    simpa only [LinearMap.smul_apply, smul_eq_mul, Ideal.Quotient.star_mk, ← map_mul,
      LinearMap.quotientTrace_mk, hcast, toLinearMap_starPositiveFunctional] using
      mul_nonneg hδ0 ((htr.starPositiveFunctional hδ n).square_nonneg a)

/-- Forgetting positivity recovers the rescaled algebraic quotient trace. -/
@[simp]
theorem toLinearMap_normalizedPositiveQuotientTrace (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    (htr.normalizedPositiveQuotientTrace hδ n).toLinearMap =
      ((δ : ℂ)⁻¹ ^ n) • (tr n).quotientTrace (htr.map_mul_comm n) :=
  (rfl)

/-- Evaluating `normalizedPositiveQuotientTrace` rescales the quotient trace by `δ⁻ⁿ`. -/
theorem normalizedPositiveQuotientTrace_apply (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x : TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.normalizedPositiveQuotientTrace hδ n x =
      ((δ : ℂ)⁻¹) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) x :=
  (rfl)

/-- Evaluating `normalizedPositiveQuotientTrace` on a quotient class rescales `tr n` by `δ⁻ⁿ`. -/
@[simp]
theorem normalizedPositiveQuotientTrace_mk (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (a : TemperleyLieb ℂ (δ : ℂ) n) :
    htr.normalizedPositiveQuotientTrace hδ n
      (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) a) =
      ((δ : ℂ)⁻¹) ^ n * tr n a := by
  rw [htr.normalizedPositiveQuotientTrace_apply, LinearMap.quotientTrace_mk]

/-- The normalized positive quotient trace takes the value `1` at the identity. -/
@[simp]
theorem normalizedPositiveQuotientTrace_one (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    htr.normalizedPositiveQuotientTrace hδ n 1 = 1 := by
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ).ne'
  rw [htr.normalizedPositiveQuotientTrace_apply, LinearMap.quotientTrace_one, htr.map_one, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero n hδ0)]

/-- The normalized positive quotient trace is tracial. -/
theorem normalizedPositiveQuotientTrace_mul_comm (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x y : TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.normalizedPositiveQuotientTrace hδ n (x * y) =
      htr.normalizedPositiveQuotientTrace hδ n (y * x) := by
  simp only [htr.normalizedPositiveQuotientTrace_apply, LinearMap.quotientTrace_mul_comm]

/-- A square in the positive Jones quotient has zero normalized trace if and only if its argument
vanishes. -/
@[simp]
theorem normalizedPositiveQuotientTrace_star_mul_self_eq_zero_iff
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr n).traceRadical (htr.map_mul_comm n)).IsStar]
    (x : TemperleyLieb ℂ (δ : ℂ) n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    htr.normalizedPositiveQuotientTrace hδ n (star x * x) = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hδ0 : (δ : ℂ)⁻¹ ^ n ≠ 0 :=
    pow_ne_zero n (inv_ne_zero (Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ).ne'))
  rw [Ideal.Quotient.star_mk, ← map_mul, htr.normalizedPositiveQuotientTrace_mk, mul_eq_zero,
    or_iff_right hδ0, Ideal.Quotient.eq_zero_iff_mem]
  exact ((htr.starPositiveFunctional hδ n).mem_traceRadical_iff_apply_star_mul_self_eq_zero
    (htr.map_mul_comm n) a).symm

/-- The normalized positive quotient trace has trivial GNS null space. -/
theorem nullSubmodule_normalizedPositiveQuotientTrace (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ) [((tr n).traceRadical (htr.map_mul_comm n)).IsStar] :
    (htr.normalizedPositiveQuotientTrace hδ n).nullSubmodule = ⊥ := by
  ext x
  simp only [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero,
    htr.normalizedPositiveQuotientTrace_star_mul_self_eq_zero_iff hδ n, Submodule.mem_bot]

/-- The normalized positive quotient trace is preserved by the strand inclusion between Jones
quotients. -/
@[simp]
theorem normalizedPositiveQuotientTrace_quotientStrandIncl (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar]
    (x : TemperleyLieb ℂ (δ : ℂ) (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.normalizedPositiveQuotientTrace hδ (n + 2) (htr.quotientStrandIncl n x) =
      htr.normalizedPositiveQuotientTrace hδ (n + 1) x := by
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pos_of_mem_jonesLoopParameters hδ).ne'
  rw [htr.normalizedPositiveQuotientTrace_apply, htr.normalizedPositiveQuotientTrace_apply,
    htr.quotientTrace_quotientStrandIncl, pow_succ ((δ : ℂ)⁻¹) (n + 1), mul_assoc,
    inv_mul_cancel_left₀ hδ0]

/-- Pulling `normalizedPositiveQuotientTrace` back along `quotientStrandInclStarAlgHom` recovers
`normalizedPositiveQuotientTrace` one strand lower. -/
@[simp]
theorem normalizedPositiveQuotientTrace_comp_quotientStrandInclStarAlgHom
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar] :
    (htr.normalizedPositiveQuotientTrace hδ (n + 2)).comp (htr.quotientStrandInclStarAlgHom n) =
      htr.normalizedPositiveQuotientTrace hδ (n + 1) := by
  ext x
  simp

/-- The **normalized Markov formula** on the positive Jones quotients: multiplying an included
element by the rescaled last generator `δ⁻¹ • e (Fin.last n)` scales the normalized trace by
`(δ ^ 2)⁻¹`. -/
theorem normalizedPositiveQuotientTrace_quotientStrandIncl_mul_mk_inv_smul_e_last
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : δ ∈ jonesLoopParameters) (n : ℕ)
    [((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))).IsStar]
    [((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))).IsStar]
    (x : TemperleyLieb ℂ (δ : ℂ) (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.normalizedPositiveQuotientTrace hδ (n + 2)
      (htr.quotientStrandIncl n x *
        Ideal.Quotient.mk ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))
          ((δ : ℂ)⁻¹ • e (δ : ℂ) (Fin.last n))) =
      ((δ : ℂ) ^ 2)⁻¹ * htr.normalizedPositiveQuotientTrace hδ (n + 1) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [htr.quotientStrandIncl_mk, ← map_mul, htr.normalizedPositiveQuotientTrace_mk,
    mul_smul_comm, map_smul, smul_eq_mul, htr.map_strandIncl_mul_e_last]
  ring

end Quotient

/-- **Pullback criterion for admissibility.** Let `δ > 0`, and suppose that for every `n` there is
a `⋆`-homomorphism `ρ n` from `TemperleyLieb ℂ (δ : ℂ) n` into a complex `⋆`-algebra `B n`
carrying a positive functional `σ n` such that `σ n (ρ n x) = δ⁻ⁿ * tr n x`. Then
`δ ∈ jonesLoopParameters`. Neither injectivity of `ρ n` nor traciality of `σ n` on `B n` is
required. -/
theorem mem_jonesLoopParameters_of_pullback (htr : IsMarkovTrace ℂ (δ : ℂ) tr) (hδ : 0 < δ)
    {B : ℕ → Type*} [∀ n, NonUnitalRing (B n)] [∀ n, Module ℂ (B n)] [∀ n, StarRing (B n)]
    {F : ℕ → Type*} [∀ n, FunLike (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, NonUnitalAlgHomClass (F n) ℂ (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, StarHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    (σ : ∀ n, StarPositiveFunctional (B n)) (ρ : ∀ n, F n)
    (hpull : ∀ n (x : TemperleyLieb ℂ (δ : ℂ) n), σ n (ρ n x) = ((δ : ℂ)⁻¹) ^ n * tr n x) :
    δ ∈ jonesLoopParameters := by
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ.ne'
  refine htr.mem_jonesLoopParameters_of_forall_nonneg hδ fun n x ↦ ?_
  have hval : tr n (star x * x) = (((δ ^ n : ℝ) : ℂ)) * ((σ n).comp (ρ n)) (star x * x) := by
    rw [StarPositiveFunctional.comp_apply, hpull, Complex.ofReal_pow, ← mul_assoc, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero n hδ0), one_mul]
  rw [hval]
  exact mul_nonneg (Complex.zero_le_real.2 (pow_nonneg hδ.le n))
    (((σ n).comp (ρ n)).square_nonneg x)

end IsMarkovTrace

end PositiveForm

section Kernel

/-- If `δ : ℂ` is a nonzero self-adjoint loop parameter and a `⋆`-algebra homomorphism
`ρ : TemperleyLieb ℂ δ n →⋆ₐ[ℂ] B` pulls back a positive functional `σ` with trivial GNS null space
to `δ⁻ⁿ • tr n`, then `RingHom.ker ρ` equals the trace radical of `tr n`. Surjectivity of `ρ` and
traciality of `σ` on `B` are not required. -/
theorem IsMarkovTrace.ker_eq_traceRadical_of_pullback {δ : ℂ} [Fact (IsSelfAdjoint δ)]
    {tr : ∀ n : ℕ, TemperleyLieb ℂ δ n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ δ tr) (hδ : δ ≠ 0) {n : ℕ}
    {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (σ : StarPositiveFunctional B) (hσ : σ.nullSubmodule = ⊥)
    (ρ : TemperleyLieb ℂ δ n →⋆ₐ[ℂ] B)
    (hpull : ∀ x : TemperleyLieb ℂ δ n, σ (ρ x) = (δ⁻¹) ^ n * tr n x) :
    RingHom.ker ρ = (tr n).traceRadical (htr.map_mul_comm n) := by
  have hcomm (x y : TemperleyLieb ℂ δ n) :
      ((δ⁻¹ ^ n) • tr n) (x * y) = ((δ⁻¹ ^ n) • tr n) (y * x) := by
    simp [htr.map_mul_comm n x y]
  rw [← ((δ⁻¹ ^ n) • tr n).traceRadical_eq_ker_of_nullSubmodule_eq_bot hcomm σ hσ ρ hpull]
  ext x
  simp [hδ]

end Kernel

section TowerPullback

/-- **Tower pullback criterion.** Let `δ > 0`, and suppose that for every `n` there is a unital
`⋆`-algebra homomorphism `ρ n` from `TemperleyLieb ℂ (δ : ℂ) n` into a complex `⋆`-algebra `B n`
carrying a normalized positive functional `σ n` (`σ n 1 = 1`) that is tracial on the image of
`ρ n`, compatible with `strandIncl`, and satisfies
`δ * σ (n + 2) (ρ (n + 2) (strandIncl x * e _ (Fin.last n))) = σ (n + 1) (ρ (n + 1) x)`. Then
`δ ∈ jonesLoopParameters`, so `δ ^ 2` lies in the Jones index set
`{4 cos² (π / m) : m ≥ 3} ∪ [4, ∞)`. Injectivity of `ρ n` is not required. -/
theorem mem_jonesLoopParameters_of_tower_pullback {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))]
    (hδ : 0 < δ) {B : ℕ → Type*} [∀ n, Ring (B n)] [∀ n, Algebra ℂ (B n)] [∀ n, StarRing (B n)]
    {F : ℕ → Type*} [∀ n, FunLike (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, AlgHomClass (F n) ℂ (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    [∀ n, StarHomClass (F n) (TemperleyLieb ℂ (δ : ℂ) n) (B n)]
    (σ : ∀ n, StarPositiveFunctional (B n)) (ρ : ∀ n, F n) (hone : ∀ n, σ n 1 = 1)
    (hcomm : ∀ n (x y : TemperleyLieb ℂ (δ : ℂ) n), σ n (ρ n x * ρ n y) = σ n (ρ n y * ρ n x))
    (hincl : ∀ n (x : TemperleyLieb ℂ (δ : ℂ) (n + 1)),
      σ (n + 2) (ρ (n + 2) (strandIncl x)) = σ (n + 1) (ρ (n + 1) x))
    (hmarkov : ∀ n (x : TemperleyLieb ℂ (δ : ℂ) (n + 1)),
      (δ : ℂ) * σ (n + 2) (ρ (n + 2) (strandIncl x * e (δ : ℂ) (Fin.last n))) =
        σ (n + 1) (ρ (n + 1) x)) :
    δ ∈ jonesLoopParameters := by
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hδ.ne'
  have htr : IsMarkovTrace ℂ (δ : ℂ) (fun n ↦ ((δ : ℂ) ^ n) • ((σ n).comp (ρ n)).toLinearMap) :=
    isMarkovTrace_pow_smul (σ := fun n ↦ ((σ n).comp (ρ n)).toLinearMap)
      (fun n ↦ by simp [hone]) (fun n x y ↦ by simp [hcomm]) (fun n x ↦ by simp [hincl])
      (fun n x ↦ by
        simpa only [StarPositiveFunctional.toLinearMap_apply,
          StarPositiveFunctional.comp_apply] using hmarkov n x)
  refine htr.mem_jonesLoopParameters_of_pullback hδ σ ρ fun n x ↦ ?_
  simp only [LinearMap.smul_apply, StarPositiveFunctional.toLinearMap_apply,
    StarPositiveFunctional.comp_apply, smul_eq_mul, ← mul_assoc, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero n hδ0), one_mul]

end TowerPullback

end TauCeti.TemperleyLieb
