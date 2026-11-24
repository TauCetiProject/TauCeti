/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.MeasureTheory.Constructions.Pi
public import TauCeti.Statistics.Estimation.Unbiased
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Probability.HasLaw
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# U-statistics

For a kernel `h : (Fin m → E) → ℝ` of `m` arguments and a sample `x : Fin n → E`, the
U-statistic `uStatistic m n h x` is the average of `h (x ∘ f)` over the `n.descFactorial m`
injections `f : Fin m → Fin n`, that is, over the ordered `m`-tuples of distinct sample indices;
the observations at those indices may coincide. It does not depend on the order of the
observations, and it is linear in the kernel. Under an i.i.d. sample of size `n ≥ m` from a law
`P`, and for a kernel `h` integrable under `Pᵐ`, it is an unbiased estimator of `∫ h d(Pᵐ)`:
the coordinates of `x` selected by an injection are again i.i.d. with law `P`, so each selected
tuple `x ∘ f` has law `Pᵐ` and each summand `h (x ∘ f)` has mean `∫ h d(Pᵐ)`.

For `m = 1` the U-statistic is the sample mean of `h`. If `n < m` there are no injections and
the U-statistic is `0`; for `m = 0` it is the constant value of `h` at the empty tuple.

## Main definitions

* `TauCeti.uStatistic m n h x`: the U-statistic of order `m` with kernel `h`.

## Main results

* `TauCeti.uStatistic_eq_sum_embedding`: the U-statistic as an average over embeddings
  `Fin m ↪ Fin n`.
* `TauCeti.uStatistic_comp_perm`: the U-statistic is a symmetric function of the sample.
* `TauCeti.uStatistic_eq_expect`: the same as a finite average `𝔼 f, h (x ∘ f)`.
* `TauCeti.uStatistic_one`: for `m = 1` it is the average `𝔼 i, h (x i)`, the sample mean of `h`
  for `0 < n` (and `0` for the empty sample).
* `TauCeti.uStatistic_add`, `TauCeti.uStatistic_sub`, `TauCeti.uStatistic_neg`,
  `TauCeti.uStatistic_smul`, `TauCeti.uStatistic_sum`, `TauCeti.uStatistic_zero_kernel`,
  `TauCeti.uStatistic_const`: the U-statistic is linear in the kernel, and for `m ≤ n` a constant
  kernel gives that constant.
* `TauCeti.integrable_uStatistic`: under a finite law `P`, the U-statistic of a `Pᵐ`-integrable
  kernel is `Pⁿ`-integrable.
* `TauCeti.integral_uStatistic`: for a probability measure `P`, `m ≤ n` and `h` integrable under
  `Pᵐ`, the mean of the U-statistic under `Pⁿ` is `∫ h d(Pᵐ)`.
* `TauCeti.isUnbiasedEstimator_uStatistic`: the same statement for a parametric family, in terms
  of `TauCeti.IsUnbiasedEstimator`.

The definition is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Asymptotics/Basic.lean`, and the measure-preservation argument for unbiasedness from
`CKSD/Asymptotics/UStatistics/Projection.lean`.

## References

* W. Hoeffding, *A class of statistics with asymptotically normal distribution*, Ann. Math.
  Statist. 19 (1948), 293–325.
* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter (1994), Section 3.2.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace TauCeti

/-- The U-statistic of order `m` with kernel `h`: the average of `h (x ∘ f)` over the
injections `f : Fin m → Fin n`. It is `0` when `n < m`, since there are no injections. -/
def uStatistic {E : Type*} (m n : ℕ) (h : (Fin m → E) → ℝ) (x : Fin n → E) : ℝ :=
  ((n.descFactorial m : ℕ) : ℝ)⁻¹ *
    ∑ f ∈ (Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective, h (x ∘ f)

variable {E : Type*} {m n : ℕ}

/-- The defining formula of `uStatistic`. -/
theorem uStatistic_def (m n : ℕ) (h : (Fin m → E) → ℝ) (x : Fin n → E) :
    uStatistic m n h x = ((n.descFactorial m : ℕ) : ℝ)⁻¹ *
      ∑ f ∈ (Finset.univ : Finset (Fin m → Fin n)).filter Function.Injective, h (x ∘ f) := by
  rw [uStatistic]

/-- The U-statistic as the average of `h (x ∘ f)` over the embeddings `f : Fin m ↪ Fin n`. -/
theorem uStatistic_eq_sum_embedding (m n : ℕ) (h : (Fin m → E) → ℝ) (x : Fin n → E) :
    uStatistic m n h x = ((n.descFactorial m : ℕ) : ℝ)⁻¹ * ∑ f : Fin m ↪ Fin n, h (x ∘ f) := by
  rw [uStatistic_def, Finset.sum_subtype (p := Function.Injective) _ (fun _ ↦ by simp)]
  exact congrArg _ (Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin m) (Fin n)) _ _
    fun _ ↦ rfl)

/-- The U-statistic as the finite average `𝔼 f, h (x ∘ f)` over the embeddings
`f : Fin m ↪ Fin n`; there are `n.descFactorial m` of them (`Fintype.card_embedding_eq`). For
`n < m` there are none, and both sides are `0`. -/
theorem uStatistic_eq_expect (m n : ℕ) (h : (Fin m → E) → ℝ) (x : Fin n → E) :
    uStatistic m n h x = 𝔼 f : Fin m ↪ Fin n, h (x ∘ f) := by
  rw [uStatistic_eq_sum_embedding, Fintype.expect_eq_sum_div_card, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fin, div_eq_inv_mul]

/-- With fewer observations than arguments of the kernel there are no injections, and the
U-statistic is `0`. -/
@[simp]
theorem uStatistic_of_lt (h : (Fin m → E) → ℝ) (x : Fin n → E) (hnm : n < m) :
    uStatistic m n h x = 0 := by
  simp [uStatistic_def, Nat.descFactorial_eq_zero_iff_lt.2 hnm]

/-- The U-statistic of order `0` is the value of `h` at the empty tuple. -/
@[simp]
theorem uStatistic_zero (n : ℕ) (h : (Fin 0 → E) → ℝ) (x : Fin n → E) :
    uStatistic 0 n h x = h Fin.elim0 := by
  simp only [uStatistic_eq_sum_embedding, Nat.descFactorial_zero, Nat.cast_one, inv_one, one_mul]
  rw [Fintype.sum_unique]
  exact congrArg h (Subsingleton.elim _ _)

/-- **Symmetry.** The U-statistic does not depend on the order of the observations. -/
@[simp]
theorem uStatistic_comp_perm (h : (Fin m → E) → ℝ) (x : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    uStatistic m n h (x ∘ σ) = uStatistic m n h x := by
  rw [uStatistic_eq_expect, uStatistic_eq_expect]
  exact Fintype.expect_equiv ((Equiv.refl _).embeddingCongr σ) _ _ fun _ ↦ rfl

/-- **The sample mean.** The U-statistic of order `1` is the finite average `𝔼 i, h (x i)` of
`h` over the observations (with `h` read on one-element tuples). For `0 < n` this is the sample
mean of `h`; for the empty sample, `n = 0`, both sides are `0`. -/
theorem uStatistic_one (h : (Fin 1 → E) → ℝ) (x : Fin n → E) :
    uStatistic 1 n h x = 𝔼 i, h (fun _ ↦ x i) := by
  rw [uStatistic_eq_expect]
  refine Fintype.expect_equiv Equiv.embeddingUnique _ _ fun f ↦ ?_
  exact congrArg h (funext fun j ↦ congrArg (x ∘ f) (Subsingleton.elim j default))

/-- The U-statistic is additive in the kernel. -/
@[simp]
theorem uStatistic_add (h₁ h₂ : (Fin m → E) → ℝ) (x : Fin n → E) :
    uStatistic m n (h₁ + h₂) x = uStatistic m n h₁ x + uStatistic m n h₂ x := by
  simp only [uStatistic_eq_expect, Pi.add_apply, Finset.expect_add_distrib]

/-- The U-statistic of a difference of kernels is the difference of the U-statistics. -/
@[simp]
theorem uStatistic_sub (h₁ h₂ : (Fin m → E) → ℝ) (x : Fin n → E) :
    uStatistic m n (h₁ - h₂) x = uStatistic m n h₁ x - uStatistic m n h₂ x := by
  simp only [uStatistic_eq_expect, Pi.sub_apply, Finset.expect_sub_distrib]

/-- The U-statistic of the negated kernel is the negated U-statistic. -/
@[simp]
theorem uStatistic_neg (h : (Fin m → E) → ℝ) (x : Fin n → E) :
    uStatistic m n (-h) x = -uStatistic m n h x := by
  simp only [uStatistic_eq_expect, Pi.neg_apply, Finset.expect_neg_distrib]

/-- The U-statistic of the zero kernel is `0`, for every sample size. -/
@[simp]
theorem uStatistic_zero_kernel (x : Fin n → E) :
    uStatistic m n (0 : (Fin m → E) → ℝ) x = 0 := by
  simp only [uStatistic_eq_expect, Pi.zero_apply, Finset.expect_const_zero]

/-- The U-statistic of a finite sum of kernels is the sum of their U-statistics. This is the
rule the Hoeffding decomposition uses on a kernel written as a sum of its projections. -/
@[simp]
theorem uStatistic_sum {κ : Type*} (s : Finset κ) (h : κ → (Fin m → E) → ℝ) (x : Fin n → E) :
    uStatistic m n (∑ i ∈ s, h i) x = ∑ i ∈ s, uStatistic m n (h i) x := by
  simp only [uStatistic_eq_expect, Finset.sum_apply, Finset.expect_sum_comm]

/-- The U-statistic is homogeneous in the kernel. -/
@[simp]
theorem uStatistic_smul (c : ℝ) (h : (Fin m → E) → ℝ) (x : Fin n → E) :
    uStatistic m n (c • h) x = c * uStatistic m n h x := by
  simp only [uStatistic_eq_expect, Pi.smul_apply, smul_eq_mul, Finset.mul_expect]

/-- For `m ≤ n` the U-statistic of a constant kernel is that constant: it averages
`n.descFactorial m` copies of it. -/
@[simp]
theorem uStatistic_const (hmn : m ≤ n) (c : ℝ) (x : Fin n → E) :
    uStatistic m n (fun _ ↦ c) x = c := by
  have : Nonempty (Fin m ↪ Fin n) := Fin.nonempty_embedding_iff.2 hmn
  rw [uStatistic_eq_expect, Fintype.expect_const]

variable [MeasurableSpace E]

/-- The U-statistic of a measurable kernel is measurable. -/
@[fun_prop]
theorem measurable_uStatistic {h : (Fin m → E) → ℝ} (hh : Measurable h) :
    Measurable (uStatistic m n h) := by
  refine funext (uStatistic_eq_sum_embedding m n h) ▸ ?_
  exact measurable_const.mul
    (Finset.measurable_sum _ fun f _ ↦ hh.comp (by fun_prop))

/-- For a finite measure `P` on `E`, if the kernel is integrable under `Pᵐ`, then the U-statistic
is integrable under `Pⁿ`. -/
theorem integrable_uStatistic (P : Measure E) [IsFiniteMeasure P] {h : (Fin m → E) → ℝ}
    (hh : Integrable h (Measure.pi fun _ : Fin m ↦ P)) :
    Integrable (uStatistic m n h) (Measure.pi fun _ : Fin n ↦ P) := by
  rcases eq_zero_or_neZero P with rfl | hP
  · -- For `P = 0` the sample space carries the zero measure, or is a point if `n = 0`.
    rcases n with _ | n
    · exact (integrable_const (uStatistic m 0 h Fin.elim0)).congr
        (.of_forall fun x ↦ congrArg _ (Subsingleton.elim _ _))
    · have h0 : (Measure.pi fun _ : Fin (n + 1) ↦ (0 : Measure E)) = 0 :=
        Measure.measure_univ_eq_zero.1 (by simp [Measure.pi_univ])
      rw [h0]
      exact integrable_zero_measure
  -- Otherwise normalize `P` to the probability measure `Q`; this rescales `Pᵏ` by a positive
  -- finite constant, which changes no integrability.
  -- `Q` is Mathlib's normalization `(P univ)⁻¹ • P`, written with an `ℝ≥0` scalar for
  -- `Measure.pi_smul`.
  have hP0 := (measureUnivNNReal_pos (NeZero.ne P)).ne'
  set Q := (measureUnivNNReal P)⁻¹ • P with hQ_def
  have hQP : Q = (P Set.univ)⁻¹ • P := by
    rw [hQ_def, ENNReal.smul_def, ENNReal.coe_inv hP0, coe_measureUnivNNReal]
  have : IsProbabilityMeasure Q := hQP ▸ inferInstance
  have hQ (k : ℕ) (f : (Fin k → E) → ℝ) :
      Integrable f (Measure.pi fun _ ↦ Q) ↔ Integrable f (Measure.pi fun _ ↦ P) := by
    rw [Measure.pi_smul, ENNReal.smul_def, integrable_smul_measure (by simp [hP0]) (by simp)]
  rw [← hQ] at hh ⊢
  refine funext (uStatistic_eq_expect m n h) ▸ integrable_expect fun f _ ↦ ?_
  exact (measurePreserving_pi_comp_embedding (fun _ ↦ Q) f).integrable_comp_of_integrable hh

/-- **Unbiasedness.** Under an i.i.d. sample of size `n ≥ m` from `P`, the U-statistic with a
`Pᵐ`-integrable kernel `h` has mean `∫ h d(Pᵐ)`. -/
theorem integral_uStatistic (P : Measure E) [IsProbabilityMeasure P] (hmn : m ≤ n)
    {h : (Fin m → E) → ℝ} (hh : Integrable h (Measure.pi fun _ : Fin m ↦ P)) :
    ∫ x, uStatistic m n h x ∂(Measure.pi fun _ : Fin n ↦ P) =
      ∫ y, h y ∂(Measure.pi fun _ : Fin m ↦ P) := by
  -- The observations selected by an embedding are again an i.i.d. sample from `P`.
  have hf (f : Fin m ↪ Fin n) := measurePreserving_pi_comp_embedding (fun _ : Fin n ↦ P) f
  have hint (f : Fin m ↪ Fin n) : Integrable (fun x : Fin n → E ↦ h (x ∘ f))
      (Measure.pi fun _ : Fin n ↦ P) :=
    (hf f).integrable_comp_of_integrable hh
  have hmean (f : Fin m ↪ Fin n) :
      ∫ x, h (x ∘ f) ∂(Measure.pi fun _ : Fin n ↦ P) = ∫ y, h y ∂(Measure.pi fun _ : Fin m ↦ P) :=
    (hf f).hasLaw.integral_comp hh.aestronglyMeasurable
  -- Each summand has the common mean, and for `m ≤ n` there is at least one embedding, so the
  -- average of that constant is the constant, as in `uStatistic_const`.
  have : Nonempty (Fin m ↪ Fin n) := Fin.nonempty_embedding_iff.2 hmn
  simp_rw [uStatistic_eq_expect, integral_expect fun f _ ↦ hint f, hmean, Fintype.expect_const]

/-- **Unbiasedness in a parametric family.** For a family of laws `P θ` on `E` and a measurable
kernel `h` that is integrable under every `(P θ)ᵐ`, the U-statistic with `n ≥ m` observations is
an unbiased estimator of `θ ↦ ∫ h d((P θ)ᵐ)` in the `n`-sample model `θ ↦ (P θ)ⁿ`. -/
theorem isUnbiasedEstimator_uStatistic {Θ : Type*} (P : Θ → Measure E)
    [∀ θ, IsProbabilityMeasure (P θ)] (hmn : m ≤ n) {h : (Fin m → E) → ℝ} (hh : Measurable h)
    (hint : ∀ θ, Integrable h (Measure.pi fun _ : Fin m ↦ P θ)) :
    IsUnbiasedEstimator (fun θ ↦ Measure.pi fun _ : Fin n ↦ P θ) (uStatistic m n h)
      (fun θ ↦ ∫ y, h y ∂(Measure.pi fun _ : Fin m ↦ P θ)) :=
  .mk (measurable_uStatistic hh) (fun θ ↦ integrable_uStatistic (P θ) (hint θ))
    fun θ ↦ integral_uStatistic (P θ) hmn (hint θ)

end TauCeti
