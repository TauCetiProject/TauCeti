/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import TauCeti.Statistics.Estimation.Unbiased
import Mathlib.Data.Fintype.CardEmbedding
import TauCeti.MeasureTheory.Constructions.Pi

/-!
# U-statistics

For a kernel `h : (Fin m → E) → ℝ` of `m` arguments and a sample `x : Fin n → E`, the
U-statistic `uStatistic m n h x` is the average of `h (x ∘ f)` over the `n.descFactorial m`
injections `f : Fin m → Fin n`, that is, over the ordered `m`-tuples of distinct observations.
It does not depend on the order of the observations, and under an i.i.d. sample of size `n ≥ m`
from a law `P` it is an unbiased estimator of `∫ h d(Pᵐ)`: each term `h (x ∘ f)` has law
`h` under `Pᵐ`, because the coordinates of `x` selected by an injection are again i.i.d.

For `m = 1` the U-statistic is the sample mean of `h`. If `n < m` there are no injections and
the U-statistic is `0`; for `m = 0` it is the constant value of `h` at the empty tuple.

## Main definitions

* `TauCeti.uStatistic m n h x`: the U-statistic of order `m` with kernel `h`.

## Main results

* `TauCeti.uStatistic_eq_sum_embedding`: the U-statistic as an average over embeddings
  `Fin m ↪ Fin n`.
* `TauCeti.uStatistic_comp_perm`: the U-statistic is a symmetric function of the sample.
* `TauCeti.uStatistic_one`: for `m = 1` it is the sample mean of `h`.
* `TauCeti.integral_uStatistic`: for `m ≤ n` and `h` integrable under `Pᵐ`, the mean of the
  U-statistic under `Pⁿ` is `∫ h d(Pᵐ)`.
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
  rw [uStatistic_def]
  congr 1
  refine Finset.sum_bij' (fun f hf ↦ ⟨f, (Finset.mem_filter.1 hf).2⟩) (fun f _ ↦ f)
    (fun _ _ ↦ Finset.mem_univ _) (fun f _ ↦ ?_) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, f.injective⟩

/-- With fewer observations than arguments of the kernel there are no injections, and the
U-statistic is `0`. -/
@[simp]
theorem uStatistic_of_lt (h : (Fin m → E) → ℝ) (x : Fin n → E) (hnm : n < m) :
    uStatistic m n h x = 0 := by
  rw [uStatistic_def, Nat.descFactorial_eq_zero_iff_lt.2 hnm, Nat.cast_zero, inv_zero, zero_mul]

/-- The U-statistic of order `0` is the value of `h` at the empty tuple. -/
@[simp]
theorem uStatistic_zero (n : ℕ) (h : (Fin 0 → E) → ℝ) (x : Fin n → E) :
    uStatistic 0 n h x = h Fin.elim0 := by
  rw [uStatistic_eq_sum_embedding, Nat.descFactorial_zero, Nat.cast_one, inv_one, one_mul,
    Fintype.sum_unique]
  exact congrArg h (Subsingleton.elim _ _)

/-- **Symmetry.** The U-statistic does not depend on the order of the observations. -/
@[simp]
theorem uStatistic_comp_perm (h : (Fin m → E) → ℝ) (x : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    uStatistic m n h (x ∘ σ) = uStatistic m n h x := by
  rw [uStatistic_eq_sum_embedding, uStatistic_eq_sum_embedding]
  congr 1
  exact Fintype.sum_equiv ((Equiv.refl _).embeddingCongr σ) _ _ fun _ ↦ rfl

/-- **The sample mean.** The U-statistic of order `1` is the average of `h` over the
observations. -/
theorem uStatistic_one (h : (Fin 1 → E) → ℝ) (x : Fin n → E) :
    uStatistic 1 n h x = (n : ℝ)⁻¹ * ∑ i, h (fun _ ↦ x i) := by
  rw [uStatistic_eq_sum_embedding, Nat.descFactorial_one]
  congr 1
  refine Fintype.sum_equiv Equiv.embeddingUnique _ _ fun f ↦ ?_
  exact congrArg h (funext fun j ↦ congrArg (x ∘ f) (Subsingleton.elim j default))

variable [MeasurableSpace E]

/-- The U-statistic of a measurable kernel is measurable. -/
@[fun_prop]
theorem measurable_uStatistic {h : (Fin m → E) → ℝ} (hh : Measurable h) :
    Measurable (uStatistic m n h) := by
  refine funext (uStatistic_eq_sum_embedding m n h) ▸ ?_
  exact measurable_const.mul
    (Finset.measurable_sum _ fun f _ ↦ hh.comp (by fun_prop))

/-- If the kernel is integrable under `Pᵐ`, then the U-statistic is integrable under `Pⁿ`. -/
theorem integrable_uStatistic (P : Measure E) [IsProbabilityMeasure P] {h : (Fin m → E) → ℝ}
    (hh : Integrable h (Measure.pi fun _ : Fin m ↦ P)) :
    Integrable (uStatistic m n h) (Measure.pi fun _ : Fin n ↦ P) := by
  refine funext (uStatistic_eq_sum_embedding m n h) ▸ ?_
  refine (integrable_finsetSum _ fun f _ ↦ ?_).const_mul _
  exact (measurePreserving_pi_comp_embedding (fun _ : Fin n ↦ P) f).integrable_comp_of_integrable
    hh

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
    (integral_map (hf f).measurable.aemeasurable
      ((hf f).map_eq ▸ hh.aestronglyMeasurable)).symm.trans (by rw [(hf f).map_eq])
  have hpos : ((n.descFactorial m : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.descFactorial_eq_zero_iff_lt.not.2 (Nat.not_lt.2 hmn))
  simp_rw [uStatistic_eq_sum_embedding, integral_const_mul, integral_finsetSum _ fun f _ ↦ hint f,
    hmean, Finset.sum_const, Finset.card_univ,
    Fintype.card_embedding_eq, Fintype.card_fin, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hpos _

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
