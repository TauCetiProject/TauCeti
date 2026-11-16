/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Decomposition
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.Analysis.InnerProductSpace.Positive.VectorFunctional
import TauCeti.Analysis.LocallyConvex.Mazur
import TauCeti.Analysis.Normed.Operator.Dense

/-!
# Strictly positive elements and σ-unital C⋆-algebras

An element `h` of a (possibly nonunital) complex C⋆-algebra `A` is *strictly positive*
(`TauCeti.CStarAlgebra.IsStrictlyPositive h`) if `0 ≤ h` and the hereditary subalgebra `h * A * h`
is dense in `A`. This generalizes the unital notion `_root_.IsStrictlyPositive` (`0 ≤ h ∧ IsUnit h`,
recovered in `TauCeti.CStarAlgebra.isStrictlyPositive_iff_root`), and provides the standard
characterization of σ-unital C⋆-algebras (those admitting a countable approximate unit).

For any `0 ≤ h`, the continuous functional calculus yields the monotone sequence of positive strict
contractions
`strictlyPositiveApproxUnit h n = cfcₙ (fun t : ℝ≥0 => t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) h`,
which satisfies `‖h - h * eₙ‖ ≤ (n + 1)⁻¹` and `eₙ * a ∈ h * A` for every `a : A`. When `h` is
strictly positive, `eₙ` is an increasing approximate unit of `A`.

## Main definitions and results

* `TauCeti.CStarAlgebra.IsStrictlyPositive`: positivity plus density of `Set.range (h * · * h)`.
* `TauCeti.CStarAlgebra.strictlyPositiveApproxUnit`: the canonical monotone sequence
  `h * ((n + 1)⁻¹ + h)⁻¹` built via the nonunital continuous functional calculus.
* `TauCeti.CStarAlgebra.isStrictlyPositive_tfae`: for `0 ≤ h`, the five standard conditions
  (Blackadar II.4.2.1) are equivalent:
  1. `IsStrictlyPositive h`;
  2. `Dense (Set.range (h * ·))`;
  3. `Dense (Set.range (· * h))`;
  4. `∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re`;
  5. `(Filter.atTop.map (strictlyPositiveApproxUnit h)).IsIncreasingApproximateUnit`.
* `TauCeti.CStarAlgebra.isStrictlyPositive_iff_root`: in a unital C⋆-algebra,
  `TauCeti.CStarAlgebra.IsStrictlyPositive h` coincides with `_root_.IsStrictlyPositive h`.
* `TauCeti.CStarAlgebra.isStrictlyPositive_tsum_of_forall_apply_eq_zero` and
  `exists_isStrictlyPositive_of_forall_apply_eq_zero`: constructing strictly positive elements from
  positive sequences not jointly annihilated by any nonzero positive functional.
* `TauCeti.CStarAlgebra.exists_isStrictlyPositive_iff_exists_seq_isIncreasingApproximateUnit`,
  `exists_isStrictlyPositive_iff_exists_seq_monotone_isIncreasingApproximateUnit`, and
  `exists_isStrictlyPositive_iff_exists_seq_tendsto_mul_right`: characterizations of σ-unital
  C⋆-algebras (Blackadar II.4.2.4).
* `TauCeti.CStarAlgebra.exists_isStrictlyPositive_of_separableSpace` and
  `exists_seq_monotone_isIncreasingApproximateUnit_of_separableSpace`: every separable C⋆-algebra
  is σ-unital.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Propositions II.4.2.1 and II.4.2.4.
* Gert K. Pedersen, *C*-Algebras and their Automorphism Groups*, Proposition 3.10.5.
* Gerard J. Murphy, *C*-Algebras and Operator Theory*, Section 3.1.
-/

public section

noncomputable section

open Filter Topology Unitization
open scoped CStarAlgebra ComplexOrder InnerProductSpace NNReal

namespace TauCeti.CStarAlgebra

section Basic

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- An element `h` of a (possibly nonunital) C⋆-algebra `A` is *strictly positive* if `0 ≤ h` and
the corner `h * A * h` is dense in `A`. In a unital C⋆-algebra this coincides with
`_root_.IsStrictlyPositive h` (`0 ≤ h ∧ IsUnit h`); see `isStrictlyPositive_iff_root`. -/
def IsStrictlyPositive (h : A) : Prop :=
  0 ≤ h ∧ Dense (Set.range fun a : A => h * a * h)

theorem isStrictlyPositive_def {h : A} :
    IsStrictlyPositive h ↔ 0 ≤ h ∧ Dense (Set.range fun a : A => h * a * h) :=
  Iff.rfl

theorem IsStrictlyPositive.nonneg {h : A} (hh : IsStrictlyPositive h) : 0 ≤ h :=
  hh.1

theorem IsStrictlyPositive.dense_range_mul_mul {h : A} (hh : IsStrictlyPositive h) :
    Dense (Set.range fun a : A => h * a * h) :=
  hh.2

/-- `0 : A` is strictly positive if and only if `A` is subsingleton (the zero C⋆-algebra). -/
theorem isStrictlyPositive_zero_iff : IsStrictlyPositive (0 : A) ↔ Subsingleton A := by
  constructor
  · intro h0
    have hrange : (Set.range fun a : A => (0 : A) * a * 0) ⊆ {0} := by
      rintro _ ⟨a, rfl⟩
      simp
    have hdense : Dense ({0} : Set A) := h0.2.mono hrange
    have huniv : ({0} : Set A) = Set.univ := by
      rw [← isClosed_singleton.closure_eq, hdense.closure_eq]
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ ({0} : Set A) := huniv ▸ Set.mem_univ a
    have hb : b ∈ ({0} : Set A) := huniv ▸ Set.mem_univ b
    rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  · intro _
    refine ⟨le_rfl, dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun a => subset_closure ?_)⟩
    exact ⟨0, Subsingleton.elim _ _⟩

end Basic

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The canonical sequence `h * ((n + 1)⁻¹ + h)⁻¹` associated with an element `h : A` via the
nonunital continuous functional calculus. For `0 ≤ h`, this is a monotone increasing sequence of
positive strict contractions that forms an increasing approximate unit of `A` if and only if `h` is
strictly positive. -/
def strictlyPositiveApproxUnit (h : A) (n : ℕ) : A :=
  cfcₙ (fun t : ℝ≥0 => t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) h

@[simp]
theorem strictlyPositiveApproxUnit_zero (n : ℕ) :
    strictlyPositiveApproxUnit (0 : A) n = 0 := by
  simp [strictlyPositiveApproxUnit]

/-- Each term of `strictlyPositiveApproxUnit h` is nonnegative. -/
theorem strictlyPositiveApproxUnit_nonneg (h : A) (n : ℕ) :
    0 ≤ strictlyPositiveApproxUnit h n :=
  cfcₙ_nonneg_of_predicate

/-- Each term of `strictlyPositiveApproxUnit h` has norm strictly less than `1`. -/
theorem norm_strictlyPositiveApproxUnit_lt_one (h : A) (n : ℕ) :
    ‖strictlyPositiveApproxUnit h n‖ < 1 := by
  have hlt : ‖strictlyPositiveApproxUnit h n‖₊ < 1 := by
    refine nnNorm_cfcₙ_nnreal_lt fun t _ => ?_
    have hc : (0 : ℝ≥0) < ((n + 1 : ℕ) : ℝ≥0)⁻¹ := by positivity
    have hden : (0 : ℝ≥0) < ((n + 1 : ℕ) : ℝ≥0)⁻¹ + t := add_pos_of_pos_of_nonneg hc t.2
    rw [← div_eq_mul_inv, div_lt_one hden]
    exact lt_add_of_pos_left t hc
  exact_mod_cast hlt

/-- Each term of `strictlyPositiveApproxUnit h` has norm at most `1`. -/
theorem norm_strictlyPositiveApproxUnit_le_one (h : A) (n : ℕ) :
    ‖strictlyPositiveApproxUnit h n‖ ≤ 1 :=
  (norm_strictlyPositiveApproxUnit_lt_one h n).le

/-- The sequence `strictlyPositiveApproxUnit h` is monotone increasing. -/
theorem strictlyPositiveApproxUnit_monotone (h : A) :
    Monotone (strictlyPositiveApproxUnit h) := by
  intro m n hmn
  have hcont : ∀ k : ℕ, ContinuousOn (fun t : ℝ≥0 => t * (((k + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹)
      (quasispectrum ℝ≥0 h) := fun k =>
    Continuous.continuousOn (by fun_prop (disch := intro x; positivity))
  refine cfcₙ_mono (a := h) (fun t _ => ?_) (hcont m) (hcont n) (by simp) (by simp)
  gcongr

/-- For `0 ≤ h`, `h` commutes with every `strictlyPositiveApproxUnit h n`. -/
theorem commute_strictlyPositiveApproxUnit {h : A} (hh : 0 ≤ h) (n : ℕ) :
    h * strictlyPositiveApproxUnit h n = strictlyPositiveApproxUnit h n * h := by
  have hf : ContinuousOn (fun t : ℝ≥0 => t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹)
      (quasispectrum ℝ≥0 h) :=
    Continuous.continuousOn (by fun_prop (disch := intro x; positivity))
  simp only [strictlyPositiveApproxUnit]
  calc h * cfcₙ (fun t : ℝ≥0 => t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) h
      = cfcₙ (fun t : ℝ≥0 => t) h *
          cfcₙ (fun t : ℝ≥0 => t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) h := by
        rw [cfcₙ_id' ℝ≥0 h hh]
    _ = cfcₙ (fun t : ℝ≥0 => t * (t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹)) h := by
        rw [← cfcₙ_mul (fun t : ℝ≥0 => t) _ h (continuousOn_id' _) rfl hf (by simp)]
    _ = cfcₙ (fun t : ℝ≥0 => (t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) * t) h :=
        cfcₙ_congr fun t _ => mul_comm t _
    _ = cfcₙ (fun t : ℝ≥0 => t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) h *
          cfcₙ (fun t : ℝ≥0 => t) h := by
        rw [cfcₙ_mul _ (fun t : ℝ≥0 => t) h hf (by simp) (continuousOn_id' _) rfl]
    _ = cfcₙ (fun t : ℝ≥0 => t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) h * h := by
        rw [cfcₙ_id' ℝ≥0 h hh]

/-- Quantitative right-approximation error on `h`:
`‖h - h * strictlyPositiveApproxUnit h n‖ ≤ (n + 1)⁻¹`. -/
theorem norm_sub_mul_strictlyPositiveApproxUnit_le {h : A} (hh : 0 ≤ h) (n : ℕ) :
    ‖h - h * strictlyPositiveApproxUnit h n‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
  let c : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)⁻¹
  have hc_pos : 0 < c := by positivity
  have hf_cont : Continuous (fun t : ℝ≥0 => t * (c + t)⁻¹) := by
    fun_prop (disch := intro x; positivity)
  have htf_cont : Continuous (fun t : ℝ≥0 => t * (t * (c + t)⁻¹)) :=
    continuous_id.mul hf_cont
  have hg_cont : Continuous (fun t : ℝ≥0 => t * (c * (c + t)⁻¹)) := by
    fun_prop (disch := intro x; positivity)
  have hmul : h * strictlyPositiveApproxUnit h n =
      cfcₙ (fun t : ℝ≥0 => t * (t * (c + t)⁻¹)) h := by
    calc h * strictlyPositiveApproxUnit h n
        = cfcₙ (fun t : ℝ≥0 => t) h * cfcₙ (fun t : ℝ≥0 => t * (c + t)⁻¹) h := by
          rw [strictlyPositiveApproxUnit, cfcₙ_id' ℝ≥0 h hh]
      _ = cfcₙ (fun t : ℝ≥0 => t * (t * (c + t)⁻¹)) h := by
          rw [← cfcₙ_mul (fun t : ℝ≥0 => t) _ h (continuousOn_id' _) rfl hf_cont.continuousOn
            (by simp)]
  have hdiff : h - h * strictlyPositiveApproxUnit h n =
      cfcₙ (fun t : ℝ≥0 => t * (c * (c + t)⁻¹)) h := by
    have hsum : cfcₙ (fun t : ℝ≥0 => t * (t * (c + t)⁻¹)) h +
        cfcₙ (fun t : ℝ≥0 => t * (c * (c + t)⁻¹)) h = h := by
      rw [← cfcₙ_add (fun t : ℝ≥0 => t * (t * (c + t)⁻¹))
        (fun t : ℝ≥0 => t * (c * (c + t)⁻¹)) h htf_cont.continuousOn (by simp)
        hg_cont.continuousOn (by simp)]
      conv_rhs => rw [← cfcₙ_id' ℝ≥0 h hh]
      refine cfcₙ_congr fun t _ => ?_
      have hden : c + t ≠ 0 := (add_pos_of_pos_of_nonneg hc_pos t.2).ne'
      calc t * (t * (c + t)⁻¹) + t * (c * (c + t)⁻¹)
          = t * ((c + t) * (c + t)⁻¹) := by ring
        _ = t * 1 := by rw [mul_inv_cancel₀ hden]
        _ = t := mul_one t
    rw [hmul, sub_eq_iff_eq_add', hsum]
  rw [hdiff]
  have hle : ‖cfcₙ (fun t : ℝ≥0 => t * (c * (c + t)⁻¹)) h‖₊ ≤ c := by
    refine nnNorm_cfcₙ_nnreal_le fun t _ => ?_
    have hden : (0 : ℝ≥0) < c + t := add_pos_of_pos_of_nonneg hc_pos t.2
    calc t * (c * (c + t)⁻¹) = c * (t / (c + t)) := by rw [div_eq_mul_inv]; ring
      _ ≤ c * 1 := by
          gcongr
          exact (div_le_one hden).mpr le_add_self
      _ = c := mul_one c
  exact_mod_cast hle

/-- Quantitative left-approximation error on `h`:
`‖h - strictlyPositiveApproxUnit h n * h‖ ≤ (n + 1)⁻¹`. -/
theorem norm_sub_strictlyPositiveApproxUnit_mul_le {h : A} (hh : 0 ≤ h) (n : ℕ) :
    ‖h - strictlyPositiveApproxUnit h n * h‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
  rw [← commute_strictlyPositiveApproxUnit hh n]
  exact norm_sub_mul_strictlyPositiveApproxUnit_le hh n

/-- Factorization of `strictlyPositiveApproxUnit h n` in the unitization `A⁺¹`:
`(eₙ : A⁺¹) = (h : A⁺¹) * rₙ = rₙ * (h : A⁺¹)` where
`rₙ = cfc (fun t => ((n + 1)⁻¹ + t)⁻¹) (h : A⁺¹)`. -/
private theorem inr_strictlyPositiveApproxUnit_eq {h : A} (hh : 0 ≤ h) (n : ℕ) :
    let r : A⁺¹ := cfc (fun t : ℝ≥0 => (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) (h : A⁺¹)
    ((strictlyPositiveApproxUnit h n : A) : A⁺¹) = (h : A⁺¹) * r ∧
      ((strictlyPositiveApproxUnit h n : A) : A⁺¹) = r * (h : A⁺¹) := by
  let c : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)⁻¹
  have hh' : 0 ≤ (h : A⁺¹) := Unitization.inr_nonneg_iff.mpr hh
  have hr_cont : ContinuousOn (fun t : ℝ≥0 => (c + t)⁻¹) (spectrum ℝ≥0 (h : A⁺¹)) :=
    Continuous.continuousOn (by fun_prop (disch := intro x; positivity))
  have h1 : ((strictlyPositiveApproxUnit h n : A) : A⁺¹) =
      cfc (fun t : ℝ≥0 => t * (c + t)⁻¹) (h : A⁺¹) :=
    Unitization.nnreal_cfcₙ_eq_cfc_inr h (fun t : ℝ≥0 => t * (c + t)⁻¹) (by simp)
  constructor
  · rw [h1, cfc_mul (fun t : ℝ≥0 => t) (fun t : ℝ≥0 => (c + t)⁻¹) (h : A⁺¹)
      (continuousOn_id' _) hr_cont, cfc_id' ℝ≥0 (h : A⁺¹) hh']
  · rw [h1]
    have hcomm : cfc (fun t : ℝ≥0 => t * (c + t)⁻¹) (h : A⁺¹) =
        cfc (fun t : ℝ≥0 => (c + t)⁻¹ * t) (h : A⁺¹) :=
      cfc_congr fun t _ => mul_comm t _
    rw [hcomm, cfc_mul (fun t : ℝ≥0 => (c + t)⁻¹) (fun t : ℝ≥0 => t) (h : A⁺¹)
      hr_cont (continuousOn_id' _), cfc_id' ℝ≥0 (h : A⁺¹) hh']

/-- Every left multiple `strictlyPositiveApproxUnit h n * a` belongs to `h * A`. -/
theorem strictlyPositiveApproxUnit_mul_mem_range {h : A} (hh : 0 ≤ h) (n : ℕ) (a : A) :
    strictlyPositiveApproxUnit h n * a ∈ Set.range fun b : A => h * b := by
  let r : A⁺¹ := cfc (fun t : ℝ≥0 => (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) (h : A⁺¹)
  have hr_mul : r * (a : A⁺¹) = ((r.fst • a + r.snd * a : A) : A⁺¹) := by
    conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq r]
    rw [add_mul, Unitization.inl_mul_inr, ← Unitization.inr_mul, ← Unitization.inr_add]
  refine ⟨r.fst • a + r.snd * a, Unitization.inr_injective (R := ℂ) ?_⟩
  rw [Unitization.inr_mul, Unitization.inr_mul,
    (inr_strictlyPositiveApproxUnit_eq hh n).1, mul_assoc, hr_mul]

/-- Every corner element `strictlyPositiveApproxUnit h n * a * strictlyPositiveApproxUnit h n`
belongs to `h * A * h`. -/
theorem strictlyPositiveApproxUnit_mul_mul_mem_range {h : A} (hh : 0 ≤ h) (n : ℕ) (a : A) :
    strictlyPositiveApproxUnit h n * a * strictlyPositiveApproxUnit h n ∈
      Set.range fun b : A => h * b * h := by
  let r : A⁺¹ := cfc (fun t : ℝ≥0 => (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) (h : A⁺¹)
  let b₁ : A := r.fst • a + r.snd * a
  let b : A := r.fst • b₁ + b₁ * r.snd
  have hr_left : r * (a : A⁺¹) = (b₁ : A⁺¹) := by
    conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq r]
    rw [add_mul, Unitization.inl_mul_inr, ← Unitization.inr_mul, ← Unitization.inr_add]
  have hr_right : (b₁ : A⁺¹) * r = (b : A⁺¹) := by
    conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq r]
    rw [mul_add, Unitization.inr_mul_inl, ← Unitization.inr_mul, ← Unitization.inr_add]
  refine ⟨b, Unitization.inr_injective (R := ℂ) ?_⟩
  have ⟨hL, hR⟩ := inr_strictlyPositiveApproxUnit_eq hh n
  simp only [Unitization.inr_mul]
  calc (h : A⁺¹) * (b : A⁺¹) * (h : A⁺¹)
      = (h : A⁺¹) * ((r * (a : A⁺¹)) * r) * (h : A⁺¹) := by rw [hr_left, hr_right]
    _ = ((h : A⁺¹) * r) * (a : A⁺¹) * (r * (h : A⁺¹)) := by noncomm_ring
    _ = ((strictlyPositiveApproxUnit h n : A) : A⁺¹) * (a : A⁺¹) *
          ((strictlyPositiveApproxUnit h n : A) : A⁺¹) := by rw [← hL, ← hR]

/-- For every `a ∈ closure (h * A)`, `strictlyPositiveApproxUnit h n * a → a` in norm. -/
theorem tendsto_strictlyPositiveApproxUnit_mul_of_mem_closure_range_mul_left {h : A} (hh : 0 ≤ h)
    {a : A} (ha : a ∈ closure (Set.range fun b : A => h * b)) :
    Tendsto (fun n => strictlyPositiveApproxUnit h n * a) atTop (𝓝 a) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨b, hb⟩ := Metric.mem_closure_range_iff.mp ha (ε / 3) (by positivity)
  have hba : ‖a - h * b‖ < ε / 3 := by simpa [dist_eq_norm] using hb
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < ε / (3 * (‖b‖ + 1)))
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have herr : ‖strictlyPositiveApproxUnit h n * (h * b) - h * b‖ < ε / 3 := by
    have h1 : ‖strictlyPositiveApproxUnit h n * h - h‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
      rw [norm_sub_rev]
      exact norm_sub_strictlyPositiveApproxUnit_mul_le hh n
    have h2 : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ :=
      inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    have h3 : ((N + 1 : ℕ) : ℝ)⁻¹ < ε / (3 * (‖b‖ + 1)) := by simpa [one_div] using hN
    have hbn : ‖b‖ < ‖b‖ + 1 := lt_add_one ‖b‖
    calc ‖strictlyPositiveApproxUnit h n * (h * b) - h * b‖
        = ‖(strictlyPositiveApproxUnit h n * h - h) * b‖ := by congr 1; noncomm_ring
      _ ≤ ‖strictlyPositiveApproxUnit h n * h - h‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ‖b‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg b)
      _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ * (‖b‖ + 1) :=
          mul_le_mul h2 hbn.le (norm_nonneg b) (by positivity)
      _ < (ε / (3 * (‖b‖ + 1))) * (‖b‖ + 1) :=
          mul_lt_mul_of_pos_right h3 (by positivity)
      _ = ε / 3 := by field_simp
  have he_le : ‖strictlyPositiveApproxUnit h n‖ ≤ 1 := norm_strictlyPositiveApproxUnit_le_one h n
  rw [dist_eq_norm]
  calc ‖strictlyPositiveApproxUnit h n * a - a‖
      = ‖strictlyPositiveApproxUnit h n * (a - h * b) +
          (strictlyPositiveApproxUnit h n * (h * b) - h * b) - (a - h * b)‖ := by
          congr 1; noncomm_ring
    _ ≤ ‖strictlyPositiveApproxUnit h n * (a - h * b) +
          (strictlyPositiveApproxUnit h n * (h * b) - h * b)‖ + ‖a - h * b‖ := norm_sub_le _ _
    _ ≤ ‖strictlyPositiveApproxUnit h n * (a - h * b)‖ +
          ‖strictlyPositiveApproxUnit h n * (h * b) - h * b‖ + ‖a - h * b‖ := by
          gcongr; exact norm_add_le _ _
    _ ≤ 1 * ‖a - h * b‖ + ‖strictlyPositiveApproxUnit h n * (h * b) - h * b‖ + ‖a - h * b‖ := by
          gcongr
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right he_le (norm_nonneg _))
    _ < ε / 3 + ε / 3 + ε / 3 := by
          rw [one_mul]
          linarith
    _ = ε := by ring

/-- For every `a ∈ closure (A * h)`, `a * strictlyPositiveApproxUnit h n → a` in norm. -/
theorem tendsto_mul_strictlyPositiveApproxUnit_of_mem_closure_range_mul_right {h : A} (hh : 0 ≤ h)
    {a : A} (ha : a ∈ closure (Set.range fun b : A => b * h)) :
    Tendsto (fun n => a * strictlyPositiveApproxUnit h n) atTop (𝓝 a) := by
  have ha' : star a ∈ closure (Set.range fun b : A => h * b) := by
    have hstar_img : star '' Set.range (fun b : A => b * h) = Set.range (fun b : A => h * b) := by
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
        exact ⟨star b, by rw [star_mul, hh.isSelfAdjoint.star_eq]⟩
      · rintro ⟨b, rfl⟩
        exact ⟨star b * h, ⟨star b, rfl⟩, by rw [star_mul, star_star, hh.isSelfAdjoint.star_eq]⟩
    rw [← hstar_img]
    exact continuous_star.continuousOn.image_closure (Set.mem_image_of_mem star ha)
  have hlim := (continuous_star.tendsto _).comp
    (tendsto_strictlyPositiveApproxUnit_mul_of_mem_closure_range_mul_left hh ha')
  rw [star_star] at hlim
  refine hlim.congr fun n => ?_
  dsimp only [Function.comp_apply]
  rw [star_mul, star_star,
    (IsSelfAdjoint.of_nonneg (strictlyPositiveApproxUnit_nonneg h n)).star_eq]

/-- If `0 ≤ h` is strictly positive on every nonzero positive functional of `A`, then in any
nondegenerate Hilbert-space representation `π` of `A`, `π (strictlyPositiveApproxUnit h n)`
converges strongly to the identity. -/
private theorem tendsto_apply_strictlyPositiveApproxUnit_of_isNondegenerate {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : π.IsNondegenerate) {h : A} (hh : 0 ≤ h)
    (hpos : ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re) (η : H) :
    Tendsto (fun n => π (strictlyPositiveApproxUnit h n) η) atTop (𝓝 η) := by
  -- Show `Set.range (π h)` is dense in `H` by checking that its orthogonal complement is `⊥`.
  let K : Submodule ℂ H := (LinearMap.range (π h).toLinearMap).topologicalClosure
  have hK_top : K = ⊤ := by
    have hK_orth : Kᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hπhv : π h v = 0 := by
        refine ext_inner_right ℂ fun w => ?_
        rw [inner_zero_left, ← ContinuousLinearMap.adjoint_inner_right,
          ← ContinuousLinearMap.star_eq_adjoint, ← map_star, hh.isSelfAdjoint.star_eq]
        exact (Submodule.mem_orthogonal' K v).mp hv (π h w)
          (Submodule.le_topologicalClosure _ ⟨w, rfl⟩)
      -- Pull back the positive vector functional `T ↦ ⟪v, T v⟫_ℂ` along `π`.
      let φCLM : A →L[ℂ] ℂ :=
        ((ContinuousLinearMap.innerPositiveLinearMap ℂ v).toLinearMap.comp
          (π : A →ₗ[ℂ] H →L[ℂ] H)).mkContinuous (‖v‖ ^ 2) fun b =>
            (ContinuousLinearMap.norm_innerPositiveLinearMap_apply_le v (π b)).trans
              (mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le π b) (sq_nonneg _))
      let φv : A →P[ℂ] ℂ :=
        PositiveContinuousLinearMap.mk₀ φCLM fun b hb =>
          (ContinuousLinearMap.innerPositiveLinearMap ℂ v).map_nonneg (map_nonneg π hb)
      have hφv_apply : ∀ b, φv b = ⟪v, π b v⟫_ℂ := fun b =>
        (PositiveContinuousLinearMap.mk₀_apply φCLM _ b).trans <|
          (LinearMap.mkContinuous_apply _ _ _ b).trans <| by simp
      have hφv0 : φv = 0 := by
        by_contra hne
        have hlt := hpos φv hne
        rw [hφv_apply h, hπhv, inner_zero_right, Complex.zero_re] at hlt
        exact lt_irrefl 0 hlt
      refine (NonUnitalStarAlgHom.isNondegenerate_iff_forall_apply_eq_zero.mp hπ) v fun b => ?_
      have hinner0 : ⟪π b v, π b v⟫_ℂ = 0 := by
        have hval : ⟪v, π (star b * b) v⟫_ℂ = 0 := by
          rw [← hφv_apply (star b * b), hφv0]
          simp
        rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp,
          ContinuousLinearMap.adjoint_inner_right] at hval
        exact hval
      exact inner_self_eq_zero.mp hinner0
    have : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    rw [← K.orthogonal_orthogonal, hK_orth, Submodule.bot_orthogonal_eq_top]
  have hdense : Dense (Set.range (π h)) := by
    rw [dense_iff_closure_eq]
    have hcoe : (K : Set H) = Set.univ := by simp [hK_top]
    simpa [K, Submodule.topologicalClosure_coe, LinearMap.coe_range] using hcoe
  -- Extend strong convergence from the dense range of `π h` using `‖π eₙ‖ ≤ 1`.
  refine ContinuousLinearMap.tendsto_apply_of_dense hdense (C := 1)
    (f := fun n => π (strictlyPositiveApproxUnit h n)) (g := ContinuousLinearMap.id ℂ H)
    (.of_forall fun n =>
      (NonUnitalStarAlgHom.norm_apply_le π _).trans (norm_strictlyPositiveApproxUnit_le_one h n))
    ?_ η
  rintro _ ⟨w, rfl⟩
  rw [ContinuousLinearMap.id_apply, tendsto_iff_norm_sub_tendsto_zero]
  have hlim0 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * ‖w‖) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖w‖
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim0
  have hsub : π (strictlyPositiveApproxUnit h n) (π h w) - π h w =
      π (strictlyPositiveApproxUnit h n * h - h) w := by
    simp [map_sub, map_mul]
  rw [hsub]
  calc ‖π (strictlyPositiveApproxUnit h n * h - h) w‖
      ≤ ‖π (strictlyPositiveApproxUnit h n * h - h)‖ * ‖w‖ := (π _).le_opNorm w
    _ ≤ ‖strictlyPositiveApproxUnit h n * h - h‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le π _) (norm_nonneg w)
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ‖w‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right (norm_sub_strictlyPositiveApproxUnit_mul_le hh n)
          (norm_nonneg w)

/-- If `0 ≤ h` is strictly positive on every nonzero positive functional of `A`, then `h * A` is
dense in `A`. -/
private theorem dense_range_mul_left_of_forall_pos {h : A} (hh : 0 ≤ h)
    (hpos : ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re) :
    Dense (Set.range fun b : A => h * b) := by
  let S : Set A := closure (Set.range fun b : A => h * b)
  have hS_conv : Convex ℝ S := by
    have hsub : Set.range (fun b : A => h * b) =
        ((LinearMap.mul ℂ A h).range.restrictScalars ℝ : Set A) := by
      ext x
      simp [LinearMap.mem_range]
    have hS_eq : S = closure ((LinearMap.mul ℂ A h).range.restrictScalars ℝ : Set A) := by
      simp [S, hsub]
    rw [hS_eq]
    exact ((LinearMap.mul ℂ A h).range.restrictScalars ℝ).convex.closure
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun a => ?_)
  refine hS_conv.mem_of_tendsto_weak (𝕜 := ℂ) (l := atTop) isClosed_closure
    (fun n => subset_closure (strictlyPositiveApproxUnit_mul_mem_range hh n a)) ?_
  rw [tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap]
  intro ω
  let f : A⁺¹ →ₚ[ℂ] ℂ := ω.extendUnitization.toPositiveLinearMap
  let πA : A →⋆ₙₐ[ℂ] (f.GNS →L[ℂ] f.GNS) :=
    f.gnsNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hω_repr : ∀ b : A, ω b = ⟪f.gnsVector, πA b f.gnsVector⟫_ℂ := fun b => by
    simp [πA, f]
  have hstrong : Tendsto (fun n => πA (strictlyPositiveApproxUnit h n) (πA a f.gnsVector))
      atTop (𝓝 (πA a f.gnsVector)) :=
    tendsto_apply_strictlyPositiveApproxUnit_of_isNondegenerate πA
      ω.isNondegenerate_gnsNonUnitalStarAlgHom_extendUnitization_comp_inr hh hpos (πA a f.gnsVector)
  have hinner : Tendsto
      (fun n => ⟪f.gnsVector, πA (strictlyPositiveApproxUnit h n) (πA a f.gnsVector)⟫_ℂ)
      atTop (𝓝 ⟪f.gnsVector, πA a f.gnsVector⟫_ℂ) :=
    ((continuous_const.inner continuous_id).tendsto _).comp hstrong
  rw [hω_repr a]
  refine hinner.congr fun n => ?_
  rw [hω_repr]
  simp [map_mul]

/-- Characterizations of strictly positive elements in a (possibly nonunital) C⋆-algebra
(Blackadar II.4.2.1): for `0 ≤ h`, strict positivity, density of `h * A`, density of `A * h`,
strict positivity under every nonzero positive linear functional, and `strictlyPositiveApproxUnit h`
being an increasing approximate unit are all equivalent. -/
theorem isStrictlyPositive_tfae {h : A} (hh : 0 ≤ h) :
    List.TFAE
      [ IsStrictlyPositive h,
        Dense (Set.range fun a : A => h * a),
        Dense (Set.range fun a : A => a * h),
        ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re,
        (atTop.map (strictlyPositiveApproxUnit h)).IsIncreasingApproximateUnit ] := by
  tfae_have 1 → 2 := fun hsp => by
    refine hsp.2.mono ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨a * h, (mul_assoc h a h).symm⟩
  tfae_have 2 → 3 := fun hd => by
    have himg : star '' Set.range (fun a : A => h * a) = Set.range (fun a : A => a * h) := by
      ext x
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨star a, by rw [star_mul, hh.isSelfAdjoint.star_eq]⟩
      · rintro ⟨a, rfl⟩
        exact ⟨h * star a, ⟨star a, rfl⟩, by rw [star_mul, star_star, hh.isSelfAdjoint.star_eq]⟩
    rw [← himg, dense_iff_closure_eq]
    refine Set.eq_univ_of_forall fun x => ?_
    rw [← star_star x]
    exact continuous_star.continuousOn.image_closure (Set.mem_image_of_mem star (hd (star x)))
  tfae_have 3 → 4 := fun hd φ hφ => by
    have hφh : 0 ≤ φ h := φ.map_nonneg hh
    refine lt_of_le_of_ne (Complex.nonneg_iff.mp hφh).1 fun hzero => ?_
    have hφh0 : φ h = 0 := Complex.ext hzero.symm (by simpa using hφh.2.symm)
    let r : A := CFC.sqrt h
    have hr_star : star r = r := (CFC.sqrt_nonneg h).isSelfAdjoint.star_eq
    have hrr : r * r = h := CFC.sqrt_mul_sqrt_self h
    have hvanish : ∀ a : A, φ (a * h) = 0 := fun a => by
      have hcs := PositiveLinearMap.norm_map_mul_star_sq_le φ (a * r) r
      rw [hr_star, mul_assoc, hrr, hφh0, norm_zero, mul_zero] at hcs
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (φ (a * h))])
    have hcl : Set.univ ⊆ {a : A | φ a = 0} :=
      hd.closure_eq ▸ closure_minimal (Set.range_subset_iff.mpr hvanish)
        (isClosed_eq (map_continuous φ) continuous_const)
    exact hφ (DFunLike.ext _ _ fun a => hcl (Set.mem_univ a))
  tfae_have 4 → 5 := fun hpos => by
    have hdense := dense_range_mul_left_of_forall_pos hh hpos
    have hmul_right : ∀ a : A,
        Tendsto (· * a) (atTop.map (strictlyPositiveApproxUnit h)) (𝓝 a) := fun a => by
      rw [tendsto_map'_iff]
      exact tendsto_strictlyPositiveApproxUnit_mul_of_mem_closure_range_mul_left hh (hdense a)
    have hselfadj : ∀ᶠ e in atTop.map (strictlyPositiveApproxUnit h), IsSelfAdjoint e :=
      eventually_map.mpr (Eventually.of_forall fun n =>
        IsSelfAdjoint.of_nonneg (strictlyPositiveApproxUnit_nonneg h n))
    exact
      { tendsto_mul_left := (CStarAlgebra.tendsto_mul_left_iff_tendsto_mul_right hselfadj).mpr
          hmul_right
        tendsto_mul_right := hmul_right
        neBot := map_neBot
        eventually_nonneg := eventually_map.mpr (Eventually.of_forall
          (strictlyPositiveApproxUnit_nonneg h))
        eventually_norm := eventually_map.mpr (Eventually.of_forall
          (norm_strictlyPositiveApproxUnit_le_one h)) }
  tfae_have 5 → 1 := fun hl => by
    refine ⟨hh, dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun a => ?_)⟩
    have hlim : Tendsto
        (fun n => strictlyPositiveApproxUnit h n * a * strictlyPositiveApproxUnit h n)
        atTop (𝓝 a) := by
      have hL : Tendsto (fun n => strictlyPositiveApproxUnit h n * a) atTop (𝓝 a) :=
        tendsto_map'_iff.mp (hl.tendsto_mul_right a)
      have hR : Tendsto (fun n => a * strictlyPositiveApproxUnit h n) atTop (𝓝 a) :=
        tendsto_map'_iff.mp (hl.tendsto_mul_left a)
      rw [tendsto_iff_norm_sub_tendsto_zero] at hL hR ⊢
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (by simpa using hR.add hL)
      have he_le : ‖strictlyPositiveApproxUnit h n‖ ≤ 1 :=
        norm_strictlyPositiveApproxUnit_le_one h n
      calc ‖strictlyPositiveApproxUnit h n * a * strictlyPositiveApproxUnit h n - a‖
          = ‖strictlyPositiveApproxUnit h n * (a * strictlyPositiveApproxUnit h n - a) +
              (strictlyPositiveApproxUnit h n * a - a)‖ := by congr 1; noncomm_ring
        _ ≤ ‖strictlyPositiveApproxUnit h n * (a * strictlyPositiveApproxUnit h n - a)‖ +
              ‖strictlyPositiveApproxUnit h n * a - a‖ := norm_add_le _ _
        _ ≤ 1 * ‖a * strictlyPositiveApproxUnit h n - a‖ +
              ‖strictlyPositiveApproxUnit h n * a - a‖ := by
            gcongr
            exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right he_le (norm_nonneg _))
        _ = ‖a * strictlyPositiveApproxUnit h n - a‖ +
              ‖strictlyPositiveApproxUnit h n * a - a‖ := by rw [one_mul]
    exact mem_closure_of_tendsto hlim
      (Eventually.of_forall fun n => strictlyPositiveApproxUnit_mul_mul_mem_range hh n a)
  tfae_finish

/-- A nonnegative element `h` is strictly positive if and only if `h * A` is dense in `A`. -/
theorem isStrictlyPositive_iff_dense_range_mul_left {h : A} (hh : 0 ≤ h) :
    IsStrictlyPositive h ↔ Dense (Set.range fun a : A => h * a) :=
  (isStrictlyPositive_tfae hh).out 1 2

/-- A nonnegative element `h` is strictly positive if and only if `A * h` is dense in `A`. -/
theorem isStrictlyPositive_iff_dense_range_mul_right {h : A} (hh : 0 ≤ h) :
    IsStrictlyPositive h ↔ Dense (Set.range fun a : A => a * h) :=
  (isStrictlyPositive_tfae hh).out 1 3

/-- A nonnegative element `h` is strictly positive if and only if every nonzero positive continuous
linear functional takes a strictly positive real value on `h`. -/
theorem isStrictlyPositive_iff_forall_positiveContinuousLinearMap_pos {h : A} (hh : 0 ≤ h) :
    IsStrictlyPositive h ↔ ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re :=
  (isStrictlyPositive_tfae hh).out 1 4

/-- A nonnegative element `h` is strictly positive if and only if `strictlyPositiveApproxUnit h`
forms an increasing approximate unit of `A`. -/
theorem isStrictlyPositive_iff_isIncreasingApproximateUnit {h : A} (hh : 0 ≤ h) :
    IsStrictlyPositive h ↔
      (atTop.map (strictlyPositiveApproxUnit h)).IsIncreasingApproximateUnit :=
  (isStrictlyPositive_tfae hh).out 1 5

/-- If `h` is strictly positive, then `h * A` is dense in `A`. -/
theorem IsStrictlyPositive.dense_range_mul_left {h : A} (hh : IsStrictlyPositive h) :
    Dense (Set.range fun a : A => h * a) :=
  (isStrictlyPositive_iff_dense_range_mul_left hh.1).mp hh

/-- If `h` is strictly positive, then `A * h` is dense in `A`. -/
theorem IsStrictlyPositive.dense_range_mul_right {h : A} (hh : IsStrictlyPositive h) :
    Dense (Set.range fun a : A => a * h) :=
  (isStrictlyPositive_iff_dense_range_mul_right hh.1).mp hh

/-- Every nonzero positive continuous linear functional takes a strictly positive real value on a
strictly positive element. -/
theorem IsStrictlyPositive.pos_of_ne_zero {h : A} (hh : IsStrictlyPositive h)
    {φ : A →P[ℂ] ℂ} (hφ : φ ≠ 0) : 0 < (φ h).re :=
  ((isStrictlyPositive_iff_forall_positiveContinuousLinearMap_pos hh.1).mp hh) φ hφ

/-- A positive continuous linear functional vanishing on a strictly positive element is zero. -/
theorem IsStrictlyPositive.eq_zero_of_apply_eq_zero {h : A} (hh : IsStrictlyPositive h)
    {φ : A →P[ℂ] ℂ} (hφh : φ h = 0) : φ = 0 := by
  by_contra hne
  have hlt := hh.pos_of_ne_zero hne
  rw [hφh, Complex.zero_re] at hlt
  exact lt_irrefl 0 hlt

/-- If `h` is strictly positive, then `strictlyPositiveApproxUnit h` is an increasing approximate
unit of `A`. -/
theorem IsStrictlyPositive.isIncreasingApproximateUnit {h : A} (hh : IsStrictlyPositive h) :
    (atTop.map (strictlyPositiveApproxUnit h)).IsIncreasingApproximateUnit :=
  (isStrictlyPositive_iff_isIncreasingApproximateUnit hh.1).mp hh

/-- If `b : ℕ → A` is a summable sequence of nonnegative elements such that no nonzero positive
continuous linear functional vanishes on every `b n`, then `∑' n, b n` is strictly positive. -/
theorem isStrictlyPositive_tsum_of_forall_apply_eq_zero {b : ℕ → A} (hb : ∀ n, 0 ≤ b n)
    (hsum : Summable b) (hsep : ∀ φ : A →P[ℂ] ℂ, (∀ n, φ (b n) = 0) → φ = 0) :
    IsStrictlyPositive (∑' n, b n) := by
  have hh_nonneg : 0 ≤ ∑' n, b n := tsum_nonneg hb
  refine (isStrictlyPositive_iff_forall_positiveContinuousLinearMap_pos hh_nonneg).mpr ?_
  intro φ hφ
  have hφh : 0 ≤ φ (∑' n, b n) := φ.map_nonneg hh_nonneg
  have hre : 0 ≤ (φ (∑' n, b n)).re := (Complex.nonneg_iff.mp hφh).1
  refine lt_of_le_of_ne hre ?_
  intro hzero
  have hhas : HasSum (fun n => (φ (b n)).re) (φ (∑' n, b n)).re :=
    Complex.reCLM.hasSum (φ.toContinuousLinearMap.hasSum hsum.hasSum)
  have hsum_re : Summable (fun n => (φ (b n)).re) := hhas.summable
  have hterm_nonneg : ∀ n, 0 ≤ (φ (b n)).re := fun n =>
    (Complex.nonneg_iff.mp (φ.map_nonneg (hb n))).1
  have hterm0 : ∀ n, φ (b n) = 0 := fun n => by
    have hle : (φ (b n)).re ≤ 0 := by
      have := hsum_re.le_tsum n (fun k _ => hterm_nonneg k)
      rwa [hhas.tsum_eq, ← hzero] at this
    have hre0 : (φ (b n)).re = 0 := le_antisymm hle (hterm_nonneg n)
    have him0 : (φ (b n)).im = 0 := (Complex.nonneg_iff.mp (φ.map_nonneg (hb n))).2.symm
    exact Complex.ext hre0 him0
  exact hφ (hsep φ hterm0)

/-- If `b : ℕ → A` is any sequence of nonnegative elements such that no nonzero positive continuous
linear functional vanishes on every `b n`, then `A` admits a strictly positive element (obtained as
a weighted sum `∑' n, 2⁻¹ ^ (n + 1) * (1 + ‖b n‖)⁻¹ • b n`). -/
theorem exists_isStrictlyPositive_of_forall_apply_eq_zero {b : ℕ → A} (hb : ∀ n, 0 ≤ b n)
    (hsep : ∀ φ : A →P[ℂ] ℂ, (∀ n, φ (b n) = 0) → φ = 0) :
    ∃ h : A, IsStrictlyPositive h := by
  let w : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n + 1) * (1 + ‖b n‖)⁻¹
  let f : ℕ → A := fun n => w n • b n
  have hw_pos : ∀ n, 0 < w n := fun n => by
    have := norm_nonneg (b n)
    positivity
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => smul_nonneg (hw_pos n).le (hb n)
  have hf_norm : ∀ n, ‖f n‖ ≤ (2 : ℝ)⁻¹ ^ (n + 1) := fun n => by
    rw [norm_smul, Real.norm_of_nonneg (hw_pos n).le]
    dsimp [w]
    rw [mul_assoc]
    refine mul_le_of_le_one_right (by positivity) ?_
    have := norm_nonneg (b n)
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    linarith
  have hgeom : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1)) := by
    simpa [pow_succ'] using summable_geometric_two.mul_left (2 : ℝ)⁻¹
  refine ⟨∑' n, f n, isStrictlyPositive_tsum_of_forall_apply_eq_zero hf_nonneg
    (Summable.of_norm_bounded hgeom hf_norm) fun φ hterm0 => hsep φ fun n => ?_⟩
  have hsmul : ((w n : ℝ) : ℂ) * φ (b n) = 0 := by
    simpa [f, ← Complex.coe_smul, map_smul, smul_eq_mul] using hterm0 n
  exact (mul_eq_zero.mp hsmul).resolve_left (Complex.ofReal_ne_zero.mpr (hw_pos n).ne')

/-- A C⋆-algebra has a strictly positive element if and only if it admits a countable left
approximate unit. -/
theorem exists_isStrictlyPositive_iff_exists_seq_tendsto_mul_right :
    (∃ h : A, IsStrictlyPositive h) ↔
      ∃ u : ℕ → A, ∀ a : A, Tendsto (fun n => u n * a) atTop (𝓝 a) := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨strictlyPositiveApproxUnit h,
      fun a => tendsto_map'_iff.mp (hh.isIncreasingApproximateUnit.tendsto_mul_right a)⟩
  · rintro ⟨u, hu⟩
    refine exists_isStrictlyPositive_of_forall_apply_eq_zero
      (fun n => mul_star_self_nonneg (u n)) fun φ hu0 => ?_
    ext a
    have hvanish : ∀ n, φ (u n * a) = 0 := fun n => by
      have hcs := PositiveLinearMap.norm_map_mul_star_sq_le φ (u n) (star a)
      rw [star_star, hu0 n, norm_zero, zero_mul] at hcs
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (φ (u n * a))])
    exact tendsto_nhds_unique (((map_continuous φ).tendsto a).comp (hu a))
      (by simp [Function.comp_def, hvanish])

/-- A C⋆-algebra has a strictly positive element (i.e., is σ-unital) if and only if it admits a
sequential increasing approximate unit (Blackadar II.4.2.4). -/
theorem exists_isStrictlyPositive_iff_exists_seq_isIncreasingApproximateUnit :
    (∃ h : A, IsStrictlyPositive h) ↔
      ∃ u : ℕ → A, (atTop.map u).IsIncreasingApproximateUnit := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨strictlyPositiveApproxUnit h, hh.isIncreasingApproximateUnit⟩
  · rintro ⟨u, hu⟩
    exact exists_isStrictlyPositive_iff_exists_seq_tendsto_mul_right.mpr
      ⟨u, fun a => tendsto_map'_iff.mp (hu.tendsto_mul_right a)⟩

/-- A C⋆-algebra has a strictly positive element if and only if it admits a monotone increasing
sequence of positive strict contractions forming an increasing approximate unit. -/
theorem exists_isStrictlyPositive_iff_exists_seq_monotone_isIncreasingApproximateUnit :
    (∃ h : A, IsStrictlyPositive h) ↔
      ∃ u : ℕ → A, Monotone u ∧ (∀ n, 0 ≤ u n ∧ ‖u n‖ < 1) ∧
        (atTop.map u).IsIncreasingApproximateUnit := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨strictlyPositiveApproxUnit h, strictlyPositiveApproxUnit_monotone h,
      fun n => ⟨strictlyPositiveApproxUnit_nonneg h n, norm_strictlyPositiveApproxUnit_lt_one h n⟩,
      hh.isIncreasingApproximateUnit⟩
  · rintro ⟨u, -, -, hu⟩
    exact exists_isStrictlyPositive_iff_exists_seq_isIncreasingApproximateUnit.mpr ⟨u, hu⟩

/-- Every separable C⋆-algebra admits a strictly positive element (hence is σ-unital). -/
theorem exists_isStrictlyPositive_of_separableSpace [TopologicalSpace.SeparableSpace A] :
    ∃ h : A, IsStrictlyPositive h := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq A
  refine exists_isStrictlyPositive_of_forall_apply_eq_zero
    (fun n => star_mul_self_nonneg (d n)) fun φ hd0 => ?_
  have hvanish : ∀ n, φ (d n) = 0 := fun n => by
    have hcs := φ.norm_map_sq_le_opNorm_mul (d n)
    rw [hd0 n, norm_zero, mul_zero] at hcs
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (φ (d n))])
  have hcl : Set.univ ⊆ {a : A | φ a = 0} :=
    hd.closure_eq ▸ closure_minimal (Set.range_subset_iff.mpr hvanish)
      (isClosed_eq (map_continuous φ) continuous_const)
  exact DFunLike.ext _ _ fun a => hcl (Set.mem_univ a)

/-- Every separable C⋆-algebra admits a monotone increasing sequence of positive strict contractions
forming an increasing approximate unit. -/
theorem exists_seq_monotone_isIncreasingApproximateUnit_of_separableSpace
    [TopologicalSpace.SeparableSpace A] :
    ∃ u : ℕ → A, Monotone u ∧ (∀ n, 0 ≤ u n ∧ ‖u n‖ < 1) ∧
      (atTop.map u).IsIncreasingApproximateUnit :=
  exists_isStrictlyPositive_iff_exists_seq_monotone_isIncreasingApproximateUnit.mp
    exists_isStrictlyPositive_of_separableSpace

end NonUnital

section Unital

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- In a unital C⋆-algebra, `TauCeti.CStarAlgebra.IsStrictlyPositive h` coincides with Mathlib's
`_root_.IsStrictlyPositive h` (`0 ≤ h ∧ IsUnit h`). -/
theorem isStrictlyPositive_iff_root {h : D} :
    IsStrictlyPositive h ↔ _root_.IsStrictlyPositive h := by
  constructor
  · intro hh
    refine ⟨hh.1, ?_⟩
    nontriviality D
    rw [← spectrum.zero_notMem_iff ℂ]
    intro hmem
    have : IsStarNormal h := hh.1.isSelfAdjoint.isStarNormal
    obtain ⟨ω, -, hω_norm, hω_pow⟩ :=
      exists_positiveContinuousLinearMap_apply_star_pow_mul_pow_eq_of_mem_spectrum hmem
    have hωh : ω h = 0 := by simpa using hω_pow 0 1
    have hω0 : ω = 0 := hh.eq_zero_of_apply_eq_zero hωh
    have h0 : ‖(ω : D →L[ℂ] ℂ)‖ = 0 := by simp [hω0]
    linarith
  · rintro ⟨hh₀, ⟨u, rfl⟩⟩
    refine ⟨hh₀, dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun a => subset_closure ?_)⟩
    exact ⟨(u⁻¹ : Dˣ) * a * (u⁻¹ : Dˣ), by simp [mul_assoc]⟩

end Unital

end TauCeti.CStarAlgebra

end
