/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import TauCeti.Analysis.CStarAlgebra.Hereditary.Ideal
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Algebra.Star.Basic
import TauCeti.Analysis.CStarAlgebra.ApproximateUnit.Basic
import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Basic
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Decomposition
import TauCeti.Analysis.InnerProductSpace.Positive.VectorFunctional
import TauCeti.Analysis.LocallyConvex.Mazur
import TauCeti.Analysis.Normed.Operator.Dense
import TauCeti.Topology.Instances.NNReal

/-!
# Strictly positive elements and σ-unital C⋆-algebras

An element `h` of a (possibly nonunital) complex C⋆-algebra `A` is *strictly positive*
(`TauCeti.CStarAlgebra.IsStrictlyPositive h`, defined in
`TauCeti.Analysis.CStarAlgebra.Hereditary.Ideal`) if `0 ≤ h` and the corner `h * A * h`
is dense in `A`. This generalizes the unital notion `_root_.IsStrictlyPositive` (`0 ≤ h ∧ IsUnit h`,
recovered in `TauCeti.CStarAlgebra.IsStrictlyPositive.iff_of_unital`), and provides the
standard characterization of σ-unital C⋆-algebras (those admitting a countable approximate unit).

For any `0 ≤ h`, the continuous functional calculus yields the monotone sequence of positive strict
contractions
`strictlyPositiveApproximateUnit h n = cfcₙ (fun t : ℝ≥0 => t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) h`,
which satisfies `‖h - h * eₙ‖ ≤ (n + 1)⁻¹`, `eₙ * h → h`, `h * eₙ → h`, and `eₙ * a ∈ h * A` for
every `a : A`. When `h` is strictly positive, `eₙ` is an increasing approximate unit of `A`.

## Main definitions and results

* `TauCeti.CStarAlgebra.strictlyPositiveApproximateUnit`: the canonical monotone sequence
  `h * ((n + 1)⁻¹ + h)⁻¹` built via the nonunital continuous functional calculus, together with
  `strictlyPositiveApproximateUnit_def`, `inr_strictlyPositiveApproximateUnit_eq`,
  `map_strictlyPositiveApproximateUnit`, `tendsto_strictlyPositiveApproximateUnit_mul_self`, and
  `tendsto_mul_strictlyPositiveApproximateUnit_self`.
* `TauCeti.CStarAlgebra.isStrictlyPositive_tfae`: for `0 ≤ h`, the five standard conditions
  (Blackadar II.4.2.1) are equivalent:
  1. `IsStrictlyPositive h`;
  2. `Dense (Set.range (h * ·))`;
  3. `Dense (Set.range (· * h))`;
  4. `∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re`;
  5. `(Filter.atTop.map (strictlyPositiveApproximateUnit h)).IsIncreasingApproximateUnit`.
* `TauCeti.CStarAlgebra.IsStrictlyPositive.of_le`, `add_nonneg`, `nonneg_add`, `smul`, `map`,
  `dense_range_of_isNondegenerate`, and
  `tendsto_apply_strictlyPositiveApproximateUnit_of_isNondegenerate`:
  order, cone, dense-range *-homomorphism permanence, and nondegenerate-representation actions
  of strict positivity.
* `TauCeti.CStarAlgebra.IsStrictlyPositive.iff_of_unital`:
  in a unital C⋆-algebra, `TauCeti.CStarAlgebra.IsStrictlyPositive h` coincides with
  `0 ≤ h ∧ IsUnit h`.
* `TauCeti.CStarAlgebra.isStrictlyPositive_tsum_of_forall_apply_eq_zero_imp_eq_zero` and
  `exists_isStrictlyPositive_of_forall_apply_eq_zero_imp_eq_zero`: constructing strictly positive
  elements from positive families not jointly annihilated by any nonzero positive functional.
* `TauCeti.CStarAlgebra.exists_isStrictlyPositive_iff_exists_seq_isIncreasingApproximateUnit`,
  `exists_isStrictlyPositive_iff_exists_seq_monotone_isIncreasingApproximateUnit`,
  `exists_isStrictlyPositive_iff_exists_seq_tendsto_mul_right`, and
  `exists_isStrictlyPositive_iff_exists_seq_tendsto_mul_left`: characterizations of σ-unital
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

theorem IsStrictlyPositive.dense_range_mul_mul {h : A} (hh : CStarAlgebra.IsStrictlyPositive h) :
    Dense (Set.range fun a : A => h * a * h) :=
  dense_iff_closure_eq.mpr hh.closure_range_eq_univ

/-- If `h` is strictly positive, then `h * A` is dense in `A`. -/
theorem IsStrictlyPositive.dense_range_mul_left {h : A} (hh : CStarAlgebra.IsStrictlyPositive h) :
    Dense (Set.range fun a : A => h * a) := by
  refine hh.dense_range_mul_mul.mono ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨a * h, (mul_assoc h a h).symm⟩

/-- If `h` is strictly positive, then `A * h` is dense in `A`. -/
theorem IsStrictlyPositive.dense_range_mul_right {h : A} (hh : CStarAlgebra.IsStrictlyPositive h) :
    Dense (Set.range fun a : A => a * h) := by
  refine hh.dense_range_mul_mul.mono ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨h * a, rfl⟩

/-- `0 : A` is strictly positive if and only if `A` is subsingleton (the zero C⋆-algebra). -/
@[simp]
theorem isStrictlyPositive_zero_iff :
    CStarAlgebra.IsStrictlyPositive (0 : A) ↔ Subsingleton A := by
  constructor
  · intro h0
    have hrange : (Set.range fun a : A => (0 : A) * a * 0) ⊆ {0} := by
      rintro _ ⟨a, rfl⟩
      simp
    have hdense : Dense ({0} : Set A) := h0.dense_range_mul_mul.mono hrange
    have huniv : ({0} : Set A) = Set.univ := by
      rw [← isClosed_singleton.closure_eq, hdense.closure_eq]
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ ({0} : Set A) := huniv ▸ Set.mem_univ a
    have hb : b ∈ ({0} : Set A) := huniv ▸ Set.mem_univ b
    rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  · intro _
    exact isStrictlyPositive_def.mpr
      ⟨le_rfl, Set.eq_univ_of_forall fun a => subset_closure ⟨0, Subsingleton.elim _ _⟩⟩

/-- In a subsingleton (zero) C⋆-algebra, every element is strictly positive. -/
@[nontriviality]
theorem IsStrictlyPositive.of_subsingleton [Subsingleton A] {a : A} :
    CStarAlgebra.IsStrictlyPositive a :=
  Subsingleton.elim a 0 ▸ isStrictlyPositive_zero_iff.mpr inferInstance

end Basic

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The canonical sequence `h * ((n + 1)⁻¹ + h)⁻¹` associated with an element `h : A` via the
nonunital continuous functional calculus. For `0 ≤ h`, this is a monotone increasing sequence of
positive strict contractions that forms an increasing approximate unit of `A` if and only if `h` is
strictly positive. -/
def strictlyPositiveApproximateUnit (h : A) (n : ℕ) : A :=
  cfcₙ (fun t : ℝ≥0 => t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) h

/-- Definitional characterization of `strictlyPositiveApproximateUnit` via `cfcₙ`. -/
theorem strictlyPositiveApproximateUnit_def (h : A) (n : ℕ) :
    strictlyPositiveApproximateUnit h n =
      cfcₙ (fun t : ℝ≥0 => t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) h :=
  (rfl)

@[simp]
theorem strictlyPositiveApproximateUnit_zero (n : ℕ) :
    strictlyPositiveApproximateUnit (0 : A) n = 0 := by
  simp [strictlyPositiveApproximateUnit]

/-- At a nonpositive element, every term of `strictlyPositiveApproximateUnit` vanishes. -/
@[simp]
theorem strictlyPositiveApproximateUnit_of_not_nonneg {h : A} (hh : ¬ 0 ≤ h) (n : ℕ) :
    strictlyPositiveApproximateUnit h n = 0 := by
  rw [strictlyPositiveApproximateUnit_def]
  exact cfcₙ_apply_of_not_predicate _ hh

/-- Each term of `strictlyPositiveApproximateUnit h` is nonnegative. -/
theorem strictlyPositiveApproximateUnit_nonneg (h : A) (n : ℕ) :
    0 ≤ strictlyPositiveApproximateUnit h n :=
  cfcₙ_nonneg_of_predicate

/-- Each term of `strictlyPositiveApproximateUnit h` has norm strictly less than `1`. -/
theorem norm_strictlyPositiveApproximateUnit_lt_one (h : A) (n : ℕ) :
    ‖strictlyPositiveApproximateUnit h n‖ < 1 := by
  have hlt : ‖strictlyPositiveApproximateUnit h n‖₊ < 1 := by
    refine nnNorm_cfcₙ_nnreal_lt fun t _ => ?_
    have hc : (0 : ℝ≥0) < ((n + 1 : ℕ) : ℝ≥0)⁻¹ := by positivity
    have hden : (0 : ℝ≥0) < ((n + 1 : ℕ) : ℝ≥0)⁻¹ + t := add_pos_of_pos_of_nonneg hc t.property
    rw [← div_eq_mul_inv, div_lt_one hden]
    exact lt_add_of_pos_left t hc
  exact_mod_cast hlt

/-- Each term of `strictlyPositiveApproximateUnit h` has norm at most `1`. -/
theorem norm_strictlyPositiveApproximateUnit_le_one (h : A) (n : ℕ) :
    ‖strictlyPositiveApproximateUnit h n‖ ≤ 1 :=
  (norm_strictlyPositiveApproximateUnit_lt_one h n).le

/-- The sequence `strictlyPositiveApproximateUnit h` is monotone increasing. -/
theorem strictlyPositiveApproximateUnit_monotone (h : A) :
    Monotone (strictlyPositiveApproximateUnit h) := by
  intro m n hmn
  have hcont : ∀ k : ℕ, ContinuousOn (fun t : ℝ≥0 => t * (((k + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹)
      (quasispectrum ℝ≥0 h) := fun k =>
    (NNReal.continuous_mul_inv_add (by positivity : (0 : ℝ≥0) < ((k + 1 : ℕ) : ℝ≥0)⁻¹)).continuousOn
  refine cfcₙ_mono (a := h) (fun t _ => ?_) (hcont m) (hcont n) (by simp) (by simp)
  gcongr

/-- Every element `h` commutes with every `strictlyPositiveApproximateUnit h n`. -/
theorem commute_strictlyPositiveApproximateUnit (h : A) (n : ℕ) :
    Commute h (strictlyPositiveApproximateUnit h n) :=
  ((Commute.refl h).cfcₙ_nnreal _).symm

/-- Nonunital *-algebra homomorphisms preserve `strictlyPositiveApproximateUnit` on nonnegative
elements. -/
theorem map_strictlyPositiveApproximateUnit {B F : Type*} [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B]
    [StarHomClass F A B] (f : F) {h : A} (hh : 0 ≤ h) (n : ℕ) :
    f (strictlyPositiveApproximateUnit h n) = strictlyPositiveApproximateUnit (f h) n := by
  rw [strictlyPositiveApproximateUnit_def, strictlyPositiveApproximateUnit_def]
  exact NonUnitalStarAlgHomClass.map_cfcₙ f _ h
    (NNReal.continuous_mul_inv_add (by positivity : (0 : ℝ≥0) < ((n + 1 : ℕ) : ℝ≥0)⁻¹)).continuousOn
    (by simp) (map_continuous f) hh (map_nonneg f hh)

/-- Algebraic `cfcₙ` identity for the approximation error
`h - h * strictlyPositiveApproximateUnit h n`. -/
private theorem sub_mul_strictlyPositiveApproximateUnit_eq {h : A} (hh : 0 ≤ h) (n : ℕ) :
    h - h * strictlyPositiveApproximateUnit h n =
      cfcₙ (fun t : ℝ≥0 =>
        t * (((n + 1 : ℕ) : ℝ≥0)⁻¹ * (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹)) h := by
  let c : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)⁻¹
  have hc_pos : 0 < c := by positivity
  have hf_cont : Continuous (fun t : ℝ≥0 => t * (c + t)⁻¹) := NNReal.continuous_mul_inv_add hc_pos
  have htf_cont : Continuous (fun t : ℝ≥0 => t * (t * (c + t)⁻¹)) :=
    continuous_id.mul hf_cont
  have hg_cont : Continuous (fun t : ℝ≥0 => t * (c * (c + t)⁻¹)) :=
    continuous_id.mul (continuous_const.mul (NNReal.continuous_inv_add hc_pos))
  have hmul : h * strictlyPositiveApproximateUnit h n =
      cfcₙ (fun t : ℝ≥0 => t * (t * (c + t)⁻¹)) h := by
    calc h * strictlyPositiveApproximateUnit h n
        = cfcₙ (fun t : ℝ≥0 => t) h * cfcₙ (fun t : ℝ≥0 => t * (c + t)⁻¹) h := by
          rw [strictlyPositiveApproximateUnit, cfcₙ_id' ℝ≥0 h hh]
      _ = cfcₙ (fun t : ℝ≥0 => t * (t * (c + t)⁻¹)) h := by
          rw [← cfcₙ_mul (fun t : ℝ≥0 => t) _ h (continuousOn_id' _) rfl hf_cont.continuousOn
            (by simp)]
  have hsum : cfcₙ (fun t : ℝ≥0 => t * (t * (c + t)⁻¹)) h +
      cfcₙ (fun t : ℝ≥0 => t * (c * (c + t)⁻¹)) h = h := by
    rw [← cfcₙ_add (fun t : ℝ≥0 => t * (t * (c + t)⁻¹))
      (fun t : ℝ≥0 => t * (c * (c + t)⁻¹)) h htf_cont.continuousOn (by simp)
      hg_cont.continuousOn (by simp)]
    conv_rhs => rw [← cfcₙ_id' ℝ≥0 h hh]
    refine cfcₙ_congr fun t _ => ?_
    have hden : c + t ≠ 0 := (add_pos_of_pos_of_nonneg hc_pos t.property).ne'
    calc t * (t * (c + t)⁻¹) + t * (c * (c + t)⁻¹)
        = t * ((c + t) * (c + t)⁻¹) := by ring
      _ = t * 1 := by rw [mul_inv_cancel₀ hden]
      _ = t := mul_one t
  rw [hmul, sub_eq_iff_eq_add', hsum]

/-- Quantitative right-approximation error on `h`:
`‖h - h * strictlyPositiveApproximateUnit h n‖ ≤ (n + 1)⁻¹`. -/
theorem norm_sub_mul_strictlyPositiveApproximateUnit_le {h : A} (hh : 0 ≤ h) (n : ℕ) :
    ‖h - h * strictlyPositiveApproximateUnit h n‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
  let c : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)⁻¹
  have hc_pos : 0 < c := by positivity
  rw [sub_mul_strictlyPositiveApproximateUnit_eq hh n]
  have hle : ‖cfcₙ (fun t : ℝ≥0 => t * (c * (c + t)⁻¹)) h‖₊ ≤ c := by
    refine nnNorm_cfcₙ_nnreal_le fun t _ => ?_
    have hden : (0 : ℝ≥0) < c + t := add_pos_of_pos_of_nonneg hc_pos t.property
    calc t * (c * (c + t)⁻¹) = c * (t / (c + t)) := by rw [div_eq_mul_inv]; ring
      _ ≤ c * 1 := by
          gcongr
          exact (div_le_one hden).mpr le_add_self
      _ = c := mul_one c
  exact_mod_cast hle

/-- Quantitative left-approximation error on `h`:
`‖h - strictlyPositiveApproximateUnit h n * h‖ ≤ (n + 1)⁻¹`. -/
theorem norm_sub_strictlyPositiveApproximateUnit_mul_le {h : A} (hh : 0 ≤ h) (n : ℕ) :
    ‖h - strictlyPositiveApproximateUnit h n * h‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
  rw [← (commute_strictlyPositiveApproximateUnit h n).eq]
  exact norm_sub_mul_strictlyPositiveApproximateUnit_le hh n

/-- For `0 ≤ h`, `strictlyPositiveApproximateUnit h n * h` converges to `h` in norm. -/
theorem tendsto_strictlyPositiveApproximateUnit_mul_self {h : A} (hh : 0 ≤ h) :
    Tendsto (fun n => strictlyPositiveApproximateUnit h n * h) atTop (𝓝 h) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [norm_sub_rev]
  simpa only [Nat.cast_add, Nat.cast_one] using
    norm_sub_strictlyPositiveApproximateUnit_mul_le hh n

/-- For `0 ≤ h`, `h * strictlyPositiveApproximateUnit h n` converges to `h` in norm. -/
theorem tendsto_mul_strictlyPositiveApproximateUnit_self {h : A} (hh : 0 ≤ h) :
    Tendsto (fun n => h * strictlyPositiveApproximateUnit h n) atTop (𝓝 h) :=
  (tendsto_strictlyPositiveApproximateUnit_mul_self hh).congr fun n =>
    (commute_strictlyPositiveApproximateUnit h n).symm.eq

/-- Factorization of `strictlyPositiveApproximateUnit h n` in the unitization `A⁺¹`:
`(eₙ : A⁺¹) = (h : A⁺¹) * rₙ = rₙ * (h : A⁺¹)` where
`rₙ = cfc (fun t => ((n + 1)⁻¹ + t)⁻¹) (h : A⁺¹)`. -/
theorem inr_strictlyPositiveApproximateUnit_eq (h : A) (n : ℕ) :
    ((strictlyPositiveApproximateUnit h n : A) : A⁺¹) =
        (h : A⁺¹) * cfc (fun t : ℝ≥0 => (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) (h : A⁺¹) ∧
      ((strictlyPositiveApproximateUnit h n : A) : A⁺¹) =
        cfc (fun t : ℝ≥0 => (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) (h : A⁺¹) * (h : A⁺¹) := by
  by_cases hh : 0 ≤ h
  · let c : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)⁻¹
    have hh' : 0 ≤ (h : A⁺¹) := (Unitization.inr_nonneg_iff ℂ).mpr hh
    have hr_cont : ContinuousOn (fun t : ℝ≥0 => (c + t)⁻¹) (spectrum ℝ≥0 (h : A⁺¹)) :=
      (NNReal.continuous_inv_add (by positivity : 0 < c)).continuousOn
    have hL : ((strictlyPositiveApproximateUnit h n : A) : A⁺¹) =
        (h : A⁺¹) * cfc (fun t : ℝ≥0 => (c + t)⁻¹) (h : A⁺¹) := by
      rw [strictlyPositiveApproximateUnit_def,
        Unitization.nnreal_cfcₙ_eq_cfc_inr h (fun t : ℝ≥0 => t * (c + t)⁻¹) (by simp),
        cfc_mul (fun t : ℝ≥0 => t) (fun t : ℝ≥0 => (c + t)⁻¹) (h : A⁺¹)
          (continuousOn_id' _) hr_cont, cfc_id' ℝ≥0 (h : A⁺¹) hh']
    exact ⟨hL, hL.trans ((Commute.refl (h : A⁺¹)).cfc_nnreal _).symm.eq⟩
  · simp [strictlyPositiveApproximateUnit_of_not_nonneg hh,
      cfc_apply_of_not_predicate _ fun h1 => hh ((Unitization.inr_nonneg_iff ℂ).mp h1)]

/-- Every left multiple `strictlyPositiveApproximateUnit h n * a` belongs to `h * A`. -/
theorem strictlyPositiveApproximateUnit_mul_mem_range (h : A) (n : ℕ) (a : A) :
    strictlyPositiveApproximateUnit h n * a ∈ Set.range fun b : A => h * b := by
  let r : A⁺¹ := cfc (fun t : ℝ≥0 => (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) (h : A⁺¹)
  refine ⟨r.fst • a + r.snd * a, Unitization.inr_injective (R := ℂ) ?_⟩
  rw [Unitization.inr_mul, Unitization.inr_mul,
    (inr_strictlyPositiveApproximateUnit_eq h n).1, mul_assoc, Unitization.mul_inr_eq_inr r a]

/-- Every right multiple `a * strictlyPositiveApproximateUnit h n` belongs to `A * h`. -/
theorem mul_strictlyPositiveApproximateUnit_mem_range (h : A) (n : ℕ) (a : A) :
    a * strictlyPositiveApproximateUnit h n ∈ Set.range fun b : A => b * h := by
  let r : A⁺¹ := cfc (fun t : ℝ≥0 => (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) (h : A⁺¹)
  refine ⟨r.fst • a + a * r.snd, Unitization.inr_injective (R := ℂ) ?_⟩
  rw [Unitization.inr_mul, Unitization.inr_mul,
    (inr_strictlyPositiveApproximateUnit_eq h n).2, ← mul_assoc, Unitization.inr_mul_eq_inr a r]

/-- Every corner element
`strictlyPositiveApproximateUnit h n * a * strictlyPositiveApproximateUnit h n` belongs to
`h * A * h`. -/
theorem strictlyPositiveApproximateUnit_mul_mul_mem_range (h : A) (n : ℕ) (a : A) :
    strictlyPositiveApproximateUnit h n * a * strictlyPositiveApproximateUnit h n ∈
      Set.range fun b : A => h * b * h := by
  let r : A⁺¹ := cfc (fun t : ℝ≥0 => (((n + 1 : ℕ) : ℝ≥0)⁻¹ + t)⁻¹) (h : A⁺¹)
  let b₁ : A := r.fst • a + r.snd * a
  let b : A := r.fst • b₁ + b₁ * r.snd
  refine ⟨b, Unitization.inr_injective (R := ℂ) ?_⟩
  have ⟨hL, hR⟩ := inr_strictlyPositiveApproximateUnit_eq h n
  simp only [Unitization.inr_mul]
  calc (h : A⁺¹) * (b : A⁺¹) * (h : A⁺¹)
      = (h : A⁺¹) * ((r * (a : A⁺¹)) * r) * (h : A⁺¹) := by
        rw [Unitization.mul_inr_eq_inr r a, Unitization.inr_mul_eq_inr b₁ r]
    _ = ((h : A⁺¹) * r) * (a : A⁺¹) * (r * (h : A⁺¹)) := by noncomm_ring
    _ = ((strictlyPositiveApproximateUnit h n : A) : A⁺¹) * (a : A⁺¹) *
          ((strictlyPositiveApproximateUnit h n : A) : A⁺¹) := by rw [← hL, ← hR]

/-- For every `a ∈ closure (h * A)`, `strictlyPositiveApproximateUnit h n * a → a` in norm. -/
theorem tendsto_strictlyPositiveApproximateUnit_mul_of_mem_closure_range_mul_left {h : A}
    (hh : 0 ≤ h) {a : A} (ha : a ∈ closure (Set.range fun b : A => h * b)) :
    Tendsto (fun n => strictlyPositiveApproximateUnit h n * a) atTop (𝓝 a) := by
  let K : Submodule ℂ A := (LinearMap.range (LinearMap.mul ℂ A h)).topologicalClosure
  have hrange : (LinearMap.range (LinearMap.mul ℂ A h) : Set A) = Set.range fun b : A => h * b := by
    ext x
    simp [LinearMap.mem_range]
  have hK : (K : Set A) = closure (Set.range fun b : A => h * b) := by
    rw [Submodule.topologicalClosure_coe, hrange]
  have haK : a ∈ K := by
    rw [← SetLike.mem_coe, hK]
    exact ha
  have hdense : Dense (((↑) : K → A) ⁻¹' Set.range fun b : A => h * b) := by
    rw [Subtype.dense_iff]
    intro x hx
    rw [hK] at hx
    refine closure_mono (fun y hy => ?_) hx
    exact ⟨⟨y, hK.symm ▸ subset_closure hy⟩, hy, rfl⟩
  refine ContinuousLinearMap.tendsto_apply_of_dense hdense (C := 1)
    (f := fun n => (ContinuousLinearMap.mul ℂ A (strictlyPositiveApproximateUnit h n)).comp
      K.subtypeL)
    (g := K.subtypeL)
    (.of_forall fun n => by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact (mul_le_mul (ContinuousLinearMap.opNorm_mul_apply_le ℂ A _) K.norm_subtypeL_le
        (norm_nonneg K.subtypeL) (norm_nonneg _)).trans <| by
          simpa using norm_strictlyPositiveApproximateUnit_le_one h n)
    ?_ ⟨a, haK⟩
  rintro ⟨_, -⟩ ⟨b, rfl⟩
  simpa [mul_assoc] using (tendsto_strictlyPositiveApproximateUnit_mul_self hh).mul_const b

/-- For every `a ∈ closure (A * h)`, `a * strictlyPositiveApproximateUnit h n → a` in norm. -/
theorem tendsto_mul_strictlyPositiveApproximateUnit_of_mem_closure_range_mul_right {h : A}
    (hh : 0 ≤ h) {a : A} (ha : a ∈ closure (Set.range fun b : A => b * h)) :
    Tendsto (fun n => a * strictlyPositiveApproximateUnit h n) atTop (𝓝 a) := by
  have ha' : star a ∈ closure (Set.range fun b : A => h * b) := by
    rw [← hh.isSelfAdjoint.image_star_range_mul_right]
    exact continuous_star.continuousOn.image_closure (Set.mem_image_of_mem star ha)
  have hlim := (continuous_star.tendsto _).comp
    (tendsto_strictlyPositiveApproximateUnit_mul_of_mem_closure_range_mul_left hh ha')
  rw [star_star] at hlim
  refine hlim.congr fun n => ?_
  dsimp only [Function.comp_apply]
  rw [star_mul, star_star,
    (IsSelfAdjoint.of_nonneg (strictlyPositiveApproximateUnit_nonneg h n)).star_eq]

omit [StarOrderedRing A] in
private theorem eq_zero_of_forall_re_apply_pos {h : A}
    (hpos : ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re) {φ : A →P[ℂ] ℂ} (hφh : φ h = 0) :
    φ = 0 := by
  by_contra hne
  have hlt := hpos φ hne
  rw [hφh, Complex.zero_re] at hlt
  exact lt_irrefl 0 hlt

/-- If `0 ≤ h` is strictly positive on every nonzero positive functional of `A`, then `π h` has
dense range in any nondegenerate Hilbert-space representation `π` of `A`. -/
private theorem dense_range_of_forall_re_apply_pos {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : π.IsNondegenerate) {h : A} (hh : 0 ≤ h)
    (hpos : ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re) :
    Dense (Set.range (π h)) := by
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range,
    Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    ContinuousLinearMap.orthogonal_range, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
    hh.isSelfAdjoint.star_eq, Submodule.eq_bot_iff]
  intro v hv
  have hπhv : π h v = 0 := LinearMap.mem_ker.mp hv
  let φv : A →P[ℂ] ℂ := PositiveContinuousLinearMap.ofClass
    ((ContinuousLinearMap.innerPositiveLinearMap ℂ v).comp (.ofClass π))
  have hφv_apply : ∀ b, φv b = ⟪v, π b v⟫_ℂ := fun b => by
    simp [φv, PositiveLinearMap.ofClass]
  have hφv0 : φv = 0 := eq_zero_of_forall_re_apply_pos hpos <| by
    rw [hφv_apply h, hπhv, inner_zero_right]
  refine (NonUnitalStarAlgHom.isNondegenerate_iff_forall_apply_eq_zero.mp hπ) v fun b => ?_
  have hinner0 : ⟪π b v, π b v⟫_ℂ = 0 := by
    have hval : ⟪v, π (star b * b) v⟫_ℂ = 0 := by
      rw [← hφv_apply (star b * b), hφv0]
      simp
    rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp,
      ContinuousLinearMap.adjoint_inner_right] at hval
    exact hval
  exact inner_self_eq_zero.mp hinner0

/-- If `0 ≤ h` is strictly positive on every nonzero positive functional of `A`, then in any
nondegenerate Hilbert-space representation `π` of `A`, `π (strictlyPositiveApproximateUnit h n)`
converges strongly to the identity. -/
private theorem tendsto_apply_strictlyPositiveApproximateUnit_of_forall_re_apply_pos {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : π.IsNondegenerate) {h : A} (hh : 0 ≤ h)
    (hpos : ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re) (η : H) :
    Tendsto (fun n => π (strictlyPositiveApproximateUnit h n) η) atTop (𝓝 η) := by
  refine ContinuousLinearMap.tendsto_apply_of_dense
    (dense_range_of_forall_re_apply_pos π hπ hh hpos) (C := 1)
    (f := fun n => π (strictlyPositiveApproximateUnit h n)) (g := ContinuousLinearMap.id ℂ H)
    (.of_forall fun n =>
      (NonUnitalStarAlgHom.norm_apply_le π _).trans
        (norm_strictlyPositiveApproximateUnit_le_one h n))
    ?_ η
  rintro _ ⟨w, rfl⟩
  have hlim := ((ContinuousLinearMap.apply ℂ H w).continuous.tendsto _).comp
    (((map_continuous π).tendsto h).comp (tendsto_strictlyPositiveApproximateUnit_mul_self hh))
  simpa [Function.comp_def, map_mul] using hlim

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
    (fun n => subset_closure (strictlyPositiveApproximateUnit_mul_mem_range h n a)) ?_
  rw [tendsto_toWeakSpace_iff_forall_positiveContinuousLinearMap]
  intro ω
  let ξ := ω.unitization.toPositiveLinearMap.gnsVector
  have hstrong : Tendsto (fun n => ω.gnsInr (strictlyPositiveApproximateUnit h n) (ω.gnsInr a ξ))
      atTop (𝓝 (ω.gnsInr a ξ)) :=
    tendsto_apply_strictlyPositiveApproximateUnit_of_forall_re_apply_pos ω.gnsInr
      ω.isNondegenerate_gnsInr hh hpos (ω.gnsInr a ξ)
  have hinner : Tendsto
      (fun n => ⟪ξ, ω.gnsInr (strictlyPositiveApproximateUnit h n) (ω.gnsInr a ξ)⟫_ℂ)
      atTop (𝓝 ⟪ξ, ω.gnsInr a ξ⟫_ℂ) :=
    ((continuous_const.inner continuous_id).tendsto _).comp hstrong
  rw [← ω.inner_gnsVector_gnsInr a]
  refine hinner.congr fun n => ?_
  rw [← ω.inner_gnsVector_gnsInr, map_mul, mul_apply_eq_comp]

/-- Characterizations of strictly positive elements in a (possibly nonunital) C⋆-algebra
(Blackadar II.4.2.1): for `0 ≤ h`, strict positivity, density of `h * A`, density of `A * h`,
strict positivity under every nonzero positive linear functional, and
`strictlyPositiveApproximateUnit h` being an increasing approximate unit are all equivalent. -/
theorem isStrictlyPositive_tfae {h : A} (hh : 0 ≤ h) :
    List.TFAE
      [ CStarAlgebra.IsStrictlyPositive h,
        Dense (Set.range fun a : A => h * a),
        Dense (Set.range fun a : A => a * h),
        ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re,
        (atTop.map (strictlyPositiveApproximateUnit h)).IsIncreasingApproximateUnit ] := by
  tfae_have 1 → 2 := IsStrictlyPositive.dense_range_mul_left
  tfae_have 2 → 3 := fun hd =>
    hh.isSelfAdjoint.image_star_range_mul_left ▸
      star_involutive.surjective.denseRange.dense_image continuous_star hd
  tfae_have 3 → 4 := fun hd φ hφ => by
    have hre : 0 ≤ (φ h).re := (Complex.nonneg_iff.mp (φ.map_nonneg hh)).1
    refine lt_of_le_of_ne hre fun hzero => ?_
    have hφh0 : φ h = 0 := PositiveLinearMap.map_eq_zero_of_re_eq_zero φ hh hzero.symm
    let r : A := CFC.sqrt h
    have hr_star : star r = r := (CFC.sqrt_nonneg h).isSelfAdjoint.star_eq
    have hrr : r * r = h := CFC.sqrt_mul_sqrt_self h
    have hvanish : Set.EqOn (φ : A → ℂ) (fun _ => 0) (Set.range fun a : A => a * h) := by
      rintro _ ⟨a, rfl⟩
      have h0 := PositiveLinearMap.map_mul_eq_zero_of_map_star_mul_self_eq_zero φ (y := r)
        (by rwa [hr_star, hrr]) (a * r)
      rwa [mul_assoc, hrr] at h0
    have hzero_fn := Continuous.ext_on hd (map_continuous φ) continuous_const hvanish
    exact hφ (DFunLike.ext _ _ fun a => congrFun hzero_fn a)
  tfae_have 4 → 5 := fun hpos => by
    have hdense := dense_range_mul_left_of_forall_pos hh hpos
    refine Filter.IsIncreasingApproximateUnit.of_tendsto_mul_right
      (eventually_map.mpr (Eventually.of_forall (strictlyPositiveApproximateUnit_nonneg h)))
      (eventually_map.mpr (Eventually.of_forall (norm_strictlyPositiveApproximateUnit_le_one h)))
      fun a => tendsto_map'_iff.mpr ?_
    exact tendsto_strictlyPositiveApproximateUnit_mul_of_mem_closure_range_mul_left hh (hdense a)
  tfae_have 5 → 1 := fun hl => by
    refine isStrictlyPositive_def.mpr ⟨hh, Set.eq_univ_of_forall fun a => ?_⟩
    exact mem_closure_of_tendsto (tendsto_map'_iff.mp (hl.tendsto_mul_self a))
      (Eventually.of_forall fun n => strictlyPositiveApproximateUnit_mul_mul_mem_range h n a)
  tfae_finish

/-- A nonnegative element `h` is strictly positive if and only if `h * A` is dense in `A`. -/
theorem isStrictlyPositive_iff_dense_range_mul_left {h : A} (hh : 0 ≤ h) :
    CStarAlgebra.IsStrictlyPositive h ↔ Dense (Set.range fun a : A => h * a) :=
  (isStrictlyPositive_tfae hh).out 1 2

/-- A nonnegative element `h` is strictly positive if and only if `A * h` is dense in `A`. -/
theorem isStrictlyPositive_iff_dense_range_mul_right {h : A} (hh : 0 ≤ h) :
    CStarAlgebra.IsStrictlyPositive h ↔ Dense (Set.range fun a : A => a * h) :=
  (isStrictlyPositive_tfae hh).out 1 3

/-- A nonnegative element `h` is strictly positive if and only if every nonzero positive continuous
linear functional takes a strictly positive real value on `h`. -/
theorem isStrictlyPositive_iff_forall_positiveContinuousLinearMap_pos {h : A} (hh : 0 ≤ h) :
    CStarAlgebra.IsStrictlyPositive h ↔ ∀ φ : A →P[ℂ] ℂ, φ ≠ 0 → 0 < (φ h).re :=
  (isStrictlyPositive_tfae hh).out 1 4

/-- An element `h` is strictly positive if and only if `strictlyPositiveApproximateUnit h`
forms an increasing approximate unit of `A`. -/
theorem isStrictlyPositive_iff_isIncreasingApproximateUnit {h : A} :
    CStarAlgebra.IsStrictlyPositive h ↔
      (atTop.map (strictlyPositiveApproximateUnit h)).IsIncreasingApproximateUnit := by
  by_cases hh : 0 ≤ h
  · exact (isStrictlyPositive_tfae hh).out 1 5
  · constructor
    · intro hsp
      exact (hh hsp.nonneg).elim
    · intro hl
      have hlim := tendsto_map'_iff.mp (hl.tendsto_mul_right h)
      have hh0 : (0 : A) = h := by
        simpa [Function.comp_def, strictlyPositiveApproximateUnit_of_not_nonneg hh] using hlim
      exact (hh (hh0 ▸ le_rfl)).elim

/-- Every nonzero positive continuous linear functional takes a strictly positive real value on a
strictly positive element. -/
theorem IsStrictlyPositive.re_apply_pos_of_ne_zero {h : A}
    (hh : CStarAlgebra.IsStrictlyPositive h) {φ : A →P[ℂ] ℂ} (hφ : φ ≠ 0) : 0 < (φ h).re :=
  ((isStrictlyPositive_iff_forall_positiveContinuousLinearMap_pos hh.nonneg).mp hh) φ hφ

/-- A positive continuous linear functional vanishing on a strictly positive element is zero. -/
theorem IsStrictlyPositive.eq_zero_of_apply_eq_zero {h : A}
    (hh : CStarAlgebra.IsStrictlyPositive h) {φ : A →P[ℂ] ℂ} (hφh : φ h = 0) : φ = 0 :=
  eq_zero_of_forall_re_apply_pos (fun _ hne => hh.re_apply_pos_of_ne_zero hne) hφh

/-- If `h` is strictly positive, then `strictlyPositiveApproximateUnit h` is an increasing
approximate unit of `A`. -/
theorem IsStrictlyPositive.isIncreasingApproximateUnit {h : A}
    (hh : CStarAlgebra.IsStrictlyPositive h) :
    (atTop.map (strictlyPositiveApproximateUnit h)).IsIncreasingApproximateUnit :=
  isStrictlyPositive_iff_isIncreasingApproximateUnit.mp hh

/-- If `h` is strictly positive, then `π h` has dense range in any nondegenerate Hilbert-space
representation `π` of `A`. -/
theorem IsStrictlyPositive.dense_range_of_isNondegenerate {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {h : A} (hh : CStarAlgebra.IsStrictlyPositive h)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : π.IsNondegenerate) :
    Dense (Set.range (π h)) :=
  dense_range_of_forall_re_apply_pos π hπ hh.nonneg fun _ hφ => hh.re_apply_pos_of_ne_zero hφ

/-- If `h` is strictly positive, then in any nondegenerate Hilbert-space representation `π` of `A`,
`π (strictlyPositiveApproximateUnit h n)` converges strongly to the identity. -/
theorem IsStrictlyPositive.tendsto_apply_strictlyPositiveApproximateUnit_of_isNondegenerate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {h : A} (hh : CStarAlgebra.IsStrictlyPositive h)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : π.IsNondegenerate) (η : H) :
    Tendsto (fun n => π (strictlyPositiveApproximateUnit h n) η) atTop (𝓝 η) :=
  tendsto_apply_strictlyPositiveApproximateUnit_of_forall_re_apply_pos π hπ hh.nonneg
    (fun _ hφ => hh.re_apply_pos_of_ne_zero hφ) η

/-- Any element dominating a strictly positive element is strictly positive. -/
theorem IsStrictlyPositive.of_le {h₁ h₂ : A} (hh₁ : CStarAlgebra.IsStrictlyPositive h₁)
    (hle : h₁ ≤ h₂) : CStarAlgebra.IsStrictlyPositive h₂ := by
  refine (isStrictlyPositive_iff_forall_positiveContinuousLinearMap_pos
    (hh₁.nonneg.trans hle)).mpr fun φ hφ => ?_
  exact (hh₁.re_apply_pos_of_ne_zero hφ).trans_le (Complex.le_def.mp (φ.monotone hle)).1

/-- Adding a nonnegative element on the right preserves strict positivity. -/
theorem IsStrictlyPositive.add_nonneg {h a : A} (hh : CStarAlgebra.IsStrictlyPositive h)
    (ha : 0 ≤ a) : CStarAlgebra.IsStrictlyPositive (h + a) :=
  hh.of_le (le_add_of_nonneg_right ha)

/-- Adding a nonnegative element on the left preserves strict positivity. -/
theorem IsStrictlyPositive.nonneg_add {a h : A} (ha : 0 ≤ a)
    (hh : CStarAlgebra.IsStrictlyPositive h) : CStarAlgebra.IsStrictlyPositive (a + h) :=
  hh.of_le (le_add_of_nonneg_left ha)

/-- Scaling a strictly positive element by a strictly positive real scalar preserves strict
positivity. -/
theorem IsStrictlyPositive.smul {h : A} (hh : CStarAlgebra.IsStrictlyPositive h) {c : ℝ}
    (hc : 0 < c) : CStarAlgebra.IsStrictlyPositive (c • h) := by
  refine isStrictlyPositive_def.mpr ⟨smul_nonneg hc.le hh.nonneg,
    (hh.dense_range_mul_mul.mono ?_).closure_eq⟩
  rintro _ ⟨a, rfl⟩
  refine ⟨(c⁻¹ * c⁻¹) • a, ?_⟩
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_assoc c⁻¹, inv_mul_cancel₀ hc.ne', mul_one, mul_inv_cancel₀ hc.ne', one_smul]

/-- A nonunital *-algebra homomorphism with dense range sends strictly positive elements to
strictly positive elements. -/
theorem IsStrictlyPositive.map {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (f : F) (hf : DenseRange f) {h : A} (hh : CStarAlgebra.IsStrictlyPositive h) :
    CStarAlgebra.IsStrictlyPositive (f h) := by
  refine isStrictlyPositive_def.mpr ⟨map_nonneg f hh.nonneg,
    ((hf.dense_image (map_continuous f) hh.dense_range_mul_mul).mono ?_).closure_eq⟩
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact ⟨f a, by simp [map_mul]⟩

/-- If `b : ι → A` is a summable family of nonnegative elements such that no nonzero positive
continuous linear functional vanishes on every `b i`, then `∑' i, b i` is strictly positive. -/
theorem isStrictlyPositive_tsum_of_forall_apply_eq_zero_imp_eq_zero {ι : Type*} {b : ι → A}
    (hb : ∀ i, 0 ≤ b i) (hsum : Summable b)
    (hsep : ∀ φ : A →P[ℂ] ℂ, (∀ i, φ (b i) = 0) → φ = 0) :
    CStarAlgebra.IsStrictlyPositive (∑' i, b i) := by
  have hh_nonneg : 0 ≤ ∑' i, b i := tsum_nonneg hb
  refine (isStrictlyPositive_iff_forall_positiveContinuousLinearMap_pos hh_nonneg).mpr ?_
  intro φ hφ
  have hφh : 0 ≤ φ (∑' i, b i) := φ.map_nonneg hh_nonneg
  have hre : 0 ≤ (φ (∑' i, b i)).re := (Complex.nonneg_iff.mp hφh).1
  refine lt_of_le_of_ne hre ?_
  intro hzero
  have hhas : HasSum (fun i => (φ (b i)).re) (φ (∑' i, b i)).re :=
    Complex.reCLM.hasSum (φ.toContinuousLinearMap.hasSum hsum.hasSum)
  have hsum_re : Summable (fun i => (φ (b i)).re) := hhas.summable
  have hterm_nonneg : ∀ i, 0 ≤ (φ (b i)).re := fun i =>
    (Complex.nonneg_iff.mp (φ.map_nonneg (hb i))).1
  have hterm0 : ∀ i, φ (b i) = 0 := fun i => by
    have hle : (φ (b i)).re ≤ 0 := by
      have := hsum_re.le_tsum i (fun k _ => hterm_nonneg k)
      rwa [hhas.tsum_eq, ← hzero] at this
    have hre0 : (φ (b i)).re = 0 := le_antisymm hle (hterm_nonneg i)
    exact PositiveLinearMap.map_eq_zero_of_re_eq_zero φ (hb i) hre0
  exact hφ (hsep φ hterm0)

/-- If `b : ι → A` is a countable family of nonnegative elements such that no nonzero positive
continuous linear functional vanishes on every `b i`, then `A` admits a strictly positive element;
see `isStrictlyPositive_tsum_of_forall_apply_eq_zero_imp_eq_zero` for an explicit `tsum`
construction. -/
theorem exists_isStrictlyPositive_of_forall_apply_eq_zero_imp_eq_zero {ι : Type*} [Countable ι]
    {b : ι → A} (hb : ∀ i, 0 ≤ b i) (hsep : ∀ φ : A →P[ℂ] ℂ, (∀ i, φ (b i) = 0) → φ = 0) :
    ∃ h : A, CStarAlgebra.IsStrictlyPositive h := by
  let _ : Encodable ι := Encodable.ofCountable ι
  let w : ι → ℝ := fun i => (2 : ℝ)⁻¹ ^ (Encodable.encode i + 1) * (1 + ‖b i‖)⁻¹
  let f : ι → A := fun i => w i • b i
  have hw_pos : ∀ i, 0 < w i := fun i => by
    have := norm_nonneg (b i)
    positivity
  have hf_nonneg : ∀ i, 0 ≤ f i := fun i => smul_nonneg (hw_pos i).le (hb i)
  have hf_norm : ∀ i, ‖f i‖ ≤ (2 : ℝ)⁻¹ ^ (Encodable.encode i + 1) := fun i => by
    rw [norm_smul, Real.norm_of_nonneg (hw_pos i).le]
    dsimp [w]
    rw [mul_assoc]
    refine mul_le_of_le_one_right (by positivity) ?_
    have := norm_nonneg (b i)
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    linarith
  have hgeom : Summable (fun i : ι => (2 : ℝ)⁻¹ ^ (Encodable.encode i + 1)) := by
    have hnat : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1)) := by
      simpa [pow_succ'] using summable_geometric_two.mul_left (2 : ℝ)⁻¹
    exact hnat.comp_injective Encodable.encode_injective
  refine ⟨∑' i, f i, isStrictlyPositive_tsum_of_forall_apply_eq_zero_imp_eq_zero hf_nonneg
    (Summable.of_norm_bounded hgeom hf_norm) fun φ hterm0 => hsep φ fun i => ?_⟩
  have hsmul : ((w i : ℝ) : ℂ) * φ (b i) = 0 := by
    simpa [f, ← Complex.coe_smul, map_smul, smul_eq_mul] using hterm0 i
  exact (mul_eq_zero.mp hsmul).resolve_left (Complex.ofReal_ne_zero.mpr (hw_pos i).ne')

/-- A C⋆-algebra has a strictly positive element if and only if it admits a countable left
approximate unit. -/
theorem exists_isStrictlyPositive_iff_exists_seq_tendsto_mul_right :
    (∃ h : A, CStarAlgebra.IsStrictlyPositive h) ↔
      ∃ u : ℕ → A, ∀ a : A, Tendsto (fun n => u n * a) atTop (𝓝 a) := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨strictlyPositiveApproximateUnit h,
      fun a => tendsto_map'_iff.mp (hh.isIncreasingApproximateUnit.tendsto_mul_right a)⟩
  · rintro ⟨u, hu⟩
    refine exists_isStrictlyPositive_of_forall_apply_eq_zero_imp_eq_zero
      (fun n => mul_star_self_nonneg (u n)) fun φ hu0 => ?_
    ext a
    have hvanish : ∀ n, φ (u n * a) = 0 := fun n =>
      PositiveLinearMap.map_mul_eq_zero_of_map_mul_star_eq_zero φ (hu0 n) a
    exact tendsto_nhds_unique (((map_continuous φ).tendsto a).comp (hu a))
      (by simp [Function.comp_def, hvanish])

/-- A C⋆-algebra has a strictly positive element if and only if it admits a countable right
approximate unit. -/
theorem exists_isStrictlyPositive_iff_exists_seq_tendsto_mul_left :
    (∃ h : A, CStarAlgebra.IsStrictlyPositive h) ↔
      ∃ u : ℕ → A, ∀ a : A, Tendsto (fun n => a * u n) atTop (𝓝 a) := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨strictlyPositiveApproximateUnit h,
      fun a => tendsto_map'_iff.mp (hh.isIncreasingApproximateUnit.tendsto_mul_left a)⟩
  · rintro ⟨u, hu⟩
    refine exists_isStrictlyPositive_iff_exists_seq_tendsto_mul_right.mpr
      ⟨fun n => star (u n), fun a => ?_⟩
    have hlim := (continuous_star.tendsto (star a)).comp (hu (star a))
    rw [star_star] at hlim
    exact hlim.congr fun n => by simp [Function.comp_apply, star_mul]

/-- A C⋆-algebra has a strictly positive element (i.e., is σ-unital) if and only if it admits a
sequential increasing approximate unit (Blackadar II.4.2.4). -/
theorem exists_isStrictlyPositive_iff_exists_seq_isIncreasingApproximateUnit :
    (∃ h : A, CStarAlgebra.IsStrictlyPositive h) ↔
      ∃ u : ℕ → A, (atTop.map u).IsIncreasingApproximateUnit := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨strictlyPositiveApproximateUnit h, hh.isIncreasingApproximateUnit⟩
  · rintro ⟨u, hu⟩
    exact exists_isStrictlyPositive_iff_exists_seq_tendsto_mul_right.mpr
      ⟨u, fun a => tendsto_map'_iff.mp (hu.tendsto_mul_right a)⟩

/-- A C⋆-algebra has a strictly positive element if and only if it admits a monotone increasing
sequence of positive strict contractions forming an increasing approximate unit. -/
theorem exists_isStrictlyPositive_iff_exists_seq_monotone_isIncreasingApproximateUnit :
    (∃ h : A, CStarAlgebra.IsStrictlyPositive h) ↔
      ∃ u : ℕ → A, Monotone u ∧ (∀ n, 0 ≤ u n ∧ ‖u n‖ < 1) ∧
        (atTop.map u).IsIncreasingApproximateUnit := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨strictlyPositiveApproximateUnit h, strictlyPositiveApproximateUnit_monotone h,
      fun n => ⟨strictlyPositiveApproximateUnit_nonneg h n,
        norm_strictlyPositiveApproximateUnit_lt_one h n⟩,
      hh.isIncreasingApproximateUnit⟩
  · rintro ⟨u, -, -, hu⟩
    exact exists_isStrictlyPositive_iff_exists_seq_isIncreasingApproximateUnit.mpr ⟨u, hu⟩

/-- Every separable C⋆-algebra admits a strictly positive element (hence is σ-unital). -/
theorem exists_isStrictlyPositive_of_separableSpace [TopologicalSpace.SeparableSpace A] :
    ∃ h : A, CStarAlgebra.IsStrictlyPositive h := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq A
  refine exists_isStrictlyPositive_of_forall_apply_eq_zero_imp_eq_zero
    (fun n => star_mul_self_nonneg (d n)) fun φ hd0 => ?_
  have hvanish : Set.EqOn (φ : A → ℂ) (fun _ => 0) (Set.range d) := by
    rintro _ ⟨n, rfl⟩
    exact PositiveLinearMap.map_eq_zero_of_map_star_mul_self_eq_zero φ (hd0 n)
  have hzero_fn := Continuous.ext_on hd (map_continuous φ) continuous_const hvanish
  exact DFunLike.ext _ _ fun a => congrFun hzero_fn a

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

variable {D : Type*} [CStarAlgebra D] [PartialOrder D]

/-- In a unital C⋆-algebra, `TauCeti.CStarAlgebra.IsStrictlyPositive h` coincides with
`0 ≤ h ∧ IsUnit h` (i.e. Mathlib's `_root_.IsStrictlyPositive h`). -/
theorem IsStrictlyPositive.iff_of_unital {h : D} :
    CStarAlgebra.IsStrictlyPositive h ↔ 0 ≤ h ∧ IsUnit h :=
  isStrictlyPositive_iff_of_unital.trans _root_.IsStrictlyPositive.iff_of_unital

end Unital

end TauCeti.CStarAlgebra

end
