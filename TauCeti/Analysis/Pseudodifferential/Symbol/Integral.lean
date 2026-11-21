/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import TauCeti.Analysis.Calculus.IteratedFDeriv.SpatialJets

/-!
# Integrals of compact parameter families of symbols

For a finite measure `μ` on a compact parameter space `Y`, `TauCeti.Symbol.integral` integrates
the coefficients of a family of symbols of the same real order `m`. Every spatial jet must be
jointly continuous in the parameter and the position-frequency variables. The symbol estimates
on each compact set of positions must have constants independent of the parameter.

Mixed coordinate derivatives commute with this coefficient integral
(`TauCeti.Symbol.mixedDeriv_integral_of_continuous_jets`), so a pointwise estimate with a
constant `C` for every member gives the estimate with constant `μ.real Set.univ * C` for the
integral (`TauCeti.Symbol.norm_mixedDeriv_integral_le`). If the seminorm `p_{K,α,β}` of every
member of the family is at most `C ≥ 0`, the integral has that seminorm at most
`μ.real Set.univ * C` (`TauCeti.Symbol.seminorm_integral_le`), as does any symbol whose
coefficient is that pointwise integral (`TauCeti.Symbol.seminorm_le_of_coefficient_eq_integral`).
For a probability measure, this is an average with seminorm at most `C`
(`TauCeti.Symbol.seminorm_integral_le_of_probability`).

Integration takes place in the coefficient operator space `V →L[ℂ] W`, with no
finite-dimensionality assumption on `V` or `W`. The parameter space needs only a topology.
The position estimates remain local on compact sets, with the native weight
`⟨ξ⟩^(m - |β|) = (1 + ‖ξ‖²)^((m - |β|)/2)`.

The integral commutes with addition and complex scalar multiplication and sends a zero
family or a zero measure to the zero symbol. If `V →L[ℂ] W` is complete, a constant
parameter family integrates to the total mass times its symbol, a probability average
fixes that family, and a Dirac measure selects its symbol at the specified parameter.
These normalization identities use completeness because Mathlib's Bochner integral in
an incomplete target is defined to be zero. The algebra identities need no completeness.

Averaging over a compact group must also preserve the classical class, which an estimate in the
symbol seminorms of `S^m_{1,0}` alone does not give. `TauCeti.HomogeneousSymbol.integral`
integrates a compact family of homogeneous symbols of degree `m` whose jets are jointly continuous
away from the zero frequency; the result is homogeneous of degree `m`.
`TauCeti.ClassicalSymbol.integral` integrates a compact family of classical symbols of order `m`
whose full symbols have jointly continuous jets, whose homogeneous terms have jointly continuous
jets away from the zero frequency, and whose remainders `a - ∑_{j<N} χ(ξ) a_{m-j}` after `N`
terms have, for one frequency cutoff `χ`, seminorms bounded independently of the parameter for
every `N`. The integral is classical of order `m`, its homogeneous terms are the integrals of the
homogeneous terms (`TauCeti.ClassicalSymbol.term_integral`), so its principal symbol is the
integral of the principal symbols (`TauCeti.ClassicalSymbol.principal_integral`), and a
probability average keeps a principal symbol shared by the whole family
(`TauCeti.ClassicalSymbol.principal_integral_of_forall_principal_eq`). For every cutoff its
remainders are the integrals of the remainders
(`TauCeti.ClassicalSymbol.coefficient_remainder_integral`), and a parameter-uniform bound `C` on
a remainder seminorm becomes `μ.real univ * C`
(`TauCeti.ClassicalSymbol.seminorm_remainder_integral_le`), as it does for the full symbol
(`TauCeti.ClassicalSymbol.seminorm_toSymbol_integral_le`). Seminorms bounded independently of the
parameter give the estimates required by `TauCeti.Symbol.integral`
(`TauCeti.Symbol.exists_bound_of_bddAbove_seminorm`). The jets of the remainders are
jointly continuous because those of the cut-off terms `χ(ξ) a_{m-j}(x, ξ)` are, by the Leibniz
rule (`TauCeti.continuousOn_spatial_jets_smul`).

## References

* Mathlib, `MeasureTheory/Integral/Bochner/Basic.lean`: the algebra and normalization
  identities of the coefficient integral.
  <https://github.com/leanprover-community/mathlib4>.
* Lean-Atiyah-Singer, `AtiyahSinger/Analysis/CompactSymbolIntegral.lean`:
  the source formalization of compact-parameter symbol integration.
  <https://github.com/alpha-squared-labs/Lean-Atiyah-Singer>.
* H. B. Lawson, Jr. and M.-L. Michelsohn, *Spin Geometry*, Chapter III,
  proof of Theorem 9.7, p. 214: compact-group averaging of operator homotopies.
  The coefficient differentiation and seminorm estimates are supplementary
  analytic inputs in the source formalization.
  <https://doi.org/10.1515/9781400883912>.
* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  484–530, (5.5)–(5.6), pp. 516–517: averaging pseudodifferential operators over a compact group.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace TauCeti.Symbol

/-- Seminorms of a family of symbols bounded independently of the parameter give the
parameter-uniform estimates of `TauCeti.Symbol.integral`. -/
theorem exists_bound_of_bddAbove_seminorm {Y : Type*} {n : ℕ} {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}
    (a : Y → Symbol n V W m)
    (ha : ∀ (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)),
      BddAbove (range fun y ↦ Symbol.seminorm K α β (a y)))
    (K : Set (CoordinateSpace n)) (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (a y).coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨C, hC⟩ := ha ⟨K, hK⟩ α β
  refine ⟨max C 0, le_max_right _ _, fun y x hx ξ ↦ ?_⟩
  exact (le_seminorm ⟨K, hK⟩ α β (a y) hx ξ).trans
    (mul_le_mul_of_nonneg_right ((hC ⟨y, rfl⟩).trans (le_max_left _ _))
      (rpow_weight_pos ξ _).le)

section ContinuousJets

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (μ : Measure Y) [IsFiniteMeasure μ]
  {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}
  (a : Y → Symbol n V W m)
  (hjets : ∀ k : ℕ, Continuous
    (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k (a p.1).coefficient p.2))

include hjets

private theorem contDiff_coefficient_integral :
    ContDiff ℝ ∞ (fun p ↦ ∫ y, (a y).coefficient p ∂μ) := by
  exact contDiffOn_univ.1 <|
    contDiffOn_integral_of_continuous_jets (μ := μ) isOpen_univ
      (fun y ↦ (a y).contDiff_coefficient.contDiffOn) (fun k ↦ (hjets k).continuousOn)

/-- Mixed coordinate derivatives commute with the coefficient integral of a compact family
whose spatial jets are jointly continuous. -/
theorem mixedDeriv_integral_of_continuous_jets (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (fun p ↦ ∫ y, (a y).coefficient p ∂μ) x ξ =
      ∫ y, mixedDeriv α β (a y).coefficient x ξ ∂μ := by
  rw [mixedDeriv_eq_iteratedFDeriv α β
    ((contDiff_coefficient_integral μ a hjets).of_le (by simp)),
    iteratedFDeriv_integral_of_continuous_jets (μ := μ) isOpen_univ
      (fun y ↦ (a y).contDiff_coefficient.contDiffOn) (fun k ↦ (hjets k).continuousOn)
      _ (mem_univ (x, ξ))]
  have hi : Integrable
      (fun y ↦ iteratedFDeriv ℝ (mixedDirections α β).length (a y).coefficient (x, ξ)) μ :=
    ((hjets (mixedDirections α β).length).comp
      (continuous_id.prodMk (continuous_const (y := (x, ξ))))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [ContinuousMultilinearMap.integral_apply hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦
    (mixedDeriv_eq_iteratedFDeriv α β ((a y).contDiff_coefficient.of_le (by simp)) x ξ).symm

/-- A symbol estimate at `(x, ξ)` with constant `C` for every member of a compact family with
jointly continuous spatial jets gives the estimate with constant `μ.real univ * C` for the
coefficient integral. -/
theorem norm_mixedDeriv_integral_le (α β : List (Fin n)) (x ξ : CoordinateSpace n)
    {C : ℝ} (hC : ∀ y, ‖mixedDeriv α β (a y).coefficient x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) :
    ‖mixedDeriv α β (fun p ↦ ∫ y, (a y).coefficient p ∂μ) x ξ‖ ≤
      (μ.real univ * C) * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  rw [mixedDeriv_integral_of_continuous_jets μ a hjets]
  exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hC)).trans_eq (by ring)

/-- A symbol whose coefficient is the pointwise integral of the coefficients of a compact family
with jointly continuous spatial jets has seminorm at most `μ.real univ * C` whenever every member
of the family has seminorm at most `C ≥ 0`. -/
theorem seminorm_le_of_coefficient_eq_integral (b : Symbol n V W m)
    (hb : b.coefficient = fun p ↦ ∫ y, (a y).coefficient p ∂μ)
    (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ y, Symbol.seminorm K α β (a y) ≤ C) :
    Symbol.seminorm K α β b ≤ μ.real univ * C := by
  refine seminorm_le_bound K α β _ (mul_nonneg measureReal_nonneg hC) fun x hx ξ ↦ ?_
  rw [hb]
  exact norm_mixedDeriv_integral_le μ a hjets α β x ξ fun y ↦
    (le_seminorm K α β (a y) hx ξ).trans
      (mul_le_mul_of_nonneg_right (h y) (rpow_weight_pos ξ _).le)

variable (hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
  ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
    ‖mixedDeriv α β (a y).coefficient x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))

/-- The coefficient integral of a compact family with jointly continuous spatial jets and
parameter-uniform symbol estimates is a symbol of the same order. -/
def integral : Symbol n V W m where
  coefficient p := ∫ y, (a y).coefficient p ∂μ
  contDiff_coefficient := contDiff_coefficient_integral μ a hjets
  exists_bound K hK α β := by
    obtain ⟨C, hC, h⟩ := hbound K hK α β
    exact ⟨μ.real univ * C, mul_nonneg measureReal_nonneg hC,
      fun x hx ξ ↦ norm_mixedDeriv_integral_le μ a hjets α β x ξ (fun y ↦ h y x hx ξ)⟩

/-- The coefficient of the symbol integral is the pointwise integral of the coefficients. -/
@[simp]
theorem coefficient_integral (p : CoordinateSpace n × CoordinateSpace n) :
    (integral μ a hjets hbound).coefficient p = ∫ y, (a y).coefficient p ∂μ :=
  (rfl)

/-- A parameter-uniform seminorm bound `C ≥ 0` becomes `μ.real univ * C` after integration. -/
theorem seminorm_integral_le (K : TopologicalSpace.Compacts (CoordinateSpace n))
    (α β : List (Fin n)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ y, Symbol.seminorm K α β (a y) ≤ C) :
    Symbol.seminorm K α β (integral μ a hjets hbound) ≤ μ.real univ * C :=
  seminorm_le_of_coefficient_eq_integral μ a hjets _
    (funext (coefficient_integral μ a hjets hbound)) K α β hC h

/-- Averaging with a probability measure preserves every parameter-uniform seminorm bound. -/
theorem seminorm_integral_le_of_probability [IsProbabilityMeasure μ]
    (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n))
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ y, Symbol.seminorm K α β (a y) ≤ C) :
    Symbol.seminorm K α β (integral μ a hjets hbound) ≤ C := by
  simpa using seminorm_integral_le μ a hjets hbound K α β hC h

end ContinuousJets

section IntegralAlgebra

variable {Y : Type*} [TopologicalSpace Y]
  {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

private theorem continuous_coefficient_family (a : Y → Symbol n V W m)
    (hjets : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (a p.1).coefficient p.2))
    (p : CoordinateSpace n × CoordinateSpace n) :
    Continuous (fun y ↦ (a y).coefficient p) := by
  have hc := (hjets 0).comp (continuous_id.prodMk (continuous_const (y := p)))
  -- Evaluating a degree-zero jet recovers the coefficient itself.
  have he : Continuous (fun y ↦ (iteratedFDeriv ℝ 0 (a y).coefficient p)
      (0 : Fin 0 → CoordinateSpace n × CoordinateSpace n)) :=
    hc.eval continuous_const
  simpa only [iteratedFDeriv_zero_apply] using he

variable [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

private theorem integrable_coefficient_family (μ : Measure Y) [IsFiniteMeasure μ]
    (a : Y → Symbol n V W m)
    (hjets : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (a p.1).coefficient p.2))
    (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable (fun y ↦ (a y).coefficient p) μ :=
  (continuous_coefficient_family a hjets p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

variable (μ : Measure Y)

section FiniteMeasure

variable [IsFiniteMeasure μ]

/-- The integral of a zero parameter family is the zero symbol. -/
@[simp]
theorem integral_zero
    {hjets : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (0 : Symbol n V W m).coefficient p.2)}
    {hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ _ : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β (0 : Symbol n V W m).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)} :
    integral μ (fun _ : Y ↦ (0 : Symbol n V W m)) hjets hbound = 0 := by
  apply Symbol.ext
  funext p
  simp only [coefficient_integral, coefficient_zero, Pi.zero_apply,
    MeasureTheory.integral_zero]

/-- Integrating against zero measure gives the zero symbol. -/
@[simp]
theorem integral_zero_measure (a : Y → Symbol n V W m)
    (hjets : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (a p.1).coefficient p.2))
    {hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β (a y).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)} :
    integral (0 : Measure Y) a hjets hbound = 0 := by
  apply Symbol.ext
  funext p
  simp only [coefficient_integral, coefficient_zero, Pi.zero_apply,
    MeasureTheory.integral_zero_measure]

/-- Integration preserves addition of compact continuous-jet symbol families. -/
theorem integral_add (a b : Y → Symbol n V W m)
    (ha : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (a p.1).coefficient p.2))
    (hb : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (b p.1).coefficient p.2))
    {hba : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β (a y).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)}
    {hbb : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β (b y).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)}
    {hab : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (a p.1 + b p.1).coefficient p.2)}
    {hbab : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β (a y + b y).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)} :
    integral μ (fun y ↦ a y + b y) hab hbab =
      integral μ a ha hba + integral μ b hb hbb := by
  apply Symbol.ext
  funext p
  simp only [coefficient_integral, coefficient_add, Pi.add_apply]
  exact MeasureTheory.integral_add (integrable_coefficient_family μ a ha p)
    (integrable_coefficient_family μ b hb p)

/-- Integration commutes with multiplication by a fixed complex scalar. -/
theorem integral_smul (c : ℂ) (a : Y → Symbol n V W m)
    (hjets : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (a p.1).coefficient p.2))
    {hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β (a y).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)}
    {hcs : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (c • a p.1).coefficient p.2)}
    {hbcs : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β (c • a y).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)} :
    integral μ (fun y ↦ c • a y) hcs hbcs = c • integral μ a hjets hbound := by
  apply Symbol.ext
  funext p
  simp only [coefficient_integral, coefficient_smul, Pi.smul_apply,
    MeasureTheory.integral_smul]

section CompleteCoefficients

variable [CompleteSpace (V →L[ℂ] W)]

/-- A constant parameter family integrates to the total mass times its symbol. -/
@[simp]
theorem integral_const (b : Symbol n V W m)
    {hjets : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k b.coefficient p.2)}
    {hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ _ : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β b.coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)} :
    integral μ (fun _ : Y ↦ b) hjets hbound = (μ.real univ : ℂ) • b := by
  apply Symbol.ext
  funext p
  simp only [coefficient_integral, MeasureTheory.integral_const, coefficient_smul,
    Pi.smul_apply]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) (μ.real univ) (b.coefficient p)

end CompleteCoefficients

end FiniteMeasure

section CompleteCoefficients

variable [CompleteSpace (V →L[ℂ] W)]

/-- A probability average fixes a constant parameter family of symbols. -/
@[simp high]
theorem integral_const_of_probability [IsProbabilityMeasure μ] (b : Symbol n V W m)
    {hjets : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k b.coefficient p.2)}
    {hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ _ : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β b.coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)} :
    integral μ (fun _ : Y ↦ b) hjets hbound = b := by
  simpa only [probReal_univ, Complex.ofReal_one, one_smul] using
    integral_const μ b (hjets := hjets) (hbound := hbound)

/-- Integrating a compact continuous-jet symbol family against a Dirac measure selects its
symbol at that parameter. -/
@[simp]
theorem integral_dirac (y₀ : Y) (a : Y → Symbol n V W m)
    (hjets : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (a p.1).coefficient p.2))
    {hbound : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β (a y).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)} :
    integral (Measure.dirac y₀) a hjets hbound = a y₀ := by
  apply Symbol.ext
  funext p
  rw [coefficient_integral]
  -- Compact-range strong measurability avoids any measurable-singleton assumption on Y.
  exact MeasureTheory.integral_dirac' _ _
    ((continuous_coefficient_family a hjets p).stronglyMeasurable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

end CompleteCoefficients

end IntegralAlgebra

end TauCeti.Symbol

/-! ### Integrals of homogeneous symbols -/

namespace TauCeti.HomogeneousSymbol

open scoped Topology

variable {Y : Type*} [TopologicalSpace Y]
  {X E V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

section Cutoff

variable (a : Y → HomogeneousSymbol X E V W m)
  (hjets : ∀ k : ℕ, ContinuousOn
    (fun p : Y × (X × E) ↦ iteratedFDeriv ℝ k (a p.1).coefficient p.2)
    (univ ×ˢ {p | p.2 ≠ 0}))

include hjets in
/-- A frequency cutoff `χ` times the members of the family gives a family whose jets are jointly
continuous everywhere: away from the zero frequency by the Leibniz rule, and near it because `χ`
vanishes there. -/
private theorem continuous_iteratedFDeriv_smul_coefficient (χ : FrequencyCutoff E) (k : ℕ) :
    Continuous (fun p : Y × (X × E) ↦
      iteratedFDeriv ℝ k (fun q : X × E ↦ χ q.2 • (a p.1).coefficient q) p.2) := by
  have hopen : IsOpen {p : X × E | p.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  have hon := continuousOn_spatial_jets_smul (𝕜 := ℝ) hopen
    ((χ.contDiff.comp contDiff_snd).contDiffOn) (fun y ↦ (a y).contDiffOn_coefficient) hjets k
  refine continuous_iff_continuousAt.2 fun ⟨y, p⟩ ↦ ?_
  rcases eq_or_ne p.2 0 with hp | hp
  · -- Near the zero frequency the cut-off family vanishes identically.
    have hnhds : {q : Y × (X × E) | ‖q.2.2‖ < 1} ∈ 𝓝 (y, p) :=
      (isOpen_lt (continuous_norm.comp (continuous_snd.comp continuous_snd))
        continuous_const).mem_nhds (by simp [hp])
    refine (continuousAt_const (y := (0 : X × E [×k]→L[ℝ] V →L[ℂ] W))).congr
      (Filter.mem_of_superset hnhds fun q hq ↦ ?_)
    have hzero := χ.comp_snd_smul_eventuallyEq_zero (a q.1).coefficient hq
    exact (by rw [(hzero.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply] :
      iteratedFDeriv ℝ k (fun r ↦ χ r.2 • (a q.1).coefficient r) q.2 = 0).symm
  · exact hon.continuousAt ((isOpen_univ.prod hopen).mem_nhds ⟨mem_univ _, hp⟩)

end Cutoff

variable [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (μ : Measure Y) [IsFiniteMeasure μ]
  (a : Y → HomogeneousSymbol X E V W m)
  (hjets : ∀ k : ℕ, ContinuousOn
    (fun p : Y × (X × E) ↦ iteratedFDeriv ℝ k (a p.1).coefficient p.2)
    (univ ×ˢ {p | p.2 ≠ 0}))

include hjets in
private theorem integrable_coefficient_family (p : X × E) :
    Integrable (fun y ↦ (a y).coefficient p) μ := by
  rcases eq_or_ne p.2 0 with hp | hp
  · obtain ⟨x, ξ⟩ := p
    simp only at hp
    subst hp
    simp
  -- Off the zero frequency the degree-zero jet is continuous in the parameter.
  have hc : Continuous (fun y ↦ iteratedFDeriv ℝ 0 (a y).coefficient p) :=
    (hjets 0).comp_continuous (continuous_id.prodMk continuous_const) fun _ ↦ ⟨mem_univ _, hp⟩
  have he : Continuous (fun y ↦ (iteratedFDeriv ℝ 0 (a y).coefficient p)
      (0 : Fin 0 → X × E)) :=
    hc.eval continuous_const
  simp only [iteratedFDeriv_zero_apply] at he
  exact he.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The integral `(x, ξ) ↦ ∫ a_y(x, ξ) dμ(y)` of a compact family of homogeneous symbols of degree
`m` whose jets are jointly continuous in the parameter and in `(x, ξ)` away from the zero
frequency. It is again homogeneous of degree `m`. -/
def integral : HomogeneousSymbol X E V W m where
  coefficient p := ∫ y, (a y).coefficient p ∂μ
  zero_covector x := by simp
  contDiffOn_coefficient := contDiffOn_integral_of_continuous_jets (μ := μ)
    (isOpen_ne_fun continuous_snd continuous_const) (fun y ↦ (a y).contDiffOn_coefficient) hjets
  homogeneous x ξ t ht := by
    simp only [(a _).homogeneous x ξ t ht]
    exact integral_smul _ _

/-- The coefficient of the integral of homogeneous symbols is the integral of the coefficients. -/
@[simp]
theorem coefficient_integral (p : X × E) :
    (integral μ a hjets).coefficient p = ∫ y, (a y).coefficient p ∂μ :=
  (rfl)

/-- A probability average fixes a constant family of homogeneous symbols. -/
@[simp]
theorem integral_const_of_probability [IsProbabilityMeasure μ] [CompleteSpace (V →L[ℂ] W)]
    (b : HomogeneousSymbol X E V W m)
    {hjets : ∀ k : ℕ, ContinuousOn
      (fun p : Y × (X × E) ↦ iteratedFDeriv ℝ k b.coefficient p.2) (univ ×ˢ {p | p.2 ≠ 0})} :
    integral μ (fun _ : Y ↦ b) hjets = b := by
  ext p
  simp

end TauCeti.HomogeneousSymbol

/-! ### Integrals of classical symbols -/

namespace TauCeti.ClassicalSymbol

open TopologicalSpace (Compacts)

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
  {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

variable (a : Y → ClassicalSymbol n V W m)
  (hjets : ∀ k : ℕ, Continuous
    (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k (a p.1).toSymbol.coefficient p.2))
  (htjets : ∀ j k : ℕ, ContinuousOn
    (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k ((a p.1).term j).coefficient p.2)
    (univ ×ˢ {p | p.2 ≠ 0}))
  (hbound : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ (N : ℕ)
    (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)),
      BddAbove (range fun y ↦ Symbol.seminorm K α β ((a y).remainder χ N)))

omit [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] in
include hjets htjets in
/-- The remainders of the family after `N` terms, for any cutoff, have jointly continuous jets. -/
theorem continuous_iteratedFDeriv_remainder (χ : FrequencyCutoff (CoordinateSpace n))
    (N k : ℕ) :
    Continuous (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k ((a p.1).remainder χ N).coefficient p.2) := by
  have heq (y : Y) : ((a y).remainder χ N).coefficient = (a y).toSymbol.coefficient -
      ∑ j ∈ Finset.range N, fun q : CoordinateSpace n × CoordinateSpace n ↦
        χ q.2 • ((a y).term j).coefficient q := by
    funext q
    simp [Finset.sum_apply]
  have hsmooth (y : Y) (j : ℕ) : ContDiff ℝ ∞ fun q : CoordinateSpace n × CoordinateSpace n ↦
      χ q.2 • ((a y).term j).coefficient q :=
    ((a y).term j).contDiff_smul_coefficient χ
  have hk : ((k : ℕ∞) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  simp_rw [heq]
  have hrw (p : Y × (CoordinateSpace n × CoordinateSpace n)) :
      iteratedFDeriv ℝ k ((a p.1).toSymbol.coefficient - ∑ j ∈ Finset.range N,
        fun q : CoordinateSpace n × CoordinateSpace n ↦ χ q.2 • ((a p.1).term j).coefficient q)
          p.2 =
        iteratedFDeriv ℝ k (a p.1).toSymbol.coefficient p.2 - ∑ j ∈ Finset.range N,
          iteratedFDeriv ℝ k (fun q : CoordinateSpace n × CoordinateSpace n ↦
            χ q.2 • ((a p.1).term j).coefficient q) p.2 := by
    have hsum : ContDiff ℝ ∞ (∑ j ∈ Finset.range N, fun q : CoordinateSpace n × CoordinateSpace n ↦
        χ q.2 • ((a p.1).term j).coefficient q) := by
      rw [Finset.sum_fn]
      exact ContDiff.sum fun j _ ↦ hsmooth p.1 j
    rw [iteratedFDeriv_sub_apply
      ((a p.1).toSymbol.contDiff_coefficient.contDiffAt.of_le hk) (hsum.contDiffAt.of_le hk),
      iteratedFDeriv_sum_apply fun j _ ↦ (hsmooth p.1 j).contDiffAt.of_le hk]
  simp_rw [hrw]
  exact (hjets k).sub (continuous_finsetSum _ fun j _ ↦
    HomogeneousSymbol.continuous_iteratedFDeriv_smul_coefficient (fun y ↦ (a y).term j)
      (htjets j) χ k)

include hjets htjets in
/-- The integrals of the remainders of the family, for any cutoff, are the remainders of the
integrated expansion. -/
private theorem integral_coefficient_remainder (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    ∫ y, ((a y).remainder χ N).coefficient p ∂μ =
      ∫ y, (a y).toSymbol.coefficient p ∂μ -
        ∑ j ∈ Finset.range N, χ p.2 • ∫ y, ((a y).term j).coefficient p ∂μ := by
  have hint (j : ℕ) : Integrable (fun y ↦ χ p.2 • ((a y).term j).coefficient p) μ :=
    (HomogeneousSymbol.integrable_coefficient_family μ (fun y ↦ (a y).term j) (htjets j) p).smul
      (χ p.2)
  simp only [coefficient_remainder]
  rw [integral_sub (Symbol.integrable_coefficient_family μ (fun y ↦ (a y).toSymbol) hjets p)
      (integrable_finsetSum _ fun j _ ↦ hint j),
    integral_finsetSum _ fun j _ ↦ hint j]
  simp only [integral_smul]

omit [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] in
include hbound in
/-- Seminorms of the remainders bounded independently of the parameter for one cutoff give the
parameter-uniform estimates of `TauCeti.Symbol.integral` for the full symbols. -/
theorem exists_bound_toSymbol (K : Set (CoordinateSpace n)) (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (a y).toSymbol.coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨χ, hχ⟩ := hbound
  -- The remainder after no terms is the full symbol.
  have heq (y : Y) : ((a y).remainder χ 0).coefficient = (a y).toSymbol.coefficient := by
    funext p
    simp
  simpa [heq] using
    Symbol.exists_bound_of_bddAbove_seminorm (fun y ↦ (a y).remainder χ 0) (hχ 0) K hK α β

/-- **Integration preserves classical symbols.** The integral of a compact family of classical
symbols of order `m` is classical of order `m`, with homogeneous terms the integrals of the
homogeneous terms. The full symbols must have jointly continuous jets, the homogeneous terms
jointly continuous jets away from the zero frequency, and the remainders after `N` terms, for some
frequency cutoff, seminorms bounded independently of the parameter for every `N`. Then the
remainders of the integral are the integrals of the remainders
(`TauCeti.ClassicalSymbol.coefficient_remainder_integral`), and a parameter-uniform seminorm
bound `C` on them becomes `μ.real univ * C`
(`TauCeti.ClassicalSymbol.seminorm_remainder_integral_le`). -/
def integral : ClassicalSymbol n V W m where
  toSymbol := Symbol.integral μ (fun y ↦ (a y).toSymbol) hjets (exists_bound_toSymbol a hbound)
  term j := HomogeneousSymbol.integral μ (fun y ↦ (a y).term j) (htjets j)
  exists_remainder' := by
    obtain ⟨χ, hχ⟩ := hbound
    refine ⟨χ, fun N ↦ ⟨Symbol.integral μ (fun y ↦ (a y).remainder χ N)
      (continuous_iteratedFDeriv_remainder a hjets htjets χ N)
      (Symbol.exists_bound_of_bddAbove_seminorm _ (hχ N)), fun p ↦ ?_⟩⟩
    simp only [Symbol.coefficient_integral, HomogeneousSymbol.coefficient_integral]
    exact integral_coefficient_remainder μ a hjets htjets χ N p

/-- The full symbol of the integral of classical symbols is the integral of the full symbols. -/
@[simp]
theorem toSymbol_integral :
    (integral μ a hjets htjets hbound).toSymbol =
      Symbol.integral μ (fun y ↦ (a y).toSymbol) hjets (exists_bound_toSymbol a hbound) :=
  (rfl)

/-- The coefficient of the full symbol of the integral of classical symbols is the integral of
the coefficients. -/
theorem coefficient_toSymbol_integral (p : CoordinateSpace n × CoordinateSpace n) :
    (integral μ a hjets htjets hbound).toSymbol.coefficient p =
      ∫ y, (a y).toSymbol.coefficient p ∂μ := by
  rw [toSymbol_integral, Symbol.coefficient_integral]

/-- A parameter-uniform seminorm bound `C ≥ 0` on the full symbols becomes `μ.real univ * C` for
the full symbol of the integral. -/
theorem seminorm_toSymbol_integral_le (K : Compacts (CoordinateSpace n)) (α β : List (Fin n))
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ y, Symbol.seminorm K α β (a y).toSymbol ≤ C) :
    Symbol.seminorm K α β (integral μ a hjets htjets hbound).toSymbol ≤ μ.real univ * C :=
  Symbol.seminorm_integral_le μ (fun y ↦ (a y).toSymbol) hjets (exists_bound_toSymbol a hbound)
    K α β hC h

/-- The homogeneous terms of the integral of classical symbols are the integrals of the
homogeneous terms. -/
@[simp]
theorem term_integral (j : ℕ) :
    (integral μ a hjets htjets hbound).term j =
      HomogeneousSymbol.integral μ (fun y ↦ (a y).term j) (htjets j) :=
  (rfl)

/-- The principal symbol of the integral of classical symbols is the integral of the principal
symbols. -/
@[simp]
theorem principal_integral :
    (integral μ a hjets htjets hbound).principal =
      HomogeneousSymbol.integral μ (fun y ↦ (a y).principal)
        (fun k ↦ by simpa only [coefficient_principal] using htjets 0 k) := by
  ext p
  simp

/-- **Averaging preserves an invariant principal symbol.** If every member of the family has
principal symbol `h`, so does its average for a probability measure. -/
theorem principal_integral_of_forall_principal_eq [IsProbabilityMeasure μ]
    [CompleteSpace (V →L[ℂ] W)]
    {h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m}
    (hh : ∀ y, (a y).principal = h) : (integral μ a hjets htjets hbound).principal = h := by
  have h0 (y : Y) : ((a y).term 0).coefficient = h.coefficient := by
    rw [← coefficient_principal, hh]
  ext p
  simp [h0]

/-- The remainder of the integral of classical symbols after `N` terms, for any frequency cutoff,
is the integral of the remainders. -/
theorem coefficient_remainder_integral (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    ((integral μ a hjets htjets hbound).remainder χ N).coefficient p =
      ∫ y, ((a y).remainder χ N).coefficient p ∂μ := by
  rw [coefficient_remainder, integral_coefficient_remainder μ a hjets htjets]
  simp

/-- The remainder of the integral of classical symbols after `N` terms, for any frequency cutoff,
is the symbol integral of the remainders, given parameter-uniform estimates on them. -/
theorem remainder_integral (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ)
    (hb : ∀ K : Set (CoordinateSpace n), IsCompact K → ∀ α β : List (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
        ‖mixedDeriv α β ((a y).remainder χ N).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m - N - β.length) / 2)) :
    (integral μ a hjets htjets hbound).remainder χ N =
      Symbol.integral μ (fun y ↦ (a y).remainder χ N)
        (continuous_iteratedFDeriv_remainder a hjets htjets χ N) hb :=
  Symbol.ext (funext (coefficient_remainder_integral μ a hjets htjets hbound χ N))

/-- A parameter-uniform seminorm bound `C ≥ 0` on the remainders after `N` terms becomes
`μ.real univ * C` for the remainder of the integral. -/
theorem seminorm_remainder_integral_le (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ)
    (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ y, Symbol.seminorm K α β ((a y).remainder χ N) ≤ C) :
    Symbol.seminorm K α β ((integral μ a hjets htjets hbound).remainder χ N) ≤
      μ.real univ * C :=
  Symbol.seminorm_le_of_coefficient_eq_integral μ (fun y ↦ (a y).remainder χ N)
    (continuous_iteratedFDeriv_remainder a hjets htjets χ N) _
    (funext (coefficient_remainder_integral μ a hjets htjets hbound χ N)) K α β hC h

/-- A probability average fixes a constant family of classical symbols. -/
@[simp]
theorem integral_const_of_probability [IsProbabilityMeasure μ] [CompleteSpace (V →L[ℂ] W)]
    (b : ClassicalSymbol n V W m)
    {hjets : ∀ k : ℕ, Continuous
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k b.toSymbol.coefficient p.2)}
    {htjets : ∀ j k : ℕ, ContinuousOn
      (fun p : Y × (CoordinateSpace n × CoordinateSpace n) ↦
        iteratedFDeriv ℝ k (b.term j).coefficient p.2)
      (univ ×ˢ {p | p.2 ≠ 0})}
    {hbound : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ (N : ℕ)
      (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)),
        BddAbove (range fun _ : Y ↦ Symbol.seminorm K α β (b.remainder χ N))} :
    integral μ (fun _ : Y ↦ b) hjets htjets hbound = b := by
  ext : 1
  apply Symbol.ext
  funext p
  simp

end TauCeti.ClassicalSymbol
