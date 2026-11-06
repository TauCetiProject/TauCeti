/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Positive
public import TauCeti.Analysis.OperatorIdeal.Family.DixmierTrace.Basic
public import TauCeti.Analysis.OperatorIdeal.Family.Modulus
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

/-!
# Additivity and linear extension of Dixmier traces

When the generalized limit `ω` is dilation invariant
(`TauCeti.GeneralizedLimit.IsDilationInvariant`), the Dixmier trace `Tr_ω`
(`TauCeti.dixmierTrace`) is additive and Loewner monotone on the cone of positive operators in the
logarithmic ideal `L^(1,∞)` (`TauCeti.OperatorIdealFamily.logarithmic`).

Over `ℂ`, every operator `T` in `L^(1,∞)` decomposes into four positive operators in `L^(1,∞)` via
the Cartesian decomposition `T = ℜ T + i ℑ T` and the positive/negative-part decomposition
`A = A⁺ - A⁻` of self-adjoint operators. Extending `Tr_ω` along this Jordan–Cartesian decomposition
defines the complex-valued Dixmier trace `TauCeti.complexDixmierTrace ω T`, which agrees with
`TauCeti.dixmierTrace ω T` on positive operators and takes the junk value `0` outside `L^(1,∞)`.

For every generalized limit `ω`, `complexDixmierTrace ω` commutes with `star`/adjoints, is
invariant under unitary conjugation, satisfies `Tr_ω(U T) = Tr_ω(T U)` for unitary `U`, and
vanishes on trace-class and finite-rank operators. When `ω` is dilation invariant, it extends to a
`ℂ`-linear and `‖·‖_(1,∞)`-continuous singular trace (`TauCeti.linearDixmierTrace`,
`TauCeti.linearDixmierTraceCLM`) of norm at most `1` on `L^(1,∞)`, satisfying full traciality
`Tr_ω(A T) = Tr_ω(T A)` against bounded operators and the two-sided ideal bound
`‖Tr_ω(A T B)‖ ≤ ‖A‖ Tr_ω(|T|) ‖B‖`.

## Main declarations

* `TauCeti.dixmierTrace_mono_of_isPositive`: Loewner monotonicity `0 ≤ S ≤ T → Tr_ω(S) ≤ Tr_ω(T)`.
* `TauCeti.dixmierTrace_add_of_isPositive`: additivity of `Tr_ω` on positive operators in `L^(1,∞)`
  for dilation-invariant `ω`.
* `TauCeti.complexDixmierTrace`: Jordan–Cartesian extension of `Tr_ω` to `E →L[ℂ] E`.
* `TauCeti.linearDixmierTrace`, `TauCeti.linearDixmierTraceCLM`: the `ℂ`-linear and continuous
  `ℂ`-linear Dixmier trace on `L^(1,∞)` for dilation-invariant `ω`.
* `TauCeti.complexDixmierTrace_comp_comm`,
  `TauCeti.complexDixmierTrace_comp_nonneg_of_isPositive`: traciality `Tr_ω(A T) = Tr_ω(T A)` and
  positivity of `B ↦ Tr_ω(B T)` for `T ≥ 0` in `L^(1,∞)`.
* `TauCeti.norm_complexDixmierTrace_comp_comp_le`,
  `TauCeti.norm_complexDixmierTrace_le_dixmierTrace`,
  `TauCeti.norm_complexDixmierTrace_le_toReal_gauge_logarithmic`: sharp ideal and norm bounds.

## References

* J. Dixmier, *Existence de traces non normales*, C. R. Acad. Sci. Paris Sér. A-B 262 (1966),
  A1107–A1108.
* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter IV, §2.β.
* G. V. Kalton, F. A. Sukochev, *Symmetric norms and spaces of operators*, J. Reine Angew. Math.
  621 (2008), 81–121.
-/

public section

open Filter Topology

open scoped NNReal ENNReal ComplexStarModule BoundedContinuousFunction

namespace TauCeti

open ContinuousLinearMap OperatorIdealFamily

/-! ### Positive-cone monotonicity and additivity -/

section PositiveCone

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Loewner monotonicity of the Dixmier trace.** If `0 ≤ S ≤ T` and `T` lies in `L^(1,∞)`, then
`Tr_ω(S) ≤ Tr_ω(T)` for every generalized limit `ω`. -/
theorem dixmierTrace_mono_of_isPositive (ω : GeneralizedLimit) {S T : E →L[𝕜] E}
    (hS : S.IsPositive) (hST : S ≤ T)
    (hT : T ∈ ((logarithmic 𝕜).operatorGauge E E).finiteSubmodule) :
    dixmierTrace ω S ≤ dixmierTrace ω T :=
  dixmierTrace_le_of_forall_kyFanGauge_le ω hT (hS.kyFanGauge_mono hST)

/-- **Additivity of the Dixmier trace on positive operators.** When `ω` is dilation invariant,
`Tr_ω(S + T) = Tr_ω(S) + Tr_ω(T)` for positive operators `S` and `T` in `L^(1,∞)`. -/
theorem dixmierTrace_add_of_isPositive {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant)
    {S T : E →L[𝕜] E} (hS : S.IsPositive) (hT : T.IsPositive)
    (hSm : S ∈ ((logarithmic 𝕜).operatorGauge E E).finiteSubmodule)
    (hTm : T ∈ ((logarithmic 𝕜).operatorGauge E E).finiteSubmodule) :
    dixmierTrace ω (S + T) = dixmierTrace ω S + dixmierTrace ω T := by
  -- Subadditivity gives `≤`; for `≥`, combine `K_(q+1)(S) + K_(q+1)(T) ≤ K_(2(q+1))(S + T)` at
  -- `q = n / 3` with dilation invariance `ω (f.dilate 3) = ω f`.
  refine le_antisymm (dixmierTrace_add_le ω hSm hTm) ?_
  obtain ⟨fS, hfS⟩ := exists_coe_eq_kyFanLogMean hSm
  obtain ⟨fT, hfT⟩ := exists_coe_eq_kyFanLogMean hTm
  obtain ⟨fST, hfST⟩ := exists_coe_eq_kyFanLogMean (Submodule.add_mem _ hSm hTm)
  rw [dixmierTrace_eq_apply ω fS hfS, dixmierTrace_eq_apply ω fT hfT,
    dixmierTrace_eq_apply ω fST hfST]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  rw [← ω.isDilationInvariant_iff.1 hω fS 3 (by positivity),
    ← ω.isDilationInvariant_iff.1 hω fT 3 (by positivity), ← map_add, ← sub_le_iff_le_add',
    ← map_sub]
  have hdiv : Tendsto (fun n : ℕ ↦ n / 3) atTop atTop :=
    tendsto_atTop_atTop.2 fun b ↦ ⟨3 * b, fun n hn ↦ by omega⟩
  have herr : Tendsto (fun n : ℕ ↦ ‖fST‖ * (Real.log 3 / Real.log ((n / 3 : ℕ) + 2)))
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (((Real.tendsto_log_natCast_add_atTop 2).comp hdiv).inv_tendsto_atTop.const_mul
        (Real.log 3)).const_mul ‖fST‖
  refine ω.apply_le_of_eventually_le ?_
  filter_upwards [eventually_ge_atTop 3, herr.eventually (gt_mem_nhds hε)] with n hn3 hnε
  simp only [sub_apply, add_apply, BoundedContinuousFunction.dilate_apply]
  set q := n / 3
  have hlogq : 0 < Real.log ((q : ℝ) + 2) := Real.log_natCast_add_pos one_lt_two q
  have hlogn : 0 < Real.log ((n : ℝ) + 2) := Real.log_natCast_add_pos one_lt_two n
  have hlog_le : Real.log ((n : ℝ) + 2) ≤ Real.log 3 + Real.log ((q : ℝ) + 2) :=
    (Real.log_le_log (by positivity) (by exact_mod_cast (by omega : n + 2 ≤ 3 * (q + 2)))).trans_eq
      (Real.log_mul (by positivity) (by positivity))
  have hST_nonneg : 0 ≤ fST n := hfST ▸ (S + T).kyFanLogMean_nonneg n
  have hsum : fS q + fT q ≤ fST n * (Real.log ((n : ℝ) + 2) / Real.log ((q : ℝ) + 2)) := by
    rw [congrFun hfS q, congrFun hfT q, congrFun hfST n, kyFanLogMean_def, kyFanLogMean_def,
      kyFanLogMean_def, ← add_div, div_mul_div_cancel₀ hlogn.ne']
    refine div_le_div_of_nonneg_right ?_ hlogq.le
    exact_mod_cast (two_mul (q + 1) ▸ hS.kyFanGauge_add_kyFanGauge_le hT (q + 1) (q + 1)).trans
      ((S + T).monotone_kyFanGauge (by omega : 2 * (q + 1) ≤ n + 1))
  have hstep : fST n * (Real.log ((n : ℝ) + 2) / Real.log ((q : ℝ) + 2)) ≤
      fST n + ‖fST‖ * (Real.log 3 / Real.log ((q : ℝ) + 2)) :=
    calc fST n * (Real.log ((n : ℝ) + 2) / Real.log ((q : ℝ) + 2))
        ≤ fST n * ((Real.log 3 + Real.log ((q : ℝ) + 2)) / Real.log ((q : ℝ) + 2)) := by gcongr
      _ = fST n + fST n * (Real.log 3 / Real.log ((q : ℝ) + 2)) := by
          rw [add_div, div_self hlogq.ne', mul_add, mul_one, add_comm (fST n * _)]
      _ ≤ fST n + ‖fST‖ * (Real.log 3 / Real.log ((q : ℝ) + 2)) := by
          have : 0 ≤ Real.log 3 / Real.log ((q : ℝ) + 2) :=
            div_nonneg (Real.log_nonneg (by norm_num)) hlogq.le
          gcongr; exact fST.apply_le_norm n
  linarith

/-- Finite-sum version of `TauCeti.dixmierTrace_add_of_isPositive`. -/
theorem dixmierTrace_sum_of_isPositive {ι : Type*} {ω : GeneralizedLimit}
    (hω : ω.IsDilationInvariant) (s : Finset ι) {f : ι → E →L[𝕜] E}
    (hpos : ∀ i ∈ s, (f i).IsPositive)
    (hmem : ∀ i ∈ s, f i ∈ ((logarithmic 𝕜).operatorGauge E E).finiteSubmodule) :
    dixmierTrace ω (∑ i ∈ s, f i) = ∑ i ∈ s, dixmierTrace ω (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      dixmierTrace_add_of_isPositive hω (hpos a (Finset.mem_insert_self a s))
        (nonneg_iff_isPositive.1 <| Finset.sum_nonneg fun i hi ↦
          nonneg_iff_isPositive.2 (hpos i (Finset.mem_insert_of_mem hi)))
        (hmem a (Finset.mem_insert_self a s))
        (Submodule.sum_mem _ fun i hi ↦ hmem i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi ↦ hpos i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hmem i (Finset.mem_insert_of_mem hi))]

/-- For a self-adjoint operator `T` in `L^(1,∞)` and a dilation-invariant generalized limit `ω`,
`Tr_ω(T⁺) + Tr_ω(T⁻) = Tr_ω(|T|) = dixmierTrace ω T`. -/
theorem dixmierTrace_posPart_add_negPart [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
    {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant) {T : E →L[𝕜] E}
    (hT : IsSelfAdjoint T) (hTm : T ∈ ((logarithmic 𝕜).operatorGauge E E).finiteSubmodule) :
    dixmierTrace ω T⁺ + dixmierTrace ω T⁻ = dixmierTrace ω T := by
  rw [← dixmierTrace_add_of_isPositive hω (nonneg_iff_isPositive.1 (CFC.posPart_nonneg T))
    (nonneg_iff_isPositive.1 (CFC.negPart_nonneg T))
    (posPart_mem_finiteSubmodule hTm) (negPart_mem_finiteSubmodule hTm),
    CFC.posPart_add_negPart T hT, ← modulus_eq_abs, dixmierTrace_modulus]

end PositiveCone

/-! ### Complex-valued extension of the Dixmier trace -/

section Complex

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open Classical in
/-- The **complex-valued Dixmier trace** on `E →L[ℂ] E`, extending `TauCeti.dixmierTrace` from the
positive cone of `L^(1,∞)` to all of `L^(1,∞)` via the Jordan–Cartesian decomposition
`T = ((ℜ T)⁺ - (ℜ T)⁻) + i ((ℑ T)⁺ - (ℑ T)⁻)`. Outside `L^(1,∞)` it takes the junk value `0`.

Additivity and `ℂ`-linearity hold when `ω` is dilation invariant (`TauCeti.linearDixmierTrace`);
a general positive extension of limits without dilation invariance is not asserted to give an
additive trace. -/
noncomputable def complexDixmierTrace (ω : GeneralizedLimit) (T : E →L[ℂ] E) : ℂ :=
  if T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule then
    ((dixmierTrace ω (ℜ T : E →L[ℂ] E)⁺ - dixmierTrace ω (ℜ T : E →L[ℂ] E)⁻ : ℝ) : ℂ) +
      Complex.I * ((dixmierTrace ω (ℑ T : E →L[ℂ] E)⁺ - dixmierTrace ω (ℑ T : E →L[ℂ] E)⁻ : ℝ) : ℂ)
  else 0

/-- Formula for `TauCeti.complexDixmierTrace` on operators in `L^(1,∞)`. -/
theorem complexDixmierTrace_of_mem (ω : GeneralizedLimit) {T : E →L[ℂ] E}
    (hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    complexDixmierTrace ω T =
      ((dixmierTrace ω (ℜ T : E →L[ℂ] E)⁺ - dixmierTrace ω (ℜ T : E →L[ℂ] E)⁻ : ℝ) : ℂ) +
        Complex.I * ((dixmierTrace ω (ℑ T : E →L[ℂ] E)⁺ -
          dixmierTrace ω (ℑ T : E →L[ℂ] E)⁻ : ℝ) : ℂ) := ite_eq_left hT

/-- Outside `L^(1,∞)`, `TauCeti.complexDixmierTrace` takes the junk value `0`. -/
theorem complexDixmierTrace_of_notMem (ω : GeneralizedLimit) {T : E →L[ℂ] E}
    (hT : T ∉ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    complexDixmierTrace ω T = 0 := ite_eq_right hT

/-- `TauCeti.complexDixmierTrace` vanishes at `0`. -/
@[simp]
theorem complexDixmierTrace_zero (ω : GeneralizedLimit) :
    complexDixmierTrace ω (0 : E →L[ℂ] E) = 0 := by
  rw [complexDixmierTrace_of_mem ω (Submodule.zero_mem _)]; simp

/-- On a self-adjoint operator in `L^(1,∞)`, `TauCeti.complexDixmierTrace` equals
`Tr_ω(T⁺) - Tr_ω(T⁻)`. -/
theorem complexDixmierTrace_of_isSelfAdjoint (ω : GeneralizedLimit) {T : E →L[ℂ] E}
    (hT : IsSelfAdjoint T) (hTm : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    complexDixmierTrace ω T = ((dixmierTrace ω T⁺ - dixmierTrace ω T⁻ : ℝ) : ℂ) := by
  rw [complexDixmierTrace_of_mem ω hTm, hT.coe_realPart, hT.imaginaryPart]; simp

/-- On a positive operator, `TauCeti.complexDixmierTrace` agrees with `TauCeti.dixmierTrace`. -/
theorem complexDixmierTrace_of_isPositive (ω : GeneralizedLimit) {T : E →L[ℂ] E}
    (hT : T.IsPositive) : complexDixmierTrace ω T = (dixmierTrace ω T : ℂ) := by
  by_cases hTm : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule
  · have hnn : 0 ≤ T := nonneg_iff_isPositive.2 hT
    rw [complexDixmierTrace_of_isSelfAdjoint ω hT.isSelfAdjoint hTm,
      (CFC.posPart_eq_self T).2 hnn, (CFC.negPart_eq_zero_iff T hT.isSelfAdjoint).2 hnn,
      dixmierTrace_zero, sub_zero]
  · rw [complexDixmierTrace_of_notMem ω hTm, dixmierTrace_of_notMem ω hTm, Complex.ofReal_zero]

/-- `TauCeti.complexDixmierTrace` commutes with negation. -/
@[simp]
theorem complexDixmierTrace_neg (ω : GeneralizedLimit) (T : E →L[ℂ] E) :
    complexDixmierTrace ω (-T) = -complexDixmierTrace ω T := by
  by_cases hTm : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule
  · rw [complexDixmierTrace_of_mem ω (Submodule.neg_mem _ hTm), complexDixmierTrace_of_mem ω hTm]
    simp only [map_neg, AddSubgroup.coe_neg, CFC.posPart_neg, CFC.negPart_neg]; push_cast; ring
  · have hneg : -T ∉ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule := fun h ↦
      hTm (by simpa using Submodule.neg_mem _ h)
    rw [complexDixmierTrace_of_notMem ω hneg, complexDixmierTrace_of_notMem ω hTm, neg_zero]

/-- `TauCeti.complexDixmierTrace` commutes with `star`. -/
@[simp]
theorem complexDixmierTrace_star (ω : GeneralizedLimit) (T : E →L[ℂ] E) :
    complexDixmierTrace ω (star T) = star (complexDixmierTrace ω T) := by
  have hre : ℜ (star T) = ℜ T := by ext1; simp [realPart_apply_coe, add_comm]
  have him : ℑ (star T) = -ℑ T := by
    ext1; rw [AddSubgroup.coe_neg, imaginaryPart_apply_coe, imaginaryPart_apply_coe, star_star,
      ← neg_sub T (star T), smul_neg, smul_neg]
  by_cases hTm : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule
  · rw [complexDixmierTrace_of_mem ω ((star_mem_finiteSubmodule_iff T).2 hTm),
      complexDixmierTrace_of_mem ω hTm, hre, him]
    simp only [AddSubgroup.coe_neg, CFC.posPart_neg, CFC.negPart_neg, map_add, map_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
  · rw [complexDixmierTrace_of_notMem ω (mt (star_mem_finiteSubmodule_iff T).1 hTm),
      complexDixmierTrace_of_notMem ω hTm, star_zero]

/-- `TauCeti.complexDixmierTrace` sends the adjoint of an operator to the conjugate trace. -/
@[simp]
theorem complexDixmierTrace_adjoint (ω : GeneralizedLimit) (T : E →L[ℂ] E) :
    complexDixmierTrace ω (adjoint T) = star (complexDixmierTrace ω T) :=
  complexDixmierTrace_star ω T

/-! ### Unitary invariance and vanishing on trace-class operators -/

/-- **Unitary invariance under linear isometric equivalences.** Conjugating `T : E →L[ℂ] E` by a
linear isometric equivalence `e : E ≃ₗᵢ[ℂ] F` preserves `TauCeti.complexDixmierTrace`. -/
@[simp]
theorem complexDixmierTrace_conjStarAlgEquiv (ω : GeneralizedLimit) (e : E ≃ₗᵢ[ℂ] F)
    (T : E →L[ℂ] E) : complexDixmierTrace ω (e.conjStarAlgEquiv T) = complexDixmierTrace ω T := by
  have hdix (X : E →L[ℂ] E) : dixmierTrace ω (e.conjStarAlgEquiv X) = dixmierTrace ω X :=
    dixmierTrace_comp_linearIsometryEquiv ω X e.symm e
  by_cases hTm : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule
  · rw [complexDixmierTrace_of_mem ω
        ((e.conjStarAlgEquiv_mem_finiteSubmodule_logarithmic_iff T).2 hTm),
      complexDixmierTrace_of_mem ω hTm,
      ← map_realPart e.conjStarAlgEquiv T, ← map_imaginaryPart e.conjStarAlgEquiv T]
    simp only [e.posPart_conjStarAlgEquiv, e.negPart_conjStarAlgEquiv, hdix]
  · rw [complexDixmierTrace_of_notMem ω
        (mt (e.conjStarAlgEquiv_mem_finiteSubmodule_logarithmic_iff T).1 hTm),
      complexDixmierTrace_of_notMem ω hTm]

/-- **Unitary conjugation invariance.** `Tr_ω(U T U⋆) = Tr_ω(T)` for every unitary operator `U`. -/
@[simp]
theorem complexDixmierTrace_unitary_conj (ω : GeneralizedLimit) (u : unitary (E →L[ℂ] E))
    (T : E →L[ℂ] E) :
    complexDixmierTrace ω ((u : E →L[ℂ] E) ∘L T ∘L star (u : E →L[ℂ] E)) =
      complexDixmierTrace ω T :=
  complexDixmierTrace_conjStarAlgEquiv ω (Unitary.linearIsometryEquiv u) T

/-- **Unitary traciality.** `Tr_ω(U T) = Tr_ω(T U)` for every unitary operator `U` and every
bounded operator `T`. -/
theorem complexDixmierTrace_unitary_comp_comm (ω : GeneralizedLimit) (u : unitary (E →L[ℂ] E))
    (T : E →L[ℂ] E) :
    complexDixmierTrace ω ((u : E →L[ℂ] E) ∘L T) =
      complexDixmierTrace ω (T ∘L (u : E →L[ℂ] E)) := by
  have h1 : (u : E →L[ℂ] E) ∘L star (u : E →L[ℂ] E) = 1 := by
    rw [← mul_def, ← Unitary.coe_star, Unitary.coe_mul_star_self]
  simpa only [comp_assoc, h1, one_def, comp_id] using
    complexDixmierTrace_unitary_conj ω u (T ∘L (u : E →L[ℂ] E))

/-- **Dixmier traces vanish on the trace class.** -/
theorem complexDixmierTrace_eq_zero_of_mem_traceClass (ω : GeneralizedLimit) {T : E →L[ℂ] E}
    (hT : T ∈ ((traceClass ℂ).operatorGauge E E).finiteSubmodule) :
    complexDixmierTrace ω T = 0 := by
  have hre := realPart_mem_finiteSubmodule hT
  have him := imaginaryPart_mem_finiteSubmodule hT
  rw [complexDixmierTrace_of_mem ω (finiteSubmodule_traceClass_le_logarithmic E E hT),
    dixmierTrace_eq_zero_of_mem_traceClass ω (posPart_mem_finiteSubmodule hre),
    dixmierTrace_eq_zero_of_mem_traceClass ω (negPart_mem_finiteSubmodule hre),
    dixmierTrace_eq_zero_of_mem_traceClass ω (posPart_mem_finiteSubmodule him),
    dixmierTrace_eq_zero_of_mem_traceClass ω (negPart_mem_finiteSubmodule him)]; simp

/-- **Dixmier traces vanish on finite-rank operators.** -/
theorem complexDixmierTrace_eq_zero_of_rank_le (ω : GeneralizedLimit) {T : E →L[ℂ] E} {n : ℕ}
    (hT : T.rank ≤ n) : complexDixmierTrace ω T = 0 :=
  complexDixmierTrace_eq_zero_of_mem_traceClass ω <| (mem_finiteSubmodule_traceClass_iff T).2 <|
    T.nuclearENorm_ne_top_iff_summable.1 (T.nuclearENorm_ne_top_of_rank_le hT)

/-! ### Scalar homogeneity, additivity, and `ℂ`-linearity -/

/-- Real homogeneity of `TauCeti.complexDixmierTrace` (valid for every generalized limit `ω`). -/
theorem complexDixmierTrace_real_smul (ω : GeneralizedLimit) (r : ℝ) (T : E →L[ℂ] E) :
    complexDixmierTrace ω (r • T) = r * complexDixmierTrace ω T := by
  have hpos {r : ℝ} (hr : 0 < r) (T : E →L[ℂ] E) :
      complexDixmierTrace ω (r • T) = r * complexDixmierTrace ω T := by
    by_cases hTm : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule
    · have hrTm : r • T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule := by
        rw [← Complex.coe_smul]; exact Submodule.smul_mem _ _ hTm
      have hpart (A : E →L[ℂ] E) :
          dixmierTrace ω (r • A)⁺ - dixmierTrace ω (r • A)⁻ =
            r * (dixmierTrace ω A⁺ - dixmierTrace ω A⁻) := by
        rw [CFC.posPart_smul_of_nonneg hr.le, CFC.negPart_smul_of_nonneg hr.le,
          ← Complex.coe_smul, ← Complex.coe_smul, dixmierTrace_smul, dixmierTrace_smul,
          Complex.norm_of_nonneg hr.le, mul_sub]
      rw [complexDixmierTrace_of_mem ω hrTm, complexDixmierTrace_of_mem ω hTm]
      simp only [map_smul, selfAdjoint.val_smul, hpart]; push_cast; ring
    · have hrTm : r • T ∉ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule := fun h ↦ hTm <| by
        have := Submodule.smul_mem _ ((r : ℂ)⁻¹) h
        rwa [← Complex.coe_smul, inv_smul_smul₀ (Complex.ofReal_ne_zero.2 hr.ne')] at this
      rw [complexDixmierTrace_of_notMem ω hrTm, complexDixmierTrace_of_notMem ω hTm, mul_zero]
  rcases lt_trichotomy 0 r with hr | rfl | hr
  · exact hpos hr T
  · simp
  · rw [← neg_neg r, neg_smul, complexDixmierTrace_neg, hpos (neg_pos.2 hr)]; push_cast; ring

/-- Multiplication by `i` commutes with `TauCeti.complexDixmierTrace` for every generalized limit
`ω`. -/
@[simp]
theorem complexDixmierTrace_I_smul (ω : GeneralizedLimit) (T : E →L[ℂ] E) :
    complexDixmierTrace ω (Complex.I • T) = Complex.I * complexDixmierTrace ω T := by
  by_cases hTm : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule
  · rw [complexDixmierTrace_of_mem ω (Submodule.smul_mem _ _ hTm), complexDixmierTrace_of_mem ω hTm]
    simp only [realPart_I_smul, imaginaryPart_I_smul, AddSubgroup.coe_neg, CFC.posPart_neg,
      CFC.negPart_neg, mul_add, ← mul_assoc, Complex.I_mul_I]; push_cast; ring
  · rw [complexDixmierTrace_of_notMem ω (fun h ↦
      hTm (by simpa [smul_smul] using Submodule.smul_mem _ (-Complex.I) h)),
      complexDixmierTrace_of_notMem ω hTm, mul_zero]

private theorem signedDixmierTrace_selfAdjoint_add {ω : GeneralizedLimit}
    (hω : ω.IsDilationInvariant) {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hAm : A ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule)
    (hBm : B ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    dixmierTrace ω (A + B)⁺ - dixmierTrace ω (A + B)⁻ =
      (dixmierTrace ω A⁺ - dixmierTrace ω A⁻) + (dixmierTrace ω B⁺ - dixmierTrace ω B⁻) := by
  have hABm := Submodule.add_mem _ hAm hBm
  have hid : (A + B)⁺ + (A⁻ + B⁻) = (A + B)⁻ + (A⁺ + B⁺) := by
    have hsum : (A + B)⁺ - (A + B)⁻ = (A⁺ - A⁻) + (B⁺ - B⁻) := by
      rw [CFC.posPart_sub_negPart (A + B) (hA.add hB), CFC.posPart_sub_negPart A hA,
        CFC.posPart_sub_negPart B hB]
    calc (A + B)⁺ + (A⁻ + B⁻) = ((A + B)⁺ - (A + B)⁻) + (A + B)⁻ + (A⁻ + B⁻) := by abel
      _ = ((A⁺ - A⁻) + (B⁺ - B⁻)) + (A + B)⁻ + (A⁻ + B⁻) := by rw [hsum]
      _ = (A + B)⁻ + (A⁺ + B⁺) := by abel
  have hadd3 {X Y Z : E →L[ℂ] E} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
      (hXm : X ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule)
      (hYm : Y ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule)
      (hZm : Z ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
      dixmierTrace ω (X + (Y + Z)) = dixmierTrace ω X + (dixmierTrace ω Y + dixmierTrace ω Z) := by
    rw [dixmierTrace_add_of_isPositive hω (nonneg_iff_isPositive.1 hX)
        (nonneg_iff_isPositive.1 (add_nonneg hY hZ)) hXm (Submodule.add_mem _ hYm hZm),
      dixmierTrace_add_of_isPositive hω (nonneg_iff_isPositive.1 hY) (nonneg_iff_isPositive.1 hZ)
        hYm hZm]
  have heq := congrArg (dixmierTrace ω) hid
  rw [hadd3 (CFC.posPart_nonneg _) (CFC.negPart_nonneg _) (CFC.negPart_nonneg _)
      (posPart_mem_finiteSubmodule hABm) (negPart_mem_finiteSubmodule hAm)
      (negPart_mem_finiteSubmodule hBm),
    hadd3 (CFC.negPart_nonneg _) (CFC.posPart_nonneg _) (CFC.posPart_nonneg _)
      (negPart_mem_finiteSubmodule hABm) (posPart_mem_finiteSubmodule hAm)
      (posPart_mem_finiteSubmodule hBm)] at heq
  linarith

/-- **Additivity on `L^(1,∞)`.** When `ω` is dilation invariant, `TauCeti.complexDixmierTrace` is
additive on `L^(1,∞)`. -/
theorem complexDixmierTrace_add {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant)
    {S T : E →L[ℂ] E} (hS : S ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule)
    (hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    complexDixmierTrace ω (S + T) = complexDixmierTrace ω S + complexDixmierTrace ω T := by
  rw [complexDixmierTrace_of_mem ω (Submodule.add_mem _ hS hT),
    complexDixmierTrace_of_mem ω hS, complexDixmierTrace_of_mem ω hT]
  simp only [map_add, AddSubgroup.coe_add]
  rw [signedDixmierTrace_selfAdjoint_add hω (ℜ S).2 (ℜ T).2
      (realPart_mem_finiteSubmodule hS) (realPart_mem_finiteSubmodule hT),
    signedDixmierTrace_selfAdjoint_add hω (ℑ S).2 (ℑ T).2
      (imaginaryPart_mem_finiteSubmodule hS) (imaginaryPart_mem_finiteSubmodule hT)]
  push_cast; ring

/-- When `ω` is dilation invariant, `TauCeti.complexDixmierTrace` respects subtraction on
`L^(1,∞)`. -/
theorem complexDixmierTrace_sub {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant)
    {S T : E →L[ℂ] E} (hS : S ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule)
    (hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    complexDixmierTrace ω (S - T) = complexDixmierTrace ω S - complexDixmierTrace ω T := by
  rw [sub_eq_add_neg, complexDixmierTrace_add hω hS (Submodule.neg_mem _ hT),
    complexDixmierTrace_neg, sub_eq_add_neg]

/-- Finite-sum version of `TauCeti.complexDixmierTrace_add`. -/
theorem complexDixmierTrace_sum {ι : Type*} {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant)
    (s : Finset ι) {f : ι → E →L[ℂ] E}
    (hf : ∀ i ∈ s, f i ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    complexDixmierTrace ω (∑ i ∈ s, f i) = ∑ i ∈ s, complexDixmierTrace ω (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      complexDixmierTrace_add hω (hf a (Finset.mem_insert_self a s))
        (Submodule.sum_mem _ fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-- **Complex homogeneity.** When `ω` is dilation invariant,
`Tr_ω(c T) = c Tr_ω(T)` for every `c : ℂ` and every bounded operator `T`. -/
@[simp]
theorem complexDixmierTrace_smul {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant) (c : ℂ)
    (T : E →L[ℂ] E) : complexDixmierTrace ω (c • T) = c * complexDixmierTrace ω T := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases hTm : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule
  · have hdecomp : c • T = c.re • T + Complex.I • (c.im • T) := by
      nth_rw 1 [← Complex.re_add_im c]
      rw [add_smul, Complex.coe_smul, mul_comm (c.im : ℂ) Complex.I, mul_smul, Complex.coe_smul]
    rw [hdecomp, complexDixmierTrace_add hω
        (Complex.coe_smul c.re T ▸ Submodule.smul_mem _ _ hTm)
        (Submodule.smul_mem _ _ (Complex.coe_smul c.im T ▸ Submodule.smul_mem _ _ hTm)),
      complexDixmierTrace_I_smul, complexDixmierTrace_real_smul, complexDixmierTrace_real_smul]
    (conv_rhs => rw [← Complex.re_add_im c]); ring
  · rw [complexDixmierTrace_of_notMem ω (fun h ↦
      hTm (by simpa [hc] using Submodule.smul_mem _ c⁻¹ h)),
      complexDixmierTrace_of_notMem ω hTm, mul_zero]

/-- **The linear Dixmier trace on `L^(1,∞)`.** For a dilation-invariant generalized limit `ω`,
`TauCeti.complexDixmierTrace` restricts to a `ℂ`-linear functional on the logarithmic ideal
`((logarithmic ℂ).operatorGauge E E).finiteSubmodule`. -/
noncomputable def linearDixmierTrace (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant) :
    ((logarithmic ℂ).operatorGauge E E).finiteSubmodule →ₗ[ℂ] ℂ where
  toFun T := complexDixmierTrace ω T.1
  map_add' S T := complexDixmierTrace_add hω S.2 T.2
  map_smul' c T := by simp [complexDixmierTrace_smul hω]

/-- Applying `TauCeti.linearDixmierTrace` evaluates `TauCeti.complexDixmierTrace` on the underlying
operator. -/
@[simp]
theorem linearDixmierTrace_apply {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant)
    (T : ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    linearDixmierTrace E hω T = complexDixmierTrace ω T.1 := (rfl)

/-! ### Traciality and sharp norm bounds -/

/-- **Traciality of the Dixmier trace.** When `ω` is dilation invariant, `Tr_ω(A T) = Tr_ω(T A)`
for every bounded operator `A : E →L[ℂ] E` and every `T` in `L^(1,∞)`. -/
theorem complexDixmierTrace_comp_comm {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant)
    (A : E →L[ℂ] E) {T : E →L[ℂ] E} (hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    complexDixmierTrace ω (A ∘L T) = complexDixmierTrace ω (T ∘L A) := by
  -- Span `E →L[ℂ] E` by four unitaries and apply unitary traciality to each summand.
  obtain ⟨u, c, rfl, -⟩ := CStarAlgebra.exists_sum_four_unitary A
  have hL : (∑ i, c i • (u i : E →L[ℂ] E)) ∘L T = ∑ i, c i • ((u i : E →L[ℂ] E) ∘L T) := by
    simp_rw [← mul_def, Finset.sum_mul, smul_mul_assoc]
  have hR : T ∘L (∑ i, c i • (u i : E →L[ℂ] E)) = ∑ i, c i • (T ∘L (u i : E →L[ℂ] E)) := by
    simp_rw [← mul_def, Finset.mul_sum, mul_smul_comm]
  rw [hL, hR, complexDixmierTrace_sum hω Finset.univ (fun i _ ↦
      Submodule.smul_mem _ _ ((logarithmic ℂ).comp_left_mem_finiteSubmodule _ hT)),
    complexDixmierTrace_sum hω Finset.univ (fun i _ ↦
      Submodule.smul_mem _ _ ((logarithmic ℂ).comp_right_mem_finiteSubmodule hT _))]
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp [complexDixmierTrace_smul hω, complexDixmierTrace_unitary_comp_comm]

/-- A commutator `A T - T A` with `T ∈ L^(1,∞)` has vanishing Dixmier trace for every
dilation-invariant `ω`. -/
theorem complexDixmierTrace_comp_sub_comp_eq_zero {ω : GeneralizedLimit}
    (hω : ω.IsDilationInvariant) (A : E →L[ℂ] E) {T : E →L[ℂ] E}
    (hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    complexDixmierTrace ω (A ∘L T - T ∘L A) = 0 := by
  rw [complexDixmierTrace_sub hω ((logarithmic ℂ).comp_left_mem_finiteSubmodule A hT)
      ((logarithmic ℂ).comp_right_mem_finiteSubmodule hT A),
    complexDixmierTrace_comp_comm hω A hT, sub_self]

open ComplexOrder in
/-- The product `B T` of a positive bounded operator `B` and a positive operator `T ∈ L^(1,∞)` has
nonnegative complex Dixmier trace for every dilation-invariant `ω`. -/
theorem complexDixmierTrace_comp_nonneg_of_isPositive {ω : GeneralizedLimit}
    (hω : ω.IsDilationInvariant) {B T : E →L[ℂ] E} (hB : B.IsPositive) (hT : T.IsPositive)
    (hTm : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    0 ≤ complexDixmierTrace ω (B ∘L T) := by
  -- Write `B = √B √B` and cycle `√B` by traciality so `Tr_ω(B T) = Tr_ω(√B T √B) ≥ 0`.
  set R := CFC.sqrt B
  have hRadj : adjoint R = R := (CFC.sqrt_nonneg B).isSelfAdjoint.star_eq
  have hRmul : R ∘L R = B := CFC.sqrt_mul_sqrt_self B (nonneg_iff_isPositive.2 hB)
  have hRpos : (R ∘L T ∘L R).IsPositive := by simpa [hRadj] using hT.conj_adjoint R
  rw [← hRmul, comp_assoc,
    complexDixmierTrace_comp_comm hω R ((logarithmic ℂ).comp_left_mem_finiteSubmodule R hTm),
    comp_assoc, complexDixmierTrace_of_isPositive ω hRpos]
  exact RCLike.nonneg_iff.2 ⟨by simpa using dixmierTrace_nonneg ω _, by simp⟩

private theorem norm_complexDixmierTrace_comp_left_le_of_isPositive {ω : GeneralizedLimit}
    (hω : ω.IsDilationInvariant) (A : E →L[ℂ] E) {T : E →L[ℂ] E} (hTpos : T.IsPositive)
    (hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    ‖complexDixmierTrace ω (A ∘L T)‖ ≤ ‖A‖ * dixmierTrace ω T := by
  -- `B ↦ Tr_ω(B T)` is positive by `complexDixmierTrace_comp_nonneg_of_isPositive`, hence
  -- automatically continuous on `E →L[ℂ] E` with `‖ψ‖ = ψ 1 = Tr_ω(T)`.
  open ComplexOrder in
  let ψ₀ : (E →L[ℂ] E) →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀
    { toFun := fun B ↦ complexDixmierTrace ω (B ∘L T)
      map_add' := fun B₁ B₂ ↦ by
        rw [add_comp, complexDixmierTrace_add hω
          ((logarithmic ℂ).comp_left_mem_finiteSubmodule B₁ hT)
          ((logarithmic ℂ).comp_left_mem_finiteSubmodule B₂ hT)]
      map_smul' := fun c B ↦ by simp [smul_comp, complexDixmierTrace_smul hω] }
    fun B hB ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      exact complexDixmierTrace_comp_nonneg_of_isPositive hω (nonneg_iff_isPositive.1 hB) hTpos hT
  let ψ : (E →L[ℂ] E) →P[ℂ] ℂ := .ofClass ψ₀
  -- `PositiveLinearMap.mk₀` has no `@[simp]` application lemma in Mathlib, so unfold it via `simp`.
  have hψ (X : E →L[ℂ] E) : (ψ : (E →L[ℂ] E) →L[ℂ] ℂ) X = complexDixmierTrace ω (X ∘L T) := by
    simp only [ψ, ψ₀, PositiveContinuousLinearMap.coe_toContinuousLinearMap,
      PositiveContinuousLinearMap.coe_ofClass, ← PositiveLinearMap.coe_toLinearMap,
      PositiveLinearMap.mk₀, LinearMap.coe_mk, AddHom.coe_mk]
  have hop : ‖(ψ : (E →L[ℂ] E) →L[ℂ] ℂ)‖ = dixmierTrace ω T := Complex.ofReal_inj.1 <| by
    rw [ψ.ofReal_opNorm_eq_map_one, ← PositiveContinuousLinearMap.coe_toContinuousLinearMap, hψ,
      one_def, id_comp, complexDixmierTrace_of_isPositive ω hTpos]
  simpa [hψ, hop, mul_comm] using (ψ : (E →L[ℂ] E) →L[ℂ] ℂ).le_opNorm A

/-- **Sharp two-sided ideal bound for the linear Dixmier trace.** When `ω` is dilation invariant
and `T` lies in `L^(1,∞)`, `‖Tr_ω(A T B)‖ ≤ ‖A‖ Tr_ω(|T|) ‖B‖`. -/
theorem norm_complexDixmierTrace_comp_comp_le {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant)
    (A : E →L[ℂ] E) {T : E →L[ℂ] E} (B : E →L[ℂ] E)
    (hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    ‖complexDixmierTrace ω (A ∘L T ∘L B)‖ ≤ ‖A‖ * dixmierTrace ω T * ‖B‖ := by
  -- Factor `T = W |T|` with `‖W‖ ≤ 1` and cycle `B` to the left by traciality.
  obtain ⟨W, hW, -, hWT, -⟩ := exists_contraction_of_gram_eq (A := T.modulus) (T := T)
    (by rw [adjoint_modulus, modulus_comp_modulus])
  have hmod : T.modulus ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule :=
    (modulus_mem_finiteSubmodule_iff T).2 hT
  have hrew : A ∘L T ∘L B = (A ∘L W ∘L T.modulus) ∘L B := by nth_rw 1 [← hWT]; simp [comp_assoc]
  have hassoc : B ∘L (A ∘L W ∘L T.modulus) = (B ∘L A ∘L W) ∘L T.modulus := by simp [comp_assoc]
  rw [hrew, ← complexDixmierTrace_comp_comm hω B ((logarithmic ℂ).comp_left_mem_finiteSubmodule A
    ((logarithmic ℂ).comp_left_mem_finiteSubmodule W hmod)), hassoc]
  have hBAW : ‖B ∘L A ∘L W‖ ≤ ‖B‖ * ‖A‖ := (B.opNorm_comp_le _).trans <|
    mul_le_mul_of_nonneg_left ((A.opNorm_comp_le W).trans
      (mul_le_of_le_one_right (norm_nonneg A) hW)) (norm_nonneg B)
  refine (norm_complexDixmierTrace_comp_left_le_of_isPositive hω _ (isPositive_modulus T)
    hmod).trans ?_
  rw [dixmierTrace_modulus]; linarith [mul_le_mul_of_nonneg_right hBAW (dixmierTrace_nonneg ω T)]

/-- Left ideal bound `‖Tr_ω(A T)‖ ≤ ‖A‖ Tr_ω(|T|)` for dilation-invariant `ω` and `T ∈ L^(1,∞)`. -/
theorem norm_complexDixmierTrace_comp_left_le {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant)
    (A : E →L[ℂ] E) {T : E →L[ℂ] E} (hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    ‖complexDixmierTrace ω (A ∘L T)‖ ≤ ‖A‖ * dixmierTrace ω T :=
  comp_id (A ∘L T) ▸ (norm_complexDixmierTrace_comp_comp_le hω A (.id ℂ E) hT).trans
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg A) (dixmierTrace_nonneg ω T)) norm_id_le)

/-- Right ideal bound `‖Tr_ω(T B)‖ ≤ Tr_ω(|T|) ‖B‖` for dilation-invariant `ω` and
`T ∈ L^(1,∞)`. -/
theorem norm_complexDixmierTrace_comp_right_le {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant)
    {T : E →L[ℂ] E} (B : E →L[ℂ] E) (hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule) :
    ‖complexDixmierTrace ω (T ∘L B)‖ ≤ dixmierTrace ω T * ‖B‖ := by
  nth_rw 1 [← id_comp T]
  exact (norm_complexDixmierTrace_comp_comp_le hω (.id ℂ E) B hT).trans (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (dixmierTrace_nonneg ω T) norm_id_le) (norm_nonneg B))

/-- **Modulus domination.** For every dilation-invariant `ω` and every bounded operator `T`,
`‖Tr_ω(T)‖ ≤ Tr_ω(|T|)`. -/
theorem norm_complexDixmierTrace_le_dixmierTrace {ω : GeneralizedLimit}
    (hω : ω.IsDilationInvariant) (T : E →L[ℂ] E) :
    ‖complexDixmierTrace ω T‖ ≤ dixmierTrace ω T := by
  by_cases hT : T ∈ ((logarithmic ℂ).operatorGauge E E).finiteSubmodule
  · nth_rw 1 [← id_comp T]
    exact (norm_complexDixmierTrace_comp_left_le hω (.id ℂ E) hT).trans
      (mul_le_of_le_one_left (dixmierTrace_nonneg ω T) norm_id_le)
  · rw [complexDixmierTrace_of_notMem ω hT, dixmierTrace_of_notMem ω hT, norm_zero]

/-- **Sharp boundedness by the logarithmic gauge.** For every dilation-invariant `ω` and every
bounded operator `T`, `‖Tr_ω(T)‖ ≤ ‖T‖_(1,∞)`. -/
theorem norm_complexDixmierTrace_le_toReal_gauge_logarithmic {ω : GeneralizedLimit}
    (hω : ω.IsDilationInvariant) (T : E →L[ℂ] E) :
    ‖complexDixmierTrace ω T‖ ≤ ((logarithmic ℂ).gauge T).toReal :=
  (norm_complexDixmierTrace_le_dixmierTrace hω T).trans
    (dixmierTrace_le_toReal_gauge_logarithmic ω T)

/-- **The continuous linear Dixmier trace on the normed carrier of `L^(1,∞)`.** When `ω` is
dilation invariant, `TauCeti.complexDixmierTrace` defines a bounded linear functional of norm at
most `1` on `((logarithmic ℂ).operatorGauge E E).Carrier`. -/
noncomputable def linearDixmierTraceCLM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant) :
    ((logarithmic ℂ).operatorGauge E E).Carrier →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun T ↦ complexDixmierTrace ω T.toContinuousLinearMap
      map_add' := fun S T ↦ complexDixmierTrace_add hω S.mem_finiteSubmodule T.mem_finiteSubmodule
      map_smul' := fun c T ↦ by simp [complexDixmierTrace_smul hω] }
    1 fun T ↦ by
      rw [one_mul, OperatorGauge.Carrier.norm_def, operatorGauge_apply]
      exact norm_complexDixmierTrace_le_toReal_gauge_logarithmic hω T.toContinuousLinearMap

/-- Applying `TauCeti.linearDixmierTraceCLM` evaluates `TauCeti.complexDixmierTrace` on the
underlying continuous linear map. -/
@[simp]
theorem linearDixmierTraceCLM_apply {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant)
    (T : ((logarithmic ℂ).operatorGauge E E).Carrier) :
    linearDixmierTraceCLM E hω T = complexDixmierTrace ω T.toContinuousLinearMap := (rfl)

/-- The continuous linear Dixmier trace on `((logarithmic ℂ).operatorGauge E E).Carrier` has
operator norm at most `1`. -/
theorem norm_linearDixmierTraceCLM_le {ω : GeneralizedLimit} (hω : ω.IsDilationInvariant) :
    ‖linearDixmierTraceCLM E hω‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _

end Complex

end TauCeti
