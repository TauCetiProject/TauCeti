/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.Commute
public import TauCeti.Analysis.OperatorIdeal.Family.TraceClass.Trace

/-!
# The conditional trace relative to a symmetry

Let `F` be a bounded operator on a Hilbert space `E`, typically a symmetry: `F² = 1`. The
**conditional trace** of a bounded operator `T` relative to `F` is

`Tr′ T = ½ Tr (F (F T + T F))`,

defined when the anticommutator `F T + T F` is trace class. The operators with this property form
a submodule, the domain of `Tr′`, which contains the trace class and every operator anticommuting
with `F`, and the conditional trace is linear on it. When `F² = 1` it extends the trace,
`Tr′ T = Tr T` for trace-class `T`, but its domain is much larger: an operator `T` with
`F T = -T F` has `Tr′ T = 0`, although it need not even be compact.

The conditional trace is the integral of the cycle defining the Chern character of a finitely
summable Fredholm module `(H, F, π)` with `F² = 1`. Its character is the cyclic cocycle
`τₙ(a₀, …, aₙ) = Tr′ (π(a₀) [F, π(a₁)] ⋯ [F, π(aₙ)])`, with the grading inserted before `π(a₀)`
in the even case. The operator inside `Tr′` need not be trace class, because the product of `n`
commutators in the Schatten class `Sₙ₊₁` is not, but its anticommutator with `F` is a product
of `n + 1` of them. The identities proved here are those that this cycle uses:

* the commutator `[F, X] = F X - X F` of `F` with any bounded `X` lies in the domain and has
  conditional trace zero (`ContinuousLinearMap.conditionalTrace_mul_sub_mul`). In the even case,
  for a grading `γ` anticommuting with `F`, the same holds for `γ (F X + X F)`
  (`ContinuousLinearMap.conditionalTrace_mul_mul_add_mul`). These are the closedness of the cycle;
* for `η` anticommuting with `F`, such as a product of an odd number of commutators `[F, π(aᵢ)]`
  when `F² = 1`, the anticommutator of `X η` with `F` is `[F, X] η`, so
  `Tr′ (X η) = ½ Tr (F [F, X] η)` (`ContinuousLinearMap.conditionalTrace_mul_of_anticommute`).

## Main definitions

* `ContinuousLinearMap.conditionalTraceDomain F`: the submodule of operators `T` with `F T + T F`
  trace class.
* `ContinuousLinearMap.conditionalTrace F T`: the conditional trace `½ Tr (F (F T + T F))`.

## Main results

* `ContinuousLinearMap.conditionalTrace_eq_trace`: if `F² = 1`, the conditional trace of a
  trace-class operator is its trace.
* `ContinuousLinearMap.conditionalTrace_add`, `ContinuousLinearMap.conditionalTrace_smul`:
  linearity on the domain.
* `ContinuousLinearMap.conditionalTrace_eq_zero_of_anticommute`: an operator anticommuting with
  `F` has conditional trace zero.
* `ContinuousLinearMap.conditionalTrace_mul_sub_mul`,
  `ContinuousLinearMap.conditionalTrace_mul_mul_add_mul`,
  `ContinuousLinearMap.conditionalTrace_mul_of_anticommute`: the commutator identities above.
* `ContinuousLinearMap.enorm_conditionalTrace_le`: `|Tr′ T| ≤ ½ ‖F‖ ‖F T + T F‖₁`.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §1, p. 299.
* A. Connes, *Non-commutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part I, §1.
-/

public section

open TauCeti TauCeti.OperatorIdealFamily
open scoped ENNReal

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-! ### The domain and the definition -/

/-- The **domain of the conditional trace** relative to `F`: the submodule of operators `T` whose
anticommutator `F T + T F` with `F` is trace class. -/
noncomputable def conditionalTraceDomain (F : E →L[𝕜] E) : Submodule 𝕜 (E →L[𝕜] E) :=
  ((traceClass 𝕜).operatorGauge E E).finiteSubmodule.comap
    (LinearMap.mulLeft 𝕜 F + LinearMap.mulRight 𝕜 F)

/-- An operator lies in the domain of the conditional trace relative to `F` exactly when its
anticommutator `F T + T F` with `F` is trace class. -/
@[simp]
theorem mem_conditionalTraceDomain {F T : E →L[𝕜] E} :
    T ∈ F.conditionalTraceDomain ↔
      F * T + T * F ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule := by
  rw [conditionalTraceDomain, Submodule.mem_comap, LinearMap.add_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply]

/-- The **conditional trace** `Tr′ T = ½ Tr (F (F T + T F))` of a bounded operator `T` relative to
`F`. It is meaningful for `T` in `F.conditionalTraceDomain`, where `F T + T F` is trace class; when
`F² = 1` it takes the junk value `0` outside this domain
(`ContinuousLinearMap.conditionalTrace_of_notMem`). -/
noncomputable def conditionalTrace (F T : E →L[𝕜] E) : 𝕜 :=
  2⁻¹ * (F * (F * T + T * F)).trace

/-- The conditional trace relative to `F` is `½ Tr (F (F T + T F))`. -/
theorem conditionalTrace_def (F T : E →L[𝕜] E) :
    F.conditionalTrace T = 2⁻¹ * (F * (F * T + T * F)).trace :=
  (rfl)

variable {F S T : E →L[𝕜] E}

/-- **The junk value.** If `F² = 1`, the conditional trace vanishes outside its domain. -/
theorem conditionalTrace_of_notMem (hF : F * F = 1) (hT : T ∉ F.conditionalTraceDomain) :
    F.conditionalTrace T = 0 := by
  refine (conditionalTrace_def F T).trans ?_
  rw [trace_of_notMem, mul_zero]
  -- `F T + T F = F (F (F T + T F))` would be trace class.
  refine fun h ↦ hT (mem_conditionalTraceDomain.2 ?_)
  simpa only [← mul_def, ← mul_assoc, hF, one_mul] using comp_left_mem_finiteSubmodule F h

/-! ### The conditional trace extends the trace -/

/-- Every trace-class operator lies in the domain of the conditional trace. -/
theorem finiteSubmodule_traceClass_le_conditionalTraceDomain (F : E →L[𝕜] E) :
    ((traceClass 𝕜).operatorGauge E E).finiteSubmodule ≤ F.conditionalTraceDomain :=
  fun T hT ↦ mem_conditionalTraceDomain.2 <| by
    simpa only [← mul_def] using
      add_mem (comp_left_mem_finiteSubmodule F hT) (comp_right_mem_finiteSubmodule hT F)

/-- **The conditional trace extends the trace.** If `F² = 1`, the conditional trace of a
trace-class operator is its trace. -/
theorem conditionalTrace_eq_trace (hF : F * F = 1)
    (hT : T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule) :
    F.conditionalTrace T = T.trace := by
  have hFT : F * T ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule := by
    simpa only [← mul_def] using comp_left_mem_finiteSubmodule F hT
  have hFTF : F * T * F ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule := by
    simpa only [← mul_def] using comp_right_mem_finiteSubmodule hFT F
  -- `Tr ((F T) F) = Tr (F (F T)) = Tr T`, by the trace property.
  have hcomm : (F * T * F).trace = T.trace := by
    rw [mul_def (F * T), ← trace_comp_comm F hFT, ← mul_def, ← mul_assoc, hF, one_mul]
  rw [conditionalTrace_def, mul_add, ← mul_assoc, hF, one_mul, ← mul_assoc,
    trace_add hT hFTF, hcomm]
  ring

/-! ### Linearity on the domain -/

/-- For `T` in the domain, `F (F T + T F)` is trace class. -/
private theorem mul_anticommutator_mem_traceClass (hT : T ∈ F.conditionalTraceDomain) :
    F * (F * T + T * F) ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule := by
  simpa only [← mul_def] using comp_left_mem_finiteSubmodule F (mem_conditionalTraceDomain.1 hT)

/-- The conditional trace is additive on its domain. -/
theorem conditionalTrace_add (hS : S ∈ F.conditionalTraceDomain)
    (hT : T ∈ F.conditionalTraceDomain) :
    F.conditionalTrace (S + T) = F.conditionalTrace S + F.conditionalTrace T := by
  have h : F * (F * (S + T) + (S + T) * F) = F * (F * S + S * F) + F * (F * T + T * F) := by
    noncomm_ring
  rw [conditionalTrace_def, h, trace_add (mul_anticommutator_mem_traceClass hS)
    (mul_anticommutator_mem_traceClass hT), mul_add, ← conditionalTrace_def,
    ← conditionalTrace_def]

/-- The conditional trace of the zero operator is zero. -/
@[simp]
theorem conditionalTrace_zero : F.conditionalTrace 0 = 0 := by
  simp [conditionalTrace_def]

/-- The conditional trace is homogeneous. Outside the domain both sides are junk values of the
same kind, so no hypothesis is needed. -/
@[simp]
theorem conditionalTrace_smul (c : 𝕜) (T : E →L[𝕜] E) :
    F.conditionalTrace (c • T) = c * F.conditionalTrace T := by
  have h : F * (F * (c • T) + c • T * F) = c • (F * (F * T + T * F)) := by
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, mul_smul_comm]
  rw [conditionalTrace_def, conditionalTrace_def, h, trace_smul, mul_left_comm]

/-- The conditional trace commutes with negation. -/
@[simp]
theorem conditionalTrace_neg (T : E →L[𝕜] E) :
    F.conditionalTrace (-T) = -F.conditionalTrace T := by
  simpa using conditionalTrace_smul (F := F) (-1 : 𝕜) T

/-- The conditional trace of a difference of operators in the domain is the difference of their
conditional traces. -/
theorem conditionalTrace_sub (hS : S ∈ F.conditionalTraceDomain)
    (hT : T ∈ F.conditionalTraceDomain) :
    F.conditionalTrace (S - T) = F.conditionalTrace S - F.conditionalTrace T := by
  rw [sub_eq_add_neg, conditionalTrace_add hS (neg_mem hT), conditionalTrace_neg, sub_eq_add_neg]

/-! ### Commutator identities -/

/-- An operator anticommuting with `F` lies in the domain of the conditional trace: its
anticommutator with `F` vanishes. -/
theorem mem_conditionalTraceDomain_of_anticommute (h : F * T = -(T * F)) :
    T ∈ F.conditionalTraceDomain := by
  rw [mem_conditionalTraceDomain, h, neg_add_cancel]
  exact zero_mem _

/-- **Operators anticommuting with `F` have conditional trace zero**, whether or not they are
trace class. -/
theorem conditionalTrace_eq_zero_of_anticommute (h : F * T = -(T * F)) :
    F.conditionalTrace T = 0 := by
  rw [conditionalTrace_def, h, neg_add_cancel, mul_zero, trace_zero, mul_zero]

/-- If `F² = 1`, the commutator `[F, X] = F X - X F` with any bounded operator `X` lies in the
domain of the conditional trace. -/
theorem mul_sub_mul_mem_conditionalTraceDomain (hF : F * F = 1) (X : E →L[𝕜] E) :
    F * X - X * F ∈ F.conditionalTraceDomain :=
  mem_conditionalTraceDomain_of_anticommute (mul_mul_sub_mul_eq_neg_of_mul_self_eq_one hF X)

/-- **The conditional trace kills commutators with `F`.** If `F² = 1`, the commutator
`[F, X] = F X - X F` with any bounded operator `X` has conditional trace zero. -/
theorem conditionalTrace_mul_sub_mul (hF : F * F = 1) (X : E →L[𝕜] E) :
    F.conditionalTrace (F * X - X * F) = 0 :=
  conditionalTrace_eq_zero_of_anticommute (mul_mul_sub_mul_eq_neg_of_mul_self_eq_one hF X)

/-- If `F² = 1` and the grading `γ` anticommutes with `F`, then `γ (F X + X F)` lies in the domain
of the conditional trace for every bounded operator `X`. -/
theorem mul_mul_add_mul_mem_conditionalTraceDomain (hF : F * F = 1) {γ : E →L[𝕜] E}
    (hγ : γ * F = -(F * γ)) (X : E →L[𝕜] E) :
    γ * (F * X + X * F) ∈ F.conditionalTraceDomain := by
  rw [mul_mul_add_mul_eq_neg_of_mul_eq_neg_mul hγ]
  exact neg_mem (mul_sub_mul_mem_conditionalTraceDomain hF _)

/-- **The graded conditional trace kills graded commutators with `F`.** If `F² = 1` and the
grading `γ` anticommutes with `F`, then `Tr′ (γ (F X + X F)) = 0` for every bounded operator
`X`. -/
theorem conditionalTrace_mul_mul_add_mul (hF : F * F = 1) {γ : E →L[𝕜] E}
    (hγ : γ * F = -(F * γ)) (X : E →L[𝕜] E) :
    F.conditionalTrace (γ * (F * X + X * F)) = 0 := by
  rw [mul_mul_add_mul_eq_neg_of_mul_eq_neg_mul hγ, conditionalTrace_neg,
    conditionalTrace_mul_sub_mul hF, neg_zero]

/-- If `η` anticommutes with `F`, then `X η` lies in the domain of the conditional trace exactly
when `[F, X] η` is trace class. -/
theorem mul_mem_conditionalTraceDomain_iff_of_anticommute {η : E →L[𝕜] E}
    (hη : F * η = -(η * F)) (X : E →L[𝕜] E) :
    X * η ∈ F.conditionalTraceDomain ↔
      (F * X - X * F) * η ∈ ((traceClass 𝕜).operatorGauge E E).finiteSubmodule := by
  rw [mem_conditionalTraceDomain, mul_mul_add_mul_mul_eq_of_mul_eq_neg_mul hη]

/-- **The conditional trace of a product with an anticommuting factor.** If `η` anticommutes with
`F`, then `Tr′ (X η) = ½ Tr (F [F, X] η)` for every bounded operator `X`. -/
theorem conditionalTrace_mul_of_anticommute {η : E →L[𝕜] E} (hη : F * η = -(η * F))
    (X : E →L[𝕜] E) :
    F.conditionalTrace (X * η) = 2⁻¹ * (F * ((F * X - X * F) * η)).trace := by
  rw [conditionalTrace_def, mul_mul_add_mul_mul_eq_of_mul_eq_neg_mul hη]

/-! ### The trace-norm bound -/

/-- **The conditional trace is bounded by the trace norm of the anticommutator**:
`|Tr′ T| ≤ ½ ‖F‖ ‖F T + T F‖₁`. Outside the domain the right-hand side is infinite. -/
theorem enorm_conditionalTrace_le (F T : E →L[𝕜] E) :
    ‖F.conditionalTrace T‖ₑ ≤ 2⁻¹ * ‖F‖ₑ * (F * T + T * F).nuclearENorm := by
  have h2 : ‖(2⁻¹ : 𝕜)‖ₑ = 2⁻¹ := by
    rw [eNorm_inv two_ne_zero, ← ofReal_norm, RCLike.norm_ofNat, ENNReal.ofReal_ofNat]
  have hF := (traceClass 𝕜).gauge_comp_left_le F (F * T + T * F)
  rw [gauge_traceClass, gauge_traceClass, ← mul_def] at hF
  rw [conditionalTrace_def, eNorm_mul, h2, mul_assoc]
  gcongr
  exact (enorm_trace_le _).trans hF

end ContinuousLinearMap
