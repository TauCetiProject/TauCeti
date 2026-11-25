/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.IdealExtension
public import TauCeti.Analysis.CStarAlgebra.State.AmenableTrace
public import TauCeti.Analysis.CStarAlgebra.Matrix.VectorState

/-!
# Checks for the extension of tracial states from closed ideals

For the closed ideal `I = M₂ ⊕ 0` of `A = M₂ ⊕ ℂ` (the kernel of the second projection) and the
tracial state `τ = tr₂` of `I`:

* `τ` is a tracial state of `I` (`isTracialState_trace`), and the tracial state
  `γ(x, λ) = tr₂(x)` of `A` (`isTracialState_traceFst`) restricts to it;
* `γ` is the only extension: every positive functional of norm at most one on `A` restricting to
  `τ` is `γ` (`eq_traceFst_of_apply_coe_eq`), and `γ` vanishes at `(0, 1)`
  (`traceFst_zero_one`);
* the unit `e = (1, 0)` of `I` is an increasing approximate unit of `I`
  (`isIncreasingApproximateUnit_pure_unit`), and the extension formula reads
  `γ(x, λ) = τ(e (x, λ) e) = tr₂(x)` (`trace_unit_mul_mul_unit`, `tendsto_trace_unit_mul_mul_unit`).

The traciality of `τ` is what makes the extension tracial: for `I = A = M₂` the state
`ω(x) = x₁₁`, the vector state of the first basis vector, is its own extension, and the step
`ω((ea)(be)) = ω((be)(ea))` with `e = 1`, `a = e₁₂`, `b = e₂₁` would read `1 = 0`
(`vectorFunctional_single_mul_ne`).
-/

public section

open Filter Topology PositiveContinuousLinearMap CStarMatrix
open scoped ComplexOrder

namespace TauCeti.IdealExtensionExample

/-- The `2 × 2` complex matrices. -/
abbrev M₂ : Type := CStarMatrix (Fin 2) (Fin 2) ℂ

/-- The C⋆-algebra `A = M₂ ⊕ ℂ`. -/
abbrev A : Type := M₂ × ℂ

/-- The closed ideal `I = M₂ ⊕ 0` of `A`, the kernel of the second projection. -/
def I : TwoSidedIdeal A :=
  TwoSidedIdeal.ker (NonUnitalStarAlgHom.snd ℂ M₂ ℂ)

/-- `(x, λ) ∈ I` exactly when `λ = 0`. -/
theorem mem_I_iff (a : A) : a ∈ I ↔ a.2 = 0 :=
  TwoSidedIdeal.mem_ker _

/-- `I = M₂ ⊕ 0` is closed. -/
instance isClosed_I : IsClosed (I : Set A) :=
  TwoSidedIdeal.isClosed_ker continuous_snd

/-- The tracial state `γ(x, λ) = tr₂(x)` of `A`. -/
noncomputable def traceFst : A →P[ℂ] ℂ :=
  (normalizedTraceMap (Fin 2)).comp (.ofClass (NonUnitalStarAlgHom.fst ℂ M₂ ℂ))

@[simp]
theorem traceFst_apply (a : A) : traceFst a = normalizedTrace a.1 := by
  simp [traceFst]

/-- The tracial state `τ = tr₂` of `I = M₂ ⊕ 0`. -/
noncomputable def trace : I →P[ℂ] ℂ :=
  traceFst.comp (.ofClass I.starAlgHom)

@[simp]
theorem trace_apply (c : I) : trace c = normalizedTrace (c : A).1 := by
  simp [trace]

/-- `γ` restricts to `τ` on `I`. -/
theorem traceFst_apply_coe (c : I) : traceFst c = trace c := by
  simp

/-- `γ(x, λ) = tr₂(x)` is a tracial state of `A`. -/
theorem isTracialState_traceFst : traceFst.IsTracialState :=
  isTracialState_normalizedTraceMap.comp_of_surjective (NonUnitalStarAlgHom.fst ℂ M₂ ℂ)
    Prod.fst_surjective

/-- **`γ` vanishes at `(0, 1)`.** -/
theorem traceFst_zero_one : traceFst ((0, 1) : A) = 0 := by
  simp [normalizedTrace_def]

/-- The unit `e = (1, 0)` of `I`. -/
def unit : I :=
  ⟨(1, 0), (mem_I_iff _).mpr rfl⟩

/-- `e` is a left unit of `I`. -/
theorem unit_mul (c : I) : unit * c = c := by
  obtain ⟨⟨x, y⟩, hc⟩ := c
  have hy : y = 0 := (mem_I_iff _).mp hc
  subst hy
  exact Subtype.ext (Prod.ext (one_mul x) (zero_mul 0))

/-- `e` is a right unit of `I`. -/
theorem mul_unit (c : I) : c * unit = c := by
  obtain ⟨⟨x, y⟩, hc⟩ := c
  have hy : y = 0 := (mem_I_iff _).mp hc
  subst hy
  exact Subtype.ext (Prod.ext (mul_one x) (mul_zero 0))

/-- `τ(e) = 1`. -/
theorem trace_unit : trace unit = 1 := by
  simp [unit, normalizedTrace_one]

/-- `‖e‖ = 1`. -/
theorem norm_unit : ‖unit‖ = 1 := by
  rw [AddSubgroupClass.coe_norm]
  simp [unit, Prod.norm_def]

/-- **`τ = tr₂` is a tracial state of `I`.** -/
theorem isTracialState_trace : IsTracialState (A := I) trace := by
  refine isTracialState_traceFst.comp_of_norm_eq_one I.starAlgHom (le_antisymm ?_ ?_)
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ ?_
    calc ‖trace c‖ = ‖traceFst (c : A)‖ := by rw [traceFst_apply_coe]
      _ ≤ 1 * ‖(c : A)‖ := by
        simpa [isTracialState_traceFst.norm_eq_one] using
          (traceFst : A →L[ℂ] ℂ).le_opNorm (c : A)
      _ = 1 * ‖c‖ := by rw [AddSubgroupClass.coe_norm]
  · have h := (trace : I →L[ℂ] ℂ).le_opNorm unit
    rw [norm_unit, mul_one] at h
    have h1 : (trace : I →L[ℂ] ℂ) unit = 1 := by simpa using trace_unit
    rwa [h1, norm_one] at h

/-- **Uniqueness of the extension.** Every positive functional of norm at most one on `A` that
restricts to `τ` on `I` is `γ(x, λ) = tr₂(x)`. -/
theorem eq_traceFst_of_apply_coe_eq {γ : A →P[ℂ] ℂ} (hγ : ‖(γ : A →L[ℂ] ℂ)‖ ≤ 1)
    (h : ∀ c : I, γ c = trace c) : γ = traceFst :=
  eq_of_apply_coe_eq (hγ.trans isTracialState_trace.norm_eq_one.ge)
    (isTracialState_traceFst.norm_eq_one.trans isTracialState_trace.norm_eq_one.symm).le
    h traceFst_apply_coe

/-- `τ` has a unique tracial extension to `A`, by
`PositiveContinuousLinearMap.IsTracialState.existsUnique_isTracialState_apply_coe_eq`; it is `γ`
by `eq_traceFst_of_apply_coe_eq`. -/
theorem existsUnique_isTracialState_apply_coe_eq :
    ∃! γ : A →P[ℂ] ℂ, γ.IsTracialState ∧ ∀ c : I, γ c = trace c :=
  isTracialState_trace.existsUnique_isTracialState_apply_coe_eq

/-- **The unit of `I` is an increasing approximate unit** of `I`, as the constant filter. -/
theorem isIncreasingApproximateUnit_pure_unit : (pure unit : Filter I).IsIncreasingApproximateUnit
    where
  tendsto_mul_left c := by simpa [mul_unit] using tendsto_pure_nhds (c * ·) unit
  tendsto_mul_right c := by simpa [unit_mul] using tendsto_pure_nhds (· * c) unit
  eventually_nonneg := by
    refine Filter.eventually_pure.mpr (Subtype.coe_le_coe.mp ?_)
    exact Prod.mk_le_mk.mpr ⟨zero_le_one, le_rfl⟩
  eventually_norm := Filter.eventually_pure.mpr norm_unit.le

/-- **The extension formula.** `τ(e (x, λ) e) = tr₂(x) = γ(x, λ)`. -/
theorem trace_unit_mul_mul_unit (a : A) :
    trace ⟨(unit : A) * a * unit, I.mul_mem_left _ _ unit.property⟩ = traceFst a := by
  simp [unit]

/-- The extension formula along the approximate unit `pure e`, from the general
`PositiveContinuousLinearMap.tendsto_apply_mul_mul_of_apply_coe_eq'`. -/
theorem tendsto_trace_unit_mul_mul_unit (a : A) :
    Tendsto (fun e : I ↦ trace ⟨(e : A) * a * e, I.mul_mem_left _ _ e.property⟩) (pure unit)
      (𝓝 (traceFst a)) :=
  tendsto_apply_mul_mul_of_apply_coe_eq'
    (isTracialState_traceFst.norm_eq_one.trans isTracialState_trace.norm_eq_one.symm).le
    traceFst_apply_coe isIncreasingApproximateUnit_pure_unit a

/-- The matrix unit `e₁₂`. -/
abbrev e₁₂ : M₂ := CStarMatrix.ofMatrix (Matrix.single 0 1 1)

/-- The matrix unit `e₂₁`. -/
abbrev e₂₁ : M₂ := CStarMatrix.ofMatrix (Matrix.single 1 0 1)

/-- **Traciality of `τ` cannot be dropped.** The vector state `ω(x) = x₁₁` of `M₂` takes the value
`1` at `e₁₂ e₂₁` and `0` at `e₂₁ e₁₂`. -/
theorem vectorFunctional_single_mul_ne :
    vectorFunctional (Pi.single 0 1) (e₁₂ * e₂₁) ≠ vectorFunctional (Pi.single 0 1) (e₂₁ * e₁₂) :=
  by
  rw [vectorFunctional_single, vectorFunctional_single]
  simp [e₁₂, e₂₁, CStarMatrix.mul_apply, Matrix.single_apply]

end TauCeti.IdealExtensionExample
