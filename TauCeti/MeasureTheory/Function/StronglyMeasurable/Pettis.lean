/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Caratheodory

/-!
# Weakly measurable functions into a separable Hilbert space

A function `h : α → E` into an inner product space is *weakly measurable* when every scalar
function `t ↦ ⟪v, h t⟫` is measurable. **Pettis' measurability theorem** says that a weakly
measurable function with essentially separable range is strongly measurable. This file proves the
case of a separable inner product space `E`, with almost everywhere strong measurability on both
sides:

* `TauCeti.aestronglyMeasurable_iff_forall_inner`: `h : α → E` is almost everywhere strongly
  measurable exactly when each `t ↦ ⟪v, h t⟫` is;
* `TauCeti.aestronglyMeasurable_strongDual_iff_forall_apply`: for `E` also complete, a function
  `g : α → StrongDual 𝕜 E` is almost everywhere strongly measurable in the operator norm exactly
  when each `t ↦ g t v` is;
* `MeasureTheory.MemLp.clm_apply_of_forall_aestronglyMeasurable`: if `A t : F →L[𝕜] E*` is
  essentially bounded and weakly measurable, `t ↦ A t x y` measurable for all `x, y`, then
  `t ↦ A t (u t)` lies in `Lᵖ(E*)` for every `u ∈ Lᵖ(F)`.

The last statement is what evolution equations need. A time-dependent operator
`A(t) : V →L[ℝ] V*` with merely measurable coefficients is in general only weakly measurable,
and not measurable for the operator norm, but for a separable Hilbert space `V`, such as
`H¹₀(Ω)`, and `u ∈ L²(0, T; V)`, the function `t ↦ A(t) u(t)` is a genuine element of
`L²(0, T; V*)`.

## Proof

Let `U n` be the span of the first `n + 1` terms of a dense sequence in `E`. The orthogonal
projection onto `U n` is a finite sum `∑ i, ⟪b i, x⟫ • b i` over an orthonormal basis `b` of
`U n`, so `t ↦ P_{U n} (h t)` is almost everywhere strongly measurable, and it converges to `h t`
because the `U n` increase to a dense subspace (`Submodule.starProjection_tendsto_self`). The dual
statement follows through the Riesz isometry `InnerProductSpace.toDual`.

## References

* B. J. Pettis, *On integration in vector spaces*, Trans. Amer. Math. Soc. **44** (1938),
  277–304.
* J. Diestel, J. J. Uhl, *Vector Measures*, Mathematical Surveys **15**, AMS, 1977, Chapter II,
  §1, Theorem 2.
-/

public section

open MeasureTheory Filter Set Submodule TopologicalSpace
open scoped InnerProductSpace ENNReal

namespace TauCeti

variable {α 𝕜 E : Type*} {_ : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [SeparableSpace E]

/-- **Pettis' theorem in a separable inner product space.** A function into a separable inner
product space is almost everywhere strongly measurable exactly when it is weakly measurable, that
is, when each of its coordinates `t ↦ ⟪v, h t⟫` is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_iff_forall_inner {h : α → E} :
    AEStronglyMeasurable h μ ↔ ∀ v, AEStronglyMeasurable (fun t ↦ ⟪v, h t⟫_𝕜) μ := by
  refine ⟨fun hh v ↦ hh.const_inner, fun hh ↦ ?_⟩
  obtain ⟨d, hd⟩ := exists_dense_seq E
  -- The spans `U n` of the initial segments of `d` increase to a dense subspace.
  set U : ℕ → Submodule 𝕜 E := fun n ↦ span 𝕜 (d '' Iic n) with hU_def
  have hU : Monotone U := fun _ _ hmn ↦ span_mono (image_mono (Iic_subset_Iic.2 hmn))
  have : ∀ n, FiniteDimensional 𝕜 (U n) := fun n ↦
    FiniteDimensional.span_of_finite 𝕜 ((finite_Iic n).image d)
  have hdense : ⊤ ≤ (⨆ n, U n).topologicalClosure := by
    intro x _
    rw [← SetLike.mem_coe, topologicalClosure_coe]
    refine closure_mono ?_ (hd x)
    rintro _ ⟨n, rfl⟩
    exact mem_iSup_of_mem n (subset_span ⟨n, self_mem_Iic, rfl⟩)
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦ ?_)
    (ae_of_all _ fun t ↦ starProjection_tendsto_self U hU (h t) hdense)
  -- Each projection is a finite sum of coordinates against an orthonormal basis of `U n`.
  set b := stdOrthonormalBasis 𝕜 (U n)
  have hsum : (fun t ↦ (U n).starProjection (h t)) =
      fun t ↦ ∑ i, ⟪(b i : E), h t⟫_𝕜 • (b i : E) := by
    funext t
    rw [starProjection_apply, b.orthogonalProjectionOnto_apply_eq_sum, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  rw [hsum]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦ (hh _).smul_const _

/-- **Pettis' theorem for the dual of a separable Hilbert space.** A function into the dual of a
separable Hilbert space is almost everywhere strongly measurable in the operator norm exactly when
each of its evaluations `t ↦ g t v` is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_strongDual_iff_forall_apply [CompleteSpace E]
    {g : α → StrongDual 𝕜 E} :
    AEStronglyMeasurable g μ ↔ ∀ v, AEStronglyMeasurable (fun t ↦ g t v) μ := by
  refine ⟨fun hg v ↦ hg.apply_continuousLinearMap v, fun hg ↦ ?_⟩
  -- Pass to the Riesz representatives, whose coordinates are conjugates of the evaluations.
  have hR : AEStronglyMeasurable (fun t ↦ (InnerProductSpace.toDual 𝕜 E).symm (g t)) μ := by
    refine (aestronglyMeasurable_iff_forall_inner (𝕜 := 𝕜)).2 fun v ↦ ?_
    refine (RCLike.continuous_conj.comp_aestronglyMeasurable (hg v)).congr (ae_of_all _ ?_)
    intro t
    simp only [← InnerProductSpace.toDual_symm_apply, inner_conj_symm]
  refine ((InnerProductSpace.toDual 𝕜 E).continuous.comp_aestronglyMeasurable hR).congr
    (ae_of_all _ fun t ↦ ?_)
  simp only [LinearIsometryEquiv.apply_symm_apply]

end TauCeti

namespace MeasureTheory

variable {α 𝕜 E F : Type*} {_ : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [SeparableSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Weakly measurable operator families act on `Lᵖ`.** Let `E` be a separable Hilbert space and
let `A t : F →L[𝕜] E*` be essentially bounded by `Λ` and weakly measurable: `t ↦ A t x y` is
almost everywhere strongly measurable for all `x, y`. Then `t ↦ A t (u t)` lies in `Lᵖ(E*)` for
every `u ∈ Lᵖ(F)`. -/
theorem MemLp.clm_apply_of_forall_aestronglyMeasurable {p : ℝ≥0∞} {u : α → F}
    {A : α → F →L[𝕜] StrongDual 𝕜 E} {Λ : ℝ} (hu : MemLp u p μ)
    (hA : ∀ x y, AEStronglyMeasurable (fun t ↦ A t x y) μ) (hA_bound : ∀ᵐ t ∂μ, ‖A t‖ ≤ Λ) :
    MemLp (fun t ↦ A t (u t)) p μ := by
  refine hu.of_le_mul (c := Λ) (TauCeti.aestronglyMeasurable_strongDual_iff_forall_apply.2
    fun y ↦ hu.aestronglyMeasurable.apply_of_forall_of_continuous (g := fun t x ↦ A t x y)
      (fun x ↦ hA x y) fun t ↦ ((ContinuousLinearMap.apply 𝕜 𝕜 y).comp (A t)).continuous) ?_
  filter_upwards [hA_bound] with t ht
  exact (A t).le_of_opNorm_le ht (u t)

end MeasureTheory
