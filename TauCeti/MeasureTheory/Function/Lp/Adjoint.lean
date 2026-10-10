/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# `Lᵖ` bounds for an operator on `L²` from bounds for its adjoint

Let `T : L²(μ; E) → L²(ν; F)` be a bounded operator between `L²` spaces of Hilbert space valued
functions, and let `T†` be its Hilbert space adjoint. If `T†` is bounded from `L^{q'}` to
`L^{p'}` on `L²`, that is `‖T† g‖_{p'} ≤ C ‖g‖_{q'}` for every `g ∈ L²`, then `T` is bounded from
`Lᵖ` to `L^q` on `L²` with the same constant, where `p, p'` and `q, q'` are pairs of Hölder
conjugate exponents and `q < ∞`.

This is the duality argument that transfers a bound in one range of exponents to the dual
range: for instance the Calderón–Zygmund bound for `1 < p < 2` gives the bound for `2 < p < ∞`.
Neither `‖T f‖_q` nor `‖f‖_p` is assumed finite, so the theorem in particular shows that `T`
maps `L² ∩ Lᵖ` into `L^q`: the pairing of `T f` is only tested against bounded functions of
finite-measure support (`AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_le`).

## Main declarations

* `ContinuousLinearMap.eLpNorm_le_of_eLpNorm_adjoint_le`: a `L^{q'} → L^{p'}` bound for the
  adjoint gives a `Lᵖ → L^q` bound for the operator.

## References

* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II, §2.4.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3.
-/

public section

open MeasureTheory TauCeti
open scoped ENNReal InnerProductSpace

namespace ContinuousLinearMap

variable {α β 𝕜 E F : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Duality for operators on `L²`.** Let `T : L²(μ; E) → L²(ν; F)` be a bounded operator on a
σ-finite target, let `p, p'` and `q, q'` be Hölder conjugate with `q < ∞`, and suppose the
adjoint satisfies `‖T† g‖_{p'} ≤ C ‖g‖_{q'}` for every `g ∈ L²`. Then
`‖T f‖_q ≤ C ‖f‖_p` for every `f ∈ L²`. -/
theorem eLpNorm_le_of_eLpNorm_adjoint_le [SigmaFinite ν] (T : Lp E 2 μ →L[𝕜] Lp F 2 ν)
    {p p' q q' : ℝ≥0∞} [p.HolderConjugate p'] [q.HolderConjugate q'] (hq : q ≠ ∞) {C : ℝ≥0∞}
    (hT : ∀ g : Lp F 2 ν, eLpNorm (adjoint T g) p' μ ≤ C * eLpNorm g q' ν) (f : Lp E 2 μ) :
    eLpNorm (T f) q ν ≤ C * eLpNorm f p μ := by
  refine (Lp.aestronglyMeasurable (T f)).eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := 𝕜)
    (q' := q') hq fun g s hs hgs hg => ?_
  -- A bounded function of finite-measure support is an element `G` of `L²`.
  have hg2 : MemLp g 2 ν := hg.mono_exponent_of_measure_support_ne_top hgs hs le_top
  set G := hg2.toLp g
  have hGg : (G : β → F) =ᵐ[ν] g := hg2.coeFn_toLp
  have hpair : ∫ x, ⟪T f x, g x⟫_𝕜 ∂ν = ∫ x, ⟪f x, adjoint T G x⟫_𝕜 ∂μ := by
    rw [← L2.inner_def, adjoint_inner_right, L2.inner_def]
    exact integral_congr_ae (hGg.mono fun x hx => by simp only [hx])
  calc ‖∫ x, ⟪T f x, g x⟫_𝕜 ∂ν‖ₑ = ‖∫ x, ⟪f x, adjoint T G x⟫_𝕜 ∂μ‖ₑ := by rw [hpair]
    _ ≤ eLpNorm f p μ * eLpNorm (adjoint T G) p' μ :=
        enorm_integral_inner_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    _ ≤ eLpNorm f p μ * (C * eLpNorm G q' ν) := by gcongr; exact hT G
    _ = C * eLpNorm f p μ * eLpNorm g q' ν := by rw [eLpNorm_congr_ae hGg]; ring

end ContinuousLinearMap
