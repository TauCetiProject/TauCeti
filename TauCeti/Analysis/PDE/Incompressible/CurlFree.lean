/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# Curl-free fields in `L²`

A field `u ∈ L²(μ; E)` is **curl free** when its distributional derivatives are symmetric,
`∂_b ⟪a, u⟫ = ∂_a ⟪b, u⟫` for all directions `a` and `b`; tested against a test function `φ`, this
is `∫ ∂_b φ ⟪a, u⟫ = ∫ ∂_a φ ⟪b, u⟫`. Each such identity is the vanishing of a continuous linear
functional on `L²`, so the curl-free fields form a closed subspace. A square integrable weak
gradient is curl free, by the symmetry of weak second derivatives.

## Main declarations

* `TauCeti.curlFreeLp`: the closed subspace of curl-free fields in `L²(μ; E)`, with
  `TauCeti.mem_curlFreeLp_iff` and `TauCeti.le_curlFreeLp_iff` its membership and inclusion
  criteria.
* `TauCeti.HasWeakFDerivOn.mem_curlFreeLp`: a square integrable weak gradient is curl free.

## References

* G. P. Galdi, *An Introduction to the Mathematical Theory of the Navier–Stokes Equations*,
  2nd ed., Springer, 2011, Section III.1.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace LineDeriv
open scoped ENNReal Distributions RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- The test field `∂_b φ • a - ∂_a φ • b`, whose pairing with a field `u` tests the symmetry
`∂_a u_b = ∂_b u_a` of the derivatives of `u` in distributions. -/
private def curlTestField (φ : 𝓓((⊤ : Opens E), ℝ)) (a b : E) (x : E) : E :=
  (∂_{b} φ) x • a - (∂_{a} φ) x • b

private theorem memLp_curlTestField (φ : 𝓓((⊤ : Opens E), ℝ)) (a b : E) :
    MemLp (curlTestField φ a b) 2 μ :=
  (((∂_{b} φ).continuous.smul continuous_const).sub
    ((∂_{a} φ).continuous.smul continuous_const)).memLp_of_hasCompactSupport
    (((∂_{b} φ).hasCompactSupport.smul_right).sub (∂_{a} φ).hasCompactSupport.smul_right)

/-- The pairing of a square integrable field with a curl test field. -/
private theorem integral_inner_curlTestField {u : E → E} (hu : MemLp u 2 μ)
    (φ : 𝓓((⊤ : Opens E), ℝ)) (a b : E) :
    ∫ x, ⟪curlTestField φ a b x, u x⟫ ∂μ =
      ∫ x, (∂_{b} φ) x * ⟪a, u x⟫ ∂μ - ∫ x, (∂_{a} φ) x * ⟪b, u x⟫ ∂μ := by
  rw [← integral_sub ((∂_{b} φ).integrable_mul_inner_of_memLp hu a)
    ((∂_{a} φ).integrable_mul_inner_of_memLp hu b)]
  simp only [curlTestField, inner_sub_left, real_inner_smul_left]

variable (μ) in
/-- The closed subspace of `L²(μ; E)` of **curl-free fields**: the fields `u` whose
distributional derivatives are symmetric, `∂_b ⟪a, u⟫ = ∂_a ⟪b, u⟫` for all directions `a` and
`b` (see `TauCeti.mem_curlFreeLp_iff`). -/
def curlFreeLp : ClosedSubmodule ℝ (Lp E 2 μ) :=
  ⨅ t : 𝓓((⊤ : Opens E), ℝ) × E × E, (⊥ : ClosedSubmodule ℝ ℝ).comap
    (MemLp.innerLpCLM ℝ (memLp_curlTestField (μ := μ) t.1 t.2.1 t.2.2))

/-- A field is curl free exactly when `∫ ∂_b φ ⟪a, u⟫ = ∫ ∂_a φ ⟪b, u⟫` for every test function
`φ` and all directions `a` and `b`. -/
theorem mem_curlFreeLp_iff {u : Lp E 2 μ} :
    u ∈ curlFreeLp μ ↔ ∀ (φ : 𝓓((⊤ : Opens E), ℝ)) (a b : E),
      ∫ x, (∂_{b} φ) x * ⟪a, u x⟫ ∂μ = ∫ x, (∂_{a} φ) x * ⟪b, u x⟫ ∂μ := by
  simp only [curlFreeLp, ClosedSubmodule.mem_iInf, ClosedSubmodule.mem_comap,
    ClosedSubmodule.mem_bot, MemLp.innerLpCLM_apply, Prod.forall,
    integral_inner_curlTestField (Lp.memLp u), sub_eq_zero]

/-- A subspace of `L²(μ; E)` consists of curl-free fields exactly when each of its elements
satisfies `∫ ∂_b φ ⟪a, u⟫ = ∫ ∂_a φ ⟪b, u⟫` for every test function `φ` and all directions `a`
and `b`. -/
theorem le_curlFreeLp_iff {K : Submodule ℝ (Lp E 2 μ)} :
    K ≤ (curlFreeLp μ).toSubmodule ↔ ∀ u ∈ K, ∀ (φ : 𝓓((⊤ : Opens E), ℝ)) (a b : E),
      ∫ x, (∂_{b} φ) x * ⟪a, u x⟫ ∂μ = ∫ x, (∂_{a} φ) x * ⟪b, u x⟫ ∂μ := by
  simp only [IsConcreteLE.le_iff, ClosedSubmodule.mem_toSubmodule_iff, mem_curlFreeLp_iff]

/-- **A square integrable weak gradient is curl free**, by the symmetry of weak second
derivatives. -/
theorem HasWeakFDerivOn.mem_curlFreeLp {q : E → ℝ} {w : Lp E 2 μ}
    (hq : HasWeakFDerivOn μ ⊤ q fun x ↦ innerSL ℝ (w x)) : w ∈ curlFreeLp μ := by
  refine mem_curlFreeLp_iff.2 fun φ a b ↦ ?_
  have h := (hq.hasWeakLineDerivOn a).integral_inner_lineDeriv_comm (hq.hasWeakLineDerivOn b) φ
  simpa [TestFunction.lineDerivOp_apply, real_inner_comm, mul_comm] using h

end TauCeti
