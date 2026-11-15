/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.UniformConvex
import TauCeti.Analysis.Normed.Module.Annihilator

/-!
# Representation of continuous functionals on `Lᵖ`

On a σ-finite measure space, the integral pairing identifies the continuous dual of `Lᵠ`
with `Lᵖ` for conjugate exponents `1 < p, q < ∞`. The isometric embedding is supplied by
`MeasureTheory.Lp.toDual`. Surjectivity follows from reflexivity of `Lᵠ`: a functional
annihilating the closed range is evaluation at an `Lᵠ` function, which must vanish by the
injectivity of the reversed integral pairing.

This representation passes distributional test-function bounds to actual `Lᵖ` weak derivatives.

## References

* G. B. Folland, *Real Analysis*, second edition, Theorem 6.16.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α 𝕜 : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {μ : Measure α}
  [SigmaFinite μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Every continuous scalar functional on `Lᵠ` is integration against an `Lᵖ` function,
for conjugate exponents strictly between one and infinity. -/
theorem toDual_surjective (hq : 1 < q) (hq_top : q ≠ ∞) :
    Function.Surjective (toDual 𝕜 μ p q) := by
  let S := (toDual 𝕜 μ p q).toLinearMap.range
  have hS : IsClosed (S : Set (StrongDual 𝕜 (Lp 𝕜 q μ))) :=
    (toDual 𝕜 μ p q).isometry.isClosedEmbedding.isClosed_range
  intro Λ
  suffices Λ ∈ S.topologicalClosure by
    rw [hS.submodule_topologicalClosure_eq] at this
    exact this
  apply (S.mem_topologicalClosure_iff_forall_dual_eq_zero Λ).2
  intro Ψ hΨ
  obtain ⟨f, rfl⟩ := surjective_inclusionInDoubleDual (𝕜 := 𝕜) (E := 𝕜) hq hq_top Ψ
  have hf : f = 0 := by
    apply (toDual 𝕜 μ q p).injective
    apply ContinuousLinearMap.ext
    intro g
    have hzero := hΨ (toDual 𝕜 μ p q g)
      (LinearMap.mem_range_self (toDual 𝕜 μ p q).toLinearMap g)
    rw [NormedSpace.dual_def, toDual_apply] at hzero
    rw [map_zero, zero_apply, toDual_apply]
    simpa only [mul_comm] using hzero
  simp [hf]

variable (𝕜 μ p q) in
/-- The norm-preserving integral representation of the continuous dual of `Lᵠ` by `Lᵖ`. -/
noncomputable def dualEquiv (hq : 1 < q) (hq_top : q ≠ ∞) :
    Lp 𝕜 p μ ≃ₗᵢ[𝕜] StrongDual 𝕜 (Lp 𝕜 q μ) :=
  LinearIsometryEquiv.ofSurjective (toDual 𝕜 μ p q) (toDual_surjective hq hq_top)

/-- Evaluation of the integral representation equivalence. -/
theorem dualEquiv_apply (hq : 1 < q) (hq_top : q ≠ ∞) (g : Lp 𝕜 p μ) (f : Lp 𝕜 q μ) :
    dualEquiv 𝕜 μ p q hq hq_top g f = ∫ x, g x * f x ∂μ :=
  toDual_apply g f

@[simp]
theorem coe_dualEquiv (hq : 1 < q) (hq_top : q ≠ ∞) :
    ⇑(dualEquiv 𝕜 μ p q hq hq_top) = toDual 𝕜 μ p q := by
  funext g
  ext f
  exact (dualEquiv_apply hq hq_top g f).trans (toDual_apply g f).symm

/-- The representing density of a functional integrates to its value on every `Lᵠ` function. -/
@[simp]
theorem integral_dualEquiv_symm_mul (hq : 1 < q) (hq_top : q ≠ ∞)
    (Λ : StrongDual 𝕜 (Lp 𝕜 q μ)) (f : Lp 𝕜 q μ) :
    ∫ x, (dualEquiv 𝕜 μ p q hq hq_top).symm Λ x * f x ∂μ = Λ f := by
  rw [← dualEquiv_apply hq hq_top, LinearIsometryEquiv.apply_symm_apply]

end MeasureTheory.Lp
