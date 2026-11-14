/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Convex
import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous

/-!
# Bounded continuous representatives of whole-space `W^{1,∞}` functions

The precise representative of a whole-space `W^{1,∞}` class is bounded and Lipschitz.
`W1p.boundedContinuousRepresentativeL` packages it as a continuous linear map into bounded
continuous functions. Its supremum norm equals the essential supremum norm of the value
component, and it is Lipschitz with constant at most the essential supremum norm of the weak
gradient.
This permits restriction to boundary sets after extending a Sobolev function to the whole space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace TauCeti.W1p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

local instance : (μ.restrict ((⊤ : Opens E) : Set E)).IsOpenPosMeasure := by
  simpa using (inferInstance : μ.IsOpenPosMeasure)

private def boundedContinuousRepresentative (u : W1p μ (⊤ : Opens E) ∞) : E →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (preciseRepresentative μ (value u)) (lipschitzWith_preciseRepresentative u).continuous
    ‖value u‖ (fun x ↦ norm_preciseRepresentative_le u (mem_univ x))

private theorem toLpTop_boundedContinuousRepresentative (u : W1p μ (⊤ : Opens E) ∞) :
    BoundedContinuousFunction.toLpTop (μ.restrict ((⊤ : Opens E) : Set E)) ℝ
      (boundedContinuousRepresentative u) =
      value u := by
  apply Lp.ext
  exact (BoundedContinuousFunction.coeFn_toLpTop
    (μ.restrict ((⊤ : Opens E) : Set E)) _).trans
    (ae_eq_preciseRepresentative u).symm

/-- The bounded Lipschitz representative of a whole-space `W^{1,∞}` function, as a continuous
linear map. Its norm is controlled by the value component alone. -/
def boundedContinuousRepresentativeL : W1p μ (⊤ : Opens E) ∞ →L[ℝ] (E →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := boundedContinuousRepresentative
      map_add' := fun u v ↦ by
        apply BoundedContinuousFunction.toLpTop_injective
          (μ.restrict ((⊤ : Opens E) : Set E)) (𝕜 := ℝ)
        simp only [map_add, toLpTop_boundedContinuousRepresentative]
        simpa only [valueL_apply] using
          (valueL (mu := μ) (Omega := ⊤) (p := ∞)).map_add u v
      map_smul' := fun c u ↦ by
        apply BoundedContinuousFunction.toLpTop_injective
          (μ.restrict ((⊤ : Opens E) : Set E)) (𝕜 := ℝ)
        simp only [map_smul, toLpTop_boundedContinuousRepresentative]
        simpa only [valueL_apply, RingHom.id_apply] using
          (valueL (mu := μ) (Omega := ⊤) (p := ∞)).map_smul c u }
    1 (fun u ↦ by
      have h : ‖boundedContinuousRepresentative u‖ ≤ ‖u‖ :=
        (BoundedContinuousFunction.norm_le (norm_nonneg u)).2 fun x ↦
          (norm_preciseRepresentative_le u (mem_univ x)).trans (norm_value_le u)
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, one_mul] using h)

/-- Evaluating the bounded continuous representative gives the precise representative. -/
-- Rewrite the representative before simplification of the whole-space open-set coercion.
@[simp↓]
theorem boundedContinuousRepresentativeL_apply (u : W1p μ (⊤ : Opens E) ∞) (x : E) :
    boundedContinuousRepresentativeL u x = preciseRepresentative μ (value u) x := (rfl)

/-- The bounded continuous representative agrees almost everywhere with the original value. -/
theorem value_ae_eq_boundedContinuousRepresentativeL (u : W1p μ (⊤ : Opens E) ∞) :
    value u =ᵐ[μ] boundedContinuousRepresentativeL u := by
  have h : value u =ᵐ[μ] preciseRepresentative μ (value u) := by
    simpa using ae_eq_preciseRepresentative u
  exact h.trans (Filter.Eventually.of_forall fun x ↦
    (boundedContinuousRepresentativeL_apply u x).symm)

/-- The supremum norm of the continuous representative is exactly the essential supremum
norm of the Sobolev value. -/
-- Rewrite the norm before simplification of the whole-space open-set coercion.
@[simp↓]
theorem norm_boundedContinuousRepresentativeL (u : W1p μ (⊤ : Opens E) ∞) :
    ‖boundedContinuousRepresentativeL u‖ = ‖value u‖ := by
  rw [← BoundedContinuousFunction.norm_toLpTop
    (μ.restrict ((⊤ : Opens E) : Set E)) (𝕜 := ℝ)]
  exact congrArg norm (toLpTop_boundedContinuousRepresentative u)

/-- The Lipschitz constant of the representative is bounded by the weak-gradient norm. -/
theorem lipschitzWith_boundedContinuousRepresentativeL (u : W1p μ (⊤ : Opens E) ∞) :
    LipschitzWith ‖gradient u‖₊ (boundedContinuousRepresentativeL u) :=
  lipschitzWith_preciseRepresentative u

end TauCeti.W1p
