/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.LipschitzRepresentative
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

/-- The bounded Lipschitz representative of a whole-space `W^{1,∞}` function, as a continuous
linear map. Its norm is controlled by the value component alone. -/
def boundedContinuousRepresentativeL : W1p μ (⊤ : Opens E) ∞ →L[ℝ] (E →ᵇ ℝ) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun x : E ↦ ⟨x, subset_closure (Opens.mem_top x)⟩,
      continuous_id.subtype_mk _⟩).comp
    (HolderSpace.toBoundedContinuousFunctionCLM.comp
      (lipschitzRepresentativeL (by simpa only [Opens.coe_top] using convex_univ)))

/-- Evaluating the bounded continuous representative gives the precise representative. -/
theorem boundedContinuousRepresentativeL_apply (u : W1p μ (⊤ : Opens E) ∞) (x : E) :
    boundedContinuousRepresentativeL u x = preciseRepresentative μ (value u) x := by
  simpa only [boundedContinuousRepresentativeL, ContinuousLinearMap.comp_apply,
    BoundedContinuousFunction.compContinuousCLM_apply,
    BoundedContinuousFunction.compContinuous_apply,
    HolderSpace.toBoundedContinuousFunctionCLM_apply, HolderSpace.toBoundedContinuousFunction_apply,
    ContinuousMap.coe_mk] using
      (lipschitzRepresentativeL_apply (by simpa only [Opens.coe_top] using convex_univ)
        u (Opens.mem_top x))

/-- The bounded continuous representative agrees almost everywhere with the original value. -/
theorem value_ae_eq_boundedContinuousRepresentativeL (u : W1p μ (⊤ : Opens E) ∞) :
    value u =ᵐ[μ] boundedContinuousRepresentativeL u := by
  have hΩ : Convex ℝ ((⊤ : Opens E) : Set E) := by simpa only [Opens.coe_top] using convex_univ
  filter_upwards [ae_lipschitzRepresentativeL_eq hΩ u] with x hx
  rw [boundedContinuousRepresentativeL_apply, ← lipschitzRepresentativeL_apply hΩ u
    (Opens.mem_top x)]
  exact (hx (Opens.mem_top x)).symm

/-- A bounded continuous function is the canonical representative exactly when it agrees
almost everywhere with the Sobolev value. -/
theorem boundedContinuousRepresentativeL_eq_iff (u : W1p μ (⊤ : Opens E) ∞) (f : E →ᵇ ℝ) :
    boundedContinuousRepresentativeL u = f ↔ value u =ᵐ[μ] f := by
  constructor
  · rintro rfl
    exact value_ae_eq_boundedContinuousRepresentativeL u
  · intro h
    apply DFunLike.coe_injective
    exact (Continuous.ae_eq_iff_eq μ (boundedContinuousRepresentativeL u).continuous
      f.continuous).1
      ((value_ae_eq_boundedContinuousRepresentativeL u).symm.trans h)

/-- The bounded continuous representative determines its Sobolev class. -/
theorem boundedContinuousRepresentativeL_injective :
    Function.Injective (boundedContinuousRepresentativeL (μ := μ)) := by
  intro u v h
  have hu := (boundedContinuousRepresentativeL_eq_iff u _).1 h
  exact ext_value (Lp.ext (ae_restrict_of_ae
    (hu.trans (value_ae_eq_boundedContinuousRepresentativeL v).symm)))

/-- The supremum norm of the continuous representative is exactly the essential supremum
norm of the Sobolev value. -/
-- Rewrite the norm before simplification of the whole-space open-set coercion.
@[simp↓]
theorem norm_boundedContinuousRepresentativeL (u : W1p μ (⊤ : Opens E) ∞) :
    ‖boundedContinuousRepresentativeL u‖ = ‖value u‖ := by
  let ν := μ.restrict ((⊤ : Opens E) : Set E)
  have : ν.IsOpenPosMeasure := by simpa [ν] using (inferInstance : μ.IsOpenPosMeasure)
  rw [← BoundedContinuousFunction.norm_toLpTop ν (𝕜 := ℝ)]
  congr 1
  exact Lp.ext ((BoundedContinuousFunction.coeFn_toLpTop ν (𝕜 := ℝ)
    (boundedContinuousRepresentativeL u)).trans
      (ae_restrict_of_ae (value_ae_eq_boundedContinuousRepresentativeL u).symm))

/-- The Lipschitz constant of the representative is bounded by the weak-gradient norm. -/
theorem lipschitzWith_boundedContinuousRepresentativeL (u : W1p μ (⊤ : Opens E) ∞) :
    LipschitzWith ‖gradient u‖₊ (boundedContinuousRepresentativeL u) := by
  rw [funext (boundedContinuousRepresentativeL_apply u)]
  exact lipschitzWith_preciseRepresentative u

end TauCeti.W1p
