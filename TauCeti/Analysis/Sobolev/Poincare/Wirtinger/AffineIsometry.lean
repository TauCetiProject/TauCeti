/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving

/-!
# The Poincaré–Wirtinger inequality under rigid motions

Let `g` be an affine isometry between finite-dimensional real inner product spaces, let `V` be
open, let `U = g⁻¹(V)` and let `S ⊆ V`. This file proves that the Poincaré–Wirtinger inequality

`‖u - ⨍_S u‖_{Lᵖ(V)} ≤ C ‖∇u‖_{Lᵖ(V)}` for every `u ∈ W^{1,p}(V)`

holds exactly when the same inequality, with the mean taken over `g⁻¹(S)`, holds on `W^{1,p}(U)`
(`TauCeti.W1p.forall_eLpNorm_value_sub_setAverage_le_iff_of_affineIsometryEquiv`). So the
admissible constants of the inequality, and hence its optimal constant, are invariant under rigid
motions of the pair `(V, S)`. The equivalence holds for every constant `C` and every exponent
`1 ≤ p ≤ ∞`, and needs no regularity, connectedness or boundedness of `V`. Whether some finite
constant exists is a separate question, answered for instance by
`TauCeti.W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith` on a bounded
connected Lipschitz domain. Taking `S = V`, so that `g⁻¹(S) = U`, gives the invariance of the
inequality for the mean over the whole domain.

Precomposition `u ↦ u ∘ g` (`TauCeti.W1p.compAffineIsometryEquivL`) preserves each of the three
quantities in the inequality: the `Lᵖ` norm of the deviation from a constant
(`TauCeti.W1p.eLpNorm_value_compAffineIsometryEquivL_sub`), the mean
(`TauCeti.W1p.setAverage_value_compAffineIsometryEquivL`) and the `Lᵖ` norm of the weak gradient
(`TauCeti.W1p.norm_gradient_compAffineIsometryEquivL`). Applied to `g` and to its inverse, this
transfers the inequality in both directions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.1 (the Poincaré–Wirtinger
  inequality).
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {F F' : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
  [FiniteDimensional ℝ F'] [MeasurableSpace F'] [BorelSpace F'] {U : Opens F} {V : Opens F'}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One direction of
`TauCeti.W1p.forall_eLpNorm_value_sub_setAverage_le_iff_of_affineIsometryEquiv`: the inequality on
`U = g⁻¹(V)` with means over `g⁻¹(S)` gives it on `V` with means over `S`, by testing it on
`v ∘ g`. -/
private theorem W1p.eLpNorm_value_sub_setAverage_le_of_affineIsometryEquiv (g : F ≃ᵃⁱ[ℝ] F')
    (hUV : (U : Set F) = g ⁻¹' V) {S : Set F'} (hS : S ⊆ V) {C : ℝ≥0∞}
    (h : ∀ u : W1p volume U p,
      eLpNorm (fun x => W1p.value u x - ⨍ y in g ⁻¹' S, W1p.value u y) p (volume.restrict U) ≤
        C * ‖W1p.gradient u‖ₑ)
    (v : W1p volume V p) :
    eLpNorm (fun x => W1p.value v x - ⨍ y in S, W1p.value v y) p (volume.restrict V) ≤
      C * ‖W1p.gradient v‖ₑ := by
  have hv := h (W1p.compAffineIsometryEquivL g hUV v)
  rwa [W1p.setAverage_value_compAffineIsometryEquivL g hUV v hS,
    W1p.eLpNorm_value_compAffineIsometryEquivL_sub, ← ofReal_norm,
    W1p.norm_gradient_compAffineIsometryEquivL, ofReal_norm] at hv

/-- **The Poincaré–Wirtinger inequality is invariant under rigid motions.** Let `g` be an affine
isometry, `U = g⁻¹(V)` and `S ⊆ V`. For every constant `C`,
`‖u - ⨍_{g⁻¹(S)} u‖_{Lᵖ(U)} ≤ C ‖∇u‖_{Lᵖ(U)}` holds for every `u ∈ W^{1,p}(U)` exactly when
`‖v - ⨍_S v‖_{Lᵖ(V)} ≤ C ‖∇v‖_{Lᵖ(V)}` holds for every `v ∈ W^{1,p}(V)`. -/
theorem W1p.forall_eLpNorm_value_sub_setAverage_le_iff_of_affineIsometryEquiv (g : F ≃ᵃⁱ[ℝ] F')
    (hUV : (U : Set F) = g ⁻¹' V) {S : Set F'} (hS : S ⊆ V) (C : ℝ≥0∞) :
    (∀ u : W1p volume U p,
      eLpNorm (fun x => W1p.value u x - ⨍ y in g ⁻¹' S, W1p.value u y) p (volume.restrict U) ≤
        C * ‖W1p.gradient u‖ₑ) ↔
      ∀ v : W1p volume V p,
        eLpNorm (fun x => W1p.value v x - ⨍ y in S, W1p.value v y) p (volume.restrict V) ≤
          C * ‖W1p.gradient v‖ₑ := by
  refine ⟨W1p.eLpNorm_value_sub_setAverage_le_of_affineIsometryEquiv g hUV hS, fun h => ?_⟩
  -- Transfer back along `g⁻¹`, for which `V = (g⁻¹)⁻¹(U)` and `S = (g⁻¹)⁻¹(g⁻¹(S))`.
  have hVU : (V : Set F') = g.symm ⁻¹' U := by
    rw [hUV, ← preimage_comp]
    ext
    simp
  have hSS : g.symm ⁻¹' (g ⁻¹' S) = S := by
    ext
    simp
  exact W1p.eLpNorm_value_sub_setAverage_le_of_affineIsometryEquiv g.symm hVU
    (hUV ▸ preimage_mono hS) (by rwa [hSS])

end TauCeti
