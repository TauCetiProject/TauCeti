/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.D1p0.Basic

/-!
# Translations of homogeneous Sobolev functions

Translation acts isometrically on the whole-space homogeneous Sobolev space
`TauCeti.D1p0 mu ⊤ p`. An element of this space is recorded by its gradient in `Lᵖ`;
translation acts on that gradient by the existing `MeasureTheory.Measure.translateLp`.
The closure of test-function gradients is invariant, since differentiation commutes with
translation. No second completion or choice of a function representative is needed.

`TauCeti.D1p0.translate` sends the function `u` to `u(· + h)`. It agrees with translation
of test functions, satisfies the additive action laws, and is strongly continuous for finite
`p`. The Sobolev embedding intertwines this action with translation in the Sobolev-conjugate
`Lᵖ` space. In particular, for `p = 2` and dimension greater than two, translations preserve
both the Dirichlet norm and the critical norm used in the sharp Sobolev inequality.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Sections 8.2–8.3.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

local instance D1p0.instIsAddHaarMeasureRestrictTop :
    (mu.restrict (⊤ : Opens E)).IsAddHaarMeasure := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    (inferInstance : mu.IsAddHaarMeasure)

/-- Translation preserves the closed subspace of whole-space test-function gradients. -/
theorem translateLp_mem_d1p0Submodule (h : E) {u : Lp E p (mu.restrict (⊤ : Opens E))}
    (hu : u ∈ (d1p0Submodule mu ⊤ p : Set _)) :
    (mu.restrict (⊤ : Opens E)).translateLp p h u ∈
      (d1p0Submodule mu ⊤ p : Set _) := by
  rw [coe_d1p0Submodule] at hu
  refine closure_minimal ?_ ((d1p0Submodule mu ⊤ p).isClosed.preimage
    ((mu.restrict (⊤ : Opens E)).translateLp p h).continuous) hu
  rintro _ ⟨phi, rfl⟩
  simp only [Set.mem_preimage]
  rw [← gradientTestFunctionLp_translateTestFunction, coe_d1p0Submodule]
  exact subset_closure (mem_range_self _)

namespace D1p0

variable (mu p) in
/-- Translation `u ↦ u(· + h)` on the whole-space homogeneous Sobolev completion, as a
linear isometric equivalence. Its inverse is translation by `-h`. -/
def translate (h : E) : D1p0 mu ⊤ p ≃ₗᵢ[ℝ] D1p0 mu ⊤ p where
  toFun u := ⟨(mu.restrict (⊤ : Opens E)).translateLp p h u,
    translateLp_mem_d1p0Submodule h u.property⟩
  invFun u := ⟨(mu.restrict (⊤ : Opens E)).translateLp p (-h) u,
    translateLp_mem_d1p0Submodule (-h) u.property⟩
  left_inv u := Subtype.ext <| by
    simpa only [Measure.translateLp_symm] using
      ((mu.restrict (⊤ : Opens E)).translateLp p h).symm_apply_apply
        (u : Lp E p (mu.restrict (⊤ : Opens E)))
  right_inv u := Subtype.ext <| by
    simpa only [Measure.translateLp_symm] using
      ((mu.restrict (⊤ : Opens E)).translateLp p h).apply_symm_apply
        (u : Lp E p (mu.restrict (⊤ : Opens E)))
  map_add' u v := Subtype.ext (map_add _ _ _)
  map_smul' c u := Subtype.ext (map_smul _ _ _)
  norm_map' u := ((mu.restrict (⊤ : Opens E)).translateLp p h).norm_map
    (u : Lp E p (mu.restrict (⊤ : Opens E)))

/- These rules run before simplification of the subtype carrier: otherwise the coercion of
`⊤ : Opens E` in the gradient's measure is simplified before the translation is recognized. -/

/-- The recorded gradient of a translated homogeneous Sobolev function is the translated
recorded gradient. -/
@[simp↓]
theorem coe_translate (h : E) (u : D1p0 mu ⊤ p) :
    (translate mu p h u : Lp E p (mu.restrict (⊤ : Opens E))) =
      (mu.restrict (⊤ : Opens E)).translateLp p h u :=
  (rfl)

/-- On test functions, the homogeneous Sobolev translation is the usual translation. -/
@[simp↓]
theorem translate_ofTestFunctionₗ (h : E) (phi : 𝓓((⊤ : Opens E), ℝ)) :
    translate mu p h (ofTestFunctionₗ mu ⊤ p phi) =
      ofTestFunctionₗ mu ⊤ p (translateTestFunction (Omega := ⊤) (h := -h)
        (by intro x _; exact Opens.mem_top _) phi) := by
  apply Subtype.ext
  simp only [coe_translate, coe_ofTestFunctionₗ, gradientTestFunctionLp_translateTestFunction]

/-- Translation by zero is the identity. -/
@[simp↓]
theorem translate_zero (u : D1p0 mu ⊤ p) : translate mu p 0 u = u := by
  apply Subtype.ext
  simp only [coe_translate, Measure.translateLp_zero]

/-- The translations form an additive action. -/
theorem translate_add (h k : E) (u : D1p0 mu ⊤ p) :
    translate mu p (h + k) u = translate mu p h (translate mu p k u) := by
  apply Subtype.ext
  simp only [coe_translate, Measure.translateLp_add, LinearIsometryEquiv.trans_apply]

/-- The inverse of a homogeneous Sobolev translation is translation by the opposite vector. -/
@[simp]
theorem translate_symm (h : E) : (translate mu p h).symm = translate mu p (-h) := by
  apply LinearIsometryEquiv.ext
  intro u
  apply (translate mu p h).injective
  simp only [LinearIsometryEquiv.apply_symm_apply, ← translate_add, add_neg_cancel,
    translate_zero]

/-- Translation of a fixed homogeneous Sobolev function depends continuously on the
translation vector for every finite exponent. -/
theorem continuous_translate (hp : p ≠ ∞) (u : D1p0 mu ⊤ p) :
    Continuous fun h : E ↦ translate mu p h u :=
  (Measure.continuous_translateLp hp (u : Lp E p (mu.restrict (⊤ : Opens E)))).subtype_mk _

/-- The Sobolev embedding intertwines translation on the homogeneous completion with
translation of its represented function in the Sobolev-conjugate `Lᵖ` space. -/
@[simp↓]
theorem sobolevEmbeddingL_translate {pstar : ENNReal} (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (Module.finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹)
    (h : E) (u : D1p0 mu ⊤ p) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    sobolevEmbeddingL hexp (translate mu p h u) =
      (mu.restrict (⊤ : Opens E)).translateLp pstar h (sobolevEmbeddingL hexp u) := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  refine (denseRange_ofTestFunctionₗ (mu := mu) (Omega := ⊤) (p := p)).induction_on u
    (isClosed_eq ((sobolevEmbeddingL hexp).continuous.comp (translate mu p h).continuous)
      (((mu.restrict (⊤ : Opens E)).translateLp pstar h).continuous.comp
        (sobolevEmbeddingL hexp).continuous)) fun phi ↦ ?_
  simp only [translate_ofTestFunctionₗ, sobolevEmbeddingL_ofTestFunctionₗ hpstar hexp,
    testFunctionLp_translateTestFunction]

end D1p0

end TauCeti
