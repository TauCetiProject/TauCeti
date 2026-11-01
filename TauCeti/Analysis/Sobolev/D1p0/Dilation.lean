/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.D1p0.Basic

/-!
# Dilations of homogeneous Sobolev functions

The positive reals act isometrically on the whole-space homogeneous Sobolev space
`TauCeti.D1p0 mu ⊤ p` by the dilations

`u ↦ r ^ (1 - n / p) • u (r⁻¹ • ·)`, `r > 0`,

where `n` is the dimension of `E`. An element of this space is recorded by its gradient in `Lᵖ`,
and by the chain rule the gradient of the dilate is `r ^ (-n / p) • ∇u (r⁻¹ • ·)`: the action on
gradients is the isometric `Lᵖ` dilation `MeasureTheory.Measure.dilateLp`. The closure of
test-function gradients is invariant because dilation maps test functions to test functions.

`TauCeti.D1p0.dilate` agrees with the dilation of test functions, satisfies the action laws, and
the Sobolev embedding intertwines it with the isometric dilation of the Sobolev-conjugate
`L^{p⋆}` space: the exponent relation `1/p⋆ + 1/n = 1/p` gives `1 - n / p = -n / p⋆`
(`TauCeti.div_toReal_eq_div_toReal_sub_one`). For `p = 2` and dimension `n ≥ 3`, these are the
dilations `u ↦ r ^ (-(n - 2) / 2) • u (r⁻¹ • ·)`, which preserve both the Dirichlet norm and the
critical `L^{2n/(n-2)}` norm of the sharp Sobolev inequality.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Sections 8.2–8.3.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Set TopologicalSpace
open scoped Distributions ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)] {r s : ℝ}

local instance D1p0.instIsAddHaarMeasureRestrictTopDilate :
    (mu.restrict (⊤ : Opens E)).IsAddHaarMeasure := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using (inferInstance : mu.IsAddHaarMeasure)

/-- The isometric `Lᵖ` dilate of a test-function gradient is the gradient of the dilated test
function `r ^ (1 - n / p) • φ (r⁻¹ • ·)`. -/
private theorem gradientTestFunctionLp_smul_dilateTestFunction (hr : 0 < r)
    (phi : 𝓓((⊤ : Opens E), ℝ)) :
    gradientTestFunctionLp (mu := mu) p
        (r ^ (1 - (finrank ℝ E : ℝ) / p.toReal) •
          dilateTestFunction (Ω := ⊤) hr.ne' (by intro x _; exact Opens.mem_top _) phi) =
      (mu.restrict (⊤ : Opens E)).dilateLp p hr (gradientTestFunctionLp p phi) := by
  rw [gradientTestFunctionLp_smul, gradientTestFunctionLp_dilateTestFunction, smul_smul,
    ← Real.rpow_add hr, sub_add_sub_cancel', sub_self, Real.rpow_zero, one_smul]

/-- Dilation preserves the closed subspace of whole-space test-function gradients. -/
theorem dilateLp_mem_d1p0Submodule (hr : 0 < r) {u : Lp E p (mu.restrict (⊤ : Opens E))}
    (hu : u ∈ (d1p0Submodule mu ⊤ p : Set _)) :
    (mu.restrict (⊤ : Opens E)).dilateLp p hr u ∈ (d1p0Submodule mu ⊤ p : Set _) := by
  rw [coe_d1p0Submodule] at hu
  refine closure_minimal ?_ ((d1p0Submodule mu ⊤ p).isClosed.preimage
    ((mu.restrict (⊤ : Opens E)).dilateLp p hr).continuous) hu
  rintro _ ⟨phi, rfl⟩
  simp only [Set.mem_preimage]
  rw [← gradientTestFunctionLp_smul_dilateTestFunction, coe_d1p0Submodule]
  exact subset_closure (mem_range_self _)

namespace D1p0

variable (mu p) in
/-- Dilation `u ↦ r ^ (1 - n / p) • u (r⁻¹ • ·)` on the whole-space homogeneous Sobolev
completion, for `r > 0`, as a linear isometric equivalence. It acts on the recorded gradient by
the isometric `Lᵖ` dilation, and its inverse is dilation by `r⁻¹`. -/
def dilate (hr : 0 < r) : D1p0 mu ⊤ p ≃ₗᵢ[ℝ] D1p0 mu ⊤ p where
  toFun u := ⟨(mu.restrict (⊤ : Opens E)).dilateLp p hr u,
    dilateLp_mem_d1p0Submodule hr u.property⟩
  invFun u := ⟨(mu.restrict (⊤ : Opens E)).dilateLp p (inv_pos.2 hr) u,
    dilateLp_mem_d1p0Submodule (inv_pos.2 hr) u.property⟩
  left_inv u := Subtype.ext <| by
    simpa only [Measure.dilateLp_symm] using
      ((mu.restrict (⊤ : Opens E)).dilateLp p hr).symm_apply_apply
        (u : Lp E p (mu.restrict (⊤ : Opens E)))
  right_inv u := Subtype.ext <| by
    simpa only [Measure.dilateLp_symm] using
      ((mu.restrict (⊤ : Opens E)).dilateLp p hr).apply_symm_apply
        (u : Lp E p (mu.restrict (⊤ : Opens E)))
  map_add' u v := Subtype.ext (map_add _ _ _)
  map_smul' c u := Subtype.ext (map_smul _ _ _)
  norm_map' u := ((mu.restrict (⊤ : Opens E)).dilateLp p hr).norm_map
    (u : Lp E p (mu.restrict (⊤ : Opens E)))

/- These rules run before simplification of the subtype carrier: otherwise the coercion of
`⊤ : Opens E` in the gradient's measure is simplified before the dilation is recognized. -/

/-- The recorded gradient of a dilated homogeneous Sobolev function is the isometric `Lᵖ` dilate
of the recorded gradient. -/
@[simp↓]
theorem coe_dilate (hr : 0 < r) (u : D1p0 mu ⊤ p) :
    (dilate mu p hr u : Lp E p (mu.restrict (⊤ : Opens E))) =
      (mu.restrict (⊤ : Opens E)).dilateLp p hr u :=
  (rfl)

/-- On test functions, the homogeneous Sobolev dilation is `φ ↦ r ^ (1 - n / p) • φ (r⁻¹ • ·)`. -/
@[simp↓]
theorem dilate_ofTestFunctionₗ (hr : 0 < r) (phi : 𝓓((⊤ : Opens E), ℝ)) :
    dilate mu p hr (ofTestFunctionₗ mu ⊤ p phi) =
      ofTestFunctionₗ mu ⊤ p (r ^ (1 - (finrank ℝ E : ℝ) / p.toReal) •
        dilateTestFunction (Ω := ⊤) hr.ne' (by intro x _; exact Opens.mem_top _) phi) := by
  apply Subtype.ext
  simp only [coe_dilate, coe_ofTestFunctionₗ]
  exact (gradientTestFunctionLp_smul_dilateTestFunction hr phi).symm

/-- Dilation by `1` is the identity. -/
@[simp↓]
theorem dilate_one (u : D1p0 mu ⊤ p) : dilate mu p one_pos u = u := by
  apply Subtype.ext
  simp only [coe_dilate, Measure.dilateLp_one]

/-- The dilations form an action of the multiplicative group of positive reals. -/
theorem dilate_mul (hr : 0 < r) (hs : 0 < s) (u : D1p0 mu ⊤ p) :
    dilate mu p (mul_pos hr hs) u = dilate mu p hr (dilate mu p hs u) := by
  apply Subtype.ext
  simp only [coe_dilate, Measure.dilateLp_mul hr hs, LinearIsometryEquiv.trans_apply]

/-- The inverse of a homogeneous Sobolev dilation is dilation by the inverse factor. -/
@[simp]
theorem dilate_symm (hr : 0 < r) : (dilate mu p hr).symm = dilate mu p (inv_pos.2 hr) := by
  refine LinearIsometryEquiv.ext fun u => (dilate mu p hr).injective (Subtype.ext ?_)
  rw [LinearIsometryEquiv.apply_symm_apply, coe_dilate, coe_dilate, ← Measure.dilateLp_symm hr,
    LinearIsometryEquiv.apply_symm_apply]

/-- The Sobolev embedding intertwines dilation on the homogeneous completion with the isometric
dilation of its represented function in the Sobolev-conjugate `Lᵖ` space. -/
@[simp↓]
theorem sobolevEmbeddingL_dilate {pstar : ENNReal} (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (hr : 0 < r) (u : D1p0 mu ⊤ p) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    sobolevEmbeddingL hexp (dilate mu p hr u) =
      (mu.restrict (⊤ : Opens E)).dilateLp pstar hr (sobolevEmbeddingL hexp u) := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  refine (denseRange_ofTestFunctionₗ (mu := mu) (Omega := ⊤) (p := p)).induction_on u
    (isClosed_eq ((sobolevEmbeddingL hexp).continuous.comp (dilate mu p hr).continuous)
      (((mu.restrict (⊤ : Opens E)).dilateLp pstar hr).continuous.comp
        (sobolevEmbeddingL hexp).continuous)) fun phi ↦ ?_
  rw [dilate_ofTestFunctionₗ, sobolevEmbeddingL_ofTestFunctionₗ hpstar hexp,
    sobolevEmbeddingL_ofTestFunctionₗ hpstar hexp, testFunctionLp_smul,
    testFunctionLp_dilateTestFunction, smul_smul, ← Real.rpow_add hr,
    div_toReal_eq_div_toReal_sub_one hexp, sub_add_sub_cancel', sub_self, Real.rpow_zero,
    one_smul]

end D1p0

end TauCeti
