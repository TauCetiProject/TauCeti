/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.D1p0.Basic

/-!
# Dilations of homogeneous Sobolev functions

Dilation acts isometrically on the whole-space homogeneous Sobolev space `TauCeti.D1p0 mu ⊤ p`,
for a Haar measure `mu` on a space `E` of dimension `n`. For `r > 0`, the dilation
`TauCeti.D1p0.dilate` sends the function `u` to

`x ↦ r ^ (1 - n / p) • u (r⁻¹ • x)`,

whose gradient is `x ↦ r ^ (-n / p) • ∇u (r⁻¹ • x)`. Since an element of `D^{1,p}_0(E)` is
recorded by its gradient in `Lᵖ`, the dilation acts on that gradient by the isometric `Lᵖ`
dilation `MeasureTheory.Measure.dilateLp`, and the normalization `r ^ (1 - n / p)` is the one
making the gradient norm invariant. The closure of test-function gradients is invariant because
the gradient of a dilated test function is a multiple of the dilated gradient. These dilations
form an action of the multiplicative group of positive reals.

For a Sobolev conjugate `1/p⋆ + 1/n = 1/p` the exponents satisfy `n / p⋆ = n / p - 1`, so the
same normalization is the isometric dilation of `L^{p⋆}`: the Sobolev embedding intertwines the
dilation of `D^{1,p}_0(E)` with that of `L^{p⋆}(E)`
(`TauCeti.D1p0.sobolevEmbeddingL_dilate`). In particular, for `p = 2` and `n > 2`, the
dilations `u ↦ r ^ (1 - n / 2) • u (r⁻¹ • ·)` preserve both the Dirichlet norm and the critical
norm of the sharp Sobolev inequality, together with the translations of
`TauCeti.D1p0.translate`.

## Main declarations

* `TauCeti.D1p0.dilate`: dilation as a linear isometric equivalence of `D^{1,p}_0(E)`, with
  `TauCeti.D1p0.coe_dilate` its action on gradients.
* `TauCeti.D1p0.dilate_ofTestFunctionₗ`: on test functions it is the usual dilation, multiplied
  by `r ^ (1 - n / p)`.
* `TauCeti.D1p0.dilate_one`, `TauCeti.D1p0.dilate_mul` and `TauCeti.D1p0.dilate_symm`: the
  action laws.
* `TauCeti.D1p0.sobolevEmbeddingL_dilate`: the Sobolev embedding intertwines the dilations of
  `D^{1,p}_0(E)` and of `L^{p⋆}(E)`.

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

/-- Dilation preserves the closed subspace of whole-space test-function gradients. -/
theorem dilateLp_mem_d1p0Submodule (hr : 0 < r) {u : Lp E p (mu.restrict (⊤ : Opens E))}
    (hu : u ∈ (d1p0Submodule mu ⊤ p : Set _)) :
    (mu.restrict (⊤ : Opens E)).dilateLp p hr u ∈ (d1p0Submodule mu ⊤ p : Set _) := by
  rw [coe_d1p0Submodule] at hu
  refine closure_minimal ?_ ((d1p0Submodule mu ⊤ p).isClosed.preimage
    ((mu.restrict (⊤ : Opens E)).dilateLp p hr).continuous) hu
  rintro _ ⟨phi, rfl⟩
  have hc : r ^ ((finrank ℝ E : ℝ) / p.toReal - 1) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have h := gradientTestFunctionLp_dilateTestFunction (mu := mu) (q := p) hr
    (by intro x _; exact Opens.mem_top _) phi
  have h' : (mu.restrict (⊤ : Opens E)).dilateLp p hr (gradientTestFunctionLp p phi) =
      gradientTestFunctionLp p ((r ^ ((finrank ℝ E : ℝ) / p.toReal - 1))⁻¹ •
        dilateTestFunction hr.ne' (by intro x _; exact Opens.mem_top _) phi) := by
    rw [gradientTestFunctionLp_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [Set.mem_preimage, h', coe_d1p0Submodule]
  exact subset_closure (mem_range_self _)

namespace D1p0

variable (mu p) in
/-- **Dilation on the whole-space homogeneous Sobolev completion**, as a linear isometric
equivalence: for `r > 0` it sends the function `u` to `x ↦ r ^ (1 - n / p) • u (r⁻¹ • x)`, where
`n` is the dimension of `E`, so that the recorded gradient is dilated by the isometric `Lᵖ`
dilation `MeasureTheory.Measure.dilateLp`. Its inverse is dilation by `r⁻¹`. -/
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

/- As for `TauCeti.D1p0.coe_translate`, these rules run before simplification of the subtype
carrier: otherwise the coercion of `⊤ : Opens E` in the gradient's measure is simplified before
the dilation is recognized. -/

/-- The recorded gradient of a dilated homogeneous Sobolev function is the `Lᵖ` dilate of the
recorded gradient. -/
@[simp↓]
theorem coe_dilate (hr : 0 < r) (u : D1p0 mu ⊤ p) :
    (dilate mu p hr u : Lp E p (mu.restrict (⊤ : Opens E))) =
      (mu.restrict (⊤ : Opens E)).dilateLp p hr u :=
  (rfl)

/-- On test functions, the homogeneous Sobolev dilation is the usual dilation multiplied by
`r ^ (1 - n / p)`. -/
@[simp↓]
theorem dilate_ofTestFunctionₗ (hr : 0 < r) (phi : 𝓓((⊤ : Opens E), ℝ)) :
    dilate mu p hr (ofTestFunctionₗ mu ⊤ p phi) =
      r ^ (1 - (finrank ℝ E : ℝ) / p.toReal) •
        ofTestFunctionₗ mu ⊤ p
          (dilateTestFunction hr.ne' (by intro x _; exact Opens.mem_top _) phi) := by
  apply Subtype.ext
  rw [coe_dilate, Submodule.coe_smul, coe_ofTestFunctionₗ, coe_ofTestFunctionₗ,
    gradientTestFunctionLp_dilateTestFunction hr, smul_smul, ← Real.rpow_add hr]
  simp

/-- Dilation by `1` is the identity. -/
@[simp↓]
theorem dilate_one (u : D1p0 mu ⊤ p) : dilate mu p one_pos u = u := by
  apply Subtype.ext
  simp only [coe_dilate, Measure.dilateLp_one]

/-- Dilating by `r * s` is dilating by `s` and then by `r`, so the dilations form an action of
the multiplicative group of positive reals. -/
theorem dilate_mul (hr : 0 < r) (hs : 0 < s) (u : D1p0 mu ⊤ p) :
    dilate mu p (mul_pos hr hs) u = dilate mu p hr (dilate mu p hs u) := by
  apply Subtype.ext
  simp only [coe_dilate, Measure.dilateLp_mul hr hs, LinearIsometryEquiv.trans_apply]

/-- The inverse of a homogeneous Sobolev dilation by `r` is dilation by `r⁻¹`. -/
@[simp]
theorem dilate_symm (hr : 0 < r) : (dilate mu p hr).symm = dilate mu p (inv_pos.2 hr) :=
  LinearIsometryEquiv.ext fun _ => rfl

/-- **The Sobolev embedding intertwines dilations**: dilating `u ∈ D^{1,p}_0(E)` and then
passing to `L^{p⋆}` is the isometric `L^{p⋆}` dilation of the function represented by `u`. The
normalizations match because `n / p⋆ = n / p - 1`. -/
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
  rw [dilate_ofTestFunctionₗ, map_smul, sobolevEmbeddingL_ofTestFunctionₗ hpstar hexp,
    sobolevEmbeddingL_ofTestFunctionₗ hpstar hexp, testFunctionLp_dilateTestFunction hr, smul_smul,
    ← Real.rpow_add hr, natCast_div_toReal_eq_div_toReal_sub_one hexp]
  simp

end D1p0

end TauCeti
