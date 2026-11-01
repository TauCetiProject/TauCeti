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

`u ↦ r ^ (1 - n / p) • u (r⁻¹ • ·)`,

where `n` is the dimension of `E`. An element of this space is recorded by its gradient in `Lᵖ`,
and the gradient of the dilated function is `r ^ (-n / p) • (∇u) (r⁻¹ • ·)`, the normalized
`Lᵖ` dilation `MeasureTheory.Measure.dilateLp` of `∇u`. So the action is the restriction of
`dilateLp` to the closed subspace of test-function gradients, which it preserves because
dilating a test function stays a test function. No second completion or choice of a function
representative is needed.

`TauCeti.D1p0.dilate` agrees with dilation of test functions, satisfies the multiplicative
action laws, and is intertwined by the Sobolev embedding with the normalized dilation of the
Sobolev-conjugate `Lᵖ` space, because `1 - n / p = -n / p⋆` when `1 / p⋆ + 1 / n = 1 / p`. For
`p = 2` and dimension `n ≥ 3` these are the dilations `u ↦ r ^ (-(n - 2) / 2) • u (r⁻¹ • ·)`, which
preserve both the Dirichlet norm and the critical `L^{2n/(n-2)}` norm compared by the sharp
Sobolev inequality, so its extremals form families invariant under them.

## Main declarations

* `TauCeti.dilateLp_mem_d1p0Submodule`: normalized dilation preserves the closure of the
  whole-space test-function gradients.
* `TauCeti.D1p0.dilate`: dilation by `r > 0` as a linear isometric equivalence of `D^{1,p}`.
* `TauCeti.D1p0.dilate_ofTestFunctionₗ`: on test functions it is
  `φ ↦ r ^ (1 - n / p) • φ (r⁻¹ • ·)`.
* `TauCeti.D1p0.dilate_one`, `TauCeti.D1p0.dilate_mul`, `TauCeti.D1p0.dilate_symm`: the action
  laws.
* `TauCeti.D1p0.sobolevEmbeddingL_dilate`: the Sobolev embedding intertwines the dilations.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics 14, AMS (2001),
  Sections 8.2–8.3, for the homogeneous space and the scale invariance of Sobolev's inequality.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 3, for the dilation invariance of the sharp Sobolev quotient.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Set TopologicalSpace
open scoped Distributions ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)] {r s : ℝ}

/-- The whole-space restriction of an additive Haar measure is an additive Haar measure. -/
local instance isAddHaarMeasure_restrict_top_d1p0Dilation :
    (mu.restrict (⊤ : Opens E)).IsAddHaarMeasure := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using (inferInstance : mu.IsAddHaarMeasure)

/-- The normalized `Lᵖ` dilation of a test-function gradient is the gradient of the test function
`r ^ (1 - n / p) • φ (r⁻¹ • ·)`. -/
private theorem dilateLp_gradientTestFunctionLp (hr : 0 < r)
    (hVO : MapsTo (fun x : E ↦ r • x) (⊤ : Opens E) (⊤ : Opens E)) (phi : 𝓓((⊤ : Opens E), ℝ)) :
    (mu.restrict (⊤ : Opens E)).dilateLp p r hr (gradientTestFunctionLp p phi) =
      gradientTestFunctionLp p
        (r ^ (1 - (finrank ℝ E : ℝ) / p.toReal) • dilateTestFunction hr.ne' hVO phi) := by
  rw [gradientTestFunctionLp_smul, gradientTestFunctionLp_dilateTestFunction, smul_smul,
    ← Real.rpow_add hr,
    show 1 - (finrank ℝ E : ℝ) / p.toReal + ((finrank ℝ E : ℝ) / p.toReal - 1) = 0 by ring,
    Real.rpow_zero, one_smul]

/-- Normalized dilation preserves the closed subspace of whole-space test-function gradients. -/
theorem dilateLp_mem_d1p0Submodule (hr : 0 < r) {u : Lp E p (mu.restrict (⊤ : Opens E))}
    (hu : u ∈ (d1p0Submodule mu ⊤ p : Set _)) :
    (mu.restrict (⊤ : Opens E)).dilateLp p r hr u ∈ (d1p0Submodule mu ⊤ p : Set _) := by
  rw [coe_d1p0Submodule] at hu
  refine closure_minimal ?_ ((d1p0Submodule mu ⊤ p).isClosed.preimage
    ((mu.restrict (⊤ : Opens E)).dilateLp p r hr).continuous) hu
  have hVO : MapsTo (fun x : E ↦ r • x) (⊤ : Opens E) (⊤ : Opens E) := fun _ _ ↦ Opens.mem_top _
  rintro _ ⟨phi, rfl⟩
  rw [Set.mem_preimage, dilateLp_gradientTestFunctionLp hr hVO, coe_d1p0Submodule]
  exact subset_closure (mem_range_self _)

namespace D1p0

variable (mu p) in
/-- **Dilation on the whole-space homogeneous Sobolev space** by a factor `r > 0`, as a linear
isometric equivalence. It sends the recorded gradient `∇u` to the normalized `Lᵖ` dilation
`r ^ (-n / p) • (∇u) (r⁻¹ • ·)`, where `n` is the dimension of `E`, which is the gradient of
`r ^ (1 - n / p) • u (r⁻¹ • ·)`: on test functions it is this dilation
(`TauCeti.D1p0.dilate_ofTestFunctionₗ`), and through the Sobolev embedding it acts on the
represented function in the same way (`TauCeti.D1p0.sobolevEmbeddingL_dilate`). Its inverse is
the dilation by `r⁻¹`. -/
def dilate (r : ℝ) (hr : 0 < r) : D1p0 mu ⊤ p ≃ₗᵢ[ℝ] D1p0 mu ⊤ p where
  toFun u := ⟨(mu.restrict (⊤ : Opens E)).dilateLp p r hr u,
    dilateLp_mem_d1p0Submodule hr u.property⟩
  invFun u := ⟨(mu.restrict (⊤ : Opens E)).dilateLp p r⁻¹ (inv_pos.2 hr) u,
    dilateLp_mem_d1p0Submodule (inv_pos.2 hr) u.property⟩
  left_inv u := Subtype.ext <| by
    simpa only [Measure.dilateLp_symm] using
      ((mu.restrict (⊤ : Opens E)).dilateLp p r hr).symm_apply_apply
        (u : Lp E p (mu.restrict (⊤ : Opens E)))
  right_inv u := Subtype.ext <| by
    simpa only [Measure.dilateLp_symm] using
      ((mu.restrict (⊤ : Opens E)).dilateLp p r hr).apply_symm_apply
        (u : Lp E p (mu.restrict (⊤ : Opens E)))
  map_add' u v := Subtype.ext (map_add _ _ _)
  map_smul' c u := Subtype.ext (map_smul _ _ _)
  norm_map' u := ((mu.restrict (⊤ : Opens E)).dilateLp p r hr).norm_map
    (u : Lp E p (mu.restrict (⊤ : Opens E)))

/- These rules run before simplification of the subtype carrier: otherwise the coercion of
`⊤ : Opens E` in the gradient's measure is simplified before the dilation is recognized. -/

/-- The recorded gradient of a dilated homogeneous Sobolev function is the normalized `Lᵖ`
dilation of the recorded gradient. -/
@[simp↓]
theorem coe_dilate (hr : 0 < r) (u : D1p0 mu ⊤ p) :
    (dilate mu p r hr u : Lp E p (mu.restrict (⊤ : Opens E))) =
      (mu.restrict (⊤ : Opens E)).dilateLp p r hr u :=
  (rfl)

/-- On test functions, the homogeneous Sobolev dilation is `φ ↦ r ^ (1 - n / p) • φ (r⁻¹ • ·)`. -/
theorem dilate_ofTestFunctionₗ (hr : 0 < r)
    (hVO : MapsTo (fun x : E ↦ r • x) (⊤ : Opens E) (⊤ : Opens E)) (phi : 𝓓((⊤ : Opens E), ℝ)) :
    dilate mu p r hr (ofTestFunctionₗ mu ⊤ p phi) =
      ofTestFunctionₗ mu ⊤ p (r ^ (1 - (finrank ℝ E : ℝ) / p.toReal) •
        dilateTestFunction hr.ne' hVO phi) := by
  apply Subtype.ext
  rw [coe_dilate, coe_ofTestFunctionₗ, coe_ofTestFunctionₗ, dilateLp_gradientTestFunctionLp]

/-- Dilation by `1` is the identity. -/
@[simp↓]
theorem dilate_one (u : D1p0 mu ⊤ p) : dilate mu p 1 one_pos u = u :=
  Subtype.ext (Measure.dilateLp_one _)

/-- Dilating by `r * s` is dilating by `s` and then by `r`. -/
theorem dilate_mul (hr : 0 < r) (hs : 0 < s) (u : D1p0 mu ⊤ p) :
    dilate mu p (r * s) (mul_pos hr hs) u = dilate mu p r hr (dilate mu p s hs u) := by
  apply Subtype.ext
  rw [coe_dilate, coe_dilate, coe_dilate, Measure.dilateLp_mul hr hs,
    LinearIsometryEquiv.trans_apply]

/-- The inverse of a homogeneous Sobolev dilation is the dilation by the inverse factor. -/
theorem dilate_symm (hr : 0 < r) :
    (dilate mu p r hr).symm = dilate mu p r⁻¹ (inv_pos.2 hr) :=
  LinearIsometryEquiv.ext fun _ ↦ (rfl)

/-- **The Sobolev embedding intertwines the dilations**: it sends the dilation of `u` by `r` on
the homogeneous Sobolev space to the normalized dilation by `r` of the represented function in
the Sobolev-conjugate `L^{p⋆}` space, since `1 - n / p = -n / p⋆`. In particular, dilations
preserve the `L^{p⋆}` norm of the represented function as well as the gradient norm. -/
theorem sobolevEmbeddingL_dilate {pstar : ENNReal} (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹) (hr : 0 < r) (u : D1p0 mu ⊤ p) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    sobolevEmbeddingL hexp (dilate mu p r hr u) =
      (mu.restrict (⊤ : Opens E)).dilateLp pstar r hr (sobolevEmbeddingL hexp u) := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  -- The exponent identity `n / p⋆ + 1 = n / p` behind the matching powers of `r`.
  have hexp' : (finrank ℝ E : ℝ) / pstar.toReal + 1 = (finrank ℝ E : ℝ) / p.toReal := by
    have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
    have hn : finrank ℝ E ≠ 0 := by
      rintro hn
      rw [hn, Nat.cast_zero, ENNReal.inv_zero, add_top] at hexp
      exact hp (ENNReal.inv_eq_top.1 hexp.symm)
    have hpinv : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hp
    have h := congrArg ENNReal.toReal hexp
    rw [ENNReal.toReal_add (ne_top_of_le_ne_top hpinv (hexp ▸ le_self_add))
      (ne_top_of_le_ne_top hpinv (hexp ▸ le_add_self)), ENNReal.toReal_inv, ENNReal.toReal_inv,
      ENNReal.toReal_inv, ENNReal.toReal_natCast] at h
    rw [div_eq_mul_inv, div_eq_mul_inv, ← h, mul_add, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)]
  refine (denseRange_ofTestFunctionₗ (mu := mu) (Omega := ⊤) (p := p)).induction_on u
    (isClosed_eq ((sobolevEmbeddingL hexp).continuous.comp (dilate mu p r hr).continuous)
      (((mu.restrict (⊤ : Opens E)).dilateLp pstar r hr).continuous.comp
        (sobolevEmbeddingL hexp).continuous)) fun phi ↦ ?_
  have hVO : MapsTo (fun x : E ↦ r • x) (⊤ : Opens E) (⊤ : Opens E) := fun _ _ ↦ Opens.mem_top _
  rw [dilate_ofTestFunctionₗ hr hVO, sobolevEmbeddingL_ofTestFunctionₗ hpstar,
    sobolevEmbeddingL_ofTestFunctionₗ hpstar, testFunctionLp_smul,
    testFunctionLp_dilateTestFunction, smul_smul, ← Real.rpow_add hr, ← hexp',
    show 1 - ((finrank ℝ E : ℝ) / pstar.toReal + 1) + (finrank ℝ E : ℝ) / pstar.toReal = 0 by ring,
    Real.rpow_zero, one_smul]

end D1p0

end TauCeti
