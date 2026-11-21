/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.LieGroup
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient

/-!
# The smooth action of the Sobolev gauge group on framed vortex fields

For an integer `k > 1`, the Sobolev framed gauge group `G_(k+1)` acts on the continuous fields of
the affine space `A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` of framed degree-`m` plane vortex fields by
`(a, α) ↦ (a - u⁻¹ du, u α)` (`TauCeti.Vortex.SobolevFieldSpace.instMulAction`). The group is a Lie
group in its exponential charts `F ↦ u exp (i F)` (`TauCeti.Vortex.gaugeChart`,
`TauCeti.Vortex.SobolevTopologicalGaugeGroup.instLieGroup`), and a field is recorded by the
coordinates of `x - x_m` in `H^k(ℂ)⁴` (`TauCeti.Vortex.SobolevFieldSpace.subRef`). The coordinates
of `u · x - x_m` are `smulCoord (Re u - 1) (Im u) y`, a polynomial expression in `Re u - 1`,
`Im u` and the coordinates `y` of `x - x_m` (`TauCeti.Vortex.SobolevFieldSpace.subRef_smul`).

This file shows that the action is smooth in these coordinates, and computes its derivative at the
identity. These are the inputs of the slice theorem for the gauge action at a vortex.

* **Smoothness.** Since `Re u - 1 = ((u - 1) + (u⁻¹ - 1)) / 2` and
  `Im u = -i ((u - 1) - (u⁻¹ - 1)) / 2`, both are smooth functions of `u ∈ G_(k+1)`
  (`TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_reSubOne`,
  `TauCeti.Vortex.SobolevTopologicalGaugeGroup.contMDiff_imPart`). Composing with the polynomial
  `smulCoord`, the coordinates of `u · x - x_m` depend smoothly on `u` and on those of `x - x_m`
  (`TauCeti.Vortex.SobolevFieldSpace.contMDiff_smulCoord`), and in exponential coordinates on the
  real phase `F` with `u = exp (i F)`
  (`TauCeti.Vortex.SobolevFieldSpace.contDiff_smulCoord_expGauge`).
* **The derivative at the identity.** At `F = 0`, `Re (exp (i F)) - 1` has derivative zero and
  `Im (exp (i F))` has derivative `G ↦ G` (`TauCeti.Vortex.hasFDerivAt_reSubOne_expGauge_zero`,
  `TauCeti.Vortex.hasFDerivAt_imPart_expGauge_zero`). Hence the derivative of
  `(F, y) ↦ exp (i F) · (x_m + y) - x_m` at `(0, y)` is `(G, η) ↦ d₀ G + η`
  (`TauCeti.Vortex.SobolevFieldSpace.hasFDerivAt_smulCoord_expGauge_zero`), where `d₀` is the
  infinitesimal gauge action at `x_m + y` on the Sobolev scale,
  `G ↦ (-∂₁ G, -∂₂ G, -G q, G p)` (`TauCeti.Vortex.sobolevGaugeDirection`). Its coordinates are the
  `L²` functions of the classical infinitesimal gauge action `TauCeti.Vortex.gaugeDirection`
  (`TauCeti.Vortex.SobolevFieldSpace.coeFn_inclusionLp_sobolevGaugeDirection`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution BesselPotentialSpace
open scoped SchwartzMap BesselPotentialSpace Manifold ContDiff

open SobolevTopologicalGaugeGroup

/-! ### The infinitesimal gauge action on the Sobolev scale -/

section sobolevGaugeDirection

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)]

variable (f m) in
/-- **The infinitesimal gauge action on the Sobolev scale.** For an integer `k > 1` and complexified
coordinates `y ∈ H^k(ℂ)⁴` of a field `x - x_m`, the infinitesimal gauge action `d₀` at `x`
(`TauCeti.Vortex.gaugeDirection`), as a bounded operator `H^(k+1)(ℂ) → H^k(ℂ)⁴`: it sends a phase
`G` to `(-∂₁ G, -∂₂ G, -(q_m + y₃) G, (p_m + y₂) G)`, where `(p_m, q_m)` is the section of the
reference field. For a continuous field `x` of `A_m^k` and a real phase `G`, its `L²` coordinates
are those of `gaugeDirection x G`
(`TauCeti.Vortex.SobolevFieldSpace.coeFn_inclusionLp_sobolevGaugeDirection`). -/
def sobolevGaugeDirection (y : Fin 4 → H^{(k : ℝ)}(ℂ)) :
    H^{(k : ℝ) + 1}(ℂ) →L[ℂ] Fin 4 → H^{(k : ℝ)}(ℂ) :=
  let ι : H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) := inclusion (lt_add_one _).le
  let M := mulCLM (finrank_real_complex_lt_two_mul (s := (k : ℝ))
    (by exact_mod_cast (Fact.out : 1 < k)))
  let D (v : ℂ) : H^{(k : ℝ) + 1}(ℂ) →L[ℂ] H^{(k : ℝ)}(ℂ) :=
    lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top v
  ContinuousLinearMap.pi ![-D 1, -D I, -((M.flip (y 3) + referenceMulCLM f m k 3) ∘L ι),
    (M.flip (y 2) + referenceMulCLM f m k 2) ∘L ι]

section apply

variable (hs' : (finrank ℝ ℂ : ℝ) < 2 * (k : ℝ)) (y : Fin 4 → H^{(k : ℝ)}(ℂ))
  (G : H^{(k : ℝ) + 1}(ℂ))

/-- The first connection coordinate of `d₀ G` is `-∂₁ G`. -/
@[simp]
theorem sobolevGaugeDirection_apply_zero :
    sobolevGaugeDirection f m y G 0 = -lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top 1 G :=
  (rfl)

/-- The second connection coordinate of `d₀ G` is `-∂₂ G`. -/
@[simp]
theorem sobolevGaugeDirection_apply_one :
    sobolevGaugeDirection f m y G 1 = -lineDerivCLM ENNReal.one_lt_two ENNReal.ofNat_ne_top I G :=
  (rfl)

/-- The first section coordinate of `d₀ G` is `-(G y₃ + q_m G)`; `hs'` is any proof that `H^k(ℂ)`
is an algebra. -/
theorem sobolevGaugeDirection_apply_two :
    sobolevGaugeDirection f m y G 2 =
      -(mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le G) (y 3) +
        referenceMulCLM f m k 3 (inclusion (lt_add_one (k : ℝ)).le G)) :=
  (rfl)

/-- The second section coordinate of `d₀ G` is `G y₂ + p_m G`. -/
theorem sobolevGaugeDirection_apply_three :
    sobolevGaugeDirection f m y G 3 =
      mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le G) (y 2) +
        referenceMulCLM f m k 2 (inclusion (lt_add_one (k : ℝ)).le G) :=
  (rfl)

end apply

end sobolevGaugeDirection

/-! ### Smoothness of the action and its derivative at the identity -/

namespace SobolevFieldSpace

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

/-- **The coordinates of the transformed field are polynomial**: `smulCoord` is a smooth function of
`Re u - 1`, `Im u` and the coordinates of `x - x_m`, being built from continuous linear maps and the
continuous bilinear product of `H^k(ℂ)`. -/
theorem contDiff_smulCoord :
    ContDiff ℂ ∞ fun p : H^{(k : ℝ) + 1}(ℂ) × H^{(k : ℝ) + 1}(ℂ) × (Fin 4 → H^{(k : ℝ)}(ℂ)) ↦
      smulCoord f m p.1 p.2.1 p.2.2 := by
  have hs' := finrank_real_complex_lt_two_mul (s := (k : ℝ)) (by exact_mod_cast (Fact.out : 1 < k))
  refine contDiff_pi.2 fun j ↦ ?_
  fin_cases j
  · simp only [Fin.zero_eta, smulCoord_zero hs']
    fun_prop
  · simp only [Fin.mk_one, smulCoord_one hs']
    fun_prop
  · simp only [Fin.reduceFinMk, smulCoord_two hs']
    fun_prop
  · simp only [Fin.reduceFinMk, smulCoord_three hs']
    fun_prop

/-- **The action of `G_(k+1)` on `A_m^k` is smooth.** The coordinates
`smulCoord (Re u - 1) (Im u) y` of `u · x - x_m` (`TauCeti.Vortex.SobolevFieldSpace.subRef_smul`),
where `y` holds the coordinates of `x - x_m`, are a smooth function of the gauge `u ∈ G_(k+1)`,
for its Lie group structure, and of `y ∈ H^k(ℂ)⁴`. -/
theorem contMDiff_smulCoord :
    ContMDiff (𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)).prod
        𝓘(ℝ, Fin 4 → H^{(k : ℝ)}(ℂ))) 𝓘(ℝ, Fin 4 → H^{(k : ℝ)}(ℂ)) ∞
      fun p : SobolevTopologicalGaugeGroup hs × (Fin 4 → H^{(k : ℝ)}(ℂ)) ↦
        smulCoord f m (reSubOne p.1) (imPart p.1) p.2 :=
  (contDiff_smulCoord.restrict_scalars ℝ).comp_contMDiff
    ((contMDiff_reSubOne.comp contMDiff_fst).prodMk_space
      ((contMDiff_imPart.comp contMDiff_fst).prodMk_space contMDiff_snd))

/-- **The orbit maps are smooth**: for a continuous field `x` of `A_m^k`, the coordinates of
`u · x - x_m` in `H^k(ℂ)⁴` depend smoothly on `u ∈ G_(k+1)`. -/
theorem contMDiff_subRef_smul (x : SobolevFieldSpace f m k) :
    ContMDiff 𝓘(ℝ, realSubmodule ℂ (zero_le_one.trans hs.le)) 𝓘(ℝ, Fin 4 → H^{(k : ℝ)}(ℂ)) ∞
      fun u : SobolevTopologicalGaugeGroup hs ↦ subRef (u • x) := by
  simp only [subRef_smul]
  exact contMDiff_smulCoord.comp (contMDiff_id.prodMk contMDiff_const)

/-- **The action in exponential coordinates is smooth**: the coordinates of `exp (i F) · x - x_m`
depend smoothly on the real phase `F ∈ H^(k+1)` and on the coordinates `y` of `x - x_m`. -/
theorem contDiff_smulCoord_expGauge :
    ContDiff ℝ ∞ fun p : realSubmodule ℂ (zero_le_one.trans hs.le) × (Fin 4 → H^{(k : ℝ)}(ℂ)) ↦
      smulCoord f m (reSubOne (expGauge hs p.1)) (imPart (expGauge hs p.1)) p.2 := by
  have hR := contMDiff_iff_contDiff.1 (contMDiff_reSubOne.comp (contMDiff_expGauge (hs := hs) ∞))
  have hJ := contMDiff_iff_contDiff.1 (contMDiff_imPart.comp (contMDiff_expGauge (hs := hs) ∞))
  exact (contDiff_smulCoord.restrict_scalars ℝ).comp
    ((hR.comp contDiff_fst).prodMk ((hJ.comp contDiff_fst).prodMk contDiff_snd))

/-- **The derivative of the action at the identity.** In exponential coordinates, the map
`(F, y) ↦ smulCoord (Re (exp (i F)) - 1) (Im (exp (i F))) y`, which sends a real phase `F` and the
coordinates `y` of `x - x_m` to those of `exp (i F) · x - x_m`, has derivative
`(G, η) ↦ d₀ G + η` at `(0, y)`, where `d₀ = sobolevGaugeDirection f m y` is the infinitesimal gauge
action at `x`. -/
theorem hasFDerivAt_smulCoord_expGauge_zero (y : Fin 4 → H^{(k : ℝ)}(ℂ)) :
    HasFDerivAt (fun p : realSubmodule ℂ (zero_le_one.trans hs.le) × (Fin 4 → H^{(k : ℝ)}(ℂ)) ↦
        smulCoord f m (reSubOne (expGauge hs p.1)) (imPart (expGauge hs p.1)) p.2)
      ((sobolevGaugeDirection f m y).restrictScalars ℝ ∘L
          (realSubmodule ℂ (zero_le_one.trans hs.le)).subtypeL ∘L .fst ℝ _ _ + .snd ℝ _ _)
      (0, y) := by
  have hs' := finrank_real_complex_lt_two_mul (s := (k : ℝ)) (by exact_mod_cast (Fact.out : 1 < k))
  have hR := (hasFDerivAt_reSubOne_expGauge_zero (hs := hs)).comp (f := Prod.fst)
    ((0 : realSubmodule ℂ (zero_le_one.trans hs.le)), y) (hasFDerivAt_fst (𝕜 := ℝ))
  have hJ := (hasFDerivAt_imPart_expGauge_zero (hs := hs)).comp (f := Prod.fst)
    ((0 : realSubmodule ℂ (zero_le_one.trans hs.le)), y) (hasFDerivAt_fst (𝕜 := ℝ))
  have hy (j : Fin 4) := (hasFDerivAt_apply (𝕜 := ℝ) j y).comp (f := Prod.snd)
    ((0 : realSubmodule ℂ (zero_le_one.trans hs.le)), y) hasFDerivAt_snd
  have hD (v : ℂ) := ((lineDerivCLM (E := ℂ) (s := (k : ℝ)) ENNReal.one_lt_two
    ENNReal.ofNat_ne_top v).restrictScalars ℝ).hasFDerivAt.comp _ hJ
  have hDR (v : ℂ) := ((lineDerivCLM (E := ℂ) (s := (k : ℝ)) ENNReal.one_lt_two
    ENNReal.ofNat_ne_top v).restrictScalars ℝ).hasFDerivAt.comp _ hR
  have hιR := ((inclusion (E := ℂ) (lt_add_one (k : ℝ)).le).restrictScalars ℝ).hasFDerivAt.comp _ hR
  have hιJ := ((inclusion (E := ℂ) (lt_add_one (k : ℝ)).le).restrictScalars ℝ).hasFDerivAt.comp _ hJ
  have hrefR (a : Fin 4) := ((referenceMulCLM f m k a).restrictScalars ℝ).hasFDerivAt.comp _ hιR
  have hrefJ (a : Fin 4) := ((referenceMulCLM f m k a).restrictScalars ℝ).hasFDerivAt.comp _ hιJ
  -- The product of `H^k(ℂ)`, as a real bilinear map.
  set M := (mulCLM hs').bilinearRestrictScalars ℝ with hM
  rw [hasFDerivAt_pi']
  intro j
  -- Assemble the derivative of each coordinate from the pieces above.
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, smulCoord_zero hs',
      smulCoord_one hs', smulCoord_two hs', smulCoord_three hs'] <;>
    [refine ((hy 0).sub (((hD 1).add (M.hasFDerivAt_of_bilinear hιR (hD 1))).sub
      (M.hasFDerivAt_of_bilinear hιJ (hDR 1)))).congr_fderiv ?_;
    refine ((hy 1).sub (((hD I).add (M.hasFDerivAt_of_bilinear hιR (hD I))).sub
      (M.hasFDerivAt_of_bilinear hιJ (hDR I)))).congr_fderiv ?_;
    refine (((((hy 2).add (M.hasFDerivAt_of_bilinear hιR (hy 2))).sub
      (M.hasFDerivAt_of_bilinear hιJ (hy 3))).add (hrefR 2)).sub (hrefJ 3)).congr_fderiv ?_;
    refine (((((hy 3).add (M.hasFDerivAt_of_bilinear hιJ (hy 2))).add
      (M.hasFDerivAt_of_bilinear hιR (hy 3))).add (hrefJ 2)).add (hrefR 3)).congr_fderiv ?_]
  -- It remains to identify each assembled derivative with the claimed one.
  all_goals
    refine ContinuousLinearMap.ext fun p ↦ ?_
    simp only [Fin.isValue, hM, ContinuousLinearMap.coe_restrictScalars', Function.comp_apply,
      AddChar.map_zero_eq_one, reSubOne_one, imPart_one, map_zero, zero_apply, add_zero, zero_add,
      sub_zero, sub_apply, add_apply, neg_add_rev, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
      Submodule.coe_subtypeL, Submodule.subtype_apply, sobolevGaugeDirection_apply_zero,
      sobolevGaugeDirection_apply_one, sobolevGaugeDirection_apply_two hs',
      sobolevGaugeDirection_apply_three hs']
    abel

/-- **`sobolevGaugeDirection` is the infinitesimal gauge action.** For a continuous field `x` of
`A_m^k` and a real phase `G ∈ H^(k+1)`, the `L²` function of each coordinate of
`sobolevGaugeDirection f m (subRef x) G` is the corresponding coordinate of
`gaugeDirection x G = (-∂₁ G, -∂₂ G, -G q, G p)`, computed from the continuous representative of
`G`, which is `C¹`. -/
theorem coeFn_inclusionLp_sobolevGaugeDirection (x : SobolevFieldSpace f m k)
    (G : realSubmodule ℂ (zero_le_one.trans hs.le)) (j : Fin 4) :
    ⇑(inclusionLp k.cast_nonneg (sobolevGaugeDirection f m (subRef x) G j)) =ᵐ[volume]
      fun z ↦ ((gaugeDirection x (continuousRep G) z j : ℝ) : ℂ) := by
  have hk : (1 : ℝ) < k := by exact_mod_cast (Fact.out : 1 < k)
  have hs' := finrank_real_complex_lt_two_mul (s := (k : ℝ)) hk
  have hfin := finrank_real_complex_lt_two_mul (s := (k : ℝ) + 1) (by linarith)
  have hC1 : ContDiff ℝ 1 (continuousRep G) := by
    refine contDiff_of_mem_realSobolevFunctions (k := 1) ?_
      (continuousRep_mem_realSobolevFunctions hfin G) (continuous_continuousRep hfin G)
    push_cast
    linarith
  have hG := coeFn_inclusionLp_ae_eq_continuousRep hfin G
  have hιG : ⇑(inclusionLp k.cast_nonneg
      (inclusion (lt_add_one (k : ℝ)).le (G : H^{(k : ℝ) + 1}(ℂ)))) =ᵐ[volume]
        fun z ↦ (continuousRep G z : ℂ) := by
    rw [inclusionLp_inclusion]
    exact hG
  have hy (a : Fin 4) := coeFn_toLp_inclusion_subRef k.cast_nonneg x a
  have hM (u v : H^{(k : ℝ)}(ℂ)) := coeFn_toLp_inclusion_mulCLM hs' k.cast_nonneg u v
  simp only [toLp_inclusion] at hy hM
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · filter_upwards [Lp.coeFn_neg (inclusionLp k.cast_nonneg (lineDerivCLM ENNReal.one_lt_two
      ENNReal.ofNat_ne_top 1 (G : H^{(k : ℝ) + 1}(ℂ)))),
      coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top
        k.cast_nonneg hC1 hG 1] with z h₁ h₂
    rw [sobolevGaugeDirection_apply_zero, map_neg, h₁, Pi.neg_apply, h₂, gaugeDirection_apply_zero,
      Complex.ofReal_neg]
  · filter_upwards [Lp.coeFn_neg (inclusionLp k.cast_nonneg (lineDerivCLM ENNReal.one_lt_two
      ENNReal.ofNat_ne_top I (G : H^{(k : ℝ) + 1}(ℂ)))),
      coeFn_inclusionLp_lineDerivCLM_ae_eq ENNReal.one_lt_two ENNReal.ofNat_ne_top
        k.cast_nonneg hC1 hG I] with z h₁ h₂
    rw [sobolevGaugeDirection_apply_one, map_neg, h₁, Pi.neg_apply, h₂, gaugeDirection_apply_one,
      Complex.ofReal_neg]
  · filter_upwards [Lp.coeFn_neg (inclusionLp k.cast_nonneg
      (mulCLM hs' (inclusion (lt_add_one (k : ℝ)).le (G : H^{(k : ℝ) + 1}(ℂ))) (subRef x 3) +
        referenceMulCLM f m k 3 (inclusion (lt_add_one (k : ℝ)).le (G : H^{(k : ℝ) + 1}(ℂ))))),
      coeFn_inclusionLp_add_ae_eq k.cast_nonneg (hM _ _)
        (coeFn_inclusionLp_referenceMulCLM_ae_eq (f := f) (m := m) 3 _), hιG, hy 3]
      with z h₁ h₂ h₃ h₄
    rw [sobolevGaugeDirection_apply_two hs', map_neg, h₁, Pi.neg_apply, h₂, h₃, h₄,
      gaugeDirection_apply_two]
    push_cast
    ring
  · filter_upwards [coeFn_inclusionLp_add_ae_eq k.cast_nonneg (hM _ _)
        (coeFn_inclusionLp_referenceMulCLM_ae_eq (f := f) (m := m) 2 _), hιG, hy 2] with z h₁ h₂ h₃
    rw [sobolevGaugeDirection_apply_three hs', h₁, h₂, h₃, gaugeDirection_apply_three]
    push_cast
    ring

end SobolevFieldSpace

end TauCeti.Vortex
