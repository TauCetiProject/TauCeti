/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
public import TauCeti.MeasureTheory.Function.Lp.RightTranslation
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.Lp.LocallyCompact
import TauCeti.MeasureTheory.Function.Lp.Order
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular
import TauCeti.MeasureTheory.Group.Convolution.Support
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Convolution by `L¹` on `Lᵖ` of a locally compact group

Let `μ` be a left-invariant measure on a topological group `G` which is locally finite and inner
regular for compact sets, for instance a regular left Haar measure on a locally compact group. An
integrable kernel `h` with values in a normed field `𝕜`, such as `ℝ` or `ℂ`, acts on the
`𝕜`-normed space `Lᵖ(G, μ; E)`, for `1 ≤ p < ∞`, by left convolution

```text
h ⋆ f = ∫ y, h(y) • L_y f dμ(y),        (L_y f)(x) = f (y⁻¹ * x),
```

an `Lᵖ`-valued Bochner integral of left translates of `f`. This is the operator form of the
classical convolution `(h ⋆ f)(x) = ∫ y, h(y) • f(y⁻¹ * x) dμ(y)`; the two agree almost
everywhere for compactly supported continuous `h` and `f`, by Fubini's theorem for compactly
supported continuous integrands, which needs no σ-finiteness. The group need not be abelian,
and neither σ-finiteness of `μ` nor second countability of `G` is assumed. The integrand is
almost everywhere strongly measurable because `y ↦ L_y f` is continuous
(`MeasureTheory.Lp.continuous_leftTranslation_apply`), and an integrable `h` lives on a
σ-finite set (`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_smul`).

Since the definition never evaluates `h ⋆ f` at a point, its algebraic properties need no Fubini
theorem. Left translation passes through the integral, and a left translation of the variable
`y` turns `L_g (h ⋆ f)` into `(L_g h) ⋆ f`, while on a locally compact group with a regular Haar
measure right translation passes directly to the second factor, `R_g (h ⋆ f) = h ⋆ (R_g f)`.
Applied to the operator `u ↦ u ⋆ f`, which is continuous and linear in `u`, left equivariance
gives associativity. The positive cone of real `Lᵖ` is closed, so convolution of nonnegative
functions is nonnegative. Integration over `G` is a continuous linear functional on `L¹` invariant
under left translation, so integrals multiply. In particular, convolution preserves nonnegative
`L¹` functions of integral one.

On a locally compact group with a regular Haar measure, the modular inversion
`(J f)(x) = c(x) • f x⁻¹` of `L¹`, where `c` is the modular character, reverses convolution:
`J (h ⋆ k) = J k ⋆ J h`. The identity is checked against set integrals for compactly supported
continuous `h` and `k`, and extended to all of `L¹` by density and continuity
(`MeasureTheory.Lp.dense_setOf_continuous_hasCompactSupport`).

The integrated form `ContRepresentation.integratedOperatorL1` is the corresponding construction
for an arbitrary strongly continuous representation in place of left translation; it is stated
for an additive, not necessarily commutative, monoid and reaches multiplicative groups only
through `Additive G`, whereas this file works with the multiplicative group `G` directly. Similarly,
`TauCeti.convolutionLp` is the additive version of this construction on a finite-dimensional real
vector space with an additive Haar measure.

## Main definitions

* `MeasureTheory.Lp.convolutionL μ p hp`: the `𝕜`-bilinear map `(h, f) ↦ h ⋆ f` from
  `L¹(G, μ; 𝕜)` and `Lᵖ(G, μ; E)` to `Lᵖ(G, μ; E)`, of norm at most one.

## Main results

* `MeasureTheory.Lp.convolutionL_apply`: the defining `Lᵖ`-valued Bochner integral.
* `MeasureTheory.Lp.integrable_smul_leftTranslation`: its integrand is integrable.
* `MeasureTheory.Lp.norm_convolutionL_apply_le`: Young's inequality `‖h ⋆ f‖_p ≤ ‖h‖₁ ‖f‖_p`.
* `MeasureTheory.Lp.leftTranslation_convolutionL`: `L_g (h ⋆ f) = (L_g h) ⋆ f`.
* `MeasureTheory.Lp.rightTranslation_convolutionL`: `R_g (h ⋆ f) = h ⋆ (R_g f)`.
* `MeasureTheory.Lp.convolutionL_assoc`: associativity, `(h ⋆ k) ⋆ f = h ⋆ (k ⋆ f)`.
* `MeasureTheory.Lp.convolutionL_nonneg`: `h ⋆ f ≥ 0` when `h ≥ 0` and `f ≥ 0`.
* `MeasureTheory.Lp.integral_convolutionL`: `∫ (h ⋆ f) = (∫ h) • ∫ f`.
* `MeasureTheory.Lp.convolutionL_toL1_ae_eq`: for compactly supported continuous `h` and `f`, the
  convolution `h ⋆ f` is represented by `x ↦ ∫ y, h y • f (y⁻¹ * x) dμ`.
* `MeasureTheory.Lp.modularInversion_convolutionL`: the modular inversion reverses convolution,
  `J (h ⋆ k) = J k ⋆ J h`.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5
  and §3.2.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, proof of Theorem G.3.1.
-/

public section

noncomputable section

open Filter Function MeasureTheory.Measure TauCeti
open scoped ENNReal

namespace MeasureTheory.Lp

section LeftInvariant

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [NormedAddCommGroup E] [NormedSpace ℝ E]

section LeftInvariant

variable [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]

omit [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E] in
/-- The integrand `y ↦ h(y) • L_y f` of a convolution is integrable. Together with
`convolutionL_apply`, this lets continuous linear maps pass through the integral defining
`h ⋆ f`. -/
theorem integrable_smul_leftTranslation (hp : p ≠ ∞) {h : G → 𝕜} (hh : Integrable h μ)
    (f : Lp E p μ) : Integrable (fun y ↦ h y • leftTranslation μ p 𝕜 y f) μ := by
  refine (hh.norm.mul_const ‖f‖).mono' (hh.aefinStronglyMeasurable.aestronglyMeasurable_smul
    (continuous_leftTranslation_apply hp f)) (.of_forall fun y ↦ ?_)
  rw [norm_smul, LinearIsometryEquiv.norm_map]

omit [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [SMulCommClass ℝ 𝕜 E] in
/-- The integral defining a convolution is bounded by the product of the norms. -/
private theorem norm_integral_smul_leftTranslation_le (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    ‖∫ y, h y • leftTranslation μ p 𝕜 y f ∂μ‖ ≤ ‖h‖ * ‖f‖ := by
  rw [L1.norm_eq_integral_norm, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((L1.integrable_coeFn h).norm.mul_const _)
    (.of_forall fun y ↦ ?_)
  rw [norm_smul, LinearIsometryEquiv.norm_map]

variable (μ p) in
/-- **Convolution** on a group `G` by an integrable kernel, as the bilinear map
`L¹(G, μ; 𝕜) →L Lᵖ(G, μ; E) →L Lᵖ(G, μ; E)` sending `(h, f)` to the `Lᵖ`-valued Bochner
integral `h ⋆ f = ∫ y, h(y) • L_y f dμ(y)` of the left translates `(L_y f)(x) = f (y⁻¹ * x)`. -/
def convolutionL (hp : p ≠ ∞) : Lp 𝕜 1 μ →L[𝕜] Lp E p μ →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 (fun (h : Lp 𝕜 1 μ) (f : Lp E p μ) ↦
        ∫ y, h y • leftTranslation μ p 𝕜 y f ∂μ)
      (fun h₁ h₂ f ↦ by
        rw [← integral_add (integrable_smul_leftTranslation hp (L1.integrable_coeFn h₁) f)
          (integrable_smul_leftTranslation hp (L1.integrable_coeFn h₂) f)]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_add h₁ h₂] with y hy
        rw [hy, Pi.add_apply, add_smul])
      (fun c h f ↦ by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_smul c h] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul, mul_smul])
      (fun h f₁ f₂ ↦ by
        rw [← integral_add (integrable_smul_leftTranslation hp (L1.integrable_coeFn h) f₁)
          (integrable_smul_leftTranslation hp (L1.integrable_coeFn h) f₂)]
        simp_rw [map_add, smul_add])
      (fun c h f ↦ by
        rw [← integral_smul]
        simp_rw [map_smul, smul_comm c]))
    1 fun h f ↦ by simpa using norm_integral_smul_leftTranslation_le h f

variable {hp : p ≠ ∞}

/-- The convolution `h ⋆ f` is the `Lᵖ`-valued integral of the left translates of `f` weighted
by `h`. -/
theorem convolutionL_apply (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    convolutionL μ p hp h f = ∫ y, h y • leftTranslation μ p 𝕜 y f ∂μ :=
  (rfl)

/-- The convolution of the `L¹` class of an integrable function `h` with `f`. -/
theorem convolutionL_toL1 {h : G → 𝕜} (hh : Integrable h μ) (f : Lp E p μ) :
    convolutionL μ p hp (hh.toL1 h) f = ∫ y, h y • leftTranslation μ p 𝕜 y f ∂μ := by
  rw [convolutionL_apply]
  refine integral_congr_ae ?_
  filter_upwards [hh.coeFn_toL1] with y hy
  rw [hy]

/-- **Young's inequality** for an `L¹` kernel: `‖h ⋆ f‖_p ≤ ‖h‖₁ ‖f‖_p`. -/
theorem norm_convolutionL_apply_le (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    ‖convolutionL μ p hp h f‖ ≤ ‖h‖ * ‖f‖ :=
  norm_integral_smul_leftTranslation_le h f

/-- Convolution has operator norm at most one as a bilinear map. -/
theorem norm_convolutionL_le : ‖convolutionL (𝕜 := 𝕜) (E := E) μ p hp‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun h f ↦ by
    simpa using norm_convolutionL_apply_le h f

/-- Convolution commutes with left translation: `L_g (h ⋆ f) = (L_g h) ⋆ f`. -/
theorem leftTranslation_convolutionL (g : G) (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    leftTranslation μ p 𝕜 g (convolutionL μ p hp h f) =
      convolutionL μ p hp (leftTranslation μ 1 𝕜 g h) f := by
  -- Left translation does not depend on the scalar field, so it commutes with the integral.
  have hg : ⇑(leftTranslation μ p ℝ g) = leftTranslation μ p 𝕜 (E := E) g :=
    funext fun u ↦ by rw [leftTranslation_apply, leftTranslation_apply]
  have hcomm := (leftTranslation μ p ℝ g).toContinuousLinearEquiv.integral_comp_comm
    (μ := μ) fun y ↦ h y • leftTranslation μ p 𝕜 y f
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, hg] at hcomm
  -- Substitute `y ↦ g * y` on the right, using left invariance of `μ`.
  rw [convolutionL_apply, convolutionL_apply, ← hcomm, ← integral_mul_left_eq_self
    (fun y ↦ leftTranslation μ 1 𝕜 g h y • leftTranslation μ p 𝕜 y f) g]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_mul_left μ g).quasiMeasurePreserving.ae
    (coeFn_leftTranslation (𝕜 := 𝕜) g h)] with y hy
  simp only [hy, inv_mul_cancel_left, map_smul, map_mul, LinearIsometryEquiv.coe_mul,
    Function.comp_apply]

end NontriviallyNormedField

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E] {hp : p ≠ ∞}

/-- **Associativity of convolution**: `(h ⋆ k) ⋆ f = h ⋆ (k ⋆ f)` for `L¹` kernels `h` and
`k`. -/
theorem convolutionL_assoc [CompleteSpace E] (h k : Lp 𝕜 1 μ) (f : Lp E p μ) :
    convolutionL μ p hp (convolutionL μ 1 ENNReal.one_ne_top h k) f =
      convolutionL μ p hp h (convolutionL μ p hp k f) := by
  -- Push the continuous linear map `u ↦ u ⋆ f` inside the integral defining `h ⋆ k`.
  have hint := ((convolutionL (𝕜 := 𝕜) μ p hp).flip f).integral_comp_comm
    (integrable_smul_leftTranslation ENNReal.one_ne_top (L1.integrable_coeFn h) k)
  simp only [ContinuousLinearMap.flip_apply, map_smul, ← leftTranslation_convolutionL] at hint
  rw [convolutionL_apply (hp := ENNReal.one_ne_top) h k, ← hint]
  exact (convolutionL_apply h _).symm

/-- The convolution of nonnegative functions is nonnegative. -/
theorem convolutionL_nonneg {h : Lp ℝ 1 μ} {f : Lp ℝ p μ} (hh : 0 ≤ h) (hf : 0 ≤ f) :
    0 ≤ convolutionL μ p hp h f := by
  rw [convolutionL_apply]
  refine integral_nonneg_of_ae ?_
  filter_upwards [(coeFn_nonneg h).2 hh] with y hy
  exact smul_nonneg hy (by simpa using leftTranslation_mono y hf)

/-- The integral of a convolution is the product of the integrals: `∫ (h ⋆ f) = (∫ h) • ∫ f`. -/
theorem integral_convolutionL [CompleteSpace E] (h : Lp 𝕜 1 μ) (f : Lp E 1 μ) :
    ∫ x, convolutionL μ 1 ENNReal.one_ne_top h f x ∂μ = (∫ x, h x ∂μ) • ∫ x, f x ∂μ := by
  rw [← L1.integral_eq_integral, L1.integral_eq, convolutionL_apply,
    ← L1.integralCLM.integral_comp_comm
      (integrable_smul_leftTranslation ENNReal.one_ne_top (L1.integrable_coeFn h) f)]
  simp_rw [← L1.integral_eq, L1.integral_smul, L1.integral_eq_integral, integral_leftTranslation,
    integral_smul_const]

/-- For compactly supported continuous `h` and `f`, the convolution `h ⋆ f` is represented almost
everywhere by the pointwise convolution `x ↦ ∫ y, h y • f (y⁻¹ * x) dμ`. -/
theorem convolutionL_toL1_ae_eq [CompleteSpace E] {h : G → 𝕜} {f : G → E} (hhc : Continuous h)
    (hhs : HasCompactSupport h) (hfc : Continuous f) (hfs : HasCompactSupport f) :
    convolutionL μ 1 ENNReal.one_ne_top ((hhc.integrable_of_hasCompactSupport hhs).toL1 h)
        ((hfc.integrable_of_hasCompactSupport hfs).toL1 f) =ᵐ[μ]
      fun x => ∫ y, h y • f (y⁻¹ * x) ∂μ := by
  have hhi := hhc.integrable_of_hasCompactSupport (μ := μ) hhs
  have hfi := hfc.integrable_of_hasCompactSupport (μ := μ) hfs
  set F : G → G → E := fun x y => h y • f (y⁻¹ * x)
  have hFc : Continuous (uncurry F) :=
    (hhc.comp continuous_snd).smul (hfc.comp (continuous_snd.inv.mul continuous_fst))
  have hFsupp (x y : G) (hxy : F x y ≠ 0) : y ∈ tsupport h ∧ y⁻¹ * x ∈ tsupport f :=
    ⟨subset_tsupport _ (left_ne_zero_of_smul hxy), subset_tsupport _ (right_ne_zero_of_smul hxy)⟩
  have hFs : HasCompactSupport (uncurry F) :=
    hasCompactSupport_uncurry_of_inv_mul_mem hhs hfs hFsupp
  have hint : Integrable (fun x => ∫ y, F x y ∂μ) μ :=
    (continuous_integral_of_compact_support μ hhs hFc fun x y hxy =>
      (hFsupp x y hxy).1).integrable_of_hasCompactSupport
      (hasCompactSupport_integral_of_inv_mul_mem μ hhs hfs hFsupp)
  refine (L1.integrable_coeFn _).ae_eq_of_forall_setIntegral_eq _ _ hint fun s _ _ => ?_
  -- Integration over `s` is a continuous linear functional on `L¹`.
  let T : Lp E 1 μ →L[𝕜] E :=
    (L1.integralCLM' (μ := μ.restrict s) 𝕜).comp (LpToLpRestrictCLM G E 𝕜 μ 1 s)
  have hT (u : Lp E 1 μ) : T u = ∫ x in s, u x ∂μ := by
    rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq', L1.integral_eq_integral]
    exact integral_congr_ae (LpToLpRestrictCLM_coeFn 𝕜 s u)
  have hL (y : G) : ∫ x in s, leftTranslation μ 1 𝕜 y (hfi.toL1 f) x ∂μ =
      ∫ x in s, f (y⁻¹ * x) ∂μ := by
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [coeFn_leftTranslation (𝕜 := 𝕜) y (hfi.toL1 f),
      (measurePreserving_mul_left μ y⁻¹).quasiMeasurePreserving.ae hfi.coeFn_toL1] with x h₁ h₂
    exact h₁.trans h₂
  rw [← hT, convolutionL_toL1 hhi,
    ← T.integral_comp_comm (integrable_smul_leftTranslation ENNReal.one_ne_top hhi _)]
  simp_rw [map_smul, hT, hL, ← integral_smul]
  -- Fubini's theorem for the compactly supported continuous integrand `(y, x) ↦ F x y`.
  exact integral_integral_swap_of_hasCompactSupport (f := fun y x => F x y)
    (hFc.comp continuous_swap) (hFs.comp_homeomorph (Homeomorph.prodComm G G))

end RCLike

end LeftInvariant

section ModularInversion

variable [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular]

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The modular inversion reverses the convolution of compactly supported continuous functions. -/
private theorem modularInversion_convolutionL_toL1 {h k : G → 𝕜} (hhc : Continuous h)
    (hhs : HasCompactSupport h) (hkc : Continuous k) (hks : HasCompactSupport k) :
    modularInversion μ 1 𝕜 (convolutionL μ 1 ENNReal.one_ne_top
        ((hhc.integrable_of_hasCompactSupport hhs).toL1 h)
        ((hkc.integrable_of_hasCompactSupport hks).toL1 k)) =
      convolutionL μ 1 ENNReal.one_ne_top
        (modularInversion μ 1 𝕜 ((hkc.integrable_of_hasCompactSupport hks).toL1 k))
        (modularInversion μ 1 𝕜 ((hhc.integrable_of_hasCompactSupport hhs).toL1 h)) := by
  rw [modularInversion_toL1 hkc hks, modularInversion_toL1 hhc hhs]
  refine Lp.ext ?_
  filter_upwards [coeFn_modularInversion (𝕜 := 𝕜) (convolutionL μ 1 ENNReal.one_ne_top
      ((hhc.integrable_of_hasCompactSupport (μ := μ) hhs).toL1 h)
      ((hkc.integrable_of_hasCompactSupport (μ := μ) hks).toL1 k)),
    (quasiMeasurePreserving_inv_of_regular μ).ae (convolutionL_toL1_ae_eq hhc hhs hkc hks),
    convolutionL_toL1_ae_eq (μ := μ) hkc.modularCharacter_smul_comp_inv
      hks.modularCharacter_smul_comp_inv hhc.modularCharacter_smul_comp_inv
      hhs.modularCharacter_smul_comp_inv]
    with x h₁ h₂ h₃
  rw [h₁, h₃, h₂]
  -- Substitute `y ↦ x * y` on the right, using left invariance of `μ`.
  conv_rhs => rw [← integral_mul_left_eq_self _ x]
  simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, ← integral_smul]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right, smul_eq_mul]
  rw [smul_mul_smul_comm, modularCharacter_mul_inv_cancel_right, mul_comm (k _)]

/-- **The modular inversion reverses convolution**: `J (h ⋆ k) = J k ⋆ J h` for `h, k ∈ L¹`,
where `(J f)(x) = c(x) • f x⁻¹` and `c` is the modular character. -/
theorem modularInversion_convolutionL (h k : Lp 𝕜 1 μ) :
    modularInversion μ 1 𝕜 (convolutionL μ 1 ENNReal.one_ne_top h k) =
      convolutionL μ 1 ENNReal.one_ne_top (modularInversion μ 1 𝕜 k)
        (modularInversion μ 1 𝕜 h) := by
  -- Both sides are continuous in `(h, k)` and agree on compactly supported continuous functions.
  have hJ := (modularInversion (E := 𝕜) μ 1 𝕜).continuous
  have hconv := (convolutionL (𝕜 := 𝕜) (E := 𝕜) μ 1 ENNReal.one_ne_top).continuous₂
  have hc₁ : Continuous fun q : Lp 𝕜 1 μ × Lp 𝕜 1 μ =>
      modularInversion μ 1 𝕜 (convolutionL μ 1 ENNReal.one_ne_top q.1 q.2) :=
    hJ.comp hconv
  have hc₂ : Continuous fun q : Lp 𝕜 1 μ × Lp 𝕜 1 μ =>
      convolutionL μ 1 ENNReal.one_ne_top (modularInversion μ 1 𝕜 q.2)
        (modularInversion μ 1 𝕜 q.1) :=
    hconv.comp ((hJ.comp continuous_snd).prodMk (hJ.comp continuous_fst))
  have hD := Lp.dense_setOf_continuous_hasCompactSupport (E := 𝕜) (μ := μ) ENNReal.one_ne_top
  refine congrFun (Continuous.ext_on (hD.prod hD) hc₁ hc₂ ?_) (h, k)
  rintro ⟨u, v⟩ ⟨⟨f, hfc, hfs, hu⟩, ⟨g, hgc, hgs, hv⟩⟩
  obtain rfl : u = _ :=
    Lp.ext (hu.trans (hfc.integrable_of_hasCompactSupport (μ := μ) hfs).coeFn_toL1.symm)
  obtain rfl : v = _ :=
    Lp.ext (hv.trans (hgc.integrable_of_hasCompactSupport (μ := μ) hgs).coeFn_toL1.symm)
  exact modularInversion_convolutionL_toL1 hfc hfs hgc hgs

end ModularInversion
section RightTranslation

variable {G E 𝕜 : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ∞}
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]

/-- Convolution commutes with right translation on the second factor:
`R_g (h ⋆ f) = h ⋆ (R_g f)`. -/
theorem rightTranslation_convolutionL (g : G) (h : Lp 𝕜 1 μ) (f : Lp E p μ) :
    rightTranslation μ p 𝕜 g (convolutionL μ p hp h f) =
      convolutionL μ p hp h (rightTranslation μ p 𝕜 g f) := by
  have hg : ⇑(rightTranslation μ p ℝ g) = ⇑(rightTranslation μ p 𝕜 (E := E) g) :=
    funext fun u ↦ Lp.ext <| (coeFn_rightTranslation (𝕜 := ℝ) g u).trans
      (coeFn_rightTranslation (𝕜 := 𝕜) g u).symm
  have hcomm := (rightTranslation μ p ℝ g).toContinuousLinearEquiv.integral_comp_comm
    (μ := μ) fun y ↦ h y • leftTranslation μ p 𝕜 y f
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, hg] at hcomm
  rw [convolutionL_apply, ← hcomm, convolutionL_apply]
  simp_rw [map_smul, leftTranslation_rightTranslation]

end RightTranslation

end LeftInvariant

end MeasureTheory.Lp
