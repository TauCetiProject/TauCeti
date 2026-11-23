/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.ChernIdentity
public import TauCeti.Analysis.PDE.SeibergWitten.L2Bounds
public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Measure
import TauCeti.Geometry.Manifold.Riemannian.FormMetric
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Taubes's scaled `L²` energy bound at large parameter

On a closed symplectic four-manifold `X` Taubes perturbs the Seiberg–Witten equations by a large
multiple `r` of the symplectic form. A solution has normalized spinor `χ = α u₀ + β` and
connection `A = A₀ + 2 a`, and, writing the curvature of `a` through the real two-form
`F = i F_a`, the curvature equation reads `F + ⋆F = (r / 4) ω - q(√r χ) - η`
(`TauCeti.Analysis.PDE.SeibergWitten.LargeParameterCurvature`). The basic integral estimate of
the large-parameter analysis is the **scaled energy bound**

`r⁻¹ ‖F_a‖₂² + ‖∇_a α‖₂² + ‖∇β‖₂² + r ‖1 - |α|² - |β|²‖₂² ≤ C`,

with `C` independent of `r` and of the solution. It says that the curvature has `L²` norm
`O(√r)` and the vacuum defect `1 - |χ|²` has `L²` norm `O(r^(-1/2))`: the sizes these quantities
have when curvature of order `r` and a defect of order one concentrate in a tube of radius
`r^(-1/2)` about a surface. Since `∇χ = (∇_a α) u₀ + α ∇u₀ + ∇β` with `u₀` a fixed unit spinor,
it also bounds `‖∇χ‖₂²`.

This file derives the bound
(`TauCeti.SeibergWitten.inv_mul_integral_add_integral_add_integral_add_mul_integral_le`) on a
compact boundaryless oriented Riemannian four-manifold from the following inputs, each of which is
stated and used elsewhere in this directory.

* The `ω`-component of the curvature equation,
  `⟨ω, F⟩ / 2 = (r / 8) (1 - |α|² + |β|²) - ⟨ω, η⟩ / 4`
  (`TauCeti.SeibergWitten.inner_div_two_eq_of_add_hodgeStar_eq`), which through the Chern
  identity gives the `L¹` defect bound `r ∫ |1 - |α|² - |β|²| ≤ C`
  (`TauCeti.SeibergWitten.mul_integralTopForm_abs_one_sub_sub_le`). Its form against the
  Riemannian measure, which `TauCeti.Analysis.PDE.SeibergWitten.CoarseBounds` takes as a
  hypothesis, is `TauCeti.SeibergWitten.mul_integral_abs_one_sub_sub_le`.
* The self-dual part of the curvature equation,
  `|F + ⋆F + η|² ≤ (r² / 8) ((1 - |α|² + |β|²)² + 4 |α|² |β|²)`
  (`TauCeti.SeibergWitten.norm_add_hodgeStar_add_sq_le`), where `F + ⋆F = 2 F⁺`.
* The pointwise bound `|α|² + |β|² ≤ 1 + K / r`.
* The projected Weitzenböck inequalities for `|α|²`, in the form used by
  `TauCeti.SeibergWitten.norm_sq_le_mul_max_one_sub_add`, and for `|β|²`, in the form used by
  `TauCeti.SeibergWitten.integral_norm_sq_add_mul_integral_norm_sq_le_of_laplaceBeltrami`.

Integrating the `α` inequality, the Laplacian drops out and
`∫ |∇_a α|² ≤ K₁ Vol(X) + (r / 4) ∫ (1 - |α|²) |α|²`
(`TauCeti.SeibergWitten.integral_norm_sq_le_mul_add_mul_integral_of_laplaceBeltrami`). The last
integral is controlled by the `L¹` defect and by `r ∫ |β|²`, which the integrated `β` inequality
bounds by `∫ |∇_a α|²` again; for `r ≥ 256 c²` the two estimates close. The defect is at most one
in absolute value, so `r ∫ (1 - |α|² - |β|²)²` is at most the `L¹` defect. Since
`(1 - |α|² + |β|²)² + 4 |α|² |β|² = (1 - |α|² - |β|²)² + 4 |β|²`, the self-dual part of the
curvature equation bounds `|2 F⁺ + η|²` by `(r² / 8) (1 - |α|² - |β|²)² + (r² / 2) |β|²`.
Finally the curvature equation prescribes only `F⁺`, and the anti-self-dual part is recovered by
Chern–Weil: `∫ |F|² = 2 ∫ |F⁺|² - ∫ F ∧ F`, where `∫ F ∧ F` is the topological
number `⟨[F], [F]⟩ = 4π² c₁(E)²` (`TauCeti.SmoothForm.integral_inner_self_eq_two_mul_sub`).

All integrals are taken against the Riemannian volume measure; integrals of top forms produced by
the Chern identity and by Chern–Weil are converted by
`TauCeti.integralTopForm_smul_riemannianVolumeForm`. The right side of the conclusion is explicit:
it depends on `K`, `K₁`, the volume, the perturbation `η`, the pairing `⟨[F], [ω]⟩` and the
characteristic number `∫ F ∧ F`, and not on the solution. It depends on `r` only through the term
`(∫ |η|² - ∫ F ∧ F) / r`, which is at most `|∫ |η|² - ∫ F ∧ F|` because `r ≥ 1`; so the right
side is bounded by a constant `C` independent of `r`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

noncomputable section

open Bundle MeasureTheory TauCeti.Manifold
open scoped Manifold

namespace TauCeti.SeibergWitten

/-- If `s, t ≥ 0`, `s + t ≤ 1 + K / r` and `K ≤ r`, then the defect `|1 - s - t|` is at most
one. -/
private theorem abs_one_sub_sub_le_one {s t r K : ℝ} (hr : 0 < r) (hKr : K ≤ r) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hst : s + t ≤ 1 + K / r) : |1 - s - t| ≤ 1 := by
  have : K / r ≤ 1 := (div_le_one hr).2 hKr
  rw [abs_le]
  constructor <;> linarith

/-- The term `(1 - s) s` of the `α` Weitzenböck inequality is controlled by the defect
`|1 - s - t|` and by `t`, for `0 ≤ s ≤ 2` and `0 ≤ t`. -/
private theorem one_sub_mul_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hs₂ : s ≤ 2) :
    (1 - s) * s ≤ 2 * |1 - s - t| + 2 * t := by
  have h₁ : (1 - s - t) * s ≤ |1 - s - t| * 2 :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hs).trans
      (mul_le_mul_of_nonneg_left hs₂ (abs_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_left hs₂ ht]

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x)]
  {A B F₁ F₂ : M → Type*} [∀ x, SeminormedAddCommGroup (A x)] [∀ x, SeminormedAddCommGroup (B x)]
  [∀ x, SeminormedAddCommGroup (F₁ x)] [∀ x, SeminormedAddCommGroup (F₂ x)] {r : ℝ}

local instance : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := 1) (F := E) (V := fun x : M ↦ TangentSpace I x)

/-- `C^(⊤ + 1)` charts, needed by `TauCeti.IsSmoothForm.contMDiff_alternatingFormInner` for the
continuity of the pointwise inner product of two smooth forms. -/
local instance : IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (⊤ : ℕ∞) M)

omit [I.Boundaryless] [T2Space M] in
/-- Integrated, the term `(1 - |α|²) |α|²` of the `α` Weitzenböck inequality is controlled by the
`L¹` defect and by `∫ |β|²`: if `|α|² + |β|² ≤ 2`, then
`∫ (1 - |α|²) |α|² ≤ 2 ∫ |1 - |α|² - |β|²| + 2 ∫ |β|²`. -/
private theorem integral_one_sub_mul_le {α : (x : M) → A x} {β : (x : M) → B x}
    (hs : Continuous fun x ↦ ‖α x‖ ^ 2) (ht : Continuous fun x ↦ ‖β x‖ ^ 2)
    (hst : ∀ x, ‖α x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 2) :
    ∫ x, (1 - ‖α x‖ ^ 2) * ‖α x‖ ^ 2 ∂riemannianVolume I M ≤
      2 * ∫ x, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂riemannianVolume I M +
        2 * ∫ x, ‖β x‖ ^ 2 ∂riemannianVolume I M := by
  have h := integral_mono (μ := riemannianVolume I M)
    (Continuous.integrable_of_compactSpace (f := fun x ↦ (1 - ‖α x‖ ^ 2) * ‖α x‖ ^ 2)
      (by fun_prop))
    (Continuous.integrable_of_compactSpace
      (f := fun x ↦ 2 * |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| + 2 * ‖β x‖ ^ 2) (by fun_prop))
    fun x ↦ one_sub_mul_le (by positivity) (by positivity) (by nlinarith [hst x, sq_nonneg ‖β x‖])
  rwa [integral_add
    (Continuous.integrable_of_compactSpace (f := fun x ↦ 2 * |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2|)
      (by fun_prop))
    (Continuous.integrable_of_compactSpace (by fun_prop)), integral_const_mul,
    integral_const_mul] at h

omit [I.Boundaryless] [T2Space M] in
/-- **The curvature energy from the self-dual part of the curvature equation.** If
`|2 F⁺ + η|² ≤ (r² / 8) ((1 - |α|² + |β|²)² + 4 |α|² |β|²)`, then
`r⁻¹ ∫ |F|² ≤ (r / 8) ∫ (1 - |α|² - |β|²)² + (r / 2) ∫ |β|² + (∫ |η|² - ∫ F ∧ F) / r`. The
anti-self-dual part of `F` enters through Chern–Weil, `∫ |F|² = 2 ∫ |F⁺|² - ∫ F ∧ F`. -/
private theorem inv_mul_integral_inner_self_le (o : Manifold.Orientation I M (Fin (2 + 2)))
    {F η : SmoothForm I M ℝ 2} {α : (x : M) → A x} {β : (x : M) → B x} (hr : 0 < r)
    (hs : Continuous fun x ↦ ‖α x‖ ^ 2) (ht : Continuous fun x ↦ ‖β x‖ ^ 2)
    (hFη : ∀ x, alternatingFormInner (TangentSpace I x) 2
        ((2 : ℝ) • (SmoothForm.selfDualPart o F).val x + η.val x)
        ((2 : ℝ) • (SmoothForm.selfDualPart o F).val x + η.val x) ≤
      r ^ 2 / 8 * ((1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) ^ 2 + 4 * ‖α x‖ ^ 2 * ‖β x‖ ^ 2)) :
    r⁻¹ * ∫ x, alternatingFormInner (TangentSpace I x) 2 (F.val x) (F.val x) ∂riemannianVolume I M ≤
      r / 8 * ∫ x, (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2 ∂riemannianVolume I M +
        r / 2 * ∫ x, ‖β x‖ ^ 2 ∂riemannianVolume I M +
        (∫ x, alternatingFormInner (TangentSpace I x) 2 (η.val x) (η.val x) ∂riemannianVolume I M -
          integralTopForm o (RoughForm.wedge F.val F.val)) / r := by
  set Fp := SmoothForm.selfDualPart o F
  -- The continuity of `|η|²`, for `fun_prop` below.
  have hη := (η.isSmoothForm.contMDiff_alternatingFormInner η.isSmoothForm).continuous
  -- Pointwise, `|F⁺|² ≤ (|2 F⁺ + η|² + |η|²) / 2 ≤ (r² / 16) d² + (r² / 4) |β|² + |η|² / 2`,
  -- with `d = 1 - |α|² - |β|²`, since `(1 - |α|² + |β|²)² + 4 |α|² |β|² = d² + 4 |β|²`.
  have hpt (x : M) : alternatingFormInner (TangentSpace I x) 2 (Fp.val x) (Fp.val x) ≤
      r ^ 2 / 16 * (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2 + r ^ 2 / 4 * ‖β x‖ ^ 2 +
        1 / 2 * alternatingFormInner (TangentSpace I x) 2 (η.val x) (η.val x) := by
    have h₀ := alternatingFormInner_self_nonneg (Fp.val x + η.val x)
    have hb := hFη x
    rw [show (1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) ^ 2 + 4 * ‖α x‖ ^ 2 * ‖β x‖ ^ 2 =
      (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2 + 4 * ‖β x‖ ^ 2 by ring] at hb
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      at h₀ hb
    linarith
  have hle := integral_mono (μ := riemannianVolume I M)
    (Continuous.integrable_of_compactSpace
      (Fp.isSmoothForm.contMDiff_alternatingFormInner Fp.isSmoothForm).continuous)
    (Continuous.integrable_of_compactSpace (by fun_prop)) hpt
  rw [integral_add (Continuous.integrable_of_compactSpace (f := fun x ↦
      r ^ 2 / 16 * (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2 + r ^ 2 / 4 * ‖β x‖ ^ 2) (by fun_prop))
      (Continuous.integrable_of_compactSpace (by fun_prop)),
    integral_add (Continuous.integrable_of_compactSpace (f := fun x ↦
      r ^ 2 / 16 * (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2) (by fun_prop))
      (Continuous.integrable_of_compactSpace (by fun_prop)),
    integral_const_mul, integral_const_mul, integral_const_mul] at hle
  -- Multiply `∫ |F|² = 2 ∫ |F⁺|² - ∫ F ∧ F` by `r⁻¹`.
  have hF2 : ∫ x, alternatingFormInner (TangentSpace I x) 2 (F.val x) (F.val x)
      ∂riemannianVolume I M ≤ r ^ 2 / 8 * ∫ x, (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2
        ∂riemannianVolume I M + r ^ 2 / 2 * ∫ x, ‖β x‖ ^ 2 ∂riemannianVolume I M +
      ∫ x, alternatingFormInner (TangentSpace I x) 2 (η.val x) (η.val x) ∂riemannianVolume I M -
        integralTopForm o (RoughForm.wedge F.val F.val) := by
    have hFc : F ∈ compactlySupportedForms I M 2 := by
      rw [compactlySupportedForms_eq_top]
      exact Submodule.mem_top
    linarith [SmoothForm.integral_inner_self_eq_two_mul_sub o even_two hFc]
  calc r⁻¹ * ∫ x, alternatingFormInner (TangentSpace I x) 2 (F.val x) (F.val x)
        ∂riemannianVolume I M
      ≤ r⁻¹ * (r ^ 2 / 8 * ∫ x, (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2 ∂riemannianVolume I M +
          r ^ 2 / 2 * ∫ x, ‖β x‖ ^ 2 ∂riemannianVolume I M +
          ∫ x, alternatingFormInner (TangentSpace I x) 2 (η.val x) (η.val x)
            ∂riemannianVolume I M -
          integralTopForm o (RoughForm.wedge F.val F.val)) :=
        mul_le_mul_of_nonneg_left hF2 (inv_nonneg.2 hr.le)
    _ = _ := by field_simp; ring

/-- **Taubes's scaled `L²` energy bound.** On a compact boundaryless Riemannian four-manifold `M`
with orientation `o`, let `ω` be a closed self-dual two-form, `F` a closed two-form and `η` a
two-form. Let `α`, `β`, `Dα`, `Dβ` be sections of families of seminormed groups, standing for the
components `α`, `β` of the normalized spinor and for `∇_a α`, `∇β`, with `|α|²` and `|β|²` of
class `C²` and `|∇_a α|²` continuous. Suppose that `1 ≤ r`, `0 ≤ K ≤ r` and
`256 c² ≤ r`, and that at every point

* `|α|² + |β|² ≤ 1 + K / r`;
* `-Δ|α|² / 2 + |∇_a α|² - (r / 4) (1 - |α|²) |α|² ≤ K₁`;
* `-Δ|β|² / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)`;
* `⟨ω, F⟩ / 2 = (r / 8) (1 - |α|² + |β|²) - ⟨ω, η⟩ / 4`;
* `|2 F⁺ + η|² ≤ (r² / 8) ((1 - |α|² + |β|²)² + 4 |α|² |β|²)`, where `F⁺ = (F + ⋆F) / 2`.

The last two are consequences of the curvature equation `F + ⋆F = (r / 4) ω - q(√r χ) - η` for
`F = i F_a`. Then, with all integrals against the Riemannian volume,

`r⁻¹ ∫ |F|² + ∫ |∇_a α|² + ∫ |∇β|² + r ∫ (1 - |α|² - |β|²)² ≤`
`2 (4 ⟨[F], [ω]⟩ + 2 ∫ ⟨ω, η⟩ + 2 K Vol(M)) + (5 / 3) K₁ Vol(M) + 2 Vol(M) +`
`(∫ |η|² - ∫ F ∧ F) / r`.

The right side does not depend on the solution: `⟨[F], [ω]⟩` and `∫ F ∧ F` depend only on the
de Rham class of `F`, which is `2π c₁(E)` for the curvature of a connection on the line `E`. -/
theorem inv_mul_integral_add_integral_add_integral_add_mul_integral_le
    (o : Manifold.Orientation I M (Fin (2 + 2))) {ω F η : SmoothForm I M ℝ 2}
    {α : (x : M) → A x} {β : (x : M) → B x} {Dα : (x : M) → F₁ x} {Dβ : (x : M) → F₂ x}
    {K K₁ c : ℝ} (hr : 1 ≤ r) (hK : 0 ≤ K) (hKr : K ≤ r) (hcr : 256 * c ^ 2 ≤ r)
    (hα : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖α x‖ ^ 2) (hβ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖β x‖ ^ 2)
    (hDα : Continuous fun x ↦ ‖Dα x‖ ^ 2) (hαβ : ∀ x, ‖α x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + K / r)
    (hWα : ∀ x, -(laplaceBeltrami I (fun y ↦ ‖α y‖ ^ 2) x / 2) + ‖Dα x‖ ^ 2 -
      r / 4 * (1 - ‖α x‖ ^ 2) * ‖α x‖ ^ 2 ≤ K₁)
    (hWβ : ∀ x, -laplaceBeltrami I (fun y ↦ ‖β y‖ ^ 2) x / 2 + ‖Dβ x‖ ^ 2 +
        r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤
      c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖))
    (hω : ω ∈ compactlySupportedClosedForms I M 2) (hω' : ω ∈ SmoothForm.selfDualForms o)
    (hF : F ∈ closedForms I M 2)
    (hFω : ∀ x, alternatingFormInner (TangentSpace I x) 2 (ω.val x) (F.val x) / 2 =
      r / 8 * (1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) -
        alternatingFormInner (TangentSpace I x) 2 (ω.val x) (η.val x) / 4)
    (hFη : ∀ x, alternatingFormInner (TangentSpace I x) 2
        ((2 : ℝ) • (SmoothForm.selfDualPart o F).val x + η.val x)
        ((2 : ℝ) • (SmoothForm.selfDualPart o F).val x + η.val x) ≤
      r ^ 2 / 8 * ((1 - ‖α x‖ ^ 2 + ‖β x‖ ^ 2) ^ 2 + 4 * ‖α x‖ ^ 2 * ‖β x‖ ^ 2)) :
    r⁻¹ * ∫ x, alternatingFormInner (TangentSpace I x) 2 (F.val x) (F.val x) ∂riemannianVolume I M +
        ∫ x, ‖Dα x‖ ^ 2 ∂riemannianVolume I M + ∫ x, ‖Dβ x‖ ^ 2 ∂riemannianVolume I M +
        r * ∫ x, (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2 ∂riemannianVolume I M ≤
      2 * (4 * poincarePairing I M o (deRhamCohomology.mk I 2 ⟨F, hF⟩)
            (compactlySupportedDeRhamCohomology.mk I 2 ⟨ω, hω⟩) +
          2 * ∫ x, alternatingFormInner (TangentSpace I x) 2 (ω.val x) (η.val x)
            ∂riemannianVolume I M +
          2 * K * riemannianTotalVolume I M) +
        5 / 3 * K₁ * riemannianTotalVolume I M + 2 * riemannianTotalVolume I M +
        (∫ x, alternatingFormInner (TangentSpace I x) 2 (η.val x) (η.val x) ∂riemannianVolume I M -
          integralTopForm o (RoughForm.wedge F.val F.val)) / r := by
  have hr0 : 0 < r := by linarith
  have hKr' : K / r ≤ 1 := (div_le_one hr0).2 hKr
  have hs : Continuous fun x ↦ ‖α x‖ ^ 2 := hα.continuous
  have ht : Continuous fun x ↦ ‖β x‖ ^ 2 := hβ.continuous
  have hst (x : M) : ‖α x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 2 := by linarith [hαβ x]
  have hc8 : 8 * c ≤ r :=
    (abs_le_of_sq_le_sq' (by nlinarith [mul_nonneg hr0.le (by linarith : (0 : ℝ) ≤ r - 1)])
      hr0.le).2
  -- The `L¹` defect bound and the `α` and `β` Weitzenböck inequalities.
  have hL := mul_integral_abs_one_sub_sub_le o hr0 hK hs ht hαβ hω hω' hF hFω
  have hA := integral_norm_sq_le_mul_add_mul_integral_of_laplaceBeltrami hα hDα hWα
  have hB := integral_norm_sq_add_mul_integral_norm_sq_le_of_laplaceBeltrami hr0 hc8 hs hβ hDα hWβ
  have hQ := inv_mul_integral_inner_self_le o hr0 hs ht hFη
  -- `∫ (1 - |α|²) |α|² ≤ 2 ∫ |1 - |α|² - |β|²| + 2 ∫ |β|²`.
  have hss := integral_one_sub_mul_le (I := I) hs ht hst
  -- `∫ (1 - |α|² - |β|²)² ≤ ∫ |1 - |α|² - |β|²|`, since the defect is at most one.
  have hD := integral_mono (μ := riemannianVolume I M)
    (Continuous.integrable_of_compactSpace (f := fun x ↦ (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2) ^ 2)
      (by fun_prop))
    (Continuous.integrable_of_compactSpace (f := fun x ↦ |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2|)
      (by fun_prop))
    fun x ↦ by
      have h := abs_one_sub_sub_le_one hr0 hKr (by positivity) (by positivity) (hαβ x)
      rw [← sq_abs]
      nlinarith [abs_nonneg (1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2)]
  -- `∫ |α|² ≤ 2 Vol(M)`.
  have hα₂ (x : M) : ‖α x‖ ^ 2 ≤ 2 := by nlinarith [hst x, sq_nonneg ‖β x‖]
  have hS := integral_mono (μ := riemannianVolume I M) hs.integrable_of_compactSpace
    (integrable_const (2 : ℝ)) hα₂
  rw [integral_const_riemannianVolume] at hS
  have hc32 : 8 * c ^ 2 / r ≤ 1 / 32 := by
    rw [div_le_iff₀ hr0]
    linarith
  have hAS : 0 ≤ ∫ x, ‖Dα x‖ ^ 2 ∂riemannianVolume I M + ∫ x, ‖α x‖ ^ 2 ∂riemannianVolume I M :=
    add_nonneg (integral_nonneg fun _ ↦ by positivity) (integral_nonneg fun _ ↦ by positivity)
  have hP₀ : 0 ≤ ∫ x, ‖Dβ x‖ ^ 2 ∂riemannianVolume I M := integral_nonneg fun _ ↦ by positivity
  have hS₀ : 0 ≤ ∫ x, ‖α x‖ ^ 2 ∂riemannianVolume I M := integral_nonneg fun _ ↦ by positivity
  have hL₀ : 0 ≤ r * ∫ x, |1 - ‖α x‖ ^ 2 - ‖β x‖ ^ 2| ∂riemannianVolume I M :=
    mul_nonneg hr0.le (integral_nonneg fun _ ↦ abs_nonneg _)
  -- The two Weitzenböck estimates close because `8 c² / r ≤ 1 / 32`.
  linarith [hB.trans (mul_le_mul_of_nonneg_right hc32 hAS),
    mul_le_mul_of_nonneg_left hss (by positivity : (0 : ℝ) ≤ r / 4),
    mul_le_mul_of_nonneg_left hD hr0.le]

end TauCeti.SeibergWitten
