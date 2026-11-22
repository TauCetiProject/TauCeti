/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
import TauCeti.Geometry.Manifold.DeRham.DegreeZero
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Regularity
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

/-!
# The global Coulomb gauge for one-forms on a closed Riemannian manifold

On an oriented Riemannian manifold `M` of dimension `m ≥ 1`, write `d*` for the codifferential
(`TauCeti.SmoothForm.codifferential`). This file proves that on a closed connected manifold every
smooth one-form `a` is, uniquely, an exact form plus a coclosed form:

`a = df + b`,   `d*b = 0`,

with `f` smooth and of integral zero, and that the two summands are `L²`-orthogonal. The
orthogonality, the uniqueness of the coclosed summand and the `L²` estimate below hold in every
degree, for a `(k + 1)`-form `a` and a `k`-form `α` in place of `f`, on any boundaryless manifold
when the forms involved are compactly supported.

* **The codifferential of a one-form has integral zero**: `∫_M d*a vol = 0` for a compactly
  supported one-form `a` on a boundaryless manifold
  (`TauCeti.SmoothForm.integral_codifferential_eq_zero`). It is the formal adjoint identity
  `∫_M ⟨dα, a⟩ vol = ∫_M ⟨α, d*a⟩ vol` for the constant function `α = 1`.
* **Existence**: on a closed connected manifold, `d*a` is therefore a smooth function of integral
  zero, so it is `Δf = d*df` for a smooth function `f` of integral zero, by the smooth Poisson
  equation (`TauCeti.Manifold.SobolevH1.exists_neg_laplaceBeltrami_eq`), and then
  `d*(a - df) = 0` (`TauCeti.SmoothForm.exists_codifferential_sub_mextDerivₗ_eq_zero`).
* **Uniqueness**: if `a - df` and `a - dg` are both coclosed, then `d*d(f - g) = 0`, so `f - g` is
  closed, by Green's formula `∫_M ⟨d*dγ, γ⟩ vol = ∫_M |dγ|² vol`, and the two coclosed forms agree
  (`TauCeti.SmoothForm.mextDerivₗ_eq_of_codifferential_sub_eq_zero`); on a connected manifold
  `f - g` is then constant, hence zero when `f` and `g` both have integral zero
  (`TauCeti.SmoothForm.existsUnique_codifferential_sub_mextDerivₗ_eq_zero`).
* **Orthogonality**: exact forms are `L²`-orthogonal to coclosed forms,
  `∫_M ⟨df, b⟩ vol = ∫_M ⟨f, d*b⟩ vol = 0`
  (`TauCeti.SmoothForm.integralTopForm_inner_mextDerivₗ_eq_zero_of_codifferential_eq_zero`).
* **The `L²` estimate**: hence
  `∫_M |a|² vol = ∫_M |a - df|² vol + ∫_M |df|² vol` when `d*(a - df) = 0`
  (`TauCeti.SmoothForm.integralTopForm_inner_self_eq_add_of_codifferential_sub_eq_zero`), so both
  summands have `L²` norm at most that of `a`
  (`TauCeti.SmoothForm.integralTopForm_inner_self_sub_le_of_codifferential_sub_eq_zero`,
  `TauCeti.SmoothForm.integralTopForm_inner_self_mextDerivₗ_le_of_codifferential_sub_eq_zero`).
  The coclosed summand `a - df` is the `L²`-orthogonal projection of `a` onto the coclosed forms.

In abelian gauge theory, for a `U(1)` connection `A₀ + a` with `a = i b` imaginary, a gauge
transformation `u = exp (i ξ)` acting on the determinant connection by `A ↦ A - 2 u⁻¹ du` changes
`b` to `b - 2 dξ`. Taking `ξ = f / 2` for the function `f` of `b` above puts the connection in the
**global Coulomb gauge** `d*(A - A₀) = 0`, the gauge condition of the Seiberg–Witten equations,
through a gauge transformation in the identity component, unique up to constant phases.

## Main results

* `TauCeti.SmoothForm.integralTopForm_codifferential_smul_riemannianVolumeForm_eq_zero`,
  `TauCeti.SmoothForm.integral_codifferential_eq_zero`: `∫_M d*a vol = 0`, as the integral of a
  top form and against the Riemannian measure.
* `TauCeti.SmoothForm.integralTopForm_inner_mextDerivₗ_eq_zero_of_codifferential_eq_zero`: exact
  one-forms are `L²`-orthogonal to coclosed one-forms.
* `TauCeti.SmoothForm.exists_codifferential_sub_mextDerivₗ_eq_zero`: every one-form on a closed
  connected manifold is `df` plus a coclosed form, with `f` of integral zero.
* `TauCeti.SmoothForm.mextDerivₗ_eq_of_codifferential_sub_eq_zero`: the coclosed summand is unique.
* `TauCeti.SmoothForm.existsUnique_codifferential_sub_mextDerivₗ_eq_zero`: the function `f` of
  integral zero is unique.
* `TauCeti.SmoothForm.integralTopForm_inner_self_eq_add_of_codifferential_sub_eq_zero`: the
  Pythagorean identity `‖a‖² = ‖a - df‖² + ‖df‖²` in `L²`, with its consequences
  `TauCeti.SmoothForm.integralTopForm_inner_self_sub_le_of_codifferential_sub_eq_zero` and
  `TauCeti.SmoothForm.integralTopForm_inner_self_mextDerivₗ_le_of_codifferential_sub_eq_zero`.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), Chapter 6 (the Hodge decomposition).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press (1996) (the global Coulomb
  gauge).
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m l : ℕ} (o : Manifold.Orientation I M (Fin m))

/-! ### Exact forms are orthogonal to coclosed forms -/

section Boundaryless

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] {k : ℕ}
  (hkl : k + 1 + l = m)

/-- **Exact forms are `L²`-orthogonal to coclosed forms**: on an oriented boundaryless Riemannian
manifold, `∫_M ⟨dα, b⟩ vol = 0` for a smooth `k`-form `α` and a smooth `(k + 1)`-form `b` with
`d*b = 0`, one of them compactly supported. -/
theorem integralTopForm_inner_mextDerivₗ_eq_zero_of_codifferential_eq_zero
    (α : SmoothForm I M ℝ k) {b : SmoothForm I M ℝ (k + 1)} (hb : codifferential o hkl b = 0)
    (h : α ∈ compactlySupportedForms I M k ∨ b ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
      ((mextDerivₗ I k α).val x) (b.val x) • riemannianVolumeForm o x) = 0 := by
  rw [integralTopForm_inner_mextDeriv_eq_inner_codifferential o hkl α b h, hb]
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, map_zero, zero_smul]
  exact integralTopForm_zero o

/-- **The coclosed summand is unique**: on an oriented boundaryless Riemannian manifold, if both
`a - dα` and `a - dβ` are coclosed and `α - β` is compactly supported, then `dα = dβ`, so the two
coclosed forms agree. -/
theorem mextDerivₗ_eq_of_codifferential_sub_eq_zero {a : SmoothForm I M ℝ (k + 1)}
    {α β : SmoothForm I M ℝ k} (hα : codifferential o hkl (a - mextDerivₗ I k α) = 0)
    (hβ : codifferential o hkl (a - mextDerivₗ I k β) = 0)
    (hαβ : α - β ∈ compactlySupportedForms I M k) :
    mextDerivₗ I k α = mextDerivₗ I k β := by
  have : NeZero m := ⟨by omega⟩
  -- `d*d(α - β) = d*((a - dβ) - (a - dα)) = 0`, so `∫_M |d(α - β)|² vol = 0` by Green's formula.
  have hdd : codifferential o hkl (mextDerivₗ I k (α - β)) = 0 := by
    rw [map_sub, show mextDerivₗ I k α - mextDerivₗ I k β =
      (a - mextDerivₗ I k β) - (a - mextDerivₗ I k α) by abel, map_sub, hα, hβ, sub_zero]
  have h := integralTopForm_inner_codifferential_mextDeriv o hkl (α - β) (α - β) (.inl hαβ)
  rw [hdd, integralTopForm_inner_zero_left, eq_comm,
    integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o hkl
      (mextDerivₗ_mem_compactlySupportedForms I hαβ), map_sub, sub_eq_zero] at h
  exact h

/-- **The Pythagorean identity of the decomposition `a = dα + (a - dα)`**: on an oriented
boundaryless Riemannian manifold, if `a - dα` is coclosed, with `a` and `α` compactly supported,
then `∫_M |a|² vol = ∫_M |a - dα|² vol + ∫_M |dα|² vol`. -/
theorem integralTopForm_inner_self_eq_add_of_codifferential_sub_eq_zero
    {a : SmoothForm I M ℝ (k + 1)} {α : SmoothForm I M ℝ k}
    (hα : codifferential o hkl (a - mextDerivₗ I k α) = 0)
    (ha : a ∈ compactlySupportedForms I M (k + 1)) (hαc : α ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1) (a.val x)
        (a.val x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
          ((a - mextDerivₗ I k α).val x) ((a - mextDerivₗ I k α).val x) •
        riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
          ((mextDerivₗ I k α).val x) ((mextDerivₗ I k α).val x) • riemannianVolumeForm o x) := by
  set b := a - mextDerivₗ I k α
  set c := mextDerivₗ I k α
  have hc : c ∈ compactlySupportedForms I M (k + 1) := mextDerivₗ_mem_compactlySupportedForms I hαc
  have hb : b ∈ compactlySupportedForms I M (k + 1) := Submodule.sub_mem _ ha hc
  -- The cross terms vanish by orthogonality of exact and coclosed forms.
  have hcb := integralTopForm_inner_mextDerivₗ_eq_zero_of_codifferential_eq_zero o hkl α hα
    (.inl hαc)
  have hbc : integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1) (b.val x)
      (c.val x) • riemannianVolumeForm o x) = 0 := by
    rw [RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm]
    exact hcb
  have hab : a = b + c := (sub_add_cancel a c).symm
  rw [hab, integralTopForm_inner_add_left o hkl b c (b + c) (.inl ⟨hb, hc⟩),
    RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm o b.val,
    RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm o c.val,
    integralTopForm_inner_add_left o hkl b c b (.inl ⟨hb, hc⟩),
    integralTopForm_inner_add_left o hkl b c c (.inl ⟨hb, hc⟩), hcb, hbc, add_zero, zero_add]

/-- **The coclosed summand has smaller `L²` norm**: on an oriented boundaryless Riemannian
manifold, if `a - dα` is coclosed, with `a` and `α` compactly supported, then
`∫_M |a - dα|² vol ≤ ∫_M |a|² vol`. -/
theorem integralTopForm_inner_self_sub_le_of_codifferential_sub_eq_zero
    {a : SmoothForm I M ℝ (k + 1)} {α : SmoothForm I M ℝ k}
    (hα : codifferential o hkl (a - mextDerivₗ I k α) = 0)
    (ha : a ∈ compactlySupportedForms I M (k + 1)) (hαc : α ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((a - mextDerivₗ I k α).val x) ((a - mextDerivₗ I k α).val x) •
      riemannianVolumeForm o x) ≤
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1) (a.val x)
        (a.val x) • riemannianVolumeForm o x) := by
  have : NeZero m := ⟨by omega⟩
  rw [integralTopForm_inner_self_eq_add_of_codifferential_sub_eq_zero o hkl hα ha hαc]
  exact le_add_of_nonneg_right
    (RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg o _)

/-- **The exact summand has smaller `L²` norm**: on an oriented boundaryless Riemannian manifold,
if `a - dα` is coclosed, with `a` and `α` compactly supported, then
`∫_M |dα|² vol ≤ ∫_M |a|² vol`. -/
theorem integralTopForm_inner_self_mextDerivₗ_le_of_codifferential_sub_eq_zero
    {a : SmoothForm I M ℝ (k + 1)} {α : SmoothForm I M ℝ k}
    (hα : codifferential o hkl (a - mextDerivₗ I k α) = 0)
    (ha : a ∈ compactlySupportedForms I M (k + 1)) (hαc : α ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((mextDerivₗ I k α).val x) ((mextDerivₗ I k α).val x) • riemannianVolumeForm o x) ≤
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1) (a.val x)
        (a.val x) • riemannianVolumeForm o x) := by
  have : NeZero m := ⟨by omega⟩
  rw [integralTopForm_inner_self_eq_add_of_codifferential_sub_eq_zero o hkl hα ha hαc]
  exact le_add_of_nonneg_left
    (RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg o _)

end Boundaryless

/-! ### The codifferential of a one-form has integral zero -/

section IntegralZero

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] (hkl : 0 + 1 + l = m)

/-- **The codifferential of a one-form has integral zero**: on an oriented boundaryless Riemannian
manifold, `∫_M d*a vol = 0` for every compactly supported smooth one-form `a`. -/
theorem integralTopForm_codifferential_smul_riemannianVolumeForm_eq_zero
    {a : SmoothForm I M ℝ 1} (ha : a ∈ compactlySupportedForms I M 1) :
    integralTopForm o (fun x ↦ (codifferential o hkl a).val x 0 • riemannianVolumeForm o x) =
      0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  -- Pair `a` with the exterior derivative of the constant function `1`.
  have h := integralTopForm_inner_mextDeriv_eq_inner_codifferential o hkl
    (ofFunction (ContMDiffMap.const 1 : C^∞⟮I, M; ℝ⟯)) a (.inr ha)
  rw [mextDerivₗ_ofFunction_const, integralTopForm_inner_zero_left] at h
  rw [h]
  congr 1
  funext x
  rw [alternatingFormInner_zero_apply _ _ 0, coe_ofFunction, RoughForm.ofFunction_apply,
    ContMDiffMap.const_apply, one_mul]

end IntegralZero

/-! ### Integrals against the Riemannian measure -/

-- The Riemannian volume measure is stated for a continuous metric.
local instance instIsContinuousRiemannianBundleOfContMDiff :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)

section Measure

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [MeasurableSpace M]
  [BorelSpace M] (hkl : 0 + 1 + l = m)

/-- **The codifferential of a one-form has integral zero**: on an oriented boundaryless Riemannian
manifold, the function `d*a` of a compactly supported smooth one-form `a` has integral zero
against the Riemannian volume measure. -/
theorem integral_codifferential_eq_zero {a : SmoothForm I M ℝ 1}
    (ha : a ∈ compactlySupportedForms I M 1) :
    ∫ x, (codifferential o hkl a).val x 0 ∂riemannianVolume I M = 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  -- `d*a` is supported in the support of `a`; evaluate it on the empty tuple.
  have hda : HasCompactSupport (β := E [⋀^Fin 0]→L[ℝ] ℝ) (codifferential o hkl a).val :=
    ((mem_compactlySupportedForms I).1 ha).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_codifferential_subset o hkl a)
  have hsupp : HasCompactSupport fun x ↦ (codifferential o hkl a).val x 0 :=
    hda.comp_left (g := fun T : E [⋀^Fin 0]→L[ℝ] ℝ ↦ T 0) (by simp)
  rw [← integralTopForm_smul_riemannianVolumeForm o
    (contMDiff_apply_zero (codifferential o hkl a)).continuous hsupp]
  exact integralTopForm_codifferential_smul_riemannianVolumeForm_eq_zero o hkl ha

end Measure

/-! ### Existence and uniqueness on a closed connected manifold -/

section Closed

variable [I.Boundaryless] [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  (hkl : 0 + 1 + l = m)

/-- **The global Coulomb gauge for one-forms**: on a closed connected oriented Riemannian manifold
of positive dimension, every smooth one-form `a` is `df` plus a coclosed form, `d*(a - df) = 0`,
for a smooth function `f` of integral zero. The function `f` solves `Δf = d*a`, by the smooth
Poisson equation. -/
theorem exists_codifferential_sub_mextDerivₗ_eq_zero [PreconnectedSpace M]
    (a : SmoothForm I M ℝ 1) :
    ∃ f : SmoothForm I M ℝ 0, ∫ x, f.val x 0 ∂riemannianVolume I M = 0 ∧
      codifferential o hkl (a - mextDerivₗ I 0 f) = 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨u, hu₀, hu⟩ := Manifold.SobolevH1.exists_neg_laplaceBeltrami_eq
    (contMDiff_apply_zero (codifferential o hkl a))
    (integral_codifferential_eq_zero o hkl (by simp [compactlySupportedForms_eq_top]))
  refine ⟨ofFunction u, by rwa [ofFunction_apply_zero], ?_⟩
  -- `d*df = Δf = -div grad u = d*a`.
  have hΔ : codifferential o hkl (mextDerivₗ I 0 (ofFunction u)) = codifferential o hkl a := by
    rw [← hodgeLaplacian_zero_add_one o (show 0 + (l + 1) = m by omega) hkl]
    apply Subtype.ext
    rw [hodgeLaplacian_eq_ofFunction_neg_laplaceBeltrami, ofFunction_apply_zero,
      RoughForm.eq_ofFunction (codifferential o hkl a).val]
    congr 1
    funext x
    exact hu x
  rw [map_sub, hΔ, sub_self]

/-- **Uniqueness of the global Coulomb gauge**: on a closed connected oriented Riemannian manifold
of positive dimension, for every smooth one-form `a` there is exactly one smooth function `f` of
integral zero with `d*(a - df) = 0`. -/
theorem existsUnique_codifferential_sub_mextDerivₗ_eq_zero [PreconnectedSpace M]
    (a : SmoothForm I M ℝ 1) :
    ∃! f : SmoothForm I M ℝ 0, ∫ x, f.val x 0 ∂riemannianVolume I M = 0 ∧
      codifferential o hkl (a - mextDerivₗ I 0 f) = 0 := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨f, hf₀, hf⟩ := exists_codifferential_sub_mextDerivₗ_eq_zero o hkl a
  refine ⟨f, ⟨hf₀, hf⟩, fun g ⟨hg₀, hg⟩ ↦ ?_⟩
  have hd := mextDerivₗ_eq_of_codifferential_sub_eq_zero o hkl hg hf
    (by simp [compactlySupportedForms_eq_top])
  -- `g - f` is closed, hence constant, and has integral zero.
  have hc : IsLocallyConstant fun x ↦ (g - f).val x 0 := by
    rw [← mem_closedForms_zero_iff, mem_closedForms_iff_mextDerivₗ_eq_zero, map_sub, hd,
      sub_self]
  have hint (φ : SmoothForm I M ℝ 0) : Integrable (fun x ↦ φ.val x 0) (riemannianVolume I M) :=
    (contMDiff_apply_zero φ).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h₀ : ∫ x, (g - f).val x 0 ∂riemannianVolume I M = 0 := by
    simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
    rw [integral_sub (hint g) (hint f), hg₀, hf₀, sub_zero]
  rw [← sub_eq_zero]
  apply Subtype.ext
  funext x
  ext v
  obtain rfl : v = 0 := Subsingleton.elim v 0
  rw [ZeroMemClass.coe_zero, Pi.zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  have hconst : ∀ y, (g - f).val y 0 = (g - f).val x 0 := fun y ↦
    hc.apply_eq_of_preconnectedSpace y x
  rw [integral_congr_ae (Filter.Eventually.of_forall hconst), integral_const, smul_eq_mul] at h₀
  have hvol : 0 < (riemannianVolume I M).real Set.univ :=
    ENNReal.toReal_pos (isOpen_univ.measure_pos _ ⟨x, Set.mem_univ x⟩).ne'
      (measure_ne_top _ _)
  simpa using (mul_eq_zero.1 h₀).resolve_left hvol.ne'

end Closed

end TauCeti.SmoothForm
