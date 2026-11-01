/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Basic
public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# The energy identity for exact middle-degree forms

Let `M` be an oriented boundaryless Riemannian manifold of dimension `k + k` with `k` even, for
instance a four-manifold and `k = 2`. A compactly supported exact form `β = dα` of degree `k`
represents the zero de Rham class, so Stokes' theorem, through the Poincaré pairing, gives
`∫_M β ∧ β = 0`; and the wedge square is
`β ∧ β = (|β⁺|² - |β⁻|²) vol` (`TauCeti.RoughForm.wedge_self_apply`). Hence the self-dual and
anti-self-dual parts of `β` have the same energy:

`∫_M |β⁺|² vol = ∫_M |β⁻|² vol`, and so `∫_M |β|² vol = 2 ∫_M |β⁺|² vol`.

For the curvature `F = da` of a connection `d + a` on the trivial line bundle over a closed
four-manifold this is `‖F‖² = 2 ‖F⁺‖²`, the case `c₁ = 0` of `‖F_A‖² = 2 ‖F_A⁺‖² - 4π² c₁(L)²`.
It is also what identifies the kernel of the operator `(d*, d⁺)` on one-forms: if `(dα)⁺ = 0`
then `dα = 0`, so a one-form with `d*α = 0` and `(dα)⁺ = 0` is harmonic. The self-dual part of an
exact form is moreover `L²`-orthogonal to the closed self-dual forms, which constrains the range
of `d⁺`.

## Main results

* `TauCeti.SmoothForm.integralTopForm_inner_self_eq_add`:
  `∫_M |β|² vol = ∫_M |β⁺|² vol + ∫_M |β⁻|² vol` for every compactly supported `β`.
* `TauCeti.SmoothForm.integralTopForm_inner_selfDualPart_self_eq_antiSelfDualPart`: for a
  compactly supported exact `β`, `∫_M |β⁺|² vol = ∫_M |β⁻|² vol`.
* `TauCeti.SmoothForm.integralTopForm_inner_self_eq_two_mul_selfDualPart`,
  `TauCeti.SmoothForm.integralTopForm_inner_self_eq_two_mul_antiSelfDualPart`:
  `∫_M |β|² vol = 2 ∫_M |β^±|² vol`.
* `TauCeti.SmoothForm.eq_zero_of_mem_exactForms_of_selfDualPart_eq_zero`,
  `TauCeti.SmoothForm.eq_zero_of_mem_exactForms_of_antiSelfDualPart_eq_zero`: a compactly
  supported exact form with vanishing self-dual (or anti-self-dual) part vanishes.
* `TauCeti.SmoothForm.integralTopForm_inner_selfDualPart_eq_zero`: for an exact `β` and a
  compactly supported closed self-dual `γ`, `∫_M ⟨β⁺, γ⟩ vol = 0`.

## References

* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University
  Press (1990).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {k : ℕ} (o : Manifold.Orientation I M (Fin (k + k)))

namespace SmoothForm

/-! ### The energy identity -/

/-- **Pythagoras for the squared `L²` norm**: the squared `L²` norm of a compactly supported
middle-degree form on an oriented Riemannian manifold of dimension `k + k`, `k` even, is the sum
of the squared `L²` norms of its self-dual and anti-self-dual parts,
`∫_M |β|² vol = ∫_M |β⁺|² vol + ∫_M |β⁻|² vol`. -/
theorem integralTopForm_inner_self_eq_add (hk : Even k) {β : SmoothForm I M ℝ k}
    (hc : β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (β.1 x) (β.1 x) •
        riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o β).1 x) ((selfDualPart o β).1 x) • riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o β).1 x) ((antiSelfDualPart o β).1 x) • riemannianVolumeForm o x) := by
  rw [← integralTopForm_add o
    ((isSmoothForm_inner_smul_riemannianVolumeForm o rfl _ _).of_le bot_le)
    ((isSmoothForm_inner_smul_riemannianVolumeForm o rfl _ _).of_le bot_le)
    (isCompact_tsupport_inner_smul_riemannianVolumeForm o rfl
      (.inl (selfDualPart_mem_compactlySupportedForms o hc)))
    (isCompact_tsupport_inner_smul_riemannianVolumeForm o rfl
      (.inl (antiSelfDualPart_mem_compactlySupportedForms o hc)))]
  congr 1
  funext x
  rw [Pi.add_apply, ← add_smul, RoughForm.alternatingFormInner_self_eq_add o hk β.1 x,
    coe_selfDualPart, coe_antiSelfDualPart]

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The energy identity**: on an oriented boundaryless Riemannian manifold of dimension `k + k`
with `k` even, the self-dual and anti-self-dual parts of a compactly supported exact `k`-form `β`
have the same squared `L²` norm, `∫_M |β⁺|² vol = ∫_M |β⁻|² vol`. -/
theorem integralTopForm_inner_selfDualPart_self_eq_antiSelfDualPart (hk : Even k)
    {β : SmoothForm I M ℝ k} (hβ : β ∈ exactForms I M k) (hc : β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o β).1 x) ((selfDualPart o β).1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o β).1 x) ((antiSelfDualPart o β).1 x) • riemannianVolumeForm o x) := by
  -- By Stokes, `0 = ∫ β ∧ β = ∫ |β⁺|² vol - ∫ |β⁻|² vol`.
  have h0 := integralTopForm_wedge_eq_zero_of_mem_exactForms o hβ
    ((mem_compactlySupportedClosedForms I).2 ⟨hc, exactForms_le_closedForms I k hβ⟩)
  have hw : RoughForm.wedge β.1 β.1 =
      (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o β).1 x) ((selfDualPart o β).1 x) • riemannianVolumeForm o x) +
      (-1 : ℝ) • fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o β).1 x) ((antiSelfDualPart o β).1 x) • riemannianVolumeForm o x := by
    funext x
    ext v
    simp only [RoughForm.wedge_self_apply o hk, coe_selfDualPart, coe_antiSelfDualPart,
      Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  rw [hw, integralTopForm_add o
    ((isSmoothForm_inner_smul_riemannianVolumeForm o rfl _ _).of_le bot_le)
    (((isSmoothForm_inner_smul_riemannianVolumeForm o rfl _ _).of_le bot_le).smul _)
    (isCompact_tsupport_inner_smul_riemannianVolumeForm o rfl
      (.inl (selfDualPart_mem_compactlySupportedForms o hc)))
    ((isCompact_tsupport_inner_smul_riemannianVolumeForm o rfl
      (.inl (antiSelfDualPart_mem_compactlySupportedForms o hc))).of_isClosed_subset
        (isClosed_tsupport _) (RoughForm.tsupport_smul_subset _ _)),
    integralTopForm_smul] at h0
  linarith

/-- The squared `L²` norm of a compactly supported exact form `β` of degree `k`, on an oriented
boundaryless Riemannian manifold of dimension `k + k` with `k` even, is twice the squared `L²`
norm of its self-dual part: `∫_M |β|² vol = 2 ∫_M |β⁺|² vol`. -/
theorem integralTopForm_inner_self_eq_two_mul_selfDualPart (hk : Even k)
    {β : SmoothForm I M ℝ k} (hβ : β ∈ exactForms I M k)
    (hc : β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (β.1 x) (β.1 x) •
        riemannianVolumeForm o x) =
      2 * integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((selfDualPart o β).1 x) ((selfDualPart o β).1 x) • riemannianVolumeForm o x) := by
  rw [integralTopForm_inner_self_eq_add o hk hc,
    ← integralTopForm_inner_selfDualPart_self_eq_antiSelfDualPart o hk hβ hc]
  ring

/-- The squared `L²` norm of a compactly supported exact form `β` of degree `k`, on an oriented
boundaryless Riemannian manifold of dimension `k + k` with `k` even, is twice the squared `L²`
norm of its anti-self-dual part: `∫_M |β|² vol = 2 ∫_M |β⁻|² vol`. -/
theorem integralTopForm_inner_self_eq_two_mul_antiSelfDualPart (hk : Even k)
    {β : SmoothForm I M ℝ k} (hβ : β ∈ exactForms I M k)
    (hc : β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (β.1 x) (β.1 x) •
        riemannianVolumeForm o x) =
      2 * integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((antiSelfDualPart o β).1 x) ((antiSelfDualPart o β).1 x) • riemannianVolumeForm o x) := by
  rw [integralTopForm_inner_self_eq_add o hk hc,
    integralTopForm_inner_selfDualPart_self_eq_antiSelfDualPart o hk hβ hc]
  ring

/-- A compactly supported exact form of even degree `k` on an oriented boundaryless Riemannian
manifold of dimension `k + k` whose self-dual part vanishes is zero. For `k = 2`: if `(dα)⁺ = 0`
for a compactly supported one-form `α` on a four-manifold, then `dα = 0`. -/
theorem eq_zero_of_mem_exactForms_of_selfDualPart_eq_zero (hk : Even k)
    {β : SmoothForm I M ℝ k} (hβ : β ∈ exactForms I M k)
    (hc : β ∈ compactlySupportedForms I M k) (h : selfDualPart o β = 0) : β = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk₀
  · rwa [exactForms_zero, Submodule.mem_bot] at hβ
  have : NeZero (k + k) := ⟨by omega⟩
  rw [← (integralTopForm_inner_self_eq_zero_iff o rfl hc),
    integralTopForm_inner_self_eq_two_mul_selfDualPart o hk hβ hc, h]
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, map_zero, zero_smul]
  exact mul_eq_zero_of_right 2 (integralTopForm_zero o)

/-- A compactly supported exact form of even degree `k` on an oriented boundaryless Riemannian
manifold of dimension `k + k` whose anti-self-dual part vanishes is zero. -/
theorem eq_zero_of_mem_exactForms_of_antiSelfDualPart_eq_zero (hk : Even k)
    {β : SmoothForm I M ℝ k} (hβ : β ∈ exactForms I M k)
    (hc : β ∈ compactlySupportedForms I M k) (h : antiSelfDualPart o β = 0) : β = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk₀
  · rwa [exactForms_zero, Submodule.mem_bot] at hβ
  have : NeZero (k + k) := ⟨by omega⟩
  rw [← (integralTopForm_inner_self_eq_zero_iff o rfl hc),
    integralTopForm_inner_self_eq_two_mul_antiSelfDualPart o hk hβ hc, h]
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, map_zero, zero_smul]
  exact mul_eq_zero_of_right 2 (integralTopForm_zero o)

/-! ### Orthogonality to closed self-dual forms -/

/-- **The self-dual part of an exact form is orthogonal to the closed self-dual forms**: on an
oriented boundaryless Riemannian manifold of dimension `k + k` with `k` even, for an exact
`k`-form `β` and a compactly supported closed self-dual `k`-form `γ`,
`∫_M ⟨β⁺, γ⟩ vol = 0`. -/
theorem integralTopForm_inner_selfDualPart_eq_zero (hk : Even k) {β : SmoothForm I M ℝ k}
    (hβ : β ∈ exactForms I M k) {γ : SmoothForm I M ℝ k}
    (hγ : γ ∈ compactlySupportedClosedForms I M k) (hγ' : hodgeStar o rfl γ = γ) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((selfDualPart o β).1 x) (γ.1 x) • riemannianVolumeForm o x) = 0 := by
  -- Pointwise `⟨β⁺, γ⟩ = ⟨β, γ⟩`, since `β⁻` is orthogonal to the self-dual `γ`, and
  -- `⟨β, γ⟩ vol = β ∧ ⋆γ = β ∧ γ`.
  have hγr : γ.1 ∈ RoughForm.selfDualForms o :=
    RoughForm.mem_selfDualForms.2 (by rw [← coe_hodgeStar, hγ'])
  have h : (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((selfDualPart o β).1 x) (γ.1 x) • riemannianVolumeForm o x) =
      RoughForm.wedge β.1 γ.1 := by
    funext x
    ext v
    have hanti := RoughForm.alternatingFormInner_eq_zero_of_mem_selfDualForms o hγr
      ((RoughForm.isProj_antiSelfDualPart o hk).map_mem β.1) x
    have hinner : alternatingFormInner (TangentSpace I x) k ((selfDualPart o β).1 x) (γ.1 x) =
        alternatingFormInner (TangentSpace I x) k (β.1 x) (γ.1 x) := by
      conv_rhs => rw [← selfDualPart_add_antiSelfDualPart o β]
      rw [Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply, coe_antiSelfDualPart,
        alternatingFormInner_comm (RoughForm.antiSelfDualPart o β.1 x), hanti, add_zero]
    have hd := congrFun (inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o rfl β γ) x
    rw [hγ'] at hd
    rw [hinner, hd, cast_apply, coe_wedge]
    simp only [Function.comp_def, Fin.cast_eq_self]
  rw [h]
  exact integralTopForm_wedge_eq_zero_of_mem_exactForms o hβ hγ

end SmoothForm

end TauCeti
