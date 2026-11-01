/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SelfDual.Energy

/-!
# The connection part of the Seiberg–Witten deformation operator

On an oriented Riemannian four-manifold `X`, the Coulomb gauge-fixed linearization of the
Seiberg–Witten equations in the direction of an imaginary one-form `a` is, up to terms of order
zero in `a` that vanish at a reducible configuration `ψ = 0`, the first-order operator

`T = (-2 d*, d⁺) : iΩ¹(X) → iΩ⁰(X) ⊕ iΩ⁺(X)`, `T a = (-2 d*a, (da)⁺)`,

where `d*` is the codifferential and `(da)⁺ = (da + ⋆da) / 2` the self-dual part of `da`. The
factor `-2` comes from the active `Spinᶜ` gauge convention `A ↦ A - 2 u⁻¹ du`, whose
infinitesimal action on connections is `ξ ↦ -2 dξ`, with formal adjoint `-2 d*`. As elsewhere,
imaginary forms are indexed by real forms, so `T` is a real-linear map from real one-forms to
pairs of a real function and a real self-dual two-form
(`TauCeti.SeibergWitten.connectionDeformation`).

On a closed four-manifold this file identifies the kernel of `T` with the harmonic one-forms,
`ker T = {a | da = 0, d*a = 0}`. The inclusion `⊇` is immediate; conversely `(da)⁺ = 0` forces
`da = 0` because `∫_X |(da)⁺|² = ∫_X |(da)⁻|²` for the exact form `da`
(`TauCeti.SmoothForm.integralTopForm_inner_selfDualPart_self_eq_antiSelfDualPart`). It also shows
that the range of `T` is `L²`-orthogonal to the closed functions and the closed self-dual
two-forms: for `df = 0`, `∫_X ⟨f, -2 d*a⟩ vol = -2 ∫_X ⟨df, a⟩ vol = 0`, and for a closed
self-dual `γ`, `∫_X ⟨(da)⁺, γ⟩ vol = ∫_X da ∧ γ = 0`. These are the harmonic functions and the
harmonic self-dual two-forms, so `H⁰ ⊕ H⁺` lies in the `L²`-orthogonal complement of the range
of `T`. That it is the whole complement, and the resulting index `b₁ - 1 - b₂⁺`, need the Hodge
decomposition and are not proved here.

## Main definitions

* `TauCeti.SeibergWitten.connectionDeformation o`: the operator `T a = (-2 d*a, (da)⁺)` from
  smooth one-forms to pairs of a smooth function and a smooth self-dual two-form
  (`TauCeti.SmoothForm.selfDualForms`).

## Main results

* `TauCeti.SeibergWitten.connectionDeformation_eq_zero_iff`: for a one-form `a` with compactly
  supported `da`, `T a = 0` if and only if `da = 0` and `d*a = 0`; on a compact manifold,
  `TauCeti.SeibergWitten.ker_connectionDeformation` states this as an equality of kernels.
* `TauCeti.SeibergWitten.integralTopForm_inner_connectionDeformation_fst_eq_zero`,
  `TauCeti.SeibergWitten.integralTopForm_inner_connectionDeformation_snd_eq_zero`: on a closed
  four-manifold, the range of `T` is `L²`-orthogonal to the closed functions and to the closed
  self-dual two-forms.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford University
  Press (1990).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.SeibergWitten

open SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2)))

/-- The connection part `T a = (-2 d*a, (da)⁺)` of the Seiberg–Witten deformation operator on an
oriented Riemannian four-manifold, from one-forms to pairs of a function and a self-dual
two-form. -/
def connectionDeformation :
    SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I M ℝ 0 × selfDualForms o :=
  ((-2 : ℝ) • codifferential o (k := 0) (l := 3) rfl).prod
    ((selfDualPart o ∘ₗ mextDerivₗ I 1).codRestrict (selfDualForms o) fun _ ↦
      selfDualPart_mem_selfDualForms o even_two _)

/-- The first component of `T a` is `-2 d*a`. -/
@[simp]
theorem connectionDeformation_apply_fst (a : SmoothForm I M ℝ 1) :
    (connectionDeformation o a).1 = (-2 : ℝ) • codifferential o (k := 0) (l := 3) rfl a :=
  (rfl)

/-- The second component of `T a` is `(da)⁺`. -/
@[simp]
theorem connectionDeformation_apply_snd (a : SmoothForm I M ℝ 1) :
    ((connectionDeformation o a).2 : SmoothForm I M ℝ 2) = selfDualPart o (mextDerivₗ I 1 a) :=
  (rfl)

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The kernel of `T`**: on an oriented boundaryless Riemannian four-manifold, a one-form `a`
with compactly supported `da` satisfies `T a = 0` exactly when `da = 0` and `d*a = 0`, that is,
when `a` is harmonic. -/
theorem connectionDeformation_eq_zero_iff {a : SmoothForm I M ℝ 1}
    (ha : mextDerivₗ I 1 a ∈ compactlySupportedForms I M 2) :
    connectionDeformation o a = 0 ↔
      mextDerivₗ I 1 a = 0 ∧ codifferential o (k := 0) (l := 3) rfl a = 0 := by
  rw [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero,
    ← Submodule.coe_eq_zero (x := (connectionDeformation o a).2),
    connectionDeformation_apply_fst, connectionDeformation_apply_snd, smul_eq_zero, and_comm]
  simp only [neg_eq_zero, OfNat.ofNat_ne_zero, false_or]
  refine and_congr_left fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  exact eq_zero_of_mem_exactForms_of_selfDualPart_eq_zero o even_two
    (by rw [exactForms_succ]; exact LinearMap.mem_range_self _ a) ha h

/-- **The kernel of `T` on a closed four-manifold** is the space of harmonic one-forms,
`ker T = ker d ∩ ker d*`. -/
theorem ker_connectionDeformation [CompactSpace M] :
    LinearMap.ker (connectionDeformation o) =
      LinearMap.ker (mextDerivₗ I 1) ⊓
        LinearMap.ker (codifferential o (k := 0) (l := 3) rfl) := by
  ext a
  rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.mem_ker,
    connectionDeformation_eq_zero_iff o (by simp [compactlySupportedForms_eq_top])]

/-- **The range of `T` is orthogonal to the closed functions**: on a closed oriented Riemannian
four-manifold, `∫_X ⟨f, -2 d*a⟩ vol = 0` for every one-form `a` and every function `f` with
`df = 0`. -/
theorem integralTopForm_inner_connectionDeformation_fst_eq_zero [CompactSpace M]
    (a : SmoothForm I M ℝ 1) {f : SmoothForm I M ℝ 0} (hf : mextDerivₗ I 0 f = 0) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 0 (f.1 x)
      ((connectionDeformation o a).1.1 x) • riemannianVolumeForm o x) = 0 := by
  have h := integralTopForm_inner_mextDeriv_eq_inner_codifferential o (k := 0) (l := 3) rfl f a
    (.inl (by simp [compactlySupportedForms_eq_top]))
  rw [hf] at h
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, map_zero, LinearMap.zero_apply,
    zero_smul] at h
  simp only [connectionDeformation_apply_fst, Submodule.coe_smul, Pi.smul_apply, map_smul,
    smul_eq_mul, mul_smul]
  rw [← Pi.smul_def, integralTopForm_smul, ← h]
  exact mul_eq_zero_of_right _ (integralTopForm_zero o)

/-- **The range of `T` is orthogonal to the closed self-dual two-forms**: on a closed oriented
Riemannian four-manifold, `∫_X ⟨(da)⁺, γ⟩ vol = 0` for every one-form `a` and every closed
self-dual two-form `γ`. -/
theorem integralTopForm_inner_connectionDeformation_snd_eq_zero [CompactSpace M]
    (a : SmoothForm I M ℝ 1) {γ : SmoothForm I M ℝ 2} (hγ : mextDerivₗ I 2 γ = 0)
    (hγ' : hodgeStar o rfl γ = γ) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) 2
      (((connectionDeformation o a).2 : SmoothForm I M ℝ 2).1 x) (γ.1 x) •
        riemannianVolumeForm o x) = 0 := by
  rw [connectionDeformation_apply_snd]
  exact integralTopForm_inner_selfDualPart_eq_zero o even_two
    (by rw [exactForms_succ]; exact LinearMap.mem_range_self _ a)
    ((mem_compactlySupportedClosedForms I).2 ⟨by simp [compactlySupportedForms_eq_top],
      (mem_closedForms_iff_mextDerivₗ_eq_zero I γ).2 hγ⟩) hγ'

end TauCeti.SeibergWitten
