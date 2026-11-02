/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import TauCeti.Geometry.Manifold.Riemannian.SelfDual

/-!
# The abelian deformation operator of the Seiberg–Witten equations

On an oriented Riemannian four-manifold `X`, the Seiberg–Witten equations for a pair `(A, ψ)`
impose the curvature equation `F_A⁺ = q(ψ) + η` and are gauge fixed on the Coulomb slice
`d*(A - A₀) = 0`. Varying only the imaginary connection form `a`, with the spinor held at zero,
gives the first-order operator

`T a = (-2 d*a, d⁺a) : iΩ¹(X) → iΩ⁰(X) ⊕ iΩ⁺(X)`,  `d⁺a = (da)⁺ = (da + ⋆da) / 2`.

Its second component is the derivative of the curvature equation. Its first component is the
formal adjoint `d₀* = -2 d*` of the infinitesimal gauge action `d₀ξ = -2 dξ`, coming from the
action `A ↦ A - 2u⁻¹du` of gauge transformations on determinant connections; it rescales the
derivative `d*a` of the Coulomb condition and cuts out the same slice. As for the quadratic
two-form `TauCeti.SeibergWitten.quadraticTwoForm`, an imaginary form `i a` is indexed here by the
real form `a`, so that `T` is a real-linear map from smooth real one-forms to pairs of a smooth
function and a smooth self-dual two-form (`TauCeti.SeibergWitten.abelianDeformationOperator`),
the self-dual forms being `TauCeti.SmoothForm.selfDualForms`.
Together with the complex Dirac operator `D_A⁺`, `T` is the leading part of the gauge-fixed
linearization of the Seiberg–Witten map, and its index enters the expected dimension of the moduli
space.

On a closed four-manifold the kernel of `T` consists of the closed and coclosed one-forms, the
harmonic one-forms `H¹(X)` (`TauCeti.SeibergWitten.ker_abelianDeformationOperator`). The extra
condition `da = 0` comes from the vanishing of `(da)⁺`: an exact two-form `β` has
`∫_X |β⁺|² vol = ∫_X |β⁻|² vol` by Stokes' theorem
(`TauCeti.SmoothForm.integralTopForm_inner_selfDualPart_eq_inner_antiSelfDualPart`), so
`β⁺ = 0` forces `β = 0`.

## Main definitions

* `TauCeti.SeibergWitten.abelianDeformationOperator o`: the operator `a ↦ (-2 d*a, (da)⁺)` from
  smooth one-forms to smooth functions and smooth self-dual two-forms.

## Main results

* `TauCeti.SeibergWitten.abelianDeformationOperator_eq_zero_iff`: on a closed four-manifold,
  `T a = 0` exactly when `da = 0` and `d*a = 0`.
* `TauCeti.SeibergWitten.ker_abelianDeformationOperator`: on a closed four-manifold, the kernel of
  `T` is the intersection of the kernels of `d` and `d*`.

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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin (2 + 2)))

/-- The **abelian deformation operator** `T a = (-2 d*a, (da)⁺)` of the Seiberg–Witten equations on
an oriented Riemannian four-manifold, from smooth one-forms to smooth functions and smooth
self-dual two-forms, an imaginary form `i a` being indexed by the real form `a`. Its first
component is the formal adjoint `-2 d*` of the infinitesimal gauge action, a rescaling of the
derivative of the Coulomb gauge condition; its second is the derivative of the curvature equation
in the connection direction. -/
def abelianDeformationOperator :
    SmoothForm I M ℝ 1 →ₗ[ℝ] SmoothForm I M ℝ 0 × SmoothForm.selfDualForms (I := I) (M := M) o :=
  ((-2 : ℝ) • SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl)).prod
    ((SmoothForm.selfDualPart o ∘ₗ mextDerivₗ I 1).codRestrict _ fun _ ↦
      SmoothForm.selfDualPart_mem_selfDualForms o even_two _)

/-- The function component of `T a` is `-2 d*a`. -/
@[simp]
theorem abelianDeformationOperator_apply_fst (a : SmoothForm I M ℝ 1) :
    (abelianDeformationOperator o a).1 =
      (-2 : ℝ) • SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl) a :=
  (rfl)

/-- The two-form component of `T a` is `d⁺a = (da)⁺`. -/
@[simp]
theorem coe_abelianDeformationOperator_apply_snd (a : SmoothForm I M ℝ 1) :
    ((abelianDeformationOperator o a).2 : SmoothForm I M ℝ 2) =
      SmoothForm.selfDualPart o (mextDerivₗ I 1 a) :=
  (rfl)

variable [CompactSpace M] [BoundarylessManifold I M] [T2Space M]

/-- On a closed oriented Riemannian four-manifold, `T a = (-2 d*a, (da)⁺)` vanishes exactly when the
one-form `a` is closed and coclosed. -/
theorem abelianDeformationOperator_eq_zero_iff (a : SmoothForm I M ℝ 1) :
    abelianDeformationOperator o a = 0 ↔
      mextDerivₗ I 1 a = 0 ∧
        SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl) a = 0 := by
  have hsnd : (abelianDeformationOperator o a).2 = 0 ↔
      SmoothForm.selfDualPart o (mextDerivₗ I 1 a) = 0 := by
    rw [← coe_abelianDeformationOperator_apply_snd, Submodule.coe_eq_zero]
  simp only [Prod.ext_iff, abelianDeformationOperator_apply_fst, Prod.fst_zero, Prod.snd_zero,
    hsnd, smul_eq_zero, neg_eq_zero, OfNat.ofNat_ne_zero, false_or]
  refine and_comm.trans <| and_congr_left fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  have hex : mextDerivₗ I 1 a ∈ exactForms I M (1 + 1) := by
    rw [exactForms_succ]
    exact LinearMap.mem_range_self _ a
  exact SmoothForm.eq_zero_of_selfDualPart_eq_zero o even_two hex
    (by simp only [compactlySupportedForms_eq_top, Submodule.mem_top]) h

/-- On a closed oriented Riemannian four-manifold, the kernel of `T` consists of the closed and
coclosed one-forms: it is the intersection of the kernels of `d` and `d*`. -/
theorem ker_abelianDeformationOperator :
    LinearMap.ker (abelianDeformationOperator o) =
      LinearMap.ker (mextDerivₗ I (F := ℝ) 1) ⊓
        LinearMap.ker (SmoothForm.codifferential o (show 0 + 1 + 3 = 2 + 2 from rfl)) := by
  ext a
  simp only [LinearMap.mem_ker, Submodule.mem_inf, abelianDeformationOperator_eq_zero_iff]

end TauCeti.SeibergWitten
