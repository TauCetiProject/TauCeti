/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Cotangent
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville

/-!
# Cotangent lifts preserve the Liouville and canonical symplectic forms

Let `h : M → N` be a smooth diffeomorphism and `T*h : T*M → T*N` its cotangent lift
`(x, p) ↦ (h x, p ∘ (dh_x)⁻¹)` (`Diffeomorph.cotangent`). The Liouville forms are natural:

`(T*h)^* λ_N = λ_M` (`Diffeomorph.mpullback_cotangent_liouvilleForm`).

Indeed `T*h` covers `h`, so `dπ_N ∘ d(T*h) = dh ∘ dπ_M`, and the lifted covector pairs with
`dh (dπ_M v)` as the original covector pairs with `dπ_M v`. Since exterior differentiation commutes
with pullback, the canonical symplectic forms `ω = -dλ` are preserved as well:

`(T*h)^* ω_N = ω_M` (`Diffeomorph.mpullback_cotangent_symplecticForm`).

So every diffeomorphism of the base gives an exact symplectomorphism of cotangent bundles. The base
may have boundary or corners and need not be finite-dimensional.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace Diffeomorph

open TauCeti TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

section Liouville

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- **Naturality of the Liouville form.** The cotangent lift of a smooth diffeomorphism
pulls the Liouville form of `T*N` back to the Liouville form of `T*M`. -/
@[simp]
theorem mpullback_cotangent_liouvilleForm (h : M ≃ₘ⟮I, J⟯ N) :
    SmoothForm.mpullback h.cotangent h.cotangent.contMDiff (liouvilleForm J N) =
      liouvilleForm I M := by
  apply Subtype.ext
  funext z
  ext v
  rw [SmoothForm.mpullback_apply, liouvilleForm_apply, liouvilleForm_apply]
  -- The lift covers `h`, so `dπ_N ∘ d(T*h) = d(π_N ∘ T*h) = d(h ∘ π_M) = dh ∘ dπ_M`.
  have hproj : π (F →L[ℝ] ℝ) (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ) ∘ h.cotangent =
      h ∘ π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) :=
    funext (proj_cotangent h)
  have hN := mfderiv_comp_apply z
    ((contMDiff_proj (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero)
    (h.cotangent.mdifferentiable (by simp) z) (v 0)
  have hM := mfderiv_comp_apply z (h.mdifferentiable (by simp) z.proj)
    ((contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero)
    (v 0)
  rw [hproj, hM] at hN
  rw [← hN]
  exact cotangent_snd_apply_mfderiv h z _

end Liouville

section Symplectic

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- **Cotangent lifts are symplectic.** The cotangent lift of a smooth diffeomorphism pulls the
canonical symplectic form of `T*N` back to the canonical symplectic form of `T*M`. -/
@[simp]
theorem mpullback_cotangent_symplecticForm (h : M ≃ₘ⟮I, J⟯ N) :
    SmoothForm.mpullback h.cotangent h.cotangent.contMDiff (symplecticForm J N) =
      symplecticForm I M := by
  rw [symplecticForm_eq_neg_mextDerivₗ, symplecticForm_eq_neg_mextDerivₗ, map_neg,
    ← SmoothForm.mextDerivₗ_mpullback, mpullback_cotangent_liouvilleForm]

end Symplectic

end Diffeomorph
