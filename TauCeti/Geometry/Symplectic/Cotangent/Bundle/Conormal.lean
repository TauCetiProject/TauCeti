/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Conormal
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Lagrangian.Exact

/-!
# The Liouville form vanishes on conormal covectors

Let `i : Q → M` be a map and let `ψ : X → T*M` take values in the conormal set
`TauCeti.CotangentBundle.conormal J I i`, through a map `g : X → Q`: the covector `ψ x` lies over
`i (g x)` and annihilates the tangent image of `i` at `g x`. Assume `ψ` and `g` are differentiable,
and `i` is differentiable at every `g x`. Then `ψ` pulls the Liouville form `λ` back to zero
(`TauCeti.CotangentBundle.mpullback_liouvilleForm_eq_zero_of_conormal`). Indeed,
`λ(dψ v) = (ψ x)(dπ dψ v)`, and `π ∘ ψ = i ∘ g`, so `dπ dψ v = di (dg v)` is annihilated by
`ψ x`.

Consequently such a smooth `ψ` is isotropic for the canonical symplectic form `ω = -dλ`
(`TauCeti.CotangentBundle.isIsotropicMap_of_conormal`). When `ψ` has injective differentials and
its source has the dimension of `M`, it is an exact Lagrangian map with primitive `0`
(`TauCeti.CotangentBundle.isExactLagrangianMap_of_conormal`). The intended example is the inclusion
of the conormal bundle `N*Q` of an embedded submanifold, with `g` its bundle projection; its
dimension is that of `M` by `TauCeti.CotangentBundle.finrank_add_finrank_conormalSpace`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3.3.
-/

public section

noncomputable section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {Q : Type*} [TopologicalSpace Q] [ChartedSpace H' Q]
  {G H'' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ G H''} {X : Type*} [TopologicalSpace X] [ChartedSpace H'' X]
  {i : Q → M} {ψ : X → CotangentBundle I M} {g : X → Q}

section Liouville

variable [IsManifold I 2 M]

/-- **The Liouville form vanishes on conormal covectors**, pointwise. If `ψ` lies over `i ∘ g`,
`ψ` and `g` are differentiable at `x`, `i` is differentiable at `g x`, and the covector `ψ x`
annihilates the tangent image of `i` at `g x`, then `ψ^*λ` vanishes at `x`. -/
theorem mpullback_liouvilleForm_apply_eq_zero_of_conormal (hproj : ∀ x, (ψ x).proj = i (g x))
    {x : X} (hψ : MDifferentiableAt K (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ψ x)
    (hg : MDifferentiableAt K J g x) (hi : MDifferentiableAt J I i (g x))
    (hann : (ψ x).2 ∘L mfderiv J I i (g x) = 0) :
    mpullback K (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ψ (liouvilleForm I M).1 x = 0 := by
  ext v
  rw [mpullback_apply, liouvilleForm_apply]
  have hπ : π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ∘ ψ = i ∘ g := funext hproj
  -- The derivative of `π ∘ ψ = i ∘ g` is computed in two ways by the chain rule.
  have hπψ := mfderiv_comp_apply x
    ((Bundle.contMDiff_proj (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) _).mdifferentiableAt
      one_ne_zero) hψ (v 0)
  rw [← hπψ, hπ, mfderiv_comp_apply x hi hg]
  exact DFunLike.congr_fun hann _

/-- **The Liouville form vanishes on conormal covectors.** If `ψ : X → T*M` lies over `i ∘ g`,
`ψ` and `g` are differentiable, `i` is differentiable at every `g x`, and each covector `ψ x`
annihilates the tangent image of `i` at `g x`, so that `ψ` takes values in the conormal set of `i`,
then `ψ^*λ = 0`. -/
theorem mpullback_liouvilleForm_eq_zero_of_conormal (hproj : ∀ x, (ψ x).proj = i (g x))
    (hψ : MDifferentiable K (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ψ) (hg : MDifferentiable K J g)
    (hi : ∀ x, MDifferentiableAt J I i (g x)) (hann : ∀ x, (ψ x).2 ∘L mfderiv J I i (g x) = 0) :
    mpullback K (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ψ (liouvilleForm I M).1 = 0 :=
  funext fun x ↦
    mpullback_liouvilleForm_apply_eq_zero_of_conormal hproj (hψ x) (hg x) (hi x) (hann x)

end Liouville

section Symplectic

variable [IsManifold I ∞ M] [IsManifold K ∞ X]

/-- **Conormal maps are isotropic.** A smooth map `ψ : X → T*M` lying over `i ∘ g`, whose
covectors `ψ x` annihilate the tangent images of `i` at `g x`, is isotropic for the canonical
symplectic form, provided `g` is differentiable and `i` is differentiable at every `g x`. -/
theorem isIsotropicMap_of_conormal (hproj : ∀ x, (ψ x).proj = i (g x))
    (hψ : ContMDiff K (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ψ) (hg : MDifferentiable K J g)
    (hi : ∀ x, MDifferentiableAt J I i (g x)) (hann : ∀ x, (ψ x).2 ∘L mfderiv J I i (g x) = 0) :
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsIsotropicMap K ψ :=
  SmoothTwoForm.IsNondegenerate.isIsotropicMap_of_mpullback_eq_mextDeriv
    symplecticForm_eq_neg_mextDerivₗ hψ contMDiff_const
    ((mpullback_liouvilleForm_eq_zero_of_conormal hproj (hψ.mdifferentiable (by simp)) hg hi
      hann).trans mextDeriv_ofFunction_zero.symm)

/-- **Conormal maps of the dimension of `M` are exact Lagrangian.** On a finite-dimensional
manifold `M`, a smooth map `ψ : X → T*M` with injective differentials from a manifold of the
dimension of `M`, lying over `i ∘ g` and with covectors `ψ x` annihilating the tangent images of
`i` at `g x`, is an exact Lagrangian map for the primitive `λ` of `ω = -dλ`, with primitive `0`,
provided `g` is differentiable and `i` is differentiable at every `g x`. -/
theorem isExactLagrangianMap_of_conormal [FiniteDimensional ℝ E]
    (hproj : ∀ x, (ψ x).proj = i (g x)) (hψ : ContMDiff K (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ψ)
    (hinj : ∀ x, Function.Injective (mfderiv K (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ψ x))
    (hdim : finrank ℝ G = finrank ℝ E) (hg : MDifferentiable K J g)
    (hi : ∀ x, MDifferentiableAt J I i (g x)) (hann : ∀ x, (ψ x).2 ∘L mfderiv J I i (g x) = 0) :
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsExactLagrangianMap K
      (liouvilleForm I M) ψ 0 := by
  refine (SmoothTwoForm.IsNondegenerate.isExactLagrangianMap_iff_of_finrank
    symplecticForm_eq_neg_mextDerivₗ hψ hinj ?_).mpr ⟨contMDiff_const,
      (mpullback_liouvilleForm_eq_zero_of_conormal hproj (hψ.mdifferentiable (by simp)) hg hi
        hann).trans mextDeriv_ofFunction_zero.symm⟩
  rw [finrank_prod, ContinuousLinearMap.dual_finrank_eq, hdim, two_mul]

end Symplectic

end TauCeti.CotangentBundle
