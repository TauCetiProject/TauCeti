/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Conormal.Subbundle
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Exact

/-!
# The Liouville form on conormal covectors and the conormal Lagrangian subbundle

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
(`TauCeti.CotangentBundle.isExactLagrangianMap_of_conormal`).

Specialising `ψ` to the canonical inclusion `TauCeti.CotangentBundle.conormalInclusion` of the
conormal vector subbundle (`TauCeti.CotangentBundle.conormalFiberBundle`) over `Q` into `T*M`:

* `conormalInclusion` pulls both the Liouville one-form `λ` and the canonical symplectic form `ω`
  back to `0`, and is an isotropic map into `T*M` for any smooth map `i : Q → M` with injective
  differentials (`TauCeti.CotangentBundle.mpullback_conormalInclusion_liouvilleForm`,
  `TauCeti.CotangentBundle.mpullback_conormalInclusion_symplecticForm`,
  `TauCeti.CotangentBundle.isIsotropicMap_conormalInclusion`);
* when `Q` is boundaryless and `i : Q → M` is a smooth embedding into a finite-dimensional manifold
  `M` (`dim Q + k = dim M`), `conormalInclusion` has source of dimension `dim M`
  (`TauCeti.CotangentBundle.finrank_conormalBundleModel`) and is a smooth embedding
  (`TauCeti.CotangentBundle.isSmoothEmbedding_conormalInclusion`), hence is both an exact Lagrangian
  map with primitive `0` (`TauCeti.CotangentBundle.isExactLagrangianMap_conormalInclusion`) and a
  Lagrangian embedding (`TauCeti.CotangentBundle.isLagrangianEmbedding_conormalInclusion`). Empty
  submanifolds `Q` are included without imposing a finite-dimensionality hypothesis on the model of
  `Q`.

## Main declarations

* `TauCeti.CotangentBundle.mpullback_liouvilleForm_eq_zero_of_conormal`,
  `TauCeti.CotangentBundle.isIsotropicMap_of_conormal`,
  `TauCeti.CotangentBundle.isExactLagrangianMap_of_conormal`: vanishing of `ψ^*λ`, isotropy, and
  exactness for general maps factoring through conormal covectors.
* `TauCeti.CotangentBundle.mpullback_conormalInclusion_liouvilleForm`,
  `TauCeti.CotangentBundle.mpullback_conormalInclusion_symplecticForm`,
  `TauCeti.CotangentBundle.isIsotropicMap_conormalInclusion`: the canonical inclusion of the
  conormal bundle pulls `λ` and `ω` back to `0` and is isotropic.
* `TauCeti.CotangentBundle.isExactLagrangianMap_conormalInclusion`,
  `TauCeti.CotangentBundle.isLagrangianEmbedding_conormalInclusion`: for a smooth embedding `i` of
  a boundaryless manifold `Q`, the conormal bundle is an exact Lagrangian embedding in `T*M` with
  primitive `0`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3.3.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Example 3.2.4 and Proposition 3.4.2.
-/

public section

noncomputable section

open Bundle Manifold Module
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

/-! ### The conormal vector subbundle as an exact Lagrangian embedding -/

section ConormalBundle

variable [IsManifold I ∞ M] [IsManifold J ∞ Q] [FiniteDimensional ℝ E] {k : ℕ}

/-- **The Liouville form vanishes on the conormal bundle.** For a smooth map `i : Q → M` with
injective differentials and `finrank ℝ F + k = finrank ℝ E`, the canonical inclusion of the
conormal bundle into `T*M` pulls the Liouville one-form `λ` back to `0`. -/
theorem mpullback_conormalInclusion_liouvilleForm (hi : ContMDiff J I ∞ i)
    (hinj : ∀ q, Function.Injective (mfderiv J I i q)) (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
    letI := conormalVectorBundle (n := ∞) hi (by simp) hinj hk
    letI := conormalContMDiffVectorBundle (n := ∞) hi (by simp) hinj hk
    SmoothForm.mpullback (conormalInclusion (Fin k → ℝ) J I i)
      (contMDiff_conormalInclusion (n := ∞) hi (by simp) hinj hk) (liouvilleForm I M) = 0 := by
  let := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
  let := conormalVectorBundle (n := ∞) hi (by simp) hinj hk
  let := conormalContMDiffVectorBundle (n := ∞) hi (by simp) hinj hk
  apply Subtype.ext
  rw [SmoothForm.coe_mpullback, ZeroMemClass.coe_zero]
  exact mpullback_liouvilleForm_eq_zero_of_conormal
    (conormalInclusion_proj (Fin k → ℝ) J I i)
    ((contMDiff_conormalInclusion (n := ∞) hi (by simp) hinj hk).mdifferentiable (by simp))
    ((Bundle.contMDiff_proj (n := ∞) (fun q ↦ conormalSpace J I i q)).mdifferentiable (by simp))
    (fun z ↦ (hi z.proj).mdifferentiableAt (by simp))
    (conormalInclusion_snd_comp_mfderiv (Fin k → ℝ) J I i)

/-- **The canonical symplectic form vanishes on the conormal bundle.** For a smooth map `i : Q → M`
with injective differentials and `finrank ℝ F + k = finrank ℝ E`, the canonical inclusion of the
conormal bundle into `T*M` pulls `ω = -dλ` back to `0`. -/
theorem mpullback_conormalInclusion_symplecticForm (hi : ContMDiff J I ∞ i)
    (hinj : ∀ q, Function.Injective (mfderiv J I i q)) (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
    letI := conormalVectorBundle (n := ∞) hi (by simp) hinj hk
    letI := conormalContMDiffVectorBundle (n := ∞) hi (by simp) hinj hk
    SmoothForm.mpullback (conormalInclusion (Fin k → ℝ) J I i)
      (contMDiff_conormalInclusion (n := ∞) hi (by simp) hinj hk) (symplecticForm I M) = 0 := by
  let := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
  let := conormalVectorBundle (n := ∞) hi (by simp) hinj hk
  let := conormalContMDiffVectorBundle (n := ∞) hi (by simp) hinj hk
  rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_conormalInclusion_liouvilleForm hi hinj hk, map_zero, neg_zero]

/-- **The conormal bundle is isotropic in `T*M`.** For any smooth map `i : Q → M` with injective
differentials and `finrank ℝ F + k = finrank ℝ E`, the canonical inclusion of the conormal bundle
into `T*M` is an isotropic map for the canonical symplectic form. -/
theorem isIsotropicMap_conormalInclusion (hi : ContMDiff J I ∞ i)
    (hinj : ∀ q, Function.Injective (mfderiv J I i q)) (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsIsotropicMap
      (J.prod 𝓘(ℝ, Fin k → ℝ)) (conormalInclusion (Fin k → ℝ) J I i) := by
  let := conormalFiberBundle (n := ∞) hi (by simp) hinj hk
  let := conormalVectorBundle (n := ∞) hi (by simp) hinj hk
  let := conormalContMDiffVectorBundle (n := ∞) hi (by simp) hinj hk
  exact isIsotropicMap_of_conormal
    (conormalInclusion_proj (Fin k → ℝ) J I i)
    (contMDiff_conormalInclusion (n := ∞) hi (by simp) hinj hk)
    ((Bundle.contMDiff_proj (n := ∞) (fun q ↦ conormalSpace J I i q)).mdifferentiable (by simp))
    (fun z ↦ (hi z.proj).mdifferentiableAt (by simp))
    (conormalInclusion_snd_comp_mfderiv (Fin k → ℝ) J I i)

/-- **The conormal bundle of an embedded submanifold is an exact Lagrangian in `T*M`.** For a
smooth embedding `i : Q → M` of a boundaryless manifold `Q` into a finite-dimensional manifold `M`
with `finrank ℝ F + k = finrank ℝ E`, the canonical inclusion of the conormal bundle into `T*M` is
an exact Lagrangian map for the Liouville primitive `λ` of `ω = -dλ`, with primitive `0`. -/
theorem isExactLagrangianMap_conormalInclusion [J.Boundaryless] (hi : IsSmoothEmbedding J I ∞ i)
    (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi.contMDiff (by simp)
      (hi.isImmersion.mfderiv_injective (by simp)) hk
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsExactLagrangianMap
      (J.prod 𝓘(ℝ, Fin k → ℝ)) (liouvilleForm I M) (conormalInclusion (Fin k → ℝ) J I i) 0 := by
  have hinj := hi.isImmersion.mfderiv_injective (by simp)
  let := conormalFiberBundle (n := ∞) hi.contMDiff (by simp) hinj hk
  let := conormalVectorBundle (n := ∞) hi.contMDiff (by simp) hinj hk
  let := conormalContMDiffVectorBundle (n := ∞) hi.contMDiff (by simp) hinj hk
  have hemb := isSmoothEmbedding_conormalInclusion (n := ∞) hi (by simp) hk
  by_cases hQ : Nonempty Q
  · obtain ⟨q₀⟩ := hQ
    have : FiniteDimensional ℝ F :=
      FiniteDimensional.of_injective (mfderiv J I i q₀).toLinearMap (hinj q₀)
    exact isExactLagrangianMap_of_conormal
      (conormalInclusion_proj (Fin k → ℝ) J I i) hemb.contMDiff
      (hemb.isImmersion.mfderiv_injective (by simp)) (finrank_conormalBundleModel hk)
      ((Bundle.contMDiff_proj (n := ∞) (fun q ↦ conormalSpace J I i q)).mdifferentiable (by simp))
      (fun z ↦ (hi.contMDiff z.proj).mdifferentiableAt (by simp))
      (conormalInclusion_snd_comp_mfderiv (Fin k → ℝ) J I i)
  · refine ⟨SmoothTwoForm.IsNondegenerate.isLagrangianMap_iff_forall.mpr fun z ↦ (hQ ⟨z.proj⟩).elim,
      contMDiff_const, funext fun z ↦ (hQ ⟨z.proj⟩).elim⟩

/-- **The conormal bundle of an embedded submanifold is a Lagrangian embedding in `T*M`.** For a
smooth embedding `i : Q → M` of a boundaryless manifold `Q` into a finite-dimensional manifold `M`
with `finrank ℝ F + k = finrank ℝ E`, the canonical inclusion of the conormal bundle into `T*M` is
a smooth Lagrangian embedding. -/
theorem isLagrangianEmbedding_conormalInclusion [J.Boundaryless] (hi : IsSmoothEmbedding J I ∞ i)
    (hk : finrank ℝ F + k = finrank ℝ E) :
    letI := conormalFiberBundle (n := ∞) hi.contMDiff (by simp)
      (hi.isImmersion.mfderiv_injective (by simp)) hk
    (isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.IsLagrangianEmbedding
      (J.prod 𝓘(ℝ, Fin k → ℝ)) (conormalInclusion (Fin k → ℝ) J I i) := by
  let := conormalFiberBundle (n := ∞) hi.contMDiff (by simp)
    (hi.isImmersion.mfderiv_injective (by simp)) hk
  exact (SmoothTwoForm.IsNondegenerate.isLagrangianEmbedding_iff_of_isSmoothEmbedding
    (isSmoothEmbedding_conormalInclusion (n := ∞) hi (by simp) hk)).mpr
    (isExactLagrangianMap_conormalInclusion hi hk).isLagrangianMap

end ConormalBundle

end TauCeti.CotangentBundle
