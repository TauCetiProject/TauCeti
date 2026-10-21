/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.Translate
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville

/-!
# Fibrewise translation and dilation of a cotangent bundle

This file records how two families of fibre-preserving diffeomorphisms of the cotangent bundle
`T*M = TauCeti.CotangentBundle I M` act on its Liouville form `λ` and on its canonical symplectic
form `ω = -dλ`. Both cover the identity of `M`, and both are instances of general vector-bundle
constructions.

* The **fibre translation** by a smooth one-form `α` on `M`, `τ_α(p) = p + α_x` for a covector `p`
  over `x`: this is `TauCeti.vectorBundleTranslateDiffeomorph` for the section of `T*M` defined by
  `α`. It satisfies `τ_α^*λ = λ + π^*α` and `τ_α^*ω = ω - π^*dα`, where `π : T*M → M` is the
  bundle projection. Hence `τ_α` preserves `ω` exactly when `α` is closed
  (`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_symplecticForm_eq_self_iff`).
* The **fibre dilation** by a nonzero real number `c`, `p ↦ c • p`: this is
  `TauCeti.vectorBundleScalarDiffeomorph` for the constant function `c`. It satisfies
  `(c •)^*λ = c • λ` and `(c •)^*ω = c • ω`. For `c = -1` this is the fibre negation, which
  reverses both `λ` and `ω`; for `c = e^t` it is the time-`t` map of the radial Liouville flow.

The cotangent projection pulls forms back injectively, because it has the zero section as a
smooth right inverse; this turns the identity `τ_α^*ω = ω - π^*dα` into the closedness criterion.
These maps are the global versions of the linear-model maps `TauCeti.cotangentFiberNeg` and
`TauCeti.cotangentFiberTranslate`; the latter translates by `-σ`, following the magnetic
convention, whereas `τ_α` translates by `+α`.

## Main declarations

* `TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_liouvilleForm` and
  `TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_symplecticForm`.
* `TauCeti.CotangentBundle.mpullback_vectorBundleScalarDiffeomorph_liouvilleForm` and
  `TauCeti.CotangentBundle.mpullback_vectorBundleScalarDiffeomorph_symplecticForm`.

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

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Action on the Liouville form -/

section Liouville

variable [IsManifold I 2 M]

/-- A self-map `g` of the cotangent bundle covering the identity commutes with the derivative of
the projection. -/
private theorem mfderiv_proj_comp_of_proj {g : CotangentBundle I M → CotangentBundle I M}
    (hg : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ g)
    (hproj : ∀ z, (g z).proj = z.proj) (z : CotangentBundle I M)
    (v : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z) :
    mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) (g z)
        (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) g z v) =
      mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) z v := by
  have hcomp := mfderiv_comp z
    ((contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (g z)).mdifferentiableAt one_ne_zero)
    ((hg z).mdifferentiableAt (by simp))
  have hπg : (TotalSpace.proj : CotangentBundle I M → M) ∘ g = TotalSpace.proj :=
    funext hproj
  rw [hπg] at hcomp
  exact (DFunLike.congr_fun hcomp v).symm

/-- **Fibre translation shifts the Liouville form.** Translating the fibres of the cotangent bundle
by a one-form `α` pulls the Liouville form back to `λ + π^*α`. -/
theorem mpullback_vectorBundleTranslateDiffeomorph_liouvilleForm (α : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback _
        (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
          (SmoothForm.degreeOneEquiv α).contMDiff).contMDiff (liouvilleForm I M) =
      liouvilleForm I M +
        SmoothForm.mpullback (TotalSpace.proj : CotangentBundle I M → M) (contMDiff_proj _) α := by
  set τ := vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
    (SmoothForm.degreeOneEquiv α).contMDiff
  apply Subtype.ext
  funext z
  ext v
  rw [SmoothForm.add_toRoughForm, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    SmoothForm.mpullback_apply, SmoothForm.mpullback_apply, liouvilleForm_apply,
    liouvilleForm_apply, mfderiv_proj_comp_of_proj τ.contMDiff
      (fun _ ↦ by rw [vectorBundleTranslateDiffeomorph_apply]) z]
  -- A one-form on a single vector only sees its first entry.
  have hv : (fun i : Fin 1 ↦ mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I
      (TotalSpace.proj : CotangentBundle I M → M) z (v i)) =
      fun _ ↦ mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (TotalSpace.proj : CotangentBundle I M → M) z
        (v 0) :=
    funext fun i ↦ by rw [Fin.fin_one_eq_zero i]
  rw [hv, ← SmoothForm.degreeOneEquiv_apply_apply, vectorBundleTranslateDiffeomorph_apply]
  -- The translated covector is a sum of continuous linear maps, evaluated pointwise.
  rfl

/-- **Fibre dilation rescales the Liouville form.** Multiplying the fibres of the cotangent bundle
by a nonzero real number `c` pulls the Liouville form back to `c • λ`. -/
theorem mpullback_vectorBundleScalarDiffeomorph_liouvilleForm {c : ℝ} (hc : c ≠ 0) :
    SmoothForm.mpullback _
        (vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
          (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
          (fun _ ↦ c) (contMDiff_const (n := ∞)) fun _ ↦ hc).contMDiff (liouvilleForm I M) =
      c • liouvilleForm I M := by
  set δ := vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
    (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (fun _ ↦ c) (contMDiff_const (n := ∞)) fun _ ↦ hc
  apply Subtype.ext
  funext z
  ext v
  rw [SmoothForm.smul_toRoughForm, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    SmoothForm.mpullback_apply, liouvilleForm_apply, liouvilleForm_apply,
    mfderiv_proj_comp_of_proj δ.contMDiff
      (fun _ ↦ by rw [vectorBundleScalarDiffeomorph_apply]) z, vectorBundleScalarDiffeomorph_apply]
  -- The dilated covector is a scalar multiple of a continuous linear map, evaluated pointwise.
  rfl

end Liouville

/-! ### Action on the canonical symplectic form -/

section Symplectic

variable [IsManifold I ∞ M]

/-- **Fibre translation shifts the canonical symplectic form.** Translating the fibres of the
cotangent bundle by a one-form `α` pulls the canonical symplectic form back to `ω - π^*dα`. -/
theorem mpullback_vectorBundleTranslateDiffeomorph_symplecticForm (α : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback _
        (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
          (SmoothForm.degreeOneEquiv α).contMDiff).contMDiff (symplecticForm I M) =
      symplecticForm I M -
        SmoothForm.mpullback (TotalSpace.proj : CotangentBundle I M → M) (contMDiff_proj _)
          (mextDerivₗ I 1 α) := by
  rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_vectorBundleTranslateDiffeomorph_liouvilleForm, map_add,
    SmoothForm.mextDerivₗ_mpullback, neg_add, sub_eq_add_neg]

/-- **Fibre dilation rescales the canonical symplectic form.** Multiplying the fibres of the
cotangent bundle by a nonzero real number `c` pulls the canonical symplectic form back to `c • ω`.
In particular the fibre negation reverses `ω`. -/
theorem mpullback_vectorBundleScalarDiffeomorph_symplecticForm {c : ℝ} (hc : c ≠ 0) :
    SmoothForm.mpullback _
        (vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
          (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
          (fun _ ↦ c) (contMDiff_const (n := ∞)) fun _ ↦ hc).contMDiff (symplecticForm I M) =
      c • symplecticForm I M := by
  rw [symplecticForm_eq_neg_mextDerivₗ, map_neg, ← SmoothForm.mextDerivₗ_mpullback,
    mpullback_vectorBundleScalarDiffeomorph_liouvilleForm hc, map_smul, smul_neg]

/-- Pullback of forms along the cotangent projection is injective: the zero section is a smooth
right inverse of the projection. -/
private theorem mpullback_proj_injective (k : ℕ) :
    Function.Injective (SmoothForm.mpullback (I' := I) (F := ℝ) (k := k)
      (TotalSpace.proj : CotangentBundle I M → M) (contMDiff_proj _)) := by
  have hzero : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (zeroSection (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) :=
    contMDiff_zeroSection ℝ _
  refine Function.LeftInverse.injective (g := SmoothForm.mpullback _ hzero) fun φ ↦ ?_
  rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  -- The projection of the zero section is the identity of `M`.
  exact DFunLike.congr_fun SmoothForm.mpullback_id φ

/-- **Fibre translation by a closed one-form is symplectic.** Translating the fibres of the
cotangent bundle by a one-form `α` preserves the canonical symplectic form exactly when `α` is
closed. -/
theorem mpullback_vectorBundleTranslateDiffeomorph_symplecticForm_eq_self_iff
    (α : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback _
        (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
          (SmoothForm.degreeOneEquiv α).contMDiff).contMDiff (symplecticForm I M) =
      symplecticForm I M ↔ α.IsClosed := by
  rw [mpullback_vectorBundleTranslateDiffeomorph_symplecticForm, sub_eq_self,
    ← map_zero (SmoothForm.mpullback (I' := I) (F := ℝ) (k := 2)
      (TotalSpace.proj : CotangentBundle I M → M) (contMDiff_proj _)),
    (mpullback_proj_injective 2).eq_iff, SmoothForm.isClosed_def, ← mextDerivₗ_apply I 1 α,
    ZeroMemClass.coe_eq_zero]

end Symplectic

end CotangentBundle

end TauCeti
