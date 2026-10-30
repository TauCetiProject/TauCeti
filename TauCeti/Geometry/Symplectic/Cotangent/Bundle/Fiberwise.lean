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
smooth right inverse (`TauCeti.SmoothForm.mpullback_proj_injective`); this turns the identity
`τ_α^*ω = ω - π^*dα` into the closedness criterion.
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

/-- **Fibre translation shifts the Liouville form.** Translating the fibres of the cotangent bundle
by a one-form `α` pulls the Liouville form back to `λ + π^*α`. -/
theorem mpullback_vectorBundleTranslateDiffeomorph_liouvilleForm (α : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback _
        (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv α)
          (SmoothForm.degreeOneEquiv α).contMDiff).contMDiff (liouvilleForm I M) =
      liouvilleForm I M +
        SmoothForm.mpullback (TotalSpace.proj : CotangentBundle I M → M) (contMDiff_proj _) α := by
  apply Subtype.ext
  funext z
  ext v
  rw [mpullback_liouvilleForm_apply_of_proj_eq (vectorBundleTranslateDiffeomorph _ _).contMDiff
      (fun _ ↦ by simp), vectorBundleTranslateDiffeomorph_apply]
  simp [Fin.fin_one_eq_zero]

/-- **Fibre dilation rescales the Liouville form.** Multiplying the fibres of the cotangent bundle
by a nonzero real number `c` pulls the Liouville form back to `c • λ`. -/
theorem mpullback_vectorBundleScalarDiffeomorph_liouvilleForm {c : ℝ} (hc : c ≠ 0) :
    SmoothForm.mpullback _
        (vectorBundleScalarDiffeomorph (I := I) (F := E →L[ℝ] ℝ)
          (V := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
          (fun _ ↦ c) (contMDiff_const (n := ∞)) fun _ ↦ hc).contMDiff (liouvilleForm I M) =
      c • liouvilleForm I M := by
  apply Subtype.ext
  funext z
  ext v
  rw [mpullback_liouvilleForm_apply_of_proj_eq (vectorBundleScalarDiffeomorph _ _ _).contMDiff
      (fun _ ↦ by simp), vectorBundleScalarDiffeomorph_apply]
  simp

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
    map_eq_zero_iff _ SmoothForm.mpullback_proj_injective, SmoothForm.isClosed_def,
    ← mextDerivₗ_apply I 1 α, ZeroMemClass.coe_eq_zero]

end Symplectic

end CotangentBundle

end TauCeti
