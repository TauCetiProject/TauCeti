/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Twisted
public import TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence

/-!
# Exact magnetic cotangent bundles

A one-form `σ` on a manifold `M` twists the canonical symplectic form `ω = -dλ` of the cotangent
bundle `T*M` by the exact magnetic term `π^*dσ`, where `π : T*M → M` is the projection. The result
is the **exact magnetic symplectic form**

`ω_σ = ω + π^*dσ`

(`TauCeti.CotangentBundle.magneticSymplecticForm`), which models a charged particle in the
magnetic field `dσ`. It is the twisted symplectic form `ω + π^*β` of
`TauCeti.Geometry.Symplectic.Cotangent.Bundle.Twisted` for the exact magnetic term `β = dσ`
(`TauCeti.CotangentBundle.magneticSymplecticForm_eq_twistedSymplecticForm`). It changes the
symplectic form exactly when `σ` is not closed
(`TauCeti.CotangentBundle.magneticSymplecticForm_eq_symplecticForm_iff`).

The magnetic term is removed by translating the fibres: the translation `τ(p) = p - σ_x` of a
covector `p` over `x` pulls `ω` back to `ω_σ`
(`TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_neg_symplecticForm`), so `τ`
is a symplectomorphism from `(T*M, ω_σ)` to `(T*M, ω)`. In particular `ω_σ` is symplectic
(`TauCeti.CotangentBundle.isSymplectic_magneticSymplecticForm`). The translation covers the
identity of `M` (`TauCeti.vectorBundleTranslateDiffeomorph_apply`), so it changes neither the
projection to `M` of a map into `T*M` nor hence its degree over `M`, and it carries the zero
section to the graph of `-σ`.

Consequently the contractible almost existence property in an exact magnetic cotangent bundle is
the same property in the standard one. A level `F⁻¹(c)` has it for `ω_σ` in a set `W` exactly
when the level `c` of `F ∘ τ⁻¹`, which is `τ(F⁻¹(c))`, has it for `ω` in `τ(W)`
(`TauCeti.CotangentBundle.hasContractibleAlmostExistence_magneticSymplecticForm_iff`). This is
how Barraud, Damian, Humilière and Oancea transport their almost existence theorems for domains
of cotangent bundles to exact magnetic cotangent bundles (their Corollary D): the domain `U` is
replaced by `τ(U)`, whose maps from closed manifolds have the same projections to `M`.

## Main declarations

* `TauCeti.CotangentBundle.magneticSymplecticForm`: the exact magnetic symplectic form
  `ω + π^*dσ`.
* `TauCeti.CotangentBundle.magneticSymplecticForm_eq_twistedSymplecticForm`: it is the twisted
  symplectic form with magnetic term `dσ`.
* `TauCeti.CotangentBundle.mpullback_vectorBundleTranslateDiffeomorph_neg_symplecticForm`: the
  fibre translation by `-σ` pulls `ω` back to `ω_σ`.
* `TauCeti.CotangentBundle.isSymplectic_magneticSymplecticForm`: `ω_σ` is symplectic.
* `TauCeti.CotangentBundle.hasContractibleAlmostExistence_magneticSymplecticForm_iff`: almost
  existence for `ω_σ` is almost existence for `ω` after the fibre translation.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Corollary D.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The **exact magnetic symplectic form** `ω_σ = ω + π^*dσ` of the cotangent bundle `T*M`, for a
one-form `σ` on `M`: the twisted symplectic form whose magnetic term is the exact two-form `dσ`. -/
def magneticSymplecticForm (σ : SmoothForm I M ℝ 1) :
    SmoothTwoForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M) :=
  twistedSymplecticForm (mextDerivₗ I 1 σ)

/-- The exact magnetic symplectic form of `σ` is the twisted symplectic form `ω + π^*β` with the
exact magnetic term `β = dσ`. -/
theorem magneticSymplecticForm_eq_twistedSymplecticForm (σ : SmoothForm I M ℝ 1) :
    magneticSymplecticForm σ = twistedSymplecticForm (mextDerivₗ I 1 σ) :=
  (rfl)

/-- Without a magnetic field the magnetic symplectic form is the canonical one. -/
@[simp]
theorem magneticSymplecticForm_zero :
    magneticSymplecticForm (0 : SmoothForm I M ℝ 1) = symplecticForm I M := by
  rw [magneticSymplecticForm_eq_twistedSymplecticForm, map_zero, twistedSymplecticForm_zero]

/-- The magnetic symplectic form of `σ` is the canonical one exactly when `σ` is closed, that is,
when the magnetic field `dσ` vanishes. -/
theorem magneticSymplecticForm_eq_symplecticForm_iff (σ : SmoothForm I M ℝ 1) :
    magneticSymplecticForm σ = symplecticForm I M ↔ σ.IsClosed := by
  rw [magneticSymplecticForm_eq_twistedSymplecticForm, twistedSymplecticForm_eq_symplecticForm_iff,
    SmoothForm.isClosed_iff_mextDerivₗ_eq_zero]

/-- **The fibre translation by `-σ` removes the magnetic term.** Translating the fibres of the
cotangent bundle by `-σ`, `p ↦ p - σ_x`, pulls the canonical symplectic form back to the exact
magnetic symplectic form `ω + π^*dσ`. So this translation is a symplectomorphism from
`(T*M, ω_σ)` to `(T*M, ω)`. -/
theorem mpullback_vectorBundleTranslateDiffeomorph_neg_symplecticForm (σ : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback _
        (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv (-σ))
          (SmoothForm.degreeOneEquiv (-σ)).contMDiff).contMDiff (symplecticForm I M) =
      magneticSymplecticForm σ := by
  rw [← twistedSymplecticForm_zero,
    mpullback_vectorBundleTranslateDiffeomorph_twistedSymplecticForm, map_neg, zero_sub, neg_neg,
    magneticSymplecticForm_eq_twistedSymplecticForm]

/-- The exact magnetic symplectic form is closed and nondegenerate. -/
theorem isSymplectic_magneticSymplecticForm (σ : SmoothForm I M ℝ 1) :
    (magneticSymplecticForm σ).IsSymplectic :=
  isSymplectic_twistedSymplecticForm (SmoothForm.isClosed_mextDerivₗ σ)

variable [FiniteDimensional ℝ E]

/-- **Almost existence transfers from `ω_σ` to `ω`.** This is the reduction step behind
Barraud–Damian–Humilière–Oancea, Corollary D (almost existence in an exact magnetic cotangent
bundle); it does not itself prove almost existence. Let `τ` be the fibre translation
`p ↦ p - σ_x`, which covers the identity of `M`. A level `F⁻¹(c)` has the contractible almost
existence property in `W` for the magnetic form `ω_σ` exactly when the level `c` of `F ∘ τ⁻¹`,
the hypersurface `τ(F⁻¹(c))`, has it in `τ(W)` for the canonical form `ω`. -/
theorem hasContractibleAlmostExistence_magneticSymplecticForm_iff (σ : SmoothForm I M ℝ 1)
    {W : Set (CotangentBundle I M)} {F : CotangentBundle I M → ℝ} {c : ℝ} :
    (magneticSymplecticForm σ).HasContractibleAlmostExistence W F c ↔
      (symplecticForm I M).HasContractibleAlmostExistence
        (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv (-σ))
          (SmoothForm.degreeOneEquiv (-σ)).contMDiff '' W)
        (F ∘ (vectorBundleTranslateDiffeomorph (SmoothForm.degreeOneEquiv (-σ))
          (SmoothForm.degreeOneEquiv (-σ)).contMDiff).symm) c :=
  (isSymplectic_symplecticForm.isNondegenerate.hasContractibleAlmostExistence_image_iff _
    (mpullback_vectorBundleTranslateDiffeomorph_neg_symplecticForm σ)).symm

end CotangentBundle

end TauCeti
