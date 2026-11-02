/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold

/-!
# The real operator dᶜ on complex-valued forms

We use the normalization `dᶜ = i (∂bar - ∂)`, hence `ddᶜ = 2i ∂∂bar` on a complex
manifold. The operator is complex linear on the existing smooth-form carrier. It commutes
with conjugation, so preserves real forms, and is natural under smooth pseudoholomorphic
pullback. Its definition and naturality work for almost complex structures. The square-zero
and anticommutation identities assume `d = ∂ + ∂bar` in two consecutive degrees, and
specialize to complex manifolds using the complex-manifold Dolbeault identities.

These formulas fix the sign and factor used in potentials for fundamental forms and in
Kähler commutator identities. No metric or compactness assumption is involved.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Sections 1.3 and 3.1.
  Here the normalization of dᶜ is explicitly the one displayed above.
-/

public section

noncomputable section

open scoped Manifold ContDiff ComplexConjugate

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [NormedAddCommGroup F] [NormedSpace ℂ F] {k : ℕ}

namespace SmoothAlmostComplexStructure

variable (J : SmoothAlmostComplexStructure I M)

/-- The complex-linear operator `dᶜ = i (∂bar - ∂)` on smooth forms. -/
def dC : SmoothForm I M F k →ₗ[ℂ] SmoothForm I M F (k + 1) :=
  Complex.I • (J.delBar - J.del)

/-- The normalization of `dᶜ` on each form. -/
theorem dC_apply (φ : SmoothForm I M F k) :
    J.dC φ = Complex.I • (J.delBar φ - J.del φ) := (rfl)

section Coefficients

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] {L : F →L[ℝ] G}

/-- Complex-linear changes of coefficients commute with `dᶜ`. -/
theorem mapCoeff_dC (hL : ∀ (c : ℂ) v, L (c • v) = c • L v)
    (φ : SmoothForm I M F k) :
    SmoothForm.mapCoeff L (J.dC φ) = J.dC (SmoothForm.mapCoeff L φ) := by
  simp only [dC_apply, SmoothForm.mapCoeff_smul_of_map_smul L (hL _), map_sub,
    J.mapCoeff_del hL, J.mapCoeff_delBar hL]

/-- Conjugate-linear changes of coefficients also commute with `dᶜ`: the sign from
conjugating `i` cancels the exchange of `∂` and `∂bar`. -/
theorem mapCoeff_dC_of_map_smul_conj
    (hL : ∀ (c : ℂ) v, L (c • v) = conj c • L v) (φ : SmoothForm I M F k) :
    SmoothForm.mapCoeff L (J.dC φ) = J.dC (SmoothForm.mapCoeff L φ) := by
  simp only [dC_apply, SmoothForm.mapCoeff_smul_of_map_smul L (hL _), map_sub,
    J.mapCoeff_del_of_map_smul_conj hL, J.mapCoeff_delBar_of_map_smul_conj hL,
    Complex.conj_I]
  module

end Coefficients

/-- Conjugation commutes with `dᶜ`, so `dᶜ` preserves conjugation-invariant forms. -/
@[simp]
theorem mapCoeff_conj_dC (φ : SmoothForm I M ℂ k) :
    SmoothForm.mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) (J.dC φ) =
      J.dC (SmoothForm.mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) φ) :=
  J.mapCoeff_dC_of_map_smul_conj (fun _ _ ↦ by simp) φ

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M'] {J' : SmoothAlmostComplexStructure I' M'} {u : M → M'}

/-- Pullback by a smooth pseudoholomorphic map commutes with `dᶜ`. -/
theorem mpullback_dC (hu : ContMDiff I I' ∞ u) (hJ : IsPseudoholomorphic J J' u)
    (φ : SmoothForm I' M' F k) :
    SmoothForm.mpullback u hu (J'.dC φ) = J.dC (SmoothForm.mpullback u hu φ) := by
  simp only [dC_apply, SmoothForm.mpullback_smul, map_sub,
    J.mpullback_del hu hJ, J.mpullback_delBar hu hJ]

end Pullback

section DelAddDelBar

variable {J}
  (hd : ∀ φ : SmoothForm I M F k, mextDerivₗ I k φ = J.del φ + J.delBar φ)
  (hd' : ∀ φ : SmoothForm I M F (k + 1), mextDerivₗ I (k + 1) φ = J.del φ + J.delBar φ)
include hd hd'

/-- If `d = ∂ + ∂bar` in degrees `k` and `k+1`, then `ddᶜ = 2i ∂∂bar` on `k`-forms. -/
theorem mextDerivₗ_dC_of_mextDerivₗ_eq_del_add_delBar (φ : SmoothForm I M F k) :
    mextDerivₗ I (k + 1) (J.dC φ) = (2 * Complex.I) • J.del (J.delBar φ) := by
  rw [dC_apply, SmoothForm.mextDerivₗ_smul, map_sub, hd', hd']
  simp only [delBar_delBar_eq_zero_of_mextDerivₗ_eq_del_add_delBar hd hd',
    del_del_eq_zero_of_mextDerivₗ_eq_del_add_delBar hd hd',
    delBar_del_of_mextDerivₗ_eq_del_add_delBar hd hd', add_zero, zero_add]
  module

/-- If `d = ∂ + ∂bar` in degrees `k` and `k+1`, then `dᶜd = -ddᶜ` on `k`-forms. -/
theorem dC_mextDerivₗ_of_mextDerivₗ_eq_del_add_delBar (φ : SmoothForm I M F k) :
    J.dC (mextDerivₗ I k φ) = -mextDerivₗ I (k + 1) (J.dC φ) := by
  rw [mextDerivₗ_dC_of_mextDerivₗ_eq_del_add_delBar hd hd', dC_apply, hd, map_add, map_add]
  simp only [delBar_delBar_eq_zero_of_mextDerivₗ_eq_del_add_delBar hd hd',
    del_del_eq_zero_of_mextDerivₗ_eq_del_add_delBar hd hd',
    delBar_del_of_mextDerivₗ_eq_del_add_delBar hd hd', add_zero, zero_add]
  module

/-- If `d = ∂ + ∂bar` in degrees `k` and `k+1`, then `(dᶜ)² = 0` on `k`-forms. -/
theorem dC_dC_of_mextDerivₗ_eq_del_add_delBar (φ : SmoothForm I M F k) :
    J.dC (J.dC φ) = 0 := by
  rw [dC_apply, dC_apply, map_smul, map_smul, map_sub, map_sub]
  simp only [delBar_delBar_eq_zero_of_mextDerivₗ_eq_del_add_delBar hd hd',
    del_del_eq_zero_of_mextDerivₗ_eq_del_add_delBar hd hd',
    delBar_del_of_mextDerivₗ_eq_del_add_delBar hd hd', sub_zero, zero_sub]
  simp

end DelAddDelBar

end SmoothAlmostComplexStructure

section ComplexManifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {N : Type*} [TopologicalSpace N] [ChartedSpace V N] [IsManifold 𝓘(ℂ, V) ∞ N]

open scoped TauCeti.ComplexManifold
open SmoothAlmostComplexStructure

/-- On a complex manifold, `ddᶜ = 2i ∂∂bar` in every degree. -/
theorem SmoothAlmostComplexStructure.mextDerivₗ_dC_ofComplexManifold
    (φ : SmoothForm 𝓘(ℝ, V) N F k) :
    mextDerivₗ 𝓘(ℝ, V) (k + 1) ((ofComplexManifold V N).dC φ) =
      (2 * Complex.I) • (ofComplexManifold V N).del ((ofComplexManifold V N).delBar φ) :=
  mextDerivₗ_dC_of_mextDerivₗ_eq_del_add_delBar mextDerivₗ_eq_del_add_delBar_ofComplexManifold
    mextDerivₗ_eq_del_add_delBar_ofComplexManifold φ

/-- On a complex manifold, `dᶜd = -ddᶜ` in every degree. -/
theorem SmoothAlmostComplexStructure.dC_mextDerivₗ_ofComplexManifold
    (φ : SmoothForm 𝓘(ℝ, V) N F k) :
    (ofComplexManifold V N).dC (mextDerivₗ 𝓘(ℝ, V) k φ) =
      -mextDerivₗ 𝓘(ℝ, V) (k + 1) ((ofComplexManifold V N).dC φ) :=
  dC_mextDerivₗ_of_mextDerivₗ_eq_del_add_delBar mextDerivₗ_eq_del_add_delBar_ofComplexManifold
    mextDerivₗ_eq_del_add_delBar_ofComplexManifold φ

/-- On a complex manifold, `(dᶜ)² = 0` in every degree. -/
@[simp]
theorem SmoothAlmostComplexStructure.dC_dC_ofComplexManifold
    (φ : SmoothForm 𝓘(ℝ, V) N F k) :
    (ofComplexManifold V N).dC ((ofComplexManifold V N).dC φ) = 0 :=
  dC_dC_of_mextDerivₗ_eq_del_add_delBar mextDerivₗ_eq_del_add_delBar_ofComplexManifold
    mextDerivₗ_eq_del_add_delBar_ofComplexManifold φ

end ComplexManifold

end TauCeti
