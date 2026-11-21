/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Exact
public import TauCeti.Geometry.Symplectic.Liouville.Radial

/-!
# Isotropic and Lagrangian maps into a complex inner product space

Let `E` be a finite-dimensional complex inner product space, such as `ℂⁿ`, with its constant
symplectic form `Im ⟪·, ·⟫_ℂ` (`TauCeti.imInnerSymplecticForm`). A map `f : M → E` from a manifold
is isotropic exactly when `Im ⟪df v, df w⟫_ℂ = 0` for all tangent vectors `v`, `w` at every point
(`TauCeti.isIsotropicMap_imInnerSymplecticForm_iff`), the differential being read in `E` through
Mathlib's `mvfderiv`. So an immersion is a Lagrangian immersion exactly when these imaginary parts
vanish and its source has half the real dimension of `E`
(`TauCeti.isLagrangianImmersion_imInnerSymplecticForm_iff`); for an immersion of an `n`-manifold
into `ℂⁿ` the dimension condition is automatic
(`TauCeti.isLagrangianImmersion_imInnerSymplecticForm_euclideanSpace_iff`). These are the forms in
which a compact Lagrangian submanifold of `ℂⁿ` is the boundary condition for holomorphic discs.

In real coordinates `z = x + i y` on `ℂⁿ` the same maps are the Lagrangian maps into `ℝⁿ × ℝⁿ` for
the standard symplectic form, since the real and imaginary parts are a linear symplectomorphism
(`TauCeti.isLagrangianMap_imInnerSymplecticForm_iff_comp`).

The radial primitive `λ_z(v) = Im ⟪z, v⟫_ℂ / 2` of `Im ⟪·, ·⟫_ℂ`
(`TauCeti.SymplecticForm.radialPrimitive`), which is `(1/2) Σ_j (x_j dy_j - y_j dx_j)` in real
coordinates, satisfies `dλ = Im ⟪·, ·⟫_ℂ`, and it pulls back to a closed one-form along every
isotropic map (`TauCeti.isClosed_mpullback_radialPrimitive_imInnerSymplecticForm`). Its periods
along the boundary loops of holomorphic discs with Lagrangian boundary are their symplectic areas.

## Main results

* `TauCeti.isIsotropicMap_imInnerSymplecticForm_iff`: isotropy of a map into `E` is the vanishing
  of `Im ⟪df ·, df ·⟫_ℂ`.
* `TauCeti.isLagrangianImmersion_imInnerSymplecticForm_iff` and
  `TauCeti.isLagrangianImmersion_imInnerSymplecticForm_euclideanSpace_iff`: Lagrangian immersions
  into `E` and into `ℂⁿ`.
* `TauCeti.isLagrangianMap_imInnerSymplecticForm_iff_comp`: Lagrangian maps into `ℂⁿ` are those
  whose real and imaginary parts form a Lagrangian map into `ℝⁿ × ℝⁿ`.
* `TauCeti.isClosed_mpullback_radialPrimitive_imInnerSymplecticForm`: the radial primitive pulls
  back to a closed form along an isotropic map.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 2.1 (the standard structure of `ℂⁿ`).
* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347 (holomorphic discs with boundary on a compact Lagrangian submanifold of `ℂⁿ`).
-/

public section

open Manifold Module
open scoped ContDiff Manifold InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- **Isotropic maps into a complex inner product space.** A map `f` is isotropic for
`Im ⟪·, ·⟫_ℂ` exactly when `Im ⟪df v, df w⟫_ℂ = 0` for all tangent vectors at every point. -/
theorem isIsotropicMap_imInnerSymplecticForm_iff {f : N → E} :
    (SymplecticForm.isNondegenerate_constSmooth (imInnerSymplecticForm E)).IsIsotropicMap J f ↔
      ∀ x (v w : TangentSpace J x), (⟪mvfderiv J f x v, mvfderiv J f x w⟫_ℂ).im = 0 := by
  simp only [SmoothTwoForm.IsNondegenerate.isIsotropicMap_iff,
    SymplecticForm.eval₂_constSmooth_mfderiv_eq, imInnerSymplecticForm_apply]

/-- **Lagrangian immersions into a complex inner product space.** An immersion `f` is a Lagrangian
immersion for `Im ⟪·, ·⟫_ℂ` exactly when `Im ⟪df v, df w⟫_ℂ = 0` for all tangent vectors at every
point and the real dimension of the source is half that of `E`. -/
theorem isLagrangianImmersion_imInnerSymplecticForm_iff {f : N → E}
    (hf : IsImmersion J 𝓘(ℝ, E) ∞ f) :
    (SymplecticForm.isNondegenerate_constSmooth (imInnerSymplecticForm E)).IsLagrangianImmersion
        J f ↔
      (∀ x (v w : TangentSpace J x), (⟪mvfderiv J f x v, mvfderiv J f x w⟫_ℂ).im = 0) ∧
        2 * finrank ℝ E' = finrank ℝ E := by
  rw [← isIsotropicMap_imInnerSymplecticForm_iff]
  exact ⟨fun h ↦ ⟨h.isIsotropicMap, h.two_mul_finrank⟩, fun h ↦ ⟨hf, h.1, h.2⟩⟩

/-- **Lagrangian immersions into `ℂⁿ`.** An immersion of a manifold modelled on `ℝⁿ` into `ℂⁿ` is a
Lagrangian immersion for `Im ⟪·, ·⟫_ℂ` exactly when `Im ⟪df v, df w⟫_ℂ = 0` for all tangent vectors
at every point. -/
theorem isLagrangianImmersion_imInnerSymplecticForm_euclideanSpace_iff {ι : Type*} [Fintype ι]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ ι) H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f : M → EuclideanSpace ℂ ι} (hf : IsImmersion I 𝓘(ℝ, EuclideanSpace ℂ ι) ∞ f) :
    (SymplecticForm.isNondegenerate_constSmooth
        (imInnerSymplecticForm (EuclideanSpace ℂ ι))).IsLagrangianImmersion I f ↔
      ∀ x (v w : TangentSpace I x), (⟪mvfderiv I f x v, mvfderiv I f x w⟫_ℂ).im = 0 := by
  rw [isLagrangianImmersion_imInnerSymplecticForm_iff hf, and_iff_left]
  rw [finrank_real_of_complex, finrank_euclideanSpace, finrank_euclideanSpace]

/-- **Lagrangian maps into `ℂⁿ` in real coordinates.** A map `f` into `ℂⁿ` is Lagrangian for
`Im ⟪·, ·⟫_ℂ` exactly when the map `(Re f, Im f)` into `ℝⁿ × ℝⁿ` is Lagrangian for the standard
symplectic form. -/
theorem isLagrangianMap_imInnerSymplecticForm_iff_comp {ι : Type*} [Fintype ι]
    {f : N → EuclideanSpace ℂ ι} :
    (SymplecticForm.isNondegenerate_constSmooth
        (imInnerSymplecticForm (EuclideanSpace ℂ ι))).IsLagrangianMap J f ↔
      (SymplecticForm.isNondegenerate_constSmooth stdSymplecticForm).IsLagrangianMap J
        (complexEuclideanEquivRealProd ι ∘ f) :=
  (isSymplectomorphism_complexEuclideanEquivRealProd_symm.symm.isLagrangianMap_comp_iff).symm

/-- **The radial primitive pulls back to a closed form.** Along an isotropic smooth map `f` into
`E`, the pullback of `λ_z(v) = Im ⟪z, v⟫_ℂ / 2` is closed: `d(f^* λ) = f^* Im ⟪·, ·⟫_ℂ = 0`. -/
theorem isClosed_mpullback_radialPrimitive_imInnerSymplecticForm [IsManifold J ∞ N] {f : N → E}
    (hf : ContMDiff J 𝓘(ℝ, E) ∞ f)
    (h : ∀ x (v w : TangentSpace J x), (⟪mvfderiv J f x v, mvfderiv J f x w⟫_ℂ).im = 0) :
    (SmoothForm.mpullback f hf (imInnerSymplecticForm E).radialPrimitive).IsClosed :=
  (imInnerSymplecticForm E).isClosed_mpullback_radialPrimitive hf
    (isIsotropicMap_imInnerSymplecticForm_iff.2 h)

end TauCeti
