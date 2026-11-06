/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Orientation
public import TauCeti.Geometry.Manifold.Orientation.AddCircle
public import TauCeti.Geometry.Symplectic.Manifold.Orientation
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Basic

/-!
# The symplectic orientation of a symplectic suspension

Let `φ` be a symplectomorphism of a finite-dimensional symplectic manifold `(M, σ)`, let
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus and let
`X_φ = (ℝ / ℤ)_s × Y_φ` carry the symplectic form `Ω = ds ∧ dt + σ_v`
(`TauCeti.SmoothMappingTorus.suspensionForm`). Since `φ` preserves the symplectic orientation of
`σ`, the mapping torus carries the orientation `dt` followed by the symplectic orientation of the
fibre (`TauCeti.SmoothMappingTorus.orientation`). This file proves that the symplectic orientation
of `Ω` is the product of the positive orientation of the circle `(ℝ / ℤ)_s` with this orientation
of `Y_φ` (`TauCeti.SmoothMappingTorus.orientation_suspensionForm`). Informally, in the
coordinates `(s, t, x)` a basis `(∂_s, ∂_t, b)` is positive for `Ω` exactly when `b` is positive
for the symplectic orientation of `σ`: the orientation of `Ω` is `ds ∧ dt` followed by the fibre
symplectic orientation.

The proof is pointwise linear algebra. In the coordinates `(s, t, x)` the form `Ω` is
`ds ∧ dt + σ` (`TauCeti.SmoothMappingTorus.eval₂_suspensionForm_mk`), the direct sum of the standard
symplectic form of the plane `ℝ²_(s,t)` with `σ`, reassociated. The symplectic orientation of a
direct sum is the product orientation (`TauCeti.SymplecticForm.orientation_prod`), that of the
standard plane is the orientation of `(∂_s, ∂_t)`
(`TauCeti.SymplecticForm.orientation_stdSymplecticForm_real`), and reassociating product
orientations only relabels the index (`Orientation.map_prodAssoc_prod`); together these give
`TauCeti.SymplecticForm.orientation_transport_prodAssoc_stdSymplecticForm_prod`.

## Main results

* `TauCeti.SmoothMappingTorus.isSymplectomorphism_prodCongr_mfderiv_mk`: in the coordinates
  `(s, t, x)`, the identity times the differential of `(t, x) ↦ [t, x]` is a symplectomorphism from
  the reassociated direct sum of `ds ∧ dt` and `σ_x` to `Ω`.
* `TauCeti.SmoothMappingTorus.orientation_suspensionForm`: the symplectic orientation of
  `Ω = ds ∧ dt + σ_v` is the product of the orientation of the circle and the orientation of the
  mapping torus given by `dt` and the symplectic orientation of `σ`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (the symplectic form `ds ∧ dt + ω_φ` on
  `S¹ × Y_φ`).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 2.1 (the orientation of a symplectic vector space).
-/

public section

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  {φ : M ≃ₘ⟮I, I⟯ M} {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
  {m : ℕ}

omit [FiniteDimensional ℝ E] in
/-- In the coordinates `(s, t, x)`, let `D` be a linear equivalence whose underlying map is the
differential of `(t, x) ↦ [t, x]` at `(t, x)`. Then `id × D` is a symplectomorphism from the direct
sum of the standard symplectic plane `ds ∧ dt` with `σ_x`, reassociated, to `Ω = ds ∧ dt + σ_v` at
`(θ, [t, x])`. -/
theorem isSymplectomorphism_prodCongr_mfderiv_mk (hN : σ.IsNondegenerate) (θ : UnitAddCircle)
    (t : ℝ) (x : M)
    (D : TangentSpace (𝓘(ℝ).prod I) (t, x) ≃L[ℝ]
      TangentSpace (𝓘(ℝ).prod I) (uncurry (mk φ) (t, x)))
    (hD : (D : TangentSpace (𝓘(ℝ).prod I) (t, x) →L[ℝ]
      TangentSpace (𝓘(ℝ).prod I) (uncurry (mk φ) (t, x))) =
        mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)) :
    SymplecticForm.IsSymplectomorphism (((stdSymplecticForm (V := ℝ)).prod
      (hN.symplecticFormAt x)).transport (LinearEquiv.prodAssoc ℝ ℝ ℝ (TangentSpace I x)))
      (((isNondegenerate_suspensionForm_iff (hσ := hσ)).2 hN).symplecticFormAt
        (θ, mk φ t x))
      ((LinearEquiv.refl ℝ ℝ).prodCongr D.toLinearEquiv :
        (ℝ × (ℝ × TangentSpace I x)) ≃ₗ[ℝ]
          TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (θ, mk φ t x)) := by
  -- Name the map, so that the goal stays type correct when its tangent spaces are unfolded.
  let L : (ℝ × (ℝ × TangentSpace I x)) ≃ₗ[ℝ]
      TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (θ, mk φ t x) :=
    (LinearEquiv.refl ℝ ℝ).prodCongr D.toLinearEquiv
  change SymplecticForm.IsSymplectomorphism _ _ L
  rw [SymplecticForm.isSymplectomorphism_iff]
  rintro ⟨a, b, v⟩ ⟨a', b', v'⟩
  have h := eval₂_suspensionForm_mk (hσ := hσ) θ t x a a' b b' v v'
  rw [← hD, ContinuousLinearEquiv.coe_coe] at h
  -- `L (a, b, v)` is the vector `a ∂_s + b ∂_t + v` of `eval₂_suspensionForm_mk`.
  have hL (a b : ℝ) (v : TangentSpace I x) : L (a, b, v) = (Manifold.tangentSpaceProdEquiv _).symm
      (a, D ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))) := by
    rw [Manifold.tangentSpaceProdEquiv_symm_apply, Manifold.tangentSpaceProdEquiv_symm_apply]
    rfl
  rw [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply, hL, hL, h]
  have hA (p : ℝ × (ℝ × TangentSpace I x)) :
      (LinearEquiv.prodAssoc ℝ ℝ ℝ (TangentSpace I x)).symm p = ((p.1, p.2.1), p.2.2) := rfl
  simp [stdSymplecticForm_apply, hA]
  ring

/-- **The symplectic orientation of a symplectic suspension.** For a symplectomorphism `φ` of
`(M, σ)`, the symplectic orientation of `Ω = ds ∧ dt + σ_v` on `(ℝ / ℤ)_s × Y_φ` is the product of
the positive orientation of the circle with the orientation of the mapping torus `Y_φ` given by
`dt` followed by the symplectic orientation of `σ`. -/
theorem orientation_suspensionForm (hN : σ.IsNondegenerate) (hm : finrank ℝ E = m) :
    ((isNondegenerate_suspensionForm_iff (hσ := hσ)).2 hN).orientation (k := 1 + (1 + m))
        (by rw [finrank_prod, finrank_prod, finrank_self, hm]) =
      (AddCircle.orientation 1).prod (orientation φ (hN.orientation hm)
        (hN.isOrientationPreservingAt_orientation hm hN hm φ hσ)) := by
  refine Manifold.Orientation.ext fun z ↦ ?_
  obtain ⟨θ, y⟩ := z
  obtain ⟨⟨t, x⟩, rfl⟩ : ∃ p : ℝ × M, mk φ p.1 p.2 = y := uncurry_mk_surjective φ y
  obtain ⟨D, hD, hDo⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).mp
    (isOrientationPreservingAt_uncurry_mk φ (hN.orientation hm)
      (hN.isOrientationPreservingAt_orientation hm hN hm φ hσ) (t, x))
  have hL := isSymplectomorphism_prodCongr_mfderiv_mk (hσ := hσ) hN θ t x D hD
  -- The tangent spaces of `M` are its model space `E`, and `uncurry (mk φ) (t, x)` is `[t, x]`.
  have hm' : finrank ℝ (TangentSpace I x) = m := hm
  have hDo' : Orientation.map (Fin (1 + m)) D.toLinearEquiv
      ((Manifold.Orientation.real.prod (hN.orientation hm)).orientationAt (t, x)) =
        (orientation φ (hN.orientation hm)
          (hN.isOrientationPreservingAt_orientation hm hN hm φ hσ)).orientationAt (mk φ t x) :=
    hDo
  rw [SmoothTwoForm.IsNondegenerate.orientationAt_orientation,
    ← hL.map_orientation (by rw [finrank_prod, finrank_prod, finrank_self, hm']),
    SymplecticForm.orientation_transport_prodAssoc_stdSymplecticForm_prod _ hm',
    Manifold.Orientation.orientationAt_prod, AddCircle.orientationAt_orientation]
  dsimp only
  rw [← hDo', Manifold.Orientation.orientationAt_prod,
    Manifold.Orientation.orientationAt_real,
    SmoothTwoForm.IsNondegenerate.orientationAt_orientation]
  -- Both sides are now `∂_s` followed by the image under `D` of `∂_t` and the orientation of `σ`;
  -- they differ only in how the point `x = (t, x).2` and its tangent spaces are written.
  exact (Orientation.map_prod _ _ _ _ (LinearEquiv.refl ℝ ℝ) D.toLinearEquiv).trans
    (by rw [Orientation.map_refl]; rfl)

end SmoothMappingTorus

end TauCeti
