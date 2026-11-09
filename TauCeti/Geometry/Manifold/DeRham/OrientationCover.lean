/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
public import TauCeti.Geometry.Manifold.Orientation.Cover.Descent
import TauCeti.Geometry.Manifold.Orientation.Cover.Integration

/-!
# De Rham cohomology and the orientation double cover

Let `π : M' → M` be the orientation double cover of a manifold `M`, and `τ` its deck involution,
which reverses the canonical orientation of `M'`.

**Pullback to the cover is injective on cohomology.** If `π^*φ = dη` on `M'`, then the
deck-invariant part `(η + τ^*η) / 2` of the primitive is still a primitive of `π^*φ`, because
`π ∘ τ = π`. Being deck-invariant, it is the pullback `π^*ψ` of a smooth form `ψ` on `M`, and
`dψ = φ` because pullback along the surjective local diffeomorphism `π` is injective
(`TauCeti.Manifold.OrientationCover.exists_mextDerivₗ_eq_of_mextDerivₗ_eq_mpullback_proj`).
The support of `ψ` is the image under `π` of the support of the invariant part, so `ψ` is
compactly supported when `η` is. Hence `π^*` is injective on de Rham cohomology and on
compactly supported de Rham cohomology, in every degree and with no orientability, connectedness
or compactness assumption.

**Integrals of pulled-back top forms vanish.** Since `τ` reverses the canonical orientation, the
integral of a `τ`-invariant top form on `M'` equals its own negative. Pullbacks along `π` are
`τ`-invariant, so `∫_{M'} π^*φ = 0` for every top form `φ` on `M`
(`TauCeti.Manifold.OrientationCover.integralTopForm_mpullback_proj_eq_zero`), and integration
`H^n_c(M') → ℝ` vanishes on the image of `π^*`.

These are the two steps by which top-degree cohomology of a nonorientable manifold is reduced to
the orientable case. When `M` is connected and nonorientable, `M'` is connected and oriented, so
if integration is injective on `H^n_c(M')`, the class `π^*[φ]` of integral zero vanishes and then
`[φ] = 0` in `H^n_c(M)`.

## Main results

* `TauCeti.Manifold.OrientationCover.deRhamCohomology_map_proj_injective`: pullback to the
  orientation cover is injective on de Rham cohomology.
* `TauCeti.Manifold.OrientationCover.compactlySupportedDeRhamCohomology_map_proj_injective`:
  pullback to the orientation cover is injective on compactly supported de Rham cohomology.
* `TauCeti.Manifold.OrientationCover.integral_map_proj_eq_zero`: integration on top compactly
  supported cohomology of the cover vanishes on classes pulled back from `M`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, proof of Theorem 17.34.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Chapter I, §6
  (forms on a covering invariant under the deck transformations).
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti.Manifold.OrientationCover

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section Primitive

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [IsManifold I ∞ M]

/-- Pullback to the orientation double cover is injective on de Rham cohomology, in every
degree. -/
theorem deRhamCohomology_map_proj_injective (k : ℕ) :
    Function.Injective (deRhamCohomology.map
      (VectorBundleOrientationCover.proj : OrientationCover I M → M) contMDiff_proj k) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨φ, rfl⟩ := deRhamCohomology.mk_surjective I k c
  rw [deRhamCohomology.map_mk, deRhamCohomology.mk_eq_zero_iff, closedForms.coe_mpullback] at hc
  rw [deRhamCohomology.mk_eq_zero_iff]
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hc ⊢
    exact smoothForm_mpullback_proj_injective (hc.trans (map_zero _).symm)
  | succ k =>
    rw [exactForms_succ] at hc ⊢
    obtain ⟨η, hη⟩ := hc
    obtain ⟨ψ, hψ, -⟩ := exists_mextDerivₗ_eq_of_mextDerivₗ_eq_mpullback_proj hη
    exact ⟨ψ, hψ⟩

/-- Pullback to the orientation double cover is injective on compactly supported de Rham
cohomology, in every degree. -/
theorem compactlySupportedDeRhamCohomology_map_proj_injective (k : ℕ) :
    Function.Injective (compactlySupportedDeRhamCohomology.map
      (VectorBundleOrientationCover.proj : OrientationCover I M → M) contMDiff_proj
      (isProperMap_proj I M) k) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective I k c
  rw [compactlySupportedDeRhamCohomology.map_mk, compactlySupportedDeRhamCohomology.mk_eq_zero_iff,
    compactlySupportedClosedForms.coe_mpullback] at hc
  rw [compactlySupportedDeRhamCohomology.mk_eq_zero_iff]
  cases k with
  | zero =>
    rw [exactCompactlySupportedForms_zero, Submodule.mem_bot] at hc ⊢
    exact smoothForm_mpullback_proj_injective (hc.trans (map_zero _).symm)
  | succ k =>
    rw [exactCompactlySupportedForms_succ] at hc ⊢
    obtain ⟨η, hηc, hη⟩ := hc
    obtain ⟨ψ, hψ, hψη⟩ := exists_mextDerivₗ_eq_of_mextDerivₗ_eq_mpullback_proj hη
    refine ⟨ψ, (mem_compactlySupportedForms I).mpr ?_, hψ⟩
    -- The support of `ψ` is the projection of the support of the invariant part of `η`.
    have h := isCompact_tsupport_invariantPart VectorBundleOrientationCover.deck.isProperMap
      ((mem_compactlySupportedForms I).mp hηc)
    rw [← hψη, RoughForm.tsupport_mpullback_eq_preimage _ (isCoveringMap_proj I M).continuous
      (isCoveringMap_proj I M).isLocalHomeomorph.isOpenMap fun p ↦
        (isLocalDiffeomorph_proj (n := 1)).isInvertible_mfderiv one_ne_zero p] at h
    simpa only [image_preimage_eq _ (VectorBundleOrientationCover.surjective_proj
      (Fintype.card_fin _))] using h.image (isCoveringMap_proj I M).continuous

end Primitive

section Integral

/-- Integration on top compactly supported cohomology of the orientation double cover, for its
canonical orientation, vanishes on every class pulled back from `M`. -/
@[simp]
theorem integral_map_proj_eq_zero [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] (c : compactlySupportedDeRhamCohomology I M (Module.finrank ℝ E)) :
    compactlySupportedDeRhamCohomology.integral canonicalOrientation
      (compactlySupportedDeRhamCohomology.map VectorBundleOrientationCover.proj contMDiff_proj
        (isProperMap_proj I M) _ c) = 0 := by
  obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective I _ c
  rw [compactlySupportedDeRhamCohomology.map_mk, compactlySupportedDeRhamCohomology.integral_mk,
    compactlySupportedClosedForms.coe_mpullback, SmoothForm.coe_mpullback]
  exact integralTopForm_mpullback_proj_eq_zero _

end Integral

end TauCeti.Manifold.OrientationCover
