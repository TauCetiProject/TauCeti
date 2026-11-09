/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Submersion
public import TauCeti.Geometry.Manifold.Instances.MappingTorus
public import TauCeti.Geometry.Manifold.Submersion.LocalDiffeomorph

/-!
# The vertical distribution of a smooth mapping torus

Let `φ : M ≃ₘ^n⟮I, I⟯ M` be a `C^n` diffeomorphism of a locally compact Hausdorff `C^n` manifold
modelled on `E`, and let `p : Y_φ → ℝ / ℤ`, `[t, x] ↦ [t]`, be the projection of its mapping torus
to the circle (`TauCeti.SmoothMappingTorus.proj`). This file proves that `p` is a `C^n`
submersion, with the model space `E` of the fibre as complement. On the covering space `ℝ × M` it
is the first projection followed by the quotient map `ℝ → ℝ / ℤ`, and both the orbit projection
`ℝ × M → Y_φ` and the quotient map of the circle are local diffeomorphisms.

Consequently, when `E` is finite-dimensional, the kernels `V_y = ker dp_y` form a `C^m`
distribution of rank `dim E` on `Y_φ` for every `m` with `m + 1 ≤ n`, the **vertical
distribution** of the mapping torus. Its local frames are the submersion-coordinate frames of
`Manifold.IsSubmersionAtOfComplement.isDistributionFrameOn_ker_mfderiv`, and
`TauCeti.IsContMDiffDistribution.contMDiffVectorBundle` makes it a `C^m` vector bundle, the
vertical tangent bundle of `Y_φ`. At each point it is the tangent space of the fibre through that
point (`TauCeti.SmoothMappingTorus.range_mfderiv_mk`), and it is complementary to the line spanned
by the suspension vector field `T = ∂_t`
(`TauCeti.SmoothMappingTorus.isCompl_span_timeVectorField_ker_mfderiv_proj`). No compactness of
`M` is needed.

## Main results

* `TauCeti.SmoothMappingTorus.isSubmersionOfComplement_proj`,
  `TauCeti.SmoothMappingTorus.isSubmersion_proj`: the projection of the mapping torus to the
  circle is a `C^n` submersion with complement `E`.
* `TauCeti.SmoothMappingTorus.isContMDiffDistribution_ker_mfderiv_proj`: the vertical
  distribution `y ↦ ker dp_y` of a `C^n` mapping torus is a `C^m` distribution of rank `dim E`
  for every `m` with `m + 1 ≤ n`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 4 (submersions) and Chapter 19 (distributions).
-/

public section

open Manifold Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [LocallyCompactSpace M]

section Submersion

variable {n : ℕ∞ω} [IsManifold I n M] (φ : M ≃ₘ^n⟮I, I⟯ M)

/-- The projection `[t, x] ↦ [t]` of the mapping torus to the circle is a `C^n` submersion, with
the model space `E` of the fibre as complement. Lifted to `ℝ × M` it is the first projection
followed by the quotient map `ℝ → ℝ / ℤ`. -/
theorem isSubmersionOfComplement_proj :
    IsSubmersionOfComplement E (𝓘(ℝ).prod I) 𝓘(ℝ) n (proj φ) := by
  refine isSubmersionOfComplement_iff.2 fun y ↦ ?_
  obtain ⟨p, rfl⟩ := uncurry_mk_surjective φ y
  have hlift : proj φ ∘ Function.uncurry (mk φ) = ((↑) : ℝ → UnitAddCircle) ∘ Prod.fst :=
    funext fun p ↦ proj_mk φ p.1 p.2
  rw [← (isLocalDiffeomorph_uncurry_mk φ p).isSubmersionAtOfComplement_comp_iff, hlift]
  exact (AddCircle.isLocalDiffeomorph_coe 1 n p.1).comp_isSubmersionAtOfComplement
    (isSubmersionOfComplement_fst.isSubmersionAt p)

/-- The projection `[t, x] ↦ [t]` of the mapping torus to the circle is a `C^n` submersion. -/
theorem isSubmersion_proj : IsSubmersion (𝓘(ℝ).prod I) 𝓘(ℝ) n (proj φ) :=
  (isSubmersionOfComplement_proj φ).isSubmersion

end Submersion

/-- **The vertical distribution of a mapping torus.** For a `C^n` diffeomorphism `φ` of a manifold
modelled on a finite-dimensional space `E`, the vertical tangent spaces `ker dp_y` of the
projection `p : Y_φ → ℝ / ℤ` form a `C^m` distribution of rank `dim E` on the mapping torus, for
every `m` with `m + 1 ≤ n`. The `C^1` manifold structure of `Y_φ` used in the statement is found
by instance search when `n = ∞`, and comes from `IsManifold.of_le` otherwise. -/
theorem isContMDiffDistribution_ker_mfderiv_proj [FiniteDimensional ℝ E] {n : ℕ∞ω}
    [IsManifold I n M] (φ : M ≃ₘ^n⟮I, I⟯ M) [IsManifold (𝓘(ℝ).prod I) 1 (SmoothMappingTorus φ)]
    {m : ℕ∞ω} (hm : m + 1 ≤ n) :
    IsContMDiffDistribution (𝓘(ℝ).prod I) m (finrank ℝ E)
      fun y : SmoothMappingTorus φ ↦ (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker := by
  have h := (isSubmersion_proj φ).isContMDiffDistribution_ker_mfderiv hm
  rwa [finrank_prod, finrank_self, Nat.add_sub_cancel_left] at h

end SmoothMappingTorus

end TauCeti
