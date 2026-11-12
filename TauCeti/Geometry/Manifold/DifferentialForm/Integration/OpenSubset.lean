/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset

/-!
# Integration of top forms over open subsets

An open subset `U` of an oriented manifold `M` carries the restricted orientation, for which the
inclusion `U → M` is an orientation-preserving open embedding. Change of variables along it shows
that integrating a top form over `M` or over `U` gives the same result whenever the form is
supported in `U`. Equivalently, for open subsets `U ≤ W`, extending a compactly supported top
form on `U` by zero to `W` does not change its integral.

This localizes integration: a compactly supported top form on a small open subset, such as a
coordinate ball, has the same integral on the whole manifold as on that subset. It is how
integration on compactly supported cohomology interacts with the extension-by-zero maps
`H^n_c(U) → H^n_c(W)`.

## Main results

* `TauCeti.integralTopForm_mpullback_subtypeVal`: `∫_U φ|_U = ∫_M φ` for a top form `φ` on `M`
  supported in `U`.
* `TauCeti.integralTopForm_extendByZero`: `∫_W ext ω = ∫_U ω` for a compactly supported top form
  `ω` on `U ≤ W`, on a Hausdorff manifold.
* `TopologicalSpace.Opens.integrableTopForm_mpullback_subtypeVal_iff`,
  `TauCeti.integrableTopForm_extendByZero_iff`: restriction and extension by zero preserve and
  reflect integrability.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 16.6.
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {k : ℕ}

namespace TopologicalSpace.Opens

open TauCeti

/-- Restricting a top form supported in an open subset `U` preserves and reflects
integrability. -/
theorem integrableTopForm_mpullback_subtypeVal_iff (U : Opens M) {φ : RoughForm I M ℝ k}
    (hφ : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ U) :
    IntegrableTopForm (mpullback I I ((↑) : U → M) φ) ↔ IntegrableTopForm φ :=
  U.isOpenEmbedding'.integrableTopForm_mpullback_iff
    (fun x ↦ (isLocalDiffeomorph_subtype_val (n := 1) x).isInvertible_mfderiv one_ne_zero) rfl
    (by rwa [Subtype.range_coe])

end TopologicalSpace.Opens

namespace TauCeti

/-- **Integration over an open subset.** The integral over `M` of a top form supported in an open
subset `U` is its integral over `U`, for the restricted orientation: `∫_U φ|_U = ∫_M φ`. -/
theorem integralTopForm_mpullback_subtypeVal (o : Manifold.Orientation I M (Fin k)) (U : Opens M)
    {φ : RoughForm I M ℝ k} (hφ : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ ⊆ U) :
    integralTopForm (o.restrict U) (mpullback I I ((↑) : U → M) φ) =
      integralTopForm o φ :=
  U.isOpenEmbedding'.integralTopForm_mpullback_of_isOrientationPreservingAt
    (o.isOrientationPreservingAt_restrict U) (by rwa [Subtype.range_coe])

section T2

variable [T2Space M]

/-- On a Hausdorff manifold, extending a compactly supported top form on `U ≤ W` by zero to `W`
preserves and reflects integrability. -/
theorem integrableTopForm_extendByZero_iff {U W : Opens M} (h : U ≤ W) {ω : RoughForm I U ℝ k}
    (hω : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ω)) :
    IntegrableTopForm (RoughForm.extendByZero W ω) ↔ IntegrableTopForm ω := by
  conv_rhs => rw [← RoughForm.mpullback_inclusion_extendByZero h ω]
  have he : IsOpenEmbedding (Opens.inclusion h) := Opens.isOpenEmbedding_of_le h
  exact (he.integrableTopForm_mpullback_iff
    -- The derivative of the inclusion is the identity of the model space.
    (fun x ↦ ⟨.refl ℝ _,
      ContinuousLinearMap.ext fun v ↦ (Manifold.mfderiv_inclusion_apply h x v).symm⟩) rfl
    ((RoughForm.tsupport_extendByZero_subset h hω).trans (image_subset_range _ _))).symm

/-- **Extension by zero preserves integrals.** On a Hausdorff manifold, extending a compactly
supported top form on `U ≤ W` by zero to `W` does not change its integral, for the orientations
restricted from `M`: `∫_W ext ω = ∫_U ω`. -/
theorem integralTopForm_extendByZero (o : Manifold.Orientation I M (Fin k)) {U W : Opens M}
    (h : U ≤ W) {ω : RoughForm I U ℝ k}
    (hω : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ω)) :
    integralTopForm (o.restrict W) (RoughForm.extendByZero W ω) =
      integralTopForm (o.restrict U) ω := by
  conv_rhs => rw [← RoughForm.mpullback_inclusion_extendByZero h ω]
  have he : IsOpenEmbedding (Opens.inclusion h) := Opens.isOpenEmbedding_of_le h
  exact (he.integralTopForm_mpullback_of_isOrientationPreservingAt
    (o.isOrientationPreservingAt_restrict_inclusion h)
    ((RoughForm.tsupport_extendByZero_subset h hω).trans (image_subset_range _ _))).symm

end T2

end TauCeti
