/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Isotropic
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# The round sphere is coisotropic

For the unit sphere `S` of a finite-dimensional real inner product space `E` with a linear
symplectic form `ω`, the inclusion `S → E` is a coisotropic embedding for the constant form `ω`
(`TauCeti.SymplecticForm.isCoisotropicEmbedding_coe_sphere`): it is a hypersurface, and maps of
codimension at most one with injective differentials are coisotropic
(`TauCeti.SmoothTwoForm.IsNondegenerate.isCoisotropicMap_of_finrank_le_finrank_add_one`). The
kernel of the form it induces is then a line field, the characteristic line field of `S`. It is
spanned by the Reeb vector field of the contact form `λ|S`
(`TauCeti.SymplecticForm.ker_bilinFormAt_mpullback_coe_sphere`, in
`TauCeti.Geometry.Contact.Sphere`); read in `E`, it is the line `ℝ (K x)` for any `K` with
`ω(u, K v) = ⟪u, v⟫` (`TauCeti.SymplecticForm.map_ker_bilinFormAt_mpullback_coe_sphere`). For `ℂⁿ`
with `ω = Σⱼ dxⱼ ∧ dyⱼ`, `K` is multiplication by `i`, so the characteristic line of `S²ⁿ⁻¹` at
`z` is `ℝ (i z)`, the tangent line of the Hopf circle through `z`.

## Main results

* `TauCeti.SymplecticForm.isCoisotropicEmbedding_coe_sphere`: the unit sphere of a symplectic
  inner product space is a coisotropic submanifold.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 8 (coisotropic submanifolds and the coisotropic embedding theorem).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their characteristic line bundles).
-/

public section

noncomputable section

open Module Metric
open scoped Manifold

namespace TauCeti

/-! ### The round sphere -/

namespace SymplecticForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)] (ω : SymplecticForm E)

/-- **The unit sphere is coisotropic.** The inclusion of the unit sphere of a finite-dimensional
real inner product space with a linear symplectic form `ω` is a coisotropic embedding for the
constant form `ω`. -/
theorem isCoisotropicEmbedding_coe_sphere :
    ω.isNondegenerate_constSmooth.IsCoisotropicEmbedding (𝓡 n)
      ((↑) : sphere (0 : E) 1 → E) := by
  refine ⟨contMDiff_coe_sphere.isImmersion_of_injective_mfderiv (by simp)
    injective_mvfderiv_subtypeVal_sphere, Topology.IsEmbedding.subtypeVal, ?_⟩
  refine ω.isNondegenerate_constSmooth.isCoisotropicMap_of_finrank_le_finrank_add_one ?_
    injective_mvfderiv_subtypeVal_sphere
  rw [finrank_euclideanSpace_fin, (Fact.out : finrank ℝ E = n + 1)]

end SymplecticForm

end TauCeti
