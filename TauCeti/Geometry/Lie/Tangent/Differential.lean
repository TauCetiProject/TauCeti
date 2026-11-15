/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# The differential at the identity of a group homomorphism

A group homomorphism `φ : K →* G` between groups modelled on manifolds has a differential at the
identity `dφ : Lie(K) → Lie(G)`, a continuous linear map between the tangent Lie algebras. This
file names that map and proves its functor laws: the identity homomorphism has identity
differential, and the chain rule holds at the identity for homomorphisms differentiable there.

## Main definitions

* `MonoidHom.groupLieAlgebraMap`: the differential at the identity of a group homomorphism, as a
  continuous linear map between tangent Lie algebras.

## Main results

* `MonoidHom.groupLieAlgebraMap_id`: the differential of the identity is the identity.
* `MonoidHom.groupLieAlgebraMap_comp`: the chain rule at the identity.
-/

public section

noncomputable section

open scoped Manifold

namespace MonoidHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {F HK : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace HK]
  {K : Type*} [TopologicalSpace K] [ChartedSpace HK K] [Group K]

/-- The differential `dφ : Lie(K) → Lie(G)` at the identity of a group homomorphism `φ : K →* G`,
as a continuous linear map between the tangent Lie algebras. It is zero when `φ` is not
differentiable at the identity. -/
def groupLieAlgebraMap (φ : K →* G) (J : ModelWithCorners 𝕜 F HK)
    (I : ModelWithCorners 𝕜 E H) : GroupLieAlgebra J K →L[𝕜] GroupLieAlgebra I G :=
  mfderiv J I φ 1

/-- The differential at the identity of `φ`, applied to `ξ`. -/
theorem groupLieAlgebraMap_apply (φ : K →* G) (J : ModelWithCorners 𝕜 F HK)
    (ξ : GroupLieAlgebra J K) : φ.groupLieAlgebraMap J I ξ = mfderiv J I φ 1 ξ :=
  (rfl)

/-- The differential of the identity homomorphism is the identity. -/
@[simp]
theorem groupLieAlgebraMap_id :
    (MonoidHom.id G).groupLieAlgebraMap I I = ContinuousLinearMap.id 𝕜 (GroupLieAlgebra I G) := by
  ext ξ
  rw [groupLieAlgebraMap_apply, coe_id, mfderiv_id]

/-- **The chain rule at the identity.** The differential of a composite of homomorphisms that are
differentiable at the identity is the composite of their differentials. -/
theorem groupLieAlgebraMap_comp {F' HK' : Type*} [NormedAddCommGroup F']
    [NormedSpace 𝕜 F'] [TopologicalSpace HK'] {J' : ModelWithCorners 𝕜 F' HK'} {K' : Type*}
    [TopologicalSpace K'] [ChartedSpace HK' K'] [Group K'] {J : ModelWithCorners 𝕜 F HK}
    (ψ : K →* G) (φ : K' →* K) (hψ : MDifferentiableAt J I ψ 1)
    (hφ : MDifferentiableAt J' J φ 1) :
    (ψ.comp φ).groupLieAlgebraMap J' I =
      (ψ.groupLieAlgebraMap J I).comp (φ.groupLieAlgebraMap J' J) := by
  ext ξ
  simp only [ContinuousLinearMap.comp_apply, groupLieAlgebraMap_apply, coe_comp]
  exact mfderiv_comp_apply_of_eq 1 hψ hφ (map_one φ) ξ

end MonoidHom
