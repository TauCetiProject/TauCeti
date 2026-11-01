/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Geometry.Lie.Adjoint.Basic

/-!
# The adjoint and coadjoint representations on the tangent Lie algebra

For a Lie group `G` with tangent Lie algebra `𝔤 = GroupLieAlgebra I G`, the differential at the
identity of conjugation, `Ad_g = TauCeti.Lie.adjointContinuousLinearMap g`, is a linear
representation of `G` on `𝔤` (`TauCeti.Lie.adjointRepresentation`). Its dual is the
**coadjoint representation** of `G` on `𝔤*` (`TauCeti.Lie.coadjointRepresentation`),

`(Ad*_g ν)(ξ) = ν(Ad_{g⁻¹} ξ)`.

This is the action through which the group enters the equivariance condition
`μ(g • x) = Ad*_g (μ x)` of a moment map `μ : M → 𝔤*`.

Both representations are built from Mathlib's `Representation` API, the coadjoint one as
`Representation.dual`, so the group laws `Ad*_{gh} = Ad*_g ∘ Ad*_h` and `Ad*_1 = id` are the
`map_mul` and `map_one` of a monoid homomorphism.

## Main definitions

* `TauCeti.Lie.adjointRepresentation`: `g ↦ Ad_g` as a representation of `G` on `𝔤`.
* `TauCeti.Lie.coadjointRepresentation`: its dual, `g ↦ Ad*_g`, a representation on `𝔤*`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.1.
* J. Marsden and T. Ratiu, *Introduction to Mechanics and Symmetry*, second edition, Springer,
  1999, Section 9.3.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 1 G]

variable (I G) in
/-- The **adjoint representation** of a Lie group `G` on its tangent Lie algebra: `g` acts by the
differential `Ad_g` at the identity of conjugation by `g`. -/
def adjointRepresentation : Representation 𝕜 G (GroupLieAlgebra I G) where
  toFun g := (adjointContinuousLinearMap (I := I) g : GroupLieAlgebra I G →ₗ[𝕜] GroupLieAlgebra I G)
  map_one' := by
    rw [adjointContinuousLinearMap_one]
    rfl
  map_mul' g h := by
    rw [adjointContinuousLinearMap_mul]
    rfl

@[simp]
theorem adjointRepresentation_apply (g : G) (ξ : GroupLieAlgebra I G) :
    adjointRepresentation I G g ξ = adjointContinuousLinearMap (I := I) g ξ :=
  (rfl)

variable (I G) in
/-- The **coadjoint representation** of a Lie group `G` on the dual `𝔤*` of its tangent Lie
algebra, the dual of the adjoint representation: `(Ad*_g ν)(ξ) = ν(Ad_{g⁻¹} ξ)`. -/
def coadjointRepresentation : Representation 𝕜 G (Module.Dual 𝕜 (GroupLieAlgebra I G)) :=
  (adjointRepresentation I G).dual

@[simp]
theorem coadjointRepresentation_apply_apply (g : G) (ν : Module.Dual 𝕜 (GroupLieAlgebra I G))
    (ξ : GroupLieAlgebra I G) :
    coadjointRepresentation I G g ν ξ = ν (adjointContinuousLinearMap (I := I) g⁻¹ ξ) :=
  (rfl)

/-- The coadjoint action of `g` precomposes with the adjoint action of `g⁻¹`. -/
theorem coadjointRepresentation_apply (g : G) (ν : Module.Dual 𝕜 (GroupLieAlgebra I G)) :
    coadjointRepresentation I G g ν = ν ∘ₗ adjointRepresentation I G g⁻¹ :=
  (rfl)

/-- The coadjoint action intertwines the pairing: `(Ad*_g ν)(Ad_g ξ) = ν(ξ)`. -/
theorem coadjointRepresentation_apply_adjointContinuousLinearMap (g : G)
    (ν : Module.Dual 𝕜 (GroupLieAlgebra I G)) (ξ : GroupLieAlgebra I G) :
    coadjointRepresentation I G g ν (adjointContinuousLinearMap (I := I) g ξ) = ν ξ := by
  rw [coadjointRepresentation_apply_apply, ← ContinuousLinearMap.comp_apply,
    ← adjointContinuousLinearMap_mul, inv_mul_cancel, adjointContinuousLinearMap_one,
    ContinuousLinearMap.id_apply]

end TauCeti.Lie
