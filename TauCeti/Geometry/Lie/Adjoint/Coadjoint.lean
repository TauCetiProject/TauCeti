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

The tangent-space adjoint maps `Ad_g = d(conj_g)_1` of a Lie group `G` form a representation of
`G` on its tangent Lie algebra `𝔤 = GroupLieAlgebra I G`
(`TauCeti.Lie.adjointRepresentation`). Its dual is the **coadjoint representation** of `G` on
`𝔤* = Module.Dual 𝕜 𝔤` (`TauCeti.Lie.coadjointRepresentation`),

`Ad*_g ν = ν ∘ Ad_{g⁻¹}`,

built with Mathlib's `Representation.dual`. The coadjoint action is the action against which
moment maps of Hamiltonian group actions are equivariant.

## Main definitions

* `TauCeti.Lie.adjointRepresentation`: the representation `g ↦ Ad_g` of `G` on `𝔤`.
* `TauCeti.Lie.coadjointRepresentation`: the representation `g ↦ Ad*_g` of `G` on `𝔤*`.

## References

* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §9.3 (the adjoint and coadjoint actions).
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 1 G]

variable (𝕜 I G) in
/-- The **adjoint representation** of a Lie group `G` on its tangent Lie algebra: `g` acts by the
differential `Ad_g` of conjugation by `g` at the identity. -/
def adjointRepresentation : Representation 𝕜 G (GroupLieAlgebra I G) where
  toFun g := adjointContinuousLinearMap (I := I) g
  map_one' := by
    ext X
    simp
  map_mul' g h := by
    ext X
    simp

@[simp]
theorem adjointRepresentation_apply (g : G) (X : GroupLieAlgebra I G) :
    adjointRepresentation 𝕜 I G g X = adjointContinuousLinearMap (I := I) g X :=
  (rfl)

variable (𝕜 I G) in
/-- The **coadjoint representation** of a Lie group `G` on the dual `𝔤*` of its tangent Lie
algebra: `Ad*_g ν = ν ∘ Ad_{g⁻¹}`. -/
def coadjointRepresentation : Representation 𝕜 G (Module.Dual 𝕜 (GroupLieAlgebra I G)) :=
  (adjointRepresentation 𝕜 I G).dual

@[simp]
theorem coadjointRepresentation_apply (g : G) (ν : Module.Dual 𝕜 (GroupLieAlgebra I G))
    (X : GroupLieAlgebra I G) :
    coadjointRepresentation 𝕜 I G g ν X = ν (adjointContinuousLinearMap (I := I) g⁻¹ X) :=
  (rfl)

end TauCeti.Lie
