/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Geometry.Diffeomorphism.Group
import TauCeti.Topology.Algebra.HomeomorphAction
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# The tautological action of the self-diffeomorphism group

The self-diffeomorphism group `TauCeti.Diff I M n = M ≃ₘ^n⟮I, I⟯ M`, built in
`TauCeti.Geometry.Diffeomorphism.Group`, acts on its manifold `M` by evaluation: `f • x = f x`.
This file records that action — faithful, continuous in the point, and `Cⁿ` in the point — and
the forgetful group homomorphism `Diff I M n →* (M ≃ₜ M)` to the homeomorphism group, which is
injective and intertwines this action with the tautological homeomorphism-group action of
`TauCeti.Topology.Algebra.HomeomorphAction`. It mirrors `Equiv.Perm.applyMulAction` and
`TauCeti.Homeomorph.applyMulAction`, one rung up the regularity ladder.

The action is what lets Mathlib's `MulAction.fixingSubgroup` define **`Diff(M, ∂M)`**, the
subgroup of self-diffeomorphisms fixing the boundary `∂M` pointwise. The geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`, layer 3, "diffeomorphism groups with the C^∞
topology") asks for it directly: "`Diff(M, ∂M)` is the closed subgroup fixing `∂M` pointwise, for
the relative statements". With the C^∞ topology a separate later deliverable, this file stops at
the group-action and subgroup level: `Diff(M, ∂M)` is the relevant instance of Mathlib's
pointwise-fixing subgroup, with closedness and homotopy-group applications deferred to the topology
layer.

## Main definitions

* `TauCeti.Diffeomorph.applyMulAction`: the `MulAction (Diff I M n) M` with `f • x = f x`.
* `TauCeti.Diffeomorph.toHomeomorphHom`: the forgetful group homomorphism `Diff I M n →* (M ≃ₜ M)`.
* `TauCeti.Diff.relBoundary`: `Diff(M, ∂M)`, the subgroup fixing the boundary `∂M` pointwise.

## Main results

* `TauCeti.Diffeomorph.applyFaithfulSMul`, `applyContinuousConstSMul`: the action is faithful and
  continuous in the point, with the same continuity inherited by every subgroup.
* `TauCeti.Diffeomorph.toHomeomorphHom_injective` and `smul_toHomeomorph`: the forgetful
  homomorphism is injective and equivariant for the homeomorphism-group action.
* `TauCeti.Diff.relBoundary_eq_fixingSubgroup`, `mem_relBoundary_iff`: `Diff(M, ∂M)` identified
  with Mathlib's pointwise-fixing subgroup, with membership unfolded to pointwise fixing.
-/

namespace TauCeti

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

namespace Diffeomorph

/-- The tautological action of the self-diffeomorphism group `Diff I M n` on `M` by evaluation.
The multiplication on `Diff I M n` is composition in the order `f * g = g.trans f`, so
`(f * g) • x = f • (g • x)`, making this a genuine left action. -/
instance applyMulAction : MulAction (Diff I M n) M where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological action of `Diff I M n` on `M` is given by evaluation. -/
@[simp]
theorem smul_def (f : Diff I M n) (x : M) : f • x = f x := rfl

/-- The tautological action of `Diff I M n` on `M` is faithful. -/
instance applyFaithfulSMul : FaithfulSMul (Diff I M n) M :=
  ⟨fun h => _root_.Diffeomorph.ext h⟩

/-- The tautological action of `Diff I M n` on `M` is continuous in the point: each
self-diffeomorphism is a continuous self-map. -/
instance applyContinuousConstSMul : ContinuousConstSMul (Diff I M n) M :=
  ⟨fun f => f.continuous⟩

/-- A subgroup of the self-diffeomorphism group acts continuously on `M` in the point, reusing
continuity of the ambient action. -/
instance applySubgroupContinuousConstSMul (H : Subgroup (Diff I M n)) :
    ContinuousConstSMul H M :=
  ⟨fun f => continuous_const_smul (f : Diff I M n)⟩

/-- Each self-diffeomorphism acts on `M` by a `Cⁿ` map: the orbit map `x ↦ f • x` is `Cⁿ`. -/
theorem contMDiff_smul (f : Diff I M n) : ContMDiff I I n (f • · : M → M) :=
  f.contMDiff

/-- The forgetful group homomorphism from the self-diffeomorphism group to the homeomorphism group
of the underlying space, sending a diffeomorphism to its underlying homeomorphism. Both groups use
the composition convention `f * g = g.trans f`, so this is multiplicative. -/
@[simps]
def toHomeomorphHom : (Diff I M n) →* (M ≃ₜ M) where
  toFun f := f.toHomeomorph
  map_one' := Homeomorph.ext fun _ => rfl
  map_mul' _ _ := Homeomorph.ext fun _ => rfl

/-- The forgetful homomorphism to homeomorphisms is injective. -/
theorem toHomeomorphHom_injective :
    Function.Injective (toHomeomorphHom : Diff I M n → (M ≃ₜ M)) := by
  intro f g h
  apply _root_.Diffeomorph.ext
  intro x
  simpa using DFunLike.congr_fun h x

/-- The diffeomorphism action factors through the homeomorphism action of
`TauCeti.Homeomorph.applyMulAction`: forgetting to a homeomorphism and acting agrees with acting
directly. -/
@[simp]
theorem smul_toHomeomorph (f : Diff I M n) (x : M) : f.toHomeomorph • x = f • x := rfl

end Diffeomorph

namespace Diff

variable (I M n)

/-- `Diff(M, ∂M)`, the subgroup of self-diffeomorphisms fixing the boundary `∂M` pointwise. The
group-level precursor to the roadmap's relative diffeomorphism group with its later C^∞ topology. -/
def relBoundary : Subgroup (Diff I M n) :=
  fixingSubgroup (Diff I M n) (I.boundary M)

variable {I M n}

/-- `Diff(M, ∂M)` is Mathlib's pointwise-fixing subgroup for the tautological action. -/
theorem relBoundary_eq_fixingSubgroup :
    relBoundary I M n = fixingSubgroup (Diff I M n) (I.boundary M) := rfl

/-- A self-diffeomorphism lies in `Diff(M, ∂M)` iff it fixes every boundary point. -/
@[simp]
theorem mem_relBoundary_iff {f : Diff I M n} :
    f ∈ relBoundary I M n ↔ ∀ x ∈ I.boundary M, f x = x :=
  mem_fixingSubgroup_iff (Diff I M n)

end Diff

end TauCeti
