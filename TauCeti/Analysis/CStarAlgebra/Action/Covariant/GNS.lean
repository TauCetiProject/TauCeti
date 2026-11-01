/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation
import TauCeti.Analysis.CStarAlgebra.GNS

/-!
# The GNS covariant representation of an invariant positive functional

Let `α` be a point-norm continuous action of a topological group `G` on a possibly nonunital
C⋆-algebra `A`, and let `f` be a positive linear functional with `f (α g a) = f a`. On Mathlib's
GNS Hilbert space `f.GNS`, the completion of `A` for the semi-inner product `⟪a, b⟫ = f (a⋆ b)`,
the assignment `[b] ↦ [α_g b]` preserves inner products by invariance. Its extension to the
completion is a unitary representation of `G`, `CStarAction.gnsImplementingGroup`, the GNS
implementing group of `f`; its matrix coefficients between classes are
`⟪[a], U_g [b]⟫ = f (a⋆ α_g(b))`, `CStarAction.inner_gnsImplementingGroup_apply_coe`.

The representation is strongly continuous. Orbits of classes are continuous because positive
functionals on C⋆-algebras are bounded, so the class map `A → f.PreGNS` is continuous. Every
vector of the completion is a uniform limit of classes, and the operators are isometric, so
continuity passes to all orbits.

Together with Mathlib's GNS representation `f.gnsNonUnitalStarAlgHom`, the implementing group
satisfies `U_g π(a) = π(α_g(a)) U_g`. This is the covariant pair
`CStarAction.gnsCovariantRepresentation`. For `β ≠ 0` every β-KMS state is invariant,
`CStarAction.IsKMSState.apply_action`, so each such state has a GNS implementing group.

## References

Bratteli–Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition,
Section 2.3.3, Corollary 2.3.17, for the unitary implementation of an automorphism leaving a
state invariant.
-/

public section

noncomputable section

open PositiveLinearMap UniformSpace
open scoped ComplexOrder InnerProductSpace

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A] [PartialOrder A]
  [StarOrderedRing A] (α : CStarAction G A) {f : A →ₚ[ℂ] ℂ}

/-- An automorphism leaving a positive functional invariant induces an isometry of its GNS
pre-Hilbert space. -/
private def preGNSIsometry (hf : ∀ g a, f (α g a) = f a) (g : G) :
    f.PreGNS →ₗᵢ[ℂ] f.PreGNS where
  toLinearMap := f.toPreGNS.toLinearMap ∘ₗ (α.toContinuousLinearMap g).toLinearMap ∘ₗ
    f.ofPreGNS.toLinearMap
  norm_map' b := by simp [preGNS_norm_def, ← map_star, ← map_mul, hf]

private theorem preGNSIsometry_apply (hf : ∀ g a, f (α g a) = f a) (g : G) (b : f.PreGNS) :
    preGNSIsometry α hf g b = f.toPreGNS (α g (f.ofPreGNS b)) := by
  simp [preGNSIsometry]

/-- The **GNS implementing group** of a positive functional `f` invariant under `α`: the unitary
representation of `G` on the GNS Hilbert space extending `[b] ↦ [α_g b]`. -/
def gnsImplementingGroup (hf : ∀ g a, f (α g a) = f a) : ContRepresentation ℂ G f.GNS :=
  .ofMonoidHom
    { toFun g := (preGNSIsometry α hf g).toContinuousLinearMap.completion
      map_one' := by
        ext v
        induction v using Completion.induction_on with
        | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
        | ih b => simp [preGNSIsometry_apply]
      map_mul' g h := by
        ext v
        induction v using Completion.induction_on with
        | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
        | ih b => simp [preGNSIsometry_apply, α.mul_apply] }

variable (hf : ∀ g a, f (α g a) = f a)

/-- The implementing group sends the class of `b` to the class of `α_g b`. -/
@[simp]
theorem gnsImplementingGroup_apply_coe (g : G) (b : f.PreGNS) :
    α.gnsImplementingGroup hf g b = (f.toPreGNS (α g (f.ofPreGNS b)) : f.GNS) :=
  -- By definition `U_g` is the completion of `preGNSIsometry α hf g`.
  (ContinuousLinearMap.completion_apply_coe _ b).trans <|
    congrArg _ (preGNSIsometry_apply α hf g b)

/-- The GNS implementing group is unitary. -/
theorem isUnitary_gnsImplementingGroup : (α.gnsImplementingGroup hf).IsUnitary := by
  refine (ContRepresentation.isUnitary_iff_norm_map _).2 fun g v => ?_
  induction v using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_norm
  | ih b => simpa [Completion.norm_coe, preGNSIsometry_apply] using
      (preGNSIsometry α hf g).norm_map b

/-- Matrix coefficients of the implementing group between classes:
`⟪[a], U_g [b]⟫ = f (a⋆ α_g(b))`. -/
theorem inner_gnsImplementingGroup_apply_coe (g : G) (a b : A) :
    ⟪(f.toPreGNS a : f.GNS), α.gnsImplementingGroup hf g (f.toPreGNS b)⟫_ℂ =
      f (star a * α g b) := by
  simp [preGNS_inner_def]

/-- The GNS implementing group is strongly continuous. -/
theorem continuous_gnsImplementingGroup_apply (v : f.GNS) :
    Continuous fun g => α.gnsImplementingGroup hf g v := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨b, hb⟩ := Completion.denseRange_coe.exists_dist_lt v hε
  refine ⟨fun g => α.gnsImplementingGroup hf g b, ?_, fun g => hεu ?_⟩
  · simp only [gnsImplementingGroup_apply_coe]
    exact Completion.continuous_coe _ |>.comp <|
      f.continuous_toPreGNS.comp (α.continuous_orbit _)
  · rwa [((α.isUnitary_gnsImplementingGroup hf).isometry g).dist_eq]

/-- The **GNS covariant representation** of a positive functional `f` invariant under `α`: Mathlib's
GNS representation of `A` on `f.GNS`, together with the GNS implementing group. -/
def gnsCovariantRepresentation : CovariantRepresentation α f.GNS where
  coefficient := f.gnsNonUnitalStarAlgHom
  group := α.gnsImplementingGroup hf
  isUnitary := α.isUnitary_gnsImplementingGroup hf
  continuous_orbit := α.continuous_gnsImplementingGroup_apply hf
  covariance g a v := by
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih b => simp

@[simp]
theorem gnsCovariantRepresentation_coefficient :
    (α.gnsCovariantRepresentation hf).coefficient = f.gnsNonUnitalStarAlgHom :=
  (rfl)

@[simp]
theorem gnsCovariantRepresentation_group :
    (α.gnsCovariantRepresentation hf).group = α.gnsImplementingGroup hf :=
  (rfl)

end TauCeti.CStarAction
