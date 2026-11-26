/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Dual

/-!
# Polars of absolutely convex hulls and zero-neighborhoods

The absolute polar for a bilinear pairing is unchanged by taking an absolutely
convex hull. For the continuous dual pairing, taking the closed absolutely convex
hull also leaves the polar unchanged. This second identity holds for any module
carrying a topology, with no continuity assumed for addition or scalar
multiplication. These identities let separation arguments pass between a
generating set and its closed disked hull.

The annihilator `StrongDual.polarSubmodule` of the kernel of a continuous functional `α` is the
line `𝕜 ∙ α` (`StrongDual.polarSubmodule_ker_eq_span_singleton`). In a finite-dimensional
topological vector space the annihilator of a subspace `S` is the continuous dual of the quotient
`E ⧸ S` (`StrongDual.polarSubmoduleEquivDualQuotient`): a functional vanishing on `S` descends to
the quotient. This is the norm-free analogue of `Submodule.quotientDualEquivAnnihilator`, so it
applies to spaces such as tangent spaces that carry a topology but no norm.

In addition, the polar of any neighborhood of zero in a topological module over a
normed field is von Neumann bounded in the strong dual
(`StrongDual.isVonNBounded_polar`), extending `NormedSpace.isBounded_polar_of_mem_nhds_zero`
beyond normed spaces: every bounded subset of the primal space is absorbed by the
neighborhood, so functionals in the polar are uniformly bounded on it.
-/

public section

open Topology
open scoped ComplexOrder Pointwise

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid F] [Module 𝕜 F]

/-- Taking the absolutely convex hull does not change the absolute polar of a
bilinear pairing. -/
@[simp]
theorem polar_absConvexHull (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (s : Set E) :
    B.polar (absConvexHull 𝕜 s) = B.polar s :=
  (B.polar_antitone subset_absConvexHull).antisymm <|
    (B.tripolar_eq_polar s).symm.trans_subset <|
      B.polar_antitone <| absConvexHull_min (B.subset_bipolar s) (polar_AbsConvex _)

end LinearMap

namespace StrongDual

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- Taking the closed absolutely convex hull does not change the absolute polar. -/
@[simp]
theorem polar_closedAbsConvexHull (s : Set E) :
    polar 𝕜 (closedAbsConvexHull 𝕜 s) = polar 𝕜 s := by
  rw [polar]
  set B := (topDualPairing 𝕜 E).flip
  have hclosed : IsClosed (B.flip.polar (B.polar s)) := by
    simp only [B, LinearMap.polar_eq_iInter, LinearMap.flip_apply, topDualPairing_apply]
    exact isClosed_biInter fun f _ ↦ isClosed_le f.continuous.norm continuous_const
  exact (B.polar_antitone subset_closedAbsConvexHull).antisymm <|
    (B.tripolar_eq_polar s).symm.trans_subset <| B.polar_antitone <|
      closedAbsConvexHull_min (B.subset_bipolar s) (LinearMap.polar_AbsConvex _) hclosed

end RCLike

section Bounded

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- The polar of a neighborhood of zero is von Neumann bounded in the strong dual. -/
theorem isVonNBounded_polar {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    Bornology.IsVonNBounded 𝕜 (polar 𝕜 U) := by
  refine ContinuousLinearMap.isVonNBounded_iff.2 fun s hs ↦ ?_
  by_cases hne : (Bornology.cobounded 𝕜).NeBot
  · obtain ⟨c, hc⟩ := (hs hU).eventually.exists
    refine (NormedSpace.isVonNBounded_closedBall 𝕜 𝕜 ‖c‖).subset ?_
    rintro _ ⟨f, hf, x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hc hx
    simp only [Metric.mem_closedBall, dist_zero_right, map_smul, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg c) (hf u hu)
  · intro V _
    rw [Absorbs, Filter.not_neBot.1 hne]
    exact Filter.eventually_bot

end Bounded

end StrongDual

namespace StrongDual

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [Module 𝕜 E]

/-- The annihilator in the continuous dual of the kernel of a functional `α` is the line spanned
by `α`. -/
theorem polarSubmodule_ker_eq_span_singleton (α : StrongDual 𝕜 E) :
    polarSubmodule 𝕜 (LinearMap.ker α.toLinearMap) = 𝕜 ∙ α := by
  refine le_antisymm (fun p hp ↦ ?_) ((Submodule.span_singleton_le_iff_mem _ _).mpr
    ((mem_polarSubmodule 𝕜 _ α).mpr fun v hv ↦ hv))
  -- A functional vanishing on `ker α` is a multiple of `α` as a linear functional.
  have hK : (⨅ _ : Unit, LinearMap.ker α.toLinearMap) ≤ LinearMap.ker p.toLinearMap :=
    fun v hv ↦ LinearMap.mem_ker.mpr ((mem_polarSubmodule 𝕜 _ p).mp hp v (by simpa using hv))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (by simpa using mem_span_of_iInf_ker_le_ker hK)
  exact Submodule.mem_span_singleton.mpr ⟨c, ContinuousLinearMap.coe_injective hc⟩

section FiniteDimensional

variable [CompleteSpace 𝕜] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The **annihilator of a subspace is the dual of the quotient**: in a finite-dimensional
topological vector space, a functional `α` vanishing on `S` descends to the functional
`[v] ↦ α v` on `E ⧸ S`, and every functional on the quotient is obtained from its composite with
the quotient map. Both spaces are finite-dimensional, so this linear equivalence is continuous.
It is the norm-free analogue of `Submodule.quotientDualEquivAnnihilator`. -/
def polarSubmoduleEquivDualQuotient (S : Submodule 𝕜 E) :
    polarSubmodule 𝕜 S ≃L[𝕜] StrongDual 𝕜 (E ⧸ S) :=
  let e : polarSubmodule 𝕜 S ≃ₗ[𝕜] StrongDual 𝕜 (E ⧸ S) :=
  { toFun α := S.liftQL (α : StrongDual 𝕜 E) fun v hv ↦
      (mem_polarSubmodule 𝕜 S (α : StrongDual 𝕜 E)).1 α.property v hv
    invFun ℓ := ⟨ℓ.comp S.mkQL, (mem_polarSubmodule 𝕜 S _).2 fun v hv ↦ by
      simp [(Submodule.Quotient.mk_eq_zero S).2 hv]⟩
    left_inv α := Subtype.ext (ContinuousLinearMap.ext fun v ↦ (rfl))
    right_inv ℓ := ContinuousLinearMap.ext fun q ↦
      Submodule.Quotient.induction_on S q fun v ↦ (rfl)
    map_add' α β := ContinuousLinearMap.ext fun q ↦
      Submodule.Quotient.induction_on S q fun v ↦ (rfl)
    map_smul' c α := ContinuousLinearMap.ext fun q ↦
      Submodule.Quotient.induction_on S q fun v ↦ (rfl) }
  -- Naming the spaces lets the instance arguments be synthesized before the result type is
  -- unified with the expected one.
  LinearEquiv.toContinuousLinearEquiv (E := polarSubmodule 𝕜 S) (F := StrongDual 𝕜 (E ⧸ S)) e

/-- The functional on `E ⧸ S` induced by `α` in the annihilator of `S` takes the value `α v` on
the class of `v`. -/
@[simp]
theorem polarSubmoduleEquivDualQuotient_apply_mk (S : Submodule 𝕜 E) (α : polarSubmodule 𝕜 S)
    (v : E) :
    polarSubmoduleEquivDualQuotient S α (Submodule.Quotient.mk v) = (α : StrongDual 𝕜 E) v :=
  (rfl)

/-- The functional in the annihilator of `S` corresponding to a functional `ℓ` on `E ⧸ S` takes
the value `ℓ [v]` on `v`. -/
@[simp]
theorem polarSubmoduleEquivDualQuotient_symm_apply (S : Submodule 𝕜 E)
    (ℓ : StrongDual 𝕜 (E ⧸ S)) (v : E) :
    ((polarSubmoduleEquivDualQuotient S).symm ℓ : StrongDual 𝕜 E) v =
      ℓ (Submodule.Quotient.mk v) :=
  (rfl)

end FiniteDimensional

end StrongDual
