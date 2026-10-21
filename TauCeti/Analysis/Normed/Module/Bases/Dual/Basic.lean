/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Reflexive
public import TauCeti.Analysis.Normed.Module.Bases.Map
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# The dual basic sequence of a Schauder basis

The coordinate functionals of a Schauder basis form a Schauder basis of their norm-closed
linear span in the continuous dual. The new coordinates are evaluation at the original
basis vectors, and the initial projections are restrictions of the adjoints of the original
projections. Their norms are bounded by the original projection norms.

A functional belongs to this closed span exactly when its compositions with the initial
projections converge in norm to that functional. Consequently a basis is shrinking exactly
when these adjoint projections converge strongly on the whole dual. In that case the
coordinate functionals form a Schauder basis of the whole dual.

All expansions use conditional summation along initial segments. Completeness of the
original space supplies the uniform bound on its projections; the scalar field need not
be real or complex.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 3, duality of bases.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (b : SchauderBasis 𝕜 E)

variable [CompleteSpace E]

/-- A functional belongs to the closed coordinate span exactly when the adjoint initial
projections converge to it in norm. -/
theorem mem_closure_span_coord_iff (f : StrongDual 𝕜 E) :
    f ∈ (Submodule.span 𝕜 (range b.coord)).topologicalClosure ↔
      Tendsto (fun n ↦ f.comp (b.proj n)) atTop (𝓝 f) := by
  constructor
  · intro hf
    let P : ℕ → StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E :=
      fun n ↦ ContinuousLinearMap.precomp 𝕜 (b.proj n)
    have heq : Equicontinuous (fun n (g : StrongDual 𝕜 E) ↦ g.comp (b.proj n)) := by
      apply ((NormedSpace.equicontinuous_TFAE P).out 4 2).mp
      refine ⟨b.nnnormProjBound, fun n g ↦ ?_⟩
      exact (ContinuousLinearMap.opNorm_comp_le g (b.proj n)).trans
        (by simpa [mul_comm] using
          mul_le_mul_of_nonneg_left (b.norm_proj_le_nnnormProjBound n) (norm_nonneg g))
    have hclosed : IsClosed {g : StrongDual 𝕜 E |
        Tendsto (fun n ↦ g.comp (b.proj n)) atTop (𝓝 g)} :=
      heq.isClosed_setOfPred_tendsto continuous_id
    apply closure_minimal (s := (Submodule.span 𝕜 (range b.coord) : Set (StrongDual 𝕜 E)))
      ?_ hclosed hf
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop i] with n hn
      symm
      ext x
      simp [proj_apply, hn]
    | zero => simp
    | add g h _ _ hg hh => simpa using hg.add hh
    | smul a g _ hg => simpa using hg.const_smul a
  · intro hf
    apply Submodule.isClosed_topologicalClosure _ |>.mem_of_tendsto hf
    exact Eventually.of_forall fun n ↦ Submodule.le_topologicalClosure _ (by
      rw [b.comp_proj_eq_sum]
      exact Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i)))

/-- The coordinate functionals form a Schauder basis of their closed linear span. -/
def dualBasis :
    SchauderBasis 𝕜 (Submodule.span 𝕜 (range b.coord)).topologicalClosure where
  basis i := ⟨b.coord i, Submodule.le_topologicalClosure _
    (Submodule.subset_span (mem_range_self i))⟩
  coord i := (ContinuousLinearMap.apply 𝕜 𝕜 (b i)).comp (Submodule.subtypeL _)
  ortho i j := by
    classical
    simp [b.ortho, Pi.single_apply, eq_comm]
  expansion f := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
    apply tendsto_subtype_rng.mpr
    simpa only [Function.comp_def, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      ContinuousLinearMap.apply_apply, ← b.comp_proj_eq_sum] using
      (b.mem_closure_span_coord_iff f).mp f.property

@[simp]
theorem coe_dualBasis_apply (i : ℕ) :
    (b.dualBasis i : StrongDual 𝕜 E) = b.coord i := (rfl)

@[simp]
theorem dualBasis_coord_apply
    (f : (Submodule.span 𝕜 (range b.coord)).topologicalClosure) (i : ℕ) :
    b.dualBasis.coord i f = (f : StrongDual 𝕜 E) (b i) := (rfl)

/-- The dual basic sequence's projections are the restricted adjoint projections. -/
theorem coe_dualBasis_proj (n : ℕ)
    (f : (Submodule.span 𝕜 (range b.coord)).topologicalClosure) :
    (b.dualBasis.proj n f : StrongDual 𝕜 E) = (f : StrongDual 𝕜 E).comp (b.proj n) := by
  rw [proj_apply, b.comp_proj_eq_sum]
  simp

/-- Dual basic sequence projections have no larger norm than the original projections. -/
theorem norm_dualBasis_proj_le (n : ℕ) : ‖b.dualBasis.proj n‖ ≤ ‖b.proj n‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  simpa only [← Submodule.norm_coe, coe_dualBasis_proj, mul_comm] using
    ContinuousLinearMap.opNorm_comp_le (f : StrongDual 𝕜 E) (b.proj n)

/-- A basis is shrinking exactly when its adjoint initial projections converge strongly
on the continuous dual. The convergence asserted here is in the norm of the dual. -/
theorem isShrinking_iff_tendsto_comp_proj : b.IsShrinking ↔
    ∀ f : StrongDual 𝕜 E, Tendsto (fun n ↦ f.comp (b.proj n)) atTop (𝓝 f) := by
  simp_rw [← b.mem_closure_span_coord_iff]
  rw [b.isShrinking_iff, Submodule.eq_top_iff']

/-- For a shrinking basis, its coordinate functionals form a basis of the whole dual,
with coefficients given by evaluation at the original basis vectors. -/
def IsShrinking.dualBasis {b : SchauderBasis 𝕜 E} (hb : b.IsShrinking) :
    SchauderBasis 𝕜 (StrongDual 𝕜 E) :=
  b.dualBasis.map ((ContinuousLinearEquiv.ofEq _ _ (b.isShrinking_iff.mp hb)).trans
    Submodule.topContEquiv)

@[simp]
theorem IsShrinking.dualBasis_apply {b : SchauderBasis 𝕜 E} (hb : b.IsShrinking) (i : ℕ) :
    hb.dualBasis i = b.coord i := by
  rw [IsShrinking.dualBasis, GeneralSchauderBasis.map_apply]
  exact b.coe_dualBasis_apply i

@[simp]
theorem IsShrinking.dualBasis_coord_apply {b : SchauderBasis 𝕜 E} (hb : b.IsShrinking)
    (i : ℕ) (f : StrongDual 𝕜 E) : hb.dualBasis.coord i f = f (b i) := by
  rw [IsShrinking.dualBasis, GeneralSchauderBasis.map_coord_apply,
    SchauderBasis.dualBasis_coord_apply]
  rfl

/-- Initial projections of the whole dual basis are exactly the adjoint projections. -/
theorem IsShrinking.dualBasis_proj {b : SchauderBasis 𝕜 E} (hb : b.IsShrinking)
    (n : ℕ) (f : StrongDual 𝕜 E) : hb.dualBasis.proj n f = f.comp (b.proj n) := by
  rw [proj_apply, b.comp_proj_eq_sum]
  simp

end SchauderBasis
