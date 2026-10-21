/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Transport of Schauder bases

A bounded linear equivalence transports a generalized Schauder basis, with its original
summation filter. The coordinate functionals are precomposed with the inverse equivalence,
and finite coordinate projections are conjugated by the equivalence. In particular, this
construction applies both to classical Schauder bases and to unconditional bases.
-/

public section

namespace GeneralSchauderBasis

variable {β 𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {L : SummationFilter β}

/-- Transport a generalized Schauder basis through a bounded linear equivalence, preserving
its summation filter. -/
def map (b : GeneralSchauderBasis β 𝕜 E L) (e : E ≃L[𝕜] F) :
    GeneralSchauderBasis β 𝕜 F L where
  basis i := e (b i)
  coord i := (b.coord i).comp (e.symm : F →L[𝕜] E)
  ortho i j := by simp [b.ortho]
  expansion x := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      map_smul, e.apply_symm_apply] using
      (e : E →L[𝕜] F).hasSum (b.expansion (e.symm x))

@[simp]
theorem map_apply (b : GeneralSchauderBasis β 𝕜 E L) (e : E ≃L[𝕜] F) (i : β) :
    b.map e i = e (b i) := (rfl)

@[simp]
theorem map_coord_apply (b : GeneralSchauderBasis β 𝕜 E L) (e : E ≃L[𝕜] F)
    (i : β) (x : F) : (b.map e).coord i x = b.coord i (e.symm x) := (rfl)

@[simp]
theorem map_refl (b : GeneralSchauderBasis β 𝕜 E L) :
    b.map (ContinuousLinearEquiv.refl 𝕜 E) = b := by
  ext <;> rfl

@[simp]
theorem map_map (b : GeneralSchauderBasis β 𝕜 E L) (e : E ≃L[𝕜] F) (f : F ≃L[𝕜] G) :
    (b.map e).map f = b.map (e.trans f) := by
  ext <;> rfl

/-- Finite coordinate projections of the transported basis are the conjugates of the
original projections. -/
theorem map_proj_apply (b : GeneralSchauderBasis β 𝕜 E L) (e : E ≃L[𝕜] F)
    (s : Finset β) (x : F) : (b.map e).proj s x = e (b.proj s (e.symm x)) := by
  simp [proj_apply, map_sum, map_smul]

end GeneralSchauderBasis
