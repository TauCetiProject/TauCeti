/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.FringePresentation.Model

/-!
# Checks for fringe neighborhoods on the overconvergent disc

The Gauss open unit ball is a fringe neighborhood of zero, but excludes the
coordinate. Closed balls of negative radius are not neighborhoods, even for
the zero seminorm. The inclusion into the Tate algebra is fringe-continuous.
-/

public section

open Topology
open TauCeti.Dagger

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The Gauss open unit ball is a fringe neighborhood on the dagger disc. -/
theorem TauCeti.Dagger.FringePresentation.disc_openUnitBall_mem_nhds :
    letI := (FringePresentation.washnitzer K 1 2 (by norm_num)).fringeTopology
    {f : washnitzerAlgebra (Fin 1) K | ‖f‖ < 1} ∈ 𝓝 0 := by
  let P := FringePresentation.washnitzer K 1 2 (by norm_num)
  have hc := (P.continuous_seminorm_iff
    (normSeminorm K (washnitzerAlgebra (Fin 1) K))
    IsUltrametricDist.isNonarchimedean_norm).2 fun ρ ↦ by
      let := P.stageTopology ρ
      exact continuous_norm.comp
        (FringePresentation.continuous_washnitzer_ofStage (K := K) 1 2 one_lt_two ρ)
  let := P.fringeTopology
  have hball : Set.Iio (1 : ℝ) ∈ 𝓝 ((normSeminorm K (washnitzerAlgebra (Fin 1) K)) 0) := by
    exact isOpen_Iio.mem_nhds (by simp)
  exact hc.continuousAt.preimage_mem_nhds hball

example : washnitzerAlgebra.X (Fin 1) K 0 ∉
    {f : washnitzerAlgebra (Fin 1) K | ‖f‖ < 1} := by
  simp

example :
    letI := (FringePresentation.washnitzer K 1 2 (by norm_num)).fringeTopology
    (0 : Seminorm K (washnitzerAlgebra (Fin 1) K)).closedBall 0 (-1) ∉ 𝓝 0 := by
  let := (FringePresentation.washnitzer K 1 2 (by norm_num)).fringeTopology
  intro h
  have := mem_of_mem_nhds h
  simp at this

example :
    @Continuous _ _ (FringePresentation.washnitzer K 1 2 (by norm_num)).fringeTopology inferInstance
      (washnitzerAlgebra.toTate (Fin 1) K) := by
  let P := FringePresentation.washnitzer K 1 2 (by norm_num)
  apply (P.continuous_linearMap_iff (washnitzerAlgebra.toTate (Fin 1) K).toLinearMap).2
  intro ρ
  let := P.stageTopology ρ
  exact washnitzerAlgebra.isometry_toTate.continuous.comp
    (FringePresentation.continuous_washnitzer_ofStage 1 2 (by norm_num) ρ)
