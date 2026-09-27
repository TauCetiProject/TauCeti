/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Compact
public import TauCeti.Combinatorics.DenseGraphLimits.Separation.Inverse

/-!
# Convergence of graphons through homomorphism densities

A sequence in the compact cut-distance quotient of unit-interval graphons converges exactly when
the homomorphism density of every finite simple graph converges. Thus finite-graph densities give
all the coordinates needed to test convergence of dense graph limits.

See Lovász, *Large Networks and Graph Limits*, Theorem 11.5.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped unitInterval

namespace TauCeti

namespace DenseGraphLimits

/-- A sequence of unit-interval graphons converges in cut distance if and only if all its finite
homomorphism densities converge to those of the limit graphon. -/
theorem tendsto_graphonSpace_iff_forall_homDensity
    (Ws : ℕ → GraphonSpaceI) (W : GraphonSpaceI) :
    Tendsto Ws atTop (nhds W) ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
        Tendsto (fun k => homDensityOnSpace F (Ws k)) atTop
          (nhds (homDensityOnSpace F W)) := by
  let Φ : GraphonSpaceI →
      (p : Σ n : ℕ, Σ F : SimpleGraph (Fin n), DecidableRel F.Adj) → ℝ :=
    fun x p => by
      letI := p.2.2
      exact homDensityOnSpace p.2.1 x
  have hcont : Continuous Φ := by
    apply continuous_pi
    intro p
    exact (letI := p.2.2; continuous_homDensityOnSpace p.2.1)
  have hinj : Function.Injective Φ := by
    intro U V h
    apply (graphonSpace_ext_iff_homDensity U V).2
    intro n F inst
    simpa only [Φ] using congrFun h ⟨n, F, inst⟩
  have hemb : Topology.IsClosedEmbedding Φ := hcont.isClosedEmbedding hinj
  rw [hemb.tendsto_nhds_iff, tendsto_pi_nhds]
  constructor
  · intro h n F inst
    simpa only [Φ, Function.comp_def] using h ⟨n, F, inst⟩
  · intro h ⟨n, F, inst⟩
    simpa only [Φ, Function.comp_def] using h n F

end DenseGraphLimits

end TauCeti
