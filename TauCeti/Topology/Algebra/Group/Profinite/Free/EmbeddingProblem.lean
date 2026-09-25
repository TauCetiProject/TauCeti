/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Algebra.ContinuousMonoidHom
import TauCeti.GroupTheory.PGroup
public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Solutions
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP

/-!
# Finite embedding problems for free pro-p groups

The universal property solves finite embedding problems with `p`-group kernel,
without a finiteness assumption on the generating type. Thus solvability by itself
does not impose topological finite generation.
-/

public section

namespace TauCeti

universe u

/-- A free pro-`p` group solves every finite embedding problem with `p`-group kernel. -/
theorem hasPGroupSolutions_freeProP (p : ℕ) (X : Type u) :
    HasPGroupSolutions p (freeProP p X) := by
  classical
  apply hasPGroupSolutions_iff.mpr
  intro P hP
  let _ : TopologicalSpace P.Q := ⊥
  let _ : TopologicalSpace P.E := ⊥
  have : DiscreteTopology P.Q := ⟨rfl⟩
  have : DiscreteTopology P.E := ⟨rfl⟩
  have hπ : Continuous P.π := P.π.continuous_iff_isOpen_ker.mpr P.isOpen_ker_π
  have hQ : IsPGroup p P.Q := isProP_iff_isPGroup.mp
    ((isProP_freeProP p X).of_surjective P.π hπ P.π_surjective)
  have hE : IsPGroup p P.E := IsPGroup.of_subgroup_of_quotient hP
    (hQ.of_equiv (QuotientGroup.quotientKerEquivOfSurjective P.α P.α_surjective).symm)
  let t : X → P.E := fun x ↦ (P.α_surjective (P.π (freeProP.of x))).choose
  have hcomp : (⟨P.α, continuous_of_discreteTopology⟩ : P.E →ₜ* P.Q).comp
      (freeProP.lift hE.isProP t) = ⟨P.π, hπ⟩ := by
    apply freeProP.hom_ext
    intro x
    rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, ContinuousMonoidHom.coe_mk P.α,
      ContinuousMonoidHom.coe_mk P.π, freeProP.lift_of]
    exact (P.α_surjective (P.π (freeProP.of x))).choose_spec
  exact ⟨(freeProP.lift hE.isProP t).toMonoidHom, FiniteEmbeddingProblem.isSolution_iff.mpr
    ⟨(freeProP.lift hE.isProP t).toMonoidHom.continuous_iff_isOpen_ker.mp
      (freeProP.lift hE.isProP t).continuous,
      MonoidHom.ext fun g ↦ DFunLike.congr_fun hcomp g⟩⟩

end TauCeti
