/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.FringePresentation.Topology

/-!
# The relation-free fringe presentation

The identity presentation of the Monsky–Washnitzer algebra has no relations.
Its fringe topology is finer than its unit Gauss topology, hence Hausdorff:
the unit Gauss norm is continuous at every radius greater than one. This gives
a nondegenerate instance of the presentation-level fringe construction, in
every dimension and without completeness of the coefficient field.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §§1.8, 4.2.
-/

public section

namespace TauCeti.Dagger.FringePresentation

open Topology _root_.MvPowerSeries

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- The relation-free fringe presentation of `W_n` at an outer radius `R > 1`. -/
noncomputable abbrev washnitzer (n : ℕ) (R : ℝ) (hR : 1 < R) :
    FringePresentation K (washnitzerAlgebra (Fin n) K) where
  n := n
  radius := R
  one_lt_radius := hR
  r := 0
  relation := Fin.elim0
  equiv := (Ideal.quotientEquivAlgOfEq K (by simp)).trans (AlgEquiv.quotientBot K _)

variable {K} (n : ℕ) (R : ℝ) (hR : 1 < R)

/-- The underlying surjection of the relation-free presentation is the identity. -/
@[simp]
theorem washnitzer_proj : (washnitzer K n R hR).proj = AlgHom.id K _ := by
  apply AlgHom.ext
  intro f
  rw [(washnitzer K n R hR).proj_apply]
  simp [washnitzer]

/-- A representative of a relation-free stage maps to the same overconvergent series. -/
@[simp]
theorem washnitzer_ofStage_mk (ρ : Set.Ioc (1 : ℝ) R)
    (f : IsRestricted.subring (R := K) (fun _ : Fin n ↦ (ρ : ℝ))) :
    (washnitzer K n R hR).ofStage ρ (Ideal.Quotient.mk _ f) =
      washnitzerAlgebra.ofRestricted ρ.2.1 (fun _ ↦ le_rfl) f := by
  rw [ofStage_mk, washnitzer_proj, AlgHom.id_apply]

/-- The map from every relation-free stage to `W_n` is continuous for the unit Gauss norm. -/
theorem continuous_washnitzer_ofStage (ρ : Set.Ioc (1 : ℝ) R) :
    @Continuous _ _ ((washnitzer K n R hR).stageTopology ρ) inferInstance
      ((washnitzer K n R hR).ofStage ρ) := by
  let P := washnitzer K n R hR
  have : Fact (0 < (ρ : ℝ)) := ⟨zero_lt_one.trans ρ.2.1⟩
  apply (P.stageIdeal ρ).isQuotientMap_mkQ.continuous_iff.mpr
  have heq : P.ofStage ρ ∘ (P.stageIdeal ρ).mkQ =
      fun f ↦ washnitzerAlgebra.ofRestricted ρ.2.1 (fun _ ↦ le_rfl) f := by
    funext f
    exact washnitzer_ofStage_mk n R hR ρ f
  rw [heq]
  apply AddMonoidHomClass.continuous_of_bound
    (washnitzerAlgebra.ofRestricted ρ.2.1 (fun _ : Fin n ↦ le_rfl)) 1
  intro f
  rw [one_mul, ← washnitzerAlgebra.norm_toTate]
  convert @TauCeti.MvPowerSeries.norm_restrictedRadiusHom_le (Fin n) K _ _
    (fun _ ↦ 1) (fun _ ↦ (ρ : ℝ)) (fun _ ↦ zero_le_one) (fun _ ↦ ρ.2.1.le)
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) f using 1
  exact congrArg norm (Subtype.ext (by simp))

/-- The relation-free fringe topology is finer than the unit Gauss topology. -/
theorem washnitzer_fringeTopology_le :
    (washnitzer K n R hR).fringeTopology ≤
      inferInstanceAs (TopologicalSpace (washnitzerAlgebra (Fin n) K)) := by
  exact fringeTopology_le (washnitzer K n R hR) (fun _ : Unit ↦ normSeminorm K _)
    (fun _ ↦ IsUltrametricDist.isNonarchimedean_norm) _ (norm_withSeminorms K _)
    (continuous_washnitzer_ofStage (K := K) n R hR)

/-- The relation-free fringe topology is Hausdorff, in every dimension. -/
theorem t2Space_washnitzer_fringeTopology :
    letI := (washnitzer K n R hR).fringeTopology
    T2Space (washnitzerAlgebra (Fin n) K) :=
  t2Space_antitone (washnitzer_fringeTopology_le (K := K) n R hR) inferInstance

end TauCeti.Dagger.FringePresentation
