/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.RCLike.Basic

import Mathlib.Topology.Algebra.Module.Star
import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Self-adjoint elements of a ball in the closure of a star-closed submodule

In a normed space over `ℝ` or `ℂ` with a continuous involution, the self-adjoint elements of norm
at most `r` of the norm closure of a star-closed submodule `s`, such as a star subalgebra, are
exactly the norm limits of self-adjoint elements of norm at most `r` of `s`
(`TauCeti.closure_inter_selfAdjoint_inter_closedBall`). The continuous map taking the real part
`selfAdjointPart ℝ a` of `a` and then the radial retraction `TauCeti.radialRetraction r` onto the
closed ball of radius `r` sends `s` into its self-adjoint elements of norm at most `r` and fixes
every self-adjoint element of norm at most `r`.

This lets an approximation by elements of the norm closure of a star subalgebra `S`, such as the
continuous functional calculus of elements of `S`, be replaced by one through elements of `S`
itself without losing self-adjointness or the norm bound; the Kaplansky density theorem uses it
this way.
-/

public section

open Metric

namespace TauCeti

variable {𝕜 A S : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [StarAddMonoid A] [NormedSpace 𝕜 A]
  [StarModule 𝕜 A] [ContinuousStar A] [SetLike S A] [AddSubmonoidClass S A]
  [SMulMemClass S 𝕜 A] [StarMemClass S A]

variable (𝕜) in
include 𝕜 in
/-- The closure of the self-adjoint elements of norm at most `r` of a star-closed `𝕜`-submodule
`s` is the set of self-adjoint elements of norm at most `r` of the closure of `s`. -/
theorem closure_inter_selfAdjoint_inter_closedBall (s : S) (r : ℝ) :
    closure ((s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r) =
      closure (s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r := by
  refine subset_antisymm (closure_minimal
    (Set.inter_subset_inter_left _ (Set.inter_subset_inter_left _ subset_closure))
    ((isClosed_closure.inter (isClosed_eq continuous_star continuous_id)).inter
      isClosed_closedBall)) ?_
  rintro z ⟨⟨hz, hzsa⟩, hzr⟩
  have hr : 0 ≤ r := dist_nonneg.trans hzr
  let : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ 𝕜 A
  have : IsScalarTower ℝ 𝕜 A := IsScalarTower.restrictScalars ℝ 𝕜 A
  have : StarModule ℝ A := ⟨fun c a => by
    rw [star_trivial c, RCLike.real_smul_eq_coe_smul (K := 𝕜),
      RCLike.real_smul_eq_coe_smul (K := 𝕜), star_smul, RCLike.star_def, RCLike.conj_ofReal]⟩
  have : SMulMemClass S ℝ A := SMulMemClass.ofIsScalarTower S ℝ 𝕜 A
  -- The real part followed by the radial retraction onto the ball sends `s` into the
  -- left-hand side and fixes `z`.
  let f : A → A := fun a => radialRetraction r (selfAdjointPart ℝ a : A)
  have hf : Continuous f := (lipschitzWith_radialRetraction hr).continuous.comp
    (continuous_subtypeVal.comp (continuous_selfAdjointPart ℝ A))
  have hfz : f z = z := by
    simp only [f, IsSelfAdjoint.coe_selfAdjointPart_apply ℝ hzsa]
    exact radialRetraction_of_norm_le (mem_closedBall_zero_iff.mp hzr)
  refine hfz ▸ map_mem_closure hf hz fun a ha =>
    ⟨⟨?_, ?_⟩, radialRetraction_mem_closedBall hr _⟩ <;> simp only [f, radialRetraction_def]
  · rw [selfAdjointPart_apply_coe]
    exact SMulMemClass.smul_mem _ (SMulMemClass.smul_mem _ (add_mem ha (star_mem ha)))
  · exact (selfAdjoint.submodule ℝ A).smul_mem _ (selfAdjointPart ℝ a).property

end TauCeti
