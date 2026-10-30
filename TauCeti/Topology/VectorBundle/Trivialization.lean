/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Constructions
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Trivializations over the whole base

A trivialization `e` of a fibre bundle `E` whose base set is the whole base is a homeomorphism
`E ≃ₜ B × F`. Read through `Bundle.Trivial.homeomorphProd`, it is a homeomorphism of total spaces
`E ≃ₜ TotalSpace F (Bundle.Trivial B F)` onto the trivial bundle
(`Bundle.Trivialization.homeomorphTrivial`). It covers the identity of the base, sends `v` to the
fibre coordinate of `e v`, and its inverse is the partial inverse of `e`
(`Bundle.Trivialization.homeomorphTrivial_apply`,
`Bundle.Trivialization.homeomorphTrivial_symm_apply`). For a linear trivialization of a
vector bundle over a nontrivially normed field `𝕜`, on the fibre over `b` it is the continuous
linear equivalence `e.continuousLinearEquivAt 𝕜 b`, with inverse its symmetric
(`Bundle.Trivialization.homeomorphTrivial_apply_eq_continuousLinearEquivAt`,
`Bundle.Trivialization.homeomorphTrivial_symm_apply_eq_continuousLinearEquivAt`).
-/

public section

noncomputable section

open Bundle

namespace Bundle.Trivialization

variable {B : Type*} [TopologicalSpace B] {F : Type*} [TopologicalSpace F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] (e : Trivialization F (π F E))

/-- The homeomorphism `E ≃ₜ B × F` of a trivialization over the whole base, read as a
homeomorphism onto the total space of the trivial bundle. -/
def homeomorphTrivial (he : e.baseSet = Set.univ) :
    TotalSpace F E ≃ₜ TotalSpace F (Bundle.Trivial B F) :=
  (e.toHomeomorphOfSourceEqUnivTargetEqUniv (by simp [e.source_eq, he])
    (by simp [e.target_eq, he])).trans (Bundle.Trivial.homeomorphProd B F).symm

@[simp]
theorem homeomorphTrivial_apply (he : e.baseSet = Set.univ) (v : TotalSpace F E) :
    e.homeomorphTrivial he v = TotalSpace.mk' F v.proj (e v).2 := by
  rw [homeomorphTrivial, Homeomorph.trans_apply, Homeomorph.symm_apply_eq]
  exact Prod.ext (e.coe_fst' (he ▸ Set.mem_univ v.proj)) rfl

@[simp]
theorem homeomorphTrivial_symm_apply (he : e.baseSet = Set.univ)
    (w : TotalSpace F (Bundle.Trivial B F)) :
    (e.homeomorphTrivial he).symm w = e.toPartialHomeomorph.symm (w.proj, w.2) := by
  rfl

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] (e : Trivialization F (π F E)) [e.IsLinear 𝕜]

theorem homeomorphTrivial_apply_eq_continuousLinearEquivAt (he : e.baseSet = Set.univ)
    (v : TotalSpace F E) :
    e.homeomorphTrivial he v = TotalSpace.mk' F v.proj (e.continuousLinearEquivAt 𝕜 v.proj
      (he ▸ Set.mem_univ _) v.2) :=
  congrArg (Bundle.Trivial.homeomorphProd B F).symm
    (e.apply_eq_prod_continuousLinearEquivAt 𝕜 v.proj (he ▸ Set.mem_univ _) v.2)

theorem homeomorphTrivial_symm_apply_eq_continuousLinearEquivAt (he : e.baseSet = Set.univ)
    (w : TotalSpace F (Bundle.Trivial B F)) :
    (e.homeomorphTrivial he).symm w = TotalSpace.mk' F w.proj
      ((e.continuousLinearEquivAt 𝕜 w.proj (he ▸ Set.mem_univ _)).symm w.2) := by
  rw [Homeomorph.symm_apply_eq, homeomorphTrivial_apply_eq_continuousLinearEquivAt 𝕜]
  exact congrArg (TotalSpace.mk' F w.proj) (ContinuousLinearEquiv.apply_symm_apply _ _).symm

end Bundle.Trivialization
