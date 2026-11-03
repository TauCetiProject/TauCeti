/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Multilinear.Basis
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# `C^n` families of continuous alternating maps

A family of continuous alternating maps `f : M → E [⋀^ι]→L[𝕜] F` on a finite-dimensional space
`E`, parametrized by a manifold, is `C^n` exactly when each evaluation `y ↦ f y v` is `C^n`.
This is the alternating counterpart of Mathlib's `contDiffWithinAt_clm_apply` for continuous
linear maps. It reduces the regularity of a differential form, read in a trivialization of the
alternating bundle, to the regularity of its values on fixed tuples of model vectors.

The converse direction expands an alternating map as `∑ₜ c t (·) • f y (b ∘ t)` over all tuples
`t` of basis indices, with scalar coefficient forms `c t` that do not depend on `f`. This is a
continuous linear function of the evaluations, so the coefficient space `F` may be
infinite-dimensional.
-/

public section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} [Fintype ι] {n : WithTop ℕ∞} {f : M → E [⋀^ι]→L[𝕜] F} {s : Set M} {x : M}

/-- A family of continuous alternating maps on a finite-dimensional space is `C^n` within a set at
a point if and only if all its evaluations are. -/
theorem contMDiffWithinAt_continuousAlternatingMap_apply :
    ContMDiffWithinAt I 𝓘(𝕜, E [⋀^ι]→L[𝕜] F) n f s x ↔
      ∀ v : ι → E, ContMDiffWithinAt I 𝓘(𝕜, F) n (fun y ↦ f y v) s x := by
  refine ⟨fun h v ↦ (ContinuousAlternatingMap.apply 𝕜 E F v).contMDiffAt.comp_contMDiffWithinAt
    x h, fun h ↦ ?_⟩
  classical
  let b := Module.finBasis 𝕜 E
  -- Evaluation of scalar alternating maps on all tuples of basis vectors is injective, so it has
  -- a linear left inverse; its values on the standard basis are the coefficient forms `c t`.
  let Φ : (E [⋀^ι]→ₗ[𝕜] 𝕜) →ₗ[𝕜] (ι → Fin (finrank 𝕜 E)) → 𝕜 :=
    { toFun a t := a fun i ↦ b (t i), map_add' _ _ := rfl, map_smul' _ _ := rfl }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun a ha ↦ AlternatingMap.coe_multilinearMap_injective
      (Basis.ext_multilinear (fun _ ↦ b) fun t ↦ ?_)
    simpa [Φ] using congr_fun ha t
  obtain ⟨Ψ, hΨ⟩ := Φ.exists_leftInverse_of_injective hΦ
  let c (t : ι → Fin (finrank 𝕜 E)) : E [⋀^ι]→L[𝕜] 𝕜 :=
    AlternatingMap.toContinuousAlternatingMap (Ψ (Pi.single t 1))
  have hc (t : ι → Fin (finrank 𝕜 E)) (v : ι → E) : c t v = Ψ (Pi.single t 1) v :=
    congr_fun (AlternatingMap.coe_toContinuousAlternatingMap _) v
  have hscalar (a : E [⋀^ι]→ₗ[𝕜] 𝕜) (v : ι → E) :
      a v = ∑ t, c t v * a fun i ↦ b (t i) := by
    have hΦa : Φ a = ∑ t, a (fun i ↦ b (t i)) • Pi.single t (1 : 𝕜) := by
      ext t'
      simp [Φ, Pi.single_apply]
    conv_lhs => rw [← show Ψ (Φ a) = a from LinearMap.congr_fun hΨ a]
    rw [hΦa, map_sum]
    simp [hc, mul_comm]
  -- The expansion transfers to `F`-valued maps coordinatewise in an algebraic basis of `F`.
  let β := Module.Free.chooseBasis 𝕜 F
  have hF (A : E [⋀^ι]→L[𝕜] F) (v : ι → E) : A v = ∑ t, c t v • A fun i ↦ b (t i) := by
    refine β.ext_elem fun j ↦ ?_
    simpa [Finsupp.coe_finsetSum, Basis.coord_apply] using
      hscalar ((β.coord j).compAlternatingMap A.toAlternatingMap) v
  -- Each coefficient form gives the continuous linear map `z ↦ c t (·) • z`.
  let L (t : ι → Fin (finrank 𝕜 E)) : F →L[𝕜] E [⋀^ι]→L[𝕜] F :=
    (ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E 𝕜 F ι).flip (c t) ∘L
      ContinuousLinearMap.smulRightL 𝕜 𝕜 F 1
  let R : ((ι → Fin (finrank 𝕜 E)) → F) →L[𝕜] E [⋀^ι]→L[𝕜] F :=
    ∑ t, L t ∘L ContinuousLinearMap.proj t
  have hf : f = fun y ↦ R fun t ↦ f y fun i ↦ b (t i) := by
    funext y
    ext v
    simp [R, L, hF (f y) v]
  rw [hf]
  exact R.contMDiffAt.comp_contMDiffWithinAt x (contMDiffWithinAt_pi_module_iff.2 fun t ↦ h _)

/-- A family of continuous alternating maps on a finite-dimensional space is `C^n` at a point if
and only if all its evaluations are. -/
theorem contMDiffAt_continuousAlternatingMap_apply :
    ContMDiffAt I 𝓘(𝕜, E [⋀^ι]→L[𝕜] F) n f x ↔
      ∀ v : ι → E, ContMDiffAt I 𝓘(𝕜, F) n (fun y ↦ f y v) x :=
  contMDiffWithinAt_continuousAlternatingMap_apply

end TauCeti
