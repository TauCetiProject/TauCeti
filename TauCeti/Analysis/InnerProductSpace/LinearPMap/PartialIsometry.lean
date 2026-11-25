/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.AdjointComp
public import TauCeti.Analysis.InnerProductSpace.PartialIsometry
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# Composing bounded partial isometries with unbounded partial linear maps

When a bounded partial isometry `u : E →L[𝕜] F` between Hilbert spaces is composed on the left with
a partial linear map `M : G →ₗ.[𝕜] E` whose range lies in the initial space `(ker u)ᗮ`, the initial
projection `u† u` acts as the identity on `range M`. Consequently:

* left-composing `u ∘ M` with `u†` recovers `M` on `M.domain`
  (`ContinuousLinearMap.IsPartialIsometry.adjoint_compPMap_compPMap`);
* `u ∘ M` is closed if and only if `M` is closed
  (`ContinuousLinearMap.IsPartialIsometry.isClosed_compPMap_iff`,
  `ContinuousLinearMap.IsPartialIsometry.isClosed_compPMap`);
* when `G` is also a Hilbert space, the maximal source Gram operator `(u ∘ M)† (u ∘ M)` coincides
  with `M† M` (`ContinuousLinearMap.IsPartialIsometry.compPMap_adjointComp`).

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), §VI.2.7.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press (1980), Theorem VIII.32.
-/

public section

open scoped InnerProduct LinearPMap

namespace ContinuousLinearMap

section Module

variable {𝕜 G E F : Type*} [RCLike 𝕜]
  [AddCommGroup G] [Module 𝕜 G]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Left-composing `u ∘ M` with `u†` recovers `M` whenever `range M` lies in the initial space
`(ker u)ᗮ` of the partial isometry `u`. -/
theorem IsPartialIsometry.adjoint_compPMap_compPMap {u : E →L[𝕜] F} (hu : u.IsPartialIsometry)
    {M : G →ₗ.[𝕜] E} (hrange : LinearMap.range M.toFun ≤ u.kerᗮ) :
    (u.adjoint : F →ₗ[𝕜] E).compPMap ((u : E →ₗ[𝕜] F).compPMap M) = M :=
  LinearPMap.ext rfl fun x hx _ ↦
    hu.adjoint_apply_apply (hrange (LinearMap.mem_range_self M.toFun ⟨x, hx⟩))

/-- Composing a partial linear map `M` on the left with a bounded partial isometry `u` whose
initial space `(ker u)ᗮ` contains `range M` preserves and reflects graph closedness. -/
theorem IsPartialIsometry.isClosed_compPMap_iff [TopologicalSpace G]
    {u : E →L[𝕜] F} (hu : u.IsPartialIsometry) {M : G →ₗ.[𝕜] E}
    (hrange : LinearMap.range M.toFun ≤ u.kerᗮ) :
    ((u : E →ₗ[𝕜] F).compPMap M).IsClosed ↔ M.IsClosed := by
  have hproj (x : M.domain) : u.adjoint (u (M x)) = M x :=
    hu.adjoint_apply_apply (hrange (LinearMap.mem_range_self M.toFun x))
  refine ⟨fun hVM ↦ ?_, fun hM ↦ ?_⟩
  · have hgraph : (M.graph : Set (G × E)) =
        {q | (q.1, u q.2) ∈ (((u : E →ₗ[𝕜] F).compPMap M).graph : Set (G × F)) ∧
          q.2 ∈ (u.kerᗮ : Set E)} := by
      ext ⟨x, z⟩
      rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
      refine ⟨?_, fun ⟨hq₁, hq₂⟩ ↦ ?_⟩
      · rintro ⟨w, rfl, rfl⟩
        exact ⟨((u : E →ₗ[𝕜] F).compPMap M).mem_graph_iff.mpr ⟨⟨w, w.property⟩, rfl, rfl⟩,
          hrange (LinearMap.mem_range_self M.toFun w)⟩
      · obtain ⟨w, hw₁, hw₂⟩ := ((u : E →ₗ[𝕜] F).compPMap M).mem_graph_iff.mp hq₁
        refine ⟨⟨w, w.property⟩, hw₁, ?_⟩
        calc M ⟨w, w.property⟩ = u.adjoint (u (M ⟨w, w.property⟩)) := (hproj ⟨w, w.property⟩).symm
          _ = u.adjoint (u z) := congrArg u.adjoint hw₂
          _ = z := hu.adjoint_apply_apply hq₂
    rw [LinearPMap.IsClosed, hgraph]
    exact (hVM.preimage (continuous_fst.prodMk (u.continuous.comp continuous_snd))).inter
      ((Submodule.isClosed_orthogonal u.ker).preimage continuous_snd)
  · have hgraph : (((u : E →ₗ[𝕜] F).compPMap M).graph : Set (G × F)) =
        {p | (p.1, u.adjoint p.2) ∈ (M.graph : Set (G × E)) ∧ u (u.adjoint p.2) = p.2} := by
      ext ⟨x, y⟩
      rw [SetLike.mem_coe, LinearPMap.mem_graph_iff]
      refine ⟨?_, fun ⟨hp₁, hp₂⟩ ↦ ?_⟩
      · rintro ⟨w, rfl, rfl⟩
        let w' : M.domain := ⟨w, w.property⟩
        exact ⟨M.mem_graph_iff.mpr ⟨w', rfl, (hproj w').symm⟩, hu.apply_adjoint_apply (M w')⟩
      · obtain ⟨w, hw₁, hw₂⟩ := M.mem_graph_iff.mp hp₁
        exact ⟨⟨w, w.property⟩, hw₁, (congrArg u hw₂).trans hp₂⟩
    rw [LinearPMap.IsClosed, hgraph]
    exact (hM.preimage (continuous_fst.prodMk (u.adjoint.continuous.comp continuous_snd))).inter
      (isClosed_eq (u.continuous.comp (u.adjoint.continuous.comp continuous_snd)) continuous_snd)

/-- Composing a closed partial linear map `M` on the left with a bounded partial isometry `u` whose
initial space `(ker u)ᗮ` contains `range M` produces a closed partial linear map. -/
theorem IsPartialIsometry.isClosed_compPMap [TopologicalSpace G]
    {u : E →L[𝕜] F} (hu : u.IsPartialIsometry) {M : G →ₗ.[𝕜] E}
    (hrange : LinearMap.range M.toFun ≤ u.kerᗮ) (hM : M.IsClosed) :
    ((u : E →ₗ[𝕜] F).compPMap M).IsClosed :=
  (hu.isClosed_compPMap_iff hrange).mpr hM

end Module

section Hilbert

variable {𝕜 G E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Composing a partial linear map `M` on the left with a bounded partial isometry `u` whose
initial space `(ker u)ᗮ` contains `range M` preserves `adjointComp`:
`(u ∘ M)† (u ∘ M) = M† M` on maximal domain. -/
theorem IsPartialIsometry.compPMap_adjointComp {u : E →L[𝕜] F} (hu : u.IsPartialIsometry)
    {M : G →ₗ.[𝕜] E} (hrange : LinearMap.range M.toFun ≤ u.kerᗮ) :
    ((u : E →ₗ[𝕜] F).compPMap M).adjointComp = M.adjointComp := by
  have hadj := u.compPMap_adjoint M
  have hcomp_apply {x : G} (hx₁ : x ∈ ((u : E →ₗ[𝕜] F).compPMap M).domain)
      (hx₂ : x ∈ M.domain) :
      u.adjoint (((u : E →ₗ[𝕜] F).compPMap M) ⟨x, hx₁⟩) = M ⟨x, hx₂⟩ := by
    have hval : ((u : E →ₗ[𝕜] F).compPMap M) ⟨x, hx₁⟩ = u (M ⟨x, hx₂⟩) := by
      rw [LinearMap.compPMap_apply, coe_coe]; rfl
    rw [hval]
    exact hu.adjoint_apply_apply (hrange (LinearMap.mem_range_self M.toFun ⟨x, hx₂⟩))
  have hdom : ((u : E →ₗ[𝕜] F).compPMap M).adjointComp.domain = M.adjointComp.domain := by
    ext x
    rw [LinearPMap.mem_adjointComp_domain, LinearPMap.mem_adjointComp_domain]
    refine ⟨fun ⟨hx, hux⟩ ↦ ?_, fun ⟨hx, hMx⟩ ↦ ?_⟩
    · have hx' : x ∈ M.domain := by simpa using hx
      rw [hadj, LinearPMap.mem_comp_toPMap_comap_domain, coe_coe, hcomp_apply hx hx'] at hux
      exact ⟨hx', hux⟩
    · have hx' : x ∈ ((u : E →ₗ[𝕜] F).compPMap M).domain := by simpa using hx
      refine ⟨hx', ?_⟩
      rw [hadj, LinearPMap.mem_comp_toPMap_comap_domain, coe_coe, hcomp_apply hx' hx]
      exact hMx
  refine LinearPMap.ext hdom fun x hx₁ hx₂ ↦ ?_
  have hMx : M ⟨x, LinearPMap.adjointComp_domain_le M hx₂⟩ ∈ M†.domain :=
    (LinearPMap.mem_adjointComp_domain.mp hx₂).choose_spec
  have hux : (u.adjoint : F →ₗ[𝕜] E)
      (((u : E →ₗ[𝕜] F).compPMap M) ⟨x, LinearPMap.adjointComp_domain_le _ hx₁⟩) ∈ M†.domain := by
    simpa only [coe_coe, hcomp_apply _ (LinearPMap.adjointComp_domain_le M hx₂)] using hMx
  have hcomp := (LinearPMap.mem_comp_toPMap_comap_domain (M†) (u.adjoint : F →ₗ[𝕜] E)
    (by rintro ⟨_, hy⟩; simpa using hy)).mpr hux
  rw [LinearPMap.adjointComp_apply _ ⟨x, hx₁⟩, LinearPMap.adjointComp_apply M ⟨x, hx₂⟩,
    LinearPMap.congr_fun hadj (LinearPMap.mem_adjointComp_domain.mp hx₁).choose_spec hcomp,
    LinearPMap.comp_toPMap_comap_apply]
  exact congrArg (M†) (Subtype.ext (by simpa only [coe_coe] using hcomp_apply _ _))

end Hilbert

end ContinuousLinearMap
