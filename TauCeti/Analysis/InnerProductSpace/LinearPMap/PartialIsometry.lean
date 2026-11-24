/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.AdjointComp
public import TauCeti.Analysis.InnerProductSpace.PartialIsometry
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SubmoduleAdjoint
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
  have hproj (x : M.domain) : u.adjoint (u (M x)) = M x :=
    hu.adjoint_apply_apply (hrange (LinearMap.mem_range_self M.toFun x))
  have hdom : ((u : E →ₗ[𝕜] F).compPMap M).adjointComp.domain = M.adjointComp.domain := by
    ext x
    rw [LinearPMap.mem_adjointComp_domain, LinearPMap.mem_adjointComp_domain]
    refine ⟨fun ⟨hx, hux⟩ ↦ ⟨hx, ?_⟩, fun ⟨hx, hMx⟩ ↦ ⟨hx, ?_⟩⟩
    · rw [hadj] at hux
      -- Unfold `.comp` domain membership on `hux` to `u.adjoint (u (M ⟨x, hx⟩)) ∈ M†.domain`.
      change u.adjoint (u (M ⟨x, hx⟩)) ∈ M†.domain at hux
      rwa [hproj ⟨x, hx⟩] at hux
    · rw [hadj]
      -- Unfold `.comp` domain membership to `u.adjoint (u (M ⟨x, hx⟩)) ∈ M†.domain`.
      change u.adjoint (u (M ⟨x, hx⟩)) ∈ M†.domain
      rwa [hproj ⟨x, hx⟩]
  refine LinearPMap.ext hdom fun x hx₁ hx₂ ↦ ?_
  have hxM : x ∈ M.domain := LinearPMap.adjointComp_domain_le M hx₂
  have hMx : M ⟨x, hxM⟩ ∈ M†.domain := (LinearPMap.mem_adjointComp_domain.mp hx₂).choose_spec
  have hux : u.adjoint (u (M ⟨x, hxM⟩)) ∈ M†.domain := (hproj ⟨x, hxM⟩).symm ▸ hMx
  rw [LinearPMap.adjointComp_apply _ ⟨x, hx₁⟩, LinearPMap.adjointComp_apply M ⟨x, hx₂⟩]
  have hcomp : ((u : E →ₗ[𝕜] F).compPMap M) ⟨x, LinearPMap.adjointComp_domain_le _ hx₁⟩ ∈
      (M†.comp ((u.adjoint : F →ₗ[𝕜] E).toPMap
        (M†.domain.comap (u.adjoint : F →ₗ[𝕜] E))) fun y ↦ y.property).domain := hux
  let lhsVal : (((u : E →ₗ[𝕜] F).compPMap M)†).domain :=
    ⟨((u : E →ₗ[𝕜] F).compPMap M) ⟨x, LinearPMap.adjointComp_domain_le _ hx₁⟩,
      (LinearPMap.mem_adjointComp_domain.mp hx₁).choose_spec⟩
  have lhs_eq : (((u : E →ₗ[𝕜] F).compPMap M)†) lhsVal =
      (M†) ⟨u.adjoint (u (M ⟨x, hxM⟩)), hux⟩ :=
    LinearPMap.congr_fun hadj lhsVal.property hcomp
  rw [lhs_eq]
  exact congrArg (M†) (Subtype.ext (hproj ⟨x, hxM⟩))

end Hilbert

end ContinuousLinearMap
