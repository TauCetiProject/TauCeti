/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import TauCeti.Analysis.Calculus.TangentCone.Chart

/-!
# Analytic changes of ambient coordinates

Analytic charts, analytic submanifolds, and analytic functions on submanifolds transport along an
open partial homeomorphism `(Fin n → 𝕜) → (Fin n' → 𝕜)` that is analytic on its source with inverse
analytic on its target, and in particular along a global analytic homeomorphism or a continuous
linear equivalence `(Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜`. Whenever the domain of such an open partial
homeomorphism is nonempty, invertibility of its derivative forces `n = n'`.

## Main declarations

* `TauCeti.IsAnalyticChart.of_isImage`, `TauCeti.IsAnalyticSubmanifold.of_isImage`,
  `TauCeti.IsAnalyticSubmanifold.image_openPartialHomeomorph`: transport of analytic charts and
  analytic submanifolds along analytic open partial homeomorphisms with analytic inverse.
* `TauCeti.AnalyticOnSubmanifold.comp_openPartialHomeomorph`,
  `TauCeti.AnalyticOnSubmanifold.comp_symm_openPartialHomeomorph`: transport of analytic functions
  on submanifolds along analytic open partial homeomorphisms.
* `TauCeti.IsAnalyticChart.preimage`, `TauCeti.IsAnalyticSubmanifold.preimage`: pullback along
  global analytic homeomorphisms.
* `TauCeti.IsAnalyticSubmanifold.preimage_continuousLinearEquiv`,
  `TauCeti.IsAnalyticSubmanifold.image_continuousLinearEquiv`,
  `TauCeti.AnalyticOnSubmanifold.comp_continuousLinearEquiv`,
  `TauCeti.AnalyticOnSubmanifold.comp_symm_continuousLinearEquiv`,
  `TauCeti.IsAnalyticSubmanifold.preimage_comp_equiv`: transport along continuous linear
  equivalences and coordinate bijections, together with `@[simp]` equivalences.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {n n' d : ℕ} {S T : Set (Fin n → 𝕜)}
  {c : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜)}

/-! ### Open partial homeomorphisms -/

/-- Pulling back an analytic chart of `T` along an analytic open partial homeomorphism `φ` with
analytic inverse, satisfying `φ.IsImage S T`, gives an analytic chart of `S`. -/
theorem IsAnalyticChart.of_isImage {φ : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜)}
    (hc : IsAnalyticChart d T c) (hφ : AnalyticOnNhd 𝕜 φ φ.source)
    (hφs : AnalyticOnNhd 𝕜 φ.symm φ.target) (hST : φ.IsImage S T) :
    IsAnalyticChart d S (φ.trans c) := by
  refine ⟨?_, ?_, fun x hx ↦ ?_⟩
  · intro x hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    simpa only [OpenPartialHomeomorph.coe_trans] using (hc.analyticOnNhd _ hx.2).comp (hφ x hx.1)
  · intro y hy
    rw [OpenPartialHomeomorph.trans_target] at hy
    simpa only [OpenPartialHomeomorph.coe_trans_symm] using
      (hφs _ hy.2).comp (hc.analyticOnNhd_symm y hy.1)
  · rw [OpenPartialHomeomorph.trans_source] at hx
    rw [OpenPartialHomeomorph.trans_apply, hc.isImage hx.2, hST hx.1]

/-- Pulling back an analytic submanifold `T` along an analytic open partial homeomorphism `φ` with
analytic inverse preserves analytic submanifolds when `S ⊆ φ.source` is nonempty and
`φ.IsImage S T`. -/
theorem IsAnalyticSubmanifold.of_isImage {T : Set (Fin n' → 𝕜)}
    {φ : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n' → 𝕜)} (hT : IsAnalyticSubmanifold d T)
    (hφ : AnalyticOnNhd 𝕜 φ φ.source) (hφs : AnalyticOnNhd 𝕜 φ.symm φ.target)
    (hS : S ⊆ φ.source) (hne : S.Nonempty) (hST : φ.IsImage S T) :
    IsAnalyticSubmanifold d S := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀φ : x₀ ∈ φ.source := hS hx₀
  have hn : n = n' := by
    obtain ⟨A, -⟩ := φ.exists_hasFDerivAt_of_chart hx₀φ (hφ x₀ hx₀φ).differentiableAt
      (hφs (φ x₀) (φ.map_source hx₀φ)).differentiableAt
    simpa using A.toLinearEquiv.finrank_eq
  subst hn
  refine ⟨⟨x₀, hx₀⟩, hT.le, fun x hx ↦ ?_⟩
  have hxφ : x ∈ φ.source := hS hx
  obtain ⟨c, hxc, hc⟩ := hT.exists_isAnalyticChart (φ x) ((hST hxφ).2 hx)
  exact ⟨φ.trans c, ⟨hxφ, hxc⟩, hc.of_isImage hφ hφs hST⟩

/-- The image of the part of an analytic submanifold lying in the source of an analytic open
partial homeomorphism with analytic inverse is an analytic submanifold of the same dimension,
provided that intersection is nonempty. -/
theorem IsAnalyticSubmanifold.image_openPartialHomeomorph
    {φ : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n' → 𝕜)} (hS : IsAnalyticSubmanifold d S)
    (hφ : AnalyticOnNhd 𝕜 φ φ.source) (hφs : AnalyticOnNhd 𝕜 φ.symm φ.target)
    (hne : (S ∩ φ.source).Nonempty) :
    IsAnalyticSubmanifold d (φ '' (S ∩ φ.source)) := by
  refine hS.of_isImage (φ := φ.symm) hφs hφ ?_ (hne.image φ) fun y hy ↦ ?_
  · rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    exact φ.map_source hx
  · refine ⟨fun hyS ↦ ⟨φ.symm y, ⟨hyS, φ.map_target hy⟩, φ.right_inv hy⟩, ?_⟩
    rintro ⟨x, ⟨hxS, hx⟩, rfl⟩
    rwa [φ.left_inv hx]

/-- Precomposing an analytic function on `T` with an analytic open partial homeomorphism `φ` with
analytic inverse gives an analytic function on `S` when `S ⊆ φ.source` and `φ.IsImage S T`. -/
theorem AnalyticOnSubmanifold.comp_openPartialHomeomorph {T : Set (Fin n' → 𝕜)}
    {φ : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n' → 𝕜)} {f : (Fin n' → 𝕜) → E}
    (hf : AnalyticOnSubmanifold d f T)
    (hφ : AnalyticOnNhd 𝕜 φ φ.source) (hφs : AnalyticOnNhd 𝕜 φ.symm φ.target)
    (hS : S ⊆ φ.source) (hST : φ.IsImage S T) :
    AnalyticOnSubmanifold d (f ∘ φ) S := by
  rw [analyticOnSubmanifold_iff] at hf ⊢
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · rintro _ ⟨⟩
  have hx₀φ : x₀ ∈ φ.source := hS hx₀
  have hn : n = n' := by
    obtain ⟨A, -⟩ := φ.exists_hasFDerivAt_of_chart hx₀φ (hφ x₀ hx₀φ).differentiableAt
      (hφs (φ x₀) (φ.map_source hx₀φ)).differentiableAt
    simpa using A.toLinearEquiv.finrank_eq
  subst hn
  intro x hx
  have hxφ : x ∈ φ.source := hS hx
  have hxT : φ x ∈ T := (hST hxφ).2 hx
  obtain ⟨c, hxc, hc, hf'⟩ := hf (φ x) hxT
  refine ⟨φ.trans c, ⟨hxφ, hxc⟩, hc.of_isImage hφ hφs hST, ?_⟩
  have hmem : ∀ᶠ u in 𝓝 (firstCoords 𝕜 n d ((φ.trans c) x)),
      c.symm (firstCoords 𝕜 d n u) ∈ φ.target := by
    have ht : firstCoords 𝕜 d n ⁻¹' (φ.trans c).target ∈
        𝓝 (firstCoords 𝕜 n d ((φ.trans c) x)) := by
      refine (firstCoords 𝕜 d n).continuous.continuousAt.preimage_mem_nhds
        ((φ.trans c).open_target.mem_nhds ?_)
      rw [(hc.of_isImage hφ hφs hST).firstCoords_firstCoords_apply ⟨hxφ, hxc⟩ hx]
      exact (φ.trans c).map_source ⟨hxφ, hxc⟩
    filter_upwards [ht] with u hu
    exact ((OpenPartialHomeomorph.trans_target φ c).subset hu).2
  have hf'' : AnalyticAt 𝕜 (fun u ↦ f (c.symm (firstCoords 𝕜 d n u)))
      (firstCoords 𝕜 n d ((φ.trans c) x)) := by
    simpa only [OpenPartialHomeomorph.trans_apply] using hf'
  refine hf''.congr ?_
  filter_upwards [hmem] with u hu
  simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans_symm, φ.right_inv hu]

/-- Pushing an analytic function on `S` forward along an analytic open partial homeomorphism `φ`
with analytic inverse gives an analytic function on `φ '' (S ∩ φ.source)`. -/
theorem AnalyticOnSubmanifold.comp_symm_openPartialHomeomorph
    {φ : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n' → 𝕜)} {f : (Fin n → 𝕜) → E}
    (hf : AnalyticOnSubmanifold d f S)
    (hφ : AnalyticOnNhd 𝕜 φ φ.source) (hφs : AnalyticOnNhd 𝕜 φ.symm φ.target) :
    AnalyticOnSubmanifold d (f ∘ φ.symm) (φ '' (S ∩ φ.source)) := by
  refine hf.comp_openPartialHomeomorph (φ := φ.symm) hφs hφ ?_ fun y hy ↦ ?_
  · rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    exact φ.map_source hx
  · refine ⟨fun hyS ↦ ⟨φ.symm y, ⟨hyS, φ.map_target hy⟩, φ.right_inv hy⟩, ?_⟩
    rintro ⟨x, ⟨hxS, hx⟩, rfl⟩
    rwa [φ.left_inv hx]

/-! ### Global homeomorphisms and continuous linear equivalences -/

/-- Pulling back an analytic chart along an analytic change of ambient coordinates gives an
analytic chart of the inverse image. -/
theorem IsAnalyticChart.preimage (hc : IsAnalyticChart d S c)
    (e : (Fin n → 𝕜) ≃ₜ (Fin n → 𝕜))
    (he : AnalyticOnNhd 𝕜 e univ) (he' : AnalyticOnNhd 𝕜 e.symm univ) :
    IsAnalyticChart d (e ⁻¹' S) (e.toOpenPartialHomeomorph.trans c) :=
  hc.of_isImage he he' fun _ _ ↦ Iff.rfl

/-- An analytic change of ambient coordinates preserves analytic submanifolds and their
dimension. The inverse must also be analytic. -/
theorem IsAnalyticSubmanifold.preimage {T : Set (Fin n' → 𝕜)} (hT : IsAnalyticSubmanifold d T)
    (e : (Fin n → 𝕜) ≃ₜ (Fin n' → 𝕜))
    (he : AnalyticOnNhd 𝕜 e univ) (he' : AnalyticOnNhd 𝕜 e.symm univ) :
    IsAnalyticSubmanifold d (e ⁻¹' T) := by
  obtain ⟨y, hy⟩ := hT.nonempty
  exact hT.of_isImage (φ := e.toOpenPartialHomeomorph) he he' (subset_univ _)
    ⟨e.symm y, by simpa using hy⟩ fun _ _ ↦ Iff.rfl

/-- Pulling back an analytic submanifold along a continuous linear equivalence
`(Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜` preserves analytic submanifolds and their dimension. -/
theorem IsAnalyticSubmanifold.preimage_continuousLinearEquiv {T : Set (Fin n' → 𝕜)}
    (hT : IsAnalyticSubmanifold d T) (e : (Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜) :
    IsAnalyticSubmanifold d (e ⁻¹' T) :=
  hT.preimage e.toHomeomorph (fun y _ ↦ e.analyticAt y) (fun y _ ↦ e.symm.analyticAt y)

/-- Mapping an analytic submanifold by a continuous linear equivalence
`(Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜` preserves analytic submanifolds and their dimension. -/
theorem IsAnalyticSubmanifold.image_continuousLinearEquiv (hS : IsAnalyticSubmanifold d S)
    (e : (Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜) :
    IsAnalyticSubmanifold d (e '' S) := by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]
  exact hS.preimage_continuousLinearEquiv e.symm

/-- Preimage under a continuous linear equivalence `(Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜` preserves
`IsAnalyticSubmanifold`. -/
@[simp]
theorem isAnalyticSubmanifold_preimage_continuousLinearEquiv_iff {T : Set (Fin n' → 𝕜)}
    (e : (Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜) :
    IsAnalyticSubmanifold d (e ⁻¹' T) ↔ IsAnalyticSubmanifold d T :=
  ⟨fun h ↦ by simpa [preimage_preimage] using h.preimage_continuousLinearEquiv e.symm,
    fun h ↦ h.preimage_continuousLinearEquiv e⟩

/-- Image under a continuous linear equivalence `(Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜` preserves
`IsAnalyticSubmanifold`. -/
@[simp]
theorem isAnalyticSubmanifold_image_continuousLinearEquiv_iff
    (e : (Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜) :
    IsAnalyticSubmanifold d (e '' S) ↔ IsAnalyticSubmanifold d S := by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm,
    isAnalyticSubmanifold_preimage_continuousLinearEquiv_iff]

/-- Precomposing an analytic function on a submanifold with a continuous linear equivalence
`(Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜` gives an analytic function on the preimage. -/
theorem AnalyticOnSubmanifold.comp_continuousLinearEquiv {T : Set (Fin n' → 𝕜)}
    {f : (Fin n' → 𝕜) → E} (hf : AnalyticOnSubmanifold d f T)
    (e : (Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜) :
    AnalyticOnSubmanifold d (f ∘ e) (e ⁻¹' T) :=
  hf.comp_openPartialHomeomorph (φ := e.toHomeomorph.toOpenPartialHomeomorph)
    (fun y _ ↦ e.analyticAt y) (fun y _ ↦ e.symm.analyticAt y) (subset_univ _) fun _ _ ↦ Iff.rfl

/-- Transporting an analytic function on a submanifold along a continuous linear equivalence
`(Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜` gives an analytic function on the image. -/
theorem AnalyticOnSubmanifold.comp_symm_continuousLinearEquiv {f : (Fin n → 𝕜) → E}
    (hf : AnalyticOnSubmanifold d f S) (e : (Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜) :
    AnalyticOnSubmanifold d (f ∘ e.symm) (e '' S) := by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm]
  exact hf.comp_continuousLinearEquiv e.symm

/-- Precomposing with a continuous linear equivalence `(Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜` preserves
`AnalyticOnSubmanifold` on the preimage. -/
@[simp]
theorem analyticOnSubmanifold_comp_continuousLinearEquiv_iff {T : Set (Fin n' → 𝕜)}
    {f : (Fin n' → 𝕜) → E} (e : (Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜) :
    AnalyticOnSubmanifold d (f ∘ e) (e ⁻¹' T) ↔ AnalyticOnSubmanifold d f T :=
  ⟨fun h ↦ by
    simpa [Function.comp_def, preimage_preimage] using h.comp_continuousLinearEquiv e.symm,
    fun h ↦ h.comp_continuousLinearEquiv e⟩

/-- Transporting along a continuous linear equivalence `(Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜` preserves
`AnalyticOnSubmanifold` on the image. -/
@[simp]
theorem analyticOnSubmanifold_comp_symm_continuousLinearEquiv_iff {f : (Fin n → 𝕜) → E}
    (e : (Fin n → 𝕜) ≃L[𝕜] Fin n' → 𝕜) :
    AnalyticOnSubmanifold d (f ∘ e.symm) (e '' S) ↔ AnalyticOnSubmanifold d f S := by
  rw [ContinuousLinearEquiv.image_eq_preimage_symm,
    analyticOnSubmanifold_comp_continuousLinearEquiv_iff]

/-- Reindexing the ambient coordinates along a bijection `Fin n ≃ Fin n'` preserves analytic
submanifolds and their dimension. For `n' = n` this is a permutation of the coordinates. -/
theorem IsAnalyticSubmanifold.preimage_comp_equiv (hS : IsAnalyticSubmanifold d S)
    (e : Fin n ≃ Fin n') : IsAnalyticSubmanifold d ((fun x : Fin n' → 𝕜 ↦ x ∘ e) ⁻¹' S) :=
  hS.preimage_continuousLinearEquiv
    (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n' ↦ 𝕜) e).symm

end TauCeti
