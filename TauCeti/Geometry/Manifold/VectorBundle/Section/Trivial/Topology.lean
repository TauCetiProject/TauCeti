/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial

/-!
# The frame topology on sections of trivial bundles

On a trivial bundle the frame topology is the weak Whitney topology of the corresponding maps: the
identification of sections with maps is continuous in both directions
(`ContMDiffSection.continuous_trivialEquiv_frameTopology`,
`ContMDiffSection.continuous_trivialEquiv_symm_frameTopology`).
-/

public noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} [IsManifold I n M] [LocallyCompactSpace E]

variable (M F) in
/-- The frame topology on the sections of the trivial bundle with fibre `F` over `M`, defined using
its preferred trivializations. -/
private abbrev trivialFrameTopology : TopologicalSpace Cₛ^n⟮I; F, Bundle.Trivial M F⟯ :=
  frameTopology (I := I) (n := n) (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x)
    (fun x ↦ ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩) fun _ ↦ subset_rfl

/-- On the sections of a trivial bundle, the identification with maps (`trivialEquiv`) is
continuous from the frame topology to the weak Whitney topology. -/
theorem continuous_trivialEquiv_frameTopology :
    letI := frameTopology (I := I) (n := n) (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x)
      (fun x ↦ ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩) fun _ ↦ subset_rfl
    Continuous (fun s : Cₛ^n⟮I; F, Bundle.Trivial M F⟯ ↦
      (trivialEquiv s : C^n⟮I, M; 𝓘(𝕜, F), F⟯)) := by
  let _ := trivialFrameTopology (I := I) (n := n) M F
  refine ContMDiffMap.continuous_of_forall_continuous_restrict
    (fun x : M ↦ ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩)
    (fun x ↦ ⟨x, mem_baseSet_trivializationAt F (Bundle.Trivial M F) x⟩) fun x ↦ ?_
  -- On a frame domain the restricted map is the frame coordinate function.
  convert continuous_frameCoordinates (I := I) (n := n)
    (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x)
    (fun x ↦ ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩) (fun _ ↦ subset_rfl) x
    using 1
  funext s
  ext y
  simp [Bundle.Trivialization.frameCoordinates_apply]

/-- On the sections of a trivial bundle, the identification with maps (`trivialEquiv`) has an
inverse which is continuous from the weak Whitney topology to the frame topology. -/
theorem continuous_trivialEquiv_symm_frameTopology :
    letI := frameTopology (I := I) (n := n) (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x)
      (fun x ↦ ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩) fun _ ↦ subset_rfl
    Continuous (fun g : C^n⟮I, M; 𝓘(𝕜, F), F⟯ ↦
      (trivialEquiv.symm g : Cₛ^n⟮I; F, Bundle.Trivial M F⟯)) := by
  let _ := trivialFrameTopology (I := I) (n := n) M F
  refine (continuous_frameTopology_iff_frameCoordinates (I := I) (n := n)
    (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x)
    (fun x ↦ ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩)
    (fun _ ↦ subset_rfl)).2 fun x ↦ ?_
  -- The frame coordinate function of a map is its restriction to the frame domain.
  convert ContMDiffMap.continuous_restrict (I := I) (J := 𝓘(𝕜, F)) (n := n)
    ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩ using 1
  funext g
  ext y
  simp [Bundle.Trivialization.frameCoordinates_apply]

end ContMDiffSection
