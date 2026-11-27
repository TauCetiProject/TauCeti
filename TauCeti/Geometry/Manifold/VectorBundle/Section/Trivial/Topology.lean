/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The frame topology on sections of trivial bundles

On a trivial bundle the frame topology is the weak Whitney topology of the corresponding maps: the
identification of sections with maps is continuous in both directions
(`ContMDiffSection.continuous_trivialEquiv_frameTopology`,
`ContMDiffSection.continuous_trivialEquiv_symm_frameTopology`).

In the preferred trivializations of `Bundle.Trivial M F` the frame coordinates of a section are
its values (`Bundle.Trivial.frameCoordinates_trivializationAt_apply`). Hence pullback of sections
of trivial bundles along a `C^n` map (`ContMDiffSection.trivialPullback`) is continuous for the
compact derivative topologies of the preferred frames
(`ContMDiffSection.continuous_trivialPullback`): composition with a fixed smooth map is continuous
in the weak Whitney topology (`ContMDiffMap.continuous_comp_manifoldWeakWhitney`).
-/

public noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}

/-- In the preferred trivializations of a trivial bundle, the frame coordinates of a section are
its values. -/
theorem Bundle.Trivial.frameCoordinates_trivializationAt_apply (x₀ : M) {U : Opens M}
    (hU : (U : Set M) ⊆ (trivializationAt F (Bundle.Trivial M F) x₀).baseSet)
    (s : Cₛ^n⟮I; F, Bundle.Trivial M F⟯) (x : U) :
    (trivializationAt F (Bundle.Trivial M F) x₀).frameCoordinates hU s x = s x := by
  simp

namespace ContMDiffSection

section TrivialEquiv

variable [IsManifold I n M] [LocallyCompactSpace E]

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

end TrivialEquiv

variable [LocallyCompactSpace E] [LocallyCompactSpace E'] [IsManifold I n M] [IsManifold J n N]

/-- Pullback of sections of trivial bundles along a `C^n` map is continuous for the compact
derivative topologies of the preferred trivializations. In these frames the coefficients of a
section are its values, so this is continuity of composition with a fixed map in the weak Whitney
topology. -/
theorem continuous_trivialPullback (f : C^n⟮I, M; J, N⟯) :
    letI := frameTopology (I := J) (n := n) (fun y : N ↦ trivializationAt F (Bundle.Trivial N F) y)
      (fun y ↦ ⟨_, (trivializationAt F (Bundle.Trivial N F) y).open_baseSet⟩) fun _ ↦ subset_rfl
    letI := frameTopology (I := I) (n := n) (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x)
      (fun x ↦ ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩) fun _ ↦ subset_rfl
    Continuous (trivialPullback (F := F) f) := by
  let := frameTopology (I := J) (n := n) (fun y : N ↦ trivializationAt F (Bundle.Trivial N F) y)
    (fun y ↦ ⟨_, (trivializationAt F (Bundle.Trivial N F) y).open_baseSet⟩) fun _ ↦ subset_rfl
  let := frameTopology (I := I) (n := n) (fun x : M ↦ trivializationAt F (Bundle.Trivial M F) x)
    (fun x ↦ ⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩) fun _ ↦ subset_rfl
  refine (continuous_frameTopology_iff_frameCoordinates _ _ _).2 fun x ↦ ?_
  -- The preferred trivializations of trivial bundles have the whole base as base set, so `f`
  -- restricts to a map between the frame domains at `x` and at `f x`.
  let g : C^n⟮I, (⟨_, (trivializationAt F (Bundle.Trivial M F) x).open_baseSet⟩ : Opens M);
      J, (⟨_, (trivializationAt F (Bundle.Trivial N F) (f x)).open_baseSet⟩ : Opens N)⟯ :=
    ⟨fun z ↦ ⟨f z, mem_univ _⟩, (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
      (f.contMDiff.comp contMDiff_subtypeVal)⟩
  refine (ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
    ((continuous_frameCoordinates _ _ _ (f x)).prodMk (continuous_const (y := g)))).congr
    fun s ↦ ?_
  ext z
  simp only [Function.comp_apply, ContMDiffMap.comp_apply,
    Bundle.Trivial.frameCoordinates_trivializationAt_apply, trivialPullback_apply]
  simp [g]

end ContMDiffSection
