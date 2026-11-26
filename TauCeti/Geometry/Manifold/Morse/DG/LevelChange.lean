/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.RepresentingChainSystem
public import TauCeti.Geometry.Manifold.Morse.DG.TwistedComplex
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.LevelChange

/-!
# The Barraud–Cornea cocycle does not depend on the levels

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`. The compactified trajectory spaces `L_c(x, y)` between critical points
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`) record broken trajectories by their
points on the levels of a family `c`, dense between any two critical values and avoiding the
critical values. The Barraud–Cornea cocycle
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`) and the DG Morse complex
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplex`) are built from a twisting chain system on these
spaces. This file shows that the choice of `c` does not matter.

For another such family `c'`, recording each broken trajectory on the levels of `c'` is a
homeomorphism `L_c(x, y) ≃ₜ L_{c'}(x, y)` compatible with breaking, with the boundaries and with
the Moore paths of broken trajectories
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceLevelHomeomorph`). Pushing a twisting
chain system forward along it (`TauCeti.TwistingChainSystem.map`) gives the **change of levels**
of the chain system (`TauCeti.IsAdaptedPseudoGradient.morseLevelChangeChainSystem`), and:

* the change of levels from `c'` back to `c` undoes it
  (`TauCeti.IsAdaptedPseudoGradient.morseLevelChangeChainSystem_morseLevelChangeChainSystem`), so
  it is a bijection between the twisting chain systems for the two families of levels;
* it carries a representing chain system of classes `μ` relative to the boundaries to a
  representing chain system of the images of `μ`
  (`TauCeti.IsAdaptedPseudoGradient.IsRepresenting.morseLevelChangeChainSystem`), such as the
  fundamental classes rel boundary of the trajectory spaces;
* the Barraud–Cornea cocycle of the change of levels is the Barraud–Cornea cocycle of the original
  system (`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle_morseLevelChangeChainSystem`), since
  the Moore paths of broken trajectories do not depend on the levels on which they are recorded;
* hence so is the DG Morse complex, with coefficients in any DG local system
  (`TauCeti.IsAdaptedPseudoGradient.dgMorseComplex_morseLevelChangeChainSystem`).

So the Barraud–Cornea cocycles, and the DG Morse complexes, obtained from all the twisting chain
systems (or all the representing chain systems) for the levels of `c` and of `c'` are the same.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.morseLevelChangeChainSystem`: the change of levels of a twisting
  chain system on the trajectory spaces.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.morseLevelChangeChainSystem_morseLevelChangeChainSystem`: the
  change of levels is invertible.
* `TauCeti.IsAdaptedPseudoGradient.IsRepresenting.morseLevelChangeChainSystem`: it preserves
  representing chain systems.
* `TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle_morseLevelChangeChainSystem`: it does not
  change the Barraud–Cornea cocycle.
* `TauCeti.IsAdaptedPseudoGradient.dgMorseComplex_morseLevelChangeChainSystem`: it does not change
  the DG Morse complex.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5 and 6.
-/

public section

noncomputable section

open CategoryTheory Set
open scoped ContDiff Manifold

universe u v

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι ι' : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ} {c' : ι' → ℝ}
  (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  (hdense' : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c'))
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  (hc' : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c' i ≠ f x)
  {R : Type*} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  {ind : criticalPoints 𝓘(ℝ, E) f → ℤ}

/-! ### The change of levels of a twisting chain system -/

/-- **The change of levels of a twisting chain system** on the trajectory spaces for the levels of
`c`: its push-forward along the homeomorphisms `L_c(x, y) ≃ₜ L_{c'}(x, y)` recording each broken
trajectory on the levels of `c'`, a twisting chain system on the trajectory spaces for the levels
of `c'`. -/
def morseLevelChangeChainSystem
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R) :
    TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc') R :=
  S.map (fun x y ↦ hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc' x y)
    fun x z y u v ↦
      hX.morseBrokenTrajectorySpaceLevelHomeomorph_comp hf hdense hdense' hc hc' x z y (u, v)

/-- The chains of the change of levels are the push-forwards of the chains along the changes of
levels of the trajectory spaces. -/
@[simp]
theorem morseLevelChangeChainSystem_chain
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    (hX.morseLevelChangeChainSystem hf hdense hdense' hc hc' S).chain x y =
      cubicalChainSumMap R (hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc'
        x y) (S.chain x y) :=
  S.map_chain _ x y

/-- **The change of levels is invertible**: changing the levels from `c` to `c'` and then back from
`c'` to `c` gives back the twisting chain system. -/
@[simp]
theorem morseLevelChangeChainSystem_morseLevelChangeChainSystem
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R) :
    hX.morseLevelChangeChainSystem hf hdense' hdense hc' hc
        (hX.morseLevelChangeChainSystem hf hdense hdense' hc hc' S) = S := by
  refine TwistingChainSystem.ext fun x y ↦ ?_
  rw [morseLevelChangeChainSystem_chain, morseLevelChangeChainSystem_chain, ← LinearMap.comp_apply,
    ← cubicalChainSumMap_comp, ← morseBrokenTrajectorySpaceLevelHomeomorph_symm,
    Homeomorph.symm_comp_toContinuousMap, cubicalChainSumMap_id, LinearMap.id_apply]

/-! ### Representing chain systems -/

/-- **The change of levels preserves representing chain systems.** If `S` represents classes `μ`
of the trajectory spaces for the levels of `c` relative to their boundaries, such as their
fundamental classes rel boundary, its change of levels represents the images of the classes `μ`
under the changes of levels of the trajectory spaces, which carry the boundaries onto the
boundaries. -/
theorem IsRepresenting.morseLevelChangeChainSystem {ι₁ ι₂ : Type v} {c₁ : ι₁ → ℝ} {c₂ : ι₂ → ℝ}
    (hdense₁ : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c₁))
    (hdense₂ : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c₂))
    (hc₁ : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c₁ i ≠ f x)
    (hc₂ : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c₂ i ≠ f x) {k : Type (max u v)} [CommRing k]
    {S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc₁) k}
    {μ : ∀ x y : criticalPoints 𝓘(ℝ, E) f, ((TopPair.ofSubset
      (X := TopCat.of (hX.morseBrokenTrajectorySpace c₁ x y))
      (hX.morseBrokenTrajectorySpaceBoundary c₁ x y)).cubicalChainComplex k).homology
        (ind x - ind y - 1).toNat}
    (hS : S.IsRepresenting (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦
      TopCat.of (hX.morseBrokenTrajectorySpace c₁ x y))
      (fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c₁ x y) μ) :
    (hX.morseLevelChangeChainSystem hf hdense₁ hdense₂ hc₁ hc₂ S).IsRepresenting
      (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦ TopCat.of (hX.morseBrokenTrajectorySpace c₂ x y))
      (fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c₂ x y) fun x y ↦
        (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k (TopPair.ofSubsetMap
          (TopCat.ofHom
            (hX.morseBrokenTrajectorySpaceLevelHomeomorph hf hdense₁ hdense₂ hc₁ hc₂ x y))
          fun _ ↦ (hX.morseBrokenTrajectorySpaceLevelHomeomorph_mem_boundary_iff hf hdense₁ hdense₂
            hc₁ hc₂).2)) (ind x - ind y - 1).toNat).hom (μ x y) :=
  hS.map _ fun _ _ _ ↦
    (hX.morseBrokenTrajectorySpaceLevelHomeomorph_mem_boundary_iff hf hdense₁ hdense₂ hc₁ hc₂).2

/-! ### The Barraud–Cornea cocycle and the DG Morse complex -/

variable {Y : Type*} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)

/-- **The Barraud–Cornea cocycle does not depend on the levels**: the Barraud–Cornea cocycle of the
change of levels of a twisting chain system is the Barraud–Cornea cocycle of the system. A broken
trajectory and its re-recording on other levels have the same Moore path. -/
@[simp]
theorem barraudCorneaCocycle_morseLevelChangeChainSystem
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R) :
    hX.barraudCorneaCocycle hf hdense' hθ hc'
        (hX.morseLevelChangeChainSystem hf hdense hdense' hc hc' S) =
      hX.barraudCorneaCocycle hf hdense hθ hc S := by
  refine TwistingCocycle.ext fun x y ↦ ?_
  rw [barraudCorneaCocycle_m, barraudCorneaCocycle_m, morseLevelChangeChainSystem_chain,
    ← LinearMap.comp_apply, ← cubicalChainSumMap_comp]
  congr 2
  refine ContinuousMap.ext fun w ↦ ?_
  apply MooreLoopSpace.ext
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_ofClass, toMoorePath_morseLoopEvaluation]
  exact congrArg (MoorePath.map θ)
    (hX.morseLevelPath_morseBrokenTrajectorySpaceLevelHomeomorph hf hdense hdense' hc hc' x y w)

/-- **The DG Morse complex does not depend on the levels**: the DG Morse complex of the change of
levels of a twisting chain system, graded by the Morse index, is the DG Morse complex of the
system, with coefficients in every DG local system. -/
@[simp]
theorem dgMorseComplex_morseLevelChangeChainSystem
    (S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
      (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R)
    (𝓕 : DGLocalSystem Y y₀ R) :
    hX.dgMorseComplex hf hdense' hθ hc'
        (hX.morseLevelChangeChainSystem hf hdense hdense' hc hc' S) 𝓕 =
      hX.dgMorseComplex hf hdense hθ hc S 𝓕 := by
  rw [dgMorseComplex_def, dgMorseComplex_def, barraudCorneaCocycle_morseLevelChangeChainSystem]

end IsAdaptedPseudoGradient

end TauCeti
