/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.RepresentingChainSystem
public import TauCeti.Geometry.Manifold.Morse.DG.TwistedComplex
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Levels

/-!
# The DG Morse complex does not depend on the levels

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`. Its trajectory spaces `L(x, y)` are realized as records of broken trajectories
on a family of levels `c`, dense between any two critical values and avoiding the critical values
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpace`), and the Barraud–Cornea cocycle
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`) and the DG Morse complex
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplex`) are built from a twisting chain system on these
spaces. This file shows that the choice of the levels does not matter for the cocycle and the
complex: the change of levels is a bijection of the twisting chain systems which keeps both.

For another such family `c'`, the change of levels
(`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySpaceHomeomorph`) is a homeomorphism of the
trajectory spaces which commutes with their composition maps, so it carries every twisting chain
system `S` on the levels of `c` to one on the levels of `c'`
(`TauCeti.IsAdaptedPseudoGradient.chainSystemChangeLevels`, a push-forward
`TauCeti.TwistingChainSystem.map`), and carrying it back recovers `S`
(`TauCeti.IsAdaptedPseudoGradient.chainSystemChangeLevels_chainSystemChangeLevels`). The change of
levels keeps the Moore path of every broken trajectory, so it keeps the evaluation into Moore loops
(`TauCeti.IsAdaptedPseudoGradient.morseLoopEvaluation_morseBrokenTrajectorySpaceHomeomorph`).
Hence the two chain systems have the same Barraud–Cornea cocycle
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle_chainSystemChangeLevels`) and the same DG
Morse complex (`TauCeti.IsAdaptedPseudoGradient.dgMorseComplex_chainSystemChangeLevels`), with
coefficients in every DG local system. The change of levels also carries a representing chain
system of classes `μ` relative to the boundaries, such as the fundamental classes rel boundary of
the trajectory spaces, to a representing chain system of the images of `μ`
(`TauCeti.TwistingChainSystem.IsRepresenting.chainSystemChangeLevels`).

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.chainSystemChangeLevels`: the twisting chain system on other
  levels induced by a twisting chain system on the trajectory spaces.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseLoopEvaluation_morseBrokenTrajectorySpaceHomeomorph`: the evaluation into Moore loops does
  not depend on the levels.
* `chainSystemChangeLevels_chainSystemChangeLevels`: changing the levels of a twisting chain system
  and changing them back recovers it.
* `TauCeti.TwistingChainSystem.IsRepresenting.chainSystemChangeLevels`: the change of levels
  preserves representing chain systems.
* `barraudCorneaCocycle_chainSystemChangeLevels`: a twisting chain system and the one it induces on
  other levels have the same Barraud–Cornea cocycle.
* `dgMorseComplex_chainSystemChangeLevels`: they have the same DG Morse complex.

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

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ} {c' : ι' → ℝ} (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  (hdense' : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c'))
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  (hc' : ∀ i' (x : criticalPoints 𝓘(ℝ, E) f), c' i' ≠ f x)
  {Y : Type*} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)

/-- **The evaluation into Moore loops does not depend on the levels**: a broken trajectory between
two critical points has the same loop whether it is recorded on the levels of `c` or of `c'`. -/
@[simp]
theorem morseLoopEvaluation_morseBrokenTrajectorySpaceHomeomorph
    (x y : criticalPoints 𝓘(ℝ, E) f) (w : hX.morseBrokenTrajectorySpace c x y) :
    hX.morseLoopEvaluation hf hdense' hθ x y (inclusion (morseBrokenTrajectorySpace_subset _ _)
        (hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' x y w)) =
      hX.morseLoopEvaluation hf hdense hθ x y
        (inclusion (morseBrokenTrajectorySpace_subset _ _) w) :=
  MooreLoopSpace.ext <| by
    rw [toMoorePath_morseLoopEvaluation, toMoorePath_morseLoopEvaluation,
      morseLevelPath_morseBrokenTrajectorySpaceHomeomorph]

variable {R : Type*} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  {ind : criticalPoints 𝓘(ℝ, E) f → ℤ}

variable (ind) in
/-- **A twisting chain system on other levels.** A twisting chain system on the trajectory spaces on
the levels of `c` induces one on the levels of `c'`: its push-forward along the change of levels,
which commutes with the composition maps. -/
noncomputable def chainSystemChangeLevels
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R) :
    TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc') R :=
  S.map (fun x y ↦ hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' x y)
    (hX.morseBrokenTrajectorySpaceHomeomorph_morseBrokenTrajectorySpaceComp hf hdense hdense' hc
      hc')

/-- The chains of the twisting chain system on other levels are the push-forwards of the chains
along the change of levels. -/
@[simp]
theorem chainSystemChangeLevels_chain
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    (hX.chainSystemChangeLevels hf hdense hdense' hc hc' ind S).chain x y =
      cubicalChainSumMap R (hX.morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' x y)
        (S.chain x y) :=
  TwistingChainSystem.map_chain ..

/-- **Changing the levels of a twisting chain system and changing them back recovers it.** So the
change of levels is a bijection between the twisting chain systems on the trajectory spaces on the
levels of `c` and on the levels of `c'`. -/
@[simp]
theorem chainSystemChangeLevels_chainSystemChangeLevels
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R) :
    hX.chainSystemChangeLevels hf hdense' hdense hc' hc ind
        (hX.chainSystemChangeLevels hf hdense hdense' hc hc' ind S) = S := by
  rw [chainSystemChangeLevels, chainSystemChangeLevels, TwistingChainSystem.map_map]
  -- The change of levels back is the inverse of the change of levels.
  simp_rw [← hX.morseBrokenTrajectorySpaceHomeomorph_symm hf hdense hdense' hc hc',
    Homeomorph.symm_comp_toContinuousMap]
  exact TwistingChainSystem.map_id S

/-- **The change of levels preserves representing chain systems.** If `S` represents classes `μ`
of the trajectory spaces on the levels of `c₁` relative to their boundaries, such as their
fundamental classes rel boundary, the twisting chain system it induces on the levels of `c₂`
represents the images of the classes `μ` under the changes of levels of the trajectory spaces,
which carry the boundaries onto the boundaries. -/
theorem _root_.TauCeti.TwistingChainSystem.IsRepresenting.chainSystemChangeLevels
    {ι₁ ι₂ : Type v} {c₁ : ι₁ → ℝ} {c₂ : ι₂ → ℝ}
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
    (hX.chainSystemChangeLevels hf hdense₁ hdense₂ hc₁ hc₂ ind S).IsRepresenting
      (M := fun x y : criticalPoints 𝓘(ℝ, E) f ↦ TopCat.of (hX.morseBrokenTrajectorySpace c₂ x y))
      (fun x y ↦ hX.morseBrokenTrajectorySpaceBoundary c₂ x y) fun x y ↦
        (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k (TopPair.ofSubsetMap
          (TopCat.ofHom (hX.morseBrokenTrajectorySpaceHomeomorph hf hdense₁ hdense₂ hc₁ hc₂ x y))
          fun w ↦
            (hX.morseBrokenTrajectorySpaceHomeomorph_mem_morseBrokenTrajectorySpaceBoundary_iff
              hf hdense₁ hdense₂ hc₁ hc₂ w).2)) (ind x - ind y - 1).toNat).hom (μ x y) :=
  hS.map _ fun _ _ w ↦
    (hX.morseBrokenTrajectorySpaceHomeomorph_mem_morseBrokenTrajectorySpaceBoundary_iff hf
      hdense₁ hdense₂ hc₁ hc₂ w).2

/-- **The Barraud–Cornea cocycle does not depend on the levels**: a twisting chain system on the
trajectory spaces on the levels of `c` and the one it induces on the levels of `c'` have the same
Barraud–Cornea cocycle. -/
@[simp]
theorem barraudCorneaCocycle_chainSystemChangeLevels
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R) :
    hX.barraudCorneaCocycle hf hdense' hθ hc'
        (hX.chainSystemChangeLevels hf hdense hdense' hc hc' ind S) =
      hX.barraudCorneaCocycle hf hdense hθ hc S :=
  TwistingCocycle.ext fun x y ↦ by
    rw [barraudCorneaCocycle_m, barraudCorneaCocycle_m, chainSystemChangeLevels_chain,
      ← LinearMap.comp_apply, ← cubicalChainSumMap_comp]
    exact congrArg (cubicalChainSumMap R · (S.chain x y)) <| ContinuousMap.ext fun w ↦
      hX.morseLoopEvaluation_morseBrokenTrajectorySpaceHomeomorph hf hdense hdense' hc hc' hθ x y w

/-- **The DG Morse complex does not depend on the levels**: a twisting chain system on the
trajectory spaces on the levels of `c`, graded by the Morse index, and the one it induces on the
levels of `c'` have the same DG Morse complex, with coefficients in every DG local system. -/
@[simp]
theorem dgMorseComplex_chainSystemChangeLevels
    (S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
      (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R)
    (𝓕 : DGLocalSystem Y y₀ R) :
    hX.dgMorseComplex hf hdense' hθ hc' (hX.chainSystemChangeLevels hf hdense hdense' hc hc' _ S)
        𝓕 =
      hX.dgMorseComplex hf hdense hθ hc S 𝓕 := by
  rw [dgMorseComplex_def, dgMorseComplex_def, barraudCorneaCocycle_chainSystemChangeLevels]

end IsAdaptedPseudoGradient

end TauCeti
