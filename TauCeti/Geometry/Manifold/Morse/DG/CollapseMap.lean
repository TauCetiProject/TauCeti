/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.ContinuationQuasiIso
public import TauCeti.Geometry.Manifold.Morse.DG.TwistedComplex

/-!
# The DG Morse complex does not depend on the collapse map

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`, and let `S` be a twisting chain system on the trajectory spaces of `f`. The
Barraud–Cornea cocycle (`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`) evaluates the
chains of `S` into the Moore loops of a space `Y` at `y₀` through a map `θ : M → Y` sending every
critical point to `y₀`. In the construction of Barraud and Cornea, `θ` is the collapse of an
embedded tree through the critical points followed by a homotopy inverse of the collapse, so it
depends on the choice of the tree. This file shows that the DG Morse homology does not.

Let `θ₀` and `θ₁` be two such maps and `H` a homotopy from `θ₀` to `θ₁`; it need not fix the
critical points. A marked homotopy `T` of `S` (`TauCeti.TwistingChainSystem.MarkedHomotopy`),
which always exists, gives the continuation cocycle
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCollapseCocycle`) from the Barraud–Cornea cocycle
for `θ₀` to the one for `θ₁`: its diagonal entries are the point chains of the tracks
`t ↦ H (t, x)` of the homotopy at the critical points, loops at `y₀`. Its continuation map
(`TauCeti.IsAdaptedPseudoGradient.dgMorseComplexCollapseHom`) is a morphism of DG Morse complexes,
for every DG local system `𝓕` on `(Y, y₀)`.

Under the Morse–Smale condition this morphism is a quasi-isomorphism
(`TauCeti.IsAdaptedPseudoGradient.quasiIso_dgMorseComplexCollapseHom`). The trajectory spaces
between critical points of equal index are empty, so the cocycle vanishes between distinct critical
points of equal index, and its diagonal entries are the point chains of the tracks alone. A track
of positive length is not a unit of the chain algebra `C_*(Ω_{y₀} Y)`, whose unit is the constant
loop of length zero, so the cocycle need not be invertible as a matrix, and the continuation map
need not be an isomorphism. But each track is a unit of the group ring
`H₀(Ω_{y₀} Y) = R[π₁(Y, y₀)]`, which is enough
(`TauCeti.TwistingChainSystem.MarkedHomotopy.quasiIso_continuationHom_mooreHomotopyCocycle`). So
the DG Morse homology for `θ₀` and for `θ₁` is identified by a specified isomorphism
(`TauCeti.IsAdaptedPseudoGradient.dgMorseHomologyCollapseIso`), and homotopic collapse maps give
quasi-isomorphic DG Morse complexes
(`TauCeti.IsAdaptedPseudoGradient.exists_quasiIso_dgMorseComplex_of_homotopic`).

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.barraudCorneaCollapseCocycle`: the continuation cocycle between
  the Barraud–Cornea cocycles of two collapse maps, given by a homotopy between them.
* `TauCeti.IsAdaptedPseudoGradient.dgMorseComplexCollapseHom`: its continuation map of DG Morse
  complexes.
* `TauCeti.IsAdaptedPseudoGradient.dgMorseHomologyCollapseIso`: the induced isomorphism of DG
  Morse homology, under the Morse–Smale condition.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.quasiIso_dgMorseComplexCollapseHom`: under the Morse–Smale
  condition, the continuation map of a homotopy of collapse maps is a quasi-isomorphism.
* `TauCeti.IsAdaptedPseudoGradient.exists_quasiIso_dgMorseComplex_of_homotopic`: homotopic collapse
  maps give quasi-isomorphic DG Morse complexes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 5 and 6.
* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. 166 (2007), 657–722, §2.
-/

public section

noncomputable section

open CategoryTheory Set
open scoped ContDiff Manifold

namespace TauCeti

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ} (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  {Y : Type u} [TopologicalSpace Y] {θ₀ θ₁ : C(M, Y)} {y₀ : Y}
  (hθ₀ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ₀ x = y₀)
  (hθ₁ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ₁ x = y₀)
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x) (H : θ₀.Homotopy θ₁)

/-- The Moore paths of the broken trajectories have additive lengths along the composition maps of
the trajectory spaces, in the form of the hypothesis of `TauCeti.TwistingChainSystem.MarkedHomotopy`
for the evaluation of the trajectory spaces into Moore paths. -/
theorem length_morseLevelPath_morseBrokenTrajectorySpaceComp (x z y : criticalPoints 𝓘(ℝ, E) f)
    (u : hX.morseBrokenTrajectorySpace c x z) (v : hX.morseBrokenTrajectorySpace c z y) :
    ((hX.morseLevelPath hf (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))).comp
        (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _))
          (hX.morseBrokenTrajectorySpaceComp hc x z y (u, v))).length =
      ((hX.morseLevelPath hf
          (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x z))).comp
            (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _)) u).length +
        ((hX.morseLevelPath hf
          (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense z y))).comp
            (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _)) v).length :=
  length_eq_add_of_eq_trans (c := ((↑) : criticalPoints 𝓘(ℝ, E) f → M))
    (e := fun x y ↦ (hX.morseLevelPath hf
      (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))).comp
        (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _)))
    (fun _ _ _ ↦ hX.source_morseLevelPath ..) (fun _ _ _ ↦ hX.target_morseLevelPath ..)
    (hX.morseLevelPath_morseBrokenTrajectorySpaceComp hf hdense hc) x z y u v

variable {R : Type u} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  [DecidableEq (criticalPoints 𝓘(ℝ, E) f)]

/-! ### The continuation cocycle of a homotopy of collapse maps -/

section Cocycle

variable {ind : criticalPoints 𝓘(ℝ, E) f → ℤ}
  {S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R}

/-- **The continuation cocycle of a homotopy of collapse maps** between the Barraud–Cornea cocycles
of `S` for `θ₀` and for `θ₁`, given by a homotopy `H` from `θ₀` to `θ₁` and a marked homotopy `T`
of `S`: the point chains of the tracks of `H` at the critical points on the diagonal, plus the
push-forwards of the chains of `T` along the evaluation of the marked trajectory spaces, which
switches from `θ₀` to `θ₁` at the mark through `H`
(`TauCeti.TwistingChainSystem.MarkedHomotopy.mooreHomotopyCocycle`). -/
def barraudCorneaCollapseCocycle
    (T : S.MarkedHomotopy (hX.length_morseLevelPath_morseBrokenTrajectorySpaceComp hf hdense hc)) :
    ContinuationCocycle (hX.barraudCorneaCocycle hf hdense hθ₀ hc S)
      (hX.barraudCorneaCocycle hf hdense hθ₁ hc S) :=
  TwistingChainSystem.MarkedHomotopy.mooreHomotopyCocycle (S := S)
    (c := ((↑) : criticalPoints 𝓘(ℝ, E) f → M))
    (e := fun x y ↦ (hX.morseLevelPath hf
      (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))).comp
        (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _)))
    (fun _ _ _ ↦ hX.source_morseLevelPath ..) (fun _ _ _ ↦ hX.target_morseLevelPath ..)
    (hX.morseLevelPath_morseBrokenTrajectorySpaceComp hf hdense hc) hθ₀ hθ₁ H T

/-- The entries of the continuation cocycle of a homotopy of collapse maps: the point chain of the
track of `H` at `x` on the diagonal, plus the push-forward of the chain of the marked homotopy
along the evaluation of the marked trajectory space into Moore loops. -/
@[simp]
theorem barraudCorneaCollapseCocycle_ν
    (T : S.MarkedHomotopy (hX.length_morseLevelPath_morseBrokenTrajectorySpaceComp hf hdense hc))
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    (hX.barraudCorneaCollapseCocycle hf hdense hθ₀ hθ₁ hc H T).ν x y =
      Matrix.diagonal (fun x ↦ cubicalChainPoint _ R (H.mooreTrackLoop (hθ₀ x) (hθ₁ x))) x y +
        cubicalChainSumMap R (markedLoopEvaluation (c := ((↑) : criticalPoints 𝓘(ℝ, E) f → M))
          (e := fun x y ↦ (hX.morseLevelPath hf
            (subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y))).comp
              (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _)))
          (fun _ _ _ ↦ hX.source_morseLevelPath ..) (fun _ _ _ ↦ hX.target_morseLevelPath ..)
          hθ₀ hθ₁ H x y) (T.chain x y) :=
  TwistingChainSystem.MarkedHomotopy.mooreHomotopyCocycle_ν ..

end Cocycle

/-! ### Independence of the collapse map -/

section Independence

variable {S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
  (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R}

/-- **The continuation map of a homotopy of collapse maps** from the DG Morse complex of `S` for
`θ₀` to the one for `θ₁`, with coefficients in a DG local system `𝓕`: the continuation map of
`barraudCorneaCollapseCocycle`. -/
def dgMorseComplexCollapseHom
    (T : S.MarkedHomotopy (hX.length_morseLevelPath_morseBrokenTrajectorySpaceComp hf hdense hc))
    (𝓕 : DGLocalSystem Y y₀ R) :
    hX.dgMorseComplex hf hdense hθ₀ hc S 𝓕 ⟶ hX.dgMorseComplex hf hdense hθ₁ hc S 𝓕 :=
  (hX.barraudCorneaCollapseCocycle hf hdense hθ₀ hθ₁ hc H T).continuationHom 𝓕.isDGRightModule

/-- **Changing the collapse map gives a quasi-isomorphism of DG Morse complexes**, under the
Morse–Smale condition: the continuation map of a homotopy `H` between two collapse maps is a
quasi-isomorphism, for every DG local system. The diagonal entries of its cocycle are the point
chains of the tracks of `H`, units of `R[π₁(Y, y₀)]`, and the trajectory spaces between critical
points of equal index are empty. -/
theorem quasiIso_dgMorseComplexCollapseHom (hMS : hX.IsMorseSmale)
    (T : S.MarkedHomotopy (hX.length_morseLevelPath_morseBrokenTrajectorySpaceComp hf hdense hc))
    (𝓕 : DGLocalSystem Y y₀ R) :
    QuasiIso (hX.dgMorseComplexCollapseHom hf hdense hθ₀ hθ₁ hc H T 𝓕) :=
  TwistingChainSystem.MarkedHomotopy.quasiIso_continuationHom_mooreHomotopyCocycle hθ₀ hθ₁ H
    (fun x y hxy ↦ by
      rw [hMS.morseBrokenTrajectorySpace_eq_empty_of_le hf (by exact_mod_cast hxy.le)]
      infer_instance) T 𝓕.isDGRightModule

/-- **The isomorphism of DG Morse homology given by a homotopy of collapse maps**, under the
Morse–Smale condition: the map induced in each degree by the quasi-isomorphism
`dgMorseComplexCollapseHom`. So the DG Morse homology does not depend on the collapse map, up to an
isomorphism specified by the homotopy and the marked homotopy. -/
def dgMorseHomologyCollapseIso (hMS : hX.IsMorseSmale)
    (T : S.MarkedHomotopy (hX.length_morseLevelPath_morseBrokenTrajectorySpaceComp hf hdense hc))
    (𝓕 : DGLocalSystem Y y₀ R) (n : ℤ) :
    (hX.dgMorseComplex hf hdense hθ₀ hc S 𝓕).homology n ≅
      (hX.dgMorseComplex hf hdense hθ₁ hc S 𝓕).homology n :=
  have := hX.quasiIso_dgMorseComplexCollapseHom hf hdense hθ₀ hθ₁ hc H hMS T 𝓕
  asIso (HomologicalComplex.homologyMap (hX.dgMorseComplexCollapseHom hf hdense hθ₀ hθ₁ hc H T 𝓕) n)

/-- The isomorphism of DG Morse homology given by a homotopy of collapse maps is the map induced
by the continuation map. -/
@[simp]
theorem dgMorseHomologyCollapseIso_hom (hMS : hX.IsMorseSmale)
    (T : S.MarkedHomotopy (hX.length_morseLevelPath_morseBrokenTrajectorySpaceComp hf hdense hc))
    (𝓕 : DGLocalSystem Y y₀ R) (n : ℤ) :
    (hX.dgMorseHomologyCollapseIso hf hdense hθ₀ hθ₁ hc H hMS T 𝓕 n).hom =
      HomologicalComplex.homologyMap (hX.dgMorseComplexCollapseHom hf hdense hθ₀ hθ₁ hc H T 𝓕) n :=
  (rfl)

omit [DecidableEq (criticalPoints 𝓘(ℝ, E) f)] in
/-- **Homotopic collapse maps give quasi-isomorphic DG Morse complexes**, under the Morse–Smale
condition: if two maps `θ₀`, `θ₁ : M → Y` sending all critical points to `y₀` are homotopic, by a
homotopy which need not fix the critical points, then some morphism from the DG Morse complex of `S`
for `θ₀` to the one for `θ₁` is a quasi-isomorphism, for every DG local system. Marked homotopies
of `S` exist (`TauCeti.TwistingChainSystem.nonempty_markedHomotopy`), since the composition maps of
the trajectory spaces are associative. -/
theorem exists_quasiIso_dgMorseComplex_of_homotopic (hMS : hX.IsMorseSmale)
    (hθ : θ₀.Homotopic θ₁) (𝓕 : DGLocalSystem Y y₀ R) :
    ∃ φ : hX.dgMorseComplex hf hdense hθ₀ hc S 𝓕 ⟶ hX.dgMorseComplex hf hdense hθ₁ hc S 𝓕,
      QuasiIso φ :=
  have ⟨H⟩ := hθ
  have ⟨T⟩ := TwistingChainSystem.nonempty_markedHomotopy
    (hX.length_morseLevelPath_morseBrokenTrajectorySpaceComp hf hdense hc) S
    (hX.morseBrokenTrajectorySpaceComp_assoc hc)
  by classical exact ⟨_, hX.quasiIso_dgMorseComplexCollapseHom hf hdense hθ₀ hθ₁ hc H hMS T 𝓕⟩

end Independence

end IsAdaptedPseudoGradient

end TauCeti
