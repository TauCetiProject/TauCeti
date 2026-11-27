/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.Basic
public import TauCeti.Geometry.Manifold.Morse.Boundary.LocalCoefficient
public import TauCeti.Geometry.Manifold.Morse.DG.DegreeZero
public import TauCeti.Geometry.Manifold.Morse.DG.TwistedComplex
public import TauCeti.Geometry.Manifold.Morse.Stable.Broken.Slice

/-!
# The DG Morse complex with coefficients in a classical local system

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X` satisfying the Morse–Smale condition, and let `S` be a twisting chain system
on the spaces `L(x, y)` of broken trajectories, recorded on levels `c`. Its Barraud–Cornea cocycle
(`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`) evaluates the chains of `S` into the chains
on the Moore loops of a space `Y` at `y₀`, through a map `θ : M → Y` sending every critical point
to `y₀`. A classical local system `L` on `Y` is a DG local system concentrated in degree zero
(`TauCeti.classicalDGLocalSystem`), on which a chain of loops acts through its degree-zero part
(`TauCeti.classicalAction`). This file identifies each entry `m x y` of the cocycle, acting on
`L(y₀)`, with the component from `x` to `y` of the Morse boundary with coefficients in the
pullback `θ^* L` (`TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundaryMap`), up to the
identifications of the fibres `L(y₀) ≅ L(θ x)` along `θ x = y₀`.

* **Loops of records are the images of the trajectories.** Mapped by `θ`, the loop of the record of
  a trajectory has the image of the path class of its trajectory as class
  (`IsAdaptedPseudoGradient.mk_toPath_morseLoopEvaluation`), since the Moore path of the record
  is homotopic to the path traced by the trajectory
  (`IsAdaptedPseudoGradient.homotopic_toPath_morseLevelPath`). In index difference one this is
  read through the bijection of the trajectory space with the middle-level slice
  (`IsAdaptedPseudoGradient.IsMorseSmale.morseBrokenTrajectorySpaceEquivSlice`), on which the
  classical Morse boundary is defined.
* **The degree-zero entries act by transport.** The entry of the Barraud–Cornea cocycle at
  `(x, y)` acts on `L(y₀)` as the sum of the transports along the images under `θ` of the
  trajectories from `x` to `y`, weighted by their coefficients in the `0`-chain of `S`
  (`IsAdaptedPseudoGradient.IsMorseSmale.classicalAction_barraudCorneaCocycle_m`).
* **Classical recovery, entry by entry.** If `S` is graded by the Morse index and gives each
  trajectory of index difference one its sign, the entry at `(x, y)` acts as the component from `x`
  to `y` of the Morse boundary with coefficients in `θ^* L`, read through the identifications
  `L(y₀) ≅ L(θ x)`
  (`IsMorseSmale.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap`).
  Entries between critical points whose indices do not differ by one have nonzero degree and act by
  zero. In characteristic two every sign is `1`, so the hypothesis is that `S` gives every
  trajectory the coefficient `1`
  (`IsMorseSmale.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap_of_charTwo`).

* **Classical recovery of the complex.** The twisted differential with coefficients concentrated
  in degree zero is the action of the entries of the cocycle
  (`TauCeti.twistedDifferential_trivialGrading_apply`). So under the same hypotheses, transporting
  a family of elements of `L(y₀)` indexed by the critical points along `L(y₀) ≅ L(θ x)` turns the
  twisted differential into the Morse boundary with coefficients in `θ^* L`
  (`IsMorseSmale.transport_twistedDifferential_eq_twistedMorseBoundary`). The twisted
  differential squares to zero by the twisting equation, hence so does the Morse boundary
  (`IsMorseSmale.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero`), and the transports
  assemble into an isomorphism of the DG Morse complex of `S` with coefficients in `L` with the
  Morse complex of `f` with coefficients in `θ^* L`
  (`IsMorseSmale.dgMorseComplexClassicalIso`, with degreewise identification
  `IsMorseSmale.dgMorseComplexClassicalXEquiv`). Both are cochain complexes, the critical points
  of index `k` sitting in degree `-k`.

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.dgMorseComplexClassicalIso`: the isomorphism of the DG Morse complex with
  coefficients in a classical local system `L` with the Morse complex with coefficients in `θ^* L`.
* `IsMorseSmale.dgMorseComplexClassicalXEquiv`: its degree-`n` part, the transport of families.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `mk_toPath_morseLoopEvaluation`: the loop of the record of a trajectory has as class the image of
  the class of the trajectory.
* `IsMorseSmale.mk_toPath_morseLoopEvaluation_eq_trajectoryPathClass`: the same, through the
  middle-level slice.
* `IsMorseSmale.classicalAction_barraudCorneaCocycle_m`: the entries of index difference one act on
  a classical local system by the weighted transports along the trajectories.
* `IsMorseSmale.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap`,
  `IsMorseSmale.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap_of_charTwo`:
  classical recovery, entry by entry, over any ring for the oriented chain system and in
  characteristic two.
* `IsMorseSmale.transport_twistedDifferential_eq_twistedMorseBoundary`: the twisted differential
  with classical coefficients is the Morse boundary with coefficients in the pullback.
* `IsMorseSmale.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero`: hence the Morse boundary
  with local coefficients squares to zero.
* `IsMorseSmale.dgMorseComplexClassicalIso`: classical recovery, as an isomorphism of the DG Morse
  complex with classical coefficients and the Morse complex with local coefficients.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3 and 5.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.
-/

public section

open MulOpposite Set
open scoped ContDiff Manifold

universe u w

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {c : ι → ℝ}
  {Y : Type*} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}

/-- **The loop of the record of a trajectory is the image of the trajectory.** Let `w` record the
trajectory through `z` from the critical point `x` to the critical point `y ≠ x`. Its loop at `y₀`,
the Moore path of `w` mapped by `θ` (`TauCeti.IsAdaptedPseudoGradient.morseLoopEvaluation`), has as
homotopy class the image under `θ` of the class of the path traced by the trajectory. -/
theorem mk_toPath_morseLoopEvaluation (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀) {x y : criticalPoints 𝓘(ℝ, E) f}
    (hxy : (x : M) ≠ y)
    (w : hX.morseBrokenTrajectoryRecords x y ((c ⁻¹' Ioo (f y) (f x)).domRestrict c)) {z : M}
    (hz : z ∈ hX.flow.unstableSet x ∩ hX.flow.stableSet y)
    (hw : ∀ i, ∃ t, hX.flow t z = w.val i) :
    Path.Homotopic.Quotient.mk (hX.morseLoopEvaluation hf hdense hθ x y w).toPath =
      ((Path.Homotopic.Quotient.mk (Flow.connectingPath hz.1 hz.2)).map θ).cast (hθ x).symm
        (hθ y).symm := by
  have hdense' := subset_closure_range_domRestrict_preimage isOpen_Ioo (hdense x y)
  have hloop : (hX.morseLoopEvaluation hf hdense hθ x y w).toPath =
      ((((hX.morseLevelPath hf hdense' w).toPath.cast (hX.source_morseLevelPath hf hdense' w).symm
        (hX.target_morseLevelPath hf hdense' w).symm).map θ.continuous).cast (hθ x).symm
          (hθ y).symm) := by
    ext s
    simp [MooreLoopSpace.toPath_apply]
  rw [hloop, Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_map,
    Path.Homotopic.Quotient.eq.2 (hX.homotopic_toPath_morseLevelPath hf hdense'
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) hxy hz w hw)]

namespace IsMorseSmale

variable (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {x y : criticalPoints 𝓘(ℝ, E) f}
  (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1)

/-- **The loop of a trajectory of index difference one is the image of the trajectory.** Under the
Morse–Smale condition, for `ind x = ind y + 1`, the loop at `y₀` of a point `w` of the trajectory
space from `x` to `y` has as homotopy class the image under `θ` of the path class
`TauCeti.IsAdaptedPseudoGradient.trajectoryPathClass` of the corresponding point of the
middle-level slice, along which the Morse boundary with local coefficients transports. -/
theorem mk_toPath_morseLoopEvaluation_eq_trajectoryPathClass
    (hdense' : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀) (w : hX.morseBrokenTrajectorySpace c x y) :
    Path.Homotopic.Quotient.mk (hX.morseLoopEvaluation hf hdense' hθ x y
        (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _) w)).toPath =
      ((hX.trajectoryPathClass (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense' x y) hind w)).map
        θ).cast (hθ x).symm (hθ y).symm := by
  rw [trajectoryPathClass_def]
  exact hX.mk_toPath_morseLoopEvaluation hf hdense' hθ
    (ne_of_manifoldMorseIndex_eq_add_one hind)
    (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _) w)
    (hX.morseTrajectorySlice_subset x y
      (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense' x y) hind w).property)
    (h.exists_flow_morseBrokenTrajectorySpaceEquivSlice hf (hdense' x y) hind w)

section ClassicalAction

variable {Y : Type u} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  {R : Type u} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  {ind : criticalPoints 𝓘(ℝ, E) f → ℤ}

/-- **Between consecutive indices the Barraud–Cornea cocycle acts on a classical local system by
transport along the trajectories.** Under the Morse–Smale condition, let `ind x = ind y + 1`, and
let `L` be a local system on `Y`, read at `y₀` as a DG local system in degree zero
(`TauCeti.classicalDGLocalSystem`). The entry at `(x, y)` of the Barraud–Cornea cocycle of a
twisting chain system `S` acts on the fibre `L(y₀)` as the sum, over the trajectories from `x` to
`y` read on the middle-level slice, of the transports along their images under `θ`, weighted by
the coefficients of the trajectories in the `0`-chain of `S`. -/
theorem classicalAction_barraudCorneaCocycle_m (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (L : LocalCoefficientSystem.{u, u, w} R (TopCat.of Y)) {x y : criticalPoints 𝓘(ℝ, E) f}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1) :
    classicalAction (x := y₀) L (op ((hX.barraudCorneaCocycle hf hdense hθ hc S).m x y)) =
      ∑ᶠ z : hX.morseTrajectorySlice x y,
        NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0)
            ((h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hind).symm z) •
          (LocalCoefficientSystem.transport L
            (((hX.trajectoryPathClass z).map θ).cast (hθ x).symm (hθ y).symm)).toLinearMap := by
  set e := h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hind
  -- A Moore loop acts on the fibre by the transport along its class.
  have hF (w : hX.morseBrokenTrajectorySpace c x y) :
      (L.fiberRightAction (MooreLoopSpace.fundamentalGroupHom y₀ (hX.morseLoopEvaluation hf hdense
        hθ x y (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _) w)))).unop =
      (LocalCoefficientSystem.transport L
        (((hX.trajectoryPathClass (e w)).map θ).cast (hθ x).symm (hθ y).symm)).toLinearMap := by
    rw [← h.mk_toPath_morseLoopEvaluation_eq_trajectoryPathClass hf hind hdense hθ w]
    ext v
    rw [MooreLoopSpace.fundamentalGroupHom_apply, LocalCoefficientSystem.fiberRightAction_apply,
      unop_op, inv_inv, LocalCoefficientSystem.monodromyRepresentation_apply, LinearEquiv.coe_coe,
      LocalCoefficientSystem.transport_apply]
  rw [classicalAction_op_apply, loopChainToGroupAlgebra_barraudCorneaCocycle_m, map_finsuppSum]
  simp only [MonoidAlgebra.lift_single]
  rw [MulOpposite.unop_finsuppSum]
  simp only [MulOpposite.unop_smul, hF, Finsupp.sum]
  rw [← finsum_eq_sum_of_support_subset _
    (s := (NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0)).support) fun w hw ↦ ?_,
    ← finsum_comp_equiv e.symm]
  · simp only [Equiv.apply_symm_apply]
  · simpa using left_ne_zero_of_smul hw

/-- **Classical recovery.** Under the Morse–Smale condition, let the index of the twisting chain
system `S` be the Morse index, and let `S` give each trajectory between critical points of
consecutive index its sign for the orientations `𝔬` in its `0`-chain, as the fundamental chains
of the oriented trajectory spaces of index difference one do. Then, for a local system `L` on `Y`
read at `y₀` as a DG local system in degree zero, the entry at `(x, y)` of the Barraud–Cornea
cocycle acts on `L(y₀)` as the component from `x` to `y` of the Morse boundary of `f` with
coefficients in the pullback `θ^* L` (`TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundaryMap`),
read through the identifications `L(y₀) ≅ L(θ x)` along `θ x = y₀`. -/
theorem classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (hind : ∀ x, ind x = manifoldMorseIndex 𝓘(ℝ, E) f x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (𝔬 : MorseOrientation f X)
    (hS : ∀ (x y : criticalPoints 𝓘(ℝ, E) f)
      (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1)
      (w : hX.morseBrokenTrajectorySpace c x y),
      NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0) w =
        hX.trajectorySign (𝔬.chart x) (𝔬.chart y) (𝔬.orientation x) (𝔬.orientation y) hxy
          (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hxy w))
    (L : LocalCoefficientSystem.{u, u, w} R (TopCat.of Y)) (x y : criticalPoints 𝓘(ℝ, E) f) :
    classicalAction (x := y₀) L (op ((hX.barraudCorneaCocycle hf hdense hθ hc S).m x y)) =
      (LocalCoefficientSystem.transport L
          ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))).symm.toLinearMap ∘ₗ
        hX.twistedMorseBoundaryMap 𝔬 ((LocalCoefficientSystem.pullback θ).obj L) x y ∘ₗ
          (LocalCoefficientSystem.transport L
            ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))).toLinearMap := by
  by_cases hxy : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1
  · have := (h.finite_morseTrajectorySlice hf hxy).to_subtype
    -- Conjugating by the identifications of the fibres is additive.
    let φ : ((((LocalCoefficientSystem.pullback (X := TopCat.of M) (Y := TopCat.of Y) θ).obj L).obj
          (FundamentalGroupoid.mk (x : M))) →ₗ[R]
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) (Y := TopCat.of Y) θ).obj L).obj
          (FundamentalGroupoid.mk (y : M))) →+
          Module.End R (L.obj (FundamentalGroupoid.mk y₀)) :=
      AddMonoidHom.mk' (fun g ↦ (LocalCoefficientSystem.transport L
          ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))).symm.toLinearMap ∘ₗ g ∘ₗ
            (LocalCoefficientSystem.transport L
              ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))).toLinearMap)
        -- The pulled-back fibres are fibres of `L` only up to unfolding the pullback, which `simp`
        -- does not see through; the composite is additive by `map_add` of the outer map.
        fun g g' ↦ LinearMap.ext fun v ↦ (map_add (LocalCoefficientSystem.transport L
          ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))).symm _ _ :)
    rw [h.classicalAction_barraudCorneaCocycle_m hf hdense hθ hc S L hxy,
      twistedMorseBoundaryMap_of_morseIndex_eq_add_one hxy]
    -- `φ` is a local definition, so the right side is `φ` of the sum only after unfolding it;
    -- no rewrite folds the composite back into `φ`.
    change _ = φ _
    rw [map_finsum φ (Set.toFinite _)]
    refine finsum_congr fun z ↦ ?_
    rw [map_zsmul, hS x y hxy, Equiv.apply_symm_apply, Int.cast_smul_eq_zsmul]
    congr 1
    simp only [φ, AddMonoidHom.mk'_apply, LocalCoefficientSystem.pullback_transport]
    rw [LocalCoefficientSystem.transport_cast L _ (hθ x).symm (hθ y).symm, LinearEquiv.coe_trans,
      LinearEquiv.coe_trans]
    -- The two sides differ only by unfolding the pulled-back fibres to fibres of `L`.
    rfl
  · rw [twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one hxy,
      classicalAction_eq_zero L (loopChainToGroupAlgebra_eq_zero_of_mem (i := ind y - ind x + 1)
        (by rw [hind, hind]; omega) ((hX.barraudCorneaCocycle hf hdense hθ hc S).mem_graded x y))]
    -- As for `φ`, the pulled-back fibres are fibres of `L` only up to unfolding the pullback, so
    -- `LinearMap.comp_zero` does not match syntactically; compare the maps pointwise instead.
    ext
    exact (map_zero (LocalCoefficientSystem.transport L
      ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))).symm).symm

/-- **Classical recovery modulo two.** In characteristic two the signs of the trajectories are
`1`. So if the `0`-chains of `S` give every trajectory between critical points of consecutive
index the coefficient `1`, as the mod-two fundamental chains of the finite trajectory spaces do,
the Barraud–Cornea cocycle acts on a classical local system as the Morse boundary with
coefficients in the pullback, for every choice of orientations. -/
theorem classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap_of_charTwo [CharP R 2]
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (hind : ∀ x, ind x = manifoldMorseIndex 𝓘(ℝ, E) f x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (hS : ∀ x y : criticalPoints 𝓘(ℝ, E) f,
      manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1 →
        ∀ w, NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0) w = 1)
    (𝔬 : MorseOrientation f X) (L : LocalCoefficientSystem.{u, u, w} R (TopCat.of Y))
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    classicalAction (x := y₀) L (op ((hX.barraudCorneaCocycle hf hdense hθ hc S).m x y)) =
      (LocalCoefficientSystem.transport L
          ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))).symm.toLinearMap ∘ₗ
        hX.twistedMorseBoundaryMap 𝔬 ((LocalCoefficientSystem.pullback θ).obj L) x y ∘ₗ
          (LocalCoefficientSystem.transport L
            ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))).toLinearMap := by
  refine h.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap hf hdense hθ hc hind S
    𝔬 (fun x y hxy w ↦ ?_) L x y
  rw [hS x y hxy w]
  rcases trajectorySign_eq_one_or_eq_neg_one (𝔬.coord_mfderiv_chart x) (𝔬.coord_mfderiv_chart y)
    (op := 𝔬.orientation x) (oq := 𝔬.orientation y) (hpq := hxy) h hf
    (hX.morseTrajectorySlice_subset x y
      (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hxy w).property) with hs | hs <;>
    rw [hs]
  · exact Int.cast_one.symm
  · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

end ClassicalAction

section ClassicalComplex

variable {Y : Type u} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  {R : Type u} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  {ind : criticalPoints 𝓘(ℝ, E) f → ℤ}

/-- **The twisted differential with classical coefficients is the twisted Morse boundary.** Under
the hypotheses of classical recovery
(`IsMorseSmale.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap`), read a family
`g` of elements of the fibre `L(y₀)`, indexed by the critical points, as the family of elements
`g x` of the fibres `L(θ x)` of the pullback `θ^* L`, along the identifications `L(y₀) ≅ L(θ x)`.
Then the differential of the twisted complex of `L(y₀)`, concentrated in degree zero, with the
Barraud–Cornea cocycle of `S` is the Morse boundary of `f` with coefficients in `θ^* L`. -/
theorem transport_twistedDifferential_eq_twistedMorseBoundary (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (hind : ∀ x, ind x = manifoldMorseIndex 𝓘(ℝ, E) f x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (𝔬 : MorseOrientation f X)
    (hS : ∀ (x y : criticalPoints 𝓘(ℝ, E) f)
      (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1)
      (w : hX.morseBrokenTrajectorySpace c x y),
      NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0) w =
        hX.trajectorySign (𝔬.chart x) (𝔬.chart y) (𝔬.orientation x) (𝔬.orientation y) hxy
          (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hxy w))
    (L : LocalCoefficientSystem.{u, u, w} R (TopCat.of Y))
    (g : criticalPoints 𝓘(ℝ, E) f → (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).carrier)
    (y : criticalPoints 𝓘(ℝ, E) f) :
    LocalCoefficientSystem.transport L ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))
        (twistedDifferential (hX.barraudCorneaCocycle hf hdense hθ hc S).m
          (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).grading
          (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).differential g y) =
      hX.twistedMorseBoundary 𝔬 ((LocalCoefficientSystem.pullback θ).obj L) hf
        (fun x ↦ LocalCoefficientSystem.transport L
          ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x)) (g x)) y := by
  -- The fibre is trivially graded with zero differential: the twisted differential is the sum of
  -- the actions of the entries. The twisted differential depends on the decomposition of the
  -- grading, so `classicalDGLocalSystem_grading` cannot rewrite it; the bundled grading is the
  -- trivial one by definition.
  have hD : twistedDifferential (hX.barraudCorneaCocycle hf hdense hθ hc S).m
      (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).grading
      (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).differential g y =
        ∑ x, op ((hX.barraudCorneaCocycle hf hdense hθ hc S).m x y) • g x := by
    rw [classicalDGLocalSystem_differential]
    exact (twistedDifferential_trivialGrading_apply
      (R := R) (M := (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).carrier)
      (hX.barraudCorneaCocycle hf hdense hθ hc S).m 0 g y).trans
        (by rw [LinearMap.zero_apply, zero_add])
  refine (congrArg (LocalCoefficientSystem.transport L
    ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))) hD).trans ?_
  -- The sum is taken in the bundled carrier, which is the fibre `L(y₀)` only up to unfolding.
  refine (map_sum (LocalCoefficientSystem.transport L
    ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))) _ Finset.univ).trans ?_
  refine Eq.trans ?_ ((twistedMorseBoundary_apply (hX := hX) (𝔬 := 𝔬)
    (L := (LocalCoefficientSystem.pullback θ).obj L) hf _ y).trans
      (finsum_eq_sum_of_fintype _)).symm
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  -- A chain acts on the bundled carrier through `classicalAction` (`op_smul_eq_classicalAction`).
  refine (congrArg (LocalCoefficientSystem.transport L
    ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))) (LinearMap.congr_fun
      (h.classicalAction_barraudCorneaCocycle_m_eq_twistedMorseBoundaryMap hf hdense hθ hc hind S 𝔬
        hS L x y) (g x))).trans ?_
  -- The composite of linear maps applies pointwise; the pulled-back fibres are fibres of `L` only
  -- up to unfolding the pullback, so `LinearMap.comp_apply` does not fire under `simp`.
  exact LinearEquiv.apply_symm_apply (LocalCoefficientSystem.transport L
    ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ y))) _

/-- **The Morse boundary with local coefficients squares to zero** as soon as a twisting chain
system gives the trajectories of index difference one their signs, through the Barraud–Cornea
cocycle. Under the identifications `L(y₀) ≅ L(θ x)` the Morse boundary of `f` with coefficients in
`θ^* L` is the differential of the twisted complex of `L(y₀)`
(`IsMorseSmale.transport_twistedDifferential_eq_twistedMorseBoundary`), which squares to zero by
the twisting equation of the cocycle. -/
theorem twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f)
    (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
    (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
    (hind : ∀ x, ind x = manifoldMorseIndex 𝓘(ℝ, E) f x)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (𝔬 : MorseOrientation f X)
    (hS : ∀ (x y : criticalPoints 𝓘(ℝ, E) f)
      (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1)
      (w : hX.morseBrokenTrajectorySpace c x y),
      NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0) w =
        hX.trajectorySign (𝔬.chart x) (𝔬.chart y) (𝔬.orientation x) (𝔬.orientation y) hxy
          (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hxy w))
    (L : LocalCoefficientSystem.{u, u, w} R (TopCat.of Y)) :
    hX.twistedMorseBoundary 𝔬 ((LocalCoefficientSystem.pullback θ).obj L) hf ∘ₗ
        hX.twistedMorseBoundary 𝔬 ((LocalCoefficientSystem.pullback θ).obj L) hf = 0 := by
  set 𝓛 := classicalDGLocalSystem (X := TopCat.of Y) y₀ L
  set T := fun x : criticalPoints 𝓘(ℝ, E) f ↦
    LocalCoefficientSystem.transport L ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))
  -- Transporting a family of `L(y₀)` intertwines the twisted differential with the boundary.
  have key (g : criticalPoints 𝓘(ℝ, E) f → 𝓛.carrier) :
      hX.twistedMorseBoundary 𝔬 ((LocalCoefficientSystem.pullback θ).obj L) hf
          (fun x ↦ T x (g x)) =
        fun y ↦ T y (twistedDifferential (hX.barraudCorneaCocycle hf hdense hθ hc S).m 𝓛.grading
          𝓛.differential g y) :=
    funext fun y ↦ (h.transport_twistedDifferential_eq_twistedMorseBoundary hf hdense hθ hc hind S
      𝔬 hS L g y).symm
  refine LinearMap.ext fun b ↦ ?_
  obtain ⟨g, rfl⟩ : ∃ g : criticalPoints 𝓘(ℝ, E) f → 𝓛.carrier, (fun x ↦ T x (g x)) = b :=
    ⟨fun x ↦ (T x).symm (b x), funext fun x ↦ (T x).apply_symm_apply (b x)⟩
  have hsq := (hX.barraudCorneaCocycle hf hdense hθ hc S).twistedDifferential_sq_zero
    𝓛.differential 𝓛.isDGRightModule g
  refine Eq.trans ?_ (LinearMap.zero_apply _).symm
  refine (congrArg (hX.twistedMorseBoundary 𝔬 ((LocalCoefficientSystem.pullback θ).obj L) hf)
    (key g)).trans ((key _).trans (funext fun y ↦ ?_))
  -- The families live in the bundled carrier, the fibre `L(y₀)` only up to unfolding.
  rw [hsq]
  exact map_zero (T y)

end ClassicalComplex

section ClassicalIso

variable {Y : Type u} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  {R : Type u} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  (S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
    (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R)
  (𝔬 : MorseOrientation f X)
  (hS : ∀ (x y : criticalPoints 𝓘(ℝ, E) f)
    (hxy : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1)
    (w : hX.morseBrokenTrajectorySpace c x y),
    NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0) w =
      hX.trajectorySign (𝔬.chart x) (𝔬.chart y) (𝔬.orientation x) (𝔬.orientation y) hxy
        (h.morseBrokenTrajectorySpaceEquivSlice hf (hdense x y) hxy w))
  (L : LocalCoefficientSystem.{u, u, w} R (TopCat.of Y))

omit [Fintype (criticalPoints 𝓘(ℝ, E) f)] in
/-- The transports `L(y₀) ≅ L(θ x)` at the critical points, as an equivalence from the families of
elements of the fibre `L(y₀)` of the DG local system to the Morse chains with coefficients in
`θ^* L`. -/
-- The bundled carrier of `classicalDGLocalSystem` is the fibre `L(y₀)` only up to unfolding, and
-- instance search does not find its module structure under the binder of `piCongrRight`; so the
-- equivalence is built on the fibre, elaborated without the expected type, and its type is fixed
-- by this declaration.
private noncomputable def transportPiEquiv (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
    (L : LocalCoefficientSystem.{u, u, w} R (TopCat.of Y)) :
    (criticalPoints 𝓘(ℝ, E) f → (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).carrier) ≃ₗ[R]
      ((p : criticalPoints 𝓘(ℝ, E) f) →
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L).obj
          (FundamentalGroupoid.mk (p : M))) :=
  (LinearEquiv.piCongrRight fun x : criticalPoints 𝓘(ℝ, E) f ↦
    LocalCoefficientSystem.transport L ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x)) :)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  [Fintype (criticalPoints 𝓘(ℝ, E) f)] in
/-- `transportPiEquiv` is the transport `L(y₀) ≅ L(θ x)` at each critical point `x`. -/
private theorem transportPiEquiv_apply
    (g : criticalPoints 𝓘(ℝ, E) f → (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).carrier)
    (x : criticalPoints 𝓘(ℝ, E) f) :
    transportPiEquiv hθ L g x =
      LocalCoefficientSystem.transport L ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))
        (g x) :=
  (LinearEquiv.piCongrRight_apply (fun x : criticalPoints 𝓘(ℝ, E) f ↦
    LocalCoefficientSystem.transport L ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))) g x :)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  [Fintype (criticalPoints 𝓘(ℝ, E) f)] in
/-- The transports `L(y₀) ≅ L(θ x)` carry the families of total degree `n` in the twisted complex
of `L(y₀)`, concentrated in degree zero, onto the families vanishing away from the critical points
of index `-n`. -/
private theorem map_twistedTotalGrading_transportPiEquiv (n : ℤ) :
    (twistedTotalGrading (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).grading
        (fun x : criticalPoints 𝓘(ℝ, E) f ↦ (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) n).map
      (transportPiEquiv hθ L).toLinearMap =
      Submodule.pi univ fun p : criticalPoints 𝓘(ℝ, E) f ↦
        trivialGrading R (((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L).obj
          (FundamentalGroupoid.mk (p : M))) (n + (manifoldMorseIndex 𝓘(ℝ, E) f p : ℤ)) := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext b
  rw [Submodule.mem_comap, mem_twistedTotalGrading_iff]
  simp only [classicalDGLocalSystem_grading, Submodule.mem_pi, mem_univ, true_implies,
    mem_trivialGrading_iff]
  refine forall_congr' fun x ↦ ?_
  -- The element lies in the bundled carrier of `classicalDGLocalSystem`, which is the fibre only up
  -- to unfolding, so `mem_trivialGrading_iff` is applied at the fibre. The inverse of
  -- `transportPiEquiv` is the inverse transport at each point.
  exact (mem_trivialGrading_iff (R := R) (A := L.obj (FundamentalGroupoid.mk y₀))).trans
    (or_congr_right (LinearEquiv.map_eq_zero_iff (LocalCoefficientSystem.transport L
      ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))).symm))

/-- The degree-`n` part of `IsMorseSmale.dgMorseComplexClassicalIso`: a family `g` of elements of
`L(y₀)`, of total degree `n`, goes to the family of its transports `g x ∈ L(θ x)`. -/
noncomputable def dgMorseComplexClassicalXEquiv (n : ℤ) :
    (hX.dgMorseComplex hf hdense hθ hc S
        (classicalDGLocalSystem (X := TopCat.of Y) y₀ L)).X n ≃ₗ[R]
      (hX.twistedMorseCochainComplex 𝔬
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L) hf
        (h.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero hf hdense hθ hc (fun _ ↦ rfl) S
          𝔬 hS L)).X n :=
  (twistedCochainComplexXEquiv (hX.barraudCorneaCocycle hf hdense hθ hc S).mem_graded
      (hX.barraudCorneaCocycle hf hdense hθ hc S).twisting
      (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).isDGRightModule n).trans
    ((LinearEquiv.ofSubmodules _ _ _ (map_twistedTotalGrading_transportPiEquiv hθ L n)).trans
      (hX.twistedMorseCochainComplexXEquiv 𝔬
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L) hf
        (h.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero hf hdense hθ hc (fun _ ↦ rfl) S
          𝔬 hS L) n).symm)

/-- Under the identifications of the terms of the two complexes with families, the degree-`n`
identification is the transport `L(y₀) ≅ L(θ x)` at each critical point `x`. -/
theorem twistedMorseCochainComplexXEquiv_dgMorseComplexClassicalXEquiv (n : ℤ)
    (g : (hX.dgMorseComplex hf hdense hθ hc S
      (classicalDGLocalSystem (X := TopCat.of Y) y₀ L)).X n)
    (x : criticalPoints 𝓘(ℝ, E) f) :
    (hX.twistedMorseCochainComplexXEquiv 𝔬
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L) hf
        (h.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero hf hdense hθ hc (fun _ ↦ rfl) S
          𝔬 hS L) n
        (h.dgMorseComplexClassicalXEquiv hf hdense hθ hc S 𝔬 hS L n g) :
          (p : criticalPoints 𝓘(ℝ, E) f) →
            ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L).obj
              (FundamentalGroupoid.mk (p : M))) x =
      LocalCoefficientSystem.transport L ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))
        ((twistedCochainComplexXEquiv (hX.barraudCorneaCocycle hf hdense hθ hc S).mem_graded
          (hX.barraudCorneaCocycle hf hdense hθ hc S).twisting
          (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).isDGRightModule n g :
            criticalPoints 𝓘(ℝ, E) f → (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).carrier)
          x) := by
  -- The source of the first factor is the twisted complex that `dgMorseComplex` unfolds to, so
  -- `LinearEquiv.trans_apply` only matches up to that unfolding. Neither `rw [dgMorseComplex_def]`
  -- (the type of `g` mentions the DG Morse complex) nor `rw`/`simp only` with
  -- `LinearEquiv.trans_apply` can make the step.
  erw [dgMorseComplexClassicalXEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.ofSubmodules_apply]
  exact transportPiEquiv_apply hθ L _ x

/-- Under the identifications of the terms of the two complexes with families, the inverse of the
degree-`n` identification is the inverse transport `L(θ x) ≅ L(y₀)` at each critical point `x`. -/
@[simp]
theorem twistedCochainComplexXEquiv_dgMorseComplexClassicalXEquiv_symm (n : ℤ)
    (b : (hX.twistedMorseCochainComplex 𝔬
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L) hf
        (h.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero hf hdense hθ hc (fun _ ↦ rfl) S
          𝔬 hS L)).X n)
    (x : criticalPoints 𝓘(ℝ, E) f) :
    (twistedCochainComplexXEquiv (hX.barraudCorneaCocycle hf hdense hθ hc S).mem_graded
        (hX.barraudCorneaCocycle hf hdense hθ hc S).twisting
        (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).isDGRightModule n
        ((h.dgMorseComplexClassicalXEquiv hf hdense hθ hc S 𝔬 hS L n).symm b) :
          criticalPoints 𝓘(ℝ, E) f → (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).carrier)
        x =
      (LocalCoefficientSystem.transport L ((Path.Homotopic.Quotient.refl y₀).cast rfl (hθ x))).symm
        ((hX.twistedMorseCochainComplexXEquiv 𝔬
          ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L) hf
          (h.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero hf hdense hθ hc (fun _ ↦ rfl) S
            𝔬 hS L) n b :
            (p : criticalPoints 𝓘(ℝ, E) f) →
              ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L).obj
                (FundamentalGroupoid.mk (p : M))) x) := by
  -- Apply the transport at `x` to both sides and read off the forward identification.
  refine (LinearEquiv.eq_symm_apply _).2
    ((h.twistedMorseCochainComplexXEquiv_dgMorseComplexClassicalXEquiv hf hdense hθ hc S 𝔬 hS L n
      _ x).symm.trans ?_)
  rw [LinearEquiv.apply_symm_apply]

/-- **Classical recovery.** Under the Morse–Smale condition, let `S` be a twisting chain system on
the trajectory spaces, graded by the Morse index, which gives each trajectory between critical
points of consecutive index its sign for the orientations `𝔬` in its `0`-chain, as the fundamental
chains of the oriented trajectory spaces of index difference one do. Then for a local system `L` on
`Y`, read at `y₀` as a DG local system concentrated in degree zero, the DG Morse complex of `S`
with coefficients in `L` is isomorphic to the Morse complex of `f` with coefficients in the
pullback `θ^* L`. The isomorphism transports a family of elements of `L(y₀)` along the
identifications `L(y₀) ≅ L(θ x)` at the critical points `x`. In particular the Morse boundary with
coefficients in `θ^* L` squares to zero
(`IsMorseSmale.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero`). -/
noncomputable def dgMorseComplexClassicalIso :
    hX.dgMorseComplex hf hdense hθ hc S (classicalDGLocalSystem (X := TopCat.of Y) y₀ L) ≅
      hX.twistedMorseCochainComplex 𝔬
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L) hf
        (h.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero hf hdense hθ hc (fun _ ↦ rfl) S
          𝔬 hS L) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (h.dgMorseComplexClassicalXEquiv hf hdense hθ hc S 𝔬 hS L n).toModuleIso)
    fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      ext g
      apply (hX.twistedMorseCochainComplexXEquiv 𝔬
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L) hf
        (h.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero hf hdense hθ hc (fun _ ↦ rfl) S
          𝔬 hS L) (i + 1)).injective
      apply Subtype.ext
      funext y
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
      rw [twistedMorseCochainComplexXEquiv_dgMorseComplexClassicalXEquiv,
        twistedMorseCochainComplexXEquiv_d]
      -- Read both sides on families: the boundary of the transported family is the transport of
      -- the twisted differential, which is the differential of the DG Morse complex.
      refine (congrArg (fun b ↦ hX.twistedMorseBoundary 𝔬
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L) hf b y)
          (funext fun x ↦ h.twistedMorseCochainComplexXEquiv_dgMorseComplexClassicalXEquiv hf
            hdense hθ hc S 𝔬 hS L i g x)).trans ?_
      refine (h.transport_twistedDifferential_eq_twistedMorseBoundary hf hdense hθ hc
        (fun _ ↦ rfl) S 𝔬 hS L _ y).symm.trans ?_
      exact congrArg _ (congrFun (twistedCochainComplexXEquiv_d
        (hX.barraudCorneaCocycle hf hdense hθ hc S).mem_graded
        (hX.barraudCorneaCocycle hf hdense hθ hc S).twisting
        (classicalDGLocalSystem (X := TopCat.of Y) y₀ L).isDGRightModule i g).symm y)

/-- The isomorphism of classical recovery is the degreewise identification. -/
@[simp]
theorem dgMorseComplexClassicalIso_hom_f_apply (n : ℤ)
    (g : (hX.dgMorseComplex hf hdense hθ hc S
      (classicalDGLocalSystem (X := TopCat.of Y) y₀ L)).X n) :
    ((h.dgMorseComplexClassicalIso hf hdense hθ hc S 𝔬 hS L).hom.f n).hom g =
      h.dgMorseComplexClassicalXEquiv hf hdense hθ hc S 𝔬 hS L n g := by
  simp only [dgMorseComplexClassicalIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]

/-- The inverse isomorphism of classical recovery is the inverse degreewise identification. -/
@[simp]
theorem dgMorseComplexClassicalIso_inv_f_apply (n : ℤ)
    (b : (hX.twistedMorseCochainComplex 𝔬
        ((LocalCoefficientSystem.pullback (X := TopCat.of M) θ).obj L) hf
        (h.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero hf hdense hθ hc (fun _ ↦ rfl) S
          𝔬 hS L)).X n) :
    ((h.dgMorseComplexClassicalIso hf hdense hθ hc S 𝔬 hS L).inv.f n).hom b =
      (h.dgMorseComplexClassicalXEquiv hf hdense hθ hc S 𝔬 hS L n).symm b := by
  simp only [dgMorseComplexClassicalIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]

end ClassicalIso

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
