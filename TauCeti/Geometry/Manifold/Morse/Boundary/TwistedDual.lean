/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Dual
public import TauCeti.Geometry.Manifold.Morse.Boundary.DualOrientation
public import TauCeti.Geometry.Manifold.Morse.Boundary.LocalCoefficient

/-!
# The twisted Morse boundary of the opposite function

Let `f` be a Morse function on a compact boundaryless manifold `M`, oriented by `oM`, and `X` a
Morse–Smale pseudo-gradient adapted to `f`, with orientation data `𝔬` for the unstable manifolds,
and let `L` be a local coefficient system of modules over a commutative ring `R` on `M`. Then `-X`
is a Morse–Smale pseudo-gradient adapted to `-f`, with the dual orientation data `𝔬.dual hX hf oM`
(`TauCeti.MorseOrientation.dual`). This file compares the Morse boundary of `f` with coefficients
in `L` (`TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundary`) with the Morse boundary of `-f`
with coefficients in the dual system `L^∨ = Hom_R(L, R)` (`TauCeti.LocalCoefficientSystem.dual`):
the second is the transpose of the first, up to the sign `(-1) ^ ind_f p` at each critical point.

The component of the boundary of `f` from `p` to `q` is the sum over the trajectories `y` from `p`
to `q` of their signs times the transports `L(p) → L(q)` along them. The same points `y` are the
trajectories of `-X` from `q` to `p` (`TauCeti.IsAdaptedPseudoGradient.neg_morseTrajectorySlice`),
and they trace the reversed paths (`TauCeti.IsAdaptedPseudoGradient.neg_trajectoryPathClass`).
Transport in `L^∨` along a reversed path is the dual map of transport in `L` along the path
(`TauCeti.LocalCoefficientSystem.transport_dual_symm`), and with the dual orientation data each
trajectory counts for `-f` with `(-1) ^ ind_f p` times its sign for `f`
(`TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign_of_unstableFrameOrientation`). Hence the
component of the boundary of `-f` from `q` to `p` is `(-1) ^ ind_f p` times the dual map of the
component of the boundary of `f` from `p` to `q`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.twistedMorseBoundaryMap_dual`).

Since a critical point of index `k` for `-f` has index `n - k` for `f`, where `n` is the dimension
of `M`, this identifies the Morse chains of `-f` with coefficients in `L^∨` in degree `k` with the
Morse cochains of `f` with coefficients in `L` in degree `n - k`, compatibly with the boundaries up
to sign. This is the local-coefficient form, on an oriented manifold, of the comparison of the
Morse complex of `-f` with the dual complex that underlies Poincaré duality, of which the integral
coefficient identity `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundaryCoeff_dual`
is the constant-coefficient counterpart. On a nonorientable
manifold the dual system has to be twisted further by the orientation local system of `M`, which
is not treated here.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.twistedMorseBoundaryMap_dual`: the component of the twisted boundary of `-f` with
  coefficients in `L^∨` from `q` to `p` is `(-1) ^ ind_f p` times the dual map of the component of
  the twisted boundary of `f` with coefficients in `L` from `p` to `q`.
* `IsMorseSmale.twistedMorseBoundary_dual_apply`: the twisted boundary of `-f` with coefficients
  in `L^∨` is the signed transpose of the twisted boundary of `f` with coefficients in `L`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 5 (the Morse complex of `-f` and Poincaré
  duality).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §3.H (local coefficients and
  Poincaré duality with twisted coefficients).
-/

public section

open Set
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {R : Type u} [CommRing R]

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} (𝔬 : MorseOrientation f X) (hf : IsMorse 𝓘(ℝ, E) f)
  (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)))
  (L : LocalCoefficientSystem.{u, v, w} R (TopCat.of M))

/-- **The twisted boundary components of the opposite function.** For the dual orientation data
and the dual local system `L^∨`, the component of the twisted Morse boundary of `-f` from `q` to
`p` is `(-1) ^ ind_f p` times the dual map of the component of the twisted Morse boundary of `f`
with coefficients in `L` from `p` to `q`. -/
theorem IsMorseSmale.twistedMorseBoundaryMap_dual (hMS : hX.IsMorseSmale)
    (q p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (hX.neg hf).twistedMorseBoundaryMap (𝔬.dual hX hf oM) L.dual q p =
      ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p : ℤ) •
        (hX.twistedMorseBoundaryMap 𝔬 L (Set.equivOfEq criticalPoints_neg p)
          (Set.equivOfEq criticalPoints_neg q)).dualMap := by
  have hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p :=
    hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg p).property
  have hq : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f q :=
    hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg q).property
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · have hqp := hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq
    -- The same index condition, stated for the critical points of `f`.
    have hpq' : manifoldMorseIndex 𝓘(ℝ, E) f (Set.equivOfEq criticalPoints_neg p) =
        manifoldMorseIndex 𝓘(ℝ, E) f (Set.equivOfEq criticalPoints_neg q) + 1 := hpq
    have := (hMS.finite_morseTrajectorySlice hf hpq').to_subtype
    have := Fintype.ofFinite (hX.morseTrajectorySlice (Set.equivOfEq criticalPoints_neg p)
      (Set.equivOfEq criticalPoints_neg q))
    rw [twistedMorseBoundaryMap_of_morseIndex_eq_add_one hqp,
      twistedMorseBoundaryMap_of_morseIndex_eq_add_one hpq']
    -- Read the trajectories of `-X` from `q` to `p` as those of `X` from `p` to `q`.
    have hslice : ∀ y, y ∈ hX.morseTrajectorySlice (Set.equivOfEq criticalPoints_neg p : M)
        (Set.equivOfEq criticalPoints_neg q) ↔ y ∈ (hX.neg hf).morseTrajectorySlice q p :=
      fun y ↦ (Set.ext_iff.1 (hX.neg_morseTrajectorySlice hf p q) y).symm
    rw [← finsum_comp_equiv (Equiv.subtypeEquivRight hslice), LinearMap.dualMap_def,
      map_finsum _ (Set.toFinite _), finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    -- Along each trajectory, transport in `L^∨` along the reversed path is the dual map of
    -- transport in `L`, and the sign for `-f` is `(-1) ^ ind_f p` times the sign for `f`.
    have hy := hX.mem_morseTrajectorySlice.1 y.property
    rw [hX.neg_trajectoryPathClass hf (p := (p : M)) (q := q) y
        ((Equiv.subtypeEquivRight hslice) y) (Equiv.subtypeEquivRight_apply_coe _ _),
      LocalCoefficientSystem.transport_dual_symm, Equiv.subtypeEquivRight_apply_coe, map_zsmul,
      smul_smul]
    -- The sign for `-f` with the dual orientation data is `(-1) ^ ind_f p` times the sign for `f`.
    exact congrArg (· • _) (neg_trajectorySign_of_unstableFrameOrientation
      (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg p))
      (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg q)) hf hp hq oM
      (𝔬.orientation _) ((𝔬.dual hX hf oM).orientation p) (𝔬.orientation _)
      ((𝔬.dual hX hf oM).orientation q)
      (reindex_unstableFrameOrientation_complementaryOrientation _ hf hp oM _)
      (reindex_unstableFrameOrientation_complementaryOrientation _ hf hq oM _) hMS hpq'
      ⟨hy.1, hy.2.1⟩)
  · have hq' : manifoldMorseIndex 𝓘(ℝ, E) (-f) q ≠ manifoldMorseIndex 𝓘(ℝ, E) (-f) p + 1 := by
      have := hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
      have := hq.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
      omega
    rw [twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one hq',
      twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one (p := Set.equivOfEq criticalPoints_neg p)
        (q := Set.equivOfEq criticalPoints_neg q) hpq, LinearMap.dualMap_def, map_zero,
      smul_zero]
    -- Both sides are the zero map; the fibres of `L^∨` are the dual modules by definition.
    rfl

/-- **The twisted boundary of the opposite function is the signed transpose.** For the dual
orientation data and the dual local system `L^∨`, the `p`-component of the twisted Morse boundary
of `-f` of a chain `c` of linear forms is `(-1) ^ ind_f p` times the sum over the critical points
`q` of the forms `c q` composed with the components of the twisted Morse boundary of `f` with
coefficients in `L` from `p` to `q`. -/
theorem IsMorseSmale.twistedMorseBoundary_dual_apply (hMS : hX.IsMorseSmale)
    (c : (q : criticalPoints 𝓘(ℝ, E) (-f)) → L.dual.obj (FundamentalGroupoid.mk (q : M)))
    (p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (hX.neg hf).twistedMorseBoundary (𝔬.dual hX hf oM) L.dual hf.neg c p =
      ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p : ℤ) •
        ∑ᶠ q, (hX.twistedMorseBoundaryMap 𝔬 L (Set.equivOfEq criticalPoints_neg p)
          (Set.equivOfEq criticalPoints_neg q)).dualMap (c q) := by
  have := hf.neg.finite_criticalPoints.to_subtype
  rw [twistedMorseBoundary_apply, smul_finsum' _ (Set.toFinite _)]
  exact finsum_congr fun q ↦
    LinearMap.congr_fun (hMS.twistedMorseBoundaryMap_dual 𝔬 hf oM L q p) (c q)

end IsAdaptedPseudoGradient

end TauCeti
