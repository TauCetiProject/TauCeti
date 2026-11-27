/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.OrientationSystem.Basic
public import TauCeti.AlgebraicTopology.LocalCoefficient.Dual

/-!
# The opposite function with coefficients in a dual local system twisted by orientations

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, not assumed
orientable, `X` a Morse–Smale pseudo-gradient adapted to `f`, and `L` a local coefficient system
of modules over a commutative ring `R` on `M`. This file compares the Morse boundary of `f` with
coefficients in `L` with the Morse boundary of `-f` with coefficients in `L^∨ ⊗ o(TM)`, the dual
system `L^∨ = Hom_R(L, R)` (`TauCeti.LocalCoefficientSystem.dual`) twisted by the orientation local
system `o(TM)` of `M` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`): the second is the
transpose of the first, up to the sign `(-1) ^ ind_f p` at each critical point.

Fix orientation data `𝔬` for `f` and orientations `o'` of the unstable manifolds of `-X` in the
negated Morse charts (`TauCeti.MorseOrientation.neg`), and orient `T_x M` at each critical point
`x` by `𝔬.orientation x` followed by `o' x`
(`TauCeti.IsAdaptedPseudoGradient.criticalOrientation`). Evaluation at this orientation
identifies the fibre of `L^∨ ⊗ o(TM)` at `x` with the fibre of `L^∨`
(`TauCeti.VectorBundleOrientationCover.tensorSignLocalSystemFiberEquiv`). Through these
identifications, the component of the Morse boundary of `-f` with coefficients in `L^∨ ⊗ o(TM)`
from `q` to `p` is `(-1) ^ ind_f p` times the dual map of the component of the Morse boundary of
`f` with coefficients in `L` from `p` to `q`
(`IsMorseSmale.tensorSignLocalSystemFiberEquiv_twistedMorseBoundaryMap_neg` in the namespace
`TauCeti.IsAdaptedPseudoGradient`).

The trajectories of `-X` from `q` to `p` are those of `X` from `p` to `q` run backwards, and along
each of them three things happen:

* transport in `L^∨` along the reversed path is the dual map of transport in `L` along the path
  (`TauCeti.LocalCoefficientSystem.transport_dual_symm`);
* the sign of the trajectory for `-f` is `(-1) ^ ind_f p` times its sign for `f`, times the sign
  `τ = ±1` recording whether orientation transport along it carries the orientation at `p` to the
  one at `q` (`TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign_eq_ite_orientationTransport`);
* transport in `o(TM)` along it, read at the orientations of its ends, is multiplication by the
  same `τ`, which cancels the first
  (`TauCeti.IsAdaptedPseudoGradient.trajectorySign_smul_signLocalSystemFiberEquiv_transport`).

A critical point of index `k` for `-f` has index `n - k` for `f`. So this identifies the Morse
chains of `-f` with coefficients in `L^∨ ⊗ o(TM)` in degree `k` with the Morse cochains of `f` with
coefficients in `L` in degree `n - k`, compatibly with the boundaries up to sign, on every compact
manifold. It is the chain-level comparison behind Poincaré duality with local coefficients twisted
by the orientation system. Two special cases are proved separately, in the namespace
`TauCeti.IsAdaptedPseudoGradient`: an oriented manifold, where `o(TM)` is trivial and the
coefficients are `L^∨` (`IsMorseSmale.twistedMorseBoundaryMap_dual`), and the constant system
`L = R`, where the coefficients are `o(TM)`
(`IsMorseSmale.signLocalSystemFiberEquiv_twistedMorseBoundaryMap_neg`).

The pointwise tensor product of local systems is the monoidal structure of the functor category
into `ModuleCat R`, which requires the coefficient ring and the fibres to live in the same
universe; the fibres of `o(TM)` live in the universe of `M` and of the model space `E`, so `R`
does too.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.tensorSignLocalSystemFiberEquiv_twistedMorseBoundaryMap_neg`: the component of the
  Morse boundary of `-f` with coefficients in `L^∨ ⊗ o(TM)` from `q` to `p` is `(-1) ^ ind_f p`
  times the dual map of the component of the Morse boundary of `f` with coefficients in `L` from
  `p` to `q`.
* `IsMorseSmale.tensorSignLocalSystemFiberEquiv_twistedMorseBoundary_neg_apply`: the Morse boundary
  of `-f` with coefficients in `L^∨ ⊗ o(TM)` is the signed transpose of the Morse boundary of `f`
  with coefficients in `L`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 5 (the Morse complex of `-f` and Poincaré
  duality).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §3.H (Poincaré duality with
  local coefficients and the orientation system).
-/

public section

open CategoryTheory MonoidalCategory Set
open scoped ContDiff Manifold TensorProduct

universe uE uM

namespace TauCeti

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} (𝔬 : MorseOrientation f X) (hf : IsMorse 𝓘(ℝ, E) f)
  (o' : ∀ p : criticalPoints 𝓘(ℝ, E) (-f),
    Orientation ℝ ({i // ((𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
      (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        (Set.equivOfEq criticalPoints_neg p).property)).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) p)))
  {R : Type max uM uE} [CommRing R]
  (L : LocalCoefficientSystem.{max uM uE, uM, max uM uE} R (TopCat.of M))

/-- **One trajectory of the opposite function with coefficients in `L^∨ ⊗ o(TM)`.** For a
trajectory of `X` from `p` to `q` through `y`, run backwards as a trajectory of `-X` through `y'`,
its sign for `-f` times transport in `L^∨ ⊗ o(TM)` along it, read at the orientation of `p`, is
`(-1) ^ ind_f p` times the transpose of its sign for `f` times transport in `L` along it, read at
the orientation of `q`. -/
private theorem trajectorySign_smul_transport_tensorSignLocalSystem (hMS : hX.IsMorseSmale)
    (q p : criticalPoints 𝓘(ℝ, E) (-f))
    (hpq' : manifoldMorseIndex 𝓘(ℝ, E) f (Set.equivOfEq criticalPoints_neg p) =
      manifoldMorseIndex 𝓘(ℝ, E) f (Set.equivOfEq criticalPoints_neg q) + 1)
    (hqp : manifoldMorseIndex 𝓘(ℝ, E) (-f) q = manifoldMorseIndex 𝓘(ℝ, E) (-f) p + 1)
    (y : hX.morseTrajectorySlice (Set.equivOfEq criticalPoints_neg p : M)
      (Set.equivOfEq criticalPoints_neg q))
    (y' : (hX.neg hf).morseTrajectorySlice q p) (hyy : (y' : M) = y)
    (c : (L.dual ⊗ VectorBundleOrientationCover.signLocalSystem E
      (TangentSpace 𝓘(ℝ, E) : M → Type _) R (Fintype.card_fin (Module.finrank ℝ E))).obj
        (FundamentalGroupoid.mk (q : M))) :
    VectorBundleOrientationCover.tensorSignLocalSystemFiberEquiv (Fintype.card_fin _) L.dual
        (b := (p : M)) (hX.criticalOrientation
          (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg p)) hf
          (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
            (Set.equivOfEq criticalPoints_neg p).property)
          (𝔬.orientation (Set.equivOfEq criticalPoints_neg p)) (o' p))
        (((hX.neg hf).trajectorySign ((𝔬.neg hf o').chart q) ((𝔬.neg hf o').chart p)
            ((𝔬.neg hf o').orientation q) ((𝔬.neg hf o').orientation p) hqp y' •
          (LocalCoefficientSystem.transport (L.dual ⊗ VectorBundleOrientationCover.signLocalSystem
            E (TangentSpace 𝓘(ℝ, E) : M → Type _) R (Fintype.card_fin _))
            ((hX.neg hf).trajectoryPathClass y')).toLinearMap) c) =
      ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p : ℤ) •
        Module.Dual.transpose (hX.trajectorySign (𝔬.chart (Set.equivOfEq criticalPoints_neg p))
            (𝔬.chart (Set.equivOfEq criticalPoints_neg q))
            (𝔬.orientation (Set.equivOfEq criticalPoints_neg p))
            (𝔬.orientation (Set.equivOfEq criticalPoints_neg q)) hpq' y •
          (LocalCoefficientSystem.transport L (hX.trajectoryPathClass y)).toLinearMap)
          (VectorBundleOrientationCover.tensorSignLocalSystemFiberEquiv (Fintype.card_fin _) L.dual
            (b := (q : M)) (hX.criticalOrientation
              (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg q)) hf
              (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
                (Set.equivOfEq criticalPoints_neg q).property)
              (𝔬.orientation (Set.equivOfEq criticalPoints_neg q)) (o' q)) c) := by
  obtain ⟨z, hz⟩ := y'
  obtain rfl : z = y := hyy
  have hy := hX.mem_morseTrajectorySlice.1 y.property
  have hy' : (y : M) ∈ hX.flow.unstableSet (Set.equivOfEq criticalPoints_neg p : M) ∩
      hX.flow.stableSet (Set.equivOfEq criticalPoints_neg q : M) := ⟨hy.1, hy.2.1⟩
  -- The trajectory of `-X` traces the reversed path.
  have hP := hX.neg_trajectoryPathClass hf y ⟨y, hz⟩ rfl
  have hP' : (hX.neg hf).trajectoryPathClass ⟨y, hz⟩ =
      .mk (Flow.connectingPath hy'.1 hy'.2).symm := hP.trans (by
    rw [trajectoryPathClass_def]
    exact (Path.Homotopic.Quotient.mk_symm _).symm)
  induction c using TensorProduct.inductionOn with
  | tmul φ s =>
    have key := trajectorySign_smul_signLocalSystemFiberEquiv_transport 𝔬 hf o' hMS q p hpq'
      hqp hy' _ hP' s
    -- Transport in `L^∨ ⊗ o(TM)` is transport in each factor, and the `o(TM)` factor is read
    -- at the orientation of `p`.
    refine (map_zsmul (LinearEquiv.toLinearMap _) _ _).trans ?_
    refine (congrArg (_ • ·) ((congrArg _
      (LocalCoefficientSystem.transport_tensor_tmul _ _ _ φ s)).trans
        (VectorBundleOrientationCover.tensorSignLocalSystemFiberEquiv_tmul _ _ _ _ _))).trans ?_
    -- The sign for `-f` times the `o(TM)` factor is the signed value at the orientation of `q`.
    refine (smul_assoc _ _ _).symm.trans ((congrArg (· • _) key).trans ?_)
    -- Transport in `L^∨` along the reversed path is the dual map of transport in `L`.
    refine (congrArg (_ • ·) ((congrArg (LocalCoefficientSystem.transport L.dual · φ) hP).trans
      (DFunLike.congr_fun (LocalCoefficientSystem.transport_dual_symm L _) φ))).trans ?_
    -- Read the right-hand side at the orientation of `q`.
    refine Eq.trans ?_ (congrArg (_ • ·) (congrArg (Module.Dual.transpose _)
      (VectorBundleOrientationCover.tensorSignLocalSystemFiberEquiv_tmul (b := (q : M)) _ _ _ φ
        s).symm))
    -- What remains is linear algebra in the dual of the fibre of `L`.
    have alg : ∀ (n t : ℤ) (r : R) (e : L.obj (FundamentalGroupoid.mk (p : M)) ≃ₗ[R]
        L.obj (FundamentalGroupoid.mk (q : M))) (φ : Module.Dual R (L.obj
          (FundamentalGroupoid.mk (q : M)))),
        ((n * t) • r) • e.dualMap φ = n • Module.Dual.transpose (t • e.toLinearMap) (r • φ) := by
      intro n t r e φ
      ext a
      simp only [LinearMap.smul_apply, LinearEquiv.dualMap_apply, Module.Dual.transpose_apply,
        LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_zsmul, smul_eq_mul,
        mul_smul, smul_mul_assoc]
    exact alg _ _ _ _ φ
  | add c d hc hd =>
    -- Both sides are additive in the chain.
    exact ((congrArg _ (map_add _ c d)).trans (map_add _ _ _)).trans
      ((congrArg₂ (· + ·) hc hd).trans
        ((congrArg _ ((congrArg _ (map_add _ c d)).trans (map_add _ _ _))).trans
          (smul_add _ _ _)).symm)

/-- **The opposite function with coefficients in `L^∨ ⊗ o(TM)`.** Orient `T_x M`, at each critical
point `x`, by `𝔬.orientation x` followed by `o' x` (`criticalOrientation`), and read the fibre of
`L^∨ ⊗ o(TM)` at `x` as that of `L^∨` by evaluation at this orientation. Then the component from
`q` to `p` of the Morse boundary of `-f`, for the orientation data `𝔬.neg hf o'` and with
coefficients in `L^∨ ⊗ o(TM)`, is `(-1) ^ ind_f p` times the dual map of the component from `p` to
`q` of the Morse boundary of `f` with coefficients in `L`. No orientation of `M` is assumed. -/
theorem IsMorseSmale.tensorSignLocalSystemFiberEquiv_twistedMorseBoundaryMap_neg
    (hMS : hX.IsMorseSmale) (q p : criticalPoints 𝓘(ℝ, E) (-f))
    (c : (L.dual ⊗ VectorBundleOrientationCover.signLocalSystem E
      (TangentSpace 𝓘(ℝ, E) : M → Type _) R (Fintype.card_fin (Module.finrank ℝ E))).obj
        (FundamentalGroupoid.mk (q : M))) :
    VectorBundleOrientationCover.tensorSignLocalSystemFiberEquiv (Fintype.card_fin _) L.dual
        (b := (p : M)) (hX.criticalOrientation
          (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg p)) hf
          (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
            (Set.equivOfEq criticalPoints_neg p).property)
          (𝔬.orientation (Set.equivOfEq criticalPoints_neg p)) (o' p))
        ((hX.neg hf).twistedMorseBoundaryMap (𝔬.neg hf o')
          (L.dual ⊗ VectorBundleOrientationCover.signLocalSystem E
            (TangentSpace 𝓘(ℝ, E) : M → Type _) R (Fintype.card_fin _)) q p c) =
      ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p : ℤ) •
        (hX.twistedMorseBoundaryMap 𝔬 L (Set.equivOfEq criticalPoints_neg p)
          (Set.equivOfEq criticalPoints_neg q)).dualMap
          (VectorBundleOrientationCover.tensorSignLocalSystemFiberEquiv (Fintype.card_fin _) L.dual
            (b := (q : M)) (hX.criticalOrientation
              (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg q)) hf
              (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
                (Set.equivOfEq criticalPoints_neg q).property)
              (𝔬.orientation (Set.equivOfEq criticalPoints_neg q)) (o' q)) c) := by
  have hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p :=
    hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg p).property
  have hq : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f q :=
    hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg q).property
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · have hqp := hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq
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
      map_finsum _ (Set.toFinite _), finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    refine ((congrArg _ (LinearMap.sum_apply _ _ c)).trans
      (map_sum (VectorBundleOrientationCover.tensorSignLocalSystemFiberEquiv (Fintype.card_fin _)
        L.dual (b := (p : M)) (hX.criticalOrientation
          (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg p)) hf hp
          (𝔬.orientation (Set.equivOfEq criticalPoints_neg p)) (o' p))).toLinearMap _ _)).trans ?_
    refine Eq.trans ?_ (congrArg _ (LinearMap.sum_apply _ _ _)).symm
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    exact trajectorySign_smul_transport_tensorSignLocalSystem 𝔬 hf o' L hMS q p hpq' hqp y _
      (Equiv.subtypeEquivRight_apply_coe hslice y) c
  · have hq' : manifoldMorseIndex 𝓘(ℝ, E) (-f) q ≠ manifoldMorseIndex 𝓘(ℝ, E) (-f) p + 1 := by
      have := hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
      have := hq.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
      omega
    rw [twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one hq',
      twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one (p := Set.equivOfEq criticalPoints_neg p)
        (q := Set.equivOfEq criticalPoints_neg q) hpq, LinearMap.dualMap_def, map_zero,
      LinearMap.zero_apply]
    -- Both sides are zero.
    exact (map_zero _).trans ((congrArg _ (LinearMap.zero_apply _)).trans (smul_zero _)).symm

/-- **The Morse boundary of the opposite function with coefficients in `L^∨ ⊗ o(TM)` is the signed
transpose.** Read through evaluation at the orientations `criticalOrientation` of `T_x M` at the
critical points, the `p`-component of the Morse boundary of `-f` with coefficients in `L^∨ ⊗ o(TM)`
of a chain `c` is `(-1) ^ ind_f p` times the sum over the critical points `q` of the forms read
from `c q`, composed with the components of the Morse boundary of `f` with coefficients in `L`
from `p` to `q`. -/
theorem IsMorseSmale.tensorSignLocalSystemFiberEquiv_twistedMorseBoundary_neg_apply
    (hMS : hX.IsMorseSmale)
    (c : (q : criticalPoints 𝓘(ℝ, E) (-f)) → (L.dual ⊗ VectorBundleOrientationCover.signLocalSystem
      E (TangentSpace 𝓘(ℝ, E) : M → Type _) R (Fintype.card_fin (Module.finrank ℝ E))).obj
        (FundamentalGroupoid.mk (q : M)))
    (p : criticalPoints 𝓘(ℝ, E) (-f)) :
    VectorBundleOrientationCover.tensorSignLocalSystemFiberEquiv (Fintype.card_fin _) L.dual
        (b := (p : M)) (hX.criticalOrientation
          (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg p)) hf
          (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
            (Set.equivOfEq criticalPoints_neg p).property)
          (𝔬.orientation (Set.equivOfEq criticalPoints_neg p)) (o' p))
        ((hX.neg hf).twistedMorseBoundary (𝔬.neg hf o')
          (L.dual ⊗ VectorBundleOrientationCover.signLocalSystem E
            (TangentSpace 𝓘(ℝ, E) : M → Type _) R (Fintype.card_fin _)) hf.neg c p) =
      ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p : ℤ) •
        ∑ᶠ q, (hX.twistedMorseBoundaryMap 𝔬 L (Set.equivOfEq criticalPoints_neg p)
          (Set.equivOfEq criticalPoints_neg q)).dualMap
          (VectorBundleOrientationCover.tensorSignLocalSystemFiberEquiv (Fintype.card_fin _) L.dual
            (b := (q : M)) (hX.criticalOrientation
              (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg q)) hf
              (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
                (Set.equivOfEq criticalPoints_neg q).property)
              (𝔬.orientation (Set.equivOfEq criticalPoints_neg q)) (o' q)) (c q)) := by
  have := hf.neg.finite_criticalPoints.to_subtype
  rw [twistedMorseBoundary_apply, map_finsum _ (Set.toFinite _), smul_finsum' _ (Set.toFinite _)]
  exact finsum_congr fun q ↦
    hMS.tensorSignLocalSystemFiberEquiv_twistedMorseBoundaryMap_neg 𝔬 hf o' L q p (c q)

end IsAdaptedPseudoGradient

end TauCeti
