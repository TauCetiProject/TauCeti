/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Sign
public import TauCeti.Geometry.Manifold.Morse.Stable.Orientation
public import TauCeti.LinearAlgebra.Orientation.Exact.Pair

/-!
# Signs of trajectories of the reversed pseudo-gradient

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, and `X` a
Morse–Smale pseudo-gradient adapted to `f`. Then `-X` is a Morse–Smale pseudo-gradient adapted
to `-f`, and a trajectory of `X` from `p` to `q`, run backwards, is a trajectory of `-X` from `q` to
`p`. When `ind p = ind q + 1`, it is counted by both integral Morse boundaries, that of `f` with the
sign `TauCeti.IsAdaptedPseudoGradient.trajectorySign` measured against orientations `op` and `oq`
of the unstable manifolds of `X` at `p` and `q`, and that of `-f` with the sign measured against
orientations `oq'` and `op'` of the unstable manifolds of `-X`, the stable manifolds of `X`. This
file compares the two signs.

A Morse chart `φ` at a critical point `x` splits the coordinates into those of negative weight,
the unstable directions of `X`, and those of positive weight, the unstable directions of `-X`
(`TauCeti.MorseChart.neg`). At a point `y` of the unstable manifold of `x`, the unstable frame of
`X` and the normal coordinates of the stable manifold of `-X` form a short exact sequence

`0 → V⁻ → T_y M → V⁺ → 0`

(`TauCeti.IsAdaptedPseudoGradient.exact_unstableFrame_neg_stableNormal`); at a point of the
stable manifold of `x`, the unstable frame of `-X` and the normal coordinates of the stable manifold
of `X` form the short exact sequence `0 → V⁺ → T_y M → V⁻ → 0`
(`TauCeti.IsAdaptedPseudoGradient.exact_neg_unstableFrame_stableNormal`). Orientations of `V⁻` and
`V⁺` therefore orient `T_y M`, subspace first (`Orientation.ofExact`). At a point `y` of a
trajectory from `p` to `q` this gives two orientations of `T_y M`, one built from `op` and `op'` at
`p` and one built from `oq'` and `oq` at `q`. Whether they agree measures the twist of the
orientation local system of `M` along the trajectory, relative to the chosen orientations.

**The sign rule** (`TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign`). With `ε = 1` when the two
orientations of `T_y M` agree and `ε = -1` otherwise,

`sign_{-X}(y) = -(-1) ^ (ind_f q * ind_{-f} p) * ε * sign_X(y)`.

This is the pointwise form of the comparison between the integral Morse complex of `-f` and the
dual of the integral Morse complex of `f`. The linear algebra is
`Orientation.ite_map_eq_prod_of_exact`: the comparison maps of `f` and `-f` at `y` are the two
comparison maps of the pair of exact sequences, for the linear form `df_y`, since `d(-f) = -df`.

**Oriented manifolds.** Let `oM` orient `M`. Along the unstable manifold of `p`, the orientation of
`T_y M` built from `op` and `op'` (`TauCeti.IsAdaptedPseudoGradient.unstableFrameOrientation`) is
that of `M` at one point exactly when it is so at any other, in particular at `p`
(`TauCeti.IsAdaptedPseudoGradient.reindex_unstableFrameOrientation_eq_orientationAt_iff`), and
likewise along the stable manifold of `q` for the orientation built from `oq'` and `oq`
(`TauCeti.IsAdaptedPseudoGradient.stableNormalOrientation`,
`TauCeti.IsAdaptedPseudoGradient.reindex_stableNormalOrientation_eq_orientationAt_iff`). So when
`op` followed by `op'` orients `M` at `p` and `oq'` followed by `oq` orients `M` at `q`, both
orientations of `T_y M` are the orientation of `M`, `ε = 1`, and

`sign_{-X}(y) = -(-1) ^ (ind_f q * ind_{-f} p) * sign_X(y)`

(`TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign_of_orientationAt`). Summing over the
trajectories, the signed count of the trajectories of `-X` from `q` to `p` is
`-(-1) ^ (ind_f q * ind_{-f} p)` times that of the trajectories of `X` from `p` to `q`
(`TauCeti.IsAdaptedPseudoGradient.neg_signedTrajectoryCount_of_orientationAt`): the signed counts
of `-f` are those of `f`, transposed, up to these signs.

**One convention at every critical point.** The orientations above follow different conventions at
`p` and at `q`. Orientation data choose one orientation per critical point, so to assemble the
signed counts into Morse boundaries the same convention is needed at both ends: `op` followed by
`op'` orients `M` at `p`, and `oq` followed by `oq'` orients `M` at `q`. At `q` the two orders of
the factors differ by `(-1) ^ (ind_f q * ind_{-f} q)`
(`TauCeti.IsAdaptedPseudoGradient.stableNormalOrientation_self`), and then

`sign_{-X}(y) = (-1) ^ ind_f p * sign_X(y)`

(`TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign_of_unstableFrameOrientation`,
`TauCeti.IsAdaptedPseudoGradient.neg_signedTrajectoryCount_of_unstableFrameOrientation`). The
assembly into the integral Morse boundary of `-f` is
`TauCeti.Geometry.Manifold.Morse.Boundary.DualOrientation`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `neg_trajectorySign`: the sign rule.
* `neg_trajectorySign_of_orientationAt`: the sign rule on an oriented manifold, with `ε = 1`.
* `neg_signedTrajectoryCount_of_orientationAt`: the signed counts of `-X` are those of `X`,
  transposed, up to the signs `-(-1) ^ (ind_f q * ind_{-f} p)`.
* `neg_trajectorySign_of_unstableFrameOrientation`,
  `neg_signedTrajectoryCount_of_unstableFrameOrientation`: with one convention at every critical
  point, the signs and signed counts of `-X` are those of `X` times `(-1) ^ ind_f p`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations) and §3, Exercise 5 (the Morse complex of
  `-f` and Poincaré duality).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

section SignRule

variable {hX : IsAdaptedPseudoGradient f X} {p q : M} {φp : MorseChart E f p}
  {φq : MorseChart E f q}
  (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))

include hφp hφq

open scoped Classical in
/-- **The sign rule for the reversed pseudo-gradient.** Let `X` be a Morse–Smale pseudo-gradient
adapted to a Morse function `f`, `p` and `q` critical points with `ind p = ind q + 1`, and `y` a
point of a trajectory from `p` to `q`. Orient the coordinates of negative weight of the Morse charts
`φp` and `φq` by `op` and `oq`, and those of positive weight, the coordinates of negative weight of
the negated charts, by `op'` and `oq'`. Then the sign of the trajectory of `-X` from `q` to `p`
through `y` is the sign of the trajectory of `X` times `-(-1) ^ (ind_f q * ind_{-f} p)` times the
comparison of two orientations of `T_y M`: the one induced by `oq'` and `oq` through the stable
manifold of `q` (`stableNormalOrientation`), and the one induced by `op` and `op'` through the
unstable manifold of `p` (`unstableFrameOrientation`). -/
theorem neg_trajectorySign (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
    (hq : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f q)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (op' : Orientation ℝ ({i // (φp.neg hp).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (oq' : Orientation ℝ ({i // (φq.neg hq).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) q))) :
    (hX.neg hf).trajectorySign (φq.neg hq) (φp.neg hp) oq' op'
        (hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq) y =
      -(-1) ^ (manifoldMorseIndex 𝓘(ℝ, E) f q * manifoldMorseIndex 𝓘(ℝ, E) (-f) p) *
        (if Orientation.reindex ℝ (TangentSpace 𝓘(ℝ, E) y) (finCongr (by
              rw [hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq, hpq]; ring))
            (stableNormalOrientation hφq hf hq oq' oq hy.2) =
          unstableFrameOrientation hφp hf hp op op' hy.1 then 1 else -1) *
        hX.trajectorySign φp φq op oq hpq y := by
  have hb := bijective_trajectoryComparison hφp hφq hMS hf hpq hy
  have hb' := bijective_trajectoryComparison (φq.coord_mfderiv_neg hφq hq)
    (φp.coord_mfderiv_neg hφp hp) (hMS.neg hf) hf.neg
    (hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq)
    ⟨(hX.stableSet_eq_unstableSet_neg hf q).subset hy.2,
      (hX.unstableSet_eq_stableSet_neg hf p).subset hy.1⟩
  rw [trajectorySign_of_bijective hb, trajectorySign_of_bijective hb',
    MorseChart.trajectoryTargetOrientation_def, MorseChart.trajectoryTargetOrientation_def,
    stableNormalOrientation_def, unstableFrameOrientation_def]
  exact Orientation.ite_map_eq_prod_of_exact (l := (mvfderiv 𝓘(ℝ, E) f y).toLinearMap) _ _ _ _ _ _
    (eΦ := LinearEquiv.ofBijective _ hb) (fun v ↦ by simp [trajectoryComparison_apply])
    (eΨ := LinearEquiv.ofBijective _ hb') (fun v ↦ by simp [trajectoryComparison_apply])
    _ _ op op' oq' oq _ _ _ _

end SignRule

/-! ### The sign rule on an oriented manifold -/

section OrientedSignRule

variable {hX : IsAdaptedPseudoGradient f X} {p q : M} {φp : MorseChart E f p}
  {φq : MorseChart E f q}
  (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
  (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
  (hq : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f q)
  (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)))
  (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
  (op' : Orientation ℝ ({i // (φp.neg hp).weight i < 0} → ℝ)
    (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) p)))
  (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
  (oq' : Orientation ℝ ({i // (φq.neg hq).weight i < 0} → ℝ)
    (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) q)))
  -- `op` followed by `op'` orients `M` at `p`, and `oq'` followed by `oq` orients `M` at `q`.
  (hop : Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
      hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))
    (unstableFrameOrientation hφp hf hp op op' (hX.mem_unstableSet_self hp.mem_criticalPoints)) =
    oM.orientationAt p)
  (hoq : Orientation.reindex ℝ _ (finCongr
      hq.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank)
    (stableNormalOrientation hφq hf hq oq' oq (hX.mem_stableSet_self hq.mem_criticalPoints)) =
    oM.orientationAt q)

include hop hoq

/-- **The sign rule for the reversed pseudo-gradient on an oriented manifold.** Let `oM` orient
`M`, and choose the orientations so that, at `p`, the orientation `op` of the unstable manifold
followed by the orientation `op'` of the stable manifold is that of `M`, and at `q` the orientation
`oq'` of the stable manifold followed by the orientation `oq` of the unstable manifold is that of
`M`. Then every trajectory from `p` to `q` counts for `-f` with the sign
`-(-1) ^ (ind_f q * ind_{-f} p)` times its sign for `f`. -/
theorem neg_trajectorySign_of_orientationAt (hMS : hX.IsMorseSmale)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    {y : M} (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    (hX.neg hf).trajectorySign (φq.neg hq) (φp.neg hp) oq' op'
        (hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq) y =
      -(-1) ^ (manifoldMorseIndex 𝓘(ℝ, E) f q * manifoldMorseIndex 𝓘(ℝ, E) (-f) p) *
        hX.trajectorySign φp φq op oq hpq y := by
  -- Both orientations of `T_y M` compared by the sign rule are the orientation of `M`.
  have hP := (reindex_unstableFrameOrientation_eq_orientationAt_iff hφp hf hp oM _ op op' hy.1
    (hX.mem_unstableSet_self hp.mem_criticalPoints)).2 hop
  have hQ := (reindex_stableNormalOrientation_eq_orientationAt_iff hφq hf hq oM _ oq' oq hy.2
    (hX.mem_stableSet_self hq.mem_criticalPoints)).2 hoq
  have hcond : Orientation.reindex ℝ (TangentSpace 𝓘(ℝ, E) y) (finCongr (by
        rw [hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq, hpq]; ring))
      (stableNormalOrientation hφq hf hq oq' oq hy.2) =
      unstableFrameOrientation hφp hf hp op op' hy.1 := by
    refine (Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
      hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))).injective ?_
    rw [Orientation.reindex_finCongr_reindex_finCongr, hP]
    exact hQ
  rw [neg_trajectorySign hφp hφq hMS hf hp hq hpq hy op op' oq oq', ite_eq_left hcond, mul_one]

/-- **Signed counts for the reversed pseudo-gradient on an oriented manifold.** With the
orientations of `neg_trajectorySign_of_orientationAt`, the signed count of the trajectories of `-X`
from `q` to `p` is `-(-1) ^ (ind_f q * ind_{-f} p)` times the signed count of the trajectories of
`X` from `p` to `q`. -/
theorem neg_signedTrajectoryCount_of_orientationAt (hMS : hX.IsMorseSmale)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    (hX.neg hf).signedTrajectoryCount (φq.neg hq) (φp.neg hp) oq' op'
        (hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq) =
      -(-1) ^ (manifoldMorseIndex 𝓘(ℝ, E) f q * manifoldMorseIndex 𝓘(ℝ, E) (-f) p) *
        hX.signedTrajectoryCount φp φq op oq hpq := by
  rw [signedTrajectoryCount_def, signedTrajectoryCount_def, hX.neg_morseTrajectorySlice hf,
    mul_finsum_mem]
  refine finsum_mem_congr rfl fun y hy ↦ ?_
  exact neg_trajectorySign_of_orientationAt hφp hφq hf hp hq oM op op' oq oq' hop hoq hMS hpq
    ⟨(hX.mem_morseTrajectorySlice.1 hy).1, (hX.mem_morseTrajectorySlice.1 hy).2.1⟩

end OrientedSignRule

/-! ### The sign rule for one convention at every critical point -/

section UnstableFrameSignRule

variable {hX : IsAdaptedPseudoGradient f X} {p q : M} {φp : MorseChart E f p}
  {φq : MorseChart E f q}
  (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
  (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
  (hq : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f q)
  (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (Module.finrank ℝ E)))
  (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
  (op' : Orientation ℝ ({i // (φp.neg hp).weight i < 0} → ℝ)
    (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) p)))
  (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
  (oq' : Orientation ℝ ({i // (φq.neg hq).weight i < 0} → ℝ)
    (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) q)))
  -- At both `p` and `q`, the unstable orientation followed by the stable one orients `M`.
  (hop : Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
      hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))
    (unstableFrameOrientation hφp hf hp op op' (hX.mem_unstableSet_self hp.mem_criticalPoints)) =
    oM.orientationAt p)
  (hoq : Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
      hq.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))
    (unstableFrameOrientation hφq hf hq oq oq' (hX.mem_unstableSet_self hq.mem_criticalPoints)) =
    oM.orientationAt q)

include hop hoq

open scoped Classical in
/-- **The sign rule for the reversed pseudo-gradient, with one convention at every critical
point.** Let `oM` orient `M`, and choose the orientations so that at both `p` and `q` the
orientation of the unstable manifold of `X` followed by that of the stable manifold orients `M`.
Then every trajectory from `p` to `q` counts for `-f` with the sign `(-1) ^ ind_f p` times its sign
for `f`.

Unlike `neg_trajectorySign_of_orientationAt`, which asks for the opposite order of the factors at
`q`, this convention can be imposed at all critical points at once, as orientation data for `f`
and for `-f` require. At `q` the two orders differ by `(-1) ^ (ind_f q * ind_{-f} q)`
(`stableNormalOrientation_self`), which turns the sign `-(-1) ^ (ind_f q * ind_{-f} p)` of that
rule into `(-1) ^ ind_f p`. -/
theorem neg_trajectorySign_of_unstableFrameOrientation (hMS : hX.IsMorseSmale)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    {y : M} (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    (hX.neg hf).trajectorySign (φq.neg hq) (φp.neg hp) oq' op'
        (hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq) y =
      (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p * hX.trajectorySign φp φq op oq hpq y := by
  have hP := hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  -- Along `W^u(p)`, the frame orientation at `y` is that of `M`.
  have hPy := (reindex_unstableFrameOrientation_eq_orientationAt_iff hφp hf hp oM _ op op' hy.1
    (hX.mem_unstableSet_self hp.mem_criticalPoints)).2 hop
  -- Along `W^s(q)`, the frame orientation at `y` is `(-1) ^ k` times that of `M`.
  have hSy := reindex_stableNormalOrientation_eq_neg_one_pow_smul hφq hf hq oM oq oq' hoq hy.2
  set k := manifoldMorseIndex 𝓘(ℝ, E) f q * manifoldMorseIndex 𝓘(ℝ, E) (-f) q
  -- Hence the two orientations of `T_y M` compared by the sign rule differ by `(-1) ^ k`.
  have hε : (if Orientation.reindex ℝ (TangentSpace 𝓘(ℝ, E) y) (finCongr (by
          rw [hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq, hpq]; ring))
        (stableNormalOrientation hφq hf hq oq' oq hy.2) =
        unstableFrameOrientation hφp hf hp op op' hy.1 then (1 : ℤ) else -1) = (-1) ^ k := by
    rw [← (Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans hP))).injective.eq_iff,
      Orientation.reindex_finCongr_reindex_finCongr, hPy, hSy]
    rcases Nat.even_or_odd k with hk | hk
    · simp [hk.neg_one_pow]
    · simp [hk.neg_one_pow, Module.Ray.neg_units_smul, (Module.Ray.ne_neg_self _).symm]
  have hq' : manifoldMorseIndex 𝓘(ℝ, E) (-f) q = manifoldMorseIndex 𝓘(ℝ, E) (-f) p + 1 :=
    hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq
  rw [neg_trajectorySign hφp hφq hMS hf hp hq hpq hy op op' oq oq', hε]
  congr 1
  -- The exponents add up to `ind_f q` modulo two, since `ind_{-f} q = ind_{-f} p + 1`.
  have hexp : manifoldMorseIndex 𝓘(ℝ, E) f q * manifoldMorseIndex 𝓘(ℝ, E) (-f) p + k =
      2 * (manifoldMorseIndex 𝓘(ℝ, E) f q * manifoldMorseIndex 𝓘(ℝ, E) (-f) p) +
        manifoldMorseIndex 𝓘(ℝ, E) f q := by
    simp only [k, hq']
    ring
  rw [neg_mul, ← pow_add, hexp, pow_add, pow_mul, neg_one_sq, one_pow, one_mul,
    show manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 from hpq, pow_succ,
    mul_neg_one]

/-- **Signed counts for the reversed pseudo-gradient, with one convention at every critical
point.** With the orientations of `neg_trajectorySign_of_unstableFrameOrientation`, the signed
count of the trajectories of `-X` from `q` to `p` is `(-1) ^ ind_f p` times the signed count of the
trajectories of `X` from `p` to `q`. -/
theorem neg_signedTrajectoryCount_of_unstableFrameOrientation (hMS : hX.IsMorseSmale)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    (hX.neg hf).signedTrajectoryCount (φq.neg hq) (φp.neg hp) oq' op'
        (hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq) =
      (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p * hX.signedTrajectoryCount φp φq op oq hpq := by
  rw [signedTrajectoryCount_def, signedTrajectoryCount_def, hX.neg_morseTrajectorySlice hf,
    mul_finsum_mem]
  refine finsum_mem_congr rfl fun y hy ↦ ?_
  exact neg_trajectorySign_of_unstableFrameOrientation hφp hφq hf hp hq oM op op' oq oq' hop hoq
    hMS hpq ⟨(hX.mem_morseTrajectorySlice.1 hy).1, (hX.mem_morseTrajectorySlice.1 hy).2.1⟩

end UnstableFrameSignRule

end IsAdaptedPseudoGradient

end TauCeti
