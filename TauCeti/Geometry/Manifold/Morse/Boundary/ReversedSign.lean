/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Sign
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
dual of the integral Morse complex of `f`. On an oriented manifold, with `op'` and `oq'` chosen so
that `op` followed by `op'` and `oq'` followed by `oq` orient `M` at `p` and at `q`, both
orientations of `T_y M` should be the orientation of `M`, making `ε = 1` and the boundary of `-f`
the transpose of the boundary of `f` up to the signs `-(-1) ^ (ind_f q * ind_{-f} p)`; carrying
the orientations along the flow to prove this is not done here. The linear algebra is
`Orientation.ite_map_eq_prod_of_exact`: the comparison maps of `f` and `-f` at `y` are the two
comparison maps of the pair of exact sequences, for the linear form `df_y`, since `d(-f) = -df`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign`: the sign rule.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations) and §3, Exercise 5 (the Morse complex of
  `-f` and Poincaré duality).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

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
manifold of `q`, and the one induced by `op` and `op'` through the unstable manifold of `p`. -/
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
            (Orientation.ofExact
              (injective_unstableFrame_of_mem (hX := hX.neg hf) (φq.coord_mfderiv_neg hφq hq)
                hf.neg ((hX.stableSet_eq_unstableSet_neg hf q).subset hy.2))
              (exact_neg_unstableFrame_stableNormal hφq hf hq hy.2)
              (surjective_stableNormal_of_mem hφq hy.2) oq' oq
              (φq.neg hq).finrank_negativeWeight_fun φq.finrank_negativeWeight_fun) =
          Orientation.ofExact (injective_unstableFrame_of_mem hφp hf hy.1)
            (exact_unstableFrame_neg_stableNormal hφp hf hp hy.1)
            (surjective_stableNormal_of_mem (hX := hX.neg hf) (φp.coord_mfderiv_neg hφp hp)
              ((hX.unstableSet_eq_stableSet_neg hf p).subset hy.1)) op op'
            φp.finrank_negativeWeight_fun (φp.neg hp).finrank_negativeWeight_fun then 1
          else -1) *
        hX.trajectorySign φp φq op oq hpq y := by
  have hb := bijective_trajectoryComparison hφp hφq hMS hf hpq hy
  have hb' := bijective_trajectoryComparison (φq.coord_mfderiv_neg hφq hq)
    (φp.coord_mfderiv_neg hφp hp) (hMS.neg hf) hf.neg
    (hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq)
    ⟨(hX.stableSet_eq_unstableSet_neg hf q).subset hy.2,
      (hX.unstableSet_eq_stableSet_neg hf p).subset hy.1⟩
  rw [trajectorySign_of_bijective hb, trajectorySign_of_bijective hb',
    MorseChart.trajectoryTargetOrientation_def, MorseChart.trajectoryTargetOrientation_def]
  exact Orientation.ite_map_eq_prod_of_exact (l := (mvfderiv 𝓘(ℝ, E) f y).toLinearMap) _ _ _ _ _ _
    (eΦ := LinearEquiv.ofBijective _ hb) (fun v ↦ by simp [trajectoryComparison_apply])
    (eΨ := LinearEquiv.ofBijective _ hb') (fun v ↦ by simp [trajectoryComparison_apply])
    _ _ op op' oq' oq _ _ _ _

end IsAdaptedPseudoGradient

end TauCeti
