/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Independence
public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere
public import TauCeti.Geometry.Manifold.ConnectedSum.Topology
public import TauCeti.Geometry.Manifold.Orientation.CoordinateBall
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The connected sum of connected oriented manifolds

The connected sum `TauCeti.ConnectedSum e₁ e₂` of two manifolds `M` and `N` is built from two
coordinate balls `e₁ : E → M` and `e₂ : E → N`, and its definition depends on them. For connected
oriented summands the dependence disappears up to diffeomorphism, as long as the two balls induce
opposite orientations of the model space `E`
(`TauCeti.ConnectedSum.nonempty_diffeomorph_of_isOrientationReversingAt`, a consequence of the disc
theorem). This file turns that well-definedness theorem into a construction which takes only the
oriented manifolds.

Let `E` be a nontrivial finite-dimensional real inner product space, and let `M` and `N` be
nonempty smooth manifolds without boundary modelled on `E`, with orientations `oM` and `oN`.
`TauCeti.OrientedConnectedSum oM oN` is the connected sum of `M` and `N` along coordinate balls
chosen once and for all: an orientation of `E`, a ball of `M` preserving orientation from it to
`oM`, and a ball of `N` reversing orientation from it to `oN`
(`TauCeti.Manifold.Orientation.exists_ball_isOrientationPreservingAt`). It is a smooth manifold
modelled on `E`, Hausdorff when the summands are, compact when they are, and connected when they
are and `E` has dimension at least two.

For connected, Hausdorff, σ-compact summands it is diffeomorphic to the connected sum along any
pair of balls inducing opposite orientations of `E`
(`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_connectedSum`). This is the statement that
`M # N` depends only on the oriented manifolds, and every other computation follows from it and
the corresponding statement for explicit balls:

* `M # N` is diffeomorphic to `N # M`
  (`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_comm`);
* reversing both orientations does not change `M # N`
  (`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_neg_neg`);
* the connected sum with the round sphere `Sⁿ`, for either of its orientations, is diffeomorphic
  to the other summand (`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_sphere`).

Reversing the orientation of only one summand can change the diffeomorphism type, as for
`ℂP² # ℂP²` and `ℂP² # -ℂP²`, so the construction genuinely takes the orientations.

## Main definitions

* `TauCeti.OrientedConnectedSum oM oN`: the connected sum of the oriented manifolds `M` and `N`.

## Main results

* `TauCeti.OrientedConnectedSum.nonempty_diffeomorph_connectedSum`: it is diffeomorphic to the
  connected sum along any pair of balls inducing opposite orientations of `E`.
* `TauCeti.OrientedConnectedSum.nonempty_diffeomorph_comm`: `M # N ≃ N # M`.
* `TauCeti.OrientedConnectedSum.nonempty_diffeomorph_neg_neg`: `(-M) # (-N) ≃ M # N`.
* `TauCeti.OrientedConnectedSum.nonempty_diffeomorph_sphere`: `M # Sⁿ ≃ M`.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6, Theorem 6.6, and
  Chapter 8, §2 (the connected sum of oriented manifolds).
-/

public section

noncomputable section

open Set Function Module Topology
open scoped Manifold ContDiff

namespace TauCeti

open Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E]
  {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [Nonempty M]
  {N : Type*} [TopologicalSpace N] [T1Space N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  [Nonempty N]
  {ι : Type*} [Fintype ι]

namespace OrientedConnectedSum

/-- The orientation of the model space `E` from which the balls of the connected sum are chosen,
the orientation of a basis of `E` indexed by `ι`. -/
def modelOrientation {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    (oX : Manifold.Orientation 𝓘(ℝ, E) X ι) : Manifold.Orientation 𝓘(ℝ, E) E ι := by
  classical
  exact model ((finBasisOfFinrankEq ℝ E oX.card_eq.symm).reindex
    (Fintype.equivFin ι).symm).orientation oX.card_eq

variable (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (oN : Manifold.Orientation 𝓘(ℝ, E) N ι)

/-- The coordinate ball of the first summand along which `M # N` is formed. It preserves
orientation from `TauCeti.OrientedConnectedSum.modelOrientation oM` to `oM`. -/
def leftBall : E → M :=
  (exists_ball_isOrientationPreservingAt (modelOrientation oM) oM (Classical.arbitrary M)).choose

/-- The coordinate ball of the second summand along which `M # N` is formed. It reverses
orientation from `TauCeti.OrientedConnectedSum.modelOrientation oM` to `oN`. -/
def rightBall : E → N :=
  (exists_ball_isOrientationPreservingAt (modelOrientation oM) (-oN)
    (Classical.arbitrary N)).choose

omit [T1Space M]

/-- The ball of the first summand is an open embedding. -/
theorem isOpenEmbedding_leftBall : IsOpenEmbedding (leftBall oM) :=
  (exists_ball_isOrientationPreservingAt (modelOrientation oM) oM
    (Classical.arbitrary M)).choose_spec.2.1

/-- The ball of the first summand is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_leftBall : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (leftBall oM) :=
  (exists_ball_isOrientationPreservingAt (modelOrientation oM) oM
    (Classical.arbitrary M)).choose_spec.2.2.1

/-- The ball of the first summand preserves orientation from the model orientation to `oM`. -/
theorem isOrientationPreservingAt_leftBall (v : E) :
    IsOrientationPreservingAt (modelOrientation oM) oM (leftBall oM) v :=
  (exists_ball_isOrientationPreservingAt (modelOrientation oM) oM
    (Classical.arbitrary M)).choose_spec.2.2.2 v

omit [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M] [T1Space N]

/-- The ball of the second summand is an open embedding. -/
theorem isOpenEmbedding_rightBall : IsOpenEmbedding (rightBall oM oN) :=
  (exists_ball_isOrientationPreservingAt (modelOrientation oM) (-oN)
    (Classical.arbitrary N)).choose_spec.2.1

/-- The ball of the second summand is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_rightBall : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (rightBall oM oN) :=
  (exists_ball_isOrientationPreservingAt (modelOrientation oM) (-oN)
    (Classical.arbitrary N)).choose_spec.2.2.1

/-- The ball of the second summand reverses orientation from the model orientation to `oN`. -/
theorem isOrientationReversingAt_rightBall (v : E) :
    IsOrientationReversingAt (modelOrientation oM) oN (rightBall oM oN) v :=
  (isOrientationPreservingAt_neg_right _ _ _ _).1
    ((exists_ball_isOrientationPreservingAt (modelOrientation oM) (-oN)
      (Classical.arbitrary N)).choose_spec.2.2.2 v)

end OrientedConnectedSum

open OrientedConnectedSum in
variable (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (oN : Manifold.Orientation 𝓘(ℝ, E) N ι) in
/-- **The connected sum `M # N` of oriented manifolds.** For nonempty smooth manifolds `M` and
`N` without boundary, modelled on a nontrivial finite-dimensional real inner product space `E` and
oriented by `oM` and `oN`, this is the connected sum `TauCeti.ConnectedSum e₁ e₂` along coordinate
balls `e₁ : E → M` and `e₂ : E → N` chosen so that `e₁` preserves and `e₂` reverses orientation
from a fixed orientation of `E`. For connected, Hausdorff, σ-compact summands its diffeomorphism
type does not depend on that choice
(`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_connectedSum`).

The definition is exposed because its topology, charts and smooth structure are those of
`TauCeti.ConnectedSum` along the chosen balls, and the instances below unfold it to reach them. -/
@[expose] def OrientedConnectedSum : Type _ :=
  ConnectedSum (leftBall oM) (rightBall oM oN)

namespace OrientedConnectedSum

variable (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (oN : Manifold.Orientation 𝓘(ℝ, E) N ι)

instance : TopologicalSpace (OrientedConnectedSum oM oN) :=
  inferInstanceAs (TopologicalSpace (ConnectedSum (leftBall oM) (rightBall oM oN)))

/-- The charts of the connected sum, those of `TauCeti.ConnectedSum.chartedSpace`. -/
instance : ChartedSpace E (OrientedConnectedSum oM oN) :=
  ConnectedSum.chartedSpace (isOpenEmbedding_leftBall oM) (isOpenEmbedding_rightBall oM oN)

/-- The connected sum of oriented smooth manifolds is a smooth manifold. -/
instance : IsManifold 𝓘(ℝ, E) ∞ (OrientedConnectedSum oM oN) :=
  ConnectedSum.isManifold (n := ⊤) (isOpenEmbedding_leftBall oM)
    (isOpenEmbedding_rightBall oM oN) (isLocalDiffeomorph_leftBall oM)
    (isLocalDiffeomorph_rightBall oM oN)

/-- The connected sum of Hausdorff manifolds is Hausdorff. -/
instance [T2Space M] [T2Space N] : T2Space (OrientedConnectedSum oM oN) :=
  ConnectedSum.t2Space (isOpenEmbedding_leftBall oM) (isOpenEmbedding_rightBall oM oN)

/-- The connected sum of compact manifolds is compact. -/
instance [CompactSpace M] [CompactSpace N] : CompactSpace (OrientedConnectedSum oM oN) :=
  ConnectedSum.compactSpace (isOpenEmbedding_leftBall oM) (isOpenEmbedding_rightBall oM oN)

/-- The connected sum of connected manifolds of dimension at least two is connected. -/
theorem connectedSpace [ConnectedSpace M] [ConnectedSpace N] (h : 1 < Module.rank ℝ E) :
    ConnectedSpace (OrientedConnectedSum oM oN) :=
  ConnectedSum.connectedSpace h (isOpenEmbedding_leftBall oM) (isOpenEmbedding_rightBall oM oN)

variable [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

/-- **The oriented connected sum is the connected sum along any compatible balls.** Let `M` and
`N` be connected, Hausdorff, σ-compact, and oriented by `oM` and `oN`. Let `e₁ : E → M` and
`e₂ : E → N` be coordinate balls, open embeddings and smooth local diffeomorphisms, inducing
opposite orientations of `E` at `0`: for some orientation `o` of `E`, `e₁` preserves orientation
from `o` to `oM` and `e₂` reverses it from `o` to `oN`. Then `M # N` is diffeomorphic to the
connected sum along `e₁` and `e₂`. -/
theorem nonempty_diffeomorph_connectedSum {e₁ : E → M} {e₂ : E → N} (h₁ : IsOpenEmbedding e₁)
    (h₂ : IsOpenEmbedding e₂) (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₁)
    (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₂) (o : Manifold.Orientation 𝓘(ℝ, E) E ι)
    (hf₁ : o.IsOrientationPreservingAt oM e₁ 0) (hf₂ : o.IsOrientationReversingAt oN e₂ 0) :
    letI := ConnectedSum.chartedSpace (H := E) h₁ h₂
    Nonempty (OrientedConnectedSum oM oN ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ ConnectedSum e₁ e₂) :=
  ConnectedSum.nonempty_diffeomorph_of_isOrientationReversingAt (isOpenEmbedding_leftBall oM)
    (isOpenEmbedding_rightBall oM oN) h₁ h₂ (isLocalDiffeomorph_leftBall oM)
    (isLocalDiffeomorph_rightBall oM oN) d₁ d₂ (modelOrientation oM) o oM oN
    (isOrientationPreservingAt_leftBall oM 0) (isOrientationReversingAt_rightBall oM oN 0) hf₁ hf₂

/-- **Reversing both orientations does not change the connected sum**: `(-M) # (-N)` is
diffeomorphic to `M # N`. -/
theorem nonempty_diffeomorph_neg_neg :
    Nonempty (OrientedConnectedSum (-oM) (-oN) ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯
      OrientedConnectedSum oM oN) :=
  nonempty_diffeomorph_connectedSum (-oM) (-oN) (isOpenEmbedding_leftBall oM)
    (isOpenEmbedding_rightBall oM oN) (isLocalDiffeomorph_leftBall oM)
    (isLocalDiffeomorph_rightBall oM oN) (-modelOrientation oM)
    (by simpa using isOrientationPreservingAt_leftBall oM 0)
    (by simpa using isOrientationReversingAt_rightBall oM oN 0)

/-- **The connected sum is commutative**: `M # N` is diffeomorphic to `N # M`. -/
theorem nonempty_diffeomorph_comm :
    Nonempty (OrientedConnectedSum oM oN ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯
      OrientedConnectedSum oN oM) := by
  -- The balls of `M # N`, exchanged, induce opposite orientations of `E` for `N` and `M`, read
  -- from the opposite orientation of `E`.
  let := ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_leftBall oM)
    (isOpenEmbedding_rightBall oM oN)
  let := ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rightBall oM oN)
    (isOpenEmbedding_leftBall oM)
  obtain ⟨φ⟩ := nonempty_diffeomorph_connectedSum oN oM (isOpenEmbedding_rightBall oM oN)
    (isOpenEmbedding_leftBall oM) (isLocalDiffeomorph_rightBall oM oN)
    (isLocalDiffeomorph_leftBall oM) (-modelOrientation oM)
    (by simpa using isOrientationReversingAt_rightBall oM oN 0)
    (by simpa using isOrientationPreservingAt_leftBall oM 0)
  exact ⟨(ConnectedSum.commDiffeomorph (n := ⊤) (isOpenEmbedding_leftBall oM)
    (isOpenEmbedding_rightBall oM oN) (isLocalDiffeomorph_leftBall oM)
    (isLocalDiffeomorph_rightBall oM oN)).trans φ.symm⟩

section Sphere

variable {n : ℕ} [NeZero n] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Fact (finrank ℝ F = n + 1)] [Nonempty (Metric.sphere (0 : F) 1)]
  {X : Type*} [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X] [ConnectedSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]

/-- **The connected sum with a sphere is trivial.** For a connected, Hausdorff, σ-compact smooth
`n`-manifold `X` with an orientation `oX`, `n ≥ 1`, and either orientation `oS` of the unit sphere
`Sⁿ` of an `(n + 1)`-dimensional real inner product space `F`, the connected sum `X # Sⁿ` is
diffeomorphic to `X`. The instance `Nonempty Sⁿ` is needed only to form the connected sum, which
chooses a ball about a point of each summand. -/
theorem nonempty_diffeomorph_sphere (oX : Manifold.Orientation (𝓡 n) X ι)
    (oS : Manifold.Orientation (𝓡 n) (Metric.sphere (0 : F) 1) ι) :
    Nonempty (OrientedConnectedSum oX oS ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ X) := by
  have : FiniteDimensional ℝ F := .of_fact_finrank_eq_succ n
  have hrank : 1 < Module.rank ℝ F := by
    rw [← finrank_eq_rank, Fact.out (p := finrank ℝ F = n + 1)]
    exact_mod_cast Nat.lt_add_of_pos_left (Nat.pos_of_ne_zero (NeZero.ne n))
  have : ConnectedSpace (Metric.sphere (0 : F) 1) :=
    isConnected_iff_connectedSpace.1 (isConnected_sphere hrank 0 zero_le_one)
  -- The ball `sphereBall v` of the sphere either reverses orientation from an orientation `o₀` of
  -- the model space, or it reverses orientation from `-o₀`.
  set v : Metric.sphere (0 : F) 1 := Classical.arbitrary _
  have hs := isLocalDiffeomorph_sphereBall (F := F) (n := n) v ∞
  set o₀ := modelOrientation oX
  obtain ⟨o, ho⟩ : ∃ o : Manifold.Orientation (𝓡 n) (EuclideanSpace ℝ (Fin n)) ι,
      o.IsOrientationReversingAt oS (sphereBall v) 0 := by
    rcases isOrientationPreservingAt_or_isOrientationReversingAt o₀ oS (sphereBall v) 0
      ((hs 0).mfderivToContinuousLinearEquiv (by simp))
      ((hs 0).mfderivToContinuousLinearEquiv_coe (by simp)) with h | h
    · exact ⟨-o₀, by simpa using h⟩
    · exact ⟨o₀, h⟩
  -- A ball of `X` preserving orientation from `o`, and the sphere with that ball is trivial.
  obtain ⟨e, -, he, de, hpres⟩ := exists_ball_isOrientationPreservingAt o oX (Classical.arbitrary X)
  let := ConnectedSum.chartedSpace (H := EuclideanSpace ℝ (Fin n)) he (isOpenEmbedding_sphereBall v)
  obtain ⟨φ⟩ := nonempty_diffeomorph_connectedSum oX oS he (isOpenEmbedding_sphereBall v) de hs o
    (hpres 0) ho
  exact ⟨φ.trans (connectedSumSphereDiffeomorph (k := ⊤) he de v)⟩

end Sphere

end OrientedConnectedSum

end TauCeti
