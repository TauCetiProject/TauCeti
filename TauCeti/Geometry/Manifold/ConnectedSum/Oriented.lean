/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Independence
public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere
public import TauCeti.Geometry.Manifold.ConnectedSum.Topology
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Analysis.InnerProductSpace.Reflection
import TauCeti.Geometry.Manifold.Orientation.CoordinateBall

/-!
# The oriented connected sum of connected oriented manifolds

The connected sum `TauCeti.ConnectedSum e₁ e₂` takes its coordinate balls `e₁ : E → M` and
`e₂ : E → N` as data. For connected, Hausdorff, σ-compact oriented manifolds `M` and `N` without
boundary, modelled on a finite-dimensional real inner product space `E`, its diffeomorphism type
depends on the balls only through their orientation behaviour at the centres
(`TauCeti.ConnectedSum.nonempty_diffeomorph_of_isOrientationPreservingAt`). This file picks the
balls, so that for such summands the oriented connected sum `M # N` becomes a manifold determined
up to diffeomorphism by the two oriented summands alone.

* **Choosing the balls.** Every point of a smooth manifold without boundary modelled on a
  nontrivial `E` is the centre of a coordinate ball which preserves any given orientations of `E`
  and of the manifold at its centre
  (`Manifold.Orientation.exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt`).
* **The oriented connected sum.** For orientations `oM` of `M` and `oN` of `N`,
  `TauCeti.OrientedConnectedSum oM oN` is the connected sum along a chosen ball of `M` and a chosen
  ball of `N` which, for some orientation of `E`, respectively preserve and reverse the
  orientations at their centres. It is a smooth manifold, Hausdorff when `M` and `N` are, compact
  when they are, and connected when they are and `E` has dimension at least two.
* **It does not depend on the choice.** For connected, Hausdorff, σ-compact summands, the oriented
  connected sum is diffeomorphic to the connected sum along any two balls which, for some
  orientation of `E`, preserve and reverse the orientations at their centres
  (`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_connectedSum`). When that orientation of `E`
  is the opposite of the one the chosen balls use, both balls are first rotated by a reflection,
  which does not change the connected sum
  (`TauCeti.ConnectedSum.compLinearIsometryEquivDiffeomorph`). Consequently the oriented connected
  sum is commutative (`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_comm`) and unchanged by
  reversing both orientations (`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_neg`).
* **The connected sum with a sphere is trivial.** If `N` is covered by a ball and a complementary
  ball, as a round sphere is, then `M # N` is diffeomorphic to `M` for every orientation of `N`
  (`TauCeti.IsComplementaryBall.nonempty_diffeomorph_orientedConnectedSum`). In particular
  `M # Sⁿ ≃ M` (`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_sphere`).

## Main definitions

* `TauCeti.OrientedConnectedSum oM oN`: the oriented connected sum of `M` and `N`.

## Main results

* `TauCeti.OrientedConnectedSum.nonempty_diffeomorph_connectedSum`: the oriented connected sum is
  diffeomorphic to the connected sum along any two balls with the right orientation behaviour.
* `TauCeti.OrientedConnectedSum.nonempty_diffeomorph_comm`: `M # N ≃ N # M`.
* `TauCeti.OrientedConnectedSum.nonempty_diffeomorph_sphere`: `M # Sⁿ ≃ M`.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1.
-/

public section

noncomputable section

open Set Function Topology Metric Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  {ι : Type*} [Fintype ι]

namespace OrientedConnectedSum

variable [Nontrivial E] [Nonempty M] [Nonempty N]
  (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (oN : Manifold.Orientation 𝓘(ℝ, E) N ι)

/-- A ball of `M` and a ball of `N` which, for some orientation of `E`, respectively preserve and
reverse the orientations `oM` and `oN` at their centres. -/
private theorem exists_balls : ∃ p : (E → M) × (E → N),
    IsOpenEmbedding p.1 ∧ IsOpenEmbedding p.2 ∧ IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ p.1 ∧
      IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ p.2 ∧
      ∃ oE : Manifold.Orientation 𝓘(ℝ, E) E ι,
        oE.IsOrientationPreservingAt oM p.1 0 ∧ oE.IsOrientationReversingAt oN p.2 0 := by
  classical
  have hι : Fintype.card ι = finrank ℝ E := oM.card_eq
  let oE : Manifold.Orientation 𝓘(ℝ, E) E ι := Manifold.Orientation.model
    ((finBasisOfFinrankEq ℝ E hι.symm).reindex (Fintype.equivFin ι).symm).orientation hι
  obtain ⟨e₁, -, h₁, d₁, hf₁⟩ :=
    Manifold.Orientation.exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt oE oM
      (Classical.arbitrary M)
  obtain ⟨e₂, -, h₂, d₂, hf₂⟩ :=
    Manifold.Orientation.exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt oE
      (-oN) (Classical.arbitrary N)
  exact ⟨(e₁, e₂), h₁, h₂, d₁, d₂, oE, hf₁, by simpa using hf₂⟩

/-- The coordinate ball of `M` along which the oriented connected sum of `M` and `N` is formed. -/
def ballLeft : E → M :=
  (exists_balls oM oN).choose.1

/-- The coordinate ball of `N` along which the oriented connected sum of `M` and `N` is formed. -/
def ballRight : E → N :=
  (exists_balls oM oN).choose.2

theorem isOpenEmbedding_ballLeft : IsOpenEmbedding (ballLeft oM oN) :=
  (exists_balls oM oN).choose_spec.1

theorem isOpenEmbedding_ballRight : IsOpenEmbedding (ballRight oM oN) :=
  (exists_balls oM oN).choose_spec.2.1

theorem isLocalDiffeomorph_ballLeft : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (ballLeft oM oN) :=
  (exists_balls oM oN).choose_spec.2.2.1

theorem isLocalDiffeomorph_ballRight : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (ballRight oM oN) :=
  (exists_balls oM oN).choose_spec.2.2.2.1

/-- For some orientation of `E`, the ball of `M` preserves and the ball of `N` reverses the
orientations at their centres. -/
theorem exists_isOrientationPreservingAt_ballLeft :
    ∃ oE : Manifold.Orientation 𝓘(ℝ, E) E ι, oE.IsOrientationPreservingAt oM (ballLeft oM oN) 0 ∧
      oE.IsOrientationReversingAt oN (ballRight oM oN) 0 :=
  (exists_balls oM oN).choose_spec.2.2.2.2

end OrientedConnectedSum

variable [Nontrivial E] [Nonempty M] [Nonempty N] [T1Space M] [T1Space N]

/-- The **oriented connected sum** `M # N` of the oriented manifolds `(M, oM)` and `(N, oN)`: the
connected sum along a ball of `M` and a ball of `N` which, for some orientation of `E`, preserve
and reverse the orientations at their centres. For connected, Hausdorff, σ-compact summands it
does not depend on the balls, up to diffeomorphism
(`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_connectedSum`). -/
def OrientedConnectedSum (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (oN : Manifold.Orientation 𝓘(ℝ, E) N ι) : Type _ :=
  ConnectedSum (OrientedConnectedSum.ballLeft oM oN) (OrientedConnectedSum.ballRight oM oN)

namespace OrientedConnectedSum

variable (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (oN : Manifold.Orientation 𝓘(ℝ, E) N ι)

instance : TopologicalSpace (OrientedConnectedSum oM oN) :=
  inferInstanceAs (TopologicalSpace (ConnectedSum (ballLeft oM oN) (ballRight oM oN)))

/-- The charts of the oriented connected sum, those of the connected sum along its balls. -/
instance : ChartedSpace E (OrientedConnectedSum oM oN) :=
  letI := ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_ballLeft oM oN)
    (isOpenEmbedding_ballRight oM oN)
  inferInstanceAs (ChartedSpace E (ConnectedSum (ballLeft oM oN) (ballRight oM oN)))

instance : IsManifold 𝓘(ℝ, E) ∞ (OrientedConnectedSum oM oN) :=
  letI := ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_ballLeft oM oN)
    (isOpenEmbedding_ballRight oM oN)
  haveI := ConnectedSum.isManifold (isOpenEmbedding_ballLeft oM oN)
    (isOpenEmbedding_ballRight oM oN) (isLocalDiffeomorph_ballLeft oM oN)
    (isLocalDiffeomorph_ballRight oM oN)
  inferInstanceAs (IsManifold 𝓘(ℝ, E) ∞ (ConnectedSum (ballLeft oM oN) (ballRight oM oN)))

instance [T2Space M] [T2Space N] : T2Space (OrientedConnectedSum oM oN) :=
  haveI := ConnectedSum.t2Space (isOpenEmbedding_ballLeft oM oN) (isOpenEmbedding_ballRight oM oN)
  inferInstanceAs (T2Space (ConnectedSum (ballLeft oM oN) (ballRight oM oN)))

instance [CompactSpace M] [CompactSpace N] : CompactSpace (OrientedConnectedSum oM oN) :=
  haveI := ConnectedSum.compactSpace (isOpenEmbedding_ballLeft oM oN)
    (isOpenEmbedding_ballRight oM oN)
  inferInstanceAs (CompactSpace (ConnectedSum (ballLeft oM oN) (ballRight oM oN)))

/-- The oriented connected sum of connected manifolds of dimension at least two is connected. -/
theorem connectedSpace [ConnectedSpace M] [ConnectedSpace N] (h : 1 < Module.rank ℝ E) :
    ConnectedSpace (OrientedConnectedSum oM oN) :=
  haveI := ConnectedSum.connectedSpace h (isOpenEmbedding_ballLeft oM oN)
    (isOpenEmbedding_ballRight oM oN)
  inferInstanceAs (ConnectedSpace (ConnectedSum (ballLeft oM oN) (ballRight oM oN)))

section Independence

variable [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]
  [T2Space N] [SigmaCompactSpace N] [PreconnectedSpace N]

/-- **The oriented connected sum does not depend on its balls.** Let `M` and `N` be connected,
Hausdorff, σ-compact smooth manifolds without boundary, oriented by `oM` and `oN`. Let
`e₁ : E → M` and `e₂ : E → N` be balls, open embeddings and smooth local diffeomorphisms, which for
some orientation `oE` of `E` respectively preserve and reverse the orientations at `0`. Then the
oriented connected sum of `M` and `N` is diffeomorphic to the connected sum along `e₁` and
`e₂`. -/
theorem nonempty_diffeomorph_connectedSum {e₁ : E → M} {e₂ : E → N} (h₁ : IsOpenEmbedding e₁)
    (h₂ : IsOpenEmbedding e₂) (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₁)
    (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₂) (oE : Manifold.Orientation 𝓘(ℝ, E) E ι)
    (hf₁ : oE.IsOrientationPreservingAt oM e₁ 0) (hf₂ : oE.IsOrientationReversingAt oN e₂ 0) :
    letI := ConnectedSum.chartedSpace (H := E) h₁ h₂
    Nonempty (OrientedConnectedSum oM oN ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ ConnectedSum e₁ e₂) := by
  let := ConnectedSum.chartedSpace (H := E) h₁ h₂
  obtain ⟨oE₀, hl, hr⟩ := exists_isOrientationPreservingAt_ballLeft oM oN
  rcases oE.eq_or_eq_neg oE₀ with rfl | rfl
  · exact ConnectedSum.nonempty_diffeomorph_of_isOrientationPreservingAt
      (isOpenEmbedding_ballLeft oM oN) (isOpenEmbedding_ballRight oM oN) h₁ h₂
      (isLocalDiffeomorph_ballLeft oM oN) (isLocalDiffeomorph_ballRight oM oN) d₁ d₂
      oE oE oM (-oN) hl hf₁ (by simpa using hr) (by simpa using hf₂)
  -- The balls `e₁` and `e₂` use the opposite orientation of `E` from the chosen balls: rotating
  -- both by a reflection of `E` brings them to the orientation of the chosen balls.
  obtain ⟨R, hR⟩ := exists_det_eq_neg_one (F := E)
  have h₁' := h₁.comp_linearIsometryEquiv R
  have h₂' := h₂.comp_linearIsometryEquiv R
  have hf₂' : oE₀.IsOrientationReversingAt oN (e₂ ∘ R) 0 :=
    Manifold.Orientation.isOrientationReversingAt_comp_of_det_eq_neg_one (by simpa using hf₂) hR
  let := ConnectedSum.chartedSpace (H := E) h₁' h₂'
  obtain ⟨φ⟩ := ConnectedSum.nonempty_diffeomorph_of_isOrientationPreservingAt
    (isOpenEmbedding_ballLeft oM oN) (isOpenEmbedding_ballRight oM oN) h₁' h₂'
    (isLocalDiffeomorph_ballLeft oM oN) (isLocalDiffeomorph_ballRight oM oN)
    (d₁.comp_linearIsometryEquiv R) (d₂.comp_linearIsometryEquiv R) oE₀ oE₀ oM (-oN) hl
    (Manifold.Orientation.isOrientationPreservingAt_comp_of_det_eq_neg_one (by simpa using hf₁)
      hR)
    (by simpa using hr) (by simpa using hf₂')
  let := ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_ballLeft oM oN)
    (isOpenEmbedding_ballRight oM oN)
  exact ⟨φ.trans (ConnectedSum.compLinearIsometryEquivDiffeomorph R h₁ h₂ d₁ d₂).symm⟩

/-- **The oriented connected sum is commutative**: `M # N` is diffeomorphic to `N # M`. -/
theorem nonempty_diffeomorph_comm :
    Nonempty (OrientedConnectedSum oM oN ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ OrientedConnectedSum oN oM) := by
  obtain ⟨oE, hl, hr⟩ := exists_isOrientationPreservingAt_ballLeft oM oN
  let := ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_ballLeft oM oN)
    (isOpenEmbedding_ballRight oM oN)
  let := ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_ballRight oM oN)
    (isOpenEmbedding_ballLeft oM oN)
  -- With the opposite orientation of `E`, the ball of `N` preserves and the ball of `M` reverses.
  obtain ⟨φ⟩ := nonempty_diffeomorph_connectedSum oN oM (isOpenEmbedding_ballRight oM oN)
    (isOpenEmbedding_ballLeft oM oN) (isLocalDiffeomorph_ballRight oM oN)
    (isLocalDiffeomorph_ballLeft oM oN) (-oE) (by simpa using hr) (by simpa using hl)
  exact ⟨(ConnectedSum.commDiffeomorph (isOpenEmbedding_ballLeft oM oN)
    (isOpenEmbedding_ballRight oM oN) (isLocalDiffeomorph_ballLeft oM oN)
    (isLocalDiffeomorph_ballRight oM oN)).trans φ.symm⟩

/-- Reversing both orientations does not change the oriented connected sum. -/
theorem nonempty_diffeomorph_neg :
    Nonempty (OrientedConnectedSum (-oM) (-oN) ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯
      OrientedConnectedSum oM oN) := by
  obtain ⟨oE, hl, hr⟩ := exists_isOrientationPreservingAt_ballLeft oM oN
  exact nonempty_diffeomorph_connectedSum (-oM) (-oN) (isOpenEmbedding_ballLeft oM oN)
    (isOpenEmbedding_ballRight oM oN) (isLocalDiffeomorph_ballLeft oM oN)
    (isLocalDiffeomorph_ballRight oM oN) (-oE) (by simpa using hl) (by simpa using hr)

end Independence

end OrientedConnectedSum

namespace IsComplementaryBall

variable [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]
  [T2Space N] [SigmaCompactSpace N] [PreconnectedSpace N]
  (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (oN : Manifold.Orientation 𝓘(ℝ, E) N ι)

/-- **The connected sum with a sphere is trivial.** If `N` is covered by a ball `s` and a
complementary ball `s'`, both smooth local diffeomorphisms, as a round sphere is, then the oriented
connected sum `M # N` is diffeomorphic to `M`, for all orientations of `M` and `N`. -/
theorem nonempty_diffeomorph_orientedConnectedSum {s s' : E → N} (h : IsComplementaryBall s s')
    (hs : IsOpenEmbedding s) (ds : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ s)
    (ds' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ s') :
    Nonempty (OrientedConnectedSum oM oN ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) := by
  obtain ⟨oE, hl, -⟩ := OrientedConnectedSum.exists_isOrientationPreservingAt_ballLeft oM oN
  have he := OrientedConnectedSum.isOpenEmbedding_ballLeft oM oN
  have de := OrientedConnectedSum.isLocalDiffeomorph_ballLeft oM oN
  obtain hp | hr := oE.isOrientationPreservingAt_or_isOrientationReversingAt oN s 0
    ((ds 0).mfderivToContinuousLinearEquiv (by simp))
    ((ds 0).mfderivToContinuousLinearEquiv_coe _)
  · -- The ball `s` preserves orientations: rotate the sphere's two balls by a reflection.
    obtain ⟨R, hR⟩ := exists_det_eq_neg_one (F := E)
    have hsR := hs.comp_linearIsometryEquiv R
    let := ConnectedSum.chartedSpace (H := E) he hsR
    obtain ⟨φ⟩ := OrientedConnectedSum.nonempty_diffeomorph_connectedSum oM oN he hsR de
      (ds.comp_linearIsometryEquiv R) oE hl
      (Manifold.Orientation.isOrientationReversingAt_comp_of_det_eq_neg_one (by simpa using hp) hR)
    exact ⟨φ.trans ((h.comp_linearIsometryEquiv R).connectedSumDiffeomorph he hsR de
      (ds.comp_linearIsometryEquiv R) (ds'.comp_linearIsometryEquiv R))⟩
  · let := ConnectedSum.chartedSpace (H := E) he hs
    obtain ⟨φ⟩ := OrientedConnectedSum.nonempty_diffeomorph_connectedSum oM oN he hs de ds oE hl hr
    exact ⟨φ.trans (h.connectedSumDiffeomorph he hs de ds ds')⟩

end IsComplementaryBall

namespace OrientedConnectedSum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ} [NeZero n]
  [Fact (finrank ℝ F = n + 1)] [Nonempty (sphere (0 : F) 1)]
  {X : Type*} [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X] [PreconnectedSpace X]
  [Nonempty X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]

/-- **`X # Sⁿ ≃ X`**: the oriented connected sum of a connected, Hausdorff, σ-compact smooth
`n`-manifold `X`, for `n ≥ 1`, with the unit sphere `Sⁿ`, is diffeomorphic to `X`, for all
orientations of `X` and of the sphere. -/
theorem nonempty_diffeomorph_sphere (oX : Manifold.Orientation (𝓡 n) X ι)
    (oS : Manifold.Orientation (𝓡 n) (sphere (0 : F) 1) ι) :
    Nonempty (OrientedConnectedSum oX oS ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ X) := by
  have : FiniteDimensional ℝ F := .of_fact_finrank_eq_succ n
  have : PreconnectedSpace (sphere (0 : F) 1) := Subtype.preconnectedSpace <|
    isPreconnected_sphere (by
      rw [← Module.finrank_eq_rank, Fact.out (p := finrank ℝ F = n + 1)]
      exact_mod_cast Nat.lt_add_of_pos_left (Nat.pos_of_ne_zero (NeZero.ne n))) 0 1
  obtain ⟨v⟩ := ‹Nonempty (sphere (0 : F) 1)›
  exact (isComplementaryBall_sphereBall v).nonempty_diffeomorph_orientedConnectedSum oX oS
    (isOpenEmbedding_sphereBall v) (isLocalDiffeomorph_sphereBall v ∞)
    (isLocalDiffeomorph_neg_sphereBall_neg v ∞)

end OrientedConnectedSum

end TauCeti
