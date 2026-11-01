/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Independence
public import TauCeti.Geometry.Manifold.ConnectedSum.Orientation
public import TauCeti.Geometry.Manifold.ConnectedSum.Topology
import TauCeti.Geometry.Manifold.CoordinateBall
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Orientation.Reflection

/-!
# The oriented connected sum of two connected oriented manifolds

The connected sum `TauCeti.ConnectedSum e₁ e₂` takes its coordinate balls `e₁ : E → M` and
`e₂ : E → N` as data. For connected oriented summands its diffeomorphism type depends on the balls
only through the orientations they induce at their centres
(`TauCeti.ConnectedSum.nonempty_diffeomorph_of_isOrientationPreservingAt`). This file uses that
theorem to define the connected sum of two oriented manifolds without choosing balls,
`TauCeti.OrientedConnectedSum oM oN`, and shows that it is well defined: it is diffeomorphic to
the connected sum along any pair of balls inducing opposite orientations of `E`
(`TauCeti.OrientedConnectedSum.nonempty_diffeomorph`).

For orientations `oM` of `M` and `oN` of `N`, the oriented connected sum is the connected sum
along a ball of `M` preserving orientation from an orientation `o` of `E` to `oM`, and a ball of
`N` reversing orientation from `o` to `oN`; such balls exist about every point
(`TauCeti.exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt`). It is a smooth
manifold, Hausdorff, compact or connected when the summands are. For connected, Hausdorff,
σ-compact summands, any other pair of balls `e₁`, `e₂` such that `e₁` preserves and `e₂` reverses
orientation at `0` from a common orientation of `E` gives a diffeomorphic connected sum
(`TauCeti.OrientedConnectedSum.nonempty_diffeomorph`). When the common orientation
of `E` is not the one used to choose the balls, both balls are first rotated by a reflection of
`E` (`TauCeti.ConnectedSum.nonempty_diffeomorph_of_comp_linearIsometryEquiv`). In particular the
oriented connected sum is commutative up to diffeomorphism
(`TauCeti.OrientedConnectedSum.nonempty_diffeomorph_comm`). It carries the orientation which
agrees with `oM` and `oN` on the punctured summands (`TauCeti.OrientedConnectedSum.orientation`).

## Main definitions

* `TauCeti.OrientedConnectedSum oM oN`: the connected sum of two oriented manifolds, along balls
  chosen to induce opposite orientations of `E`.
* `TauCeti.OrientedConnectedSum.leftBall oM oN`, `TauCeti.OrientedConnectedSum.rightBall oM oN`:
  the chosen balls of `M` and `N`.
* `TauCeti.OrientedConnectedSum.orientation oM oN`: the orientation of the oriented connected sum.

## Main results

* `TauCeti.OrientedConnectedSum.nonempty_diffeomorph`: the oriented connected sum is diffeomorphic
  to the connected sum along any pair of balls inducing opposite orientations.
* `TauCeti.OrientedConnectedSum.nonempty_diffeomorph_comm`: the oriented connected sum is
  commutative.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6, Theorem 6.6.
-/

public section

noncomputable section

open Function Topology Module
open scoped Manifold ContDiff

namespace TauCeti

section Oriented

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [Nonempty M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [Nonempty N]
  (oM : Manifold.Orientation 𝓘(ℝ, E) M ι) (oN : Manifold.Orientation 𝓘(ℝ, E) N ι)

namespace OrientedConnectedSum

open Manifold.Orientation

/-- Balls of `M` and `N` inducing opposite orientations of `E` exist: take any orientation `o` of
`E`, a ball of `M` preserving orientation from `o` to `oM`, and a ball of `N` preserving
orientation from `o` to `-oN`. -/
private theorem exists_balls : ∃ (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (e₁ : E → M)
    (e₂ : E → N), IsOpenEmbedding e₁ ∧ IsOpenEmbedding e₂ ∧
      IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₁ ∧ IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₂ ∧
      (∀ v, IsOrientationPreservingAt o oM e₁ v) ∧ ∀ v, IsOrientationReversingAt o oN e₂ v := by
  classical
  let o : Manifold.Orientation 𝓘(ℝ, E) E ι := model
    ((finBasisOfFinrankEq ℝ E oM.card_eq.symm).reindex (Fintype.equivFin ι).symm).orientation
    oM.card_eq
  obtain ⟨e₁, h₁, d₁, -, ho₁⟩ :=
    exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt o oM
      (Classical.arbitrary M)
  obtain ⟨e₂, h₂, d₂, -, ho₂⟩ :=
    exists_isOpenEmbedding_isLocalDiffeomorph_isOrientationPreservingAt o (-oN)
      (Classical.arbitrary N)
  exact ⟨o, e₁, e₂, h₁, h₂, d₁, d₂, ho₁, fun v ↦ (isOrientationPreservingAt_neg_right ..).1 (ho₂ v)⟩

/-- The ball of `M` along which the oriented connected sum `M # N` is formed. -/
def leftBall : E → M :=
  (exists_balls oM oN).choose_spec.choose

/-- The ball of `N` along which the oriented connected sum `M # N` is formed. -/
def rightBall : E → N :=
  (exists_balls oM oN).choose_spec.choose_spec.choose

/-- The ball of `M` along which `M # N` is formed is an open embedding. -/
theorem isOpenEmbedding_leftBall : IsOpenEmbedding (leftBall oM oN) :=
  (exists_balls oM oN).choose_spec.choose_spec.choose_spec.1

/-- The ball of `N` along which `M # N` is formed is an open embedding. -/
theorem isOpenEmbedding_rightBall : IsOpenEmbedding (rightBall oM oN) :=
  (exists_balls oM oN).choose_spec.choose_spec.choose_spec.2.1

/-- The ball of `M` along which `M # N` is formed is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_leftBall :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (leftBall oM oN) :=
  (exists_balls oM oN).choose_spec.choose_spec.choose_spec.2.2.1

/-- The ball of `N` along which `M # N` is formed is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_rightBall :
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (rightBall oM oN) :=
  (exists_balls oM oN).choose_spec.choose_spec.choose_spec.2.2.2.1

/-- The balls of the oriented connected sum induce opposite orientations of `E`: for some
orientation `o` of `E`, the ball of `M` preserves orientation from `o` to `oM` and the ball of `N`
reverses orientation from `o` to `oN`, at every point. -/
theorem exists_isOrientationPreservingAt_leftBall_and_isOrientationReversingAt_rightBall :
    ∃ o : Manifold.Orientation 𝓘(ℝ, E) E ι,
      (∀ v, IsOrientationPreservingAt o oM (leftBall oM oN) v) ∧
        ∀ v, IsOrientationReversingAt o oN (rightBall oM oN) v :=
  ⟨(exists_balls oM oN).choose, (exists_balls oM oN).choose_spec.choose_spec.choose_spec.2.2.2.2⟩

end OrientedConnectedSum

variable [T1Space M] [T1Space N]

open OrientedConnectedSum in
/-- The **oriented connected sum** `M # N` of two oriented manifolds `M` and `N` modelled on a
nontrivial finite-dimensional real inner product space `E`: the connected sum along balls
`OrientedConnectedSum.leftBall oM oN` of `M` and `OrientedConnectedSum.rightBall oM oN` of `N`
which induce opposite orientations of `E`. For connected summands its diffeomorphism type does
not depend on the choice of the balls (`TauCeti.OrientedConnectedSum.nonempty_diffeomorph`). -/
abbrev OrientedConnectedSum : Type _ :=
  ConnectedSum (leftBall oM oN) (rightBall oM oN)

namespace OrientedConnectedSum

open Manifold.Orientation

instance : ChartedSpace E (OrientedConnectedSum oM oN) :=
  ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_leftBall oM oN)
    (isOpenEmbedding_rightBall oM oN)

instance : IsManifold 𝓘(ℝ, E) ∞ (OrientedConnectedSum oM oN) :=
  ConnectedSum.isManifold (H := E) (n := ⊤) (isOpenEmbedding_leftBall oM oN)
    (isOpenEmbedding_rightBall oM oN) (isLocalDiffeomorph_leftBall oM oN)
    (isLocalDiffeomorph_rightBall oM oN)

instance [T2Space M] [T2Space N] : T2Space (OrientedConnectedSum oM oN) :=
  ConnectedSum.t2Space (isOpenEmbedding_leftBall oM oN) (isOpenEmbedding_rightBall oM oN)

instance [CompactSpace M] [CompactSpace N] : CompactSpace (OrientedConnectedSum oM oN) :=
  ConnectedSum.compactSpace (isOpenEmbedding_leftBall oM oN) (isOpenEmbedding_rightBall oM oN)

/-- The oriented connected sum of connected manifolds of dimension at least two is connected. -/
theorem connectedSpace [ConnectedSpace M] [ConnectedSpace N] (h : 1 < Module.rank ℝ E) :
    ConnectedSpace (OrientedConnectedSum oM oN) :=
  ConnectedSum.connectedSpace h (isOpenEmbedding_leftBall oM oN) (isOpenEmbedding_rightBall oM oN)

omit [Nontrivial E] in
/-- A smooth local diffeomorphism `E → X` is a `C^1` local diffeomorphism, by the inverse function
theorem. -/
private theorem isLocalDiffeomorph_one {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold 𝓘(ℝ, E) ∞ X] {e : E → X}
    (d : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e) : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e :=
  isLocalDiffeomorph_of_mfderiv_eq (d.contMDiff.of_le (by simp)) le_rfl
    fun y ↦ ⟨(d y).mfderivToContinuousLinearEquiv (by simp), rfl⟩

/-- The **orientation of the oriented connected sum** `M # N`: the orientation which agrees with
`oM` on the punctured summand `M ∖ {leftBall oM oN 0}` and with `oN` on `N ∖ {rightBall oM oN 0}`
(`TauCeti.OrientedConnectedSum.isOrientationPreservingAt_inl`,
`TauCeti.OrientedConnectedSum.isOrientationPreservingAt_inr`). -/
def orientation : Manifold.Orientation 𝓘(ℝ, E) (OrientedConnectedSum oM oN) ι :=
  ConnectedSum.orientation (isOpenEmbedding_leftBall oM oN) (isOpenEmbedding_rightBall oM oN)
    (isLocalDiffeomorph_one (isLocalDiffeomorph_leftBall oM oN))
    (isLocalDiffeomorph_one (isLocalDiffeomorph_rightBall oM oN)) oM oN
    (exists_isOrientationPreservingAt_leftBall_and_isOrientationReversingAt_rightBall oM oN).choose
    (fun v _ ↦ (exists_isOrientationPreservingAt_leftBall_and_isOrientationReversingAt_rightBall
      oM oN).choose_spec.1 v)
    fun v _ ↦ (exists_isOrientationPreservingAt_leftBall_and_isOrientationReversingAt_rightBall
      oM oN).choose_spec.2 v

/-- The inclusion of the punctured first summand `M ∖ {leftBall oM oN 0}` into `M # N` preserves
orientation from the restriction of `oM` to the orientation of `M # N`. -/
theorem isOrientationPreservingAt_inl (x : ConnectedSum.puncture (leftBall oM oN)) :
    IsOrientationPreservingAt (oM.restrict _) (orientation oM oN)
      (ConnectedSum.inl (leftBall oM oN) (rightBall oM oN)) x :=
  ConnectedSum.isOrientationPreservingAt_inl _ _ _ _ _ _ (isOrientationPreservingAt_restrict _ _ x)

/-- The inclusion of the punctured second summand `N ∖ {rightBall oM oN 0}` into `M # N` preserves
orientation from the restriction of `oN` to the orientation of `M # N`. -/
theorem isOrientationPreservingAt_inr (y : ConnectedSum.puncture (rightBall oM oN)) :
    IsOrientationPreservingAt (oN.restrict _) (orientation oM oN)
      (ConnectedSum.inr (leftBall oM oN) (rightBall oM oN)) y :=
  ConnectedSum.isOrientationPreservingAt_inr _ _ _ _ _ _ (isOrientationPreservingAt_restrict _ _ y)

/-- **The oriented connected sum is well defined.** Let `M` and `N` be connected, Hausdorff,
σ-compact smooth manifolds without boundary modelled on `E`, with orientations `oM` and `oN`. If
the coordinate balls `e₁ : E → M` and `e₂ : E → N` are open embeddings and smooth local
diffeomorphisms, and for some orientation `o` of `E` the ball `e₁` preserves orientation from `o`
to `oM` at `0` while `e₂` reverses orientation from `o` to `oN` at `0`, then the oriented connected
sum is diffeomorphic to the connected sum along `e₁` and `e₂`. -/
theorem nonempty_diffeomorph [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]
    [T2Space N] [SigmaCompactSpace N] [PreconnectedSpace N] {e₁ : E → M} {e₂ : E → N}
    (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₂)
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (hf₁ : IsOrientationPreservingAt o oM e₁ 0)
    (hf₂ : IsOrientationReversingAt o oN e₂ 0) :
    letI := ConnectedSum.chartedSpace (H := E) h₁ h₂
    Nonempty (OrientedConnectedSum oM oN ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ ConnectedSum e₁ e₂) := by
  let := ConnectedSum.chartedSpace (H := E) h₁ h₂
  obtain ⟨o₀, ho₁, ho₂⟩ :=
    exists_isOrientationPreservingAt_leftBall_and_isOrientationReversingAt_rightBall oM oN
  have ho₂' (v : E) : IsOrientationPreservingAt o₀ (-oN) (rightBall oM oN) v :=
    (isOrientationPreservingAt_neg_right ..).2 (ho₂ v)
  rw [← isOrientationPreservingAt_neg_right] at hf₂
  rcases o.eq_or_eq_neg o₀ with rfl | rfl
  · exact ConnectedSum.nonempty_diffeomorph_of_isOrientationPreservingAt
      (isOpenEmbedding_leftBall oM oN) (isOpenEmbedding_rightBall oM oN) h₁ h₂
      (isLocalDiffeomorph_leftBall oM oN) (isLocalDiffeomorph_rightBall oM oN) d₁ d₂ o o oM (-oN)
      (ho₁ 0) hf₁ (ho₂' 0) hf₂
  -- Otherwise `e₁` and `e₂` preserve orientation from `-o₀`: rotate both by a reflection of `E`,
  -- which reverses `o₀`.
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  set ρ := (ℝ ∙ u)ᗮ.reflection
  have hρe : IsOpenEmbedding ρ := ρ.toHomeomorph.isOpenEmbedding
  have hρd : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ρ :=
    ρ.toContinuousLinearEquiv.toDiffeomorph.isLocalDiffeomorph
  have hρo := isOrientationReversingAt_reflection o₀ hu 0
  have hg₁ : IsOrientationPreservingAt o₀ oM (e₁ ∘ ρ) 0 :=
    IsOrientationReversingAt.comp (by simpa [ρ] using hf₁) hρo
  have hg₂ : IsOrientationPreservingAt o₀ (-oN) (e₂ ∘ ρ) 0 :=
    IsOrientationReversingAt.comp (by simpa [ρ] using hf₂) hρo
  have d₁' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (e₁ ∘ ρ) := fun v ↦ (hρd v).comp (hg := d₁ (ρ v))
  have d₂' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (e₂ ∘ ρ) := fun v ↦ (hρd v).comp (hg := d₂ (ρ v))
  let := ConnectedSum.chartedSpace (H := E) (h₁.comp hρe) (h₂.comp hρe)
  obtain ⟨φ⟩ := ConnectedSum.nonempty_diffeomorph_of_isOrientationPreservingAt
    (isOpenEmbedding_leftBall oM oN) (isOpenEmbedding_rightBall oM oN) (h₁.comp hρe)
    (h₂.comp hρe) (isLocalDiffeomorph_leftBall oM oN) (isLocalDiffeomorph_rightBall oM oN) d₁' d₂'
    o₀ o₀ oM (-oN) (ho₁ 0) hg₁ (ho₂' 0) hg₂
  obtain ⟨ψ⟩ := ConnectedSum.nonempty_diffeomorph_of_comp_linearIsometryEquiv (n := ⊤) ρ h₁ h₂
    (h₁.comp hρe) (h₂.comp hρe) d₁ d₂ d₁' d₂' (fun _ ↦ rfl) fun _ ↦ rfl
  exact ⟨φ.trans ψ.symm⟩

/-- **The oriented connected sum is commutative.** For connected, Hausdorff, σ-compact oriented
summands, `M # N` is diffeomorphic to `N # M`. -/
theorem nonempty_diffeomorph_comm [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]
    [T2Space N] [SigmaCompactSpace N] [PreconnectedSpace N] :
    Nonempty (OrientedConnectedSum oM oN ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ OrientedConnectedSum oN oM) := by
  obtain ⟨o₀, ho₁, ho₂⟩ :=
    exists_isOrientationPreservingAt_leftBall_and_isOrientationReversingAt_rightBall oM oN
  -- The balls of `M # N`, exchanged, induce opposite orientations of `E` from `-o₀`.
  obtain ⟨φ⟩ := nonempty_diffeomorph oN oM (isOpenEmbedding_rightBall oM oN)
    (isOpenEmbedding_leftBall oM oN) (isLocalDiffeomorph_rightBall oM oN)
    (isLocalDiffeomorph_leftBall oM oN) (-o₀)
    ((isOrientationPreservingAt_neg_left ..).2 (ho₂ 0))
    ((isOrientationReversingAt_neg_left ..).2 (ho₁ 0))
  let := ConnectedSum.chartedSpace (H := E) (isOpenEmbedding_rightBall oM oN)
    (isOpenEmbedding_leftBall oM oN)
  exact ⟨(ConnectedSum.commDiffeomorph (n := ⊤) (isOpenEmbedding_leftBall oM oN)
    (isOpenEmbedding_rightBall oM oN) (isLocalDiffeomorph_leftBall oM oN)
    (isLocalDiffeomorph_rightBall oM oN)).trans φ.symm⟩

end OrientedConnectedSum

end Oriented

end TauCeti
