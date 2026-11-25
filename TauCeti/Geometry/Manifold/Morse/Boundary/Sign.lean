/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.Stable.ChartChange
public import TauCeti.LinearAlgebra.Orientation.LinearMapSign
public import TauCeti.LinearAlgebra.Orientation.Prod
import TauCeti.Analysis.Normed.Module.Orientation
import TauCeti.Data.Set.Card
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
import TauCeti.LinearAlgebra.Determinant.Prod
import TauCeti.LinearAlgebra.Ray

/-!
# Signs of index-one Morse trajectories

Let `f` be a Morse function on a compact boundaryless manifold, `X` a Morse–Smale pseudo-gradient
adapted to `f`, and `p`, `q` critical points with `ind p = ind q + 1`. The integral Morse
differential counts the trajectories from `p` to `q` with signs, once the unstable manifold of each
critical point is oriented. This file defines these signs and the signed count.

Fix Morse charts `φp` at `p` and `φq` at `q` in which `X` is linear, and orientations `op` and
`oq` of their spaces `Vp` and `Vq` of coordinates of negative weight, of dimensions `ind p` and
`ind q`; these are orientations of the unstable manifolds at `p` and `q`. At a point `y` of a
trajectory from `p` to `q`:

* the unstable frame `Fp = hX.unstableFrame φp y : Vp → T_y M` carries `op` to the tangent space of
  `W^u(p)` at `y`;
* the normal coordinates `Nq = hX.stableNormal φq y : T_y M → Vq` carry the normal space of
  `W^s(q)` at `y` onto `Vq`, oriented by `oq`;
* the differential of `f` measures the direction of the flow, along which `f` decreases.

The **comparison map** `v ↦ (df_y (Fp v), Nq (Fp v))` from `Vp` to `ℝ × Vq`
(`TauCeti.IsAdaptedPseudoGradient.trajectoryComparison`) is an isomorphism under the Morse–Smale
condition (`TauCeti.IsAdaptedPseudoGradient.bijective_trajectoryComparison`): the tangent spaces of
`W^u(p)` and `W^s(q)` meet in the line spanned by the velocity `X y`, on which `df_y` does not
vanish. The **sign** of the trajectory through `y`
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign`) is `+1` if this isomorphism carries `op` to the
product of the standard orientation of `ℝ` with `oq`, and `-1` otherwise. Since `df_y (-X y) > 0`,
this says: the trajectory counts positively when the negative-flow direction `-X y` followed by a
lift of a positive basis of `Vq` is a positive basis of `T_y W^u(p)`. This is the ordered
decomposition `T W^u(p) = ℝ (-X) ⊕ T W^u(q)` of the orientation conventions for the Morse complex,
with `T W^u(q)` standing for the normal space of `W^s(q)`.

The orientation data are recorded in the coordinates of the chosen Morse charts. A Morse chart
identifies its space of coordinates of negative weight with the tangent space of the unstable
manifold at the critical point, and two Morse charts at the same point differ there by the change
of negative coordinates `TauCeti.MorseChart.negativeChange`. The signs do not depend on the
charts: changing the charts and transporting the orientations along the changes of negative
coordinates leaves every sign unchanged
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign_map_negativeChange`), since the unstable frames
and the normal coordinates of two charts differ by these changes
(`TauCeti.Geometry.Manifold.Morse.Stable.ChartChange`).

The sign does not change when the point moves along the flow
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign_flow`), so it is the sign of the unparametrized
trajectory: along the flow, the unstable frame and the normal coordinates are rescaled by positive
factors, and the velocity is carried to the velocity.

The comparison map depends continuously on `y` along `W^u(p) ∩ W^s(q)`
(`TauCeti.IsAdaptedPseudoGradient.continuousWithinAt_trajectoryComparison`), whatever the indices
of `p` and `q`: near a point `y₀`, the unstable frame and the normal coordinates are both read at
fixed times of linear flow, in the charts `φp ∘ Φ_{-T}` and `φq ∘ Φ_{T'}`. Consequently, near
every point where the comparison map is an isomorphism, the sign is locally constant on
`W^u(p) ∩ W^s(q)`, not only along each trajectory
(`TauCeti.IsAdaptedPseudoGradient.eventually_trajectorySign_eq`). For critical points whose indices
differ by more than one, the comparison maps are not isomorphisms, and their continuity is the
input for orienting the spaces of trajectories coherently through them.

Reversing either orientation reverses every sign
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign_neg_left`,
`TauCeti.IsAdaptedPseudoGradient.trajectorySign_neg_right`). The **signed count**
`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount` sums the signs over the points of the
trajectories from `p` to `q` on the middle level. Every sign is a unit, so modulo two the signed
count is the number of trajectories
(`TauCeti.IsAdaptedPseudoGradient.intCast_signedTrajectoryCount`), which is the coefficient of
the mod-two Morse boundary (`IsMorseSmale.morseBoundaryCoeff_eq_intCast_signedTrajectoryCount`
in the namespace `TauCeti.IsAdaptedPseudoGradient`).

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `trajectoryComparison`: the comparison map `Vp → ℝ × Vq` at a point of a trajectory.
* `trajectorySign`: the sign of the trajectory through a point.
* `signedTrajectoryCount`: the number of trajectories from `p` to `q` counted with signs.

## Main results

* `bijective_trajectoryComparison`, `bijective_mvfderiv_prod_stableNormal`: the comparison map and
  the stable comparison map `v ↦ (df_y v, Nq v)` are isomorphisms at the points of trajectories
  between critical points of consecutive index (and top source index).
* `trajectorySign_eq_one_or_eq_neg_one`: so the sign of such a trajectory is `±1`.
* `exists_trajectorySign_eq_and_map_eq`, `trajectorySign_eq_of_map_eq`: where the comparison map
  is an isomorphism, the sign is the unit by which it scales the target orientation; the second
  reads it off any linear equivalence agreeing with the comparison map.
* `trajectorySign_flow`: the sign is constant along each trajectory.
* `continuousWithinAt_trajectoryComparison`, `continuousOn_trajectoryComparison`: the comparison
  map depends continuously on the point of `W^u(p) ∩ W^s(q)`.
* `eventually_trajectorySign_eq`: so the sign is locally constant on `W^u(p) ∩ W^s(q)` where the
  comparison map is an isomorphism.
* `trajectorySign_neg_left`, `trajectorySign_neg_right`, `trajectorySign_eq_neg_of_map_eq_neg`:
  reversing an orientation or reversing the induced comparison orientation reverses the signs.
* `signBasis_mul_trajectorySign`: changing the orientation at the target to that of a basis
  multiplies the sign by their relative sign.
* `exists_trajectorySign_eq_one_and_eq_neg_one_of_trajectorySign_eq_neg` and
  `signedTrajectoryCount_eq_zero_of_exists_trajectorySign`: opposite-signed trajectories give slice
  points of signs `+1` and `-1`, and on a two-point slice their signed count vanishes.
* `unstableFrameEquiv_symm_trans_trajectoryComparison_apply`: reading the comparison map from a
  top-index critical point in local chart coordinates at the target critical point.
* `intCast_signedTrajectoryCount`,
  `IsMorseSmale.morseBoundaryCoeff_eq_intCast_signedTrajectoryCount`: the signed count reduces
  modulo two to the number of trajectories, the coefficient of the mod-two Morse boundary.
* `trajectoryComparison_negativeChange`: changing the Morse charts composes the comparison map
  with the changes of negative coordinates.
* `trajectorySign_map_negativeChange`, `signedTrajectoryCount_map_negativeChange`: the signs and
  the signed count do not depend on the Morse charts, only on the orientations of the unstable
  manifolds which they induce.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds and the signs
  of flow lines).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Function Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable {x : M} (φ : MorseChart E f x)

/-- An orientation of the space of coordinates of negative weight of a Morse chart, indexed by the
Morse index: the orientation of a basis. It serves wherever some orientation is needed and the
result does not depend on which. -/
noncomputable def negativeOrientation :
    Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)) :=
  (Module.finBasisOfFinrankEq ℝ _ φ.finrank_negativeWeight_fun).orientation

/-- The orientation of `ℝ × V`, for `V` the space of coordinates of negative weight of a Morse
chart at `q`, against which the signs of the trajectories from a critical point `p` of index
`ind q + 1` to `q` are measured: the standard orientation of `ℝ` followed by `oq`, indexed by
`Fin (ind p)`. -/
noncomputable def trajectoryTargetOrientation {p : M}
    (oq : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x + 1) :
    Orientation ℝ (ℝ × ({i // φ.weight i < 0} → ℝ)) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) :=
  Orientation.reindex ℝ _
    (finCongr (by omega : 1 + manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f p))
    ((Module.Basis.singleton (Fin 1) ℝ).orientation.prod oq (Module.finrank_self ℝ)
      φ.finrank_negativeWeight_fun)

variable {p : M}
  {oq : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x))}
  {hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x + 1}

/-- The index of the source is the dimension of `ℝ × V`, which carries the target orientation. -/
private theorem card_fin_eq_finrank_prod
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x + 1) :
    Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) =
      Module.finrank ℝ (ℝ × ({i // φ.weight i < 0} → ℝ)) := by
  rw [Fintype.card_fin, φ.finrank_prod_negativeWeight_fun]
  omega

/-- The defining formula of the target orientation. -/
theorem trajectoryTargetOrientation_def :
    φ.trajectoryTargetOrientation oq hpq = Orientation.reindex ℝ _
      (finCongr (by omega : 1 + manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f p))
      ((Module.Basis.singleton (Fin 1) ℝ).orientation.prod oq (Module.finrank_self ℝ)
        φ.finrank_negativeWeight_fun) :=
  (rfl)

/-- The target orientation of the reversed orientation is the reversed target orientation. -/
@[simp]
theorem trajectoryTargetOrientation_neg :
    φ.trajectoryTargetOrientation (-oq) hpq = -φ.trajectoryTargetOrientation oq hpq := by
  rw [trajectoryTargetOrientation_def, Orientation.prod_neg_right, Orientation.reindex_neg,
    trajectoryTargetOrientation_def]

/-- Every orientation of `ℝ × V` agrees with the target orientation or with its reverse. -/
theorem eq_or_eq_neg_trajectoryTargetOrientation
    (o : Orientation ℝ (ℝ × ({i // φ.weight i < 0} → ℝ)) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))) :
    o = φ.trajectoryTargetOrientation oq hpq ∨ o = -φ.trajectoryTargetOrientation oq hpq :=
  o.eq_or_eq_neg _ (Nat.card_eq_fintype_card.trans (φ.card_fin_eq_finrank_prod hpq))

/-- Transporting the orientation `oq` of the coordinates of negative weight of `φ` to those of
another Morse chart `φ'` at the same point, along a linear isomorphism `e`, transports the target
orientation along the isomorphism `id × e` of `ℝ × V`. -/
theorem trajectoryTargetOrientation_map (φ' : MorseChart E f x)
    (e : ({i // φ.weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // φ'.weight i < 0} → ℝ)) :
    φ'.trajectoryTargetOrientation (Orientation.map _ e oq) hpq =
      Orientation.map _ ((LinearEquiv.refl ℝ ℝ).prodCongr e)
        (φ.trajectoryTargetOrientation oq hpq) := by
  rw [trajectoryTargetOrientation_def, trajectoryTargetOrientation_def, Orientation.map_reindex,
    Orientation.map_prod, Orientation.map_refl, Equiv.refl_apply]

end MorseChart

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) {p q : M} (φp : MorseChart E f p)
  (φq : MorseChart E f q)

/-- The **comparison map** at a point `y`: it sends `v` in the space of coordinates of negative
weight of the Morse chart `φp` to the pair formed by the derivative of `f` along the unstable frame
of `W^u(p)` on `v`, and the normal coordinates of `W^s(q)` of that vector. -/
noncomputable def trajectoryComparison (y : M) :
    ({i // φp.weight i < 0} → ℝ) →L[ℝ] ℝ × ({i // φq.weight i < 0} → ℝ) :=
  ((mvfderiv 𝓘(ℝ, E) f y).comp (hX.unstableFrame φp y)).prod
    ((hX.stableNormal φq y).comp (hX.unstableFrame φp y))

/-- The two components of the comparison map. -/
@[simp]
theorem trajectoryComparison_apply (y : M) (v : {i // φp.weight i < 0} → ℝ) :
    hX.trajectoryComparison φp φq y v =
      (mvfderiv 𝓘(ℝ, E) f y (hX.unstableFrame φp y v),
        hX.stableNormal φq y (hX.unstableFrame φp y v)) :=
  (rfl)

/-- The **sign of the trajectory** through `y` from `p` to `q`, for orientations `op` and `oq` of
the unstable manifolds at `p` and `q`: the sign `Orientation.linearMapSign` of the comparison map,
that is, `1` when it is an isomorphism carrying `op` to the standard orientation of `ℝ` followed by
`oq`, `-1` when it is an isomorphism reversing these orientations, and `0` when it is not an
isomorphism. The last case does not happen on trajectories
from `p` to `q` when `X` is linear in `φp` and `φq` and satisfies the Morse–Smale condition
(`TauCeti.IsAdaptedPseudoGradient.bijective_trajectoryComparison`). -/
noncomputable def trajectorySign
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) (y : M) : ℤ :=
  op.linearMapSign (φq.trajectoryTargetOrientation oq hpq)
    (hX.trajectoryComparison φp φq y).toLinearMap

/-- The sign of a trajectory is the sign of the comparison map. -/
theorem trajectorySign_def
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) (y : M) :
    hX.trajectorySign φp φq op oq hpq y =
      op.linearMapSign (φq.trajectoryTargetOrientation oq hpq)
        (hX.trajectoryComparison φp φq y).toLinearMap :=
  (rfl)

/-- The number of trajectories from `p` to `q` counted with their signs, read on the middle
level `(f p + f q) / 2`. -/
noncomputable def signedTrajectoryCount
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) : ℤ :=
  ∑ᶠ y ∈ hX.morseTrajectorySlice p q, hX.trajectorySign φp φq op oq hpq y

/-- The defining formula of the signed count. -/
theorem signedTrajectoryCount_def
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.signedTrajectoryCount φp φq op oq hpq =
      ∑ᶠ y ∈ hX.morseTrajectorySlice p q, hX.trajectorySign φp φq op oq hpq y :=
  (rfl)

variable {hX φp φq}

variable {op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))}
  {oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q))}
  {hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1}

open scoped Classical in
/-- Where the comparison map is an isomorphism, the sign compares the orientation it carries `op`
to with the target orientation. -/
theorem trajectorySign_of_bijective {y : M} (h : Bijective (hX.trajectoryComparison φp φq y)) :
    hX.trajectorySign φp φq op oq hpq y =
      if Orientation.map _
          (LinearEquiv.ofBijective (hX.trajectoryComparison φp φq y).toLinearMap h) op =
        φq.trajectoryTargetOrientation oq hpq then 1 else -1 :=
  Orientation.linearMapSign_of_bijective h

/-- Where the comparison map is not an isomorphism, the sign is `0`. -/
theorem trajectorySign_of_not_bijective {y : M}
    (h : ¬Bijective (hX.trajectoryComparison φp φq y)) :
    hX.trajectorySign φp φq op oq hpq y = 0 :=
  Orientation.linearMapSign_of_not_bijective h

/-- **The sign of a trajectory is `±1`** wherever the comparison map is an isomorphism. -/
theorem trajectorySign_eq_one_or_eq_neg_one_of_bijective {y : M}
    (h : Bijective (hX.trajectoryComparison φp φq y)) :
    hX.trajectorySign φp φq op oq hpq y = 1 ∨ hX.trajectorySign φp φq op oq hpq y = -1 :=
  Orientation.linearMapSign_eq_one_or_eq_neg_one_of_bijective h

/-- **The sign as a unit.** Where the comparison map is an isomorphism, it carries `op` to the
target orientation scaled by a unit sign `u`, and the sign of the trajectory is `u`. -/
theorem exists_trajectorySign_eq_and_map_eq {y : M}
    (h : Bijective (hX.trajectoryComparison φp φq y)) :
    ∃ u : ℤˣ, hX.trajectorySign φp φq op oq hpq y = u ∧
      Orientation.map _ (LinearEquiv.ofBijective (hX.trajectoryComparison φp φq y).toLinearMap h)
          op =
        Units.map (Int.castRingHom ℝ).toMonoidHom u • φq.trajectoryTargetOrientation oq hpq :=
  Orientation.exists_linearMapSign_eq_and_map_eq (φq.card_fin_eq_finrank_prod hpq) h

/-- **Reading off the sign.** If a linear equivalence `L` agrees with the comparison map and
carries `op` to the target orientation scaled by a unit sign `u`, the sign of the trajectory is
`u`. -/
theorem trajectorySign_eq_of_map_eq {y : M}
    (L : ({i // φp.weight i < 0} → ℝ) ≃ₗ[ℝ] ℝ × ({i // φq.weight i < 0} → ℝ))
    (hL : ∀ v, L v = hX.trajectoryComparison φp φq y v) {u : ℤˣ}
    (hu : Orientation.map _ L op =
      Units.map (Int.castRingHom ℝ).toMonoidHom u • φq.trajectoryTargetOrientation oq hpq) :
    hX.trajectorySign φp φq op oq hpq y = u :=
  Orientation.linearMapSign_eq_of_map_eq L hL hu

/-- **Reversing the orientation at the source reverses the sign.** -/
@[simp]
theorem trajectorySign_neg_left (y : M) :
    hX.trajectorySign φp φq (-op) oq hpq y = -hX.trajectorySign φp φq op oq hpq y :=
  Orientation.linearMapSign_neg_left (φq.card_fin_eq_finrank_prod hpq)

/-- **Reversing the orientation at the target reverses the sign.** -/
@[simp]
theorem trajectorySign_neg_right (y : M) :
    hX.trajectorySign φp φq op (-oq) hpq y = -hX.trajectorySign φp φq op oq hpq y := by
  rw [trajectorySign_def, trajectorySign_def, MorseChart.trajectoryTargetOrientation_neg]
  exact Orientation.linearMapSign_neg_right (φq.card_fin_eq_finrank_prod hpq)

/-- **Measuring signs against a basis at the target.** The sign of a trajectory for the
orientation of a basis `b` of the coordinates of negative weight at the target is its sign for
`oq`, multiplied by the sign of `oq` relative to `b`. -/
theorem signBasis_mul_trajectorySign
    (b : Module.Basis (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)) ℝ ({i // φq.weight i < 0} → ℝ))
    (y : M) :
    (oq.signBasis b : ℤ) * hX.trajectorySign φp φq op oq hpq y =
      hX.trajectorySign φp φq op b.orientation hpq y := by
  rcases b.orientation_eq_or_eq_neg oq with rfl | rfl <;> simp

/-- Reversing the orientation at the source reverses the signed count. -/
@[simp]
theorem signedTrajectoryCount_neg_left :
    hX.signedTrajectoryCount φp φq (-op) oq hpq = -hX.signedTrajectoryCount φp φq op oq hpq := by
  simp only [signedTrajectoryCount_def, trajectorySign_neg_left, finsum_neg_distrib]

/-- Reversing the orientation at the target reverses the signed count. -/
@[simp]
theorem signedTrajectoryCount_neg_right :
    hX.signedTrajectoryCount φp φq op (-oq) hpq = -hX.signedTrajectoryCount φp φq op oq hpq := by
  simp only [signedTrajectoryCount_def, trajectorySign_neg_right, finsum_neg_distrib]

/-- If the comparison maps at `y₁` and `y₂` are bijective and transport `op` to opposite
orientations, then `y₁` and `y₂` carry opposite trajectory signs. -/
theorem trajectorySign_eq_neg_of_map_eq_neg {y₁ y₂ : M}
    (hC₁ : Bijective (hX.trajectoryComparison φp φq y₁))
    (hC₂ : Bijective (hX.trajectoryComparison φp φq y₂))
    (hneg : Orientation.map _
        (LinearEquiv.ofBijective (hX.trajectoryComparison φp φq y₂).toLinearMap hC₂) op =
      -Orientation.map _
        (LinearEquiv.ofBijective (hX.trajectoryComparison φp φq y₁).toLinearMap hC₁) op) :
    hX.trajectorySign φp φq op oq hpq y₂ = -hX.trajectorySign φp φq op oq hpq y₁ := by
  rw [trajectorySign_of_bijective hC₁, trajectorySign_of_bijective hC₂, hneg]
  exact Orientation.ite_neg_eq_eq_neg_ite (by
    rw [Fintype.card_fin, Module.finrank_prod, Module.finrank_self,
      φq.finrank_negativeWeight_fun]; omega)

/-- If the trajectory slice from `p` to `q` has two points carrying signs `+1` and `-1`, then the
signed trajectory count vanishes. -/
theorem signedTrajectoryCount_eq_zero_of_exists_trajectorySign
    (hncard : (hX.morseTrajectorySlice p q).ncard = 2)
    (hex : ∃ y₁ ∈ hX.morseTrajectorySlice p q, ∃ y₂ ∈ hX.morseTrajectorySlice p q,
      hX.trajectorySign φp φq op oq hpq y₁ = 1 ∧ hX.trajectorySign φp φq op oq hpq y₂ = -1) :
    hX.signedTrajectoryCount φp φq op oq hpq = 0 := by
  obtain ⟨y₁, hy₁, y₂, hy₂, hs₁, hs₂⟩ := hex
  have hyne : y₁ ≠ y₂ := fun h ↦ by have := h ▸ hs₁; omega
  have hslice : hX.morseTrajectorySlice p q = {y₁, y₂} :=
    (Set.eq_of_subset_of_ncard_le (pair_subset hy₁ hy₂)
      (by rw [hncard, ncard_pair hyne]) (finite_of_ncard_pos (by omega))).symm
  rw [signedTrajectoryCount_def, hslice, finsum_mem_insert _ hyne (finite_singleton y₂),
    finsum_mem_singleton, hs₁, hs₂]
  ring

variable (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
include hφp hφq

/-- On a trajectory between critical points of consecutive index, a vector of the unstable frame
whose normal coordinates vanish is a multiple of the velocity: the tangent spaces of `W^u(p)` and
`W^s(q)` meet in the line spanned by `X y`. -/
private theorem exists_unstableFrame_eq_smul (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) {v : {i // φp.weight i < 0} → ℝ}
    (hv : hX.stableNormal φq y (hX.unstableFrame φp y v) = 0) :
    ∃ c : ℝ, hX.unstableFrame φp y v = c • X y := by
  have hne : p ≠ q := by rintro rfl; omega
  have htr := hMS.span_mtangentConeAt_sup_eq_top hy
  have hXne : X y ≠ 0 := hX.ne_zero_of_mfderiv_ne_zero
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hy)
  have hline := hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex
    hX hf hy htr
  have hline1 : Module.finrank ℝ (Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet p ∩ hX.flow.stableSet q) y)) = 1 := by omega
  -- `u = Fp v` is tangent to `W^u(p)` and to `W^s(q)`, hence to their intersection, the line
  -- spanned by `w = X y`. Both are read as vectors of the model space `E`.
  obtain ⟨u, hu⟩ : ∃ u : E, hX.unstableFrame φp y v = u := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : E, X y = w := ⟨_, rfl⟩
  have hu₁ : u ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet p) y) :=
    (Set.ext_iff.1 (hX.range_unstableFrame hφp hf hy.1) u).1 ⟨v, hu⟩
  have hu₂ : u ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet q) y) :=
    (hX.stableNormal_eq_zero_iff hφq hy.2 u).1 (hu ▸ hv)
  have hu₃ : u ∈ Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet p ∩ hX.flow.stableSet q) y) := by
    rw [hX.span_mtangentConeAt_unstableSet_inter_stableSet hX hf hy htr]
    exact ⟨hu₁, hu₂⟩
  have hline' : Submodule.span ℝ {w} = Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet p ∩ hX.flow.stableSet q) y) :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2
      (hw ▸ hX.mem_span_mtangentConeAt_unstableSet_inter_stableSet hy))
      (by rw [finrank_span_singleton (hw ▸ hXne), hline1])
  rw [← hline', Submodule.mem_span_singleton] at hu₃
  obtain ⟨c, hc⟩ := hu₃
  exact ⟨c, hu.trans (hc.symm.trans (congrArg (c • ·) hw.symm))⟩

/-- **The comparison map is an isomorphism along a trajectory.** Let `X` be a Morse–Smale
pseudo-gradient adapted to a Morse function, and `p`, `q` critical points with
`ind p = ind q + 1`. At every point `y` of a trajectory from `p` to `q`, the comparison map
`Vp → ℝ × Vq` is bijective: the tangent spaces of `W^u(p)` and `W^s(q)` meet in the line spanned
by `X y`, on which the differential of `f` does not vanish. -/
theorem bijective_trajectoryComparison (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    Bijective (hX.trajectoryComparison φp φq y) := by
  have hne : p ≠ q := by rintro rfl; omega
  have hcrit := hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hy
  have hinj : Injective (hX.trajectoryComparison φp φq y) := by
    refine (injective_iff_map_eq_zero (hX.trajectoryComparison φp φq y)).2 fun v hv ↦ ?_
    rw [trajectoryComparison_apply, Prod.mk_eq_zero] at hv
    -- `Fp v` is a multiple `c • X y` of the velocity, and along `X y` the differential of `f` is
    -- nonzero, so `c = 0`.
    obtain ⟨c, hc⟩ := exists_unstableFrame_eq_smul hφp hφq hMS hf hpq hy hv.2
    have hc0 : c = 0 := by
      have h := hv.1
      rw [hc, map_smul, smul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_right (hX.mvfderiv_apply_lt_zero y hcrit).ne
    rw [hc0, zero_smul] at hc
    exact hX.injective_unstableFrame_of_mem hφp hf hy.1 (hc.trans (map_zero _).symm)
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [Module.finrank_prod, Module.finrank_self, φp.finrank_negativeWeight_fun,
    φq.finrank_negativeWeight_fun]
  omega

omit hφp hφq in
/-- **The stable comparison map along a trajectory from a critical point of top index.** At a
point `z` of a trajectory from a critical point `p` of index `n` to a critical point `q` of index
`n - 1`, the map `v ↦ (df_z v, N_q v)` is an isomorphism: it is the comparison map after the
inverse of the unstable frame of `p`. -/
theorem bijective_mvfderiv_prod_stableNormal (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hφp : ∀ y ∈ φp.toChart.source, φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source, φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {z : M}
    (hz : z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    Bijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φq z)) := by
  obtain ⟨S, hS⟩ := (hX.eventually_mem_linearBackwardTimes hφp hf hz.1).exists
  refine (Bijective.of_comp_iff _ (bijective_unstableFrame hφp hp hS)).1 ?_
  convert bijective_trajectoryComparison hφp hφq hMS hf hpq hz using 1
  funext c
  rw [comp_apply, trajectoryComparison_apply, ContinuousLinearMap.prod_apply]

/-- **The sign of a trajectory between critical points of consecutive index is `±1`.** -/
theorem trajectorySign_eq_one_or_eq_neg_one (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    hX.trajectorySign φp φq op oq hpq y = 1 ∨ hX.trajectorySign φp φq op oq hpq y = -1 :=
  trajectorySign_eq_one_or_eq_neg_one_of_bijective
    (bijective_trajectoryComparison hφp hφq hMS hf hpq hy)

/-- **The sign is constant along a trajectory.** Moving a point of a trajectory between critical
points of consecutive index by the flow does not change its sign, so the sign is an invariant of
the unparametrized trajectory. Along the flow, the unstable frame and the normal coordinates are
rescaled by positive factors, and the comparison maps at the two points differ by an
orientation-preserving map of `ℝ × Vq` fixing the second component. -/
theorem trajectorySign_flow (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (t : ℝ) :
    hX.trajectorySign φp φq op oq hpq (hX.flow t y) = hX.trajectorySign φp φq op oq hpq y := by
  have hne : p ≠ q := by rintro rfl; omega
  have hy' : hX.flow t y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    ⟨(Flow.apply_mem_unstableSet_iff _ t).2 hy.1, (Flow.apply_mem_stableSet_iff _ t).2 hy.2⟩
  have hC := bijective_trajectoryComparison hφp hφq hMS hf hpq hy
  have hC' := bijective_trajectoryComparison hφp hφq hMS hf hpq hy'
  rw [trajectorySign_of_bijective hC, trajectorySign_of_bijective hC']
  set e := LinearEquiv.ofBijective (hX.trajectoryComparison φp φq y).toLinearMap hC
  set e' := LinearEquiv.ofBijective (hX.trajectoryComparison φp φq (hX.flow t y)).toLinearMap hC'
  have he (v : {i // φp.weight i < 0} → ℝ) : e v = hX.trajectoryComparison φp φq y v :=
    LinearEquiv.ofBijective_apply _ v
  have he' (v : {i // φp.weight i < 0} → ℝ) :
      e' v = hX.trajectoryComparison φp φq (hX.flow t y) v :=
    LinearEquiv.ofBijective_apply _ v
  obtain ⟨Tp, hTp⟩ := (hX.eventually_mem_linearBackwardTimes hφp hf hy.1).exists
  obtain ⟨Tq, hTq⟩ := (hX.eventually_mem_linearForwardTimes hφq hy.2).exists
  -- The unstable frame is rescaled by `e^{-t}` and the normal coordinates by `e^{t}`, so the
  -- comparison maps at `y` and at `Φ_t y` have the same second component.
  have hcomp (v : {i // φp.weight i < 0} → ℝ) :
      hX.trajectoryComparison φp φq (hX.flow t y) v =
        (Real.exp (-t) * mvfderiv 𝓘(ℝ, E) f (hX.flow t y)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow t) y (hX.unstableFrame φp y v)),
          hX.stableNormal φq y (hX.unstableFrame φp y v)) := by
    rw [trajectoryComparison_apply, unstableFrame_flow hφp hTp, map_smul, map_smul,
      stableNormal_mfderiv_flow hφq hTq, smul_smul, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, one_smul, smul_eq_mul]
  -- So `e' = B ∘ e` for an endomorphism `B` of `ℝ × Vq` fixing the second component.
  set B := e.symm.trans e'
  have hBe (w : ℝ × ({i // φq.weight i < 0} → ℝ)) : B w = e' (e.symm w) :=
    LinearEquiv.trans_apply w
  have hB (w : ℝ × ({i // φq.weight i < 0} → ℝ)) : (B w).2 = w.2 := by
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [hBe, e.symm_apply_apply, he', he, hcomp, trajectoryComparison_apply]
  -- `B` scales the axis `ℝ × 0`, the image of the velocity, by a positive factor, since `f`
  -- decreases along the flow at both points.
  have h1 : 0 < (B (1, 0)).1 := by
    have hv : hX.trajectoryComparison φp φq y (e.symm (1, 0)) = (1, 0) :=
      (he _).symm.trans (e.apply_symm_apply _)
    rw [trajectoryComparison_apply, Prod.mk.injEq] at hv
    obtain ⟨c, hc⟩ := exists_unstableFrame_eq_smul hφp hφq hMS hf hpq hy hv.2
    have h0 := hX.mvfderiv_apply_lt_zero y
      (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hy)
    have h0' := hX.mvfderiv_apply_lt_zero (hX.flow t y)
      (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hy')
    have hv1 := hv.1
    rw [hc, map_smul, smul_eq_mul] at hv1
    have hcneg : c < 0 := by nlinarith
    rw [hBe, he', hcomp, hc, map_smul, hX.mfderiv_flow_apply_self, map_smul, smul_eq_mul]
    exact mul_pos (Real.exp_pos _) (mul_pos_of_neg_of_neg hcneg h0')
  have hmap : Orientation.map _ e' op = Orientation.map _ B (Orientation.map _ e op) := by
    have hee : e' = e.trans B := LinearEquiv.ext fun v ↦ by
      rw [LinearEquiv.trans_apply, hBe, e.symm_apply_apply]
    rw [hee, Orientation.map_trans]
  rw [hmap, ((Orientation.map _ e op).map_eq_iff_det_pos B (φq.card_fin_eq_finrank_prod hpq)).2
    (by rw [LinearMap.det_eq_fst_of_snd_eq _ hB]; exact h1)]

/-- **The comparison maps vary continuously on `W^u(p) ∩ W^s(q)`.** The comparison map at `y`
is continuous at every point of `W^u(p) ∩ W^s(q)` within that set, as a function of `y` with values
in the fixed space of linear maps from the coordinates of negative weight of `φp` to `ℝ` times those
of `φq`. No index or transversality condition is needed. -/
theorem continuousWithinAt_trajectoryComparison (hf : IsMorse 𝓘(ℝ, E) f) {y₀ : M}
    (hy₀ : y₀ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    ContinuousWithinAt (hX.trajectoryComparison φp φq)
      (hX.flow.unstableSet p ∩ hX.flow.stableSet q) y₀ := by
  -- The derivative of `f` along the unstable frame.
  have h₁ := (hX.continuousWithinAt_mvfderiv_comp_unstableFrame hφp hf
    (hf.contMDiff.contMDiffAt.of_le (by norm_cast)) hy₀.1).mono
    (inter_subset_left (t := hX.flow.stableSet q))
  -- Near `y₀` on `W^s(q)`, the normal coordinates are, at one time `T` of linear forward flow,
  -- `e^{-T}` times the coordinates of negative weight of the derivative of `h = φq ∘ Φ_T`.
  obtain ⟨T, hT⟩ := hX.exists_eventually_mem_linearForwardTimes hφq hy₀.2
  have hT₀ : T ∈ hX.linearForwardTimes φq y₀ := hT.self_of_nhds hy₀.2
  set h : M → E := φq.toChart ∘ hX.flow T
  have hh : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 h y₀ :=
    ((contMDiffAt_of_mem_maximalAtlas φq.mem_maximalAtlas
      ((hX.mem_linearForwardTimes φq).1 hT₀).1).comp _
        (hX.contMDiff_flow_apply T).contMDiffAt).of_le (by norm_cast)
  set C : E →L[ℝ] ({i // φq.weight i < 0} → ℝ) :=
    Real.exp (-T) • LinearMap.toContinuousLinearMap φq.negativeCoord
  have hCh : ContinuousWithinAt
      (fun y ↦ C.comp ((mvfderiv 𝓘(ℝ, E) h y).comp (hX.unstableFrame φp y)))
      (hX.flow.unstableSet p ∩ hX.flow.stableSet q) y₀ :=
    continuousWithinAt_const.clm_comp
      ((hX.continuousWithinAt_mvfderiv_comp_unstableFrame hφp hf hh hy₀.1).mono
        (inter_subset_left (t := hX.flow.stableSet q)))
  have h₂ : ContinuousWithinAt (fun y ↦ (hX.stableNormal φq y).comp (hX.unstableFrame φp y))
      (hX.flow.unstableSet p ∩ hX.flow.stableSet q) y₀ := by
    refine hCh.congr_of_eventuallyEq_of_mem ?_ hy₀
    filter_upwards [nhdsWithin_le_nhds hT, self_mem_nhdsWithin] with y hyT hy
    ext v : 1
    simp only [C, ContinuousLinearMap.comp_apply, smul_apply,
      LinearMap.coe_toContinuousLinearMap', stableNormal_apply hφq (hyT hy.2)]
    rw [mvfderiv_apply_eq_mfderiv_apply]
  -- The comparison map is the pairing of its two components by `ContinuousLinearMap.prodₗᵢ`.
  -- Mathlib has no apply lemma for `prodₗᵢ`; this holds by `rfl` because `prodₗᵢ ℝ (A, B)` is
  -- `A.prod B` by definition, and `trajectoryComparison` is defined as exactly this `prod`.
  have hprod : hX.trajectoryComparison φp φq = fun y ↦ ContinuousLinearMap.prodₗᵢ ℝ
      ((mvfderiv 𝓘(ℝ, E) f y).comp (hX.unstableFrame φp y),
        (hX.stableNormal φq y).comp (hX.unstableFrame φp y)) :=
    rfl
  rw [hprod]
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.continuousAt.comp_continuousWithinAt
    (h₁.prodMk h₂)

/-- **The comparison maps vary continuously on all of `W^u(p) ∩ W^s(q)`.** -/
theorem continuousOn_trajectoryComparison (hf : IsMorse 𝓘(ℝ, E) f) :
    ContinuousOn (hX.trajectoryComparison φp φq) (hX.flow.unstableSet p ∩ hX.flow.stableSet q) :=
  fun _ hy ↦ continuousWithinAt_trajectoryComparison hφp hφq hf hy

/-- **The sign of a trajectory is locally constant.** Near a point `y₀` of `W^u(p) ∩ W^s(q)` at
which the comparison map is an isomorphism, the trajectories have the sign of the trajectory
through `y₀`. -/
theorem eventually_trajectorySign_eq (hf : IsMorse 𝓘(ℝ, E) f) {y₀ : M}
    (hy₀ : y₀ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hC : Bijective (hX.trajectoryComparison φp φq y₀)) :
    ∀ᶠ y in 𝓝[hX.flow.unstableSet p ∩ hX.flow.stableSet q] y₀,
      hX.trajectorySign φp φq op oq hpq y = hX.trajectorySign φp φq op oq hpq y₀ := by
  set f₀ := (LinearEquiv.ofBijective (hX.trajectoryComparison φp φq y₀).toLinearMap
    hC).toContinuousLinearEquiv
  have hcard : Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) =
      Module.finrank ℝ ({i // φp.weight i < 0} → ℝ) := by
    rw [Fintype.card_fin, φp.finrank_negativeWeight_fun]
  -- On the subtype `W^u(p) ∩ W^s(q)`, the comparison maps form a family continuous at `y₀`.
  have hL := (continuousWithinAt_iff_continuousAt_domRestrict _ hy₀).1
    (continuousWithinAt_trajectoryComparison hφp hφq hf hy₀)
  -- Both sides are the comparison map at `y₀`: `domRestrict` evaluates at `y₀`, and `f₀` is
  -- that map, made an equivalence.
  have hL₀ : (hX.flow.unstableSet p ∩ hX.flow.stableSet q).domRestrict
      (hX.trajectoryComparison φp φq) ⟨y₀, hy₀⟩ = f₀ :=
    ContinuousLinearMap.ext fun v ↦ by simp [f₀, Set.domRestrict_apply]
  rw [← eventually_nhds_subtype_iff _ ⟨y₀, hy₀⟩]
  -- Near `y₀` the comparison maps stay isomorphisms, and transport `op` as at `y₀`.
  filter_upwards [op.eventually_map_eq_map_of_continuousAt hcard (fun _ ↦ hL) hL₀,
    hL.preimage_mem_nhds (hL₀ ▸ ContinuousLinearEquiv.nhds f₀)] with y hy ⟨g, hg⟩
  have hgy : (g : _ →L[ℝ] _) = hX.trajectoryComparison φp φq y := by
    rw [hg, Set.domRestrict_apply]
  have hCb : Bijective (hX.trajectoryComparison φp φq y) := by
    rw [← hgy, ContinuousLinearEquiv.coe_coe]
    exact g.bijective
  have hge : LinearEquiv.ofBijective _ hCb = g.toLinearEquiv :=
    LinearEquiv.ext fun v ↦ by simp [← hgy]
  rw [trajectorySign_of_bijective hCb, trajectorySign_of_bijective hC, hge, hy g hg,
    LinearEquiv.toLinearEquiv_toContinuousLinearEquiv]

/-- **The signed count reduces to the trajectory count modulo two.** -/
theorem intCast_signedTrajectoryCount (hMS : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) :
    (hX.signedTrajectoryCount φp φq op oq hpq : ZMod 2) =
      ((hX.morseTrajectorySlice p q).ncard : ZMod 2) := by
  rw [signedTrajectoryCount_def]
  exact intCast_finsum_mem_eq_ncard_of_eq_one_or_eq_neg_one
    (hMS.finite_morseTrajectorySlice hf hpq) fun _ hy ↦ by
      obtain ⟨hu, hs, -⟩ := hX.mem_morseTrajectorySlice.1 hy
      exact trajectorySign_eq_one_or_eq_neg_one hφp hφq hMS hf ⟨hu, hs⟩

/-- If two points of `W^u(p) ∩ W^s(q)` carry opposite trajectory signs, then the middle-level slice
`morseTrajectorySlice p q` contains a point of sign `+1` and a point of sign `-1`. -/
theorem exists_trajectorySign_eq_one_and_eq_neg_one_of_trajectorySign_eq_neg
    (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {z₁ z₂ : M} (hz₁ : z₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hz₂ : z₂ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hsign : hX.trajectorySign φp φq op oq hpq z₂ = -hX.trajectorySign φp φq op oq hpq z₁) :
    ∃ y₁ ∈ hX.morseTrajectorySlice p q, ∃ y₂ ∈ hX.morseTrajectorySlice p q,
      hX.trajectorySign φp φq op oq hpq y₁ = 1 ∧ hX.trajectorySign φp φq op oq hpq y₂ = -1 := by
  have hne : p ≠ q := by rintro rfl; omega
  obtain ⟨t₁, ht₁, -⟩ := hX.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet hne hz₁
  obtain ⟨t₂, ht₂, -⟩ := hX.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet hne hz₂
  set w₁ := hX.flow t₁ z₁
  set w₂ := hX.flow t₂ z₂
  have hw₁ : w₁ ∈ hX.morseTrajectorySlice p q :=
    hX.mem_morseTrajectorySlice.2 ⟨(Flow.apply_mem_unstableSet_iff _ t₁).2 hz₁.1,
      (Flow.apply_mem_stableSet_iff _ t₁).2 hz₁.2, ht₁⟩
  have hw₂ : w₂ ∈ hX.morseTrajectorySlice p q :=
    hX.mem_morseTrajectorySlice.2 ⟨(Flow.apply_mem_unstableSet_iff _ t₂).2 hz₂.1,
      (Flow.apply_mem_stableSet_iff _ t₂).2 hz₂.2, ht₂⟩
  have hsw₁ := hX.trajectorySign_flow (op := op) (oq := oq) (hpq := hpq) hφp hφq hMS hf hz₁ t₁
  have hsw₂ := hX.trajectorySign_flow (op := op) (oq := oq) (hpq := hpq) hφp hφq hMS hf hz₂ t₂
  rcases hX.trajectorySign_eq_one_or_eq_neg_one (op := op) (oq := oq) (hpq := hpq) hφp hφq hMS
      hf hz₁ with h₁ | h₁
  · exact ⟨w₁, hw₁, w₂, hw₂, hsw₁.trans h₁, hsw₂.trans (hsign.trans (by rw [h₁]))⟩
  · exact ⟨w₂, hw₂, w₁, hw₁, hsw₂.trans (hsign.trans (by rw [h₁]; ring)), hsw₁.trans h₁⟩

/-- At a point `z ∈ W^u(p)` where `0 ∈ hX.linearForwardTimes φq z` and `D` represents the chart
derivative `mfderiv φq.toChart z`, reading the comparison map from a top-index critical point `p`
through `(hX.unstableFrameEquiv ...).trans D.toLinearEquiv` sends `w ∈ E` to
`(df_z (D⁻¹ w), φq.negativeCoord w)`. -/
theorem unstableFrameEquiv_symm_trans_trajectoryComparison_apply
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = Module.finrank ℝ E)
    {z : M} (hz : z ∈ hX.flow.unstableSet p)
    (h0 : 0 ∈ hX.linearForwardTimes φq z) (D : TangentSpace 𝓘(ℝ, E) z ≃L[ℝ] E)
    (hD : ∀ v, D v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart z v)
    (hC : Bijective (hX.trajectoryComparison φp φq z)) (w : E) :
    (((hX.unstableFrameEquiv hφp hf hp hz).trans D.toLinearEquiv).symm.trans
      (LinearEquiv.ofBijective (hX.trajectoryComparison φp φq z).toLinearMap hC)) w =
    (mvfderiv 𝓘(ℝ, E) f z (D.symm w), φq.negativeCoord w) := by
  set v := ((hX.unstableFrameEquiv hφp hf hp hz).trans D.toLinearEquiv).symm w
  have hv : D (hX.unstableFrame φp z v) = w := by
    simpa only [v, LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
      unstableFrameEquiv_apply] using
      ((hX.unstableFrameEquiv hφp hf hp hz).trans D.toLinearEquiv).apply_symm_apply w
  have hsn := hX.stableNormal_apply_of_zero_mem hφq h0 (hX.unstableFrame φp z v)
  rw [← hD _, hv] at hsn
  rw [LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe,
    trajectoryComparison_apply]
  exact Prod.ext (congrArg (mvfderiv 𝓘(ℝ, E) f z) (D.eq_symm_apply.2 hv)) hsn

omit hφp hφq in
/-- **The mod-two Morse boundary is the reduction of the signed counts.** For critical points of
consecutive index with Morse charts in which `X` is linear, and any orientations of their unstable
manifolds, the coefficient of `q` in the mod-two Morse boundary of `p` is the signed count of the
trajectories from `p` to `q`, reduced modulo two. -/
theorem IsMorseSmale.morseBoundaryCoeff_eq_intCast_signedTrajectoryCount
    (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q : criticalPoints 𝓘(ℝ, E) f}
    {φp : MorseChart E f p} {φq : MorseChart E f q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hMS.morseBoundaryCoeff hf p q = (hX.signedTrajectoryCount φp φq op oq hpq : ZMod 2) := by
  rw [hMS.morseBoundaryCoeff_eq_ncard hf hpq,
    intCast_signedTrajectoryCount hφp hφq hMS hf]

end IsAdaptedPseudoGradient

/-! ### Changing the Morse charts -/

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {p q : M} {φp φp' : MorseChart E f p}
  {φq φq' : MorseChart E f q}
  (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφp' : ∀ y ∈ φp'.toChart.source,
    φp'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp'.toChart y (X y)) =
      fun i ↦ -(φp'.weight i * φp'.coord (φp'.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
  (hφq' : ∀ y ∈ φq'.toChart.source,
    φq'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq'.toChart y (X y)) =
      fun i ↦ -(φq'.weight i * φq'.coord (φq'.toChart y) i))
include hφp hφp' hφq hφq'

/-- **The comparison map in other Morse charts.** On a trajectory from `p` to `q`, replacing the
Morse charts `φp` and `φq` by `φp'` and `φq'` composes the comparison map with the changes of
negative coordinates at both ends. -/
theorem trajectoryComparison_negativeChange (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (v : {i // φp.weight i < 0} → ℝ) :
    hX.trajectoryComparison φp' φq' y (φp.negativeChange φp' v) =
      ((hX.trajectoryComparison φp φq y v).1,
        φq.negativeChange φq' (hX.trajectoryComparison φp φq y v).2) := by
  rw [trajectoryComparison_apply, trajectoryComparison_apply,
    unstableFrame_negativeChange hφp hφp' hf hy.1, negativeChange_stableNormal hφq hφq' hy.2]

/-- **The sign of a trajectory does not depend on the Morse charts.** On a trajectory from `p` to
`q`, the sign for the orientations `op` and `oq` in the charts `φp` and `φq` is the sign in the
charts `φp'` and `φq'` for the orientations transported along the changes of negative coordinates.
So the sign depends only on the orientations of the unstable manifolds which the charts induce. -/
theorem trajectorySign_map_negativeChange (hf : IsMorse 𝓘(ℝ, E) f)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    hX.trajectorySign φp' φq' (Orientation.map _ (φp.negativeChange φp') op)
        (Orientation.map _ (φq.negativeChange φq') oq) hpq y =
      hX.trajectorySign φp φq op oq hpq y := by
  rw [trajectorySign_def, trajectorySign_def, MorseChart.trajectoryTargetOrientation_map]
  exact Orientation.linearMapSign_map_map _ _
    (trajectoryComparison_negativeChange hφp hφp' hφq hφq' hf hy)

/-- **The signed count does not depend on the Morse charts**: it is unchanged when the Morse
charts are changed and the orientations of their coordinates of negative weight are transported
along the changes of negative coordinates. -/
theorem signedTrajectoryCount_map_negativeChange (hf : IsMorse 𝓘(ℝ, E) f)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.signedTrajectoryCount φp' φq' (Orientation.map _ (φp.negativeChange φp') op)
        (Orientation.map _ (φq.negativeChange φq') oq) hpq =
      hX.signedTrajectoryCount φp φq op oq hpq := by
  rw [signedTrajectoryCount_def, signedTrajectoryCount_def]
  refine finsum_mem_congr rfl fun y hy ↦ ?_
  rw [mem_morseTrajectorySlice] at hy
  exact trajectorySign_map_negativeChange hφp hφp' hφq hφq' hf op oq hpq ⟨hy.1, hy.2.1⟩

end IsAdaptedPseudoGradient

end TauCeti
