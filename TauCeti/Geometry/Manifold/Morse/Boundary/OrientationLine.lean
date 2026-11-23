/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.LinearAlgebra.Orientation.Line

/-!
# The Morse boundary on orientation lines

Let `f` be a Morse function on a compact boundaryless manifold and `X` a pseudo-gradient adapted
to `f`. The integral Morse boundary `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary` acts on
the free module on the critical points, once the unstable manifold of every critical point has
been oriented. This file constructs the same boundary without choosing orientations: the chains
are the elements of the orientation lines of the unstable manifolds.

Fix a Morse chart `φ p` at each critical point `p`; the comparisons below need `X` to be linear
in these charts. It identifies the tangent space of the unstable manifold of `p` at `p` with its
space `Vp` of coordinates of negative weight. The **orientation
line** of `p` with coefficients in a ring `R` (`TauCeti.MorseChart.unstableOrientationLine`) is
the `R`-module `o(p)` of the functions on the orientations of `Vp` that change sign with the
orientation (`TauCeti.orientationLine`); it is free of rank one, and each orientation of `Vp` is
a generator. The chains are the families `c` with `c p ∈ o(p)` for every critical point `p`.

For critical points with `ind p = ind q + 1`, the **trajectory map**
`o(p) → o(q)` (`TauCeti.IsAdaptedPseudoGradient.trajectoryLineMap`) sends `g` to the function
`oq ↦ g op * n(op, oq)`, where `n(op, oq)` is the signed count of the trajectories from `p` to `q`
(`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount`). Reversing `op` reverses both factors,
so the product does not depend on the orientation `op` of `Vp`
(`TauCeti.IsAdaptedPseudoGradient.trajectoryLineMap_apply`), and reversing `oq` reverses the
count, so the result lies in `o(q)`. The **boundary** on orientation lines
(`TauCeti.IsAdaptedPseudoGradient.orientationLineBoundary`) is the sum of these maps.

Orientation data `𝔬 : TauCeti.MorseOrientation f X` in the charts `φ`, which exist exactly when
`X` is linear in them, turn this boundary into the integral boundary: evaluating each `c p` at
the chosen orientation of `p` is an isomorphism from the chains on orientation lines to the free
module on the critical points
(`TauCeti.MorseOrientation.orientationLineEquiv`), and it intertwines the two boundaries
(`TauCeti.IsAdaptedPseudoGradient.orientationLineEquiv_orientationLineBoundary`). In particular,
the boundary on orientation lines squares to zero exactly when the integral boundary does, for any
choice of orientations
(`TauCeti.IsAdaptedPseudoGradient.orientationLineBoundary_comp_self_eq_zero_iff`), and the
integral boundaries of any two choices of orientations in the same charts are conjugate, as
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_reverse` makes explicit.

Nor does the boundary on orientation lines depend on the Morse charts, when `X` is linear in them.
Two Morse charts at the same critical point differ, on their coordinates of negative weight, by the
change of negative coordinates `TauCeti.MorseChart.negativeChange`, along which the orientation
lines are transported (`LinearEquiv.orientationLineCongr`). These transports intertwine the
boundaries defined in the two families of charts
(`TauCeti.orientationLineChartEquiv_orientationLineBoundary`), because the
signed counts do not depend on the charts
(`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount_map_negativeChange`). So the boundary on
orientation lines is defined, up to canonical isomorphism, by `f` and `X` alone, among the Morse
charts in which `X` is linear (which exist,
`TauCeti.IsAdaptedPseudoGradient.nonempty_morseOrientation`); the integral Morse boundary is
isomorphic to it, though only through a choice of orientations.
The transports are coherent: the one from a family of charts to itself is the identity
(`TauCeti.orientationLineChartEquiv_self`), and they compose
(`TauCeti.orientationLineChartEquiv_trans_orientationLineChartEquiv`).

## Main definitions

* `TauCeti.MorseChart.unstableOrientationLine`: the orientation line of the unstable manifold at
  the centre of a Morse chart.
* `TauCeti.IsAdaptedPseudoGradient.trajectoryLineMap`: the signed count of the trajectories from
  `p` to `q`, as a map of orientation lines `o(p) → o(q)`.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineBoundary`: the Morse boundary on the orientation
  lines.
* `TauCeti.MorseOrientation.orientationLineEquiv`: evaluation at chosen orientations, from the
  chains on orientation lines to the free module on the critical points.
* `TauCeti.orientationLineChartEquiv`: the transport of the chains on
  orientation lines between two families of Morse charts.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.trajectoryLineMap_apply`: the trajectory map, computed with
  any orientation at the source.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineEquiv_orientationLineBoundary`: chosen
  orientations identify the boundary on orientation lines with the integral Morse boundary.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineBoundary_comp_self_eq_zero_iff`: the boundary on
  orientation lines squares to zero if and only if the integral Morse boundary does.
* `TauCeti.orientationLineChartEquiv_orientationLineBoundary`: the boundary on orientation lines
  does not depend on the Morse charts in which `X` is linear.
* `TauCeti.orientationLineChartEquiv_self` and
  `TauCeti.orientationLineChartEquiv_trans_orientationLineChartEquiv`: the transports between
  families of Morse charts are coherent.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (the Morse complex over `ℤ` and its independence of the
  orientations).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Set Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable {x : M} (φ : MorseChart E f x) (R : Type*) [Ring R]

/-- The **orientation line**, with coefficients in `R`, of the unstable manifold at the centre `x`
of a Morse chart: the functions on the orientations of the space of coordinates of negative weight,
which the chart identifies with the tangent space of the unstable manifold of `x` at `x`, that
change sign with the orientation. -/
noncomputable abbrev unstableOrientationLine :
    Submodule R (Orientation ℝ ({i // φ.weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)) → R) :=
  orientationLine R ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x))

end MorseChart

section ChartChange

variable [FiniteDimensional ℝ E] (φ φ' : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p)
  (R : Type*) [Ring R]

/-- The **transport of the chains on orientation lines** from the Morse charts `φ` to the Morse
charts `φ'`, along the changes of negative coordinates `(φ p).negativeChange (φ' p)` at every
critical point `p`. -/
noncomputable def orientationLineChartEquiv :
    ((p : criticalPoints 𝓘(ℝ, E) f) → (φ p).unstableOrientationLine R) ≃ₗ[R]
      ((p : criticalPoints 𝓘(ℝ, E) f) → (φ' p).unstableOrientationLine R) :=
  LinearEquiv.piCongrRight fun p ↦ ((φ p).negativeChange (φ' p)).orientationLineCongr R

variable {φ φ' R} in
@[simp]
theorem orientationLineChartEquiv_apply
    (c : (p : criticalPoints 𝓘(ℝ, E) f) → (φ p).unstableOrientationLine R)
    (p : criticalPoints 𝓘(ℝ, E) f) :
    orientationLineChartEquiv φ φ' R c p =
      ((φ p).negativeChange (φ' p)).orientationLineCongr R (c p) :=
  (rfl)

variable {φ R} in
/-- The transport of the chains on orientation lines from a family of Morse charts to itself is
the identity. -/
@[simp]
theorem orientationLineChartEquiv_self : orientationLineChartEquiv φ φ R = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun c ↦ funext fun p ↦ by simp

end ChartChange

namespace MorseOrientation

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
  (𝔬 : MorseOrientation f X) (hf : IsMorse 𝓘(ℝ, E) f) (R : Type*) [Ring R]

/-- **Evaluation at chosen orientations.** Orientation data identify the chains on the orientation
lines of the unstable manifolds, in the charts of the data, with the free module on the critical
points: a family `c` goes to the finitely supported function whose value at `p` is `c p`
evaluated at the chosen orientation of `p`. -/
noncomputable def orientationLineEquiv :
    ((p : criticalPoints 𝓘(ℝ, E) f) → (𝔬.chart p).unstableOrientationLine R) ≃ₗ[R]
      (criticalPoints 𝓘(ℝ, E) f →₀ R) :=
  haveI := hf.finite_criticalPoints.to_subtype
  (LinearEquiv.piCongrRight fun p ↦ (𝔬.orientation p).orientationLineEquiv R
    (𝔬.chart p).card_fin_manifoldMorseIndex_eq_finrank).trans
      (Finsupp.linearEquivFunOnFinite R R _).symm

variable {𝔬 hf R}

@[simp]
theorem orientationLineEquiv_apply
    (c : (p : criticalPoints 𝓘(ℝ, E) f) → (𝔬.chart p).unstableOrientationLine R)
    (p : criticalPoints 𝓘(ℝ, E) f) :
    𝔬.orientationLineEquiv hf R c p = (c p).val (𝔬.orientation p) := by
  simp [orientationLineEquiv]

/-- The family of elements of the orientation lines taking the values of `c` at the chosen
orientations. -/
@[simp]
theorem orientationLineEquiv_symm_apply (c : criticalPoints 𝓘(ℝ, E) f →₀ R)
    (p : criticalPoints 𝓘(ℝ, E) f) :
    ((𝔬.orientationLineEquiv hf R).symm c p).val (𝔬.orientation p) = c p := by
  rw [← orientationLineEquiv_apply (hf := hf) ((𝔬.orientationLineEquiv hf R).symm c),
    LinearEquiv.apply_symm_apply]

end MorseOrientation

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  (hX : IsAdaptedPseudoGradient f X) {p q : M} (φp : MorseChart E f p) (φq : MorseChart E f q)
  (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)

section TrajectoryMap

variable (R : Type*) [Ring R]

/-- The **trajectory map** of orientation lines `o(p) → o(q)`, for critical points `p` and `q` with
`ind p = ind q + 1`: it sends `g` to the function `oq ↦ g op * n(op, oq)`, for `n(op, oq)` the
signed count of the trajectories from `p` to `q`. The product does not depend on the orientation
`op` (`TauCeti.IsAdaptedPseudoGradient.trajectoryLineMap_apply`); the definition uses the one of
a basis. -/
noncomputable def trajectoryLineMap :
    φp.unstableOrientationLine R →ₗ[R] φq.unstableOrientationLine R where
  toFun g := ⟨fun oq ↦ g.val φp.negativeOrientation *
      hX.signedTrajectoryCount φp φq φp.negativeOrientation oq hpq,
    mem_orientationLine_iff.2 fun oq ↦ by simp⟩
  map_add' g g' := by ext; simp [add_mul]
  map_smul' r g := by ext; simp [mul_assoc]

variable {hX φp φq hpq R}

/-- **The trajectory map, read with any orientation at the source**: its value at `oq` is
`g op * n(op, oq)` for every orientation `op` of the unstable manifold at `p`, since reversing
`op` reverses both factors. -/
theorem trajectoryLineMap_apply (g : φp.unstableOrientationLine R)
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q))) :
    (hX.trajectoryLineMap φp φq hpq R g).val oq =
      g.val op * hX.signedTrajectoryCount φp φq op oq hpq := by
  simp only [trajectoryLineMap, LinearMap.coe_mk, AddHom.coe_mk]
  rcases φp.negativeOrientation.eq_or_eq_neg_of_card_eq_finrank op
    φp.card_fin_manifoldMorseIndex_eq_finrank with h | h <;> simp [h]

end TrajectoryMap

section Boundary

variable (φ : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p) (R : Type*) [Ring R]

/-- **The Morse boundary on orientation lines.** The `R`-linear map of the families `c` with
`c p` in the orientation line of the unstable manifold at each critical point `p` (in the Morse
chart `φ p`) whose component at `q` is the sum, over the critical points `p` with
`ind p = ind q + 1`, of the trajectory maps `o(p) → o(q)` applied to `c p`. No orientation is
chosen. When `X` is linear in the charts `φ`, so that `φ = 𝔬.chart` for orientation data `𝔬`,
reading it in any orientations gives the integral Morse boundary
(`TauCeti.IsAdaptedPseudoGradient.orientationLineEquiv_orientationLineBoundary`). -/
noncomputable def orientationLineBoundary :
    ((p : criticalPoints 𝓘(ℝ, E) f) → (φ p).unstableOrientationLine R) →ₗ[R]
      ((q : criticalPoints 𝓘(ℝ, E) f) → (φ q).unstableOrientationLine R) :=
  LinearMap.pi fun q ↦ ∑ᶠ p : criticalPoints 𝓘(ℝ, E) f,
    if hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 then
      (hX.trajectoryLineMap (φ p) (φ q) hpq R).comp (LinearMap.proj p)
    else 0

variable {hX φ R}

/-- The component at `q` of the boundary on orientation lines of `c`, evaluated at an orientation
`oq`: the sum over the critical points `p` with `ind p = ind q + 1` of `c p op * n(op, oq)`, for
any orientations `op`. -/
theorem orientationLineBoundary_apply (hf : IsMorse 𝓘(ℝ, E) f)
    (c : (p : criticalPoints 𝓘(ℝ, E) f) → (φ p).unstableOrientationLine R)
    (o : (p : criticalPoints 𝓘(ℝ, E) f) →
      Orientation ℝ ({i // (φ p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (q : criticalPoints 𝓘(ℝ, E) f) :
    (hX.orientationLineBoundary φ R c q).val (o q) =
      ∑ᶠ p : criticalPoints 𝓘(ℝ, E) f,
        if hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 then
          (c p).val (o p) * hX.signedTrajectoryCount (φ p) (φ q) (o p) (o q) hpq
        else 0 := by
  have := hf.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  simp only [orientationLineBoundary, LinearMap.pi_apply, finsum_eq_sum_of_fintype]
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  split_ifs with hpq
  · rw [LinearMap.comp_apply, LinearMap.proj_apply, trajectoryLineMap_apply]
  · rfl

end Boundary

section Orientation

variable {hX} {𝔬 : MorseOrientation f X} {hf : IsMorse 𝓘(ℝ, E) f} {R : Type*} [Ring R]

/-- **Chosen orientations identify the boundary on orientation lines with the integral Morse
boundary.** Evaluation at the orientations of `𝔬` carries the boundary on the orientation lines,
in the Morse charts of `𝔬`, to the integral Morse boundary with coefficients in `R` defined by
`𝔬`. -/
theorem orientationLineEquiv_orientationLineBoundary
    (c : (p : criticalPoints 𝓘(ℝ, E) f) → (𝔬.chart p).unstableOrientationLine R) :
    𝔬.orientationLineEquiv hf R (hX.orientationLineBoundary 𝔬.chart R c) =
      hX.signedMorseBoundary 𝔬 hf R (𝔬.orientationLineEquiv hf R c) := by
  have := hf.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  ext q
  rw [MorseOrientation.orientationLineEquiv_apply,
    orientationLineBoundary_apply hf c 𝔬.orientation, signedMorseBoundary_apply,
    Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _), finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [MorseOrientation.orientationLineEquiv_apply]
  split_ifs with hpq
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq]
  · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpq, Int.cast_zero, mul_zero]

variable (hf) in
/-- Chosen orientations conjugate the boundary on orientation lines to the integral Morse
boundary. -/
theorem orientationLineBoundary_eq_symm_conjRingEquiv_signedMorseBoundary :
    hX.orientationLineBoundary 𝔬.chart R =
      (𝔬.orientationLineEquiv hf R).symm.conjRingEquiv (hX.signedMorseBoundary 𝔬 hf R) :=
  LinearMap.ext fun c ↦ by
    rw [LinearEquiv.conjRingEquiv_apply_apply, LinearEquiv.symm_symm,
      ← orientationLineEquiv_orientationLineBoundary, LinearEquiv.symm_apply_apply]

variable (hf) in
/-- **The boundary on orientation lines squares to zero if and only if the integral Morse boundary
does**, for any choice of orientations in the same Morse charts. -/
theorem orientationLineBoundary_comp_self_eq_zero_iff :
    hX.orientationLineBoundary 𝔬.chart R ∘ₗ hX.orientationLineBoundary 𝔬.chart R = 0 ↔
      hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 := by
  rw [orientationLineBoundary_eq_symm_conjRingEquiv_signedMorseBoundary hf,
    ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul,
    map_eq_zero_iff _ (RingEquiv.injective _)]

end Orientation

end IsAdaptedPseudoGradient

section ChartChange

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {hX : IsAdaptedPseudoGradient f X} {φ φ' : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p}
  {R : Type*} [Ring R]

/-- **The boundary on orientation lines does not depend on the Morse charts.** If `X` is linear in
the Morse charts `φ` and in the Morse charts `φ'`, the transport of the chains on orientation lines
along the changes of negative coordinates carries the boundary defined in the charts `φ` to the
boundary defined in the charts `φ'`. -/
theorem orientationLineChartEquiv_orientationLineBoundary (hf : IsMorse 𝓘(ℝ, E) f)
    (hφ : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ p).toChart.source,
      (φ p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ p).toChart y (X y)) =
        fun i ↦ -((φ p).weight i * (φ p).coord ((φ p).toChart y) i))
    (hφ' : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ' p).toChart.source,
      (φ' p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ' p).toChart y (X y)) =
        fun i ↦ -((φ' p).weight i * (φ' p).coord ((φ' p).toChart y) i))
    (c : (p : criticalPoints 𝓘(ℝ, E) f) → (φ p).unstableOrientationLine R) :
    orientationLineChartEquiv φ φ' R (hX.orientationLineBoundary φ R c) =
      hX.orientationLineBoundary φ' R (orientationLineChartEquiv φ φ' R c) := by
  funext q
  -- Fix orientations `o` in the charts `φ`. Compare the two sides at the transport of `o q`, and
  -- read the boundary in the charts `φ'` at the transports of the orientations `o`.
  obtain ⟨o⟩ : Nonempty ((p : criticalPoints 𝓘(ℝ, E) f) →
      Orientation ℝ ({i // (φ p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))) :=
    ⟨fun p ↦ (φ p).negativeOrientation⟩
  refine orientationLine_ext (φ' q).card_fin_manifoldMorseIndex_eq_finrank
    (Orientation.map _ ((φ q).negativeChange (φ' q)) (o q)) ?_
  rw [orientationLineChartEquiv_apply, LinearEquiv.orientationLineCongr_apply_map,
    IsAdaptedPseudoGradient.orientationLineBoundary_apply hf c o q,
    IsAdaptedPseudoGradient.orientationLineBoundary_apply (φ := φ') hf _
      (fun p ↦ Orientation.map _ ((φ p).negativeChange (φ' p)) (o p)) q]
  refine finsum_congr fun p ↦ ?_
  split_ifs with hpq
  · rw [orientationLineChartEquiv_apply, LinearEquiv.orientationLineCongr_apply_map,
      IsAdaptedPseudoGradient.signedTrajectoryCount_map_negativeChange (hφ p) (hφ' p) (hφ q)
        (hφ' q) hf]
  · rfl

variable (hX) in
include hX in
/-- **The transports of the chains on orientation lines compose** for three families of Morse
charts in which `X` is linear, since the changes of negative coordinates do
(`TauCeti.IsAdaptedPseudoGradient.negativeChange_trans_negativeChange`). -/
theorem orientationLineChartEquiv_trans_orientationLineChartEquiv (hf : IsMorse 𝓘(ℝ, E) f)
    {φ'' : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p}
    (hφ : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ p).toChart.source,
      (φ p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ p).toChart y (X y)) =
        fun i ↦ -((φ p).weight i * (φ p).coord ((φ p).toChart y) i))
    (hφ' : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ' p).toChart.source,
      (φ' p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ' p).toChart y (X y)) =
        fun i ↦ -((φ' p).weight i * (φ' p).coord ((φ' p).toChart y) i))
    (hφ'' : ∀ p : criticalPoints 𝓘(ℝ, E) f, ∀ y ∈ (φ'' p).toChart.source,
      (φ'' p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ'' p).toChart y (X y)) =
        fun i ↦ -((φ'' p).weight i * (φ'' p).coord ((φ'' p).toChart y) i)) :
    (orientationLineChartEquiv φ φ' R).trans (orientationLineChartEquiv φ' φ'' R) =
      orientationLineChartEquiv φ φ'' R :=
  LinearEquiv.ext fun c ↦ funext fun p ↦ by
    rw [LinearEquiv.trans_apply, orientationLineChartEquiv_apply, orientationLineChartEquiv_apply,
      orientationLineChartEquiv_apply, ← LinearEquiv.trans_apply,
      ← LinearEquiv.orientationLineCongr_trans,
      hX.negativeChange_trans_negativeChange (hφ p) (hφ' p) hf (hφ'' p)]

end ChartChange

end TauCeti
