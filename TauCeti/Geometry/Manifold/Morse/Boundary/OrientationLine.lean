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

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient
adapted to `f`. The integral Morse boundary
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary` needs an orientation of the unstable
manifold at every critical point, and changing these orientations conjugates it by sign changes.
This file constructs the **coefficient-free** version, which needs no orientations: the chains are
the direct sum over the critical points `p` of the orientation lines `o(p)` of the unstable
manifolds, and the boundary is assembled from maps `o(p) → o(q)` given by the signed counts of the
trajectories from `p` to `q`.

The unstable manifold at `p` is read in a Morse chart `φ p` in which `X` is linear, where its
tangent space is the space `Vp` of coordinates of negative weight. A chain is a family of elements
of the orientation lines `TauCeti.orientationLine ℝ Vp (Fin (ind p)) R`, the odd functions on the
orientations of `Vp` with values in a ring `R` (`TauCeti.OrientationLineMorseChain`). For
critical points `p` and `q` with `ind p = ind q + 1`, the signed count of the trajectories from `p`
to `q` (`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount`) changes sign when either
orientation is reversed, so it induces a map of orientation lines
(`TauCeti.IsAdaptedPseudoGradient.orientationLineMorseBoundaryCoeff`), and these maps form the
boundary (`TauCeti.IsAdaptedPseudoGradient.orientationLineMorseBoundary`).

* **Comparison with the integral boundary.** Orientations `𝔬 : MorseOrientation f X` in the
  charts `φ = 𝔬.chart` trivialize every orientation line, by evaluation at `𝔬.orientation p`
  (`TauCeti.MorseOrientation.orientationLineMorseChainEquiv`). This isomorphism with the free
  module on the critical points carries the boundary on orientation lines to
  `signedMorseBoundary 𝔬`
  (`TauCeti.MorseOrientation.orientationLineMorseChainEquiv_orientationLineMorseBoundary`), so
  one squares to zero exactly when the other does. Reversing orientations changes the
  trivialization by the sign reversal `Finsupp.signReversal`
  (`TauCeti.MorseOrientation.orientationLineMorseChainEquiv_reverse`), which is how the
  integral boundaries for different orientations are conjugate.
* **Independence of the Morse charts.** Two families of Morse charts `φ` and `φ'` in which `X` is
  linear are related by the changes of negative coordinates `MorseChart.negativeChange`, which
  transport the orientation lines (`TauCeti.orientationLineMorseChainCongr`). This transport
  intertwines the two boundaries
  (`TauCeti.IsAdaptedPseudoGradient.orientationLineMorseChainCongr_orientationLineMorseBoundary`)
  and is functorial, so the boundary on orientation lines is determined by `X` up to canonical
  isomorphism.

As for `signedMorseBoundary`, the definitions take no Morse–Smale hypothesis; the counts are
those of trajectories only when `X` is Morse–Smale.

## Main definitions

* `TauCeti.OrientationLineMorseChain φ R`: the chains, a family of elements of the orientation lines
  of the unstable manifolds, read in the Morse charts `φ`.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineMorseBoundaryCoeff`: the map `o(p) → o(q)` given
  by the signed count of trajectories.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineMorseBoundary`: the Morse boundary on orientation
  lines.
* `TauCeti.MorseOrientation.orientationLineMorseChainEquiv`: the trivialization of the chains by a
  choice of orientations.
* `TauCeti.orientationLineMorseChainCongr`: the transport of chains between two families of Morse
  charts.

## Main results

* `TauCeti.MorseOrientation.orientationLineMorseChainEquiv_orientationLineMorseBoundary`: the
  trivialization carries the boundary on orientation lines to the integral boundary.
* `TauCeti.MorseOrientation.orientationLineMorseBoundary_comp_self_eq_zero_iff`: the boundary on
  orientation lines squares to zero exactly when the integral boundary does.
* `TauCeti.MorseOrientation.orientationLineMorseChainEquiv_reverse`: reversing orientations changes
  the trivialization by a sign reversal.
* `TauCeti.IsAdaptedPseudoGradient.orientationLineMorseChainCongr_orientationLineMorseBoundary`:
  changing the Morse charts intertwines the boundaries.
* `TauCeti.orientationLineMorseChainCongr_self`,
  `TauCeti.IsAdaptedPseudoGradient.orientationLineMorseChainCongr_trans`: the transport is
  functorial.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and the Morse complex over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients and its independence of the choice of
  orientations).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

variable (φ : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p) (R : Type*) [Ring R]

/-- The **chains of the Morse complex on orientation lines**: at every critical point `p` of `f`,
an element of the orientation line, with coefficients in `R`, of the space of coordinates of
negative weight of the Morse chart `φ p`, which is the tangent space of the unstable manifold at
`p`. Since `f` has finitely many critical points on a compact manifold, this is their direct sum. -/
abbrev OrientationLineMorseChain : Type _ :=
  (p : criticalPoints 𝓘(ℝ, E) f) →
    orientationLine ℝ ({i // (φ p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) R

/-- The **transport of chains between two families of Morse charts**: at each critical point, the
orientation line is transported along the change of negative coordinates
`MorseChart.negativeChange` from `φ p` to `φ' p`. -/
noncomputable def orientationLineMorseChainCongr
    (φ' : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p) :
    OrientationLineMorseChain φ R ≃ₗ[R] OrientationLineMorseChain φ' R :=
  LinearEquiv.piCongrRight fun p ↦ orientationLineCongr R ((φ p).negativeChange (φ' p))

variable {φ R}

@[simp]
theorem orientationLineMorseChainCongr_apply
    (φ' : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p) (c : OrientationLineMorseChain φ R)
    (p : criticalPoints 𝓘(ℝ, E) f) :
    orientationLineMorseChainCongr φ R φ' c p =
      orientationLineCongr R ((φ p).negativeChange (φ' p)) (c p) :=
  (rfl)

variable (φ R) in
/-- Transport from a family of Morse charts to itself is the identity. -/
@[simp]
theorem orientationLineMorseChainCongr_self :
    orientationLineMorseChainCongr φ R φ = LinearEquiv.refl R _ := by
  ext c p : 2
  simp [MorseChart.negativeChange_self]

omit [FiniteDimensional ℝ E] in
/-- The cardinality of the index type of the orientations of the unstable coordinates of a Morse
chart is their dimension. -/
private theorem card_fin_eq_finrank_negativeWeight {x : M} (φx : MorseChart E f x) :
    Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)) =
      Module.finrank ℝ ({i // φx.weight i < 0} → ℝ) := by
  rw [Fintype.card_fin, φx.finrank_negativeWeight_fun]

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

variable (φ R) in
/-- The **coefficient map** `o(p) → o(q)` of the Morse boundary on orientation lines: for
`ind p = ind q + 1`, the map induced by the signed count of the trajectories from `p` to `q`, which
changes sign when either orientation is reversed (`TauCeti.orientationLineHom`); `0` otherwise.
Its value at an orientation `oq` on an element `x` is `x op` times the signed count for `op` and
`oq`, for any orientation `op`
(`TauCeti.IsAdaptedPseudoGradient.orientationLineMorseBoundaryCoeff_apply`). -/
noncomputable def orientationLineMorseBoundaryCoeff (p q : criticalPoints 𝓘(ℝ, E) f) :
    orientationLine ℝ ({i // (φ p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) R
      →ₗ[R]
    orientationLine ℝ ({i // (φ q).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)) R :=
  if hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 then
    orientationLineHom R (fun op oq ↦ (hX.signedTrajectoryCount (φ p) (φ q) op oq hpq : R))
      fun _ _ ↦ by rw [signedTrajectoryCount_neg_right, Int.cast_neg]
  else 0

/-- **The coefficient map in terms of orientations**: for `ind p = ind q + 1`, its value at `oq`
is the value at any orientation `op` times the signed count of the trajectories for `op` and
`oq`. -/
theorem orientationLineMorseBoundaryCoeff_apply {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (x : orientationLine ℝ ({i // (φ p).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) R)
    (op : Orientation ℝ ({i // (φ p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
    (oq : Orientation ℝ ({i // (φ q).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q))) :
    (hX.orientationLineMorseBoundaryCoeff φ R p q x : _ → R) oq =
      (x : _ → R) op * (hX.signedTrajectoryCount (φ p) (φ q) op oq hpq : R) := by
  simp only [orientationLineMorseBoundaryCoeff, hpq, ↓reduceDIte]
  exact orientationLineHom_apply (card_fin_eq_finrank_negativeWeight (φ p))
    (fun _ _ ↦ by rw [signedTrajectoryCount_neg_left, Int.cast_neg]) _ x op oq

/-- The coefficient map vanishes between critical points whose indices do not differ by one. -/
@[simp]
theorem orientationLineMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one
    {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p ≠ manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.orientationLineMorseBoundaryCoeff φ R p q = 0 :=
  dite_eq_right hpq

/-- The coefficient maps read in the trivialization by `𝔬`: the coefficient map from `p` to `q`
sends an element with value `r` at `𝔬.orientation p` to one with value `r` times the integral
boundary coefficient `signedMorseBoundaryCoeff 𝔬 p q` at `𝔬.orientation q`. -/
theorem orientationLineMorseBoundaryCoeff_apply_orientation (𝔬 : MorseOrientation f X)
    (p q : criticalPoints 𝓘(ℝ, E) f)
    (x : orientationLine ℝ ({i // (𝔬.chart p).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) R) :
    (hX.orientationLineMorseBoundaryCoeff 𝔬.chart R p q x : _ → R) (𝔬.orientation q) =
      (x : _ → R) (𝔬.orientation p) * (hX.signedMorseBoundaryCoeff 𝔬 p q : R) := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [hX.orientationLineMorseBoundaryCoeff_apply hpq x (𝔬.orientation p),
      signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq]
  · simp [hpq]

variable (φ R) in
/-- **The Morse boundary on orientation lines.** The `R`-linear endomorphism of the chains whose
component at `q` is the sum over the critical points `p` of the coefficient maps `o(p) → o(q)`
applied to the component at `p`
(`TauCeti.IsAdaptedPseudoGradient.orientationLineMorseBoundary_apply`).
It needs no orientations; a choice of orientations identifies it with the integral Morse
boundary (`TauCeti.MorseOrientation.orientationLineMorseChainEquiv_orientationLineMorseBoundary`).
-/
noncomputable def orientationLineMorseBoundary (hf : IsMorse 𝓘(ℝ, E) f) :
    OrientationLineMorseChain φ R →ₗ[R] OrientationLineMorseChain φ R :=
  haveI := hf.finite_criticalPoints.to_subtype
  haveI := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  LinearMap.pi fun q ↦
    ∑ p, (hX.orientationLineMorseBoundaryCoeff φ R p q).comp (LinearMap.proj p)

/-- The component at `q` of the boundary of a chain `c` is the sum over the critical points `p`
of the coefficient map from `p` to `q` applied to `c p`. -/
theorem orientationLineMorseBoundary_apply (hf : IsMorse 𝓘(ℝ, E) f)
    (c : OrientationLineMorseChain φ R) (q : criticalPoints 𝓘(ℝ, E) f) :
    hX.orientationLineMorseBoundary φ R hf c q =
      ∑ᶠ p, hX.orientationLineMorseBoundaryCoeff φ R p q (c p) := by
  have := hf.finite_criticalPoints.to_subtype
  let := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  rw [finsum_eq_sum_of_fintype]
  simp [orientationLineMorseBoundary]

end IsAdaptedPseudoGradient

/-! ### Comparison with the integral Morse boundary -/

namespace MorseOrientation

variable (𝔬 : MorseOrientation f X) (R)

/-- **The trivialization of the chains by orientations**: evaluating the component at each
critical point `p` at the orientation `𝔬.orientation p` identifies the chains on orientation lines,
in the charts of `𝔬`, with the free `R`-module on the critical points. -/
noncomputable def orientationLineMorseChainEquiv (hf : IsMorse 𝓘(ℝ, E) f) :
    OrientationLineMorseChain 𝔬.chart R ≃ₗ[R] (criticalPoints 𝓘(ℝ, E) f →₀ R) :=
  haveI := hf.finite_criticalPoints.to_subtype
  (LinearEquiv.piCongrRight fun p ↦ orientationLineEquiv R (𝔬.orientation p)
    (card_fin_eq_finrank_negativeWeight (𝔬.chart p))).trans
    (Finsupp.linearEquivFunOnFinite R R _).symm

variable {𝔬 R} (hf : IsMorse 𝓘(ℝ, E) f)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The coefficient of `p` in the trivialization of a chain is its component at `p` evaluated at
the orientation `𝔬.orientation p`. -/
@[simp]
theorem orientationLineMorseChainEquiv_apply (c : OrientationLineMorseChain 𝔬.chart R)
    (p : criticalPoints 𝓘(ℝ, E) f) :
    𝔬.orientationLineMorseChainEquiv R hf c p = (c p : _ → R) (𝔬.orientation p) := by
  simp [orientationLineMorseChainEquiv]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The component at `p` of the chain with coefficients `a` takes the value `a p` at
`𝔬.orientation p`. -/
@[simp]
theorem orientationLineMorseChainEquiv_symm_apply_orientation
    (a : criticalPoints 𝓘(ℝ, E) f →₀ R) (p : criticalPoints 𝓘(ℝ, E) f) :
    ((𝔬.orientationLineMorseChainEquiv R hf).symm a p : _ → R) (𝔬.orientation p) = a p := by
  rw [← orientationLineMorseChainEquiv_apply hf, LinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- **Reversing orientations changes the trivialization by a sign reversal**: for the orientations
reversed at the critical points of `S`, the coefficients of the trivialization are negated on `S`.
The charts, hence the chains, are unchanged. -/
theorem orientationLineMorseChainEquiv_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f))
    [DecidablePred (· ∈ S)] (c : OrientationLineMorseChain 𝔬.chart R) :
    (𝔬.reverse S).orientationLineMorseChainEquiv R hf c =
      Finsupp.signReversal R S (𝔬.orientationLineMorseChainEquiv R hf c) := by
  ext p
  refine (orientationLineMorseChainEquiv_apply (𝔬 := 𝔬.reverse S) hf c p).trans ?_
  rw [Finsupp.signReversal_apply, orientationLineMorseChainEquiv_apply, reverse_orientation]
  by_cases hp : p ∈ S <;> simp [hp]

/-- **The trivialization carries the boundary on orientation lines to the integral Morse
boundary**: after a choice of orientations `𝔬`, the coefficient-free boundary is
`signedMorseBoundary 𝔬`. -/
theorem orientationLineMorseChainEquiv_orientationLineMorseBoundary
    (hX : IsAdaptedPseudoGradient f X) (c : OrientationLineMorseChain 𝔬.chart R) :
    𝔬.orientationLineMorseChainEquiv R hf (hX.orientationLineMorseBoundary 𝔬.chart R hf c) =
      hX.signedMorseBoundary 𝔬 hf R (𝔬.orientationLineMorseChainEquiv R hf c) := by
  have := hf.finite_criticalPoints.to_subtype
  let := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  ext q
  rw [orientationLineMorseChainEquiv_apply, hX.orientationLineMorseBoundary_apply,
    IsAdaptedPseudoGradient.signedMorseBoundary_apply,
    Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _, finsum_eq_sum_of_fintype]
  simp only [orientationLineMorseChainEquiv_apply]
  rw [Submodule.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun p _ ↦
    hX.orientationLineMorseBoundaryCoeff_apply_orientation 𝔬 p q (c p)

/-- **The boundary on orientation lines squares to zero exactly when the integral Morse boundary
does**, for the orientations `𝔬` in the same charts. -/
theorem orientationLineMorseBoundary_comp_self_eq_zero_iff (hX : IsAdaptedPseudoGradient f X) :
    hX.orientationLineMorseBoundary 𝔬.chart R hf ∘ₗ hX.orientationLineMorseBoundary 𝔬.chart R hf =
        0 ↔
      hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 := by
  set e := 𝔬.orientationLineMorseChainEquiv R hf
  have key (c : OrientationLineMorseChain 𝔬.chart R) :
      e (hX.orientationLineMorseBoundary 𝔬.chart R hf
          (hX.orientationLineMorseBoundary 𝔬.chart R hf c)) =
        hX.signedMorseBoundary 𝔬 hf R (hX.signedMorseBoundary 𝔬 hf R (e c)) := by
    rw [orientationLineMorseChainEquiv_orientationLineMorseBoundary,
      orientationLineMorseChainEquiv_orientationLineMorseBoundary]
  constructor
  · refine fun h ↦ LinearMap.ext fun a ↦ ?_
    have h₀ := LinearMap.congr_fun h (e.symm a)
    have h₁ := key (e.symm a)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h₀ ⊢
    rwa [h₀, map_zero, LinearEquiv.apply_symm_apply, eq_comm] at h₁
  · refine fun h ↦ LinearMap.ext fun c ↦ e.injective ?_
    have h₀ := LinearMap.congr_fun h (e c)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h₀ ⊢
    rw [key, h₀, map_zero]

end MorseOrientation

/-! ### Independence of the Morse charts -/

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X}
  {φ φ' : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p}
  (hφ : ∀ p, ∀ y ∈ (φ p).toChart.source,
    (φ p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ p).toChart y (X y)) =
      fun i ↦ -((φ p).weight i * (φ p).coord ((φ p).toChart y) i))
  (hφ' : ∀ p, ∀ y ∈ (φ' p).toChart.source,
    (φ' p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ' p).toChart y (X y)) =
      fun i ↦ -((φ' p).weight i * (φ' p).coord ((φ' p).toChart y) i))
  (hf : IsMorse 𝓘(ℝ, E) f)
include hφ hφ' hf

/-- **The coefficient maps do not depend on the Morse charts**: transporting along the changes of
negative coordinates at `p` and at `q` intertwines the coefficient maps in the charts `φ` and
`φ'`, in which `X` is linear. -/
theorem orientationLineMorseBoundaryCoeff_orientationLineCongr (p q : criticalPoints 𝓘(ℝ, E) f)
    (x : orientationLine ℝ ({i // (φ p).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) R) :
    hX.orientationLineMorseBoundaryCoeff φ' R p q
        (orientationLineCongr R ((φ p).negativeChange (φ' p)) x) =
      orientationLineCongr R ((φ q).negativeChange (φ' q))
        (hX.orientationLineMorseBoundaryCoeff φ R p q x) := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · ext oq'
    obtain ⟨oq, rfl⟩ := (Orientation.map _ ((φ q).negativeChange (φ' q))).surjective oq'
    let op := (Module.finBasisOfFinrankEq ℝ _ (φ p).finrank_negativeWeight_fun).orientation
    rw [hX.orientationLineMorseBoundaryCoeff_apply hpq _ (Orientation.map _
      ((φ p).negativeChange (φ' p)) op), orientationLineCongr_apply_map,
      orientationLineCongr_apply_map, hX.orientationLineMorseBoundaryCoeff_apply hpq x op,
      signedTrajectoryCount_map_negativeChange (hφ p) (hφ' p) (hφ q) (hφ' q) hf]
  · simp [hpq]

/-- **The boundary on orientation lines does not depend on the Morse charts**: the transport of
chains along the changes of negative coordinates intertwines the boundaries in the charts `φ` and
`φ'`, in which `X` is linear. -/
theorem orientationLineMorseChainCongr_orientationLineMorseBoundary
    (c : OrientationLineMorseChain φ R) :
    orientationLineMorseChainCongr φ R φ' (hX.orientationLineMorseBoundary φ R hf c) =
      hX.orientationLineMorseBoundary φ' R hf (orientationLineMorseChainCongr φ R φ' c) := by
  have := hf.finite_criticalPoints.to_subtype
  let := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  funext q
  simp only [orientationLineMorseChainCongr_apply, orientationLineMorseBoundary_apply,
    finsum_eq_sum_of_fintype, map_sum,
    orientationLineMorseBoundaryCoeff_orientationLineCongr hφ hφ' hf]

omit hf in
/-- **The transport of chains is functorial**: transporting from `φ` to `φ'` and then to `φ''` is
transporting from `φ` to `φ''`, for families of Morse charts in which `X` is linear. -/
theorem orientationLineMorseChainCongr_trans
    {φ'' : (p : criticalPoints 𝓘(ℝ, E) f) → MorseChart E f p}
    (hφ'' : ∀ p, ∀ y ∈ (φ'' p).toChart.source,
      (φ'' p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ'' p).toChart y (X y)) =
        fun i ↦ -((φ'' p).weight i * (φ'' p).coord ((φ'' p).toChart y) i))
    (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f) :
    (orientationLineMorseChainCongr φ R φ').trans (orientationLineMorseChainCongr φ' R φ'') =
      orientationLineMorseChainCongr φ R φ'' := by
  ext c p : 2
  rw [LinearEquiv.trans_apply, orientationLineMorseChainCongr_apply,
    orientationLineMorseChainCongr_apply, orientationLineMorseChainCongr_apply,
    ← LinearEquiv.trans_apply, ← orientationLineCongr_trans,
    hX.negativeChange_trans_negativeChange (hφ p) (hφ' p) hf (hφ'' p)]

end IsAdaptedPseudoGradient

end TauCeti
