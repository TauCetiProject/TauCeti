/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Sign

/-!
# The integral Morse boundary

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient
adapted to `f`. The integral Morse boundary counts the trajectories of `X` between critical points
of consecutive index with signs, once the unstable manifold of every critical point is oriented.
This file packages these choices and defines the boundary, over `ℤ` and more generally over any
ring of coefficients.

A `TauCeti.MorseOrientation f X` chooses, at every critical point `p` of `f`, a Morse chart in
which `X` is linear and an orientation of its space of coordinates of negative weight, which is an
orientation of the unstable manifold of `p` at `p`. Such choices always exist
(`TauCeti.IsAdaptedPseudoGradient.nonempty_morseOrientation`).

The coefficient of `q` in the boundary of `p`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff`) is the signed count of the
trajectories from `p` to `q` (`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount`) when
`ind p = ind q + 1`, and `0` otherwise. The boundary
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary`) is its linear extension to the free
`R`-module on the critical points, for any ring `R`. It lowers the index by one. It is compatible
with every change of coefficients along a ring homomorphism
(`TauCeti.IsAdaptedPseudoGradient.mapRange_signedMorseBoundary`); in particular the integral
boundary is the boundary with coefficients in `ℤ`. Under the Morse–Smale condition, the boundary
with coefficients in `ZMod 2` is the mod-two Morse boundary, whatever the orientations
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundary_eq_morseBoundary`), so that the
integral boundary reduces modulo two to the mod-two boundary.

Reversing the orientations at the critical points of a set `S` (`TauCeti.MorseOrientation.reverse`)
conjugates the boundary by the involution of the chains that negates the coefficients of the
points of `S` (`TauCeti.morseChainReversal`,
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_reverse`). Any two choices of orientations
in the same Morse charts differ in this way (`TauCeti.MorseOrientation.exists_reverse_eq`), so
the boundaries they define are isomorphic.

That the integral boundary squares to zero, which needs the orientations of the compactified
spaces of index-two trajectories, is not proved here; the mod-two statement is
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_comp_morseBoundary`.

## Main definitions

* `TauCeti.MorseOrientation f X`: Morse charts in which `X` is linear, with orientations of their
  unstable coordinates, at all critical points of `f`.
* `TauCeti.MorseOrientation.reverse`: the reversal of these orientations on a set of critical
  points.
* `TauCeti.morseChainReversal`: the involution of the chains negating the coefficients on a set.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff`: the signed count of the trajectories
  from `p` to `q`, or `0` unless `ind p = ind q + 1`.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary`: the Morse boundary with coefficients in a
  ring `R`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.nonempty_morseOrientation`: orientation data exist.
* `TauCeti.IsAdaptedPseudoGradient.morseIndex_eq_add_one_of_signedMorseBoundaryCoeff_ne_zero`:
  the boundary lowers the index by one.
* `TauCeti.IsAdaptedPseudoGradient.mapRange_signedMorseBoundary`: change of coefficients.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundary_eq_morseBoundary`: with
  coefficients in `ZMod 2` it is the mod-two Morse boundary.
* `TauCeti.MorseOrientation.exists_reverse_eq`: two choices of orientations in the same charts
  differ by a reversal.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_reverse`: reversing orientations conjugates
  the boundary by `TauCeti.morseChainReversal`.

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

variable (f X) in
/-- **Orientation data for the integral Morse boundary.** At every critical point `p` of `f`, a
Morse chart in which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`, and an orientation of its space of
coordinates of negative weight. The chart identifies this space with the tangent space at `p` of
the unstable manifold of `p`, so the orientation orients the unstable manifold. -/
structure MorseOrientation where
  /-- The Morse chart at each critical point. -/
  chart (p : criticalPoints 𝓘(ℝ, E) f) : MorseChart E f p
  /-- In each chart, `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`. -/
  coord_mfderiv_chart (p : criticalPoints 𝓘(ℝ, E) f) : ∀ y ∈ (chart p).toChart.source,
    (chart p).coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chart p).toChart y (X y)) =
      fun i ↦ -((chart p).weight i * (chart p).coord ((chart p).toChart y) i)
  /-- The orientation of the coordinates of negative weight of each chart. -/
  orientation (p : criticalPoints 𝓘(ℝ, E) f) :
    Orientation ℝ ({i // (chart p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))

namespace MorseOrientation

variable (𝔬 : MorseOrientation f X) (S : Set (criticalPoints 𝓘(ℝ, E) f)) [DecidablePred (· ∈ S)]

/-- The orientation data with the same Morse charts and the orientations reversed at the critical
points of `S`. -/
-- The body is exposed: the type of `orientation` depends on `chart`, and stating
-- `reverse_orientation` needs `(𝔬.reverse S).chart` to reduce to `𝔬.chart`.
@[expose]
def reverse : MorseOrientation f X where
  chart := 𝔬.chart
  coord_mfderiv_chart := 𝔬.coord_mfderiv_chart
  orientation p := if p ∈ S then -𝔬.orientation p else 𝔬.orientation p

/-- Reversing orientations keeps the Morse charts. -/
@[simp]
theorem reverse_chart : (𝔬.reverse S).chart = 𝔬.chart :=
  rfl

/-- The reversed orientation at a critical point: negated on `S`, unchanged off `S`. -/
@[simp]
theorem reverse_orientation (p : criticalPoints 𝓘(ℝ, E) f) :
    (𝔬.reverse S).orientation p = if p ∈ S then -𝔬.orientation p else 𝔬.orientation p :=
  rfl

/-- Reversing the orientations on the empty set changes nothing. -/
@[simp]
theorem reverse_empty : 𝔬.reverse ∅ = 𝔬 := by
  cases 𝔬
  simp [reverse]

/-- Reversing the orientations on `S` twice gives back the original orientations. -/
@[simp]
theorem reverse_reverse : (𝔬.reverse S).reverse S = 𝔬 := by
  cases 𝔬 with
  | mk chart h o =>
    simp only [reverse]
    congr 1
    funext p
    by_cases hS : p ∈ S
    · simp only [hS, ↓reduceIte]
      exact neg_neg (o p)
    · simp only [hS, ↓reduceIte]
      rfl

open scoped Classical in
/-- **Any two choices of orientations in the same Morse charts differ by a reversal**, on the set
of critical points where they disagree: any two orientations of a finite-dimensional real vector
space are equal or opposite. -/
theorem exists_reverse_eq (o : (p : criticalPoints 𝓘(ℝ, E) f) →
    Orientation ℝ ({i // (𝔬.chart p).weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))) :
    ∃ S : Set (criticalPoints 𝓘(ℝ, E) f), 𝔬.reverse S = { 𝔬 with orientation := o } := by
  refine ⟨{p | o p ≠ 𝔬.orientation p}, ?_⟩
  cases 𝔬 with
  | mk chart h o₀ =>
    simp only [reverse]
    congr 1
    funext p
    by_cases hp : o p = o₀ p
    · simp only [Set.mem_ofPred_eq, hp, ne_eq, not_true_eq_false, ↓reduceIte]
    · simp only [Set.mem_ofPred_eq, hp, ne_eq, not_false_eq_true, ↓reduceIte]
      have hcard : Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) =
          Module.finrank ℝ ({i // (chart p).weight i < 0} → ℝ) := by
        rw [Fintype.card_fin, (chart p).finrank_negativeWeight_fun]
      exact (((o p).eq_or_eq_neg (o₀ p) hcard).resolve_left hp).symm

end MorseOrientation

section Reversal

variable (R : Type*) [Ring R] (S : Set (criticalPoints 𝓘(ℝ, E) f)) [DecidablePred (· ∈ S)]

/-- The **orientation-reversal isomorphism** of the Morse chains with coefficients in `R`: it
negates the coefficients of the critical points of `S`, and is its own inverse. It intertwines the
Morse boundaries for orientations differing exactly on `S`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_reverse`). -/
noncomputable def morseChainReversal :
    (criticalPoints 𝓘(ℝ, E) f →₀ R) ≃ₗ[R] (criticalPoints 𝓘(ℝ, E) f →₀ R) :=
  LinearEquiv.ofInvolutive
    (Finsupp.linearCombination R fun p ↦ Finsupp.single p (if p ∈ S then -1 else 1)) <| by
      intro c
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add c d hc hd => simp only [map_add] at hc hd ⊢; rw [hc, hd]
      | single p a => by_cases hp : p ∈ S <;> simp [hp]

variable {R S}

/-- The reversal negates a basis chain `a • p` exactly when `p ∈ S`. -/
@[simp]
theorem morseChainReversal_single (p : criticalPoints 𝓘(ℝ, E) f) (a : R) :
    morseChainReversal R S (Finsupp.single p a) = Finsupp.single p (if p ∈ S then -a else a) := by
  have h : ⇑(morseChainReversal R S) =
      Finsupp.linearCombination R fun p ↦ Finsupp.single p (if p ∈ S then (-1 : R) else 1) :=
    LinearEquiv.coe_ofInvolutive _ _
  rw [h, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul]
  split_ifs <;> simp

/-- The coefficient of `q` in the reversal of a chain `c` is `-c q` on `S` and `c q` off `S`. -/
@[simp]
theorem morseChainReversal_apply (c : criticalPoints 𝓘(ℝ, E) f →₀ R)
    (q : criticalPoints 𝓘(ℝ, E) f) :
    morseChainReversal R S c q = if q ∈ S then -c q else c q := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => by_cases hq : q ∈ S <;> simp_all [add_comm]
  | single p a =>
    by_cases hpq : p = q
    · subst hpq
      by_cases hp : p ∈ S <;> simp [hp]
    · by_cases hp : p ∈ S <;> by_cases hq : q ∈ S <;> simp [hp, hq, Finsupp.single_eq_of_ne' hpq]

/-- The reversal is an involution. -/
@[simp]
theorem morseChainReversal_morseChainReversal (c : criticalPoints 𝓘(ℝ, E) f →₀ R) :
    morseChainReversal R S (morseChainReversal R S c) = c := by
  ext q
  by_cases hq : q ∈ S <;> simp [hq]

/-- The reversal is its own inverse. -/
@[simp]
theorem morseChainReversal_symm : (morseChainReversal R S).symm = morseChainReversal R S :=
  LinearEquiv.ext fun c ↦ (morseChainReversal R S).symm_apply_eq.2
    (morseChainReversal_morseChainReversal c).symm

end Reversal

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  (hX : IsAdaptedPseudoGradient f X) (𝔬 : MorseOrientation f X)

/-- The coefficient of the critical point `q` in the integral Morse boundary of the critical point
`p`: the number of trajectories from `p` to `q` counted with their signs when
`ind p = ind q + 1`, and `0` otherwise. -/
noncomputable def signedMorseBoundaryCoeff (p q : criticalPoints 𝓘(ℝ, E) f) : ℤ :=
  if hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 then
    hX.signedTrajectoryCount (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p) (𝔬.orientation q) hpq
  else 0

variable {hX 𝔬}

/-- For critical points of consecutive index, the boundary coefficient is the signed count of the
trajectories. -/
theorem signedMorseBoundaryCoeff_of_morseIndex_eq_add_one {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.signedMorseBoundaryCoeff 𝔬 p q =
      hX.signedTrajectoryCount (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p) (𝔬.orientation q) hpq :=
  dite_eq_left hpq

/-- The boundary coefficient vanishes between critical points whose indices do not differ by
one. -/
@[simp]
theorem signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one
    {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p ≠ manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.signedMorseBoundaryCoeff 𝔬 p q = 0 :=
  dite_eq_right hpq

/-- **The integral boundary lowers the index by one**: a nonzero boundary coefficient joins
critical points whose indices differ by one. -/
theorem morseIndex_eq_add_one_of_signedMorseBoundaryCoeff_ne_zero
    {p q : criticalPoints 𝓘(ℝ, E) f} (hpq : hX.signedMorseBoundaryCoeff 𝔬 p q ≠ 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 := by
  by_contra h
  exact hpq (signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one h)

/-- **Reversing orientations changes the signs of the boundary coefficients.** If the
orientations are reversed at the critical points of `S`, the coefficient of `q` in the boundary of
`p` changes sign exactly when one of `p` and `q` lies in `S`. -/
theorem signedMorseBoundaryCoeff_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f))
    [DecidablePred (· ∈ S)] (p q : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedMorseBoundaryCoeff (𝔬.reverse S) p q =
      (if p ∈ S then -1 else 1) * (if q ∈ S then -1 else 1) *
        hX.signedMorseBoundaryCoeff 𝔬 p q := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq,
      signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq, MorseOrientation.reverse_orientation,
      MorseOrientation.reverse_orientation]
    by_cases hp : p ∈ S <;> by_cases hq : q ∈ S <;>
      simp [hp, hq, MorseOrientation.reverse_chart]
  · simp [hpq]

section Boundary

variable (hX 𝔬) in
/-- **The Morse boundary with coefficients in a ring `R`.** The `R`-linear endomorphism of the free
module on the critical points of `f` sending a critical point `p` to the sum of the critical points
`q` with `ind q = ind p - 1`, each weighted by the number of trajectories from `p` to `q` counted
with their signs. For `R = ℤ` this is the integral Morse boundary. -/
noncomputable def signedMorseBoundary (hf : IsMorse 𝓘(ℝ, E) f) (R : Type*) [Ring R] :
    (criticalPoints 𝓘(ℝ, E) f →₀ R) →ₗ[R] (criticalPoints 𝓘(ℝ, E) f →₀ R) :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.linearCombination R fun p ↦
    Finsupp.ofSupportFinite (fun q ↦ (hX.signedMorseBoundaryCoeff 𝔬 p q : R)) (toFinite _)

variable (hf : IsMorse 𝓘(ℝ, E) f) {R : Type*} [Ring R]

/-- The coefficient of `q` in the Morse boundary of a chain `c` is the sum over the critical
points `p` of `c p` times the signed count of the trajectories from `p` to `q`. -/
theorem signedMorseBoundary_apply (c : criticalPoints 𝓘(ℝ, E) f →₀ R)
    (q : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedMorseBoundary 𝔬 hf R c q =
      c.sum fun p a ↦ a * (hX.signedMorseBoundaryCoeff 𝔬 p q : R) := by
  simp [signedMorseBoundary, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q` in the Morse boundary of `a • p` is `a` times the signed count of the
trajectories from `p` to `q`. -/
@[simp]
theorem signedMorseBoundary_single_apply (p q : criticalPoints 𝓘(ℝ, E) f) (a : R) :
    hX.signedMorseBoundary 𝔬 hf R (Finsupp.single p a) q =
      a * (hX.signedMorseBoundaryCoeff 𝔬 p q : R) := by
  rw [signedMorseBoundary_apply, Finsupp.sum_single_index (zero_mul _)]

/-- **Change of coefficients.** A ring homomorphism `g : R →+* R'`, applied to the coefficients of
the chains, intertwines the Morse boundaries with coefficients in `R` and in `R'`. -/
theorem mapRange_signedMorseBoundary {R' : Type*} [Ring R'] (g : R →+* R')
    (c : criticalPoints 𝓘(ℝ, E) f →₀ R) :
    Finsupp.mapRange g (map_zero g) (hX.signedMorseBoundary 𝔬 hf R c) =
      hX.signedMorseBoundary 𝔬 hf R' (Finsupp.mapRange g (map_zero g) c) := by
  ext q
  rw [Finsupp.mapRange_apply, signedMorseBoundary_apply, signedMorseBoundary_apply,
    Finsupp.sum_mapRange_index (fun _ ↦ zero_mul _), map_finsuppSum]
  simp only [map_mul, map_intCast]

/-- **Reversing orientations conjugates the boundary.** The Morse boundary for the orientations
reversed at the critical points of `S` is the conjugate of the original boundary by the
involution `TauCeti.morseChainReversal` negating the coefficients on `S`. In particular, the two
boundaries are isomorphic. -/
theorem signedMorseBoundary_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f))
    [DecidablePred (· ∈ S)] :
    hX.signedMorseBoundary (𝔬.reverse S) hf R =
      (morseChainReversal R S).toLinearMap ∘ₗ hX.signedMorseBoundary 𝔬 hf R ∘ₗ
        (morseChainReversal R S).toLinearMap := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [signedMorseBoundary_single_apply, morseChainReversal_single, morseChainReversal_apply,
    signedMorseBoundaryCoeff_reverse]
  by_cases hp : p ∈ S <;> by_cases hq : q ∈ S <;> simp [hp, hq]

/-- **The mod-two reduction of the boundary coefficients.** Under the Morse–Smale condition, the
signed count of the trajectories from `p` to `q`, reduced modulo two, is the coefficient of `q` in
the mod-two Morse boundary of `p`, whatever the orientations. -/
theorem IsMorseSmale.intCast_signedMorseBoundaryCoeff (h : hX.IsMorseSmale)
    (p q : criticalPoints 𝓘(ℝ, E) f) :
    (hX.signedMorseBoundaryCoeff 𝔬 p q : ZMod 2) = h.morseBoundaryCoeff hf p q := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq,
      h.morseBoundaryCoeff_eq_intCast_signedTrajectoryCount hf (𝔬.coord_mfderiv_chart p)
        (𝔬.coord_mfderiv_chart q)]
  · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpq,
      h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf hpq, Int.cast_zero]

/-- **With coefficients in `ZMod 2`, the Morse boundary is the mod-two Morse boundary.** Under the
Morse–Smale condition, the signs of the trajectories disappear modulo two, so the boundary does
not depend on the orientations. Together with
`TauCeti.IsAdaptedPseudoGradient.mapRange_signedMorseBoundary`, this says that the integral
boundary reduces modulo two to the mod-two boundary. -/
theorem IsMorseSmale.signedMorseBoundary_eq_morseBoundary (h : hX.IsMorseSmale) :
    hX.signedMorseBoundary 𝔬 hf (ZMod 2) = h.morseBoundary hf :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by
    rw [signedMorseBoundary_single_apply, h.morseBoundary_single_apply,
      h.intCast_signedMorseBoundaryCoeff hf]

end Boundary

omit [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M] in
/-- **Orientation data exist.** For an adapted pseudo-gradient, every critical point has a Morse
chart in which the pseudo-gradient is linear, and every finite-dimensional real vector space has
an orientation. -/
theorem nonempty_morseOrientation (hX : IsAdaptedPseudoGradient f X) :
    Nonempty (MorseOrientation f X) := by
  choose φ hφ using fun p : criticalPoints 𝓘(ℝ, E) f ↦
    hX.exists_morseChart p (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2)
  exact ⟨⟨φ, hφ, fun p ↦
    (Module.finBasisOfFinrankEq ℝ _ (φ p).finrank_negativeWeight_fun).orientation⟩⟩

end IsAdaptedPseudoGradient

end TauCeti
