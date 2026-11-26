/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
public import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# Changing the orientations of the integral Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient
adapted to `f`. The integral Morse boundary `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary`
depends on orientation data `𝔬 : TauCeti.MorseOrientation f X`: a Morse chart at every critical
point, in which `X` is linear, and an orientation of the unstable manifold read in that chart. This
file shows that any two choices `𝔬` and `𝔬'` give isomorphic integral Morse chain complexes,
through explicit sign changes of the generators, and that these isomorphisms compose.

The charts of `𝔬` and `𝔬'` at a critical point `p` may differ. They are compared by the change of
negative coordinates `TauCeti.MorseChart.negativeChange`, along which the orientation chosen by `𝔬`
is transported into the chart of `𝔬'`. The transported orientation either agrees with the one
chosen by `𝔬'` or is its opposite; the **reversal set** `TauCeti.MorseOrientation.reversalSet 𝔬 𝔬'`
consists of the critical points where it is the opposite. The signed counts of trajectories do not
depend on the charts once orientations are transported
(`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount_map_negativeChange`), and reversing an
orientation at either end of a trajectory reverses its sign. Hence the boundary coefficient of `q`
in the boundary of `p` changes by one sign for each of `p` and `q` in the reversal set
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff_reversalSet`), and the boundary for
`𝔬'` is the conjugate of the boundary for `𝔬` by the involution `Finsupp.signReversal` of the
chains negating the coefficients on the reversal set
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_eq_signReversal_comp`, and its graded form
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryAt_eq_signReversal_comp`). In particular the
integral boundary squares to zero for one choice of orientation data exactly when it does for any
other.

When the boundaries square to zero, the sign reversals are therefore the components of an
isomorphism of integral Morse chain complexes
(`TauCeti.IsAdaptedPseudoGradient.signedMorseComplexIso`), and so of their homologies, through
`HomologicalComplex.homologyMapIso`. These isomorphisms form a transitive system: the one from a
choice of orientation data to itself is the identity
(`TauCeti.IsAdaptedPseudoGradient.signedMorseComplexIso_self`), and the one from `𝔬` to `𝔬''` is the
composite of those from `𝔬` to `𝔬'` and from `𝔬'` to `𝔬''`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseComplexIso_trans`), because the reversal sets do
(`TauCeti.MorseOrientation.mem_reversalSet_iff_xor`). So the integral Morse homology of `(f, X)` is
determined, up to canonical isomorphism, by `f` and `X` alone.

When the charts agree, the reversal set of `𝔬` and `𝔬.reverse S` is `S`
(`TauCeti.MorseOrientation.reversalSet_reverse`), and the conjugation above is
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_reverse`.

## Main definitions

* `TauCeti.MorseOrientation.reversalSet`: the critical points at which two choices of orientation
  data orient the unstable manifold oppositely.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseComplexIso`: the isomorphism of integral Morse chain
  complexes for two choices of orientation data.

## Main results

* `TauCeti.MorseOrientation.mem_reversalSet_iff_xor`: reversal sets compose by symmetric
  difference.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff_reversalSet`: the boundary
  coefficients for two choices of orientation data.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_eq_signReversal_comp` and
  `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryAt_eq_signReversal_comp`: the boundaries for
  two choices of orientation data are conjugate.
* `signedMorseBoundary_comp_signedMorseBoundary_eq_zero_iff_eq_zero`, in the namespace
  `TauCeti.IsAdaptedPseudoGradient`: whether the integral boundary squares to zero does not depend
  on the orientation data.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseComplexIso_self`,
  `TauCeti.IsAdaptedPseudoGradient.signedMorseComplexIso_trans` and
  `TauCeti.IsAdaptedPseudoGradient.signedMorseComplexIso_symm`: the isomorphisms form a transitive
  system.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and the Morse complex over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (independence of the Morse complex with integer coefficients from the choice of
  orientations).
-/

public section

open CategoryTheory Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseOrientation

variable (𝔬 𝔬' : MorseOrientation f X)

/-- The **reversal set** of two choices of orientation data: the critical points `p` at which the
orientation of the unstable manifold chosen by `𝔬'` is not the orientation chosen by `𝔬`,
transported along the change of negative coordinates from the Morse chart of `𝔬` at `p` to that of
`𝔬'`. At these points the two orientations are opposite
(`TauCeti.MorseOrientation.orientation_eq_neg_of_mem_reversalSet`). -/
def reversalSet : Set (criticalPoints 𝓘(ℝ, E) f) :=
  {p | 𝔬'.orientation p ≠
    Orientation.map _ ((𝔬.chart p).negativeChange (𝔬'.chart p)) (𝔬.orientation p)}

variable {𝔬 𝔬'} {p : criticalPoints 𝓘(ℝ, E) f}

/-- The defining property of the reversal set. -/
theorem mem_reversalSet_iff :
    p ∈ 𝔬.reversalSet 𝔬' ↔ 𝔬'.orientation p ≠
      Orientation.map _ ((𝔬.chart p).negativeChange (𝔬'.chart p)) (𝔬.orientation p) :=
  Iff.rfl

/-- Off the reversal set, `𝔬'` chooses the orientation of `𝔬` transported into its chart. -/
theorem orientation_eq_of_notMem_reversalSet (hp : p ∉ 𝔬.reversalSet 𝔬') :
    𝔬'.orientation p =
      Orientation.map _ ((𝔬.chart p).negativeChange (𝔬'.chart p)) (𝔬.orientation p) :=
  not_not.1 hp

/-- On the reversal set, `𝔬'` chooses the opposite of the orientation of `𝔬` transported into its
chart. -/
theorem orientation_eq_neg_of_mem_reversalSet (hp : p ∈ 𝔬.reversalSet 𝔬') :
    𝔬'.orientation p =
      -Orientation.map _ ((𝔬.chart p).negativeChange (𝔬'.chart p)) (𝔬.orientation p) :=
  (Orientation.ne_iff_eq_neg_of_card_eq_finrank _ _
    (𝔬'.chart p).card_fin_manifoldMorseIndex_eq_finrank).1 hp

/-- `𝔬'` chooses the orientation of `𝔬` transported into its chart, reversed exactly on the
reversal set. -/
theorem orientation_eq_ite [Decidable (p ∈ 𝔬.reversalSet 𝔬')] :
    𝔬'.orientation p = if p ∈ 𝔬.reversalSet 𝔬' then
      -Orientation.map _ ((𝔬.chart p).negativeChange (𝔬'.chart p)) (𝔬.orientation p) else
      Orientation.map _ ((𝔬.chart p).negativeChange (𝔬'.chart p)) (𝔬.orientation p) := by
  split_ifs with hp
  exacts [orientation_eq_neg_of_mem_reversalSet hp, orientation_eq_of_notMem_reversalSet hp]

variable (𝔬) in
/-- Orientation data reverse themselves nowhere. -/
@[simp]
theorem reversalSet_self : 𝔬.reversalSet 𝔬 = ∅ :=
  eq_empty_iff_forall_notMem.2 fun p hp ↦ hp <| by
    rw [MorseChart.negativeChange_self, Orientation.map_refl, Equiv.refl_apply]

variable (𝔬) in
/-- **Reversing the orientations on `S` has reversal set `S`.** -/
@[simp]
theorem reversalSet_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f)) [DecidablePred (· ∈ S)] :
    𝔬.reversalSet (𝔬.reverse S) = S := by
  ext p
  -- The charts of `𝔬.reverse S` are those of `𝔬` by definition; `change` states the membership
  -- with the charts of `𝔬`, since rewriting `reverse_chart` inside the dependent types fails.
  change (if p ∈ S then -𝔬.orientation p else 𝔬.orientation p) ≠
    Orientation.map _ ((𝔬.chart p).negativeChange (𝔬.chart p)) (𝔬.orientation p) ↔ p ∈ S
  rw [MorseChart.negativeChange_self, Orientation.map_refl, Equiv.refl_apply]
  by_cases hp : p ∈ S
  · simpa [hp] using (Module.Ray.ne_neg_self (𝔬.orientation p)).symm
  · simp [hp]

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

/-- **Reversal sets compose by symmetric difference.** For three choices of orientation data, a
critical point lies in the reversal set of `𝔬` and `𝔬''` exactly when it lies in one, and only one,
of the reversal sets of `𝔬` and `𝔬'` and of `𝔬'` and `𝔬''`. This uses that the changes of negative
coordinates compose, which holds since the pseudo-gradient is linear in all three charts. -/
theorem mem_reversalSet_iff_xor (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f)
    {𝔬'' : MorseOrientation f X} :
    p ∈ 𝔬.reversalSet 𝔬'' ↔ Xor (p ∈ 𝔬.reversalSet 𝔬') (p ∈ 𝔬'.reversalSet 𝔬'') := by
  have htrans := hX.negativeChange_trans_negativeChange (𝔬.coord_mfderiv_chart p)
    (𝔬'.coord_mfderiv_chart p) hf (𝔬''.coord_mfderiv_chart p)
  have hne := (Module.Ray.ne_neg_self
    (Orientation.map _ ((𝔬.chart p).negativeChange (𝔬''.chart p)) (𝔬.orientation p))).symm
  -- Write the orientation of `𝔬''` as a signed transport of that of `𝔬'`, and that of `𝔬'` as a
  -- signed transport of that of `𝔬`.
  rw [mem_reversalSet_iff]
  by_cases h₁ : p ∈ 𝔬.reversalSet 𝔬' <;> by_cases h₂ : p ∈ 𝔬'.reversalSet 𝔬''
  · rw [orientation_eq_neg_of_mem_reversalSet h₂, orientation_eq_neg_of_mem_reversalSet h₁,
      Orientation.map_neg, ← Orientation.map_trans, htrans]
    simp only [h₁, h₂, xor_self, iff_false, not_not]
    exact neg_neg
      (Orientation.map _ ((𝔬.chart p).negativeChange (𝔬''.chart p)) (𝔬.orientation p))
  · rw [orientation_eq_of_notMem_reversalSet h₂, orientation_eq_neg_of_mem_reversalSet h₁,
      Orientation.map_neg, ← Orientation.map_trans, htrans]
    simpa [h₁, h₂] using hne
  · rw [orientation_eq_neg_of_mem_reversalSet h₂, orientation_eq_of_notMem_reversalSet h₁,
      ← Orientation.map_trans, htrans]
    simpa [h₁, h₂] using hne
  · rw [orientation_eq_of_notMem_reversalSet h₂, orientation_eq_of_notMem_reversalSet h₁,
      ← Orientation.map_trans, htrans]
    simp [h₁, h₂]

/-- The reversal set does not depend on the order of the two choices of orientation data. -/
theorem reversalSet_comm (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f) :
    𝔬'.reversalSet 𝔬 = 𝔬.reversalSet 𝔬' := by
  ext p
  have h := mem_reversalSet_iff_xor (𝔬 := 𝔬) (𝔬' := 𝔬') (𝔬'' := 𝔬) (p := p) hX hf
  rw [reversalSet_self, mem_empty_iff_false, false_iff, xor_iff_not_iff, not_not] at h
  exact h.symm

end MorseOrientation

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {hX : IsAdaptedPseudoGradient f X} {𝔬 𝔬' : MorseOrientation f X} {hf : IsMorse 𝓘(ℝ, E) f}

variable (𝔬 𝔬' hf) in
include hf in
/-- **Changing the orientation data changes the signs of the boundary coefficients.** For two
choices `𝔬` and `𝔬'` of orientation data, the coefficient of `q` in the boundary of `p` for `𝔬'` is
the coefficient for `𝔬` multiplied by `-1` for each of `p` and `q` in the reversal set of `𝔬` and
`𝔬'`. -/
theorem signedMorseBoundaryCoeff_reversalSet [DecidablePred (· ∈ 𝔬.reversalSet 𝔬')]
    (p q : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedMorseBoundaryCoeff 𝔬' p q =
      (if p ∈ 𝔬.reversalSet 𝔬' then -1 else 1) * (if q ∈ 𝔬.reversalSet 𝔬' then -1 else 1) *
        hX.signedMorseBoundaryCoeff 𝔬 p q := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq,
      signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq,
      ← signedTrajectoryCount_map_negativeChange (𝔬.coord_mfderiv_chart p)
        (𝔬'.coord_mfderiv_chart p) (𝔬.coord_mfderiv_chart q) (𝔬'.coord_mfderiv_chart q) hf]
    -- Write the orientations of `𝔬'` as signed transports of those of `𝔬`.
    rw [MorseOrientation.orientation_eq_ite (𝔬 := 𝔬) (p := p),
      MorseOrientation.orientation_eq_ite (𝔬 := 𝔬) (p := q)]
    split_ifs <;> simp
  · simp [hpq]

variable (𝔬 𝔬' hf) in
/-- **Changing the orientation data conjugates the boundary.** For two choices `𝔬` and `𝔬'` of
orientation data, the integral Morse boundary for `𝔬'` is the conjugate of that for `𝔬` by the
involution `Finsupp.signReversal` negating the coefficients on the reversal set of `𝔬` and `𝔬'`. -/
theorem signedMorseBoundary_eq_signReversal_comp (R : Type*) [Ring R]
    [DecidablePred (· ∈ 𝔬.reversalSet 𝔬')] :
    hX.signedMorseBoundary 𝔬' hf R =
      (Finsupp.signReversal R (𝔬.reversalSet 𝔬')).toLinearMap ∘ₗ hX.signedMorseBoundary 𝔬 hf R ∘ₗ
        (Finsupp.signReversal R (𝔬.reversalSet 𝔬')).toLinearMap :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Finsupp.signReversal_single, Finsupp.signReversal_apply, signedMorseBoundary_single_apply,
      signedMorseBoundary_single_apply, signedMorseBoundaryCoeff_reversalSet 𝔬 𝔬' hf]
    split_ifs <;> simp

variable (𝔬 𝔬' hf) in
/-- **Changing the orientation data conjugates the graded boundary.** For two choices `𝔬` and `𝔬'`
of orientation data, the graded integral Morse boundary for `𝔬'` is the conjugate of that for `𝔬`
by the involutions `Finsupp.signReversal` of the graded chains negating the coefficients of the
points of the reversal set of `𝔬` and `𝔬'`. -/
theorem signedMorseBoundaryAt_eq_signReversal_comp (R : Type*) [Ring R]
    [DecidablePred (· ∈ 𝔬.reversalSet 𝔬')] (n : ℕ) :
    hX.signedMorseBoundaryAt 𝔬' hf R n =
      (Finsupp.signReversal R {q | ↑q ∈ 𝔬.reversalSet 𝔬'}).toLinearMap ∘ₗ
        hX.signedMorseBoundaryAt 𝔬 hf R n ∘ₗ
          (Finsupp.signReversal R {p | ↑p ∈ 𝔬.reversalSet 𝔬'}).toLinearMap :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Finsupp.signReversal_single, Finsupp.signReversal_apply, signedMorseBoundaryAt_single_apply,
      signedMorseBoundaryAt_single_apply, signedMorseBoundaryCoeff_reversalSet 𝔬 𝔬' hf]
    split_ifs <;> simp_all

variable (𝔬 𝔬' hf) in
/-- **Whether the integral boundary squares to zero does not depend on the orientation data.** -/
theorem signedMorseBoundary_comp_signedMorseBoundary_eq_zero_iff_eq_zero (R : Type*) [Ring R] :
    hX.signedMorseBoundary 𝔬' hf R ∘ₗ hX.signedMorseBoundary 𝔬' hf R = 0 ↔
      hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 := by
  classical
  -- The sign reversal is an involution, so the boundary for `𝔬'` is the image of that for `𝔬`
  -- under the ring automorphism of conjugation by it.
  have h : hX.signedMorseBoundary 𝔬' hf R =
      (Finsupp.signReversal R (𝔬.reversalSet 𝔬')).conjRingEquiv (hX.signedMorseBoundary 𝔬 hf R) :=
    LinearMap.ext fun c ↦ by
      rw [LinearEquiv.conjRingEquiv_apply_apply, Finsupp.signReversal_symm,
        signedMorseBoundary_eq_signReversal_comp 𝔬 𝔬' hf, LinearMap.comp_apply,
        LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul,
    map_eq_zero_iff _ (RingEquiv.injective _)]

/-! ### The isomorphism of integral Morse chain complexes -/

variable {R : Type*} [Ring R]
  (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0)
  (hsq' : hX.signedMorseBoundary 𝔬' hf R ∘ₗ hX.signedMorseBoundary 𝔬' hf R = 0)

/-- **The integral Morse complex does not depend on the orientation data.** For two choices `𝔬`
and `𝔬'` of orientation data for which the integral Morse boundary squares to zero, the integral
Morse chain complexes are isomorphic. In each degree the isomorphism negates the coefficients of
the critical points of the reversal set of `𝔬` and `𝔬'`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseComplexIso_hom_f_apply`). It induces an isomorphism of
integral Morse homologies through `HomologicalComplex.homologyMapIso`. -/
noncomputable def signedMorseComplexIso [DecidablePred (· ∈ 𝔬.reversalSet 𝔬')] :
    hX.signedMorseComplex 𝔬 hf R hsq ≅ hX.signedMorseComplex 𝔬' hf R hsq' :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Finsupp.signReversal R {p : {p : criticalPoints 𝓘(ℝ, E) f //
      manifoldMorseIndex 𝓘(ℝ, E) f p = n} | ↑p ∈ 𝔬.reversalSet 𝔬'}).toModuleIso) <| by
    rintro _ n rfl
    rw [signedMorseComplex_d, signedMorseComplex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun (c : {p : criticalPoints 𝓘(ℝ, E) f //
      manifoldMorseIndex 𝓘(ℝ, E) f p = n + 1} →₀ R) ↦ ?_)
    -- The terms of `signedMorseComplex` are the graded chain modules only by definition, so the
    -- goal is stated on the underlying chains.
    change hX.signedMorseBoundaryAt 𝔬' hf R n (Finsupp.signReversal R _ c) =
      Finsupp.signReversal R _ (hX.signedMorseBoundaryAt 𝔬 hf R n c)
    rw [signedMorseBoundaryAt_eq_signReversal_comp 𝔬 𝔬' hf R n, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      Finsupp.signReversal_signReversal]

variable [DecidablePred (· ∈ 𝔬.reversalSet 𝔬')]

/-- The orientation-change isomorphism negates the coefficients of a chain on the reversal set. -/
@[simp]
theorem signedMorseComplexIso_hom_f_apply (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :
    (hX.signedMorseComplexIso hsq hsq').hom.f n c = Finsupp.signReversal R
      {p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} |
        ↑p ∈ 𝔬.reversalSet 𝔬'} c :=
  (rfl)

/-- The inverse of the orientation-change isomorphism also negates the coefficients of a chain on
the reversal set. -/
@[simp]
theorem signedMorseComplexIso_inv_f_apply (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :
    (hX.signedMorseComplexIso hsq hsq').inv.f n c = Finsupp.signReversal R
      {p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} |
        ↑p ∈ 𝔬.reversalSet 𝔬'} c :=
  -- The inverse component is the inverse of the sign reversal, which is the sign reversal.
  DFunLike.congr_fun Finsupp.signReversal_symm c

/-- **The orientation-change isomorphism from orientation data to themselves is the identity.** -/
@[simp]
theorem signedMorseComplexIso_self [DecidablePred (· ∈ 𝔬.reversalSet 𝔬)] :
    hX.signedMorseComplexIso hsq hsq = Iso.refl _ := by
  ext n : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  -- The component in degree `n` is, by definition, the sign reversal of the graded chains on the
  -- empty reversal set.
  exact DFunLike.congr_fun (Finsupp.signReversal_eq_refl (R := R) (A := R)
    (S := {p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} |
      ↑p ∈ 𝔬.reversalSet 𝔬}) fun p hp ↦ by simp at hp) c

variable (hX) in
include hX in
/-- **The orientation-change isomorphisms compose.** For three choices `𝔬`, `𝔬'` and `𝔬''` of
orientation data, the isomorphism from `𝔬` to `𝔬'` followed by that from `𝔬'` to `𝔬''` is the
isomorphism from `𝔬` to `𝔬''`. -/
theorem signedMorseComplexIso_trans {𝔬'' : MorseOrientation f X}
    (hsq'' : hX.signedMorseBoundary 𝔬'' hf R ∘ₗ hX.signedMorseBoundary 𝔬'' hf R = 0)
    [DecidablePred (· ∈ 𝔬'.reversalSet 𝔬'')] [DecidablePred (· ∈ 𝔬.reversalSet 𝔬'')] :
    hX.signedMorseComplexIso hsq hsq' ≪≫ hX.signedMorseComplexIso hsq' hsq'' =
      hX.signedMorseComplexIso hsq hsq'' := by
  ext n : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  -- The components in degree `n` are, by definition, sign reversals of the graded chains, which
  -- compose by symmetric difference of the reversal sets.
  exact DFunLike.congr_fun (Finsupp.signReversal_trans_signReversal (R := R) (A := R)
    (S := {p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} |
      ↑p ∈ 𝔬.reversalSet 𝔬'})
    (T := {p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} |
      ↑p ∈ 𝔬'.reversalSet 𝔬''})
    (U := {p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} |
      ↑p ∈ 𝔬.reversalSet 𝔬''})
    fun _ ↦ MorseOrientation.mem_reversalSet_iff_xor hX hf) c

variable (hX) in
include hX in
/-- **The orientation-change isomorphisms are inverse to each other.** -/
theorem signedMorseComplexIso_symm [DecidablePred (· ∈ 𝔬'.reversalSet 𝔬)] :
    (hX.signedMorseComplexIso hsq hsq').symm = hX.signedMorseComplexIso hsq' hsq := by
  ext n : 2
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  -- The components in degree `n` are, by definition, inverse sign reversals of the graded chains
  -- on the same reversal set.
  exact DFunLike.congr_fun ((Finsupp.signReversal_symm (R := R) (A := R)).trans
    (Finsupp.signReversal_congr (R := R) (A := R)
      (S := {p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} |
        ↑p ∈ 𝔬.reversalSet 𝔬'})
      (T := {p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} |
        ↑p ∈ 𝔬'.reversalSet 𝔬})
      fun _ ↦ by rw [MorseOrientation.reversalSet_comm hX hf])) c

end IsAdaptedPseudoGradient

end TauCeti
