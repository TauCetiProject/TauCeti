/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Changing the orientations and the coefficients of the integral Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient
adapted to `f`. The integral Morse chain complex
`TauCeti.IsAdaptedPseudoGradient.signedMorseComplex 𝔬 hf R hsq` depends on orientation data
`𝔬 : TauCeti.MorseOrientation f X` (a Morse chart at each critical point, in which `X` is linear,
and an orientation of its coordinates of negative weight) and on a coefficient ring `R`. This
file shows that, up to isomorphism of chain complexes, it does not depend on the orientation data,
and that changing the coefficients along a homomorphism of commutative rings is extension of
scalars.

**Orientations.** Any two orientation data `𝔬` and `𝔬'` give isomorphic complexes. First, the
orientations of `𝔬` can be carried into the Morse charts of `𝔬'` along the changes of negative
coordinates (`TauCeti.MorseOrientation.transport`); this does not change any boundary coefficient
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff_transport`), since the signed counts of
trajectories do not depend on the charts. In the charts of `𝔬'`, the transported orientations and
those of `𝔬'` then differ by a reversal at the set of critical points where they are opposite
(`TauCeti.MorseOrientation.reversalSet`, `TauCeti.MorseOrientation.transport_reverse_reversalSet`).
So the integral boundary of `𝔬'` is the conjugate of that of `𝔬` by the involution negating the
coefficients on this set
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_eq_signReversal_comp`). In particular the
boundary squares to zero for `𝔬'` exactly when it does for `𝔬`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_comp_self_eq_zero_iff`), and the sign
reversals in each degree form an isomorphism of chain complexes
(`TauCeti.IsAdaptedPseudoGradient.signedMorseComplexOrientationIso`), hence give isomorphisms of
the integral Morse homology in every degree.

**Coefficients.** The boundary coefficients are integers, so a ring homomorphism `g : R →+* R'`
applied to the coefficients intertwines the boundaries, and `∂ ∘ ∂ = 0` with coefficients in `R`
implies it with coefficients in `R'`
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_comp_self_eq_zero_of_ringHom`); for `R = ℤ`
this gives every ring at once. For commutative rings the complex with coefficients in `R'` is the
extension of scalars of the complex with coefficients in `R`: the isomorphisms
`R' ⊗_R R^{(P)} ≅ R'^{(P)}` of free modules on the critical points `P` of each index,
`r' ⊗ c ↦ r' • g(c)` (`ModuleCat.extendScalarsFinsuppIso`), form an isomorphism of chain complexes
(`TauCeti.IsAdaptedPseudoGradient.signedMorseComplexExtendScalarsIso`). The ring `R'` may be in any
universe above that of `R`, so for `R = ℤ` this is the identification
`CM_*(f; R') = CM_*(f; ℤ) ⊗ R'` of the Morse complex with coefficients in any commutative ring with
the integral Morse complex tensored with that ring.

## Main definitions

* `TauCeti.MorseOrientation.transport`: the orientations of `𝔬` carried into the Morse charts of
  `𝔬'`.
* `TauCeti.MorseOrientation.reversalSet`: the critical points where the orientations of `𝔬'` are
  opposite to the transported orientations of `𝔬`.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseComplexOrientationIso`: the isomorphism of integral
  Morse complexes for two choices of orientation data.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseComplexExtendScalarsIso`: the isomorphism between the
  extension of scalars of the integral Morse complex along `g : R →+* R'` and the integral Morse
  complex with coefficients in `R'`.

## Main results

* `TauCeti.MorseOrientation.transport_reverse_reversalSet`: the transported orientations, reversed
  on the reversal set, are the orientations of `𝔬'`.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_eq_signReversal_comp` and
  `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryAt_eq_signReversal_comp`: the boundaries for
  two choices of orientation data are conjugate by a sign reversal.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_comp_self_eq_zero_iff`: whether the
  boundary squares to zero does not depend on the orientation data.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_comp_self_eq_zero_of_ringHom`: `∂² = 0`
  passes along ring homomorphisms of the coefficients.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (the Morse complex over `ℤ`, and its independence of the
  orientations).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients and the change of coefficients).
-/

public section

open CategoryTheory Set
open scoped ContDiff Manifold TensorProduct ChangeOfRings

namespace TauCeti

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseOrientation

variable (𝔬 𝔬' : MorseOrientation f X)

/-- **Transport of orientation data to other Morse charts.** The orientation data with the Morse
charts of `𝔬'` and, at each critical point `p`, the orientation of `𝔬` carried along the change of
negative coordinates `(𝔬.chart p).negativeChange (𝔬'.chart p)` from the chart of `𝔬` to that of
`𝔬'`. Both orient the unstable manifold of `p` in the same way, so the integral boundary does not
change (`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff_transport`). -/
-- The body is exposed: the type of `orientation` depends on `chart`, and stating
-- `transport_orientation` needs `(𝔬.transport 𝔬').chart` to reduce to `𝔬'.chart`.
@[expose]
noncomputable def transport : MorseOrientation f X where
  chart := 𝔬'.chart
  coord_mfderiv_chart := 𝔬'.coord_mfderiv_chart
  orientation p := Orientation.map _ ((𝔬.chart p).negativeChange (𝔬'.chart p)) (𝔬.orientation p)

/-- Transported orientation data have the Morse charts of the target data. -/
@[simp]
theorem transport_chart : (𝔬.transport 𝔬').chart = 𝔬'.chart :=
  rfl

/-- The orientation of the transported data at `p` is the orientation of `𝔬` carried along the
change of negative coordinates. -/
@[simp]
theorem transport_orientation (p : criticalPoints 𝓘(ℝ, E) f) :
    (𝔬.transport 𝔬').orientation p =
      Orientation.map _ ((𝔬.chart p).negativeChange (𝔬'.chart p)) (𝔬.orientation p) :=
  rfl

/-- The **reversal set** of two choices of orientation data: the critical points at which the
orientation of `𝔬'` is opposite to the orientation of `𝔬` transported into the Morse chart of
`𝔬'`. Reversing the transported orientations on this set gives `𝔬'`
(`TauCeti.MorseOrientation.transport_reverse_reversalSet`). -/
def reversalSet : Set (criticalPoints 𝓘(ℝ, E) f) :=
  {p | 𝔬'.orientation p ≠ (𝔬.transport 𝔬').orientation p}

/-- A critical point is in the reversal set when the orientation of `𝔬'` there is not the
transported orientation of `𝔬`. -/
@[simp]
theorem mem_reversalSet {p : criticalPoints 𝓘(ℝ, E) f} :
    p ∈ 𝔬.reversalSet 𝔬' ↔ 𝔬'.orientation p ≠ (𝔬.transport 𝔬').orientation p :=
  Iff.rfl

/-- Membership in the reversal set is decided classically. -/
noncomputable instance : DecidablePred (· ∈ 𝔬.reversalSet 𝔬') :=
  Classical.decPred _

/-- **Two choices of orientation data differ by a transport and a reversal**: reversing the
orientations of `𝔬`, transported into the Morse charts of `𝔬'`, at the points of the reversal
set gives `𝔬'`, since two orientations of a finite-dimensional real vector space are equal or
opposite. -/
theorem transport_reverse_reversalSet : (𝔬.transport 𝔬').reverse (𝔬.reversalSet 𝔬') = 𝔬' := by
  -- `reverse_eq_mk` reverses on the reversal set itself, with another decidability instance.
  classical
  convert (𝔬.transport 𝔬').reverse_eq_mk 𝔬'.orientation
  · exact 𝔬.mem_reversalSet 𝔬'
  · rfl

end MorseOrientation

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {hX : IsAdaptedPseudoGradient f X} (hf : IsMorse 𝓘(ℝ, E) f) {𝔬 𝔬' : MorseOrientation f X}

/-! ### Changing the orientations -/

section Orientation

variable {R : Type*} [Ring R]

include hf in
/-- **Transporting orientation data keeps the boundary coefficients**: the signed counts of
trajectories do not depend on the Morse charts, once the orientations are carried along the
changes of negative coordinates. -/
@[simp]
theorem signedMorseBoundaryCoeff_transport (p q : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedMorseBoundaryCoeff (𝔬.transport 𝔬') p q = hX.signedMorseBoundaryCoeff 𝔬 p q := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq,
      signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq]
    exact signedTrajectoryCount_map_negativeChange (𝔬.coord_mfderiv_chart p)
      (𝔬'.coord_mfderiv_chart p) (𝔬.coord_mfderiv_chart q) (𝔬'.coord_mfderiv_chart q) hf _ _ hpq
  · simp [hpq]

/-- **Transporting orientation data keeps the integral boundary.** -/
@[simp]
theorem signedMorseBoundary_transport :
    hX.signedMorseBoundary (𝔬.transport 𝔬') hf R = hX.signedMorseBoundary 𝔬 hf R :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by
    rw [signedMorseBoundary_single_apply, signedMorseBoundary_single_apply,
      signedMorseBoundaryCoeff_transport hf]

/-- **Transporting orientation data keeps the graded integral boundary.** -/
@[simp]
theorem signedMorseBoundaryAt_transport (n : ℕ) :
    hX.signedMorseBoundaryAt (𝔬.transport 𝔬') hf R n = hX.signedMorseBoundaryAt 𝔬 hf R n :=
  Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ by
    rw [signedMorseBoundaryAt_single_apply, signedMorseBoundaryAt_single_apply,
      signedMorseBoundaryCoeff_transport hf]

variable (𝔬 𝔬') in
/-- **Changing the orientation data conjugates the integral boundary.** The integral boundary for
`𝔬'` is the conjugate of that for `𝔬` by the involution `Finsupp.signReversal` negating the
coefficients of the critical points of the reversal set `𝔬.reversalSet 𝔬'`, where the orientations
of `𝔬'` are opposite to those of `𝔬`. The Morse charts of `𝔬` and `𝔬'` may differ. -/
theorem signedMorseBoundary_eq_signReversal_comp :
    hX.signedMorseBoundary 𝔬' hf R =
      (Finsupp.signReversal R (𝔬.reversalSet 𝔬')).toLinearMap ∘ₗ hX.signedMorseBoundary 𝔬 hf R ∘ₗ
        (Finsupp.signReversal R (𝔬.reversalSet 𝔬')).toLinearMap := by
  conv_lhs => rw [← 𝔬.transport_reverse_reversalSet 𝔬']
  rw [signedMorseBoundary_reverse, signedMorseBoundary_transport]

variable (𝔬 𝔬') in
/-- **Changing the orientation data conjugates the graded integral boundary**, by the sign
reversals of the graded chains on the reversal set `𝔬.reversalSet 𝔬'`. -/
theorem signedMorseBoundaryAt_eq_signReversal_comp (n : ℕ) :
    hX.signedMorseBoundaryAt 𝔬' hf R n =
      (Finsupp.signReversal R {q | ↑q ∈ 𝔬.reversalSet 𝔬'}).toLinearMap ∘ₗ
        hX.signedMorseBoundaryAt 𝔬 hf R n ∘ₗ
          (Finsupp.signReversal R {p | ↑p ∈ 𝔬.reversalSet 𝔬'}).toLinearMap := by
  conv_lhs => rw [← 𝔬.transport_reverse_reversalSet 𝔬']
  rw [signedMorseBoundaryAt_reverse, signedMorseBoundaryAt_transport]

variable (𝔬 𝔬') in
/-- **`∂² = 0` does not depend on the orientation data**: the integral boundary for `𝔬'` squares to
zero exactly when the one for `𝔬` does, since the two are conjugate by an involution. -/
theorem signedMorseBoundary_comp_self_eq_zero_iff :
    hX.signedMorseBoundary 𝔬' hf R ∘ₗ hX.signedMorseBoundary 𝔬' hf R = 0 ↔
      hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 := by
  have h : hX.signedMorseBoundary 𝔬' hf R =
      (Finsupp.signReversal R (𝔬.reversalSet 𝔬')).conjRingEquiv (hX.signedMorseBoundary 𝔬 hf R) :=
    LinearMap.ext fun c ↦ by
      rw [LinearEquiv.conjRingEquiv_apply_apply, Finsupp.signReversal_symm,
        signedMorseBoundary_eq_signReversal_comp hf 𝔬 𝔬', LinearMap.comp_apply,
        LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul,
    map_eq_zero_iff _ (RingEquiv.injective _)]

variable (𝔬 𝔬') in
/-- **The integral Morse complexes of two choices of orientation data are isomorphic.** In degree
`n` the isomorphism negates the coefficients of the critical points of index `n` in the reversal
set `𝔬.reversalSet 𝔬'`, where the orientations of `𝔬'` are opposite to those of `𝔬`. In
particular the integral Morse homology does not depend on the orientations of the unstable
manifolds, nor on the Morse charts in which they are read. -/
noncomputable def signedMorseComplexOrientationIso
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) :
    hX.signedMorseComplex 𝔬 hf R hsq ≅
      hX.signedMorseComplex 𝔬' hf R ((signedMorseBoundary_comp_self_eq_zero_iff hf 𝔬 𝔬').2 hsq) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Finsupp.signReversal R {p | ↑p ∈ 𝔬.reversalSet 𝔬'}).toModuleIso)
    fun i j hij ↦ by
      obtain rfl : j + 1 = i := hij
      have H : hX.signedMorseBoundaryAt 𝔬' hf R j ∘ₗ
          (Finsupp.signReversal R {p | ↑p ∈ 𝔬.reversalSet 𝔬'}).toLinearMap =
            (Finsupp.signReversal R {q | ↑q ∈ 𝔬.reversalSet 𝔬'}).toLinearMap ∘ₗ
              hX.signedMorseBoundaryAt 𝔬 hf R j :=
        LinearMap.ext fun c ↦ by simp [signedMorseBoundaryAt_eq_signReversal_comp hf 𝔬 𝔬' j]
      rw [signedMorseComplex_d, signedMorseComplex_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun c ↦ LinearMap.congr_fun H c)

/-- The component in degree `n` of the isomorphism of integral Morse complexes for two choices of
orientation data negates the coefficients of the points of the reversal set. -/
@[simp]
theorem signedMorseComplexOrientationIso_hom_f_apply
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :
    (signedMorseComplexOrientationIso hf 𝔬 𝔬' hsq).hom.f n c =
      Finsupp.signReversal R
        {p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} |
          ↑p ∈ 𝔬.reversalSet 𝔬'} c :=
  (rfl)

/-- The component in degree `n` of the inverse of the isomorphism of integral Morse complexes for
two choices of orientation data again negates the coefficients of the points of the reversal
set. -/
@[simp]
theorem signedMorseComplexOrientationIso_inv_f_apply
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :
    (signedMorseComplexOrientationIso hf 𝔬 𝔬' hsq).inv.f n c =
      Finsupp.signReversal R
        {p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} |
          ↑p ∈ 𝔬.reversalSet 𝔬'} c :=
  DFunLike.congr_fun Finsupp.signReversal_symm c

end Orientation

/-! ### Changing the coefficients -/

section Coefficients

variable (𝔬) in
include hf in
/-- **`∂² = 0` passes along ring homomorphisms of the coefficients.** If the integral boundary with
coefficients in `R` squares to zero, so does the one with coefficients in `R'`, for any ring
homomorphism `g : R →+* R'`: the boundary coefficients are integers, so `g` intertwines the two
boundaries, and every chain with coefficients in `R'` is a combination of images of chains with
coefficients in `R`. For `R = ℤ` this gives `∂² = 0` with coefficients in every ring at once. -/
theorem signedMorseBoundary_comp_self_eq_zero_of_ringHom {R R' : Type*} [Ring R] [Ring R']
    (g : R →+* R')
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) :
    hX.signedMorseBoundary 𝔬 hf R' ∘ₗ hX.signedMorseBoundary 𝔬 hf R' = 0 := by
  refine Finsupp.lhom_ext fun p a ↦ ?_
  calc hX.signedMorseBoundary 𝔬 hf R' (hX.signedMorseBoundary 𝔬 hf R' (Finsupp.single p a))
      = a • hX.signedMorseBoundary 𝔬 hf R' (hX.signedMorseBoundary 𝔬 hf R'
          (Finsupp.mapRange g (map_zero g) (Finsupp.single p 1))) := by
        simp [← map_smul, Finsupp.smul_single]
    _ = a • Finsupp.mapRange g (map_zero g)
          ((hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R)
            (Finsupp.single p 1)) := by
        rw [LinearMap.comp_apply, mapRange_signedMorseBoundary, mapRange_signedMorseBoundary]
    _ = 0 := by simp [hsq]

variable {R : Type u} {R' : Type (max u v)} [CommRing R] [CommRing R'] (g : R →+* R')

variable (𝔬) in
open scoped Classical in
/-- **Change of coefficients for the integral Morse complex.** For a homomorphism `g : R →+* R'` of
commutative rings, the extension of scalars along `g` of the integral Morse complex with
coefficients in `R` is the integral Morse complex with coefficients in `R'`. In degree `n` the
isomorphism sends `r' ⊗ c` to `r' • g(c)`, where `g(c)` applies `g` to the coefficients of the chain
`c` (`TauCeti.IsAdaptedPseudoGradient.signedMorseComplexExtendScalarsIso_hom_f_tmul`). The ring
`R'` may be in any universe above that of `R`, so for `R = ℤ` this identifies the integral Morse
complex with coefficients in any commutative ring `R'` with `CM_*(f; ℤ) ⊗ R'`. -/
noncomputable def signedMorseComplexExtendScalarsIso
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) :
    ((ModuleCat.extendScalars g).mapHomologicalComplex _).obj
        (hX.signedMorseComplex 𝔬 hf R hsq) ≅
      hX.signedMorseComplex 𝔬 hf R' (signedMorseBoundary_comp_self_eq_zero_of_ringHom hf 𝔬 g hsq) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ ModuleCat.extendScalarsFinsuppIso g _)
    fun i j hij ↦ by
      obtain rfl : j + 1 = i := hij
      rw [Functor.mapHomologicalComplex_obj_d, signedMorseComplex_d, signedMorseComplex_d]
      exact (ModuleCat.extendScalarsFinsuppIso_hom_naturality g
        (mapRange_signedMorseBoundaryAt hf g)).symm

open scoped Classical in
/-- The component in degree `n` of the change of coefficients sends `r' ⊗ c` to `r' • g(c)`, where
the chain `g(c)` is obtained by applying `g` to the coefficients of `c`. -/
theorem signedMorseComplexExtendScalarsIso_hom_f_tmul
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (n : ℕ) (r' : R')
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :
    (signedMorseComplexExtendScalarsIso hf 𝔬 g hsq).hom.f n (r' ⊗ₜ[R,g] c) =
      r' • Finsupp.mapRange g (map_zero g) c :=
  ModuleCat.extendScalarsFinsuppIso_hom_tmul g r' c

open scoped Classical in
/-- The component in degree `n` of the change of coefficients sends `1 ⊗ c` to the chain `g(c)`
obtained by applying `g` to the coefficients of `c`. -/
theorem signedMorseComplexExtendScalarsIso_hom_f_one_tmul
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (n : ℕ)
    (c : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n} →₀ R) :
    (signedMorseComplexExtendScalarsIso hf 𝔬 g hsq).hom.f n ((1 : R') ⊗ₜ[R,g] c) =
      Finsupp.mapRange g (map_zero g) c :=
  ModuleCat.extendScalarsFinsuppIso_hom_one_tmul g c

open scoped Classical in
/-- The component in degree `n` of the inverse of the change of coefficients sends the chain
`r' • p` of a critical point `p` of index `n` to `r' ⊗ p`. -/
theorem signedMorseComplexExtendScalarsIso_inv_f_single
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (n : ℕ)
    (p : {p : criticalPoints 𝓘(ℝ, E) f // manifoldMorseIndex 𝓘(ℝ, E) f p = n}) (r' : R') :
    (signedMorseComplexExtendScalarsIso hf 𝔬 g hsq).inv.f n (Finsupp.single p r') =
      r' ⊗ₜ[R,g] Finsupp.single p (1 : R) :=
  ModuleCat.extendScalarsFinsuppIso_inv_single g p r'

end Coefficients

end IsAdaptedPseudoGradient

end TauCeti
