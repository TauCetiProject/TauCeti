/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Reflection
import TauCeti.Analysis.Complex.CauchyRiemann.NormalDerivative
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Interior
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.PartialDerivative
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Complex.Wirtinger.RealBoundary.Reflection
import TauCeti.Analysis.Sobolev.Local.Multiplication.HalfDisc.Higher
import TauCeti.Analysis.Sobolev.Local.Reflection.Tangential
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Higher-order regularity up to the real axis for rough Cauchy–Riemann equations

Let `Ω ⊆ ℂ` be an open set invariant under complex conjugation, write `z = s + i t` and
`H = Ω ∩ {0 ≤ t}`, and let `V` be a finite-dimensional real inner product space with a continuous
linear automorphism `R` (for `V = ℂⁿ` with real boundary values, coordinatewise conjugation).
Consider a weak solution `ξ` up to the real axis of

`∂_s ξ + J ∂_t ξ + S ξ = η`

with `J² = -1`, `p > 2`, `1/p + 1/q < 1` and `q ≤ p`. The order-zero reflection
`TauCeti.IsWeakCRSolutionHalf.isWeakCRSolution_crReflection` turns it into a weak solution on all of
`Ω` of the reflected equation, for the coefficients `crReflectionCoeff R J`,
`crReflectionDeriv R DJ` and `crReflectionZeroth R S`, and the twisted reflections
`TauCeti.twistedReflection R` of `ξ` and `η`. Assume that the reflected coefficients are Sobolev
coefficients on `Ω`, the hypothesis of `TauCeti.IsWeakCRSolutionHalf.memWkpLoc_one`. This file
proves that `ξ` gains one derivative over `η` at every order up to the axis: if
`J, S ∈ W^{k,p}_loc(H)` and `η ∈ W^{k,q}_loc(H)`, then `ξ ∈ W^{k+1,q}_loc(H)`
(`TauCeti.IsWeakCRSolutionHalf.memWkpLoc_succ`). This is the weak regularity statement of
McDuff–Salamon, Proposition B.4.9, with a totally real boundary condition and a zeroth-order term.

The reflected coefficient `crReflectionCoeff R J` is in general only of class `W^{1,p}` across the
axis, whatever the regularity of `J` up to the axis, so the interior theorem
`TauCeti.IsWeakCRSolution.memWkpLoc_succ` does not apply to the doubled equation beyond `k = 0`.
The induction instead runs through the tangential derivative `∂_s`:

* *Tangential step* (`TauCeti.IsWeakCRSolution.crReflection_partial_one`). Reflection commutes
  with `∂_s`, and tangential weak derivatives glue across the axis with no boundary condition
  (`TauCeti.HasWeakLineDerivOn.twistedReflection_one`). So the case `e = 1` of the differentiated
  equation `TauCeti.IsSobolevCRCoefficients.isWeakCRSolution_partial` on the doubled domain says
  that the reflection of `∂_s ξ` solves the reflected form of
  `∂_s (∂_s ξ) + J ∂_t (∂_s ξ) + (S + (∂_s J) J) ∂_s ξ = ∂_s η - (∂_s J) J (S ξ - η) - (∂_s S) ξ`.
  The term `(∂_s J) ∂_t ξ` of the differentiated equation has been rewritten with
  `∂_t ξ = J (∂_s ξ + S ξ - η)`, and its part `(∂_s J) J ∂_s ξ` moved into the zeroth-order
  coefficient, so that the right side is in `W^{k,q}_loc` as soon as `ξ ∈ W^{k+1,q}_loc`, also at
  `k = 0`. The equation is again of the reflected kind, with the same `J`.
* *Normal derivative* (`TauCeti.memWkpLoc_succ_of_ae_cauchyRiemann_halfPlane`). Once
  `∂_s ξ ∈ W^{k+1,q}_loc(H)`, the equation gives `∂_t ξ = J (∂_s ξ + S ξ - η)`, using
  `J⁻¹ = -J`, which is in `W^{k+1,q}_loc(H)` by the half-disc products
  `TauCeti.MemWkpLoc.clm_apply_succ_halfPlane`.

## Main results

* `TauCeti.IsWeakCRSolution.crReflection_partial_one`: the tangential derivative of a reflected
  solution is a reflected solution.
* `TauCeti.memWkpLoc_succ_of_ae_cauchyRiemann_halfPlane`: recovery of the normal derivative.
* `TauCeti.ae_cauchyRiemann_of_crReflection`, `TauCeti.hasWeakFDerivOn_of_crReflectionCoeff` and
  `TauCeti.memWkpLoc_one_twistedReflection`: the equation, the derivative of `J` and order-one
  regularity, read off a reflected solution.
* `TauCeti.IsWeakCRSolution.memWkpLoc_succ_of_crReflection`: `W^{k+1,q}` regularity up to the
  axis for a reflected solution.
* `TauCeti.IsWeakCRSolutionHalf.memWkpLoc_succ`: `W^{k+1,q}` regularity up to the axis for a weak
  solution with a totally real boundary condition.
* `TauCeti.IsWeakCRSolutionHalf.memWkpLoc_succ_of_hasWeakFDerivOn`: the same with hypotheses on
  the half-plane coefficients in place of the hypothesis that the reflected coefficients are
  Sobolev coefficients: `J` continuous up to the axis with weak derivative `DJ` in `Lᵖ_loc`,
  anticommuting with `R` on the axis (`TauCeti.isSobolevCRCoefficients_crReflection`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Proposition B.4.9.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Complex Set Filter ContinuousLinearMap
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {R : V ≃L[ℝ] V} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
  {ξ η : ℂ → V}

/-! ### Recovery of the normal derivative -/

/-- **Recovery of the normal derivative.** Let `ξ ∈ W^{k+1,q}_loc(Ω ∩ {0 ≤ t})` have weak
derivative `Dξ` on the open upper part and solve `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on
`Ω ∩ {0 ≤ t}`, with `J² = -1` there, `p > 2` and `1 < q ≤ p`. If `J, S ∈ W^{k+1,p}_loc` and
`η ∈ W^{k+1,q}_loc` up to the axis and the tangential derivative `∂_s ξ = Dξ · 1` is in
`W^{k+1,q}_loc` up to the axis, then `ξ ∈ W^{k+2,q}_loc(Ω ∩ {0 ≤ t})`: the normal derivative is
`∂_t ξ = J (∂_s ξ + S ξ - η)`. -/
theorem memWkpLoc_succ_of_ae_cauchyRiemann_halfPlane [FiniteDimensional ℝ V] {p q : ℝ≥0} {k : ℕ}
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {Dξ : ℂ → ℂ →L[ℝ] V}
    (hξ : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) ξ)
    (hDξ : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) ξ Dξ)
    (heq : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
      Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hJ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) J)
    (hS : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) S)
    (hη : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) η)
    (h1 : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => Dξ z 1)) :
    MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1 + 1) ξ := by
  have hI : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => Dξ z I) :=
    (hJ.clm_apply_succ_halfPlane hp hq hqp
      ((h1.add (hS.clm_apply_succ_halfPlane hp hq hqp hξ)).sub hη)).congr_ae
      (((ae_cauchyRiemann_iff_ae_apply_I_eq
        (hJ2.mono fun _ => mul_self_eq_neg_one_iff_comp_eq_neg_id.1)).1 heq).mono
          fun _ => Eq.symm)
  refine memWkpLoc_succ_iff.2 ⟨hξ.memLpLoc, Dξ, hDξ, ?_⟩
  rw [fun_eq_smulRightL_reCLM_add_smulRightL_imCLM Dξ]
  exact (h1.clm_comp _).add (hI.clm_comp _)

/-! ### The tangential step on the doubled domain -/

omit [CompleteSpace V] in
/-- Off the real axis, the reflection of `(∂_s J) J` is the product of the reflections of `∂_s J`
and `J`. -/
private theorem crReflectionZeroth_comp_apply {z : ℂ} (hz : z.im ≠ 0) (v : V) :
    crReflectionZeroth R (fun w => (DJ w 1).comp (J w)) z v =
      crReflectionDeriv R DJ z 1 (crReflectionCoeff R J z v) := by
  rcases lt_or_gt_of_ne hz with hz | hz
  · simp [crReflectionZeroth_apply_of_im_neg hz, crReflectionDeriv_apply_of_im_neg hz,
      crReflectionCoeff_apply_of_im_neg hz]
  · simp [crReflectionZeroth_of_im_pos hz, crReflectionDeriv_of_im_pos hz,
      crReflectionCoeff_of_im_pos hz]

omit [CompleteSpace V] in
/-- Off the real axis, the right side of the tangential step is the reflection of
`∂_s η - (∂_s J) J (S ξ - η) - (∂_s S) ξ`. -/
private theorem twistedReflection_partial_one_rhs {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {Dη : ℂ → ℂ →L[ℝ] V} {z : ℂ} (hz : z.im ≠ 0) :
    twistedReflection (R : V →L[ℝ] V) (fun w => Dη w 1) z -
        crReflectionDeriv R DJ z 1 (crReflectionCoeff R J z
          (crReflectionZeroth R S z (twistedReflection (R : V →L[ℝ] V) ξ z) -
            twistedReflection (R : V →L[ℝ] V) η z)) -
        crReflectionZeroth R (fun w => DS w 1) z (twistedReflection (R : V →L[ℝ] V) ξ z) =
      twistedReflection (R : V →L[ℝ] V)
        (fun w => Dη w 1 - DJ w 1 (J w (S w (ξ w) - η w)) - DS w 1 (ξ w)) z := by
  rcases lt_or_gt_of_ne hz with hz | hz
  · simp [twistedReflection_of_im_neg hz, crReflectionZeroth_apply_of_im_neg hz,
      crReflectionDeriv_apply_of_im_neg hz, crReflectionCoeff_apply_of_im_neg hz]
  · simp [twistedReflection_of_im_pos hz, crReflectionZeroth_of_im_pos hz,
      crReflectionDeriv_of_im_pos hz, crReflectionCoeff_of_im_pos hz]

/-- **The tangential step.** Let `Ω` be invariant under conjugation, let the reflected coefficients
be Sobolev coefficients on `Ω` with `1/p + 1/q ≤ 1` and `p, q` finite, and let the twisted
reflection of `ξ` be a weak solution on `Ω` of the reflected equation with right side the twisted
reflection of `η`, of class `W^{1,q}_loc(Ω)`. Let `J² = -1` almost everywhere on `Ω ∩ {0 ≤ t}`,
and let `Dξ`, `DS` and `Dη` be weak derivatives of `ξ`, `S` and `η` on the open upper part, with
`Dξ` and `Dη` integrable and `DS` locally `Lᵖ` up to the axis, and `(∂_s J) J ∈ Lᵖ_loc` up to
the axis. Then the twisted reflection of `∂_s ξ` is a weak solution on `Ω` of the reflected
equation with zeroth-order coefficient `S + (∂_s J) J` and right side the twisted reflection of
`∂_s η - (∂_s J) J (S ξ - η) - (∂_s S) ξ`. -/
theorem IsWeakCRSolution.crReflection_partial_one [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hc : IsSobolevCRCoefficients p Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S))
    (h : IsWeakCRSolution q Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S) (twistedReflection (R : V →L[ℝ] V) ξ)
      (twistedReflection (R : V →L[ℝ] V) η))
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hw : MemWkpLoc q Ω 1 (twistedReflection (R : V →L[ℝ] V) ξ))
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hDξ : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) ξ Dξ)
    (hDξ1 : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dξ)
    (hDS : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) S DS)
    (hDSp : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DS)
    (hDη : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) η Dη)
    (hDη1 : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) Dη)
    (hM : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (fun z => (DJ z 1).comp (J z))) :
    IsWeakCRSolution q Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R (fun z => S z + (DJ z 1).comp (J z)))
      (twistedReflection (R : V →L[ℝ] V) (fun z => Dξ z 1))
      (twistedReflection (R : V →L[ℝ] V)
        (fun z => Dη z 1 - DJ z 1 (J z (S z (ξ z) - η z)) - DS z 1 (ξ z))) := by
  have hp1 : 1 ≤ p := ENNReal.inv_le_one.1 (le_self_add.trans hpq)
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hJJ := ae_crReflectionCoeff_mul_self (R := R) hΩ hJ2
  obtain ⟨Dξ', hDξ', hDξ'q⟩ := hw.exists_weakFDeriv_of_isOpen
  have heq := (hc.isWeakCRSolution_iff_ae hpq hp hq hDξ' hw.memLpLoc hDξ'q.memLpLoc
    h.locallyIntegrableOn).1 h
  -- The tangential derivatives of the reflected solution, zeroth-order term and right side.
  have hξs := (hDξ.hasWeakLineDerivOn 1).twistedReflection_one hΩ
    (h.memLpLoc.of_twistedReflection.mono_exponent hq1)
    (hDξ1.clm_comp (apply ℝ V 1)) (R : V →L[ℝ] V)
  have hSs : HasWeakLineDerivOn volume Ω (crReflectionZeroth R S)
      (crReflectionZeroth R fun z => DS z 1) 1 := by
    rw [crReflectionZeroth_def, crReflectionZeroth_def]
    exact (hDS.hasWeakLineDerivOn 1).twistedReflection_one hΩ
      (((memLpLoc_crReflectionZeroth_iff hΩ).1 hc.memLpLoc_zeroth).mono_exponent hp1)
      ((hDSp.clm_comp (apply ℝ (V →L[ℝ] V) 1)).mono_exponent hp1) _
  have hηs := (hDη.hasWeakLineDerivOn 1).twistedReflection_one hΩ
    ((memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).2
      h.locallyIntegrableOn).of_twistedReflection
    (hDη1.clm_comp (apply ℝ V 1)) (R : V →L[ℝ] V)
  have hT := (hc.isWeakCRSolution_partial hpq hp hq hDξ' hw.memLpLoc hDξ'q.memLpLoc heq hSs
    ((memLpLoc_crReflectionZeroth_iff hΩ).2 (hDSp.clm_comp (apply ℝ (V →L[ℝ] V) 1)))
    hηs).add_zeroth ((memLpLoc_crReflectionZeroth_iff (R := R) hΩ).2 hM) hpq
  have hsol := (hDξ'.hasWeakLineDerivOn 1).ae_eq hξs
  refine (isWeakCRSolution_congr_ae .rfl .rfl
    (.of_forall fun z => (congrFun (crReflectionZeroth_add R S _) z).symm) hsol ?_).1 hT
  -- Eliminate `∂_t` of the reflected solution with the doubled equation.
  filter_upwards [heq, hJJ, ae_restrict_of_ae Complex.ae_im_ne_zero] with z hz hJz hz0
  rw [(add_apply_add_eq_iff_eq_apply_add_sub (mul_self_eq_neg_one_iff_comp_eq_neg_id.1 hJz)).1 hz,
    crReflectionZeroth_comp_apply hz0,
    ← twistedReflection_partial_one_rhs hz0]
  simp only [map_add, map_sub]
  abel

/-! ### Regularity of every order -/

/-- **The equation up to the axis from the reflected equation.** Let the reflected coefficients be
Sobolev coefficients on `Ω` with `1/p + 1/q ≤ 1` and `p, q` finite, and let the twisted reflection
of `ξ`, of class `W^{1,q}_loc(Ω)`, be a weak solution on `Ω` of the reflected equation with right
side the twisted reflection of `η`. Then for every weak derivative `Dξ` of `ξ` on the open upper
part, `∂_s ξ + J ∂_t ξ + S ξ = η` holds almost everywhere on `Ω ∩ {0 ≤ t}`. -/
theorem ae_cauchyRiemann_of_crReflection [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hc : IsSobolevCRCoefficients p Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S))
    (h : IsWeakCRSolution q Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S) (twistedReflection (R : V →L[ℝ] V) ξ)
      (twistedReflection (R : V →L[ℝ] V) η))
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hw : MemWkpLoc q Ω 1 (twistedReflection (R : V →L[ℝ] V) ξ)) {Dξ : ℂ → ℂ →L[ℝ] V}
    (hDξ : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) ξ Dξ) :
    ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
      Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z := by
  obtain ⟨Dξ', hDξ', hDξ'q⟩ := hw.exists_weakFDeriv_of_isOpen
  have heq := (hc.isWeakCRSolution_iff_ae hpq hp hq hDξ' hw.memLpLoc hDξ'q.memLpLoc
    h.locallyIntegrableOn).1 h
  have hU : Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ≤ Ω :=
    fun z hz => (interior_subset hz).1
  have hD := (hDξ'.mono hU).ae_eq
    (hDξ.congr_ae ((ae_restrict_interior_inter_setOf_im_nonneg_im_pos Ω).mono fun _ hz =>
      (twistedReflection_of_im_pos hz).symm))
  rw [Measure.restrict_congr_set (inter_setOf_im_nonneg_ae_eq_interior Ω)]
  filter_upwards [ae_restrict_interior_inter_setOf_im_nonneg_im_pos Ω,
    ae_restrict_of_ae_restrict_of_subset hU heq, hD]
    with z hz0 hz hDz
  simpa [hDz, hz0] using hz

omit [CompleteSpace V] in
/-- If the reflected coefficients are Sobolev coefficients on `Ω`, then `DJ` is a weak derivative
of `J` on the open upper part, where the reflections agree with `J` and `DJ`. -/
theorem hasWeakFDerivOn_of_crReflectionCoeff {p : ℝ≥0∞}
    (hc : IsSobolevCRCoefficients p Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S)) :
    HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) J DJ :=
  ((hc.hasWeakFDerivOn.mono (show Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ≤ Ω from
    fun _ hz => (interior_subset hz).1)).congr_ae
    ((ae_restrict_interior_inter_setOf_im_nonneg_im_pos Ω).mono fun _ hz => by
      simp [hz])).congr_ae_deriv
    ((ae_restrict_interior_inter_setOf_im_nonneg_im_pos Ω).mono fun _ hz => by simp [hz])

/-- **Order-one regularity on the doubled domain.** Let `Ω` be invariant under conjugation, let
the reflected coefficients be Sobolev coefficients on `Ω` for some `p > 2`, with `J² = -1` almost
everywhere on `Ω ∩ {0 ≤ t}`, and let the twisted reflection of `ξ` be a weak solution on `Ω` of the
reflected equation with right side the twisted reflection of `η`, for `1/p + 1/q < 1` and `q ≤ p`.
If `η ∈ L^q_loc` up to the axis, then the twisted reflection of `ξ` is in `W^{1,q}_loc(Ω)`. -/
theorem memWkpLoc_one_twistedReflection [FiniteDimensional ℝ V] {p q : ℝ≥0}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hp : 2 < p) (hq : 1 < q)
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p)
    (h : IsWeakCRSolution q Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S) (twistedReflection (R : V →L[ℝ] V) ξ)
      (twistedReflection (R : V →L[ℝ] V) η))
    (hc : IsSobolevCRCoefficients p Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S))
    (hη : MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η) :
    MemWkpLoc q Ω 1 (twistedReflection (R : V →L[ℝ] V) ξ) :=
  h.memWkpLoc_one_of_le hc (by exact_mod_cast hp) (ae_crReflectionCoeff_mul_self hΩ hJ2) hpq
    (by exact_mod_cast hq) ENNReal.coe_ne_top (by exact_mod_cast hqp) (hη.twistedReflection hΩ _)

/-- **`W^{k+1,q}` regularity up to the real axis for a reflected solution.** Let `Ω` be invariant
under conjugation, let the reflected coefficients be Sobolev coefficients on `Ω` for some `p > 2`,
with `J² = -1` almost everywhere on `Ω ∩ {0 ≤ t}`, and let the twisted reflection of `ξ` be a weak
solution on `Ω` of the reflected equation with right side the twisted reflection of `η`, for
`1/p + 1/q < 1` and `q ≤ p`. If `J, S ∈ W^{k,p}_loc` and `η ∈ W^{k,q}_loc` up to the axis, then
`ξ ∈ W^{k+1,q}_loc(Ω ∩ {0 ≤ t})`. -/
theorem IsWeakCRSolution.memWkpLoc_succ_of_crReflection [FiniteDimensional ℝ V] {p q : ℝ≥0}
    {k : ℕ} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hc : IsSobolevCRCoefficients p Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S))
    (h : IsWeakCRSolution q Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S) (twistedReflection (R : V →L[ℝ] V) ξ)
      (twistedReflection (R : V →L[ℝ] V) η))
    (hp : 2 < p) (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p)
    (hJ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k J)
    (hS : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k S)
    (hη : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k η) :
    MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) ξ := by
  have hq : 1 < q := by
    have : (1 : ℝ≥0∞) < q := ENNReal.one_lt_right_of_inv_add_inv_lt_one hpq
    exact_mod_cast this
  have hDJ := hasWeakFDerivOn_of_crReflectionCoeff hc
  induction k generalizing S ξ η with
  | zero =>
    exact ((memWkpLoc_one_twistedReflection hΩ hp hq hJ2 hpq hqp h hc hη.memLpLoc).mono
      inter_subset_left).congr_ae
      (ae_restrict_of_ae_restrict_of_subset inter_subset_right
        (twistedReflection_ae_eq_restrict _ ξ))
  | succ k ih =>
    have hξ := ih hc h hJ.of_succ hS.of_succ hη.of_succ
    have hw := memWkpLoc_one_twistedReflection hΩ hp hq hJ2 hpq hqp h hc hη.memLpLoc
    obtain ⟨Dξ, hDξ, hDξk⟩ := hξ.exists_weakFDeriv
    obtain ⟨DS, hDS, hDSk⟩ := hS.exists_weakFDeriv
    obtain ⟨Dη, hDη, hDηk⟩ := hη.exists_weakFDeriv
    have hDJ1 := (hJ.memWkpLoc_of_hasWeakFDerivOn_inter_setOf_im_nonneg hDJ).clm_comp
      (apply ℝ (V →L[ℝ] V) 1)
    have hM := hDJ1.bilin_of_memWkpLoc_succ_halfPlane (compL ℝ V V V) hp (hq.trans_le hqp)
      le_rfl hJ
    have hT := h.crReflection_partial_one hΩ hc hpq.le ENNReal.coe_ne_top ENNReal.coe_ne_top hJ2
      hw hDξ (hDξk.memLpLoc.mono_exponent (by exact_mod_cast hq.le)) hDS hDSk.memLpLoc hDη
      (hDηk.memLpLoc.mono_exponent (by exact_mod_cast hq.le)) hM.memLpLoc
    -- The right side of the tangential step is in `W^{k,q}_loc` up to the axis.
    have hη' := ((hDηk.clm_comp (apply ℝ V 1)).sub
      (hDJ1.bilin_of_memWkpLoc_succ_halfPlane (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp
        (hJ.clm_apply_succ_halfPlane hp hq hqp
          ((hS.clm_apply_succ_halfPlane hp hq hqp hξ).sub hη)))).sub
      ((hDSk.clm_comp (apply ℝ (V →L[ℝ] V) 1)).bilin_of_memWkpLoc_succ_halfPlane
        (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq hqp hξ)
    have hc' : IsSobolevCRCoefficients p Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
        (crReflectionZeroth R fun z => S z + (DJ z 1).comp (J z)) := by
      have := hc.add_zeroth ((memLpLoc_crReflectionZeroth_iff (R := R) hΩ).2 hM.memLpLoc)
      rwa [← Pi.add_def, ← crReflectionZeroth_add] at this
    have h1 := ih hc' hT hJ.of_succ (hS.of_succ.add hM) hη'
    exact memWkpLoc_succ_of_ae_cauchyRiemann_halfPlane hp hq hqp hξ hDξ
      (ae_cauchyRiemann_of_crReflection hc h hpq.le ENNReal.coe_ne_top ENNReal.coe_ne_top
        hw hDξ) hJ2 hJ hS hη h1

/-- **`W^{k+1,q}` regularity up to the real axis** (McDuff–Salamon, Proposition B.4.9, with a
totally real boundary condition). Let `Ω` be invariant under conjugation and `R` an isometric
involution of the finite-dimensional space `V` whose fixed vectors lie in `Λ`, and suppose that the
reflected coefficients are Sobolev coefficients on `Ω` for some `p > 2`, with `J² = -1` almost
everywhere on `Ω ∩ {0 ≤ t}`. Let `ξ ∈ L^q_loc` be a weak solution up to the real axis of
`∂_s ξ + J ∂_t ξ + S ξ = η` with boundary subspace `Λ`, for `1/p + 1/q < 1` and `q ≤ p`. If
`J, S ∈ W^{k,p}_loc` and `η ∈ W^{k,q}_loc` up to the axis, then
`ξ ∈ W^{k+1,q}_loc(Ω ∩ {0 ≤ t})`.

For `k = 0` this is `TauCeti.IsWeakCRSolutionHalf.memWkpLoc_one` with `r = q`. -/
theorem IsWeakCRSolutionHalf.memWkpLoc_succ [FiniteDimensional ℝ V] {p q : ℝ≥0} {k : ℕ}
    {Λ : Submodule ℝ V} {R : V ≃ₗᵢ[ℝ] V} (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η)
    (hR : Function.Involutive R) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΛ : ∀ v, R v = v → v ∈ Λ)
    (hc : IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
      (crReflectionDeriv R.toContinuousLinearEquiv DJ)
      (crReflectionZeroth R.toContinuousLinearEquiv S))
    (hp : 2 < p) (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p)
    (hJ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k J)
    (hS : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k S)
    (hη : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k η) :
    MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) ξ :=
  (h.isWeakCRSolution_crReflection hR hΩ hΛ
    ((memLpLoc_crReflectionCoeff_iff hΩ).1 hc.memLpLoc_coeff)
    ((memLpLoc_crReflectionDeriv_iff hΩ).1 hc.memLpLoc_deriv)
    ((memLpLoc_crReflectionZeroth_iff hΩ).1 hc.memLpLoc_zeroth)
    hpq.le).memWkpLoc_succ_of_crReflection hΩ hc hp hJ2 hpq hqp hJ hS hη

/-- **`W^{k+1,q}` regularity up to the real axis for Sobolev coefficients** (McDuff–Salamon,
Proposition B.4.9, with a totally real boundary condition). Let `Ω` be invariant under conjugation
and `R` an isometric involution of the finite-dimensional space `V` whose fixed vectors lie in
`Λ`, and `p > 2`. Let `J` be continuous on `Ω ∩ {0 ≤ t}`, with `J² = -1` almost everywhere there,
with weak derivative `DJ` on the open upper part, locally `Lᵖ` up to the axis, and anticommuting
with `R` on `Ω ∩ ℝ`. Let `ξ ∈ L^q_loc` be a weak solution up to the real axis of
`∂_s ξ + J ∂_t ξ + S ξ = η` with boundary subspace `Λ`, for `1/p + 1/q < 1` and `q ≤ p`. If
`J, S ∈ W^{k,p}_loc` and `η ∈ W^{k,q}_loc` up to the axis, then
`ξ ∈ W^{k+1,q}_loc(Ω ∩ {0 ≤ t})`. -/
theorem IsWeakCRSolutionHalf.memWkpLoc_succ_of_hasWeakFDerivOn [FiniteDimensional ℝ V]
    {p q : ℝ≥0} {k : ℕ} {Λ : Submodule ℝ V} {R : V ≃ₗᵢ[ℝ] V}
    (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) (hR : Function.Involutive R)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΛ : ∀ v, R v = v → v ∈ Λ)
    (hJW : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) J DJ)
    (hJc : ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hJR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v))
    (hDJ : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DJ)
    (hp : 2 < p) (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1) (hqp : q ≤ p)
    (hJ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k J)
    (hS : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k S)
    (hη : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k η) :
    MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) ξ :=
  h.memWkpLoc_succ hR hΩ hΛ
    (isSobolevCRCoefficients_crReflection hΩ (by exact_mod_cast one_le_two.trans hp.le) hJW hJc
      hJR hDJ hS.memLpLoc) hp hJ2 hpq hqp hJ hS hη

end TauCeti
