/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak.Bootstrap
public import TauCeti.Analysis.Sobolev.Cylinder.WeakDeriv
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving

/-!
# Regularity of `W^{1,p}` solutions of Cauchy–Riemann equations on the cylinder

Let `V` be a finite-dimensional real normed space, `2 < p < ∞`, and let `ℓ ≥ 1`. Consider a
quasilinear first-order equation on the cylinder `ℝ × S¹`,

`∂s u + A(z, u) ∂t u + G(z, u) = 0`,

with coefficients `A : ℝ × ℝ → V → End V` and `G : ℝ × ℝ → V → V` of class `C^ℓ` jointly in
`(z, x)`, of period one in `t`, and with `A(z, u z)² = -1`, such as the Floer equation
`∂s u + J(u) (∂t u - X_H(u)) = 0`, where `A = J` and `G = -J X_H`. Its solutions near a `C^ℓ`
reference map `w` of the cylinder are sought in the form `u = w + ξ` with an increment
`x = (ξ, ξ_s, ξ_t)` in the Sobolev space `W^{1,p}(ℝ × S¹, V)` (`TauCeti.CylinderSobolev.W1p`), whose
value `ξ` is continuous by the Sobolev embedding (`TauCeti.CylinderSobolev.continuousValue`). Such a
`u` is a solution when

`∂s w + ξ_s + A(z, u) (∂t w + ξ_t) + G(z, u) = 0`

almost everywhere on the strip `ℝ × [0, 1]`. This file shows that every such solution is of class
`C^ℓ` on the plane (`TauCeti.CylinderSobolev.contDiff_add_continuousValue_of_ae_eq_zero`), and
smooth when the data are.

The jet components `ξ_s` and `ξ_t` are the weak partial derivatives of `ξ` on the plane
(`TauCeti.CylinderSobolev.exists_hasWeakFDerivOn_continuousValue`), and all terms of the equation
have period one in `t`, so it holds almost everywhere on the plane
(`TauCeti.CylinderSobolev.ae_of_ae_stripMeasure_of_periodic`). Read in the complex coordinate
`z = s + i t`, `u` is then a continuous weak solution of `∂s u + J(z, u) ∂t u = η(z, u)` with
`J = A` and `η = -G`, with weak derivative locally in `Lᵖ`, in the sense of
`TauCeti.IsWeakCauchyRiemannOn`; interior elliptic bootstrapping
(`TauCeti.contDiffOn_of_isWeakCauchyRiemannOn`) gives its regularity.

In the Floer theory of the cylinder, the nonlinear Floer section is formed on `W^{1,p}` increments
of a reference map, and its zeros near a solution are the solutions of this form. This is the
regularity half of the statement that they are smooth Floer cylinders, the input of the
transversality and gluing arguments which take place in `W^{1,p}`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B.4
  (elliptic bootstrapping) and Section 3.1, on the regularity of `W^{1,p}` solutions of the
  nonlinear Cauchy–Riemann equation for `p > 2`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.CylinderSobolev

open StripSobolev (jet jet_apply stripMeasure)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **`W^{1,p}` solutions of Cauchy–Riemann equations on the cylinder are regular.** Let
`2 < p < ∞` and `1 ≤ ℓ ≤ ∞`, let `w` be a `C^ℓ` map of period one in `t`, and let `A` and `G` be
of class `C^ℓ` jointly in `(z, x)`, of period one in `t`. If `x = (ξ, ξ_s, ξ_t) ∈ W^{1,p}` and
`u = w + ξ`, with `ξ` its continuous representative, satisfies `A(z, u z)² = -1` and the equation
`∂s w + ξ_s + A(z, u) (∂t w + ξ_t) + G(z, u) = 0` almost everywhere on the strip, then `u` is of
class `C^ℓ` on the plane. -/
theorem contDiff_add_continuousValue_of_ae_eq_zero (hp : 2 < p) (hpt : p ≠ ∞) {ℓ : ℕ∞}
    (hℓ : 1 ≤ ℓ) {w : ℝ × ℝ → V} (hw : ContDiff ℝ ℓ w) (hwper : ∀ s t, w (s, t + 1) = w (s, t))
    {A : ℝ × ℝ → V → V →L[ℝ] V} {G : ℝ × ℝ → V → V}
    (hA : ContDiff ℝ ℓ fun y : (ℝ × ℝ) × V ↦ A y.1 y.2)
    (hG : ContDiff ℝ ℓ fun y : (ℝ × ℝ) × V ↦ G y.1 y.2)
    (hAper : ∀ s t, A (s, t + 1) = A (s, t)) (hGper : ∀ s t, G (s, t + 1) = G (s, t))
    (x : W1p V p)
    (hA2 : ∀ᵐ z ∂stripMeasure,
      A z (w z + continuousValue p x z) * A z (w z + continuousValue p x z) = -1)
    (h : ∀ᵐ z ∂stripMeasure,
      fderiv ℝ w z (1, 0) + ((x : Lp (V × V × V) p stripMeasure) z).2.1 +
        A z (w z + continuousValue p x z)
          (fderiv ℝ w z (0, 1) + ((x : Lp (V × V × V) p stripMeasure) z).2.2) +
        G z (w z + continuousValue p x z) = 0) :
    ContDiff ℝ ℓ fun z ↦ w z + continuousValue p x z := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  obtain ⟨D, hD, hDloc, hDper, hDx⟩ := exists_hasWeakFDerivOn_continuousValue hp hpt x
  set u : ℝ × ℝ → V := fun z ↦ w z + continuousValue p x z
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast hℓ)
  have huc : Continuous u := hw1.continuous.add (continuousValue p x).continuous
  have huper (s t : ℝ) : u (s, t + 1) = u (s, t) := by
    simp [u, hwper, continuousValue_add_one hp hpt]
  -- The weak derivative of `u` on the plane is `Dw + D`, locally in `Lᵖ`.
  set Du : ℝ × ℝ → ℝ × ℝ →L[ℝ] V := fun z ↦ fderiv ℝ w z + D z
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hDu : HasWeakFDerivOn volume ⊤ u Du :=
    (hw1.contDiffOn.hasWeakFDerivOn_fderiv (Ω := ⊤)).add hD
  have hDuloc : MemLpLoc p univ Du := (hw1.continuous_fderiv one_ne_zero).memLpLoc.add hDloc
  -- All terms of the equation have period one in `t`, so it holds on the whole plane.
  have hae : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      Du z (1, 0) + A z (u z) (Du z (0, 1)) = -G z (u z) := by
    refine ae_of_ae_stripMeasure_of_periodic (fun s t ↦ ?_) ?_
    · have hj := jet_add_one_of_periodic hwper s t
      simp only [jet_apply, Prod.mk.injEq] at hj
      simp only [Du, add_apply, hj.2.1, hj.2.2, hDper, huper, hAper, hGper]
    · filter_upwards [h, hDx] with z hz hDz
      rw [eq_neg_iff_add_eq_zero, ← hz]
      simp [Du, hDz.1, hDz.2, u, add_assoc]
  have hA2' : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), A z (u z) * A z (u z) = -1 :=
    ae_of_ae_stripMeasure_of_periodic (fun s t ↦ by simp only [huper, hAper]) hA2
  -- In the complex coordinate, `u` is a weak solution of `∂s u + A(z, u) ∂t u = -G(z, u)`.
  set e : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM
  have hpres := (Complex.coe_measurableEquivRealProd_eq_equivRealProdCLM ▸
    Complex.volume_preserving_equiv_real_prod).quasiMeasurePreserving
  have hweak : IsWeakCauchyRiemannOn p ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) (fun z ↦ A (e z))
      (fun z v ↦ -G (e z) v) (u ∘ e) := by
    refine isWeakCauchyRiemannOn_iff_of_isOpen.2 ⟨(huc.comp e.continuous).continuousOn,
      (huc.comp e.continuous).memLpLoc, fun z ↦ (Du (e z)).comp (e : ℂ →L[ℝ] ℝ × ℝ),
      hDu.comp_continuousLinearEquiv_of_isAddHaarMeasure e (mapsTo_univ _ _), ?_, ?_⟩
    · have hloc := ((e.memLpLoc_comp_right_iff volume volume).2 hDuloc).clm_comp
        ((ContinuousLinearMap.compL ℝ ℂ (ℝ × ℝ) V).flip (e : ℂ →L[ℝ] ℝ × ℝ))
      simpa using hloc
    · simpa [e] using hpres.ae hae
  have hreg := contDiffOn_of_isWeakCauchyRiemannOn hp (W := univ) isOpen_univ
    (hA.comp ((e.contDiff.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
    (hG.comp ((e.contDiff.comp contDiff_fst).prodMk contDiff_snd)).neg.contDiffOn
    (fun _ _ ↦ mem_univ _) (by simpa [e] using hpres.ae hA2') hweak
  have h' := (contDiffOn_univ.1 (by simpa using hreg)).comp e.symm.contDiff
  simpa [Function.comp_def] using h'

end TauCeti.CylinderSobolev
