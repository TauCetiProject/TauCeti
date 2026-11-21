/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pregluing
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Basic
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart

/-!
# Pre-gluing two Floer pairs of pants broken at an orbit

Composing two pair-of-pants products counts the configurations at the ends of the one-dimensional
moduli spaces of Floer solutions on the plumbed four-punctured sphere: a pair of pants `u'` on
`S' = ℂ ∖ {0, 1}` whose output converges to an orbit `x`, and a pair of pants `u` on `S` whose
input `q ∈ {0, 1}` converges to the same orbit. Both maps are read in the real coordinates
`ℝ × ℝ ≃ ℂ`. Gluing them begins with an approximate solution on the plumbed four-punctured sphere
`ℂ ∖ {0, 1, ψ(1)}` of neck length `L = 2R`, where `ψ = q.plumbingMap L` is the plumbing map
(`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap`), which is the translation `z ↦ z + L` in
end coordinates.

The output end of `u'`, read in the end chart `φ_∞` of `S'`, is the map `v = u' ∘ φ_∞`, defined on
the whole plane. Its loops converge to `x` as `s → -∞`, and for large negative `s` it solves the
Floer equation of the cylindrical datum `H_∞(t) dt`. The *pre-glued composition*
`TauCeti.Floer.preglueComposition q x u u' R` is the pre-glued pair of pants
`TauCeti.Floer.preglueEnd q x u v R` of `u` and this cylinder at the end `q`.

* **On the receiving pair of pants it is `u`.** Where the longitudinal coordinate of the end `q`
  is at most `R - 1` it is `u` (`TauCeti.Floer.preglueComposition_of_le`), and near such points
  other than the center of the end it agrees with `u`
  (`TauCeti.Floer.preglueComposition_eventuallyEq_of_lt`).
* **On the inserted pair of pants it is `u'`.** At the image `ψ(w)` of a point `w ≠ 0` whose
  longitudinal coordinate on the end at `∞` is at least `1 - R` it is `u'(w)`
  (`TauCeti.Floer.preglueComposition_realChart_plumbingMap`), because the end chart of `q` at
  `z + L` is the image under `ψ` of the end chart of `∞` at `z`
  (`TauCeti.Floer.endChart_add_eq_realChart_plumbingMap`). So the pre-glued composition is a map on
  the plumbed four-punctured sphere which pulls back to `u'` along the plumbing map
  (`TauCeti.Floer.preglueComposition_comp_realChart_plumbingMap_eventuallyEq`), and is `u' ∘ ψ⁻¹`
  near the image of the inserted part
  (`TauCeti.Floer.preglueComposition_eventuallyEq_comp_realChart`).
* **It is smooth.** For `R ≥ 1` and `Cⁿ` maps `u`, `u'` on the pair of pants it is `Cⁿ` on the
  plumbed four-punctured sphere (`TauCeti.Floer.contDiffOn_preglueComposition`).
* **Off the neck it solves the plumbed Floer equation.** The plumbed perturbation
  `TauCeti.Floer.plumbedPerturbation Ha Hb q (2R)` is the perturbation of `S` on the receiving part
  of the four-punctured sphere and the pushforward of the perturbation of `S'` on the inserted
  part. So if `u` solves the Floer equation of `S` and `u'` that of `S'`, the pre-glued composition
  solves the plumbed Floer equation, for the same almost complex structure, on the receiving part
  `s_q < R - 1`
  (`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_preglueComposition_of_lt`) and on the
  image of the inserted part `s_∞ > 1 - R`
  (`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_preglueComposition_realChart`).
* **On the neck the cylindrical error is exponentially small.** In the end chart of `q` the neck
  is a long cylinder. Fix cylindrical neck data: a Hamiltonian `H` and a `t`-dependent almost
  complex structure `J`. If `u ∘ φ_q` and `v` converge to `x` in `C¹` at an exponential rate `κ`
  and solve the cylindrical Floer equation of `(H, J)` beyond the heights `T` and `T'`
  respectively, the cylindrical Floer operator of `(H, J)` applied to the pre-glued composition,
  read in the end chart, is at most `C' e^{-κ R}` on the whole neck `T < s < 2R + T'`, whose
  length grows with `R`
  (`TauCeti.SymplecticForm.exists_eventually_norm_floerOperator_preglueComposition_comp_le`).
* **On the neck the plumbed Floer operator is the cylindrical one.** At every point `(s, t)` of the
  neck `2 ≤ s ≤ L - 2` of the end `q`, the pullback of the plumbed perturbation
  `TauCeti.Floer.plumbedPerturbation` of neck length `L` along the positive end chart has no `ds`
  component and `dt` component `H_q(t)`, the common Hamiltonian of the two glued ends
  (`TauCeti.Floer.perturbationPullback_positiveEndChart_plumbedPerturbation_stdComplexLineReal`,
  `TauCeti.Floer.perturbationPullback_positiveEndChart_plumbedPerturbation_stdComplexLineImag`).
  So the plumbed Floer operator read in the end chart is there the cylindrical one
  (`TauCeti.SymplecticForm.`
  `floerOperator_perturbationPullback_positiveEndChart_plumbedPerturbation`),
  and the neck estimate bounds the plumbed pre-gluing error by `C' e^{-κ R}`
  (`TauCeti.SymplecticForm.`
  `exists_eventually_norm_floerOperator_plumbedPerturbation_preglueComposition_comp_le`). This
  error vanishes on the neck outside the band `R - 1 ≤ s ≤ R + 1` where the pre-glued map
  interpolates through `x`
  (`TauCeti.SymplecticForm.floerOperator_plumbedPerturbation_preglueComposition_comp_eq_zero`), so
  for every `p > 0` the integral of its `p`-th power over the neck, in the cylindrical coordinates
  in which the gluing estimates are made, is at most `2 (C' e^{-κ R})^p`
  (`TauCeti.SymplecticForm.`
  `exists_eventually_setLIntegral_floerOperator_plumbedPerturbation_preglueComposition_comp_le`).

These are the properties of the approximate solution consumed by the gluing theorem for the two
broken products at the ends of the associativity family. The Sobolev setting, the right inverse
of the linearized operator and the Newton iteration that corrects the pre-glued composition to a
solution are not treated here.

## Main definitions

* `TauCeti.Floer.preglueComposition q x u u' R`: the pre-glued composition of the pair of pants
  `u'` into the input `q` of the pair of pants `u`, through the orbit `x`, with gluing parameter
  `R` and neck length `2R`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the gluing of pairs of pants along a common orbit.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Chapter 10,
  on the pre-gluing construction and its error estimate.
-/

public section

open Filter Set Topology Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart realChart_apply)

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Floer

/-- **The plumbing law in the end charts.** The end chart of `q` at `y + (L, 0)` is the image under
the plumbing map of neck length `L` of the end chart of `∞` at `y`. -/
theorem endChart_add_eq_realChart_plumbingMap (q : Puncture) (L : ℝ) (y : ℝ × ℝ) :
    endChart q (y + (L, 0)) = realChart (q.plumbingMap L) (endChart inf y) := by
  have h : Complex.equivRealProdCLM.symm (y + (L, 0)) = Complex.equivRealProdCLM.symm y + L := by
    rw [map_add, Complex.equivRealProdCLM_symm_apply (L, 0)]
    simp
  rw [endChart_apply, endChart_apply, realChart_apply, ContinuousLinearEquiv.symm_apply_apply, h,
    cylindricalEndLift_add_ofReal]

variable {q : Puncture} {x : ℝ → V} {u u' : ℝ × ℝ → V} {R : ℝ} {z w : ℝ × ℝ}

/-- **The pre-glued composition of two pairs of pants.** The pre-glued pair of pants of `u` and of
the output end `u' ∘ φ_∞` of the pair of pants `u'` at the input `q` of `u`, through the loop `x`,
with gluing parameter `R`. It is `u` on the receiving part of the plumbed four-punctured sphere of
neck length `2R` (`TauCeti.Floer.preglueComposition_of_le`) and `u' ∘ ψ⁻¹` on the inserted part
(`TauCeti.Floer.preglueComposition_realChart_plumbingMap`), and interpolates through `x` on the
neck. -/
noncomputable def preglueComposition (q : Puncture) (x : ℝ → V) (u u' : ℝ × ℝ → V) (R : ℝ) :
    ℝ × ℝ → V :=
  preglueEnd q x u (u' ∘ endChart inf) R

theorem preglueComposition_def (q : Puncture) (x : ℝ → V) (u u' : ℝ × ℝ → V) (R : ℝ) :
    preglueComposition q x u u' R = preglueEnd q x u (u' ∘ endChart inf) R :=
  (rfl)

/-- **On the receiving pair of pants the pre-glued composition is `u`.** At a point whose signed
longitudinal coordinate on the end `q` is at most `R - 1`, the pre-glued composition is `u`. -/
theorem preglueComposition_of_le
    (h : q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ R - 1) :
    preglueComposition q x u u' R z = u z :=
  preglueEnd_of_le h

/-- Near a point other than the center of the end `q` whose signed longitudinal coordinate on `q`
is less than `R - 1`, the pre-glued composition agrees with `u`. -/
theorem preglueComposition_eventuallyEq_of_lt
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (h : q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < R - 1) :
    preglueComposition q x u u' R =ᶠ[𝓝 z] u :=
  preglueEnd_eventuallyEq_of_lt hz h

/-- **On the inserted pair of pants the pre-glued composition is `u'`.** For an input `q` and
`R ≥ 0`, at the image under the plumbing map of neck length `2R` of a point `w ≠ 0` whose
longitudinal coordinate on the end at `∞` is at least `1 - R`, the pre-glued composition is
`u'(w)`. -/
theorem preglueComposition_realChart_plumbingMap (hq : q ≠ inf) (hR : 0 ≤ R)
    (hw : Complex.equivRealProdCLM.symm w ≠ 0)
    (h : 1 - R ≤ (inf.endCoord (Complex.equivRealProdCLM.symm w)).re) :
    preglueComposition q x u u' R (realChart (q.plumbingMap (2 * R)) w) = u' w := by
  set ζ := inf.endCoord (Complex.equivRealProdCLM.symm w)
  have hζ : q.endCoord (Complex.equivRealProdCLM.symm (realChart (q.plumbingMap (2 * R)) w)) =
      ζ + ((2 * R : ℝ) : ℂ) := by
    rw [Complex.equivRealProdCLM_symm_realChart, endCoord_plumbingMap q _ hw]
  -- The point lies beyond the neck of the end `q`, where the pre-glued map is the translate of
  -- the cylinder `u' ∘ φ_∞`, evaluated at the end coordinate `ζ` of `w` at `∞`.
  have hpt : ((ζ + ((2 * R : ℝ) : ℂ)).re - 2 * R, (ζ + ((2 * R : ℝ) : ℂ)).im) =
      Complex.equivRealProdCLM ζ := by
    ext <;> simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
      Complex.equivRealProdCLM_apply] <;> ring
  rw [preglueComposition_def, preglueEnd_of_add_one_le hR (by
      rw [hζ, endSign_eq_one hq, one_mul, Complex.add_re, Complex.ofReal_re]; linarith),
    hζ, endSign_eq_one hq, one_mul, one_mul, hpt, comp_apply,
    endChart_equivRealProdCLM_endCoord (by simpa using hw)]

/-- **The pre-glued composition pulls back to `u'` along the plumbing map.** For an input `q` and
`R ≥ 0`, near a point `w ≠ 0` whose longitudinal coordinate on the end at `∞` is greater than
`1 - R`, the pre-glued composition composed with the plumbing map of neck length `2R` is `u'`. -/
theorem preglueComposition_comp_realChart_plumbingMap_eventuallyEq (hq : q ≠ inf) (hR : 0 ≤ R)
    (hw : Complex.equivRealProdCLM.symm w ≠ 0)
    (h : 1 - R < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re) :
    preglueComposition q x u u' R ∘ realChart (q.plumbingMap (2 * R)) =ᶠ[𝓝 w] u' := by
  have hc : ContinuousAt (fun w : ℝ × ℝ ↦ (inf.endCoord (Complex.equivRealProdCLM.symm w)).re) w :=
    (inf.contDiffAt_re_endCoord (by simpa using hw) (n := 0)).continuousAt.comp
      Complex.equivRealProdCLM.symm.continuous.continuousAt
  filter_upwards [continuousAt_const.eventually_lt hc h,
    (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).mem_nhds hw]
    with w' h₁ h₂
  exact preglueComposition_realChart_plumbingMap hq hR h₂ h₁.le

/-- **The pre-glued composition is `u'` composed with the inverse plumbing map.** For an input `q`
and `R ≥ 0`, near the image under the plumbing map `ψ` of neck length `2R` of a point `w ≠ 0` whose
longitudinal coordinate on the end at `∞` is greater than `1 - R`, the pre-glued composition is
`u' ∘ ψ⁻¹`, with `ψ⁻¹(ζ) = (ζ - c_q) / ψ'`, in real coordinates. -/
theorem preglueComposition_eventuallyEq_comp_realChart (hq : q ≠ inf) (hR : 0 ≤ R)
    (hw : Complex.equivRealProdCLM.symm w ≠ 0)
    (h : 1 - R < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re) :
    preglueComposition q x u u' R =ᶠ[𝓝 (realChart (q.plumbingMap (2 * R)) w)]
      u' ∘ realChart fun ζ ↦ (ζ - q.endCenter) / q.plumbingFactor (2 * R) := by
  have hgc : Continuous (realChart fun ζ ↦ (ζ - q.endCenter) / q.plumbingFactor (2 * R)) :=
    (TauCeti.Complex.contDiff_realChart (n := 0) (by fun_prop)).continuous
  have h' := preglueComposition_comp_realChart_plumbingMap_eventuallyEq (x := x) (u := u)
    (u' := u') hq hR hw h
  rw [← leftInverse_realChart_plumbingMap q (2 * R) w] at h'
  filter_upwards [hgc.continuousAt.eventually h'] with z hz
  rwa [comp_apply, rightInverse_realChart_plumbingMap] at hz

/-- **The pre-glued composition in the end chart.** If the loop `x` has period one and `R ≥ 1`, the
pre-glued composition read in the positive end chart of `q` is the pre-glued map of `u ∘ φ'_q` and
of the output end `u' ∘ φ_∞`, translated by `R`. -/
theorem preglueComposition_comp_positiveEndChart (hx : Periodic x 1) (hR : 1 ≤ R) :
    preglueComposition q x u u' R ∘ positiveEndChart q =
      fun y ↦ preglue x (u ∘ positiveEndChart q) (u' ∘ endChart inf) R (y - (R, 0)) :=
  preglueEnd_comp_positiveEndChart hx (periodic_comp_endChart inf u') hR

/-- **The pre-glued composition is smooth.** For an input `q`, if `u` and `u'` are `Cⁿ` on the pair
of pants, the loop `x` is `Cⁿ` and of period one, and `R ≥ 1`, then the pre-glued composition is
`Cⁿ` on the plumbed four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}` of neck length `2R`. -/
theorem contDiffOn_preglueComposition {n : ℕ∞} (hq : q ≠ inf) (hx : ContDiff ℝ n x)
    (hxper : Periodic x 1) (hu : ContDiffOn ℝ n u thricePuncturedSphereReal)
    (hu' : ContDiffOn ℝ n u' thricePuncturedSphereReal) (hR : 1 ≤ R) :
    ContDiffOn ℝ n (preglueComposition q x u u' R)
      {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (2 * R) 1} := by
  intro z hz
  set y : ℝ × ℝ := (q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re,
    q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).im)
  have hy : positiveEndChart q y = z := positiveEndChart_endSign_mul_endCoord (ne_endCenter hz.1 q)
  -- The point of `S'` read off at `y - (2R, 0)` by the cylinder `u' ∘ φ_∞` is `ψ⁻¹(z)`, which is
  -- neither `0` nor `1` because `z` is neither the center `ψ(0)` of the end nor `ψ(1)`.
  have hψ : realChart (q.plumbingMap (2 * R)) (endChart inf (y - (2 * R, 0))) = z := by
    rw [← endChart_add_eq_realChart_plumbingMap, sub_add_cancel, ← hy, positiveEndChart_apply,
      endSign_eq_one hq, one_smul]
  have hmem : endChart inf (y - (2 * R, 0)) ∈ thricePuncturedSphereReal := by
    have hz' := hz
    rw [← hψ] at hz'
    simp only [mem_ofPred_eq, Complex.equivRealProdCLM_symm_realChart] at hz'
    rw [mem_thricePuncturedSphereReal_iff]
    refine ⟨fun h ↦ ne_endCenter hz'.1 q ?_, fun h ↦ hz'.2 ?_⟩
    · rw [h, plumbingMap_zero]
    · rw [h]
  have hv : ContDiffAt ℝ n (u' ∘ endChart inf) (y - (2 * R, 0)) :=
    (hu'.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hmem)).comp _
      (contDiff_endChart inf n).contDiffAt
  rw [← hy] at hz ⊢
  exact (contDiffAt_preglueEnd_positiveEndChart hx hxper
    (periodic_comp_endChart inf u') hR
    (hu.contDiffAt (isOpen_thricePuncturedSphereReal.mem_nhds hz.1)) hv).contDiffWithinAt

section Neck

variable {X : Type*} {Ha Hb : Puncture → ℝ → X → ℝ} {L : ℝ} {ζ : ℝ × ℝ}

/-- At a point `(s, t)` of the neck `2 ≤ s ≤ L - 2` of the end `q`, read in the positive end
chart, the plumbed perturbation of neck length `L` takes the same values as the perturbation of
the receiving pair of pants, so their pullbacks along the end chart agree there. -/
private theorem perturbationPullback_positiveEndChart_plumbedPerturbation_eq (hq : q ≠ inf)
    (hab : Hb q = Ha inf) (h : ζ.1 ≤ L - 2) (v : ℝ × ℝ) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        v ζ =
      perturbationPullback (endChart q)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        v ζ := by
  have hφ : positiveEndChart q = endChart q := by
    funext y
    rw [positiveEndChart_apply, endSign_eq_one hq, one_smul]
  funext y
  rw [hφ, perturbationPullback_apply, perturbationPullback_apply,
    plumbedPerturbation_of_re_endCoord_le hq hab (by rwa [re_endCoord_endChart])]

/-- **The plumbed perturbation has no `ds` component on the neck.** At a point `(s, t)` of the
neck `2 ≤ s ≤ L - 2` of the end `q`, the `ds` component of the pullback of the plumbed
perturbation of neck length `L` along the positive end chart vanishes. -/
theorem perturbationPullback_positiveEndChart_plumbedPerturbation_stdComplexLineReal
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (h₁ : 2 ≤ ζ.1) (h₂ : ζ.1 ≤ L - 2) (y : X) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineReal ζ y = 0 := by
  rw [perturbationPullback_positiveEndChart_plumbedPerturbation_eq hq hab h₂]
  exact perturbationPullback_endChart_stdComplexLineReal_of_le (T₀ := 2) (H := Hb)
    (fun w x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x)
    (by rwa [endSign_eq_one hq, one_mul]) y

/-- **The plumbed perturbation is `H_q(t) dt` on the neck.** At a point `(s, t)` of the neck
`2 ≤ s ≤ L - 2` of the end `q`, the `dt` component of the pullback of the plumbed perturbation of
neck length `L` along the positive end chart is the Hamiltonian `H_q(t)` of the end `q` of the
receiving pair of pants, which is also the Hamiltonian of the output end of the inserted one. -/
theorem perturbationPullback_positiveEndChart_plumbedPerturbation_stdComplexLineImag
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (hHb : Periodic (Hb q) 1) (h₁ : 2 ≤ ζ.1)
    (h₂ : ζ.1 ≤ L - 2) (y : X) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineImag ζ y = Hb q ζ.2 y := by
  rw [perturbationPullback_positiveEndChart_plumbedPerturbation_eq hq hab h₂]
  exact perturbationPullback_endChart_stdComplexLineImag_of_le (T₀ := 2) (H := Hb)
    (fun w x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hHb
    (by rwa [endSign_eq_one hq, one_mul]) y

end Neck

end Floer

namespace SymplecticForm

open Floer

variable [FiniteDimensional ℝ V] {Ha Hb : Puncture → ℝ → V → ℝ} {q : Puncture} {x : ℝ → V}
  {u u' : ℝ × ℝ → V} {R : ℝ} {z w : ℝ × ℝ}

/-- **On the receiving part the pre-glued composition solves the plumbed Floer equation.** Let `u`
solve the Floer equation `(du - X_K)^{0,1} = 0` of the perturbation `K_b` of the receiving pair of
pants at a point `z` other than the center of the end `q`, whose longitudinal coordinate on `q` is
less than `R - 1`. If `R ≥ 1` and the Hamiltonians match on the neck, the pre-glued composition
solves there the Floer equation of the plumbed perturbation of neck length `2R`, for the same
almost complex structure. -/
theorem isComplexLinearMap_perturbedFDeriv_preglueComposition_of_lt (ω : SymplecticForm V)
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (hR : 1 ≤ R)
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (h : (q.endCoord (Complex.equivRealProdCLM.symm z)).re < R - 1)
    {J : AlmostComplexStructure V}
    (hu : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x
        Complex.I)
      (preglueComposition q x u u' R) z : ℝ × ℝ →ₗ[ℝ] V) := by
  have hK (v : ℂ) (y : V) : plumbedPerturbation Ha Hb q (2 * R)
      (Complex.equivRealProdCLM.symm z) y v =
        pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) y v := by
    rw [plumbedPerturbation_of_re_endCoord_le hq hab (by linarith) y]
  rwa [ω.perturbedFDeriv_congr_of_eventuallyEq _ _ (preglueComposition_eventuallyEq_of_lt hz
      (by rwa [endSign_eq_one hq, one_mul])),
    ω.perturbedFDeriv_congr
      (Ks' := fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
      (Kt' := fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
      _ (funext (hK 1)) (funext (hK Complex.I))]

/-- **On the inserted part the pre-glued composition solves the plumbed Floer equation.** Let `u'`
be differentiable at a point `w` of the inserted pair of pants whose longitudinal coordinate on
the end at `∞` is greater than `1 - R`, and solve there the Floer equation `(du' - X_K)^{0,1} = 0`
of its perturbation `K_a`, built from period-one `C¹` Hamiltonians. If `R > 1` and the Hamiltonians
match on the neck, the pre-glued composition solves the Floer equation of the plumbed
perturbation of neck length `2R` at the image of `w` under the plumbing map, for the same almost
complex structure: there it is `u'` composed with the inverse of the holomorphic plumbing map,
along which the plumbed perturbation is the pushforward of `K_a`. -/
theorem isComplexLinearMap_perturbedFDeriv_preglueComposition_realChart (ω : SymplecticForm V)
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hR : 1 < R) (hw : w ∈ thricePuncturedSphereReal)
    (h : 1 - R < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re)
    (hu' : DifferentiableAt ℝ u' w) {J : AlmostComplexStructure V}
    (hu'F : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
      u' w : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x
        Complex.I)
      (preglueComposition q x u u' R) (realChart (q.plumbingMap (2 * R)) w) :
        ℝ × ℝ →ₗ[ℝ] V) := by
  set L := 2 * R
  set b := q.plumbingFactor L
  set z := realChart (q.plumbingMap L) w
  -- Near `z` the pre-glued composition is `u' ∘ g`, for the inverse `g` of the plumbing map.
  set f : ℂ → ℂ := fun ζ ↦ (ζ - q.endCenter) / b
  set g := realChart f
  have hEq : preglueComposition q x u u' R =ᶠ[𝓝 z] u' ∘ g :=
    preglueComposition_eventuallyEq_comp_realChart hq (by linarith) hw.1 h
  have hf (ζ : ℂ) : HasDerivAt f b⁻¹ ζ := by
    simpa [f, div_eq_mul_inv] using ((hasDerivAt_id ζ).sub_const q.endCenter).mul_const b⁻¹
  have hgz : g z = w := leftInverse_realChart_plumbingMap q L w
  -- Along `g` the inserted perturbation pulls back to the plumbed perturbation, since `z` lies
  -- beyond the height `2` on the end `q`.
  have hre : 2 < (q.endCoord (Complex.equivRealProdCLM.symm z)).re := by
    rw [Complex.equivRealProdCLM_symm_realChart, re_endCoord_plumbingMap q L hw.1]
    linarith
  have hK (v : ℝ × ℝ) (y : V) :
      plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) y
        (Complex.equivRealProdCLM.symm v) = perturbationPullback g
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        v z y := by
    rw [perturbationPullback_realChart _ (hf _), plumbedPerturbation_eq_comp hq hab hre,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply']
  have hKt (ζ : ℂ) : DifferentiableAt ℝ (fun y ↦ pairOfPantsPerturbation Ha
      (Complex.equivRealProdCLM.symm (g z)) y ζ) (u' (g z)) := by
    rw [hgz]
    exact differentiableAt_pairOfPantsPerturbation_target hHa hHas hw _ ζ
  have hpull := ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
    (TauCeti.Complex.hasFDerivAt_realChart (hf _)).differentiableAt (hgz ▸ hu') (hKt 1)
    (hKt Complex.I) (isComplexLinearMap_fderiv_realChart (hf _)) (hgz ▸ hu'F)
  rwa [ω.perturbedFDeriv_congr_of_eventuallyEq _ _ hEq,
    ω.perturbedFDeriv_congr
      (Ks' := perturbationPullback g
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineReal)
      (Kt' := perturbationPullback g
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineImag) _
      (funext fun y ↦ by rw [← hK, equivRealProdCLM_symm_stdComplexLineReal])
      (funext fun y ↦ by rw [← hK, equivRealProdCLM_symm_stdComplexLineImag])]

/-- **The pre-gluing error on the neck is exponentially small.** Let `H` be a `C²` Hamiltonian and
`J_t(y)` a continuous family of endomorphisms, the cylindrical data of the neck, and let `x` be an
orbit of `X_{H_t}` of period one. Suppose that `u ∘ φ'_q` converges to `x` in `C¹` at the
exponential rate `κ > 0` as `s → ∞` and solves the Floer equation of the datum `H_t dt` beyond the
height `T`, and that the output end `u' ∘ φ_∞` of the inserted pair of pants converges to `x` in
`C¹` at the rate `κ` as `s → -∞` and solves the Floer equation below the height `T'`. Then for
every large gluing parameter `R`, the Floer operator of the pre-glued composition, read in the
positive end chart of `q`, is at most `C' e^{-κ R}` on the whole neck `(T, 2R + T') × [0, 1]`. -/
theorem exists_eventually_norm_floerOperator_preglueComposition_comp_le (ω : SymplecticForm V)
    (q : Puncture) {J : ℝ → V → V →L[ℝ] V} {H : ℝ → V → ℝ} {C κ T T' : ℝ}
    (hH : ContDiff ℝ 2 (uncurry H)) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxper : Periodic x 1)
    (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (u ∘ positiveEndChart q) (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u (positiveEndChart q (s, t)) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ positiveEndChart q) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (huF : ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ H p.2) (u ∘ positiveEndChart q) z = 0)
    (hu'd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (u' ∘ endChart inf) (s, t))
    (hu' : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u' (endChart inf (s, t)) - x t‖ ≤ C * Real.exp (κ * s))
    (hdu' : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u' ∘ endChart inf) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H t) (x t))‖ ≤
        C * Real.exp (κ * s))
    (hu'F : ∀ z ∈ Iio T' ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ H p.2) (u' ∘ endChart inf) z = 0) :
    ∃ C', ∀ᶠ R in atTop, ∀ z ∈ Ioo T (2 * R + T') ×ˢ Icc (0 : ℝ) 1,
      ‖ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0) (fun p ↦ H p.2)
          (preglueComposition q x u u' R ∘ positiveEndChart q) z‖ ≤
        C' * Real.exp (-(κ * R)) := by
  simpa only [preglueComposition_def] using
    ω.exists_eventually_norm_floerOperator_preglueEnd_comp_le_of_Iio q hH hJ hx hxper hκ hud hu hdu
      huF hu'd hu' hdu' (periodic_comp_endChart inf u') hu'F

/-! ### The plumbed Floer operator on the neck -/

/-- **On the neck the plumbed Floer operator is the cylindrical one.** Read in the positive end
chart of the input `q`, the Floer operator of the plumbed perturbation of neck length `L` is, at
every point `(s, t)` of the neck `2 ≤ s ≤ L - 2`, the Floer operator of the cylindrical datum
`H_q(t) dt`, for any map and any family of endomorphisms. -/
theorem floerOperator_perturbationPullback_positiveEndChart_plumbedPerturbation
    (ω : SymplecticForm V) (hq : q ≠ inf) (hab : Hb q = Ha inf) (hHb : Periodic (Hb q) 1)
    {L : ℝ} (J : ℝ × ℝ → V → V →L[ℝ] V) (f : ℝ × ℝ → V) (h₁ : 2 ≤ z.1) (h₂ : z.1 ≤ L - 2) :
    ω.floerOperator J
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag) f z =
      ω.floerOperator J (fun _ _ ↦ 0) (fun p ↦ Hb q p.2) f z := by
  have hs := funext (perturbationPullback_positiveEndChart_plumbedPerturbation_stdComplexLineReal
    (Ha := Ha) hq hab h₁ h₂)
  have ht := funext (perturbationPullback_positiveEndChart_plumbedPerturbation_stdComplexLineImag
    (Ha := Ha) hq hab hHb h₁ h₂)
  rw [floerOperator_def, floerOperator_def, hs, ht]

/-- **The pre-gluing error of the plumbed Floer operator on the neck is exponentially small.** Let
the input `q` of the receiving pair of pants and the output of the inserted one carry the same
Hamiltonian `H_q`, of class `C²` and period one, and let `J_t(y)` be a continuous family of
endomorphisms, the almost complex structures of the neck in the positive end chart of `q`. Let `x`
be an orbit of `X_{H_q}` of period one. Suppose that `u ∘ φ'_q` converges to `x` in `C¹` at the
exponential rate `κ > 0` as `s → ∞` and solves the Floer equation of `H_q(t) dt` beyond the height
`T ≥ 2`, and that the output end `u' ∘ φ_∞` of the inserted pair of pants converges to `x` in `C¹`
at the rate `κ` as `s → -∞` and solves the Floer equation below the height `T' ≤ -2`. Then for
every large gluing parameter `R`, the Floer operator of the plumbed perturbation of neck length
`2R`, applied to the pre-glued composition and read in the positive end chart of `q`, is at most
`C' e^{-κ R}` on the whole neck `(T, 2R + T') × [0, 1]`. -/
theorem exists_eventually_norm_floerOperator_plumbedPerturbation_preglueComposition_comp_le
    (ω : SymplecticForm V) (hq : q ≠ inf) (hab : Hb q = Ha inf) (hHb : Periodic (Hb q) 1)
    {J : ℝ → V → V →L[ℝ] V} {C κ T T' : ℝ} (hT : 2 ≤ T) (hT' : T' ≤ -2)
    (hH : ContDiff ℝ 2 (uncurry (Hb q))) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (Hb q t) (x t)) t) (hxper : Periodic x 1)
    (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (u ∘ positiveEndChart q) (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u (positiveEndChart q (s, t)) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ positiveEndChart q) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Hb q t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (huF : ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ Hb q p.2) (u ∘ positiveEndChart q) z = 0)
    (hu'd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (u' ∘ endChart inf) (s, t))
    (hu' : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u' (endChart inf (s, t)) - x t‖ ≤ C * Real.exp (κ * s))
    (hdu' : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u' ∘ endChart inf) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Hb q t) (x t))‖ ≤
        C * Real.exp (κ * s))
    (hu'F : ∀ z ∈ Iio T' ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ Hb q p.2) (u' ∘ endChart inf) z = 0) :
    ∃ C', ∀ᶠ R in atTop, ∀ z ∈ Ioo T (2 * R + T') ×ˢ Icc (0 : ℝ) 1,
      ‖ω.floerOperator (fun p ↦ J p.2)
          (perturbationPullback (positiveEndChart q)
            (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x
              Complex.I) stdComplexLineReal)
          (perturbationPullback (positiveEndChart q)
            (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x
              Complex.I) stdComplexLineImag)
          (preglueComposition q x u u' R ∘ positiveEndChart q) z‖ ≤
        C' * Real.exp (-(κ * R)) := by
  obtain ⟨C', hC'⟩ := ω.exists_eventually_norm_floerOperator_preglueComposition_comp_le q hH hJ
    hx hxper hκ hud hu hdu huF hu'd hu' hdu' hu'F
  refine ⟨C', hC'.mono fun R hR z hz ↦ ?_⟩
  rw [ω.floerOperator_perturbationPullback_positiveEndChart_plumbedPerturbation hq hab hHb _ _
    (hT.trans hz.1.1.le) (by linarith [hz.1.2])]
  exact hR z hz

/-- **The plumbed pre-gluing error is supported in the gluing band.** Let the input `q` of the
receiving pair of pants and the output of the inserted one carry the same Hamiltonian `H_q`, of
period one, let `x` be a loop of period one and `R ≥ 1`. Suppose that `u ∘ φ'_q` solves the Floer
equation of `H_q(t) dt` beyond the height `T ≥ 2` and that the output end `u' ∘ φ_∞` of the
inserted pair of pants solves it below the height `T' ≤ -2`. Then on the neck
`(T, 2R + T') × [0, 1]`, read in the positive end chart of `q`, the Floer operator of the plumbed
perturbation of neck length `2R` vanishes on the pre-glued composition outside the band
`R - 1 ≤ s ≤ R + 1` where it interpolates through `x`. -/
theorem floerOperator_plumbedPerturbation_preglueComposition_comp_eq_zero (ω : SymplecticForm V)
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (hHb : Periodic (Hb q) 1) (J : ℝ → V → V →L[ℝ] V)
    {T T' : ℝ} (hT : 2 ≤ T) (hT' : T' ≤ -2) (hxper : Periodic x 1) (hR : 1 ≤ R)
    (huF : ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ Hb q p.2) (u ∘ positiveEndChart q) z = 0)
    (hu'F : ∀ z ∈ Iio T' ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ Hb q p.2) (u' ∘ endChart inf) z = 0)
    (hz : z ∈ Ioo T (2 * R + T') ×ˢ Icc (0 : ℝ) 1) (hzR : 1 < |z.1 - R|) :
    ω.floerOperator (fun p ↦ J p.2)
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x
            Complex.I) stdComplexLineReal)
        (perturbationPullback (positiveEndChart q)
          (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x
            Complex.I) stdComplexLineImag)
        (preglueComposition q x u u' R ∘ positiveEndChart q) z = 0 := by
  obtain ⟨⟨hzT, hzT'⟩, hzt⟩ := hz
  rw [ω.floerOperator_perturbationPullback_positiveEndChart_plumbedPerturbation hq hab hHb _ _
      (hT.trans hzT.le) (by linarith), preglueComposition_comp_positiveEndChart hxper hR,
    floerOperator_comp_sub]
  -- Off the band the pre-glued map is a translate of `u ∘ φ'_q` or of `u' ∘ φ_∞`.
  rcases lt_abs.1 hzR with h | h
  · rw [ω.floerOperator_preglue_of_one_lt J (Hb q) x _ _ R (by simp only [Prod.fst_sub]; linarith)]
    exact hu'F _ ⟨by simp only [Prod.fst_sub, mem_Iio]; linarith, by simpa using hzt⟩
  · rw [ω.floerOperator_preglue_of_lt_neg_one J (Hb q) x _ _ R
      (by simp only [Prod.fst_sub]; linarith), sub_add_cancel]
    exact huF z ⟨hzT, hzt⟩

open MeasureTheory in
/-- **The integrated pre-gluing error of the plumbed Floer operator is exponentially small.**
Under the hypotheses of
`exists_eventually_norm_floerOperator_plumbedPerturbation_preglueComposition_comp_le`, for every
exponent `p > 0` and every large gluing parameter `R`, the integral over the neck
`(T, 2R + T') × [0, 1]`, in the cylindrical coordinates of the positive end chart of `q`, of the
`p`-th power of the Floer operator of the plumbed perturbation of neck length `2R` applied to the
pre-glued composition is at most `2 (C' e^{-κ R})^p`: the operator is at most `C' e^{-κ R}` there
and vanishes outside the band `R - 1 ≤ s ≤ R + 1`, of area `2`. -/
theorem exists_eventually_setLIntegral_floerOperator_plumbedPerturbation_preglueComposition_comp_le
    (ω : SymplecticForm V) (hq : q ≠ inf) (hab : Hb q = Ha inf) (hHb : Periodic (Hb q) 1)
    {J : ℝ → V → V →L[ℝ] V} {C κ T T' : ℝ} (hT : 2 ≤ T) (hT' : T' ≤ -2)
    (hH : ContDiff ℝ 2 (uncurry (Hb q))) (hJ : Continuous (uncurry J))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (Hb q t) (x t)) t) (hxper : Periodic x 1)
    (hκ : 0 < κ)
    (hud : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (u ∘ positiveEndChart q) (s, t))
    (hu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u (positiveEndChart q (s, t)) - x t‖ ≤ C * Real.exp (-(κ * s)))
    (hdu : ∀ᶠ s in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u ∘ positiveEndChart q) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Hb q t) (x t))‖ ≤
        C * Real.exp (-(κ * s)))
    (huF : ∀ z ∈ Ioi T ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ Hb q p.2) (u ∘ positiveEndChart q) z = 0)
    (hu'd : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (u' ∘ endChart inf) (s, t))
    (hu' : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖u' (endChart inf (s, t)) - x t‖ ≤ C * Real.exp (κ * s))
    (hdu' : ∀ᶠ s in atBot, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (u' ∘ endChart inf) (s, t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Hb q t) (x t))‖ ≤
        C * Real.exp (κ * s))
    (hu'F : ∀ z ∈ Iio T' ×ˢ Icc (0 : ℝ) 1, ω.floerOperator (fun p ↦ J p.2) (fun _ _ ↦ 0)
      (fun p ↦ Hb q p.2) (u' ∘ endChart inf) z = 0)
    {p : ℝ} (hp : 0 < p) :
    ∃ C', ∀ᶠ R in atTop, ∫⁻ z in Ioo T (2 * R + T') ×ˢ Icc (0 : ℝ) 1,
      ‖ω.floerOperator (fun p ↦ J p.2)
          (perturbationPullback (positiveEndChart q)
            (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x
              Complex.I) stdComplexLineReal)
          (perturbationPullback (positiveEndChart q)
            (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation Ha Hb q (2 * R) (Complex.equivRealProdCLM.symm z) x
              Complex.I) stdComplexLineImag)
          (preglueComposition q x u u' R ∘ positiveEndChart q) z‖ₑ ^ p ≤
        2 * ENNReal.ofReal (C' * Real.exp (-(κ * R))) ^ p := by
  obtain ⟨C', hC'⟩ :=
    ω.exists_eventually_norm_floerOperator_plumbedPerturbation_preglueComposition_comp_le
      (Ha := Ha) hq hab hHb hT hT' hH hJ hx hxper hκ hud hu hdu huF hu'd hu' hdu' hu'F
  refine ⟨C', (hC'.and (eventually_ge_atTop 1)).mono fun R ⟨hR, hR₁⟩ ↦ ?_⟩
  set c := ENNReal.ofReal (C' * Real.exp (-(κ * R))) ^ p
  set B : Set (ℝ × ℝ) := Icc (R - 1) (R + 1) ×ˢ Icc (0 : ℝ) 1
  have hB : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  -- Pointwise, the integrand is at most `c` on the band `B` and vanishes off it.
  calc _ ≤ ∫⁻ z in Ioo T (2 * R + T') ×ˢ Icc (0 : ℝ) 1, B.indicator (fun _ ↦ c) z :=
        setLIntegral_mono (measurable_const.indicator hB) fun z hz ↦ by
          by_cases hzB : z ∈ B
          · rw [indicator_of_mem hzB, ← ofReal_norm]
            exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hR z hz)) hp.le
          · have hzR : 1 < |z.1 - R| := by
              by_contra h
              rw [not_lt, abs_le] at h
              exact hzB ⟨⟨by linarith [h.1], by linarith [h.2]⟩, hz.2⟩
            rw [ω.floerOperator_plumbedPerturbation_preglueComposition_comp_eq_zero hq hab hHb J
              hT hT' hxper hR₁ huF hu'F hz hzR, eNorm_zero, ENNReal.zero_rpow_of_pos hp]
            exact zero_le
    _ ≤ ∫⁻ z, B.indicator (fun _ ↦ c) z := setLIntegral_le_lintegral _ _
    _ = 2 * c := by
        rw [lintegral_indicator_const hB, Measure.volume_eq_prod, Measure.prod_prod,
          Real.volume_Icc, Real.volume_Icc, mul_comm]
        norm_num

end SymplecticForm

end TauCeti
