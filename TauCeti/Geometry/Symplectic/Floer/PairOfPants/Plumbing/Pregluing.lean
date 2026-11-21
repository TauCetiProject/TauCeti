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
  Identifying this operator with the plumbed Floer operator of
  `TauCeti.Floer.plumbedPerturbation` on the neck is not proved here.

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
theorem preglueComposition_of_le (h : (positiveEndCoord q z).1 ≤ R - 1) :
    preglueComposition q x u u' R z = u z :=
  preglueEnd_of_le h

/-- Near a point other than the center of the end `q` whose signed longitudinal coordinate on `q`
is less than `R - 1`, the pre-glued composition agrees with `u`. -/
theorem preglueComposition_eventuallyEq_of_lt
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (h : (positiveEndCoord q z).1 < R - 1) : preglueComposition q x u u' R =ᶠ[𝓝 z] u :=
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
      (by rwa [fst_positiveEndCoord, endSign_eq_one hq, one_mul])),
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

end SymplecticForm

end TauCeti
