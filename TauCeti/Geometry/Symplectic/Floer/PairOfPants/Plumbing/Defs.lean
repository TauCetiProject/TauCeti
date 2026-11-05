/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Plumbing
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic

/-!
# Plumbing formulas for pair-of-pants Hamiltonian data

The output end of one pair of pants is glued to an input end of another using the affine
plumbing map. Matching end Hamiltonians make the two perturbations agree on the cylindrical
neck. The datum `TauCeti.Floer.plumbedPerturbation` uses the pushed-forward inserted datum
on one half-neck and the receiving datum elsewhere. The formulas here identify it on the
open overlap, before proving family regularity in `Plumbing.Family` and curvature bounds in
`Plumbing.Basic`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on gluing perturbation data for compositions of pair-of-pants products.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-- **The perturbations match on the neck.** Suppose the Hamiltonian on the output end of the
inserted pair of pants is the Hamiltonian on the input end `q` of the receiving one. At a point
`w` of the end at `∞` with end coordinate `z`, where `Re z ≤ -2` and `±Re (z + L) ≥ 2` so that
both perturbations are cylindrical, the perturbation of the receiving pair of pants at `ψ(w)`
evaluated on `ψ'(w) v` is the perturbation of the inserted one at `w` evaluated on `v`. -/
theorem pairOfPantsPerturbation_plumbingMap (hab : Hb q = Ha inf) {w : ℂ}
    (h₁ : (inf.endCoord w).re ≤ -2) (h₂ : 2 ≤ q.endSign * ((inf.endCoord w).re + L))
    (x : M) (v : ℂ) :
    pairOfPantsPerturbation Hb (q.plumbingMap L w) x (q.plumbingFactor L * v) =
      pairOfPantsPerturbation Ha w x v := by
  have hw : w ≠ 0 := by
    simpa using inf.ne_endCenter_of_re_endCoord_ne_zero (by linarith : (inf.endCoord w).re < 0).ne
  have hz := endCoord_plumbingMap q L hw
  rw [pairOfPantsPerturbation_eq_smul_endAngularForm (r := q) (by rw [hz]; simpa using h₂),
    pairOfPantsPerturbation_eq_smul_endAngularForm (r := inf) (by simp; linarith),
    smul_apply, smul_apply, ← deriv_plumbingMap q L w,
    endAngularForm_plumbingMap, hz, hab]
  simp

open Classical in
/-- **The plumbed perturbation.** The perturbation datum on the four-punctured sphere
`ℂ ∖ {0, 1, ψ(1)}` obtained by plumbing the output end of a pair of pants with Hamiltonians `Ha`
into the input end `q` of a pair of pants with Hamiltonians `Hb`, along a neck of length `L`. On
the half `Re z > L/2` of the end `q` it is the pushforward `v ↦ K_a(ψ⁻¹ w)(v / ψ')` of the
perturbation of the inserted pair of pants along the plumbing map `ψ`, and elsewhere it is the
perturbation of the receiving pair of pants. -/
def plumbedPerturbation (Ha Hb : Puncture → ℝ → M → ℝ) (q : Puncture) (L : ℝ) (w : ℂ) (x : M) :
    ℂ →L[ℝ] ℝ :=
  if L / 2 < (q.endCoord w).re then
    (pairOfPantsPerturbation Ha ((w - q.endCenter) / q.plumbingFactor L) x).comp
      (ContinuousLinearMap.mul ℝ ℂ (q.plumbingFactor L)⁻¹)
  else pairOfPantsPerturbation Hb w x

open Classical in
theorem plumbedPerturbation_def (Ha Hb : Puncture → ℝ → M → ℝ) (q : Puncture) (L : ℝ) (w : ℂ)
    (x : M) :
    plumbedPerturbation Ha Hb q L w x =
      if L / 2 < (q.endCoord w).re then
        (pairOfPantsPerturbation Ha ((w - q.endCenter) / q.plumbingFactor L) x).comp
          (ContinuousLinearMap.mul ℝ ℂ (q.plumbingFactor L)⁻¹)
      else pairOfPantsPerturbation Hb w x := by
  rw [plumbedPerturbation]

/-- **The plumbed perturbation on the receiving pair of pants.** Away from the collar
`Re z > L - 2` of the end `q`, the plumbed perturbation is the perturbation of the receiving pair
of pants. -/
theorem plumbedPerturbation_of_re_endCoord_le (hq : q ≠ inf) (hab : Hb q = Ha inf) {w : ℂ}
    (hw : (q.endCoord w).re ≤ L - 2) (x : M) :
    plumbedPerturbation Ha Hb q L w x = pairOfPantsPerturbation Hb w x := by
  rw [plumbedPerturbation_def]
  split_ifs with h
  · -- On the part `L/2 < Re z ≤ L - 2` of the neck the two perturbations match.
    have hc : w ≠ q.endCenter :=
      q.ne_endCenter_of_re_endCoord_ne_zero (by linarith : 0 < (q.endCoord w).re).ne'
    have hre := re_endCoord_inf_sub_endCenter_div q L hc
    ext v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
      ← pairOfPantsPerturbation_plumbingMap (L := L) hab (by linarith)
        (by rw [endSign_eq_one hq]; linarith) x, plumbingMap_sub_endCenter_div,
      mul_inv_cancel_left₀ (q.plumbingFactor_ne_zero L)]
  · rfl

/-- **The plumbed perturbation on the inserted pair of pants.** Away from the collar `Re z < 2 - L`
of the end at `∞`, the pullback of the plumbed perturbation along the plumbing map is the
perturbation of the inserted pair of pants. -/
theorem plumbedPerturbation_plumbingMap (hq : q ≠ inf) (hab : Hb q = Ha inf) {w : ℂ}
    (hw : w ≠ 0)
    (h : 2 - L ≤ (inf.endCoord w).re) (x : M) (v : ℂ) :
    plumbedPerturbation Ha Hb q L (q.plumbingMap L w) x (q.plumbingFactor L * v) =
      pairOfPantsPerturbation Ha w x v := by
  rw [plumbedPerturbation_def, re_endCoord_plumbingMap q L hw]
  split_ifs with h'
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
      inv_mul_cancel_left₀ (q.plumbingFactor_ne_zero L),
      plumbingMap_sub_endCenter_div_plumbingFactor]
  · -- On the part `2 - L ≤ Re z ≤ -L/2` of the neck the two perturbations match.
    exact pairOfPantsPerturbation_plumbingMap hab (by linarith)
      (by rw [endSign_eq_one hq]; linarith) x v

/-- On the open region of the end `q` with longitudinal coordinate `> 2`, the plumbed
perturbation is the pushforward of the inserted datum. This region is independent of length. -/
theorem plumbedPerturbation_eq_comp (hq : q ≠ inf) (hab : Hb q = Ha inf) {w : ℂ}
    (hw : 2 < (q.endCoord w).re) (x : M) :
    plumbedPerturbation Ha Hb q L w x =
      (pairOfPantsPerturbation Ha ((w - q.endCenter) / q.plumbingFactor L) x).comp
        (ContinuousLinearMap.mul ℝ ℂ (q.plumbingFactor L)⁻¹) := by
  have hc : w ≠ q.endCenter :=
    q.ne_endCenter_of_re_endCoord_ne_zero (by linarith : 0 < (q.endCoord w).re).ne'
  have hre := re_endCoord_inf_sub_endCenter_div q L hc
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ← plumbedPerturbation_plumbingMap hq hab
      (q.sub_endCenter_div_plumbingFactor_ne_zero L hc) (by rw [hre]; linarith),
    plumbingMap_sub_endCenter_div, mul_inv_cancel_left₀ (q.plumbingFactor_ne_zero L)]

end TauCeti.Floer
