/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Plumbing
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic

/-!
# Plumbing pair-of-pants perturbation data along a neck

Composing two pair-of-pants products plugs the output of one pair of pants `S'` into an input
`q ∈ {0, 1}` of another `S`. On the domain this is the plumbing map
`ψ = TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L` of neck length `L`, which glues the
part `Re z > -L` of `S'`, in the end coordinate at `∞`, to the part `Re z < L` of `S`, in the end
coordinate of `q`, into the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`
(`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap_image_union`).

This file glues the Hamiltonian perturbations of the two pairs of pants
(`TauCeti.Floer.pairOfPantsPerturbation`) along the same neck. If the Hamiltonian `Ha ∞` on the
output end of `S'` is the Hamiltonian `Hb q` on the input end of `S`, then on the part of the
neck where both perturbations are cylindrical, the pushforward of the perturbation of `S'` along
`ψ` is the perturbation of `S`: both are `H(t) dt`, and `ψ` is the translation `z ↦ z + L` in end
coordinates (`TauCeti.Floer.pairOfPantsPerturbation_plumbingMap`). The glued datum
`TauCeti.Floer.plumbedPerturbation` uses the pushforward on the half `Re z > L/2` of the end `q`
and the perturbation of `S` elsewhere. It restricts to each of the two given perturbations away
from a collar of width `2` at the end of each piece, and for `L > 4`, when these two regions
overlap in an open neck, it is smooth on the four-punctured sphere. Its four ends therefore carry
the two input Hamiltonians of `S'` at `c_q` and `ψ(1)`, and the remaining input and output
Hamiltonians of `S`.

## Main definitions

* `TauCeti.Floer.plumbedPerturbation Ha Hb q L`: the perturbation on the plumbed four-punctured
  sphere.

## Main results

* `TauCeti.Floer.pairOfPantsPerturbation_plumbingMap`: the two perturbations match on the neck.
* `TauCeti.Floer.plumbedPerturbation_of_re_endCoord_le`: off the collar `Re z > L - 2` of the end
  `q`, the glued datum is the perturbation of the receiving pair of pants.
* `TauCeti.Floer.plumbedPerturbation_plumbingMap`: off the collar `Re z < 2 - L` of the end at
  `∞`, the pullback of the glued datum along `ψ` is the perturbation of the inserted pair of pants.
* `TauCeti.Floer.contMDiffAt_plumbedPerturbation`: the glued datum is smooth on the four-punctured
  sphere.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on gluing perturbation data for compositions of pair-of-pants products.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on gluing
  perturbation data along strip-like ends.
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
theorem pairOfPantsPerturbation_plumbingMap (hHa : Periodic (Ha inf) 1)
    (hHb : Periodic (Hb q) 1) (hab : Hb q = Ha inf) {w : ℂ}
    (h₁ : (inf.endCoord w).re ≤ -2) (h₂ : 2 ≤ q.endSign * ((inf.endCoord w).re + L))
    (x : M) (v : ℂ) :
    pairOfPantsPerturbation Hb (q.plumbingMap L w) x (q.plumbingFactor L * v) =
      pairOfPantsPerturbation Ha w x v := by
  set z := inf.endCoord w
  have hwz : inf.cylindricalEndLift z = w :=
    inf.cylindricalEndLift_endCoord
      (inf.ne_endCenter_of_re_endCoord_ne_zero (by linarith : z.re < 0).ne)
  -- Write the tangent vector `v` as the image of a tangent vector `v'` of the cylinder.
  obtain ⟨v', rfl⟩ : ∃ v', v = deriv inf.cylindricalEndLift z * v' :=
    ⟨v / _, (mul_div_cancel₀ v (deriv_cylindricalEndLift_ne_zero _ _)).symm⟩
  rw [← hwz, ← cylindricalEndLift_add_ofReal, ← mul_assoc,
    ← deriv_cylindricalEndLift_add_ofReal,
    pairOfPantsPerturbation_cylindricalEndLift hHb (by simpa using h₂) x v',
    pairOfPantsPerturbation_cylindricalEndLift hHa (by simp; linarith) x v', hab]
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
theorem plumbedPerturbation_of_re_endCoord_le (hq : q ≠ inf) (hHa : Periodic (Ha inf) 1)
    (hHb : Periodic (Hb q) 1) (hab : Hb q = Ha inf) {w : ℂ}
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
      ← pairOfPantsPerturbation_plumbingMap (L := L) hHa hHb hab (by linarith)
        (by rw [endSign_eq_one hq]; linarith) x, plumbingMap_sub_endCenter_div,
      mul_inv_cancel_left₀ (q.plumbingFactor_ne_zero L)]
  · rfl

/-- **The plumbed perturbation on the inserted pair of pants.** Away from the collar `Re z < 2 - L`
of the end at `∞`, the pullback of the plumbed perturbation along the plumbing map is the
perturbation of the inserted pair of pants. -/
theorem plumbedPerturbation_plumbingMap (hq : q ≠ inf) (hHa : Periodic (Ha inf) 1)
    (hHb : Periodic (Hb q) 1) (hab : Hb q = Ha inf) {w : ℂ} (hw : w ≠ 0)
    (h : 2 - L ≤ (inf.endCoord w).re) (x : M) (v : ℂ) :
    plumbedPerturbation Ha Hb q L (q.plumbingMap L w) x (q.plumbingFactor L * v) =
      pairOfPantsPerturbation Ha w x v := by
  rw [plumbedPerturbation_def, re_endCoord_plumbingMap q L hw]
  split_ifs with h'
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
      inv_mul_cancel_left₀ (q.plumbingFactor_ne_zero L),
      plumbingMap_sub_endCenter_div_plumbingFactor]
  · -- On the part `2 - L ≤ Re z ≤ -L/2` of the neck the two perturbations match.
    exact pairOfPantsPerturbation_plumbingMap hHa hHb hab (by linarith)
      (by rw [endSign_eq_one hq]; linarith) x v

/-- Near a point of the end `q` with longitudinal coordinate `> 2`, the plumbed perturbation is
the pushforward of the perturbation of the inserted pair of pants. -/
private theorem plumbedPerturbation_eq_comp (hq : q ≠ inf) (hHa : Periodic (Ha inf) 1)
    (hHb : Periodic (Hb q) 1) (hab : Hb q = Ha inf) {w : ℂ}
    (hw : 2 < (q.endCoord w).re) (x : M) :
    plumbedPerturbation Ha Hb q L w x =
      (pairOfPantsPerturbation Ha ((w - q.endCenter) / q.plumbingFactor L) x).comp
        (ContinuousLinearMap.mul ℝ ℂ (q.plumbingFactor L)⁻¹) := by
  have hc : w ≠ q.endCenter :=
    q.ne_endCenter_of_re_endCoord_ne_zero (by linarith : 0 < (q.endCoord w).re).ne'
  have hre := re_endCoord_inf_sub_endCenter_div q L hc
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ← plumbedPerturbation_plumbingMap hq hHa hHb hab
      (q.sub_endCenter_div_plumbingFactor_ne_zero L hc) (by rw [hre]; linarith),
    plumbingMap_sub_endCenter_div, mul_inv_cancel_left₀ (q.plumbingFactor_ne_zero L)]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The plumbed perturbation is smooth.** For Hamiltonians of period one which are `C^n` on
`ℝ × M`, with matching Hamiltonians on the glued ends and neck length `L > 4`, the plumbed
perturbation is `C^n` on `S₄ × M`, where `S₄ = ℂ ∖ {0, 1, ψ(1)}` is the plumbed four-punctured
sphere. -/
theorem contMDiffAt_plumbedPerturbation {n : ℕ∞} (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1)
    (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => plumbedPerturbation Ha Hb q L p.1 p.2) (w, x) := by
  have hc : w ≠ q.endCenter := ne_endCenter hw.1 q
  -- The longitudinal coordinate of the end `q` is continuous near `w`.
  have hcont : ContinuousAt (fun p : ℂ × M => (q.endCoord p.1).re) (w, x) :=
    ContinuousAt.comp (g := fun w => (q.endCoord w).re) (f := Prod.fst)
      (q.contDiffAt_re_endCoord hc (n := 0)).continuousAt continuousAt_fst
  rcases lt_or_ge (q.endCoord w).re (L - 2) with hlt | hge
  · -- Off the collar of the end `q`, the datum is the perturbation of the receiving sphere.
    refine (contMDiffAt_pairOfPantsPerturbation hHb hHbs ⟨w, hw.1⟩ x).congr_of_eventuallyEq ?_
    filter_upwards [hcont.eventually (gt_mem_nhds hlt)] with p hp
    exact plumbedPerturbation_of_re_endCoord_le hq (hHa inf) (hHb q) hab hp.le p.2
  · -- Deep in the end `q`, the datum is the pushforward of the perturbation of the inserted
    -- sphere along the affine plumbing map.
    have h2 : 2 < (q.endCoord w).re := by linarith
    set a := q.plumbingFactor L
    set w' := (w - q.endCenter) / a
    have hw' : q.plumbingMap L w' = w := q.plumbingMap_sub_endCenter_div L w
    have hw'0 : w' ≠ 0 := q.sub_endCenter_div_plumbingFactor_ne_zero L hc
    have hw'1 : w' ≠ 1 := fun h => hw.2 (by rw [← hw', h])
    have hf : ContMDiffAt (𝓘(ℝ, ℂ).prod I) (𝓘(ℝ, ℂ).prod I) n
        (fun p : ℂ × M => ((p.1 - q.endCenter) / a, p.2)) (w, x) :=
      ((((contDiff_id.sub contDiff_const).div_const a).contMDiff.contMDiffAt).comp _
        contMDiffAt_fst).prodMk contMDiffAt_snd
    have hK := ((contMDiffAt_pairOfPantsPerturbation hHa hHas ⟨w', hw'0, hw'1⟩ x).comp
      (w, x) hf).clm_comp (contMDiffAt_const (c := ContinuousLinearMap.mul ℝ ℂ a⁻¹))
    refine hK.congr_of_eventuallyEq ?_
    filter_upwards [hcont.eventually (lt_mem_nhds h2)] with p hp
    exact plumbedPerturbation_eq_comp hq (hHa inf) (hHb q) hab hp p.2

end TauCeti.Floer
