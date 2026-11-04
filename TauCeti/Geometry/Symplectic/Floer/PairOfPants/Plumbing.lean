/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Plumbing
public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Basic
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Symplectic.Floer.Pullback

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
from a collar of width `2` at the end of each piece. For `L > 4`, when these two regions overlap
in an open neck, and for period-one Hamiltonians of class `C^n` (smooth ones, taking `n = ∞`), it
is of class `C^n` on the four-punctured sphere. Its four ends therefore carry
the two input Hamiltonians of `S'` at `c_q` and `ψ(1)`, and the remaining input and output
Hamiltonians of `S`.

The energy identity turns a bound on the integrated curvature `∫ |R_K|` of the perturbation into
an energy bound, so the curvature of the plumbed datum must stay bounded as the neck grows. For a
symplectic vector space target it does. Off the half `Re z > L/2` of the end `q` the plumbed datum
is the perturbation of `S`, and on that half its pullback along the affine map `ψ` is the
perturbation of `S'`. Since the absolute curvature integral is invariant under changes of
coordinates (`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_image`), the integrated
curvature of the plumbed datum is at most the sum of the bounds for `S` and `S'` given by
`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`, which
does not depend on `L`. The curvature of the neck itself vanishes, as the datum is `H(t) dt` there.

## Main definitions

* `TauCeti.Floer.plumbedPerturbation Ha Hb q L`: the perturbation on the plumbed four-punctured
  sphere.

## Main results

* `TauCeti.Floer.pairOfPantsPerturbation_plumbingMap`: the two perturbations match on the neck.
* `TauCeti.Floer.plumbedPerturbation_of_re_endCoord_le`: off the collar `Re z > L - 2` of the end
  `q`, the glued datum is the perturbation of the receiving pair of pants.
* `TauCeti.Floer.plumbedPerturbation_plumbingMap`: off the collar `Re z < 2 - L` of the end at
  `∞`, the pullback of the glued datum along `ψ` is the perturbation of the inserted pair of pants.
* `TauCeti.Floer.contMDiffAt_plumbedPerturbation`: for `L > 4` and period-one Hamiltonians of
  class `C^n`, the glued datum is of class `C^n` on the four-punctured sphere; smooth Hamiltonians
  give a smooth datum.
* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le`: for
  `L > 4`, the integrated curvature of the glued datum along any map into a symplectic vector
  space is at most the sum of bounds for the six end Hamiltonians of the two pairs of pants,
  uniformly in `L`.

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

/-- Near a point of the end `q` with longitudinal coordinate `> 2`, the plumbed perturbation is
the pushforward of the perturbation of the inserted pair of pants. -/
private theorem plumbedPerturbation_eq_comp (hq : q ≠ inf) (hab : Hb q = Ha inf) {w : ℂ}
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
    exact plumbedPerturbation_of_re_endCoord_le hq hab hp.le p.2
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
    exact plumbedPerturbation_eq_comp hq hab hp p.2

omit [TopologicalSpace M] [ChartedSpace G M] in
/-- Near a point off the collar `Re z ≥ L - 2` of the end `q`, the plumbed perturbation is the
perturbation of the receiving pair of pants. -/
private theorem eventually_plumbedPerturbation_eq (hq : q ≠ inf) (hab : Hb q = Ha inf) {w : ℂ}
    (hw : w ≠ q.endCenter) (h : (q.endCoord w).re < L - 2) :
    ∀ᶠ w' in 𝓝 w, plumbedPerturbation Ha Hb q L w' = pairOfPantsPerturbation Hb w' := by
  filter_upwards [((q.contDiffAt_re_endCoord hw (n := 0)).continuousAt).eventually
    (gt_mem_nhds h)] with w' hw'
  exact funext fun x => plumbedPerturbation_of_re_endCoord_le hq hab hw'.le x

omit [TopologicalSpace M] [ChartedSpace G M] in
/-- Near a point off the collar `Re z ≤ 2 - L` of the end at `∞` of the inserted pair of pants,
the pullback of the plumbed perturbation along the plumbing map is the perturbation of the
inserted pair of pants. -/
private theorem eventually_plumbedPerturbation_plumbingMap (hq : q ≠ inf) (hab : Hb q = Ha inf)
    {w : ℂ} (hw : w ≠ 0) (h : 2 - L < (inf.endCoord w).re) :
    ∀ᶠ w' in 𝓝 w, ∀ x v, plumbedPerturbation Ha Hb q L (q.plumbingMap L w') x
      (q.plumbingFactor L * v) = pairOfPantsPerturbation Ha w' x v := by
  have hc : ContinuousAt (fun w => (inf.endCoord w).re) w :=
    (inf.contDiffAt_re_endCoord (by simpa using hw) (n := 0)).continuousAt
  filter_upwards [eventually_ne_nhds hw, hc.eventually (lt_mem_nhds h)] with w' hw' h' x v
  exact plumbedPerturbation_plumbingMap hq hab hw' h'.le x v

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ha Hb : Puncture → ℝ → V → ℝ} {q : Puncture} {L : ℝ}

/-- The plumbing map in the real coordinates `ℝ × ℝ ≃ ℂ`. -/
private noncomputable def plumbingChart (q : Puncture) (L : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  Complex.equivRealProdCLM ∘ q.plumbingMap L ∘ Complex.equivRealProdCLM.symm

private theorem plumbingChart_apply (q : Puncture) (L : ℝ) (z : ℝ × ℝ) :
    plumbingChart q L z =
      Complex.equivRealProdCLM (q.plumbingMap L (Complex.equivRealProdCLM.symm z)) :=
  (rfl)

private theorem contDiff_plumbingChart (q : Puncture) (L : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (plumbingChart q L) := by
  have hψ : ContDiff ℝ n (q.plumbingMap L) := by
    have h : q.plumbingMap L = fun w => q.endCenter + q.plumbingFactor L * w :=
      funext (plumbingMap_apply q L)
    rw [h]
    fun_prop
  exact Complex.equivRealProdCLM.contDiff.comp (hψ.comp Complex.equivRealProdCLM.symm.contDiff)

private theorem injective_plumbingChart (q : Puncture) (L : ℝ) :
    Injective (plumbingChart q L) :=
  Complex.equivRealProdCLM.injective.comp
    ((q.plumbingMap_injective L).comp Complex.equivRealProdCLM.symm.injective)

private theorem fderiv_plumbingChart_apply (q : Puncture) (L : ℝ) (z v : ℝ × ℝ) :
    fderiv ℝ (plumbingChart q L) z v = Complex.equivRealProdCLM
      (q.plumbingFactor L * Complex.equivRealProdCLM.symm v) := by
  have h := ((q.hasDerivAt_plumbingMap L
    (Complex.equivRealProdCLM.symm z)).hasFDerivAt.restrictScalars ℝ)
  rw [plumbingChart, (Complex.equivRealProdCLM.hasFDerivAt.comp z
    (h.comp z Complex.equivRealProdCLM.symm.hasFDerivAt)).fderiv]
  simp [mul_comm]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The pullback along the plumbing chart of a datum `P` on `ℂ`, written in the real
coordinates through its values on `1` and `i`, evaluates `P` at the image under the plumbing
map on the image of the tangent vector. -/
private theorem perturbationPullback_plumbingChart (P : ℂ → V → ℂ →L[ℝ] ℝ) (v w : ℝ × ℝ)
    (x : V) :
    perturbationPullback (plumbingChart q L)
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) v w x =
      P (q.plumbingMap L (Complex.equivRealProdCLM.symm w)) x
        (q.plumbingFactor L * Complex.equivRealProdCLM.symm v) := by
  -- A real-linear functional `κ` on `ℂ` satisfies `κ ξ = Re ξ · κ 1 + Im ξ · κ i`.
  have hκ (κ : ℂ →L[ℝ] ℝ) (ξ : ℂ) : ξ.re * κ 1 + ξ.im * κ Complex.I = κ ξ := by
    have hξ : ξ = ξ.re • (1 : ℂ) + ξ.im • Complex.I := by simp
    conv_rhs => rw [hξ]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [perturbationPullback_apply, fderiv_plumbingChart_apply, plumbingChart_apply,
    ContinuousLinearEquiv.symm_apply_apply, Complex.equivRealProdCLM_apply, hκ]

/-- At points other than the four punctures, the plumbed perturbation of `C¹` Hamiltonians is
differentiable jointly in the domain and target points. -/
private theorem differentiableAt_plumbedPerturbation (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1)
    (x : V) :
    DifferentiableAt ℝ (fun p : ℂ × V ↦ plumbedPerturbation Ha Hb q L p.1 p.2) (w, x) := by
  have hmfd {H : Puncture → ℝ → V → ℝ} (hH : ∀ r, ContDiff ℝ 1 (uncurry (H r))) (r : Puncture) :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry (H r)) := by
    have h := (hH r).contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have h := contMDiffAt_plumbedPerturbation (n := 1) hq hHa hHb (hmfd hHas) (hmfd hHbs) hab hL
    hw x
  have h' : ContMDiffAt 𝓘(ℝ, ℂ × V) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × V ↦ plumbedPerturbation Ha Hb q L p.1 p.2) (w, x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  exact h'.contDiffAt.differentiableAt one_ne_zero

/-- The longitudinal coordinate of an end, in the real coordinates, is measurable. -/
private theorem measurable_re_endCoord (r : Puncture) :
    Measurable fun z : ℝ × ℝ ↦ (r.endCoord (Complex.equivRealProdCLM.symm z)).re := by
  simp_rw [re_endCoord]
  exact (Real.measurable_log.comp (by fun_prop : Continuous fun z : ℝ × ℝ ↦
    ‖(Complex.equivRealProdCLM.symm z - r.endCenter) / r.endScale‖).measurable).neg.div_const _

variable [FiniteDimensional ℝ V]

/-- Off the collar `Re z ≥ L/2` of the end `q`, the curvature of the plumbed perturbation is the
curvature of the perturbation of the receiving pair of pants. -/
private theorem hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_le (ω : SymplecticForm V)
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (hL : 4 < L) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (hre : (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2) :
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        z := by
  have hP := (Complex.equivRealProdCLM.symm.continuous.tendsto z).eventually
    (eventually_plumbedPerturbation_eq (L := L) hq hab hz (by linarith))
  exact ω.hamiltonianCurvature_congr_of_eventuallyEq
    (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
    (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])

/-- Off the collar `Re z ≤ -L/2` of the end at `∞` of the inserted pair of pants, the curvature of
the pullback of the plumbed perturbation along the plumbing chart is the curvature of the
perturbation of the inserted pair of pants. -/
private theorem hamiltonianCurvature_perturbationPullback_plumbedPerturbation
    (ω : SymplecticForm V) (hq : q ≠ inf) (hab : Hb q = Ha inf) (hL : 4 < L) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0)
    (hre : -(L / 2) < (inf.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    ω.hamiltonianCurvature
        (perturbationPullback (plumbingChart q L)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
            Complex.I) stdComplexLineReal)
        (perturbationPullback (plumbingChart q L)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
            Complex.I) stdComplexLineImag) z =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        z := by
  have hP := (Complex.equivRealProdCLM.symm.continuous.tendsto z).eventually
    (eventually_plumbedPerturbation_plumbingMap (L := L) hq hab hz (by linarith))
  have h₁ : Complex.equivRealProdCLM.symm stdComplexLineReal = 1 := by
    apply Complex.ext <;> simp [stdComplexLineReal_eq]
  have hI : Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
    apply Complex.ext <;> simp [stdComplexLineImag_eq]
  exact ω.hamiltonianCurvature_congr_of_eventuallyEq
    (hP.mono fun z' hz' ↦ funext fun x ↦ by rw [perturbationPullback_plumbingChart, h₁, hz'])
    (hP.mono fun z' hz' ↦ funext fun x ↦ by rw [perturbationPullback_plumbingChart, hI, hz'])

/-- On the part `A` of the plane off the collar `Re z > L/2` of the end `q`, the integrated
curvature of the plumbed perturbation is that of the receiving pair of pants, and so is at most
the sum of bounds for its end Hamiltonians. -/
private theorem setLIntegral_enorm_hamiltonianCurvature_plumbedPerturbation_le_receiving
    (ω : SymplecticForm V) (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hab : Hb q = Ha inf) (hL : 4 < L)
    {Bb : Puncture → ℝ} (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → V) :
    ∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ q.endCenter ∧
        (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2},
      ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ r, ENNReal.ofReal (Bb r) := by
  have hAm : MeasurableSet {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ q.endCenter ∧
      (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2} :=
    ((measurableSet_singleton q.endCenter).compl.preimage
      Complex.equivRealProdCLM.symm.continuous.measurable).inter
      (measurableSet_le (measurable_re_endCoord q) measurable_const)
  calc _ ≤ ∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ q.endCenter ∧
          (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2},
        ‖ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)‖ₑ :=
        setLIntegral_mono' hAm fun z hz ↦ by
          rw [hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_le ω hq hab hL hz.1 hz.2]
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hHb hHbs hBb u

/-- On the image under the plumbing chart of the part `S` of the inserted pair of pants off the
collar `Re z < -L/2` of its end at `∞`, the integrated curvature of the plumbed perturbation is
that of the inserted pair of pants, and so is at most the sum of bounds for its end
Hamiltonians. -/
private theorem setLIntegral_enorm_hamiltonianCurvature_plumbedPerturbation_le_inserted
    (ω : SymplecticForm V) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hab : Hb q = Ha inf) (hL : 4 < L)
    {Ba : Puncture → ℝ} (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (u : ℝ × ℝ → V) :
    ∫⁻ z in plumbingChart q L '' {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1 ∧
        -(L / 2) < (inf.endCoord (Complex.equivRealProdCLM.symm z)).re},
      ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ r, ENNReal.ofReal (Ba r) := by
  set S := {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1 ∧
    -(L / 2) < (inf.endCoord (Complex.equivRealProdCLM.symm z)).re}
  have hSm : MeasurableSet S :=
    ((measurableSet_singleton 0).compl.preimage
      Complex.equivRealProdCLM.symm.continuous.measurable).inter
      (((measurableSet_singleton 1).compl.preimage
        Complex.equivRealProdCLM.symm.continuous.measurable).inter
        (measurableSet_lt measurable_const (measurable_re_endCoord inf)))
  -- The plumbing chart maps `S` into the plumbed four-punctured sphere, where the plumbed
  -- perturbation is differentiable.
  have hdiff {w : ℝ × ℝ} (hw : w ∈ S) (y : V) :
      DifferentiableAt ℝ (fun p : ℂ × V ↦ plumbedPerturbation Ha Hb q L p.1 p.2)
        (Complex.equivRealProdCLM.symm (plumbingChart q L w), y) := by
    refine differentiableAt_plumbedPerturbation hq hHa hHb hHas hHbs hab hL ?_ y
    rw [plumbingChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos ?_,
      fun h ↦ hw.2.1 (q.plumbingMap_injective L h)⟩
    rw [endSign_eq_one hq, one_mul, re_endCoord_plumbingMap q L hw.1]
    linarith [hw.2.2]
  have hdom {w : ℝ × ℝ} (hw : w ∈ S) (y : V) (v : ℂ) : DifferentiableAt ℝ
      (fun z ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) y v)
      (plumbingChart q L w) :=
    ((hdiff hw y).comp (f := fun z ↦ (Complex.equivRealProdCLM.symm z, y))
      (plumbingChart q L w) (Complex.equivRealProdCLM.symm.differentiableAt.prodMk
        (differentiableAt_const y))).clm_apply (differentiableAt_const v)
  have htgt {w : ℝ × ℝ} (hw : w ∈ S) (y : V) (v : ℂ) : DifferentiableAt ℝ
      (fun y ↦ plumbedPerturbation Ha Hb q L
        (Complex.equivRealProdCLM.symm (plumbingChart q L w)) y v) y :=
    ((hdiff hw y).comp (f := fun y ↦ (Complex.equivRealProdCLM.symm (plumbingChart q L w), y))
      y ((differentiableAt_const _).prodMk differentiableAt_id)).clm_apply
      (differentiableAt_const v)
  rw [ω.lintegral_enorm_hamiltonianCurvature_image hSm (injective_plumbingChart q L).injOn
    (fun w _ ↦ (contDiff_plumbingChart q L).contDiffAt)
    (fun w hw ↦ hdom hw _ 1) (fun w hw ↦ hdom hw _ Complex.I)
    (fun w hw ↦ htgt hw _ 1) (fun w hw ↦ htgt hw _ Complex.I)]
  calc _ = ∫⁻ w in S, ‖ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
          w ((u ∘ plumbingChart q L) w)‖ₑ :=
        setLIntegral_congr_fun hSm fun w hw ↦ by
          rw [hamiltonianCurvature_perturbationPullback_plumbedPerturbation ω hq hab hL hw.1
            hw.2.2, comp_apply]
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hHa hHas hBa _

/-- **The integrated curvature of the plumbed perturbation is bounded uniformly in the neck
length.** Plumb the output end of a pair of pants with period-one `C¹` Hamiltonians `Ha` into the
input end `q` of one with period-one `C¹` Hamiltonians `Hb`, along a neck of length `L > 4`,
where `Hb q = Ha ∞`, and write the components of the plumbed perturbation
`TauCeti.Floer.plumbedPerturbation` in the global coordinate `z = s + i t` of `ℂ` as
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. If `|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, then for every
map `u` into the target the integral of `|R_K(z, u(z))|` over the plane is at most
`∑ r, Ba r + ∑ r, Bb r`. The bound does not depend on `L`. -/
theorem lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ r, ENNReal.ofReal (Ba r) + ∑ r, ENNReal.ofReal (Bb r) := by
  -- The plane is covered, up to two points, by the part `A` where the plumbed datum is the
  -- datum of the receiving pair of pants, and the image under the plumbing chart of a part `S`
  -- of the inserted pair of pants where its pullback is the datum of the inserted one.
  set A := {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ q.endCenter ∧
    (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}
  set S := {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1 ∧
    -(L / 2) < (inf.endCoord (Complex.equivRealProdCLM.symm z)).re}
  set N : Set (ℝ × ℝ) :=
    {Complex.equivRealProdCLM q.endCenter, Complex.equivRealProdCLM (q.plumbingMap L 1)}
  have hcover : univ ⊆ (A ∪ plumbingChart q L '' S) ∪ N := by
    intro z _
    by_cases h₀ : Complex.equivRealProdCLM.symm z = q.endCenter
    · exact Or.inr (by simp [N, ← h₀])
    by_cases h₁ : Complex.equivRealProdCLM.symm z = q.plumbingMap L 1
    · exact Or.inr (by simp [N, ← h₁])
    by_cases hle : (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2
    · exact Or.inl (Or.inl ⟨h₀, hle⟩)
    refine Or.inl (Or.inr ⟨Complex.equivRealProdCLM
      ((Complex.equivRealProdCLM.symm z - q.endCenter) / q.plumbingFactor L), ?_, ?_⟩)
    · refine ⟨?_, ?_, ?_⟩ <;> rw [ContinuousLinearEquiv.symm_apply_apply]
      · exact q.sub_endCenter_div_plumbingFactor_ne_zero L h₀
      · intro h
        exact h₁ (by rw [← h, plumbingMap_sub_endCenter_div])
      · rw [re_endCoord_inf_sub_endCenter_div q L h₀]
        linarith
    · rw [plumbingChart_apply, ContinuousLinearEquiv.symm_apply_apply,
        plumbingMap_sub_endCenter_div, ContinuousLinearEquiv.apply_symm_apply]
  have hN : volume N = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Set.toFinite N).measure_zero _
  calc _ = ∫⁻ z in univ, ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ := (setLIntegral_univ _).symm
    _ ≤ _ := lintegral_mono_set hcover
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ ≤ _ := lintegral_union_le _ _ _
    _ ≤ ∑ r, ENNReal.ofReal (Bb r) + ∑ r, ENNReal.ofReal (Ba r) :=
        add_le_add
          (setLIntegral_enorm_hamiltonianCurvature_plumbedPerturbation_le_receiving ω hq hHb hHbs
            hab hL hBb u)
          (setLIntegral_enorm_hamiltonianCurvature_plumbedPerturbation_le_inserted ω hq hHa hHb
            hHas hHbs hab hL hBa u)
    _ = _ := add_comm _ _

end TauCeti.SymplecticForm
