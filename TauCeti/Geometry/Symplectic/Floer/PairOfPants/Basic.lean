/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.EndCoordinate
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Hamiltonian perturbation data on the pair of pants

The pair-of-pants product of Hamiltonian Floer theory counts solutions of the perturbed
Cauchy–Riemann equation `(du - X_K)^{0,1} = 0` on the thrice-punctured sphere
`S = ℂ ∖ {0, 1}`, with positive (input) cylindrical ends at `0` and `1` and a negative (output)
cylindrical end at `∞`. The perturbation is a one-form `K` on `S` with values in smooth functions
on the target manifold `M`, which must equal `H_q(t) dt` in the end coordinates `(s, t)` of each
end `q` far out on the end, where `H_q` is the period-one Hamiltonian attached to that end.

This file constructs such a perturbation from any three smooth period-one Hamiltonians,
`TauCeti.Floer.pairOfPantsPerturbation`: on the end `q` it is `β(±s) H_q(t) dt` for a smooth
cutoff `β` vanishing for `±s ≤ 1` and equal to `1` for `±s ≥ 2`, and it vanishes off the three
ends. Its value at `w` is a real covector on `ℂ`, so the `ds` and `dt` components of its pullback
along an end lift `φ` are its values on `φ'(z)` and `φ'(z) i`. The results are:

* `TauCeti.Floer.contMDiffAt_pairOfPantsPerturbation`: the perturbation is smooth on `S × M`.
* `TauCeti.Floer.pairOfPantsPerturbation_cylindricalEndLift_of_pos`: on the part `±s > 0` of the
  end `q` its pullback is the continuation datum `β(±s - 1) H_q(t) dt`.
* `TauCeti.Floer.pairOfPantsPerturbation_cylindricalEndLift`: on the part `±s ≥ 2` of the end `q`
  its pullback is `H_q(t) dt`, that is `K_s = 0` and `K_t = H_q(t)`.
* `TauCeti.Floer.pairOfPantsEndComponent H q v`: the component of the pullback along the tangent
  vector `v` of the cylinder, in the end coordinates of the end `q`, so that `K_s` and `K_t` are
  its components along `v = 1` and `v = i`; `TauCeti.Floer.pairOfPantsEndComponent_of_pos`
  computes them on the part `±s > 0` of the end.
* `TauCeti.Floer.exists_cylindricalEndLift_of_pairOfPantsPerturbation_ne_zero`: it is supported
  in the parts `±s > 1` of the three ends, so it vanishes off the ends.

The angular coordinate `t` of an end is defined only modulo `1`, which is why the Hamiltonians are
required to have period one: smoothness across the ray where the angular coordinate jumps is
`TauCeti.ThricePuncturedSphere.Puncture.contMDiffAt_comp_im_endCoord`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on perturbation data for the pair-of-pants product.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), on
  perturbation one-forms on punctured surfaces that agree with `H dt` on the ends.
-/

public noncomputable section

open Set Real Manifold Topology
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*}

/-- The Hamiltonian perturbation one-form on the pair of pants given by period-one Hamiltonians
`H q` on its three ends. At `w ∈ ℂ` and `x ∈ M` it is the covector
`∑ q, β(±s_q(w)) H_q(t_q(w), x) dt_q`, where `(s_q, t_q)` are the coordinates of the end `q`,
the sign is that of the end, and `β` is the smooth transition from `0` on `(-∞, 1]` to `1` on
`[2, ∞)`. -/
def pairOfPantsPerturbation (H : Puncture → ℝ → M → ℝ) (w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  ∑ q, (smoothTransition (q.endSign * (q.endCoord w).re - 1) * H q (q.endCoord w).im x) •
    q.endAngularForm w

/-- The defining equation of the perturbation: the cutoff-weighted sum over the three ends of
`H_q(t_q(w), x) dt_q`. -/
theorem pairOfPantsPerturbation_def (H : Puncture → ℝ → M → ℝ) (w : ℂ) (x : M) :
    pairOfPantsPerturbation H w x =
      ∑ q, (smoothTransition (q.endSign * (q.endCoord w).re - 1) * H q (q.endCoord w).im x) •
        q.endAngularForm w := by
  rw [pairOfPantsPerturbation]

variable {H : Puncture → ℝ → M → ℝ}

/-- Where the cutoff of the end `q` is nonzero, the point lies on the part `±s > 1` of that end,
and in particular it is not the center of the end. -/
private theorem one_lt_endSign_mul_re_endCoord {q : Puncture} {w : ℂ}
    (h : smoothTransition (q.endSign * (q.endCoord w).re - 1) ≠ 0) :
    1 < q.endSign * (q.endCoord w).re ∧ w ≠ q.endCenter := by
  have h₁ : 1 < q.endSign * (q.endCoord w).re := by
    by_contra! h'
    exact h (smoothTransition.zero_of_nonpos (by linarith))
  refine ⟨h₁, fun hw => ?_⟩
  rw [hw, re_endCoord] at h₁
  norm_num at h₁

/-- The perturbation is supported in the parts `±s > 1` of the three ends. -/
theorem exists_cylindricalEndLift_of_pairOfPantsPerturbation_ne_zero {w : ℂ} {x : M}
    (h : pairOfPantsPerturbation H w x ≠ 0) :
    ∃ (q : Puncture) (z : ℂ), 1 < q.endSign * z.re ∧ q.cylindricalEndLift z = w := by
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hc : smoothTransition (q.endSign * (q.endCoord w).re - 1) ≠ 0 :=
    fun hc => hq (by simp [hc])
  obtain ⟨h₁, hw⟩ := one_lt_endSign_mul_re_endCoord hc
  exact ⟨q, q.endCoord w, h₁, q.cylindricalEndLift_endCoord hw⟩

/-- **The perturbation on an end.** On the part `±s > 0` of the end `q`, the pullback of the
perturbation along the end lift `φ` is the continuation datum `β(±s - 1) H_q(t) dt`: it sends a
tangent vector `v` of the cylinder to `Im v · β(±s - 1) H_q(t)`. -/
theorem pairOfPantsPerturbation_cylindricalEndLift_of_pos {q : Puncture}
    (hH : Function.Periodic (H q) 1) {z : ℂ} (hz : 0 < q.endSign * z.re) (x : M) (v : ℂ) :
    pairOfPantsPerturbation H (q.cylindricalEndLift z) x (deriv q.cylindricalEndLift z * v) =
      v.im * (smoothTransition (q.endSign * z.re - 1) * H q z.im x) := by
  rw [pairOfPantsPerturbation, Finset.sum_eq_single q]
  · obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift z
    have hre : (q.endCoord (q.cylindricalEndLift z)).re = z.re := by simp [hk]
    have him : (q.endCoord (q.cylindricalEndLift z)).im = z.im + k := by simp [hk]
    have hp : H q (z.im + k) x = H q z.im x := by
      simpa using congrFun (hH.int_mul k z.im) x
    rw [smul_apply, endAngularForm_cylindricalEndLift, hre, him, hp, smul_eq_mul, mul_comm]
  · -- The cutoffs of the other ends vanish, since distinct ends are disjoint.
    intro r _ hr
    have hc : smoothTransition (r.endSign * (r.endCoord (q.cylindricalEndLift z)).re - 1) = 0 := by
      by_contra hc
      obtain ⟨h₁, hw⟩ := one_lt_endSign_mul_re_endCoord hc
      exact cylindricalEndLift_ne_cylindricalEndLift (z := z) (z' := r.endCoord _) hr.symm
        hz (by linarith) (r.cylindricalEndLift_endCoord hw).symm
    simp [hc]
  · simp

/-- **The perturbation is `H_q(t) dt` far out on each end.** On the part `±s ≥ 2` of the end `q`,
the pullback of the perturbation along the end lift `φ` sends a tangent vector `v` of the
cylinder to `Im v · H_q(t)`: its `ds` component (`v = 1`) vanishes and its `dt` component
(`v = i`) is `H_q(t)`. -/
theorem pairOfPantsPerturbation_cylindricalEndLift {q : Puncture}
    (hH : Function.Periodic (H q) 1) {z : ℂ} (hz : 2 ≤ q.endSign * z.re) (x : M) (v : ℂ) :
    pairOfPantsPerturbation H (q.cylindricalEndLift z) x (deriv q.cylindricalEndLift z * v) =
      v.im * H q z.im x := by
  rw [pairOfPantsPerturbation_cylindricalEndLift_of_pos hH (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

variable {q : Puncture}

/-- The component of the pair-of-pants perturbation along the tangent vector `v` of the cylinder,
in the end coordinates `z = (s, t)` of the end `q`: the pullback of the perturbation along the end
lift `φ`, evaluated at the point `s + i t` on `v`. The components `K_s` and `K_t` of the pulled-back
datum `K_s ds + K_t dt` are those along `v = 1` and `v = i`. -/
def pairOfPantsEndComponent (H : Puncture → ℝ → M → ℝ) (q : Puncture) (v : ℂ) (z : ℝ × ℝ)
    (x : M) : ℝ :=
  pairOfPantsPerturbation H (q.cylindricalEndLift ⟨z.1, z.2⟩) x
    (deriv q.cylindricalEndLift ⟨z.1, z.2⟩ * v)

theorem pairOfPantsEndComponent_def (H : Puncture → ℝ → M → ℝ) (q : Puncture) (v : ℂ)
    (z : ℝ × ℝ) (x : M) :
    pairOfPantsEndComponent H q v z x =
      pairOfPantsPerturbation H (q.cylindricalEndLift ⟨z.1, z.2⟩) x
        (deriv q.cylindricalEndLift ⟨z.1, z.2⟩ * v) :=
  (rfl)

/-- On the part `±s > 0` of the end `q`, the component of the perturbation along `v` is
`Im v · β(±s - 1) H_q(t)`. -/
theorem pairOfPantsEndComponent_of_pos (hH : Function.Periodic (H q) 1) {z : ℝ × ℝ}
    (hz : 0 < q.endSign * z.1) (v : ℂ) (x : M) :
    pairOfPantsEndComponent H q v z x =
      v.im * (smoothTransition (q.endSign * z.1 - 1) * H q z.2 x) :=
  pairOfPantsPerturbation_cylindricalEndLift_of_pos hH hz x v

/-- On the part `±s > 0` of the end `q`, the `ds` component of the perturbation vanishes. -/
theorem pairOfPantsEndComponent_one_of_pos (hH : Function.Periodic (H q) 1) {z : ℝ × ℝ}
    (hz : 0 < q.endSign * z.1) (x : M) : pairOfPantsEndComponent H q 1 z x = 0 := by
  simp [pairOfPantsEndComponent_of_pos hH hz]

/-- On the part `±s > 0` of the end `q`, the `dt` component of the perturbation is
`β(±s - 1) H_q(t)`. -/
theorem pairOfPantsEndComponent_I_of_pos (hH : Function.Periodic (H q) 1) {z : ℝ × ℝ}
    (hz : 0 < q.endSign * z.1) (x : M) :
    pairOfPantsEndComponent H q Complex.I z x =
      smoothTransition (q.endSign * z.1 - 1) * H q z.2 x := by
  simp [pairOfPantsEndComponent_of_pos hH hz]

/-- The part `±s > 0` of the end `q`, in end coordinates, is open. -/
private theorem isOpen_endSign_mul_fst_pos (q : Puncture) :
    IsOpen {z : ℝ × ℝ | 0 < q.endSign * z.1} :=
  isOpen_lt continuous_const (continuous_const.mul continuous_fst)

/-- Near a point of the part `±s > 0` of the end `q`, the components of the perturbation are those
of the continuation datum `β(±s - 1) H_q(t) dt`. -/
theorem eventuallyEq_pairOfPantsEndComponent (hH : Function.Periodic (H q) 1) {z : ℝ × ℝ}
    (hz : 0 < q.endSign * z.1) :
    pairOfPantsEndComponent H q 1 =ᶠ[𝓝 z] (fun _ _ ↦ 0) ∧
      pairOfPantsEndComponent H q Complex.I =ᶠ[𝓝 z]
        fun w x ↦ smoothTransition (q.endSign * w.1 - 1) * H q w.2 x := by
  have h := (isOpen_endSign_mul_fst_pos q).mem_nhds hz
  refine ⟨?_, ?_⟩ <;> filter_upwards [h] with w hw <;> funext x
  exacts [pairOfPantsEndComponent_one_of_pos hH hw x, pairOfPantsEndComponent_I_of_pos hH hw x]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The perturbation is smooth.** For Hamiltonians of period one which are `C^n` on `ℝ × M`,
the perturbation is `C^n` on `S × M`, where `S = ℂ ∖ {0, 1}` is the thrice-punctured sphere. -/
theorem contMDiffAt_pairOfPantsPerturbation {n : ℕ∞} (hH : ∀ q, Function.Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (Function.uncurry (H q)))
    (w : ThricePuncturedSphere) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => pairOfPantsPerturbation H p.1 p.2) ((w : ℂ), x) := by
  simp only [pairOfPantsPerturbation]
  refine contMDiffAt_finsetSum fun q _ => ?_
  have hw : (w : ℂ) ≠ q.endCenter := by
    rcases q.endCenter_eq_zero_or_eq_one with h | h <;> rw [h]
    exacts [w.2.1, w.2.2]
  have hc : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℝ) n
      (fun p : ℂ × M => smoothTransition (q.endSign * (q.endCoord p.1).re - 1)) ((w : ℂ), x) :=
    (smoothTransition.contDiff.contDiffAt.comp (w : ℂ)
      ((contDiffAt_const.mul (q.contDiffAt_re_endCoord hw)).sub contDiffAt_const)).contMDiffAt.comp
      ((w : ℂ), x) contMDiffAt_fst
  have hf : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => q.endAngularForm p.1) ((w : ℂ), x) :=
    ContMDiffAt.comp (I' := 𝓘(ℝ, ℂ)) (g := q.endAngularForm) _
      (q.contDiffAt_endAngularForm hw).contMDiffAt contMDiffAt_fst
  exact (hc.smul (q.contMDiffAt_comp_im_endCoord (hH q) (hHs q) hw x)).smul hf

end TauCeti.Floer
