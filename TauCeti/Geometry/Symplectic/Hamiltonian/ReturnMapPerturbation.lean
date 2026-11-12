/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.RadialTwist
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo.Nondegenerate
import TauCeti.Dynamics.PeriodicPts.LocalPerturbation

/-!
# Making a periodic orbit nondegenerate by a Hamiltonian twist

Let `φ` be a map of the plane `ℂ` and `p` a periodic point of period `k`, whose linearized return
map `A`, the derivative of `φ^[k]` at `p`, has determinant one, as for an area-preserving map. The
orbit is *nondegenerate in all iterates* when no positive power of `A` has eigenvalue `1`, that
is, `det (1 - A ^ n) ≠ 0` for every `n ≥ 1`. This is the condition under which the periodic
orbits of an area-preserving surface map give the orbit tori, with their four-twist labels, in
Taubes's count of pseudoholomorphic curves in the product of a circle with the mapping torus.

This file shows that the condition can always be reached by an arbitrarily small Hamiltonian
perturbation localized near `p` (`TauCeti.exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero`).
Take a disc of radius `r` about `p` that contains no other point of the orbit. There is a smooth
compactly supported Hamiltonian `H` whose time-one map `ψ`

* fixes `p` and every point outside the disc, so that the orbit of `p` is unchanged and so is `φ`
  near its other points;
* moves no point by more than a prescribed `ε > 0`;
* turns `p` into a periodic point of `φ ∘ ψ`, of the same period `k`, whose linearized return map
  `B` satisfies `det (1 - B ^ n) ≠ 0` for every `n ≥ 1`.

Since `ψ` is the time-one map of a Hamiltonian flow it preserves the area form
(`TauCeti.SymplecticForm.apply_fderiv_hamiltonianFlow`), so `φ ∘ ψ` is area preserving whenever
`φ` is.

The Hamiltonian is a radial twist `w ↦ -θ G(‖w - p‖²) / 2` (`TauCeti.radialHamiltonian`) for a
smooth profile `G` equal to the identity near `0` and vanishing on `[r² / 4, ∞)`
(`TauCeti.exists_contDiff_cutoff_id`). Its time-one map is the rotation by the angle `θ` near `p`
(`TauCeti.hasFDerivAt_hamiltonianFlow_radialHamiltonian_center`) and the identity near the other
orbit points, so the linearized return map of `φ ∘ ψ` is `A` composed with multiplication by
`exp (θ i)` (`HasFDerivAt.iterate_comp_of_eventuallyEq_id`). Only countably many angles make some
power of that map degenerate
(`LinearMap.countable_setOf_exists_det_one_sub_pow_mul_lmul_exp_eq_zero`), so `θ` can be chosen
as small as the displacement bound `‖ψ w - w‖ ≤ |θ| sup |G'| r / 2` requires
(`TauCeti.norm_hamiltonianFlow_radialHamiltonian_sub_le_mul_sqrt`).

The statement concerns one orbit of a map of the plane. Other periodic orbits meeting the disc may
be changed by `ψ`.

## Main results

* `TauCeti.exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero`: a localized, arbitrarily
  small Hamiltonian twist makes a periodic orbit nondegenerate in all iterates.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, for Hamiltonian flows of the standard symplectic plane.
-/

public section

noncomputable section

namespace TauCeti

open Complex Filter Metric Topology
open scoped ContDiff

/-- **A localized Hamiltonian twist makes a periodic orbit nondegenerate in all iterates.** Let
`p` be a periodic point of period `k > 0` of a map `φ` of the plane, continuous along the orbit,
whose linearized return map `A` has determinant one, and let `r > 0` be at most the distance from
`p` to the other points of its orbit. For every `ε > 0` there is a smooth compactly supported
Hamiltonian `H` whose time-one map `ψ` fixes `p` and every point at distance at least `r` from `p`,
moves no point by more than `ε`, and makes `p` a periodic point of `φ ∘ ψ` of period `k` whose
linearized return map `B` has `det (1 - B ^ n) ≠ 0` for every `n ≠ 0`. The conclusions hold for
every Lipschitz constant of the Hamiltonian vector field, one of which exists. -/
theorem exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero {φ : ℂ → ℂ} {p : ℂ} {k : ℕ}
    {A : ℂ →L[ℝ] ℂ} (hk : 0 < k) (hp : φ^[k] p = p) (hA : HasFDerivAt φ^[k] A p)
    (hdet : A.det = 1) (hφ : ∀ j < k, ContinuousAt φ (φ^[j] p)) {r : ℝ} (hr : 0 < r)
    (horb : ∀ j, 0 < j → j < k → r ≤ ‖φ^[j] p - p‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℂ → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∃ K, LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField H)) ∧
      ∀ {K : NNReal} (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField H)),
        stdComplexSymplecticForm.hamiltonianFlow H hX 1 p = p ∧
        (∀ w, r ≤ ‖w - p‖ → stdComplexSymplecticForm.hamiltonianFlow H hX 1 w = w) ∧
        (∀ w, ‖stdComplexSymplecticForm.hamiltonianFlow H hX 1 w - w‖ ≤ ε) ∧
        (φ ∘ stdComplexSymplecticForm.hamiltonianFlow H hX 1)^[k] p = p ∧
        ∃ B : ℂ →L[ℝ] ℂ, HasFDerivAt (φ ∘ stdComplexSymplecticForm.hamiltonianFlow H hX 1)^[k]
          B p ∧ ∀ n ≠ 0, (1 - B ^ n).det ≠ 0 := by
  -- A smooth cutoff `G₁` of the identity, vanishing on `[r² / 4, ∞)`, with bounded derivative.
  obtain ⟨G₁, hG₁, -, hG₁R', hG₁d⟩ := exists_contDiff_cutoff_id (by positivity : 0 < r ^ 2 / 8)
    (by nlinarith : r ^ 2 / 8 < r ^ 2 / 4)
  have hG₁R (s : ℝ) (hs : r ^ 2 / 4 ≤ s) : G₁ s = 0 := hG₁R' s (hs.trans (le_abs_self s))
  have hG₁0 : ∀ᶠ s in 𝓝 0, HasDerivAt G₁ 1 s :=
    (eventually_abs_sub_lt 0 (by positivity : 0 < r ^ 2 / 8)).mono fun s hs ↦
      hG₁d s (by simpa using hs)
  have hG₁c : HasCompactSupport G₁ :=
    HasCompactSupport.intro (isCompact_closedBall 0 (r ^ 2 / 4)) fun s hs ↦
      hG₁R' s (by simpa using hs : r ^ 2 / 4 < |s|).le
  obtain ⟨C, hC⟩ := (hG₁.continuous_deriv (by simp)).bounded_above_of_compact_support hG₁c.deriv
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- Choose a small angle `θ` outside the countable set of degenerate angles.
  obtain ⟨θ, hθ, hθ0, hθε⟩ :=
    ((LinearMap.countable_setOf_exists_det_one_sub_pow_mul_lmul_exp_eq_zero hdet).dense_compl
      ℝ).exists_between (show (0 : ℝ) < ε / ((C + 1) * r) by positivity)
  -- The profile `θ G₁` twists the disc of radius `r / 2` about `p`, with slope `θ` near `0`.
  set G : ℝ → ℝ := fun s ↦ θ * G₁ s with hG_def
  have hGc : ContDiff ℝ ∞ G := contDiff_const.mul hG₁
  have hGR (s : ℝ) (hs : r ^ 2 / 4 ≤ s) : G s = 0 := by simp [G, hG₁R s hs]
  have hG0 : ∀ᶠ s in 𝓝 0, HasDerivAt G θ s :=
    hG₁0.mono fun s hs ↦ by simpa using hs.const_mul θ
  have hGdiff : Differentiable ℝ G := hGc.differentiable (by simp)
  have hHc : ContDiff ℝ ∞ (radialHamiltonian G p) := contDiff_radialHamiltonian hGc p
  have hHs : HasCompactSupport (radialHamiltonian G p) := hasCompactSupport_radialHamiltonian hGR p
  refine ⟨radialHamiltonian G p, hHc, hHs,
    stdComplexSymplecticForm.exists_lipschitzWith_hamiltonianVectorField (hHc.of_le (by simp)) hHs,
    fun hX ↦ ?_⟩
  set ψ := stdComplexSymplecticForm.hamiltonianFlow (radialHamiltonian G p) hX 1
  have hfix (w : ℂ) (hw : r ^ 2 / 4 < ‖w - p‖ ^ 2) : ψ w = w :=
    hamiltonianFlow_radialHamiltonian_eq_self_of_lt hX hGR hw 1
  have hψp : ψ p = p := hamiltonianFlow_radialHamiltonian_center hX (hGdiff 0) 1
  have hψ' := hasFDerivAt_hamiltonianFlow_radialHamiltonian_center hX hG0 1
  -- `ψ` is the identity near the points of the orbit other than `p`.
  have hid (j : ℕ) (hj : 0 < j) (hjk : j < k) : ψ =ᶠ[𝓝 (φ^[j] p)] id := by
    have hopen : IsOpen {w : ℂ | r ^ 2 / 4 < ‖w - p‖ ^ 2} :=
      isOpen_lt continuous_const (by fun_prop)
    have hmem : r ^ 2 / 4 < ‖φ^[j] p - p‖ ^ 2 := by nlinarith [horb j hj hjk]
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact hfix w hw
  refine ⟨hψp, fun w hw ↦ hfix w (by nlinarith), fun w ↦ ?_, ?_,
    _, hA.iterate_comp_of_eventuallyEq_id hψ' hk hψp hφ hid, fun n hn h ↦ hθ ⟨n, hn, ?_⟩⟩
  · -- The time-one map turns the disc of radius `r / 2` through an angle at most `θ C`.
    calc ‖ψ w - w‖ ≤ |1| * (θ * C) * Real.sqrt (r ^ 2 / 4) :=
          norm_hamiltonianFlow_radialHamiltonian_sub_le_mul_sqrt hX hGdiff
            (fun s ↦ by
              rw [hG_def, deriv_const_mul_field', abs_mul, abs_of_pos hθ0]
              exact mul_le_mul_of_nonneg_left (by simpa using hC s) hθ0.le) hGR w 1
      _ ≤ ε := by
        rw [abs_one, one_mul, show r ^ 2 / 4 = (r / 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
        rw [lt_div_iff₀ (by positivity)] at hθε
        nlinarith
  · rw [(Function.iterate_comp_eventuallyEq_of_eventuallyEq_id hk hψp hψ'.continuousAt hφ
      hid).eq_of_nhds, Function.comp_apply, hψp, hp]
  · -- The return map `A ∘ exp (θ i)` is nondegenerate in all iterates by the choice of `θ`.
    have hcoe : ((A.comp (exp (I * ↑(1 * θ)) • ContinuousLinearMap.id ℝ ℂ) : ℂ →L[ℝ] ℂ) :
        ℂ →ₗ[ℝ] ℂ) = (A : ℂ →ₗ[ℝ] ℂ) * Algebra.lmul ℝ ℂ (exp (θ * I)) := by
      ext v
      simp [mul_comm]
    rw [← hcoe]
    convert h using 2
    simp

end TauCeti
