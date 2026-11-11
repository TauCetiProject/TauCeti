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
# Making periodic orbits nondegenerate by Hamiltonian twists

Let `φ` be a map of the plane `ℂ` and `p` a periodic point of period `k`, whose linearized return
map `A`, the derivative of `φ^[k]` at `p`, has determinant one, as for an area-preserving map. The
orbit is *nondegenerate in all iterates* when no positive power of `A` has eigenvalue `1`, that
is, `det (1 - A ^ n) ≠ 0` for every `n ≥ 1`. This is the condition under which the periodic
orbits of an area-preserving surface map give the orbit tori, with their four-twist labels, in
Taubes's count of pseudoholomorphic curves in the product of a circle with the mapping torus.

This file shows that the condition can always be reached, for finitely many periodic orbits at
once, by an arbitrarily small Hamiltonian perturbation localized near one point of each orbit
(`TauCeti.exists_hamiltonianFlow_forall_forall_det_one_sub_pow_ne_zero`). Let `p i`, for `i` in a
finite type, be periodic points on distinct orbits, and let `r > 0` be at most the distance from
each `p i` to every other point of the union of these orbits. There is a smooth compactly supported
Hamiltonian `H` whose time-one map `ψ`

* is the identity near every point at distance at least `r / 2` from all the `p i`, so that the
  orbits of the `p i` are unchanged, and so is every orbit of `φ` that stays at that distance from
  the `p i`, together with its linearized return map
  (`HasFDerivAt.iterate_comp_of_forall_eventuallyEq_id`);
* moves no point by more than a prescribed `ε > 0`;
* turns each `p i` into a periodic point of `φ ∘ ψ`, of the same period, whose linearized return
  map `B` satisfies `det (1 - B ^ n) ≠ 0` for every `n ≥ 1`.

Since `ψ` is the time-one map of a Hamiltonian flow it preserves the area form
(`TauCeti.SymplecticForm.apply_fderiv_hamiltonianFlow`), so `φ ∘ ψ` is area preserving whenever
`φ` is. The case of a single orbit is
`TauCeti.exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero`.

The Hamiltonian is a sum of radial twists `w ↦ -θᵢ G(‖w - p i‖²) / 2`
(`TauCeti.radialHamiltonian`) for a smooth profile `G` equal to the identity near `0` and
vanishing on `[r² / 9, ∞)` (`TauCeti.exists_contDiff_cutoff_id`). The discs of radius `r / 2`
about the `p i` are disjoint, and on each of them `H` agrees with a single twist, so the flow of
`H` is that of the twist there (`TauCeti.hamiltonianFlow_sum_radialHamiltonian`), while away from
them it is the identity (`TauCeti.hamiltonianFlow_sum_radialHamiltonian_eventuallyEq_id`).
The time-one map is therefore the rotation by the angle `θᵢ` near `p i` and the identity near the
other orbit points, so the linearized return map of `φ ∘ ψ` at `p i` is `A i` composed with
multiplication by `exp (θᵢ √-1)` (`HasFDerivAt.iterate_comp_of_eventuallyEq_id`). Only countably
many angles make some power of that map degenerate
(`LinearMap.countable_setOf_exists_det_one_sub_pow_mul_lmul_exp_eq_zero`), so each `θᵢ` can be
chosen as small as the displacement bound `‖ψ w - w‖ ≤ |θᵢ| sup |G'| r / 2` requires.

The perturbation concerns the chosen orbits of a map of the plane. Periodic orbits of `φ ∘ ψ`
passing through the discs of radius `r / 2` about the `p i`, other than the chosen ones, are not
controlled.

## Main results

* `TauCeti.exists_hamiltonianFlow_forall_forall_det_one_sub_pow_ne_zero`: localized, arbitrarily
  small Hamiltonian twists make finitely many periodic orbits nondegenerate in all iterates at
  once.
* `TauCeti.exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero`: the case of one orbit.

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

/-- **A twist profile for one return map.** For a return map `A` of determinant one, a radius
`r > 0` and a tolerance `ε > 0`, there is a smooth profile `G` vanishing on `[r² / 9, ∞)`, with
`G' = θ` near `0` and `|G'| r ≤ ε`, such that `A` followed by the rotation by `θ` is nondegenerate
in all iterates. -/
private theorem exists_twist_profile {A : ℂ →L[ℝ] ℂ} (hdet : A.det = 1) {r : ℝ} (hr : 0 < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (G : ℝ → ℝ) (θ : ℝ), ContDiff ℝ ∞ G ∧ (∀ s, r ^ 2 / 9 ≤ s → G s = 0) ∧
      (∀ᶠ s in 𝓝 0, HasDerivAt G θ s) ∧ (∀ s, |deriv G s| * r ≤ ε) ∧
      ∀ n ≠ 0, (1 - (A.comp (exp (I * ↑(1 * θ)) • ContinuousLinearMap.id ℝ ℂ)) ^ n).det ≠ 0 := by
  -- A smooth cutoff `G₁` of the identity, vanishing on `[r² / 9, ∞)`, with bounded derivative.
  obtain ⟨G₁, hG₁, -, hG₁R, hG₁d⟩ := exists_contDiff_cutoff_id (by positivity : 0 < r ^ 2 / 18)
    (by nlinarith : r ^ 2 / 18 < r ^ 2 / 9)
  have hG₁c : HasCompactSupport G₁ :=
    HasCompactSupport.intro (isCompact_closedBall 0 (r ^ 2 / 9)) fun s hs ↦
      hG₁R s (by simpa using hs : r ^ 2 / 9 < |s|).le
  obtain ⟨C, hC⟩ := (hG₁.continuous_deriv (by simp)).bounded_above_of_compact_support hG₁c.deriv
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- Choose a small angle `θ` outside the countable set of degenerate angles.
  obtain ⟨θ, hθ, hθ0, hθε⟩ :=
    ((LinearMap.countable_setOf_exists_det_one_sub_pow_mul_lmul_exp_eq_zero hdet).dense_compl
      ℝ).exists_between (show (0 : ℝ) < ε / ((C + 1) * r) by positivity)
  refine ⟨fun s ↦ θ * G₁ s, θ, contDiff_const.mul hG₁, fun s hs ↦ ?_, ?_, fun s ↦ ?_,
    fun n hn h ↦ hθ ⟨n, hn, ?_⟩⟩
  · simp [hG₁R s (hs.trans (le_abs_self s))]
  · filter_upwards [eventually_abs_sub_lt 0 (by positivity : 0 < r ^ 2 / 18)] with s hs
    simpa using (hG₁d s (by simpa using hs)).const_mul θ
  · rw [deriv_const_mul_field', abs_mul, abs_of_pos hθ0]
    rw [lt_div_iff₀ (by positivity)] at hθε
    nlinarith [hC s, norm_nonneg (deriv G₁ s), Real.norm_eq_abs (deriv G₁ s)]
  · -- The return map `A ∘ exp (θ i)` is nondegenerate in all iterates by the choice of `θ`.
    have hcoe : ((A.comp (exp (I * ↑(1 * θ)) • ContinuousLinearMap.id ℝ ℂ) : ℂ →L[ℝ] ℂ) :
        ℂ →ₗ[ℝ] ℂ) = (A : ℂ →ₗ[ℝ] ℂ) * Algebra.lmul ℝ ℂ (exp (θ * I)) := by
      ext v
      simp [mul_comm]
    rw [← hcoe]
    convert h using 2
    simp

/-- **Localized Hamiltonian twists make finitely many periodic orbits nondegenerate at once.**
Let `p i`, for `i` in a finite type, be periodic points of periods `k i > 0` of a map `φ` of the
plane, continuous along their orbits, whose linearized return maps `A i` have determinant one.
Suppose that every point of these orbits other than `p i` itself is at distance at least `r > 0`
from `p i`; in particular the orbits are distinct. For every `ε > 0` there is a smooth compactly
supported Hamiltonian `H` whose time-one map `ψ`

* is the identity near every point at distance at least `r / 2` from all the `p i`, so that
  every orbit of `φ` staying at that distance keeps its iterates, in particular its period and its
  linearized return map, under `φ ∘ ψ`
  (`Function.iterate_comp_eventuallyEq_of_forall_eventuallyEq_id`);
* moves no point by more than `ε`;
* fixes each `p i` and makes it a periodic point of `φ ∘ ψ` of period `k i` whose linearized return
  map `B` has `det (1 - B ^ n) ≠ 0` for every `n ≠ 0`.

The conclusions hold for every Lipschitz constant of the Hamiltonian vector field, one of which
exists. -/
theorem exists_hamiltonianFlow_forall_forall_det_one_sub_pow_ne_zero {ι : Type*} [Finite ι]
    {φ : ℂ → ℂ} {p : ι → ℂ} {k : ι → ℕ} {A : ι → ℂ →L[ℝ] ℂ} (hk : ∀ i, 0 < k i)
    (hp : ∀ i, φ^[k i] (p i) = p i) (hA : ∀ i, HasFDerivAt φ^[k i] (A i) (p i))
    (hdet : ∀ i, (A i).det = 1) (hφ : ∀ i, ∀ j < k i, ContinuousAt φ (φ^[j] (p i))) {r : ℝ}
    (hr : 0 < r) (horb : ∀ i j m, m < k j → (j, m) ≠ (i, 0) → r ≤ ‖φ^[m] (p j) - p i‖) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ H : ℂ → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∃ K, LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField H)) ∧
      ∀ {K : NNReal} (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField H)),
        (∀ w, (∀ i, r / 2 ≤ ‖w - p i‖) →
          stdComplexSymplecticForm.hamiltonianFlow H hX 1 =ᶠ[𝓝 w] id) ∧
        (∀ w, ‖stdComplexSymplecticForm.hamiltonianFlow H hX 1 w - w‖ ≤ ε) ∧
        ∀ i, stdComplexSymplecticForm.hamiltonianFlow H hX 1 (p i) = p i ∧
          (φ ∘ stdComplexSymplecticForm.hamiltonianFlow H hX 1)^[k i] (p i) = p i ∧
          ∃ B : ℂ →L[ℝ] ℂ,
            HasFDerivAt (φ ∘ stdComplexSymplecticForm.hamiltonianFlow H hX 1)^[k i] B (p i) ∧
            ∀ n ≠ 0, (1 - B ^ n).det ≠ 0 := by
  have := Fintype.ofFinite ι
  choose G θ hGc hGR hG0 hGd hθ using fun i ↦ exists_twist_profile (hdet i) hr hε
  have hdiff (i : ι) : Differentiable ℝ (G i) := (hGc i).differentiable (by simp)
  have hsep (i j : ι) (hij : j ≠ i) : r ≤ ‖p j - p i‖ := by
    simpa using horb i j 0 (hk j) (by simpa using hij)
  -- The Hamiltonian is the sum of the radial twists about the points `p i`, each supported in
  -- the disc of radius `r / 3` about its centre.
  set H : ℂ → ℝ := fun w ↦ ∑ i, radialHamiltonian (G i) (p i) w
  have hHc : ContDiff ℝ ∞ H := ContDiff.sum fun i _ ↦ contDiff_radialHamiltonian (hGc i) (p i)
  have hHs : HasCompactSupport H := by
    refine HasCompactSupport.intro (isCompact_iUnion fun i ↦ isCompact_closedBall (p i) (r / 3))
      fun w hw ↦ Finset.sum_eq_zero fun i _ ↦ ?_
    simp only [Set.mem_iUnion, Metric.mem_closedBall, dist_eq_norm, not_exists, not_le] at hw
    simp [hGR i _ (by nlinarith [hw i] : r ^ 2 / 9 ≤ ‖w - p i‖ ^ 2)]
  refine ⟨H, hHc, hHs,
    stdComplexSymplecticForm.exists_lipschitzWith_hamiltonianVectorField (hHc.of_le (by simp)) hHs,
    fun hX ↦ ?_⟩
  set ψ := stdComplexSymplecticForm.hamiltonianFlow H hX 1
  -- On the disc of radius `r / 2` about `p i`, the time-one map is the twist about `p i`, and
  -- away from these discs it is the identity.
  have htwist (i : ι) (w : ℂ) (hw : ‖w - p i‖ < r / 2) :
      ψ w = p i + exp (I * ↑(1 * deriv (G i) (‖w - p i‖ ^ 2))) * (w - p i) :=
    hamiltonianFlow_sum_radialHamiltonian hGR hX (hdiff i _) (fun j hji ↦ by
      rw [show r ^ 2 / 9 = (r / 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      linarith [hsep i j hji]) 1
  have hfix (w : ℂ) (hw : ∀ i, r / 2 ≤ ‖w - p i‖) : ψ =ᶠ[𝓝 w] id :=
    hamiltonianFlow_sum_radialHamiltonian_eventuallyEq_id hGR hX (fun i ↦ by nlinarith [hw i]) 1
  refine ⟨hfix, fun w ↦ ?_, fun i ↦ ?_⟩
  · -- Each disc turns through a small angle, and the rest of the plane is fixed.
    by_cases hw : ∃ i, ‖w - p i‖ < r / 2
    · obtain ⟨i, hi⟩ := hw
      rw [htwist i w hi, show ∀ e : ℂ, p i + e * (w - p i) - w = (e - 1) * (w - p i) by
        intro e; ring, norm_mul]
      calc _ ≤ |1 * deriv (G i) (‖w - p i‖ ^ 2)| * ‖w - p i‖ := by
            gcongr
            exact Real.norm_exp_I_mul_ofReal_sub_one_le
        _ ≤ ε := by
          rw [one_mul]
          nlinarith [hGd i (‖w - p i‖ ^ 2), abs_nonneg (deriv (G i) (‖w - p i‖ ^ 2))]
    · push Not at hw
      rw [(hfix w hw).eq_of_nhds, id, sub_self, norm_zero]
      exact hε.le
  · -- Near `p i` the time-one map is the rotation by `θ i` about `p i`.
    have hsq : Tendsto (fun w : ℂ ↦ ‖w - p i‖ ^ 2) (𝓝 (p i)) (𝓝 0) := by
      have : Continuous fun w : ℂ ↦ ‖w - p i‖ ^ 2 := by fun_prop
      simpa using this.tendsto (p i)
    have hnear : ψ =ᶠ[𝓝 (p i)] fun w ↦ p i + exp (I * ↑(1 * θ i)) * (w - p i) := by
      filter_upwards [ball_mem_nhds (p i) (by positivity : 0 < r / 2), hsq.eventually (hG0 i)]
        with w hw hw'
      rw [htwist i w (by simpa [dist_eq_norm] using hw), hw'.deriv]
    have hψp : ψ (p i) = p i := by simp [hnear.eq_of_nhds]
    have hψ' : HasFDerivAt ψ (exp (I * ↑(1 * θ i)) • ContinuousLinearMap.id ℝ ℂ) (p i) :=
      HasFDerivAt.congr_of_eventuallyEq ((((hasFDerivAt_id (𝕜 := ℝ) (p i)).sub_const
        (p i)).const_mul (exp (I * ↑(1 * θ i)))).const_add (p i)) hnear
    -- The time-one map is the identity near the other points of the orbit of `p i`.
    have hid (j : ℕ) (hj : 0 < j) (hjk : j < k i) : ψ =ᶠ[𝓝 (φ^[j] (p i))] id :=
      hfix _ fun i' ↦ by
        linarith [horb i' i j hjk (by simp [hj.ne']), (by positivity : 0 < r)]
    refine ⟨hψp, ?_, _, (hA i).iterate_comp_of_eventuallyEq_id hψ' (hk i) hψp (hφ i) hid, hθ i⟩
    rw [(Function.iterate_comp_eventuallyEq_of_eventuallyEq_id (hk i) hψp hψ'.continuousAt (hφ i)
      hid).eq_of_nhds, Function.comp_apply, hψp, hp]

/-- **A localized Hamiltonian twist makes a periodic orbit nondegenerate in all iterates.** Let
`p` be a periodic point of period `k > 0` of a map `φ` of the plane, continuous along the orbit,
whose linearized return map `A` has determinant one, and let `r > 0` be at most the distance from
`p` to the other points of its orbit. For every `ε > 0` there is a smooth compactly supported
Hamiltonian `H` whose time-one map `ψ` fixes `p` and every point at distance at least `r` from `p`,
moves no point by more than `ε`, and makes `p` a periodic point of `φ ∘ ψ` of period `k` whose
linearized return map `B` has `det (1 - B ^ n) ≠ 0` for every `n ≠ 0`. The conclusions hold for
every Lipschitz constant of the Hamiltonian vector field, one of which exists. This is the case of
a single orbit of `TauCeti.exists_hamiltonianFlow_forall_forall_det_one_sub_pow_ne_zero`. -/
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
  obtain ⟨H, hHc, hHs, hlip, h⟩ :=
    exists_hamiltonianFlow_forall_forall_det_one_sub_pow_ne_zero (ι := Unit) (fun _ ↦ hk)
      (fun _ ↦ hp) (fun _ ↦ hA) (fun _ ↦ hdet) (fun _ ↦ hφ) hr
      (fun _ _ m hm hne ↦ horb m (Nat.pos_of_ne_zero fun h ↦ hne (by rw [h])) hm) hε
  refine ⟨H, hHc, hHs, hlip, fun hX ↦ ?_⟩
  obtain ⟨hfix, hmove, hper⟩ := h hX
  obtain ⟨hψp, hpk, hB⟩ := hper ()
  exact ⟨hψp, fun w hw ↦ (hfix w fun _ ↦ by linarith).eq_of_nhds, hmove, hpk, hB⟩

end TauCeti
