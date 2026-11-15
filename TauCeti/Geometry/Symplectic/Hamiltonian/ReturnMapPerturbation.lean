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

This file shows that the condition can always be reached, simultaneously for finitely many
periodic orbits, by an arbitrarily small Hamiltonian perturbation localized near one point of each
orbit (`TauCeti.exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero_of_finite`). Let `p i` be
finitely many periodic points on pairwise distinct orbits and take `r > 0` such that the disc of
radius `r` about each `p i` contains no point of these orbits other than `p i` itself. There is a
smooth compactly supported Hamiltonian `H` whose time-one map `ψ`

* fixes every `p i` and every point outside the discs, so that the orbits are unchanged and so is
  `φ` near their other points;
* moves no point by more than a prescribed `ε > 0`;
* turns each `p i` into a periodic point of `φ ∘ ψ`, of the same period `k i`, whose linearized
  return map `B` satisfies `det (1 - B ^ n) ≠ 0` for every `n ≥ 1`.

Since `ψ` is the time-one map of a Hamiltonian flow it preserves the area form
(`TauCeti.SymplecticForm.apply_fderiv_hamiltonianFlow`), so `φ ∘ ψ` is area preserving whenever
`φ` is.

The Hamiltonian is a sum of radial twists `w ↦ -θ i G(‖w - p i‖²) / 2`
(`TauCeti.radialHamiltonian`) for a smooth profile `G` equal to the identity near `0` and
vanishing on `[r² / 9, ∞)` (`TauCeti.exists_contDiff_cutoff_id`). Their supports are disjoint, so
the time-one map of the sum is the rotation by the angle `θ i` near `p i` and the identity near the
other orbit points (`TauCeti.exists_hamiltonianFlow_eventuallyEq_rotation`). The linearized return
map of `φ ∘ ψ` at `p i` is therefore `A i` composed with multiplication by `exp (I * θ i)`
(`HasFDerivAt.iterate_comp_of_eventuallyEq_id`). For each orbit only countably many angles make
some power of that map degenerate
(`LinearMap.countable_setOf_exists_det_one_sub_pow_mul_lmul_exp_eq_zero`), and the angles of
different orbits can be chosen independently, as small as the displacement bound
`‖ψ w - w‖ ≤ max |θ i| sup |G'| r / 3` requires
(`TauCeti.norm_hamiltonianFlow_radialHamiltonian_sub_le_mul_sqrt`). A single orbit is the special
case `TauCeti.exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero`.

The statements concern finitely many given orbits of a map of the plane. Points of other periodic
orbits within distance `r` of some `p i` may be moved by `ψ`, and `φ ∘ ψ` may have periodic orbits
that `φ` does not have.

## Main results

* `TauCeti.exists_hamiltonianFlow_eventuallyEq_rotation`: disjoint Hamiltonian twists rotating
  finitely many points by prescribed angles.
* `TauCeti.exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero_of_finite`: localized,
  arbitrarily small Hamiltonian twists make finitely many periodic orbits nondegenerate in all
  iterates.
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

/-- **Disjoint Hamiltonian twists rotating finitely many points by prescribed angles.** Let
`p i` be finitely many points of the plane at mutual distance at least `r > 0`. There is a
constant `C` such that for all angles `θ i` some smooth compactly supported Hamiltonian `H` has
a time-one map `ψ` that agrees near each `p i` with the rotation by `θ i` about `p i`, is the
identity near every point at distance at least `r` from all the `p i`, and moves no point by more
than `C D r` when all `|θ i| ≤ D`. The Hamiltonian is a sum of radial twists supported in the
discs of radius `r / 3` about the `p i`. The conclusions hold for every Lipschitz constant of the
Hamiltonian vector field, one of which exists. -/
theorem exists_hamiltonianFlow_eventuallyEq_rotation {ι : Type*} [Finite ι] {p : ι → ℂ} {r : ℝ}
    (hr : 0 < r) (hp : Pairwise fun i j ↦ r ≤ ‖p i - p j‖) :
    ∃ C : ℝ, ∀ θ : ι → ℝ, ∃ H : ℂ → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∃ K, LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField H)) ∧
      ∀ {K : NNReal} (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField H)),
        (∀ i, stdComplexSymplecticForm.hamiltonianFlow H hX 1 =ᶠ[𝓝 (p i)]
          fun w ↦ p i + exp (I * θ i) * (w - p i)) ∧
        (∀ w, (∀ i, r ≤ ‖w - p i‖) → stdComplexSymplecticForm.hamiltonianFlow H hX 1 =ᶠ[𝓝 w] id) ∧
        ∀ D, 0 ≤ D → (∀ i, |θ i| ≤ D) →
          ∀ w, ‖stdComplexSymplecticForm.hamiltonianFlow H hX 1 w - w‖ ≤ C * D * r := by
  cases nonempty_fintype ι
  -- A smooth cutoff `G₁` of the identity, vanishing on `[r² / 9, ∞)`, with bounded derivative.
  obtain ⟨G₁, hG₁, -, hG₁R', hG₁d⟩ := exists_contDiff_cutoff_id (by positivity : 0 < r ^ 2 / 18)
    (by nlinarith : r ^ 2 / 18 < r ^ 2 / 9)
  have hG₁R (s : ℝ) (hs : r ^ 2 / 9 ≤ s) : G₁ s = 0 := hG₁R' s (hs.trans (le_abs_self s))
  have hG₁c : HasCompactSupport G₁ :=
    HasCompactSupport.intro (isCompact_closedBall 0 (r ^ 2 / 9)) fun s hs ↦
      hG₁R' s (by simpa using hs : r ^ 2 / 9 < |s|).le
  obtain ⟨C, hC⟩ := (hG₁.continuous_deriv (by simp)).bounded_above_of_compact_support hG₁c.deriv
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, fun θ ↦ ?_⟩
  -- The profile `θ i G₁` twists the disc of radius `r / 3` about `p i`, with slope `θ i` near `0`.
  let G : ι → ℝ → ℝ := fun i s ↦ θ i * G₁ s
  have hGc (i : ι) : ContDiff ℝ ∞ (G i) := contDiff_const.mul hG₁
  have hGdiff (i : ι) : Differentiable ℝ (G i) := (hGc i).differentiable (by simp)
  have hGR (i : ι) (s : ℝ) (hs : r ^ 2 / 9 ≤ s) : G i s = 0 := by simp [G, hG₁R s hs]
  have hG0 (i : ι) : ∀ᶠ s in 𝓝 0, HasDerivAt (G i) (θ i) s :=
    (eventually_abs_sub_lt 0 (by positivity : 0 < r ^ 2 / 18)).mono fun s hs ↦ by
      simpa using (hG₁d s (by simpa using hs)).const_mul (θ i)
  have hGd (i : ι) (s : ℝ) : |deriv (G i) s| ≤ |θ i| * C := by
    rw [deriv_const_mul_field', abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa using hC s) (abs_nonneg _)
  have hsep : ((Finset.univ : Finset ι) : Set ι).Pairwise
      fun i j ↦ 4 * (r ^ 2 / 9) < ‖p i - p j‖ ^ 2 :=
    fun i _ j _ hij ↦ by nlinarith [hp hij]
  have hHc : ContDiff ℝ ∞ fun w ↦ ∑ i, radialHamiltonian (G i) (p i) w :=
    ContDiff.sum fun i _ ↦ contDiff_radialHamiltonian (hGc i) (p i)
  have hHs : HasCompactSupport fun w ↦ ∑ i, radialHamiltonian (G i) (p i) w := by
    rw [← Finset.sum_fn]
    exact HasCompactSupport.finset_sum fun i _ ↦ hasCompactSupport_radialHamiltonian (hGR i) (p i)
  choose K' hXi using fun i ↦ exists_lipschitzWith_hamiltonianVectorField_radialHamiltonian
    ((hGc i).of_le (by simp)) (hGR i) (p i)
  refine ⟨_, hHc, hHs, stdComplexSymplecticForm.exists_lipschitzWith_hamiltonianVectorField
    (hHc.of_le (by simp)) hHs, fun hX ↦ ⟨fun i ↦ ?_, fun w hw ↦ ?_, fun D hD hθD w ↦ ?_⟩⟩
  · -- Near `p i` the time-one map is that of the `i`-th twist alone, a rotation by `θ i`.
    have hball : ∀ᶠ w in 𝓝 (p i), ‖w - p i‖ ^ 2 < r ^ 2 / 9 := by
      have : Continuous fun w : ℂ ↦ ‖w - p i‖ ^ 2 := by fun_prop
      exact this.continuousAt.eventually_lt continuousAt_const (by simpa using by positivity)
    filter_upwards [hball, hamiltonianFlow_radialHamiltonian_eventuallyEq (hXi i) (hG0 i) 1]
      with w hw hw'
    rw [hamiltonianFlow_sum_radialHamiltonian hX (fun j _ ↦ hGR j) hsep (Finset.mem_univ i)
      (hXi i) (hGdiff i _) hw.le, hw', one_mul]
  · -- Away from the discs the time-one map is the identity.
    exact hamiltonianFlow_sum_radialHamiltonian_eventuallyEq_id hX (fun j _ ↦ hGR j)
      (fun j _ ↦ by nlinarith [hw j]) 1
  · -- Points of the disc about `p i` turn through an angle at most `|θ i| C`.
    by_cases h : ∃ i, ‖w - p i‖ ^ 2 ≤ r ^ 2 / 9
    · obtain ⟨i, hi⟩ := h
      rw [hamiltonianFlow_sum_radialHamiltonian hX (fun j _ ↦ hGR j) hsep (Finset.mem_univ i)
        (hXi i) (hGdiff i _) hi]
      calc _ ≤ |1| * (|θ i| * C) * Real.sqrt (r ^ 2 / 9) :=
            norm_hamiltonianFlow_radialHamiltonian_sub_le_mul_sqrt (hXi i) (hGdiff i) (hGd i)
              (hGR i) w 1
        _ ≤ C * D * r := by
          rw [abs_one, one_mul, show r ^ 2 / 9 = (r / 3) ^ 2 by ring,
            Real.sqrt_sq (by positivity)]
          have h₁ : |θ i| * C ≤ D * C := mul_le_mul_of_nonneg_right (hθD i) hC0
          nlinarith [mul_le_mul_of_nonneg_right h₁ (by positivity : 0 ≤ r / 3), mul_nonneg hD hC0]
    · simp only [not_exists, not_le] at h
      rw [hamiltonianFlow_sum_radialHamiltonian_eq_self hX (fun j _ ↦ hGR j) (fun j _ ↦ h j),
        sub_self, norm_zero]
      exact mul_nonneg (mul_nonneg hC0 hD) hr.le

/-- **Localized Hamiltonian twists make finitely many periodic orbits nondegenerate in all
iterates.** Let `p i` be finitely many periodic points on pairwise distinct orbits, of periods
`k i > 0`, of a map `φ` of the plane, continuous along their orbits, whose linearized return maps
`A i` have determinant one. Let `r > 0` be at most the distance from each `p i` to every other
point of its own orbit and to every point of the other orbits. For every `ε > 0` there is a smooth
compactly supported Hamiltonian `H` whose time-one map `ψ` fixes every `p i` and every point at
distance at least `r` from all the `p i`, moves no point by more than `ε`, and makes each `p i` a
periodic point of `φ ∘ ψ` of period `k i` whose linearized return map `B` has
`det (1 - B ^ n) ≠ 0` for every `n ≠ 0`. The conclusions hold for every Lipschitz constant of the
Hamiltonian vector field, one of which exists.

Since `ψ` is the identity near the points of the orbits other than the `p i`, the orbits of `φ`
are orbits of `φ ∘ ψ`. Points of other periodic orbits of `φ` within `r` of some `p i` may be
moved. -/
theorem exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero_of_finite {ι : Type*} [Finite ι]
    {φ : ℂ → ℂ} {p : ι → ℂ} {k : ι → ℕ} {A : ι → ℂ →L[ℝ] ℂ} (hk : ∀ i, 0 < k i)
    (hp : ∀ i, φ^[k i] (p i) = p i) (hA : ∀ i, HasFDerivAt φ^[k i] (A i) (p i))
    (hdet : ∀ i, (A i).det = 1) (hφ : ∀ i, ∀ j < k i, ContinuousAt φ (φ^[j] (p i))) {r : ℝ}
    (hr : 0 < r) (horb : ∀ i i' j, j < k i' → (0 < j ∨ i' ≠ i) → r ≤ ‖φ^[j] (p i') - p i‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℂ → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∃ K, LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField H)) ∧
      ∀ {K : NNReal} (hX : LipschitzWith K (stdComplexSymplecticForm.hamiltonianVectorField H)),
        (∀ i, stdComplexSymplecticForm.hamiltonianFlow H hX 1 (p i) = p i) ∧
        (∀ w, (∀ i, r ≤ ‖w - p i‖) → stdComplexSymplecticForm.hamiltonianFlow H hX 1 w = w) ∧
        (∀ w, ‖stdComplexSymplecticForm.hamiltonianFlow H hX 1 w - w‖ ≤ ε) ∧
        ∀ i, (φ ∘ stdComplexSymplecticForm.hamiltonianFlow H hX 1)^[k i] (p i) = p i ∧
          ∃ B : ℂ →L[ℝ] ℂ, HasFDerivAt (φ ∘ stdComplexSymplecticForm.hamiltonianFlow H hX 1)^[k i]
            B (p i) ∧ ∀ n ≠ 0, (1 - B ^ n).det ≠ 0 := by
  obtain ⟨C, hC⟩ := exists_hamiltonianFlow_eventuallyEq_rotation hr fun i j hij ↦ by
    simpa using horb j i 0 (hk i) (Or.inr hij)
  -- Choose for each orbit a small angle outside the countable set of degenerate angles.
  choose θ hθ hθ0 hθε using fun i ↦
    ((LinearMap.countable_setOf_exists_det_one_sub_pow_mul_lmul_exp_eq_zero (hdet i)).dense_compl
      ℝ).exists_between (show (0 : ℝ) < ε / ((|C| + 1) * r) by positivity)
  obtain ⟨H, hHc, hHs, hHX, hψ⟩ := hC θ
  refine ⟨H, hHc, hHs, hHX, fun hX ↦ ?_⟩
  obtain ⟨hrot, hid, hdisp⟩ := hψ hX
  set ψ := stdComplexSymplecticForm.hamiltonianFlow H hX 1
  have hψp (i : ι) : ψ (p i) = p i := by simpa using (hrot i).eq_of_nhds
  have hψ' (i : ι) : HasFDerivAt ψ (exp (I * θ i) • ContinuousLinearMap.id ℝ ℂ) (p i) :=
    ((((hasFDerivAt_id (𝕜 := ℝ) (p i)).sub_const (p i)).const_mul
      (exp (I * θ i))).const_add (p i)).congr_of_eventuallyEq (hrot i)
  -- `ψ` is the identity near the points of the orbits other than the `p i`.
  have hidorb (i : ι) (j : ℕ) (hj : 0 < j) (hjk : j < k i) : ψ =ᶠ[𝓝 (φ^[j] (p i))] id :=
    hid _ fun l ↦ horb l i j hjk (Or.inl hj)
  refine ⟨hψp, fun w hw ↦ (hid w hw).eq_of_nhds, fun w ↦ (hdisp _ (by positivity)
    (fun i ↦ (abs_of_pos (hθ0 i)).trans_le (hθε i).le) w).trans ?_, fun i ↦ ⟨?_, _,
    (hA i).iterate_comp_of_eventuallyEq_id (hψ' i) (hk i) (hψp i) (hφ i) (hidorb i),
    fun n hn h ↦ hθ i ⟨n, hn, ?_⟩⟩⟩
  · -- The angles are small enough for the displacement bound.
    calc C * (ε / ((|C| + 1) * r)) * r = C / (|C| + 1) * ε := by field_simp
      _ ≤ 1 * ε := by
        gcongr
        rw [div_le_one (by positivity)]
        linarith [le_abs_self C]
      _ = ε := one_mul ε
  · rw [(Function.iterate_comp_eventuallyEq_of_eventuallyEq_id (hk i) (hψp i)
      (hψ' i).continuousAt (hφ i) (hidorb i)).eq_of_nhds, Function.comp_apply, hψp, hp]
  · -- The return map `A i ∘ exp (I * θ i)` is nondegenerate in all iterates by the choice of `θ i`.
    have hcoe : ((A i).comp (exp (I * θ i) • ContinuousLinearMap.id ℝ ℂ) : ℂ →ₗ[ℝ] ℂ) =
        (A i : ℂ →ₗ[ℝ] ℂ) * Algebra.lmul ℝ ℂ (exp (θ i * I)) := by
      ext v
      simp [mul_comm]
    rw [← hcoe]
    convert h using 2
    simp

/-- **A localized Hamiltonian twist makes a periodic orbit nondegenerate in all iterates.** Let
`p` be a periodic point of period `k > 0` of a map `φ` of the plane, continuous along the orbit,
whose linearized return map `A` has determinant one, and let `r > 0` be at most the distance from
`p` to the other points of its orbit. For every `ε > 0` there is a smooth compactly supported
Hamiltonian `H` whose time-one map `ψ` fixes `p` and every point at distance at least `r` from `p`,
moves no point by more than `ε`, and makes `p` a periodic point of `φ ∘ ψ` of period `k` whose
linearized return map `B` has `det (1 - B ^ n) ≠ 0` for every `n ≠ 0`. The conclusions hold for
every Lipschitz constant of the Hamiltonian vector field, one of which exists. This is the case of
a single orbit in `TauCeti.exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero_of_finite`. -/
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
  obtain ⟨H, hHc, hHs, hHX, hψ⟩ := exists_hamiltonianFlow_forall_det_one_sub_pow_ne_zero_of_finite
    (ι := Unit) (p := fun _ ↦ p) (k := fun _ ↦ k) (A := fun _ ↦ A) (fun _ ↦ hk) (fun _ ↦ hp)
    (fun _ ↦ hA) (fun _ ↦ hdet) (fun _ ↦ hφ) hr
    (fun _ _ j hjk h ↦ horb j (h.resolve_right (by simp)) hjk) hε
  refine ⟨H, hHc, hHs, hHX, fun hX ↦ ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hψ hX
  exact ⟨h₁ (), fun w hw ↦ h₂ w fun _ ↦ hw, h₃, h₄ ()⟩

end TauCeti
