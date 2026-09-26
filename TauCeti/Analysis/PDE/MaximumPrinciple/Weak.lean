/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.DirichletProblem
public import TauCeti.Analysis.Sobolev.W1p.Truncation

/-!
# Weak maximum and comparison principles

For a coercive divergence-form energy form, a weak subsolution with nonpositive boundary data
is nonpositive almost everywhere. The boundary condition is expressed by membership of the
positive part in `W^{1,2}_0(Ω)`. It is meaningful on arbitrary open domains and requires no trace
operator or regularity of the boundary. The corresponding condition on `(u - v)⁺` gives the
weak comparison principle. For nonnegative potential, a boundary bound `k ≥ 0` is expressed
by `(u - k)⁺ ∈ W^{1,2}_0(Ω)` and implies `u ≤ k` almost everywhere.

For `-div(a ∇u) + b · ∇u + c u`, uniform ellipticity, bounded measurable coefficients,
`c ≥ 0`, a Poincaré bound `P`, and drift smallness `βP < λ` suffice. On a domain contained
in a ball of radius `R`, one may take `P = 2R`. For weak Dirichlet solutions, nonpositive
forcing gives a nonpositive solution, and ordered forcing terms give ordered solutions, with a
positive quadratic lower bound.

## Main declarations

* `TauCeti.PDE.value_eq_zero_of_energyFormH1_self_nonpos`: coercivity forces a zero-boundary
  function with nonpositive energy to vanish.
* `TauCeti.PDE.value_nonpos_of_energyFormH1_nonpos`: the coercive weak maximum principle.
* `TauCeti.PDE.value_le_of_energyFormH1_nonpos`: the maximum principle with boundary bound `k ≥ 0`.
* `TauCeti.PDE.value_le_of_energyFormH1_le`: the coercive weak comparison principle.
* `TauCeti.PDE.IsWeakSolutionDirichlet.value_nonpos_of_energy_bound`: the sign of a weak solution.
* `TauCeti.PDE.IsWeakSolutionDirichlet.value_le_of_energy_bound`: comparison for ordered forcing.
* `TauCeti.PDE.UniformlyEllipticOn.value_nonpos_of_small_drift_of_poincare`: the weak maximum
  principle from a Poincaré bound.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_small_drift_of_poincare`: its constant-bound
  version.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_of_small_drift_of_poincare`: its comparison theorem.
* `TauCeti.PDE.UniformlyEllipticOn.value_nonpos_of_small_drift_of_subset_ball`: the ball corollary.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_const_of_small_drift_of_subset_ball`: the ball
  corollary with boundary bound `k ≥ 0`.
* `TauCeti.PDE.UniformlyEllipticOn.value_le_of_small_drift_of_subset_ball`: ball comparison.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}

/-- Testing the energy form against the positive part of `u` gives the energy of that positive
part. This identity holds for all coefficients, without integrability assumptions. -/
@[simp]
theorem energyFormH1_posPart_right (u : W1p mu Omega 2) :
    energyFormH1 a b c u (W1p.posPart (by norm_num) u) =
      energyFormH1 a b c (W1p.posPart (by norm_num) u) (W1p.posPart (by norm_num) u) := by
  classical
  simp only [energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_posPart (W1p.value u),
    W1p.gradient_posPart_ae (by norm_num) u] with x hv hg
  have hvalue : W1p.value (W1p.posPart (by norm_num) u) x = max (W1p.value u x) 0 := by
    rw [W1p.value_posPart]
    exact hv
  -- The indicator set is passed explicitly: `hx` is stated as an inequality, and the
  -- indicator lemmas cannot infer the set `{y | 0 < W1p.value u y}` from it alone.
  by_cases hx : 0 < W1p.value u x
  · have hjet : jetField (W1p.posPart (by norm_num) u) x = jetField u x := by
      rw [jetField_apply, hvalue, hg, max_eq_left hx.le,
        indicator_of_mem (s := {y | 0 < W1p.value u y}) hx, jetField_apply]
    rw [hjet]
  · have hjet : jetField (W1p.posPart (by norm_num) u) x = 0 := by
      rw [jetField_apply, hvalue, hg, max_eq_right (le_of_not_gt hx),
        indicator_of_notMem (s := {y | 0 < W1p.value u y}) hx]
      rfl
    rw [hjet]
    simp only [map_zero]

/-- The energy of `(u - k)⁺` is bounded by the energy obtained by testing `u` against it,
provided the potential and the truncation level `k` are nonnegative. -/
theorem energyFormH1_posPartAbove_self_le
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hc : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ c x) {k : ℝ} (hk : 0 ≤ k)
    (u : W1p mu Omega 2) :
    energyFormH1 a b c (W1p.posPartAbove (by norm_num) hk u)
        (W1p.posPartAbove (by norm_num) hk u) ≤
      energyFormH1 a b c u (W1p.posPartAbove (by norm_num) hk u) := by
  classical
  simp only [energyFormH1_def]
  apply integral_mono_ae (integrable_energyIntegrand_jetField hcoeff _ _)
    (integrable_energyIntegrand_jetField hcoeff _ _)
  filter_upwards [W1p.value_posPartAbove_ae (by norm_num) hk u,
    W1p.gradient_posPartAbove_ae (by norm_num) hk u, hc] with x hv hg hcx
  -- Above the level, the gradients agree and only the potential term decreases. As in
  -- `energyFormH1_posPart_right`, the indicator set is passed explicitly because `hx` is an
  -- inequality rather than a membership proof.
  by_cases hx : k < W1p.value u x
  · rw [indicator_of_mem (s := {y | k < W1p.value u y}) hx] at hg
    simp only [energyIntegrand_apply, jetField_apply, hv, hg,
      max_eq_left (sub_nonneg.mpr hx.le), massForm_apply]
    exact add_le_add_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sub_le_self _ hk) hcx)
        (sub_nonneg.mpr hx.le)) _
  · have hjet : jetField (W1p.posPartAbove (by norm_num) hk u) x = 0 := by
      rw [jetField_apply, hv, hg, max_eq_right (sub_nonpos.mpr (le_of_not_gt hx)),
        indicator_of_notMem (s := {y | k < W1p.value u y}) hx]
      rfl
    simp only [hjet, map_zero, le_refl]

/-- A zero-boundary Sobolev function with nonpositive energy vanishes almost everywhere when
the energy form has a positive quadratic lower bound on `W^{1,2}_0(Ω)`. -/
theorem value_eq_zero_of_energyFormH1_self_nonpos {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {w : W1p0 mu Omega 2}
    (hw : energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2) ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value (w : W1p mu Omega 2) x = 0 := by
  have hnorm : ‖w‖ = 0 := by
    have hbound := (hlower w).trans hw
    apply le_antisymm ?_ (norm_nonneg w)
    exact le_of_not_gt fun hpos ↦ (not_lt_of_ge hbound) (mul_pos hC (pow_pos hpos 2))
  have hw : (w : W1p mu Omega 2) = 0 :=
    congrArg (fun v : W1p0 mu Omega 2 ↦ (v : W1p mu Omega 2)) (norm_eq_zero.mp hnorm)
  have hzero : W1p.value (w : W1p mu Omega 2) = 0 := by
    rw [hw, ← W1p.valueL_apply, map_zero]
  rw [hzero]
  exact Lp.coeFn_zero (E := ℝ) (p := 2) (μ := mu.restrict Omega)

/-- A weak subsolution of a coercive divergence-form operator is nonpositive almost everywhere
if its positive part belongs to `W^{1,2}_0(Ω)`. The quadratic lower bound is required only on
the zero-boundary Sobolev space. -/
theorem value_nonpos_of_energyFormH1_nonpos {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ 0 := by
  let w : W1p0 mu Omega 2 := ⟨W1p.posPart (by norm_num) u, hboundary⟩
  have hvalue : ∀ᵐ x ∂mu.restrict Omega,
      W1p.value (w : W1p mu Omega 2) x = max (W1p.value u x) 0 := by
    dsimp only [w]
    rw [W1p.value_posPart]
    exact Lp.coeFn_posPart (W1p.value u)
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x :=
    hvalue.mono fun x hx ↦ hx.symm ▸ le_max_right _ _
  have henergy := hu w hnonneg
  dsimp only [w] at henergy
  rw [energyFormH1_posPart_right] at henergy
  filter_upwards [hvalue, value_eq_zero_of_energyFormH1_self_nonpos (w := w) hC hlower henergy]
    with x hx hz
  rw [hz] at hx
  exact (le_max_left _ _).trans hx.symm.le

/-- A weak subsolution with boundary values at most `k ≥ 0` is at most `k` almost everywhere
when the potential is nonnegative and the energy is coercive on `W^{1,2}_0(Ω)`. The boundary
condition is expressed by `(u - k)⁺ ∈ W^{1,2}_0(Ω)`. -/
theorem value_le_of_energyFormH1_nonpos
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hc : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ c x) {k : ℝ} (hk : 0 ≤ k)
    {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k := by
  let w : W1p0 mu Omega 2 := ⟨W1p.posPartAbove (by norm_num) hk u, hboundary⟩
  have hvalue : ∀ᵐ x ∂mu.restrict Omega,
      W1p.value (w : W1p mu Omega 2) x = max (W1p.value u x - k) 0 := by
    dsimp only [w]
    exact W1p.value_posPartAbove_ae (by norm_num) hk u
  have hnonneg : ∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x :=
    hvalue.mono fun x hx ↦ hx.symm ▸ le_max_right _ _
  have henergy := (energyFormH1_posPartAbove_self_le hcoeff hc hk u).trans (hu w hnonneg)
  filter_upwards [hvalue, value_eq_zero_of_energyFormH1_self_nonpos (w := w) hC hlower henergy]
    with x hx hz
  rw [hz] at hx
  exact sub_nonpos.mp ((le_max_left _ _).trans hx.symm.le)

/-- Weak comparison for a coercive energy form: ordered weak operator values and
`(u - v)⁺ ∈ W^{1,2}_0(Ω)` imply `u ≤ v` almost everywhere. -/
theorem value_le_of_energyFormH1_le {u v : W1p mu Omega 2}
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (huv : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) ≤
          energyFormH1 a b c v (w : W1p mu Omega 2)) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  classical
  have hsub := value_nonpos_of_energyFormH1_nonpos hboundary hC hlower (by
    intro w hw
    rw [← energyFormH1L_apply hcoeff]
    simpa only [map_sub, sub_apply, energyFormH1L_apply] using
      sub_nonpos.mpr (huv w hw))
  have hvalue : W1p.value (u - v) = W1p.value u - W1p.value v := by
    simp only [← W1p.valueL_apply, map_sub]
  filter_upwards [hsub, Lp.coeFn_sub (W1p.value u) (W1p.value v)] with x hx hval
  rw [hvalue, hval, Pi.sub_apply] at hx
  exact sub_nonpos.mp hx

/-- A homogeneous weak Dirichlet solution with nonpositive forcing is nonpositive almost
everywhere when the energy form has a positive quadratic lower bound on `W^{1,2}_0(Ω)`. -/
theorem IsWeakSolutionDirichlet.value_nonpos_of_energy_bound
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u) {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hf : ∀ᵐ x ∂mu.restrict Omega, f x ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value (u : W1p mu Omega 2) x ≤ 0 := by
  refine TauCeti.PDE.value_nonpos_of_energyFormH1_nonpos
    (W1p.posPart_mem_w1p0Submodule (by norm_num) u.property) hC hlower ?_
  intro v hv
  rw [(isWeakSolutionDirichlet_iff f u).mp hu v]
  exact integral_nonpos_of_ae (hf.and hv |>.mono fun x hx ↦
    mul_nonpos_of_nonpos_of_nonneg hx.1 hx.2)

/-- Homogeneous weak Dirichlet solutions with ordered forcing are ordered almost everywhere
when the energy form is bounded and has a positive quadratic lower bound on `W^{1,2}_0(Ω)`. -/
theorem IsWeakSolutionDirichlet.value_le_of_energy_bound
    {f g : Lp ℝ 2 (mu.restrict Omega)} {u v : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u) (hv : IsWeakSolutionDirichlet a b c g v)
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    {C : ℝ} (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hfg : ∀ᵐ x ∂mu.restrict Omega, f x ≤ g x) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.value (u : W1p mu Omega 2) x ≤ W1p.value (v : W1p mu Omega 2) x := by
  refine value_le_of_energyFormH1_le hcoeff
    (W1p.posPart_mem_w1p0Submodule (by norm_num)
      ((w1p0Submodule mu Omega 2).sub_mem u.property v.property)) hC hlower ?_
  intro w hw
  rw [(isWeakSolutionDirichlet_iff f u).mp hu w, (isWeakSolutionDirichlet_iff g v).mp hv w]
  exact integral_mono_ae
    ((Lp.memLp f).integrable_mul (Lp.memLp (W1p.value (w : W1p mu Omega 2))))
    ((Lp.memLp g).integrable_mul (Lp.memLp (W1p.value (w : W1p mu Omega 2))))
    (hfg.and hw |>.mono fun x hx ↦ mul_le_mul_of_nonneg_right hx.1 hx.2)

-- The coercive energy estimate used below follows L. C. Evans, *Partial Differential
-- Equations*, §6.2. For the weak-subsolution maximum principle, see D. Gilbarg and
-- N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Chapter 8,
-- Theorem 8.1.
section Poincare

variable [DecidableEq ι] {lam Lam beta gamma P : ℝ}

/-- For `-div(a ∇u) + b · ∇u + cu` with uniformly elliptic, bounded measurable
coefficients and `c ≥ 0`, a Poincaré bound `P` and `βP < λ` imply that a weak subsolution
with `u⁺ ∈ W^{1,2}_0(Ω)` is nonpositive almost everywhere. -/
theorem UniformlyEllipticOn.value_nonpos_of_small_drift_of_poincare
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    (hbeta : 0 ≤ beta) (hP : 0 ≤ P)
    (hpoincare : ∀ w : W1p0 mu Omega 2,
      ‖W1p.value (w : W1p mu Omega 2)‖ ≤
        P * ‖W1p.gradient (w : W1p mu Omega 2)‖)
    (hsmall : beta * P < lam)
    {u : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ 0 := by
  have hC := energyFormH1_poincare_constant_pos h.pos hbeta hP hsmall
  refine value_nonpos_of_energyFormH1_nonpos hboundary hC ?_ hu
  intro w
  exact h.mul_norm_sq_le_energyFormH1_self_of_poincare ha hb hc hb_bound hc_bound
    hc_nonneg (hpoincare w)

/-- For `-div(a ∇u) + b · ∇u + cu` with uniformly elliptic, bounded measurable
coefficients and `c ≥ 0`, a Poincaré bound `P` and `βP < λ` imply that a weak subsolution
with `k ≥ 0` and `(u - k)⁺ ∈ W^{1,2}_0(Ω)` is at most `k` almost everywhere. -/
theorem UniformlyEllipticOn.value_le_const_of_small_drift_of_poincare
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    (hbeta : 0 ≤ beta) (hP : 0 ≤ P)
    (hpoincare : ∀ w : W1p0 mu Omega 2,
      ‖W1p.value (w : W1p mu Omega 2)‖ ≤
        P * ‖W1p.gradient (w : W1p mu Omega 2)‖)
    (hsmall : beta * P < lam)
    {k : ℝ} (hk : 0 ≤ k) {u : W1p mu Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ k := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hb_bound hc_bound
  have hC := energyFormH1_poincare_constant_pos h.pos hbeta hP hsmall
  refine value_le_of_energyFormH1_nonpos hcoeff
    ((ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx ↦ hc_nonneg x hx)
    hk hboundary hC ?_ hu
  intro w
  exact h.mul_norm_sq_le_energyFormH1_self_of_poincare ha hb hc hb_bound hc_bound
    hc_nonneg (hpoincare w)

/-- For `-div(a ∇u) + b · ∇u + cu` with uniformly elliptic, bounded measurable
coefficients and `c ≥ 0`, a Poincaré bound `P` and `βP < λ` imply `u ≤ v` almost
everywhere when `(u - v)⁺ ∈ W^{1,2}_0(Ω)` and the weak operator values are ordered. -/
theorem UniformlyEllipticOn.value_le_of_small_drift_of_poincare
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    (hbeta : 0 ≤ beta) (hP : 0 ≤ P)
    (hpoincare : ∀ w : W1p0 mu Omega 2,
      ‖W1p.value (w : W1p mu Omega 2)‖ ≤
        P * ‖W1p.gradient (w : W1p mu Omega 2)‖)
    (hsmall : beta * P < lam)
    {u v : W1p mu Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule mu Omega 2)
    (huv : ∀ w : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (w : W1p mu Omega 2) x) →
        energyFormH1 a b c u (w : W1p mu Omega 2) ≤
          energyFormH1 a b c v (w : W1p mu Omega 2)) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hb_bound hc_bound
  have hC := energyFormH1_poincare_constant_pos h.pos hbeta hP hsmall
  refine value_le_of_energyFormH1_le hcoeff hboundary hC ?_ huv
  intro w
  exact h.mul_norm_sq_le_energyFormH1_self_of_poincare ha hb hc hb_bound hc_bound
    hc_nonneg (hpoincare w)

end Poincare

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam beta gamma : ℝ}

/-- For `-div(a ∇u) + b · ∇u + cu` on `Ω ⊆ B(z, R)` with uniformly elliptic,
bounded measurable coefficients, `c ≥ 0`, and `β(2R) < λ`, a weak subsolution with
`u⁺ ∈ W^{1,2}_0(Ω)` is nonpositive almost everywhere. -/
theorem UniformlyEllipticOn.value_nonpos_of_small_drift_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hbeta : 0 ≤ beta) (hR : 0 ≤ R)
    (hsmall : beta * (2 * R) < lam)
    {u : W1p volume Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ v : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (v : W1p volume Omega 2) x) →
        energyFormH1 a b c u (v : W1p volume Omega 2) ≤ 0) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ 0 := by
  apply h.value_nonpos_of_small_drift_of_poincare ha hb hc hb_bound hc_bound
    hc_nonneg hbeta (by positivity : 0 ≤ 2 * R)
    (fun w ↦ W1p.norm_value_le_mul_norm_gradient_of_subset_ball
      (by norm_num) hOmega w.property) hsmall hboundary hu

/-- For `-div(a ∇u) + b · ∇u + cu` on `Ω ⊆ B(z, R)` with uniformly elliptic,
bounded measurable coefficients, `c ≥ 0`, and `β(2R) < λ`, a weak subsolution with
`k ≥ 0` and `(u - k)⁺ ∈ W^{1,2}_0(Ω)` is at most `k` almost everywhere. -/
theorem UniformlyEllipticOn.value_le_const_of_small_drift_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hbeta : 0 ≤ beta) (hR : 0 ≤ R)
    (hsmall : beta * (2 * R) < lam)
    {k : ℝ} (hk : 0 ≤ k) {u : W1p volume Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ v : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (v : W1p volume Omega 2) x) →
        energyFormH1 a b c u (v : W1p volume Omega 2) ≤ 0) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ k := by
  apply h.value_le_const_of_small_drift_of_poincare ha hb hc hb_bound hc_bound
    hc_nonneg hbeta (by positivity : 0 ≤ 2 * R)
    (fun w ↦ W1p.norm_value_le_mul_norm_gradient_of_subset_ball
      (by norm_num) hOmega w.property) hsmall hk hboundary hu

/-- For `-div(a ∇u) + b · ∇u + cu` on `Ω ⊆ B(z, R)` with uniformly elliptic,
bounded measurable coefficients, `c ≥ 0`, and `β(2R) < λ`, ordered weak operator values
and `(u - v)⁺ ∈ W^{1,2}_0(Ω)` imply `u ≤ v` almost everywhere. -/
theorem UniformlyEllipticOn.value_le_of_small_drift_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hbeta : 0 ≤ beta) (hR : 0 ≤ R)
    (hsmall : beta * (2 * R) < lam)
    {u v : W1p volume Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule volume Omega 2)
    (huv : ∀ w : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (w : W1p volume Omega 2) x) →
        energyFormH1 a b c u (w : W1p volume Omega 2) ≤
          energyFormH1 a b c v (w : W1p volume Omega 2)) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  apply h.value_le_of_small_drift_of_poincare ha hb hc hb_bound hc_bound
    hc_nonneg hbeta (by positivity : 0 ≤ 2 * R)
    (fun w ↦ W1p.norm_value_le_mul_norm_gradient_of_subset_ball
      (by norm_num) hOmega w.property) hsmall hboundary huv

end Euclidean

end TauCeti.PDE
