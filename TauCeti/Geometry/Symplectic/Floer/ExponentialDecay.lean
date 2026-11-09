/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Periodic
public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder
import TauCeti.Analysis.Calculus.FDeriv.Remainder
import TauCeti.Analysis.SpecificLimits.DiscreteGronwall
import TauCeti.Geometry.Symplectic.Hamiltonian.Variation
import TauCeti.MeasureTheory.Integral.IntervalIntegral.CauchySchwarz
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exponential decay of the energy at a nondegenerate end

Let `(V, ω)` be a symplectic vector space and `H : ℝ → V → ℝ` a `C²` Hamiltonian, and let `x` be a
`1`-periodic orbit of its Hamiltonian vector field `X_{H_t}` which is *nondegenerate*: the
linearized return map `Ψ(1)`, where `Ψ = TauCeti.dysonSeriesLeft S` is the propagator of
`ζ' = S_t ζ` for `S_t = dX_{H_t}(x(t))`, has no nonzero fixed vector. Equivalently, `x(0)` is a
nondegenerate fixed point of the time-one map
(`TauCeti.SymplecticForm.fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft`), and the
asymptotic operator of `x` has no nonzero one-periodic kernel element
(`TauCeti.SymplecticForm.isNondegenerateFixedPt_iff_forall_eq_zero_of_asymptoticOperator_eq_zero`).

**The action near a nondegenerate orbit.** A nondegenerate orbit is a critical point of the action
functional `A_H` at which the gradient `γ ↦ γ' - X_{H_t}(γ)` is nondegenerate. Accordingly, there
are `δ > 0` and `C ≥ 0` such that every `C¹` loop `γ` which is `δ`-close to `x` satisfies

`|A_H(γ) - A_H(x)| ≤ C ∫₀¹ ‖γ' - X_{H_t}(γ)‖² dt`

(`TauCeti.SymplecticForm.exists_abs_hamiltonianAction_sub_le_of_nondegenerate`). Write
`γ = x + ξ`. Since `x` is a critical point, the action difference is `½ ∫₀¹ ω(ξ, ξ') + ∫₀¹ R`,
with `R` the second-order Taylor remainder of `H_t` at `x(t)`
(`TauCeti.SymplecticForm.hamiltonianAction_sub_hamiltonianAction_eq_integral`), so it is quadratic
in `ξ` and the defect `η = γ' - X_{H_t}(γ)`. The loop `ξ` solves `ξ' = S_t ξ + η + r` with `r` of
size `o(‖ξ‖)`, and by nondegeneracy the a priori estimate for periodic solutions
(`TauCeti.exists_forall_norm_le_mul_integral_norm`) bounds `sup ‖ξ‖` by `∫₀¹ ‖η‖`
(`TauCeti.SymplecticForm.exists_forall_norm_sub_le_mul_integral_of_nondegenerate`).

**Exponential decay.** Let `u` be a finite-energy solution of the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on the half-cylinder `s > a`, for uniformly tame almost complex
structures, whose loops `u(s, ·)` converge uniformly to the nondegenerate orbit `x` as `s → ∞`.
Then the energy of `u` over `[s, ∞) × [0, 1]` decays exponentially in `s`
(`TauCeti.SymplecticForm.exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp`). This
energy is `E(s) = A_H(x) - A_H(u(s, ·))`. By the estimate above and the coercivity of the energy
density, `E(s)` is at most a constant `K` times the energy `∫₀¹ e(s, t) dt` of the slice at `s`
(`TauCeti.SymplecticForm.exists_abs_hamiltonianAction_sub_le_mul_setIntegral_floerEnergyDensity`),
which is `-E'(s)`. Integrating over steps of length `K` halves `E`, and
`TauCeti.le_div_mul_exp_of_antitoneOn` turns this into exponential decay at the rate `log 2 / K`.

Exponential decay of the energy is the first step towards the exponential convergence of a Floer
solution to its asymptotic orbit, which places the moduli spaces of Floer cylinders and pairs of
pants in weighted Sobolev spaces. Pointwise exponential decay of `u - x` and its derivatives is
not treated here.

## Main results

* `TauCeti.SymplecticForm.exists_forall_norm_sub_le_mul_integral_of_nondegenerate`: a loop near a
  nondegenerate orbit is uniformly within a constant times the `L¹` norm of its defect.
* `TauCeti.SymplecticForm.exists_abs_hamiltonianAction_sub_le_of_nondegenerate`: the action
  difference near a nondegenerate orbit is bounded by the squared `L²` norm of the defect.
* `TauCeti.SymplecticForm.exists_abs_hamiltonianAction_sub_le_mul_setIntegral_floerEnergyDensity`:
  the action defect of a loop of a Floer solution near a nondegenerate orbit is bounded by the
  energy of its slice.
* `TauCeti.SymplecticForm.exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp`: the
  energy of a finite-energy Floer half-cylinder asymptotic to a nondegenerate orbit decays
  exponentially.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the exponential decay of finite-energy Floer trajectories
  at nondegenerate orbits.
* J. Robbin and D. Salamon, *Asymptotic behaviour of holomorphic strips*, Ann. Inst. H. Poincaré
  Anal. Non Linéaire 18 (2001), 573–612.
-/

public section

open Set Filter Topology MeasureTheory Function intervalIntegral Metric
open scoped ENNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {x : ℝ → V}

/-- **Loops near a nondegenerate orbit.** Let `H` be a `C²` Hamiltonian and let `x` be an orbit of
its Hamiltonian vector field with `x 1 = x 0`, nondegenerate in the sense that the propagator `Ψ`
of the linearized equation `ζ' = dX_{H_t}(x(t)) ζ` has no nonzero fixed vector at time `1`. Then
there are `δ > 0` and `C ≥ 0` such that every loop `γ` with continuous derivative `γ'`,
`γ 1 = γ 0` and `‖γ t - x t‖ ≤ δ` on `[0, 1]` satisfies
`‖γ t - x t‖ ≤ C ∫₀¹ ‖γ' - X_{H_s}(γ)‖ ds` on `[0, 1]`. In particular `x` is the only orbit in this
neighbourhood. -/
theorem exists_forall_norm_sub_le_mul_integral_of_nondegenerate (hH : ContDiff ℝ 2 (uncurry H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hx1 : x 1 = x 0)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0) :
    ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ {γ γ' : ℝ → V}, Continuous γ' → (∀ t, HasDerivAt γ (γ' t) t) →
      γ 1 = γ 0 → (∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - x t‖ ≤ δ) → ∀ t ∈ Icc (0 : ℝ) 1,
      ‖γ t - x t‖ ≤ C * ∫ s in (0 : ℝ)..1, ‖γ' s - ω.hamiltonianVectorField (H s) (γ s)‖ := by
  set X : ℝ → V → V := fun t ↦ ω.hamiltonianVectorField (H t)
  set S : ℝ → V →L[ℝ] V := fun t ↦ fderiv ℝ (X t) (x t)
  have hXc : ContDiff ℝ 1 (uncurry X) := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hS : Continuous S := ω.continuous_fderiv_hamiltonianVectorField_comp hH hxc
  -- The a priori estimate for periodic solutions of `ξ' = S ξ + f`.
  have hunit : IsUnit ((1 : ℝ) • (1 : V →L[ℝ] V) - dysonSeriesLeft S 1) := by
    refine ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.2
      ((LinearMap.isUnit_iff_ker_eq_bot _).2 (LinearMap.ker_eq_bot'.2 fun v hv ↦ hnd v ?_))
    have hv' : v - dysonSeriesLeft S 1 v = 0 := by simpa using hv
    exact (sub_eq_zero.1 hv').symm
  obtain ⟨C₀, hC₀, hA⟩ := exists_forall_norm_le_mul_integral_norm hS zero_le_one hunit
  -- The linearization error `r` is at most `ε₁ ‖ξ‖`, small enough to be absorbed.
  set ε₁ : ℝ := 1 / (2 * (C₀ + 1))
  have hC₀ε₁ : C₀ * ε₁ ≤ 1 / 2 := by
    have hε₁ : C₀ * ε₁ = C₀ / (2 * (C₀ + 1)) := by ring
    rw [hε₁, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨δ, hδ, hlin⟩ := IsCompact.exists_pos_forall_norm_sub_sub_fderiv_le
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)) hXc hxc.continuousOn (ε := ε₁) (by positivity)
  refine ⟨δ, hδ, 2 * C₀, by positivity, fun {γ γ'} hγ' hγ hγ1 hγx ↦ ?_⟩
  set ξ : ℝ → V := fun t ↦ γ t - x t with hξdef
  set η : ℝ → V := fun t ↦ γ' t - X t (γ t) with hηdef
  set r : ℝ → V := fun t ↦ X t (γ t) - X t (x t) - S t (ξ t) with hrdef
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t ↦ (hγ t).continuousAt
  have hXcomp {p : ℝ → V} (hp : Continuous p) : Continuous fun t ↦ X t (p t) :=
    hXc.continuous.comp (continuous_id.prodMk hp)
  have hξc : Continuous ξ := hγc.sub hxc
  have hηc : Continuous η := hγ'.sub (hXcomp hγc)
  have hrc : Continuous r := ((hXcomp hγc).sub (hXcomp hxc)).sub (hS.clm_apply hξc)
  have hr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖r t‖ ≤ ε₁ * ‖ξ t‖ := by
    simpa [hrdef, hξdef, add_sub_cancel] using hlin t ht (ξ t) (hγx t ht)
  -- `ξ` is a periodic solution of `ξ' = S ξ + (η + r)`; bound it at a point where it is maximal.
  have hξd (t : ℝ) : HasDerivAt ξ (S t (ξ t) + (η t + r t)) t :=
    ((hγ t).sub (hx t)).congr_deriv (by simp only [hηdef, hrdef]; abel)
  have hbound := hA (hηc.add hrc) hξd (by simp [hξdef, hγ1, hx1])
  obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) hξc.norm.continuousOn
  set m := ‖ξ t₀‖
  set N := ∫ t in (0 : ℝ)..1, ‖η t‖
  have hfm : ∫ t in (0 : ℝ)..1, ‖η t + r t‖ ≤ N + ε₁ * m := by
    calc _ ≤ ∫ t in (0 : ℝ)..1, (‖η t‖ + ε₁ * m) :=
          integral_mono_on zero_le_one ((hηc.add hrc).norm.intervalIntegrable _ _)
            ((hηc.norm.add continuous_const).intervalIntegrable _ _) fun t ht ↦
            (norm_add_le _ _).trans (add_le_add le_rfl
              ((hr t ht).trans (mul_le_mul_of_nonneg_left (hmax ht) (by positivity))))
      _ = N + ε₁ * m := by
          rw [integral_add (hηc.norm.intervalIntegrable _ _) intervalIntegrable_const,
            intervalIntegral.integral_const, sub_zero, one_smul]
  have hm : m ≤ 2 * C₀ * N := by
    have h := (hbound t₀ ht₀).trans (mul_le_mul_of_nonneg_left hfm hC₀)
    have h' := mul_le_mul_of_nonneg_right hC₀ε₁ (norm_nonneg (ξ t₀))
    nlinarith
  exact fun t ht ↦ (hmax ht).trans hm

/-- **The action near a nondegenerate orbit.** Let `H` be a `C²` Hamiltonian and let `x` be an
orbit of its Hamiltonian vector field with `x 1 = x 0`, nondegenerate in the sense that the
propagator `Ψ` of the linearized equation `ζ' = dX_{H_t}(x(t)) ζ` has no nonzero fixed vector at
time `1`. Then there are `δ > 0` and `C ≥ 0` such that every loop `γ` with continuous derivative
`γ'`, `γ 1 = γ 0` and `‖γ t - x t‖ ≤ δ` on `[0, 1]` satisfies
`|A_H(γ) - A_H(x)| ≤ C ∫₀¹ ‖γ' - X_{H_t}(γ)‖² dt`. -/
theorem exists_abs_hamiltonianAction_sub_le_of_nondegenerate (hH : ContDiff ℝ 2 (uncurry H))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hx1 : x 1 = x 0)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0) :
    ∃ δ > 0, ∃ C, 0 ≤ C ∧ ∀ {γ γ' : ℝ → V}, Continuous γ' → (∀ t, HasDerivAt γ (γ' t) t) →
      γ 1 = γ 0 → (∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - x t‖ ≤ δ) →
      |ω.hamiltonianAction H γ - ω.hamiltonianAction H x| ≤
        C * ∫ t in (0 : ℝ)..1, ‖γ' t - ω.hamiltonianVectorField (H t) (γ t)‖ ^ 2 := by
  set X : ℝ → V → V := fun t ↦ ω.hamiltonianVectorField (H t)
  set S : ℝ → V →L[ℝ] V := fun t ↦ fderiv ℝ (X t) (x t)
  have hXc : ContDiff ℝ 1 (uncurry X) := ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  obtain ⟨δ₁, hδ₁, C₀, hC₀, hiso⟩ :=
    exists_forall_norm_sub_le_mul_integral_of_nondegenerate hH hx hx1 hnd
  -- Near `x`, the vector field is Lipschitz at `x t` with constant `|L| + 1`.
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (ω.continuous_fderiv_hamiltonianVectorField_comp hH hxc).continuousOn
  obtain ⟨δ₂, hδ₂, hlin⟩ := IsCompact.exists_pos_forall_norm_sub_sub_fderiv_le
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)) hXc hxc.continuousOn one_pos
  have hXlip (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (y : V) (hy : ‖y - x t‖ ≤ δ₂) :
      ‖X t y - X t (x t)‖ ≤ (|L| + 1) * ‖y - x t‖ := by
    have h := hlin t ht (y - x t) hy
    rw [add_sub_cancel] at h
    calc ‖X t y - X t (x t)‖ = ‖S t (y - x t) + (X t y - X t (x t) - S t (y - x t))‖ := by
          congr 1; abel
      _ ≤ |L| * ‖y - x t‖ + 1 * ‖y - x t‖ := (norm_add_le _ _).trans (add_le_add
          ((S t).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right
            ((hL t ht).trans (le_abs_self _)) (norm_nonneg _))) h)
      _ = _ := by ring
  set B := ‖ω.toBilinForm.toContinuousBilinearMap‖
  have hB0 : 0 ≤ B := by positivity
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, B * C₀ / 2 + 3 / 2 * B * (|L| + 1) * C₀ ^ 2, by positivity,
    fun {γ γ'} hγ' hγ hγ1 hγx ↦ ?_⟩
  set ξ : ℝ → V := fun t ↦ γ t - x t with hξdef
  set η : ℝ → V := fun t ↦ γ' t - X t (γ t) with hηdef
  set ξ' : ℝ → V := fun t ↦ γ' t - X t (x t) with hξ'def
  set R : ℝ → ℝ := fun t ↦ H t (γ t) - H t (x t) - fderiv ℝ (H t) (x t) (ξ t) with hRdef
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t ↦ (hγ t).continuousAt
  have hXcomp {p : ℝ → V} (hp : Continuous p) : Continuous fun t ↦ X t (p t) :=
    hXc.continuous.comp (continuous_id.prodMk hp)
  have hηc : Continuous η := hγ'.sub (hXcomp hγc)
  have hRc : Continuous R := by
    simp only [hRdef, ← ω.apply_hamiltonianVectorField]
    exact (((hH.continuous.comp (continuous_id.prodMk hγc)).sub
      (hH.continuous.comp (continuous_id.prodMk hxc)))).sub
      (ω.continuous_apply_comp (hXcomp hxc) (hγc.sub hxc))
  have hδ₁x (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖ξ t‖ ≤ δ₁ := (hγx t ht).trans (min_le_left _ _)
  have hδ₂x (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖ξ t‖ ≤ δ₂ := (hγx t ht).trans (min_le_right _ _)
  -- `sup ‖ξ‖ ≤ C₀ N` with `N = ∫ ‖η‖`, by nondegeneracy.
  set N := ∫ t in (0 : ℝ)..1, ‖η t‖
  obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) (hγc.sub hxc).norm.continuousOn
  set m := ‖ξ t₀‖
  have hm0 : 0 ≤ m := norm_nonneg _
  have hξm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖ξ t‖ ≤ m := hmax ht
  have hm : m ≤ C₀ * N := hiso hγ' hγ hγ1 hδ₁x t₀ ht₀
  -- Both terms of the action expansion are quadratic in `ξ` and `η`.
  have hξ'b (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖ξ' t‖ ≤ ‖η t‖ + (|L| + 1) * m := by
    have h : ξ' t = η t + (X t (γ t) - X t (x t)) := by simp only [hξ'def, hηdef]; abel
    rw [h]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((hXlip t ht _ (hδ₂x t ht)).trans
      (mul_le_mul_of_nonneg_left (hξm t ht) (by positivity))))
  have hRb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |R t| ≤ B * (|L| + 1) * m ^ 2 := by
    have h := ω.abs_sub_sub_fderiv_le_of_norm_hamiltonianVectorField_sub_le
      (fun y ↦ (hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) y)
      (by positivity) (fun z hz ↦ hXlip t ht z (by simpa [dist_eq_norm] using hz)) (hδ₂x t ht)
    calc |R t| ≤ B * (|L| + 1) * ‖ξ t‖ ^ 2 := h
      _ ≤ B * (|L| + 1) * m ^ 2 := by gcongr; exact hξm t ht
  have hpb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |(1 / 2 : ℝ) * ω (ξ t) (ξ' t) + R t| ≤
        (1 / 2 : ℝ) * B * m * ‖η t‖ + (3 / 2 : ℝ) * B * (|L| + 1) * m ^ 2 := by
    have h1 : |ω (ξ t) (ξ' t)| ≤ B * m * (‖η t‖ + (|L| + 1) * m) :=
      (ω.abs_apply_le_opNorm_mul_norm_mul_norm _ _).trans
        (by gcongr; exacts [hξm t ht, hξ'b t ht])
    calc _ ≤ |(1 / 2 : ℝ) * ω (ξ t) (ξ' t)| + |R t| := abs_add_le _ _
      _ = (1 / 2 : ℝ) * |ω (ξ t) (ξ' t)| + |R t| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      _ ≤ (1 / 2 : ℝ) * (B * m * (‖η t‖ + (|L| + 1) * m)) + B * (|L| + 1) * m ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) (hRb t ht)
      _ = _ := by ring
  have hint : |∫ t in (0 : ℝ)..1, ((1 / 2 : ℝ) * ω (ξ t) (ξ' t) + R t)| ≤
      (1 / 2 : ℝ) * B * m * N + (3 / 2 : ℝ) * B * (|L| + 1) * m ^ 2 := by
    have hi : IntervalIntegrable (fun t ↦ (1 / 2 : ℝ) * B * m * ‖η t‖) volume 0 1 :=
      (continuous_const.mul hηc.norm).intervalIntegrable _ _
    calc _ ≤ ∫ t in (0 : ℝ)..1, |(1 / 2 : ℝ) * ω (ξ t) (ξ' t) + R t| :=
          abs_integral_le_integral_abs zero_le_one
      _ ≤ ∫ t in (0 : ℝ)..1,
          ((1 / 2 : ℝ) * B * m * ‖η t‖ + (3 / 2 : ℝ) * B * (|L| + 1) * m ^ 2) :=
          integral_mono_on zero_le_one (((continuous_const.mul (ω.continuous_apply_comp
            (hγc.sub hxc) (hγ'.sub (hXcomp hxc)))).add hRc).abs.intervalIntegrable _ _)
            (hi.add intervalIntegrable_const) hpb
      _ = _ := by
          rw [intervalIntegral.integral_add hi intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero,
            one_smul]
  -- The `L¹` norm of the defect is at most its `L²` norm.
  have hN0 : 0 ≤ N := integral_nonneg zero_le_one fun _ _ ↦ norm_nonneg _
  have hN2 : N ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖η t‖ ^ 2 := by
    have h := integral_le_sqrt_mul_sqrt_integral_sq zero_le_one (fun t _ ↦ norm_nonneg (η t))
      ((hηc.norm.pow 2).intervalIntegrable _ _)
    rw [sub_zero, Real.sqrt_one, one_mul] at h
    calc N ^ 2 ≤ √(∫ t in (0 : ℝ)..1, ‖η t‖ ^ 2) ^ 2 := by gcongr
      _ = _ := Real.sq_sqrt (integral_nonneg zero_le_one fun _ _ ↦ by positivity)
  rw [ω.hamiltonianAction_sub_hamiltonianAction_eq_integral (hH.of_le (by norm_num)) hx hx1 hγ' hγ
    hγ1]
  calc _ ≤ (1 / 2 : ℝ) * B * m * N + (3 / 2 : ℝ) * B * (|L| + 1) * m ^ 2 := hint
    _ ≤ (1 / 2 : ℝ) * B * (C₀ * N) * N + (3 / 2 : ℝ) * B * (|L| + 1) * (C₀ * N) ^ 2 := by
        gcongr
    _ = (B * C₀ / 2 + 3 / 2 * B * (|L| + 1) * C₀ ^ 2) * N ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hN2 (by positivity)

variable {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {a c M : ℝ}

/-- **The action defect of a Floer slice near a nondegenerate orbit.** Let `H` be a `C²`
Hamiltonian and let `x` be a nondegenerate orbit as in
`TauCeti.SymplecticForm.exists_abs_hamiltonianAction_sub_le_of_nondegenerate`. Let `u` be a `C¹`
solution of the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on the half-cylinder `s > a`,
with `1`-periodic loops and almost complex structures satisfying `c ‖v‖² ≤ ω(v, J z v)` and
`‖J z v‖ ≤ M ‖v‖`, `c > 0`. Then there are `δ > 0` and `K > 0` such that every loop `u(s, ·)`
which is `δ`-close to `x` on `[0, 1]` has action within `K` times the energy of its slice:
`|A_H(u(s, ·)) - A_H(x)| ≤ K ∫₀¹ e(s, t) dt`. -/
theorem exists_abs_hamiltonianAction_sub_le_mul_setIntegral_floerEnergyDensity
    (hH : ContDiff ℝ 2 (uncurry H)) (hu : ContDiffOn ℝ 1 u (Ioi a ×ˢ univ))
    (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hc : 0 < c) (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hx1 : x 1 = x 0)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0) :
    ∃ δ > 0, ∃ K, 0 < K ∧ ∀ s, a < s → (∀ t ∈ Icc (0 : ℝ) 1, ‖u (s, t) - x t‖ ≤ δ) →
      |ω.hamiltonianAction H (fun t ↦ u (s, t)) - ω.hamiltonianAction H x| ≤
        K * ∫ t in Icc (0 : ℝ) 1, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u (s, t) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u with he
  have hopen : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  obtain ⟨δ, hδ, C₁, hC₁, hB⟩ := exists_abs_hamiltonianAction_sub_le_of_nondegenerate hH hx hx1 hnd
  refine ⟨δ, hδ, C₁ * ((1 + M ^ 2) / c) + 1, by positivity, fun s hsa hclose ↦ ?_⟩
  -- The energy density controls the defect of the loops pointwise.
  have hdef (z : ℝ × ℝ) (hz : z ∈ Ioi a ×ˢ Icc 0 1) :
      ‖fderiv ℝ u z (0, 1) - ω.hamiltonianVectorField (H z.2) (u z)‖ ^ 2 ≤
        (1 + M ^ 2) / c * e z ∧ 0 ≤ e z := by
    have h := ω.mul_norm_sq_add_norm_sq_perturbedFDeriv_le_mul_floerEnergyDensity hc.le
      (hJc z hz) (hJM z hz) (hfloer z hz)
    rw [← sliceDefect_hamiltonianVectorField, sliceDefect_def] at h
    have h₁ := sq_nonneg ‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineReal‖
    have h₂ := sq_nonneg ‖fderiv ℝ u z (0, 1) - ω.hamiltonianVectorField (H z.2) (u z)‖
    refine ⟨?_, ?_⟩
    · rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      nlinarith
    · nlinarith [sq_nonneg M]
  have hmem (t : ℝ) : (s, t) ∈ Ioi a ×ˢ (univ : Set ℝ) := ⟨hsa, mem_univ t⟩
  have hslicec : Continuous fun t ↦ e (s, t) :=
    (ω.continuousOn_floerEnergyDensity hopen hu contDiffOn_const
      (contDiff_uncurry_cylindrical (hH.of_le (by norm_num))).contDiffOn).comp_continuous
      (continuous_const.prodMk continuous_id) hmem
  -- The loop `u(s, ·)` has derivative `∂_t u`, and the action estimate applies to it.
  have hγ' : Continuous fun t ↦ fderiv ℝ u (s, t) (0, 1) :=
    ((hu.continuousOn_fderiv_of_isOpen hopen le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) hmem).clm_apply continuous_const
  have hγ (t : ℝ) : HasDerivAt (fun t ↦ u (s, t)) (fderiv ℝ u (s, t) (0, 1)) t :=
    ((hu.differentiableOn one_ne_zero _ (hmem t)).differentiableAt
      (hopen.mem_nhds (hmem t))).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  have hact := hB hγ' hγ (by simpa using hper s hsa 0) hclose
  have hint : ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (s, t) (0, 1) -
      ω.hamiltonianVectorField (H t) (u (s, t))‖ ^ 2 ≤
      (1 + M ^ 2) / c * ∫ t in Icc (0 : ℝ) 1, e (s, t) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      ← intervalIntegral.integral_const_mul]
    refine integral_mono_on zero_le_one ?_
      ((continuous_const.mul hslicec).intervalIntegrable _ _)
      fun t ht ↦ (hdef (s, t) ⟨hsa, ht⟩).1
    exact ((hγ'.sub ((ω.contDiff_hamiltonianVectorField_uncurry (n := 1) hH).continuous.comp
      (continuous_id.prodMk ((hu.continuousOn.comp_continuous
        (continuous_const.prodMk continuous_id) hmem))))).norm.pow 2).intervalIntegrable _ _
  have hg0 : 0 ≤ ∫ t in Icc (0 : ℝ) 1, e (s, t) :=
    setIntegral_nonneg measurableSet_Icc fun t ht ↦ (hdef (s, t) ⟨hsa, ht⟩).2
  calc _ ≤ C₁ * ((1 + M ^ 2) / c * ∫ t in Icc (0 : ℝ) 1, e (s, t)) :=
        hact.trans (mul_le_mul_of_nonneg_left hint hC₁)
    _ ≤ (C₁ * ((1 + M ^ 2) / c) + 1) * ∫ t in Icc (0 : ℝ) 1, e (s, t) := by
        rw [← mul_assoc, add_mul, one_mul]
        exact le_add_of_nonneg_right hg0

/-- **Exponential decay of the energy at a nondegenerate end.** Let `H` be a `C²` Hamiltonian,
`1`-periodic in time, and let `u` be a `C²` solution of the Floer equation
`∂_s u + J (∂_t u - X_{H_t}(u)) = 0` on the half-cylinder `s > a`, with `1`-periodic loops,
almost complex structures satisfying `c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖` with `c > 0`, and
finite energy. Suppose that the loops `u(s, ·)` converge uniformly as `s → ∞` to a `1`-periodic
orbit `x` which is nondegenerate: the propagator of `ζ' = dX_{H_t}(x(t)) ζ` has no nonzero fixed
vector at time `1`. Then the energy of `u` over `[s, ∞) × [0, 1]` is eventually at most
`C exp (-κ s)`, for some `κ > 0`. -/
theorem exists_pos_eventually_setLIntegral_floerEnergyDensity_Ici_le_exp
    (hH : ContDiff ℝ 2 (uncurry H)) (hHper : Periodic H 1)
    (hu : ContDiffOn ℝ 2 u (Ioi a ×ˢ univ)) (hper : ∀ s, a < s → Periodic (fun t ↦ u (s, t)) 1)
    (hc : 0 < c) (hJc : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J z v))
    (hJM : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ∀ v, ‖J z v‖ ≤ M * ‖v‖)
    (hfloer : ∀ z ∈ Ioi a ×ˢ Icc 0 1, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in Ioi a ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hxper : Periodic x 1) (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t)
    (hnd : ∀ v, dysonSeriesLeft (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) 1 v = v →
      v = 0)
    (hux : TendstoUniformly (fun s t ↦ u (s, t)) x atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∫⁻ z in Ici s ×ˢ Icc 0 1,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≤
        ENNReal.ofReal (C * Real.exp (-(κ * s))) := by
  set e : ℝ × ℝ → ℝ := ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u with he
  set A : ℝ → ℝ := fun s ↦ ω.hamiltonianAction H (fun t ↦ u (s, t)) with hAdef
  have hH1 : ContDiff ℝ 1 (uncurry H) := hH.of_le (by norm_num)
  have hopen : IsOpen (Ioi a ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hJ : ∀ z ∈ Ioi a ×ˢ Icc 0 1, ω.Tames (J z) := fun z hz v hv ↦
    (mul_pos hc (pow_pos (norm_pos_iff.2 hv) 2)).trans_le (hJc z hz v)
  obtain ⟨δ, hδ, K, hKpos, hslice⟩ :=
    exists_abs_hamiltonianAction_sub_le_mul_setIntegral_floerEnergyDensity hH
      (hu.of_le (by norm_num)) hper hc hJc hJM hfloer hx (by simpa using hxper 0) hnd
  -- Eventually the loops are `min δ 1`-close to `x`.
  obtain ⟨s₁, hs₁⟩ := eventually_atTop.1
    (Metric.tendstoUniformly_iff.1 hux (min δ 1) (lt_min hδ one_pos))
  set s₀ := max s₁ (a + 1)
  have hs₀a : a < s₀ := (lt_add_one a).trans_le (le_max_right _ _)
  have hclose (s : ℝ) (hs : s₀ ≤ s) (t : ℝ) : ‖u (s, t) - x t‖ ≤ min δ 1 := by
    have h := hs₁ s ((le_max_left _ _).trans hs) t
    rw [dist_comm, dist_eq_norm] at h
    exact h.le
  -- The actions tend to the action of `x`, which is therefore the asymptotic orbit of `u`.
  have hsub : Ioi s₀ ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ Icc 0 1 :=
    prod_mono (Ioi_subset_Ioi hs₀a.le) le_rfl
  have hK : IsCompact (cthickening 1 (range x)) :=
    (hxper.compact_of_continuous one_ne_zero hxc).cthickening
  obtain ⟨x₀, -, -, ⟨φ, -, hφ, hux₀⟩, hlim⟩ :=
    exists_periodic_hasDerivAt_tendsto_hamiltonianAction_of_floer (a := s₀) hH1 hHper
      (hu.mono (prod_mono (Ioi_subset_Ioi hs₀a.le) le_rfl)) (fun s hs ↦ hper s (hs₀a.trans hs))
      hK (fun s hs t ↦ mem_cthickening_of_dist_le _ (x t) 1 _ (mem_range_self t) (by
        rw [dist_eq_norm]; exact (hclose s hs.le t).trans (min_le_right _ _)))
      hc (fun z hz ↦ hJc z (hsub hz)) (fun z hz ↦ hJM z (hsub hz)) (fun z hz ↦ hfloer z (hsub hz))
      (ne_top_of_le_ne_top hE (lintegral_mono_set hsub))
  have hx₀ : x₀ = x := funext fun t ↦
    tendsto_nhds_unique (hux₀.tendsto_at t) ((hux.tendsto_at t).comp hφ)
  rw [hx₀] at hlim
  -- The action defect `f s = A_H(x) - A_H(u(s, ·))` is nonnegative and nonincreasing.
  have hmono : MonotoneOn A (Ioi a) := monotoneOn_hamiltonianAction_of_floer hH1 hu hper hJ hfloer
  set f : ℝ → ℝ := fun s ↦ ω.hamiltonianAction H x - A s with hfdef
  have hf0 (s : ℝ) (hs : a < s) : 0 ≤ f s :=
    sub_nonneg.2 (ge_of_tendsto hlim ((eventually_ge_atTop s).mono fun s' h ↦
      hmono hs (hs.trans_le h) h))
  have hfanti : AntitoneOn f (Ici s₀) := fun s hs s' hs' h ↦
    sub_le_sub_left (hmono (hs₀a.trans_le hs) (hs₀a.trans_le hs') h) _
  have hfle (s : ℝ) (hs : s₀ ≤ s) : f s ≤ K * ∫ t in Icc (0 : ℝ) 1, e (s, t) := by
    refine le_trans ?_ (hslice s (hs₀a.trans_le hs) fun t _ ↦
      (hclose s hs t).trans (min_le_left _ _))
    rw [abs_sub_comm]
    exact le_abs_self _
  -- Over a step of length `K` the action defect drops by half: integrating `f ≤ K ∫ e(r, ·)` over
  -- `r ∈ [s, s + K]` gives `K f (s + K) ≤ K (f s - f (s + K))`.
  have hec : ContinuousOn e (Ioi a ×ˢ univ) :=
    ω.continuousOn_floerEnergyDensity hopen (hu.of_le (by norm_num)) contDiffOn_const
      (contDiff_uncurry_cylindrical hH1).contDiffOn
  have hstep (s : ℝ) (hs : s₀ ≤ s) : f (s + K) ≤ 1 / 2 * f s := by
    have hsa : a < s := hs₀a.trans_le hs
    have hR : Icc s (s + K) ×ˢ Icc (0 : ℝ) 1 ⊆ Ioi a ×ˢ univ :=
      prod_mono (fun r hr ↦ hsa.trans_le hr.1) (subset_univ _)
    have hRint : IntegrableOn e (Icc s (s + K) ×ˢ Icc (0 : ℝ) 1) :=
      (hec.mono hR).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have hdiff := ω.integral_floerEnergyDensity_eq_hamiltonianAction_sub hH1 hopen hu
      (by linarith : s ≤ s + K) hR fun r hr ↦ by simpa using hper r (hsa.trans_le hr.1) 0
    rw [← he, Measure.volume_eq_prod,
      setIntegral_prod e (by rwa [Measure.volume_eq_prod] at hRint)] at hdiff
    have hgint : IntegrableOn (fun r ↦ ∫ t in Icc (0 : ℝ) 1, e (r, t)) (Icc s (s + K)) := by
      have h : Integrable e ((volume.restrict (Icc s (s + K))).prod
          (volume.restrict (Icc (0 : ℝ) 1))) := by
        rw [Measure.prod_restrict]
        exact hRint
      exact h.integral_prod_left
    have hlow : ∫ r in Icc s (s + K), f (s + K) / K ≤
        ∫ r in Icc s (s + K), ∫ t in Icc (0 : ℝ) 1, e (r, t) :=
      setIntegral_mono_on (integrableOn_const (by simp)) hgint measurableSet_Icc fun r hr ↦ by
        rw [div_le_iff₀' hKpos]
        exact (hfanti (mem_Ici.2 (hs.trans hr.1)) (mem_Ici.2 (by linarith)) hr.2).trans
          (hfle r (hs.trans hr.1))
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul,
      add_sub_cancel_left, mul_div_cancel₀ _ hKpos.ne'] at hlow
    have : f s - f (s + K) = A (s + K) - A s := by simp only [hfdef]; ring
    linarith
  -- Halving over every step of length `K` is exponential decay at the rate `log 2 / K`.
  obtain hdecay := fun s (hs : s₀ ≤ s) ↦ le_div_mul_exp_of_antitoneOn hKpos (by norm_num)
    (by norm_num) hfanti (hf0 s₀ hs₀a) hstep hs
  set κ : ℝ := Real.log 2 / K
  refine ⟨κ, div_pos (Real.log_pos one_lt_two) hKpos, 2 * f s₀ * Real.exp (κ * s₀),
    (eventually_ge_atTop s₀).mono fun s hs ↦ ?_⟩
  rw [setLIntegral_floerEnergyDensity_Ici_eq_of_tendsto_hamiltonianAction hH1 hu hper hJ hfloer
    (hs₀a.trans_le hs) hlim]
  refine ENNReal.ofReal_le_ofReal ((hdecay s hs).trans_eq ?_)
  have hexp : Real.log (1 / 2) / K * (s - s₀) = κ * s₀ + -(κ * s) := by
    rw [one_div, Real.log_inv]
    ring
  rw [hexp, Real.exp_add]
  ring

end TauCeti.SymplecticForm
