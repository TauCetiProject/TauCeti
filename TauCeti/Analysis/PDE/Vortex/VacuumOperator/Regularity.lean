/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Sobolev regularity of vortex deformations of the vacuum

For a field `vacuum + ψ`, the vacuum operator `L₀ ψ = gaugeFixedOperator vacuumField ψ` plus the
quadratic remainder of the vortex equation is the gauge-fixing row `d₀* ψ` followed by the three
vortex defects of `vacuum + ψ` (`gaugeFixedOperator_vacuumField_add_quadraticTerm`). The quadratic
remainder is a sum of products of coordinates of `ψ`. Products of bounded functions stay in `L²`
and in `H¹`, and `H^k(ℂ)` is an algebra for `k ≥ 2`, so the quadratic remainder of a smooth bounded
`ψ ∈ H^k` lies in `H^k`.

A `C¹` field `ψ` is a weak solution of `L₀ ψ = g` with `g` its classical image, by integration by
parts against compactly supported test fields
(`integral_inner_gaugeFixedOperator_of_hasCompactSupport_right`). Elliptic regularity of the
vacuum operator for weak solutions
(`mem_sobolevFields_add_one_of_integral_inner_gaugeFixedAdjoint_vacuumField_eq`) then gives a
bootstrap: a smooth bounded square-integrable `ψ` whose gauge-fixing row and vortex defects lie in
every `H^k` lies itself in every `H^k`
(`mem_sobolevFields_of_forall_mem_sobolevFields_equation`). This applies to the deformation of the
vacuum of a plane vortex in its winding end trivialization, cut off near the origin, where the
gauge-fixing row and the vortex defects vanish outside a compact set.

## Main results

* `TauCeti.Vortex.gaugeFixedOperator_vacuumField_add_quadraticTerm`: the gauge-fixed vortex
  equation expanded about the vacuum.
* `TauCeti.Vortex.mem_sobolevFields_of_forall_mem_sobolevFields_equation`: Sobolev regularity of
  all orders for smooth bounded gauge-fixed vortex deformations of the vacuum in `L²`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1 (elliptic regularity on the
  Sobolev scale).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory TemperedDistribution
open scoped ContDiff

/-- **The gauge-fixed vortex equation about the vacuum.** For a field `vacuum + ψ`, the vacuum
operator `L₀ ψ` plus the quadratic remainder of the vortex equation is the gauge-fixing row
`d₀* ψ` followed by the three vortex defects of `vacuum + ψ`. -/
theorem gaugeFixedOperator_vacuumField_add_quadraticTerm {ψ : ℂ → EuclideanSpace ℝ (Fin 4)}
    {z : ℂ} (hψ : DifferentiableAt ℝ ψ z) :
    gaugeFixedOperator vacuumField ψ z +
        !₂[0, quadraticTerm ψ z 0, quadraticTerm ψ z 1, quadraticTerm ψ z 2] =
      !₂[gaugeAdjoint vacuumField ψ z, equation (vacuumField + ψ) z 0,
        equation (vacuumField + ψ) z 1, equation (vacuumField + ψ) z 2] := by
  have hψi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ ψ w i) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hψ
  have hvac (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ vacuumField w i) z :=
    (contDiff_euclidean.1 (contDiff_vacuumField (n := 1)) i).differentiable one_ne_zero z
  have h := equation_add_smul hvac hψi 1
  rw [one_smul, one_smul, one_pow, one_smul, equation_vacuumField, zero_add] at h
  ext i
  fin_cases i <;> simp [h, gaugeFixedOperator_apply_zero, gaugeFixedOperator_apply_one,
    gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three]

/-- The quadratic remainder of the vortex equation, a sum of products of coordinates, lies in
`H^k` for a smooth bounded field in `H^k`: below order two by the boundedness of the factors, from
order two on because `H^k(ℂ)` is an algebra. -/
private theorem quadraticTerm_mem_sobolevFields {ψ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hψ : ContDiff ℝ ∞ ψ) {B : ℝ} (hB : ∀ z, ‖ψ z‖ ≤ B) {k : ℕ} (hk : ψ ∈ sobolevFields k) :
    (fun z ↦ !₂[0, quadraticTerm ψ z 0, quadraticTerm ψ z 1, quadraticTerm ψ z 2]) ∈
      sobolevFields k := by
  have hc (i : Fin 4) : (fun z ↦ ψ z i) ∈ realSobolevFunctions ℂ k 2 := mem_sobolevFields.1 hk i
  have hcd (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ ψ z i) := contDiff_euclidean.1 hψ i
  have hcB (i : Fin 4) (z : ℂ) : |ψ z i| ≤ B :=
    (Real.norm_eq_abs (ψ z i) ▸ PiLp.norm_apply_le (ψ z) i).trans (hB z)
  have hmul (i j : Fin 4) :
      (fun z ↦ ψ z i) * (fun z ↦ ψ z j) ∈ realSobolevFunctions ℂ k 2 := by
    rcases k with _ | _ | k
    · simpa using mul_mem_realSobolevFunctions_zero_of_bounded (hcd i).continuous (hcB i)
        (by simpa using hc j)
    · simpa using mul_mem_realSobolevFunctions_one_of_bounded ((hcd i).of_le (by simp))
        ((hcd j).of_le (by simp)) (hcB i) (hcB j) (by simpa using hc i) (by simpa using hc j)
    · refine mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul ?_) (hc i) (hc j)
      push_cast
      linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert zero_mem (realSobolevFunctions ℂ k 2) using 1
    funext z
    simp
  · convert Submodule.smul_mem _ (1 / 2 : ℝ) (add_mem (hmul 2 2) (hmul 3 3)) using 1
    funext z
    simp
    ring
  · convert sub_mem (neg_mem (hmul 0 3)) (hmul 1 2) using 1
    funext z
    simp
  · convert sub_mem (hmul 0 2) (hmul 1 3) using 1
    funext z
    simp

/-- **Regularity of gauge-fixed vortex deformations of the vacuum.** Let `ψ` be a smooth bounded
field in `L²` such that the gauge-fixing row `d₀* ψ` and the vortex defects of `vacuum + ψ` lie in
every `H^k`, for instance because they vanish outside a compact set. Then `ψ` lies in every
`H^k`. -/
theorem mem_sobolevFields_of_forall_mem_sobolevFields_equation
    {ψ : ℂ → EuclideanSpace ℝ (Fin 4)} (hψ : ContDiff ℝ ∞ ψ) {B : ℝ} (hB : ∀ z, ‖ψ z‖ ≤ B)
    (h₀ : ψ ∈ sobolevFields 0)
    (hE : ∀ k : ℕ, (fun z ↦ !₂[gaugeAdjoint vacuumField ψ z, equation (vacuumField + ψ) z 0,
      equation (vacuumField + ψ) z 1, equation (vacuumField + ψ) z 2]) ∈ sobolevFields k)
    (k : ℕ) : ψ ∈ sobolevFields k := by
  induction k with
  | zero => simpa using h₀
  | succ k ih =>
    have hL : gaugeFixedOperator vacuumField ψ ∈ sobolevFields k := by
      convert sub_mem (hE k) (quadraticTerm_mem_sobolevFields hψ hB ih) using 1
      funext z
      rw [Pi.sub_apply, ← gaugeFixedOperator_vacuumField_add_quadraticTerm
        (hψ.differentiable (by simp) z), add_sub_cancel_right]
    -- Integrating by parts, `ψ` is a weak `L²` solution of `L₀ ψ = g` for its classical image
    -- `g ∈ H^k`.
    exact_mod_cast mem_sobolevFields_add_one_of_integral_inner_gaugeFixedAdjoint_vacuumField_eq
      (memLp_of_mem_sobolevFields ih) hL fun η hη hc ↦
        (integral_inner_gaugeFixedOperator_of_hasCompactSupport_right
          (contDiff_vacuumField (n := 0)).continuous (hψ.of_le (by simp)) (hη.of_le (by simp))
          hc).symm

end TauCeti.Vortex
