/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The plane vortex equation on the affine Sobolev field space

In the real coordinates `x = (b₁, b₂, p, q)` of `TauCeti.Vortex.equation`, the vortex equation,
its linearization `d₁ = linearizedEquation x`, the infinitesimal gauge action
`d₀ = gaugeDirection x` and the gauge-fixed operator `L_x = d₀* ⊕ d₁` with its formal adjoint
are classical first-order differential expressions. This file proves that, for every natural
`k ≥ 1`, they act on the Sobolev scale of framed degree-`m` fields
`A_m^s = x_m + H^s(ℂ; ℝ⁴)` (`TauCeti.Vortex.framedFieldSpace`):

* the equation maps `A_m^(k+1)` to defects in `H^k(ℂ; ℝ ⊕ ℂ)`
  (`TauCeti.Vortex.equation_apply_mem_realSobolevFunctions`);
* at every field `x` of `A_m^(k+1)` the deformation complex has the orders
  `H^(k+2)(ℂ; ℝ) → H^(k+1)(ℂ; ℝ⁴) → H^k(ℂ; ℝ ⊕ ℂ)`
  (`TauCeti.Vortex.gaugeDirection_mem_sobolevFields`,
  `TauCeti.Vortex.linearizedEquation_apply_mem_realSobolevFunctions`), and `L_x` and `L_x*` map
  `H^(k+1)(ℂ; ℝ⁴)` to `H^k(ℂ; ℝ⁴)` (`TauCeti.Vortex.gaugeFixedOperator_mem_sobolevFields`,
  `TauCeti.Vortex.gaugeFixedAdjoint_mem_sobolevFields`).

The expressions differentiate the given representative of a field pointwise, so the statements
concern `C¹` representatives. That every field of sufficiently high order has a `C¹`
representative is not proved here.

The base point of the affine space is the smooth reference field `x_m`, equal to
`(-i m dθ, (z / |z|)^m)` outside a disc. There it solves the vortex equation
(`TauCeti.Vortex.equation_referenceField_eq_zero`), so its defect is smooth with compact
support (`TauCeti.Vortex.hasCompactSupport_equation_referenceField`). For `x = x_m + y` the equation expands exactly as
`equation x = equation x_m + d₁ y + quadraticTerm y` (`TauCeti.Vortex.equation_add_smul`). The
linear term involves the derivatives of `y` and the products of the coordinates of `x_m` with
those of `y`. These coordinates do not decay, but all their derivatives are bounded, so they
multiply `H^k` into itself. The products of two Sobolev coordinates are controlled by the algebra
property of `H^s(ℂ)`, `s > 1`; this is where `k ≥ 1` is used.

All statements are memberships. Boundedness and smoothness of the completed maps, the weak
equation and elliptic regularity are not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Metric TemperedDistribution
open scoped ContDiff Topology

/-! ### The defect of the reference field -/

/-- Every coordinate of the defect of the reference field is a smooth compactly supported
function, hence lies in every Sobolev space. -/
theorem equation_referenceField_apply_mem_realSobolevFunctions (f : ContDiffBump (0 : ℝ))
    (m : ℕ) (i : Fin 3) (s : ℝ) :
    (fun z ↦ equation (referenceField f m) z i) ∈ realSobolevFunctions ℂ s 2 :=
  mem_realSobolevFunctions_of_hasCompactSupport
    (contDiff_euclidean.1 (contDiff_equation (contDiff_referenceField f m) le_top) i)
    ((hasCompactSupport_equation_referenceField f m).comp_left
      (g := fun v : EuclideanSpace ℝ (Fin 3) ↦ v i) rfl) s

/-! ### Mapping properties on the Sobolev scale -/

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The products `x_i y_j` of a framed field of order `k + 1` and a Sobolev field of order
`k + 1` have order `k + 1`, in particular order `k`. -/
private theorem mul_mem_realSobolevFunctions_of_mem_sobolevFields (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hy : y ∈ sobolevFields (k + 1)) (i j : Fin 4) :
    (fun z ↦ x z i * y z j) ∈ realSobolevFunctions ℂ k 2 := by
  have hx' : x ∈ framedFieldSpace f m ((k + 1 : ℕ) : ℝ) := by rwa [Nat.cast_add_one]
  have hyj : (fun z ↦ y z j) ∈ realSobolevFunctions ℂ ((k + 1 : ℕ) : ℝ) 2 := by
    rw [Nat.cast_add_one]
    exact mem_sobolevFields.1 hy j
  exact realSobolevFunctions_mono (by norm_num) (by norm_num) (by exact_mod_cast Nat.le_succ k)
    (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by omega) hx' i hyj)

/-- **The linearized vortex equation on the Sobolev scale.** For `k ≥ 1`, at a field of
`A_m^(k+1)`, the linearization `d₁` maps `C¹` fields of order `k + 1` to defects of order `k`. -/
theorem linearizedEquation_apply_mem_realSobolevFunctions (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hy : y ∈ sobolevFields (k + 1))
    (hy₁ : ContDiff ℝ 1 y) (i : Fin 3) :
    (fun z ↦ linearizedEquation x y z i) ∈ realSobolevFunctions ℂ k 2 := by
  have D := fderiv_apply_mem_realSobolevFunctions_of_mem_sobolevFields (Nat.cast_nonneg k) hy hy₁
  have P := mul_mem_realSobolevFunctions_of_mem_sobolevFields hk hx hy
  fin_cases i
  · convert add_mem (add_mem (sub_mem (D 0 I) (D 1 1)) (P 2 2)) (P 3 3) using 1
    ext z
    simp
  · convert sub_mem (sub_mem (sub_mem (sub_mem (sub_mem (D 2 1) (D 3 I)) (P 0 3)) (P 3 0))
      (P 1 2)) (P 2 1) using 1
    ext z
    simp only [Fin.mk_one, linearizedEquation_apply_one, Pi.sub_apply]
    ring
  · convert sub_mem (sub_mem (add_mem (add_mem (add_mem (D 3 1) (D 2 I)) (P 0 2)) (P 2 0))
      (P 1 3)) (P 3 1) using 1
    ext z
    simp only [Fin.reduceFinMk, linearizedEquation_apply_two, Pi.sub_apply, Pi.add_apply]
    ring

/-- The quadratic remainder of the vortex equation maps Sobolev fields of order `s > 1` to
defects of order `s`. -/
theorem quadraticTerm_apply_mem_realSobolevFunctions {s : ℝ} (hs : 1 < s)
    (hy : y ∈ sobolevFields s) (i : Fin 3) :
    (fun z ↦ quadraticTerm y z i) ∈ realSobolevFunctions ℂ s 2 := by
  have P (a b : Fin 4) : (fun z ↦ y z a) * (fun z ↦ y z b) ∈ realSobolevFunctions ℂ s 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs)
      (mem_sobolevFields.1 hy a) (mem_sobolevFields.1 hy b)
  fin_cases i
  · convert Submodule.smul_mem _ (1 / 2 : ℝ) (add_mem (P 2 2) (P 3 3)) using 1
    ext z
    simp only [Fin.zero_eta, quadraticTerm_apply_zero, Pi.smul_apply, Pi.add_apply,
      Pi.mul_apply, smul_eq_mul]
    ring
  · convert neg_mem (add_mem (P 0 3) (P 1 2)) using 1
    ext z
    simp only [Fin.mk_one, quadraticTerm_apply_one, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
    ring
  · convert sub_mem (P 0 2) (P 1 3) using 1
    ext z
    simp

/-- **The vortex equation on the Sobolev scale.** For `k ≥ 1`, the vortex equation maps the
`C¹` fields of the affine space `A_m^(k+1)` to defects of order `k`: each of its three
coordinates lies in `H^k(ℂ)`. -/
theorem equation_apply_mem_realSobolevFunctions (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hx₁ : ContDiff ℝ 1 x) (i : Fin 3) :
    (fun z ↦ equation x z i) ∈ realSobolevFunctions ℂ k 2 := by
  -- Expand `x = x_m + y` about the reference field: the defect of `x_m` is compactly supported,
  -- the linear term has order `k`, and the quadratic term has order `k + 1`.
  set y := x - referenceField f m with hy_def
  have hy : y ∈ sobolevFields (k + 1) := mem_framedFieldSpace.1 hx
  have href : ContDiff ℝ ∞ (referenceField f m) := contDiff_referenceField f m
  have hy₁ : ContDiff ℝ 1 y := hx₁.sub (href.of_le (by exact_mod_cast le_top))
  have hdiff {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : ContDiff ℝ 1 u) (z : ℂ) (j : Fin 4) :
      DifferentiableAt ℝ (fun w ↦ u w j) z :=
    (contDiff_euclidean.1 hu j).differentiable one_ne_zero z
  have hexp (z : ℂ) : equation x z = equation (referenceField f m) z +
      linearizedEquation (referenceField f m) y z + quadraticTerm y z := by
    have h := equation_add_smul (hdiff (href.of_le (by exact_mod_cast le_top)) z) (hdiff hy₁ z) 1
    rwa [one_smul, one_smul, one_pow, one_smul, hy_def, add_sub_cancel] at h
  have hQ := realSobolevFunctions_mono (by norm_num) (by norm_num) (by linarith)
    (quadraticTerm_apply_mem_realSobolevFunctions
      (by linarith [(by exact_mod_cast hk : (1 : ℝ) ≤ k)]) hy i)
  convert add_mem (add_mem (equation_referenceField_apply_mem_realSobolevFunctions f m i k)
    (linearizedEquation_apply_mem_realSobolevFunctions hk
      (referenceField_mem_framedFieldSpace f m _) hy hy₁ i)) hQ using 1
  ext z
  simp [hexp z]

/-- **The gauge-fixing row on the Sobolev scale.** For `k ≥ 1`, at a field of `A_m^(k+1)`, the
formal adjoint `d₀*` of the infinitesimal gauge action maps `C¹` fields of order `k + 1` to
functions of order `k`. -/
theorem gaugeAdjoint_mem_realSobolevFunctions (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hy : y ∈ sobolevFields (k + 1))
    (hy₁ : ContDiff ℝ 1 y) :
    gaugeAdjoint x y ∈ realSobolevFunctions ℂ k 2 := by
  have D := fderiv_apply_mem_realSobolevFunctions_of_mem_sobolevFields (Nat.cast_nonneg k) hy hy₁
  have P := mul_mem_realSobolevFunctions_of_mem_sobolevFields hk hx hy
  convert sub_mem (add_mem (add_mem (D 0 1) (D 1 I)) (P 2 3)) (P 3 2) using 1
  ext z
  simp

/-- **The gauge-fixed operator on the Sobolev scale.** For `k ≥ 1`, at a field of `A_m^(k+1)`,
`L_x = d₀* ⊕ d₁` maps `C¹` fields of order `k + 1` to fields of order `k`. -/
theorem gaugeFixedOperator_mem_sobolevFields (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) (hy : y ∈ sobolevFields (k + 1))
    (hy₁ : ContDiff ℝ 1 y) :
    gaugeFixedOperator x y ∈ sobolevFields k := by
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [-gaugeAdjoint_def] using gaugeAdjoint_mem_realSobolevFunctions hk hx hy hy₁
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hy₁ 0
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hy₁ 1
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hy₁ 2

/-- **The formal adjoint of the gauge-fixed operator on the Sobolev scale.** For `k ≥ 1`, at a
field of `A_m^(k+1)`, `L_x*` maps `C¹` fields of order `k + 1` to fields of order `k`. -/
theorem gaugeFixedAdjoint_mem_sobolevFields (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : η ∈ sobolevFields (k + 1)) (hη₁ : ContDiff ℝ 1 η) :
    gaugeFixedAdjoint x η ∈ sobolevFields k := by
  have D := fderiv_apply_mem_realSobolevFunctions_of_mem_sobolevFields (Nat.cast_nonneg k) hη hη₁
  have P := mul_mem_realSobolevFunctions_of_mem_sobolevFields hk hx hη
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert sub_mem (add_mem (sub_mem (neg_mem (D 0 1)) (D 1 I)) (P 2 3)) (P 3 2) using 1
    ext z
    simp
  · convert sub_mem (sub_mem (add_mem (neg_mem (D 0 I)) (D 1 1)) (P 2 2)) (P 3 3) using 1
    ext z
    simp
  · convert add_mem (sub_mem (add_mem (sub_mem (sub_mem (neg_mem (D 2 1)) (D 3 I)) (P 1 2))
      (P 0 3)) (P 3 0)) (P 2 1) using 1
    ext z
    simp
  · convert add_mem (add_mem (sub_mem (sub_mem (add_mem (neg_mem (D 3 1)) (D 2 I)) (P 0 2))
      (P 1 3)) (P 2 0)) (P 3 1) using 1
    ext z
    simp

/-- **The infinitesimal gauge action on the Sobolev scale.** For `k ≥ 1`, at a field of
`A_m^(k+1)`, the infinitesimal gauge action `d₀` maps `C¹` phases of order `k + 2` to fields of
order `k + 1`. -/
theorem gaugeDirection_mem_sobolevFields (hk : 1 ≤ k)
    (hx : x ∈ framedFieldSpace f m (k + 1)) {g : ℂ → ℝ}
    (hg : g ∈ realSobolevFunctions ℂ (k + 2) 2) (hg₁ : ContDiff ℝ 1 g) :
    gaugeDirection x g ∈ sobolevFields (k + 1) := by
  have hx' : x ∈ framedFieldSpace f m ((k + 1 : ℕ) : ℝ) := by rwa [Nat.cast_add_one]
  have hg' : g ∈ realSobolevFunctions ℂ ((k + 1 : ℕ) : ℝ) 2 :=
    realSobolevFunctions_mono (by norm_num) (by norm_num) (by push_cast; linarith) hg
  have D (v : ℂ) : (fun z ↦ fderiv ℝ g z v) ∈ realSobolevFunctions ℂ (k + 1) 2 :=
    fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) (by positivity) hg₁
      (by convert hg using 2; ring) v
  have P (i : Fin 4) : (fun z ↦ x z i * g z) ∈ realSobolevFunctions ℂ (k + 1) 2 := by
    simpa only [Nat.cast_add_one] using
      mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by omega) hx' i hg'
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert neg_mem (D 1) using 1
    ext z
    simp
  · convert neg_mem (D I) using 1
    ext z
    simp
  · convert neg_mem (P 3) using 1
    ext z
    simp [mul_comm]
  · convert P 2 using 1
    ext z
    simp [mul_comm]

end TauCeti.Vortex
