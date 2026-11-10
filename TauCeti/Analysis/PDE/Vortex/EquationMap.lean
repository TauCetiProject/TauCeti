/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
public import TauCeti.Analysis.PDE.Vortex.Multiplier
public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The plane vortex equation on the Sobolev scale

The framed degree-`m` plane vortex fields form the affine space
`A_m^(k+1) = (a_m, α_m) + H^(k+1)(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.framedFieldSpace`), centered at
a smooth reference pair which equals `(-i m dθ, exp (i m θ))` outside a disc. This file shows
that the vortex equation `∂bar_a α = 0`, `*iF_a = (1 - |α|²) / 8` and its deformation complex
are maps between the expected Sobolev spaces, for every integer `k ≥ 1`:

* the equation defect `TauCeti.Vortex.equation x` of a `C¹` field `x ∈ A_m^(k+1)` has its three
  real components in `H^k(ℂ)` (`equation_apply_mem_realSobolevFunctions`);
* at every `x ∈ A_m^(k+1)`, the linearized equation `d₁ = TauCeti.Vortex.linearizedEquation x`
  maps `C¹` variations in `H^(k+1)` to `H^k` (`linearizedEquation_apply_mem_realSobolevFunctions`);
* at every `x ∈ A_m^(k+1)`, the infinitesimal gauge action
  `d₀ = TauCeti.Vortex.gaugeDirection x` maps `C¹` phases in `H^(k+2)` to `H^(k+1)`
  (`gaugeDirection_mem_sobolevFields`);
* at every `x ∈ A_m^(k+1)`, the gauge-fixed operator `L_x = d₀* ⊕ d₁`
  (`TauCeti.Vortex.gaugeFixedOperator x`) and its formal adjoint `L_x*`
  (`TauCeti.Vortex.gaugeFixedAdjoint x`) map `C¹` fields in `H^(k+1)` to `H^k`
  (`gaugeFixedOperator_mem_sobolevFields`, `gaugeFixedAdjoint_mem_sobolevFields`).

The reference field is an exact vortex outside the cutoff disc (`equation_referenceField_eq_zero`).
Its equation defect is therefore smooth with compact support, and lies in every `H^s`. The exact
quadratic expansion `equation (x_m + y) = equation x_m + d₁ y + quadraticTerm y` about the reference
field (`TauCeti.Vortex.equation_add_smul`) then reduces the equation map to three kinds of terms:
first derivatives of `H^(k+1)` functions, which lie in `H^k`; products of a reference coordinate,
which is smooth with bounded derivatives, with an `H^(k+1)` function; and products of two `H^(k+1)`
functions, which lie in `H^(k+1)` because `H^(k+1)(ℂ)` is an algebra for `k ≥ 1`
(`mul_mem_realSobolevFunctions_of_mem_framedFieldSpace`).

The fields are pointwise representatives and the operators are classical differential expressions,
so the statements assume `C¹` regularity of the field, variation or phase. These are membership
statements: no bound in the Sobolev norm, smoothness of the equation map or Fredholm property is
asserted.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

namespace TauCeti.Vortex

open Complex Filter Metric TemperedDistribution
open scoped Topology ContDiff

/-! ### The equation of the reference field -/

/-- Each component of the equation defect of the reference field lies in every Sobolev space. -/
theorem equation_referenceField_apply_mem_realSobolevFunctions (f : ContDiffBump (0 : ℝ))
    (m : ℕ) (s : ℝ) (i : Fin 3) :
    (fun z ↦ equation (referenceField f m) z i) ∈ realSobolevFunctions ℂ s 2 :=
  mem_realSobolevFunctions_of_hasCompactSupport
    (contDiff_euclidean.1 (contDiff_equation (contDiff_referenceField f m)
      ENat.coe_top_add_one.le) i)
    ((hasCompactSupport_equation_referenceField f m).comp_left
      (g := fun v : EuclideanSpace ℝ (Fin 3) ↦ v i) rfl) s

/-! ### The deformation complex and the equation map -/

/-- A first derivative of a `C¹` variation in `H^(k+1)` lies in `H^k`. -/
private theorem fderiv_apply_mem_of_mem_sobolevFields {k : ℕ}
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (hyc : ContDiff ℝ 1 y)
    (b : Fin 4) (v : ℂ) :
    (fun z ↦ fderiv ℝ (fun w ↦ y w b) z v) ∈ realSobolevFunctions ℂ k 2 :=
  fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) k.cast_nonneg
    (contDiff_euclidean.1 hyc b) (mem_sobolevFields.1 hy b) v

/-- For `k ≥ 1`, a coordinate of a field of `A_m^(k+1)` times a coordinate of a variation in
`H^(k+1)` lies in `H^k`. -/
private theorem mul_apply_mem_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (a b : Fin 4) :
    (fun z ↦ x z a * y z b) ∈ realSobolevFunctions ℂ k 2 := by
  have hcast : ((k + 1 : ℕ) : ℝ) = k + 1 := Nat.cast_succ k
  rw [← hcast] at hx hy
  exact realSobolevFunctions_mono (by norm_num) (by norm_num) (by rw [hcast]; linarith)
    (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by omega) hx a
      (mem_sobolevFields.1 hy b))

/-- **The linearized equation on the Sobolev scale.** For an integer `k ≥ 1` and any field
`x ∈ A_m^(k+1)`, the linearized vortex equation `d₁ = linearizedEquation x` maps a `C¹`
variation in `H^(k+1)` to a defect with components in `H^k`. -/
theorem linearizedEquation_apply_mem_realSobolevFunctions {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (hyc : ContDiff ℝ 1 y)
    (i : Fin 3) :
    (fun z ↦ linearizedEquation x y z i) ∈ realSobolevFunctions ℂ k 2 := by
  have hd := fderiv_apply_mem_of_mem_sobolevFields hy hyc
  have hp := mul_apply_mem_of_mem_framedFieldSpace hk hx hy
  fin_cases i
  · convert add_mem (add_mem (sub_mem (hd 0 I) (hd 1 1)) (hp 2 2)) (hp 3 3) using 1
    ext z
    simp
  · convert sub_mem (sub_mem (sub_mem (sub_mem (sub_mem (hd 2 1) (hd 3 I)) (hp 0 3)) (hp 3 0))
      (hp 1 2)) (hp 2 1) using 1
    ext z
    simp only [Fin.reduceFinMk, Fin.isValue, linearizedEquation_apply_one, Pi.sub_apply]
    ring
  · convert sub_mem (sub_mem (add_mem (add_mem (add_mem (hd 3 1) (hd 2 I)) (hp 0 2)) (hp 2 0))
      (hp 1 3)) (hp 3 1) using 1
    ext z
    simp only [Fin.reduceFinMk, Fin.isValue, linearizedEquation_apply_two, Pi.add_apply,
      Pi.sub_apply]
    ring

/-- The gauge-fixing row `d₀* y = ∂₁ y₀ + ∂₂ y₁ + p y₃ - q y₂` at a field `x ∈ A_m^(k+1)`,
`k ≥ 1`, maps a `C¹` variation in `H^(k+1)` to `H^k`. -/
theorem gaugeAdjoint_mem_realSobolevFunctions {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (hyc : ContDiff ℝ 1 y) :
    gaugeAdjoint x y ∈ realSobolevFunctions ℂ k 2 := by
  have hd := fderiv_apply_mem_of_mem_sobolevFields hy hyc
  have hp := mul_apply_mem_of_mem_framedFieldSpace hk hx hy
  convert sub_mem (add_mem (add_mem (hd 0 1) (hd 1 I)) (hp 2 3)) (hp 3 2) using 1
  ext z
  simp

/-- **The gauge-fixed operator on the Sobolev scale.** For an integer `k ≥ 1` and any field
`x ∈ A_m^(k+1)`, the gauge-fixed operator `L_x = d₀* ⊕ d₁` maps a `C¹` variation in `H^(k+1)` to
`H^k(ℂ; ℝ ⊕ ℝ ⊕ ℂ)`. -/
theorem gaugeFixedOperator_mem_sobolevFields {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields (k + 1)) (hyc : ContDiff ℝ 1 y) :
    gaugeFixedOperator x y ∈ sobolevFields k := by
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [-gaugeAdjoint_def] using gaugeAdjoint_mem_realSobolevFunctions hk hx hy hyc
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hyc 0
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hyc 1
  · simpa using linearizedEquation_apply_mem_realSobolevFunctions hk hx hy hyc 2

/-- **The adjoint gauge-fixed operator on the Sobolev scale.** For an integer `k ≥ 1` and any
field `x ∈ A_m^(k+1)`, the formal adjoint `L_x*` maps a `C¹` field in `H^(k+1)(ℂ; ℝ ⊕ ℝ ⊕ ℂ)` to
a variation in `H^k`. -/
theorem gaugeFixedAdjoint_mem_sobolevFields {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : η ∈ sobolevFields (k + 1)) (hηc : ContDiff ℝ 1 η) :
    gaugeFixedAdjoint x η ∈ sobolevFields k := by
  have hd := fderiv_apply_mem_of_mem_sobolevFields hη hηc
  have hp := mul_apply_mem_of_mem_framedFieldSpace hk hx hη
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert sub_mem (add_mem (sub_mem (neg_mem (hd 0 1)) (hd 1 I)) (hp 2 3)) (hp 3 2) using 1
    ext z
    simp only [Fin.zero_eta, Fin.isValue, gaugeFixedAdjoint_apply_zero, Pi.sub_apply,
      Pi.add_apply, Pi.neg_apply]
  · convert sub_mem (sub_mem (add_mem (neg_mem (hd 0 I)) (hd 1 1)) (hp 2 2)) (hp 3 3) using 1
    ext z
    simp only [Fin.mk_one, Fin.isValue, gaugeFixedAdjoint_apply_one, Pi.sub_apply, Pi.add_apply,
      Pi.neg_apply]
  · convert add_mem (sub_mem (add_mem (sub_mem (sub_mem (neg_mem (hd 2 1)) (hd 3 I)) (hp 1 2))
      (hp 0 3)) (hp 3 0)) (hp 2 1) using 1
    ext z
    simp only [Fin.reduceFinMk, Fin.isValue, gaugeFixedAdjoint_apply_two, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply]
  · convert add_mem (add_mem (sub_mem (sub_mem (add_mem (neg_mem (hd 3 1)) (hd 2 I)) (hp 0 2))
      (hp 1 3)) (hp 2 0)) (hp 3 1) using 1
    ext z
    simp only [Fin.reduceFinMk, Fin.isValue, gaugeFixedAdjoint_apply_three, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply]

/-- The quadratic remainder of the vortex equation maps `H^s` fields, `s > 1`, to `H^s`. -/
theorem quadraticTerm_apply_mem_realSobolevFunctions {s : ℝ} (hs : 1 < s)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields s) (i : Fin 3) :
    (fun z ↦ quadraticTerm y z i) ∈ realSobolevFunctions ℂ s 2 := by
  have hp (a b : Fin 4) : (fun z ↦ y z a * y z b) ∈ realSobolevFunctions ℂ s 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) (mem_sobolevFields.1 hy a)
      (mem_sobolevFields.1 hy b)
  fin_cases i
  · convert Submodule.smul_mem _ (1 / 2 : ℝ) (add_mem (hp 2 2) (hp 3 3)) using 1
    ext z
    simp only [Fin.zero_eta, Fin.isValue, quadraticTerm_apply_zero, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul]
    ring
  · convert neg_mem (add_mem (hp 0 3) (hp 1 2)) using 1
    ext z
    simp only [Fin.mk_one, Fin.isValue, quadraticTerm_apply_one, Pi.neg_apply, Pi.add_apply]
    ring
  · convert sub_mem (hp 0 2) (hp 1 3) using 1
    ext z
    simp

/-- **The vortex equation map on the Sobolev scale.** For an integer `k ≥ 1`, the equation
defect `(*iF_a - (1 - |α|²) / 8, Re ∂bar_a α, Im ∂bar_a α)` of a `C¹` field `x ∈ A_m^(k+1)` has
its three components in `H^k`. -/
theorem equation_apply_mem_realSobolevFunctions {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 ≤ k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1))
    (hxc : ContDiff ℝ 1 x) (i : Fin 3) :
    (fun z ↦ equation x z i) ∈ realSobolevFunctions ℂ k 2 := by
  set y := x - referenceField f m
  have hy : y ∈ sobolevFields (k + 1) := mem_framedFieldSpace.1 hx
  have hyc : ContDiff ℝ 1 y := hxc.sub ((contDiff_referenceField f m).of_le (by simp))
  -- Expand the equation exactly about the reference field.
  have hexp (z : ℂ) : equation x z = equation (referenceField f m) z +
      linearizedEquation (referenceField f m) y z + quadraticTerm y z := by
    have h := equation_add_smul (z := z)
      (fun j ↦ (contDiff_euclidean.1 (contDiff_referenceField f m) j).differentiable
        (by simp) z)
      (fun j ↦ (contDiff_euclidean.1 hyc j).differentiable one_ne_zero z) 1
    simpa only [one_smul, one_pow, y, add_sub_cancel] using h
  have hq := realSobolevFunctions_mono (p := 2) (by norm_num) (by norm_num)
    (by linarith : (k : ℝ) ≤ k + 1)
    (quadraticTerm_apply_mem_realSobolevFunctions (by norm_cast; omega) hy i)
  convert add_mem (add_mem (equation_referenceField_apply_mem_realSobolevFunctions f m k i)
    (linearizedEquation_apply_mem_realSobolevFunctions hk
      (referenceField_mem_framedFieldSpace f m _) hy hyc i)) hq using 1
  ext z
  simp [hexp z]

/-- **The infinitesimal gauge action on the Sobolev scale.** For an integer `k ≥ 1` and any
field `x ∈ A_m^(k+1)`, the infinitesimal gauge action `d₀ = gaugeDirection x` maps a `C¹` phase
in `H^(k+2)` to a variation in `H^(k+1)`. -/
theorem gaugeDirection_mem_sobolevFields {f : ContDiffBump (0 : ℝ)} {m k : ℕ} (hk : 1 ≤ k)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m (k + 1)) {g : ℂ → ℝ}
    (hg : g ∈ realSobolevFunctions ℂ (k + 2) 2) (hgc : ContDiff ℝ 1 g) :
    gaugeDirection x g ∈ sobolevFields (k + 1) := by
  have hcast : ((k + 1 : ℕ) : ℝ) = k + 1 := Nat.cast_succ k
  have hd (v : ℂ) : (fun z ↦ fderiv ℝ g z v) ∈ realSobolevFunctions ℂ (k + 1) 2 :=
    fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) (by positivity) hgc
      (by convert hg using 2; ring) v
  have hx' : x ∈ framedFieldSpace f m ((k + 1 : ℕ) : ℝ) := by rwa [hcast]
  have hg' : g ∈ realSobolevFunctions ℂ ((k + 1 : ℕ) : ℝ) 2 :=
    realSobolevFunctions_mono (by norm_num) (by norm_num) (by rw [hcast]; linarith) hg
  have hp (a : Fin 4) : (fun z ↦ x z a * g z) ∈ realSobolevFunctions ℂ (k + 1) 2 :=
    hcast ▸ mul_mem_realSobolevFunctions_of_mem_framedFieldSpace (by omega) hx' a hg'
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert neg_mem (hd 1) using 1
    ext z
    simp
  · convert neg_mem (hd I) using 1
    ext z
    simp
  · convert neg_mem (hp 3) using 1
    ext z
    simp [mul_comm]
  · convert hp 2 using 1
    ext z
    simp [mul_comm]

end TauCeti.Vortex
