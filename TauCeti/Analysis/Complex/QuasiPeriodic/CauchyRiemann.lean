/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.QuasiPeriodic.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

/-!
# Periodic solutions of `∂bar + c` on a torus

Let `L ⊆ ℂ` be a lattice and `c ∈ ℂ`. In a periodic unitary frame, the Cauchy–Riemann operator of
a flat unitary line bundle on the torus `ℂ ⧸ L` is `∂bar + c` with a constant coefficient `c`. This
file shows that, when the holonomy of that line has infinite order, the operator `∂bar + c` has no
nonzero periodic solution on any finite covering torus `ℂ ⧸ L'`, `L' ≤ L` of finite index
(`TauCeti.eq_zero_of_conjWirtingerDeriv_add_mul_eq_zero_of_irrational`).

Multiplying by the twisted exponential `e(z) = exp (c conj z - conj c z)`, of modulus one, turns a
solution `v` of `∂bar v + c v = 0` into a holomorphic map `e v`, since `∂bar e = c e`
(`TauCeti.conjWirtingerDeriv_cexp_mul_sub_conj_mul_conj`). If `v` is `L'`-periodic, then `e v` is
quasi-periodic, `(e v)(z + ω) = exp (2i Im (c conj ω)) (e v)(z)`
(`TauCeti.cexp_mul_add_sub_conj_mul_conj_add`), so it is a holomorphic section of the flat line of
holonomy `exp (2πi Im (c conj ω) / π)` pulled back to `ℂ ⧸ L'`. When `Im (c conj ω₀) / π` is
irrational for some `ω₀ ∈ L`, that holonomy has infinite order and the section vanishes
(`Differentiable.eq_zero_of_add_eq_fourierChar_pow_smul`).

This is the condition that a square-zero torus whose normal operator is `∂bar + c` in a periodic
frame is nondegenerate on all its finite unbranched covers. It holds for instance whenever the
holonomy of the flat normal connection is irrational along one period of the lattice.

## Main results

* `TauCeti.eq_zero_of_conjWirtingerDeriv_add_mul_eq_zero_of_irrational`: if `Im (c conj ω₀) / π`
  is irrational for some `ω₀ ∈ L`, every periodic solution of `∂bar v + c v = 0` on a finite
  covering torus of `ℂ ⧸ L` vanishes.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893 (square-zero tori and their finite covers).
-/

public section

open Complex ComplexConjugate Real

namespace TauCeti

/-- **No periodic solutions of `∂bar + c` on finite covers.** Let `L ⊆ ℂ` be a lattice and `c ∈ ℂ`
such that `Im (c conj ω₀) / π` is irrational for some `ω₀ ∈ L`, so that the flat unitary line of
the operator `∂bar + c` has holonomy of infinite order. Then for every subgroup `L' ≤ L` of finite
index, every `L'`-periodic, real-differentiable solution of `∂bar v + c v = 0` on `ℂ` vanishes. -/
theorem eq_zero_of_conjWirtingerDeriv_add_mul_eq_zero_of_irrational {L : Submodule ℤ ℂ}
    [DiscreteTopology L] [IsZLattice ℝ L] {c ω₀ : ℂ} (hω₀L : ω₀ ∈ L)
    (hω₀ : Irrational ((c * conj ω₀).im / π)) {L' : AddSubgroup ℂ} (hL' : L' ≤ L.toAddSubgroup)
    (hidx : L'.relIndex L.toAddSubgroup ≠ 0) {v : ℂ → ℂ} (hv : Differentiable ℝ v)
    (heq : ∀ z, conjWirtingerDeriv v z 1 + c * v z = 0)
    (hper : ∀ ω ∈ L', ∀ z, v (z + ω) = v z) : v = 0 := by
  -- The twisted exponential `e z = exp (a z - conj a conj z)`, `a = -conj c`, has `∂bar e = c e`.
  set a : ℂ := -conj c with ha
  set e : ℂ → ℂ := fun z ↦ cexp (a * z - conj a * conj z) with he
  have he_diff : Differentiable ℝ e :=
    (contDiff_cexp_mul_sub_conj_mul_conj (n := 1) a).differentiable one_ne_zero
  -- So `e v` is holomorphic.
  have hhol : Differentiable ℂ fun z ↦ e z * v z := fun z ↦ by
    rw [differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (f := fun z ↦ e z * v z)
      ((he_diff z).mul (hv z)), conjWirtingerDeriv_fun_mul (he_diff z) (hv z)]
    simp only [add_apply, smul_apply, smul_eq_mul, he,
      conjWirtingerDeriv_cexp_mul_sub_conj_mul_conj]
    rw [ha, map_neg, conj_conj]
    linear_combination cexp (-conj c * z - -c * conj z) * heq z
  -- The holonomy of the flat line of `e v` along `ω` is `exp (2πi θ ω)`.
  let θ : L →+ ℝ :=
    { toFun := fun ω ↦ (c * conj (ω : ℂ)).im / π
      map_zero' := by simp
      map_add' := fun ω ω' ↦ by simp [mul_add, add_div] }
  have hθ : Irrational (θ ⟨ω₀, hω₀L⟩) := by simpa [θ] using hω₀
  have hL'' : L'.toIntSubmodule ≤ L := by
    rw [← Submodule.toAddSubgroup_toIntSubmodule L]
    exact AddSubgroup.toIntSubmodule.monotone hL'
  have hzero := hhol.eq_zero_of_add_eq_fourierChar_pow_smul (L := L) (c := θ) hθ hL''
    (by simpa using hidx) one_ne_zero fun z ω hω ↦ by
      simp only [he, cexp_mul_add_sub_conj_mul_conj_add, hper ω hω z, pow_one,
        Real.fourierChar_apply, smul_eq_mul, ← mul_assoc]
      congr 3
      simp only [θ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ha]
      push_cast
      field_simp
      simp [mul_comm]
  funext z
  simpa [he, Complex.exp_ne_zero] using congrFun hzero z

end TauCeti
