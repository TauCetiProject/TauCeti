/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.RotatingLineBoundary

/-!
# The adjoint problem on the disc with boundary values on a rotating line

Fix an integer `k` and consider the Cauchy–Riemann operator `∂/∂(conj z)` on the closed unit disc
with boundary values on the rotating line `w ^ (k / 2) ℝ`, whose kernel is
`TauCeti.unitDiscCauchyRiemannKernel k`. By the duality of McDuff–Salamon (C.1.3), its cokernel is
the space of adjoint solutions: `(0,1)`-forms `η = conj g d(conj z)` with `g` holomorphic on the
open disc, continuous up to the boundary, and with `η(∂_θ)` on the same line `w ^ (k / 2) ℝ`
along the unit circle. Since `d(conj z)(∂_θ) = -I conj w` at `w = e^{iθ}`, the adjoint boundary
condition reads

`v = w ^ k * conj v` for `v = -I * conj w * conj (g w)`, `‖w‖ = 1`.

The pointwise computation `TauCeti.adjoint_boundary_iff` shows that this holds exactly when
`I * g w` lies on the line `w ^ ((-k - 2) / 2) ℝ`. So `g` is an adjoint solution for the index
`k` exactly when `I • g` is a solution of the original problem for the index `-k - 2`
(`TauCeti.mem_unitDiscAdjointKernel_iff_smul_mem`), and the adjoint kernel has real dimension
`max (-1 - k) 0` (`TauCeti.finrank_unitDiscAdjointKernel`). Combined with the kernel dimension
`max (k + 1) 0` this gives index `k + 1` for every `k`
(`TauCeti.finrank_unitDiscCauchyRiemannKernel_sub_finrank_unitDiscAdjointKernel`), which is
`χ(D) + μ` for the disc with a boundary loop of Maslov index `k`. For `k ≥ -1` the adjoint kernel
vanishes (`TauCeti.unitDiscAdjointKernel_eq_bot`).

The identification of the adjoint kernel with the cokernel of the Sobolev realization of the
Cauchy–Riemann operator needs the bordered Fredholm theory and is not treated here.

## Main definitions

* `TauCeti.unitDiscAdjointKernel k`: the real subspace of functions `g` on the closed unit disc
  that are restrictions of functions holomorphic on the open disc and continuous on its closure,
  satisfying the adjoint boundary condition on the unit circle.

## Main results

* `TauCeti.adjoint_boundary_iff`: the adjoint boundary condition at a point of the unit circle is
  the boundary condition of index `-k - 2` for `I` times the value.
* `TauCeti.mem_unitDiscAdjointKernel_iff`: membership in the adjoint kernel, unfolded.
* `TauCeti.mem_unitDiscAdjointKernel_iff_smul_mem`: `g` is an adjoint solution for the index `k`
  if and only if `I • g ∈ unitDiscCauchyRiemannKernel (-k - 2)`.
* `TauCeti.finrank_unitDiscAdjointKernel`: the adjoint kernel has real dimension
  `(-k - 1).toNat`.
* `TauCeti.finrank_unitDiscCauchyRiemannKernel_sub_finrank_unitDiscAdjointKernel`: the index
  identity `dim ker - dim coker = k + 1`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the duality (C.1.3) and Theorem C.1.10).
-/

public section

namespace TauCeti

open Complex Metric Module Set
open scoped ComplexConjugate

variable {k : ℤ}

/-- **The adjoint boundary condition.** At a point `w` of the unit circle, the value
`v = -I * conj w * conj c` of the form `conj c d(conj z)` on `∂_θ` lies on the line
`w ^ (k / 2) ℝ` exactly when `I * c` lies on the line `w ^ ((-k - 2) / 2) ℝ`. -/
theorem adjoint_boundary_iff {w : ℂ} (hw : ‖w‖ = 1) (c : ℂ) :
    -I * conj w * conj c = w ^ k * conj (-I * conj w * conj c) ↔
      I * c = w ^ (-k - 2) * conj (I * c) := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have e₁ : conj w * w = 1 := by
    rw [conj_mul', hw]
    norm_num
  have e₂ : w ^ (-k - 2) * w ^ k * w ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hw0, ← zpow_add₀ hw0, Nat.cast_ofNat,
      show -k - 2 + k + 2 = 0 by ring, zpow_zero]
  simp only [map_mul, map_neg, conj_I, conj_conj]
  constructor
  · intro h
    linear_combination (-(w ^ (-k - 2)) * w) * h - I * w ^ (-k - 2) * conj c * e₁ - I * c * e₂
  · intro h
    linear_combination (-(w ^ k) * w) * h + I * conj c * conj w * e₂ -
      I * conj c * w ^ k * w ^ (-k - 2) * w * e₁

/-- Multiplication by `I`, as a real-linear automorphism of the functions on the closed disc. -/
private noncomputable def mulI : (closedBall (0 : ℂ) 1 → ℂ) ≃ₗ[ℝ] (closedBall (0 : ℂ) 1 → ℂ) :=
  (LinearEquiv.smulOfNeZero ℂ _ I I_ne_zero).restrictScalars ℝ

private theorem mulI_apply (g : closedBall (0 : ℂ) 1 → ℂ) : mulI g = I • g := rfl

/-- The kernel of the adjoint problem on the closed unit disc for the boundary condition of
Maslov index `k`: the functions `g` on the closed unit disc that are restrictions of functions
`u` holomorphic on the open disc and continuous on its closure with
`-I * conj w * conj (u w) = w ^ k * conj (-I * conj w * conj (u w))` for `‖w‖ = 1`
(`TauCeti.mem_unitDiscAdjointKernel_iff`). It is defined as the preimage of
`TauCeti.unitDiscCauchyRiemannKernel (-k - 2)` under multiplication by `I`, which is the content
of `TauCeti.adjoint_boundary_iff`. -/
noncomputable def unitDiscAdjointKernel (k : ℤ) : Submodule ℝ (closedBall (0 : ℂ) 1 → ℂ) :=
  (unitDiscCauchyRiemannKernel (-k - 2)).map (mulI.symm : _ →ₗ[ℝ] _)

variable {g : closedBall (0 : ℂ) 1 → ℂ}

/-- A function `g` is an adjoint solution for the index `k` exactly when `I • g` is a solution of
the original problem for the index `-k - 2`. -/
theorem mem_unitDiscAdjointKernel_iff_smul_mem :
    g ∈ unitDiscAdjointKernel k ↔ I • g ∈ unitDiscCauchyRiemannKernel (-k - 2) := by
  rw [unitDiscAdjointKernel, Submodule.mem_map_equiv, LinearEquiv.symm_symm, mulI_apply]

/-- Membership in the adjoint kernel: `g` is the restriction of a function holomorphic on the open
disc and continuous on its closure that satisfies the adjoint boundary condition. -/
theorem mem_unitDiscAdjointKernel_iff :
    g ∈ unitDiscAdjointKernel k ↔ ∃ u : ℂ → ℂ, DiffContOnCl ℂ u (ball 0 1) ∧
      (∀ w ∈ sphere (0 : ℂ) 1,
        -I * conj w * conj (u w) = w ^ k * conj (-I * conj w * conj (u w))) ∧
      (closedBall 0 1).domRestrict u = g := by
  have hII (x : ℂ) : I * (-I * x) = x := by
    rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  rw [mem_unitDiscAdjointKernel_iff_smul_mem, mem_unitDiscCauchyRiemannKernel_iff]
  constructor
  · rintro ⟨u, hu, hb, hug⟩
    refine ⟨fun z => -I * u z, hu.const_smul (-I), fun w hw => ?_, ?_⟩
    · rw [adjoint_boundary_iff (by simpa using hw), hII]
      exact hb w hw
    · funext z
      have := congrFun hug z
      simp only [Set.domRestrict_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [this, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  · rintro ⟨u, hu, hb, rfl⟩
    refine ⟨fun z => I * u z, hu.const_smul I, fun w hw => ?_, rfl⟩
    exact (adjoint_boundary_iff (by simpa using hw) (u w)).mp (hb w hw)

/-- For `k ≥ -1` the adjoint problem has only the zero solution. -/
theorem unitDiscAdjointKernel_eq_bot (hk : -1 ≤ k) : unitDiscAdjointKernel k = ⊥ := by
  rw [unitDiscAdjointKernel, unitDiscCauchyRiemannKernel_eq_bot (by omega), Submodule.map_bot]

/-- The adjoint solutions form a finite-dimensional real vector space. -/
instance finiteDimensional_unitDiscAdjointKernel (k : ℤ) :
    FiniteDimensional ℝ (unitDiscAdjointKernel k) := by
  rw [unitDiscAdjointKernel]
  infer_instance

/-- **The dimension of the adjoint kernel.** The adjoint problem for the index `k` has real
dimension `-1 - k` when `k ≤ -1`, and `0` when `k ≥ -1`. -/
theorem finrank_unitDiscAdjointKernel (k : ℤ) :
    finrank ℝ (unitDiscAdjointKernel k) = (-k - 1).toNat := by
  rw [unitDiscAdjointKernel, LinearEquiv.finrank_map_eq, finrank_unitDiscCauchyRiemannKernel]
  congr 1
  ring

/-- **The index of the Cauchy–Riemann operator on the disc.** For the boundary condition of
Maslov index `k`, the dimension of the kernel minus the dimension of the adjoint kernel is
`k + 1 = χ(D) + k`, for every integer `k`. -/
theorem finrank_unitDiscCauchyRiemannKernel_sub_finrank_unitDiscAdjointKernel (k : ℤ) :
    (finrank ℝ (unitDiscCauchyRiemannKernel k) : ℤ) - finrank ℝ (unitDiscAdjointKernel k) =
      k + 1 := by
  rw [finrank_unitDiscCauchyRiemannKernel, finrank_unitDiscAdjointKernel]
  omega

end TauCeti
