/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Map

/-!
# The loop formula for the boundary Maslov index on the annulus

Let `E` be a complex normed space and `A = {z | r ≤ ‖z‖ ≤ R}` the closed
annulus, `0 ≤ r ≤ R`. A bundle pair `(E, F)` over `A` read in a trivialization `A × E` is a pair of
loops of maximal totally real subspaces of `E` (`TauCeti.TotallyRealLoop`): `Λ` on the outer circle,
parametrized counterclockwise by `t ↦ R e^{2πit}`, and `Γ` on the inner circle, parametrized
counterclockwise by `t ↦ r e^{2πit}`. Oriented as the boundary of `A`, the outer circle runs
counterclockwise and the inner circle clockwise, so the loop formula of McDuff--Salamon,
Theorem C.3.6, computes the boundary Maslov index as

`μ(E, F) = μ(Λ) + μ(Γ.symm)`.

The individual summands are not invariants of the bundle pair, but the sum is: a second
trivialization differs from the first by a continuous map `B : A → GL(E)`, and the loops read in
it are `t ↦ B (R e^{2πit}) (Λ t)` and `t ↦ B (r e^{2πit}) (Γ t)`. The boundary-oriented sum of
their Maslov indices is again `μ(Λ) + μ(Γ.symm)`
(`TauCeti.TotallyRealLoop.maslovIndex_map_add_maslovIndex_map_symm_of_continuousOn_annulus`).
By the product formula (`TauCeti.TotallyRealLoop.maslovIndex_map`) the outer index shifts by twice
the degree of the determinant loop of `B` on the outer circle, whatever loop it moves
(`TauCeti.TotallyRealLoop.maslovIndex_map_sub_maslovIndex`), and the inner index by twice the
degree on the inner circle. The two determinant loops are freely homotopic through the circles of
radius `s ∈ [r, R]`, so the shifts agree, and reversing the inner circle makes them cancel.

For `r = 0` the inner circle is a point, where `B` is constant, and the statement is the
independence of the trivialization on the disc
(`TauCeti.TotallyRealLoop.maslovIndex_map_of_continuousOn_closedBall`, derived from it).

The definition of `μ(E, F)` as the first Chern number of the doubled bundle, of which the loop
formula is a theorem, is not treated here.

## Main declarations

* `TauCeti.TotallyRealLoop.maslovIndex_map_add_maslovIndex_map_symm_of_continuousOn_annulus`: the
  boundary-oriented sum of the Maslov indices of the two boundary loops of the annulus is
  independent of the trivialization.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3, Theorems C.3.5 and C.3.6 (the boundary
  Maslov index of a bundle pair, its axioms, and the loop formula in a trivialization).
-/

public section

open Metric Module Real
open scoped unitInterval

namespace TauCeti

namespace TotallyRealLoop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Independence of the trivialization on the annulus.** Let `B` be a continuous map from the
closed annulus `r ≤ ‖z‖ ≤ R` to the complex-linear automorphisms of `E`, with loops of boundary
values `b t = B (R e^{2πit})` on the outer circle and `c t = B (r e^{2πit})` on the inner circle.
Moving the outer loop `Λ` by `b` and the inner loop `Γ` by `c` does not change the sum of the Maslov
indices of the boundary loops oriented as the boundary of the annulus, the outer one
counterclockwise and the inner one clockwise. -/
theorem maslovIndex_map_add_maslovIndex_map_symm_of_continuousOn_annulus
    (Λ Γ : TotallyRealLoop E) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (B : ℂ → E ≃L[ℂ] E)
    (hB : ContinuousOn (fun z => (B z : E →L[ℂ] E)) (closedBall 0 R \ ball 0 r))
    (b : I → E ≃L[ℂ] E) (hb : Continuous fun t => (b t : E →L[ℂ] E)) (hb01 : b 0 = b 1)
    (hbB : ∀ t, b t = B (R * Circle.expLoop t))
    (c : I → E ≃L[ℂ] E) (hc : Continuous fun t => (c t : E →L[ℂ] E)) (hc01 : c 0 = c 1)
    (hcB : ∀ t, c t = B (r * Circle.expLoop t)) :
    (Λ.map b hb hb01).maslovIndex + (Γ.map c hc hc01).symm.maslovIndex =
      Λ.maslovIndex + Γ.symm.maslovIndex := by
  -- Move the inner circle to the outer one through the circles of radius `r + s (R - r)`.
  let H (p : I × I) : E ≃L[ℂ] E := B ((r + p.1 * (R - r) : ℝ) * (Circle.expLoop p.2 : ℂ))
  have hmem (p : I × I) :
      ((r + p.1 * (R - r) : ℝ) * (Circle.expLoop p.2 : ℂ) : ℂ) ∈
        closedBall (0 : ℂ) R \ ball 0 r := by
    have h0 : 0 ≤ (p.1 : ℝ) * (R - r) := mul_nonneg p.1.2.1 (sub_nonneg.2 hrR)
    have h1 : (p.1 : ℝ) * (R - r) ≤ R - r :=
      mul_le_of_le_one_left (sub_nonneg.2 hrR) p.1.2.2
    simp only [Set.mem_sdiff, mem_closedBall_zero_iff, mem_ball_zero_iff, norm_mul,
      Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg hr h0)]
    constructor <;> linarith
  have hH : Continuous fun p => (H p : E →L[ℂ] E) :=
    hB.comp_continuous (by fun_prop) hmem
  have hH01 (s : I) : H (s, 0) = H (s, 1) := by
    simp only [H, Circle.expLoop.source, Circle.expLoop.target]
  have h₀ : Γ.map (fun t => H (0, t)) (hH.comp (Continuous.prodMk_right 0)) (hH01 0) =
      Γ.map c hc hc01 :=
    ext fun t => by simp [H, hcB]
  have h₁ : Γ.map (fun t => H (1, t)) (hH.comp (Continuous.prodMk_right 1)) (hH01 1) =
      Γ.map b hb hb01 :=
    ext fun t => by simp [H, hbB]
  have hhom := Γ.maslovIndex_map_eq_of_homotopy H hH hH01
  rw [h₀, h₁] at hhom
  have hshift := Λ.maslovIndex_map_sub_maslovIndex Γ b hb hb01
  rw [maslovIndex_symm, maslovIndex_symm]
  omega

/-! ### Checks -/

/-- Composition on the annulus: `(ℂ, ℝ)` on both boundary circles has boundary Maslov index
`0 + 0 = 0`, in every trivialization over the annulus. -/
example {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (B : ℂ → ℂ ≃L[ℂ] ℂ)
    (hB : ContinuousOn (fun z => (B z : ℂ →L[ℂ] ℂ)) (closedBall 0 R \ ball 0 r))
    (b : I → ℂ ≃L[ℂ] ℂ) (hb : Continuous fun t => (b t : ℂ →L[ℂ] ℂ)) (hb01 : b 0 = b 1)
    (hbB : ∀ t, b t = B (R * Circle.expLoop t))
    (c : I → ℂ ≃L[ℂ] ℂ) (hc : Continuous fun t => (c t : ℂ →L[ℂ] ℂ)) (hc01 : c 0 = c 1)
    (hcB : ∀ t, c t = B (r * Circle.expLoop t)) :
    ((const isMaximalTotallyReal_span_one).map b hb hb01).maslovIndex +
      ((const isMaximalTotallyReal_span_one).map c hc hc01).symm.maslovIndex = 0 := by
  rw [maslovIndex_map_add_maslovIndex_map_symm_of_continuousOn_annulus _ _ hr hrR B hB b hb hb01
    hbB c hc hc01 hcB]
  simp

/-- Multiplication by `z ^ m` on `ℂ`, for `z ≠ 0`, extended by the identity at `0`. -/
private noncomputable def zpowEquiv (m : ℤ) (z : ℂ) : ℂ ≃L[ℂ] ℂ :=
  if h : z = 0 then ContinuousLinearEquiv.refl ℂ ℂ
  else ContinuousLinearEquiv.smulLeft (Units.mk0 (z ^ m) (zpow_ne_zero m h))

private theorem coe_zpowEquiv (m : ℤ) {z : ℂ} (hz : z ≠ 0) :
    (zpowEquiv m z : ℂ →L[ℂ] ℂ) = z ^ m • ContinuousLinearMap.id ℂ ℂ := by
  ext
  simp [zpowEquiv, hz]

private theorem continuousOn_zpowEquiv (m : ℤ) :
    ContinuousOn (fun z => (zpowEquiv m z : ℂ →L[ℂ] ℂ)) {0}ᶜ := by
  refine ContinuousOn.congr (f := fun z : ℂ => z ^ m • ContinuousLinearMap.id ℂ ℂ) ?_
    fun z hz => coe_zpowEquiv m hz
  exact (continuousOn_zpow₀ m).smul continuousOn_const

private theorem mul_expLoop_ne_zero {ρ : ℝ} (hρ : ρ ≠ 0) (t : I) :
    ((ρ : ℂ) * (Circle.expLoop t : ℂ)) ≠ 0 :=
  mul_ne_zero (by exact_mod_cast hρ) (Circle.coe_ne_zero _)

private theorem continuous_zpowEquiv_expLoop (m : ℤ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    Continuous fun t => (zpowEquiv m (ρ * Circle.expLoop t) : ℂ →L[ℂ] ℂ) :=
  (continuousOn_zpowEquiv m).comp_continuous (by fun_prop) (mul_expLoop_ne_zero hρ)

private theorem zpowEquiv_expLoop_zero_eq_one (m : ℤ) (ρ : ℝ) :
    zpowEquiv m (ρ * Circle.expLoop 0) = zpowEquiv m (ρ * Circle.expLoop 1) := by
  simp only [Circle.expLoop.source, Circle.expLoop.target]

/-- Moving any loop by multiplication by `z ^ m` on the circle of radius `ρ > 0` adds `2 m` to its
Maslov index. -/
private theorem maslovIndex_map_zpowEquiv (Λ : TotallyRealLoop ℂ) (m : ℤ) {ρ : ℝ} (hρ : 0 < ρ) :
    (Λ.map (fun t => zpowEquiv m (ρ * Circle.expLoop t))
      (continuous_zpowEquiv_expLoop m hρ.ne') (zpowEquiv_expLoop_zero_eq_one m ρ)).maslovIndex =
      Λ.maslovIndex + 2 * m := by
  let δ : Path (1 : Circle) 1 :=
    { toFun := fun t => Circle.exp (2 * π * m * t)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by
        rw [Set.Icc.coe_one, mul_one, Circle.exp_eq_one]
        exact ⟨m, by ring⟩ }
  rw [Λ.maslovIndex_map _ _ _ δ fun t => ?_, Circle.degree_eq_of_sub_eq δ
    (θ := fun t => 2 * π * m * t) (by fun_prop) (fun _ => rfl) (n := m) (by simp; ring)]
  have hlin : ((zpowEquiv m (ρ * Circle.expLoop t)).toLinearEquiv : ℂ →ₗ[ℂ] ℂ) =
      ((ρ : ℂ) * Circle.expLoop t) ^ m • LinearMap.id := by
    ext
    simp [zpowEquiv, hρ.ne']
  have hexp :
      Complex.exp (2 * π * t * Complex.I) ^ m = Complex.exp (2 * π * m * t * Complex.I) := by
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  rw [hlin]
  simp [mul_zpow, abs_of_pos hρ, δ, Complex.norm_exp, hexp]

/-- The individual circle indices are not invariants: multiplication by `z ^ m`, a change of
trivialization over the annulus `r ≤ ‖z‖ ≤ R` with `0 < r`, moves `(ℂ, ℝ)` on the outer circle to a
loop of index `2 m` and on the inner circle, read clockwise, to a loop of index `-2 m`; the
boundary-oriented sum stays `0`, as the loop formula says. -/
example (m : ℤ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ((const isMaximalTotallyReal_span_one).map (fun t => zpowEquiv m (R * Circle.expLoop t))
      (continuous_zpowEquiv_expLoop m (hr.trans_le hrR).ne')
      (zpowEquiv_expLoop_zero_eq_one m R)).maslovIndex = 2 * m ∧
    ((const isMaximalTotallyReal_span_one).map (fun t => zpowEquiv m (r * Circle.expLoop t))
      (continuous_zpowEquiv_expLoop m hr.ne')
      (zpowEquiv_expLoop_zero_eq_one m r)).symm.maslovIndex = -(2 * m) ∧
    ((const isMaximalTotallyReal_span_one).map (fun t => zpowEquiv m (R * Circle.expLoop t))
      (continuous_zpowEquiv_expLoop m (hr.trans_le hrR).ne')
      (zpowEquiv_expLoop_zero_eq_one m R)).maslovIndex +
    ((const isMaximalTotallyReal_span_one).map (fun t => zpowEquiv m (r * Circle.expLoop t))
      (continuous_zpowEquiv_expLoop m hr.ne')
      (zpowEquiv_expLoop_zero_eq_one m r)).symm.maslovIndex = 0 := by
  refine ⟨by rw [maslovIndex_map_zpowEquiv _ m (hr.trans_le hrR), maslovIndex_const, zero_add],
    by rw [maslovIndex_symm, maslovIndex_map_zpowEquiv _ m hr, maslovIndex_const, zero_add], ?_⟩
  rw [maslovIndex_map_add_maslovIndex_map_symm_of_continuousOn_annulus _ _ hr.le hrR
    (zpowEquiv m) ((continuousOn_zpowEquiv m).mono fun z hz => ?_) _ _ _ (fun _ => rfl) _ _ _
    fun _ => rfl]
  · simp
  · rintro rfl
    simp [hr] at hz

end TotallyRealLoop

end TauCeti
