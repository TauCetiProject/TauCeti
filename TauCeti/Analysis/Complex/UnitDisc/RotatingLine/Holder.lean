/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Analysis.Complex.Circle.Rotation
import TauCeti.Analysis.Complex.Pompeiu.Holder.Gain
import TauCeti.Analysis.Complex.UnitDisc.RiemannHilbert
import TauCeti.Analysis.Holder.Jet.Bounds
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.Normed.Module.Ball.HolderExtension
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# The disc problem with rotating-line boundary values and Hölder forcing

Fix an integer `k`. This file solves the inhomogeneous Cauchy–Riemann equation on the closed unit
disc with boundary values on the rotating lines `e^{ikθ/2} ℝ`,

`∂u/∂(conj z) = f` on the open disc, `u w = w ^ k * conj (u w)` on the unit circle,

for forcing `f` that is only `α`-Hölder on the closed disc, `0 < α < 1`, and finds solutions of
class `C^{1,α}` up to the boundary: `u` is `α`-Hölder on the closed disc, real differentiable on
the open disc, and its real derivative extends from the open disc to an `α`-Hölder field on the
closed disc.

**Existence.** For `k ≥ -1` the problem is solvable
(`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_of_holderOnWith`). The forcing is
extended from the closed disc to a compactly supported Hölder source `g`
(`HolderOnWith.exists_holderWith_eqOn_closedBall`), whose Cauchy transform
`T g w = π⁻¹ ∫ (w - z)⁻¹ g z` is `C¹` with `α`-Hölder derivative and inverts `∂/∂(conj z)`. The
boundary defect `φ w = w ^ k * conj (T g w) - T g w` then has an `α`-Hölder derivative along the
rotations of the circle, so the Riemann–Hilbert problem `h - w ^ k * conj h = φ` has a holomorphic
solution `h` whose derivative is `α`-Hölder up to the boundary
(`TauCeti.exists_holderOnWith_closedBall_deriv_sub_zpow_mul_conj_eq`), and `u = T g + h`.

**The augmented problem.** For `k ≥ 3` the kernel contains
`a₀ + a₁ z + conj a₁ z^(k-1) + conj a₀ z^k`, whose centre value is `a₀` and whose first derivative
at the centre is `a₁`. Adding it prescribes the centre value `u 0` and the first jet `∂ₛu(0)`,
the real derivative of `u` at `0` in the direction `1`
(`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_and_eq_and_fderiv_eq_of_holderOnWith`).
For `k = 3`, the normalization of the real-boundary disc problem in the linear theory of
holomorphic discs, the kernel is exactly these cubics, so the solution is unique
(`TauCeti.eqOn_of_conjWirtingerDeriv_eq_of_eq_zpow_mul_conj_of_eq_of_fderiv_eq`). Together, for
Maslov index three the map `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` from the `C^{1,α}` functions with
these boundary values to `C^α` forcing and two complex numbers is bijective.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the boundary value problem on the disc,
  Theorem C.4.1, solved by the Cauchy transform followed by a Riemann–Hilbert correction).
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate NNReal

/-! ### The boundary defect of a `C^{1,α}` function -/

/-- **The derivative of the boundary defect along the rotations.** Let `T` be real differentiable
at each point of the unit circle, with `T` and its derivative `α`-Hölder on the circle. Then the
boundary defect `φ w = w ^ k * conj (T w) - T w` has at each point `w` of the circle a derivative
`v w` along the rotations `t ↦ φ (e^{it} w)`, and `v` is `α`-Hölder on the circle. -/
private theorem exists_hasDerivAt_zpow_mul_conj_sub_holderOnWith (k : ℤ) {T : ℂ → ℂ}
    (hT : ∀ w ∈ sphere (0 : ℂ) 1, DifferentiableAt ℝ T w) {α C D : ℝ≥0} (hα0 : 0 < α)
    (hα1 : α ≤ 1) (hTH : HolderOnWith C α T (sphere 0 1))
    (hDH : HolderOnWith D α (fderiv ℝ T) (sphere 0 1)) :
    ∃ (v : ℂ → ℂ) (L : ℝ≥0), (∀ w ∈ sphere (0 : ℂ) 1,
      HasDerivAt (fun t : ℝ ↦ (exp (I * t) * w) ^ k * conj (T (exp (I * t) * w)) -
        T (exp (I * t) * w)) (v w) 0) ∧ HolderOnWith L α v (sphere 0 1) := by
  -- Functions holomorphic away from the origin are Hölder on the circle.
  have hS {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g {0}ᶜ) : ∃ C, HolderOnWith C α g (sphere 0 1) :=
    ((hg.contDiffOn (n := 1) isOpen_compl_singleton).locallyLipschitzOn_of_isOpen
      isOpen_compl_singleton).exists_holderOnWith_of_isCompact hα1 (isCompact_sphere 0 1)
      fun _ hw ↦ ne_of_mem_sphere hw one_ne_zero
  have hzpow (m : ℤ) : DifferentiableOn ℂ (fun w : ℂ ↦ w ^ m) {0}ᶜ :=
    differentiableOn_zpow m _ (Or.inl fun h ↦ h rfl)
  -- The derivative of `T` in the rotation direction `i w`, and its Hölder bound.
  set R : ℂ → ℂ := fun w ↦ fderiv ℝ T w (I * w)
  obtain ⟨Ci, hIH⟩ := hS (g := fun w ↦ I * w) (differentiable_id.const_mul I).differentiableOn
  obtain ⟨CR, hRH⟩ := (ContinuousLinearMap.apply ℝ ℂ).exists_holderOnWith_comp₂_of_isCompact
    (isCompact_sphere 0 1) hα0 hIH hDH
  -- The three terms of `v`.
  obtain ⟨C₁, h₁⟩ := hS (g := fun w ↦ (k : ℂ) * w ^ (k - 1) * (I * w))
    (((hzpow (k - 1)).const_mul _).mul (differentiable_id.const_mul I).differentiableOn)
  obtain ⟨C₂, h₂⟩ := hS (hzpow k)
  obtain ⟨CA, hA⟩ := (ContinuousLinearMap.mul ℝ ℂ).exists_holderOnWith_comp₂_of_isCompact
    (isCompact_sphere 0 1) hα0 h₁ (Complex.isometry_conj.comp_holderOnWith hTH)
  obtain ⟨CB, hB⟩ := (ContinuousLinearMap.mul ℝ ℂ).exists_holderOnWith_comp₂_of_isCompact
    (isCompact_sphere 0 1) hα0 h₂ (Complex.isometry_conj.comp_holderOnWith hRH)
  refine ⟨fun w ↦ (k : ℂ) * w ^ (k - 1) * (I * w) * conj (T w) + w ^ k * conj (R w) - R w, _,
    fun w hw ↦ ?_, (hA.add hB).sub hRH⟩
  have hw0 : w ≠ 0 := ne_of_mem_sphere hw one_ne_zero
  have hγ0 : exp (I * ((0 : ℝ) : ℂ)) * w = w := by simp
  have hγ : HasDerivAt (fun t : ℝ ↦ exp (I * t) * w) (I * w) 0 := by
    simpa using hasDerivAt_exp_I_mul_mul w 0
  have hTγ : HasDerivAt (fun t : ℝ ↦ T (exp (I * t) * w)) (R w) 0 :=
    (hT w hw).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ hγ0.symm
  have hpow : HasDerivAt (fun t : ℝ ↦ (exp (I * t) * w) ^ k) ((k : ℂ) * w ^ (k - 1) * (I * w))
      0 := (hasDerivAt_zpow k w (Or.inl hw0)).comp_of_eq 0 hγ hγ0.symm
  have hd := (hpow.mul hTγ.star).sub hTγ
  rw [hγ0, Complex.star_def] at hd
  exact hd

/-- **Adding a holomorphic map.** Adding a map `p` holomorphic on an open set `U` to a map `u`
real differentiable on `U` keeps it real differentiable on `U`, adds the real derivatives and leaves
`∂u/∂(conj z)` unchanged. -/
private theorem differentiableOn_add_and_fderiv_add_and_conjWirtingerDeriv_add {U : Set ℂ}
    (hU : IsOpen U) {u p : ℂ → ℂ} (hu : DifferentiableOn ℝ u U) (hp : DifferentiableOn ℂ p U) :
    DifferentiableOn ℝ (u + p) U ∧
      (∀ z ∈ U, fderiv ℝ (u + p) z = fderiv ℝ u z + fderiv ℝ p z) ∧
      ∀ z ∈ U, conjWirtingerDeriv (u + p) z 1 = conjWirtingerDeriv u z 1 := by
  have huD (z : ℂ) (hz : z ∈ U) : DifferentiableAt ℝ u z := hu.differentiableAt (hU.mem_nhds hz)
  have hpD (z : ℂ) (hz : z ∈ U) : DifferentiableAt ℂ p z := hp.differentiableAt (hU.mem_nhds hz)
  refine ⟨hu.add fun z hz ↦ ((hpD z hz).restrictScalars ℝ).differentiableWithinAt,
    fun z hz ↦ fderiv_add (huD z hz) ((hpD z hz).restrictScalars ℝ), fun z hz ↦ ?_⟩
  rw [add_comm u p]
  exact congr($((hpD z hz).conjWirtingerDeriv_add_left (f := u)) 1)

/-! ### Existence -/

/-- **The disc problem with rotating-line boundary values is solvable for Hölder forcing.** Let
`k ≥ -1`, `0 < α < 1`, and let `f` be `α`-Hölder on the closed unit disc. Then there is `u`,
`α`-Hölder on the closed disc and real differentiable on the open disc, whose real derivative
extends from the open disc to an `α`-Hölder field on the closed disc, with `∂u/∂(conj z) = f` on
the open disc and boundary values `u(e^{iθ}) ∈ e^{ikθ/2} ℝ`, that is `u w = w ^ k * conj (u w)` on
the unit circle. -/
theorem exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_of_holderOnWith {k : ℤ} (hk : -1 ≤ k)
    {α C : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) {f : ℂ → ℂ}
    (hf : HolderOnWith C α f (closedBall 0 1)) :
    ∃ u : ℂ → ℂ, (∃ K, HolderOnWith K α u (closedBall 0 1)) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∃ (u' : ℂ → ℂ →L[ℝ] ℂ) (K : ℝ≥0), HolderOnWith K α u' (closedBall 0 1) ∧
        ∀ z ∈ ball (0 : ℂ) 1, fderiv ℝ u z = u' z) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      ∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w) := by
  -- The Cauchy transform `T` of a compactly supported Hölder extension `g` of `f`.
  obtain ⟨g, H, M, hgH, hgM, hgs, hgf⟩ := hf.exists_holderWith_eqOn_closedBall one_pos hα1.le
  obtain ⟨C₀, hC₀⟩ := exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul
    (F := ℂ) hα0 hα1 (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 2 * 1) zero_le_one
  obtain ⟨hTd, hDH, -, hTbar⟩ := hC₀ hgs hgH hgM
  set T : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • g z
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 (1 + 1) := closedBall_subset_ball (by norm_num)
  have hTdiff (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : DifferentiableAt ℝ T z :=
    (hTd.contDiffAt (isOpen_ball.mem_nhds (hsub hz))).differentiableAt one_ne_zero
  obtain ⟨CT, hTH⟩ := (hTd.mono hsub).exists_holderOnWith (convex_closedBall 0 1)
    (isCompact_closedBall 0 1) hα1.le
  -- The holomorphic correction `h` of the boundary values of `T`.
  obtain ⟨v, L, hv, hvH⟩ := exists_hasDerivAt_zpow_mul_conj_sub_holderOnWith k
    (fun w hw ↦ hTdiff w (sphere_subset_closedBall hw)) hα0 hα1.le
    (hTH.mono sphere_subset_closedBall) (hDH.mono sphere_subset_closedBall)
  obtain ⟨h, hhd, ⟨Ch, hhH⟩, ⟨h', Ch', hh'H, hh'd⟩, hhb⟩ :=
    exists_holderOnWith_closedBall_deriv_sub_zpow_mul_conj_eq
      (φ := fun w ↦ w ^ k * conj (T w) - T w) hk hα0 hα1 hv hvH
      fun w hw ↦ zpow_mul_conj_sub_eq_neg_of_mem_sphere hw k (T w)
  obtain ⟨hd, hfd, hbar⟩ := differentiableOn_add_and_fderiv_add_and_conjWirtingerDeriv_add
    isOpen_ball (fun z hz ↦ (hTdiff z (ball_subset_closedBall hz)).differentiableWithinAt)
    hhd.differentiableOn
  set Λ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℂ
  refine ⟨T + h, ⟨_, hTH.add hhH⟩, hd,
    ⟨fderiv ℝ T + Λ ∘ h', _, hDH.add (Λ.lipschitzWith.comp_holderOnWith hh'H),
      fun z hz ↦ ?_⟩, fun z hz ↦ ?_, fun w hw ↦ ?_⟩
  · -- The real derivative of the holomorphic `h` is multiplication by `h' z = deriv h z`.
    rw [hfd z hz, ((hhd.differentiableAt isOpen_ball hz).hasDerivAt.complexToReal_fderiv).fderiv,
      Pi.add_apply, Function.comp_apply, hh'd z hz]
    ext
    simp [Λ, mul_comm]
  · rw [hbar z hz, hTbar z (hsub (ball_subset_closedBall hz)), hgf (ball_subset_closedBall hz)]
  · have := hhb w hw
    simp only [Pi.add_apply, map_add, mul_add]
    linear_combination this

/-- **Prescribing the centre value and the first jet.** Let `k ≥ 3`, `0 < α < 1`, let `f` be
`α`-Hölder on the closed unit disc, and let `a b : ℂ`. Then there is `u`, `α`-Hölder on the closed
disc and real differentiable on the open disc, whose real derivative extends from the open disc
to an `α`-Hölder field on the closed disc, with `∂u/∂(conj z) = f` on the open disc, boundary
values `u w = w ^ k * conj (u w)` on the unit circle, centre value `u 0 = a` and first jet
`∂ₛu(0) = b`. For `k = 3` the solution is unique
(`TauCeti.eqOn_of_conjWirtingerDeriv_eq_of_eq_zpow_mul_conj_of_eq_of_fderiv_eq`). -/
theorem exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_and_eq_and_fderiv_eq_of_holderOnWith
    {k : ℤ} (hk : 3 ≤ k) {α C : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) {f : ℂ → ℂ}
    (hf : HolderOnWith C α f (closedBall 0 1)) (a b : ℂ) :
    ∃ u : ℂ → ℂ, (∃ K, HolderOnWith K α u (closedBall 0 1)) ∧ DifferentiableOn ℝ u (ball 0 1) ∧
      (∃ (u' : ℂ → ℂ →L[ℝ] ℂ) (K : ℝ≥0), HolderOnWith K α u' (closedBall 0 1) ∧
        ∀ z ∈ ball (0 : ℂ) 1, fderiv ℝ u z = u' z) ∧
      (∀ z ∈ ball (0 : ℂ) 1, conjWirtingerDeriv u z 1 = f z) ∧
      (∀ w ∈ sphere (0 : ℂ) 1, u w = w ^ k * conj (u w)) ∧ u 0 = a ∧
      fderiv ℝ u 0 1 = b := by
  lift k to ℕ using by omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  obtain ⟨u, ⟨K, huH⟩, hud, ⟨u', K', hu'H, hu'⟩, hubar, hub⟩ :=
    exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_of_holderOnWith (k := ((j + 3 : ℕ) : ℤ))
      (by omega) hα0 hα1 hf
  -- The kernel element `p` correcting the centre value and the first jet.
  set a₀ := a - u 0
  set a₁ := b - fderiv ℝ u 0 1
  set p : ℂ → ℂ := fun z ↦ a₀ + a₁ * z + conj a₁ * z ^ (j + 2) + conj a₀ * z ^ (j + 3)
  have hpd : Differentiable ℂ p := by fun_prop
  have hp2 : ContDiff ℝ 2 p := (by fun_prop : ContDiff ℂ 2 p).restrict_scalars ℝ
  obtain ⟨Kp, hpH⟩ := (hp2.of_le one_le_two).contDiffOn.exists_holderOnWith
    (convex_closedBall 0 1) (isCompact_closedBall 0 1) hα1.le
  obtain ⟨Kp', hp'H⟩ := (hp2.fderiv_right (m := 1) le_rfl).contDiffOn.exists_holderOnWith
    (convex_closedBall 0 1) (isCompact_closedBall 0 1) hα1.le
  have hp1 : fderiv ℝ p 0 1 = a₁ := by
    have hp : HasDerivAt p (a₁ * 1 + conj a₁ * (↑(j + 2) * 0 ^ (j + 2 - 1)) +
        conj a₀ * (↑(j + 3) * 0 ^ (j + 3 - 1))) 0 :=
      ((((hasDerivAt_id (0 : ℂ)).const_mul a₁).const_add a₀).add
        ((hasDerivAt_pow (j + 2) (0 : ℂ)).const_mul _)).add
        ((hasDerivAt_pow (j + 3) (0 : ℂ)).const_mul _)
    rw [hp.complexToReal_fderiv.fderiv]
    simp
  have hpb (w : ℂ) (hw : w ∈ sphere (0 : ℂ) 1) : p w = w ^ ((j + 3 : ℕ) : ℤ) * conj (p w) := by
    have hq : w * w⁻¹ = 1 := mul_inv_cancel₀ (ne_of_mem_sphere hw one_ne_zero)
    have e₁ : w ^ (j + 3) * w⁻¹ ^ (j + 3) = 1 := by rw [← mul_pow, hq, one_pow]
    have e₂ : w ^ (j + 3) * w⁻¹ ^ (j + 2) = w := by
      rw [show w ^ (j + 3) * w⁻¹ ^ (j + 2) = w * (w * w⁻¹) ^ (j + 2) by ring, hq, one_pow,
        mul_one]
    have e₃ : w ^ (j + 3) * w⁻¹ = w ^ (j + 2) := by
      rw [show w ^ (j + 3) * w⁻¹ = w ^ (j + 2) * (w * w⁻¹) by ring, hq, mul_one]
    simp only [p, zpow_natCast, map_add, map_mul, map_pow, conj_conj,
      ← inv_eq_conj (mem_sphere_zero_iff_norm.mp hw)]
    linear_combination -a₀ * e₁ - a₁ * e₂ - conj a₁ * e₃
  obtain ⟨hd, hfd, hbar⟩ := differentiableOn_add_and_fderiv_add_and_conjWirtingerDeriv_add
    isOpen_ball hud hpd.differentiableOn
  refine ⟨u + p, ⟨_, huH.add hpH⟩, hd,
    ⟨fun z ↦ u' z + fderiv ℝ p z, _, hu'H.add hp'H, fun z hz ↦ by rw [hfd z hz, hu' z hz]⟩,
    fun z hz ↦ by rw [hbar z hz, hubar z hz], fun w hw ↦ ?_, by simp [p, a₀], ?_⟩
  · rw [Pi.add_apply, map_add, mul_add, ← hub w hw, ← hpb w hw]
  · rw [hfd 0 (mem_ball_self one_pos), add_apply, hp1]
    simp [a₁]

end TauCeti
