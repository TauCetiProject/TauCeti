/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Geometry.Manifold.Riemannian.Poisson

/-!
# Schrödinger operators with a nonnegative potential on a closed manifold

Let `M` be a compact connected manifold without boundary, with a continuous Riemannian metric, its
Riemannian volume `dV` and the Sobolev space `H¹(M)` (`TauCeti.Manifold.SobolevH1`). For a bounded
potential `V ∈ L^∞(M)` this file inverts the Schrödinger operator `Δ⁺ + V`, where `Δ⁺ = -div grad`
is the nonnegative Laplacian, in the weak sense on all of `H¹(M)`, as soon as `V ≥ 0` and
`∫ V dV > 0`.

The weak form of `Δ⁺w + V w = f`, for `f ∈ L²(M)`, asks for `w ∈ H¹(M)` with

`D(w, v) + P_V(w, v) = ∫ f v dV` for every `v ∈ H¹(M)`,

where `D` is the Dirichlet form (`TauCeti.Manifold.SobolevH1.dirichletForm`) and
`P_V(w, v) = ∫ V w v dV` is the potential form (`TauCeti.Manifold.SobolevH1.potentialForm`).
Unlike the Poisson equation `Δ⁺w = f` (`TauCeti.Manifold.SobolevH1.existsUnique_dirichletForm_eq`),
no compatibility condition on `f` is needed and the solution is unique in all of `H¹(M)`: a
nonnegative potential that is not almost everywhere zero removes the constants from the kernel.

The key estimate is the coercivity of `D + P_V` in the full `H¹` norm
(`TauCeti.Manifold.SobolevH1.exists_norm_sq_le_mul_dirichletForm_add_potentialForm`). Write
`w = w₀ + m` with `m` the mean of `w`, so that `w₀` has integral zero. The Poincaré–Wirtinger
inequality on `H¹(M)` (`TauCeti.Manifold.SobolevH1.exists_norm_toLp_sq_le`) bounds `‖w₀‖²_{L²}` by
`D(w, w)`. Since `P_V` is a nonnegative symmetric form,
`m² ∫ V dV = P_V(m, m) ≤ 2 P_V(w, w) + 2 P_V(w₀, w₀)`, and `P_V(w₀, w₀) ≤ ‖V‖_∞ ‖w₀‖²_{L²}`. So the
mean is controlled by `D(w, w) + P_V(w, w)` too. The Lax–Milgram theorem then gives existence and
uniqueness (`TauCeti.Manifold.SobolevH1.existsUnique_dirichletForm_add_potentialForm_eq`), and
coercivity bounds the solution, `‖w‖_{H¹} ≤ C ‖f‖_{L²}`
(`TauCeti.Manifold.SobolevH1.exists_norm_le_mul_norm_of_dirichletForm_add_potentialForm_eq`).

The main example is the gauge-fixing Laplacian of the Seiberg–Witten equations on a closed
four-manifold. The infinitesimal action `ξ ↦ (-2 dξ, ξ ψ)` of an imaginary function `ξ` at a
configuration `(A, ψ)` composed with its formal adjoint is `4 Δ⁺ + |ψ|²`, which is `4` times the
Schrödinger operator with the continuous potential `V = |ψ|² / 4`. This potential is nonnegative,
and it has positive integral exactly when the spinor `ψ` is not identically zero. The weak inverse
of this operator on `H¹(M)` is therefore available at every configuration with nonzero spinor.

## Main definitions

* `TauCeti.Manifold.SobolevH1.potentialForm V`: the continuous bilinear form
  `P_V(w, v) = ∫ V w v dV` on `H¹(M)`.

## Main results

* `TauCeti.Manifold.SobolevH1.potentialForm_apply`,
  `TauCeti.Manifold.SobolevH1.potentialForm_ofSmooth`: `P_V(w, v) = ∫ V w v dV`.
* `TauCeti.Manifold.SobolevH1.potentialForm_self_nonneg`,
  `TauCeti.Manifold.SobolevH1.potentialForm_self_le`: `0 ≤ P_V(w, w) ≤ ‖V‖_∞ ‖w‖²_{L²}` for
  `V ≥ 0`.
* `TauCeti.Manifold.SobolevH1.exists_norm_sq_le_mul_dirichletForm_add_potentialForm`: the
  coercivity estimate `‖w‖²_{H¹} ≤ C (D(w, w) + P_V(w, w))`.
* `TauCeti.Manifold.SobolevH1.isCoercive_dirichletForm_add_potentialForm`: `D + P_V` is
  coercive.
* `TauCeti.Manifold.SobolevH1.existsUnique_dirichletForm_add_potentialForm_eq`: existence and
  uniqueness of the weak solution of `Δ⁺w + V w = f`.
* `TauCeti.Manifold.SobolevH1.exists_norm_le_mul_norm_of_dirichletForm_add_potentialForm_eq`:
  the bound `‖w‖_{H¹} ≤ C ‖f‖_{L²}` on weak solutions.
* `TauCeti.Manifold.SobolevH1.exists_integral_mul_neg_laplaceBeltrami_add_eq`: the
  distributional form of the solution, for a `C¹` metric.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer (2001), §8.2 (the Lax–Milgram solution of the weak Dirichlet problem).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press (1996), §4.4 (the gauge-fixing
  Laplacian and the local slice).
-/

public section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold InnerProductSpace ENNReal

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-! ### The potential form -/

/-- The **potential form** `P_V(w, v) = ∫ V w v dV` of a bounded potential `V` on `H¹(M)`
(`TauCeti.Manifold.SobolevH1.potentialForm_apply`). Together with the Dirichlet form it is the
weak form of the Schrödinger operator `Δ⁺ + V`. It is the `L²` pairing of `V w` with `v`, where
multiplication by `V` acts on `L²(M)` through Hölder's inequality. -/
def potentialForm (V : Lp ℝ ∞ (riemannianVolume I M)) :
    SobolevH1 I M →L[ℝ] SobolevH1 I M →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp
    (((ContinuousLinearMap.mul ℝ ℝ).holderL (riemannianVolume I M) ∞ 2 2 V).comp toLp) toLp

/-- Unfolding lemma for `TauCeti.Manifold.SobolevH1.potentialForm`: the `L²` pairing of `V w`
with `v`. -/
private theorem potentialForm_eq_inner (V : Lp ℝ ∞ (riemannianVolume I M))
    (w v : SobolevH1 I M) :
    potentialForm V w v = ⟪(ContinuousLinearMap.mul ℝ ℝ).holder 2 V (toLp w), toLp v⟫_ℝ :=
  (rfl)

/-- The potential form is `P_V(w, v) = ∫ V w v dV`. -/
theorem potentialForm_apply (V : Lp ℝ ∞ (riemannianVolume I M)) (w v : SobolevH1 I M) :
    potentialForm V w v = ∫ x, V x * toLp w x * toLp v x ∂riemannianVolume I M := by
  rw [potentialForm_eq_inner, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) V (toLp w)] with x hx
  rw [hx, RCLike.inner_apply, conj_trivial, ContinuousLinearMap.mul_apply']
  ring

/-- The potential form is symmetric. -/
theorem potentialForm_comm (V : Lp ℝ ∞ (riemannianVolume I M)) (w v : SobolevH1 I M) :
    potentialForm V w v = potentialForm V v w := by
  simp only [potentialForm_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)

/-- The potential form of a nonnegative potential is nonnegative on the diagonal. -/
theorem potentialForm_self_nonneg {V : Lp ℝ ∞ (riemannianVolume I M)}
    (hV : ∀ᵐ x ∂riemannianVolume I M, 0 ≤ V x) (w : SobolevH1 I M) :
    0 ≤ potentialForm V w w := by
  rw [potentialForm_apply]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hV] with x hx
  simpa [mul_assoc] using mul_nonneg hx (mul_self_nonneg (toLp w x))

/-- The potential form is bounded on the diagonal by the `L²` norm:
`P_V(w, w) ≤ ‖V‖_∞ ‖w‖²_{L²}`. -/
theorem potentialForm_self_le (V : Lp ℝ ∞ (riemannianVolume I M)) (w : SobolevH1 I M) :
    potentialForm V w w ≤ ‖V‖ * ‖toLp w‖ ^ 2 := by
  have h := (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le (r := 2) V (toLp w)
  have hmul : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  rw [potentialForm_eq_inner]
  refine (real_inner_le_norm _ _).trans ?_
  have hVw := mul_nonneg (norm_nonneg V) (norm_nonneg (toLp w))
  nlinarith [mul_le_mul_of_nonneg_right hmul hVw, norm_nonneg (toLp w)]

/-- The potential form of two smooth functions is `∫ V u v dV`. -/
@[simp]
theorem potentialForm_ofSmooth (V : Lp ℝ ∞ (riemannianVolume I M)) (u v : C^∞⟮I, M; ℝ⟯) :
    potentialForm V (ofSmooth u) (ofSmooth v) = ∫ x, V x * u x * v x ∂riemannianVolume I M := by
  rw [potentialForm_apply]
  refine integral_congr_ae ?_
  filter_upwards [toLp_ofSmooth_ae_eq u, toLp_ofSmooth_ae_eq v] with x hu hv
  rw [hu, hv]

/-- The potential form against a smooth function `φ` is `∫ V w φ dV`. -/
theorem potentialForm_ofSmooth_right (V : Lp ℝ ∞ (riemannianVolume I M)) (w : SobolevH1 I M)
    (φ : C^∞⟮I, M; ℝ⟯) :
    potentialForm V w (ofSmooth φ) = ∫ x, V x * toLp w x * φ x ∂riemannianVolume I M := by
  rw [potentialForm_apply]
  refine integral_congr_ae ?_
  filter_upwards [toLp_ofSmooth_ae_eq φ] with x hx
  rw [hx]

/-! ### Coercivity -/

variable [I.Boundaryless] [PreconnectedSpace M]

/-- **Coercivity of the Schrödinger form.** On a closed connected manifold with a continuous metric,
let `V ∈ L^∞(M)` be nonnegative with `∫ V dV > 0`. Then there is a constant `C` such that every
`w ∈ H¹(M)` satisfies `‖w‖²_{H¹} ≤ C (D(w, w) + P_V(w, w))`, where `D` is the Dirichlet form and
`P_V(w, w) = ∫ V w² dV`. -/
theorem exists_norm_sq_le_mul_dirichletForm_add_potentialForm
    {V : Lp ℝ ∞ (riemannianVolume I M)} (hV₀ : ∀ᵐ x ∂riemannianVolume I M, 0 ≤ V x)
    (hV : 0 < ∫ x, V x ∂riemannianVolume I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SobolevH1 I M,
      ‖w‖ ^ 2 ≤ C * (dirichletForm w w + potentialForm V w w) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_toLp_sq_le (I := I) (M := M)
  set vol := (riemannianVolume I M).real univ
  set S := ∫ x, V x ∂riemannianVolume I M
  set B := ‖V‖
  set one := ofSmooth (1 : C^∞⟮I, M; ℝ⟯)
  -- The constant function `1` has `‖1‖²_{L²} = Vol(M)`, and `Vol(M) > 0` since `∫ V dV > 0`.
  have hone : ‖toLp one‖ ^ 2 = vol := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp_ofSmooth]
    simp [vol]
  have hvol : 0 < vol := by
    refine lt_of_le_of_ne measureReal_nonneg fun h ↦ hV.ne' ?_
    have hμ : riemannianVolume I M = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      exact (measureReal_eq_zero_iff (measure_ne_top _ univ)).1 h.symm
    simp [S, hμ]
  have hB : 0 ≤ B := norm_nonneg V
  refine ⟨1 + 2 * C + 4 * (vol / S) * (B * C) + 4 * (vol / S), by positivity, fun w ↦ ?_⟩
  -- Split off the mean `m` of `w`: `w₀ = w - m • 1` has integral zero.
  set m := ⟪toLp w, toLp one⟫_ℝ / vol
  set w₀ := w - m • one
  have hw₀ : ⟪toLp w₀, toLp one⟫_ℝ = 0 := by
    rw [map_sub, map_smul, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hone, div_mul_cancel₀ _ hvol.ne', sub_self]
  have hint₀ : ∫ x, toLp w₀ x ∂riemannianVolume I M = 0 := by
    rw [← hw₀, inner_toLp_ofSmooth_right]
    simp
  -- The Dirichlet form does not see the constant part.
  have hD₀ : dirichletForm w₀ w₀ = dirichletForm w w := by
    simp only [w₀, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
      dirichletForm_ofSmooth_one, one]
    rw [dirichletForm_comm (ofSmooth 1) w, dirichletForm_ofSmooth_one]
    ring
  -- Poincaré–Wirtinger bounds the oscillation `w₀` by the Dirichlet energy.
  have hL₀ : ‖toLp w₀‖ ^ 2 ≤ C * dirichletForm w w := by
    simpa [hint₀, hD₀] using hC w₀
  -- The potential form bounds the mean.
  have hP₀ : potentialForm V w₀ w₀ ≤ B * ‖toLp w₀‖ ^ 2 := potentialForm_self_le V w₀
  have hPm : m ^ 2 * S ≤ 2 * potentialForm V w w + 2 * potentialForm V w₀ w₀ := by
    -- `P` is nonnegative and symmetric, so `P(w - w₀) ≤ 2 P(w) + 2 P(w₀)`, and `w - w₀ = m • 1`.
    have hsum := potentialForm_self_nonneg hV₀ (w + w₀)
    have h : potentialForm V (w - w₀) (w - w₀) ≤
        2 * potentialForm V w w + 2 * potentialForm V w₀ w₀ := by
      simp only [map_sub, map_add, sub_apply, add_apply] at hsum ⊢
      rw [potentialForm_comm V w₀ w] at hsum ⊢
      linarith
    rw [sub_sub_cancel] at h
    simpa [map_smul, smul_apply, smul_eq_mul, potentialForm_ofSmooth, one, ← mul_assoc, ← sq,
      mul_comm (m ^ 2)] using h
  have hD := dirichletForm_self_nonneg w
  have hP := potentialForm_self_nonneg hV₀ w
  have hm : m ^ 2 ≤ (2 * potentialForm V w w + 2 * (B * (C * dirichletForm w w))) / S := by
    rw [le_div_iff₀ hV]
    nlinarith [mul_le_mul_of_nonneg_left hL₀ hB]
  -- The `L²` norm of `w = w₀ + m • 1`.
  have hL : ‖toLp w‖ ^ 2 ≤ 2 * ‖toLp w₀‖ ^ 2 + 2 * (m ^ 2 * vol) := by
    have hpar := parallelogram_law_with_norm ℝ (toLp w₀) (toLp (m • one))
    have hw : toLp w₀ + toLp (m • one) = toLp w := by simp [w₀]
    rw [hw, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hone] at hpar
    nlinarith [sq_nonneg ‖toLp w₀ - m • toLp one‖]
  have hvS : 0 ≤ vol / S := by positivity
  have key : 2 * (m ^ 2 * vol) ≤
      4 * (vol / S) * potentialForm V w w + 4 * (vol / S) * (B * (C * dirichletForm w w)) := by
    have h := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2 * vol)
    calc 2 * (m ^ 2 * vol) = 2 * vol * m ^ 2 := by ring
      _ ≤ 2 * vol * ((2 * potentialForm V w w + 2 * (B * (C * dirichletForm w w))) / S) := h
      _ = _ := by ring
  rw [norm_sq_eq_dirichletForm_add]
  nlinarith [mul_nonneg hvS hP, mul_nonneg (mul_nonneg hvS (mul_nonneg hB hC0)) hP,
    mul_nonneg hC0 hP, mul_nonneg hvS hD]

/-- **The Schrödinger form is coercive.** On a closed connected manifold with a continuous metric,
`D + P_V` is coercive on `H¹(M)` for every nonnegative `V ∈ L^∞(M)` with `∫ V dV > 0`. -/
theorem isCoercive_dirichletForm_add_potentialForm {V : Lp ℝ ∞ (riemannianVolume I M)}
    (hV₀ : ∀ᵐ x ∂riemannianVolume I M, 0 ≤ V x) (hV : 0 < ∫ x, V x ∂riemannianVolume I M) :
    IsCoercive (dirichletForm + potentialForm V : SobolevH1 I M →L[ℝ] SobolevH1 I M →L[ℝ] ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_sq_le_mul_dirichletForm_add_potentialForm hV₀ hV
  refine ⟨(C + 1)⁻¹, by positivity, fun w ↦ ?_⟩
  have hD := dirichletForm_self_nonneg w
  have hP := potentialForm_self_nonneg hV₀ w
  rw [add_apply, add_apply, mul_assoc, ← sq, inv_mul_le_iff₀ (by positivity)]
  nlinarith [hC w]

/-! ### The weak Schrödinger equation -/

/-- **The weak Schrödinger equation on a closed manifold.** On a closed connected manifold with a
continuous metric, let `V ∈ L^∞(M)` be nonnegative with `∫ V dV > 0`. Then for every `f ∈ L²(M)`
there is exactly one `w ∈ H¹(M)` solving `Δ⁺w + V w = f` weakly, that is, with
`D(w, v) + ∫ V w v dV = ∫ f v dV` for every `v ∈ H¹(M)`, where `D` is the Dirichlet form. -/
theorem existsUnique_dirichletForm_add_potentialForm_eq {V : Lp ℝ ∞ (riemannianVolume I M)}
    (hV₀ : ∀ᵐ x ∂riemannianVolume I M, 0 ≤ V x) (hV : 0 < ∫ x, V x ∂riemannianVolume I M)
    (f : Lp ℝ 2 (riemannianVolume I M)) :
    ∃! w : SobolevH1 I M, ∀ v, dirichletForm w v + potentialForm V w v =
      ∫ x, f x * toLp v x ∂riemannianVolume I M := by
  -- The right-hand side as a continuous linear functional.
  set ℓ : StrongDual ℝ (SobolevH1 I M) := (innerSL ℝ f).comp toLp
  have hℓ (v : SobolevH1 I M) : ℓ v = ∫ x, f x * toLp v x ∂riemannianVolume I M := by
    simp [ℓ, L2.inner_def, mul_comm]
  simpa only [add_apply, hℓ] using
    (isCoercive_dirichletForm_add_potentialForm hV₀ hV).existsUnique_forall_eq ℓ

/-- **The weak inverse of `Δ⁺ + V` is bounded from `L²` to `H¹`.** On a closed connected manifold
with a continuous metric, let `V ∈ L^∞(M)` be nonnegative with `∫ V dV > 0`. Then there is a
constant `C` such that every weak solution `w ∈ H¹(M)` of `Δ⁺w + V w = f` satisfies
`‖w‖_{H¹} ≤ C ‖f‖_{L²}`. -/
theorem exists_norm_le_mul_norm_of_dirichletForm_add_potentialForm_eq
    {V : Lp ℝ ∞ (riemannianVolume I M)} (hV₀ : ∀ᵐ x ∂riemannianVolume I M, 0 ≤ V x)
    (hV : 0 < ∫ x, V x ∂riemannianVolume I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (riemannianVolume I M)) (w : SobolevH1 I M),
      (∀ v, dirichletForm w v + potentialForm V w v =
        ∫ x, f x * toLp v x ∂riemannianVolume I M) → ‖w‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_sq_le_mul_dirichletForm_add_potentialForm hV₀ hV
  refine ⟨C, hC0, fun f w hw ↦ ?_⟩
  -- Testing the equation against `w` itself: `D(w, w) + P_V(w, w) = ⟪f, w⟫_{L²}`.
  have hfw : dirichletForm w w + potentialForm V w w = ⟪f, toLp w⟫_ℝ := by
    rw [hw w, L2.inner_def]
    simp [mul_comm]
  have hle : ‖w‖ ^ 2 ≤ C * (‖f‖ * ‖w‖) := by
    refine (hC w).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    rw [hfw]
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_toLp_le w) (norm_nonneg f))
  rcases (norm_nonneg w).eq_or_lt with h | h
  · rw [← h]
    positivity
  · nlinarith

variable [IsManifold I ∞ M] [T2Space M]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **The distributional Schrödinger equation.** On a closed connected manifold with a `C¹`
metric, let `V ∈ L^∞(M)` be nonnegative with `∫ V dV > 0`, and let `f ∈ L²(M)`. Then there is
`w ∈ H¹(M)` with `∫ w Δ⁺φ dV + ∫ V w φ dV = ∫ f φ dV` for every smooth function `φ`, where
`Δ⁺ = -div grad`. -/
theorem exists_integral_mul_neg_laplaceBeltrami_add_eq {V : Lp ℝ ∞ (riemannianVolume I M)}
    (hV₀ : ∀ᵐ x ∂riemannianVolume I M, 0 ≤ V x) (hV : 0 < ∫ x, V x ∂riemannianVolume I M)
    (f : Lp ℝ 2 (riemannianVolume I M)) :
    ∃ w : SobolevH1 I M, ∀ φ : C^∞⟮I, M; ℝ⟯,
      ∫ x, toLp w x * -laplaceBeltrami I φ x ∂riemannianVolume I M +
          ∫ x, V x * toLp w x * φ x ∂riemannianVolume I M =
        ∫ x, f x * φ x ∂riemannianVolume I M := by
  obtain ⟨w, hw, -⟩ := existsUnique_dirichletForm_add_potentialForm_eq hV₀ hV f
  refine ⟨w, fun φ ↦ ?_⟩
  rw [← dirichletForm_ofSmooth_right, ← potentialForm_ofSmooth_right, hw]
  exact integral_congr_ae ((toLp_ofSmooth_ae_eq φ).mono fun x hx ↦ congrArg (f x * ·) hx)

end TauCeti.Manifold.SobolevH1
