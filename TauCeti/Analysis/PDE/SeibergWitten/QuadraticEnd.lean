/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The rank-one quadratic endomorphism of the Seiberg–Witten equations

For a vector `ψ` of a complex inner product space `E`, set
`Q₀(ψ) = ψψ* - (‖ψ‖² / 2) Id`, where `ψψ*` is `InnerProductSpace.rankOne ℂ ψ ψ`, the map
`v ↦ ⟪ψ, v⟫ ψ`. When `E` has complex dimension two (a fibre of the positive half-spinor bundle
of a `Spinᶜ` four-manifold), `Q₀(ψ)` is the trace-free part of `ψψ*`, and the Seiberg–Witten
curvature equation reads `C(F_A⁺) = Q₀(ψ)`, where `C` is Clifford multiplication by
self-dual two-forms.

This file proves the pointwise algebra and calculus of `Q₀` needed by the nonlinear analysis of
the equations. The map `Q₀` is real-quadratic but not complex-linear, so its polarization and its
derivative are only real-linear.

## Main definitions

* `TauCeti.SeibergWitten.quadraticEnd ψ`: the endomorphism `Q₀(ψ) = ψψ* - (‖ψ‖² / 2) Id`.
* `TauCeti.SeibergWitten.quadraticEndPolar`: its real polarization
  `B(ψ, φ) = φψ* + ψφ* - Re⟪ψ, φ⟫ Id`, as a continuous real-bilinear map.

## Main results

* `trace_quadraticEnd`: `Q₀(ψ)` is trace free when `E` has complex dimension two.
* `isSelfAdjoint_quadraticEnd`: `Q₀(ψ)` is self-adjoint.
* `quadraticEnd_apply_self`: `Q₀(ψ) ψ = (‖ψ‖² / 2) ψ`.
* `quadraticEnd_smul`, `quadraticEnd_smul_of_norm_eq_one`: `Q₀(c ψ) = |c|² Q₀(ψ)`; in particular
  `Q₀` is invariant under unit phases.
* `quadraticEnd_add`: `Q₀(ψ + φ) = Q₀(ψ) + Q₀(φ) + B(ψ, φ)`.
* `trace_quadraticEndPolar`, `isSelfAdjoint_quadraticEndPolar`: like `Q₀(ψ)`, every `B(ψ, φ)` is
  trace free in complex dimension two and self-adjoint.
* `norm_quadraticEnd_apply`, `norm_quadraticEnd`: `Q₀(ψ)` is `‖ψ‖² / 2` times an isometry, so
  its operator norm is `‖ψ‖² / 2`; in particular `Q₀(ψ) = 0` only for `ψ = 0`.
* `norm_quadraticEndPolar_le`, `norm_quadraticEnd_sub_le`: `‖B(ψ, φ)‖ ≤ ‖ψ‖ ‖φ‖` and
  `‖Q₀(ψ) - Q₀(φ)‖ ≤ ‖ψ - φ‖ (‖ψ‖ + ‖φ‖) / 2`.
* `hasFDerivAt_quadraticEnd`: the real Fréchet derivative of `Q₀` at `ψ` is `B(ψ, ·)`, that is
  `DQ₀|_ψ (φ) = φψ* + ψφ* - Re⟪ψ, φ⟫ Id`.
* `quadraticEndPolar_smul_self`: `B(ψ, c ψ) = 2 Re(c) Q₀(ψ)`, so the derivative kills the
  infinitesimal gauge directions `ξ ψ` with `ξ` imaginary.

## References

* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open InnerProductSpace ContinuousLinearMap
open scoped ComplexConjugate InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The rank-one quadratic endomorphism `Q₀(ψ) = ψψ* - (‖ψ‖² / 2) Id` of a complex inner product
space. In complex dimension two this is the trace-free part of `ψψ*`. -/
def quadraticEnd (ψ : E) : E →L[ℂ] E :=
  rankOne ℂ ψ ψ - ((‖ψ‖ : ℂ) ^ 2 / 2) • ContinuousLinearMap.id ℂ E

/-- Unfolding lemma for `quadraticEnd`. -/
theorem quadraticEnd_def (ψ : E) :
    quadraticEnd ψ = rankOne ℂ ψ ψ - ((‖ψ‖ : ℂ) ^ 2 / 2) • ContinuousLinearMap.id ℂ E :=
  (rfl)

/-- `Q₀(ψ) v = ⟪ψ, v⟫ ψ - (‖ψ‖² / 2) v`. -/
@[simp]
theorem quadraticEnd_apply (ψ v : E) :
    quadraticEnd ψ v = ⟪ψ, v⟫_ℂ • ψ - ((‖ψ‖ : ℂ) ^ 2 / 2) • v := by
  simp [quadraticEnd]

/-- `Q₀(0) = 0`. -/
@[simp]
theorem quadraticEnd_zero : quadraticEnd (0 : E) = 0 := by
  ext; simp

/-- `ψ` is an eigenvector of `Q₀(ψ)` with eigenvalue `‖ψ‖² / 2`. -/
theorem quadraticEnd_apply_self (ψ : E) :
    quadraticEnd ψ ψ = ((‖ψ‖ : ℂ) ^ 2 / 2) • ψ := by
  rw [quadraticEnd_apply, inner_self_eq_norm_sq_to_K, ← sub_smul, RCLike.ofReal_eq_complex_ofReal]
  congr 1
  ring

/-- `Q₀` is homogeneous of degree two for the real structure: `Q₀(c ψ) = |c|² Q₀(ψ)`. -/
theorem quadraticEnd_smul (c : ℂ) (ψ : E) :
    quadraticEnd (c • ψ) = ‖c‖ ^ 2 • quadraticEnd ψ := by
  simp only [quadraticEnd_def, map_smul, map_smulₛₗ, smul_apply, smul_smul, Complex.conj_mul',
    norm_smul]
  push_cast
  module

/-- `Q₀` is invariant under unit phases: `Q₀(u ψ) = Q₀(ψ)` when `|u| = 1`. -/
theorem quadraticEnd_smul_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) (ψ : E) :
    quadraticEnd (u • ψ) = quadraticEnd ψ := by
  simp [quadraticEnd_smul, hu]

/-- `Q₀(-ψ) = Q₀(ψ)`. -/
@[simp]
theorem quadraticEnd_neg (ψ : E) : quadraticEnd (-ψ) = quadraticEnd ψ := by
  simpa using quadraticEnd_smul_of_norm_eq_one (u := -1) (by simp) ψ

/-- In complex dimension two, `Q₀(ψ)` is trace free. -/
theorem trace_quadraticEnd [FiniteDimensional ℂ E] (h₂ : Module.finrank ℂ E = 2) (ψ : E) :
    LinearMap.trace ℂ E (quadraticEnd ψ) = 0 := by
  simp [quadraticEnd_def, trace_rankOne, h₂, inner_self_eq_norm_sq_to_K]

/-- `Q₀(ψ)` is self-adjoint. -/
theorem isSelfAdjoint_quadraticEnd [CompleteSpace E] (ψ : E) :
    IsSelfAdjoint (quadraticEnd ψ) := by
  simp [IsSelfAdjoint, quadraticEnd, star_eq_adjoint, adjoint_id]

/-- `Q₀(ψ)` scales the norm of every vector by exactly `‖ψ‖² / 2`: for `ψ ≠ 0` it is `‖ψ‖² / 2`
times the reflection fixing `ψ` and negating its orthogonal complement. -/
theorem norm_quadraticEnd_apply (ψ v : E) :
    ‖quadraticEnd ψ v‖ = ‖ψ‖ ^ 2 / 2 * ‖v‖ := by
  -- Write `Q₀(ψ) v = x - r v` with `x = ⟪ψ, v⟫ ψ` and `r = ‖ψ‖² / 2`. Since
  -- `‖x‖² = |⟪ψ, v⟫|² ‖ψ‖² = 2 r Re⟪x, v⟫`, the cross terms cancel in `‖x - r v‖²`.
  set r : ℝ := ‖ψ‖ ^ 2 / 2 with hr
  have hQ : quadraticEnd ψ v = ⟪ψ, v⟫_ℂ • ψ - r • v := by simp [hr, ← Complex.coe_smul]
  have hx : RCLike.re ⟪⟪ψ, v⟫_ℂ • ψ, v⟫_ℂ = ‖⟪ψ, v⟫_ℂ‖ ^ 2 := by
    rw [inner_smul_left, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [hQ, @norm_sub_sq ℂ, inner_smul_right_eq_smul, RCLike.smul_re, hx, norm_smul, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  ring

/-- The operator norm of `Q₀(ψ)` is at most `‖ψ‖² / 2`. -/
theorem norm_quadraticEnd_le (ψ : E) : ‖quadraticEnd ψ‖ ≤ ‖ψ‖ ^ 2 / 2 :=
  opNorm_le_bound _ (by positivity) fun v ↦ (norm_quadraticEnd_apply ψ v).le

/-- The operator norm of `Q₀(ψ)` is `‖ψ‖² / 2`. -/
@[simp]
theorem norm_quadraticEnd (ψ : E) : ‖quadraticEnd ψ‖ = ‖ψ‖ ^ 2 / 2 := by
  refine le_antisymm (norm_quadraticEnd_le ψ) ?_
  rcases eq_or_ne ψ 0 with rfl | hψ
  · simp
  -- Test the operator norm against `ψ` itself.
  have := (quadraticEnd ψ).le_opNorm ψ
  rw [norm_quadraticEnd_apply] at this
  exact le_of_mul_le_mul_right this (norm_pos_iff.2 hψ)

/-- `Q₀(ψ)` vanishes exactly when `ψ` does. -/
@[simp]
theorem quadraticEnd_eq_zero_iff {ψ : E} : quadraticEnd ψ = 0 ↔ ψ = 0 := by
  rw [← norm_eq_zero, norm_quadraticEnd]
  simp

/-- The real polarization `B(ψ, φ) = φψ* + ψφ* - Re⟪ψ, φ⟫ Id` of `Q₀`, as a continuous
real-bilinear map. It satisfies `Q₀(ψ + φ) = Q₀(ψ) + Q₀(φ) + B(ψ, φ)` and is the real Fréchet
derivative of `Q₀` at `ψ`. -/
def quadraticEndPolar : E →L[ℝ] E →L[ℝ] (E →L[ℂ] E) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun ψ φ ↦ rankOne ℂ φ ψ + rankOne ℂ ψ φ -
        ((Complex.re ⟪ψ, φ⟫_ℂ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E)
      (fun ψ ψ' φ ↦ by
        simp only [map_add, add_apply, inner_add_left, Complex.add_re, Complex.ofReal_add,
          add_smul]
        abel)
      (fun r ψ φ ↦ by
        rw [← Complex.coe_smul r ψ, ← Complex.coe_smul r (_ : E →L[ℂ] E)]
        simp only [map_smulₛₗ, smul_apply, inner_smul_left, Complex.conj_ofReal,
          Complex.re_ofReal_mul, Complex.ofReal_mul, mul_smul, smul_sub, smul_add,
          RingHom.id_apply])
      (fun ψ φ φ' ↦ by
        simp only [map_add, add_apply, inner_add_right, Complex.add_re, Complex.ofReal_add,
          add_smul]
        abel)
      (fun r ψ φ ↦ by
        rw [← Complex.coe_smul r φ, ← Complex.coe_smul r (_ : E →L[ℂ] E)]
        simp only [map_smulₛₗ, smul_apply, inner_smul_right, Complex.conj_ofReal,
          Complex.re_ofReal_mul, Complex.ofReal_mul, mul_smul, smul_sub, smul_add,
          RingHom.id_apply]))
    3 fun ψ φ ↦ by
      dsimp only [LinearMap.mk₂_apply]
      refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) ((norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_id_le (𝕜 := ℂ) (E := E)) (norm_nonneg _)))).trans ?_)
      rw [norm_rankOne, norm_rankOne, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have := (Complex.abs_re_le_norm ⟪ψ, φ⟫_ℂ).trans (norm_inner_le_norm ψ φ)
      linarith [mul_comm ‖ψ‖ ‖φ‖]

/-- Unfolding lemma for `quadraticEndPolar`. -/
theorem quadraticEndPolar_apply (ψ φ : E) :
    quadraticEndPolar ψ φ = rankOne ℂ φ ψ + rankOne ℂ ψ φ -
      ((Complex.re ⟪ψ, φ⟫_ℂ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ E :=
  (rfl)

/-- `B(ψ, φ) v = ⟪ψ, v⟫ φ + ⟪φ, v⟫ ψ - Re⟪ψ, φ⟫ v`. -/
@[simp]
theorem quadraticEndPolar_apply_apply (ψ φ v : E) :
    quadraticEndPolar ψ φ v = ⟪ψ, v⟫_ℂ • φ + ⟪φ, v⟫_ℂ • ψ - ((Complex.re ⟪ψ, φ⟫_ℂ : ℝ) : ℂ) • v :=
  (rfl)

/-- The polarization of `Q₀` is symmetric. -/
theorem quadraticEndPolar_comm (ψ φ : E) : quadraticEndPolar ψ φ = quadraticEndPolar φ ψ := by
  rw [quadraticEndPolar_apply, quadraticEndPolar_apply, add_comm (rankOne ℂ φ ψ),
    ← RCLike.re_to_complex, inner_re_symm, RCLike.re_to_complex]

/-- The polarization of `Q₀` restricts on the diagonal to `2 Q₀`. -/
@[simp]
theorem quadraticEndPolar_self (ψ : E) : quadraticEndPolar ψ ψ = 2 • quadraticEnd ψ := by
  ext v
  rw [quadraticEndPolar_apply, ← RCLike.re_to_complex, inner_self_eq_norm_sq]
  simp only [sub_apply, add_apply, smul_apply, quadraticEnd_apply, rankOne_apply,
    id_apply]
  push_cast
  module

/-- Real polarization of `Q₀`: `Q₀(ψ + φ) = Q₀(ψ) + Q₀(φ) + B(ψ, φ)`. -/
theorem quadraticEnd_add (ψ φ : E) :
    quadraticEnd (ψ + φ) = quadraticEnd ψ + quadraticEnd φ + quadraticEndPolar ψ φ := by
  ext v
  simp only [quadraticEndPolar_apply, add_apply, sub_apply, smul_apply, quadraticEnd_apply,
    rankOne_apply, id_apply, inner_add_left]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, norm_add_sq (𝕜 := ℂ),
    RCLike.re_to_complex]
  push_cast
  module

/-- In complex dimension two, the polarization `B(ψ, φ)` of `Q₀` is trace free. -/
theorem trace_quadraticEndPolar [FiniteDimensional ℂ E] (h₂ : Module.finrank ℂ E = 2)
    (ψ φ : E) : LinearMap.trace ℂ E (quadraticEndPolar ψ φ) = 0 := by
  simp [eq_sub_of_add_eq' (quadraticEnd_add ψ φ).symm, trace_quadraticEnd h₂]

/-- The polarization `B(ψ, φ)` of `Q₀` is self-adjoint. -/
theorem isSelfAdjoint_quadraticEndPolar [CompleteSpace E] (ψ φ : E) :
    IsSelfAdjoint (quadraticEndPolar ψ φ) := by
  rw [eq_sub_of_add_eq' (quadraticEnd_add ψ φ).symm]
  exact (isSelfAdjoint_quadraticEnd _).sub
    ((isSelfAdjoint_quadraticEnd _).add (isSelfAdjoint_quadraticEnd _))

/-- `B(ψ, i ψ) = 0`: the derivative of `Q₀` vanishes along the infinitesimal phase direction
`i ψ`. -/
@[simp]
theorem quadraticEndPolar_I_smul_self (ψ : E) : quadraticEndPolar ψ (Complex.I • ψ) = 0 := by
  ext v
  simp [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  module

/-- `B(ψ, c ψ) = 2 Re(c) Q₀(ψ)`. In particular `B(ψ, ξ ψ) = 0` for imaginary `ξ`: the derivative
of `Q₀` vanishes along the infinitesimal phase directions. -/
theorem quadraticEndPolar_smul_self (c : ℂ) (ψ : E) :
    quadraticEndPolar ψ (c • ψ) = (2 * c.re) • quadraticEnd ψ := by
  -- Split `c ψ = Re(c) ψ + Im(c) (i ψ)` and use real bilinearity.
  have hc : c • ψ = c.re • ψ + c.im • Complex.I • ψ := by
    nth_rw 1 [← c.re_add_im]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [hc, map_add, map_smul, map_smul, quadraticEndPolar_I_smul_self, smul_zero, add_zero,
    quadraticEndPolar_self]
  module

/-- `B(ψ - φ, ψ + φ) = 2 (Q₀(ψ) - Q₀(φ))`. -/
theorem quadraticEndPolar_sub_add (ψ φ : E) :
    quadraticEndPolar (ψ - φ) (ψ + φ) = 2 • (quadraticEnd ψ - quadraticEnd φ) := by
  rw [map_sub, map_add, sub_apply, sub_apply, quadraticEndPolar_self, quadraticEndPolar_self,
    quadraticEndPolar_comm φ ψ]
  abel

/-- The polarization of `Q₀` satisfies `‖B(ψ, φ)‖ ≤ ‖ψ‖ ‖φ‖`. -/
theorem norm_quadraticEndPolar_le (ψ φ : E) : ‖quadraticEndPolar ψ φ‖ ≤ ‖ψ‖ * ‖φ‖ := by
  -- First the weaker bound `‖B(ψ, φ)‖ ≤ (‖ψ‖² + ‖φ‖²) / 2`, from the parallelogram law.
  have key : ∀ ψ φ : E, ‖quadraticEndPolar ψ φ‖ ≤ (‖ψ‖ ^ 2 + ‖φ‖ ^ 2) / 2 := by
    intro ψ φ
    have h : (2 : ℝ) • quadraticEndPolar ψ φ = quadraticEnd (ψ + φ) - quadraticEnd (ψ - φ) := by
      rw [quadraticEnd_add, sub_eq_add_neg ψ φ, quadraticEnd_add, quadraticEnd_neg, map_neg]
      module
    have hle := norm_sub_le (quadraticEnd (ψ + φ)) (quadraticEnd (ψ - φ))
    rw [← h, norm_smul, Real.norm_two] at hle
    nlinarith [norm_quadraticEnd_le (ψ + φ), norm_quadraticEnd_le (ψ - φ),
      parallelogram_law_with_norm ℂ ψ φ]
  -- Then rescale `ψ` by `t = ‖φ‖ / ‖ψ‖`, using real bilinearity.
  rcases eq_or_ne ψ 0 with rfl | hψ
  · simp
  rcases eq_or_ne φ 0 with rfl | hφ
  · simp
  set t := ‖φ‖ / ‖ψ‖ with ht_def
  have ht : 0 < t := by positivity
  have htψ : t * ‖ψ‖ = ‖φ‖ := div_mul_cancel₀ _ (norm_ne_zero_iff.2 hψ)
  have hkey := key (t • ψ) φ
  rw [map_smul, smul_apply, norm_smul, norm_smul, Real.norm_of_nonneg ht.le, htψ] at hkey
  have hφ2 : t * (‖ψ‖ * ‖φ‖) = ‖φ‖ ^ 2 := by rw [← mul_assoc, htψ, sq]
  refine le_of_mul_le_mul_left ?_ ht
  linarith

/-- `Q₀` is locally Lipschitz: `‖Q₀(ψ) - Q₀(φ)‖ ≤ ‖ψ - φ‖ (‖ψ‖ + ‖φ‖) / 2`. -/
theorem norm_quadraticEnd_sub_le (ψ φ : E) :
    ‖quadraticEnd ψ - quadraticEnd φ‖ ≤ ‖ψ - φ‖ * (‖ψ‖ + ‖φ‖) / 2 := by
  have h := norm_quadraticEndPolar_le (ψ - φ) (ψ + φ)
  rw [quadraticEndPolar_sub_add, two_nsmul, ← two_smul ℝ, norm_smul, Real.norm_two] at h
  have := norm_add_le ψ φ
  have := norm_nonneg (ψ - φ)
  nlinarith

private theorem quadraticEnd_eq_smul_quadraticEndPolar :
    (quadraticEnd : E → E →L[ℂ] E) = fun ψ ↦ (1 / 2 : ℝ) • quadraticEndPolar ψ ψ := by
  ext1 ψ
  rw [quadraticEndPolar_self]
  module

/-- The real Fréchet derivative of `Q₀` at `ψ` is `B(ψ, ·)`, that is
`DQ₀|_ψ (φ) = φψ* + ψφ* - Re⟪ψ, φ⟫ Id`; this holds in the strict sense. -/
theorem hasStrictFDerivAt_quadraticEnd (ψ : E) :
    HasStrictFDerivAt quadraticEnd (quadraticEndPolar ψ) ψ := by
  rw [quadraticEnd_eq_smul_quadraticEndPolar]
  refine (((quadraticEndPolar (E := E)).hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id ψ)
    (hasStrictFDerivAt_id ψ)).const_smul (1 / 2 : ℝ)).congr_fderiv ?_
  -- The derivative of `ψ ↦ B(ψ, ψ)` is `φ ↦ B(ψ, φ) + B(φ, ψ)`; symmetry of `B` finishes.
  ext φ : 1
  simp [quadraticEndPolar_comm φ ψ]
  module

/-- The real Fréchet derivative of `Q₀` at `ψ` is `B(ψ, ·)`. -/
theorem hasFDerivAt_quadraticEnd (ψ : E) :
    HasFDerivAt quadraticEnd (quadraticEndPolar ψ) ψ :=
  (hasStrictFDerivAt_quadraticEnd ψ).hasFDerivAt

/-- The real Fréchet derivative of `Q₀` at `ψ` is `B(ψ, ·)`. -/
theorem fderiv_quadraticEnd (ψ : E) :
    fderiv ℝ quadraticEnd ψ = quadraticEndPolar ψ :=
  (hasFDerivAt_quadraticEnd ψ).fderiv

/-- `Q₀` is a smooth map of the underlying real vector space. -/
theorem contDiff_quadraticEnd {n : WithTop ℕ∞} :
    ContDiff ℝ n (quadraticEnd : E → E →L[ℂ] E) := by
  rw [quadraticEnd_eq_smul_quadraticEndPolar]
  have hB : ContDiff ℝ n fun p : E × E ↦ quadraticEndPolar p.1 p.2 :=
    (quadraticEndPolar (E := E)).isBoundedBilinearMap.contDiff
  exact (hB.comp (contDiff_id.prodMk contDiff_id)).const_smul _

end TauCeti.SeibergWitten
