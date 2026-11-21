/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.Equicontinuity
import TauCeti.Topology.Algebra.Module.FiniteDimension
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# The radial connection of an abelian Higgs pair and compactness modulo gauge in `Cᵏ`

The radial phase and the local compactness of abelian Higgs pairs in radial gauge are in
`TauCeti.Analysis.PDE.SeibergWitten.RadialGauge`; this file treats the gauge `exp (i K b)` as a
unitary map, bounds the derivatives of the radial connection by those of the curvature, and
extracts limits of the connections in `Cᵏ_loc`.

Let `(a, α)` be a pair consisting of an imaginary connection form `a = i b` on the trivial
Hermitian line over a real normed space `E` and a section `α : E → ℂ`, with covariant derivative
`∇_b α = dα + i b α` (`TauCeti.SeibergWitten.covariantDeriv`). A circle-valued gauge `u` acts by
`(b, α) ↦ (b - Im (u⁻¹ du), u α)` and `∇_{b - Im (u⁻¹ du)} (u α) = u ∇_b α`
(`TauCeti.SeibergWitten.covariantDeriv_sub_phaseForm_mul`), while the curvature `-db` is
unchanged. The connection form itself can be large in a bad gauge even when the curvature is
small; this file chooses a gauge in which the connection is controlled by the curvature alone.

Fix a centre `x₀`. Contracting the curvature along the rays from `x₀` with the Poincaré homotopy
operator `K` (`TauCeti.poincareHomotopy`) gives the **radial connection**

`b_rad = K (db)`,  `b_rad(x) = ∫₀¹ t db(x₀ + t (x - x₀))(x - x₀, ·) dt`

(`TauCeti.SeibergWitten.radialConnection`). It vanishes on the radial direction,
`b_rad(x)(x - x₀) = 0` (`TauCeti.SeibergWitten.radialConnection_apply_sub_center`), and has the same
curvature as `b` (`TauCeti.SeibergWitten.extDeriv_radialConnection`). By the homotopy formula
`d (K b) + K (db) = b`, the gauge `u = exp (i K b)` with phase
`(K b)(x) = ∫₀¹ b(x₀ + t (x - x₀))(x - x₀) dt` (`TauCeti.SeibergWitten.radialGauge`) satisfies
`Im (u⁻¹ du) = b - b_rad` (`TauCeti.SeibergWitten.phaseForm_radialGauge`): it carries `(b, α)` to
the pair `(b_rad, u α)` in **radial gauge**, and fixes the fibre over `x₀`, `u(x₀) = 1`. The
radial connection depends only on the curvature, so it is unchanged by gauge transformations of `b`
(`TauCeti.SeibergWitten.radialConnection_sub_phaseForm`).

Since `b_rad` is an integral of the curvature, its derivatives on a ball about `x₀` are bounded
by those of the curvature: for every order `i` there is a constant `A`, depending only on `x₀`,
the radius and `i`, with `‖Dⁱ b_rad‖ ≤ A sup_{j ≤ i} ‖Dʲ db‖` on the ball
(`TauCeti.SeibergWitten.exists_norm_iteratedFDeriv_radialConnection_le`). In radial gauge the
section has `d(u α) = u ∇_b α - i b_rad u α`, so its derivative is bounded by the gauge invariant
quantities `|∇_b α|` and `|α|` together with `|b_rad|`
(`TauCeti.SeibergWitten.norm_fderiv_radialGauge_mul_le`).

This radial, or exponential, gauge gives **compactness modulo gauge**
(`TauCeti.SeibergWitten.exists_strictMono_tendstoLocallyUniformlyOn_radialConnection`): for a
sequence of pairs on a finite-dimensional space whose curvatures have derivatives of order at most
`k + 1` bounded on a ball about `x₀`, and whose sections satisfy `|α| ≤ C` and `|∇_b α| ≤ C` there,
a subsequence of the radial gauge pairs converges on the ball: the connections in `Cᵏ_loc`, that
is with their derivatives of order at most `k` locally uniformly on the ball, and the sections
locally uniformly. Taubes's analysis supplies such bounds for the large-parameter Seiberg–Witten
fields rescaled by `r^(-1/2)` about a point, and this is the step that extracts their limits modulo
gauge. Convergence of the sections in `Cᵏ` would need bounds on their higher
covariant derivatives, which are not treated here.

## Main definitions

* `TauCeti.SeibergWitten.radialConnection x₀ b`: the connection form `K (db)` in radial gauge.
* `TauCeti.SeibergWitten.radialGauge x₀ b`: the gauge `exp (i K b)` carrying `b` to it.

## References

* K. K. Uhlenbeck, *Removable singularities in Yang–Mills fields*, Comm. Math. Phys. 83 (1982),
  11–29, Section 2 (exponential gauge).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open ContinuousAlternatingMap Complex Filter Metric Set
open scoped Topology

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : E → ℂ} {x₀ x : E}

/-! ### The radial gauge -/

/-- The **radial connection** `K (db)` with centre `x₀`: the Poincaré homotopy operator applied
to the curvature `db` of the connection form `b`. It is the connection form of the gauge
equivalent pair in radial gauge (`TauCeti.SeibergWitten.phaseForm_radialGauge`). -/
def radialConnection (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) : E → E [⋀^Fin 1]→L[ℝ] ℝ :=
  poincareHomotopy x₀ (extDeriv b)

theorem radialConnection_def (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) :
    radialConnection x₀ b = poincareHomotopy x₀ (extDeriv b) :=
  (rfl)

/-- The **radial gauge** with centre `x₀`: the circle-valued function `exp (i (K b))`, whose phase
`(K b)(x) = ∫₀¹ b(x₀ + t (x - x₀))(x - x₀) dt` is the Poincaré homotopy operator applied to `b`.
It carries `b` to the radial connection (`TauCeti.SeibergWitten.phaseForm_radialGauge`). -/
def radialGauge (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (x : E) : ℂ :=
  exp ((poincareHomotopy x₀ b x 0 : ℝ) * I)

theorem radialGauge_def (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (x : E) :
    radialGauge x₀ b x = exp ((poincareHomotopy x₀ b x 0 : ℝ) * I) :=
  (rfl)

/-- The radial gauge takes values in the unit circle. -/
@[simp]
theorem norm_radialGauge (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (x : E) :
    ‖radialGauge x₀ b x‖ = 1 :=
  norm_exp_ofReal_mul_I _

/-- The radial gauge fixes the fibre over the centre. -/
@[simp]
theorem radialGauge_self (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) : radialGauge x₀ b x₀ = 1 := by
  simp [radialGauge]

/-- The radial connection vanishes at the centre. -/
@[simp]
theorem radialConnection_self (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) :
    radialConnection x₀ b x₀ = 0 :=
  poincareHomotopy_self x₀ _

/-- The radial connection vanishes on the radial direction `x - x₀`. -/
@[simp]
theorem radialConnection_apply_sub_center (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) (x : E) :
    radialConnection x₀ b x (fun _ ↦ x - x₀) = 0 := by
  rw [radialConnection, ← Matrix.vecCons_const]
  exact poincareHomotopy_apply_vecCons_sub_center x₀ _ x _

/-- The radial gauge is as smooth as the connection form. -/
theorem contDiff_radialGauge {r : ℕ∞} (x₀ : E) (hb : ContDiff ℝ r b) :
    ContDiff ℝ r (radialGauge x₀ b) :=
  ((ofRealCLM.contDiff.comp (contDiff_poincareHomotopy_apply_zero x₀ hb)).mul
    contDiff_const).cexp

/-- The radial connection of a `C^(r + 1)` connection form is `C^r`. -/
theorem contDiff_radialConnection {r : ℕ∞} (x₀ : E) (hb : ContDiff ℝ (r + 1) b) :
    ContDiff ℝ r (radialConnection x₀ b) :=
  contDiff_poincareHomotopy x₀ (contDiff_extDeriv hb le_rfl)

/-- **The radial gauge.** The gauge `u = exp (i K b)` carries the connection form `b` to the
radial connection `K (db)`: its phase form is `Im (u⁻¹ du) = b - K (db)`. This is the homotopy
formula `d (K b) + K (db) = b`. -/
theorem phaseForm_radialGauge (x₀ : E) (hb : ContDiff ℝ 1 b) (x : E) :
    phaseForm (radialGauge x₀ b) x = b x - radialConnection x₀ b x := by
  set f : E → ℝ := fun y ↦ poincareHomotopy x₀ b y 0 with hf_def
  have hf : DifferentiableAt ℝ f x :=
    (contDiff_poincareHomotopy_apply_zero x₀ hb).differentiable one_ne_zero x
  -- The homotopy formula, with the zero-form `K b` read as the function `f`.
  have hK : poincareHomotopy x₀ b = fun y ↦ constOfIsEmpty ℝ E (Fin 0) (f y) := by
    funext y
    rw [← constOfIsEmptyLIE_apply (𝕜 := ℝ), hf_def]
    beta_reduce
    rw [← constOfIsEmptyLIE_symm_apply (𝕜 := ℝ), LinearIsometryEquiv.apply_symm_apply]
  have hhom := extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv x₀ hb x
  rw [hK, extDeriv_constOfIsEmpty] at hhom
  rw [radialConnection, ← hhom, add_sub_cancel_right]
  -- The phase form of `exp (i f)` is `df`.
  have hd : HasFDerivAt (radialGauge x₀ b)
      (radialGauge x₀ b x • ((ContinuousLinearMap.mul ℝ ℂ).flip I).comp
        (ofRealCLM.comp (fderiv ℝ f x))) x :=
    ((ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt).mul_const' I).cexp
  ext v
  rw [phaseForm_apply, hd.fderiv]
  have hu0 : radialGauge x₀ b x ≠ 0 := exp_ne_zero _
  simp [hu0, hf_def]

/-- The radial connection is the gauge transform of `b` by the radial gauge,
`K (db) = b - Im (u⁻¹ du)` for `u = exp (i K b)`. -/
theorem sub_phaseForm_radialGauge (x₀ : E) (hb : ContDiff ℝ 1 b) :
    b - phaseForm (radialGauge x₀ b) = radialConnection x₀ b := by
  funext x
  rw [Pi.sub_apply, phaseForm_radialGauge x₀ hb, sub_sub_cancel]

/-- **Covariance in radial gauge.** The radial gauge carries the section `α` to `u α` with
`∇_{K (db)} (u α) = u ∇_b α`. -/
theorem covariantDeriv_radialConnection_radialGauge_mul (x₀ : E) (hb : ContDiff ℝ 1 b)
    (hα : DifferentiableAt ℝ α x) :
    covariantDeriv (radialConnection x₀ b) (radialGauge x₀ b * α) x =
      radialGauge x₀ b x • covariantDeriv b α x := by
  rw [← sub_phaseForm_radialGauge x₀ hb]
  exact covariantDeriv_sub_phaseForm_mul (.of_forall (norm_radialGauge x₀ b))
    ((contDiff_radialGauge x₀ hb).differentiable one_ne_zero x) hα

/-- The radial connection has the same curvature as `b`. -/
theorem extDeriv_radialConnection (x₀ : E) (hb : ContDiff ℝ 2 b) :
    extDeriv (radialConnection x₀ b) = extDeriv b := by
  funext x
  have h := extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv x₀
    (contDiff_extDeriv hb (by norm_num)) x
  rwa [extDeriv_extDeriv hb (by simp), poincareHomotopy_zero, Pi.zero_apply, add_zero] at h

/-- **Gauge invariance.** The radial connection depends only on the curvature, so it does not
change under a gauge transformation `b ↦ b - Im (u⁻¹ du)` by a nowhere vanishing `C²` function
`u`. -/
theorem radialConnection_sub_phaseForm (x₀ : E) (b : E → E [⋀^Fin 1]→L[ℝ] ℝ) {u : E → ℂ}
    (hu : ContDiff ℝ 2 u) (hu₀ : ∀ y, u y ≠ 0) :
    radialConnection x₀ (b - phaseForm u) = radialConnection x₀ b := by
  rw [radialConnection, radialConnection]
  congr 1
  funext y
  have hφ : DifferentiableAt ℝ (phaseForm u) y :=
    (contDiffAt_phaseForm hu.contDiffAt (hu₀ y)
      (by norm_num : ((1 : ℕ) : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt one_ne_zero
  by_cases hb : DifferentiableAt ℝ b y
  · rw [extDeriv_sub hb hφ, extDeriv_phaseForm hu.contDiffAt (hu₀ y), sub_zero]
  · -- Neither `b` nor `b - Im (u⁻¹ du)` is differentiable at `y`, so both derivatives vanish.
    have hb' : ¬ DifferentiableAt ℝ (b - phaseForm u) y := fun h ↦
      hb (by simpa using h.add hφ)
    rw [extDeriv_zero_of_not_differentiableAt hb,
      extDeriv_zero_of_not_differentiableAt hb']

/-- In radial gauge the derivative of the section is controlled by gauge invariant quantities and
the radial connection: `|d(u α)| ≤ |∇_b α| + |K (db)| |α|`, since
`d(u α) = u ∇_b α - i K (db) u α`. -/
theorem norm_fderiv_radialGauge_mul_le (x₀ : E) (hb : ContDiff ℝ 1 b)
    (hα : DifferentiableAt ℝ α x) :
    ‖fderiv ℝ (radialGauge x₀ b * α) x‖ ≤
      ‖covariantDeriv b α x‖ + ‖radialConnection x₀ b x‖ * ‖α x‖ := by
  have hβ : fderiv ℝ (radialGauge x₀ b * α) x =
      covariantDeriv (radialConnection x₀ b) (radialGauge x₀ b * α) x -
        ((ofSubsingletonLIE (0 : Fin 1)).symm (radialConnection x₀ b x)).smulRight
          (I * (radialGauge x₀ b * α) x) := by
    ext v
    simp only [Pi.mul_apply, _root_.sub_apply, covariantDeriv_apply,
      ContinuousLinearMap.smulRight_apply, ofSubsingletonLIE_symm_apply,
      ofSubsingleton_symm_apply_apply, real_smul]
    ring
  rw [hβ]
  refine (norm_sub_le _ _).trans (add_le_add (le_of_eq ?_) (le_of_eq ?_))
  · rw [covariantDeriv_radialConnection_radialGauge_mul x₀ hb hα, norm_smul, norm_radialGauge,
      one_mul]
  · simp [ContinuousLinearMap.norm_smulRight_apply, -ofSubsingletonLIE_symm_apply]

/-- Pointwise bounds `|α| ≤ C`, `|∇_b α| ≤ C` and `|K (db)| ≤ M` bound the derivatives of order
at most `1` of the section `u α` in radial gauge by `C + M C`. -/
private theorem norm_iteratedFDeriv_radialGauge_mul_le (x₀ : E) (hb : ContDiff ℝ 1 b)
    (hα : DifferentiableAt ℝ α x) {C M : ℝ} (hM0 : 0 ≤ M) (hαC : ‖α x‖ ≤ C)
    (hcov : ‖covariantDeriv b α x‖ ≤ C) (hM : ‖radialConnection x₀ b x‖ ≤ M) {j : ℕ}
    (hj : j ≤ 1) :
    ‖iteratedFDeriv ℝ j (radialGauge x₀ b * α) x‖ ≤ C + M * C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hαC
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · rw [norm_iteratedFDeriv_zero, Pi.mul_apply, norm_mul, norm_radialGauge, one_mul]
    exact hαC.trans (le_add_of_nonneg_right (mul_nonneg hM0 hC))
  · rw [norm_iteratedFDeriv_one]
    exact (norm_fderiv_radialGauge_mul_le x₀ hb hα).trans
      (add_le_add hcov (mul_le_mul hM hαC (norm_nonneg _) hM0))

/-! ### Derivative bounds and compactness modulo gauge -/

/-- **Derivative bounds in radial gauge.** On a ball about the centre, the derivatives of order
`i` of the radial connection are bounded by a constant times a bound on the derivatives of order
at most `i` of the curvature. The constant depends only on the centre, the radius and `i`. -/
theorem exists_norm_iteratedFDeriv_radialConnection_le [FiniteDimensional ℝ E] (x₀ : E) (R : ℝ)
    (i : ℕ) :
    ∃ A, 0 ≤ A ∧ ∀ {b : E → E [⋀^Fin 1]→L[ℝ] ℝ}, ContDiff ℝ (i + 1) b → ∀ {B : ℝ},
      (∀ j ≤ i, ∀ z ∈ ball x₀ R, ‖iteratedFDeriv ℝ j (extDeriv b) z‖ ≤ B) →
      ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ i (radialConnection x₀ b) x‖ ≤ A * B := by
  rcases le_or_gt R 0 with hR | hR
  · exact ⟨0, le_rfl, fun _ _ _ x hx ↦ absurd hx (by simp [ball_eq_empty.2 hR])⟩
  -- Cut off outside the ball: the cutoff is `1` on the ball, where it does not change derivatives.
  let χ : ContDiffBump x₀ := ⟨R, R + 1, hR, by linarith⟩
  obtain ⟨A, hA0, hA⟩ := exists_norm_iteratedFDeriv_smul_poincareHomotopy_le (F := ℝ) x₀ 1
    (i := i) χ.contDiff χ.hasCompactSupport
  refine ⟨A, hA0, fun {b} hb {B} hB x hx ↦ ?_⟩
  have heq : (fun y ↦ χ y • radialConnection x₀ b y) =ᶠ[𝓝 x] radialConnection x₀ b := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_smul]
  rw [← (heq.iteratedFDeriv ℝ i).eq_of_nhds]
  exact hA (contDiff_extDeriv hb le_rfl) fun j hj z hz ↦
    hB j hj z ((convex_ball x₀ R).segment_subset (mem_ball_self hR) hx hz)

/-- Uniform bounds on the derivatives of order at most `k + 1` of the radial connections of a
sequence of connection forms, on a ball about the centre, from uniform bounds on the derivatives of
their curvatures. -/
private theorem exists_forall_norm_iteratedFDeriv_radialConnection_le [FiniteDimensional ℝ E]
    {b : ℕ → E → E [⋀^Fin 1]→L[ℝ] ℝ} (x₀ : E) (R : ℝ) (k : ℕ)
    (hb : ∀ n, ContDiff ℝ (k + 2) (b n)) {A : ℝ}
    (hF : ∀ n, ∀ j ≤ k + 1, ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ j (extDeriv (b n)) x‖ ≤ A) :
    ∃ M, 0 ≤ M ∧ ∀ n, ∀ j ≤ k + 1, ∀ x ∈ ball x₀ R,
      ‖iteratedFDeriv ℝ j (radialConnection x₀ (b n)) x‖ ≤ M := by
  choose! A' hA'0 hA' using exists_norm_iteratedFDeriv_radialConnection_le x₀ R
  refine ⟨∑ j ∈ Finset.range (k + 2), A' j * |A|,
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hA'0 j) (abs_nonneg A), fun n j hj x hx ↦ ?_⟩
  calc ‖iteratedFDeriv ℝ j (radialConnection x₀ (b n)) x‖
      ≤ A' j * A :=
        hA' j ((hb n).of_le (by norm_cast; omega)) (fun i hi ↦ hF n i (by omega)) x hx
    _ ≤ A' j * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) (hA'0 j)
    _ ≤ ∑ j ∈ Finset.range (k + 2), A' j * |A| :=
        Finset.single_le_sum (fun j _ ↦ mul_nonneg (hA'0 j) (abs_nonneg A))
          (Finset.mem_range.2 (by omega))

/-- **Compactness modulo gauge.** Let `(bₙ, αₙ)` be pairs on a finite-dimensional space, with
`bₙ` of class `C^(k+2)` and `αₙ` of class `C¹`, whose curvatures have derivatives of order at most
`k + 1` bounded by `A` on the ball of radius `R` about `x₀`, and whose sections satisfy `|αₙ| ≤ C`
and `|∇_{bₙ} αₙ| ≤ C` there. Then along a subsequence the radial gauge pairs
`(K (dbₙ), uₙ αₙ)` converge on the ball: the radial connections, with their derivatives of order at
most `k`, locally uniformly to a connection form `b` of class `Cᵏ`, and the sections locally
uniformly to a continuous section. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_radialConnection [FiniteDimensional ℝ E]
    {b : ℕ → E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : ℕ → E → ℂ} (x₀ : E) (R : ℝ) (k : ℕ)
    (hb : ∀ n, ContDiff ℝ (k + 2) (b n)) (hα : ∀ n, ContDiff ℝ 1 (α n)) {A C : ℝ}
    (hF : ∀ n, ∀ j ≤ k + 1, ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ j (extDeriv (b n)) x‖ ≤ A)
    (hαC : ∀ n, ∀ x ∈ ball x₀ R, ‖α n x‖ ≤ C)
    (hcov : ∀ n, ∀ x ∈ ball x₀ R, ‖covariantDeriv (b n) (α n) x‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (b' : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α' : E → ℂ),
      ContDiffOn ℝ k b' (ball x₀ R) ∧ ContinuousOn α' (ball x₀ R) ∧
      (∀ j ≤ k, TendstoLocallyUniformlyOn
        (fun n ↦ iteratedFDeriv ℝ j (radialConnection x₀ (b (φ n)))) (iteratedFDeriv ℝ j b')
          atTop (ball x₀ R)) ∧
      TendstoLocallyUniformlyOn (fun n ↦ radialGauge x₀ (b (φ n)) * α (φ n)) α' atTop
        (ball x₀ R) := by
  have hb1 (n : ℕ) : ContDiff ℝ 1 (b n) := (hb n).of_le (by norm_cast; omega)
  obtain ⟨M, hM0, hM⟩ := exists_forall_norm_iteratedFDeriv_radialConnection_le x₀ R k hb hF
  -- The radial connections converge in `Cᵏ` along a subsequence.
  obtain ⟨φ, hφ, b', hb', hconv⟩ := exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv
    isOpen_ball k (fun n ↦ (contDiff_radialConnection x₀ ((hb n).of_le (by norm_cast))).contDiffOn)
    fun K _ hK ↦ ⟨M, fun n j hj x hx ↦ hM n j hj x (hK hx)⟩
  -- In radial gauge the sections are bounded with bounded derivatives, so they converge along a
  -- further subsequence.
  have hβ (n : ℕ) : ContDiff ℝ 1 (radialGauge x₀ (b (φ n)) * α (φ n)) :=
    (contDiff_radialGauge x₀ (hb1 (φ n))).mul (hα (φ n))
  obtain ⟨ψ, hψ, α', hα', hconvα⟩ := exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv
    isOpen_ball 0 (fun n ↦ (hβ n).contDiffOn) fun K _ hK ↦ ⟨C + M * C, fun n j hj x hx ↦
      norm_iteratedFDeriv_radialGauge_mul_le x₀ (hb1 (φ n))
        ((hα (φ n)).differentiable one_ne_zero x) hM0 (hαC (φ n) x (hK hx))
        (hcov (φ n) x (hK hx))
        (by simpa using hM (φ n) 0 (Nat.zero_le _) x (hK hx)) hj⟩
  exact ⟨φ ∘ ψ, hφ.comp hψ, b', α', hb', contDiffOn_zero.1 hα',
    fun j hj ↦ (hconv j hj).comp_tendsto hψ.tendsto_atTop,
    tendstoLocallyUniformlyOn_iteratedFDeriv_zero_iff.1 (hconvα 0 le_rfl)⟩

end TauCeti.SeibergWitten
