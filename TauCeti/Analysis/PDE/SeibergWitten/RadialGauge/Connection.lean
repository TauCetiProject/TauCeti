/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.SeibergWitten.IteratedCovariantDeriv
public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Calculus.ContDiff.Pi
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
gauge.

The sections converge in `Cˡ`, for `l ≤ k + 1`, when their higher covariant derivatives are
bounded. The radial gauge multiplies the iterated covariant derivatives `∇ʲ α`
(`iteratedCovariantDeriv`) by `u`, so their norms are unchanged
(`TauCeti.SeibergWitten.norm_iteratedCovariantDeriv_radialConnection_radialGauge_mul`), and in
radial gauge the connection form is bounded with its derivatives, so bounds on `∇ʲ α` for
`j ≤ l + 1` bound the derivatives of order at most `l + 1` of `u α`
(`TauCeti.SeibergWitten.exists_norm_iteratedFDeriv_le_of_norm_iteratedCovariantDeriv_le`). A
subsequence of the radial gauge pairs then converges on the ball, the connections in `Cᵏ_loc` and
the sections in `Cˡ_loc`
(`exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv_radialGauge_mul`); the compactness
above is its case `l = 0`. When the bounds hold on every ball about `x₀`, uniformly for finitely
many sections transformed by the same gauge, such as the components of a spinor, one subsequence
converges in this sense on the whole space
(`exists_strictMono_tendstoLocallyUniformly_iteratedFDeriv_radialGauge_mul`).
These are the gauge-theoretic half of the local compactness of Taubes's rescaled solutions; the
bounds on the curvature and on the covariant derivatives themselves come from the equations.

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
    {ι : Type*} {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} (x₀ : E) (R : ℝ) (k : ℕ)
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

/-- **Covariance in radial gauge.** The radial gauge carries the iterated covariant derivatives
of `α` for `b` to those of `u α` for the radial connection:
`∇ⁿ_{K (db)} (u α) = u ∇ⁿ_b α` for `u = exp (i K b)`. -/
theorem iteratedCovariantDeriv_radialConnection_radialGauge_mul (x₀ : E) {n : ℕ}
    (hb : ContDiff ℝ (max (n - 1) 1 : ℕ) b) (hα : ContDiff ℝ n α) (x : E) :
    iteratedCovariantDeriv (radialConnection x₀ b) (radialGauge x₀ b * α) n x =
      radialGauge x₀ b x • iteratedCovariantDeriv b α n x := by
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_cast; omega)
  rw [← sub_phaseForm_radialGauge x₀ hb1]
  exact congrFun (iteratedCovariantDeriv_sub_phaseForm_mul (norm_radialGauge x₀ b)
    ((contDiff_radialGauge x₀ hb1).differentiable one_ne_zero) hα
    (hb.of_le (by norm_cast; omega))) x

/-- The radial gauge preserves the norms of the iterated covariant derivatives. -/
theorem norm_iteratedCovariantDeriv_radialConnection_radialGauge_mul (x₀ : E) {n : ℕ}
    (hb : ContDiff ℝ (max (n - 1) 1 : ℕ) b) (hα : ContDiff ℝ n α) (x : E) :
    ‖iteratedCovariantDeriv (radialConnection x₀ b) (radialGauge x₀ b * α) n x‖ =
      ‖iteratedCovariantDeriv b α n x‖ := by
  rw [iteratedCovariantDeriv_radialConnection_radialGauge_mul x₀ hb hα, norm_smul,
    norm_radialGauge, one_mul]

/-- The radial gauge of a `C^(k+2)` connection form, times a `C^(l+1)` section with `l ≤ k + 1`,
is `C^(l+1)`. -/
private theorem contDiff_radialGauge_mul {k l : ℕ} (hl : l ≤ k + 1) (x₀ : E)
    (hb : ContDiff ℝ (k + 2) b) (hα : ContDiff ℝ (l + 1) α) :
    ContDiff ℝ (l + 1) (radialGauge x₀ b * α) :=
  ((contDiff_radialGauge x₀ hb).of_le
    (by beta_reduce; exact_mod_cast (by omega : l + 1 ≤ k + 2))).mul hα

/-- Uniform bounds on the derivatives of order at most `l + 1` of a family of sections in radial
gauge, on a ball about the centre, from uniform bounds on the derivatives of order at most `k + 1`
of the curvatures and on the iterated covariant derivatives of order at most `l + 1` of the
sections. -/
private theorem exists_forall_norm_iteratedFDeriv_radialGauge_mul_le [FiniteDimensional ℝ E]
    {ι : Type*} {b : ι → E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : ι → E → ℂ} (x₀ : E) (R : ℝ) {k l : ℕ}
    (hl : l ≤ k + 1) (hb : ∀ n, ContDiff ℝ (k + 2) (b n)) (hα : ∀ n, ContDiff ℝ (l + 1) (α n))
    {A C : ℝ}
    (hF : ∀ n, ∀ j ≤ k + 1, ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ j (extDeriv (b n)) x‖ ≤ A)
    (hcov : ∀ n, ∀ j ≤ l + 1, ∀ x ∈ ball x₀ R, ‖iteratedCovariantDeriv (b n) (α n) j x‖ ≤ C) :
    ∃ B, 0 ≤ B ∧ ∀ n, ∀ j ≤ l + 1, ∀ x ∈ ball x₀ R,
      ‖iteratedFDeriv ℝ j (radialGauge x₀ (b n) * α n) x‖ ≤ B := by
  obtain ⟨M, -, hM⟩ := exists_forall_norm_iteratedFDeriv_radialConnection_le x₀ R k hb hF
  choose K hK using fun m ↦
    exists_norm_iteratedFDeriv_le_of_norm_iteratedCovariantDeriv_le (E := E) C M m
  refine ⟨∑ i ∈ Finset.range (l + 2), |K i|, Finset.sum_nonneg fun i _ ↦ abs_nonneg (K i),
    fun n j hj x hx ↦ ?_⟩
  have hc : ContDiff ℝ (k + 1) (radialConnection x₀ (b n)) := contDiff_radialConnection x₀ (hb n)
  refine (hK j ((contDiff_radialGauge_mul hl x₀ (hb n) (hα n)).of_le (by norm_cast))
    (hc.of_le (by norm_cast; omega)) (fun i hi y hy ↦ ?_)
    (fun i hi y hy ↦ hM n i (by omega) y hy) x hx).trans
    ((le_abs_self _).trans (Finset.single_le_sum (fun i _ ↦ abs_nonneg (K i))
      (Finset.mem_range.2 (by omega))))
  rw [norm_iteratedCovariantDeriv_radialConnection_radialGauge_mul x₀
    ((hb n).of_le (by norm_cast; omega)) ((hα n).of_le (by norm_cast; omega))]
  exact hcov n i (by omega) y hy

/-- **Compactness modulo gauge in `Cᵏ`.** Let `(bₙ, αₙ)` be pairs on a finite-dimensional space,
with `bₙ` of class `C^(k+2)` and `αₙ` of class `C^(l+1)` for some `l ≤ k + 1`, whose curvatures
have derivatives of order at most `k + 1` bounded by `A` on the ball of radius `R` about `x₀`, and
whose iterated covariant derivatives `∇ʲ αₙ` of order at most `l + 1` are bounded by `C` there.
Then along a subsequence the radial gauge pairs `(K (dbₙ), uₙ αₙ)` converge on the ball: the
radial connections, with their derivatives of order at most `k`, converge locally uniformly on the
ball to a connection form `b` of class `Cᵏ`, and the sections, with their derivatives of order at
most `l`, to a section `α` of class `Cˡ`. -/
theorem exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv_radialGauge_mul
    [FiniteDimensional ℝ E] {b : ℕ → E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : ℕ → E → ℂ} (x₀ : E) (R : ℝ)
    (k l : ℕ) (hl : l ≤ k + 1) (hb : ∀ n, ContDiff ℝ (k + 2) (b n))
    (hα : ∀ n, ContDiff ℝ (l + 1) (α n)) {A C : ℝ}
    (hF : ∀ n, ∀ j ≤ k + 1, ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ j (extDeriv (b n)) x‖ ≤ A)
    (hcov : ∀ n, ∀ j ≤ l + 1, ∀ x ∈ ball x₀ R, ‖iteratedCovariantDeriv (b n) (α n) j x‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (b' : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α' : E → ℂ),
      ContDiffOn ℝ k b' (ball x₀ R) ∧ ContDiffOn ℝ l α' (ball x₀ R) ∧
      (∀ j ≤ k, TendstoLocallyUniformlyOn
        (fun n ↦ iteratedFDeriv ℝ j (radialConnection x₀ (b (φ n)))) (iteratedFDeriv ℝ j b')
          atTop (ball x₀ R)) ∧
      ∀ j ≤ l, TendstoLocallyUniformlyOn
        (fun n ↦ iteratedFDeriv ℝ j (radialGauge x₀ (b (φ n)) * α (φ n)))
          (iteratedFDeriv ℝ j α') atTop (ball x₀ R) := by
  obtain ⟨M, -, hM⟩ := exists_forall_norm_iteratedFDeriv_radialConnection_le x₀ R k hb hF
  -- The radial connections converge in `Cᵏ` along a subsequence.
  obtain ⟨φ, hφ, b', hb', hconv⟩ := exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv
    isOpen_ball k (fun n ↦ (contDiff_radialConnection x₀ ((hb n).of_le (by norm_cast))).contDiffOn)
    fun K _ hK ↦ ⟨M, fun n j hj x hx ↦ hM n j hj x (hK hx)⟩
  -- In radial gauge the sections have bounded derivatives of order at most `l + 1`, so they
  -- converge in `Cˡ` along a further subsequence.
  obtain ⟨B, -, hB⟩ := exists_forall_norm_iteratedFDeriv_radialGauge_mul_le x₀ R hl hb hα hF hcov
  obtain ⟨ψ, hψ, α', hα', hconvα⟩ := exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv
    isOpen_ball l (fun n ↦ (contDiff_radialGauge_mul hl x₀ (hb (φ n)) (hα (φ n))).contDiffOn)
    fun K' _ hK' ↦ ⟨B, fun n j hj x hx ↦ hB (φ n) j hj x (hK' hx)⟩
  exact ⟨φ ∘ ψ, hφ.comp hψ, b', α', hb', hα',
    fun j hj ↦ (hconv j hj).comp_tendsto hψ.tendsto_atTop, hconvα⟩

/-- **Compactness modulo gauge on the whole space.** Let `bₙ` be connection forms of class
`C^(k+2)` on a finite-dimensional space and `αₙ = (αₙⱼ)ⱼ` finitely many sections of class
`C^(l+1)`, `l ≤ k + 1`, such as the components of a spinor in a constant frame. Suppose that on
every ball about `x₀` the derivatives of order at most `k + 1` of the curvatures and the iterated
covariant derivatives `∇ʲ αₙⱼ` of order at most `l + 1` are bounded uniformly in `n` and in the
component. Then along one subsequence the radial gauge pairs converge locally uniformly on the
whole space: the radial connections `K (dbₙ)` with their derivatives of order at most `k` to a
connection form of class `Cᵏ`, and the sections `(uₙ αₙⱼ)ⱼ`, all transformed by the same radial
gauge `uₙ`, with their derivatives of order at most `l` to a section of class `Cˡ`. -/
theorem exists_strictMono_tendstoLocallyUniformly_iteratedFDeriv_radialGauge_mul
    [FiniteDimensional ℝ E] {κ : Type*} [Fintype κ] {b : ℕ → E → E [⋀^Fin 1]→L[ℝ] ℝ}
    {α : ℕ → κ → E → ℂ} (x₀ : E) (k l : ℕ) (hl : l ≤ k + 1)
    (hb : ∀ n, ContDiff ℝ (k + 2) (b n)) (hα : ∀ n j, ContDiff ℝ (l + 1) (α n j))
    (hF : ∀ R, ∃ A, ∀ n, ∀ i ≤ k + 1, ∀ x ∈ ball x₀ R,
      ‖iteratedFDeriv ℝ i (extDeriv (b n)) x‖ ≤ A)
    (hcov : ∀ R, ∃ C, ∀ n j, ∀ i ≤ l + 1, ∀ x ∈ ball x₀ R,
      ‖iteratedCovariantDeriv (b n) (α n j) i x‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (b' : E → E [⋀^Fin 1]→L[ℝ] ℝ) (α' : E → κ → ℂ),
      ContDiff ℝ k b' ∧ ContDiff ℝ l α' ∧
      (∀ i ≤ k, TendstoLocallyUniformly
        (fun n ↦ iteratedFDeriv ℝ i (radialConnection x₀ (b (φ n)))) (iteratedFDeriv ℝ i b')
          atTop) ∧
      ∀ i ≤ l, TendstoLocallyUniformly
        (fun n ↦ iteratedFDeriv ℝ i (fun x j ↦ radialGauge x₀ (b (φ n)) x * α (φ n) j x))
          (iteratedFDeriv ℝ i α') atTop := by
  -- On every ball the radial connections have derivatives of order at most `k + 1` bounded
  -- uniformly in `n`.
  have hM (R : ℝ) : ∃ M, ∀ n, ∀ i ≤ k + 1, ∀ x ∈ ball x₀ R,
      ‖iteratedFDeriv ℝ i (radialConnection x₀ (b n)) x‖ ≤ M := by
    obtain ⟨A, hA⟩ := hF R
    obtain ⟨M, -, hM⟩ := exists_forall_norm_iteratedFDeriv_radialConnection_le x₀ R k hb hA
    exact ⟨M, hM⟩
  -- The radial connections converge in `Cᵏ_loc` along a subsequence.
  have hc (n : ℕ) : ContDiff ℝ (k + 1) (radialConnection x₀ (b n)) :=
    contDiff_radialConnection x₀ (hb n)
  obtain ⟨φ, hφ, b', hb', hconv⟩ := exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv
    isOpen_univ k (fun n ↦ (hc n).contDiffOn) fun K hK _ ↦ by
      obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball x₀
      obtain ⟨M, hM⟩ := hM R
      exact ⟨M, fun n i hi x hx ↦ hM n i hi x (hKR hx)⟩
  -- In radial gauge the sections have derivatives of order at most `l + 1` bounded on every ball,
  -- uniformly in `n` and in the component, so they converge in `Cˡ_loc` along a further
  -- subsequence.
  have hβ (n : ℕ) (j : κ) : ContDiff ℝ (l + 1) (radialGauge x₀ (b n) * α n j) :=
    contDiff_radialGauge_mul hl x₀ (hb n) (hα n j)
  obtain ⟨ψ, hψ, α', hα', hconvα⟩ := exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv
    isOpen_univ l (fun n ↦ (contDiff_pi.2 fun j ↦ hβ (φ n) j).contDiffOn) fun K hK _ ↦ by
      obtain ⟨R, hKR⟩ := hK.isBounded.subset_ball x₀
      obtain ⟨A, hA⟩ := hF R
      obtain ⟨C, hC⟩ := hcov R
      obtain ⟨B, hB0, hB⟩ := exists_forall_norm_iteratedFDeriv_radialGauge_mul_le
        (b := fun p : ℕ × κ ↦ b p.1) (α := fun p ↦ α p.1 p.2) x₀ R hl (fun p ↦ hb p.1)
        (fun p ↦ hα p.1 p.2) (fun p ↦ hA p.1) (fun p ↦ hC p.1 p.2)
      exact ⟨B, fun n i hi x hx ↦ norm_iteratedFDeriv_pi_le hB0
        (fun j ↦ ((hβ (φ n) j).of_le (by norm_cast)).contDiffAt)
        fun j ↦ hB (φ n, j) i hi x (hKR hx)⟩
  exact ⟨φ ∘ ψ, hφ.comp hψ, b', α', contDiffOn_univ.1 hb', contDiffOn_univ.1 hα',
    fun i hi ↦ tendstoLocallyUniformlyOn_univ.1
      ((hconv i hi).comp_tendsto hψ.tendsto_atTop),
    fun i hi ↦ tendstoLocallyUniformlyOn_univ.1 (hconvα i hi)⟩

/-- **Compactness modulo gauge.** Let `(bₙ, αₙ)` be pairs on a finite-dimensional space, with
`bₙ` of class `C^(k+2)` and `αₙ` of class `C¹`, whose curvatures have derivatives of order at most
`k + 1` bounded by `A` on the ball of radius `R` about `x₀`, and whose sections satisfy `|αₙ| ≤ C`
and `|∇_{bₙ} αₙ| ≤ C` there. Then along a subsequence the radial gauge pairs
`(K (dbₙ), uₙ αₙ)` converge on the ball: the radial connections, with their derivatives of order at
most `k`, locally uniformly to a connection form `b` of class `Cᵏ`, and the sections locally
uniformly to a continuous section. This is the case `l = 0` of
`exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv_radialGauge_mul`. -/
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
  obtain ⟨φ, hφ, b', α', hb', hα', hconv, hconvα⟩ :=
    exists_strictMono_tendstoLocallyUniformlyOn_iteratedFDeriv_radialGauge_mul x₀ R k 0
      (Nat.zero_le _) hb (fun n ↦ by simpa using hα n) hF (C := C) fun n j hj x hx ↦ by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · simpa using hαC n x hx
        · simpa using hcov n x hx
  exact ⟨φ, hφ, b', α', hb', contDiffOn_zero.1 hα', hconv,
    tendstoLocallyUniformlyOn_iteratedFDeriv_zero_iff.1 (hconvα 0 le_rfl)⟩

end TauCeti.SeibergWitten
