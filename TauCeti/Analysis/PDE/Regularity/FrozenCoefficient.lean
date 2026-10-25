/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HarmonicReplacement
public import TauCeti.Analysis.Sobolev.W1p.Restriction
public import TauCeti.Topology.MetricSpace.Holder.Basic
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Comparison with the frozen-coefficient problem

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) = -div G` in `Ω`,

tested against test functions, with a variable coefficient matrix `a`. On an open `B ⊆ Ω`, freeze
the coefficients at a constant elliptic matrix `A`, typically `A = a(x₀)` for a centre `x₀`, and
let `w ∈ H¹(B)` be the weak solution of the frozen problem `-∂ⱼ(Aⁱʲ ∂ᵢw) = 0` in `B` with the
boundary values of `u`, `u - w ∈ H¹₀(B)`. This file bounds the energy of the error `u - w`:
if `‖a(x) - A‖ ≤ ε` on `B` and `A` has lower ellipticity constant `λ`, then

`λ ‖∇(u - w)‖_{L²(B)} ≤ ε ‖∇u‖_{L²(B)} + ‖G - c‖_{L²(B)}`

for every constant `c` such that `G - c ∈ L²(B)`. For `α`-Hölder coefficients and data on an
open set `B ⊆ B(x₀, r)`, freezing at `x₀` makes both terms of order `r^α`:

`λ ‖∇(u - w)‖_{L²(B)} ≤ r^α ([a]_α ‖∇u‖_{L²(B)} + [G]_α |B|^{1/2})`.

This is the comparison step of Campanato's approach to the Schauder estimates for equations with
Hölder continuous coefficients. Squared, it bounds `∫_B ‖∇u - ∇w‖²` by
`2 λ⁻² r^{2α} ([a]_α² ∫_B ‖∇u‖² + [G]_α² |B|)`. Together with the decay of solutions of the frozen
problem on concentric balls
(`TauCeti.PDE.setIntegral_ball_norm_sub_setAverage_sq_le_of_sum_smul_fderiv_fderiv_eq_zero`), the
coefficient term plays the role of the perturbation `ε` in the iteration lemma
`TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add` and the data term that of its
inhomogeneity. For `a = 1` and `A = 1` the coefficient term vanishes and the estimate is the one
behind `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`.

The coefficient oscillation is measured in the operator norm of the attached bilinear forms
`TauCeti.PDE.matrixBilinearForm`, as in the Lipschitz hypothesis of whole-space `H²` regularity.

## The argument

Since constants have zero divergence, `u` solves `-∂ⱼ(aⁱʲ ∂ᵢu) = -div (G - c)` on `B` against all
of `H¹₀(B)` (`TauCeti.PDE.forall_energyFormH1_restrictL_eq_inner`). Adding `-∂ⱼ((A - a)ⁱʲ ∂ᵢu)`
to both sides, `u` solves the frozen equation

`-∂ⱼ(Aⁱʲ ∂ᵢu) = -div (G - c + (A - a) ∇u)` on `B`,

whose field is square integrable with norm at most `‖G - c‖_{L²(B)} + ε ‖∇u‖_{L²(B)}`. The
energy estimate for the replacement relative to the elliptic matrix `A`
(`TauCeti.PDE.UniformlyEllipticOn.mul_norm_gradient_sub_le`) bounds `λ ‖∇(u - w)‖_{L²(B)}` by
the norm of that field.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.mul_norm_gradient_restrictL_sub_le`: the comparison estimate
  for a frozen elliptic matrix `A` with `‖a - A‖ ≤ ε` on `B`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_sub_mem_w1p0Submodule_mul_norm_gradient_sub_le`: on an
  open set inside a ball `B(x₀, r)`, the replacement frozen at `x₀` exists and its error is
  `O(r^α)` for `α`-Hölder coefficients and data.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5 (Schauder estimates for equations with
  variable coefficients, by freezing the coefficients).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 3.
-/

public section

noncomputable section

open InnerProductSpace Matrix MeasureTheory Metric Set TopologicalSpace
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

/-- **Comparison with the frozen problem.** Let `u ∈ H¹(Ω)` solve `-∂ⱼ(aⁱʲ ∂ᵢu) = -div G`
weakly on `Ω`, tested against test functions, let `B ⊆ Ω` be open, and let `A` be a constant
matrix, uniformly elliptic with lower constant `λ`, with `‖a(x) - A‖ ≤ ε` for `x ∈ B` in the
operator norm of the attached bilinear forms. If `w ∈ H¹(B)` has the boundary values of `u`,
`u - w ∈ H¹₀(B)`, and solves the frozen problem `-∂ⱼ(Aⁱʲ ∂ᵢw) = 0` weakly on `B`, then for every
constant `c` with `G - c ∈ L²(B)`

`λ ‖∇(u - w)‖_{L²(B)} ≤ ε ‖∇u‖_{L²(B)} + ‖G - c‖_{L²(B)}`. -/
theorem UniformlyEllipticOn.mul_norm_gradient_restrictL_sub_le
    {Omega B : Opens (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ} {lam Lam : ℝ}
    (hA : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ ι)) (fun _ => A) lam Lam)
    (hB : B ≤ Omega) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : AEStronglyMeasurable a (mu.restrict B)) {ε : ℝ}
    (haA : ∀ x ∈ (B : Set (EuclideanSpace ℝ ι)),
      ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ ε)
    {u : W1p mu Omega 2} {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu)
    {c : EuclideanSpace ℝ ι} (hGc : MemLp (fun x => G x - c) 2 (mu.restrict B))
    {w : W1p mu B 2} (huw : W1p.restrictL hB u - w ∈ w1p0Submodule mu B 2)
    (hw : ∀ v : W1p0 mu B 2, energyFormH1 (fun _ => A) 0 0 w (v : W1p mu B 2) = 0) :
    lam * ‖W1p.gradient (W1p.restrictL hB u - w)‖ ≤
      ε * ‖W1p.gradient (W1p.restrictL hB u)‖ + ‖hGc.toLp‖ := by
  have hBm := B.isOpen.measurableSet
  -- The coefficients are bounded on `B`, by `‖A‖ + |ε|`.
  have hbd : ∀ x ∈ (B : Set (EuclideanSpace ℝ ι)), ∀ η ξ : EuclideanSpace ℝ ι,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ (‖matrixBilinearForm A‖ + |ε|) * ‖η‖ * ‖ξ‖ := fun x hx η ξ => by
    rw [← matrixBilinearForm_apply, ← Real.norm_eq_abs]
    refine ((matrixBilinearForm (a x)).le_opNorm₂ η ξ).trans ?_
    gcongr
    calc ‖matrixBilinearForm (a x)‖
        ≤ ‖matrixBilinearForm A‖ + ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ :=
          norm_le_norm_add_norm_sub' (matrixBilinearForm (a x)) (matrixBilinearForm A)
      _ ≤ ‖matrixBilinearForm A‖ + |ε| := by
          gcongr
          exact (haA x hx).trans (le_abs_self ε)
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict B) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) (by positivity) ha
      aestronglyMeasurable_const aestronglyMeasurable_const hbd (fun _ _ => by simp)
      (fun _ _ => by simp)
  -- The field `(A - a) ∇u` is square integrable on `B`, with norm at most `ε ‖∇u‖`.
  set D : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun x => toEuclideanCLM (n := ι) (𝕜 := ℝ) (A - a x) (W1p.gradient (W1p.restrictL hB u) x)
  have hDbd : ∀ᵐ x ∂mu.restrict B, ‖D x‖ ≤ ε * ‖W1p.gradient (W1p.restrictL hB u) x‖ := by
    filter_upwards [ae_restrict_mem hBm] with x hx
    refine (norm_toEuclideanCLM_apply_le _ _).trans ?_
    gcongr
    rw [matrixBilinearForm_sub]
    exact (norm_sub_rev (matrixBilinearForm A) (matrixBilinearForm (a x))).trans_le (haA x hx)
  have hDm : AEStronglyMeasurable D (mu.restrict B) :=
    (continuous_uncurry_toEuclideanCLM (n := ι) (𝕜 := ℝ)).comp_aestronglyMeasurable
      (f := fun x => (A - a x, (W1p.gradient (W1p.restrictL hB u) x : EuclideanSpace ℝ ι)))
      ((aestronglyMeasurable_const.sub ha).prodMk (Lp.aestronglyMeasurable _))
  have hD : MemLp D 2 (mu.restrict B) :=
    (Lp.memLp (W1p.gradient (W1p.restrictL hB u))).of_le_mul hDm hDbd
  -- `u` solves the frozen equation on `B` with the field `G - c + (A - a) ∇u`.
  have hF : ∀ v : W1p0 mu B 2,
      energyFormH1 (fun _ => A) 0 0 (W1p.restrictL hB u) (v : W1p mu B 2) =
        ⟪hGc.toLp + hD.toLp, W1p.gradient (v : W1p mu B 2)⟫_ℝ := fun v => by
    rw [inner_add_left, ← forall_energyFormH1_restrictL_eq_inner hB hcoeff hu hGc v,
      energyFormH1_def, energyFormH1_def, L2.inner_def]
    refine (integral_congr_ae ?_).trans (integral_add
      (PDE.integrable_energyIntegrand_jetField hcoeff (W1p.restrictL hB u) (v : W1p mu B 2))
      (L2.integrable_inner _ _))
    filter_upwards [hD.coeFn_toLp] with x hx
    simp only [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply,
      Pi.zero_apply, inner_zero_left, zero_mul, add_zero, hx, D, matrixBilinearForm_apply]
    rw [real_inner_comm, inner_toEuclideanCLM, sub_mulVec, dotProduct_sub]
    ring
  calc lam * ‖W1p.gradient (W1p.restrictL hB u - w)‖ ≤ ‖hGc.toLp + hD.toLp‖ :=
        hA.mul_norm_gradient_sub_le aestronglyMeasurable_const huw hw hF
    _ ≤ ‖hGc.toLp‖ + ‖hD.toLp‖ := norm_add_le _ _
    _ ≤ ‖hGc.toLp‖ + ε * ‖W1p.gradient (W1p.restrictL hB u)‖ := by
        gcongr
        refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
        filter_upwards [hD.coeFn_toLp, hDbd] with x hx hxbd
        rwa [hx]
    _ = ε * ‖W1p.gradient (W1p.restrictL hB u)‖ + ‖hGc.toLp‖ := add_comm _ _

/-- **The replacement frozen at a centre.** Let `u ∈ H¹(Ω)` solve `-∂ⱼ(aⁱʲ ∂ᵢu) = -div G` weakly
on `Ω ⊆ ℝ^{n+1}`, tested against test functions, let `B ⊆ Ω` be open with `B ⊆ B(x₀, r)`, and let
`a` be uniformly elliptic with constants `0 < λ ≤ Λ` on a set containing `x₀`. Suppose that on
`B(x₀, r)` the coefficients are `α`-Hölder with constant `K_a`, in the operator norm of the
attached bilinear forms, and `G` is `α`-Hölder with constant `K_G`, where `α > 0`. Then there is
`w ∈ H¹(B)` with the boundary values of `u`, `u - w ∈ H¹₀(B)`, solving the problem
`-∂ⱼ(a(x₀)ⁱʲ ∂ᵢw) = 0` with coefficients frozen at `x₀` weakly on `B`, such that

`λ ‖∇(u - w)‖_{L²(B)} ≤ r^α (K_a ‖∇u‖_{L²(B)} + K_G |B|^{1/2})`.

The replacement is unique, by
`UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball`. -/
theorem UniformlyEllipticOn.exists_sub_mem_w1p0Submodule_mul_norm_gradient_sub_le {n : ℕ}
    {Omega B : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} (h : UniformlyEllipticOn s a lam Lam)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} (hx₀ : x₀ ∈ s) {r : ℝ} {α Ka KG : ℝ≥0} (hα : 0 < α)
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ r))
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hGK : HolderOnWith KG α G (ball x₀ r)) (hB : B ≤ Omega)
    (hBr : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball x₀ r) {u : W1p volume Omega 2}
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) :
    ∃ w : W1p volume B 2, W1p.restrictL hB u - w ∈ w1p0Submodule volume B 2 ∧
      (∀ v : W1p0 volume B 2,
        energyFormH1 (fun _ => a x₀) 0 0 w (v : W1p volume B 2) = 0) ∧
      lam * ‖W1p.gradient (W1p.restrictL hB u - w)‖ ≤
        r ^ (α : ℝ) * (Ka * ‖W1p.gradient (W1p.restrictL hB u)‖ +
          KG * √(volume.real (B : Set (EuclideanSpace ℝ (Fin (n + 1)))))) := by
  have hBm := B.isOpen.measurableSet
  have hA :
      UniformlyEllipticOn (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) (fun _ => a x₀) lam Lam :=
    uniformlyEllipticOn_iff.2 ⟨h.pos, h.le, fun _ _ => ⟨h.lower_bound hx₀, h.upper_bound hx₀⟩⟩
  have hBfin : volume (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hBr)
  have : IsFiniteMeasure (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hBfin
  -- On `B`, the oscillation of `G` about its value at `x₀` is at most `K_G r^α`.
  have hGbd : ∀ x ∈ (B : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ‖G x - G x₀‖ ≤ KG * r ^ (α : ℝ) := fun x hx => by
    rw [← dist_eq_norm]
    exact hGK.dist_le_mul_rpow_of_mem_ball (hBr hx)
  -- A matrix is a function of its entries, and the entries of `a` are continuous on the ball.
  have ha :
      AEStronglyMeasurable a (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    ContinuousOn.aestronglyMeasurable (β := Fin (n + 1) → Fin (n + 1) → ℝ)
      ((continuousOn_of_continuousOn_matrixBilinearForm (haK.continuousOn hα)).mono hBr) hBm
  have hGc : MemLp (fun x => G x - G x₀) 2
      (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    MemLp.of_bound ((((hGK.continuousOn hα).mono hBr).aestronglyMeasurable hBm).sub
      aestronglyMeasurable_const) (KG * r ^ (α : ℝ))
      ((ae_restrict_iff' hBm).2 (ae_of_all _ hGbd))
  -- The replacement frozen at `x₀`.
  obtain ⟨w, ⟨huw, hw⟩, -⟩ :=
    UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
      (b := 0) (c := 0) hA aestronglyMeasurable_const aestronglyMeasurable_const
      aestronglyMeasurable_const le_rfl (fun _ _ => by simp) (gamma := 0) (fun _ _ => by simp)
      (fun _ _ => le_rfl) (le_max_right r 0) (hBr.trans (ball_subset_ball (le_max_left r 0)))
      (by simpa using hA.pos) 0 (W1p.restrictL hB u)
  have hw0 : ∀ v : W1p0 volume B 2,
      energyFormH1 (fun _ => a x₀) 0 0 w (v : W1p volume B 2) = 0 := fun v => by
    rw [hw v, ← dirichletForcing_apply_eq_setIntegral, dirichletForcing_apply, inner_zero_left]
  have hsub : W1p.restrictL hB u - w ∈ w1p0Submodule volume B 2 := by
    have hwu :=
      (ClosedSubmodule.mem_toSubmodule_iff (w - W1p.restrictL hB u)
        (w1p0Submodule volume B 2)).2 huw
    exact (ClosedSubmodule.mem_toSubmodule_iff _ _).1 (sub_mem_comm_iff.1 hwu)
  refine ⟨w, hsub, hw0, ?_⟩
  have hest := hA.mul_norm_gradient_restrictL_sub_le hB ha (ε := Ka * r ^ (α : ℝ))
    (fun x hx => by
      have := haK.dist_le_mul_rpow_of_mem_ball (hBr hx)
      rwa [dist_eq_norm] at this) hu hGc hsub hw0
  -- The `L²(B)` norm of `G - G x₀` is at most `|B|^{1/2} K_G r^α`.
  have hGn := hGc.norm_toLp_le_measureReal_rpow_mul (by norm_num) hBfin
    ((ae_restrict_iff' hBm).2 (ae_of_all _ hGbd))
  rw [ENNReal.toReal_ofNat, ← one_div, ← Real.sqrt_eq_rpow] at hGn
  calc lam * ‖W1p.gradient (W1p.restrictL hB u - w)‖
      ≤ Ka * r ^ (α : ℝ) * ‖W1p.gradient (W1p.restrictL hB u)‖ + ‖hGc.toLp‖ := hest
    _ ≤ Ka * r ^ (α : ℝ) * ‖W1p.gradient (W1p.restrictL hB u)‖ +
        √(volume.real (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) * (KG * r ^ (α : ℝ)) := by
        gcongr
    _ = r ^ (α : ℝ) * (Ka * ‖W1p.gradient (W1p.restrictL hB u)‖ +
          KG * √(volume.real (B : Set (EuclideanSpace ℝ (Fin (n + 1)))))) := by ring

end PDE

end TauCeti
