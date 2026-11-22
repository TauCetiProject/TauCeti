/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Basic
public import TauCeti.Analysis.PDE.Regularity.Boundary.VariableCoefficientDecay
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.HolderOnWith
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.InterBall

/-!
# Schauder estimates up to a flat boundary for divergence-form equations

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝ^{n+1}`, and let `u ∈ H¹(U)` vanish on
`U ∖ H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`,

so that `u` has zero boundary values on the flat part `U ∩ ∂H` of the boundary. This file proves
the `C^{1,β}` estimate for `u` up to that flat part, for coefficients `a` and a field `G` that are
`α`-Hölder and a scalar datum `f ∈ L^q`: if `S` is a subset of the closed half-space whose open
`R`-thickening `S_R` lies in `U`, then the precise representative of `∇u` for the Lebesgue measure
on `H`, the limit of its averages over the half-balls `B(x, r) ∩ H`, is `β`-Hölder on `S` for every
`0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`, with constant

`C (K_G R^{α-β} + R^{1-(n+1)/q-β} ‖f‖_{L^q(S_R ∩ H)} + R^{-(n+1)/2-β} ‖∇u‖_{L²(U)})`

(`exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith_of_memLp`, and its
case `f = 0`, `β = α`,
`exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith`, both in
`TauCeti.PDE`). These
are the boundary counterparts of the interior estimates of
`TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Basic`. Unlike the reflection argument of
`TauCeti.Analysis.PDE.Regularity.Boundary.GradientHolder`, nothing is assumed about `a` or `G` at
the hyperplane: neither symmetry under the reflection nor a vanishing tangential part. The
gradient of `u` jumps across `∂H`, since `u` vanishes off `H`, which is why the estimate is stated
for the averages over half-balls.

## The argument

The estimate combines the decay at boundary centres of
`TauCeti.Analysis.PDE.Regularity.Boundary.VariableCoefficientDecay` with the interior decay of
`TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Basic`, by Campanato's method. Fix
`x` in the closed half-space, let `d` be its distance to `∂H` and `z` the nearest point of `∂H`.

* **Radii `t ≳ d`.** The half-ball `B(x, t) ∩ H` lies in a half-ball `B(z, s) ∩ H` with
  `s ≈ t`, centred on the hyperplane, where `∇u` is close in square mean to a normal vector
  `p_s`, at the rate `s^{n+1+2β}`
  (`exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_of_holderOnWith`
  in `TauCeti.PDE`).
* **Radii `t ≲ d`.** The ball `B(x, t)` lies in `H`, and the interior decay is applied on `B(x, d)`
  to `u - ⟪p, ·⟫` rather than to `u`, where `p = p_{2d}`. This function solves the equation with
  `G` replaced by `G - (a p)^♯`, which is Hölder with constant `K_G + ‖p‖ K_a`, and its gradient
  `∇u - p` is small on `B(x, d)` in square mean, by the boundary decay at `z`. Without the
  subtraction the interior estimate would start from `∫_{B(x, d)} ‖∇u‖² ≈ d^{n+1}`, which is too
  large by a factor `d^{-2β}`.

Together they bound the square mean oscillation of `∇u` on `B(x, t) ∩ H` by a multiple of
`t^{n+1+2β}` at every point `x` of `S` and every radius `t` below a fixed fraction of `R`. The
half-space has density at least `1 / 2` in every ball centred in its closure, so Campanato's
theorem on a set with the measure density property
(`holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le_of_norm_le` in
`TauCeti.MeasureTheory`)
gives the Hölder estimate.

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Sections 5.1 and 5.4 (Schauder estimates up to a
  flat boundary by Campanato's method).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33 (the `C^{1,α}` estimate up to the boundary).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- The continuous linear map sending a bilinear form `A` to the vector `(A p)^♯` representing
`η ↦ A η p`. Subtracting the linear function `⟪p, ·⟫` from a solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` replaces `G` by `G - (a p)^♯`. -/
private def conormalShiftL (p : EuclideanSpace ℝ (Fin (n + 1))) :
    (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  (toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm.toContinuousLinearEquiv.toContinuousLinearMap
    ∘L ContinuousLinearMap.apply ℝ _ p
    ∘L (ContinuousLinearMap.flipₗᵢ ℝ (EuclideanSpace ℝ (Fin (n + 1)))
      (EuclideanSpace ℝ (Fin (n + 1))) ℝ).toContinuousLinearEquiv.toContinuousLinearMap

private theorem conormalShiftL_apply (p : EuclideanSpace ℝ (Fin (n + 1)))
    (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) :
    conormalShiftL p A = (toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm
      (ContinuousLinearMap.flipₗᵢ ℝ (EuclideanSpace ℝ (Fin (n + 1)))
        (EuclideanSpace ℝ (Fin (n + 1))) ℝ A p) := (rfl)

private theorem inner_conormalShiftL_apply (p : EuclideanSpace ℝ (Fin (n + 1)))
    (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (η : EuclideanSpace ℝ (Fin (n + 1))) :
    ⟪conormalShiftL p A, η⟫_ℝ = A η p := by
  rw [conormalShiftL_apply, toDual_symm_apply]
  rfl

private theorem norm_conormalShiftL_apply_le (p : EuclideanSpace ℝ (Fin (n + 1)))
    (A : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ) :
    ‖conormalShiftL p A‖ ≤ ‖p‖ * ‖A‖ := by
  rw [conormalShiftL_apply, LinearIsometryEquiv.norm_map]
  calc _ ≤ ‖ContinuousLinearMap.flipₗᵢ ℝ _ _ ℝ A‖ * ‖p‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖p‖ * ‖A‖ := by rw [LinearIsometryEquiv.norm_map, mul_comm]

/-- Postcomposing with `conormalShiftL p` multiplies a Hölder constant by `‖p‖`. -/
private theorem holderOnWith_conormalShiftL {p : EuclideanSpace ℝ (Fin (n + 1))}
    {F : EuclideanSpace ℝ (Fin (n + 1)) →
      (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)}
    {K α : ℝ≥0} {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hF : HolderOnWith K α F s) :
    HolderOnWith (‖p‖₊ * K) α (fun x => conormalShiftL p (F x)) s := by
  have hL : LipschitzWith ‖p‖₊ (conormalShiftL p) := LipschitzWith.of_dist_le_mul fun A B => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, coe_nnNorm]
    exact norm_conormalShiftL_apply_le p (A - B)
  exact hL.comp_holderOnWith hF

/-- The linear function `⟪p, ·⟫` on a ball, as an element of `H¹`, with gradient `p`. -/
private theorem exists_gradient_ae_eq_const (x₀ : EuclideanSpace ℝ (Fin (n + 1))) (ρ : ℝ)
    (p : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ L : W1p volume (⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      W1p.gradient L =ᵐ[volume.restrict (ball x₀ ρ)] fun _ => p := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ ρ)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hgrad : ∇ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => ⟪p, y⟫_ℝ) = fun _ => p :=
    funext fun y => gradient_inner_const_left p y
  have hℓ : MemLp (fun y : EuclideanSpace ℝ (Fin (n + 1)) => ⟪p, y⟫_ℝ) 2
      (volume.restrict (ball x₀ ρ)) :=
    MemLp.of_bound (innerSL ℝ p).continuous.aestronglyMeasurable (‖p‖ * (‖x₀‖ + ρ))
      (ae_restrict_of_forall_mem measurableSet_ball fun y hy => by
        rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm p y).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        have := norm_le_norm_add_norm_sub' y x₀
        rw [← dist_eq_norm] at this
        linarith [(mem_ball.1 hy).le])
  obtain ⟨L, -, hLg⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn
    (Omega := ⟨ball x₀ ρ, isOpen_ball⟩) (p := 2)
    (u := fun y : EuclideanSpace ℝ (Fin (n + 1)) => ⟪p, y⟫_ℝ)
    (innerSL ℝ p).contDiff.contDiffOn hℓ (by rw [hgrad]; exact memLp_const p)
  exact ⟨L, hgrad ▸ hLg⟩

/-- **Subtracting a linear function from a solution.** Let `u ∈ H¹(U)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`, let `B = ball x₀ ρ ⊆ U ∩ H`, let `a` be uniformly
elliptic on `B`, let `a` and `G` be `α`-Hölder on `B`, and let `f ∈ L²(B)`. For every vector `p`,
the function `w = u - ⟪p, ·⟫` on `B` has gradient `∇u - p` and solves the equation with `G`
replaced by `G - (a p)^♯`, where `(a p)^♯` represents `η ↦ ηᵀ a p`. -/
private theorem exists_gradient_ae_eq_sub_and_forall_energyFormH1_eq
    {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume U 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    (hB : ball x₀ ρ ⊆ (U ⊓ H : Opens (EuclideanSpace ℝ (Fin (n + 1)))))
    {lam Lam : ℝ} (h : UniformlyEllipticOn (ball x₀ ρ) a lam Lam) {α Ka KG : ℝ≥0} (hα : 0 < α)
    (haK : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x₀ ρ))
    (hGK : HolderOnWith KG α G (ball x₀ ρ)) (hf : MemLp f 2 (volume.restrict (ball x₀ ρ)))
    (hu : ∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
        (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
      (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in U ⊓ H, f x * φ x)
    (p : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ w : W1p volume (⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      W1p.gradient w =ᵐ[volume.restrict (ball x₀ ρ)] (fun y => W1p.gradient u y - p) ∧
      ∀ φ : 𝓓((⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
        energyFormH1 a 0 0 w (W1p.ofTestFunctionₗ volume _ 2 φ) =
          (∫ x in (⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
            ⟪G x - conormalShiftL p (matrixBilinearForm (a x)),
              ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in (⟨ball x₀ ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))),
            f x * φ x := by
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ ρ, isOpen_ball⟩
  have hBU : B ≤ U ⊓ H := hB
  have hBU' : B ≤ U := hBU.trans inf_le_left
  have : IsFiniteMeasure (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨L, hLg⟩ := exists_gradient_ae_eq_const (n := n) x₀ ρ p
  refine ⟨W1p.restrictL hBU' u - L, ?_, fun φ => ?_⟩
  · filter_upwards [W1p.gradient_sub_ae (W1p.restrictL hBU' u) L,
      W1p.gradient_restrictL_ae hBU' u, hLg] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  -- The equation for `u` on `B`, in `L²` form.
  have ha := memLp_energyIntegrand_of_holderOnWith (mu := volume) (B := B) subset_rfl h hα haK
  have hG2 : MemLp (fun x => G x - G x₀) 2 (volume.restrict (B : Set _)) :=
    memLp_sub_of_holderOnWith measurableSet_ball subset_rfl hα hGK
  have hP2 : MemLp (fun x => conormalShiftL p (matrixBilinearForm (a x)) -
      conormalShiftL p (matrixBilinearForm (a x₀))) 2 (volume.restrict (B : Set _)) :=
    memLp_sub_of_holderOnWith measurableSet_ball subset_rfl hα (holderOnWith_conormalShiftL haK)
  have hGP : MemLp (fun x => (G x - conormalShiftL p (matrixBilinearForm (a x))) -
      (G x₀ - conormalShiftL p (matrixBilinearForm (a x₀)))) 2 (volume.restrict (B : Set _)) :=
    (hG2.sub hP2).ae_eq (ae_of_all _ fun x => by simp only [Pi.sub_apply]; abel)
  have h1 := forall_energyFormH1_restrictL_eq_inner_add_inner hBU ha hu hG2 hf
    ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
  rw [W1p.restrictL_restrictL] at h1
  -- The energy form of the linear function against `φ`.
  have h2 : energyFormH1 a 0 0 L (W1p.ofTestFunctionₗ volume B 2 φ) =
      ⟪hP2.toLp, W1p.gradient (W1p.ofTestFunctionₗ volume B 2 φ)⟫_ℝ := by
    rw [inner_toLp_gradient_ofTestFunctionₗ hP2 φ, energyFormH1_def]
    refine integral_congr_ae ?_
    filter_upwards [jetField_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ, hLg] with x hx hL
    rw [hx, jetField_apply, hL, energyIntegrand_apply, inner_conormalShiftL_apply]
    simp
  have hsub : hGP.toLp = hG2.toLp - hP2.toLp := by
    rw [← MemLp.toLp_sub]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun x => by simp only [Pi.sub_apply]; abel)
  have hfφ : ⟪hf.toLp, W1p.value (W1p.ofTestFunctionₗ volume B 2 φ)⟫_ℝ =
      ∫ x in B, f x * φ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ]
      with x hx hφx
    rw [hx, hφx]
    simp [mul_comm]
  have hlin : energyFormH1 a 0 0 (W1p.restrictL hBU' u - L) (W1p.ofTestFunctionₗ volume B 2 φ) =
      energyFormH1 a 0 0 (W1p.restrictL hBU' u) (W1p.ofTestFunctionₗ volume B 2 φ) -
        energyFormH1 a 0 0 L (W1p.ofTestFunctionₗ volume B 2 φ) := by
    simp only [Pi.zero_def, ← energyFormH1L_apply ha, map_sub, sub_apply]
  rw [hlin, h1, h2, ← inner_toLp_gradient_ofTestFunctionₗ hGP φ, hsub, inner_sub_left,
    ← hfφ]
  ring

/-- **The square mean oscillation on a smaller set.** If `B(x, t) ⊆ B(z, s) ⊆ U` and `g ∈ L²(U)`,
then the square mean oscillation of `g` on `B(x, t) ∩ H` is at most `∫_{B(z, s) ∩ H} ‖g - P‖²`, for
every vector `P`. -/
private theorem setIntegral_ball_inter_norm_sub_setAverage_sq_le
    {U H : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (g : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict U))
    {x z : EuclideanSpace ℝ (Fin (n + 1))} {t s : ℝ} (hzs : ball z s ⊆ U)
    (hxt : ball x t ⊆ ball z s) (P : EuclideanSpace ℝ (Fin (n + 1))) :
    ∫ y in ball x t ∩ H, ‖g y - ⨍ w in ball x t ∩ H, g w‖ ^ 2 ≤
      ∫ y in ball z s ∩ H, ‖g y - P‖ ^ 2 := by
  have hg : MemLp g 2 (volume.restrict (ball z s ∩ H)) :=
    (Lp.memLp g).mono_measure (Measure.restrict_mono (inter_subset_left.trans hzs) le_rfl)
  have hsub : ball x t ∩ H ⊆ ball z s ∩ H := inter_subset_inter_left _ hxt
  have hfin : volume (ball x t ∩ H) ≠ ⊤ := measure_ball_inter_ne_top
  have hgt : MemLp g 2 (volume.restrict (ball x t ∩ H)) :=
    hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  refine (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq hfin
    (hgt.integrableOn_of_subset one_le_two subset_rfl hfin)
    (hgt.integrableOn_norm_sub_sq_of_subset subset_rfl hfin P)).trans ?_
  exact setIntegral_mono_set (hg.integrableOn_norm_sub_sq_of_subset subset_rfl
    measure_ball_inter_ne_top P) (ae_of_all _ fun _ => by positivity)
    (Filter.Eventually.of_forall hsub)

/-- **Decay at an interior centre, after subtracting a linear function.** Let `0 < γ < 1` with
`γ ≤ α`. There are `θ ∈ (0, 1]` and `C ≥ 0`, depending only on `n`, `α`, `γ`, `λ`, `Λ` and `M`,
such that the following holds. Let `u ∈ H¹(U)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`,
let `B(x, d) ⊆ U ∩ H`, let `a` be uniformly elliptic on `B(x, d)`, let `a` and `G` be `α`-Hölder
there with constants `K_a` and `K_G`, where `K_a d^α ≤ M`, and let `f ∈ L²(B(x, d))`. Let `p` be a
vector. If `r^{2α} (K_G + ‖p‖ K_a)² r^{n+1} + 4 r² ∫_{B(x, r)} f² ≤ V (r / d)^{n+1+2γ}` for
`0 < r ≤ d` and `∫_{B(x, d)} ‖∇u - p‖² ≤ V`, then
`∫_{B(x, t)} ‖∇u - (∇u)_{B(x, t)}‖² ≤ C V (t / d)^{n+1+2γ}` for `0 < t ≤ θ d`. -/
private theorem exists_setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_sub
    {α : ℝ≥0} {γ : ℝ} (hγ : 0 < γ) (hγα : γ ≤ α) (hγ1 : γ < 1) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {x p : EuclideanSpace ℝ (Fin (n + 1))}
      {d V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (ball x d) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball x d) →
      HolderOnWith KG α G (ball x d) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      MemLp f 2 (volume.restrict (ball x d)) →
      ball x d ⊆ (U ⊓ H : Opens (EuclideanSpace ℝ (Fin (n + 1)))) → 0 < d →
      (Ka : ℝ) * d ^ (α : ℝ) ≤ M →
      (∀ r, 0 < r → r ≤ d → r ^ (2 * (α : ℝ)) * (((KG : ℝ) + ‖p‖ * Ka) ^ 2 * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * ∫ y in ball x r, f y ^ 2 ≤ V * (r / d) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ y in ball x d, ‖W1p.gradient u y - p‖ ^ 2 ≤ V →
      ∀ t, 0 < t → t ≤ θ * d →
        ∫ y in ball x t, ‖W1p.gradient u y - ⨍ w in ball x t, W1p.gradient u w‖ ^ 2 ≤
          C * V * (t / d) ^ (2 * γ + ((n : ℝ) + 1)) := by
  have hα : 0 < α := by exact_mod_cast hγ.trans_le hγα
  obtain ⟨θ, C, hθ, hθ1, hC, h⟩ :=
    exists_setIntegral_norm_gradient_sub_setAverage_sq_le_of_holderOnWith (n := n) hγ hγα hγ1
      (lam := lam) (Lam := Lam) (M := M)
  refine ⟨θ, C, hθ, hθ1, hC, ?_⟩
  intro U H u a G f x p d V Ka KG hell haK hGK hu hf hB hd hM hD hΦ t ht htθ
  obtain ⟨w, hwg, hw⟩ := exists_gradient_ae_eq_sub_and_forall_energyFormH1_eq hB hell hα haK
    hGK hf hu p
  have hGK' := hGK.sub (holderOnWith_conormalShiftL (p := p) haK)
  have hd' := h hell (mem_ball_self hd) haK hGK' hw hf subset_rfl hd hM
    (fun r hr hrd => (le_of_eq (by push_cast; ring)).trans (hD r hr hrd))
    ((integral_congr_ae (by
      filter_upwards [hwg] with y hy
      rw [hy])).trans_le hΦ) t ht htθ
  -- The gradients of `w` and `u` differ by the constant `p` on `B(x, t)`, and the average
  -- minimizes the square mean oscillation.
  have htd : ball x t ⊆ ball x d := ball_subset_ball (htθ.trans (mul_le_of_le_one_left hd.le hθ1))
  have hwg' := ae_restrict_of_ae_restrict_of_subset htd hwg
  have hg : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → _) 2
      (volume.restrict (ball x t)) :=
    (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono
      (htd.trans (hB.trans (SetLike.coe_subset_coe.2 inf_le_left))) le_rfl)
  have hfin : volume (ball x t) ≠ ⊤ := measure_ball_lt_top.ne
  refine (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq hfin
    (hg.integrableOn_of_subset one_le_two subset_rfl hfin)
    (hg.integrableOn_norm_sub_sq_of_subset subset_rfl hfin
      ((⨍ y in ball x t, W1p.gradient w y) + p))).trans (le_of_eq_of_le ?_ hd')
  refine integral_congr_ae ?_
  filter_upwards [hwg'] with y hy
  rw [hy, sub_add_eq_sub_sub_swap]

/-- A half-space `H = {y | c₀ < ⟪y, ν⟫}` has density at least one half in every closed ball
centred in its closure. -/
private theorem two_inv_mul_volume_closedBall_le_volume_closedBall_inter
    {H : Set (EuclideanSpace ℝ (Fin (n + 1)))} {ν x : EuclideanSpace ℝ (Fin (n + 1))} {c₀ : ℝ}
    (hν : ν ≠ 0) (hH : ∀ y, y ∈ H ↔ c₀ < ⟪y, ν⟫_ℝ) (hx : c₀ ≤ ⟪x, ν⟫_ℝ) (r : ℝ) :
    (((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * volume (closedBall x r) ≤ volume (closedBall x r ∩ H) := by
  calc _ = volume ({y | ⟪x, ν⟫_ℝ < ⟪y, ν⟫_ℝ} ∩ closedBall x r) := by
        rw [volume.addHaar_setOf_lt_inner_inter_closedBall hν rfl, ENNReal.coe_inv two_ne_zero,
          ENNReal.coe_ofNat, ENNReal.div_eq_inv_mul]
    _ ≤ _ := by
        rw [inter_comm]
        exact measure_mono (inter_subset_inter_right _ fun y hy => (hH y).2 (hx.trans_lt hy))

/-- The foot `z` of the perpendicular from `x` to the hyperplane `⟪·, ν⟫ = c₀` lies on it, at
distance `d = (⟪x, ν⟫ - c₀) / ‖ν‖` from `x`, and the ball `B(x, d)` lies in the half-space
`c₀ < ⟪·, ν⟫` when `d ≥ 0`. -/
private theorem exists_inner_eq_and_dist_eq {ν : EuclideanSpace ℝ (Fin (n + 1))} (hν : ν ≠ 0)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (c₀ : ℝ) :
    ∃ z, ⟪z, ν⟫_ℝ = c₀ ∧ dist x z = |⟪x, ν⟫_ℝ - c₀| / ‖ν‖ ∧
      ∀ y ∈ ball x ((⟪x, ν⟫_ℝ - c₀) / ‖ν‖), c₀ < ⟪y, ν⟫_ℝ := by
  have hν0 : 0 < ‖ν‖ := norm_pos_iff.2 hν
  refine ⟨x - ((⟪x, ν⟫_ℝ - c₀) / ‖ν‖ ^ 2) • ν, ?_, ?_, fun y hy => ?_⟩
  · rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring
  · rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by
      positivity : (0 : ℝ) < ‖ν‖ ^ 2)]
    field_simp
  · have h1 : ⟪y, ν⟫_ℝ = ⟪x, ν⟫_ℝ + ⟪y - x, ν⟫_ℝ := by rw [inner_sub_left]; ring
    have h2 : -(‖y - x‖ * ‖ν‖) ≤ ⟪y - x, ν⟫_ℝ := (neg_le_of_abs_le (abs_real_inner_le_norm _ _))
    have h3 : ‖y - x‖ * ‖ν‖ < ⟪x, ν⟫_ℝ - c₀ := by
      rw [← dist_eq_norm, ← lt_div_iff₀ hν0]
      exact mem_ball.1 hy
    linarith

/-- The data term after subtracting a linear function `⟪p, ·⟫`: if the data with constant `K_G`
decay like `V (r / R)^e` and `‖p‖² R^{n+1} ≤ K₂ V`, then the data with the constant
`K_G + ‖p‖ K_a` decay like `(2 + 2 K₂ M²) V (r / R)^e`, where `M ≥ K_a R^α` and
`e ≤ n + 1 + 2α`. -/
private theorem rpow_mul_add_sq_mul_add_le {r R α e Ka KG P I V K₂ M : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (hKa : 0 ≤ Ka) (he : e ≤ (n : ℝ) + 1 + 2 * α)
    (hD : r ^ (2 * α) * (KG ^ 2 * r ^ ((n : ℝ) + 1)) + 4 * r ^ 2 * I ≤ V * (r / R) ^ e)
    (hI : 0 ≤ I) (hp : P ^ 2 * R ^ ((n : ℝ) + 1) ≤ K₂ * V) (hM : Ka * R ^ α ≤ M) :
    r ^ (2 * α) * ((KG + P * Ka) ^ 2 * r ^ ((n : ℝ) + 1)) + 4 * r ^ 2 * I ≤
      (2 + 2 * K₂ * M ^ 2) * V * (r / R) ^ e := by
  have hR : 0 < R := hr.trans_le hrR
  have hq : 0 < r / R := div_pos hr hR
  have hq1 : r / R ≤ 1 := (div_le_one hR).2 hrR
  -- The new term `r^{2α} P² K_a² r^{n+1}` is `(K_a R^α)² (P² R^{n+1}) (r / R)^{n+1+2α}`.
  have hsplit : r ^ (2 * α) * (P ^ 2 * Ka ^ 2 * r ^ ((n : ℝ) + 1)) =
      (Ka * R ^ α) ^ 2 * (P ^ 2 * R ^ ((n : ℝ) + 1)) * (r / R) ^ ((n : ℝ) + 1 + 2 * α) := by
    have h1 : r = r / R * R := by field_simp
    have h2 : r ^ (2 * α) = (r / R) ^ (2 * α) * (R ^ α) ^ 2 := by
      conv_lhs => rw [h1]
      rw [Real.mul_rpow hq.le hR.le, mul_comm 2 α, Real.rpow_mul hR.le, Real.rpow_two]
    have h3 : r ^ ((n : ℝ) + 1) = (r / R) ^ ((n : ℝ) + 1) * R ^ ((n : ℝ) + 1) := by
      conv_lhs => rw [h1]
      rw [Real.mul_rpow hq.le hR.le]
    rw [h2, h3, Real.rpow_add hq ((n : ℝ) + 1) (2 * α)]
    ring
  have hMa : (Ka * R ^ α) ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) hM 2
  have hVq : 0 ≤ K₂ * V := (by positivity : 0 ≤ P ^ 2 * R ^ ((n : ℝ) + 1)).trans hp
  have hT : r ^ (2 * α) * (P ^ 2 * Ka ^ 2 * r ^ ((n : ℝ) + 1)) ≤
      M ^ 2 * (K₂ * V) * (r / R) ^ e := by
    rw [hsplit]
    calc _ ≤ M ^ 2 * (K₂ * V) * (r / R) ^ ((n : ℝ) + 1 + 2 * α) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hq hq1 he)
          (by positivity)
  have hsq : (KG + P * Ka) ^ 2 ≤ 2 * KG ^ 2 + 2 * (P ^ 2 * Ka ^ 2) := by
    nlinarith [sq_nonneg (KG - P * Ka)]
  calc _ ≤ r ^ (2 * α) * ((2 * KG ^ 2 + 2 * (P ^ 2 * Ka ^ 2)) * r ^ ((n : ℝ) + 1)) +
        4 * r ^ 2 * I := by gcongr
    _ = 2 * (r ^ (2 * α) * (KG ^ 2 * r ^ ((n : ℝ) + 1)) + 4 * r ^ 2 * I) +
        2 * (r ^ (2 * α) * (P ^ 2 * Ka ^ 2 * r ^ ((n : ℝ) + 1))) - 4 * r ^ 2 * I := by ring
    _ ≤ 2 * (V * (r / R) ^ e) + 2 * (M ^ 2 * (K₂ * V) * (r / R) ^ e) - 0 := by
        gcongr
        positivity
    _ = _ := by ring

/-- **The normal vector at a boundary centre.** Let `H = {y | c₀ < ⟪y, ν⟫}`, let `z` lie on its
boundary hyperplane, let `d > 0`, and let `g ∈ L²(U)` with `B(z, 2d) ⊆ U`. Let `p₀` be the multiple
of `ν` closest to `g` in `L²(B(z, 2d) ∩ H)`. If `∫_{B(z, 2d) ∩ H} ‖g‖² ≤ C_m V (4d / R)^{n+1}` and
`∫_{B(z, 2d) ∩ H} ‖g - p₀‖² ≤ C_b V (4d / R)^e`, then `‖p₀‖² R^{n+1} ≤ 2^{n+2} C_m V / ω`, where `ω`
is the volume of the unit ball, and `∫_{B(x, d)} ‖g - p₀‖² ≤ C_b 4^e V (d / R)^e` for every ball
`B(x, d) ⊆ B(z, 2d) ∩ H`. -/
private theorem exists_norm_sq_mul_rpow_le_and_setIntegral_ball_norm_sub_sq_le
    {U H : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {g : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict U)}
    {ν x z : EuclideanSpace ℝ (Fin (n + 1))} {c₀ d R V Cm Cb e : ℝ} (hν : ν ≠ 0)
    (hH : ∀ y, y ∈ H ↔ c₀ < ⟪y, ν⟫_ℝ) (hz : ⟪z, ν⟫_ℝ = c₀) (hd : 0 < d) (hR : 0 < R)
    (hzU : ball z (2 * d) ⊆ U) (hxz : ball x d ⊆ ball z (2 * d) ∩ H)
    (hM : ∫ y in ball z (2 * d) ∩ H, ‖g y‖ ^ 2 ≤ Cm * V * (2 * d / (R / 2)) ^ ((n : ℝ) + 1))
    (hC : ∫ y in ball z (2 * d) ∩ H, ‖g y -
        (⟪⨍ w in ball z (2 * d) ∩ H, g w, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
      Cb * V * (2 * d / (R / 2)) ^ e) :
    ∃ p : EuclideanSpace ℝ (Fin (n + 1)), ‖p‖ ^ 2 * R ^ ((n : ℝ) + 1) ≤
        2 ^ (n + 2) * Cm / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * V ∧
      ∫ y in ball x d, ‖g y - p‖ ^ 2 ≤ Cb * 4 ^ e * V * (d / R) ^ e := by
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hω : 0 < ω := measureReal_ball_pos volume _ one_pos
  have hg2 : MemLp (g : EuclideanSpace ℝ (Fin (n + 1)) → _) 2
      (volume.restrict (ball z (2 * d) ∩ H)) :=
    (Lp.memLp g).mono_measure (Measure.restrict_mono (inter_subset_left.trans hzU) le_rfl)
  set A := ⨍ w in ball z (2 * d) ∩ H, g w
  refine ⟨(⟪A, ν⟫_ℝ / ‖ν‖ ^ 2) • ν, ?_, ?_⟩
  · -- `‖p₀‖ ≤ ‖A‖`, and `‖A‖²` is at most the mean of `‖g‖²` over `B(z, 2d) ∩ H`.
    have hν0 : 0 < ‖ν‖ := norm_pos_iff.2 hν
    have hpA : ‖(⟪A, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ≤ ‖A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < ‖ν‖ ^ 2),
        div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [abs_real_inner_le_norm A ν, norm_nonneg A]
    have hvol : ω * (2 * d) ^ (n + 1) / 2 ≤ volume.real (ball z (2 * d) ∩ H) := by
      have h := volume.mul_measureReal_ball_le_measureReal_ball_inter
        (two_inv_mul_volume_closedBall_le_volume_closedBall_inter hν hH hz.ge (2 * d))
      rw [volume.addHaar_real_ball_of_pos z (by positivity), finrank_euclideanSpace_fin] at h
      push_cast at h
      linarith
    have hA := (measureReal_mul_sq_norm_setAverage_le measure_ball_inter_ne_top hg2).trans hM
    have hq : (2 * d / (R / 2)) ^ ((n : ℝ) + 1) * R ^ ((n : ℝ) + 1) =
        2 ^ (n + 1) * (2 * d) ^ (n + 1) := by
      rw [← Real.mul_rpow (by positivity) hR.le,
        show 2 * d / (R / 2) * R = 2 * (2 * d) by field_simp,
        show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, mul_pow]
    have hR0 : 0 < R ^ ((n : ℝ) + 1) := by positivity
    have h1 : ‖A‖ ^ 2 * R ^ ((n : ℝ) + 1) * (ω * (2 * d) ^ (n + 1) / 2) ≤
        Cm * V * (2 ^ (n + 1) * (2 * d) ^ (n + 1)) := by
      rw [← hq]
      calc _ = ω * (2 * d) ^ (n + 1) / 2 * ‖A‖ ^ 2 * R ^ ((n : ℝ) + 1) := by ring
        _ ≤ Cm * V * (2 * d / (R / 2)) ^ ((n : ℝ) + 1) * R ^ ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hvol (sq_nonneg _)).trans hA)
            hR0.le
        _ = _ := by ring
    have h2 : Cm * V * (2 ^ (n + 1) * (2 * d) ^ (n + 1)) =
        2 ^ (n + 2) * Cm / ω * V * (ω * (2 * d) ^ (n + 1) / 2) := by
      field_simp
      ring
    rw [h2] at h1
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hpA 2) hR0.le).trans
      (le_of_mul_le_mul_right h1 (by positivity))
  · -- The boundary excess decay bounds `∫_{B(x, d)} ‖g - p₀‖²`.
    calc _ ≤ _ := setIntegral_mono_set (hg2.integrableOn_norm_sub_sq_of_subset subset_rfl
          measure_ball_inter_ne_top _) (ae_of_all _ fun _ => by positivity)
          (Filter.Eventually.of_forall hxz)
      _ ≤ _ := hC
      _ = _ := by
        rw [show 2 * d / (R / 2) = 4 * (d / R) by field_simp; ring,
          Real.mul_rpow (by positivity) (by positivity)]
        ring

/-- **The square mean oscillation at radii beyond the distance to the boundary.** Let `z` lie at
distance `d` from `x`, and let `g ∈ L²(U)` with `B(x, R) ⊆ U`. Suppose that at the centre `z`, for
`0 < ρ ≤ θ' R / 2`, the square distance of `g` from the normal vector `p_ρ` closest to it on
`B(z, ρ) ∩ H` is at most `C_b V (ρ / (R / 2))^e`. If `d < t / θ` and `t ≤ θ θ' R / 4`, with
`θ, θ' ≤ 1`, then the square mean oscillation of `g` on `B(x, t) ∩ H` is at most
`C_b (4 / θ)^e V (t / R)^e`: the half-ball `B(x, t) ∩ H` lies in `B(z, 2t / θ) ∩ H`. -/
private theorem setIntegral_ball_inter_norm_sub_setAverage_sq_le_of_dist_lt
    {U H : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {g : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict U)}
    {ν x z : EuclideanSpace ℝ (Fin (n + 1))} {d t θ θ' R V Cb e : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (ht : 0 < t) (htθ : t ≤ θ * θ' * R / 4) (hθ'1 : θ' ≤ 1) (hR : 0 < R) (hxz : dist x z = d)
    (hdt : d < t / θ) (hBU : ball x R ⊆ U)
    (hC : ∀ ρ, 0 < ρ → ρ ≤ θ' * (R / 2) → ∫ y in ball z ρ ∩ H, ‖g y -
        (⟪⨍ w in ball z ρ ∩ H, g w, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤ Cb * V * (ρ / (R / 2)) ^ e) :
    ∫ y in ball x t ∩ H, ‖g y - ⨍ w in ball x t ∩ H, g w‖ ^ 2 ≤
      Cb * (4 / θ) ^ e * (V * (t / R) ^ e) := by
  have hs0 : 0 < 2 * t / θ := by positivity
  have hsθ : 2 * t / θ ≤ θ' * (R / 2) := by
    rw [div_le_iff₀ hθ]; nlinarith
  have hts : t ≤ t / θ := le_div_self ht.le hθ hθ1
  have hxt : ball x t ⊆ ball z (2 * t / θ) := ball_subset_ball' (by
    rw [hxz]
    have : 2 * t / θ = t / θ + t / θ := by ring
    linarith)
  have hzs : ball z (2 * t / θ) ⊆ U := (ball_subset_ball' (by
    rw [dist_comm, hxz]
    have h1 : t / θ ≤ θ' * R / 4 := by rw [div_le_iff₀ hθ]; nlinarith
    nlinarith)).trans hBU
  calc _ ≤ _ := setIntegral_ball_inter_norm_sub_setAverage_sq_le g hzs hxt _
    _ ≤ Cb * V * (2 * t / θ / (R / 2)) ^ e := hC _ hs0 hsθ
    _ = _ := by
        rw [show 2 * t / θ / (R / 2) = 4 / θ * (t / R) by field_simp; ring,
          Real.mul_rpow (by positivity) (by positivity)]
        ring

/-- **Decay at a nearby boundary centre.** Let `0 < γ < 1` with `γ ≤ α`. There are
`θ ∈ (0, 1]`, `C_m ≥ 0` and `C_b ≥ 0`, depending only on `n`, `α`, `γ`, `λ`, `Λ` and `M`, such that,
in the setting of `exists_setIntegral_ball_inter_norm_gradient_sub_setAverage_sq_le` below, at every
point `z` of the hyperplane `∂H` with `dist x z < R / 2` the gradient satisfies the Morrey and the
Campanato decay estimates on the half-balls `B(z, ρ) ∩ H`, `0 < ρ ≤ θ R / 2`, relative to the
radius `R / 2`. -/
private theorem exists_decay_ball_inter_of_dist_lt {α : ℝ≥0} {γ : ℝ} (hγ : 0 < γ) (hγα : γ ≤ α)
    (hγ1 : γ < 1) {lam Lam M : ℝ} :
    ∃ θ Cm Cb : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ Cm ∧ 0 ≤ Cb ∧
      ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {ν x z : EuclideanSpace ℝ (Fin (n + 1))}
      {c₀ R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (ball x R) a lam Lam → ν ≠ 0 →
      (∀ y, y ∈ H ↔ c₀ < ⟪y, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ → dist x z < R / 2 →
      HolderOnWith Ka α (fun y => matrixBilinearForm (a y)) (ball x R) →
      HolderOnWith KG α G (ball x R) →
      (∀ᵐ y ∂volume.restrict U, y ∉ H → W1p.value u y = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ y in U ⊓ H, ⟪G y, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) y⟫_ℝ) +
          ∫ y in U ⊓ H, f y * φ y) →
      MemLp f 2 (volume.restrict (ball x R ∩ H)) → ball x R ⊆ U → 0 < R →
      (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ y ∈ ball x (R / 2), ∀ r, 0 < r → r ≤ R / 2 →
        r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
          4 * r ^ 2 * ∫ w in ball y r ∩ H, f w ^ 2 ≤ V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ y in ball x R ∩ H, ‖W1p.gradient u y‖ ^ 2 ≤ V →
      (∀ ρ, 0 < ρ → ρ ≤ θ * (R / 2) → ∫ y in ball z ρ ∩ H, ‖W1p.gradient u y‖ ^ 2 ≤
        Cm * V * (ρ / (R / 2)) ^ ((n : ℝ) + 1)) ∧
      (∀ ρ, 0 < ρ → ρ ≤ θ * (R / 2) → ∫ y in ball z ρ ∩ H, ‖W1p.gradient u y -
          (⟪⨍ w in ball z ρ ∩ H, W1p.gradient u w, ν⟫_ℝ / ‖ν‖ ^ 2) • ν‖ ^ 2 ≤
        Cb * V * (ρ / (R / 2)) ^ ((n : ℝ) + 1 + 2 * γ)) := by
  have hα : 0 < α := by exact_mod_cast hγ.trans_le hγα
  obtain ⟨θm, Cm, hθm, hθm1, hCm, hMor⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sq_le_of_holderOnWith (n := n) hα hγ
      (lam := lam) (Lam := Lam) (M := M)
  obtain ⟨θb, Cb, hθb, -, hCb, hCam⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_of_holderOnWith
      (n := n) hγ hγα hγ1 (lam := lam) (Lam := Lam) (M := M)
  refine ⟨min θm θb, Cm, Cb, lt_min hθm hθb, (min_le_left _ _).trans hθm1, hCm, hCb, ?_⟩
  intro U H u a G f ν x z c₀ R V Ka KG hell hν hH hz hxz haK hGK hu0 hu hf hBU hR hM hD hΦR
  have hV0 : 0 ≤ V := (setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
    fun _ _ => by positivity).trans hΦR
  have hzR : ball z (R / 2) ⊆ ball x R := ball_subset_ball' (by rw [dist_comm]; linarith)
  have hzx : z ∈ ball x (R / 2) := by rw [mem_ball, dist_comm]; exact hxz
  have hzR' := mem_ball.2 ((mem_ball.1 hzx).trans (half_lt_self hR))
  have hM' : (Ka : ℝ) * (R / 2) ^ (α : ℝ) ≤ M := (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (half_pos hR).le (half_le_self hR.le) α.coe_nonneg) Ka.coe_nonneg).trans hM
  -- The data decay relative to `R / 2` as well.
  have hDz : ∀ r, 0 < r → r ≤ R / 2 → r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
      4 * r ^ 2 * ∫ w in ball z r ∩ H, f w ^ 2 ≤ V * (r / (R / 2)) ^ ((n : ℝ) + 1 + 2 * γ) :=
    fun r hr hrR => (hD z hzx r hr hrR).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (by positivity) (div_le_div_of_nonneg_left hr.le (half_pos hR) (half_le_self hR.le))
      (by positivity)) hV0)
  have hfz := hf.mono_measure (Measure.restrict_mono (inter_subset_inter_left _ hzR) le_rfl)
  have hgR : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → _) 2
      (volume.restrict (ball x R ∩ H)) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono (inter_subset_left.trans hBU) le_rfl)
  have hint : IntegrableOn (fun y => ‖W1p.gradient u y‖ ^ 2) (ball x R ∩ H) := by
    simpa only [sub_zero] using
      hgR.integrableOn_norm_sub_sq_of_subset subset_rfl measure_ball_inter_ne_top 0
  have hΦz := (setIntegral_mono_set hint (ae_of_all _ fun _ => by positivity)
    (Filter.Eventually.of_forall (inter_subset_inter_left _ hzR))).trans hΦR
  exact ⟨fun ρ hρ hρθ => hMor hell hzR' hν hH hz (haK.mono hzR) (hGK.mono hzR) hu0 hu hfz
      (hzR.trans hBU) (half_pos hR) hM' hDz hΦz ρ hρ
      (hρθ.trans (by gcongr; exact min_le_left _ _)),
    fun ρ hρ hρθ => hCam hell hzR' hν hH hz (haK.mono hzR) (hGK.mono hzR) hu0 hu hfz
      (hzR.trans hBU) (half_pos hR) hM' hDz hΦz ρ hρ
      (hρθ.trans (by gcongr; exact min_le_right _ _))⟩

/-- **Decay of the gradient at a point of the closed half-space.** Let `0 < γ < 1` with `γ ≤ α`.
There are `θ ∈ (0, 1]` and `C ≥ 0`, depending only on `n`, `α`, `γ`, `λ`, `Λ` and `M`, such that
the following holds. Let `H = {y | c₀ < ⟪y, ν⟫}` with `ν ≠ 0`, let `u ∈ H¹(U)` vanish on `U ∖ H`
and solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`, and let `x` lie in the closure of `H`,
with `B(x, R) ⊆ U`. Let `a` be uniformly elliptic on `B(x, R)`, let `a` and `G` be `α`-Hölder there
with constants `K_a` and `K_G`, where `K_a R^α ≤ M`, and let `f ∈ L²(B(x, R) ∩ H)`. If the data
decay like `r^{2α} K_G² r^{n+1} + 4 r² ∫_{B(y, r) ∩ H} f² ≤ V (r / R)^{n+1+2γ}` at every centre
`y ∈ B(x, R / 2)` for `0 < r ≤ R / 2`, and `∫_{B(x, R) ∩ H} ‖∇u‖² ≤ V`, then for `0 < t ≤ θ R`
the square mean oscillation of `∇u` on `B(x, t) ∩ H` is at most `C V (t / R)^{n+1+2γ}`.

Let `d` be the distance from `x` to `∂H` and `z` the nearest point of `∂H`. At radii `t ≳ d` the
half-ball `B(z, 2t / θ') ∩ H` contains `B(x, t) ∩ H`, and the decay at the boundary centre `z`
applies. At radii `t ≲ d` the ball `B(x, t)` lies inside `H`, and the interior decay applies to
`u - ⟪p, ·⟫` on `B(x, d)`, where `p` is the normal vector closest to `∇u` on `B(z, 2d) ∩ H`: by the
boundary decay, `∇u - p` is small on `B(x, d)` in square mean, as the interior estimate needs. -/
private theorem exists_setIntegral_ball_inter_norm_gradient_sub_setAverage_sq_le
    {α : ℝ≥0} {γ : ℝ} (hγ : 0 < γ) (hγα : γ ≤ α) (hγ1 : γ < 1) {lam Lam M : ℝ} :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {ν x : EuclideanSpace ℝ (Fin (n + 1))}
      {c₀ R V : ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (ball x R) a lam Lam → ν ≠ 0 →
      (∀ y, y ∈ H ↔ c₀ < ⟪y, ν⟫_ℝ) → c₀ ≤ ⟪x, ν⟫_ℝ →
      HolderOnWith Ka α (fun y => matrixBilinearForm (a y)) (ball x R) →
      HolderOnWith KG α G (ball x R) →
      (∀ᵐ y ∂volume.restrict U, y ∉ H → W1p.value u y = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ y in U ⊓ H, ⟪G y, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) y⟫_ℝ) +
          ∫ y in U ⊓ H, f y * φ y) →
      MemLp f 2 (volume.restrict (ball x R ∩ H)) → ball x R ⊆ U → 0 < R →
      (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ y ∈ ball x (R / 2), ∀ r, 0 < r → r ≤ R / 2 →
        r ^ (2 * (α : ℝ)) * ((KG : ℝ) ^ 2 * r ^ ((n : ℝ) + 1)) +
          4 * r ^ 2 * ∫ w in ball y r ∩ H, f w ^ 2 ≤ V * (r / R) ^ ((n : ℝ) + 1 + 2 * γ)) →
      ∫ y in ball x R ∩ H, ‖W1p.gradient u y‖ ^ 2 ≤ V →
      ∀ t, 0 < t → t ≤ θ * R →
        ∫ y in ball x t ∩ H, ‖W1p.gradient u y - ⨍ w in ball x t ∩ H, W1p.gradient u w‖ ^ 2 ≤
          C * V * (t / R) ^ ((n : ℝ) + 1 + 2 * γ) := by
  obtain ⟨θB, Cm, Cb, hθB0, hθB1, hCm, hCb, hbd⟩ :=
    exists_decay_ball_inter_of_dist_lt (n := n) hγ hγα hγ1 (lam := lam) (Lam := Lam) (M := M)
  obtain ⟨θi, Ci, hθi, hθi1, hCi, hInt⟩ :=
    exists_setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_sub (n := n) hγ hγα hγ1
      (lam := lam) (Lam := Lam) (M := M)
  set e : ℝ := (n : ℝ) + 1 + 2 * γ
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hω : 0 < ω := measureReal_ball_pos volume _ one_pos
  set K₂ : ℝ := 2 ^ (n + 2) * Cm / ω
  set K : ℝ := Cb * 4 ^ e + (4 / θB) ^ e + 2 + 2 * K₂ * M ^ 2
  refine ⟨θi * θB / 4, Ci * K + Cb * (4 / θi) ^ e, by positivity,
    by nlinarith [mul_le_mul hθi1 hθB1 hθB0.le zero_le_one], by positivity, ?_⟩
  intro U H u a G f ν x c₀ R V Ka KG hell hν hH hx haK hGK hu0 hu hf hBU hR hM hD hΦR t ht htθ
  have hV0 : 0 ≤ V := (setIntegral_nonneg (measurableSet_ball.inter H.isOpen.measurableSet)
    fun _ _ => by positivity).trans hΦR
  have hgR : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → _) 2
      (volume.restrict (ball x R ∩ H)) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono (inter_subset_left.trans hBU) le_rfl)
  have hmono : ∀ s ⊆ ball x R ∩ H, ∫ y in s, ‖W1p.gradient u y‖ ^ 2 ≤ V := fun s hs =>
    (setIntegral_mono_set (by simpa only [sub_zero] using
      hgR.integrableOn_norm_sub_sq_of_subset subset_rfl measure_ball_inter_ne_top 0)
      (ae_of_all _ fun _ => by positivity) (Filter.Eventually.of_forall hs)).trans hΦR
  -- The foot `z` of the perpendicular from `x` to `∂H`, at distance `d`.
  obtain ⟨z, hz, hxz, hballH⟩ := exists_inner_eq_and_dist_eq hν x c₀
  set d := (⟪x, ν⟫_ℝ - c₀) / ‖ν‖ with hd
  have hd0 : 0 ≤ d := div_nonneg (sub_nonneg.2 hx) (norm_nonneg _)
  rw [abs_of_nonneg (sub_nonneg.2 hx), ← hd] at hxz
  have hxH : ball x d ⊆ H := fun y hy => (hH y).2 (hballH y hy)
  -- When `d ≤ θ R / 4`, both decay estimates hold at `z`, on the half-balls of radius `R / 2`.
  have hbdry (hdR : d ≤ θB * R / 4) := hbd hell hν hH hz (by rw [hxz]; nlinarith) haK hGK hu0 hu hf
    hBU hR hM hD hΦR
  have hfinal : 0 ≤ V * (t / R) ^ e := by positivity
  set d₁ := min d (θB * R / 4)
  by_cases hcase : t ≤ θi * d₁
  swap
  · -- Radii `t ≳ d`: compare with the half-ball `B(z, 2 t / θi) ∩ H`.
    push Not at hcase
    have hd₁t : d₁ < t / θi := by rwa [lt_div_iff₀ hθi, mul_comm]
    have hd₁R : d₁ < θB * R / 4 := hd₁t.trans_le (by
      rw [div_le_iff₀ hθi]; linarith)
    have hdR : d < θB * R / 4 := by
      rcases min_lt_iff.1 hd₁R with h | h
      · exact h
      · exact absurd h (lt_irrefl _)
    have hdd : d₁ = d := min_eq_left hdR.le
    obtain ⟨-, hCz⟩ := hbdry hdR.le
    calc _ ≤ Cb * (4 / θi) ^ e * (V * (t / R) ^ e) :=
          setIntegral_ball_inter_norm_sub_setAverage_sq_le_of_dist_lt hθi hθi1 ht
            (htθ.trans_eq (by ring)) hθB1 hR
            hxz (hdd ▸ hd₁t) hBU hCz
      _ ≤ (Ci * K + Cb * (4 / θi) ^ e) * V * (t / R) ^ e := by
          rw [mul_assoc _ V]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hfinal
  -- Radii `t ≲ d`: the interior decay for `u - ⟪p, ·⟫` on `B(x, d₁)`.
  have hd₁0 : 0 < d₁ := pos_of_mul_pos_right (ht.trans_le hcase) hθi.le
  have hd₁d : d₁ ≤ d := min_le_left _ _
  have hd₁R : d₁ ≤ θB * R / 4 := min_le_right _ _
  have hd₁R2 : d₁ ≤ R / 2 := hd₁R.trans (by nlinarith)
  have hxd₁ : ball x d₁ ⊆ ball x R := ball_subset_ball (hd₁R2.trans (half_le_self hR.le))
  have hxd₁H : ball x d₁ ⊆ ball x R ∩ H := subset_inter hxd₁ ((ball_subset_ball hd₁d).trans hxH)
  -- The vector `p`: the normal vector closest to `∇u` on `B(z, 2d) ∩ H` if `d` is small, else `0`.
  obtain ⟨p, hp, hΦp⟩ : ∃ p : EuclideanSpace ℝ (Fin (n + 1)),
      ‖p‖ ^ 2 * R ^ ((n : ℝ) + 1) ≤ K₂ * V ∧
      ∫ y in ball x d₁, ‖W1p.gradient u y - p‖ ^ 2 ≤ K * V * (d₁ / R) ^ e := by
    by_cases hnear : d ≤ θB * R / 4
    · obtain ⟨hMz, hCz⟩ := hbdry hnear
      have hdd : d₁ = d := min_eq_left hnear
      have hdpos : 0 < d := hdd ▸ hd₁0
      have h2d : 2 * d ≤ θB * (R / 2) := by linarith
      have hzU : ball z (2 * d) ⊆ ball x R := ball_subset_ball' (by
        rw [dist_comm, hxz]; nlinarith)
      obtain ⟨p, hp, hΦp⟩ := exists_norm_sq_mul_rpow_le_and_setIntegral_ball_norm_sub_sq_le hν hH hz
        hdpos hR (hzU.trans hBU) (subset_inter (ball_subset_ball' (by rw [hxz]; linarith)) hxH)
        (hMz _ (by positivity) h2d) (hCz _ (by positivity) h2d)
      refine ⟨p, hp, ?_⟩
      rw [hdd]
      refine hΦp.trans ?_
      gcongr
      linarith [(by positivity : 0 ≤ (4 / θB) ^ e), (by positivity : 0 ≤ 2 * K₂ * M ^ 2)]
    · refine ⟨0, ?_, ?_⟩
      · rw [norm_zero, zero_pow two_ne_zero, zero_mul]
        exact mul_nonneg (by positivity) hV0
      have hd₁' : d₁ = θB * R / 4 := min_eq_right (not_le.1 hnear).le
      have h1 : (4 / θB) ^ e * (d₁ / R) ^ e = 1 := by
        rw [← Real.mul_rpow (by positivity) (by positivity), hd₁']
        rw [show 4 / θB * (θB * R / 4 / R) = 1 by field_simp, Real.one_rpow]
      calc _ ≤ V := by simpa only [sub_zero] using hmono _ hxd₁H
        _ = (4 / θB) ^ e * V * (d₁ / R) ^ e := by rw [mul_right_comm, h1, one_mul]
        _ ≤ _ := by gcongr; linarith [(by positivity : 0 ≤ Cb * 4 ^ e),
            (by positivity : 0 ≤ 2 * K₂ * M ^ 2)]
  -- The data with `G` replaced by `G - (a p)^♯` decay as the interior estimate needs.
  have hDx : ∀ r, 0 < r → r ≤ d₁ → r ^ (2 * (α : ℝ)) *
      (((KG : ℝ) + ‖p‖ * Ka) ^ 2 * r ^ ((n : ℝ) + 1)) + 4 * r ^ 2 * ∫ y in ball x r, f y ^ 2 ≤
        K * V * (d₁ / R) ^ e * (r / d₁) ^ e := fun r hr hrd => by
    have hrH : ball x r ∩ H = ball x r :=
      inter_eq_left.2 ((ball_subset_ball (hrd.trans hd₁d)).trans hxH)
    have h := hD x (mem_ball_self (half_pos hR)) r hr (hrd.trans hd₁R2)
    rw [hrH] at h
    have h' := rpow_mul_add_sq_mul_add_le hr (hrd.trans (hd₁R2.trans (half_le_self hR.le)))
      Ka.coe_nonneg (by linarith : e ≤ (n : ℝ) + 1 + 2 * α) h
      (setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _) hp hM
    refine h'.trans ?_
    rw [mul_assoc (K * V), ← Real.mul_rpow (by positivity) (by positivity),
      show d₁ / R * (r / d₁) = r / R by field_simp]
    gcongr
    linarith [(by positivity : 0 ≤ Cb * 4 ^ e), (by positivity : 0 ≤ (4 / θB) ^ e)]
  have hB : ball x d₁ ⊆ (U ⊓ H : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :=
    subset_inter (hxd₁.trans hBU) (hxd₁H.trans inter_subset_right)
  have hM₁ : (Ka : ℝ) * d₁ ^ (α : ℝ) ≤ M := (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
    hd₁0.le (hd₁R2.trans (half_le_self hR.le)) α.coe_nonneg) Ka.coe_nonneg).trans hM
  have hell₁ : UniformlyEllipticOn (ball x d₁) a lam Lam :=
    uniformlyEllipticOn_iff.2 ⟨hell.pos, (uniformlyEllipticOn_iff.1 hell).2.1,
      fun y hy => (uniformlyEllipticOn_iff.1 hell).2.2 (hxd₁ hy)⟩
  have h := hInt hell₁ (haK.mono hxd₁) (hGK.mono hxd₁) hu
    (hf.mono_measure (Measure.restrict_mono hxd₁H le_rfl)) hB hd₁0 hM₁ hDx hΦp t ht hcase
  have htH : ball x t ∩ H = ball x t :=
    inter_eq_left.2 ((ball_subset_ball ((hcase.trans (mul_le_of_le_one_left hd₁0.le hθi1)).trans
      hd₁d)).trans hxH)
  rw [htH]
  calc _ ≤ _ := h
    _ = Ci * K * V * (t / R) ^ e := by
        rw [show 2 * γ + ((n : ℝ) + 1) = e by ring, mul_assoc Ci, mul_assoc (K * V),
          ← Real.mul_rpow (by positivity) (by positivity),
          show d₁ / R * (t / d₁) = t / R by field_simp]
        ring
    _ ≤ _ := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)

/-- **The data on a small half-ball.** The half-space form of
`TauCeti.PDE.rpow_mul_add_mul_setIntegral_sq_le`: if `f ∈ L^q(T ∩ H)` and `B(z, r) ⊆ T`, the data
term on `B(z, r) ∩ H` decays with the exponent `n + 1 + 2β`. -/
private theorem rpow_mul_add_mul_setIntegral_ball_inter_sq_le
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {T H : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hH : MeasurableSet H) {q : ℝ≥0∞} (hq : 2 ≤ q) (hf : MemLp f q (volume.restrict (T ∩ H)))
    {α β KG Q R r : ℝ} (hβα : β ≤ α) (hβq : β ≤ 1 - ((n : ℝ) + 1) / q.toReal) (hKG : 0 ≤ KG)
    (hGQ : R ^ (α - β) * KG ≤ Q)
    (hfQ : R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) *
      (eLpNorm f q (volume.restrict (T ∩ H))).toReal ≤ Q)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hr : 0 < r) (hrR : r ≤ R) (hsub : ball z r ⊆ T) :
    r ^ (2 * α) * (KG ^ 2 * r ^ ((n : ℝ) + 1)) + 4 * r ^ 2 * ∫ x in ball z r ∩ H, f x ^ 2 ≤
      (1 + 4 * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ^ (1 - 2 / q.toReal)) *
        (R ^ (((n : ℝ) + 1) / 2 + β) * Q) ^ 2 * (r / R) ^ ((n : ℝ) + 1 + 2 * β) := by
  -- Extend `f` by zero off `H`.
  have hrestr : (volume.restrict T).restrict H = volume.restrict (T ∩ H) :=
    Measure.restrict_restrict hH |>.trans (by rw [inter_comm])
  have hf' : MemLp (H.indicator f) q (volume.restrict T) :=
    (memLp_indicator_iff_restrict hH.nullMeasurableSet).2 (hrestr ▸ hf)
  have hnorm : eLpNorm (H.indicator f) q (volume.restrict T) =
      eLpNorm f q (volume.restrict (T ∩ H)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hH.nullMeasurableSet, hrestr]
  have hint : ∫ x in ball z r, H.indicator f x ^ 2 = ∫ x in ball z r ∩ H, f x ^ 2 := by
    rw [← setIntegral_indicator hH]
    congr 1
    funext x
    by_cases hx : x ∈ H <;> simp [hx]
  have h := rpow_mul_add_mul_setIntegral_sq_le hq hf' hβα hβq hKG hGQ (hnorm ▸ hfQ) hr hrR hsub
  rwa [hint] at h

/-- **Schauder estimate up to a flat boundary for divergence-form equations with a scalar datum.**
Let `0 < β < 1` with `β ≤ α`, let `2 ≤ q ≤ ∞` and `β ≤ 1 - (n + 1) / q`, where `(n + 1) / ∞ = 0`.
There is a constant `C`, depending only on `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`, such that the
following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, and let `u ∈ H¹(U)` vanish on `U ∖ H`
and solve `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `U ∩ H`, that is
`∫ ⟨a ∇u, ∇φ⟩ = ∫ ⟨G, ∇φ⟩ + ∫ f φ` for every test function `φ` on `U ∩ H`: so `u` has zero boundary
values on the flat part `U ∩ ∂H` of the boundary. Let `S` be a subset of the closed half-space
whose open `R`-thickening `S_R` lies in `U`, let `a` be uniformly elliptic with constants `λ`, `Λ`
on `S_R`, let `a` and `G` be `α`-Hölder on `S_R` with constants `K_a` and `K_G`, the oscillation of
`a` measured in the operator norm of the attached bilinear forms, where `K_a R^α ≤ M`, and let
`f ∈ L^q(S_R ∩ H)`. Then the precise representative of `∇u` with respect to the Lebesgue measure on
`H` is `β`-Hölder on `S`, with constant

`C (K_G R^{α-β} + R^{1-(n+1)/q-β} ‖f‖_{L^q(S_R ∩ H)} + R^{-(n+1)/2-β} ‖∇u‖_{L²(U)})`.

The set `S` may meet the hyperplane `∂H`, so this is the `C^{1,β}` estimate up to the flat part of
the boundary. The precise representative is the limit of the averages of `∇u` over the half-balls
`B(x, r) ∩ H`; it agrees with `∇u` almost everywhere on `H`
(`TauCeti.MeasureTheory.ae_eq_preciseRepresentative_of_hasBesicovitchCovering`). No symmetry of
`a` and no condition on `a` or `G` at the hyperplane is needed. -/
theorem
    exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith_of_memLp
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {ν : EuclideanSpace ℝ (Fin (n + 1))} {c₀ : ℝ}
      {Ka KG : ℝ≥0} {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → (∀ x ∈ S, c₀ ≤ ⟪x, ν⟫_ℝ) →
      UniformlyEllipticOn (thickening R S) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (thickening R S) →
      HolderOnWith KG α G (thickening R S) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      MemLp f q (volume.restrict (thickening R S ∩ H)) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        (∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in U ⊓ H, f x * φ x) →
      0 < R → thickening R S ⊆ U →
        HolderOnWith (C * (KG * R ^ ((α : ℝ) - β) +
            R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) *
              (eLpNorm f q (volume.restrict (thickening R S ∩ H))).toReal +
            R ^ (-(((n : ℝ) + 1) / 2 + β)) * ‖W1p.gradient u‖)).toNNReal β
          (preciseRepresentative (volume.restrict (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  have hβ' : (0 : ℝ) < β := hβ
  obtain ⟨θ, C₀, hθ, hθ1, hC₀, hdec⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sub_setAverage_sq_le (n := n) (α := α) hβ'
      (by exact_mod_cast hβα) (by exact_mod_cast hβ1) (lam := lam) (Lam := Lam) (M := M)
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) with hωdef
  have hω : 0 < ω := measureReal_ball_pos volume _ one_pos
  set c₁ : ℝ := 1 + 4 * ω ^ (1 - 2 / q.toReal)
  have hc₁ : 1 ≤ c₁ := le_add_of_nonneg_right (by positivity)
  set Mo : ℝ := √(2 * (C₀ * c₁) / ω)
  set Bo : ℝ := √(2 / (ω * θ ^ (n + 1)))
  set cc : ℝ := 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) /
    (((2 : ℝ≥0)⁻¹ : ℝ≥0) * (1 - 2 ^ (-(β : ℝ))))
  have hcc : 0 ≤ cc := div_nonneg (by positivity) (mul_nonneg (by positivity)
    (sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hβ'))).le)
  refine ⟨2 * 2 ^ (β : ℝ) * (cc * Mo + Bo * θ ^ (-(β : ℝ))), by positivity, ?_⟩
  intro U H u a G f ν c₀ Ka KG S R hν hH hS hell haK hGK hM hf hu0 hu hR hRS
  have hHm : MeasurableSet (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) := H.isOpen.measurableSet
  set Kf := (eLpNorm f q (volume.restrict (thickening R S ∩ H))).toReal
  set Q := (KG : ℝ) * R ^ ((α : ℝ) - β) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) * Kf +
    R ^ (-(((n : ℝ) + 1) / 2 + β)) * ‖W1p.gradient u‖ with hQ
  have hRu : 0 ≤ R ^ (-(((n : ℝ) + 1) / 2 + β)) * ‖W1p.gradient u‖ := by positivity
  have hRG : 0 ≤ (KG : ℝ) * R ^ ((α : ℝ) - β) := by positivity
  have hRf : 0 ≤ R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) * Kf := by positivity
  have hGQ : R ^ ((α : ℝ) - β) * KG ≤ Q := by rw [mul_comm]; linarith
  have hfQ : R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) * Kf ≤ Q := by linarith
  set X := R ^ (((n : ℝ) + 1) / 2 + β) * Q with hX
  have hVR : X ^ 2 = R ^ ((n : ℝ) + 1) * (R ^ (β : ℝ) * Q) ^ 2 :=
    Real.rpow_div_two_add_mul_sq Q hR
  have hXu : ‖W1p.gradient u‖ ≤ X := by
    rw [hX, hQ, mul_add, ← mul_assoc _ (R ^ _), ← Real.rpow_add hR, add_neg_cancel,
      Real.rpow_zero, one_mul]
    exact le_add_of_nonneg_left (by positivity)
  have hX2 : ‖W1p.gradient u‖ ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hXu 2
  set V := c₁ * X ^ 2 with hV
  have hxR : ∀ x ∈ S, ball x R ⊆ thickening R S := fun x hx => ball_subset_thickening hx R
  have hgS : ∀ x ∈ S, ∀ t ≤ R, MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → _) 2
      (volume.restrict (ball x t ∩ H)) := fun x hx t htR =>
    (Lp.memLp _).mono_measure (Measure.restrict_mono
      (inter_subset_left.trans (((ball_subset_ball htR).trans (hxR x hx)).trans hRS)) le_rfl)
  -- The square mean oscillation of `∇u` on the half-balls decays like `t^{n+1+2β}`.
  have hdecx : ∀ x ∈ S, ∀ t, 0 < t → t ≤ θ * R →
      ∫ y in ball x t ∩ H, ‖W1p.gradient u y - ⨍ w in ball x t ∩ H, W1p.gradient u w‖ ^ 2 ≤
        C₀ * V * (t / R) ^ ((n : ℝ) + 1 + 2 * β) := fun x hx t ht htθ => by
    have hfin : IsFiniteMeasure (volume.restrict (ball x R ∩ H)) :=
      isFiniteMeasure_restrict.2 measure_ball_inter_ne_top
    refine hdec (uniformlyEllipticOn_iff.2 ⟨hell.pos, (uniformlyEllipticOn_iff.1 hell).2.1,
        fun y hy => (uniformlyEllipticOn_iff.1 hell).2.2 (hxR x hx hy)⟩) hν hH (hS x hx)
      (haK.mono (hxR x hx)) (hGK.mono (hxR x hx)) hu0 hu
      ((hf.mono_measure (Measure.restrict_mono (inter_subset_inter_left _ (hxR x hx))
        le_rfl)).mono_exponent hq) ((hxR x hx).trans hRS) hR hM
      (fun y hy r hr hrR => ?_) ?_ t ht htθ
    · exact rpow_mul_add_mul_setIntegral_ball_inter_sq_le hHm hq hf (by exact_mod_cast hβα) hβq
        KG.coe_nonneg hGQ hfQ hr (hrR.trans (half_le_self hR.le))
        ((ball_subset_ball' (by linarith [(mem_ball.1 hy).le])).trans (hxR x hx))
    · exact (Lp.setIntegral_norm_sq_le_norm_sq _ (inter_subset_left.trans
        ((hxR x hx).trans hRS))).trans (hX2.trans (le_mul_of_one_le_left (sq_nonneg _) hc₁))
  have hdens : ∀ x ∈ S, ∀ r : ℝ, (((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * volume (closedBall x r) ≤
      volume (closedBall x r ∩ H) := fun x hx r =>
    two_inv_mul_volume_closedBall_le_volume_closedBall_inter hν hH (hS x hx) r
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  -- The mean oscillation of `∇u` on the half-ball `B(x, t) ∩ H` is at most `Mo Q t^β`.
  have hosc : ∀ x ∈ S, ∀ t, 0 < t → t ≤ θ * R →
      ⨍ y in closedBall x t, ‖W1p.gradient u y - ⨍ w in closedBall x t, W1p.gradient u w
          ∂volume.restrict H‖ ∂volume.restrict H ≤ Mo * Q * t ^ (β : ℝ) := fun x hx t ht htθ => by
    have h := setAverage_closedBall_restrict_norm_sub_le (μ := volume) (κ := (β : ℝ))
      (C := C₀) (V := V) (by norm_num) hR ht (hdens x hx t) (hgS x hx t (htθ.trans hθR))
      ((hdecx x hx t ht htθ).trans_eq (by
        rw [finrank_euclideanSpace_fin, ← Real.rpow_natCast, Real.rpow_add (div_pos ht hR)]
        push_cast
        ring_nf))
    refine h.trans_eq ?_
    have hRn : R ^ (n + 1) = R ^ ((n : ℝ) + 1) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    have key : C₀ * (V / volume.real (ball x R)) / (((2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) =
        2 * (C₀ * c₁) / ω * (R ^ (β : ℝ) * Q) ^ 2 := by
      rw [volume.addHaar_real_ball_of_pos x hR, finrank_euclideanSpace_fin, ← hωdef, hRn, hV,
        hVR]
      push_cast
      field_simp
    rw [key, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [mul_assoc Mo, mul_comm (R ^ (β : ℝ)) Q, mul_assoc Q, ← Real.rpow_add hR,
      add_neg_cancel, Real.rpow_zero, mul_one]
  -- The average of `∇u` over the half-ball `B(x, θ R) ∩ H` is at most `Bo R^β Q`.
  have havg : ∀ x ∈ S, ‖⨍ y in closedBall x (θ * R), W1p.gradient u y ∂volume.restrict H‖ ≤
      Bo * R ^ (β : ℝ) * Q := fun x hx => by
    rw [volume.restrict_restrict_closedBall_eq_restrict_ball_inter]
    have hθR0 : 0 < θ * R := by positivity
    have h1 := (measureReal_mul_sq_norm_setAverage_le measure_ball_inter_ne_top
      (hgS x hx _ hθR)).trans ((Lp.setIntegral_norm_sq_le_norm_sq _ (inter_subset_left.trans
        (((ball_subset_ball hθR).trans (hxR x hx)).trans hRS))).trans hX2)
    have hvol : ω * (θ * R) ^ (n + 1) / 2 ≤ volume.real (ball x (θ * R) ∩ H) := by
      have h := volume.mul_measureReal_ball_le_measureReal_ball_inter (hdens x hx (θ * R))
      rw [volume.addHaar_real_ball_of_pos x hθR0, finrank_euclideanSpace_fin, ← hωdef] at h
      push_cast at h
      linarith
    have hRn : R ^ ((n : ℝ) + 1) = R ^ (n + 1) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    rw [hVR, hRn] at h1
    have h2 : ‖⨍ y in ball x (θ * R) ∩ H, W1p.gradient u y‖ ^ 2 ≤ (Bo * R ^ (β : ℝ) * Q) ^ 2 := by
      have h3 : ‖⨍ y in ball x (θ * R) ∩ H, W1p.gradient u y‖ ^ 2 *
          (ω * (θ * R) ^ (n + 1) / 2) ≤
            (Bo * R ^ (β : ℝ) * Q) ^ 2 * (ω * (θ * R) ^ (n + 1) / 2) := by
        rw [show (Bo * R ^ (β : ℝ) * Q) ^ 2 * (ω * (θ * R) ^ (n + 1) / 2) =
            R ^ (n + 1) * (R ^ (β : ℝ) * Q) ^ 2 by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), mul_pow θ]
          field_simp]
        nlinarith [sq_nonneg ‖⨍ y in ball x (θ * R) ∩ H, W1p.gradient u y‖]
      exact le_of_mul_le_mul_right h3 (by positivity)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hH' := holderOnWith_preciseRepresentative_restrict_of_setAverage_norm_sub_le_of_norm_le
    (μ := volume) (Ω := (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) (c := 2⁻¹) (ρ := θ * R) hβ
    (by norm_num) (by positivity) (fun x hx => by
      rw [IntegrableOn, volume.restrict_restrict_closedBall_eq_restrict_ball_inter]
      exact (hgS x hx _ hθR).integrableOn_of_subset one_le_two subset_rfl measure_ball_inter_ne_top)
    (fun x hx r _ _ => hdens x hx r) hosc havg
  have hconst : cc * (Mo * Q) + Bo * R ^ (β : ℝ) * Q * (θ * R) ^ (-(β : ℝ)) =
      (cc * Mo + Bo * θ ^ (-(β : ℝ))) * Q := by
    rw [Real.mul_rpow hθ.le hR.le, Real.rpow_neg hR.le]
    field_simp [(Real.rpow_pos_of_pos hR (β : ℝ)).ne']
  rwa [hconst, ← mul_assoc] at hH'

/-- **Schauder estimate up to a flat boundary for divergence-form equations.** Let `0 < α < 1`.
There is a constant `C`, depending only on `n`, `α`, `λ`, `Λ` and `M`, such that the following
holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, and let `u ∈ H¹(U)` vanish on `U ∖ H` and solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly on `U ∩ H`. Let `S` be a subset of the closed half-space whose open
`R`-thickening `S_R` lies in `U`, let `a` be uniformly elliptic with constants `λ`, `Λ` on `S_R`,
and let `a` and `G` be `α`-Hölder on `S_R` with constants `K_a` and `K_G`, where `K_a R^α ≤ M`.
Then the precise representative of `∇u` with respect to the Lebesgue measure on `H` is `α`-Hölder
on `S`, with constant `C (K_G + R^{-(n+1)/2-α} ‖∇u‖_{L²(U)})`.

This is the case `f = 0`, `q = ∞`, `β = α` of
`exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith_of_memLp`; it is the
boundary counterpart of the interior estimate
`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`. -/
theorem exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume U 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {ν : EuclideanSpace ℝ (Fin (n + 1))} {c₀ : ℝ}
      {Ka KG : ℝ≥0} {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → (∀ x ∈ S, c₀ ≤ ⟪x, ν⟫_ℝ) →
      UniformlyEllipticOn (thickening R S) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (thickening R S) →
      HolderOnWith KG α G (thickening R S) → (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ φ : 𝓓(U ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
          (W1p.ofTestFunctionₗ volume (U ⊓ H) 2 φ) =
        ∫ x in U ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      0 < R → thickening R S ⊆ U →
        HolderOnWith (C * (KG + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)).toNNReal α
          (preciseRepresentative (volume.restrict (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  -- The datum is `f = 0`, which lies in `L^∞`.
  obtain ⟨C, hC, h⟩ :=
    exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith_of_memLp
      (n := n) hα hα1 le_rfl le_top (by simpa using hα1.le) (lam := lam) (Lam := Lam) (M := M)
  refine ⟨C, hC, fun hν hH hS hell haK hGK hM hu0 hu hR hRS => ?_⟩
  have h' := h hν hH hS hell haK hGK hM (f := 0) MemLp.zero hu0
    (fun φ => by rw [hu φ, Pi.zero_def]; simp only [zero_mul, integral_zero, add_zero]) hR hRS
  simpa only [sub_self, Real.rpow_zero, mul_one, eLpNorm_zero, ENNReal.toReal_zero, mul_zero,
    add_zero] using h'

end PDE

end TauCeti
