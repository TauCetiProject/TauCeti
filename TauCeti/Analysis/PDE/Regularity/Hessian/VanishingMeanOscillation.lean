/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.SmallMeanOscillation
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Cutoff
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Matrix.Contraction.LpNorm
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable
import TauCeti.Analysis.PDE.Ellipticity.Integral
import TauCeti.Analysis.SpecificLimits.Absorption
import TauCeti.Analysis.Sobolev.Wkp.Interpolation
import TauCeti.Analysis.PDE.Regularity.Hessian.Interior
import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import TauCeti.Analysis.Sobolev.Wkp.Extension
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball

/-!
# Interior and whole-space `W^{2,p}` estimates for coefficients of vanishing mean oscillation

Let `a` be a coefficient matrix on `ℝ^{n+1}`, neither symmetric nor continuous in general, and let
`u ∈ W^{2,p}(Ω)` be a strong solution of the non-divergence-form equation

`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on a ball `B_R = B(x₀, R) ⊆ Ω`.

Suppose that `a` is uniformly elliptic with constants `0 < λ ≤ Λ` on `B(x₀, 2 R)` and that its VMO
modulus at the scale `16 R` is at most `δ`: on every ball of radius at most `16 R`, `a` deviates in
mean from its average by at most `δ`, in the operator norm of `a(x)` acting on Euclidean space
(`Matrix.toEuclideanCLM`; this is also the norm of the attached bilinear form,
`TauCeti.PDE.norm_matrixBilinearForm_eq_norm_toEuclideanCLM`). This file proves the interior
estimate

`(R - r)² ‖D²u‖_{Lᵖ(B_r)} ≤ C (R² ‖f‖_{Lᵖ(B_R)} + ‖u‖_{Lᵖ(B_R)})`, `2 < p < ∞`, `r < R`,

with `C` and the threshold `δ` depending only on `n`, `p`, `λ` and `Λ`
(`TauCeti.PDE.exists_mul_lpNorm_iteratedGradient_ball_le_of_vmoModulus_le`). For coefficients of
vanishing mean oscillation the threshold is reached below some radius `r₀`, and on every ball of
radius `R ≤ r₀`
`‖D²u‖_{Lᵖ(B_{R/2})} ≤ C (‖f‖_{Lᵖ(B_R)} + R⁻² ‖u‖_{Lᵖ(B_R)})`
(`TauCeti.PDE.exists_lpNorm_iteratedGradient_ball_le_of_memVMO`). The restriction `p > 2` is that of
the whole-space estimate for coefficients of small mean oscillation; the interior estimate treats
the principal part alone.

Averaging the `p`-th powers of the interior estimates over all centres turns them into the estimate
on the whole space (`TauCeti.lpNorm_le_of_ae_lpNorm_restrict_ball_le_add`): for `a` uniformly
elliptic on `ℝ^{n+1}` with vanishing mean oscillation, every `u ∈ W^{2,p}(ℝ^{n+1})` satisfies

`‖D²u‖_{Lᵖ} ≤ C (‖∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu‖_{Lᵖ} + r₀⁻² ‖u‖_{Lᵖ})`

with the same `r₀` and `C` depending only on `n`, `p`, `λ` and `Λ`
(`TauCeti.PDE.exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_memVMO`). Bounded lower-order
terms `⟪b, ∇u⟫ + c u` are then absorbed by the interpolation inequality for the gradient
(`TauCeti.PDE.exists_norm_iteratedGradient_le_of_sum_mul_inner_add_inner_add_mul_eq_of_memVMO`).
For `2 < p < ∞` these give the Hessian part of the a priori estimate in Krylov's whole-space
theorem, without its zero-order shift `λ u`, `λ ≥ λ₀` (which removes `‖u‖_{Lᵖ}` from the right
side), and without the range `1 < p ≤ 2`.

## The argument

* **Extension of the coefficients.** The VMO modulus controls the mean oscillation of `a` on small
  balls only, while the whole-space estimate
  `TauCeti.PDE.exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le` needs small
  mean oscillation at every scale. The field `ψ a + (1 - ψ) a_{B(x₀, 2 R)}`, for the ramp `ψ` from
  `1` on `B(x₀, R)` to `0` off `B(x₀, 2 R)`, agrees with `a` on `B_R`, is uniformly elliptic
  everywhere, since the uniformly elliptic operators form a closed convex set, and has BMO seminorm
  at most `(2 + 20 · 8ⁿ⁺¹) δ`
  (`MeasureTheory.LocallyIntegrable.exists_forall_mem_and_bmoSeminorm_le_and_eqOn`). On every ball
  it is therefore close in mean to its average, which is uniformly elliptic.
* **Localization.** For a cutoff `ζ` between `B_s` and `B_t`, `t ≤ R`, the product `ζ u` lies in
  `W^{2,2}_0(B_t)`, since `W^{2,p}(B_t) ⊆ W^{2,2}(B_t)` on the ball of finite measure, and its
  Hessian is `ζ D²u + T` with the Leibniz remainder `T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ`. Its extension
  by zero is a whole-space solution with the extended coefficients and right side
  `ζ f + ∑ᵢⱼ aᵢⱼ Tᵢⱼ`, so the whole-space estimate bounds `D²u` on `B_s` by `f` on `B_R`, `∇u` on
  `B_t` and `u` on `B_R`.
* **Absorption.** As for the estimate with coefficients of small oscillation
  (`TauCeti.PDE.exists_mul_lpNorm_iteratedGradient_ball_le_of_sum_mul_inner_add_inner_add_mul_eq`),
  the interpolation inequality between concentric balls
  (`TauCeti.Wkp.exists_lpNorm_gradient_ball_le`) and the weighted seminorms of
  `TauCeti.sq_mul_le_of_forall_le` remove the gradient term.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475, Theorem 2.6 (the whole-space `W^{2,p}` estimate
  for coefficients of vanishing mean oscillation; the interior estimate follows by a cutoff).
* F. Chiarenza, M. Frasca, P. Longo, *Interior W^{2,p} estimates for non divergence elliptic
  equations with discontinuous coefficients*, Ricerche Mat. **40** (1991), 149–168.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.11 and its proof (the weighted interior seminorms).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace Metric Module Set
open scoped ENNReal NNReal InnerProductSpace Gradient ContDiff Matrix

section Coefficient

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Extension of a coefficient field from a ball.** Let `a` be uniformly elliptic with the
constants `λ, Λ` on `B(x₀, 2 R)`, with VMO modulus `η(16 R) ≤ δ` as a function with values in the
operators on `ℝⁿ`. Then `a` agrees on `B(x₀, R)` with a measurable coefficient field `a'`, uniformly
elliptic with the constants `λ, Λ` everywhere, whose mean deviation from some constant matrix,
uniformly elliptic with the same constants, is at most `(2 + 20 · 8ⁿ) δ` on every ball, of any
radius, in the operator norm of the attached bilinear forms. -/
private theorem exists_eqOn_ball_and_forall_setAverage_matrixBilinearForm_sub_le {lam Lam δ R : ℝ}
    (hδ : 0 ≤ δ) (hR : 0 < R) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {x₀ : EuclideanSpace ℝ ι}
    (hloc : LocallyIntegrable (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume)
    (hell : UniformlyEllipticOn (ball x₀ (2 * R)) a lam Lam)
    (hη : vmoModulus (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume (16 * R) ≤
      ENNReal.ofReal δ) :
    ∃ a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ, AEStronglyMeasurable a' volume ∧
      UniformlyEllipticOn univ a' lam Lam ∧ EqOn a' a (ball x₀ R) ∧
      ∀ (c : EuclideanSpace ℝ ι) (r : ℝ), 0 < r → ∃ A : Matrix ι ι ℝ,
        UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
          ⨍ x in ball c r, ‖matrixBilinearForm (a' x) - matrixBilinearForm A‖ ≤
            (2 + 20 * 8 ^ finrank ℝ (EuclideanSpace ℝ ι)) * δ := by
  obtain ⟨β, hβloc, hβK, hbmo, hβb⟩ :=
    hloc.exists_forall_mem_and_bmoSeminorm_le_and_eqOn (E := EuclideanSpace ℝ ι)
      (F := EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (μ := volume)
      (S := ellipticCLMSet lam Lam) (convex_ellipticCLMSet lam Lam)
      (isClosed_ellipticCLMSet lam Lam) hR fun x hx =>
        (toEuclideanCLM_mem_ellipticCLMSet_iff _).2 ((uniformlyEllipticOn_iff.1 hell).2.2 hx)
  set a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ := fun x => (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (β x)
  have he (x : EuclideanSpace ℝ ι) : Matrix.toEuclideanCLM (𝕜 := ℝ) (a' x) = β x :=
    StarAlgEquiv.apply_symm_apply _ _
  have ha' : AEStronglyMeasurable a' volume :=
    Matrix.aestronglyMeasurable_toEuclideanCLM_iff.1
      (hβloc.aestronglyMeasurable.congr (ae_of_all _ fun x => (he x).symm))
  have hell' : UniformlyEllipticOn univ a' lam Lam :=
    uniformlyEllipticOn_of_forall_toEuclideanCLM_mem hell.pos hell.le fun x _ => by
      rw [he]
      exact hβK x
  refine ⟨a', ha', hell', fun x hx => ?_, fun c r hr => ?_⟩
  · simp only [a', hβb hx, StarAlgEquiv.symm_apply_apply]
  -- On a ball, freeze at the average of `β`, whose mean oscillation is at most its BMO seminorm.
  have hD : (2 + 20 * 8 ^ finrank ℝ (EuclideanSpace ℝ ι) : ℝ≥0∞) * ENNReal.ofReal δ =
      ENNReal.ofReal ((2 + 20 * 8 ^ finrank ℝ (EuclideanSpace ℝ ι)) * δ) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    norm_cast
  refine (hell'.mono_set (subset_univ _)).exists_uniformlyEllipticOn_const_and_setAverage_le
    measurableSet_ball ha'.restrict (measure_ball_pos volume c hr).ne' measure_ball_lt_top.ne
    (by positivity) ?_
  simpa only [he, hD] using
    (setLAverage_enorm_sub_setAverage_le_bmoSeminorm β volume c r).trans
    (hbmo.trans (mul_le_mul_of_nonneg_left hη zero_le))

end Coefficient

section Estimate

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- **The small mean oscillation estimate on an open set of finite measure.** The whole-space
estimate `exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le`, applied to
the extension by zero of `w ∈ W^{2,2}_0(U)`, bounds `‖D²w‖_{Lᵖ(U)}` by the `Lᵖ(U)` norm of
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼw` when `D²w ∈ Lᵖ(U)`. -/
private theorem exists_lpNorm_iteratedGradient_le_of_mem_wkp0Submodule (hp : 2 < p)
    (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → UniformlyEllipticOn univ a lam Lam →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
      ∀ {U : Opens (EuclideanSpace ℝ (Fin (n + 1)))},
        volume (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≠ ⊤ →
      ∀ w ∈ wkp0Submodule (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) U 2 2,
        MemLp (Wkp.iteratedGradient 1 w : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p
          (volume.restrict U) →
      ∀ {F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}, MemLp F p (volume.restrict U) →
        (∀ᵐ x ∂volume.restrict U,
          Matrix.contraction (a x) (Wkp.iteratedGradient 1 w x) = F x) →
        lpNorm (Wkp.iteratedGradient 1 w) p (volume.restrict U) ≤
          C * lpNorm F p (volume.restrict U) := by
  obtain ⟨C, δ, hδ, hCZ⟩ :=
    exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le (n := n)
      (ENNReal.one_lt_two.trans hp) hp_top lam Lam
  refine ⟨C, δ, hδ, fun {a} ha haΛ hosc {U} hUfin w hw0 hwp {F} hF heq => ?_⟩
  have : IsFiniteMeasure (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 hUfin
  have hUm : MeasurableSet (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) := U.isOpen.measurableSet
  set W : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ 2 2 :=
    (Wkp0.extendByZeroₗᵢ (le_top : U ≤ ⊤) 2 ⟨w, hw0⟩).val
  have hW : ∀ᵐ x, Wkp.iteratedGradient 1 W x =
      (U : Set _).indicator (Wkp.iteratedGradient 1 w : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) x := by
    simpa only [Filter.EventuallyEq, Opens.coe_top, Measure.restrict_univ] using
      Wkp0.iteratedGradient_extendByZeroₗᵢ_ae_eq_indicator le_top 1 ⟨w, hw0⟩
  have hWeq : ∀ᵐ x, ∑ i, ∑ j, a x i j *
      ⟪Wkp.iteratedGradient 1 W x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
        (U : Set _).indicator F x := by
    filter_upwards [ae_contraction_iteratedGradient_extendByZeroₗᵢ_eq_indicator (w := ⟨w, hw0⟩)
      heq] with x hx
    rw [← hx, Matrix.contraction_apply]
  have hkey := hCZ ha (fun x => haΛ.opNorm_matrixBilinearForm_le (mem_univ x)) hosc
    (min_le_right p 2) W _ hWeq
    (((memLp_indicator_iff_restrict hUm.nullMeasurableSet).2 hwp).ae_eq
      (hW.mono fun _ h => h.symm))
    ((memLp_indicator_iff_restrict hUm.nullMeasurableSet).2 hF)
  have e1 : eLpNorm (Wkp.iteratedGradient 1 W : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p volume =
      eLpNorm (Wkp.iteratedGradient 1 w : EuclideanSpace ℝ (Fin (n + 1)) →
        EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p
        (volume.restrict U) := by
    rw [eLpNorm_congr_ae hW]
    exact eLpNorm_indicator_eq_eLpNorm_restrict
      (ε := EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
      hUm.nullMeasurableSet
  rw [e1, eLpNorm_indicator_eq_eLpNorm_restrict (f := F) hUm.nullMeasurableSet] at hkey
  rw [← toReal_eLpNorm, ← toReal_eLpNorm, ← ENNReal.coe_toReal, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hF.eLpNorm_ne_top) hkey

/-- **The localized estimate for coefficients of small mean oscillation.** For `2 < p < ∞`, a
coefficient field `a` of small mean oscillation at every scale, an open set `U ⊆ Ω` of finite
measure, a smooth cutoff `ζ` with compact support in `U` and `‖∇ζ‖ ≤ M₁`, `‖D²ζ‖ ≤ M₂`, every
`u ∈ W^{2,p}(Ω)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` on `U` satisfies
`‖ζ D²u‖ ≤ C ‖ζ f‖ + (C (n + 1)² Λ + 1) (2 M₁ ‖∇u‖ + M₂ ‖u‖)` in `Lᵖ(U)`. -/
private theorem exists_lpNorm_smul_iteratedGradient_le (hp : 2 < p) (hp_top : p ≠ ⊤)
    (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        AEStronglyMeasurable a volume → UniformlyEllipticOn univ a lam Lam →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
      ∀ {Omega U : Opens (EuclideanSpace ℝ (Fin (n + 1)))}, U ≤ Omega →
        volume (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≠ ⊤ →
      ∀ {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {M₁ M₂ : ℝ}, ContDiff ℝ ∞ ζ →
        HasCompactSupport ζ → tsupport ζ ⊆ U → (∀ x, ‖∇ ζ x‖ ≤ M₁) →
        (∀ x, ‖fderiv ℝ (∇ ζ) x‖ ≤ M₂) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega p 2)
        {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}, MemLp f p (volume.restrict U) →
        (∀ᵐ x ∂volume.restrict U,
          Matrix.contraction (a x) (Wkp.iteratedGradient 1 u x) = f x) →
        lpNorm (fun x => ζ x • Wkp.iteratedGradient 1 u x) p (volume.restrict U) ≤
          C * lpNorm (fun x => ζ x * f x) p (volume.restrict U) +
            (C * ((n + 1 : ℕ) : ℝ) ^ 2 * Lam + 1) *
              (2 * M₁ * lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p
                (volume.restrict U) + M₂ * lpNorm (Wkp.value 2 u) p (volume.restrict U)) := by
  obtain ⟨C, δ, hδ, hW0⟩ := exists_lpNorm_iteratedGradient_le_of_mem_wkp0Submodule (n := n) hp
    hp_top lam Lam
  refine ⟨C, δ, hδ, fun {a} ha haΛ hosc {Omega U} hU hUfin {ζ M₁ M₂} hζ hcpt hζU hM₁ hM₂ u f hf
    heq => ?_⟩
  obtain ⟨w, hw0, hDw⟩ := Wkp.exists_mem_wkp0Submodule_iteratedGradient_ae_eq (q := 2) hp.le
    ENNReal.ofNat_ne_top hU hUfin hζ hcpt hζU u
  set T := fun x => leibnizRemainder ζ (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x)
    (Wkp.value 2 u x) x
  have hζ_top := hζ.continuous.memLp_top_of_hasCompactSupport hcpt
    (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))))
  have hζH : MemLp (fun x => ζ x • Wkp.iteratedGradient 1 u x) p (volume.restrict U) :=
    hζ_top.smul ((Lp.memLp _).mono_measure (Measure.restrict_mono hU le_rfl))
  have hTm : AEStronglyMeasurable T (volume.restrict U) := by
    refine ((Lp.aestronglyMeasurable (Wkp.iteratedGradient 1 w)).sub
      hζH.aestronglyMeasurable).congr ?_
    filter_upwards [hDw] with x hx
    simp only [Pi.sub_apply, hx, add_sub_cancel_left, T]
  obtain ⟨hTU, hTle⟩ := Wkp.memLp_leibnizRemainder_and_lpNorm_le hU hM₁ hM₂ u hTm
  obtain ⟨hE, hEle⟩ := Matrix.memLp_contraction_and_lpNorm_le ha.restrict
    (ae_of_all _ fun x i j => haΛ.abs_apply_le (mem_univ x) i j) hTU
  have hζf : MemLp (fun x => ζ x * f x) p (volume.restrict U) := hζ_top.smul hf
  -- The equation `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ(ζ u) = ζ f + ∑ᵢⱼ aᵢⱼ Tᵢⱼ` and the estimate for `ζ u`.
  have hwp : MemLp (Wkp.iteratedGradient 1 w : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) p
      (volume.restrict U) := (hζH.add hTU).ae_eq (hDw.mono fun _ h => h.symm)
  have hkey := hW0 ha haΛ hosc hUfin w hw0 hwp (hζf.add hE) (by
      filter_upwards [hDw, heq] with x h1 h2
      rw [h1, map_add, map_smul, h2, smul_eq_mul, Pi.add_apply])
  have hsub : lpNorm (fun x => ζ x • Wkp.iteratedGradient 1 u x) p (volume.restrict U) =
      lpNorm (fun x => Wkp.iteratedGradient 1 w x - T x) p (volume.restrict U) :=
    lpNorm_congr_ae (hDw.mono fun x h => by dsimp only; rw [h, add_sub_cancel_right])
  rw [hsub]
  have h1 := lpNorm_sub_le (g := T) hwp Fact.out
  have h2 := lpNorm_add_le (g := fun x => Matrix.contraction (a x) (T x)) hζf Fact.out
  have hC : (0 : ℝ) ≤ C := C.property
  calc _ ≤ _ := h1
    _ ≤ C * (lpNorm (fun x => ζ x * f x) p (volume.restrict U) +
          ((n + 1 : ℕ) : ℝ) ^ 2 * Lam * lpNorm T p (volume.restrict U)) +
          lpNorm T p (volume.restrict U) := by
        gcongr
        exact hkey.trans (mul_le_mul_of_nonneg_left (h2.trans (by gcongr)) hC)
    _ = C * lpNorm (fun x => ζ x * f x) p (volume.restrict U) +
          (C * ((n + 1 : ℕ) : ℝ) ^ 2 * Lam + 1) * lpNorm T p (volume.restrict U) := by ring
    _ ≤ _ := by
        have hΛ : 0 ≤ Lam := haΛ.upper_nonneg
        gcongr

/-- **The localized estimate between concentric balls.** For `0 < s < t ≤ R`, the localized
estimate `exists_lpNorm_smul_iteratedGradient_le`, for the coefficients extended from `B_R` by
`exists_eqOn_ball_and_forall_setAverage_matrixBilinearForm_sub_le` and a cutoff between `B_s` and
`B_t`, bounds `D²u` on `B_s` by `f` and `∇u` on `B_t` and by `u` on `B_R`. -/
private theorem exists_lpNorm_iteratedGradient_ball_le_of_lt (hp : 2 < p) (hp_top : p ≠ ⊤)
    (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ},
        LocallyIntegrable (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume →
        UniformlyEllipticOn (ball x₀ (2 * R)) a lam Lam →
        vmoModulus (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume (16 * R) ≤
          ENNReal.ofReal δ →
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}, ball x₀ R ⊆ Omega →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega p 2)
        {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}, MemLp f p (volume.restrict (ball x₀ R)) →
        (∀ᵐ x ∂(volume.restrict (ball x₀ R)),
          Matrix.contraction (a x) (Wkp.iteratedGradient 1 u x) = f x) →
      ∀ {s t : ℝ}, 0 < s → s < t → t ≤ R →
        lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ s)) ≤
          C * lpNorm f p (volume.restrict (ball x₀ R)) +
            (C * ((n + 1 : ℕ) : ℝ) ^ 2 * Lam + 1) * (c / (t - s) *
              lpNorm (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)) p
                (volume.restrict (ball x₀ t)) +
              c / (t - s) ^ 2 * lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ R))) := by
  obtain ⟨C, δ, hδ, hloc'⟩ := exists_lpNorm_smul_iteratedGradient_le (n := n) hp hp_top lam Lam
  obtain ⟨c, hc0, hcut⟩ :=
    exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ (Fin (n + 1)))
  have hD : (0 : ℝ) < 2 + 20 * 8 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by positivity
  refine ⟨C, δ / (2 + 20 * 8 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))), div_pos hδ hD, 4 * c,
    by positivity, fun {a x₀ R} hloc hell hη {Omega} hR u f hf heq s t hs hst htR => ?_⟩
  obtain ⟨a', ha'm, ha'Λ, ha'a, ha'osc⟩ :=
    exists_eqOn_ball_and_forall_setAverage_matrixBilinearForm_sub_le (div_pos hδ hD).le
      (hs.trans (hst.trans_le htR)) hloc hell hη
  obtain ⟨ζ, hζ, hζr, hζ1, hζts, hζg, hζh⟩ := hcut x₀ hs.le (show s < (s + t) / 2 by linarith)
  have hζc : HasCompactSupport ζ :=
    (isCompact_closedBall x₀ _).of_isClosed_subset (isClosed_tsupport ζ) hζts
  set U : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ t, isOpen_ball⟩
  have hUR : (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball x₀ R := ball_subset_ball htR
  have hres : volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≤
      volume.restrict (ball x₀ R) := Measure.restrict_mono hUR le_rfl
  have key := hloc' ha'm ha'Λ (fun c r hr => (ha'osc c r hr).imp fun A hA =>
      ⟨hA.1, hA.2.trans_eq (by field_simp)⟩) (Omega := Omega) (U := U)
    (fun x hx => hR (hUR hx)) measure_ball_lt_top.ne hζ hζc
    (hζts.trans (closedBall_subset_ball (by linarith))) hζg hζh u (hf.mono_measure hres) (by
      filter_upwards [ae_restrict_mem (measurableSet_ball (x := x₀) (ε := t)),
        ae_restrict_of_ae_restrict_of_subset hUR heq] with x hx h
      rw [ha'a (hUR hx)]
      exact h)
  -- `ζ = 1` on `B_s`, `|ζ| ≤ 1`, and `B_t ⊆ B_R`.
  have hlow : lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ s)) ≤
      lpNorm (fun x => ζ x • Wkp.iteratedGradient 1 u x) p (volume.restrict U) := by
    have hae : (Wkp.iteratedGradient 1 u : EuclideanSpace ℝ (Fin (n + 1)) → _)
        =ᵐ[volume.restrict (ball x₀ s)] fun x => ζ x • Wkp.iteratedGradient 1 u x := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      rw [hζ1 (ball_subset_closedBall hx), Pi.one_apply, one_smul]
    rw [lpNorm_congr_ae hae]
    refine lpNorm_mono_measure ?_ (Measure.restrict_mono (ball_subset_ball hst.le) le_rfl)
    exact (hζ.continuous.memLp_top_of_hasCompactSupport hζc _).smul
      ((Lp.memLp _).mono_measure (Measure.restrict_mono (hUR.trans hR) le_rfl))
  have hΛ : 0 ≤ Lam := hell.upper_nonneg
  have hm : (s + t) / 2 - s = (t - s) / 2 := by ring
  have hts : t - s ≠ 0 := sub_ne_zero.2 hst.ne'
  rw [show 2 * (c / ((s + t) / 2 - s)) = 4 * c / (t - s) by rw [hm]; field_simp; ring,
    show c / ((s + t) / 2 - s) ^ 2 = 4 * c / (t - s) ^ 2 by rw [hm]; field_simp; ring] at key
  refine hlow.trans (key.trans ?_)
  gcongr
  · refine (lpNorm_smul_le_mul_lpNorm_of_ae_le (ψ := ζ) (hf.mono_measure hres) (c := 1)
      (ae_of_all _ fun x => ?_)).trans ?_
    · rw [Real.norm_eq_abs]
      exact abs_le.2 ⟨by linarith [(hζr ⟨x, rfl⟩).1], (hζr ⟨x, rfl⟩).2⟩
    · rw [one_mul]
      exact lpNorm_mono_measure hf hres
  · exact le_rfl
  · exact lpNorm_mono_measure ((Lp.memLp _).mono_measure (Measure.restrict_mono hR le_rfl)) hres

/-- The bookkeeping of constants in
`TauCeti.PDE.exists_mul_lpNorm_iteratedGradient_ball_le_of_vmoModulus_le`. -/
private theorem add_mul_le_mul_add {C C₂ K R X Z : ℝ} (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (hX : 0 ≤ X)
    (hZ : 0 ≤ Z) :
    2 * (R ^ 2 * (C * X)) + C₂ * K ^ 2 * Z ≤ (2 * C + C₂ * K ^ 2) * (R ^ 2 * X + Z) := by
  have h : 0 ≤ 2 * C * Z + C₂ * K ^ 2 * (R ^ 2 * X) := by positivity
  linarith [show (2 * C + C₂ * K ^ 2) * (R ^ 2 * X + Z) =
    2 * (R ^ 2 * (C * X)) + C₂ * K ^ 2 * Z + (2 * C * Z + C₂ * K ^ 2 * (R ^ 2 * X)) by ring]

/-- **The interior Calderón–Zygmund estimate for coefficients of vanishing mean oscillation.**
Let `2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`,
`λ` and `Λ`, with the following property. Let `a` be a coefficient matrix on `ℝ^{n+1}`, neither
symmetric nor continuous in general, whose operators `a(x)` are locally integrable, uniformly
elliptic with the constants `λ, Λ` on `B(x₀, 2 R)`, and of VMO modulus `η_a(16 R) ≤ δ`: on every
ball of radius at most `16 R`, `a` deviates in mean from its average by at most `δ` in operator
norm. Let `r < R` with `B(x₀, R) ⊆ Ω`. Then every `u ∈ W^{2,p}(Ω)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost
everywhere on `B_R = B(x₀, R)` satisfies

`(R - r)² ‖D²u‖_{Lᵖ(B_r)} ≤ C (R² ‖f‖_{Lᵖ(B_R)} + ‖u‖_{Lᵖ(B_R)})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. No boundary condition on `u`
is imposed, and `f` is not assumed to be in `Lᵖ`: the equation and the bound on `a` force it. For
coefficients of vanishing mean oscillation the smallness holds below a radius `r₀` depending on
`a`, see `TauCeti.PDE.exists_lpNorm_iteratedGradient_ball_le_of_memVMO`. -/
theorem exists_mul_lpNorm_iteratedGradient_ball_le_of_vmoModulus_le (hp : 2 < p)
    (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ},
        LocallyIntegrable (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume →
        UniformlyEllipticOn (ball x₀ (2 * R)) a lam Lam →
        vmoModulus (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume (16 * R) ≤
          ENNReal.ofReal δ →
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}, ball x₀ R ⊆ Omega →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega p 2)
        (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
        (∀ᵐ x ∂(volume.restrict (ball x₀ R)),
          ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
            EuclideanSpace.single j 1⟫_ℝ = f x) →
      ∀ {r : ℝ}, r < R →
        (R - r) ^ 2 * lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ r)) ≤
          C * (R ^ 2 * lpNorm f p (volume.restrict (ball x₀ R)) +
            lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ R))) := by
  obtain ⟨C, δ, hδ, cA, hcA, hstep⟩ :=
    exists_lpNorm_iteratedGradient_ball_le_of_lt (n := n) hp hp_top lam Lam
  obtain ⟨cB, hcB, hinterp⟩ :=
    Wkp.exists_lpNorm_gradient_ball_le (E := EuclideanSpace ℝ (Fin (n + 1))) (mu := volume) hp_top
  set N : ℝ := ((n + 1 : ℕ) : ℝ) ^ 2 with hN
  set K : ℝ := C * N * max Lam 0 + 1 with hK
  set C₂ : ℝ := 8 * cA + 256 * cA ^ 2 * N + 16 * cA * N * (4 * cB + 1) with hC₂def
  refine ⟨Real.toNNReal (2 * C + C₂ * K ^ 2), δ, hδ,
    fun {a x₀ R} hloc hell hη {Omega} hR u f heq {r} hrR => ?_⟩
  have hK1 : 1 ≤ K := le_add_of_nonneg_left (by rw [hN]; positivity)
  have hC₂ : 0 ≤ C₂ := by
    rw [hC₂def, hN]
    positivity
  have hKΛ : C * N * Lam + 1 = K := by rw [hK, max_eq_left hell.upper_nonneg]
  have hCfin : ((2 * C + C₂ * K ^ 2).toNNReal : ℝ) = 2 * C + C₂ * K ^ 2 :=
    Real.coe_toNNReal _ (add_nonneg (by positivity) (mul_nonneg hC₂ (sq_nonneg K)))
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, Measure.restrict_empty, lpNorm_measure_zero, mul_zero, hCfin]
    exact mul_nonneg (add_nonneg (by positivity) (mul_nonneg hC₂ (sq_nonneg K)))
      (add_nonneg (mul_nonneg (sq_nonneg R) lpNorm_nonneg) lpNorm_nonneg)
  -- The right side `f` is the contraction of `a` with `D²u`, hence in `Lᵖ(B_R)`.
  have hRΩ : volume.restrict (ball x₀ R) ≤ volume.restrict (Omega : Set _) :=
    Measure.restrict_mono hR le_rfl
  have hf : MemLp f p (volume.restrict (ball x₀ R)) := memLp_of_ae_sum_mul_inner_eq
    measurableSet_ball hR u
    (Matrix.aestronglyMeasurable_toEuclideanCLM_iff.1 hloc.aestronglyMeasurable).restrict
    (ae_of_all _ fun x hx i j => hell.abs_apply_le (ball_subset_ball (by linarith) hx) i j) heq
  have hmono : ∀ {E' : Type} [NormedAddCommGroup E']
      (w : Lp E' p (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) {σ : ℝ},
      σ ≤ R → lpNorm w p (volume.restrict (ball x₀ σ)) ≤ lpNorm w p (volume.restrict (ball x₀ R)) :=
    fun w σ hσ => lpNorm_mono_measure ((Lp.memLp w).mono_measure hRΩ)
      (Measure.restrict_mono (ball_subset_ball hσ) le_rfl)
  have hΦ := sq_mul_le_of_forall_le (k := fun σ => lpNorm (Wkp.iteratedGradient 1 u) p
      (volume.restrict (ball x₀ σ))) (h := fun σ => lpNorm (Wkp.iteratedGradient 0
        (Wkp.lowerOrder 1 u)) p (volume.restrict (ball x₀ σ)))
    (y := fun σ => lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ σ))) (hr.trans hrR)
    (mul_nonneg C.property lpNorm_nonneg) hK1 hcA hcB
    (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2) (fun _ => lpNorm_nonneg)
    (fun _ => lpNorm_nonneg)
    (fun σ hσ => hmono _ hσ.2.le) (fun σ hσ => hmono _ hσ.2.le) (fun σ hσ => hmono _ hσ.2.le)
    (fun {s t} hs hst htR => by
      have h := hstep hloc hell hη hR u hf
        (heq.mono fun x hx => by rw [Matrix.contraction_apply, hx]) hs hst htR
      rwa [hKΛ] at h)
    (fun {s t} hs hst htR {ε} hε => by
      simpa only [finrank_euclideanSpace_fin] using
        hinterp u hs hst ((ball_subset_ball htR).trans hR) hε)
    hr hrR
  rw [hCfin]
  exact hΦ.trans (add_mul_le_mul_add C.property hC₂ lpNorm_nonneg lpNorm_nonneg)

/-- **The interior Calderón–Zygmund estimate for coefficients of vanishing mean oscillation, below
a radius `r₀`.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There is a constant `C`, depending only on `n`,
`p`, `λ` and `Λ`, with the following property. Let `a` be a coefficient matrix on `ℝ^{n+1}`,
uniformly elliptic with the constants `λ, Λ`, whose operators `a(x)` have vanishing mean
oscillation. Then there is a radius `r₀ > 0` such that for every ball `B_R = B(x₀, R) ⊆ Ω` with
`R ≤ r₀`, every `u ∈ W^{2,p}(Ω)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `B_R` satisfies

`‖D²u‖_{Lᵖ(B_{R/2})} ≤ C (‖f‖_{Lᵖ(B_R)} + R⁻² ‖u‖_{Lᵖ(B_R)})`.

For the explicit dependence of the admissible radii on the VMO modulus of `a`, see
`TauCeti.PDE.exists_mul_lpNorm_iteratedGradient_ball_le_of_vmoModulus_le`. -/
theorem exists_lpNorm_iteratedGradient_ball_le_of_memVMO (hp : 2 < p) (hp_top : p ≠ ⊤)
    (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      MemVMO (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume →
      UniformlyEllipticOn univ a lam Lam →
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}, R ≤ r₀ →
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}, ball x₀ R ⊆ Omega →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega p 2)
        (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
        (∀ᵐ x ∂(volume.restrict (ball x₀ R)),
          ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
            EuclideanSpace.single j 1⟫_ℝ = f x) →
        lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ (R / 2))) ≤
          C * (lpNorm f p (volume.restrict (ball x₀ R)) +
            (R ^ 2)⁻¹ * lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ R))) := by
  obtain ⟨C, δ, hδ, hmain⟩ :=
    exists_mul_lpNorm_iteratedGradient_ball_le_of_vmoModulus_le (n := n) hp hp_top lam Lam
  refine ⟨4 * C, fun {a} hvmo hell => ?_⟩
  obtain ⟨hbmo, hlim⟩ := memVMO_iff_tendsto.1 hvmo
  -- The VMO modulus is below `δ` on `(0, r₁)`.
  obtain ⟨r₁, hr₁, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ)))
  have hr₁' : 0 < r₁ := hr₁
  refine ⟨r₁ / 32, by positivity, fun {x₀ R} hRr {Omega} hR u f heq => ?_⟩
  rcases le_or_gt R 0 with hR0 | hR0
  · rw [ball_eq_empty.2 (by linarith), Measure.restrict_empty, lpNorm_measure_zero]
    exact mul_nonneg (4 * C).property (add_nonneg lpNorm_nonneg
      (mul_nonneg (inv_nonneg.2 (sq_nonneg R)) lpNorm_nonneg))
  have hη : vmoModulus (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume (16 * R) ≤
      ENNReal.ofReal δ := (hsub ⟨by positivity, by linarith⟩).le
  have h := hmain hbmo.locallyIntegrable (hell.mono_set (subset_univ _)) hη hR u f heq
    (show R / 2 < R by linarith)
  rw [show R - R / 2 = R / 2 by ring] at h
  calc lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ (R / 2)))
      = 4 / R ^ 2 * ((R / 2) ^ 2 *
          lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ (R / 2)))) := by
        field_simp
        ring
    _ ≤ 4 / R ^ 2 * (C * (R ^ 2 * lpNorm f p (volume.restrict (ball x₀ R)) +
          lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ R)))) := by gcongr
    _ = _ := by
        push_cast
        field_simp

/-! ### The estimate on the whole space -/

/-- **The Calderón–Zygmund estimate in `W^{2,p}(ℝ^{n+1})` for coefficients of vanishing mean
oscillation.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There is a constant `C`, depending only on `n`,
`p`, `λ` and `Λ`, with the following property. Let `a` be a coefficient matrix on `ℝ^{n+1}`,
uniformly elliptic with the constants `λ, Λ`, whose operators `a(x)` have vanishing mean
oscillation. Then there is a radius `r₀ > 0` such that every `u ∈ W^{2,p}(ℝ^{n+1})` with
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f ∈ Lᵖ(ℝ^{n+1})` almost everywhere satisfies

`‖D²u‖_{Lᵖ} ≤ C (‖f‖_{Lᵖ} + r₀⁻² ‖u‖_{Lᵖ})`.

The radius `r₀` is that of the interior estimate
`TauCeti.PDE.exists_lpNorm_iteratedGradient_ball_le_of_memVMO`. -/
theorem exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_memVMO (hp : 2 < p)
    (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      MemVMO (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume →
      UniformlyEllipticOn univ a lam Lam →
      ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))))),
        (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ = f x) →
        ‖Wkp.iteratedGradient 1 u‖ ≤ C * (‖f‖ + (r₀ ^ 2)⁻¹ * ‖Wkp.value 2 u‖) := by
  obtain ⟨C, hC⟩ := exists_lpNorm_iteratedGradient_ball_le_of_memVMO (n := n) hp hp_top lam Lam
  refine ⟨2 ^ (n + 2) * C, fun {a} hvmo hell => ?_⟩
  obtain ⟨r₀, hr₀, hloc⟩ := hC hvmo hell
  refine ⟨r₀, hr₀, fun u f heq => ?_⟩
  -- The interior estimate on `B(y, r₀)`, at every centre `y`.
  have hlocal : ∀ y, lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball y (r₀ / 2))) ≤
      C * lpNorm f p (volume.restrict (ball y (2 * (r₀ / 2)))) +
        C * (r₀ ^ 2)⁻¹ * lpNorm (Wkp.value 2 u) p (volume.restrict (ball y (2 * (r₀ / 2)))) :=
    fun y => by
      rw [show 2 * (r₀ / 2) = r₀ by ring, mul_assoc, ← mul_add]
      exact hloc le_rfl (fun x _ => trivial) u f (ae_restrict_of_ae heq)
  have hglobal := lpNorm_le_of_ae_lpNorm_restrict_ball_le_add (Fact.out : 1 ≤ p) hp_top
    (Lp.memLp_of_restrict_coe_opens_top _) (Lp.memLp_of_restrict_coe_opens_top f)
    (Lp.memLp_of_restrict_coe_opens_top _) C.coe_nonneg (by positivity) (half_pos hr₀)
    (Filter.Eventually.of_forall hlocal)
  rw [finrank_euclideanSpace_fin, ← Lp.norm_eq_lpNorm_of_restrict_coe_opens_top,
    ← Lp.norm_eq_lpNorm_of_restrict_coe_opens_top,
    ← Lp.norm_eq_lpNorm_of_restrict_coe_opens_top] at hglobal
  refine hglobal.trans_eq ?_
  push_cast
  ring

/-- **Moving bounded lower-order terms to the right side.** If `b` and `c` are measurable with
`‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere, and `u ∈ W^{2,p}(ℝ^{n+1})` solves
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ` almost everywhere, then `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = g` for some
`g ∈ Lᵖ` with `‖g‖ ≤ ‖f‖ + β ‖∇u‖ + γ ‖u‖`. -/
private theorem exists_sum_mul_inner_eq_and_norm_le_of_sum_mul_inner_add_inner_add_mul_eq
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {β γ : ℝ} (hb : AEStronglyMeasurable b volume)
    (hbβ : ∀ᵐ x, ‖b x‖ ≤ β) (hc : AEStronglyMeasurable c volume) (hcγ : ∀ᵐ x, |c x| ≤ γ)
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2)
    (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
      (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))))
    (heq : ∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
        EuclideanSpace.single j 1⟫_ℝ +
      ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c x * Wkp.value 2 u x = f x) :
    ∃ g : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
        (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))),
      (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
        EuclideanSpace.single j 1⟫_ℝ = g x) ∧
      ‖g‖ ≤ ‖f‖ + β * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + γ * ‖Wkp.value 2 u‖ := by
  set v := Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)
  have hbv : ∀ᵐ x, ‖⟪b x, v x⟫_ℝ‖ ≤ β * ‖v x‖ := by
    filter_upwards [hbβ] with x hx
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hcu : ∀ᵐ x, ‖c x * Wkp.value 2 u x‖ ≤ γ * ‖Wkp.value 2 u x‖ := by
    filter_upwards [hcγ] with x hx
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  -- The lower-order terms are `Lᵖ` functions.
  have hB : MemLp (fun x => ⟪b x, v x⟫_ℝ) p ((volume : Measure (EuclideanSpace ℝ
      (Fin (n + 1)))).restrict (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (Lp.memLp v).of_le_mul (hb.restrict.inner (Lp.aestronglyMeasurable v)) (ae_restrict_of_ae hbv)
  have hCu : MemLp (fun x => c x * Wkp.value 2 u x) p ((volume : Measure (EuclideanSpace ℝ
      (Fin (n + 1)))).restrict (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (Lp.memLp (Wkp.value 2 u)).of_le_mul (hc.restrict.mul (Lp.aestronglyMeasurable _))
      (ae_restrict_of_ae hcu)
  refine ⟨f - hB.toLp _ - hCu.toLp _, ?_, ?_⟩
  · -- Almost everywhere statements for `volume` restricted to `⊤` hold for `volume`.
    refine Filter.Eventually.filter_mono Measure.ae_le_ae_restrict_coe_opens_top ?_
    filter_upwards [Lp.coeFn_sub (f - hB.toLp _) (hCu.toLp _), Lp.coeFn_sub f (hB.toLp _),
      hB.coeFn_toLp, hCu.coeFn_toLp, ae_restrict_of_ae heq] with x h₁ h₂ h₃ h₄ hx
    rw [h₁, Pi.sub_apply, h₂, Pi.sub_apply, h₃, h₄, ← hx]
    ring
  · have h₁ : ‖hB.toLp _‖ ≤ β * ‖v‖ := Lp.norm_le_mul_norm_of_ae_le_mul <| by
      filter_upwards [hB.coeFn_toLp, ae_restrict_of_ae hbv] with x hx hxb
      rwa [hx]
    have h₂ : ‖hCu.toLp _‖ ≤ γ * ‖Wkp.value 2 u‖ := Lp.norm_le_mul_norm_of_ae_le_mul <| by
      filter_upwards [hCu.coeFn_toLp, ae_restrict_of_ae hcu] with x hx hxc
      rwa [hx]
    calc ‖f - hB.toLp _ - hCu.toLp _‖ ≤ ‖f‖ + ‖hB.toLp _‖ + ‖hCu.toLp _‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ _ := by gcongr

/-- **The Calderón–Zygmund estimate in `W^{2,p}(ℝ^{n+1})` for coefficients of vanishing mean
oscillation, with lower-order terms.** Let `2 < p < ∞`, let `a` be a coefficient matrix on
`ℝ^{n+1}`, uniformly elliptic with constants `λ, Λ`, whose operators `a(x)` have vanishing mean
oscillation, and let `b`, `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere. Then
there is a constant `C` such that every `u ∈ W^{2,p}(ℝ^{n+1})` with
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ(ℝ^{n+1})` almost everywhere satisfies

`‖D²u‖_{Lᵖ} ≤ C (‖f‖_{Lᵖ} + ‖u‖_{Lᵖ})`.

The constant `C` depends on `n`, `p`, `λ`, `Λ`, `β`, `γ`, and on `a` through the radius `r₀` of
`TauCeti.PDE.exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_memVMO`. -/
theorem exists_norm_iteratedGradient_le_of_sum_mul_inner_add_inner_add_mul_eq_of_memVMO
    (hp : 2 < p) (hp_top : p ≠ ⊤) {lam Lam : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hvmo : MemVMO (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (a x)) volume)
    (hell : UniformlyEllipticOn univ a lam Lam)
    {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {β γ : ℝ} (hb : AEStronglyMeasurable b volume)
    (hbβ : ∀ᵐ x, ‖b x‖ ≤ β) (hc : AEStronglyMeasurable c volume) (hcγ : ∀ᵐ x, |c x| ≤ γ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ⊤ p 2)
      (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
        (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))))),
      (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ +
        ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ + c x * Wkp.value 2 u x = f x) →
      ‖Wkp.iteratedGradient 1 u‖ ≤ C * (‖f‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C, hC⟩ :=
    exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_memVMO (n := n) hp hp_top lam Lam
  obtain ⟨r₀, -, hest⟩ := hC hvmo hell
  set β' := max β 0
  set γ' := max γ 0
  have hβ' : 0 ≤ β' := le_max_right _ _
  -- The step of the interpolation inequality, chosen so that `C β' ε ≤ 1 / 2`.
  set ε := (2 * C * β' + 1)⁻¹ with hε_def
  have hε : 0 < ε := by positivity
  have hCε : (C : ℝ) * β' * ε ≤ 1 / 2 := by
    rw [hε_def, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith [mul_nonneg C.coe_nonneg hβ']
  set K := β' * (((n + 1 : ℕ) : ℝ) ^ 2 / ε) + γ' + (r₀ ^ 2)⁻¹
  have hK : 0 ≤ K := by positivity
  refine ⟨2 * C * (1 + K), fun u f heq => ?_⟩
  -- Move the lower-order terms to the right side; the gradient term is absorbed below by the
  -- interpolation inequality.
  obtain ⟨g, hg, hgf⟩ := exists_sum_mul_inner_eq_and_norm_le_of_sum_mul_inner_add_inner_add_mul_eq
    hb (hbβ.mono fun _ hx => hx.trans (le_max_left _ _)) hc
    (hcγ.mono fun _ hx => hx.trans (le_max_left _ _)) u f heq
  have hinterp := Wkp.norm_iteratedGradient_lowerOrder_le hp_top u hε
  rw [finrank_euclideanSpace_fin] at hinterp
  -- Absorb the gradient term.
  set D := ‖Wkp.iteratedGradient 1 u‖
  set U := ‖Wkp.value 2 u‖
  have hU : 0 ≤ U := norm_nonneg _
  have hf : 0 ≤ ‖f‖ := norm_nonneg _
  have hCK : (C : ℝ) * (β' * (ε * D)) ≤ D / 2 := by
    have := mul_le_mul_of_nonneg_right hCε (norm_nonneg (Wkp.iteratedGradient 1 u))
    linarith
  have hD : D ≤ (C : ℝ) * (‖f‖ + K * U) + D / 2 := by
    calc D ≤ C * (‖g‖ + (r₀ ^ 2)⁻¹ * U) := hest u g hg
      _ ≤ C * ((‖f‖ + β' * (ε * D + ((n + 1 : ℕ) : ℝ) ^ 2 / ε * U) + γ' * U) +
          (r₀ ^ 2)⁻¹ * U) := by gcongr; exact hgf.trans (by gcongr)
      _ = C * (‖f‖ + K * U) + C * (β' * (ε * D)) := by ring
      _ ≤ _ := by gcongr
  calc D ≤ 2 * C * (‖f‖ + K * U) := by linarith
    _ ≤ 2 * C * (1 + K) * (‖f‖ + U) := by
      rw [mul_assoc (2 * (C : ℝ))]
      gcongr
      nlinarith

end Estimate

end PDE

end TauCeti
