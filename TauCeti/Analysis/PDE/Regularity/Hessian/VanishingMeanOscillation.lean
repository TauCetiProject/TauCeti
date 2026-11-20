/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.SmallMeanOscillation
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Cutoff
import Mathlib.Analysis.Convex.Integral
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Matrix.Contraction.LpNorm
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable
import TauCeti.Analysis.SpecificLimits.Absorption
import TauCeti.Analysis.Sobolev.Wkp.Interpolation
import TauCeti.Analysis.PDE.Regularity.Hessian.Interior
import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import TauCeti.Analysis.Sobolev.Wkp.Extension
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure

/-!
# The interior `W^{2,p}` estimate for coefficients of vanishing mean oscillation

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
the whole-space estimate for coefficients of small mean oscillation; the principal part alone is
treated.

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
  set e := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
  have he (M : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) : e (e.symm M) = M :=
    e.apply_symm_apply M
  refine ⟨fun x => e.symm (β x),
    Matrix.aestronglyMeasurable_toEuclideanCLM_iff.1
      (hβloc.aestronglyMeasurable.congr (ae_of_all _ fun x => (he (β x)).symm)),
    uniformlyEllipticOn_of_forall_toEuclideanCLM_mem hell.pos hell.le fun x _ => by
      rw [he]
      exact hβK x, fun x hx => ?_, fun c r hr => ?_⟩
  · simp only [hβb hx, e.symm_apply_apply]
  -- On a ball, freeze at the average `κ` of `β`, which is elliptic.
  have hβB : IntegrableOn β (ball c r) volume :=
    (hβloc.integrableOn_isCompact (isCompact_closedBall c r)).mono_set ball_subset_closedBall
  set κ := ⨍ y in ball c r, β y
  have hκ : κ ∈ ellipticCLMSet lam Lam := Convex.set_average_mem (convex_ellipticCLMSet lam Lam)
    (isClosed_ellipticCLMSet lam Lam) (measure_ball_pos volume c hr).ne' measure_ball_lt_top.ne
    (ae_of_all _ hβK) hβB
  refine ⟨e.symm κ, uniformlyEllipticOn_of_forall_toEuclideanCLM_mem hell.pos hell.le
    fun _ _ => by rwa [he], ?_⟩
  have hint : IntegrableOn (fun x => β x - κ) (ball c r) volume :=
    hβB.sub (integrableOn_const measure_ball_lt_top.ne)
  -- The mean oscillation of `β` on the ball is at most its BMO seminorm.
  have hle := (setLAverage_enorm_sub_setAverage_le_bmoSeminorm β volume c r).trans
    (hbmo.trans (mul_le_mul_of_nonneg_left hη zero_le))
  have hD : (2 + 20 * 8 ^ finrank ℝ (EuclideanSpace ℝ ι) : ℝ≥0∞) * ENNReal.ofReal δ =
      ENNReal.ofReal ((2 + 20 * 8 ^ finrank ℝ (EuclideanSpace ℝ ι)) * δ) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    norm_cast
  rw [setLAverage_enorm_eq_ofReal_setAverage_norm hint, hD,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have heq (x : EuclideanSpace ℝ ι) :
      ‖matrixBilinearForm (e.symm (β x)) - matrixBilinearForm (e.symm κ)‖ = ‖β x - κ‖ := by
    rw [← matrixBilinearForm_sub, norm_matrixBilinearForm_eq_norm_toEuclideanCLM, map_sub, he, he]
  simpa only [heq] using hle

end Coefficient

section Estimate

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

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
    exists_eLpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_setAverage_le (n := n) hp hp_top
      lam Lam
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
  have hkey := hCZ ha (fun x => haΛ.opNorm_matrixBilinearForm_le (mem_univ x)) hosc W _ hWeq
    (((integrable_indicator_iff hUm).2 (hwp.integrable Fact.out)).congr
      (hW.mono fun _ h => h.symm))
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

end Estimate

end PDE

end TauCeti
