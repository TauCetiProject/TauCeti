/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Subcritical
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# The bottom of the spectrum of the conformal Laplacian

Let `(M, g)` be a closed smooth Riemannian manifold of dimension `n > 2`, with conformal Laplacian
`L_g = aₙ Δ⁺_g + Scal_g` and weak energy form `E_g(w, w) = aₙ ∫ |∇w|² dV + ∫ Scal_g w² dV` on
`H¹(M)` (`TauCeti.Yamabe.energyForm`). At the exponent `q = 2` the subcritical Yamabe quotient is
the **Rayleigh quotient** of `L_g`,

`Q²(w) = E_g(w, w) / ‖w‖²_{L²}` (`TauCeti.Yamabe.subcriticalYamabeQuotient_two`),

and its infimum over nonzero `w ∈ H¹(M)`,

`λ₁(L_g) = sInf (subcriticalYamabeQuotient I 2 '' {w | w ≠ 0})`,

is the variational form of the first eigenvalue of `L_g`. This file develops the properties of
`λ₁(L_g)` that need no compactness:

* **The Rayleigh inequality** `λ₁ ‖w‖²_{L²} ≤ E_g(w, w)` for every `w ∈ H¹(M)`
  (`sInf_subcriticalYamabeQuotient_two_mul_le_energyForm`).
* **Minimizers are weak eigenfunctions.** If `E_g(w, w) = λ₁ ‖w‖²_{L²}`, then
  `E_g(w, v) = λ₁ ⟪w, v⟫_{L²}` for every `v ∈ H¹(M)`
  (`energyForm_eq_sInf_subcriticalYamabeQuotient_two_mul_inner`): the quadratic
  `t ↦ E_g(w + t v, w + t v) - λ₁ ‖w + t v‖²_{L²}` is nonnegative and vanishes at `t = 0`.
* **The mean scalar curvature bounds `λ₁`.** On a nonempty `M`, testing with the constant function
  gives `λ₁ ≤ ∫ Scal_g dV / Vol(M, g)`
  (`sInf_subcriticalYamabeQuotient_two_le_integral_scalarCurvature_div`), with equality exactly when
  `Scal_g` is constant (`sInf_subcriticalYamabeQuotient_two_eq_integral_scalarCurvature_div_iff`).
  In the equality case the constant function is a minimizer, hence a weak eigenfunction, and
  `L_g 1 = Scal_g`.
* **Positive eigenfunctions.** If a smooth positive `u` solves `L_g u = c u`, then `c = λ₁`
  (`sInf_subcriticalYamabeQuotient_two_eq_of_conformalLaplacian_eq_mul`). Writing a smooth `φ` as
  `u v`, the pointwise identity `|∇(u v)|² = ⟪∇(u v²), ∇u⟫ + u² |∇v|²` gives
  `E_g(φ, φ) ≥ E_g(u v², u) = c ‖φ‖²_{L²}`, and density of smooth functions extends this to
  `H¹(M)`.
* **The sign of the Yamabe invariant.** The Yamabe invariant `Y = inf {Q_g(w) | w ≠ 0}` has the
  sign of `λ₁(L_g)` (`sign_sInf_weakYamabeQuotient_eq`), by
  `TauCeti.Yamabe.sign_sInf_subcriticalYamabeQuotient_eq` at the exponents `pₙ` and `2`.

That the infimum `λ₁(L_g)` is attained, by a positive smooth eigenfunction, needs the compactness of
`H¹(M) → L²(M)` and elliptic regularity, and is not proved here.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91.
* L. C. Evans, *Partial Differential Equations*, Section 6.5.1 (the variational principle for the
  principal eigenvalue).
-/

public section

open Bundle MeasureTheory Module Set TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Yamabe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [I.Boundaryless] in
/-- **The Rayleigh quotient of the conformal Laplacian.** At the exponent `2`, the subcritical
Yamabe quotient of `w ∈ H¹(M)` is `E_g(w, w) / ‖w‖²_{L²}`. -/
theorem subcriticalYamabeQuotient_two (w : SobolevH1 I M) :
    subcriticalYamabeQuotient I 2 w = energyForm I w w / ‖SobolevH1.toLp w‖ ^ 2 := by
  rw [subcriticalYamabeQuotient_def, div_self two_ne_zero, Real.rpow_one]
  simpa only [Real.norm_eq_abs, Real.rpow_two] using
    congrArg (energyForm I w w / ·) (Lp.integral_norm_sq_eq_norm_sq (SobolevH1.toLp w))

/-- A nonzero `w ∈ H¹(M)` has positive `L²` norm. -/
private theorem norm_toLp_sq_pos {w : SobolevH1 I M} (hw : w ≠ 0) : 0 < ‖SobolevH1.toLp w‖ ^ 2 :=
  pow_pos (norm_pos_iff.2 fun h ↦ hw (SobolevH1.toLp_injective (h.trans (map_zero _).symm))) 2

/-- **The Rayleigh inequality.** On a closed manifold of dimension `n > 2`, the infimum `λ₁` of the
Rayleigh quotient of the conformal Laplacian satisfies `λ₁ ‖w‖²_{L²} ≤ E_g(w, w)` for every
`w ∈ H¹(M)`. -/
theorem sInf_subcriticalYamabeQuotient_two_mul_le_energyForm (hn : 2 < finrank ℝ E)
    (w : SobolevH1 I M) :
    sInf (subcriticalYamabeQuotient I 2 '' {w : SobolevH1 I M | w ≠ 0}) *
        ‖SobolevH1.toLp w‖ ^ 2 ≤ energyForm I w w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [← le_div_iff₀ (norm_toLp_sq_pos hw), ← subcriticalYamabeQuotient_two]
  exact csInf_le (bddBelow_image_subcriticalYamabeQuotient le_rfl (two_lt_criticalExponent hn).le)
    ⟨w, hw, rfl⟩

/-- **Rayleigh minimizers are weak eigenfunctions.** On a closed manifold of dimension `n > 2`, if
`w ∈ H¹(M)` attains the infimum `λ₁` of the Rayleigh quotient of the conformal Laplacian, in the
sense that `E_g(w, w) = λ₁ ‖w‖²_{L²}`, then `E_g(w, v) = λ₁ ⟪w, v⟫_{L²}` for every `v ∈ H¹(M)`:
`w` is a weak solution of `L_g w = λ₁ w`. -/
theorem energyForm_eq_sInf_subcriticalYamabeQuotient_two_mul_inner (hn : 2 < finrank ℝ E)
    {w : SobolevH1 I M}
    (hw : energyForm I w w =
      sInf (subcriticalYamabeQuotient I 2 '' {w : SobolevH1 I M | w ≠ 0}) *
        ‖SobolevH1.toLp w‖ ^ 2)
    (v : SobolevH1 I M) :
    energyForm I w v =
      sInf (subcriticalYamabeQuotient I 2 '' {w : SobolevH1 I M | w ≠ 0}) *
        inner ℝ (SobolevH1.toLp w) (SobolevH1.toLp v) := by
  set l := sInf (subcriticalYamabeQuotient I 2 '' {w : SobolevH1 I M | w ≠ 0})
  set a := energyForm I v v - l * ‖SobolevH1.toLp v‖ ^ 2
  set b := 2 * (energyForm I w v - l * inner ℝ (SobolevH1.toLp w) (SobolevH1.toLp v))
  -- The Rayleigh inequality along the line `w + t v` is a nonnegative quadratic in `t` that
  -- vanishes at `t = 0`, so its linear coefficient vanishes.
  have hquad (t : ℝ) : 0 ≤ a * (t * t) + b * t + 0 := by
    have h := sInf_subcriticalYamabeQuotient_two_mul_le_energyForm hn (w + t • v)
    rw [← real_inner_self_eq_norm_sq] at h hw
    simp only [a, b, ← real_inner_self_eq_norm_sq, map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (SobolevH1.toLp v), energyForm_comm v w] at h ⊢
    nlinarith [h, hw]
  have hb : b = 0 := by
    have h := discrim_le_zero hquad
    rw [discrim, mul_zero, sub_zero] at h
    exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h (sq_nonneg b))
  simp only [b, mul_eq_zero, two_ne_zero, false_or, sub_eq_zero] at hb
  exact hb

omit [I.Boundaryless] in
/-- The weak energy of the constant function `1` is the total scalar curvature. -/
private theorem energyForm_ofSmooth_one_self :
    energyForm I (SobolevH1.ofSmooth (1 : C^∞⟮I, M; ℝ⟯)) (SobolevH1.ofSmooth 1) =
      ∫ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x
        ∂riemannianVolume I M := by
  rw [energyForm_ofSmooth_self]
  simp [ContMDiffMap.coe_one, Pi.one_def, mgradient_const]

omit [I.Boundaryless] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The squared `L²` norm of the constant function `1` is the total volume. -/
private theorem norm_toLp_ofSmooth_one_sq :
    ‖SobolevH1.toLp (SobolevH1.ofSmooth (1 : C^∞⟮I, M; ℝ⟯))‖ ^ 2 = riemannianTotalVolume I M := by
  rw [← real_inner_self_eq_norm_sq, SobolevH1.inner_toLp_ofSmooth]
  simp [riemannianTotalVolume_def]

/-- **The mean scalar curvature bounds the bottom of the spectrum.** On a nonempty closed manifold
of dimension `n > 2`, the infimum `λ₁` of the Rayleigh quotient of the conformal Laplacian is at
most the mean scalar curvature `∫ Scal_g dV / Vol(M, g)`. -/
theorem sInf_subcriticalYamabeQuotient_two_le_integral_scalarCurvature_div [Nonempty M]
    (hn : 2 < finrank ℝ E) :
    sInf (subcriticalYamabeQuotient I 2 '' {w : SobolevH1 I M | w ≠ 0}) ≤
      (∫ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x
        ∂riemannianVolume I M) / riemannianTotalVolume I M := by
  rw [le_div_iff₀ riemannianTotalVolume_pos, ← norm_toLp_ofSmooth_one_sq,
    ← energyForm_ofSmooth_one_self]
  exact sInf_subcriticalYamabeQuotient_two_mul_le_energyForm hn _

/-- **Equality case of the mean scalar curvature bound.** On a nonempty closed manifold of
dimension `n > 2`, the infimum `λ₁` of the Rayleigh quotient of the conformal Laplacian equals the
mean scalar curvature `∫ Scal_g dV / Vol(M, g)` if and only if `Scal_g` is constant. -/
theorem sInf_subcriticalYamabeQuotient_two_eq_integral_scalarCurvature_div_iff [Nonempty M]
    (hn : 2 < finrank ℝ E) :
    sInf (subcriticalYamabeQuotient I 2 '' {w : SobolevH1 I M | w ≠ 0}) =
        (∫ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x
          ∂riemannianVolume I M) / riemannianTotalVolume I M ↔
      ∃ c : ℝ, ∀ x, (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x = c := by
  set S := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  set l := sInf (subcriticalYamabeQuotient I 2 '' {w : SobolevH1 I M | w ≠ 0})
  have hV := riemannianTotalVolume_pos (I := I) (M := M)
  have hS : Continuous S :=
    (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous
  constructor
  · intro h
    -- The constant function `1` attains `λ₁`, so it is a weak eigenfunction: `∫ Scal φ = λ₁ ∫ φ`.
    have h1 : energyForm I (SobolevH1.ofSmooth (1 : C^∞⟮I, M; ℝ⟯)) (SobolevH1.ofSmooth 1) =
        l * ‖SobolevH1.toLp (SobolevH1.ofSmooth (1 : C^∞⟮I, M; ℝ⟯))‖ ^ 2 := by
      rw [energyForm_ofSmooth_one_self, norm_toLp_ofSmooth_one_sq, h, div_mul_cancel₀ _ hV.ne']
    have hcont : Continuous fun x ↦ S x - l := hS.sub continuous_const
    have hae : ∀ᵐ x ∂riemannianVolume I M, S x - l = 0 := by
      refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hcont.locallyIntegrable
        fun φ hφ _ ↦ ?_
      let φ' : C^∞⟮I, M; ℝ⟯ := ⟨φ, hφ⟩
      have he := energyForm_eq_sInf_subcriticalYamabeQuotient_two_mul_inner hn h1
        (SobolevH1.ofSmooth φ')
      rw [energyForm_ofSmooth, SobolevH1.inner_toLp_ofSmooth] at he
      simp only [φ', ContMDiffMap.coe_one, Pi.one_def, mgradient_const, Pi.zero_apply,
        inner_zero_left, mul_zero, zero_add, one_mul, ContMDiffMap.coeFn_mk] at he
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub (f := fun x ↦ φ x * S x) (g := fun x ↦ φ x * l)
        (hφ.continuous.mul hS).integrable_of_compactSpace
        (hφ.continuous.mul continuous_const).integrable_of_compactSpace, integral_mul_const,
        sub_eq_zero]
      simp only [mul_comm (φ _)]
      rw [mul_comm]
      exact he
    exact ⟨l, fun x ↦ sub_eq_zero.1 (congrFun ((hcont.ae_eq_iff_eq _ continuous_zero).1 hae) x)⟩
  · rintro ⟨c, hc⟩
    have hmean : (∫ x, S x ∂riemannianVolume I M) / riemannianTotalVolume I M = c := by
      simp only [hc, integral_const_riemannianVolume, mul_div_cancel_right₀ _ hV.ne']
    rw [hmean]
    refine le_antisymm (hmean ▸ sInf_subcriticalYamabeQuotient_two_le_integral_scalarCurvature_div
      hn) ?_
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : SobolevH1 I M)
    refine le_csInf ⟨_, w₀, hw₀, rfl⟩ fun _ ⟨w, hw, h⟩ ↦ h ▸ ?_
    -- With constant scalar curvature `c`, `E_g(w, w) = aₙ D(w, w) + c ‖w‖²_{L²} ≥ c ‖w‖²_{L²}`.
    rw [subcriticalYamabeQuotient_two, le_div_iff₀ (norm_toLp_sq_pos hw), energyForm_apply]
    have hsq : ∫ x, S x * SobolevH1.toLp w x * SobolevH1.toLp w x ∂riemannianVolume I M =
        c * ‖SobolevH1.toLp w‖ ^ 2 := by
      simp only [hc, mul_assoc, integral_const_mul, ← sq]
      rw [← Lp.integral_norm_sq_eq_norm_sq]
      simp only [Real.norm_eq_abs, sq_abs]
    rw [hsq]
    exact le_add_of_nonneg_left (mul_nonneg (conformalCoefficient_nonneg _)
      (SobolevH1.dirichletForm_self_nonneg w))

/-! ### Positive eigenfunctions -/

/-- If `L_g u = c u`, then `E_g(f, u) = c ⟪f, u⟫_{L²}` for every smooth `f`. -/
private theorem energyForm_ofSmooth_eq_mul_inner {u : C^∞⟮I, M; ℝ⟯} {c : ℝ}
    (hc : ∀ x, conformalLaplacian I u x = c * u x) (f : C^∞⟮I, M; ℝ⟯) :
    energyForm I (SobolevH1.ofSmooth f) (SobolevH1.ofSmooth u) =
      c * inner ℝ (SobolevH1.toLp (SobolevH1.ofSmooth f))
        (SobolevH1.toLp (SobolevH1.ofSmooth u)) := by
  rw [energyForm_ofSmooth_right, SobolevH1.inner_toLp_ofSmooth, ← integral_const_mul]
  refine integral_congr_ae ((SobolevH1.toLp_ofSmooth_ae_eq f).mono fun x hx ↦ ?_)
  dsimp only
  rw [hx, hc]
  ring

/-- **Positive eigenfunctions bound the energy below.** If `u` is smooth and positive with
`L_g u = c u`, then `c ‖φ‖²_{L²} ≤ E_g(φ, φ)` for every smooth `φ`. -/
private theorem mul_norm_toLp_sq_le_energyForm_ofSmooth {u : C^∞⟮I, M; ℝ⟯} (hu : ∀ x, 0 < u x)
    {c : ℝ} (hc : ∀ x, conformalLaplacian I u x = c * u x) (φ : C^∞⟮I, M; ℝ⟯) :
    c * ‖SobolevH1.toLp (SobolevH1.ofSmooth φ)‖ ^ 2 ≤
      energyForm I (SobolevH1.ofSmooth φ) (SobolevH1.ofSmooth φ) := by
  set S := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  set a := conformalCoefficient (finrank ℝ E)
  have hv : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ φ x / u x :=
    φ.contMDiff.div₀ u.contMDiff fun x ↦ (hu x).ne'
  let v : C^∞⟮I, M; ℝ⟯ := ⟨fun x ↦ φ x / u x, hv⟩
  have hφ : φ = u * v := ContMDiffMap.ext fun x ↦ by
    rw [ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.coeFn_mk, mul_div_cancel₀ _ (hu x).ne']
  have hd (f : C^∞⟮I, M; ℝ⟯) : MDifferentiable I 𝓘(ℝ) f := f.contMDiff.mdifferentiable (by simp)
  have hint (f g : C^∞⟮I, M; ℝ⟯) : Integrable (fun x ↦ a * inner ℝ (mgradient I f x)
      (mgradient I g x) + S x * (f x * g x)) (riemannianVolume I M) :=
    ((continuous_const.mul (continuous_inner_mgradient (f.contMDiff.of_le (by simp))
      (g.contMDiff.of_le (by simp)))).add
      ((CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous.mul
        ((map_continuous f).mul (map_continuous g)))).integrable_of_compactSpace
  -- Write `φ = u v`. Then `E_g(u v², u) = c ∫ u² v² dV`, and pointwise
  -- `|∇(u v)|² = ⟪∇(u v²), ∇u⟫ + u² |∇v|²`, so `E_g(u v², u) ≤ E_g(φ, φ)`.
  calc c * ‖SobolevH1.toLp (SobolevH1.ofSmooth φ)‖ ^ 2 =
      energyForm I (SobolevH1.ofSmooth (u * (v * v))) (SobolevH1.ofSmooth u) := by
        rw [energyForm_ofSmooth_eq_mul_inner hc, SobolevH1.inner_toLp_ofSmooth,
          ← real_inner_self_eq_norm_sq, SobolevH1.inner_toLp_ofSmooth, hφ]
        simp only [ContMDiffMap.coe_mul, Pi.mul_apply]
        congr 1
        exact integral_congr_ae (.of_forall fun x ↦ by ring)
    _ ≤ energyForm I (SobolevH1.ofSmooth φ) (SobolevH1.ofSmooth φ) := by
        rw [energyForm_ofSmooth, energyForm_ofSmooth]
        refine integral_mono (hint _ _) (hint _ _) fun x ↦ ?_
        rw [hφ]
        simp only [ContMDiffMap.coe_mul]
        rw [mgradient_mul (hd u) ((hd v).mul (hd v)), mgradient_mul (hd v) (hd v),
          mgradient_mul (hd u) (hd v)]
        simp only [Pi.mul_apply, inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm (mgradient I u x),
          norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        nlinarith [mul_nonneg (conformalCoefficient_nonneg (finrank ℝ E))
          (mul_nonneg (sq_nonneg (u x)) (sq_nonneg ‖mgradient I v x‖))]

/-- **The eigenvalue of a positive eigenfunction is the first eigenvalue.** On a nonempty closed
manifold of dimension `n > 2`, if a smooth positive function `u` satisfies `L_g u = c u`, then `c`
is the infimum `λ₁` of the Rayleigh quotient of the conformal Laplacian over nonzero
`w ∈ H¹(M)`. -/
theorem sInf_subcriticalYamabeQuotient_two_eq_of_conformalLaplacian_eq_mul [Nonempty M]
    (hn : 2 < finrank ℝ E) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x)
    {c : ℝ} (hc : ∀ x, conformalLaplacian I u x = c * u x) :
    sInf (subcriticalYamabeQuotient I 2 '' {w : SobolevH1 I M | w ≠ 0}) = c := by
  let U : C^∞⟮I, M; ℝ⟯ := ⟨u, hu⟩
  -- By density of smooth functions, `c ‖w‖²_{L²} ≤ E_g(w, w)` on all of `H¹(M)`.
  have hle (w : SobolevH1 I M) : c * ‖SobolevH1.toLp w‖ ^ 2 ≤ energyForm I w w := by
    induction w using SobolevH1.induction_on with
    | hp => exact isClosed_le (by fun_prop) ((energyForm I).continuous₂.comp
        (continuous_id.prodMk continuous_id))
    | h φ => exact mul_norm_toLp_sq_le_energyForm_ofSmooth (u := U) hu_pos hc φ
  have hU0 : SobolevH1.ofSmooth U ≠ 0 := by
    intro h0
    have hae : (u : M → ℝ) =ᵐ[riemannianVolume I M] 0 :=
      (SobolevH1.toLp_ofSmooth_ae_eq U).symm.trans (by rw [h0, map_zero]; exact Lp.coeFn_zero ..)
    exact (hu_pos (Classical.arbitrary M)).ne'
      (congrFun ((hu.continuous.ae_eq_iff_eq _ continuous_zero).1 hae) _)
  refine le_antisymm ((csInf_le (bddBelow_image_subcriticalYamabeQuotient le_rfl
    (two_lt_criticalExponent hn).le) ⟨_, hU0, rfl⟩).trans_eq ?_)
    (le_csInf ⟨_, _, hU0, rfl⟩ fun _ ⟨w, hw, h⟩ ↦ h ▸ ?_)
  · rw [subcriticalYamabeQuotient_two, energyForm_ofSmooth_eq_mul_inner (u := U) hc,
      real_inner_self_eq_norm_sq, mul_div_cancel_right₀ _ (norm_toLp_sq_pos hU0).ne']
  · rw [subcriticalYamabeQuotient_two, le_div_iff₀ (norm_toLp_sq_pos hw)]
    exact hle w

/-- **The sign of the Yamabe invariant is the sign of the first eigenvalue.** On a closed manifold
of dimension `n > 2`, the Yamabe invariant `Y = inf {Q_g(w) | w ≠ 0}` has the same sign as the
infimum `λ₁` of the Rayleigh quotient of the conformal Laplacian over nonzero `w ∈ H¹(M)`. -/
theorem sign_sInf_weakYamabeQuotient_eq (hn : 2 < finrank ℝ E) :
    SignType.sign (sInf (weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0})) =
      SignType.sign (sInf (subcriticalYamabeQuotient I 2 '' {w : SobolevH1 I M | w ≠ 0})) := by
  have hp := two_lt_criticalExponent hn
  rw [← funext (subcriticalYamabeQuotient_criticalExponent (I := I) (M := M))]
  exact sign_sInf_subcriticalYamabeQuotient_eq hp.le le_rfl le_rfl hp.le

end TauCeti.Yamabe
