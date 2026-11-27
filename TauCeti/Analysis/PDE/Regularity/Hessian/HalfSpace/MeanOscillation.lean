/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.MeanOscillation
public import TauCeti.Analysis.PDE.Regularity.Hessian.MeanOscillation
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.PDE.Ellipticity.Contraction
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.W1p.TangentialDerivative
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Integral.Average.Oscillation

/-!
# Mean oscillation of the Hessian at a flat boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `z` lie on its boundary hyperplane, and write
`B_t⁺ = B(z, t) ∩ H`. Let `u ∈ W^{2,2}(H)` have zero boundary values, `u ∈ W^{1,2}_0(H)`, and be a
strong solution of the non-divergence-form equation `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` on `B_r⁺`, with a bounded
measurable coefficient matrix `a`, neither continuous nor symmetric. Freezing the coefficients at
any constant matrix `A`, uniformly elliptic with constants `0 < λ ≤ Λ`, and writing
`θ = ‖a - A‖`, this file proves the boundary counterpart of Krylov's mean oscillation estimate for
the Hessian, in the `TauCeti.PDE` namespace,
`exists_setIntegral_ball_inter_norm_iteratedGradient_sub_setAverage_sq_le_add`: there is
`C = C(n, λ, Λ)` such that for `0 < ρ ≤ r`

`∫_{B_ρ⁺} ‖D²u - (D²u)_{B_ρ⁺}‖² ≤ C (ρ / r)^(n + 3) ∫_{B_r⁺} ‖D²u‖²`
`  + C (∫_{B_r⁺} f² + ∫_{B_r⁺} θ² ‖D²u‖²)`.

The constant matrix `A` is arbitrary and enters only through the weighted error
`∫_{B_r⁺} θ² ‖D²u‖²`; taking `A` to be an average of `a` makes this the frozen-coefficient step of
the sharp-function proof of the `W^{2,p}` estimate up to a flat boundary, once that term is
controlled. Unlike the reflection arguments used for continuous coefficients,
nothing requires the coefficients near the boundary to be close to a reflection-invariant matrix.

## The argument

* **Tangential columns.** For a tangential direction `τ`, `⟪τ, ν⟫ = 0`, translations along `τ` map
  `H` to itself, so `∂_τ u` keeps the zero boundary values of `u`
  (`TauCeti.W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn`). Its zero extension vanishes off `H`, has
  gradient `D²u τ` on `H` and solves `-div(A ∇(∂_τ u)) = -div(g τ)` with `g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`
  (`TauCeti.PDE.exists_hasWeakLineDerivOn_and_gradient_ae_eq_and_energyFormH1_eq`). The boundary
  mean oscillation estimate for the gradient of divergence-form solutions, in `TauCeti.PDE`,
  `exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_add`, bounds
  the mean oscillation of `D²u τ`.
* **The normal-normal entry.** With `w = ν / ‖ν‖` and `τⱼ = eⱼ - ⟪eⱼ, w⟫ w`, a symmetric
  endomorphism `S` is controlled by the `S τⱼ` up to its component `⟪S w, w⟫`, and since
  `⟪A w, w⟫ ≥ λ` that component is recovered from the contraction `∑ᵢⱼ Aᵢⱼ ⟪S eᵢ, eⱼ⟫`
  (`TauCeti.PDE.norm_sq_le_sum_norm_apply_sub_sq_add_contraction_sq`). Applied to
  `S = D²u - (D²u)_{B_ρ⁺}`, the contraction is `g - g_{B_ρ⁺}`, whose `L²` norm is bounded by that of
  `g = f + ∑ᵢⱼ (A - a)ᵢⱼ ∂ᵢ∂ⱼu` (`TauCeti.PDE.setIntegral_contraction_iteratedGradient_sq_le`).

## References

* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate Studies
  in Mathematics **96**, AMS, 2008 (estimates near a flat boundary).
* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
-/

public section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- **Tangential derivatives at a flat boundary.** Let `H = {x | c₀ < ⟪x, ν⟫}` and let
`u ∈ W^{2,2}(H)` have zero boundary values, `u ∈ W^{1,2}_0(H)`. For a tangential direction `τ`,
`⟪τ, ν⟫ = 0`, the zero extension `W` of the weak derivative `∂_τ u` to the whole space lies in
`H¹(ℝ^{n+1})`, vanishes off `H`, has gradient `D²u τ` on `H`, and solves the differentiated
equation `-div(A ∇W) = -div(g τ)` on `H` for every constant matrix `A`, with
`g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`. -/
private theorem exists_w1p_top_and_gradient_ae_eq_and_energyFormH1_eq
    {H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) H 2 2)
    {ν τ : EuclideanSpace ℝ (Fin (n + 1))} {c₀ : ℝ} (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hu0 : Wkp.lowerOrder 1 u ∈ w1p0Submodule volume H 2) (hτ : ⟪τ, ν⟫_ℝ = 0) :
    ∃ W : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ᵐ x ∂volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1)))), x ∉ H → W1p.value W x = 0) ∧
      (∀ s ⊆ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))),
        (W1p.gradient W : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          =ᵐ[volume.restrict s] fun x => Wkp.iteratedGradient 1 u x τ) ∧
      ∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
        (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H, ℝ)),
        energyFormH1 (fun _ => A) 0 0 (W1p.restrictL inf_le_left W)
            (W1p.ofTestFunctionₗ volume (⊤ ⊓ H) 2 φ) =
          ∫ x in (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ⊓ H,
            ⟪Matrix.contraction A (Wkp.iteratedGradient 1 u x) • τ,
              ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
  obtain ⟨d, hd, hdg, hdeq⟩ :=
    exists_hasWeakLineDerivOn_and_gradient_ae_eq_and_energyFormH1_eq u τ
  -- Translations along `τ` map `H` to itself, so `∂_τ u` keeps the zero boundary values of `u`.
  choose D hD using fun i => (exists_hasWeakLineDerivOn_and_gradient_ae_eq_and_energyFormH1_eq u
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ i)).imp fun _ h => h.1
  have hmem : d ∈ w1p0Submodule volume H 2 :=
    W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn (by simp) (convex_of_halfSpace hH)
      (fun t => mapsTo_add_smul_of_halfSpace hH hτ t) _ hu0 hD hd
  refine ⟨(W1p0.extendByZeroL (le_top : H ≤ ⊤) ⟨d, hmem⟩ : W1p volume ⊤ 2), ?_, fun s hs => ?_,
    fun A => ?_⟩
  · exact ae_restrict_of_ae (W1p0.value_extendByZeroL_ae_eq_zero_compl _)
  · filter_upwards [ae_restrict_of_ae (s := s)
        (W1p0.gradient_extendByZeroL_top_ae (⟨d, hmem⟩ : W1p0 volume H 2)),
      ae_restrict_of_ae_restrict_of_subset hs hdg,
      ae_restrict_of_ae_restrict_of_subset hs (ae_restrict_mem H.isOpen.measurableSet)]
      with x h1 h2 hx
    rw [h1, indicator_of_mem hx]
    exact h2
  · -- On `⊤ ⊓ H = H` the restriction of the zero extension is `∂_τ u` itself.
    have key : ∀ (V : Opens (EuclideanSpace ℝ (Fin (n + 1)))) (_ : V = H) (hVt : V ≤ ⊤)
        (φ : 𝓓(V, ℝ)), energyFormH1 (fun _ => A) 0 0
          (W1p.restrictL hVt (W1p0.extendByZeroL (le_top : H ≤ ⊤) ⟨d, hmem⟩ : W1p volume ⊤ 2))
          (W1p.ofTestFunctionₗ volume V 2 φ) =
        ∫ x in V, ⟪Matrix.contraction A (Wkp.iteratedGradient 1 u x) • τ,
          ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
      rintro V rfl hVt φ
      rw [W1p0.restrictL_extendByZeroL]
      exact hdeq A φ
    exact key _ (top_inf_eq H) inf_le_left

/-- **Mean oscillation of a tangential column of the Hessian at a flat boundary.** With the
notation of `exists_w1p_top_and_gradient_ae_eq_and_energyFormH1_eq`, the column `D²u τ` of the
Hessian in a tangential direction `τ` is the gradient of a function vanishing on the boundary
hyperplane and solving `-div(A ∇W) = -div(g τ)`, so its square mean oscillation on
`B_ρ⁺ = B(z, ρ) ∩ H` decays like that of a solution of the homogeneous equation, up to the `L²`
norm of `g τ`, `g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`. -/
private theorem exists_setIntegral_ball_inter_norm_apply_sub_setAverage_sq_le {lam Lam : ℝ}
    (hlam : 0 < lam) :
    ∃ D : ℝ, 0 < D ∧ ∀ {H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) H 2 2}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {ν z τ : EuclideanSpace ℝ (Fin (n + 1))}
      {c₀ r ρ : ℝ},
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ →
      Wkp.lowerOrder 1 u ∈ w1p0Submodule volume H 2 → ⟪τ, ν⟫_ℝ = 0 → 0 < ρ → ρ ≤ r →
      ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x τ -
          ⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y τ‖ ^ 2 ≤
        D * (ρ / r) ^ (n + 3) * (∫ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x τ‖ ^ 2) +
          D * ∫ x in ball z r ∩ H,
            ‖Matrix.contraction A (Wkp.iteratedGradient 1 u x) • τ‖ ^ 2 := by
  obtain ⟨D, hD, hdec⟩ :=
    exists_setIntegral_ball_inter_norm_gradient_sub_inner_setAverage_div_smul_sq_le_add
      (n := n) (Lam := Lam) hlam
  refine ⟨D, hD, fun {H u A ν z τ c₀ r ρ} hA hν hH hzc hu0 hτ hρ hρr => ?_⟩
  obtain ⟨W, hW0, hWg, hWeq⟩ := exists_w1p_top_and_gradient_ae_eq_and_energyFormH1_eq u hH hu0 hτ
  have hsH : ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ H := inter_subset_right
  have htH : ball z ρ ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ H := inter_subset_right
  have hT : MemLp (fun x => Wkp.iteratedGradient 1 u x) 2
      (volume.restrict (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) := Lp.memLp _
  have hTτ : MemLp (fun x => Wkp.iteratedGradient 1 u x τ) 2
      (volume.restrict (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) τ).comp_memLp' hT
  have hG : MemLp (fun x => Matrix.contraction A (Wkp.iteratedGradient 1 u x) • τ - 0) 2
      (volume.restrict (ball z r ∩ H)) := by
    simpa only [sub_zero, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using
      (((ContinuousLinearMap.toSpanSingleton ℝ τ).comp (Matrix.contraction A)).comp_memLp'
        hT).mono_measure (Measure.restrict_mono hsH le_rfl)
  -- `sub_self`, `norm_zero` and `simp` do not fire on bilinear forms directly (their subtraction
  -- and norm are not the generic instances): pass through `matrixBilinearForm_sub`, `opNorm_zero`.
  have hθ : ‖matrixBilinearForm A - matrixBilinearForm A‖ = 0 := by
    rw [← matrixBilinearForm_sub, sub_self]
    simpa using ContinuousLinearMap.opNorm_zero
  have h := hdec (U := ⊤) (u := W) (a := fun _ => A) (K := 0) (c := 0) hA
    aestronglyMeasurable_const (fun _ _ => le_of_eq hθ) hν hH hzc
    (fun _ _ => by simp only [Opens.coe_top, mem_univ]) hW0 (hWeq A) hG hρ hρr 0
  beta_reduce at h
  have hht : volume (ball z ρ ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≠ ⊤ :=
    (measure_mono inter_subset_left).trans_lt measure_ball_lt_top |>.ne
  have : IsFiniteMeasure
      (volume.restrict (ball z ρ ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :=
    isFiniteMeasure_restrict.2 hht
  set p := (⟪⨍ y in ball z ρ ∩ H, W1p.gradient W y, ν⟫_ℝ / ‖ν‖ ^ 2) • ν
  calc ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x τ -
          ⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y τ‖ ^ 2
      ≤ ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x τ - p‖ ^ 2 :=
        setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq hht
          ((hTτ.mono_measure (Measure.restrict_mono htH le_rfl)).integrable one_le_two)
          (hTτ.integrableOn_norm_sub_sq_of_subset htH hht p)
    _ = ∫ x in ball z ρ ∩ H, ‖W1p.gradient W x - p‖ ^ 2 :=
        integral_congr_ae ((hWg _ htH).mono fun x hx => by simp only [hx])
    _ ≤ _ := h
    _ = _ := by
        rw [integral_congr_ae (g := fun x => ‖Wkp.iteratedGradient 1 u x τ‖ ^ 2)
          ((hWg _ hsH).mono fun x hx => by simp only [zero_smul, sub_zero, hx])]
        have h0 : ∀ x, ‖matrixBilinearForm A - matrixBilinearForm A‖ ^ 2 *
            ‖W1p.gradient W x‖ ^ 2 = 0 := fun x => by
          rw [mul_eq_zero, pow_eq_zero_iff two_ne_zero]
          exact Or.inl hθ
        simp only [h0, integral_zero, zero_add, sub_zero]

/-- **The Hessian is controlled by its tangential columns and the equation.** Let `w` be a unit
vector, `τⱼ = eⱼ - ⟪eⱼ, w⟫ w`, and let `A` be a matrix with `λ ≤ ⟪A w, w⟫` and `‖A‖ ≤ Λ`. Almost
everywhere on a set `t ⊆ Ω` of finite measure, the deviation of the Hessian of `u ∈ W^{2,2}(Ω)` from
its average over `t` is controlled by the deviations of its columns `D²u τⱼ` and of
`g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` from their averages. -/
private theorem ae_norm_iteratedGradient_sub_setAverage_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hΛ : ‖matrixBilinearForm A‖ ≤ Lam)
    {w : EuclideanSpace ℝ (Fin (n + 1))} (hw : ‖w‖ = 1) (hAw : lam ≤ matrixBilinearForm A w w)
    {τ : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))}
    (hτ : ∀ j, τ j = EuclideanSpace.single j 1 - ⟪EuclideanSpace.single j 1, w⟫_ℝ • w)
    {t : Set (EuclideanSpace ℝ (Fin (n + 1)))} (htΩ : t ⊆ Omega) (ht : volume t ≠ ⊤) :
    ∀ᵐ x ∂volume.restrict t, ‖Wkp.iteratedGradient 1 u x -
        ⨍ y in t, Wkp.iteratedGradient 1 u y‖ ^ 2 ≤
      2 * (n + 1) * (2 + 2 * (n + 1) * Lam / lam) ^ 2 *
          ∑ j, ‖Wkp.iteratedGradient 1 u x (τ j) - ⨍ y in t, Wkp.iteratedGradient 1 u y (τ j)‖ ^ 2 +
        2 / lam ^ 2 * (Matrix.contraction A (Wkp.iteratedGradient 1 u x) -
          ⨍ y in t, Matrix.contraction A (Wkp.iteratedGradient 1 u y)) ^ 2 := by
  have : IsFiniteMeasure (volume.restrict t) := isFiniteMeasure_restrict.2 ht
  have hT : Integrable (fun x => Wkp.iteratedGradient 1 u x) (volume.restrict t) :=
    ((Lp.memLp (Wkp.iteratedGradient 1 u)).mono_measure
      (Measure.restrict_mono htΩ le_rfl)).integrable one_le_two
  -- Averages commute with continuous linear functionals of the Hessian.
  have havg : ∀ L : (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) →L[ℝ] ℝ,
      L (⨍ y in t, Wkp.iteratedGradient 1 u y) =
        ⨍ y in t, L (Wkp.iteratedGradient 1 u y) := fun L => by
    rw [setAverage_eq, setAverage_eq, map_smul, L.integral_comp_comm hT]
  have hsym := ae_restrict_of_ae_restrict_of_subset htΩ (ae_all_iff.2 fun j =>
    Wkp.inner_iteratedGradient_one_apply_ae_eq u w (τ j))
  -- The average of the Hessian is symmetric between `w` and each `τⱼ`.
  have hMsym : ∀ j, ⟪(⨍ y in t, Wkp.iteratedGradient 1 u y) w, τ j⟫_ℝ =
      ⟪(⨍ y in t, Wkp.iteratedGradient 1 u y) (τ j), w⟫_ℝ := fun j => by
    set M := ⨍ y in t, Wkp.iteratedGradient 1 u y
    have h1 := havg ((innerSL ℝ (τ j)).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) w))
    have h2 := havg ((innerSL ℝ w).comp
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) (τ j)))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply] at h1 h2
    rw [← real_inner_comm (M w) (τ j), ← real_inner_comm (M (τ j)) w, h1, h2]
    exact average_congr (hsym.mono fun y hy => by
      beta_reduce
      rw [real_inner_comm (Wkp.iteratedGradient 1 u y w) (τ j)]
      exact (hy j).trans (real_inner_comm _ _))
  filter_upwards [hsym] with x hx
  have key := norm_sq_le_sum_norm_apply_sub_sq_add_contraction_sq hlam hΛ hw hAw hτ
    (Wkp.iteratedGradient 1 u x - ⨍ y in t, Wkp.iteratedGradient 1 u y) fun j => by
      rw [sub_apply, sub_apply, inner_sub_left, inner_sub_left, hx j, hMsym j]
  rw [map_sub, havg] at key
  simpa only [sub_apply, ContinuousLinearMap.average_apply hT, Nat.cast_add, Nat.cast_one]
    using key

/-- **The integrated pointwise bound.** With `w`, `A` and `t` as in
`ae_norm_iteratedGradient_sub_setAverage_sq_le`, the square mean oscillation of the Hessian over
`t` is controlled by those of its columns `D²u τⱼ` and of `g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`. -/
private theorem setIntegral_norm_iteratedGradient_sub_setAverage_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hΛ : ‖matrixBilinearForm A‖ ≤ Lam)
    {w : EuclideanSpace ℝ (Fin (n + 1))} (hw : ‖w‖ = 1) (hAw : lam ≤ matrixBilinearForm A w w)
    {τ : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1))}
    (hτ : ∀ j, τ j = EuclideanSpace.single j 1 - ⟪EuclideanSpace.single j 1, w⟫_ℝ • w)
    {t : Set (EuclideanSpace ℝ (Fin (n + 1)))} (htΩ : t ⊆ Omega) (htf : volume t ≠ ⊤) :
    ∫ x in t, ‖Wkp.iteratedGradient 1 u x - ⨍ y in t, Wkp.iteratedGradient 1 u y‖ ^ 2 ≤
      2 * (n + 1) * (2 + 2 * (n + 1) * Lam / lam) ^ 2 * (∑ j, ∫ x in t,
        ‖Wkp.iteratedGradient 1 u x (τ j) - ⨍ y in t, Wkp.iteratedGradient 1 u y (τ j)‖ ^ 2) +
      2 / lam ^ 2 * ∫ x in t, (Matrix.contraction A (Wkp.iteratedGradient 1 u x) -
        ⨍ y in t, Matrix.contraction A (Wkp.iteratedGradient 1 u y)) ^ 2 := by
  have hT : MemLp (fun x => Wkp.iteratedGradient 1 u x) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) := Lp.memLp _
  have hTτ : ∀ v, MemLp (fun x => Wkp.iteratedGradient 1 u x v) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) := fun v =>
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) v).comp_memLp' hT
  have hg : MemLp (fun x => Matrix.contraction A (Wkp.iteratedGradient 1 u x)) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (Matrix.contraction A).comp_memLp' hT
  have hgsq : ∀ c : ℝ, IntegrableOn (fun x =>
      (Matrix.contraction A (Wkp.iteratedGradient 1 u x) - c) ^ 2) t := fun c =>
    (hg.integrableOn_norm_sub_sq_of_subset htΩ htf c).congr
      (ae_of_all _ fun x => by simp only [Real.norm_eq_abs, sq_abs])
  have hint := integral_mono_ae (hT.integrableOn_norm_sub_sq_of_subset htΩ htf _)
    (((integrable_finsetSum _ fun j _ => (hTτ _).integrableOn_norm_sub_sq_of_subset htΩ htf
      _).const_mul _).add ((hgsq _).const_mul _))
    (ae_norm_iteratedGradient_sub_setAverage_sq_le u hlam hΛ hw hAw hτ htΩ htf)
  refine hint.trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_add (((integrable_finsetSum _ fun j _ =>
      (hTτ _).integrableOn_norm_sub_sq_of_subset htΩ htf _).const_mul _))
      ((hgsq _).const_mul _), integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun j _ => (hTτ _).integrableOn_norm_sub_sq_of_subset htΩ htf _]

/-- For `w = ‖ν‖⁻¹ ν` the tangential parts `eⱼ - ⟪eⱼ, w⟫ w` of the coordinate vectors are
orthogonal to `ν`. -/
private theorem inner_single_sub_inner_smul_eq_zero {ν : EuclideanSpace ℝ (Fin (n + 1))}
    (hν : ν ≠ 0) (j : Fin (n + 1)) :
    ⟪EuclideanSpace.single j (1 : ℝ) - ⟪EuclideanSpace.single j (1 : ℝ), ‖ν‖⁻¹ • ν⟫_ℝ •
      (‖ν‖⁻¹ • ν), ν⟫_ℝ = 0 := by
  have hν0 : ‖ν‖ ≠ 0 := norm_ne_zero_iff.2 hν
  simp only [inner_sub_left, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
    RCLike.conj_to_real]
  field_simp
  ring

/-- For a unit vector `w`, the tangential parts `eⱼ - ⟪eⱼ, w⟫ w` have norm at most `2`. -/
private theorem norm_single_sub_inner_smul_le_two {w : EuclideanSpace ℝ (Fin (n + 1))}
    (hw : ‖w‖ = 1) (j : Fin (n + 1)) :
    ‖EuclideanSpace.single j (1 : ℝ) - ⟪EuclideanSpace.single j (1 : ℝ), w⟫_ℝ • w‖ ≤ 2 := by
  have h1 := abs_real_inner_le_norm (EuclideanSpace.single j (1 : ℝ)) w
  rw [PiLp.norm_single, norm_one, hw, mul_one] at h1
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, hw, mul_one, Real.norm_eq_abs, PiLp.norm_single, norm_one]
  linarith

/-- A column `D²u τ` with `‖τ‖ ≤ 2`, and `g τ` for `g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`, have at most four times the
`L²` mass of `D²u` and of `g` on a set `s ⊆ Ω` of finite measure. -/
private theorem setIntegral_norm_apply_sq_le_and_setIntegral_norm_smul_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) Omega 2 2)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) {τ : EuclideanSpace ℝ (Fin (n + 1))}
    (hτ : ‖τ‖ ≤ 2) {s : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hsΩ : s ⊆ Omega)
    (hsm : MeasurableSet s) (hsf : volume s ≠ ⊤) :
    ∫ x in s, ‖Wkp.iteratedGradient 1 u x τ‖ ^ 2 ≤
        4 * ∫ x in s, ‖Wkp.iteratedGradient 1 u x‖ ^ 2 ∧
      ∫ x in s, ‖Matrix.contraction A (Wkp.iteratedGradient 1 u x) • τ‖ ^ 2 ≤
        4 * ∫ x in s, Matrix.contraction A (Wkp.iteratedGradient 1 u x) ^ 2 := by
  have hT : MemLp (fun x => Wkp.iteratedGradient 1 u x) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) := Lp.memLp _
  have hgs := ((Matrix.contraction A).comp_memLp' hT).integrableOn_norm_sub_sq_of_subset hsΩ hsf 0
  have hTs := hT.integrableOn_norm_sub_sq_of_subset hsΩ hsf 0
  have hTτs := ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin (n + 1))) τ).comp_memLp'
    hT).integrableOn_norm_sub_sq_of_subset hsΩ hsf 0
  simp only [sub_zero] at hTs hgs hTτs
  have hgτs : IntegrableOn (fun x =>
      ‖Matrix.contraction A (Wkp.iteratedGradient 1 u x) • τ‖ ^ 2) s :=
    (hgs.const_mul (‖τ‖ ^ 2)).congr (ae_of_all _ fun x => by
      simp only [Function.comp_apply, norm_smul, mul_pow]
      ring)
  have hgs' : IntegrableOn (fun x => Matrix.contraction A (Wkp.iteratedGradient 1 u x) ^ 2) s :=
    hgs.congr (ae_of_all _ fun x => by simp only [Function.comp_apply, Real.norm_eq_abs, sq_abs])
  rw [← integral_const_mul, ← integral_const_mul]
  refine ⟨setIntegral_mono_on hTτs (hTs.const_mul 4) hsm fun x _ => ?_,
    setIntegral_mono_on hgτs (hgs'.const_mul 4) hsm fun x _ => ?_⟩
  · have h1 := (Wkp.iteratedGradient 1 u x).le_opNorm τ
    have h2 := mul_le_mul_of_nonneg_left hτ (norm_nonneg (Wkp.iteratedGradient 1 u x))
    nlinarith [norm_nonneg (Wkp.iteratedGradient 1 u x τ)]
  · rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_comm]
    gcongr
    nlinarith [norm_nonneg τ]

/-- The arithmetic that collects the constants in
`exists_setIntegral_ball_inter_norm_iteratedGradient_sub_setAverage_sq_le_add`. -/
private theorem final_bound {C₁ D lam q I F Θ G Gt X Ψ : ℝ} (hC₁0 : 0 ≤ C₁) (hD : 0 ≤ D)
    (hq : 0 ≤ q) (hI : 0 ≤ I) (hF : 0 ≤ F) (hΘ : 0 ≤ Θ)
    (hX : X ≤ C₁ * Ψ + 2 / lam ^ 2 * Gt) (hsum : Ψ ≤ (n + 1) * (D * q * (4 * I) + D * (4 * G)))
    (hGt : Gt ≤ G) (hG : G ≤ 2 * (F + (n + 1) ^ 2 * Θ)) :
    X ≤ (4 * C₁ * (n + 1) * D + 2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) + 1) *
        q * I +
      (4 * C₁ * (n + 1) * D + 2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) + 1) *
        (F + Θ) := by
  have hn : (1 : ℝ) ≤ (n + 1) ^ 2 := one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)])
  refine hX.trans ?_
  have hG' : G ≤ 2 * (n + 1) ^ 2 * (F + Θ) := hG.trans (by nlinarith)
  have hP : 0 ≤ 4 * C₁ * (n + 1) * D := by positivity
  have hR : 0 ≤ 4 * C₁ * (n + 1) * D + 2 / lam ^ 2 := by positivity
  have hR' : 0 ≤ 2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) := by positivity
  calc C₁ * Ψ + 2 / lam ^ 2 * Gt
      ≤ C₁ * ((n + 1) * (D * q * (4 * I) + D * (4 * G))) + 2 / lam ^ 2 * G :=
        add_le_add (mul_le_mul_of_nonneg_left hsum hC₁0)
          (mul_le_mul_of_nonneg_left hGt (by positivity))
    _ = 4 * C₁ * (n + 1) * D * (q * I) + (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) * G := by ring
    _ ≤ (4 * C₁ * (n + 1) * D + 2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) + 1) *
          (q * I) + (2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2)) * (F + Θ) := by
        refine add_le_add (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hq hI)) ?_
        calc (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) * G
            ≤ (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) * (2 * (n + 1) ^ 2 * (F + Θ)) :=
              mul_le_mul_of_nonneg_left hG' hR
          _ = _ := by ring
    _ ≤ _ := by
        rw [← mul_assoc _ q I]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hF hΘ))

/-- **Mean oscillation of the Hessian at a flat boundary.** Let `H = {x | c₀ < ⟪x, ν⟫}` with
`ν ≠ 0`, let `z` lie on its boundary hyperplane, and write `B_t⁺ = B(z, t) ∩ H`. Let
`u ∈ W^{2,2}(H)` have zero boundary values, `u ∈ W^{1,2}_0(H)`, and solve
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere on `B_r⁺`. Let `A` be a constant matrix, uniformly elliptic
with constants `0 < λ ≤ Λ`, and suppose that `a` is measurable on `B_r⁺` and that
`θ(x) = ‖a(x) - A‖`, in the operator norm of the attached bilinear forms, is bounded there. Then
there is `C`, depending only on `n`, `λ` and `Λ`, such that for `0 < ρ ≤ r`

`∫_{B_ρ⁺} ‖D²u - (D²u)_{B_ρ⁺}‖² ≤ C (ρ / r)^(n + 3) ∫_{B_r⁺} ‖D²u‖²`
`  + C (∫_{B_r⁺} f² + ∫_{B_r⁺} θ² ‖D²u‖²)`.

Neither continuity nor symmetry of `a` is assumed. This is the boundary counterpart of the
interior estimate
`setIntegral_ball_norm_iteratedGradient_sub_setAverage_sq_le_of_norm_matrixBilinearForm_sub_le`.
-/
theorem exists_setIntegral_ball_inter_norm_iteratedGradient_sub_setAverage_sq_le_add
    {lam Lam : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) H 2 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      {ν z : EuclideanSpace ℝ (Fin (n + 1))} {c₀ r ρ K : ℝ},
      UniformlyEllipticOn (ball z r) (fun _ => A) lam Lam →
      AEStronglyMeasurable a (volume.restrict (ball z r ∩ H)) →
      (∀ x ∈ ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ K) → ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪z, ν⟫_ℝ = c₀ →
      Wkp.lowerOrder 1 u ∈ w1p0Submodule volume H 2 →
      (∀ᵐ x ∂volume.restrict (ball z r ∩ H), ∑ i, ∑ j, a x i j *
        ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ =
          f x) →
      0 < ρ → ρ ≤ r →
      ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x -
          ⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y‖ ^ 2 ≤
        C * (ρ / r) ^ (n + 3) * (∫ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x‖ ^ 2) +
          C * ((∫ x in ball z r ∩ H, f x ^ 2) +
            ∫ x in ball z r ∩ H, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ^ 2 *
              ‖Wkp.iteratedGradient 1 u x‖ ^ 2) := by
  obtain ⟨D, hD, hcol⟩ := exists_setIntegral_ball_inter_norm_apply_sub_setAverage_sq_le
    (n := n) (Lam := Lam) hlam
  set C₁ : ℝ := 2 * (n + 1) * (2 + 2 * (n + 1) * Lam / lam) ^ 2
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨4 * C₁ * (n + 1) * D + 2 * (n + 1) ^ 2 * (4 * C₁ * (n + 1) * D + 2 / lam ^ 2) + 1,
    by positivity, fun {H u a A f ν z c₀ r ρ K} hA ha haK hν hH hzc hu0 heq hρ hρr => ?_⟩
  have hz : z ∈ ball z r := mem_ball_self (hρ.trans_le hρr)
  have hΛ := matrixBilinearForm_opNorm_le_of_upper_bound A (hA.pos.le.trans hA.le)
    (hA.upper_bound hz)
  -- The unit normal `w` and the tangential parts `τⱼ = eⱼ - ⟪eⱼ, w⟫ w` of the coordinate vectors.
  set w := ‖ν‖⁻¹ • ν
  have hw : ‖w‖ = 1 := norm_smul_inv_norm hν
  have hAw : lam ≤ matrixBilinearForm A w w := by
    have := hA.lower_bound hz w
    rwa [← matrixBilinearForm_self, hw, one_pow, mul_one] at this
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)), ∀ j,
      τ j = EuclideanSpace.single j 1 - ⟪EuclideanSpace.single j 1, w⟫_ℝ • w := ⟨_, fun _ => rfl⟩
  have hτν : ∀ j, ⟪τ j, ν⟫_ℝ = 0 := fun j => hτ j ▸ inner_single_sub_inner_smul_eq_zero hν j
  have hτ2 : ∀ j, ‖τ j‖ ≤ 2 := fun j => hτ j ▸ norm_single_sub_inner_smul_le_two hw j
  have hts : ball z ρ ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z r ∩ H :=
    inter_subset_inter_left _ (ball_subset_ball hρr)
  have hsm : MeasurableSet (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    measurableSet_ball.inter H.isOpen.measurableSet
  have hsf : volume (ball z r ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have htf : volume (ball z ρ ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) ≠ ⊤ :=
    ((measure_mono hts).trans_lt hsf.lt_top).ne
  have hint' := setIntegral_norm_iteratedGradient_sub_setAverage_sq_le u hlam hΛ hw hAw hτ
    inter_subset_right htf
  have hq : 0 ≤ (ρ / r) ^ (n + 3) := pow_nonneg (div_nonneg hρ.le (hρ.trans_le hρr).le) _
  -- Each tangential column decays, up to the `L²` norm of `g = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`.
  have hcolj : ∀ j, ∫ x in ball z ρ ∩ H, ‖Wkp.iteratedGradient 1 u x (τ j) -
      ⨍ y in ball z ρ ∩ H, Wkp.iteratedGradient 1 u y (τ j)‖ ^ 2 ≤
      D * (ρ / r) ^ (n + 3) * (4 * ∫ x in ball z r ∩ H, ‖Wkp.iteratedGradient 1 u x‖ ^ 2) +
        D * (4 * ∫ x in ball z r ∩ H, Matrix.contraction A (Wkp.iteratedGradient 1 u x) ^ 2) :=
      fun j => by
    obtain ⟨h1, h2⟩ := setIntegral_norm_apply_sq_le_and_setIntegral_norm_smul_sq_le u A (hτ2 j)
      inter_subset_right hsm hsf
    exact (hcol hA hν hH hzc hu0 (hτν j) hρ hρr).trans (add_le_add
      (mul_le_mul_of_nonneg_left h1 (mul_nonneg hD.le hq)) (mul_le_mul_of_nonneg_left h2 hD.le))
  -- The oscillation of `g` is at most its `L²` norm, which the equation controls.
  have hGt := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sq_of_subset
    (((Matrix.contraction A).comp_memLp' (Lp.memLp (Wkp.iteratedGradient 1 u))).mono_measure
      (Measure.restrict_mono inter_subset_right le_rfl)) hts hsf
  simp only [Real.norm_eq_abs, sq_abs] at hGt
  have hG := setIntegral_contraction_iteratedGradient_sq_le hsm ha haK u inter_subset_right heq
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hcolj j
  push_cast [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  refine final_bound hC₁0 hD.le hq ?_ ?_ ?_ hint' hsum hGt hG <;>
    exact setIntegral_nonneg hsm fun _ _ => by positivity

end PDE

end TauCeti
