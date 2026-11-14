/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Immersion

/-!
# Hessian, Laplace–Beltrami operator, and polar Laplacian on the round sphere

For an ambient function `F : E → ℝ` twice differentiable at a point `p` of the unit sphere
`Sⁿ ⊂ E` (`dim E = n + 1`), the Gauss formula for the isometric immersion `Sⁿ → E` expresses the
round scalar Hessian of the restriction `F ∘ (↑)` as

`Hess_{Sⁿ}(F|_{Sⁿ})(p)(v, w) = D²F(p)(v, w) - ⟪∇F(p), p⟫ ⟪v, w⟫`,

where tangent vectors are read in `E` through the differential of the inclusion. Tracing over an
orthonormal basis of `T_p Sⁿ` extended by the unit normal `p` to an orthonormal basis of `E` gives
the ambient restriction formula for the round Laplace–Beltrami operator `Δ_{Sⁿ} = div ∘ grad`:

`Δ_{Sⁿ}(F|_{Sⁿ})(p) = Δ_E F(p) - D²F(p)(p, p) - n ⟪∇F(p), p⟫`.

When `F` is positively homogeneous of real degree `μ` along the ray `t • p` (`t > 0`), Euler's
identities `⟪∇F(p), p⟫ = μ F(p)` and `D²F(p)(p, p) = μ (μ - 1) F(p)` collapse this to

`Δ_{Sⁿ}(F|_{Sⁿ})(p) = Δ_E F(p) - μ (μ + n - 1) F(p)`.

Conversely, extending a function `f : Sⁿ → ℝ` radially to `E` by `TauCeti.sphereExtend f` yields
the polar decomposition of the Euclidean Laplacian away from `0`:

`Δ_E (y ↦ g ‖y‖ * sphereExtend f y)(x) =
  (g''(‖x‖) + n g'(‖x‖) / ‖x‖) sphereExtend f x + g(‖x‖) Δ_{Sⁿ} f (x / ‖x‖) / ‖x‖²`,

and for radial power profiles `‖y‖ ^ μ * sphereExtend f y`,

`Δ_E (y ↦ ‖y‖ ^ μ * sphereExtend f y)(x) =
  ‖x‖ ^ (μ - 2) (μ (μ + n - 1) sphereExtend f x + Δ_{Sⁿ} f (x / ‖x‖))`.

## Main results

* `TauCeti.hessian_comp_coe_sphere`, `TauCeti.hessian_inner_coe_sphere`: round Hessian of `F ∘ (↑)`
  and of linear height functions `p ↦ ⟪a, p⟫`.
* `TauCeti.laplaceBeltrami_comp_coe_sphere`, `TauCeti.laplaceBeltrami_inner_coe_sphere`: round
  Laplace–Beltrami operator of `F ∘ (↑)` and of linear height functions (`-n ⟪a, p⟫`).
* `TauCeti.laplaceBeltrami_comp_coe_sphere_of_smul`: Euler homogeneity formula
  `Δ_{Sⁿ}(F|_{Sⁿ})(p) = Δ_E F(p) - μ (μ + n - 1) F(p)`.
* `TauCeti.fderiv_sphereExtend_self`, `TauCeti.inner_gradient_sphereExtend_self`,
  `TauCeti.contDiffAt_sphereExtend`: radial derivative/gradient orthogonality and smoothness away
  from `0` of `sphereExtend f`.
* `TauCeti.laplacian_sphereExtend`, `TauCeti.laplacian_mul_sphereExtend`,
  `TauCeti.laplacian_norm_rpow_mul_sphereExtend`: polar decomposition of the Euclidean Laplacian.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 2
  and 8 (Gauss formula and the round Laplacian).
* M. E. Taylor, *Partial Differential Equations II*, 2nd ed., Springer (2011), Chapter 8, §4
  (polar coordinates and the spherical Laplacian).
-/

public section

open Bundle CovariantDerivative Filter InnerProductSpace Laplacian Metric Module Topology
open scoped ContDiff Gradient Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

/-! ### Round Hessian and Laplace–Beltrami of restricted ambient functions -/

section AmbientRestriction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

local notation "ι" => ((↑) : sphere (0 : E) 1 → E)

/-- **Round Hessian of a restricted ambient function.** For `F : E → ℝ` twice differentiable at
`p ∈ Sⁿ`, the scalar Hessian of `F ∘ (↑)` for the round metric is the ambient second derivative on
the pushforward tangent vectors minus `⟪∇ F p, p⟫` times the round metric. -/
theorem hessian_comp_coe_sphere [CompleteSpace E] {F : E → ℝ} {p : sphere (0 : E) 1}
    (hF : ContDiffAt ℝ 2 F p) (v w : TangentSpace (𝓡 n) p) :
    Manifold.hessian (𝓡 n) (F ∘ ι) p v w =
      iteratedFDeriv ℝ 2 F p ![mvfderiv (𝓡 n) ι p v, mvfderiv (𝓡 n) ι p w] -
        inner ℝ (∇ F p) (p : E) * inner ℝ v w := by
  have hf : ContMDiffAt (𝓡 n) 𝓘(ℝ) 2 (F ∘ ι) p :=
    hF.contMDiffAt.comp p (contMDiff_coe_sphere (m := 2) p)
  have hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y ↦ (⟨y, Manifold.mgradient (𝓡 n) (F ∘ ι) y⟩ :
        TangentBundle (𝓡 n) (sphere (0 : E) 1))) p :=
    (Manifold.contMDiffAt_mgradient (I := 𝓡 n) (n := 1)
      (by simpa only [one_add_one_eq_two] using hf)).mdifferentiableAt one_ne_zero
  let V := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hVp : V p = v := FiberBundle.extend_apply_self (EuclideanSpace ℝ (Fin n)) v
  have hV : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y ↦ (⟨y, V y⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) p :=
    FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have hev : (fun q : sphere (0 : E) 1 ↦ mvfderiv (𝓡 n) ι q (Manifold.mgradient (𝓡 n) (F ∘ ι) q))
      =ᶠ[𝓝 p] (fun z : E ↦ ∇ F z - inner ℝ (∇ F z) z • z) ∘ ι := by
    have hFd : ∀ᶠ z in 𝓝 (p : E), DifferentiableAt ℝ F z :=
      (hF.eventually (by simp)).mono fun z hz ↦ hz.differentiableAt (by simp)
    exact (continuous_subtype_val.continuousAt.eventually hFd).mono fun q hq ↦
      mvfderiv_coe_mgradient_comp_coe_sphere hq
  have hgrad : DifferentiableAt ℝ (∇ F) p :=
    (hF.gradient_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hc : DifferentiableAt ℝ (fun z : E ↦ inner ℝ (∇ F z) z) p :=
    hgrad.inner ℝ differentiableAt_fun_id
  have hG : HasFDerivAt (fun z : E ↦ ∇ F z - inner ℝ (∇ F z) z • z)
      (fderiv ℝ (∇ F) p - (inner ℝ (∇ F p) (p : E) • .id ℝ E +
        (fderiv ℝ (fun z : E ↦ inner ℝ (∇ F z) z) p).smulRight (p : E))) (p : E) :=
    hgrad.hasFDerivAt.sub (hc.hasFDerivAt.smul (hasFDerivAt_id (p : E)))
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ι p :=
    (contMDiff_coe_sphere (m := 1) p).mdifferentiableAt one_ne_zero
  rw [Manifold.hessian_def, ← hVp,
    (isLeviCivitaConnection_leviCivitaConnection (I := 𝓡 n)).inner_apply_eq_inner_mvfderiv
      (contMDiff_coe_sphere (m := 2) p) inner_tangentSpace_sphere hV hY,
    hVp, hev.mvfderiv_eq, mvfderiv_comp_apply_of_differentiableAt hG.differentiableAt hι, hG.fderiv]
  have hdual : inner ℝ (fderiv ℝ (∇ F) p (mvfderiv (𝓡 n) ι p v)) (mvfderiv (𝓡 n) ι p w) =
      iteratedFDeriv ℝ 2 F p ![mvfderiv (𝓡 n) ι p v, mvfderiv (𝓡 n) ι p w] := by
    have hLF : (toDual ℝ E).toContinuousLinearEquiv ∘ ∇ F = fderiv ℝ F :=
      funext fun _ ↦ toDual_gradient
    rw [iteratedFDeriv_two_apply, ← hLF, ContinuousLinearEquiv.comp_fderiv]
    rfl
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_add_left, real_inner_smul_left,
    inner_coe_mvfderiv_subtypeVal_sphere, mul_zero, add_zero, hdual, ← inner_tangentSpace_sphere]

/-- The round Hessian of the height function `q ↦ ⟪a, q⟫` at `p ∈ Sⁿ` is `-⟪a, p⟫` times the round
metric. -/
theorem hessian_inner_coe_sphere (a : E) (p : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) p) :
    Manifold.hessian (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p v w =
      -inner ℝ a (p : E) * inner ℝ v w := by
  have hX : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y ↦ (⟨y, Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) y⟩ :
        TangentBundle (𝓡 n) (sphere (0 : E) 1))) p :=
    (Manifold.contMDiff_mgradient (((innerSL ℝ a).contDiff.contMDiff.comp
      contMDiff_coe_sphere).of_le le_top) p).mdifferentiableAt one_ne_zero
  let V := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hVp : V p = v := FiberBundle.extend_apply_self (EuclideanSpace ℝ (Fin n)) v
  have hV : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun y ↦ (⟨y, V y⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1))) p :=
    FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  have heq : (fun q : sphere (0 : E) 1 ↦ mvfderiv (𝓡 n) ι q
        (Manifold.mgradient (𝓡 n) (fun y : sphere (0 : E) 1 ↦ inner ℝ a (y : E)) q)) =
      (fun z : E ↦ a - inner ℝ a z • z) ∘ ι :=
    funext fun q ↦ mvfderiv_coe_mgradient_inner_coe_sphere a q
  have hG : HasFDerivAt (fun z : E ↦ a - inner ℝ a z • z)
      (0 - (inner ℝ a (p : E) • .id ℝ E + (innerSL ℝ a).smulRight (p : E))) (p : E) :=
    (hasFDerivAt_const a (p : E)).sub (((innerSL ℝ a).hasFDerivAt).smul (hasFDerivAt_id (p : E)))
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ι p :=
    (contMDiff_coe_sphere (m := 1) p).mdifferentiableAt one_ne_zero
  rw [Manifold.hessian_def, ← hVp,
    (isLeviCivitaConnection_leviCivitaConnection (I := 𝓡 n)).inner_apply_eq_inner_mvfderiv
      (contMDiff_coe_sphere (m := 2) p) inner_tangentSpace_sphere hV hX,
    hVp, heq, mvfderiv_comp_apply_of_differentiableAt hG.differentiableAt hι, hG.fderiv]
  simp only [zero_sub, neg_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, inner_neg_left, inner_add_left, real_inner_smul_left,
    inner_coe_mvfderiv_subtypeVal_sphere, mul_zero, add_zero, ← inner_tangentSpace_sphere, neg_mul]

/-- **Round Laplace–Beltrami of a restricted ambient function.** For `F : E → ℝ` twice
differentiable at `p ∈ Sⁿ`,
`Δ_{Sⁿ}(F|_{Sⁿ})(p) = Δ_E F(p) - D²F(p)(p, p) - n ⟪∇ F p, p⟫`. -/
theorem laplaceBeltrami_comp_coe_sphere [FiniteDimensional ℝ E] {F : E → ℝ}
    {p : sphere (0 : E) 1} (hF : ContDiffAt ℝ 2 F p) :
    Manifold.laplaceBeltrami (𝓡 n) (F ∘ ι) p =
      Δ F p - iteratedFDeriv ℝ 2 F p ![p, p] - n * inner ℝ (∇ F p) (p : E) := by
  let b : OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) p) :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
      (ne_zero_of_mem_unit_sphere p)).map (sphereTangentEquiv p).symm
  set e : Fin (n + 1) → E := Fin.cons (p : E) fun i ↦ mvfderiv (𝓡 n) ι p (b i)
  have he : Orthonormal ℝ e := by
    refine ⟨Fin.cases ?_ fun i ↦ ?_, Fin.cases ?_ fun i ↦ ?_⟩
    · exact norm_eq_of_mem_sphere p
    · exact (norm_tangentSpace_sphere p (b i)).symm.trans (b.orthonormal.1 i)
    · exact Fin.cases (fun h ↦ (h rfl).elim) fun j _ ↦ inner_coe_mvfderiv_subtypeVal_sphere p (b j)
    · refine Fin.cases (fun _ ↦ ?_) fun j hij ↦ ?_
      · exact (real_inner_comm _ _).trans (inner_coe_mvfderiv_subtypeVal_sphere p (b i))
      · exact (inner_tangentSpace_sphere p (b i) (b j)).symm.trans
          (b.orthonormal.2 (Fin.succ_inj.not.1 hij))
  have hcard : Fintype.card (Fin (n + 1)) = finrank ℝ E := by
    rw [Fintype.card_fin, (Fact.out : finrank ℝ E = n + 1)]
  let B₀ := basisOfLinearIndependentOfCardEqFinrank' e he.linearIndependent hcard
  have hB₀ : ⇑B₀ = e := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  let B : OrthonormalBasis (Fin (n + 1)) ℝ E := B₀.toOrthonormalBasis (hB₀.symm ▸ he)
  have hB : ⇑B = e := (Module.Basis.coe_toOrthonormalBasis _ _).trans hB₀
  have hΔ : Δ F p = iteratedFDeriv ℝ 2 F p ![p, p] +
      ∑ i : Fin n,
        iteratedFDeriv ℝ 2 F p ![mvfderiv (𝓡 n) ι p (b i), mvfderiv (𝓡 n) ι p (b i)] := by
    rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis F B) p, hB, Fin.sum_univ_succ]
    simp only [e, Fin.cons_zero, Fin.cons_succ]
  rw [Manifold.laplaceBeltrami_eq_sum_hessian (𝓡 n) (F ∘ ι) p b]
  simp only [hessian_comp_coe_sphere hF, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one,
    one_pow, mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hΔ]
  ring

/-- The height function `q ↦ ⟪a, q⟫` on `Sⁿ` is a round Laplace–Beltrami eigenfunction with
eigenvalue `n`: `Δ_{Sⁿ}(⟪a, ·⟫)(p) = -n ⟪a, p⟫`. -/
theorem laplaceBeltrami_inner_coe_sphere (a : E) (p : sphere (0 : E) 1) :
    Manifold.laplaceBeltrami (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p =
      -(n : ℝ) * inner ℝ a (p : E) := by
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  rw [Manifold.laplaceBeltrami_eq_finrank_mul_of_hessian_eq_mul_inner
    (hessian_inner_coe_sphere a p), hdim]
  ring

/-- **Euler homogeneity reduction for the round Laplace–Beltrami operator.** If `F : E → ℝ` is `C²`
at `p ∈ Sⁿ` and satisfies `F (t • p) = t ^ μ * F p` for `t > 0`, then
`Δ_{Sⁿ}(F|_{Sⁿ})(p) = Δ_E F(p) - μ (μ + n - 1) F(p)`. -/
theorem laplaceBeltrami_comp_coe_sphere_of_smul [FiniteDimensional ℝ E] {F : E → ℝ}
    {p : sphere (0 : E) 1} {μ : ℝ} (hF : ContDiffAt ℝ 2 F p)
    (hsmul : ∀ t : ℝ, 0 < t → F (t • (p : E)) = t ^ μ * F p) :
    Manifold.laplaceBeltrami (𝓡 n) (F ∘ ι) p = Δ F p - μ * (μ + n - 1) * F p := by
  let L : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight (p : E)
  have hL1 : L 1 = (p : E) := one_smul ℝ (p : E)
  have hFd : ∀ᶠ y in 𝓝 (p : E), DifferentiableAt ℝ F y :=
    (hF.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hL_ev : ∀ᶠ t in 𝓝 (1 : ℝ), DifferentiableAt ℝ F (L t) :=
    L.continuous.continuousAt.eventually (hL1.symm ▸ hFd)
  have hd_lhs : deriv (F ∘ L) =ᶠ[𝓝 (1 : ℝ)] fun t ↦ fderiv ℝ F (L t) (p : E) :=
    hL_ev.mono fun t ht ↦ by
      simpa [L] using (ht.hasFDerivAt.comp_hasDerivAt t L.hasFDerivAt.hasDerivAt).deriv
  have hd_rhs : deriv (F ∘ L) =ᶠ[𝓝 (1 : ℝ)] fun t ↦ μ * t ^ (μ - 1) * F p := by
    have heq : F ∘ L =ᶠ[𝓝 (1 : ℝ)] fun t ↦ t ^ μ * F p :=
      Filter.eventually_of_mem (Ioi_mem_nhds zero_lt_one) fun t ht ↦ hsmul t ht
    filter_upwards [heq.deriv, Ioi_mem_nhds zero_lt_one] with t ht ht0
    rw [ht, ((Real.hasDerivAt_rpow_const (p := μ) (Or.inl ht0.ne')).mul_const (F p)).deriv]
  have h1 : inner ℝ (∇ F p) (p : E) = μ * F p := by
    have h := (hd_lhs.symm.trans hd_rhs).eq_of_nhds
    simpa [hL1, inner_gradient_left] using h
  have h2 : iteratedFDeriv ℝ 2 F p ![p, p] = μ * (μ - 1) * F p := by
    have hF' : DifferentiableAt ℝ (fderiv ℝ F) (L 1) :=
      hL1.symm ▸ (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have h2_lhs : HasDerivAt (fun t ↦ fderiv ℝ F (L t) (p : E))
        (iteratedFDeriv ℝ 2 F p ![p, p]) 1 := by
      refine ((hF'.hasFDerivAt.comp_hasDerivAt 1 L.hasFDerivAt.hasDerivAt).clm_apply
        (hasDerivAt_const 1 (p : E))).congr_deriv ?_
      simp [L, hL1, iteratedFDeriv_two_apply]
    have h2_rhs : HasDerivAt (fun t ↦ μ * t ^ (μ - 1) * F p) (μ * (μ - 1) * F p) 1 := by
      simpa [mul_assoc] using
        (((Real.hasDerivAt_rpow_const (p := μ - 1) (Or.inl one_ne_zero)).const_mul μ).mul_const
          (F p))
    exact (h2_lhs.congr_of_eventuallyEq (hd_rhs.symm.trans hd_lhs)).unique h2_rhs
  rw [laplaceBeltrami_comp_coe_sphere hF, h1, h2]
  ring

end AmbientRestriction

/-! ### Polar decomposition of the Euclidean Laplacian via `sphereExtend` -/

section PolarLaplacian

/-- The radial directional derivative of `sphereExtend f` at `x` along `x` vanishes unconditionally,
as `sphereExtend f` is constant on positive rays. -/
@[simp]
theorem fderiv_sphereExtend_self {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (f : sphere (0 : E) 1 → G) (x : E) :
    fderiv ℝ (sphereExtend f) x x = 0 := by
  rcases eq_or_ne x 0 with rfl | _
  · simp
  by_cases hd : DifferentiableAt ℝ (sphereExtend f) x
  · have hpath : HasDerivAt (fun t : ℝ ↦ t • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have h1 : HasDerivAt (sphereExtend f ∘ fun t : ℝ ↦ t • x)
        (fderiv ℝ (sphereExtend f) x x) 1 :=
      HasFDerivAt.comp_hasDerivAt 1 (by simpa only [one_smul] using hd.hasFDerivAt) hpath
    have hconst : (sphereExtend f ∘ fun t : ℝ ↦ t • x) =ᶠ[𝓝 (1 : ℝ)] fun _ ↦ sphereExtend f x :=
      Filter.eventually_of_mem (Ioi_mem_nhds zero_lt_one) fun t ht ↦
        sphereExtend_smul_of_pos f ht x
    exact h1.unique ((hasDerivAt_const (1 : ℝ) (sphereExtend f x)).congr_of_eventuallyEq hconst)
  · rw [fderiv_zero_of_not_differentiableAt hd, zero_apply]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean gradient of `sphereExtend f` is everywhere orthogonal to the position vector, with
no regularity or dimension assumptions. -/
theorem inner_gradient_sphereExtend_self [CompleteSpace E] (f : sphere (0 : E) 1 → ℝ) (x : E) :
    ⟪∇ (sphereExtend f) x, x⟫_ℝ = 0 := by
  rw [inner_gradient_left, fderiv_sphereExtend_self]

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- Away from the origin, `sphereExtend f` inherits `C^m` regularity from `f` at `x / ‖x‖`. -/
theorem contDiffAt_sphereExtend {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {m : ℕ∞ω} {f : sphere (0 : E) 1 → G} {x : E} (hx : x ≠ 0)
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, G) m f
      ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩) :
    ContDiffAt ℝ m (sphereExtend f) x := by
  let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let xU : U := ⟨x, hx⟩
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, G) m (sphereExtend f ∘ (Subtype.val : U → E)) xU := by
    refine (hf.comp xU (contMDiff_normalize_sphere xU)).congr_of_eventuallyEq ?_
    exact .of_forall fun y ↦ sphereExtend_of_ne_zero f y.2
  exact contMDiffAt_iff_contDiffAt.1 (contMDiffAt_subtype_iff.1 hcomp)

variable [FiniteDimensional ℝ E]

/-- **Euclidean Laplacian of a `0`-homogeneous radial extension.** For `x ≠ 0` and `f : Sⁿ → ℝ`
twice differentiable at `x / ‖x‖`, `Δ (sphereExtend f) x = Δ_{Sⁿ} f (x / ‖x‖) / ‖x‖²`. -/
theorem laplacian_sphereExtend {f : sphere (0 : E) 1 → ℝ} {x : E} (hx : x ≠ 0)
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ) 2 f
      ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩) :
    Δ (sphereExtend f) x =
      Manifold.laplaceBeltrami (𝓡 n) f
        ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩ /
        ‖x‖ ^ 2 := by
  set p : sphere (0 : E) 1 :=
    ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩
  have hp_eq : (⟨NormedSpace.normalize (p : E), mem_sphere_zero_iff_norm.2
      (NormedSpace.norm_normalize (ne_zero_of_mem_unit_sphere p))⟩ : sphere (0 : E) 1) = p :=
    Subtype.ext (NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere p))
  have hfp : ContMDiffAt (𝓡 n) 𝓘(ℝ) 2 f
      ⟨NormedSpace.normalize (p : E), mem_sphere_zero_iff_norm.2
        (NormedSpace.norm_normalize (ne_zero_of_mem_unit_sphere p))⟩ :=
    hp_eq.symm ▸ hf
  have hunit : Manifold.laplaceBeltrami (𝓡 n) f p = Δ (sphereExtend f) p := by
    have h := laplaceBeltrami_comp_coe_sphere_of_smul (n := n) (μ := 0)
      (contDiffAt_sphereExtend (ne_zero_of_mem_unit_sphere p) hfp)
      (fun t ht ↦ by simp [sphereExtend_smul_of_pos f ht])
    simpa [sphereExtend_comp_coe] using h
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hscale := congrFun (laplacian_comp_smul_right ‖x‖ (sphereExtend f)) p
  have hfun : (fun y : E ↦ sphereExtend f (‖x‖ • y)) = sphereExtend f :=
    funext (sphereExtend_smul_of_pos f hr)
  have hx_eq : ‖x‖ • (p : E) = x := NormedSpace.norm_smul_normalize x
  rw [hfun, hx_eq, smul_eq_mul] at hscale
  rw [hunit, hscale, mul_div_cancel_left₀ _ (pow_ne_zero 2 hr.ne')]

/-- **Polar decomposition of the Euclidean Laplacian** for a radial-angular product
`y ↦ g ‖y‖ * sphereExtend f y` away from the origin. -/
theorem laplacian_mul_sphereExtend {g : ℝ → ℝ} {f : sphere (0 : E) 1 → ℝ} {x : E} (hx : x ≠ 0)
    (hg : ContDiffAt ℝ 2 g ‖x‖)
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ) 2 f
      ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩) :
    Δ (fun y : E ↦ g ‖y‖ * sphereExtend f y) x =
      (deriv (deriv g) ‖x‖ + n * deriv g ‖x‖ / ‖x‖) * sphereExtend f x +
        g ‖x‖ * Manifold.laplaceBeltrami (𝓡 n) f
          ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩ /
          ‖x‖ ^ 2 := by
  have hgn : ContDiffAt ℝ 2 (fun y : E ↦ g ‖y‖) x := hg.comp x (contDiffAt_norm ℝ hx)
  have hfn : ContDiffAt ℝ 2 (sphereExtend f) x := contDiffAt_sphereExtend hx hf
  have horth : ⟪∇ (fun y : E ↦ g ‖y‖) x, ∇ (sphereExtend f) x⟫_ℝ = 0 := by
    rw [inner_gradient_left, show (fun y : E ↦ g ‖y‖) = g ∘ norm from rfl,
      fderiv_comp x (hg.differentiableAt (by norm_num))
        (hasFDerivAt_norm_of_ne hx).differentiableAt,
      (hasFDerivAt_norm_of_ne hx).fderiv]
    simp
  have hdim : (finrank ℝ E : ℝ) - 1 = n := by
    rw [(Fact.out : finrank ℝ E = n + 1)]
    push_cast
    ring
  rw [hgn.laplacian_fun_mul hfn, hg.laplacian_comp_norm hx, laplacian_sphereExtend hx hf, horth,
    hdim]
  ring

/-- **Polar Laplacian of a homogeneous radial-angular product** `y ↦ ‖y‖ ^ μ * sphereExtend f y`
away from the origin (`μ ∈ ℝ`). -/
theorem laplacian_norm_rpow_mul_sphereExtend (μ : ℝ) {f : sphere (0 : E) 1 → ℝ} {x : E}
    (hx : x ≠ 0)
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ) 2 f
      ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩) :
    Δ (fun y : E ↦ ‖y‖ ^ μ * sphereExtend f y) x =
      ‖x‖ ^ (μ - 2) * (μ * (μ + n - 1) * sphereExtend f x +
        Manifold.laplaceBeltrami (𝓡 n) f
          ⟨NormedSpace.normalize x,
            mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩) := by
  have hpow : ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖ ^ μ) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.2 hx)
  have hfn : ContDiffAt ℝ 2 (sphereExtend f) x := contDiffAt_sphereExtend hx hf
  have horth : ⟪∇ (fun y : E ↦ ‖y‖ ^ μ) x, ∇ (sphereExtend f) x⟫_ℝ = 0 := by
    rw [inner_gradient_left, fderiv_norm_rpow_of_ne μ hx]
    simp
  have hdim : (finrank ℝ E : ℝ) = n + 1 := by exact_mod_cast (Fact.out : finrank ℝ E = n + 1)
  have hnorm : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hrpow : ‖x‖ ^ μ / ‖x‖ ^ 2 = ‖x‖ ^ (μ - 2) := by
    rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg hnorm.le, ← Real.rpow_add hnorm]
    ring_nf
  rw [hpow.laplacian_fun_mul hfn, laplacian_norm_rpow_of_ne μ hx, laplacian_sphereExtend hx hf,
    horth, hdim, mul_div_left_comm, hrpow]
  ring

end PolarLaplacian

end TauCeti

end
