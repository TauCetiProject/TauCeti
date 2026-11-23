/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.InnerProductSpace.OrthogonalLast
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Immersion

/-!
# Hessian, Laplace–Beltrami operator, and polar Laplacian on the round sphere

For an ambient function `F : E → ℝ` that is `C²` at a point `p` of the unit sphere `Sⁿ ⊂ E`
(`dim E = n + 1`), the Gauss formula for the isometric immersion `Sⁿ → E` expresses the round scalar
Hessian of the restriction `F ∘ (↑)` as

`Hess_{Sⁿ}(F|_{Sⁿ})(p)(v, w) = D²F(p)(v, w) - ⟪∇F(p), p⟫ ⟪v, w⟫`,

where tangent vectors are read in `E` through the differential of the inclusion. Tracing over an
orthonormal basis of `T_p Sⁿ` extended by the unit normal `p` to an orthonormal basis of `E` gives
the ambient restriction formula for the round Laplace–Beltrami operator `Δ_{Sⁿ} = div ∘ grad`:

`Δ_{Sⁿ}(F|_{Sⁿ})(p) = Δ_E F(p) - D²F(p)(p, p) - n ⟪∇F(p), p⟫`.

When `F` is positively homogeneous of real degree `μ` along the ray `t • p` near `t = 1`, Euler's
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
* `TauCeti.laplacian_sphereExtend`, `TauCeti.laplacian_comp_norm_mul_sphereExtend`,
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

/-- **Round Hessian of a restricted ambient function.** For `F : E → ℝ` that is `C²` at `p ∈ Sⁿ`,
the scalar Hessian of `F ∘ (↑)` for the round metric is the ambient second derivative on the
pushforward tangent vectors minus `⟪∇ F p, p⟫` times the round metric. -/
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
    exact (continuous_subtypeVal.continuousAt.eventually hFd).mono fun q hq ↦
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
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, inner_add_left, real_inner_smul_left,
    inner_coe_mvfderiv_subtypeVal_sphere, mul_zero, add_zero, inner_fderiv_gradient,
    ← inner_tangentSpace_sphere]

/-- The round Hessian of the height function `q ↦ ⟪a, q⟫` at `p ∈ Sⁿ` is `-⟪a, p⟫` times the round
metric. -/
theorem hessian_inner_coe_sphere (a : E) (p : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) p) :
    Manifold.hessian (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p v w =
      -inner ℝ a (p : E) * inner ℝ v w := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  have hfn : (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) = (innerSL ℝ a) ∘ ι :=
    funext fun q ↦ (innerSL_apply_apply ℝ a (q : E)).symm
  rw [hfn, hessian_comp_coe_sphere (innerSL ℝ a).contDiff.contDiffAt,
    (innerSL ℝ a).iteratedFDeriv_add_two 0 (p : E)]
  simp

/-- **Round Laplace–Beltrami of a restricted ambient function.** For `F : E → ℝ` that is `C²` at
`p ∈ Sⁿ`, `Δ_{Sⁿ}(F|_{Sⁿ})(p) = Δ_E F(p) - D²F(p)(p, p) - n ⟪∇ F p, p⟫`. -/
theorem laplaceBeltrami_comp_coe_sphere [FiniteDimensional ℝ E] {F : E → ℝ}
    {p : sphere (0 : E) 1} (hF : ContDiffAt ℝ 2 F p) :
    Manifold.laplaceBeltrami (𝓡 n) (F ∘ ι) p =
      Δ F p - iteratedFDeriv ℝ 2 F p ![p, p] - n * inner ℝ (∇ F p) (p : E) := by
  have hcard : finrank ℝ E = Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin, (Fact.out : finrank ℝ E = n + 1)]
  have hv : Orthonormal ℝ (({Fin.last n} : Set (Fin (n + 1))).domRestrict fun _ ↦ (p : E)) :=
    ⟨fun _ ↦ norm_eq_of_mem_sphere p, fun x y hxy ↦
      (hxy (Subtype.ext ((Set.mem_singleton_iff.1 x.property).trans
        (Set.mem_singleton_iff.1 y.property).symm))).elim⟩
  obtain ⟨B, hB⟩ := hv.exists_orthonormalBasis_extension_of_card_eq hcard
  have hBlast : B (Fin.last n) = (p : E) := hB (Fin.last n) rfl
  let b : OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) p) :=
    (B.orthogonalLast.map (.ofEq _ _ (by rw [hBlast]))).map (sphereTangentEquiv p).symm
  have hb (i : Fin n) : mvfderiv (𝓡 n) ι p (b i) = B i.castSucc := by
    rw [mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv]
    simp [b]
  have hΔ : Δ F p = iteratedFDeriv ℝ 2 F p ![p, p] +
      ∑ i : Fin n,
        iteratedFDeriv ℝ 2 F p ![mvfderiv (𝓡 n) ι p (b i), mvfderiv (𝓡 n) ι p (b i)] := by
    rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis F B) p, Fin.sum_univ_castSucc,
      hBlast, add_comm]
    simp only [hb]
  rw [Manifold.laplaceBeltrami_eq_sum_hessian (𝓡 n) (F ∘ ι) p b]
  simp only [hessian_comp_coe_sphere hF, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one,
    one_pow, mul_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hΔ]
  ring

/-- The height function `q ↦ ⟪a, q⟫` on `Sⁿ` is a round Laplace–Beltrami eigenfunction with
eigenvalue `-n`: `Δ_{Sⁿ}(⟪a, ·⟫)(p) = -n ⟪a, p⟫`. -/
theorem laplaceBeltrami_inner_coe_sphere (a : E) (p : sphere (0 : E) 1) :
    Manifold.laplaceBeltrami (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p =
      -(n : ℝ) * inner ℝ a (p : E) := by
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  rw [Manifold.laplaceBeltrami_eq_finrank_mul_of_hessian_eq_mul_inner
    (hessian_inner_coe_sphere a p), hdim]
  ring

/-- **Euler homogeneity reduction for the round Laplace–Beltrami operator.** If `F : E → ℝ` is `C²`
at `p ∈ Sⁿ` and satisfies `F (t • p) = t ^ μ * F p` for `t` near `1`, then
`Δ_{Sⁿ}(F|_{Sⁿ})(p) = Δ_E F(p) - μ (μ + n - 1) F(p)`. -/
theorem laplaceBeltrami_comp_coe_sphere_of_smul [FiniteDimensional ℝ E] {F : E → ℝ}
    {p : sphere (0 : E) 1} {μ : ℝ} (hF : ContDiffAt ℝ 2 F p)
    (hsmul : (fun t : ℝ ↦ F (t • (p : E))) =ᶠ[𝓝 (1 : ℝ)] fun t ↦ t ^ μ * F p) :
    Manifold.laplaceBeltrami (𝓡 n) (F ∘ ι) p = Δ F p - μ * (μ + n - 1) * F p := by
  have hhom : (fun t : ℝ ↦ F (t • (p : E))) =ᶠ[𝓝 (1 : ℝ)] fun t ↦ t ^ μ • F p := by
    simpa only [smul_eq_mul] using hsmul
  have hFd : ∀ᶠ t in 𝓝 (1 : ℝ), DifferentiableAt ℝ F (t • (p : E)) := by
    have hF_ev : ∀ᶠ y in 𝓝 (p : E), DifferentiableAt ℝ F y :=
      (hF.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
    have hcont : ContinuousAt (fun t : ℝ ↦ t • (p : E)) 1 :=
      continuous_id.continuousAt.smul continuousAt_const
    exact hcont.eventually (by simpa only [one_smul] using hF_ev)
  have h1 : inner ℝ (∇ F p) (p : E) = μ * F p := by
    rw [inner_gradient_left]
    simpa using (hF.differentiableAt (by simp)).hasFDerivAt.apply_self_eq_smul_of_eventuallyEq
      (Real.hasDerivAt_rpow_const (p := μ) (Or.inl one_ne_zero)) hhom
  have h2 : iteratedFDeriv ℝ 2 F p ![p, p] = μ * (μ - 1) * F p := by
    have hF' : DifferentiableAt ℝ (fderiv ℝ F) p :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have hw : ∀ᶠ t in 𝓝 (1 : ℝ), HasDerivAt (fun s : ℝ ↦ s ^ μ) (μ * t ^ (μ - 1)) t :=
      Filter.eventually_of_mem (Ioi_mem_nhds zero_lt_one) fun t ht ↦
        Real.hasDerivAt_rpow_const (p := μ) (Or.inl ht.ne')
    have hw' : HasDerivAt (fun t : ℝ ↦ μ * t ^ (μ - 1)) (μ * (μ - 1)) 1 := by
      simpa using (Real.hasDerivAt_rpow_const (p := μ - 1) (Or.inl one_ne_zero)).const_mul μ
    simpa [smul_eq_mul] using
      iteratedFDeriv_two_self_eq_smul_of_eventuallyEq hFd hF' hw hw' hhom
  rw [laplaceBeltrami_comp_coe_sphere hF, h1, h2]
  ring

end AmbientRestriction

/-! ### Polar decomposition of the Euclidean Laplacian via `sphereExtend` -/

section PolarLaplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] [FiniteDimensional ℝ E]

/-- **Euclidean Laplacian of a `0`-homogeneous radial extension.** For `x ≠ 0` and `f : Sⁿ → ℝ`
that is `C²` at `x / ‖x‖`, `Δ (sphereExtend f) x = Δ_{Sⁿ} f (x / ‖x‖) / ‖x‖²`. -/
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
      (Filter.eventually_of_mem (Ioi_mem_nhds zero_lt_one) fun t ht ↦ by
        simp [sphereExtend_smul_of_pos f ht])
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
theorem laplacian_comp_norm_mul_sphereExtend {g : ℝ → ℝ} {f : sphere (0 : E) 1 → ℝ} {x : E}
    (hx : x ≠ 0) (hg : ContDiffAt ℝ 2 g ‖x‖)
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
    rw [inner_gradient_left,
      fderiv_fun_comp x (hg.differentiableAt (by norm_num))
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
  have hnorm : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hg : ContDiffAt ℝ 2 (fun r : ℝ ↦ r ^ μ) ‖x‖ :=
    contDiffAt_id.rpow_const_of_ne hnorm.ne'
  have hrad : deriv (deriv (fun r : ℝ ↦ r ^ μ)) ‖x‖ +
      n * deriv (fun r : ℝ ↦ r ^ μ) ‖x‖ / ‖x‖ = μ * (μ + n - 1) * ‖x‖ ^ (μ - 2) := by
    have h := (hg.laplacian_comp_norm hx).symm.trans (laplacian_norm_rpow_of_ne μ hx)
    rw [(Fact.out : finrank ℝ E = n + 1)] at h
    push_cast at h
    rw [add_sub_cancel_right] at h
    rw [h]
    ring
  have hrpow : ‖x‖ ^ μ / ‖x‖ ^ 2 = ‖x‖ ^ (μ - 2) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hnorm]
  rw [laplacian_comp_norm_mul_sphereExtend hx hg hf, hrad, mul_div_right_comm, hrpow]
  ring

end PolarLaplacian

end TauCeti

end
