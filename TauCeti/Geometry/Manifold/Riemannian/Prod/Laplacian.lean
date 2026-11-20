/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Prod
import TauCeti.Geometry.Manifold.ContMDiff.Defs

/-!
# The Laplace–Beltrami operator of a product metric

Give `M × N` the product of Riemannian metrics on `M` and `N`. For a function `u` on `M × N`
which is `C²` at `p = (x, y)`, this file shows that its Hessian, on tangent vectors of one
factor, is the Hessian of the corresponding slice of `u`:

`Hess u ((v, 0), (w, 0)) = Hess (u(·, y)) (v, w)`,

`Hess u ((0, v), (0, w)) = Hess (u(x, ·)) (v, w)`,

and that the Laplace–Beltrami operator `Δ = div ∘ grad` of the product splits as the sum of the
Laplacians of the two slices:

`Δ u (x, y) = Δ (u(·, y)) x + Δ (u(x, ·)) y`.

So `Δ_{M × N} = Δ_M ⊗ 1 + 1 ⊗ Δ_N`, with no condition on the factors beyond the regularity of
their metrics. In particular a product of functions `f(x) g(y)` has Laplacian
`(Δ f) g + f (Δ g)`, and a product of eigenfunctions is an eigenfunction whose eigenvalue is the
sum of the two eigenvalues: on a flat torus `S¹ × S¹`, `cos(kx) cos(ly)` satisfies
`Δ u = -(k² + l²) u`. That such products exhaust the spectrum of a closed product is a
completeness statement about eigenbases, which is not proved here. Since the rough Laplacian
of the flat connection on the trivial line bundle is `-Δ`
(`CovariantDerivative.roughLaplacian_trivial`), the splitting is also the identity
`∇*∇_{M × N} = ∇*∇_M ⊗ 1 + 1 ⊗ ∇*∇_N` for trivial line bundles.

The Hessian is computed on product vector fields: the Levi-Civita connection of the product
metric differentiates a field `(Y, 0)` along `(X, 0)` as the Levi-Civita connection of `M`
(`TauCeti.Manifold.leviCivitaConnection_prodVectorField`), and the derivative of a function on
`M × N` along a vector `(v, 0)` is the derivative of its slice
(`MDifferentiableAt.mvfderiv_prod_eq_apply_of_snd_eq_zero`). The Laplacian is the trace of the
Hessian in the orthonormal basis of the product tangent space obtained from orthonormal bases of
the factors.

## Main results

* `TauCeti.Manifold.hessian_prod_mk_zero`, `TauCeti.Manifold.hessian_prod_zero_mk`: the Hessian of
  a function on a product, on vectors tangent to one factor.
* `TauCeti.Manifold.laplaceBeltrami_prod`: the Laplacian of a product metric is the sum of the
  Laplacians of the slices.
* `TauCeti.Manifold.laplaceBeltrami_prod_mul`: the Laplacian of `f(x) g(y)` is
  `(Δ f)(x) g(y) + f(x) (Δ g)(y)`.
* `TauCeti.Manifold.laplaceBeltrami_prod_mul_of_eq_neg_mul`: a product of eigenfunctions with
  eigenvalues `λ` and `μ` is an eigenfunction with eigenvalue `λ + μ`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the divergence and the Laplacian), Chapter 4 (the covariant Hessian, Example 4.22) and
  Chapter 5 (the Levi-Civita connection).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold TauCeti

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {u : M × N → ℝ} {p : M × N}

variable
  [FiniteDimensional ℝ E] [IsManifold I 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  [FiniteDimensional ℝ F] [IsManifold J 2 N] [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

/-- **The Hessian of a function on a product, on vectors tangent to the first factor**, is the
Hessian of its slice through `p`: `Hess u ((v, 0), (w, 0)) = Hess (u(·, p.2)) (v, w)`. -/
theorem hessian_prod_mk_zero (hu : ContMDiffAt (I.prod J) 𝓘(ℝ) 2 u p)
    (v w : TangentSpace I p.1) :
    hessian (I.prod J) u p ((v, 0) : TangentSpace I p.1 × TangentSpace J p.2)
        ((w, 0) : TangentSpace I p.1 × TangentSpace J p.2) =
      hessian I (fun x ↦ u (x, p.2)) p.1 v w := by
  set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
  set Y : Π x : M, TangentSpace I x := FiberBundle.extend E w
  set Z : Π y : N, TangentSpace J y := fun _ ↦ 0
  have hY : MDiffAt (T% Y) p.1 := FiberBundle.mdifferentiableAt_extend I E w
  have hZ : MDiffAt (T% Z) p.2 :=
    (contMDiff_zeroSection ℝ (TangentSpace J : N → Type _) (n := 1)).mdifferentiableAt one_ne_zero
  have hYZ := mdifferentiableAt_prodVectorField (X := Y) (Y := Z) hY hZ
  have hslice : ContMDiffAt I 𝓘(ℝ) 2 (fun x ↦ u (x, p.2)) p.1 :=
    hu.comp_of_eq (contMDiffAt_id.prodMk contMDiffAt_const) rfl
  have hV : prodVectorField X Z p = ((v, 0) : TangentSpace I p.1 × TangentSpace J p.2) :=
    Prod.ext ((prodVectorField_fst X Z p).trans (FiberBundle.extend_apply_self E v))
      (prodVectorField_snd X Z p)
  have hW : prodVectorField Y Z p = ((w, 0) : TangentSpace I p.1 × TangentSpace J p.2) :=
    Prod.ext ((prodVectorField_fst Y Z p).trans (FiberBundle.extend_apply_self E w))
      (prodVectorField_snd Y Z p)
  have hud : MDiffAt u p := hu.mdifferentiableAt two_ne_zero
  -- The second factor of a field `(X', Z)` is the zero field `Z`.
  have hZ₀ (X' : Π x : M, TangentSpace I x) (q : M × N) :
      (prodVectorField X' Z q).2 = (0 : TangentSpace J q.2) :=
    prodVectorField_snd X' Z q
  rw [← hV, ← hW, hessian_apply_eq_mvfderiv_sub p hu _ _ hYZ,
    ← FiberBundle.extend_apply_self E v, ← FiberBundle.extend_apply_self E w,
    hessian_apply_eq_mvfderiv_sub p.1 hslice X Y hY]
  congr 1
  · -- The derivative of `q ↦ du_q (Y q.1, 0)` along `(X p.1, 0)` only sees the slice through `p`.
    rw [(mdifferentiableAt_mvfderiv_apply hu le_rfl hYZ).mvfderiv_prod_eq_apply_of_snd_eq_zero
        (hZ₀ X p),
      prodVectorField_fst]
    refine congrArg (fun φ : TangentSpace I p.1 →L[ℝ] ℝ ↦ φ (X p.1))
      (Filter.EventuallyEq.mvfderiv_eq ?_)
    filter_upwards [((Continuous.prodMk_left p.2).tendsto p.1).eventually
      (hu.eventually_mdifferentiableAt two_ne_zero)] with x hx
    rw [hx.mvfderiv_prod_eq_apply_of_snd_eq_zero (hZ₀ Y _), prodVectorField_fst]
  · rw [leviCivitaConnection_prodVectorField hY hZ, hud.mvfderiv_prod_eq_add_apply,
      prodVectorField_snd, prodVectorField_fst]
    -- The second factor contributes `∇_0 0 = 0`.
    rw [show Z p.2 = 0 from rfl, map_zero, map_zero, add_zero]

/-- **The Hessian of a function on a product, on vectors tangent to the second factor**, is the
Hessian of its slice through `p`: `Hess u ((0, v), (0, w)) = Hess (u(p.1, ·)) (v, w)`. -/
theorem hessian_prod_zero_mk (hu : ContMDiffAt (I.prod J) 𝓘(ℝ) 2 u p)
    (v w : TangentSpace J p.2) :
    hessian (I.prod J) u p ((0, v) : TangentSpace I p.1 × TangentSpace J p.2)
        ((0, w) : TangentSpace I p.1 × TangentSpace J p.2) =
      hessian J (fun y ↦ u (p.1, y)) p.2 v w := by
  set X : Π y : N, TangentSpace J y := FiberBundle.extend F v
  set Y : Π y : N, TangentSpace J y := FiberBundle.extend F w
  set Z : Π x : M, TangentSpace I x := fun _ ↦ 0
  have hY : MDiffAt (T% Y) p.2 := FiberBundle.mdifferentiableAt_extend J F w
  have hZ : MDiffAt (T% Z) p.1 :=
    (contMDiff_zeroSection ℝ (TangentSpace I : M → Type _) (n := 1)).mdifferentiableAt one_ne_zero
  have hZY := mdifferentiableAt_prodVectorField (X := Z) (Y := Y) hZ hY
  have hslice : ContMDiffAt J 𝓘(ℝ) 2 (fun y ↦ u (p.1, y)) p.2 :=
    hu.comp_of_eq (contMDiffAt_const.prodMk contMDiffAt_id) rfl
  have hV : prodVectorField Z X p = ((0, v) : TangentSpace I p.1 × TangentSpace J p.2) :=
    Prod.ext (prodVectorField_fst Z X p)
      ((prodVectorField_snd Z X p).trans (FiberBundle.extend_apply_self F v))
  have hW : prodVectorField Z Y p = ((0, w) : TangentSpace I p.1 × TangentSpace J p.2) :=
    Prod.ext (prodVectorField_fst Z Y p)
      ((prodVectorField_snd Z Y p).trans (FiberBundle.extend_apply_self F w))
  have hud : MDiffAt u p := hu.mdifferentiableAt two_ne_zero
  -- The first factor of a field `(Z, X')` is the zero field `Z`.
  have hZ₀ (X' : Π y : N, TangentSpace J y) (q : M × N) :
      (prodVectorField Z X' q).1 = (0 : TangentSpace I q.1) :=
    prodVectorField_fst Z X' q
  rw [← hV, ← hW, hessian_apply_eq_mvfderiv_sub p hu _ _ hZY,
    ← FiberBundle.extend_apply_self F v, ← FiberBundle.extend_apply_self F w,
    hessian_apply_eq_mvfderiv_sub p.2 hslice X Y hY]
  congr 1
  · -- The derivative of `q ↦ du_q (0, Y q.2)` along `(0, X p.2)` only sees the slice through `p`.
    rw [(mdifferentiableAt_mvfderiv_apply hu le_rfl hZY).mvfderiv_prod_eq_apply_of_fst_eq_zero
        (hZ₀ X p),
      prodVectorField_snd]
    refine congrArg (fun φ : TangentSpace J p.2 →L[ℝ] ℝ ↦ φ (X p.2))
      (Filter.EventuallyEq.mvfderiv_eq ?_)
    filter_upwards [((Continuous.prodMk_right p.1).tendsto p.2).eventually
      (hu.eventually_mdifferentiableAt two_ne_zero)] with y hy
    rw [hy.mvfderiv_prod_eq_apply_of_fst_eq_zero (hZ₀ Y _), prodVectorField_snd]
  · rw [leviCivitaConnection_prodVectorField hZ hY, hud.mvfderiv_prod_eq_add_apply,
      prodVectorField_snd, prodVectorField_fst]
    -- The first factor contributes `∇_0 0 = 0`.
    rw [show Z p.1 = 0 from rfl, map_zero, map_zero, zero_add]

/-- **The Laplace–Beltrami operator of a product metric** is the sum of the Laplacians of the two
slices through the point: `Δ u (x, y) = Δ (u(·, y)) x + Δ (u(x, ·)) y`. -/
theorem laplaceBeltrami_prod (hu : ContMDiffAt (I.prod J) 𝓘(ℝ) 2 u p) :
    laplaceBeltrami (I.prod J) u p =
      laplaceBeltrami I (fun x ↦ u (x, p.2)) p.1 + laplaceBeltrami J (fun y ↦ u (p.1, y)) p.2 := by
  -- Orthonormal bases of the factors combine into an orthonormal basis of the product, whose
  -- vectors lie in one factor each.
  let b₁ := stdOrthonormalBasis ℝ (TangentSpace I p.1)
  let b₂ := stdOrthonormalBasis ℝ (TangentSpace J p.2)
  rw [laplaceBeltrami_eq_sum_hessian _ u p
      ((b₁.prod b₂).map (tangentSpaceProdLinearIsometryEquiv p).symm),
    laplaceBeltrami_eq_sum_hessian _ _ p.1 b₁, laplaceBeltrami_eq_sum_hessian _ _ p.2 b₂,
    Fintype.sum_sum_type]
  simp only [OrthonormalBasis.map_apply, tangentSpaceProdLinearIsometryEquiv_symm_apply,
    OrthonormalBasis.prod_apply, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
    LinearMap.inl_apply, LinearMap.inr_apply, tangentSpaceProdEquiv_symm_apply,
    hessian_prod_mk_zero hu, hessian_prod_zero_mk hu]

/-- **The Laplacian of a product of functions** on a product metric is
`Δ (f ⊗ g) = (Δ f) ⊗ g + f ⊗ (Δ g)`. -/
theorem laplaceBeltrami_prod_mul {f : M → ℝ} {g : N → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f p.1)
    (hg : ContMDiffAt J 𝓘(ℝ) 2 g p.2) :
    laplaceBeltrami (I.prod J) (fun q ↦ f q.1 * g q.2) p =
      laplaceBeltrami I f p.1 * g p.2 + f p.1 * laplaceBeltrami J g p.2 := by
  rw [laplaceBeltrami_prod (u := fun q ↦ f q.1 * g q.2)
    ((hf.comp p contMDiffAt_fst).mul (hg.comp p contMDiffAt_snd))]
  have h₁ : (fun x ↦ f x * g p.2) = g p.2 • f :=
    funext fun x ↦ by rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have h₂ : (fun y ↦ f p.1 * g y) = f p.1 • g :=
    funext fun y ↦ by rw [Pi.smul_apply, smul_eq_mul]
  rw [h₁, h₂, laplaceBeltrami_smul_of_contMDiffAt I _ hf,
    laplaceBeltrami_smul_of_contMDiffAt J _ hg, mul_comm (g p.2)]

/-- **Products of eigenfunctions** on a product metric are eigenfunctions, with the sum of the
eigenvalues: if `Δ f = -λ f` and `Δ g = -μ g`, then `Δ (f ⊗ g) = -(λ + μ) (f ⊗ g)`. -/
theorem laplaceBeltrami_prod_mul_of_eq_neg_mul {f : M → ℝ} {g : N → ℝ} {lam mu : ℝ}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f p.1) (hg : ContMDiffAt J 𝓘(ℝ) 2 g p.2)
    (hfeig : laplaceBeltrami I f p.1 = -lam * f p.1)
    (hgeig : laplaceBeltrami J g p.2 = -mu * g p.2) :
    laplaceBeltrami (I.prod J) (fun q ↦ f q.1 * g q.2) p = -(lam + mu) * (f p.1 * g p.2) := by
  rw [laplaceBeltrami_prod_mul hf hg, hfeig, hgeig]
  ring

end TauCeti.Manifold
