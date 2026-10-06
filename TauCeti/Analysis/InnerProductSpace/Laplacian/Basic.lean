/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Geometric invariance of the Laplacian

Mathlib's `Mathlib/Analysis/InnerProductSpace/Laplacian.lean` records that the Laplacian `Δ`
commutes with *left* composition by a continuous linear map or equivalence acting on the
*values* of a function (`ContDiffAt.laplacian_CLM_comp_left`, `laplacian_CLE_comp_left`).
This file supplies the complementary *right* composition, acting on the *domain* variable: the
geometric invariance of `Δ` under rigid motions and scalar homotheties of a Euclidean space:
affine isometry equivalences, with orthogonal changes of variable (linear isometry equivalences)
and translations as special cases, and affine homotheties with the expected quadratic scaling.

For an affine isometry equivalence `e : E ≃ᵃⁱ[ℝ] E'` and any `f : E' → F`,

`Δ (f ∘ e) = (Δ f) ∘ e`.

In particular, for a linear isometry equivalence `l : E ≃ₗᵢ[ℝ] E'`,

`Δ (f ∘ l) = (Δ f) ∘ l`,

and for a translation by `a : E`,

`Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a)`.

All three identities hold with *no* differentiability hypothesis on `f`, because the underlying
`iteratedFDeriv` composition laws are unconditional (the iterated derivative is junk-valued off
the smooth locus, yet still transforms correctly under a linear change of variable). The harmonic
corollaries, where smoothness re-enters, live in the companion files
`TauCeti/Analysis/InnerProductSpace/Harmonic/Isometry.lean` and
`TauCeti/Analysis/InnerProductSpace/Harmonic/Dilation.lean`.

The file also records the characterization `laplacian_eq_traceL` of the Laplacian as the trace of
the second Fréchet derivative and the base second-derivative computation `laplacian_norm_sq`
(`Δ ‖x‖² = 2 · dim E`), a reusable characteristic value of the Laplacian on the squared norm,
its chain-rule generalization `ContDiff.laplacian_comp_norm_sq` to radial functions
`x ↦ ρ (‖x‖²)`, the Leibniz rules `ContDiffAt.laplacian_fun_mul` and
`ContDiffAt.laplacian_fun_smul` for products with a scalar function, the companion rule
`ContDiffAt.laplacian_norm_sq` for the squared norm of a vector-valued function, and the locality
statement `tsupport_laplacian_subset` that `Δ f` vanishes wherever `f` vanishes identically.

## Main declarations

* `TauCeti.laplacian_comp_affineIsometryEquiv_right`: `Δ (f ∘ e) = (Δ f) ∘ e` for an
  affine isometry equivalence `e`.
* `TauCeti.laplacian_comp_linearIsometryEquiv_right`: `Δ (f ∘ l) = (Δ f) ∘ l` for an
  isometry `l`.
* `TauCeti.laplacian_comp_add_right`: translation invariance of `Δ`.
* `TauCeti.laplacian_comp_homothety_right`: `Δ` scales by `c ^ 2` under
  `AffineMap.homothety a c`.
* `TauCeti.laplacian_comp_smul_right`: the origin-centered homothety special case.
* `TauCeti.laplacian_eq_traceL`: the Laplacian as the trace of the second Fréchet derivative.
* `TauCeti.laplacian_norm_sq`: `Δ (fun x => ‖x‖ ^ 2) x = 2 * dim E`, the Laplacian of the
  squared norm.
* `ContDiff.laplacian_comp_norm_sq`: the Laplacian of a radial function `x ↦ ρ (‖x‖ ^ 2)` is
  `4 ‖x‖² ρ'' (‖x‖²) + 2 (dim E) ρ' (‖x‖²)`.
* `ContDiffAt.laplacian_fun_mul`: the Leibniz rule `Δ (f g) = f Δg + 2 ⟪∇f, ∇g⟫ + g Δf`.
* `ContDiffAt.laplacian_fun_smul`: its vector-valued form
  `Δ (f • g) = f • Δg + 2 Dg(∇f) + Δf • g`.
* `ContDiffAt.laplacian_norm_sq`: the Laplacian of a squared norm,
  `Δ ‖f‖² = 2 ∑ᵢ ‖Df (bᵢ)‖² + 2 ⟪f, Δf⟫` for an orthonormal basis `b`.
* `TauCeti.tsupport_laplacian_subset`: `tsupport (Δ f) ⊆ tsupport f`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Laplacian of a function is the trace of its second Fréchet derivative, expressed as a
continuous linear functional of `fderiv ℝ (fderiv ℝ f) x` in the standard orthonormal basis. -/
theorem laplacian_eq_traceL (f : E → F) (x : E) :
    Δ f x = (∑ i, (ContinuousLinearMap.apply ℝ F (stdOrthonormalBasis ℝ E i)).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) (stdOrthonormalBasis ℝ E i)))
        (fderiv ℝ (fderiv ℝ f) x) := by
  simp [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- Scalar dilation as a continuous linear equivalence. -/
private noncomputable abbrev smulLeftContinuousLinearEquiv (c : ℝ) (hc : c ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The iterated derivative transforms under a linear isometry equivalence on the right by
pulling the directions through the isometry. This is the unconditional engine behind the
geometric invariance of the Laplacian. -/
private theorem iteratedFDeriv_comp_linearIsometryEquiv_apply (l : E ≃ₗᵢ[ℝ] E') (f : E' → F)
    (i : ℕ) (x : E) (m : Fin i → E) :
    iteratedFDeriv ℝ i (f ∘ l) x m = iteratedFDeriv ℝ i f (l x) (fun j ↦ l (m j)) := by
  have h := l.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := x) (Set.mem_univ _) i
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [← LinearIsometryEquiv.coe_toContinuousLinearEquiv l]
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- **Geometric invariance of the Laplacian under isometries.** For a linear isometry
equivalence `l`, the Laplacian commutes with right composition by `l`:
`Δ (f ∘ l) = (Δ f) ∘ l`. No differentiability hypothesis is needed. -/
theorem laplacian_comp_linearIsometryEquiv_right (l : E ≃ₗᵢ[ℝ] E') (f : E' → F) :
    Δ (f ∘ l) = (Δ f) ∘ l := by
  ext x
  simp only [Function.comp_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l) (stdOrthonormalBasis ℝ E),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map l)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_linearIsometryEquiv_apply l f 2 x]
  congr 1
  funext j
  fin_cases j <;> simp [OrthonormalBasis.map_apply]

/-- **Translation invariance of the Laplacian.** Shifting the argument by a constant `a`
commutes with the Laplacian: `Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a)`. No
differentiability hypothesis is needed. -/
theorem laplacian_comp_add_right (f : E → F) (a : E) :
    Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a) := by
  ext x
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_add_right']

/-- **Geometric invariance of the Laplacian under affine isometries.** For an affine isometry
equivalence `e`, the Laplacian commutes with right composition by `e`:
`Δ (f ∘ e) = (Δ f) ∘ e`. No differentiability hypothesis is needed. -/
theorem laplacian_comp_affineIsometryEquiv_right (e : E ≃ᵃⁱ[ℝ] E') (f : E' → F) :
    Δ (f ∘ e) = (Δ f) ∘ e := by
  have hcomp : f ∘ e = (fun y ↦ f (y + e 0)) ∘ e.linearIsometryEquiv := by
    funext x
    have hx : e x = e.linearIsometryEquiv x + e 0 := by
      simpa using e.map_vadd (0 : E) x
    simp [Function.comp_apply, hx]
  rw [hcomp, laplacian_comp_linearIsometryEquiv_right e.linearIsometryEquiv
      (fun y ↦ f (y + e 0)),
    laplacian_comp_add_right f (e 0)]
  ext x
  have hx : e x = e.linearIsometryEquiv x + e 0 := by
    simpa using e.map_vadd (0 : E) x
  simp [Function.comp_apply, hx]

/-- **Scaling law for the Laplacian under origin-centered dilation.**

Right-composition by `x ↦ c • x` multiplies the Laplacian by `c ^ 2`. The statement is
unconditional in `f`, matching Mathlib's unconditional definition of `Δ` through iterated
Fréchet derivatives. -/
theorem laplacian_comp_smul_right (c : ℝ) (f : E → F) :
    Δ (fun x ↦ f (c • x)) = fun x ↦ c ^ 2 • (Δ f) (c • x) := by
  by_cases hc : c = 0
  · subst c
    ext x
    simp
  · let l : E ≃L[ℝ] E := smulLeftContinuousLinearEquiv c hc
    have hfun : (fun x : E ↦ f (c • x)) = f ∘ l := by
      funext x
      simp [l, smulLeftContinuousLinearEquiv]
    rw [hfun]
    ext x
    simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l)
      (stdOrthonormalBasis ℝ E), laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (stdOrthonormalBasis ℝ E), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hder :
        (iteratedFDeriv ℝ 2 (f ∘ l) x)
            ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] =
          ((iteratedFDeriv ℝ 2 f (l x)).compContinuousLinearMap fun _ => (l : E →L[ℝ] E))
            ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i] := by
      have h := l.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (l x)) 2
      simpa [← iteratedFDerivWithin_univ, Set.preimage_univ] using
        congrArg
          (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F =>
            L ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]) h
    rw [hder]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hx : l x = c • x := by
      simp [l, smulLeftContinuousLinearEquiv]
    rw [hx]
    let M := iteratedFDeriv ℝ 2 f (c • x)
    let v : Fin 2 → E := ![(stdOrthonormalBasis ℝ E) i, (stdOrthonormalBasis ℝ E) i]
    -- `compContinuousLinearMap_apply` exposes the two derivative directions as `fun j ↦ c • v j`;
    -- `map_smul_univ` then pulls the two scalar factors out of the bilinear map.
    change M (fun j => c • v j) = c ^ 2 • M v
    simpa [M, v, pow_two] using M.map_smul_univ (fun _ : Fin 2 => c) v

/-- **Scaling law for the Laplacian under a homothety.**

Right-composition by `AffineMap.homothety a c` multiplies the Laplacian by `c ^ 2`. -/
theorem laplacian_comp_homothety_right (a : E) (c : ℝ) (f : E → F) :
    Δ (fun x ↦ f (AffineMap.homothety a c x)) =
      fun x ↦ c ^ 2 • (Δ f) (AffineMap.homothety a c x) := by
  have hfun : (fun x : E ↦ f (AffineMap.homothety a c x)) =
      fun x ↦ (fun z ↦ f (c • z + a)) (x + -a) := by
    funext x
    simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, sub_eq_add_neg, add_comm]
  rw [hfun, laplacian_comp_add_right (fun z ↦ f (c • z + a)) (-a)]
  rw [laplacian_comp_smul_right c (fun z ↦ f (z + a))]
  rw [laplacian_comp_add_right f a]
  ext x
  simp [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, sub_eq_add_neg, add_comm]

/-- The Laplacian of the squared norm on a finite-dimensional real inner product space is twice
the dimension. -/
@[simp]
theorem laplacian_norm_sq (x : E) :
    Δ (fun y : E => ‖y‖ ^ 2) x = 2 * (Module.finrank ℝ E : ℝ) := by
  -- The Hessian of `‖·‖²` is the constant bilinear map `2 • innerSL ℝ`.
  have hsnd : fderiv ℝ (fderiv ℝ fun y : E => ‖y‖ ^ 2) x
      = (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) := by
    rw [fderiv_norm_sq]
    exact (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).fderiv
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y : E => ‖y‖ ^ 2)
    (stdOrthonormalBasis ℝ E)) x]
  -- Each orthonormal diagonal Hessian entry equals `2`.
  have hterm : ∀ i, iteratedFDeriv ℝ 2 (fun y : E => ‖y‖ ^ 2) x
      ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i] = 2 := by
    intro i
    have hself : (innerSL ℝ (stdOrthonormalBasis ℝ E i)) (stdOrthonormalBasis ℝ E i) = (1 : ℝ) := by
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq,
        (stdOrthonormalBasis ℝ E).orthonormal.norm_eq_one i, one_pow]
    rw [iteratedFDeriv_two_apply, hsnd]
    simp [hself]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- **The Laplacian of a radial function.** For a `C²` function `ρ : ℝ → ℝ`, the Laplacian of
`x ↦ ρ (‖x‖ ^ 2)` is `4 ‖x‖² ρ'' (‖x‖²) + 2 (dim E) ρ' (‖x‖²)`. -/
@[simp]
theorem _root_.ContDiff.laplacian_comp_norm_sq {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (x : E) :
    Δ (fun y : E => ρ (‖y‖ ^ 2)) x =
      4 * ‖x‖ ^ 2 * deriv (deriv ρ) (‖x‖ ^ 2) +
        2 * (Module.finrank ℝ E : ℝ) * deriv ρ (‖x‖ ^ 2) := by
  have hρ1 : ContDiff ℝ 1 (deriv ρ) := hρ.deriv'
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hρ'd : Differentiable ℝ (deriv ρ) := hρ1.differentiable one_ne_zero
  -- The first derivative, by the chain rule through the squared norm.
  have hfst : fderiv ℝ (fun y : E => ρ (‖y‖ ^ 2)) =
      fun y => deriv ρ (‖y‖ ^ 2) • (2 • innerSL ℝ y) := by
    funext y
    exact ((hρd _).hasDerivAt.comp_hasFDerivAt y
      (hasStrictFDerivAt_norm_sq y).hasFDerivAt).fderiv
  -- The second derivative, by the product rule for `c • f` with `c = ρ' ∘ ‖·‖²`.
  have hc : DifferentiableAt ℝ (fun y : E => deriv ρ (‖y‖ ^ 2)) x :=
    ((hρ'd _).hasDerivAt.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt)
      |>.differentiableAt
  have hcd : fderiv ℝ (fun y : E => deriv ρ (‖y‖ ^ 2)) x =
      deriv (deriv ρ) (‖x‖ ^ 2) • (2 • innerSL ℝ x) :=
    ((hρ'd _).hasDerivAt.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt).fderiv
  have hi : DifferentiableAt ℝ (fun y : E => (2 • innerSL ℝ y : E →L[ℝ] ℝ)) x :=
    (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).differentiableAt
  have hid : fderiv ℝ (fun y : E => (2 • innerSL ℝ y : E →L[ℝ] ℝ)) x =
      (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) :=
    (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).fderiv
  set b := stdOrthonormalBasis ℝ E
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y : E => ρ (‖y‖ ^ 2)) b) x]
  have hterm : ∀ i, iteratedFDeriv ℝ 2 (fun y : E => ρ (‖y‖ ^ 2)) x ![b i, b i] =
      4 * deriv (deriv ρ) (‖x‖ ^ 2) * ⟪x, b i⟫_ℝ ^ 2 + 2 * deriv ρ (‖x‖ ^ 2) := by
    intro i
    rw [iteratedFDeriv_two_apply, hfst, fderiv_fun_smul hc hi, hcd, hid]
    have hself : (innerSL ℝ (b i)) (b i) = (1 : ℝ) := by
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
    simp [hself]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.mul_sum,
    b.sum_sq_inner_left x]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

open Filter Gradient Topology in
/-- **The Leibniz rule for the Laplacian.** For scalar functions twice differentiable at `x`,
`Δ (f g) = f Δg + 2 ⟪∇f, ∇g⟫ + g Δf` at `x`. -/
theorem _root_.ContDiffAt.laplacian_fun_mul {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun y ↦ f y * g y) x = f x * Δ g x + 2 * ⟪∇ f x, ∇ g x⟫_ℝ + g x * Δ f x := by
  have hfd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hfg : fderiv ℝ (fun y ↦ f y * g y) =ᶠ[𝓝 x]
      fun y ↦ f y • fderiv ℝ g y + g y • fderiv ℝ f y := by
    filter_upwards [hfd, hgd] with y hfy hgy
    exact fderiv_mul hfy hgy
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg' : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- Each diagonal Hessian entry of the product, by differentiating the product rule once more.
  have hterm : ∀ v, iteratedFDeriv ℝ 2 (fun y ↦ f y * g y) x ![v, v] =
      f x * iteratedFDeriv ℝ 2 g x ![v, v] + 2 * (fderiv ℝ f x v * fderiv ℝ g x v) +
        g x * iteratedFDeriv ℝ 2 f x ![v, v] := by
    intro v
    have h1 : DifferentiableAt ℝ (fun y ↦ f y • fderiv ℝ g y) x := hfd.self_of_nhds.smul hg'
    have h2 : DifferentiableAt ℝ (fun y ↦ g y • fderiv ℝ f y) x := hgd.self_of_nhds.smul hf'
    rw [iteratedFDeriv_two_apply, hfg.fderiv_eq, fderiv_fun_add h1 h2,
      fderiv_fun_smul hfd.self_of_nhds hg', fderiv_fun_smul hgd.self_of_nhds hf',
      iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  set b := stdOrthonormalBasis ℝ E
  -- The mixed first-order terms assemble into the inner product of the gradients.
  have hgrad : ⟪∇ f x, ∇ g x⟫_ℝ = ∑ i, fderiv ℝ f x (b i) * fderiv ℝ g x (b i) := by
    rw [← b.sum_inner_mul_inner (∇ f x) (∇ g x)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_gradient_left, real_inner_comm, inner_gradient_left]
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ b) x,
    congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f b) x,
    congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis g b) x, hgrad]
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]

open Gradient in
/-- **The Leibniz rule for the Laplacian**, vector-valued form.  For a scalar function `f` and a
vector-valued function `g`, both twice differentiable at `x`,
`Δ (f • g) = f • Δg + 2 • Dg(∇f) + Δf • g` at `x`. -/
theorem _root_.ContDiffAt.laplacian_fun_smul {f : E → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    Δ (fun y ↦ f y • g y) x = f x • Δ g x + (2 : ℝ) • fderiv ℝ g x (∇ f x) + Δ f x • g x := by
  -- Test both sides against continuous linear functionals, reducing to the scalar rule.
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ ↦ ?_
  have hℓg : ContDiffAt ℝ 2 (ℓ ∘ g) x := ℓ.contDiff.contDiffAt.comp x hg
  have hcomp : ⇑ℓ ∘ (fun y ↦ f y • g y) = fun y ↦ f y * (ℓ ∘ g) y := by
    funext y
    simp
  have hd : fderiv ℝ (ℓ ∘ g) x = ℓ.comp (fderiv ℝ g x) :=
    (ℓ.hasFDerivAt.comp x (hg.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hfg : ContDiffAt ℝ 2 (fun y ↦ f y • g y) x := hf.smul hg
  have h := hfg.laplacian_CLM_comp_left (l := ℓ)
  rw [hcomp, hf.laplacian_fun_mul hℓg, hg.laplacian_CLM_comp_left, inner_gradient_right,
    conj_trivial, hd] at h
  rw [← Function.comp_apply (f := ℓ), ← h]
  simp only [Function.comp_apply, map_add, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply]
  ring

open Topology in
/-- **The Laplacian of a squared norm.** For a function `f` with values in a real inner product
space, twice differentiable at `x`, and any orthonormal basis `b` of `E`,
`Δ ‖f‖² = 2 ∑ᵢ ‖Df (bᵢ)‖² + 2 ⟪f, Δf⟫` at `x`. The first term does not depend on `b`: it is
twice the squared Hilbert--Schmidt norm of `Df x`. -/
theorem _root_.ContDiffAt.laplacian_norm_sq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] {f : E → G} {x : E} (hf : ContDiffAt ℝ 2 f x) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    Δ (fun y ↦ ‖f y‖ ^ 2) x = 2 * ∑ i, ‖fderiv ℝ f x (b i)‖ ^ 2 + 2 * ⟪f x, Δ f x⟫_ℝ := by
  have hfd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hw : DifferentiableAt ℝ (fderiv ℝ fun y ↦ ‖f y‖ ^ 2) x :=
    ((hf.norm_sq ℝ).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- Each diagonal Hessian entry, by differentiating `D ‖f‖² · v = 2 ⟪f, Df v⟫` once more.
  have hterm : ∀ v, iteratedFDeriv ℝ 2 (fun y ↦ ‖f y‖ ^ 2) x ![v, v] =
      2 * ‖fderiv ℝ f x v‖ ^ 2 + 2 * ⟪f x, iteratedFDeriv ℝ 2 f x ![v, v]⟫_ℝ := by
    intro v
    have hd : (fun y ↦ fderiv ℝ (fun y ↦ ‖f y‖ ^ 2) y v) =ᶠ[𝓝 x]
        fun y ↦ 2 * ⟪f y, fderiv ℝ f y v⟫_ℝ := by
      filter_upwards [hfd] with y hy
      rw [hy.hasFDerivAt.norm_sq.fderiv]
      simp
    have hv : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y v) x :=
      hf'.clm_apply (differentiableAt_const v)
    have hsnd : fderiv ℝ (fderiv ℝ fun y ↦ ‖f y‖ ^ 2) x v v =
        fderiv ℝ (fun y ↦ fderiv ℝ (fun y ↦ ‖f y‖ ^ 2) y v) x v := by
      rw [fderiv_clm_apply hw (differentiableAt_const v)]
      simp
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hsnd, hd.fderiv_eq, fderiv_const_mul (hfd.self_of_nhds.inner ℝ hv), smul_apply,
      fderiv_inner_apply ℝ hfd.self_of_nhds hv, fderiv_clm_apply hf' (differentiableAt_const v)]
    simp
    ring
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ b) x,
    congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f b) x]
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, inner_sum]

open Topology in
/-- The Laplacian vanishes wherever the function vanishes identically: `Δ` is local. -/
theorem tsupport_laplacian_subset (f : E → F) : tsupport (Δ f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  by_contra hxf
  have h0 : Δ f =ᶠ[𝓝 x] Δ (fun _ : E => (0 : F)) :=
    laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hxf)
  exact hx (by simpa using h0.eq_of_nhds)

end TauCeti
