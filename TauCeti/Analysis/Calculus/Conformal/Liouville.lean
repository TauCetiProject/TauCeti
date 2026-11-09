/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Conformal.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.KulkarniNomizu
import TauCeti.Geometry.Euclidean.Inversion

/-!
# Liouville's theorem on conformal maps

Let `E` and `F` be real inner product spaces of the same finite dimension `n ≥ 3`, and let
`f : E → F` be a `C³` map which is conformal at every point of a connected open set `U`. Then `f`
is the restriction to `U` of a Möbius transformation: either a similarity
`x ↦ r • A x + a`, or a similarity composed with the inversion `EuclideanGeometry.inversion b 1`
in the unit sphere about a point `b ∉ U`
(`TauCeti.exists_eq_smul_linearIsometry_add_or_inversion_of_conformalAt`). This fails in
dimension `2`, where every holomorphic map with nonvanishing derivative is conformal.

## The argument

Write the conformality of `f` on `U` through the *reciprocal conformal factor* `ρ > 0`:

`ρ(x)² ⟪Df(x) u, Df(x) v⟫ = ⟪u, v⟫`.

Differentiating this identity and solving for the second derivative (the Koszul formula) gives, in
every dimension,

`ρ D²f(u, v) = Df(⟪u, v⟫ ∇ρ - ⟪∇ρ, u⟫ v - ⟪∇ρ, v⟫ u)`

(`TauCeti.smul_fderiv_fderiv_apply_eq_of_inner_fderiv`): the vector inside `Df` is `ρ` times the
Christoffel symbols of the metric `ρ⁻² ⟪·, ·⟫`, which `f` carries isometrically to a flat one.
Differentiating once more and using the symmetry of `D³f` shows that the Kulkarni–Nomizu product
of `B = ρ Hess ρ - (‖∇ρ‖² / 2) ⟪·, ·⟫` with the inner product vanishes, which is the flatness of
that metric. In dimension at least `3` this forces
`B = 0` (`LinearMap.BilinForm.kulkarniNomizu_innerₗ_eq_zero_iff`), that is

`ρ Hess ρ = (‖∇ρ‖² / 2) id`

(`TauCeti.smul_fderiv_gradient_eq_of_inner_fderiv`). The function `‖∇ρ‖² / (2 ρ)` then has zero
derivative, so `Hess ρ` is a constant multiple `σ` of the identity and `ρ` is a quadratic
polynomial. Positivity of `ρ` and the relation `‖∇ρ‖² = 2 σ ρ` leave two cases: `ρ` is constant,
or `ρ = (σ / 2) ‖x - b‖²` with `σ > 0` and `b ∉ U`
(`TauCeti.eq_const_or_eq_mul_norm_sub_sq_of_inner_fderiv`). A constant `ρ` makes `D²f` vanish, so
`f` is a similarity (`TauCeti.exists_eq_smul_linearIsometry_add_of_inner_fderiv`). In the second
case `f ∘ inversion b 1` has constant reciprocal conformal factor `σ / 2`, hence is a similarity
(`TauCeti.exists_eq_smul_linearIsometry_inversion_add_of_inner_fderiv`).

The `C³` hypothesis is what the argument needs: it uses the third derivative of `f`. The theorem
holds for `C¹` maps by a regularity argument (Hartman), which is not formalized here.

## Main results

* `TauCeti.smul_fderiv_fderiv_apply_eq_of_inner_fderiv`: the second derivative of a conformal map
  in terms of the gradient of its reciprocal conformal factor.
* `TauCeti.smul_fderiv_gradient_eq_of_inner_fderiv`: in dimension at least `3` the reciprocal
  conformal factor satisfies `ρ Hess ρ = (‖∇ρ‖² / 2) id`.
* `TauCeti.eq_const_or_eq_mul_norm_sub_sq_of_inner_fderiv`: hence on a connected open set it is
  either constant or `(σ / 2) ‖x - b‖²`.
* `TauCeti.exists_eq_smul_linearIsometry_add_of_inner_fderiv`: a conformal map with constant
  conformal factor on a connected open set is a similarity.
* `TauCeti.exists_eq_smul_linearIsometry_inversion_add_of_inner_fderiv`: a conformal map with
  reciprocal conformal factor `(σ / 2) ‖x - b‖²` is a similarity composed with an inversion.
* `TauCeti.exists_eq_smul_linearIsometry_add_or_inversion_of_conformalAt`: Liouville's theorem.

## References

* P. Hartman, *On isometries and on a theorem of Liouville*, Math. Z. 69 (1958), 202–210.
* D. E. Blair, *Inversion Theory and Conformal Mapping*, Student Mathematical Library 9,
  American Mathematical Society (2000).
-/

public section

open Filter Topology InnerProductSpace
open scoped RealInnerProductSpace Gradient

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → F} {ρ : E → ℝ} {U : Set E}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The reciprocal conformal factor is the reciprocal of the length of the image of any unit
vector. -/
private theorem eq_inv_norm_fderiv_apply
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    (hρ0 : ∀ x ∈ U, 0 < ρ x) {x : E} (hx : x ∈ U) {e : E} (he : ‖e‖ = 1) :
    ρ x = ‖fderiv ℝ f x e‖⁻¹ := by
  have h := hρ x hx e e
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, he, one_pow, ← mul_pow] at h
  have h1 : ρ x * ‖fderiv ℝ f x e‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (mul_nonneg (hρ0 x hx).le (norm_nonneg _)) two_ne_zero).1 h
  exact eq_inv_of_mul_eq_one_left h1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The reciprocal conformal factor of a `C^(m + 1)` map is `C^m`. -/
private theorem contDiffOn_of_inner_fderiv [Nontrivial E] {m : ℕ}
    (hf : ContDiffOn ℝ (m + 1) f U) (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    (hρ0 : ∀ x ∈ U, 0 < ρ x) : ContDiffOn ℝ m ρ U := by
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  have hne : ∀ x ∈ U, fderiv ℝ f x e ≠ 0 := fun x hx h0 ↦ by
    have := hρ x hx e e
    rw [h0, inner_zero_left, mul_zero, real_inner_self_eq_norm_sq, he] at this
    norm_num at this
  have hd : ContDiffOn ℝ m (fun y ↦ fderiv ℝ f y e) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  refine ContDiffOn.congr (fun x hx ↦ ?_) (fun x hx ↦ eq_inv_norm_fderiv_apply hρ hρ0 hx he)
  exact (((contDiffAt_norm ℝ (hne x hx)).comp x ((hd x hx).contDiffAt (hU.mem_nhds hx))).inv
    (norm_ne_zero_iff.2 (hne x hx))).contDiffWithinAt

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A map whose derivative scales inner products by a nonzero factor has injective derivative. -/
private theorem injective_fderiv_of_inner
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    {x : E} (hx : x ∈ U) : Function.Injective (fderiv ℝ f x) := fun a b hab ↦ by
  have := hρ x hx (a - b) (a - b)
  rw [map_sub, hab, sub_self, inner_zero_left, mul_zero] at this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this.symm)

omit [FiniteDimensional ℝ F] in
/-- The derivative of `ρ² ⟪Df u, Df v⟫ = ⟪u, v⟫` in the direction `w`. -/
private theorem inner_fderiv_fderiv_add_eq_zero (hf : ContDiffOn ℝ 2 f U) (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    {x : E} (hx : x ∈ U) (hρx : DifferentiableAt ℝ ρ x) (u v w : E) :
    2 * ρ x * ⟪∇ ρ x, w⟫ * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ +
      ρ x ^ 2 * (⟪fderiv ℝ (fderiv ℝ f) x w u, fderiv ℝ f x v⟫ +
        ⟪fderiv ℝ (fderiv ℝ f) x w v, fderiv ℝ f x u⟫) = 0 := by
  have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt (hU.mem_nhds hx)
  have hρg : HasFDerivAt ρ (toDual ℝ E (∇ ρ x)) x :=
    hasGradientAt_iff_hasFDerivAt.1 hρx.hasGradientAt
  have hd := (hρg.pow 2).mul ((hfx.hasFDerivAt_fderiv_apply le_rfl u).inner ℝ
    (hfx.hasFDerivAt_fderiv_apply le_rfl v))
  have hc : HasFDerivAt (fun y ↦ ρ y ^ 2 * ⟪fderiv ℝ f y u, fderiv ℝ f y v⟫) (0 : E →L[ℝ] ℝ) x :=
    (hasFDerivAt_const ⟪u, v⟫ x).congr_of_eventuallyEq
      (eventually_of_mem (hU.mem_nhds hx) fun y hy ↦ hρ y hy u v)
  have := congrArg (fun L : E →L[ℝ] ℝ ↦ L w) (hd.unique hc)
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.flip_apply, toDual_apply_apply,
    smul_eq_mul, nsmul_eq_mul, zero_apply] at this
  rw [real_inner_comm (fderiv ℝ (fderiv ℝ f) x w v)] at this
  linear_combination this

/-- **The second derivative of a conformal map.** Let `f` be `C²` on an open set `U`, between
spaces of the same finite dimension, with `ρ(x)² ⟪Df(x) u, Df(x) v⟫ = ⟪u, v⟫` for a positive
function `ρ` (the reciprocal of the conformal factor). Then
`ρ D²f(u, v) = Df(⟪u, v⟫ ∇ρ - ⟪∇ρ, u⟫ v - ⟪∇ρ, v⟫ u)`: the vector inside `Df` is `ρ` times the
Christoffel symbols of the metric `ρ⁻² ⟪·, ·⟫`. This holds in every dimension. -/
theorem smul_fderiv_fderiv_apply_eq_of_inner_fderiv
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) (hf : ContDiffOn ℝ 2 f U) (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    (hρ0 : ∀ x ∈ U, 0 < ρ x) {x : E} (hx : x ∈ U) (u v : E) :
    ρ x • fderiv ℝ (fderiv ℝ f) x u v =
      fderiv ℝ f x (⟪u, v⟫ • ∇ ρ x - ⟪∇ ρ x, u⟫ • v - ⟪∇ ρ x, v⟫ • u) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim u 0, Subsingleton.elim v 0]
  have hρx : DifferentiableAt ℝ ρ x :=
    ((contDiffOn_of_inner_fderiv (m := 1) hf hU hρ hρ0).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
  have hs : ∀ a b, fderiv ℝ (fderiv ℝ f) x a b = fderiv ℝ (fderiv ℝ f) x b a :=
    (hf.contDiffAt (hU.mem_nhds hx)).isSymmSndFDerivAt (by simp)
  have hsurj : Function.Surjective (fderiv ℝ f x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hEF
      (f := (fderiv ℝ f x : E →ₗ[ℝ] F))).1 (injective_fderiv_of_inner hρ hx)
  rw [← sub_eq_zero]
  set X := ρ x • fderiv ℝ (fderiv ℝ f) x u v -
      fderiv ℝ f x (⟪u, v⟫ • ∇ ρ x - ⟪∇ ρ x, u⟫ • v - ⟪∇ ρ x, v⟫ • u) with hX
  obtain ⟨z, hz⟩ := hsurj X
  -- The Koszul formula: three instances of the differentiated identity determine `⟪D²f u v, Df z⟫`.
  have Eu := inner_fderiv_fderiv_add_eq_zero hf hU hρ hx hρx v z u
  have Ev := inner_fderiv_fderiv_add_eq_zero hf hU hρ hx hρx u z v
  have Ez := inner_fderiv_fderiv_add_eq_zero hf hU hρ hx hρx u v z
  rw [hs v u] at Ev
  rw [hs z u, hs z v] at Ez
  have h1 := hρ x hx (∇ ρ x) z
  have h2 := hρ x hx u v
  have key : ρ x ^ 2 * ⟪X, fderiv ℝ f x z⟫ = 0 := by
    simp only [hX, inner_sub_left, inner_smul_left, map_sub, map_smul, RCLike.conj_to_real]
    linear_combination (ρ x / 2) * (Eu + Ev - Ez) - ⟪u, v⟫ * h1 + ⟪∇ ρ x, z⟫ * h2
  rw [hz] at key
  exact inner_self_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (by have := hρ0 x hx; positivity))

/-- The derivative of the identity `smul_fderiv_fderiv_apply_eq_of_inner_fderiv` in the
direction `w`, for a `C³` map. -/
private theorem smul_fderiv_fderiv_fderiv_apply (hEF : Module.finrank ℝ E = Module.finrank ℝ F)
    (hf : ContDiffOn ℝ 3 f U) (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    (hρ0 : ∀ x ∈ U, 0 < ρ x) [Nontrivial E] {x : E} (hx : x ∈ U) (u v w : E) :
    ⟪∇ ρ x, w⟫ • fderiv ℝ (fderiv ℝ f) x u v +
        ρ x • fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x w u v =
      fderiv ℝ (fderiv ℝ f) x w (⟪u, v⟫ • ∇ ρ x - ⟪∇ ρ x, u⟫ • v - ⟪∇ ρ x, v⟫ • u) +
        fderiv ℝ f x (⟪u, v⟫ • fderiv ℝ (∇ ρ) x w - ⟪fderiv ℝ (∇ ρ) x w, u⟫ • v -
          ⟪fderiv ℝ (∇ ρ) x w, v⟫ • u) := by
  have hfx : ContDiffAt ℝ 3 f x := hf.contDiffAt (hU.mem_nhds hx)
  have hρc : ContDiffAt ℝ 2 ρ x :=
    (contDiffOn_of_inner_fderiv (m := 2) hf hU hρ hρ0).contDiffAt (hU.mem_nhds hx)
  have hρg : HasFDerivAt ρ (toDual ℝ E (∇ ρ x)) x :=
    hasGradientAt_iff_hasFDerivAt.1 (hρc.differentiableAt (by simp)).hasGradientAt
  have hg : HasFDerivAt (∇ ρ) (fderiv ℝ (∇ ρ) x) x :=
    ((hρc.gradient_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  have hD1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    hfx.hasFDerivAt_fderiv (by norm_num)
  have hD2 : HasFDerivAt (fderiv ℝ (fderiv ℝ f)) (fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) x :=
    (hfx.fderiv_right (m := 2) (by norm_num)).hasFDerivAt_fderiv le_rfl
  have hK := ((hg.const_smul ⟪u, v⟫).sub ((hg.inner ℝ (hasFDerivAt_const u x)).smul_const v)).sub
    ((hg.inner ℝ (hasFDerivAt_const v x)).smul_const u)
  have hΦ := (hρg.smul ((hD2.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x))).sub (hD1.clm_apply hK)
  have hc : HasFDerivAt (fun y ↦ ρ y • fderiv ℝ (fderiv ℝ f) y u v -
      fderiv ℝ f y (⟪u, v⟫ • ∇ ρ y - ⟪∇ ρ y, u⟫ • v - ⟪∇ ρ y, v⟫ • u)) (0 : E →L[ℝ] F) x :=
    (hasFDerivAt_const 0 x).congr_of_eventuallyEq
      (eventually_of_mem (hU.mem_nhds hx) fun y hy ↦ sub_eq_zero.2
        (smul_fderiv_fderiv_apply_eq_of_inner_fderiv hEF (hf.of_le (by norm_num)) hU hρ hρ0
          hy u v))
  have := congrArg (fun L : E →L[ℝ] F ↦ L w) (hΦ.unique hc)
  simp only [ContinuousLinearMap.comp_zero, zero_add, toDual_gradient,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
    inner_gradient_left, Pi.sub_apply, Pi.smul_apply, map_sub, map_smul, sub_apply, add_apply,
    smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, zero_apply,
    fderivInnerCLM_apply, inner_zero_right] at this
  simp only [map_sub, map_smul, inner_gradient_left]
  linear_combination (norm := module) this

/-- The vector `⟪a, b⟫ • g - ⟪g, a⟫ • b - ⟪g, b⟫ • a`, which is `Df⁻¹ (ρ D²f(a, b))` for
`g = ∇ρ`. -/
private def christoffel (g a b : E) : E := ⟪a, b⟫ • g - ⟪g, a⟫ • b - ⟪g, b⟫ • a

omit [FiniteDimensional ℝ E] in
/-- The antisymmetrized derivative of the Christoffel symbols, paired with `z`, is minus the
Kulkarni–Nomizu product of `B = p ⟪G ·, ·⟫ - (‖g‖² / 2) ⟪·, ·⟫` with the inner product. -/
private theorem inner_christoffel_sub_eq_neg_kulkarniNomizu (G : E →L[ℝ] E) (g u v w z : E)
    (p : ℝ) (hG : ⟪G w, u⟫ = ⟪G u, w⟫) :
    ⟪(christoffel g w (christoffel g u v) + p • christoffel (G w) u v -
        ⟪g, w⟫ • christoffel g u v) -
      (christoffel g u (christoffel g w v) + p • christoffel (G u) w v -
        ⟪g, u⟫ • christoffel g w v), z⟫ =
    -LinearMap.BilinForm.kulkarniNomizu (p • (innerₗ E).comp (G : E →ₗ[ℝ] E) -
      (‖g‖ ^ 2 / 2) • innerₗ E) (innerₗ E) w u z v := by
  simp only [christoffel, inner_sub_left, inner_sub_right, inner_add_left, inner_smul_left,
    inner_smul_right, LinearMap.BilinForm.kulkarniNomizu_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, innerₗ_apply_apply, ContinuousLinearMap.coe_coe,
    smul_eq_mul, RCLike.conj_to_real, real_inner_self_eq_norm_sq, hG]
  simp only [real_inner_comm]
  ring

/-- Multiplying `smul_fderiv_fderiv_fderiv_apply` by `ρ` expresses `ρ² D³f(w, u, v)` as `Df` of a
vector built from `∇ρ` and `Hess ρ`. Since `D³f` is symmetric in `w` and `u` and `Df` is injective,
that vector is symmetric in `w` and `u`. -/
private theorem christoffel_comm [Nontrivial E] (hEF : Module.finrank ℝ E = Module.finrank ℝ F)
    (hf : ContDiffOn ℝ 3 f U) (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    (hρ0 : ∀ x ∈ U, 0 < ρ x) {x : E} (hx : x ∈ U) (w u v : E) :
    christoffel (∇ ρ x) w (christoffel (∇ ρ x) u v) +
        ρ x • christoffel (fderiv ℝ (∇ ρ) x w) u v - ⟪∇ ρ x, w⟫ • christoffel (∇ ρ x) u v =
      christoffel (∇ ρ x) u (christoffel (∇ ρ x) w v) +
        ρ x • christoffel (fderiv ℝ (∇ ρ) x u) w v - ⟪∇ ρ x, u⟫ • christoffel (∇ ρ x) w v := by
  have h2 : ∀ u v, ρ x • fderiv ℝ (fderiv ℝ f) x u v =
      fderiv ℝ f x (christoffel (∇ ρ x) u v) :=
    fun u v ↦ smul_fderiv_fderiv_apply_eq_of_inner_fderiv hEF (hf.of_le (by norm_num)) hU hρ hρ0
      hx u v
  have hD : ∀ w u v, (ρ x * ρ x) • fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x w u v =
      fderiv ℝ f x (christoffel (∇ ρ x) w (christoffel (∇ ρ x) u v) +
        ρ x • christoffel (fderiv ℝ (∇ ρ) x w) u v - ⟪∇ ρ x, w⟫ • christoffel (∇ ρ x) u v) := by
    intro w u v
    have h3 := smul_fderiv_fderiv_fderiv_apply hEF hf hU hρ hρ0 hx u v w
    have h2a := h2 u v
    have h2b := h2 w (christoffel (∇ ρ x) u v)
    simp only [christoffel, map_add, map_sub, map_smul] at h3 h2a h2b ⊢
    linear_combination (norm := module) ρ x • h3 - ⟪∇ ρ x, w⟫ • h2a + h2b
  have hD3 : fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x w u v =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x u w v :=
    congrArg (fun L : E →L[ℝ] F ↦ L v)
      (((hf.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 2) le_rfl).isSymmSndFDerivAt
        (by simp) w u)
  apply injective_fderiv_of_inner hρ hx
  rw [← hD, ← hD, hD3]

/-- **The Hessian equation of the reciprocal conformal factor.** Let `f` be `C³` on an open set
`U` between spaces of the same finite dimension `n ≥ 3`, with `ρ(x)² ⟪Df(x) u, Df(x) v⟫ = ⟪u, v⟫`
for a positive function `ρ`. Then `ρ Hess ρ = (‖∇ρ‖² / 2) id` on `U`. This is the flatness of the
metric `ρ⁻² ⟪·, ·⟫`; it fails in dimension `2`. -/
theorem smul_fderiv_gradient_eq_of_inner_fderiv (hE : 3 ≤ Module.finrank ℝ E)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) (hf : ContDiffOn ℝ 3 f U) (hU : IsOpen U)
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    (hρ0 : ∀ x ∈ U, 0 < ρ x) {x : E} (hx : x ∈ U) :
    ρ x • fderiv ℝ (∇ ρ) x = (‖∇ ρ x‖ ^ 2 / 2) • ContinuousLinearMap.id ℝ E := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  have hρc : ContDiffAt ℝ 2 ρ x :=
    (contDiffOn_of_inner_fderiv (m := 2) hf hU hρ hρ0).contDiffAt (hU.mem_nhds hx)
  have hGs : ∀ a b, ⟪fderiv ℝ (∇ ρ) x a, b⟫ = ⟪fderiv ℝ (∇ ρ) x b, a⟫ := by
    have := isSymmetric_of_hasFDerivAt_gradient
      ((hρc.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp))
      ((hρc.gradient_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
    intro a b
    have h := this a b
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [h, real_inner_comm]
  -- The Kulkarni–Nomizu product of `B = ρ Hess ρ - (‖∇ρ‖² / 2) ⟪·, ·⟫` with `⟪·, ·⟫` vanishes.
  have hB : LinearMap.BilinForm.kulkarniNomizu
      (ρ x • (innerₗ E).comp (fderiv ℝ (∇ ρ) x : E →ₗ[ℝ] E) - (‖∇ ρ x‖ ^ 2 / 2) • innerₗ E)
      (innerₗ E) = 0 := by
    ext w u z v
    have := inner_christoffel_sub_eq_neg_kulkarniNomizu (fderiv ℝ (∇ ρ) x) (∇ ρ x) u v w z (ρ x)
      (hGs w u)
    rw [christoffel_comm hEF hf hU hρ hρ0 hx w u v, sub_self, inner_zero_left] at this
    simpa using (neg_eq_zero.1 this.symm)
  have hB0 := (LinearMap.BilinForm.kulkarniNomizu_innerₗ_eq_zero_iff hE).1 hB
  ext a
  refine ext_inner_right ℝ fun b ↦ ?_
  have := congrArg (fun B : LinearMap.BilinForm ℝ E ↦ B a b) hB0
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    innerₗ_apply_apply, ContinuousLinearMap.coe_coe, smul_eq_mul, LinearMap.zero_apply] at this
  simp only [smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left]
  linarith

/-- On a connected open set, the Hessian of the reciprocal conformal factor is a constant
multiple `σ` of the identity, and `‖∇ρ‖² = 2 σ ρ`. -/
private theorem exists_fderiv_gradient_eq_smul_id (hE : 3 ≤ Module.finrank ℝ E)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F)
    (hf : ContDiffOn ℝ 3 f U) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    (hρ0 : ∀ x ∈ U, 0 < ρ x) :
    ∃ σ : ℝ, ∀ x ∈ U, fderiv ℝ (∇ ρ) x = σ • ContinuousLinearMap.id ℝ E ∧
      ‖∇ ρ x‖ ^ 2 = 2 * σ * ρ x := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  have hρc : ContDiffOn ℝ 2 ρ U := contDiffOn_of_inner_fderiv (m := 2) hf hU hρ hρ0
  have hloc : ∀ x ∈ U, HasFDerivAt ρ (toDual ℝ E (∇ ρ x)) x ∧
      HasFDerivAt (∇ ρ) (fderiv ℝ (∇ ρ) x) x := fun x hx ↦ by
    have hc := hρc.contDiffAt (hU.mem_nhds hx)
    exact ⟨hasGradientAt_iff_hasFDerivAt.1 (hc.differentiableAt (by simp)).hasGradientAt,
      ((hc.gradient_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt⟩
  have hG : ∀ x ∈ U,
      fderiv ℝ (∇ ρ) x = (‖∇ ρ x‖ ^ 2 / (2 * ρ x)) • ContinuousLinearMap.id ℝ E :=
    fun x hx ↦ by
      have h := smul_fderiv_gradient_eq_of_inner_fderiv hE hEF hf hU hρ hρ0 hx
      have hp := (hρ0 x hx).ne'
      rw [← inv_smul_smul₀ hp (fderiv ℝ (∇ ρ) x), h, smul_smul]
      congr 1
      field_simp
  -- `‖∇ρ‖² / (2ρ)` has zero derivative: `D‖∇ρ‖² = 2 ⟪∇ρ, Hess ρ ·⟫ = (‖∇ρ‖² / ρ) Dρ`.
  have hσ : ∀ x ∈ U, HasFDerivAt (fun y ↦ ‖∇ ρ y‖ ^ 2 * (2 * ρ y)⁻¹) (0 : E →L[ℝ] ℝ) x :=
    fun x hx ↦ by
      obtain ⟨h1, h2⟩ := hloc x hx
      have hp := (hρ0 x hx).ne'
      refine (h2.norm_sq.mul ((hasDerivAt_inv (by positivity)).comp_hasFDerivAt x
        (h1.const_mul 2))).congr_fderiv ?_
      ext w
      rw [hG x hx]
      simp
      field_simp
      ring
  obtain ⟨σ, hσc⟩ := hU.exists_is_const_of_fderiv_eq_zero hU'
    (fun x hx ↦ (hσ x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hσ x hx).fderiv)
  refine ⟨σ, fun x hx ↦ ⟨by rw [hG x hx, div_eq_mul_inv, hσc x hx], ?_⟩⟩
  have := hσc x hx
  have hp := (hρ0 x hx).ne'
  field_simp at this
  linarith

/-- **The reciprocal conformal factor is constant or a multiple of `‖x - b‖²`.** Under the
hypotheses of `smul_fderiv_gradient_eq_of_inner_fderiv`, on a connected open set `U` the
reciprocal conformal factor `ρ` is either constant, or equal to `(σ / 2) ‖x - b‖²` for some
`σ > 0` and some point `b ∉ U`. -/
theorem eq_const_or_eq_mul_norm_sub_sq_of_inner_fderiv (hE : 3 ≤ Module.finrank ℝ E)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F)
    (hf : ContDiffOn ℝ 3 f U) (hU : IsOpen U) (hU' : IsConnected U)
    (hρ : ∀ x ∈ U, ∀ u v, ρ x ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫)
    (hρ0 : ∀ x ∈ U, 0 < ρ x) :
    (∃ c, ∀ x ∈ U, ρ x = c) ∨ ∃ σ, 0 < σ ∧ ∃ b ∉ U, ∀ x ∈ U, ρ x = σ / 2 * ‖x - b‖ ^ 2 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  obtain ⟨σ, hσ⟩ := exists_fderiv_gradient_eq_smul_id hE hEF hf hU hU'.isPreconnected hρ hρ0
  have hρc : ContDiffOn ℝ 2 ρ U := contDiffOn_of_inner_fderiv (m := 2) hf hU hρ hρ0
  have hgd : DifferentiableOn ℝ (∇ ρ) U := fun x hx ↦
    (((hρc.contDiffAt (hU.mem_nhds hx)).gradient_right (m := 1) (by norm_num)).differentiableAt
      (by simp)).differentiableWithinAt
  -- Integrate `Hess ρ = σ id` twice: `∇ρ x = σ x + c` and `ρ x = σ / 2 ‖x‖² + ⟪c, x⟫ + β`.
  obtain ⟨c, hc⟩ := hU.exists_eq_add_of_fderiv_eq hU'.isPreconnected hgd
    (g := fun x ↦ σ • x) (by fun_prop) fun x hx ↦ by
      rw [(hσ x hx).1]
      exact ((hasFDerivAt_id x).const_smul σ).fderiv.symm
  have hq : ∀ x, HasFDerivAt (fun y : E ↦ σ / 2 * ‖y‖ ^ 2 + ⟪c, y⟫)
      (toDual ℝ E (σ • x + c)) x := fun x ↦ by
    refine (((hasFDerivAt_id x).norm_sq.const_mul (σ / 2)).add
      (innerSL ℝ c).hasFDerivAt).congr_fderiv ?_
    ext w
    simp
    ring
  obtain ⟨β, hβ⟩ := hU.exists_eq_add_of_fderiv_eq hU'.isPreconnected
    (hρc.differentiableOn (by norm_num)) (fun x _ ↦ (hq x).differentiableAt.differentiableWithinAt)
    fun x hx ↦ by
      rw [(hq x).fderiv, ← toDual_gradient, hc hx]
  -- The relation `‖∇ρ‖² = 2 σ ρ` at one point fixes `β`.
  obtain ⟨x₀, hx₀⟩ := hU'.nonempty
  have hrel : ‖c‖ ^ 2 = 2 * σ * β := by
    have h := (hσ x₀ hx₀).2
    rw [hc hx₀, hβ hx₀, norm_add_sq_real, norm_smul, real_inner_smul_left, mul_pow,
      Real.norm_eq_abs, sq_abs, real_inner_comm] at h
    linarith
  rcases eq_or_ne σ 0 with h0 | h0
  · refine Or.inl ⟨β, fun x hx ↦ ?_⟩
    have hc0 : c = 0 := by
      rw [h0, mul_zero, zero_mul, sq_eq_zero_iff, norm_eq_zero] at hrel
      exact hrel
    rw [hβ hx, h0, hc0]
    simp
  · have key : ∀ x ∈ U, ρ x = σ / 2 * ‖x - (-(σ⁻¹ • c))‖ ^ 2 := fun x hx ↦ by
      rw [hβ hx]
      dsimp only
      rw [sub_neg_eq_add, norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow,
        Real.norm_eq_abs, sq_abs, real_inner_comm x c, hrel]
      field_simp
    have hσ0 : 0 < σ := by
      by_contra hneg
      have h1 := key x₀ hx₀
      have h2 := hρ0 x₀ hx₀
      nlinarith [sq_nonneg ‖x₀ - (-(σ⁻¹ • c))‖]
    refine Or.inr ⟨σ, hσ0, -(σ⁻¹ • c), fun hb ↦ ?_, key⟩
    have := hρ0 _ hb
    rw [key _ hb, sub_self, norm_zero] at this
    simp at this

/-- **A conformal map with constant conformal factor is a similarity.** If `f` is `C²` on a
connected open set `U`, between spaces of the same finite dimension, and
`c² ⟪Df(x) u, Df(x) v⟫ = ⟪u, v⟫` on `U` for a constant `c > 0`, then `f x = c⁻¹ • A x + a` on `U`
for a linear isometry `A` and a vector `a`. -/
theorem exists_eq_smul_linearIsometry_add_of_inner_fderiv
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F)
    (hf : ContDiffOn ℝ 2 f U) (hU : IsOpen U) (hU' : IsConnected U) {c : ℝ} (hc : 0 < c)
    (hρ : ∀ x ∈ U, ∀ u v, c ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫) :
    ∃ (A : E →ₗᵢ[ℝ] F) (a : F), ∀ x ∈ U, f x = c⁻¹ • A x + a := by
  have hD2 : ∀ x ∈ U, fderiv ℝ (fderiv ℝ f) x = 0 := fun x hx ↦ by
    have hg : ∇ (fun _ : E ↦ c) x = 0 := by simp [gradient]
    ext u v
    have h := smul_fderiv_fderiv_apply_eq_of_inner_fderiv (ρ := fun _ ↦ c) hEF hf hU hρ
      (fun _ _ ↦ hc) hx u v
    rw [hg] at h
    simp only [smul_zero, inner_zero_left, zero_smul, sub_zero, map_zero] at h
    simpa [hc.ne'] using h
  have hd1 : DifferentiableOn ℝ (fderiv ℝ f) U := fun x hx ↦
    (((hf.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by simp)).differentiableWithinAt
  obtain ⟨L, hL⟩ := hU.exists_is_const_of_fderiv_eq_zero hU'.isPreconnected hd1 hD2
  obtain ⟨a, ha⟩ := hU.exists_eq_add_of_fderiv_eq hU'.isPreconnected
    (hf.differentiableOn (by norm_num)) L.differentiable.differentiableOn
    fun x hx ↦ by rw [hL x hx, L.fderiv]
  obtain ⟨x₀, hx₀⟩ := hU'.nonempty
  have hiso : ∀ u v, ⟪(c • L : E →L[ℝ] F) u, (c • L : E →L[ℝ] F) v⟫ = ⟪u, v⟫ := fun u v ↦ by
    have := hρ x₀ hx₀ u v
    rw [hL x₀ hx₀] at this
    simp only [smul_apply, real_inner_smul_left, real_inner_smul_right]
    linear_combination this
  refine ⟨((c • L : E →L[ℝ] F) : E →ₗ[ℝ] F).isometryOfInner hiso, a, fun x hx ↦ ?_⟩
  rw [ha hx, LinearMap.coe_isometryOfInner]
  simp [smul_smul, inv_mul_cancel₀ hc.ne']

open EuclideanGeometry in
/-- **A conformal map with reciprocal conformal factor `(σ / 2) ‖x - b‖²` is a similarity composed
with an inversion.** If `f` is `C²` on a connected open set `U` not containing `b`, between spaces
of the same finite dimension, and `((σ / 2) ‖x - b‖²)² ⟪Df(x) u, Df(x) v⟫ = ⟪u, v⟫` on `U` for some
`σ > 0`, then `f x = (σ / 2)⁻¹ • A (inversion b 1 x) + a` on `U` for a linear isometry `A` and a
vector `a`. -/
theorem exists_eq_smul_linearIsometry_inversion_add_of_inner_fderiv
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F)
    (hf : ContDiffOn ℝ 2 f U) (hU : IsOpen U) (hU' : IsConnected U) {σ : ℝ} (hσ : 0 < σ)
    {b : E} (hb : b ∉ U)
    (hρ : ∀ x ∈ U, ∀ u v,
      (σ / 2 * ‖x - b‖ ^ 2) ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = ⟪u, v⟫) :
    ∃ (A : E →ₗᵢ[ℝ] F) (a : F), ∀ x ∈ U, f x = (σ / 2)⁻¹ • A (inversion b 1 x) + a := by
  have hιc : ∀ y, y ≠ b → ContDiffAt ℝ 2 (inversion b 1) y := fun y hy ↦ contDiffAt_inversion hy
  have hbU : ∀ x ∈ U, x ≠ b := fun x hx h ↦ hb (h ▸ hx)
  -- The image `V = inversion b 1 '' U` is a connected open set on which `inversion b 1` lands
  -- back in `U`.
  have hV : inversion b 1 '' U = {b}ᶜ ∩ inversion b 1 ⁻¹' U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(inversion_eq_center one_ne_zero).not.2 (hbU x hx),
        by simpa [inversion_inversion b one_ne_zero] using hx⟩
    · rintro ⟨hy, hyU⟩
      exact ⟨inversion b 1 y, hyU, inversion_inversion b one_ne_zero y⟩
  have hVo : IsOpen (inversion b 1 '' U) := by
    rw [hV]
    exact ContinuousOn.isOpen_inter_preimage
      (fun y hy ↦ (hιc y hy).continuousAt.continuousWithinAt) isOpen_compl_singleton hU
  have hVc : IsConnected (inversion b 1 '' U) :=
    hU'.image _ fun x hx ↦ (hιc x (hbU x hx)).continuousAt.continuousWithinAt
  have hmem : ∀ y ∈ inversion b 1 '' U, y ≠ b ∧ inversion b 1 y ∈ U := fun y hy ↦ by
    rw [hV] at hy
    exact hy
  have hh : ContDiffOn ℝ 2 (f ∘ inversion b 1) (inversion b 1 '' U) :=
    hf.comp (fun y hy ↦ (hιc y (hmem y hy).1).contDiffWithinAt) fun y hy ↦ (hmem y hy).2
  have hhρ : ∀ y ∈ inversion b 1 '' U, ∀ u v, (σ / 2) ^ 2 *
      ⟪fderiv ℝ (f ∘ inversion b 1) y u, fderiv ℝ (f ∘ inversion b 1) y v⟫ = ⟪u, v⟫ :=
    fun y hy u v ↦ by
      obtain ⟨hyb, hyU⟩ := hmem y hy
      have hfd : DifferentiableAt ℝ f (inversion b 1 y) :=
        (hf.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by norm_num)
      rw [fderiv_comp y hfd ((hιc y hyb).differentiableAt (by norm_num))]
      simp only [ContinuousLinearMap.comp_apply]
      have h1 := hρ (inversion b 1 y) hyU (fderiv ℝ (inversion b 1) y u)
        (fderiv ℝ (inversion b 1) y v)
      rw [inner_fderiv_inversion, ← dist_eq_norm, dist_inversion_center] at h1
      have hd : dist y b ≠ 0 := dist_ne_zero.2 hyb
      field_simp at h1
      linear_combination h1 / 4
  obtain ⟨A, a, hA⟩ := exists_eq_smul_linearIsometry_add_of_inner_fderiv hEF hh hVo hVc
    (by positivity) hhρ
  refine ⟨A, a, fun x hx ↦ ?_⟩
  have := hA (inversion b 1 x) ⟨x, hx, rfl⟩
  rwa [Function.comp_apply, inversion_inversion b one_ne_zero] at this

/-- **Liouville's theorem on conformal maps.** Let `E` and `F` be real inner product spaces of
the same finite dimension `n ≥ 3`, and let `f : E → F` be `C³` and conformal at every point of a
connected open set `U`. Then `f` is the restriction to `U` of a Möbius transformation: there are
`r > 0`, a linear isometry `A` and a vector `a` such that either `f x = r • A x + a` on `U`, or
`f x = r • A (inversion b 1 x) + a` on `U` for some point `b ∉ U`. -/
theorem exists_eq_smul_linearIsometry_add_or_inversion_of_conformalAt
    (hE : 3 ≤ Module.finrank ℝ E) (hEF : Module.finrank ℝ E = Module.finrank ℝ F)
    (hf : ContDiffOn ℝ 3 f U) (hU : IsOpen U) (hU' : IsConnected U)
    (hconf : ∀ x ∈ U, ConformalAt f x) :
    ∃ (r : ℝ) (A : E →ₗᵢ[ℝ] F) (a : F), 0 < r ∧
      ((∀ x ∈ U, f x = r • A x + a) ∨
        ∃ b ∉ U, ∀ x ∈ U, f x = r • A (EuclideanGeometry.inversion b 1 x) + a) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  -- The reciprocal conformal factor is `‖Df(x) e‖⁻¹` for a unit vector `e`.
  have hfac : ∀ x ∈ U, ∃ c, 0 < c ∧ ‖fderiv ℝ f x e‖ ^ 2 = c ∧
      ∀ u v, ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = c * ⟪u, v⟫ := fun x hx ↦ by
    obtain ⟨c, hc, hcuv⟩ := conformalAt_iff'.1 (hconf x hx)
    refine ⟨c, hc, ?_, hcuv⟩
    rw [← real_inner_self_eq_norm_sq, hcuv, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
  have hρ : ∀ x ∈ U, ∀ u v, ‖fderiv ℝ f x e‖⁻¹ ^ 2 * ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ =
      ⟪u, v⟫ := fun x hx u v ↦ by
    obtain ⟨c, hc, he', hcuv⟩ := hfac x hx
    rw [inv_pow, he', hcuv, inv_mul_cancel_left₀ hc.ne']
  have hρ0 : ∀ x ∈ U, 0 < ‖fderiv ℝ f x e‖⁻¹ := fun x hx ↦ by
    obtain ⟨c, hc, he', -⟩ := hfac x hx
    refine inv_pos.2 (norm_pos_iff.2 fun h0 ↦ ?_)
    rw [h0, norm_zero, zero_pow two_ne_zero] at he'
    exact hc.ne he'
  rcases eq_const_or_eq_mul_norm_sub_sq_of_inner_fderiv hE hEF hf hU hU' hρ hρ0 with
    ⟨c, hc⟩ | ⟨σ, hσ, b, hb, hρb⟩
  · obtain ⟨x₀, hx₀⟩ := hU'.nonempty
    have hc0 : 0 < c := hc x₀ hx₀ ▸ hρ0 x₀ hx₀
    obtain ⟨A, a, hA⟩ := exists_eq_smul_linearIsometry_add_of_inner_fderiv hEF
      (hf.of_le (by norm_num)) hU hU' hc0 fun x hx ↦ hc x hx ▸ hρ x hx
    exact ⟨c⁻¹, A, a, inv_pos.2 hc0, Or.inl hA⟩
  · obtain ⟨A, a, hA⟩ := exists_eq_smul_linearIsometry_inversion_add_of_inner_fderiv hEF
      (hf.of_le (by norm_num)) hU hU' hσ hb fun x hx ↦ hρb x hx ▸ hρ x hx
    exact ⟨(σ / 2)⁻¹, A, a, by positivity, Or.inr ⟨b, hb, hA⟩⟩

end TauCeti
