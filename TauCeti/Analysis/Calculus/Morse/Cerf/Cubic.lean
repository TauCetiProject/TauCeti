/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
-- Private: used only inside proofs.
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Fredholm.LevelSet.FiniteDimensional
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Generic one-parameter families have only cubic degenerate critical points

A one-parameter family of functions `f t : E → ℝ` on a finite-dimensional real normed space has
degenerate critical points at isolated parameters, where pairs of critical points are born or die.
Cerf's theorem says that for a generic family each of these is a *birth–death point*: the family
is transverse there, so that the Hessian has corank one, and along a nonzero vector `v` of the
kernel of the Hessian the third derivative `D³ (f t)_x (v, v, v)` does not vanish. This file
proves that these conditions hold after almost every perturbation of the family by a polynomial of
degree at most three.

The perturbations are the polynomials `y ↦ a y + B (y, y) + C (y, y, y)`
(`TauCeti.cubicPerturbation (a, B, C)`), with `a` a continuous linear functional and `B`, `C`
continuous bilinear and trilinear forms, not assumed symmetric. The coefficients form the
finite-dimensional space `TauCeti.CubicCoefficients E`, which carries any Haar measure, and the
perturbed family is `f t - cubicPerturbation p`.

The genericity statements are proved for any linear map `P` from a finite-dimensional space `Λ` to
functions on `E` that is jointly smooth in the parameter and the point and whose members realize
enough derivatives at the points considered, so that they also apply to the localized polynomial
perturbations of a chart on a manifold.

* **Transversality**
  (`TauCeti.ae_forall_surjective_fderiv_fderiv_sub_of_forall_exists_fderiv_eq`). If the members of
  `P` realize every differential, then for almost every `p` the derivative of the parametrized
  differential `(t, x) ↦ d(f t - P p)_x` is onto at every critical point. This is the parametric
  transversality theorem `TauCeti.ae_isRegularParameterOn` for `((t, x), p) ↦ d(f t - P p)_x`,
  as in `TauCeti.ae_forall_surjective_fderiv_fderiv_sub` for linear perturbations.
* **The cubic condition**
  (`TauCeti.ae_forall_fderiv_fderiv_fderiv_sub_apply_ne_zero_of_forall_exists_fderiv_eq`). If along
  every nonzero `v` the members of `P` realize every differential, every Hessian applied to `v` and
  every third derivative at `(v, v, v)`, then for almost every `p`, at every critical point `x` of
  `f t - P p` and for every nonzero `v` with `Hess(f t - P p)_x v = 0`, the third derivative
  `D³ (f t - P p)_x (v, v, v)` is nonzero.

The cubic condition is a dimension count. The map

`Φ ((t, x, v), p) = (d(f t - P p)_x, Hess(f t - P p)_x v, D³ (f t - P p)_x (v, v, v))`

goes from `(ℝ × E × E) × Λ` to `E* × E* × ℝ`, and its zeros with `v ≠ 0` are the failures of the
cubic condition. By hypothesis its derivative in the parameter is onto at every point with
`v ≠ 0`, so by parametric transversality, for almost every `p`, the derivative of `Φ (·, p)` is
onto at every zero with `v ≠ 0`. But `ℝ × E × E` and `E* × E* × ℝ` have the same dimension, so
this derivative is injective, while it kills the direction `(0, 0, v)`: along
`s ↦ ((t, x, (1 + s) v), p)` the map `Φ` is `(Φ₁, (1 + s) Φ₂, (1 + s)³ Φ₃)`, whose derivative at a
zero vanishes. So for almost every `p` there are no such zeros. The map `Φ` involves third
derivatives, so it is `C¹` once the family is jointly `C⁴`, which is the regularity the
transversality theorem asks for when the source and the target have the same dimension.

Polynomials of degree at most three realize every such jet
(`TauCeti.exists_cubicPerturbation_fderiv_eq`): choosing `ℓ` with `ℓ v = 1`, the cubic
`y ↦ c / 6 * ℓ y ^ 3` has third derivative `c` at `(v, v, v)`, the quadratic form
`y ↦ ℓ y * γ y` has Hessian `γ + γ v • ℓ` along `v`, which takes every value as `γ` varies, and
a linear functional changes only the differential.

At a transverse critical point the Hessian has corank at most one
(`TauCeti.finrank_ker_fderiv_fderiv_le_one`) and the parameter derivative of the differential does
not vanish on its kernel (`TauCeti.surjective_fderiv_fderiv_iff`). So after almost every
perturbation every degenerate critical point satisfies all the conditions of a birth–death point.

## Main declarations

* `TauCeti.cubicPerturbation`: the polynomial `y ↦ a y + B (y, y) + C (y, y, y)`, as a linear map
  from the coefficients `TauCeti.CubicCoefficients E` to functions on `E`.
* `TauCeti.exists_cubicPerturbation_fderiv_eq`: polynomials of degree at most three realize every
  differential, Hessian along a nonzero `v` and third derivative at `(v, v, v)`.
* `TauCeti.ae_forall_surjective_fderiv_fderiv_sub_cubicPerturbation`: for almost every `p`, the
  family `f t - cubicPerturbation p` is transverse at all of its critical points.
* `TauCeti.ae_forall_fderiv_fderiv_fderiv_sub_cubicPerturbation_apply_ne_zero`: for almost every
  `p`, the third derivative of `f t - cubicPerturbation p` does not vanish on the nonzero kernel
  vectors of the Hessian at its critical points.
* `TauCeti.exists_norm_lt_forall_surjective_and_fderiv_fderiv_fderiv_sub_cubicPerturbation_ne_zero`:
  both conditions hold together after an arbitrarily small perturbation.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173, Chapter III.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (generic one-parameter families and bifurcations).
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Derivatives of sums and differences -/

section Difference

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {u w : E → G} {x : E} {s : ℝ}

private theorem fderiv_sub_smul_of_differentiable (hu : DifferentiableAt ℝ u x)
    (hw : Differentiable ℝ w) :
    fderiv ℝ (fun y ↦ u y - s • w y) x = fderiv ℝ u x - s • fderiv ℝ w x := by
  rw [fderiv_fun_sub hu (by fun_prop), fderiv_fun_const_smul (hw x)]

/-- Near a point at which `u` is `C¹`, subtracting a multiple of a differentiable map `w`
subtracts the same multiple of its differential. -/
private theorem eventuallyEq_fderiv_sub_smul (hu : ContDiffAt ℝ 1 u x) (hw : Differentiable ℝ w) :
    fderiv ℝ (fun y ↦ u y - s • w y) =ᶠ[𝓝 x] fun y ↦ fderiv ℝ u y - s • fderiv ℝ w y := by
  filter_upwards [hu.eventually (by simp)] with y hy
  exact fderiv_sub_smul_of_differentiable (hy.differentiableAt one_ne_zero) hw

/-- The second differential of `u - s • w` is that of `u` minus `s` times that of `w`. -/
private theorem fderiv_fderiv_sub_smul (hu : ContDiffAt ℝ 2 u x) (hw : ContDiff ℝ 2 w) :
    fderiv ℝ (fderiv ℝ (fun y ↦ u y - s • w y)) x =
      fderiv ℝ (fderiv ℝ u) x - s • fderiv ℝ (fderiv ℝ w) x := by
  rw [(eventuallyEq_fderiv_sub_smul (hu.of_le (by norm_num))
    (hw.differentiable (by simp))).fderiv_eq]
  exact fderiv_sub_smul_of_differentiable
    ((hu.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)
    ((hw.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero)

/-- The third differential of `u - s • w` is that of `u` minus `s` times that of `w`. -/
private theorem fderiv_fderiv_fderiv_sub_smul (hu : ContDiffAt ℝ 3 u x) (hw : ContDiff ℝ 3 w) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y ↦ u y - s • w y))) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - s • fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x := by
  have hev : fderiv ℝ (fderiv ℝ (fun y ↦ u y - s • w y)) =ᶠ[𝓝 x]
      fun y ↦ fderiv ℝ (fderiv ℝ u) y - s • fderiv ℝ (fderiv ℝ w) y := by
    filter_upwards [(hu.of_le (m := 2) (by norm_num)).eventually (by simp)] with y hy
    exact fderiv_fderiv_sub_smul hy (hw.of_le (by norm_num))
  rw [hev.fderiv_eq]
  exact fderiv_sub_smul_of_differentiable
    ((hu.fderiv_right (m := 2) le_rfl).fderiv_right (m := 1) le_rfl
    |>.differentiableAt one_ne_zero)
    (((hw.fderiv_right (m := 2) le_rfl).fderiv_right (m := 1) le_rfl).differentiable one_ne_zero)

/-- The first three differentials of a sum of `C³` maps are the sums of their differentials. -/
private theorem fderiv_add_three (hu : ContDiff ℝ 3 u) (hw : ContDiff ℝ 3 w) (x : E) :
    fderiv ℝ (fun y ↦ u y + w y) x = fderiv ℝ u x + fderiv ℝ w x ∧
      fderiv ℝ (fderiv ℝ (fun y ↦ u y + w y)) x =
        fderiv ℝ (fderiv ℝ u) x + fderiv ℝ (fderiv ℝ w) x ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y ↦ u y + w y))) x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x + fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x := by
  have hu1 := hu.fderiv_right (m := 2) (by norm_num)
  have hw1 := hw.fderiv_right (m := 2) (by norm_num)
  have hu2 := hu1.fderiv_right (m := 1) (by norm_num)
  have hw2 := hw1.fderiv_right (m := 1) (by norm_num)
  have e1 : fderiv ℝ (fun y ↦ u y + w y) = fun y ↦ fderiv ℝ u y + fderiv ℝ w y :=
    funext fun y ↦ fderiv_fun_add (hu.differentiable (by simp) y) (hw.differentiable (by simp) y)
  have e2 : fderiv ℝ (fun y ↦ fderiv ℝ u y + fderiv ℝ w y) =
      fun y ↦ fderiv ℝ (fderiv ℝ u) y + fderiv ℝ (fderiv ℝ w) y :=
    funext fun y ↦ fderiv_fun_add (hu1.differentiable (by simp) y)
      (hw1.differentiable (by simp) y)
  refine ⟨congrFun e1 x, by rw [e1, e2], ?_⟩
  rw [e1, e2]
  exact fderiv_fun_add (hu2.differentiable one_ne_zero x) (hw2.differentiable one_ne_zero x)

end Difference

/-! ### Derivatives of particular polynomials -/

/-- The second differential of a linear functional vanishes. -/
private theorem fderiv_fderiv_clm (a : E →L[ℝ] ℝ) (x : E) : fderiv ℝ (fderiv ℝ a) x = 0 := by
  rw [show fderiv ℝ a = fun _ ↦ a from funext fun _ ↦ a.fderiv]
  exact fderiv_const_apply a

/-- The third differential of a linear functional vanishes. -/
private theorem fderiv_fderiv_fderiv_clm (a : E →L[ℝ] ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ a)) x = 0 := by
  rw [show fderiv ℝ (fderiv ℝ a) = fun _ ↦ 0 from funext (fderiv_fderiv_clm a)]
  exact fderiv_const_apply _

/-- The second differential of the quadratic form `y ↦ ℓ y * β y` along `v` is
`ℓ v • β + β v • ℓ`, and its third differential vanishes along `v`. -/
private theorem fderiv_fderiv_mul_clm (ℓ β : E →L[ℝ] ℝ) (x v : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ ℓ y * β y)) x v = ℓ v • β + β v • ℓ ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y ↦ ℓ y * β y))) x v v v = 0 := by
  have h2 : ∀ y k, fderiv ℝ (fderiv ℝ fun y ↦ ℓ y * β y) y v k = ℓ v * β k + β v * ℓ k :=
    fun y k ↦ by
      rw [fderiv_fderiv_fun_mul_apply ℓ.contDiff.contDiffAt β.contDiff.contDiffAt,
        fderiv_fderiv_clm, fderiv_fderiv_clm, ℓ.fderiv, β.fderiv]
      simp
  refine ⟨ContinuousLinearMap.ext fun k ↦ by simp [h2, mul_comm], ?_⟩
  have hd2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ fun y ↦ ℓ y * β y)) :=
    ((show ContDiff ℝ 3 fun y ↦ ℓ y * β y by fun_prop).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (m := 1) (by norm_num)
  rw [← fderiv_clm_apply_const_apply₂ (hd2.differentiable one_ne_zero x),
    show (fun y ↦ fderiv ℝ (fderiv ℝ fun y ↦ ℓ y * β y) y v v) = fun _ ↦ ℓ v * β v + β v * ℓ v
      from funext fun y ↦ h2 y v]
  simp

/-- The third differential of the cubic `y ↦ c * ℓ y ^ 3` along `v` is `6 * c * ℓ v ^ 3`. -/
private theorem fderiv_fderiv_fderiv_mul_pow_three (ℓ : E →L[ℝ] ℝ) (c : ℝ) (x v : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y ↦ c * ℓ y ^ 3))) x v v v = 6 * c * ℓ v ^ 3 := by
  set g : E → ℝ := fun y ↦ c * ℓ y ^ 3
  have hg : ContDiff ℝ 3 g := by fun_prop
  have h1 : ∀ y, fderiv ℝ g y v = 3 * c * ℓ v * ℓ y ^ 2 := fun y ↦ by
    rw [((ℓ.hasFDerivAt.pow 3).const_mul c).fderiv]
    simp
    ring
  have h2 : ∀ y, fderiv ℝ (fderiv ℝ g) y v v = 6 * c * ℓ v ^ 2 * ℓ y := fun y ↦ by
    rw [← fderiv_clm_apply_const_apply ((hg.fderiv_right (m := 2) (by norm_num)).differentiable
      (by norm_num) y), show (fun y ↦ fderiv ℝ g y v) = fun y ↦ 3 * c * ℓ v * ℓ y ^ 2 from
      funext h1, ((ℓ.hasFDerivAt.pow 2).const_mul (3 * c * ℓ v)).fderiv]
    simp
    ring
  have hd2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  rw [← fderiv_clm_apply_const_apply₂ (hd2.differentiable one_ne_zero x),
    show (fun y ↦ fderiv ℝ (fderiv ℝ g) y v v) = fun y ↦ 6 * c * ℓ v ^ 2 * ℓ y from funext h2,
    (ℓ.hasFDerivAt.const_mul (6 * c * ℓ v ^ 2)).fderiv]
  simp
  ring

/-! ### Polynomial perturbations of degree at most three -/

/-- The coefficients `(a, B, C)` of a polynomial of degree at most three without constant term on
`E`: a continuous linear functional, a continuous bilinear form and a continuous trilinear form. -/
abbrev CubicCoefficients (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Type _ :=
  (E →L[ℝ] ℝ) × (E [×2]→L[ℝ] ℝ) × (E [×3]→L[ℝ] ℝ)

/-- The polynomial `y ↦ a y + B (y, y) + C (y, y, y)` of degree at most three without constant
term with coefficients `p = (a, B, C)`, as a linear function of the coefficients. -/
noncomputable def cubicPerturbation : CubicCoefficients E →ₗ[ℝ] E → ℝ where
  toFun p y := p.1 y + p.2.1 (fun _ ↦ y) + p.2.2 (fun _ ↦ y)
  map_add' p q := by
    ext y
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    simp
    ring
  map_smul' s p := by
    ext y
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
    simp
    ring

/-- The value of the polynomial with coefficients `(a, B, C)` at `y`. -/
@[simp]
theorem cubicPerturbation_apply (p : CubicCoefficients E) (y : E) :
    cubicPerturbation p y = p.1 y + p.2.1 (fun _ ↦ y) + p.2.2 (fun _ ↦ y) :=
  (rfl)

/-- The perturbation is jointly smooth in the coefficients and the point. -/
theorem contDiff_cubicPerturbation {n : WithTop ℕ∞} :
    ContDiff ℝ n fun q : CubicCoefficients E × E ↦ cubicPerturbation q.1 q.2 := by
  have hm (k : ℕ) : ContDiff ℝ n fun q : (E [×k]→L[ℝ] ℝ) × (Fin k → E) ↦ q.1 q.2 :=
    contDiff_iff_contDiffAt.2 fun _ ↦
      (ContinuousLinearMap.id ℝ (E [×k]→L[ℝ] ℝ)).cpolynomialAt_uncurry_of_multilinear.contDiffAt
  have hy (k : ℕ) : ContDiff ℝ n fun q : CubicCoefficients E × E ↦ fun _ : Fin k ↦ q.2 :=
    contDiff_pi.2 fun _ ↦ contDiff_snd
  simp only [cubicPerturbation_apply]
  exact ((contDiff_fst.fst.clm_apply contDiff_snd).add
    ((hm 2).comp (contDiff_fst.snd.fst.prodMk (hy 2)))).add
    ((hm 3).comp (contDiff_fst.snd.snd.prodMk (hy 3)))

/-- A linear functional as a perturbation. -/
private theorem cubicPerturbation_linear (a : E →L[ℝ] ℝ) :
    cubicPerturbation ((a, 0, 0) : CubicCoefficients E) = a := by
  ext y
  simp [cubicPerturbation_apply]

/-- The quadratic form `y ↦ ℓ y * β y` as a perturbation. -/
private theorem cubicPerturbation_quadratic (ℓ β : E →L[ℝ] ℝ) :
    cubicPerturbation ((0, (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2)
      ℝ).compContinuousLinearMap ![ℓ, β], 0) : CubicCoefficients E) = fun y ↦ ℓ y * β y := by
  ext y
  simp [cubicPerturbation_apply, Fin.prod_univ_two]

/-- The cube `y ↦ c * ℓ y ^ 3` of a linear functional as a perturbation. -/
private theorem cubicPerturbation_cube (ℓ : E →L[ℝ] ℝ) (c : ℝ) :
    cubicPerturbation ((0, 0, c • (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3)
      ℝ).compContinuousLinearMap fun _ ↦ ℓ) : CubicCoefficients E) = fun y ↦ c * ℓ y ^ 3 := by
  ext y
  simp [cubicPerturbation_apply, Finset.prod_const]

/-- Every first derivative at a point is the derivative of a cubic polynomial. -/
private theorem exists_fderiv_cubicPerturbation_eq (x : E) (a : E →L[ℝ] ℝ) :
    ∃ q, fderiv ℝ (cubicPerturbation q) x = a :=
  ⟨(a, 0, 0), by rw [cubicPerturbation_linear]; exact a.fderiv⟩

/-- **Cubic polynomials realize every third-order jet along a nonzero vector.** For a nonzero
`v`, any functionals `a`, `b` and any `c`, some polynomial of degree at most three has
differential `a` at `x`, Hessian `b` along `v` and third derivative `c` at `(v, v, v)`. -/
theorem exists_cubicPerturbation_fderiv_eq (x : E) {v : E} (hv : v ≠ 0) (a b : E →L[ℝ] ℝ)
    (c : ℝ) :
    ∃ q, fderiv ℝ (cubicPerturbation q) x = a ∧
      fderiv ℝ (fderiv ℝ (cubicPerturbation q)) x v = b ∧
      fderiv ℝ (fderiv ℝ (fderiv ℝ (cubicPerturbation q))) x v v v = c := by
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hv
  -- The cubic part fixes the third derivative, the quadratic part then the Hessian, and the
  -- linear part last the differential.
  have h₃ := fderiv_fderiv_fderiv_mul_pow_three ℓ (c / 6) x v
  obtain ⟨b', hb'⟩ : ∃ b', b' = b - fderiv ℝ (fderiv ℝ fun y ↦ c / 6 * ℓ y ^ 3) x v :=
    ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : E →L[ℝ] ℝ, γ = b' - (b' v / 2) • ℓ := ⟨_, rfl⟩
  have h₂ := fderiv_fderiv_mul_clm ℓ γ x v
  obtain ⟨a', ha'⟩ : ∃ a', a' = a - fderiv ℝ (fun y ↦ ℓ y * γ y) x -
      fderiv ℝ (fun y ↦ c / 6 * ℓ y ^ 3) x := ⟨_, rfl⟩
  have hsum := fderiv_add_three (u := fun y ↦ a' y + ℓ y * γ y)
    (w := fun y ↦ c / 6 * ℓ y ^ 3) (by fun_prop) (by fun_prop) x
  have hsum' := fderiv_add_three (u := a') (w := fun y ↦ ℓ y * γ y) a'.contDiff (by fun_prop) x
  refine ⟨(a', 0, 0) + (0, (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2)
    ℝ).compContinuousLinearMap ![ℓ, γ], 0) + (0, 0, (c / 6) •
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ).compContinuousLinearMap fun _ ↦ ℓ), ?_⟩
  rw [map_add, map_add, cubicPerturbation_linear, cubicPerturbation_quadratic,
    cubicPerturbation_cube, show ⇑a' + (fun y ↦ ℓ y * γ y) + (fun y ↦ c / 6 * ℓ y ^ 3) =
      fun y ↦ (a' y + ℓ y * γ y) + c / 6 * ℓ y ^ 3 from rfl]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum.1, hsum'.1, a'.fderiv, ha']
    abel
  · rw [hsum.2.1, hsum'.2.1, fderiv_fderiv_clm, zero_add]
    ext k
    change fderiv ℝ (fderiv ℝ fun y ↦ ℓ y * γ y) x v k +
      fderiv ℝ (fderiv ℝ fun y ↦ c / 6 * ℓ y ^ 3) x v k = b k
    rw [h₂.1, hℓ, one_smul]
    subst hγ hb'
    simp [hℓ]
    ring
  · rw [hsum.2.2, hsum'.2.2, fderiv_fderiv_fderiv_clm, zero_add]
    change fderiv ℝ (fderiv ℝ (fderiv ℝ fun y ↦ ℓ y * γ y)) x v v v +
      fderiv ℝ (fderiv ℝ (fderiv ℝ fun y ↦ c / 6 * ℓ y ^ 3)) x v v v = c
    rw [h₂.2, h₃, hℓ]
    ring

/-! ### Genericity for linear families of perturbations -/

section Generic

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {f : ℝ → E → ℝ}
  {P : Λ →ₗ[ℝ] E → ℝ}

/-- The perturbed family is jointly `C^n` in the parameters and the point. -/
private theorem contDiffAt_sub_perturbation {n : WithTop ℕ∞} {t : ℝ} {x : E}
    (hf : ContDiffAt ℝ n (uncurry f) (t, x)) (hP : ContDiff ℝ n fun q : Λ × E ↦ P q.1 q.2)
    (p : Λ) : ContDiffAt ℝ n (fun q : (ℝ × Λ) × E ↦ f q.1.1 q.2 - P q.1.2 q.2) ((t, p), x) := by
  have h1 : ContDiffAt ℝ n (fun q : (ℝ × Λ) × E ↦ f q.1.1 q.2) ((t, p), x) :=
    hf.comp ((t, p), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have h2 : ContDiffAt ℝ n (fun q : (ℝ × Λ) × E ↦ P q.1.2 q.2) ((t, p), x) :=
    hP.contDiffAt.comp ((t, p), x) (contDiffAt_fst.snd.prodMk contDiffAt_snd)
  exact h1.sub h2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Moving the coefficients from `p` to `p + s • q` subtracts `s • P q` from the perturbed
family. -/
private theorem sub_perturbation_add_smul (t : ℝ) (p q : Λ) (s : ℝ) :
    (fun y ↦ f t y - P (p + s • q) y) = fun y ↦ (f t y - P p y) - s • P q y := by
  ext y
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The differential, the Hessian along `v` and the third derivative at `(v, v, v)` of the
perturbed family `f t - P p` at `x`, as a function of `((t, x, v), p)`. -/
private noncomputable def jetMap (f : ℝ → E → ℝ) (P : Λ →ₗ[ℝ] E → ℝ)
    (w : (ℝ × E × E) × Λ) : (E →L[ℝ] ℝ) × (E →L[ℝ] ℝ) × ℝ :=
  (fderiv ℝ (fun y ↦ f w.1.1 y - P w.2 y) w.1.2.1,
    fderiv ℝ (fderiv ℝ (fun y ↦ f w.1.1 y - P w.2 y)) w.1.2.1 w.1.2.2,
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y ↦ f w.1.1 y - P w.2 y))) w.1.2.1 w.1.2.2 w.1.2.2 w.1.2.2)

/-- The jet map is `C¹` where the family is jointly `C⁴`. -/
private theorem contDiffAt_jetMap {t : ℝ} {x v : E} (hf : ContDiffAt ℝ 4 (uncurry f) (t, x))
    (hP : ContDiff ℝ 4 fun q : Λ × E ↦ P q.1 q.2) (p : Λ) :
    ContDiffAt ℝ 1 (jetMap f P) ((t, x, v), p) := by
  have h1 := (contDiffAt_sub_perturbation hf hP p).fderiv_slice (m := 3) (by norm_num)
  have h2 := h1.fderiv_slice (m := 2) (by norm_num)
  have h3 := h2.fderiv_slice (m := 1) (by norm_num)
  have hσ : ContDiffAt ℝ 1 (fun w : (ℝ × E × E) × Λ ↦ ((w.1.1, w.2), w.1.2.1)) ((t, x, v), p) := by
    fun_prop
  have hv : ContDiffAt ℝ 1 (fun w : (ℝ × E × E) × Λ ↦ w.1.2.2) ((t, x, v), p) := by fun_prop
  exact ((h1.of_le (by norm_num)).comp ((t, x, v), p) hσ).prodMk
    ((((h2.of_le (by norm_num)).comp ((t, x, v), p) hσ).clm_apply hv).prodMk
      (((h3.comp ((t, x, v), p) hσ).clm_apply hv).clm_apply hv |>.clm_apply hv))

/-- Along the direction `(0, 0, v)` the jet map scales its last two components by `1 + s` and
`(1 + s) ^ 3`, so its derivative there is `(0, Hess v, 3 D³ (v, v, v))`. -/
private theorem fderiv_jetMap_apply_scale {w : (ℝ × E × E) × Λ}
    (hd : DifferentiableAt ℝ (jetMap f P) w) :
    fderiv ℝ (jetMap f P) w ((0, 0, w.1.2.2), 0) =
      (0, (jetMap f P w).2.1, 3 * (jetMap f P w).2.2) := by
  obtain ⟨⟨t, x, v⟩, p⟩ := w
  refine (hd.hasFDerivAt.hasLineDerivAt _).unique ?_
  unfold HasLineDerivAt
  have hline : (fun s : ℝ ↦ jetMap f P (((t, x, v), p) + s • ((0, 0, v), 0))) =
      fun s ↦ ((jetMap f P ((t, x, v), p)).1, (1 + s) • (jetMap f P ((t, x, v), p)).2.1,
        (1 + s) ^ 3 * (jetMap f P ((t, x, v), p)).2.2) := by
    ext1 s
    have hsv : v + s • v = (1 + s) • v := by rw [add_smul, one_smul]
    simp only [jetMap, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, hsv, map_smul]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp
    ring
  rw [hline]
  have hs : HasDerivAt (fun s : ℝ ↦ 1 + s) 1 0 := (hasDerivAt_id 0).const_add 1
  refine ((hasDerivAt_const (0 : ℝ) (jetMap f P ((t, x, v), p)).1).prodMk
    ((hs.smul_const (jetMap f P ((t, x, v), p)).2.1).prodMk
      ((hs.fun_pow 3).mul_const (jetMap f P ((t, x, v), p)).2.2))).congr_deriv ?_
  refine Prod.ext rfl (Prod.ext (one_smul _ _) ?_)
  simp

/-- In the direction `q` of the coefficients the jet map moves by minus the jet of `P q`. -/
private theorem fderiv_jetMap_apply_coeff {t : ℝ} {x v : E} {p : Λ}
    (hf : ContDiffAt ℝ 4 (uncurry f) (t, x)) (hP : ContDiff ℝ 4 fun q : Λ × E ↦ P q.1 q.2)
    (q : Λ) :
    fderiv ℝ (jetMap f P) ((t, x, v), p) ((0, 0, 0), q) =
      -(fderiv ℝ (P q) x, fderiv ℝ (fderiv ℝ (P q)) x v,
        fderiv ℝ (fderiv ℝ (fderiv ℝ (P q))) x v v v) := by
  have hu : ContDiffAt ℝ 3 (fun y ↦ f t y - P p y) x :=
    ((contDiffAt_sub_perturbation hf hP p).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le
      (by norm_num)
  have hw : ContDiff ℝ 3 (P q) :=
    (hP.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)
  refine (((contDiffAt_jetMap hf hP p).differentiableAt one_ne_zero).hasFDerivAt.hasLineDerivAt
    _).unique ?_
  unfold HasLineDerivAt
  have hline : (fun s : ℝ ↦ jetMap f P (((t, x, v), p) + s • ((0, 0, 0), q))) =
      fun s ↦ jetMap f P ((t, x, v), p) - s • (fderiv ℝ (P q) x, fderiv ℝ (fderiv ℝ (P q)) x v,
        fderiv ℝ (fderiv ℝ (fderiv ℝ (P q))) x v v v) := by
    ext1 s
    simp only [jetMap, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
    rw [sub_perturbation_add_smul]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact fderiv_sub_smul_of_differentiable (hu.differentiableAt (by norm_num)) (hw.differentiable
        (by norm_num))
    · simp only [Prod.snd_sub, Prod.fst_sub]
      rw [show fderiv ℝ (fderiv ℝ (fun y ↦ (f t y - P p y) - s • P q y)) x =
        _ from fderiv_fderiv_sub_smul (hu.of_le (by norm_num)) (hw.of_le (by norm_num))]
      rfl
    · simp only [Prod.snd_sub]
      rw [show fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y ↦ (f t y - P p y) - s • P q y))) x =
        _ from fderiv_fderiv_fderiv_sub_smul hu hw]
      simp
  rw [hline]
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (fderiv ℝ (P q) x, fderiv ℝ (fderiv ℝ (P q)) x v,
    fderiv ℝ (fderiv ℝ (fderiv ℝ (P q))) x v v v)).const_sub (jetMap f P ((t, x, v), p))

/-- **For almost every member of a rich linear family of perturbations, the family is transverse
at all of its critical points.** Let `f t` be a family of functions on a finite-dimensional real
normed space `E`, jointly `C³` at every point of a set `W ⊆ ℝ × E`, and let `P` be a linear map
from a finite-dimensional space `Λ` to functions on `E`, jointly `C³` in the parameter and the
point, whose members realize every differential at the points of `W`. For a Haar measure `ν` on
`Λ` and `ν`-almost every `p`, at every `(t, x) ∈ W` at which `x` is a critical point of
`f t - P p`, the derivative of the parametrized differential `(t, x) ↦ d(f t - P p)_x` is onto. -/
theorem ae_forall_surjective_fderiv_fderiv_sub_of_forall_exists_fderiv_eq [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ Λ] [MeasurableSpace Λ] [BorelSpace Λ] (ν : Measure Λ)
    [ν.IsAddHaarMeasure] {W : Set (ℝ × E)} (hf : ∀ z ∈ W, ContDiffAt ℝ 3 (uncurry f) z)
    (hP : ContDiff ℝ 3 fun q : Λ × E ↦ P q.1 q.2)
    (hjet : ∀ z ∈ W, ∀ a : E →L[ℝ] ℝ, ∃ q, fderiv ℝ (P q) z.2 = a) :
    ∀ᵐ p ∂ν, ∀ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - P p y) z.2 = 0 →
      Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (fun y ↦ f w.1 y - P p y) w.2) z) := by
  set G : (ℝ × E) × Λ → E →L[ℝ] ℝ := fun w ↦ fderiv ℝ (fun y ↦ f w.1.1 y - P w.2 y) w.1.2
  set U : Set ((ℝ × E) × Λ) := {w | w.1 ∈ W}
  -- `G` is `C²` at the points over `W`.
  have hGc : ∀ w ∈ U, ContDiffAt ℝ 2 G w := by
    rintro ⟨⟨t, x⟩, p⟩ hw
    exact ((contDiffAt_sub_perturbation (hf (t, x) hw) hP p).fderiv_slice (m := 2) le_rfl).comp
      ((t, x), p) ((contDiffAt_fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)
  -- Its derivative in the direction of the coefficients is onto.
  have htotal : ∀ w ∈ U, G w = 0 → Surjective (fderiv ℝ G w) := by
    rintro ⟨⟨t, x⟩, p⟩ hw - a
    obtain ⟨q, hq⟩ := hjet (t, x) hw (-a)
    have hu : ContDiffAt ℝ 1 (fun y ↦ f t y - P p y) x :=
      ((contDiffAt_sub_perturbation (hf (t, x) hw) hP p).comp x
        (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num)
    have hw' : Differentiable ℝ (P q) :=
      (hP.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)
    refine ⟨((0, 0), q), (((hGc _ hw).differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt
      _).unique ?_⟩
    unfold HasLineDerivAt
    have hline : (fun s : ℝ ↦ G (((t, x), p) + s • ((0, 0), q))) =
        fun s ↦ G ((t, x), p) + s • a := by
      ext1 s
      simp only [G, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero]
      rw [sub_perturbation_add_smul,
        fderiv_sub_smul_of_differentiable (hu.differentiableAt one_ne_zero) hw',
        hq, smul_neg, sub_neg_eq_add]
    rw [hline]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add (G ((t, x), p))
  have hreg := ae_isRegularParameterOn ν (U := U) (c := 0) (n := 2) (fun w hw _ ↦ hGc w hw)
    htotal (by
      rw [Module.finrank_prod, Module.finrank_self, ContinuousLinearMap.dual_finrank_eq]
      norm_num)
  filter_upwards [hreg] with p hp z hz hz0
  have hs := isRegularParameterOn_iff.1 hp z hz hz0
  rwa [← fderiv_slice_left ((hGc (z, p) hz).differentiableAt (by norm_num))] at hs

/-- **For almost every member of a rich linear family of perturbations, the third derivative does
not vanish on the kernel of a degenerate Hessian.** Let `f t` be a family of functions on a
finite-dimensional real normed space `E`, jointly `C⁴` at every point of a set `W ⊆ ℝ × E`, and
let `P` be a linear map from a finite-dimensional space `Λ` to functions on `E`, jointly `C⁴` in
the parameter and the point, whose members realize, at the points of `W` and along every nonzero
vector `v`, every differential, every Hessian applied to `v` and every third derivative at
`(v, v, v)`. For a Haar measure `ν` on `Λ` and `ν`-almost every `p`, at every critical point
`(t, x) ∈ W` of `f t - P p` and for every nonzero `v` in the kernel of its Hessian there,
`D³ (f t - P p)_x (v, v, v) ≠ 0`. -/
theorem ae_forall_fderiv_fderiv_fderiv_sub_apply_ne_zero_of_forall_exists_fderiv_eq
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ Λ] [MeasurableSpace Λ] [BorelSpace Λ]
    (ν : Measure Λ) [ν.IsAddHaarMeasure] {W : Set (ℝ × E)}
    (hf : ∀ z ∈ W, ContDiffAt ℝ 4 (uncurry f) z) (hP : ContDiff ℝ 4 fun q : Λ × E ↦ P q.1 q.2)
    (hjet : ∀ z ∈ W, ∀ v ≠ 0, ∀ (a b : E →L[ℝ] ℝ) (c : ℝ), ∃ q, fderiv ℝ (P q) z.2 = a ∧
      fderiv ℝ (fderiv ℝ (P q)) z.2 v = b ∧ fderiv ℝ (fderiv ℝ (fderiv ℝ (P q))) z.2 v v v = c) :
    ∀ᵐ p ∂ν, ∀ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - P p y) z.2 = 0 → ∀ v ≠ 0,
      fderiv ℝ (fderiv ℝ (fun y ↦ f z.1 y - P p y)) z.2 v = 0 →
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y ↦ f z.1 y - P p y))) z.2 v v v ≠ 0 := by
  set U : Set ((ℝ × E × E) × Λ) := {w | (w.1.1, w.1.2.1) ∈ W ∧ w.1.2.2 ≠ 0}
  have hc : ∀ w ∈ U, ContDiffAt ℝ 1 (jetMap f P) w := fun w hw ↦ contDiffAt_jetMap (hf _ hw.1) hP _
  -- The derivative of the jet map in the direction of the coefficients is onto.
  have htotal : ∀ w ∈ U, jetMap f P w = 0 → Surjective (fderiv ℝ (jetMap f P) w) := by
    rintro ⟨⟨t, x, v⟩, p⟩ hw - y
    obtain ⟨q, h1, h2, h3⟩ := hjet (t, x) hw.1 v hw.2 (-y.1) (-y.2.1) (-y.2.2)
    refine ⟨((0, 0, 0), q), ?_⟩
    rw [fderiv_jetMap_apply_coeff (hf _ hw.1) hP, h1, h2, h3]
    simp
  have hfin : finrank ℝ (ℝ × E × E) = finrank ℝ ((E →L[ℝ] ℝ) × (E →L[ℝ] ℝ) × ℝ) := by
    simp only [Module.finrank_prod, Module.finrank_self, ContinuousLinearMap.dual_finrank_eq]
    ring
  have hreg := ae_isRegularParameterOn ν (U := U) (c := 0) (n := 1) (fun w hw _ ↦ hc w hw)
    htotal (by rw [hfin]; simp)
  filter_upwards [hreg] with p hp z hz hz0 v hv hHv hD3
  have hzero : jetMap f P ((z.1, z.2, v), p) = 0 := Prod.ext hz0 (Prod.ext hHv hD3)
  -- The derivative of `jetMap f P (·, p)` is onto, hence injective, but it kills `(0, 0, v)`.
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2
    (isRegularParameterOn_iff.1 hp (z.1, z.2, v) ⟨hz, hv⟩ hzero)
  have hscale := fderiv_jetMap_apply_scale
    ((hc ((z.1, z.2, v), p) ⟨hz, hv⟩).differentiableAt one_ne_zero)
  rw [hzero] at hscale
  refine hv (congrArg (fun u : ℝ × E × E ↦ u.2.2) (hinj ?_ : ((0, 0, v) : ℝ × E × E) = 0))
  rw [map_zero]
  simpa [Prod.zero_eq_mk] using hscale

end Generic

/-! ### Genericity for polynomial perturbations -/

section Cubic

variable [FiniteDimensional ℝ E] {f : ℝ → E → ℝ}

/-- **For almost every polynomial perturbation of degree at most three, the family is transverse
at all of its critical points.** Let `f t` be a family of functions on a finite-dimensional real
normed space `E`, jointly `C³` at every point of a set `W ⊆ ℝ × E`. For a Haar measure `ν` on the
coefficients and `ν`-almost every `p`, at every `(t, x) ∈ W` at which `x` is a critical point of
`f t - cubicPerturbation p`, the derivative of the parametrized differential
`(t, x) ↦ d(f t - cubicPerturbation p)_x` is onto. -/
theorem ae_forall_surjective_fderiv_fderiv_sub_cubicPerturbation
    [MeasurableSpace (CubicCoefficients E)] [BorelSpace (CubicCoefficients E)]
    (ν : Measure (CubicCoefficients E)) [ν.IsAddHaarMeasure] {W : Set (ℝ × E)}
    (hf : ∀ z ∈ W, ContDiffAt ℝ 3 (uncurry f) z) :
    ∀ᵐ p ∂ν, ∀ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - cubicPerturbation p y) z.2 = 0 →
      Surjective (fderiv ℝ
        (fun w : ℝ × E ↦ fderiv ℝ (fun y ↦ f w.1 y - cubicPerturbation p y) w.2) z) :=
  ae_forall_surjective_fderiv_fderiv_sub_of_forall_exists_fderiv_eq ν hf
    contDiff_cubicPerturbation fun z _ ↦ exists_fderiv_cubicPerturbation_eq z.2

/-- **For almost every polynomial perturbation of degree at most three, the third derivative does
not vanish on the kernel of a degenerate Hessian.** Let `f t` be a family of functions on a
finite-dimensional real normed space `E`, jointly `C⁴` at every point of a set `W ⊆ ℝ × E`. For a
Haar measure `ν` on the coefficients and `ν`-almost every `p`, at every critical point
`(t, x) ∈ W` of `f t - cubicPerturbation p` and for every nonzero `v` in the kernel of its Hessian
there, the third derivative `D³ (f t - cubicPerturbation p)_x (v, v, v)` is nonzero. -/
theorem ae_forall_fderiv_fderiv_fderiv_sub_cubicPerturbation_apply_ne_zero
    [MeasurableSpace (CubicCoefficients E)] [BorelSpace (CubicCoefficients E)]
    (ν : Measure (CubicCoefficients E)) [ν.IsAddHaarMeasure] {W : Set (ℝ × E)}
    (hf : ∀ z ∈ W, ContDiffAt ℝ 4 (uncurry f) z) :
    ∀ᵐ p ∂ν, ∀ z ∈ W, fderiv ℝ (fun y ↦ f z.1 y - cubicPerturbation p y) z.2 = 0 → ∀ v ≠ 0,
      fderiv ℝ (fderiv ℝ (fun y ↦ f z.1 y - cubicPerturbation p y)) z.2 v = 0 →
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y ↦ f z.1 y - cubicPerturbation p y))) z.2 v v v ≠ 0 :=
  ae_forall_fderiv_fderiv_fderiv_sub_apply_ne_zero_of_forall_exists_fderiv_eq ν hf
    contDiff_cubicPerturbation fun z _ _ hv ↦ exists_cubicPerturbation_fderiv_eq z.2 hv

/-- **After an arbitrarily small polynomial perturbation of degree at most three, the family is
transverse with nonvanishing cubic term at all of its critical points.** Let `f t` be a family of
functions on a finite-dimensional real normed space `E`, jointly `C⁴` at every point of a set
`W ⊆ ℝ × E`. For every `ε > 0` there are coefficients `p` of norm less than `ε` such that at every
critical point `(t, x) ∈ W` of `f t - cubicPerturbation p` the family is transverse, and the third
derivative of `f t - cubicPerturbation p` at `x` does not vanish at `(v, v, v)` for any nonzero
`v` in the kernel of the Hessian. -/
theorem exists_norm_lt_forall_surjective_and_fderiv_fderiv_fderiv_sub_cubicPerturbation_ne_zero
    {W : Set (ℝ × E)} (hf : ∀ z ∈ W, ContDiffAt ℝ 4 (uncurry f) z) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : CubicCoefficients E, ‖p‖ < ε ∧ ∀ z ∈ W,
      fderiv ℝ (fun y ↦ f z.1 y - cubicPerturbation p y) z.2 = 0 →
        Surjective (fderiv ℝ
          (fun w : ℝ × E ↦ fderiv ℝ (fun y ↦ f w.1 y - cubicPerturbation p y) w.2) z) ∧
        ∀ v ≠ 0, fderiv ℝ (fderiv ℝ (fun y ↦ f z.1 y - cubicPerturbation p y)) z.2 v = 0 →
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y ↦ f z.1 y - cubicPerturbation p y))) z.2 v v v ≠
            0 := by
  borelize (CubicCoefficients E)
  have hae := (ae_forall_surjective_fderiv_fderiv_sub_cubicPerturbation
    (addHaar : Measure (CubicCoefficients E)) fun z hz ↦ (hf z hz).of_le (by norm_num)).and
    (ae_forall_fderiv_fderiv_fderiv_sub_cubicPerturbation_apply_ne_zero addHaar hf)
  obtain ⟨p, hp, hball⟩ := (dense_of_ae hae).exists_mem_open Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self hε⟩
  exact ⟨p, by simpa [Metric.mem_ball, dist_zero_right] using hball,
    fun z hz hz0 ↦ ⟨hp.1 z hz hz0, hp.2 z hz hz0⟩⟩

end Cubic

end TauCeti
