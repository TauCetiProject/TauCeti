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
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.FDeriv.Add
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.Calculus.Morse.Cerf
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Fredholm.LevelSet.FiniteDimensional
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Generic one-parameter families have only cubic degenerate critical points

A generic one-parameter family of functions `f t : E → ℝ` on a finite-dimensional real normed
space has degenerate critical points only at isolated parameters, where pairs of critical points
are born or die; this isolation is not proved here. Cerf's theorem says that for a generic family
each degenerate critical point is a *birth–death point*: the family is transverse there, so that
the Hessian has corank one, and along a nonzero vector `v` of the kernel of the Hessian the third
derivative `D³ (f t)_x (v, v, v)` does not vanish. This file proves that these conditions hold
after almost every perturbation of the family by a polynomial of degree at most three.

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
  (`TauCeti.ae_forall_surjective_fderiv_fderiv_sub_of_forall_exists_fderiv_eq`, in
  `TauCeti.Analysis.Calculus.Morse.Cerf`). If the members of `P` realize every differential, then
  for almost every `p` the derivative of the parametrized differential `(t, x) ↦ d(f t - P p)_x` is
  onto at every critical point.
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
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_apply]
    ring
  map_smul' s p := by
    ext y
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_apply,
      smul_eq_mul]
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

/-- The cube `y ↦ ℓ y ^ 3` of a linear functional as a perturbation. -/
private theorem cubicPerturbation_cube (ℓ : E →L[ℝ] ℝ) :
    cubicPerturbation ((0, 0, (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3)
      ℝ).compContinuousLinearMap fun _ ↦ ℓ) : CubicCoefficients E) = fun y ↦ ℓ y ^ 3 := by
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
  set K : E → ℝ := fun y ↦ ℓ y ^ 3
  obtain ⟨b', hb'⟩ : ∃ b', b' = b - (c / 6) • fderiv ℝ (fderiv ℝ K) x v := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : E →L[ℝ] ℝ, γ = b' - (b' v / 2) • ℓ := ⟨_, rfl⟩
  set Q : E → ℝ := fun y ↦ ℓ y * γ y
  obtain ⟨a', ha'⟩ : ∃ a', a' = a - fderiv ℝ Q x - (c / 6) • fderiv ℝ K x := ⟨_, rfl⟩
  have hK : ContDiff ℝ 3 K := by fun_prop
  have hQ : ContDiff ℝ 3 Q := by fun_prop
  have haQ : ContDiff ℝ 3 (⇑a' + Q) := a'.contDiff.add hQ
  have hcK : ContDiff ℝ 3 ((c / 6) • K) := by fun_prop
  -- `Q` is the quadratic map of the bilinear form `ℓ.smulRight γ`, with constant Hessian.
  have hQB : fderiv ℝ (fderiv ℝ Q) = fun _ ↦ (ℓ.smulRight γ).flip + ℓ.smulRight γ := by
    rw [show Q = fun y ↦ ℓ.smulRight γ y y by ext; simp [Q]]
    exact funext (ℓ.smulRight γ).fderiv_fderiv_apply_self
  refine ⟨(a', 0, 0) + (0, (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2)
    ℝ).compContinuousLinearMap ![ℓ, γ], 0) + (c / 6) •
      (0, 0, (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ).compContinuousLinearMap fun _ ↦ ℓ),
    ?_, ?_, ?_⟩ <;>
    rw [map_add, map_add, map_smul, cubicPerturbation_linear, cubicPerturbation_quadratic,
      cubicPerturbation_cube]
  · rw [fderiv_add (haQ.differentiable (by norm_num) x) (hcK.differentiable (by norm_num) x),
      fderiv_add a'.differentiableAt (hQ.differentiable (by norm_num) x),
      fderiv_const_smul (hK.differentiable (by norm_num) x), a'.fderiv, ha']
    abel
  · rw [fderiv_fderiv_add (haQ.contDiffAt.of_le (by norm_num)) (hcK.contDiffAt.of_le (by norm_num)),
      fderiv_fderiv_add a'.contDiff.contDiffAt (hQ.contDiffAt.of_le (by norm_num)),
      a'.fderiv_fderiv, fderiv_fderiv_const_smul]
    ext k
    simp only [add_apply, smul_apply, Pi.zero_apply, zero_add, hQB,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, hℓ, one_mul]
    subst hγ hb'
    simp only [sub_apply, smul_apply, smul_eq_mul, hℓ, mul_one]
    ring
  · rw [fderiv_fderiv_fderiv_add haQ.contDiffAt hcK.contDiffAt,
      fderiv_fderiv_fderiv_add a'.contDiff.contDiffAt hQ.contDiffAt, a'.fderiv_fderiv_fderiv,
      hQB, fderiv_fun_const, fderiv_fderiv_fderiv_const_smul]
    simp only [smul_apply, Pi.zero_apply, zero_add, K, ℓ.fderiv_fderiv_fderiv_pow_three_apply, hℓ,
      smul_eq_mul]
    ring

/-! ### Genericity for linear families of perturbations -/

section Generic

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] {f : ℝ → E → ℝ}
  {P : Λ →ₗ[ℝ] E → ℝ}

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
  have h1 := (hf.sub_uncurry_prod (hP.contDiffAt (x := (p, x)))).fderiv_slice
    (m := 3) (by norm_num)
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
  have hline : (fun s : ℝ ↦ jetMap f P (((t, x, v), p) + s • ((0, 0, v), 0))) =
      fun s ↦ ((jetMap f P ((t, x, v), p)).1, (1 + s) • (jetMap f P ((t, x, v), p)).2.1,
        (1 + s) ^ 3 * (jetMap f P ((t, x, v), p)).2.2) := by
    ext1 s
    have hsv : v + s • v = (1 + s) • v := by rw [add_smul, one_smul]
    simp only [jetMap, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, hsv, map_smul]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    simp only [smul_apply, smul_eq_mul]
    ring
  rw [HasLineDerivAt, hline]
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
    ((hf.sub_uncurry_prod (hP.contDiffAt (x := (p, x)))).comp x
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num)
  have hw : ContDiff ℝ 3 (P q) :=
    (hP.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)
  -- Along the line in the direction of `q`, the jet map moves by minus `s` times the jet of `P q`.
  refine ((contDiffAt_jetMap hf hP p).differentiableAt one_ne_zero).fderiv_apply_eq_of_add_smul
    (.of_forall fun s ↦ ?_)
  have hsw : ContDiffAt ℝ 3 (s • P q) x := (hw.const_smul s).contDiffAt
  simp only [jetMap, Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, smul_neg,
    ← sub_eq_add_neg, Prod.mk_sub_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact P.fderiv_sub_map_add_smul (hu.differentiableAt (by norm_num))
      (hw.differentiable (by norm_num) x) s
  · rw [P.sub_map_add_smul (f t) p q s,
      fderiv_fderiv_sub (hu.of_le (by norm_num)) (hsw.of_le (by norm_num)),
      fderiv_fderiv_const_smul, sub_apply, smul_apply]
  · rw [P.sub_map_add_smul (f t) p q s, fderiv_fderiv_fderiv_sub hu hsw,
      fderiv_fderiv_fderiv_const_smul, sub_apply, sub_apply, sub_apply, smul_apply, smul_apply,
      smul_apply, smul_eq_mul]

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

end Cubic

end TauCeti
