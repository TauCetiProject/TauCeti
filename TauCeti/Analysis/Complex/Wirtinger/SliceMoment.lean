/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.SliceMoment
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.Algebra.Module.Alternating.Basic

/-!
# The moment defects of a closed two-form along a normal Cauchy–Riemann operator

Let `T` be a closed two-form on `V × ℂ`, compactly supported in the fibre direction, where `V`
is a complex normed space of base coordinates and `w ∈ ℂ` is the normal coordinate. Its normal
slices `μ_z = T(z, w)(∂_x, ∂_y) dx dy` have the moments and mixed moments

`M_k(z) = ∫ wᵏ dμ_z`,  `Q_ℓ(z) = ∫ w^ℓ \bar w dμ_z`

(`TauCeti.sliceMoment`). Given a real normal Cauchy–Riemann operator
`D_C = \bar∂ + ν W + μ \bar W`, with `(0,1)`-forms `ν, μ : V →L⋆[ℂ] ℂ` at the base point `z`,
the *moment defects* are

`E_k = \bar∂ M_k + k ν M_k + k μ Q_{k-1}`.

If the slices were the counting measures of `m` points moving along solutions of `D_C`, the
defects would vanish; in general the Newton coefficients of the `M_k` satisfy the equation of the
elementary symmetric functions of `m` solutions of `D_C` up to an error controlled by the `E_k`
(`TauCeti.conjWirtingerDeriv_add_eq_sum_of_newton`). This file expresses `E_k` through the type
of `T` for the almost complex structure attached to `D_C`.

**The normal structure.** At the fibre point `w` let

`J_N(v, ζ) = (i v, i ζ + 2 i (ν(v) w + μ(v) \bar w))`

(`TauCeti.normalStructure`). It squares to `-1`, it is `i` on the fibre, and it sends the
horizontal lift `H_v = (v, -(ν(v) w + μ(v) \bar w))` (`TauCeti.normalLift`) to `H_{i v}`. Its
complex curves are the graphs of solutions of `D_C`: the tangent space of the graph of `f` at `z`
is `J_N`-invariant exactly when `\bar∂ f + f ν + \bar f μ = 0` at `z`
(`TauCeti.normalStructure_apply_fderiv_iff`).

**The defect density.** For a two-form `τ` at a point of the fibre put

`δ(τ)(v) = τ(H_v, ∂_x) + i τ(H_v, ∂_y) + i (τ(H_{iv}, ∂_x) + i τ(H_{iv}, ∂_y))`

(`TauCeti.sliceDefectDensity`). In complexified terms it is `4 τ(\bar Z_v, ∂_{\bar w})`, where
`\bar Z_v = (H_v + i H_{iv}) / 2` and `∂_{\bar w}` are `(0,1)`-vectors of `J_N`, so it is the mixed
base–fibre part of the `(0,2)`-component of `τ` for `J_N` (all of it when `V = ℂ`). It changes
sign under `τ ↦ J_N^* τ`
(`TauCeti.sliceDefectDensity_compContinuousLinearMap_normalStructure`), so it only sees the
`J_N`-anti-invariant part `(τ - J_N^* τ) / 2` and vanishes on `J_N`-invariant forms, the forms of
type `(1,1)`.

**The defect identity.** If `T` is `C¹` and closed along the fibre over `z`, then for every base
direction `v`

`E_k(z) v = ∫ (i k / 2) w^(k-1) δ(T(z, w))(v) dw`

(`TauCeti.conjWirtingerDeriv_sliceMoment_pow_add_add_apply`). Consequently `E_k(z) = 0` when `T`
is of type `(1,1)` for `J_N` along the fibre
(`TauCeti.conjWirtingerDeriv_sliceMoment_pow_add_add_eq_zero`), and in general

`‖E_k(z) v‖ ≤ 2 k ‖v‖ ∫ ‖w‖^(k-1) (1 + (‖ν‖ + ‖μ‖) ‖w‖) ‖(T - J_N^* T)(z, w) / 2‖ dw`

(`TauCeti.norm_conjWirtingerDeriv_sliceMoment_pow_add_add_apply_le`), so the moment defects are
controlled by the `J_N`-anti-invariant part of `T` alone: once that part is bounded, the last
statement bounds `E_k`. In Taubes's analysis of Seiberg–Witten solutions near a pseudoholomorphic
curve, `T` is the rescaled cutoff curvature current, whose type estimate is relative to the actual
almost complex structure `J_a` rather than the frozen `J_N`. Turning that estimate into bounds on
`E_k` still needs the comparison of `J_a` with `J_N` and the slice-motion and base-freezing terms,
which are not proved here.

The identity comes from the derivative of the slice moments, `dM_k = π_*(k w^(k-1) dw ∧ T)`
(`TauCeti.fderiv_sliceMoment_pow_apply`), whose `(0,1)`-part pairs the base directions with
`∂_{\bar w}`, and from the vertical components of the horizontal lifts, which produce the terms
`k ν M_k + k μ Q_{k-1}`.

## Main definitions

* `TauCeti.normalLift ν μ w v`: the horizontal lift `(v, -(ν(v) w + μ(v) \bar w))`.
* `TauCeti.normalStructure ν μ w`: the almost complex structure `J_N` of `V × ℂ` at `w`, also
  bundled as `TauCeti.normalAlmostComplexStructure ν μ w`.
* `TauCeti.sliceDefectDensity ν μ w τ v`: the mixed `(0,2)`-component `δ(τ)(v)` of a two-form
  `τ`.

## Main results

* `TauCeti.normalStructure_normalStructure`, `TauCeti.normalStructure_normalLift`,
  `TauCeti.normalStructure_apply_fderiv_iff`: `J_N² = -1`, `J_N H_v = H_{iv}`, and the complex
  graphs of `J_N` are the solutions of `D_C`.
* `TauCeti.sliceDefectDensity_eq`: the defect density in terms of the values of `τ` on the
  horizontal directions `(v, 0)`, `(i v, 0)` and on the fibre.
* `TauCeti.sliceDefectDensity_compContinuousLinearMap_normalStructure`,
  `TauCeti.sliceDefectDensity_eq_zero_of_compContinuousLinearMap_eq`,
  `TauCeti.sliceDefectDensity_smul_sub_compContinuousLinearMap`,
  `TauCeti.norm_sliceDefectDensity_le`.
* `TauCeti.conjWirtingerDeriv_sliceMoment_pow_add_add_apply`: the defect identity.
* `TauCeti.conjWirtingerDeriv_sliceMoment_pow_add_add_eq_zero`: the defects of a two-form of type
  `(1,1)` vanish.
* `TauCeti.norm_conjWirtingerDeriv_sliceMoment_pow_add_add_apply_le`: the defects are bounded by
  the anti-invariant part.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open MeasureTheory Complex ComplexConjugate

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### The normal structure of a normal Cauchy–Riemann operator -/

section NormalStructure

variable (ν μ : V →L⋆[ℂ] ℂ) (w : ℂ)

/-- The horizontal lift `H_v = (v, -(ν(v) w + μ(v) \bar w))` of a base direction `v` at the fibre
point `w`. These are the directions on which the normal structure `TauCeti.normalStructure ν μ w`
acts by `i` on the base: `J_N H_v = H_{i v}`. -/
def normalLift (v : V) : V × ℂ :=
  (v, -(ν v * w + μ v * conj w))

theorem normalLift_apply (v : V) : normalLift ν μ w v = (v, -(ν v * w + μ v * conj w)) :=
  (rfl)

/-- The horizontal lift of `i v`: its fibre component is `i (ν(v) w + μ(v) \bar w)`. -/
theorem normalLift_I_smul (v : V) :
    normalLift ν μ w (I • v) = (I • v, I * (ν v * w + μ v * conj w)) := by
  simp only [normalLift_apply, map_smulₛₗ, conj_I, smul_eq_mul]
  ext
  · rfl
  · ring

/-- The horizontal lift is odd. -/
theorem normalLift_neg (v : V) : normalLift ν μ w (-v) = -normalLift ν μ w v := by
  simp only [normalLift_apply, map_neg, Prod.neg_mk]
  ring_nf

/-- The **normal structure** `J_N(v, ζ) = (i v, i ζ + 2 i (ν(v) w + μ(v) \bar w))` of the normal
Cauchy–Riemann operator `D_C = \bar∂ + ν W + μ \bar W` at the fibre point `w`. It is an almost
complex structure of `V × ℂ` (`TauCeti.normalStructure_normalStructure`), equal to `i` on the
fibre, and its complex graphs are the solutions of `D_C`
(`TauCeti.normalStructure_apply_fderiv_iff`). -/
def normalStructure : V × ℂ →L[ℝ] V × ℂ where
  toFun p := (I • p.1, I * p.2 + 2 * I * (ν p.1 * w + μ p.1 * conj w))
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, smul_add, map_add, Prod.mk_add_mk]
    congr 1
    ring
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Prod.smul_mk,
      map_real_smul ν ν.continuous, map_real_smul μ μ.continuous, smul_comm (c : ℝ) I, real_smul]
    congr 1
    ring
  cont := (continuous_const.smul continuous_fst).prodMk ((continuous_const.mul continuous_snd).add
    (continuous_const.mul (((ν.continuous.comp continuous_fst).mul continuous_const).add
      ((μ.continuous.comp continuous_fst).mul continuous_const))))

theorem normalStructure_apply (p : V × ℂ) :
    normalStructure ν μ w p = (I • p.1, I * p.2 + 2 * I * (ν p.1 * w + μ p.1 * conj w)) :=
  (rfl)

/-- On the fibre the normal structure is multiplication by `i`. -/
@[simp]
theorem normalStructure_zero_prod (ζ : ℂ) : normalStructure ν μ w (0, ζ) = (0, I * ζ) := by
  simp [normalStructure_apply]

/-- The normal structure is an almost complex structure: `J_N (J_N p) = -p`. -/
@[simp]
theorem normalStructure_normalStructure (p : V × ℂ) :
    normalStructure ν μ w (normalStructure ν μ w p) = -p := by
  ext
  · simp [normalStructure_apply, smul_smul]
  · simp only [normalStructure_apply, map_smulₛₗ, conj_I, smul_eq_mul, Prod.snd_neg]
    linear_combination p.2 * I_sq

/-- The normal structure as a pointwise almost complex structure of `V × ℂ`. -/
def normalAlmostComplexStructure : AlmostComplexStructure (V × ℂ) where
  toLinearMap := normalStructure ν μ w
  square_neg := LinearMap.ext fun p ↦ normalStructure_normalStructure ν μ w p

@[simp]
theorem coe_normalAlmostComplexStructure :
    ⇑(normalAlmostComplexStructure ν μ w) = normalStructure ν μ w :=
  (rfl)

/-- The normal structure sends the horizontal lift of `v` to the horizontal lift of `i v`. -/
@[simp]
theorem normalStructure_normalLift (v : V) :
    normalStructure ν μ w (normalLift ν μ w v) = normalLift ν μ w (I • v) := by
  rw [normalLift_I_smul, normalLift_apply, normalStructure_apply]
  ext
  · rfl
  · ring

/-- **The complex graphs of the normal structure are the solutions of `D_C`.** For a function
`f : V → ℂ` and a base point `z`, the tangent map `v ↦ (v, Df(z) v)` of the graph of `f` is
complex linear from `i` to the normal structure at `f(z)` exactly when
`\bar∂ f(z) + f(z) ν + \bar f(z) μ = 0`, that is, when `f` solves `D_C f = 0` at `z`. -/
theorem normalStructure_apply_fderiv_iff {f : V → ℂ} {z : V} :
    (∀ v, normalStructure ν μ (f z) (v, fderiv ℝ f z v) = (I • v, fderiv ℝ f z (I • v))) ↔
      conjWirtingerDeriv f z + f z • ν + conj (f z) • μ = 0 := by
  constructor
  · intro h
    ext v
    have hv := congrArg Prod.snd (h v)
    simp only [normalStructure_apply] at hv
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      conjWirtingerDeriv_apply, smul_eq_mul, zero_apply]
    rw [← hv]
    linear_combination (2⁻¹ * fderiv ℝ f z v + ν v * f z + μ v * conj (f z)) * I_sq
  · intro h v
    have hv := congrArg (fun L ↦ L v) h
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      conjWirtingerDeriv_apply, smul_eq_mul, zero_apply] at hv
    rw [normalStructure_apply]
    ext
    · rfl
    · simp only
      linear_combination (2 * I) * hv - fderiv ℝ f z (I • v) * I_sq

/-- The normal structure depends Lipschitz continuously on the fibre point. -/
theorem norm_normalStructure_sub_le (w' : ℂ) :
    ‖normalStructure ν μ w - normalStructure ν μ w'‖ ≤ 2 * (‖ν‖ + ‖μ‖) * ‖w - w'‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p ↦ ?_
  have hp : (normalStructure ν μ w - normalStructure ν μ w') p =
      (0, 2 * I * (ν p.1 * (w - w') + μ p.1 * conj (w - w'))) := by
    simp only [sub_apply, normalStructure_apply, Prod.mk_sub_mk, sub_self,
      map_sub]
    congr 1
    ring
  rw [hp, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), norm_mul, norm_mul,
    Complex.norm_two, norm_I, mul_one]
  have h₁ : ‖ν p.1‖ ≤ ‖ν‖ * ‖p‖ := (ν.le_opNorm _).trans (by gcongr; exact norm_fst_le p)
  have h₂ : ‖μ p.1‖ ≤ ‖μ‖ * ‖p‖ := (μ.le_opNorm _).trans (by gcongr; exact norm_fst_le p)
  calc 2 * ‖ν p.1 * (w - w') + μ p.1 * conj (w - w')‖
      ≤ 2 * (‖ν p.1‖ * ‖w - w'‖ + ‖μ p.1‖ * ‖w - w'‖) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj]
    _ ≤ 2 * (‖ν‖ * ‖p‖ * ‖w - w'‖ + ‖μ‖ * ‖p‖ * ‖w - w'‖) := by gcongr
    _ = 2 * (‖ν‖ + ‖μ‖) * ‖w - w'‖ * ‖p‖ := by ring

/-- The normal structure depends continuously on the fibre point. -/
@[fun_prop]
theorem continuous_normalStructure : Continuous (normalStructure ν μ) := by
  refine (LipschitzWith.of_dist_le_mul (K := 2 * (‖ν‖₊ + ‖μ‖₊)) fun w w' ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  push_cast
  exact norm_normalStructure_sub_le ν μ w w'

/-- The horizontal lift is bounded by `‖v‖ (1 + (‖ν‖ + ‖μ‖) ‖w‖)`. -/
theorem norm_normalLift_le (v : V) :
    ‖normalLift ν μ w v‖ ≤ ‖v‖ * (1 + (‖ν‖ + ‖μ‖) * ‖w‖) := by
  rw [normalLift_apply, Prod.norm_def, norm_neg]
  refine max_le (le_mul_of_one_le_right (norm_nonneg _) (by
    have := mul_nonneg (add_nonneg (norm_nonneg ν) (norm_nonneg μ)) (norm_nonneg w)
    linarith)) ?_
  calc ‖ν v * w + μ v * conj w‖ ≤ ‖ν v‖ * ‖w‖ + ‖μ v‖ * ‖w‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj]
    _ ≤ ‖ν‖ * ‖v‖ * ‖w‖ + ‖μ‖ * ‖v‖ * ‖w‖ := by gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖v‖ * (1 + (‖ν‖ + ‖μ‖) * ‖w‖) := by
        have := norm_nonneg v
        nlinarith

end NormalStructure

/-! ### The defect density of a two-form -/

section Density

variable (ν μ : V →L⋆[ℂ] ℂ) (w : ℂ)

/-- The **defect density** of a two-form `τ` at the fibre point `w`, in the base direction `v`:

`δ(τ)(v) = τ(H_v, ∂_x) + i τ(H_v, ∂_y) + i (τ(H_{iv}, ∂_x) + i τ(H_{iv}, ∂_y))`,

with `H_v` the horizontal lift `TauCeti.normalLift ν μ w v`. Complexified, it is
`4 τ(\bar Z_v, ∂_{\bar w})` with `\bar Z_v = (H_v + i H_{iv}) / 2`: the part of the
`(0,2)`-component of `τ` for the normal structure `TauCeti.normalStructure ν μ w` pairing a base
direction with the fibre. It vanishes on the `(1,1)`-forms of the normal structure
(`TauCeti.sliceDefectDensity_eq_zero_of_compContinuousLinearMap_eq`). -/
def sliceDefectDensity (τ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v : V) : ℂ :=
  τ ![normalLift ν μ w v, (0, 1)] + I * τ ![normalLift ν μ w v, (0, I)] +
    I * (τ ![normalLift ν μ w (I • v), (0, 1)] + I * τ ![normalLift ν μ w (I • v), (0, I)])

theorem sliceDefectDensity_def (τ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v : V) :
    sliceDefectDensity ν μ w τ v =
      τ ![normalLift ν μ w v, (0, 1)] + I * τ ![normalLift ν μ w v, (0, I)] +
        I * (τ ![normalLift ν μ w (I • v), (0, 1)] + I * τ ![normalLift ν μ w (I • v), (0, I)]) :=
  (rfl)

/-- The defect density through the values of `τ` on the horizontal directions `(v, 0)` and
`(i v, 0)` and its slice density `τ(∂_x, ∂_y)`:

`δ(τ)(v) = τ((v,0), ∂_x) + i τ((v,0), ∂_y) + i τ((iv,0), ∂_x) - τ((iv,0), ∂_y)
  - 2 i (ν(v) w + μ(v) \bar w) τ(∂_x, ∂_y)`. -/
theorem sliceDefectDensity_eq (τ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v : V) :
    sliceDefectDensity ν μ w τ v =
      τ ![(v, 0), (0, 1)] + I * τ ![(v, 0), (0, I)] + I * τ ![(I • v, 0), (0, 1)] -
        τ ![(I • v, 0), (0, I)] -
        2 * I * (ν v * w + μ v * conj w) * τ ![(0, 1), (0, I)] := by
  rw [sliceDefectDensity_def, normalLift_I_smul, normalLift_apply]
  set a := ν v * w + μ v * conj w
  rw [τ.apply_prod_one v (-a), τ.apply_prod_I v (-a), τ.apply_prod_one (I • v) (I * a),
    τ.apply_prod_I (I • v) (I * a)]
  simp only [neg_re, neg_im, I_mul_re, I_mul_im, smul_eq_mul]
  conv_rhs => rw [← re_add_im a]
  push_cast
  linear_combination ((a.im : ℂ) * τ ![(0, 1), (0, I)] + τ ![(I • v, 0), (0, I)]) * I_sq

/-- The defect density of the zero form vanishes. -/
@[simp]
theorem sliceDefectDensity_zero (v : V) : sliceDefectDensity ν μ w 0 v = 0 := by
  simp [sliceDefectDensity_def]

/-- The defect density is additive in the two-form. -/
@[simp]
theorem sliceDefectDensity_add (τ σ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v : V) :
    sliceDefectDensity ν μ w (τ + σ) v =
      sliceDefectDensity ν μ w τ v + sliceDefectDensity ν μ w σ v := by
  simp only [sliceDefectDensity_def, ContinuousAlternatingMap.add_apply]
  push_cast
  ring

/-- The defect density is real homogeneous in the two-form. -/
@[simp]
theorem sliceDefectDensity_smul (c : ℝ) (τ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v : V) :
    sliceDefectDensity ν μ w (c • τ) v = c * sliceDefectDensity ν μ w τ v := by
  simp only [sliceDefectDensity_def, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The defect density changes sign with the two-form. -/
@[simp]
theorem sliceDefectDensity_neg (τ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v : V) :
    sliceDefectDensity ν μ w (-τ) v = -sliceDefectDensity ν μ w τ v := by
  simp only [sliceDefectDensity_def, ContinuousAlternatingMap.neg_apply]
  push_cast
  ring

/-- The defect density is subtractive in the two-form. -/
@[simp]
theorem sliceDefectDensity_sub (τ σ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v : V) :
    sliceDefectDensity ν μ w (τ - σ) v =
      sliceDefectDensity ν μ w τ v - sliceDefectDensity ν μ w σ v := by
  rw [sub_eq_add_neg, sliceDefectDensity_add, sliceDefectDensity_neg, sub_eq_add_neg]

/-- The defect density changes sign when the two-form is pulled back by the normal structure:
`δ(J_N^* τ) = -δ(τ)`. -/
theorem sliceDefectDensity_compContinuousLinearMap_normalStructure
    (τ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v : V) :
    sliceDefectDensity ν μ w (τ.compContinuousLinearMap (normalStructure ν μ w)) v =
      -sliceDefectDensity ν μ w τ v := by
  have hJI : normalStructure ν μ w ((0 : V), I) = -(0, 1) := by
    rw [normalStructure_zero_prod, I_mul_I, Prod.neg_mk, neg_zero]
  have hJ1 : normalStructure ν μ w ((0 : V), (1 : ℂ)) = (0, I) := by
    rw [normalStructure_zero_prod, mul_one]
  have hJIv : normalStructure ν μ w (normalLift ν μ w (I • v)) = -normalLift ν μ w v := by
    rw [normalStructure_normalLift, smul_smul, I_mul_I, neg_one_smul, normalLift_neg]
  have hcomp (X Y : V × ℂ) :
      ⇑(normalStructure ν μ w) ∘ ![X, Y] = ![normalStructure ν μ w X, normalStructure ν μ w Y] := by
    funext i; fin_cases i <;> rfl
  simp only [sliceDefectDensity_def, ContinuousAlternatingMap.compContinuousLinearMap_apply, hcomp,
    normalStructure_normalLift, hJIv, hJI, hJ1, ContinuousAlternatingMap.map_vecCons_neg,
    ContinuousAlternatingMap.map_vecCons_vecCons_neg]
  push_cast
  linear_combination (τ ![normalLift ν μ w v, (0, 1)] +
    τ ![normalLift ν μ w (I • v), (0, I)]) * I_sq

/-- The defect density vanishes on forms invariant under the normal structure, that is, on forms
of type `(1,1)`. -/
theorem sliceDefectDensity_eq_zero_of_compContinuousLinearMap_eq
    {τ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ} (hτ : τ.compContinuousLinearMap (normalStructure ν μ w) = τ)
    (v : V) : sliceDefectDensity ν μ w τ v = 0 := by
  have h := sliceDefectDensity_compContinuousLinearMap_normalStructure ν μ w τ v
  rw [hτ] at h
  linear_combination h / 2

/-- The defect density only sees the anti-invariant part `(τ - J_N^* τ) / 2` of the two-form. -/
theorem sliceDefectDensity_smul_sub_compContinuousLinearMap (τ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v : V) :
    sliceDefectDensity ν μ w
        ((2 : ℝ)⁻¹ • (τ - τ.compContinuousLinearMap (normalStructure ν μ w))) v =
      sliceDefectDensity ν μ w τ v := by
  rw [sliceDefectDensity_smul, sliceDefectDensity_sub,
    sliceDefectDensity_compContinuousLinearMap_normalStructure]
  push_cast
  ring

/-- The defect density is bounded by `4 ‖τ‖ ‖v‖ (1 + (‖ν‖ + ‖μ‖) ‖w‖)`. -/
theorem norm_sliceDefectDensity_le (τ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (v : V) :
    ‖sliceDefectDensity ν μ w τ v‖ ≤ 4 * ‖τ‖ * ‖v‖ * (1 + (‖ν‖ + ‖μ‖) * ‖w‖) := by
  set B := ‖v‖ * (1 + (‖ν‖ + ‖μ‖) * ‖w‖)
  have hlift (u : V) (hu : ‖u‖ = ‖v‖) (y : ℂ) (hy : ‖y‖ = 1) :
      ‖(τ ![normalLift ν μ w u, (0, y)] : ℂ)‖ ≤ ‖τ‖ * B := by
    have h0y : ‖((0 : V), y)‖ = 1 := by
      rw [Prod.norm_def, norm_zero, hy, max_eq_right zero_le_one]
    rw [norm_real, Real.norm_eq_abs]
    refine (τ.le_opNorm _).trans ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, h0y, mul_one]
    gcongr
    exact (norm_normalLift_le ν μ w u).trans_eq (by rw [hu])
  have hIv : ‖I • v‖ = ‖v‖ := by rw [norm_smul, norm_I, one_mul]
  have h₁ := hlift v rfl 1 norm_one
  have h₂ := hlift v rfl I norm_I
  have h₃ := hlift (I • v) hIv 1 norm_one
  have h₄ := hlift (I • v) hIv I norm_I
  calc ‖sliceDefectDensity ν μ w τ v‖
      ≤ ‖(τ ![normalLift ν μ w v, (0, 1)] : ℂ)‖ + ‖(τ ![normalLift ν μ w v, (0, I)] : ℂ)‖ +
          (‖(τ ![normalLift ν μ w (I • v), (0, 1)] : ℂ)‖ +
            ‖(τ ![normalLift ν μ w (I • v), (0, I)] : ℂ)‖) := by
        rw [sliceDefectDensity_def]
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans_eq ?_) ?_)
        · rw [norm_mul, norm_I, one_mul]
        · rw [norm_mul, norm_I, one_mul]
          refine (norm_add_le _ _).trans_eq ?_
          rw [norm_mul, norm_I, one_mul]
    _ ≤ ‖τ‖ * B + ‖τ‖ * B + (‖τ‖ * B + ‖τ‖ * B) := by gcongr
    _ = 4 * ‖τ‖ * ‖v‖ * (1 + (‖ν‖ + ‖μ‖) * ‖w‖) := by ring

/-- The pointwise form of the moment defect identity: `(i k / 2) w^(k-1) δ(τ)(v)` is half the
integrand of `dM_k(v)` in `TauCeti.fderiv_sliceMoment_pow_apply`, plus `i / 2` times that of
`dM_k(i v)`, plus the slice density weighted by `k ν(v) wᵏ` and by `k μ(v) w^(k-1) \bar w`. -/
private theorem mul_sliceDefectDensity_eq (τ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ) (v : V) :
    I * k / 2 * w ^ (k - 1) * sliceDefectDensity ν μ w τ v =
      2⁻¹ * (k * w ^ (k - 1) * (I * τ ![(v, 0), (0, 1)] - τ ![(v, 0), (0, I)])) +
        2⁻¹ * I * (k * w ^ (k - 1) * (I * τ ![(I • v, 0), (0, 1)] - τ ![(I • v, 0), (0, I)])) +
        k * ν v * (τ ![(0, 1), (0, I)] • w ^ k) +
        k * μ v * (τ ![(0, 1), (0, I)] • (w ^ (k - 1) * conj w)) := by
  simp only [sliceDefectDensity_eq, real_smul]
  rcases k with _ | n
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    -- Both sides are polynomial in the values of `τ`; they differ by a multiple of `I ^ 2 + 1`.
    linear_combination (↑n + 1) / 2 * w ^ n * (τ ![(v, 0), (0, I)] -
      2 * (ν v * w + μ v * conj w) * τ ![(0, 1), (0, I)]) * I_sq

end Density

/-! ### The moment defects of a closed two-form -/

section Moments

variable {T : V × ℂ → (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ} {K : Set ℂ} {z : V}

/-- A continuous function on the fibre over `z` that vanishes wherever `T` does is integrable,
when `T` vanishes over the complement of a compact set. -/
private theorem integrable_of_forall_eq_zero (hK : IsCompact K)
    (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {f : ℂ → ℂ} (hf : Continuous f)
    (h : ∀ w, T (z, w) = 0 → f w = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun w hw ↦ h w (hT z w hw))

/-- **The moment defect identity.** Let `T` be a `C¹` two-form on `V × ℂ` vanishing over the
complement of a compact set `K` and closed at every point of the fibre over `z`, and let
`ν, μ` be the coefficients of `D_C = \bar∂ + ν W + μ \bar W` at `z`. Then the moment defect
`E_k = \bar∂ M_k + k ν M_k + k μ Q_{k-1}` of the slice moments `M_k = ∫ wᵏ dμ_z` and
`Q_ℓ = ∫ w^ℓ \bar w dμ_z` is the fibre integral of the defect density:

`E_k(z) v = ∫ (i k / 2) w^(k-1) δ(T(z, w))(v) dw`. -/
theorem conjWirtingerDeriv_sliceMoment_pow_add_add_apply (hK : IsCompact K)
    (hTc : ContDiff ℝ 1 T) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0)
    (hdT : ∀ w, extDeriv T (z, w) = 0) (ν μ : V →L⋆[ℂ] ℂ) (k : ℕ) (v : V) :
    (conjWirtingerDeriv (sliceMoment T (· ^ k)) z + (k * sliceMoment T (· ^ k) z) • ν +
        (k * sliceMoment T (fun w ↦ w ^ (k - 1) * conj w) z) • μ) v =
      ∫ w, I * k / 2 * w ^ (k - 1) * sliceDefectDensity ν μ w (T (z, w)) v := by
  -- The four integrands of `mul_sliceDefectDensity_eq`: those of `dM_k(v)` and `dM_k(i v)`, and
  -- the slice density weighted by `wᵏ` and `w^(k-1) \bar w`. All are integrable.
  have hc (A : Fin 2 → V × ℂ) : Continuous fun w ↦ T (z, w) A :=
    (ContinuousAlternatingMap.apply ℝ (V × ℂ) ℝ A).continuous.comp
      (hTc.continuous.comp (Continuous.prodMk_right z))
  have hint {f : ℂ → ℂ} (hf : Continuous f) (h : ∀ w, T (z, w) = 0 → f w = 0) :
      Integrable f :=
    integrable_of_forall_eq_zero hK hT hf h
  set f₁ : ℂ → ℂ := fun w ↦ k * w ^ (k - 1) *
    (I * T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![(v, 0), (0, I)])
  set f₂ : ℂ → ℂ := fun w ↦ k * w ^ (k - 1) *
    (I * T (z, w) ![(I • v, 0), (0, 1)] - T (z, w) ![(I • v, 0), (0, I)])
  set g₁ : ℂ → ℂ := fun w ↦ T (z, w) ![(0, 1), (0, I)] • w ^ k
  set g₂ : ℂ → ℂ := fun w ↦ T (z, w) ![(0, 1), (0, I)] • (w ^ (k - 1) * conj w)
  have hcf (u : V) : Continuous fun w : ℂ ↦ k * w ^ (k - 1) *
      (I * T (z, w) ![(u, 0), (0, 1)] - T (z, w) ![(u, 0), (0, I)]) :=
    (continuous_const.mul (continuous_pow _)).mul ((continuous_const.mul
      (continuous_ofReal.comp (hc _))).sub (continuous_ofReal.comp (hc _)))
  have hf₁ : Integrable f₁ := hint (hcf v) fun w hw ↦ by simp [f₁, hw]
  have hf₂ : Integrable f₂ := hint (hcf (I • v)) fun w hw ↦ by simp [f₂, hw]
  have hg₁ : Integrable g₁ :=
    hint ((hc _).smul (continuous_pow _)) fun w hw ↦ by simp [g₁, hw]
  have hg₂ : Integrable g₂ :=
    hint ((hc _).smul ((continuous_pow _).mul continuous_conj)) fun w hw ↦ by simp [g₂, hw]
  -- Rewrite the integrand pointwise and split the integral into the four pieces.
  have i₁ : Integrable fun w ↦ 2⁻¹ * f₁ w := hf₁.const_mul _
  have i₂ : Integrable fun w ↦ 2⁻¹ * I * f₂ w := hf₂.const_mul _
  have i₁₂ : Integrable fun w ↦ 2⁻¹ * f₁ w + 2⁻¹ * I * f₂ w := i₁.add i₂
  have i₃ : Integrable fun w ↦ k * ν v * g₁ w := hg₁.const_mul _
  have i₁₂₃ : Integrable fun w ↦ 2⁻¹ * f₁ w + 2⁻¹ * I * f₂ w + k * ν v * g₁ w := i₁₂.add i₃
  rw [integral_congr_ae (Filter.Eventually.of_forall fun w ↦
      mul_sliceDefectDensity_eq ν μ w (T (z, w)) k v), integral_add i₁₂₃ (hg₂.const_mul _),
    integral_add i₁₂ i₃, integral_add i₁ i₂, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]
  -- The first two pieces are `dM_k(v)` and `dM_k(i v)`, which combine to `\bar∂ M_k(v)`; the
  -- last two are the slice moments `M_k` and `Q_{k-1}`.
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
    conjWirtingerDeriv_apply, fderiv_sliceMoment_pow_apply hK hTc hT hdT, sliceMoment_def,
    smul_eq_mul, f₁, f₂, g₁, g₂]
  ring

/-- **The moment defects of a `(1,1)`-form vanish.** Under the hypotheses of
`TauCeti.conjWirtingerDeriv_sliceMoment_pow_add_add_apply`, if `T` is invariant under the normal
structure of `D_C` at every point of the fibre over `z`, then
`\bar∂ M_k + k ν M_k + k μ Q_{k-1} = 0` at `z`. -/
theorem conjWirtingerDeriv_sliceMoment_pow_add_add_eq_zero (hK : IsCompact K)
    (hTc : ContDiff ℝ 1 T) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0)
    (hdT : ∀ w, extDeriv T (z, w) = 0) {ν μ : V →L⋆[ℂ] ℂ}
    (hJ : ∀ w, (T (z, w)).compContinuousLinearMap (normalStructure ν μ w) = T (z, w)) (k : ℕ) :
    conjWirtingerDeriv (sliceMoment T (· ^ k)) z + (k * sliceMoment T (· ^ k) z) • ν +
        (k * sliceMoment T (fun w ↦ w ^ (k - 1) * conj w) z) • μ = 0 := by
  ext v
  rw [conjWirtingerDeriv_sliceMoment_pow_add_add_apply hK hTc hT hdT,
    zero_apply]
  simp [sliceDefectDensity_eq_zero_of_compContinuousLinearMap_eq ν μ _ (hJ _)]

/-- **The moment defects are bounded by the anti-invariant part of `T`.** Under the hypotheses of
`TauCeti.conjWirtingerDeriv_sliceMoment_pow_add_add_apply`,

`‖E_k(z) v‖ ≤ 2 k ‖v‖ ∫ ‖w‖^(k-1) (1 + (‖ν‖ + ‖μ‖) ‖w‖) ‖(T - J_N^* T)(z, w) / 2‖ dw`,

where `J_N = TauCeti.normalStructure ν μ w` is the normal structure of `D_C`. -/
theorem norm_conjWirtingerDeriv_sliceMoment_pow_add_add_apply_le (hK : IsCompact K)
    (hTc : ContDiff ℝ 1 T) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0)
    (hdT : ∀ w, extDeriv T (z, w) = 0) (ν μ : V →L⋆[ℂ] ℂ) (k : ℕ) (v : V) :
    ‖(conjWirtingerDeriv (sliceMoment T (· ^ k)) z + (k * sliceMoment T (· ^ k) z) • ν +
        (k * sliceMoment T (fun w ↦ w ^ (k - 1) * conj w) z) • μ) v‖ ≤
      2 * k * ‖v‖ * ∫ w, ‖w‖ ^ (k - 1) * (1 + (‖ν‖ + ‖μ‖) * ‖w‖) *
        ‖(2 : ℝ)⁻¹ • (T (z, w) - (T (z, w)).compContinuousLinearMap (normalStructure ν μ w))‖ := by
  set A : ℂ → (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ := fun w ↦
    (2 : ℝ)⁻¹ • (T (z, w) - (T (z, w)).compContinuousLinearMap (normalStructure ν μ w))
  have hTz : Continuous fun w ↦ T (z, w) := hTc.continuous.comp (Continuous.prodMk_right z)
  have hA : Continuous A := by
    refine (hTz.sub ?_).const_smul (2 : ℝ)⁻¹
    simp_rw [← ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
    exact ((ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp
      (continuous_normalStructure ν μ)).clm_apply hTz)
  have hg : Integrable fun w ↦ 2 * k * ‖v‖ * (‖w‖ ^ (k - 1) * (1 + (‖ν‖ + ‖μ‖) * ‖w‖) *
      ‖A w‖) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.intro hK fun w hw ↦ ?_)
    have h₀ : (0 : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ).compContinuousLinearMap
        (normalStructure ν μ w) = 0 := by
      ext
      simp
    simp [A, hT z w hw, h₀]
  rw [conjWirtingerDeriv_sliceMoment_pow_add_add_apply hK hTc hT hdT, ← integral_const_mul]
  refine norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun w ↦ ?_)
  rw [← sliceDefectDensity_smul_sub_compContinuousLinearMap, norm_mul, norm_mul, norm_div,
    norm_mul, norm_I, one_mul, Complex.norm_natCast, Complex.norm_two, norm_pow]
  have h := norm_sliceDefectDensity_le ν μ w (A w) v
  calc ↑k / 2 * ‖w‖ ^ (k - 1) * ‖sliceDefectDensity ν μ w (A w) v‖
      ≤ ↑k / 2 * ‖w‖ ^ (k - 1) * (4 * ‖A w‖ * ‖v‖ * (1 + (‖ν‖ + ‖μ‖) * ‖w‖)) := by gcongr
    _ = 2 * k * ‖v‖ * (‖w‖ ^ (k - 1) * (1 + (‖ν‖ + ‖μ‖) * ‖w‖) * ‖A w‖) := by ring

end Moments

end TauCeti
