/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Metrizable.Urysohn
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.MeasureTheory.Function.Lp.LeftTranslation

/-!
# Idempotent kernels and the vanishing of their constant terms

Let `G` be a topological group with a left-invariant measure `μ`. An integrable function
`e : G → ℂ` acts on the bounded continuous functions on `G` through the right regular
representation,

```text
(ρ(e) F)(x) = ∫ g, e g * F (x * g) ∂μ,
```

an operator of norm at most `∫ ‖e‖` that commutes with left translations. Composition corresponds
to convolution: `ρ(e) ∘ ρ(e')` is `ρ` of `h ↦ ∫ g, e g * e' (g⁻¹ * h) ∂μ`.

An **idempotent kernel** is a continuous integrable `e` with `e g⁻¹ = conj (e g)`, `e 1 ≠ 0` and
`∫ z, e z * e ((z * x)⁻¹ * y) ∂μ = e x⁻¹ / e 1 * e y` for all `x` and `y`: in terms of convolution,
`e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e`, so that `e` is a self-adjoint idempotent of rank one. The
normalized coefficients `deg_π · conj ⟨π(g) v, v⟩` of a unit vector `v` in an integrable discrete
series representation `π` are the basic examples. Taking `x = 1` shows `e ⋆ e = e`, and evaluating
at `y = 1` gives `e 1 = ∫ ‖e‖²`, a positive real number.

The main theorem, `TauCeti.rightRegularIntegral_eq_zero`, is the vanishing of the constant terms
of an integrable idempotent `e ⋆ e = e`. Let `H : G → ℝ` be a continuous height whose right
variation `|H (x * g) - H x|` is bounded by `ℓ g` with `‖e‖ * ℓ` integrable, and let `D` be a
subgroup of `G × ℂˣ` whose elements `(r, c)` shift the height, `H (r * g) = H g - log ‖c‖`, and
which contains dilations `(x * b * x⁻¹, c)` with `log ‖c‖ ≠ 0` and `b` in any prescribed
neighbourhood of `1`, simultaneously for all `x`. Then `ρ(e) f = 0` for every bounded continuous
`f` that is left invariant under the radical `{r | (r, 1) ∈ D}`. Applied to the dilations of a
parabolic subgroup of a unitary group and a height `H`, this is the analytic input of the theorem
that coefficients of integrable discrete series are cusp forms.

The proof is an operator argument on the Banach space `V` of bounded continuous functions that
are invariant under the radical and reproduced by `e`. Every `ρ(e) f` lies in `V`, so it
suffices that `V = 0`. The twisted operator `T = ρ(e) ∘ exp(i t H)` maps `V` to itself, and on `V`
it is within `|t| ∫ ‖e‖ ℓ` of multiplication by the phase `exp(i t H)`, so it is injective for
small `t`. Left translation by an element `(r₀, c)` of `D` maps `V` to itself and multiplies the
phase by `exp(-i t log ‖c‖)`; choosing `t` so that a power `T ^ k` acquires the factor `-1`, left
translation anticommutes with `T ^ k`. On functions invariant under the radical, left translation
by `r₀` agrees at each point `x` with left translation by any `x * b * x⁻¹` with the same `c`,
and functions reproduced by `e` are uniformly continuous under small right translations, so left
translation by `r₀` is within `1 / 2` of the identity on `V`. An operator anticommuting with one so
close to the identity vanishes (`TauCeti.eq_zero_of_norm_sub_one_lt_one_of_mul_eq_neg_mul`), so
`T ^ k = 0` on `V`, and injectivity gives `V = 0`. Only the idempotence `e ⋆ e = e` of the
kernel enters; neither its continuity nor its symmetry nor the rank-one identity is used.

## Main definitions

* `TauCeti.rightRegularIntegral e μ`: the operator `F ↦ (x ↦ ∫ g, e g * F (x * g) ∂μ)` on
  bounded continuous functions, for integrable `e`.
* `TauCeti.IsIdempotentKernel e μ`: `e` is an idempotent kernel.

## Main results

* `TauCeti.rightRegularIntegral_apply`, `TauCeti.norm_rightRegularIntegral_le`: the defining
  integral and the bound `‖ρ(e)‖ ≤ ∫ ‖e‖`.
* `TauCeti.rightRegularIntegral_compContinuous_mulLeft`: `ρ(e)` commutes with left translations.
* `TauCeti.rightRegularIntegral_rightRegularIntegral_apply`: `ρ(e) ∘ ρ(e')` is integration
  against the convolution of `e` and `e'`.
* `TauCeti.IsIdempotentKernel.integral_mul_inv_mul`: an idempotent kernel satisfies `e ⋆ e = e`.
* `TauCeti.IsIdempotentKernel.apply_one_eq_integral_norm_sq`,
  `TauCeti.IsIdempotentKernel.integral_norm_sq_pos`: `e 1 = ∫ ‖e‖² > 0`.
* `TauCeti.rightRegularIntegral_eq_zero`: an integrable idempotent `e ⋆ e = e` kills the bounded
  continuous functions invariant under the radical of a group of dilations.
* `TauCeti.IsIdempotentKernel.integral_mul_comp_mul_left_eq_zero`: the same statement for an
  idempotent kernel, `∫ g, e g * f (x * g) ∂μ = 0`.

## References

* R. Godement, C. R. Acad. Sci. Paris 225 (1947), for the cuspidality of coefficients of
  integrable discrete series.
* N. R. Wallach, *Real reductive groups I*, Academic Press (1988), Chapter 7.
* B. Barnes, Proc. Edinburgh Math. Soc. 23 (1980), and A. Valette, Math. Ann. 294 (1992), for
  arguments through minimal idempotents.

## Provenance

The strategy of the proof of `TauCeti.rightRegularIntegral_eq_zero` (a reproducing operator
twisted by a phase of the height, and a dilation close to the identity anticommuting with a power
of it) is that of `New.DiscreteSeries.integral_idempotentKernel_mul_eq_zero` (file
`src/Lib/DiscreteSeries/CuspKernel.lean`) in grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC). The statement here is more general: only the
idempotence `e ⋆ e = e` of the kernel is assumed.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ComplexConjugate

namespace TauCeti

variable {G : Type*}

section RightRegularIntegral

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {e : G → ℂ} {μ : Measure G}

/-- For integrable `e` and bounded continuous `F`, the integrand `g ↦ e g * F (x * g)` is
integrable. -/
private theorem integrable_mul_apply_mul (he : Integrable e μ) (F : G →ᵇ ℂ) (x : G) :
    Integrable (fun g => e g * F (x * g)) μ :=
  he.mul_bdd (F.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun g => F.norm_coe_le_norm (x * g))

omit [IsTopologicalGroup G] [BorelSpace G] in
private theorem norm_integral_mul_apply_mul_le (he : Integrable e μ) (F : G →ᵇ ℂ) (x : G) :
    ‖∫ g, e g * F (x * g) ∂μ‖ ≤ (∫ g, ‖e g‖ ∂μ) * ‖F‖ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (he.norm.mul_const _) (Eventually.of_forall fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (F.norm_coe_le_norm _) (norm_nonneg _)

private theorem continuous_integral_mul_apply_mul [FirstCountableTopology G]
    (he : Integrable e μ) (F : G →ᵇ ℂ) : Continuous fun x => ∫ g, e g * F (x * g) ∂μ :=
  continuous_of_dominated (bound := fun g => ‖e g‖ * ‖F‖)
    (fun x => (integrable_mul_apply_mul he F x).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun g => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (F.norm_coe_le_norm _) (norm_nonneg _))
    (he.norm.mul_const _)
    (Eventually.of_forall fun g =>
      continuous_const.mul (F.continuous.comp (continuous_id.mul continuous_const)))

/-- The bounded continuous function `x ↦ ∫ g, e g * F (x * g) ∂μ`, for integrable `e`. -/
private def rightRegularIntegralAux [FirstCountableTopology G] (he : Integrable e μ)
    (F : G →ᵇ ℂ) : G →ᵇ ℂ :=
  .ofNormedAddCommGroup _ (continuous_integral_mul_apply_mul he F) _
    (norm_integral_mul_apply_mul_le he F)

variable [FirstCountableTopology G]

open scoped Classical in
variable (e μ) in
/-- **The right regular representation integrated against `e`**: the operator
`F ↦ (x ↦ ∫ g, e g * F (x * g) ∂μ)` on bounded continuous functions, for integrable `e`, and `0`
otherwise. It is `∫ g, e g • R_g ∂μ` for the right translations `(R_g F)(x) = F (x * g)`; it
commutes with left translations, and for a left-invariant measure composition corresponds to
convolution (`TauCeti.rightRegularIntegral_rightRegularIntegral_apply`). -/
def rightRegularIntegral : (G →ᵇ ℂ) →L[ℂ] G →ᵇ ℂ :=
  if he : Integrable e μ then
    LinearMap.mkContinuous
      { toFun := rightRegularIntegralAux he
        map_add' := fun F F' => by
          ext x
          simp [rightRegularIntegralAux, mul_add,
            integral_add (integrable_mul_apply_mul he F x) (integrable_mul_apply_mul he F' x)]
        map_smul' := fun c F => by
          ext x
          simp [rightRegularIntegralAux, mul_left_comm _ c, integral_const_mul] }
      (∫ g, ‖e g‖ ∂μ) fun F =>
        BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
          (mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (norm_nonneg _))
          (norm_integral_mul_apply_mul_le he F)
  else 0

/-- The value of `ρ(e) F` at `x` is `∫ g, e g * F (x * g) ∂μ`. -/
theorem rightRegularIntegral_apply (he : Integrable e μ) (F : G →ᵇ ℂ) (x : G) :
    rightRegularIntegral e μ F x = ∫ g, e g * F (x * g) ∂μ := by
  simp only [rightRegularIntegral, he, ↓reduceDIte]
  rfl

/-- The operator norm of `ρ(e)` is at most `∫ ‖e‖`. -/
theorem norm_rightRegularIntegral_le : ‖rightRegularIntegral e μ‖ ≤ ∫ g, ‖e g‖ ∂μ := by
  have h0 : 0 ≤ ∫ g, ‖e g‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  by_cases he : Integrable e μ
  · refine ContinuousLinearMap.opNorm_le_bound _ h0 fun F =>
      (BoundedContinuousFunction.norm_le (mul_nonneg h0 (norm_nonneg _))).2 fun x => ?_
    rw [rightRegularIntegral_apply he]
    exact norm_integral_mul_apply_mul_le he F x
  · simpa [rightRegularIntegral, he] using h0

/-- `ρ(e)` commutes with left translations. -/
@[simp]
theorem rightRegularIntegral_compContinuous_mulLeft (F : G →ᵇ ℂ) (r : G) :
    rightRegularIntegral e μ (F.compContinuous (ContinuousMap.mulLeft r)) =
      (rightRegularIntegral e μ F).compContinuous (ContinuousMap.mulLeft r) := by
  by_cases he : Integrable e μ
  · ext x
    simp [rightRegularIntegral_apply he, mul_assoc]
  · simp [rightRegularIntegral, he]

variable [μ.IsMulLeftInvariant]

/-- Right translation of `ρ(e) F` is left translation of `e`:
`(ρ(e) F)(x * b) = ∫ g, e (b⁻¹ * g) * F (x * g) ∂μ`. -/
theorem rightRegularIntegral_apply_mul (he : Integrable e μ) (F : G →ᵇ ℂ) (x b : G) :
    rightRegularIntegral e μ F (x * b) = ∫ g, e (b⁻¹ * g) * F (x * g) ∂μ := by
  rw [rightRegularIntegral_apply he,
    ← integral_mul_left_eq_self (fun g => e (b⁻¹ * g) * F (x * g)) b]
  simp [mul_assoc]

/-- **Composition is convolution**: `ρ(e) (ρ(e') F)` is integration against the convolution
`h ↦ ∫ g, e g * e' (g⁻¹ * h) ∂μ` of `e` and `e'`. -/
theorem rightRegularIntegral_rightRegularIntegral_apply [SecondCountableTopology G] [SFinite μ]
    {e' : G → ℂ} (he : Integrable e μ) (he' : Integrable e' μ) (F : G →ᵇ ℂ) (x : G) :
    rightRegularIntegral e μ (rightRegularIntegral e' μ F) x =
      ∫ h, (∫ g, e g * e' (g⁻¹ * h) ∂μ) * F (x * h) ∂μ := by
  -- `Φ` is the integrand in the variables `(g, h)` of `ρ(e) ρ(e')`, and `Ψ` is `Φ` after the
  -- shear `(g, h) ↦ (g, g * h)`, which preserves `μ × μ`.
  set Φ : G × G → ℂ := fun q => e q.1 * e' q.2 * F (x * (q.1 * q.2))
  set Ψ : G × G → ℂ := fun q => e q.1 * e' (q.1⁻¹ * q.2) * F (x * q.2)
  have hm := measurePreserving_prod_mul μ μ
  have hm' := (MeasurableEquiv.shearMulRight G).measurableEmbedding
  have hΨΦ : Ψ ∘ (fun q : G × G => (q.1, q.1 * q.2)) = Φ := by
    ext q; simp [Ψ, Φ]
  have hΦ : Integrable Φ (μ.prod μ) :=
    (he.mul_prod he').mul_bdd
      (F.continuous.comp (continuous_const.mul continuous_mul)).aestronglyMeasurable
      (Eventually.of_forall fun q => F.norm_coe_le_norm _)
  have hΨ : Integrable Ψ (μ.prod μ) := (hm.integrable_comp_emb hm').1 (hΨΦ ▸ hΦ)
  calc rightRegularIntegral e μ (rightRegularIntegral e' μ F) x
      = ∫ g, ∫ h, Φ (g, h) ∂μ ∂μ := by
        simp_rw [rightRegularIntegral_apply he, rightRegularIntegral_apply he', Φ,
          ← integral_const_mul, mul_assoc]
    _ = ∫ q, Ψ q ∂(μ.prod μ) := by
        rw [← integral_prod Φ hΦ, ← hΨΦ]
        exact hm.integral_comp hm' Ψ
    _ = ∫ h, ∫ g, Ψ (g, h) ∂μ ∂μ := integral_prod_symm Ψ hΨ
    _ = _ := by simp_rw [Ψ, integral_mul_const]

end RightRegularIntegral

section IdempotentKernel

variable [Group G] [TopologicalSpace G] [MeasurableSpace G]

/-- An **idempotent kernel** on a group `G` with a measure `μ`: a continuous integrable
`e : G → ℂ` with `e g⁻¹ = conj (e g)`, `e 1 ≠ 0` and
`∫ z, e z * e ((z * x)⁻¹ * y) ∂μ = e x⁻¹ / e 1 * e y` for all `x` and `y`. In terms of
convolution the last identity reads `e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e`: `e` is a self-adjoint
idempotent (`TauCeti.IsIdempotentKernel.integral_mul_inv_mul`) of rank one. -/
structure IsIdempotentKernel (e : G → ℂ) (μ : Measure G) : Prop where
  /-- An idempotent kernel is continuous. -/
  continuous : Continuous e
  /-- An idempotent kernel is integrable. -/
  integrable : Integrable e μ
  /-- An idempotent kernel is hermitian: `e g⁻¹ = conj (e g)`. -/
  apply_inv (g : G) : e g⁻¹ = conj (e g)
  /-- An idempotent kernel does not vanish at `1`. -/
  apply_one_ne_zero : e 1 ≠ 0
  /-- The rank-one idempotence identity `e ⋆ δ_x ⋆ e = (e x⁻¹ / e 1) • e`. -/
  integral_mul_mul_inv_mul (x y : G) : ∫ z, e z * e ((z * x)⁻¹ * y) ∂μ = e x⁻¹ / e 1 * e y

namespace IsIdempotentKernel

variable {e : G → ℂ} {μ : Measure G}

/-- **An idempotent kernel is idempotent for convolution**: `∫ z, e z * e (z⁻¹ * y) ∂μ = e y`. -/
theorem integral_mul_inv_mul (he : IsIdempotentKernel e μ) (y : G) :
    ∫ z, e z * e (z⁻¹ * y) ∂μ = e y := by
  simpa [div_self he.apply_one_ne_zero] using he.integral_mul_mul_inv_mul 1 y

/-- The value of an idempotent kernel at `1` is the square of its `L²` norm:
`e 1 = ∫ ‖e‖²`. -/
theorem apply_one_eq_integral_norm_sq (he : IsIdempotentKernel e μ) :
    e 1 = ((∫ z, ‖e z‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal, ← he.integral_mul_inv_mul 1]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [he.apply_inv, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The value of an idempotent kernel at `1` is a positive real number: `0 < ∫ ‖e‖²`. -/
theorem integral_norm_sq_pos (he : IsIdempotentKernel e μ) : 0 < ∫ z, ‖e z‖ ^ 2 ∂μ := by
  refine (integral_nonneg fun z => by positivity).lt_of_ne fun h => he.apply_one_ne_zero ?_
  rw [he.apply_one_eq_integral_norm_sq, ← h, Complex.ofReal_zero]

/-- An idempotent kernel is square integrable. -/
theorem memLp_two (he : IsIdempotentKernel e μ) : MemLp e 2 μ :=
  (memLp_two_iff_integrable_sq_norm he.integrable.aestronglyMeasurable).2 <|
    Integrable.of_integral_ne_zero he.integral_norm_sq_pos.ne'

end IsIdempotentKernel

end IdempotentKernel

section Phase

variable [TopologicalSpace G] {H : G → ℝ} (hH : Continuous H)

/-- The phase `z ↦ exp (i t H z)`, a bounded continuous function of modulus one. -/
private def phase (t : ℝ) : G →ᵇ ℂ :=
  .ofNormedAddCommGroup (fun z => Complex.exp (Complex.I * ↑(t * H z))) (by fun_prop) 1
    fun z => (Complex.norm_exp_I_mul_ofReal _).le

private theorem phase_apply (t : ℝ) (z : G) :
    phase hH t z = Complex.exp (Complex.I * ↑(t * H z)) :=
  rfl

private theorem norm_phase_apply (t : ℝ) (z : G) : ‖phase hH t z‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

include hH in
/-- The right variation of the phase is controlled by that of `H`. -/
private theorem norm_phase_mul_sub_le [Group G] {ℓ : G → ℝ}
    (hHℓ : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g) (t : ℝ)
    (z g : G) : ‖phase hH t (z * g) - phase hH t z‖ ≤ |t| * ℓ g := by
  have h : phase hH t (z * g) - phase hH t z =
      phase hH t z * (Complex.exp (Complex.I * ↑(t * (H (z * g) - H z))) - 1) := by
    rw [phase_apply, phase_apply, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, norm_phase_apply, one_mul]
  calc _ ≤ ‖t * (H (z * g) - H z)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |t| * |H (z * g) - H z| := by rw [Real.norm_eq_abs, abs_mul]
    _ ≤ |t| * ℓ g := mul_le_mul_of_nonneg_left (hHℓ z g) (abs_nonneg t)

/-- An element `(r, c)` of `D` multiplies the phase by `exp (-i t log ‖c‖)`. -/
private theorem phase_mul_left [Group G] {D : Subgroup (G × ℂˣ)}
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖)
    {r : G} {c : ℂˣ} (hrc : (r, c) ∈ D) (t : ℝ) (z : G) :
    phase hH t (r * z) =
      Complex.exp (-(Complex.I * ↑(t * Real.log ‖(c : ℂ)‖))) * phase hH t z := by
  rw [phase_apply, phase_apply, ← Complex.exp_add, hD_shift _ hrc z]
  congr 1
  push_cast
  ring

end Phase

section Vanishing

/-- If `S` and `A` preserve a submodule `V`, `S` anticommutes with `A`, and `S` moves every
element of `V` by at most `δ < 1` times its norm, then `A` vanishes on `V`. -/
private theorem apply_eq_zero_of_mul_eq_neg_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {V : Submodule ℂ E} {S A : E →L[ℂ] E} (hS : ∀ x ∈ V, S x ∈ V)
    (hA : ∀ x ∈ V, A x ∈ V) (h : S * A = -(A * S)) {δ : ℝ} (hδ : δ < 1)
    (hSV : ∀ x ∈ V, ‖S x - x‖ ≤ δ * ‖x‖) {x : E} (hx : x ∈ V) : A x = 0 := by
  have hcomm : S.restrict hS * A.restrict hA = -(A.restrict hA * S.restrict hS) := by
    ext y
    simpa using congrArg (fun T : E →L[ℂ] E => T y) h
  have hnear : ‖S.restrict hS - 1‖ < 1 := by
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (le_max_right δ 0) fun y => ?_)
      (max_lt hδ one_pos)
    simpa using (hSV y y.property).trans
      (mul_le_mul_of_nonneg_right (le_max_left δ 0) (norm_nonneg y))
  have h0 := eq_zero_of_norm_sub_one_lt_one_of_mul_eq_neg_mul (A := V →L[ℂ] V) hnear hcomm
  simpa using congrArg (fun T : V →L[ℂ] V => (T ⟨x, hx⟩ : E)) h0

/-- If `a * b = z • (b * a)`, then `a * b ^ n = z ^ n • (b ^ n * a)`. -/
private theorem mul_pow_eq_smul {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    {a b : A} {z : R} (h : a * b = z • (b * a)) (n : ℕ) : a * b ^ n = z ^ n • (b ^ n * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h, mul_smul_comm, smul_smul,
      ← mul_assoc, ← pow_succ]

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {e : G → ℂ} {μ : Measure G} [μ.IsMulLeftInvariant]
  {D : Subgroup (G × ℂˣ)} {H ℓ : G → ℝ} (hH : Continuous H)

variable (e μ D) in
/-- The bounded continuous functions `F` reproduced by `e`, `ρ(e) F = F`, and left invariant
under the radical `{r | (r, 1) ∈ D}`. -/
private def reproducing : Submodule ℂ (G →ᵇ ℂ) where
  carrier := {F | rightRegularIntegral e μ F = F ∧
    ∀ r : G, (r, (1 : ℂˣ)) ∈ D → ∀ g, F (r * g) = F g}
  add_mem' {F F'} hF hF' :=
    ⟨by rw [map_add, hF.1, hF'.1], fun r hr g => by simp [hF.2 r hr g, hF'.2 r hr g]⟩
  zero_mem' := ⟨map_zero _, fun _ _ _ => rfl⟩
  smul_mem' c F hF := ⟨by rw [map_smul, hF.1], fun r hr g => by simp [hF.2 r hr g]⟩

/-- An idempotent `e ⋆ e = e` maps the functions invariant under the radical into `V`. -/
private theorem rightRegularIntegral_mem_reproducing [SFinite μ] (he : Integrable e μ)
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e) {f : G →ᵇ ℂ}
    (hf : ∀ r : G, (r, (1 : ℂˣ)) ∈ D → ∀ g, f (r * g) = f g) :
    rightRegularIntegral e μ f ∈ reproducing e μ D := by
  refine ⟨?_, fun r hr g => ?_⟩
  · ext x
    rw [rightRegularIntegral_rightRegularIntegral_apply he he, rightRegularIntegral_apply he]
    refine integral_congr_ae ?_
    filter_upwards [he_idem] with h hh
    rw [hh]
  · simp only [rightRegularIntegral_apply he, mul_assoc, hf r hr]

variable (e μ) in
/-- The twisted reproducing operator `F ↦ ρ(e) (exp (i t H) * F)`. -/
private def twisted (t : ℝ) : (G →ᵇ ℂ) →L[ℂ] G →ᵇ ℂ :=
  rightRegularIntegral e μ ∘L ContinuousLinearMap.mul ℂ (G →ᵇ ℂ) (phase hH t)

omit [μ.IsMulLeftInvariant] in
private theorem twisted_apply (t : ℝ) (F : G →ᵇ ℂ) :
    twisted e μ hH t F = rightRegularIntegral e μ (phase hH t * F) :=
  rfl

/-- The twisted operator maps `V` into itself. -/
private theorem twisted_mem_reproducing [SFinite μ] (he : Integrable e μ)
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e)
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖) (t : ℝ)
    {F : G →ᵇ ℂ} (hF : F ∈ reproducing e μ D) : twisted e μ hH t F ∈ reproducing e μ D :=
  rightRegularIntegral_mem_reproducing he he_idem fun r hr g => by
    simp [phase_mul_left hH hD_shift hr, hF.2 r hr g]

omit [μ.IsMulLeftInvariant] in
/-- Left translation by the first component of an element of `D` maps `V` into itself, since it
normalizes the radical. -/
private theorem compContinuous_mulLeft_mem_reproducing {r : G} {c : ℂˣ} (hrc : (r, c) ∈ D)
    {F : G →ᵇ ℂ} (hF : F ∈ reproducing e μ D) :
    F.compContinuous (ContinuousMap.mulLeft r) ∈ reproducing e μ D := by
  refine ⟨by rw [rightRegularIntegral_compContinuous_mulLeft, hF.1], fun ρ hρ g => ?_⟩
  have hmem : (r * ρ * r⁻¹, (1 : ℂˣ)) ∈ D := by
    simpa using D.mul_mem (D.mul_mem hrc hρ) (D.inv_mem hrc)
  simpa [mul_assoc] using hF.2 _ hmem (r * g)

omit [μ.IsMulLeftInvariant] in
/-- Left translation by `r` with `(r, c) ∈ D` commutes with the twisted operator up to the
factor `exp (-i t log ‖c‖)`. -/
private theorem compContinuousCLM_mul_twisted
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖) {r : G} {c : ℂˣ}
    (hrc : (r, c) ∈ D) (t : ℝ) :
    BoundedContinuousFunction.compContinuousCLM ℂ ℂ (ContinuousMap.mulLeft r) * twisted e μ hH t =
      Complex.exp (-(Complex.I * ↑(t * Real.log ‖(c : ℂ)‖))) •
        (twisted e μ hH t * BoundedContinuousFunction.compContinuousCLM ℂ ℂ
          (ContinuousMap.mulLeft r)) := by
  ext F : 1
  simp only [mul_apply_eq_comp, smul_apply, BoundedContinuousFunction.compContinuousCLM_apply,
    twisted_apply, ← rightRegularIntegral_compContinuous_mulLeft]
  have h : (phase hH t * F).compContinuous (ContinuousMap.mulLeft r) =
      Complex.exp (-(Complex.I * ↑(t * Real.log ‖(c : ℂ)‖))) •
        (phase hH t * F.compContinuous (ContinuousMap.mulLeft r)) := by
    ext z
    simp [phase_mul_left hH hD_shift hrc, mul_assoc]
  rw [h, map_smul]

/-- **Left translation by `r₀` is close to the identity on `V`.** At each point `z`, left
translation by `r₀` agrees on `V` with left translation by a conjugate `z * b * z⁻¹` carrying the
same `c`, that is with right translation by `b`, which moves functions reproduced by `e` by at
most `∫ ‖e (b⁻¹ * ·) - e‖` times their norm. -/
private theorem norm_compContinuous_mulLeft_sub_le (he : Integrable e μ) {W : Set G} {δ : ℝ}
    (hδ : 0 ≤ δ) (hW : ∀ b ∈ W, ∫ g, ‖e (b⁻¹ * g) - e g‖ ∂μ ≤ δ) {r₀ : G} {c : ℂˣ}
    (hr₀ : (r₀, c) ∈ D) (hc : ∀ x : G, ∃ b ∈ W, (x * b * x⁻¹, c) ∈ D) {F : G →ᵇ ℂ}
    (hF : F ∈ reproducing e μ D) :
    ‖F.compContinuous (ContinuousMap.mulLeft r₀) - F‖ ≤ δ * ‖F‖ := by
  refine (BoundedContinuousFunction.norm_le (mul_nonneg hδ (norm_nonneg F))).2 fun z => ?_
  obtain ⟨b, hbW, hb⟩ := hc z
  have hρ : (r₀ * (z * b * z⁻¹)⁻¹, (1 : ℂˣ)) ∈ D := by
    simpa using D.mul_mem hr₀ (D.inv_mem hb)
  have h₁ : F (r₀ * z) = F (z * b) := by
    rw [← hF.2 _ hρ (z * b)]
    group
  have hint : Integrable (fun g => e (b⁻¹ * g) * F (z * g)) μ :=
    (he.comp_mul_left b⁻¹).mul_bdd
      (F.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun g => F.norm_coe_le_norm _)
  have h₂ : F (z * b) - F z = ∫ g, (e (b⁻¹ * g) - e g) * F (z * g) ∂μ := by
    have hb' : F (z * b) = ∫ g, e (b⁻¹ * g) * F (z * g) ∂μ := by
      rw [← rightRegularIntegral_apply_mul he, hF.1]
    have hz : F z = ∫ g, e g * F (z * g) ∂μ := by
      rw [← rightRegularIntegral_apply he, hF.1]
    rw [hb', hz, ← integral_sub hint (integrable_mul_apply_mul he F z)]
    simp_rw [sub_mul]
  rw [sub_apply,
    BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mulLeft, h₁, h₂]
  calc _ ≤ ∫ g, ‖e (b⁻¹ * g) - e g‖ * ‖F‖ ∂μ :=
        norm_integral_le_of_norm_le (((he.comp_mul_left b⁻¹).sub he).norm.mul_const _)
          (Eventually.of_forall fun g => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (F.norm_coe_le_norm _) (norm_nonneg _))
    _ ≤ δ * ‖F‖ := by
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right (hW b hbW) (norm_nonneg F)

omit [μ.IsMulLeftInvariant] in
/-- **The twisted operator is injective on reproduced functions** for small `t`: it is within
`|t| ∫ ‖e‖ ℓ` of multiplication by the phase, which preserves the norm. -/
private theorem norm_mul_one_sub_le_norm_twisted (he : Integrable e μ)
    (hHℓ : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g) (hℓ : Integrable (fun g => ‖e g‖ * ℓ g) μ)
    (t : ℝ) {F : G →ᵇ ℂ} (hF : rightRegularIntegral e μ F = F) :
    ‖F‖ * (1 - |t| * ∫ g, ‖e g‖ * ℓ g ∂μ) ≤ ‖twisted e μ hH t F‖ := by
  set C := ∫ g, ‖e g‖ * ℓ g ∂μ
  have hC : 0 ≤ C := integral_nonneg fun g =>
    mul_nonneg (norm_nonneg _) ((abs_nonneg _).trans (hHℓ 1 g))
  suffices h : ‖F‖ ≤ ‖twisted e μ hH t F‖ + |t| * C * ‖F‖ by linarith
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun z => ?_
  have hφF : Integrable (fun g => e g * (phase hH t * F) (z * g)) μ :=
    integrable_mul_apply_mul he _ z
  -- `T F z - φ z * F z` is the integral of `e g * (φ (z * g) - φ z) * F (z * g)`.
  have hFz : F z = ∫ g, e g * F (z * g) ∂μ := by rw [← rightRegularIntegral_apply he, hF]
  have hd : twisted e μ hH t F z - phase hH t z * F z =
      ∫ g, e g * (phase hH t (z * g) - phase hH t z) * F (z * g) ∂μ := by
    rw [twisted_apply, rightRegularIntegral_apply he, hFz, ← integral_const_mul,
      ← integral_sub hφF ((integrable_mul_apply_mul he F z).const_mul _)]
    congr 1 with g
    simp only [FunLike.coe_mul, Pi.mul_apply]
    ring
  have hpt : ∀ g, ‖e g * (phase hH t (z * g) - phase hH t z) * F (z * g)‖ ≤
      |t| * ‖F‖ * (‖e g‖ * ℓ g) := fun g => by
    rw [norm_mul, norm_mul]
    have h₁ := norm_phase_mul_sub_le hH hHℓ t z g
    have h₂ := F.norm_coe_le_norm (z * g)
    have h₃ : 0 ≤ ℓ g := (abs_nonneg _).trans (hHℓ 1 g)
    calc _ ≤ ‖e g‖ * (|t| * ℓ g) * ‖F‖ := by gcongr
      _ = _ := by ring
  have hle : ‖twisted e μ hH t F z - phase hH t z * F z‖ ≤ |t| * C * ‖F‖ := by
    rw [hd]
    calc _ ≤ ∫ g, |t| * ‖F‖ * (‖e g‖ * ℓ g) ∂μ :=
          norm_integral_le_of_norm_le (hℓ.const_mul _) (Eventually.of_forall hpt)
      _ = |t| * C * ‖F‖ := by rw [integral_const_mul]; ring
  calc ‖F z‖ = ‖phase hH t z * F z‖ := by rw [norm_mul, norm_phase_apply, one_mul]
    _ = ‖twisted e μ hH t F z - (twisted e μ hH t F z - phase hH t z * F z)‖ := by
        rw [sub_sub_cancel]
    _ ≤ ‖twisted e μ hH t F z‖ + ‖twisted e μ hH t F z - phase hH t z * F z‖ :=
        norm_sub_le _ _
    _ ≤ _ := add_le_add ((twisted e μ hH t F).norm_coe_le_norm z) hle

omit [SecondCountableTopology G] [BorelSpace G] in
/-- The left translates of an integrable function converge to it in `L¹`:
`∫ ‖e (b⁻¹ * ·) - e‖ → 0` as `b → 1`. -/
private theorem tendsto_integral_norm_comp_inv_mul_sub [BorelSpace G] [IsLocallyFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] (he : Integrable e μ) :
    Tendsto (fun b => ∫ g, ‖e (b⁻¹ * g) - e g‖ ∂μ) (𝓝 1) (𝓝 0) := by
  have hinv : Tendsto (fun b : G => b⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (continuous_inv (G := G)).tendsto 1
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (((memLp_one_iff_integrable.2 he).tendsto_eLpNorm_comp_mul_left_sub
      ENNReal.one_ne_top).comp hinv)
  rw [ENNReal.toReal_zero] at h
  refine h.congr fun b => ?_
  have hm : AEStronglyMeasurable (fun x => e (b⁻¹ * x) - e x) μ :=
    ((he.comp_mul_left b⁻¹).sub he).aestronglyMeasurable
  simp only [Function.comp_apply]
  rw [eLpNorm_one_eq_lintegral_eNorm hm, ← integral_norm_eq_lintegral_eNorm hm]

/-- A twist `t` and a power `k` with `|t| * C < 1` and `exp (-i t L) ^ k = -1`, for `0 ≤ C`
and `L ≠ 0`. -/
private theorem exists_abs_mul_lt_one_and_exp_pow_eq_neg_one {C L : ℝ} (hC : 0 ≤ C)
    (hL : L ≠ 0) :
    ∃ (k : ℕ) (t : ℝ), |t| * C < 1 ∧ Complex.exp (-(Complex.I * ↑(t * L))) ^ k = -1 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (Real.pi * C / |L|)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
  set t := Real.pi / (k * L) with ht
  refine ⟨k, t, ?_, ?_⟩
  · rw [ht, abs_div, abs_mul, abs_of_pos Real.pi_pos, Nat.abs_cast, div_mul_eq_mul_div,
      div_lt_one (by positivity)]
    rwa [div_lt_iff₀ (abs_pos.2 hL)] at hk
  · have htL : (k : ℝ) * (t * L) = Real.pi := by
      rw [ht]
      field_simp
    have h : (k : ℂ) * -(Complex.I * ↑(t * L)) = -(Real.pi * Complex.I) := by
      rw [← htL]
      push_cast
      ring
    rw [← Complex.exp_natCast_mul, h, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

/-- The powers of the twisted operator map `V` into itself. -/
private theorem pow_twisted_mem_reproducing [SFinite μ] (he : Integrable e μ)
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e)
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖) (t : ℝ) (n : ℕ)
    {F : G →ᵇ ℂ} (hF : F ∈ reproducing e μ D) :
    (twisted e μ hH t ^ n) F ∈ reproducing e μ D := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact twisted_mem_reproducing hH he he_idem hD_shift t ih

/-- On `V`, the powers of the twisted operator satisfy
`‖F‖ * (1 - |t| ∫ ‖e‖ ℓ) ^ n ≤ ‖T ^ n F‖`. -/
private theorem norm_mul_pow_le_norm_pow_twisted [SFinite μ] (he : Integrable e μ)
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e)
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖)
    (hHℓ : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g) (hℓ : Integrable (fun g => ‖e g‖ * ℓ g) μ)
    {t : ℝ} (ht : |t| * ∫ g, ‖e g‖ * ℓ g ∂μ ≤ 1) (n : ℕ) {F : G →ᵇ ℂ}
    (hF : F ∈ reproducing e μ D) :
    ‖F‖ * (1 - |t| * ∫ g, ‖e g‖ * ℓ g ∂μ) ^ n ≤ ‖(twisted e μ hH t ^ n) F‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (twisted e μ hH t) n, mul_apply_eq_comp, pow_succ, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right ih (by linarith)).trans
      (norm_mul_one_sub_le_norm_twisted hH he hHℓ hℓ t
        (pow_twisted_mem_reproducing hH he he_idem hD_shift t n hF).1)

omit [μ.IsMulLeftInvariant] in
include hH in
/-- **An integrable idempotent kills the functions invariant under the radical of a group of
dilations.** Let `μ` be a left Haar measure on a second countable locally compact group `G`, and
`e : G → ℂ` with `e ⋆ e = e` almost everywhere (the statement has content for integrable `e`;
otherwise `ρ(e) = 0` by definition). Let `H : G → ℝ` be continuous with
`|H (x * g) - H x| ≤ ℓ g` and `‖e‖ * ℓ` integrable, and `D` a subgroup of `G × ℂˣ` such that
`H (r * g) = H g - log ‖c‖` for `(r, c) ∈ D`, and such that every neighbourhood `W` of `1` has a
`c` with `log ‖c‖ ≠ 0` for which every `x` admits `b ∈ W` with `(x * b * x⁻¹, c) ∈ D`. Then
`ρ(e) f = 0`, that is `∫ g, e g * f (x * g) ∂μ = 0` for all `x`, for every bounded continuous `f`
with `f (r * g) = f g` whenever `(r, 1) ∈ D`. -/
theorem rightRegularIntegral_eq_zero [LocallyCompactSpace G] [μ.IsHaarMeasure]
    (he_idem : (fun y => ∫ z, e z * e (z⁻¹ * y) ∂μ) =ᵐ[μ] e)
    (hHℓ : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g) (hℓ : Integrable (fun g => ‖e g‖ * ℓ g) μ)
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖)
    (hD_near : ∀ W ∈ 𝓝 (1 : G), ∃ c : ℂˣ, Real.log ‖(c : ℂ)‖ ≠ 0 ∧
      ∀ x : G, ∃ b ∈ W, (x * b * x⁻¹, c) ∈ D)
    {f : G →ᵇ ℂ} (hf : ∀ r : G, (r, (1 : ℂˣ)) ∈ D → ∀ g : G, f (r * g) = f g) :
    rightRegularIntegral e μ f = 0 := by
  by_cases he : ¬Integrable e μ
  · simp [rightRegularIntegral, he]
  rw [not_not] at he
  -- It suffices that the space `V` of reproduced radical-invariant functions is `0`.
  suffices hV : ∀ F ∈ reproducing e μ D, F = 0 from
    hV _ (rightRegularIntegral_mem_reproducing he he_idem hf)
  intro F hF
  -- A dilation `(b₀, c)` with `log ‖c‖ ≠ 0` whose conjugates `x * b * x⁻¹` carrying the same
  -- `c` have `b` so close to `1` that right translation by `b` moves `V` by at most `1 / 2`.
  obtain ⟨c, hc, hcD⟩ := hD_near _
    ((tendsto_integral_norm_comp_inv_mul_sub he).eventually (gt_mem_nhds one_half_pos))
  obtain ⟨b₀, -, hb₀⟩ := hcD 1
  rw [one_mul, inv_one, mul_one] at hb₀
  -- A twist `t` for which `T ^ k` anticommutes with left translation by `b₀`, and `|t| C < 1`.
  obtain ⟨k, t, htC, hζ⟩ := exists_abs_mul_lt_one_and_exp_pow_eq_neg_one
    (integral_nonneg fun g => mul_nonneg (norm_nonneg (e g)) ((abs_nonneg _).trans (hHℓ 1 g))) hc
  have hST : BoundedContinuousFunction.compContinuousCLM ℂ ℂ (ContinuousMap.mulLeft b₀) *
      twisted e μ hH t ^ k = -(twisted e μ hH t ^ k *
        BoundedContinuousFunction.compContinuousCLM ℂ ℂ (ContinuousMap.mulLeft b₀)) := by
    rw [mul_pow_eq_smul (compContinuousCLM_mul_twisted hH hD_shift hb₀ t) k, hζ, neg_one_smul]
  -- So `T ^ k` vanishes on `V`, while `‖T ^ k F‖ ≥ (1 - |t| C) ^ k ‖F‖`.
  have hzero := apply_eq_zero_of_mul_eq_neg_mul
    (fun F hF => compContinuous_mulLeft_mem_reproducing hb₀ hF)
    (fun F hF => pow_twisted_mem_reproducing hH he he_idem hD_shift t k hF) hST one_half_lt_one
    (fun F hF => norm_compContinuous_mulLeft_sub_le he one_half_pos.le
      (fun b hb => le_of_lt hb) hb₀ hcD hF) hF
  have h := norm_mul_pow_le_norm_pow_twisted hH he he_idem hD_shift hHℓ hℓ htC.le k hF
  rw [hzero, norm_zero] at h
  exact norm_eq_zero.mp <| le_antisymm
    (nonpos_of_mul_nonpos_left h (pow_pos (by linarith) k)) (norm_nonneg F)

end Vanishing

/-- **Idempotent kernels kill the bounded functions invariant under the radical of a group of
dilations**: `∫ g, e g * f (x * g) ∂μ = 0` under the hypotheses of
`TauCeti.rightRegularIntegral_eq_zero`, for an idempotent kernel `e`. -/
theorem IsIdempotentKernel.integral_mul_comp_mul_left_eq_zero [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure] {e : G → ℂ} (he : IsIdempotentKernel e μ)
    {H ℓ : G → ℝ} (hH : Continuous H) (hHℓ : ∀ x g : G, |H (x * g) - H x| ≤ ℓ g)
    (hℓ : Integrable (fun g => ‖e g‖ * ℓ g) μ) {D : Subgroup (G × ℂˣ)}
    (hD_shift : ∀ p ∈ D, ∀ g : G, H (p.1 * g) = H g - Real.log ‖(p.2 : ℂ)‖)
    (hD_near : ∀ W ∈ 𝓝 (1 : G), ∃ c : ℂˣ, Real.log ‖(c : ℂ)‖ ≠ 0 ∧
      ∀ x : G, ∃ b ∈ W, (x * b * x⁻¹, c) ∈ D)
    (f : G →ᵇ ℂ) (hf : ∀ r : G, (r, (1 : ℂˣ)) ∈ D → ∀ g : G, f (r * g) = f g) (x : G) :
    ∫ g, e g * f (x * g) ∂μ = 0 := by
  rw [← rightRegularIntegral_apply he.integrable, rightRegularIntegral_eq_zero hH
    (Eventually.of_forall he.integral_mul_inv_mul) hHℓ hℓ hD_shift hD_near hf]
  rfl

end TauCeti
