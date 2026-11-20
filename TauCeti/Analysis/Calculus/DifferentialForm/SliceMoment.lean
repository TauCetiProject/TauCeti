/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.DifferentialForm.Wedge
import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Topology.Algebra.Module.Alternating.Wedge.TwoForm
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic

/-!
# Moments of the normal slices of a closed two-form

Let `T` be a two-form on a product `E × ℂ`, thought of as a tubular neighbourhood of a
pseudoholomorphic curve with base coordinate `z ∈ E` and complex normal coordinate `w ∈ ℂ`.
Its restriction to the normal fibre `{z} × ℂ` is the signed measure
`μ_z = T(z, w)(∂_x, ∂_y) dx dy`, the *normal slice* of `T` at `z`, where `w = x + i y`. For a
weight `g : ℂ → F` the slice moment is

`sliceMoment T g z = ∫ g dμ_z = ∫_ℂ T(z, w)(∂_x, ∂_y) g(w) dx dy`

(`TauCeti.sliceMoment`). The moments `M_k(z) = ∫ wᵏ dμ_z` and the mixed moments
`Q_ℓ(z) = ∫ w^ℓ \bar w dμ_z` are the cases `g = wᵏ` and `g = w^ℓ \bar w`. In Taubes's analysis
of Seiberg–Witten solutions near a pseudoholomorphic curve, `T` is the rescaled cutoff
curvature current, and the Newton coefficients of the `M_k` are the coefficients of the monic
polynomial whose roots locate the branches of the limiting curve
(`TauCeti.hasFDerivAt_of_newton`, `TauCeti.conjWirtingerDeriv_add_eq_sum_of_newton`).

Suppose that `T` vanishes on `E × (ℂ \ K)` for a compact set `K`. Then:

* if `T` and `g` are `Cⁿ`, so is `sliceMoment T g` (`TauCeti.contDiff_sliceMoment`);
* if `T` and `g` are `C¹` and `T` is closed along the fibre over `z`, the derivative of the slice
  moment is the fibre integral of `dg ∧ T`, with no boundary term:

  `D (sliceMoment T g)(z) v = ∫_ℂ (T(z, w)(v, ∂_x) ∂_y g(w) - T(z, w)(v, ∂_y) ∂_x g(w)) dx dy`

  (`TauCeti.fderiv_sliceMoment_apply`). Here `v` is a base direction, lifted horizontally to
  `(v, 0)`. For `g = wᵏ` this is `dM_k = π_*(k w^(k-1) dw ∧ T)`
  (`TauCeti.fderiv_sliceMoment_pow_apply`).

Further results concern the flux `M₀(z) = ∫ dμ_z` and the pairing of `T` with forms pulled back
from the base, when `E` is two-dimensional with basis `b`:

* if `T` is `C¹` and closed, the slice moment of a constant weight, in particular the flux, does
  not depend on the base point (`TauCeti.sliceMoment_const_eq_sliceMoment_const`);
* for any continuous `T` and a compactly supported base two-form `β`, the integral of `T ∧ π^*β`
  over `E × ℂ` is `∫ M₀ β` (`TauCeti.integral_wedge_compContinuousLinearMap_fst`);
* if moreover `T` is `C¹` and closed, then for a compactly supported `C¹` one-form `η` on
  `E × ℂ`, `∫ T ∧ (c π^*β + dη) = c M₀ ∫ β`
  (`TauCeti.integral_wedge_smul_compContinuousLinearMap_fst_add_extDeriv`): closedness makes the
  flux constant and kills the exact term. When `β` is the area form of the curve and
  `c π^*β + dη` tames the almost complex structure, this is the product-chart form of the pairing
  `T(Ω) = c m area(C)` of a closed current of transverse flux `m` with a taming form; the global
  identity follows by summing over a partition of unity on `C`, which is not done here.

Top-degree coefficients on `E × ℂ` are taken on the product frame `(b₀, 0), (b₁, 0), (0, 1),
(0, i)`, `(b.prod Complex.basisOneI).reindex finSumFinEquiv`, and integrated against its Haar
measure, the product of the Haar measure of `b` and Lebesgue measure on `ℂ`.

Now let the base be a complex normed space `V`, so that `V × ℂ` has the complex structure of
multiplication by `i`, and let the weight `g` be entire. Then `D (sliceMoment T g)(z) v` is the
fibre integral `π_*(g'(w) dw ∧ T)` (`TauCeti.fderiv_sliceMoment_apply_of_differentiable`), and the
conjugate Wirtinger derivative of the slice moment is the same fibre integral with `T` replaced by
its part `T⁻(u, u') = (T(u, u') - T(i u, i u')) / 2` anti-invariant under the complex structure
(`TauCeti.conjWirtingerDeriv_sliceMoment_apply`, with the norm bound
`TauCeti.norm_conjWirtingerDeriv_sliceMoment_apply_le`). For `g = wᵏ` this computes the defects
`E_k = \bar∂ M_k` of the moment equations of `TauCeti.conjWirtingerDeriv_add_eq_sum_of_newton` for
the normal Cauchy–Riemann operator `\bar∂` of the product structure: they are controlled by the
failure of `T` to have type `(1,1)`, and only by it. Hence:

* if `T` is closed and of type `(1,1)`, that is `T(i u, i u') = T(u, u')`, every slice moment of an
  entire weight is holomorphic on the base (`TauCeti.differentiable_sliceMoment`);
* if moreover the slice density `T(z, w)(∂_x, ∂_y)` is bounded, Liouville's theorem makes every such
  slice moment independent of the base point (`TauCeti.sliceMoment_eq_sliceMoment_of_abs_le`), and
  with the moments `M_k` their Newton coefficients are constant. This is the analogue for closed
  forms of the base independence of a confined holomorphic divisor
  (`Differentiable.exists_forall_analyticOrderAt_eq_count`).

More generally, let `D = \bar∂ + ν W + μ \bar W` be a real Cauchy–Riemann operator on the normal
line, with `(0,1)`-forms `ν` and `μ` on `V`, such as the normal operator of a pseudoholomorphic
curve, and let `L w` be the complex structure of `V × ℂ` at `(z, w)` whose holomorphic graphs solve
`D`, `L w (v, 0) = (i v, 2 i (ν(v) w + μ(v) \bar w))` and `L w (0, n) = (0, i n)`. Then the defects
`E_k = \bar∂ M_k + k M_k ν + k Q_{k-1} μ` of the moment equations of `D` are the fibre integrals
`π_*(k w^(k-1) dw ∧ T⁻)`, where now `T⁻` is the part of `T` anti-invariant under `L w`
(`TauCeti.conjWirtingerDeriv_sliceMoment_add_add_apply`,
`TauCeti.conjWirtingerDeriv_sliceMoment_pow_add_add_apply`, with the norm bound
`TauCeti.norm_conjWirtingerDeriv_sliceMoment_add_add_apply_le`). The coefficients `ν` and `μ` are
absorbed exactly; if `T` is invariant under `L w` along the fibre, the moments solve the moment
equations of `D` (`TauCeti.conjWirtingerDeriv_sliceMoment_add_add_eq_zero`).

The derivative formula comes from differentiating under the integral sign and the closedness
`dT = 0`, which trades the base derivative of the slice density for fibre derivatives of the
mixed components `T(v, ∂_x)` and `T(v, ∂_y)`; integrating these by parts over the fibre moves
the derivatives onto `g`, and the compact support in the fibre leaves no boundary term.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Complex

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {T : E × ℂ → (E × ℂ) [⋀^Fin 2]→L[ℝ] ℝ} {g : ℂ → F} {K : Set ℂ}

/-- The moment `∫ g dμ_z` of the normal slice `μ_z = T(z, w)(∂_x, ∂_y) dx dy` of a two-form `T` on
`E × ℂ` over the base point `z`, for a weight `g` on the normal fibre `ℂ`. -/
def sliceMoment (T : E × ℂ → (E × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (g : ℂ → F) (z : E) : F :=
  ∫ w, T (z, w) ![(0, 1), (0, I)] • g w

/-- The slice moment is the integral over the fibre of the slice density times the weight. -/
theorem sliceMoment_def (T : E × ℂ → (E × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (g : ℂ → F) (z : E) :
    sliceMoment T g z = ∫ w, T (z, w) ![(0, 1), (0, I)] • g w := (rfl)

/-- The slice moment of a form supported over `K` integrates over `K` only. -/
private theorem sliceMoment_eq_setIntegral (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) (g : ℂ → F) :
    sliceMoment T g = fun z ↦ ∫ w in K, T (z, w) ![(0, 1), (0, I)] • g w :=
  funext fun z ↦
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ by simp [hT z w hw]).symm

/-- A form vanishing over the open set `ℂ \ K` has vanishing derivative there. -/
private theorem fderiv_eq_zero_of_notMem (hK : IsClosed K) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0)
    (z : E) {w : ℂ} (hw : w ∉ K) : fderiv ℝ T (z, w) = 0 := by
  refine fderiv_of_notMem_tsupport ℝ fun h ↦ hw ?_
  refine (closure_minimal (fun x hx ↦ ?_) (isClosed_univ.prod hK) h).2
  exact ⟨mem_univ _, by_contra fun hxK ↦ hx (hT x.1 x.2 hxK)⟩

/-- The derivative of a coefficient of `T` along the normal fibre over `z`. -/
private theorem hasFDerivAt_coeff_fiber (hTc : ContDiff ℝ 1 T) (z : E) (w : ℂ)
    (A : Fin 2 → E × ℂ) :
    HasFDerivAt (fun w' ↦ T (z, w') A) ((ContinuousAlternatingMap.apply ℝ (E × ℂ) ℝ A).comp
      ((fderiv ℝ T (z, w)).comp (ContinuousLinearMap.inr ℝ E ℂ))) w :=
  (ContinuousAlternatingMap.apply ℝ (E × ℂ) ℝ A).hasFDerivAt.comp w
    (((hTc.differentiable one_ne_zero) (z, w)).hasFDerivAt.comp w (hasFDerivAt_prodMk_right z w))

/-- The derivative of a coefficient of `T` along the base, at a fixed fibre coordinate `w`. -/
private theorem hasFDerivAt_coeff_base (hTc : ContDiff ℝ 1 T) (z : E) (w : ℂ)
    (A : Fin 2 → E × ℂ) :
    HasFDerivAt (fun z' ↦ T (z', w) A) ((ContinuousAlternatingMap.apply ℝ (E × ℂ) ℝ A).comp
      ((fderiv ℝ T (z, w)).comp (ContinuousLinearMap.inl ℝ E ℂ))) z :=
  (ContinuousAlternatingMap.apply ℝ (E × ℂ) ℝ A).hasFDerivAt.comp z
    (((hTc.differentiable one_ne_zero) (z, w)).hasFDerivAt.comp z (hasFDerivAt_prodMk_left z w))

/-- **Smoothness of slice moments.** If `T` vanishes over the complement of a compact set and `T`
and `g` are `Cⁿ`, then the slice moment `z ↦ ∫ g dμ_z` is `Cⁿ`. -/
theorem contDiff_sliceMoment {n : ℕ∞} (hK : IsCompact K) (hTc : ContDiff ℝ n T)
    (hg : ContDiff ℝ n g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) :
    ContDiff ℝ n (sliceMoment T g) := by
  rw [sliceMoment_eq_setIntegral hT]
  exact ContDiff.parametric_integral hK subset_rfl hK.measure_lt_top.ne
    (((ContinuousAlternatingMap.apply ℝ (E × ℂ) ℝ _).contDiff.comp hTc).smul
      (hg.comp contDiff_snd))

/-- The closedness `dT = 0` at a point, evaluated on a base direction `(v, 0)` and the fibre frame
`(∂_x, ∂_y)`: the base derivative of the slice density is a sum of fibre derivatives of the mixed
coefficients. -/
private theorem fderiv_apply_base_eq {x : E × ℂ} (hdT : extDeriv T x = 0) (v : E) :
    fderiv ℝ T x (v, 0) ![(0, 1), (0, I)] =
      fderiv ℝ T x (0, 1) ![(v, 0), (0, I)] - fderiv ℝ T x (0, I) ![(v, 0), (0, 1)] := by
  have h := extDeriv_apply_triple x ((v, 0) : E × ℂ) (0, 1) (0, I) (ω := T)
  rw [hdT, ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at h
  linear_combination -h

/-- A coefficient of a continuous `T` is continuous along the fibre. -/
private theorem continuous_coeff (hTc : Continuous T) (z : E) (A : Fin 2 → E × ℂ) :
    Continuous fun w ↦ T (z, w) A :=
  (ContinuousAlternatingMap.apply ℝ (E × ℂ) ℝ A).continuous.comp
    (hTc.comp (Continuous.prodMk_right z))

/-- A continuous function vanishing off a compact set is integrable on `ℂ`. -/
private theorem integrable_of_vanishing {G : Type*} [NormedAddCommGroup G] {f : ℂ → G}
    (hK : IsCompact K) (hf : Continuous f) (h : ∀ w ∉ K, f w = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hK h)

/-- A fibre derivative of a coefficient of `T`, weighted by `g`, is integrable on the fibre. -/
private theorem integrable_fderiv_coeff_smul (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hg : Continuous g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) (z : E) (A : Fin 2 → E × ℂ) (u : ℂ) :
    Integrable fun w ↦ fderiv ℝ T (z, w) (0, u) A • g w :=
  integrable_of_vanishing hK (((ContinuousAlternatingMap.apply ℝ (E × ℂ) ℝ A).continuous.comp
    (((hTc.continuous_fderiv one_ne_zero).comp (Continuous.prodMk_right z)).clm_apply
      continuous_const)).smul hg) fun w hw ↦ by
    simp [fderiv_eq_zero_of_notMem hK.isClosed hT z hw]

/-- A coefficient of `T`, weighted by a continuous `g`, is integrable on the fibre. -/
private theorem integrable_coeff_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : ℂ → G} (hK : IsCompact K) (hTc : ContDiff ℝ 1 T) (hg : Continuous g)
    (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) (z : E) (A : Fin 2 → E × ℂ) :
    Integrable fun w ↦ T (z, w) A • g w :=
  integrable_of_vanishing hK ((continuous_coeff hTc.continuous z A).smul hg) fun w hw ↦ by
    simp [hT z w hw]

/-- **Integration by parts along a fibre.** A fibre derivative of a coefficient of `T`, weighted
by `g`, integrates to minus the coefficient weighted by the derivative of `g`. -/
private theorem integral_fderiv_coeff_smul (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hg : ContDiff ℝ 1 g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) (z : E) (A : Fin 2 → E × ℂ)
    (u : ℂ) :
    ∫ w, fderiv ℝ T (z, w) (0, u) A • g w = -∫ w, T (z, w) A • fderiv ℝ g w u := by
  have hfd (w : ℂ) : fderiv ℝ (fun w' ↦ T (z, w') A) w u = fderiv ℝ T (z, w) (0, u) A := by
    simp [(hasFDerivAt_coeff_fiber hTc z w A).fderiv]
  have hcg' : Continuous fun w ↦ fderiv ℝ g w u :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := fun w' ↦ T (z, w') A) (g := g) (v := u)
    (by
      simp only [hfd]
      exact integrable_fderiv_coeff_smul hK hTc hg.continuous hT z A u)
    (integrable_coeff_smul hK hTc hcg' hT z A)
    (integrable_coeff_smul hK hTc hg.continuous hT z A)
    (fun w _ ↦ (hasFDerivAt_coeff_fiber hTc z w A).differentiableAt)
    (fun w _ ↦ (hg.differentiable one_ne_zero) w)
  simp only [hfd] at h
  rw [h, neg_neg]

/-- **The derivative of a slice moment.** Let `T` be a `C¹` two-form on `E × ℂ` vanishing over the
complement of a compact set `K`, closed at every point of the fibre over `z`, and let `g` be `C¹`.
In the direction of a base vector `v`, the derivative of the slice moment `∫ g dμ_z` is the fibre
integral of `dg ∧ T` evaluated on `(v, 0)`:

`D (sliceMoment T g)(z) v = ∫ (T(z, w)(v, ∂_x) ∂_y g(w) - T(z, w)(v, ∂_y) ∂_x g(w)) dw`.

There is no boundary term, since `T` has compact support in the fibre. -/
theorem fderiv_sliceMoment_apply (hK : IsCompact K) (hTc : ContDiff ℝ 1 T) (hg : ContDiff ℝ 1 g)
    (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : E} (hdT : ∀ w, extDeriv T (z, w) = 0) (v : E) :
    fderiv ℝ (sliceMoment T g) z v = ∫ w, (T (z, w) ![(v, 0), (0, 1)] • fderiv ℝ g w I -
      T (z, w) ![(v, 0), (0, I)] • fderiv ℝ g w 1) := by
  set e : Fin 2 → E × ℂ := ![(0, 1), (0, I)] with he
  set f : E → ℂ → F := fun z' w ↦ T (z', w) e • g w
  have hf : ContDiff ℝ 1 (Function.uncurry f) :=
    ((ContinuousAlternatingMap.apply ℝ (E × ℂ) ℝ e).contDiff.comp hTc).smul
      (hg.comp contDiff_snd)
  have hm : sliceMoment T g = fun z' ↦ ∫ w in K, f z' w := sliceMoment_eq_setIntegral hT g
  -- Differentiate under the integral sign over the compact set `K`.
  have hD := hasFDerivAt_integral_of_contDiffOn (μ := volume) (x₀ := z) (u := univ) univ_mem hK
    hK.measure_lt_top.ne subset_rfl hf.contDiffOn
  have hpart (w : ℂ) : fderiv ℝ (fun z' ↦ f z' w) z v = fderiv ℝ T (z, w) (v, 0) e • g w := by
    simp [f, ((hasFDerivAt_coeff_base hTc z w e).smul_const (g w)).fderiv]
  have hint : IntegrableOn (fun w ↦ fderiv ℝ (fun z' ↦ f z' w) z) K :=
    ((ContDiff.fderiv (f := fun w z' ↦ f z' w) (n := 0)
      (hf.comp (contDiff_snd.prodMk contDiff_fst)) (contDiff_const (c := z))
      le_rfl).continuous.continuousOn).integrableOn_compact hK
  rw [hm, hD.fderiv, ContinuousLinearMap.integral_apply hint,
    setIntegral_congr_fun hK.measurableSet fun w _ ↦ hpart w]
  -- Return to the integral over `ℂ`, then use `dT = 0` and integrate by parts in the fibre.
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ by
    simp [fderiv_eq_zero_of_notMem hK.isClosed hT z hw]]
  simp only [he, fderiv_apply_base_eq (hdT _) v, sub_smul]
  have hi := integrable_fderiv_coeff_smul hK hTc hg.continuous hT z
  have hj (u : ℂ) (A : Fin 2 → E × ℂ) := integrable_coeff_smul hK hTc
    ((hg.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := u))) hT z A
  rw [integral_sub (hi _ 1) (hi _ I), integral_sub (hj I _) (hj 1 _),
    integral_fderiv_coeff_smul hK hTc hg hT, integral_fderiv_coeff_smul hK hTc hg hT]
  abel

/-- **The derivative of a holomorphic slice moment.** Under the hypotheses of
`TauCeti.fderiv_sliceMoment_apply`, for an entire weight `g : ℂ → ℂ` the derivative of the slice
moment `∫ g dμ_z` along a base vector `v` is

`D (sliceMoment T g)(z) v = ∫ g'(w) (i T(z, w)(v, ∂_x) - T(z, w)(v, ∂_y)) dw`,

the fibre integral `π_*(g'(w) dw ∧ T)` evaluated on `(v, 0)`. -/
theorem fderiv_sliceMoment_apply_of_differentiable (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : E}
    (hdT : ∀ w, extDeriv T (z, w) = 0) (v : E) :
    fderiv ℝ (sliceMoment T g) z v = ∫ w, deriv g w *
      (I * T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![(v, 0), (0, I)]) := by
  rw [fderiv_sliceMoment_apply hK hTc (hg.contDiff.restrict_scalars ℝ) hT hdT v]
  refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
  simp only [((hg w).hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, real_smul]
  ring

/-- **The derivative of the moments `M_k`.** Under the hypotheses of
`TauCeti.fderiv_sliceMoment_apply`, the moment `M_k(z) = ∫ wᵏ dμ_z` has derivative

`D M_k(z) v = ∫ k w^(k-1) (i T(z, w)(v, ∂_x) - T(z, w)(v, ∂_y)) dw`,

the fibre integral `π_*(k w^(k-1) dw ∧ T)` evaluated on `(v, 0)`. -/
theorem fderiv_sliceMoment_pow_apply (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : E} (hdT : ∀ w, extDeriv T (z, w) = 0) (k : ℕ)
    (v : E) :
    fderiv ℝ (sliceMoment T (· ^ k)) z v = ∫ w, (k : ℂ) * w ^ (k - 1) *
      (I * T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![(v, 0), (0, I)]) := by
  simp only [fderiv_sliceMoment_apply_of_differentiable hK hTc (differentiable_pow k) hT hdT v,
    deriv_pow_field]

/-- **A bound for slice moments.** A slice moment is bounded by the bounds of the slice density
and the weight: if `T` vanishes over the complement of the compact set `K`,
`|T(z, w)(∂_x, ∂_y)| ≤ C` and `‖g(w)‖ ≤ B` for `w ∈ K`, then `‖∫ g dμ_z‖ ≤ C B vol(K)`. -/
theorem norm_sliceMoment_le {B C : ℝ} (hK : IsCompact K) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0)
    {z : E} (hC : ∀ w ∈ K, |T (z, w) ![(0, 1), (0, I)]| ≤ C) (hB : ∀ w ∈ K, ‖g w‖ ≤ B) :
    ‖sliceMoment T g z‖ ≤ C * B * volume.real K := by
  rw [sliceMoment_eq_setIntegral hT]
  refine norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun w hw ↦ ?_
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hC w hw) (hB w hw) (norm_nonneg _) ((abs_nonneg _).trans (hC w hw))

/-! ### The flux of a closed form and its pairing with base forms -/

/-- **The fibre flux of a closed form is constant.** If `T` is a closed `C¹` two-form on `E × ℂ`
vanishing over the complement of a compact set `K`, then the slice moment of a constant weight,
for instance the flux `M₀(z) = ∫ dμ_z`, takes the same value over every base point. -/
theorem sliceMoment_const_eq_sliceMoment_const (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) (hdT : ∀ x, extDeriv T x = 0) (c : F) (z z' : E) :
    sliceMoment T (fun _ ↦ c) z = sliceMoment T (fun _ ↦ c) z' := by
  refine is_const_of_fderiv_eq_zero
    ((contDiff_sliceMoment (n := 1) hK hTc contDiff_const hT).differentiable one_ne_zero)
    (fun z ↦ ?_) z z'
  ext v
  rw [fderiv_sliceMoment_apply hK hTc contDiff_const hT (fun w ↦ hdT _) v]
  simp

/-- The value of `T ∧ π^*β` on the product frame `(b₀, 0), (b₁, 0), (0, 1), (0, i)` is the slice
density of `T` times the value of `β` on `b`: every other way of distributing the four vectors
gives `β` a fibre vector, on which the pullback vanishes. -/
private theorem wedge_compContinuousLinearMap_fst_apply (b : Module.Basis (Fin 2) ℝ E)
    (θ : (E × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (β : E [⋀^Fin 2]→L[ℝ] ℝ) :
    θ.wedge (β.compContinuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ))
        ((b.prod Complex.basisOneI).reindex finSumFinEquiv) =
      θ ![(0, 1), (0, I)] * β b := by
  have hframe : ⇑((b.prod Complex.basisOneI).reindex finSumFinEquiv) =
      ![(b 0, 0), (b 1, 0), (0, 1), (0, I)] := by
    refine funext (Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_)) <;>
      simp only [Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
        finSumFinEquiv_symm_apply_natAdd] <;>
      fin_cases i <;> simp [Module.Basis.prod_apply, Complex.coe_basisOneI]
  have hb : ⇑b = ![b 0, b 1] := by
    ext i : 1
    fin_cases i <;> rfl
  have h₁ (v : E) : β ![v, 0] = 0 := β.map_coord_zero 1 rfl
  have h₀ (v : E) : β ![0, v] = 0 := β.map_coord_zero 0 rfl
  have hfst (u v : E × ℂ) : Prod.fst ∘ ![u, v] = ![u.1, v.1] := by
    ext i : 1
    fin_cases i <;> rfl
  rw [hframe, ContinuousAlternatingMap.wedge_def,
    ContinuousAlternatingMap.pairedWedge_mul_apply_two_two, hb]
  simp [hfst, h₀, h₁]

/-- The coefficient of `T ∧ π^*β` on the product frame has compact support when `T` vanishes
outside a compact set of the fibre and `β` has compact support. -/
private theorem hasCompactSupport_mul_apply (hK : IsCompact K) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0)
    {β : E → E [⋀^Fin 2]→L[ℝ] ℝ} (hβc : HasCompactSupport β) (v : Fin 2 → E) :
    HasCompactSupport fun x : E × ℂ ↦ T x ![(0, 1), (0, I)] * β x.1 v := by
  refine HasCompactSupport.intro (hβc.prod hK) fun x hx ↦ ?_
  simp only [Set.mem_prod, not_and_or] at hx
  rcases hx with hx | hx
  · simp [image_eq_zero_of_notMem_tsupport hx]
  · simp [hT x.1 x.2 hx]

/-- **The pairing of a two-form with a pulled-back base form.** Let `T` be a continuous two-form
on `E × ℂ` vanishing over the complement of a compact set `K` of the fibre, and `β` a compactly
supported continuous two-form on a two-dimensional base `E` with basis `b`. Then the integral of
`T ∧ π^*β` is the integral over the base of the flux `M₀(z) = ∫ dμ_z` of `T` times `β`. Top-degree
coefficients are taken on the product frame `(b₀, 0), (b₁, 0), (0, 1), (0, i)` and integrated
against its Haar measure. -/
theorem integral_wedge_compContinuousLinearMap_fst [MeasurableSpace E] [BorelSpace E]
    (b : Module.Basis (Fin 2) ℝ E) (hK : IsCompact K) (hTc : Continuous T)
    (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {β : E → E [⋀^Fin 2]→L[ℝ] ℝ} (hβ : Continuous β)
    (hβc : HasCompactSupport β) :
    ∫ x, (T x).wedge ((β x.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ))
        ((b.prod Complex.basisOneI).reindex finSumFinEquiv)
        ∂((b.prod Complex.basisOneI).reindex finSumFinEquiv).addHaar =
      ∫ z, sliceMoment T (fun _ ↦ (1 : ℝ)) z * β z b ∂b.addHaar := by
  set f : E × ℂ → ℝ := fun x ↦ T x ![(0, 1), (0, I)] * β x.1 b
  have hf : Integrable f (b.addHaar.prod volume) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (hasCompactSupport_mul_apply hK hT hβc b)
  simp only [wedge_compContinuousLinearMap_fst_apply, Module.Basis.addHaar_reindex,
    Module.Basis.prod_addHaar, Complex.addHaar_basisOneI]
  rw [integral_prod f hf]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  simp [f, sliceMoment_def, integral_mul_const]

open ContinuousAlternatingMap in
/-- **The pairing of a closed two-form with `c π^*β + dη`.** Let `T` be a closed `C¹` two-form on
`E × ℂ` vanishing over the complement of a compact set `K` of the fibre, so that its flux
`m = ∫ dμ_z` does not depend on the base point `z₀`
(`TauCeti.sliceMoment_const_eq_sliceMoment_const`). For a compactly supported continuous base
two-form `β` and a compactly supported `C¹` one-form `η` on `E × ℂ`,

`∫ T ∧ (c π^*β + dη) = c m ∫ β`.

The exact term integrates to zero because `T` is closed. In a tube around a pseudoholomorphic curve
`C` with `β` its area form and `c π^*β + dη` a taming form, this is the product-chart form of the
identity `T(Ω) = c m area(C)` for a closed current of transverse flux `m`; the global identity
follows by summing over a partition of unity on `C`, which is not done here. -/
theorem integral_wedge_smul_compContinuousLinearMap_fst_add_extDeriv [MeasurableSpace E]
    [BorelSpace E] (b : Module.Basis (Fin 2) ℝ E) (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) (hdT : ∀ x, extDeriv T x = 0)
    {β : E → E [⋀^Fin 2]→L[ℝ] ℝ} (hβ : Continuous β) (hβc : HasCompactSupport β)
    {η : E × ℂ → (E × ℂ) [⋀^Fin 1]→L[ℝ] ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (c : ℝ) (z₀ : E) :
    ∫ x, (T x).wedge (c • (β x.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ) +
        extDeriv η x) ((b.prod Complex.basisOneI).reindex finSumFinEquiv)
        ∂((b.prod Complex.basisOneI).reindex finSumFinEquiv).addHaar =
      c * sliceMoment T (fun _ ↦ (1 : ℝ)) z₀ * ∫ z, β z b ∂b.addHaar := by
  set e := (b.prod Complex.basisOneI).reindex finSumFinEquiv
  -- The exact term vanishes: integrate by parts and use `dT = 0`.
  have hparts := e.integral_extDeriv_wedge_eq_integral_wedge_extDeriv (k := 2) (l := 1)
    (by norm_num) hTc hη hηc
  -- The index cast `2 + (1 + 1) = 2 + 2` is the identity.
  have e₁ : ⇑e ∘ Fin.cast (show 2 + (1 + 1) = 2 + 2 by omega) = ⇑e := rfl
  simp only [hdT, e₁, wedge_zero_left, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
    integral_zero, neg_one_sq, neg_mul, one_mul, zero_eq_neg] at hparts
  have hexact : ∫ x, (T x).wedge (extDeriv η x) e ∂e.addHaar = 0 := hparts
  have hint₁ : Integrable (fun x ↦ (T x).wedge
      ((β x.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ E ℂ)) e) e.addHaar := by
    simp only [e, wedge_compContinuousLinearMap_fst_apply]
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (hasCompactSupport_mul_apply hK hT hβc b)
  have hint₂ : Integrable (fun x ↦ (T x).wedge (extDeriv η x) e) e.addHaar := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (((hTc.of_le zero_le_one).wedge
        (contDiff_extDeriv (r := 0) hη (by norm_num))).continuous).eval_const _
    · exact (hηc.extDeriv.wedge_left (φ := T)).comp_left
        (g := fun ω : (E × ℂ) [⋀^Fin (2 + (1 + 1))]→L[ℝ] ℝ ↦ ω e) rfl
  simp only [wedge_add_right, wedge_smul_right, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [integral_add (hint₁.const_mul c) hint₂, hexact, add_zero, integral_const_mul,
    integral_wedge_compContinuousLinearMap_fst b hK hTc.continuous hT hβ hβc]
  simp only [sliceMoment_const_eq_sliceMoment_const hK hTc hT hdT (1 : ℝ) _ z₀,
    integral_const_mul]
  ring

/-! ### Holomorphic slice moments of forms of type `(1,1)` -/

section Holomorphic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {T : V × ℂ → (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ} {g : ℂ → ℂ}

/-- **The conjugate Wirtinger derivative of a holomorphic slice moment.** Let `T` be a `C¹`
two-form on `V × ℂ`, for a complex normed space `V`, vanishing over the complement of a compact
set `K` and closed at every point of the fibre over `z`, and let `g` be entire. Then

`\bar∂ (sliceMoment T g)(z) v = ∫ g'(w) (i T⁻(z, w)(v, ∂_x) - T⁻(z, w)(v, ∂_y)) dw`,

where `T⁻(u, u') = (T(u, u') - T(i u, i u')) / 2` is the part of `T` anti-invariant under the
complex structure of `V × ℂ`. This is the formula of
`TauCeti.fderiv_sliceMoment_apply_of_differentiable` with `T` replaced by `T⁻`: the `J`-invariant
part, the `(1,1)` part of `T`, does not contribute.
Written out, `T⁻(z, w)(v, ∂_x) = (T(z, w)(v, ∂_x) - T(z, w)(i v, ∂_y)) / 2` and
`T⁻(z, w)(v, ∂_y) = (T(z, w)(v, ∂_y) + T(z, w)(i v, ∂_x)) / 2`. -/
theorem conjWirtingerDeriv_sliceMoment_apply (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hg : Differentiable ℂ g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : V}
    (hdT : ∀ w, extDeriv T (z, w) = 0) (v : V) :
    conjWirtingerDeriv (sliceMoment T g) z v = ∫ w, deriv g w *
      (I * ((T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![(I • v, 0), (0, I)]) / 2 : ℝ) -
        ((T (z, w) ![(v, 0), (0, I)] + T (z, w) ![(I • v, 0), (0, 1)]) / 2 : ℝ)) := by
  have hd : Continuous (deriv g) := hg.deriv.continuous
  have hi (A B : Fin 2 → V × ℂ) :
      Integrable fun w ↦ deriv g w * (I * T (z, w) A - T (z, w) B) :=
    ((integrable_coeff_smul (g := fun w ↦ I * deriv g w) hK hTc (continuous_const.mul hd) hT
      z A).sub (integrable_coeff_smul hK hTc hd hT z B)).congr (ae_of_all _ fun w ↦ by
        simp only [Pi.sub_apply, real_smul]; ring)
  have h₂ : Integrable fun w ↦ I • (deriv g w *
      (I * T (z, w) ![(I • v, 0), (0, 1)] - T (z, w) ![(I • v, 0), (0, I)])) :=
    (hi _ _).smul I
  rw [conjWirtingerDeriv_apply, fderiv_sliceMoment_apply_of_differentiable hK hTc hg hT hdT,
    fderiv_sliceMoment_apply_of_differentiable hK hTc hg hT hdT, ← integral_smul,
    ← integral_add (hi _ _) h₂, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
  simp only [smul_eq_mul]
  push_cast
  linear_combination (deriv g w * T (z, w) ![(I • v, 0), (0, 1)] / 2) * I_sq

/-- **A bound for the conjugate Wirtinger derivative of a holomorphic slice moment.** Under the
hypotheses of `TauCeti.conjWirtingerDeriv_sliceMoment_apply`, `‖\bar∂ (sliceMoment T g)(z) v‖` is
at most the fibre integral of `‖g'(w)‖ (|T⁻(z, w)(v, ∂_x)| + |T⁻(z, w)(v, ∂_y)|)`, where `T⁻` is the
part of `T` anti-invariant under the complex structure of `V × ℂ`. So the slice moments are
nearly holomorphic where `T` is nearly of type `(1,1)`. -/
theorem norm_conjWirtingerDeriv_sliceMoment_apply_le (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hg : Differentiable ℂ g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : V}
    (hdT : ∀ w, extDeriv T (z, w) = 0) (v : V) :
    ‖conjWirtingerDeriv (sliceMoment T g) z v‖ ≤ ∫ w, ‖deriv g w‖ *
      (|(T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![(I • v, 0), (0, I)]) / 2| +
        |(T (z, w) ![(v, 0), (0, I)] + T (z, w) ![(I • v, 0), (0, 1)]) / 2|) := by
  have hc := continuous_coeff hTc.continuous z
  rw [conjWirtingerDeriv_sliceMoment_apply hK hTc hg hT hdT v]
  refine norm_integral_le_of_norm_le (integrable_of_vanishing hK
    (hg.deriv.continuous.norm.mul ((((hc _).sub (hc _)).div_const _).abs.add
      (((hc _).add (hc _)).div_const _).abs)) fun w hw ↦ by simp [hT z w hw])
    (ae_of_all _ fun w ↦ ?_)
  rw [norm_mul]
  gcongr
  refine (norm_sub_le _ _).trans_eq ?_
  simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **Slice moments of a form of type `(1,1)` are holomorphic at a point.** If, in addition to
the hypotheses of `TauCeti.conjWirtingerDeriv_sliceMoment_apply`, the form `T` is invariant under
the complex structure of `V × ℂ` along the fibre over `z`, `T(i u, i u') = T(u, u')`, then the
slice moment `∫ g dμ_z` of every entire weight `g` has vanishing conjugate Wirtinger derivative
at `z`. -/
theorem conjWirtingerDeriv_sliceMoment_eq_zero (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hg : Differentiable ℂ g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : V}
    (hdT : ∀ w, extDeriv T (z, w) = 0)
    (hJ : ∀ w, ∀ u u' : V × ℂ, T (z, w) ![I • u, I • u'] = T (z, w) ![u, u']) :
    conjWirtingerDeriv (sliceMoment T g) z = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [conjWirtingerDeriv_sliceMoment_apply hK hTc hg hT hdT v, zero_apply]
  refine (integral_congr_ae (ae_of_all _ fun w ↦ ?_)).trans (integral_zero _ _)
  have h₁ := hJ w (v, 0) (0, 1)
  have h₂ := hJ w (I • v, 0) (0, 1)
  simp only [Prod.smul_mk, smul_zero, smul_smul, smul_eq_mul, mul_zero, mul_one, I_mul_I,
    neg_one_smul] at h₁ h₂
  -- `T` is linear in its first slot, so `T(-v, ∂_y) = -T(v, ∂_y)`.
  have hneg : T (z, w) ![(-v, 0), (0, I)] = -T (z, w) ![(v, 0), (0, I)] := by
    rw [show ((-v, 0) : V × ℂ) = (-1 : ℝ) • (v, 0) by simp,
      ContinuousAlternatingMap.vecCons_smul, neg_one_smul]
  rw [h₁, ← h₂, hneg]
  push_cast
  ring

/-- **Slice moments of a form of type `(1,1)` are complex differentiable at a point**, under the
hypotheses of `TauCeti.conjWirtingerDeriv_sliceMoment_eq_zero`. -/
theorem differentiableAt_sliceMoment (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hg : Differentiable ℂ g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : V}
    (hdT : ∀ w, extDeriv T (z, w) = 0)
    (hJ : ∀ w, ∀ u u' : V × ℂ, T (z, w) ![I • u, I • u'] = T (z, w) ![u, u']) :
    DifferentiableAt ℂ (sliceMoment T g) z :=
  (differentiableAt_iff_conjWirtingerDeriv_eq_zero
    ((contDiff_sliceMoment hK hTc (hg.contDiff.restrict_scalars ℝ) hT).differentiable
      one_ne_zero z)).2 (conjWirtingerDeriv_sliceMoment_eq_zero hK hTc hg hT hdT hJ)

/-- **Slice moments of a closed form of type `(1,1)` are holomorphic.** Let `T` be a closed `C¹`
two-form on `V × ℂ`, invariant under the complex structure of `V × ℂ` and vanishing over the
complement of a compact set `K` of the fibre. Then for every entire weight `g` the slice moment
`z ↦ ∫ g dμ_z` is complex differentiable on `V`; in particular so are the moments
`M_k(z) = ∫ wᵏ dμ_z`. -/
theorem differentiable_sliceMoment (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hg : Differentiable ℂ g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) (hdT : ∀ x, extDeriv T x = 0)
    (hJ : ∀ x, ∀ u u' : V × ℂ, T x ![I • u, I • u'] = T x ![u, u']) :
    Differentiable ℂ (sliceMoment T g) := fun _ ↦
  differentiableAt_sliceMoment hK hTc hg hT (fun _ ↦ hdT _) fun _ ↦ hJ _

/-- **Liouville's theorem for slice moments.** Let `T` be a closed `C¹` two-form on `V × ℂ`,
invariant under the complex structure of `V × ℂ`, vanishing over the complement of a compact set
`K` of the fibre, and with bounded slice density `|T(z, w)(∂_x, ∂_y)| ≤ C`. Then every slice moment
`∫ g dμ_z` of an entire weight `g` is independent of the base point `z`. In particular the moments
`M_k(z) = ∫ wᵏ dμ_z`, and with them the Newton coefficients of the slices, are constant. -/
theorem sliceMoment_eq_sliceMoment_of_abs_le (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hg : Differentiable ℂ g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) (hdT : ∀ x, extDeriv T x = 0)
    (hJ : ∀ x, ∀ u u' : V × ℂ, T x ![I • u, I • u'] = T x ![u, u']) {C : ℝ}
    (hC : ∀ x, |T x ![(0, 1), (0, I)]| ≤ C) (z z' : V) :
    sliceMoment T g z = sliceMoment T g z' := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hg.continuous.continuousOn
  refine (differentiable_sliceMoment hK hTc hg hT hdT hJ).apply_eq_apply_of_bounded ?_ z z'
  exact isBounded_iff_forall_norm_le.2
    ⟨_, forall_mem_range.2 fun z ↦ norm_sliceMoment_le hK hT (fun w _ ↦ hC (z, w)) hB⟩


/-! ### Slice moments in the frame of a normal Cauchy–Riemann operator -/

open scoped ComplexConjugate

/-- A real endomorphism `L` of `V × ℂ` acting on the vertical directions by multiplication by `i`
sends `∂_x` to `∂_y` and `∂_y` to `-∂_x`. -/
private theorem apply_zero_one_and_apply_zero_I {L : V × ℂ →L[ℝ] V × ℂ}
    (hL₂ : ∀ n, L (0, n) = (0, I * n)) : L (0, 1) = (0, I) ∧ L (0, I) = (0, -1) := by
  simp [hL₂]

/-- The pointwise identity behind `TauCeti.conjWirtingerDeriv_sliceMoment_add_add_apply`. Let `L`
be a real endomorphism of `V × ℂ` with `L (0, n) = (0, i n)` and `L (v, 0) = (i v, c)`. The
integrand of `TauCeti.conjWirtingerDeriv_sliceMoment_apply`, built from the part of `θ`
anti-invariant under multiplication by `i`, is the same expression for the part anti-invariant
under `L`, plus `(i / 2) c θ(∂_x, ∂_y)`. -/
private theorem antiInvariant_eq_add (θ : (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ) (L : V × ℂ →L[ℝ] V × ℂ)
    {v : V} {c : ℂ} (hL₁ : L (v, 0) = (I • v, c)) (hL₂ : ∀ n, L (0, n) = (0, I * n)) :
    I * (((θ ![(v, 0), (0, 1)] - θ ![(I • v, 0), (0, I)]) / 2 : ℝ) : ℂ) -
        (((θ ![(v, 0), (0, I)] + θ ![(I • v, 0), (0, 1)]) / 2 : ℝ) : ℂ) =
      I * (((θ ![(v, 0), (0, 1)] - θ ![L (v, 0), L (0, 1)]) / 2 : ℝ) : ℂ) -
        (((θ ![(v, 0), (0, I)] - θ ![L (v, 0), L (0, I)]) / 2 : ℝ) : ℂ) +
        I / 2 * c * θ ![(0, 1), (0, I)] := by
  have hc : ((I • v, c) : V × ℂ) =
      (I • v, 0) + (c.re • ((0 : V), (1 : ℂ)) + c.im • ((0 : V), I)) := by
    refine Prod.ext (by simp) ?_
    simp
  obtain ⟨h₁, h₂⟩ := apply_zero_one_and_apply_zero_I hL₂
  rw [show ((0, -1) : V × ℂ) = (-1 : ℝ) • ((0 : V), (1 : ℂ)) by simp] at h₂
  -- `θ` is linear in its second slot as well.
  have hsmul (x y : V × ℂ) (r : ℝ) : θ ![x, r • y] = r * θ ![x, y] := by
    rw [θ.apply_vecCons_swap, ContinuousAlternatingMap.vecCons_smul, θ.apply_vecCons_swap y x]
    simp
  have hxx : θ ![((0 : V), (1 : ℂ)), (0, 1)] = 0 :=
    θ.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hyy : θ ![((0 : V), I), (0, I)] = 0 :=
    θ.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hyx : θ ![((0 : V), I), (0, 1)] = -θ ![(0, 1), (0, I)] := θ.apply_vecCons_swap _ _
  rw [hL₁, h₁, h₂, hsmul, hc]
  simp only [ContinuousAlternatingMap.vecCons_add, ContinuousAlternatingMap.vecCons_smul,
    hxx, hyy, hyx, smul_eq_mul]
  push_cast
  linear_combination (I * θ ![(0, 1), (0, I)] / 2) * Complex.re_add_im c -
    ((θ ![(0, 1), (0, I)] : ℂ) * c.im / 2) * I_sq

/-- **The moment defects of a normal Cauchy–Riemann operator as fibre integrals.** Let `T` be a
`C¹` two-form on `V × ℂ` vanishing over the complement of a compact set `K` and closed at every
point of the fibre over `z`, and let `g` be entire. Let `ν` and `μ` be `(0,1)`-forms on `V`, the
coefficients of the real Cauchy–Riemann operator `D = \bar∂ + ν W + μ \bar W` on the normal line,
and let `L w` be the complex structure of `V × ℂ` at `(z, w)` whose holomorphic graphs solve
`D`:

`L w (v, 0) = (i v, 2 i (ν(v) w + μ(v) \bar w))`,  `L w (0, n) = (0, i n)`.

Then the defect of the slice moment `∫ g dμ_z` for `D`,
`\bar∂ (∫ g dμ_z) + (∫ w g'(w) dμ_z) ν + (∫ \bar w g'(w) dμ_z) μ`, is the fibre integral of
`g'(w) dw ∧ T⁻`, where `T⁻(u, u') = (T(u, u') - T(L w u, L w u')) / 2` is the part of `T`
anti-invariant under `L w`:

`= ∫ g'(w) (i T⁻(z, w)((v, 0), ∂_x) - T⁻(z, w)((v, 0), ∂_y)) dw`.

For `ν = μ = 0` this is `TauCeti.conjWirtingerDeriv_sliceMoment_apply`. -/
theorem conjWirtingerDeriv_sliceMoment_add_add_apply (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hg : Differentiable ℂ g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : V}
    (hdT : ∀ w, extDeriv T (z, w) = 0) {L : ℂ → V × ℂ →L[ℝ] V × ℂ} (ν μ : V →L⋆[ℂ] ℂ)
    (hL₁ : ∀ w v, L w (v, 0) = (I • v, 2 * I * (ν v * w + μ v * conj w)))
    (hL₂ : ∀ w n, L w (0, n) = (0, I * n)) (v : V) :
    (conjWirtingerDeriv (sliceMoment T g) z + sliceMoment T (fun w ↦ w * deriv g w) z • ν +
        sliceMoment T (fun w ↦ conj w * deriv g w) z • μ) v =
      ∫ w, deriv g w *
        (I * ((T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![L w (v, 0), L w (0, 1)]) / 2 : ℝ) -
          ((T (z, w) ![(v, 0), (0, I)] - T (z, w) ![L w (v, 0), L w (0, I)]) / 2 : ℝ)) := by
  have hd : Continuous (deriv g) := hg.deriv.continuous
  have hc := continuous_coeff hTc.continuous z
  have hP : Integrable fun w ↦ deriv g w *
      (I * ((T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![(I • v, 0), (0, I)]) / 2 : ℝ) -
        ((T (z, w) ![(v, 0), (0, I)] + T (z, w) ![(I • v, 0), (0, 1)]) / 2 : ℝ)) :=
    integrable_of_vanishing hK (hd.mul ((continuous_const.mul (continuous_ofReal.comp
      (((hc _).sub (hc _)).div_const _))).sub (continuous_ofReal.comp
        (((hc _).add (hc _)).div_const _)))) fun w hw ↦ by simp [hT z w hw]
  have hX (f : ℂ → ℂ) (hf : Continuous f) (c : ℂ) :
      Integrable fun w ↦ T (z, w) ![(0, 1), (0, I)] • f w * c :=
    (integrable_coeff_smul hK hTc hf hT z _).mul_const c
  have h₁ : Continuous fun w ↦ w * deriv g w := continuous_id.mul hd
  have h₂ : Continuous fun w ↦ conj w * deriv g w := continuous_conj.mul hd
  rw [add_apply, add_apply, conjWirtingerDeriv_sliceMoment_apply hK hTc hg hT hdT v, smul_apply,
    smul_apply, sliceMoment_def, sliceMoment_def, smul_eq_mul, smul_eq_mul,
    ← integral_mul_const, ← integral_mul_const,
    ← integral_add hP (hX _ h₁ _), ← integral_add ?_ (hX _ h₂ _)]
  · refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
    simp only [antiInvariant_eq_add (T (z, w)) (L w) (hL₁ w v) (hL₂ w), real_smul]
    linear_combination (deriv g w * T (z, w) ![(0, 1), (0, I)] * (ν v * w + μ v * conj w)) * I_sq
  · exact hP.add (hX _ h₁ _)

/-- **The moment equations of a normal Cauchy–Riemann operator, with their defects as fibre
integrals.** Under the hypotheses of `TauCeti.conjWirtingerDeriv_sliceMoment_add_add_apply`, the
moments `M_k = ∫ wᵏ dμ_z` and mixed moments `Q_ℓ = ∫ w^ℓ \bar w dμ_z` have the defect

`E_k = \bar∂ M_k + k M_k ν + k Q_{k-1} μ`

of the moment equation of `D = \bar∂ + ν W + μ \bar W`, and

`E_k(v) = ∫ k w^(k-1) (i T⁻(z, w)((v, 0), ∂_x) - T⁻(z, w)((v, 0), ∂_y)) dw`,

where `T⁻` is the part of `T` anti-invariant under the complex structure `L w`. These `E_k` are
the inputs of `TauCeti.conjWirtingerDeriv_add_eq_sum_of_newton`. -/
theorem conjWirtingerDeriv_sliceMoment_pow_add_add_apply (hK : IsCompact K)
    (hTc : ContDiff ℝ 1 T) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : V}
    (hdT : ∀ w, extDeriv T (z, w) = 0) {L : ℂ → V × ℂ →L[ℝ] V × ℂ} (ν μ : V →L⋆[ℂ] ℂ)
    (hL₁ : ∀ w v, L w (v, 0) = (I • v, 2 * I * (ν v * w + μ v * conj w)))
    (hL₂ : ∀ w n, L w (0, n) = (0, I * n)) (k : ℕ) (v : V) :
    (conjWirtingerDeriv (sliceMoment T (· ^ k)) z + (k * sliceMoment T (· ^ k) z) • ν +
        (k * sliceMoment T (fun w ↦ w ^ (k - 1) * conj w) z) • μ) v =
      ∫ w, (k : ℂ) * w ^ (k - 1) *
        (I * ((T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![L w (v, 0), L w (0, 1)]) / 2 : ℝ) -
          ((T (z, w) ![(v, 0), (0, I)] - T (z, w) ![L w (v, 0), L w (0, I)]) / 2 : ℝ)) := by
  have hmul (f : ℂ → ℂ) : (k : ℂ) * sliceMoment T f z = sliceMoment T (fun w ↦ k * f w) z := by
    simp only [sliceMoment_def, ← integral_const_mul, real_smul]
    exact integral_congr_ae (ae_of_all _ fun w ↦ by ring)
  have hpow (w : ℂ) : w * ((k : ℂ) * w ^ (k - 1)) = k * w ^ k := by
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      ring
  have hconj (w : ℂ) : conj w * ((k : ℂ) * w ^ (k - 1)) = k * (w ^ (k - 1) * conj w) := by ring
  have h := conjWirtingerDeriv_sliceMoment_add_add_apply hK hTc (differentiable_pow k) hT hdT ν
    μ hL₁ hL₂ v
  simp only [deriv_pow_field, hpow, hconj] at h
  rw [hmul, hmul]
  exact h

/-- **A bound for the moment defects of a normal Cauchy–Riemann operator.** Under the hypotheses
of `TauCeti.conjWirtingerDeriv_sliceMoment_add_add_apply`, the defect of the slice moment
`∫ g dμ_z` for `D = \bar∂ + ν W + μ \bar W` is at most the fibre integral of
`‖g'(w)‖ (|T⁻(z, w)((v, 0), ∂_x)| + |T⁻(z, w)((v, 0), ∂_y)|)`, where `T⁻` is the part of `T`
anti-invariant under the complex structure `L w` whose holomorphic graphs solve `D`. So the
moments nearly solve the moment equations of `D` where `T` is nearly of type `(1,1)` for `L`. -/
theorem norm_conjWirtingerDeriv_sliceMoment_add_add_apply_le (hK : IsCompact K)
    (hTc : ContDiff ℝ 1 T) (hg : Differentiable ℂ g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : V}
    (hdT : ∀ w, extDeriv T (z, w) = 0) {L : ℂ → V × ℂ →L[ℝ] V × ℂ} (ν μ : V →L⋆[ℂ] ℂ)
    (hL₁ : ∀ w v, L w (v, 0) = (I • v, 2 * I * (ν v * w + μ v * conj w)))
    (hL₂ : ∀ w n, L w (0, n) = (0, I * n)) (v : V) :
    ‖(conjWirtingerDeriv (sliceMoment T g) z + sliceMoment T (fun w ↦ w * deriv g w) z • ν +
        sliceMoment T (fun w ↦ conj w * deriv g w) z • μ) v‖ ≤ ∫ w, ‖deriv g w‖ *
      (|(T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![L w (v, 0), L w (0, 1)]) / 2| +
        |(T (z, w) ![(v, 0), (0, I)] - T (z, w) ![L w (v, 0), L w (0, I)]) / 2|) := by
  -- Rewrite `L w` explicitly, so that the integrand is visibly continuous in `w`.
  have hL₃ (w : ℂ) := (apply_zero_one_and_apply_zero_I (hL₂ w)).1
  have hL₄ (w : ℂ) := (apply_zero_one_and_apply_zero_I (hL₂ w)).2
  rw [conjWirtingerDeriv_sliceMoment_add_add_apply hK hTc hg hT hdT ν μ hL₁ hL₂ v]
  simp only [hL₁, hL₃, hL₄]
  have hcT : Continuous fun w : ℂ ↦ T (z, w) :=
    hTc.continuous.comp (Continuous.prodMk_right z)
  have hc (x y : ℂ → V × ℂ) (hx : Continuous x) (hy : Continuous y) :
      Continuous fun w ↦ T (z, w) ![x w, y w] :=
    hcT.eval (continuous_pi fun i ↦ by fin_cases i <;> simpa)
  have hx : Continuous fun w : ℂ ↦ ((I • v, 2 * I * (ν v * w + μ v * conj w)) : V × ℂ) := by
    fun_prop
  refine norm_integral_le_of_norm_le (integrable_of_vanishing hK
    (hg.deriv.continuous.norm.mul
      (((((hc _ _ continuous_const continuous_const).sub
        (hc _ _ hx continuous_const)).div_const _).abs.add
      (((hc _ _ continuous_const continuous_const).sub
        (hc _ _ hx continuous_const)).div_const _).abs))) fun w hw ↦ by simp [hT z w hw])
    (ae_of_all _ fun w ↦ ?_)
  rw [norm_mul]
  gcongr
  refine (norm_sub_le _ _).trans_eq ?_
  simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **The moments of a form of type `(1,1)` solve the moment equations exactly.** If, in addition
to the hypotheses of `TauCeti.conjWirtingerDeriv_sliceMoment_add_add_apply`, the form `T` is
invariant under the complex structure `L w` along the fibre over `z`, then the slice moment
`∫ g dμ_z` satisfies the moment equation of `D = \bar∂ + ν W + μ \bar W` at `z`:

`\bar∂ (∫ g dμ_z) + (∫ w g'(w) dμ_z) ν + (∫ \bar w g'(w) dμ_z) μ = 0`.

For `g = wᵏ` this is `\bar∂ M_k + k M_k ν + k Q_{k-1} μ = 0`
(`TauCeti.conjWirtingerDeriv_sliceMoment_pow_add_add_apply`), and for `ν = μ = 0` it is
`TauCeti.conjWirtingerDeriv_sliceMoment_eq_zero`. -/
theorem conjWirtingerDeriv_sliceMoment_add_add_eq_zero (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hg : Differentiable ℂ g) (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : V}
    (hdT : ∀ w, extDeriv T (z, w) = 0) {L : ℂ → V × ℂ →L[ℝ] V × ℂ} (ν μ : V →L⋆[ℂ] ℂ)
    (hL₁ : ∀ w v, L w (v, 0) = (I • v, 2 * I * (ν v * w + μ v * conj w)))
    (hL₂ : ∀ w n, L w (0, n) = (0, I * n))
    (hJ : ∀ w, ∀ u u' : V × ℂ, T (z, w) ![L w u, L w u'] = T (z, w) ![u, u']) :
    conjWirtingerDeriv (sliceMoment T g) z + sliceMoment T (fun w ↦ w * deriv g w) z • ν +
        sliceMoment T (fun w ↦ conj w * deriv g w) z • μ = 0 := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [conjWirtingerDeriv_sliceMoment_add_add_apply hK hTc hg hT hdT ν μ hL₁ hL₂ v, zero_apply]
  simp [hJ]

end Holomorphic

end TauCeti
