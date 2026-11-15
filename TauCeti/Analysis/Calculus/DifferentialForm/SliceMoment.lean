/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral

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
private theorem fderiv_apply_base_eq (hTc : ContDiff ℝ 1 T) {x : E × ℂ}
    (hdT : extDeriv T x = 0) (v : E) :
    fderiv ℝ T x (v, 0) ![(0, 1), (0, I)] =
      fderiv ℝ T x (0, 1) ![(v, 0), (0, I)] - fderiv ℝ T x (0, I) ![(v, 0), (0, 1)] := by
  have hd := (hTc.differentiable one_ne_zero) x
  have h := extDeriv_apply hd ![(v, 0), (0, 1), (0, I)]
  rw [hdT, Fin.sum_univ_three] at h
  have hr (A : Fin 2 → E × ℂ) (u : E × ℂ) : fderiv ℝ (T · A) x u = fderiv ℝ T x u A := by
    rw [fderiv_continuousAlternatingMap_apply hd (fun _ ↦ differentiableAt_const _)]
    simp
  have h₀ : Fin.removeNth 0 ![((v, 0) : E × ℂ), (0, 1), (0, I)] = ![(0, 1), (0, I)] := by
    funext i; fin_cases i <;> rfl
  have h₁ : Fin.removeNth 1 ![((v, 0) : E × ℂ), (0, 1), (0, I)] = ![(v, 0), (0, I)] := by
    funext i; fin_cases i <;> rfl
  have h₂ : Fin.removeNth 2 ![((v, 0) : E × ℂ), (0, 1), (0, I)] = ![(v, 0), (0, 1)] := by
    funext i; fin_cases i <;> rfl
  simp only [h₀, h₁, h₂, hr, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, Fin.val_zero,
    Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, even_two,
    Even.neg_pow, one_pow] at h
  linear_combination -h

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
  integrable_of_vanishing hK (((ContinuousAlternatingMap.apply ℝ (E × ℂ) ℝ A).continuous.comp
    (hTc.continuous.comp (Continuous.prodMk_right z))).smul hg) fun w hw ↦ by simp [hT z w hw]

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
  simp only [he, fderiv_apply_base_eq hTc (hdT _) v, sub_smul]
  have hi := integrable_fderiv_coeff_smul hK hTc hg.continuous hT z
  have hj (u : ℂ) (A : Fin 2 → E × ℂ) := integrable_coeff_smul hK hTc
    ((hg.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := u))) hT z A
  rw [integral_sub (hi _ 1) (hi _ I), integral_sub (hj I _) (hj 1 _),
    integral_fderiv_coeff_smul hK hTc hg hT, integral_fderiv_coeff_smul hK hTc hg hT]
  abel

/-- **The derivative of the moments `M_k`.** Under the hypotheses of
`TauCeti.fderiv_sliceMoment_apply`, the moment `M_k(z) = ∫ wᵏ dμ_z` has derivative

`D M_k(z) v = ∫ k w^(k-1) (i T(z, w)(v, ∂_x) - T(z, w)(v, ∂_y)) dw`,

the fibre integral `π_*(k w^(k-1) dw ∧ T)` evaluated on `(v, 0)`. -/
theorem fderiv_sliceMoment_pow_apply (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) {z : E} (hdT : ∀ w, extDeriv T (z, w) = 0) (k : ℕ)
    (v : E) :
    fderiv ℝ (sliceMoment T (· ^ k)) z v = ∫ w, (k : ℂ) * w ^ (k - 1) *
      (I * T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![(v, 0), (0, I)]) := by
  rw [fderiv_sliceMoment_apply hK hTc (by fun_prop : ContDiff ℝ 1 fun w : ℂ ↦ w ^ k) hT hdT v]
  refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
  simp only [((hasDerivAt_pow k w).hasFDerivAt.restrictScalars ℝ).fderiv,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, real_smul]
  ring

end TauCeti
