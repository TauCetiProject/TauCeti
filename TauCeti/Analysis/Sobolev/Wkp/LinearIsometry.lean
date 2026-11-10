/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving
public import TauCeti.Analysis.Sobolev.Wkp.Zero

/-!
# Transport of `W^{k,p}` along linear isometries

Let `e : E ≃ₗᵢ[ℝ] E'` be a linear isometry between finite-dimensional real inner product spaces
carrying `μ` to `ν` (for instance `volume` to `volume`, `LinearIsometryEquiv.measurePreserving`),
and let `U = e⁻¹(W)` for open sets `U ⊆ E` and `W ⊆ E'`. For every order `k` and every exponent
`1 ≤ p ≤ ∞`, precomposition with `e` is a linear isometric equivalence

`TauCeti.Wkp.compLinearIsometryEquiv : W^{k,p}(W) ≃ₗᵢ[ℝ] W^{k,p}(U)`.

The value of `u ∘ e` is `u ∘ e`, and its weak derivative of order `k + 1` at `x` is the highest
weak derivative of `u` at `e x`, pulled back by `e` in every slot: at order two this is
`D²(u ∘ e)(x) = e† ∘ D²u(e x) ∘ e`, the formula of
`TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`, where `e† = e⁻¹` is the adjoint of `e`.
The pullback of iterated gradients is `(e.iteratedGradientCongr j).symm`, where
`LinearIsometryEquiv.iteratedGradientCongr` pushes iterated gradients forward along `e`.
Zero boundary values are preserved and reflected: a test function on `W` composed with `e` is a
test function on `U`.

This transports results stated on a model space, such as the Lipschitz-domain theorems on
`WithLp 2 (ℝ × E)`, to any isometric copy of it, for instance from `WithLp 2 (ℝ × ℝ)` to `ℂ`
along `Complex.equivRealProdL2`.

## The argument

At first order the transport is `TauCeti.W1p.compMeasurePreservingL`, whose weak gradient is
`e† (∇u ∘ e) = e⁻¹ (∇u ∘ e)`. Above first order, the highest derivative `D` of `u` is the weak
derivative of the preceding field `G`; the weak chain rule for linear changes of variables
(`TauCeti.HasWeakFDerivOn.comp_continuousLinearEquiv`) followed by the pullback in the remaining
slots (`TauCeti.HasWeakFDerivOn.clm_comp`) shows that the pullback of `D` is the weak derivative of
the pullback of `G`. Both pullbacks are isometric on `Lᵖ`, so the transport does not increase the
norm, and the transport along `e⁻¹` inverts it.

## Main declarations

* `LinearIsometryEquiv.iteratedGradientCongr`: the push-forward of iterated gradients along `e`.
* `TauCeti.Wkp.compLinearIsometryEquiv`: precomposition with `e` on `W^{k,p}`.
* `TauCeti.Wkp.value_compLinearIsometryEquiv_ae`,
  `TauCeti.Wkp.iteratedGradient_compLinearIsometryEquiv_ae`: its value and highest derivative.
* `TauCeti.Wkp.compLinearIsometryEquiv_mem_wkp0Submodule_iff`: zero boundary values are preserved
  and reflected.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal

/-! ### Iterated gradients along a linear isometry -/

section IteratedGradient

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

/-- The push-forward of iterated gradients along a linear isometry `e`: the identity of
`TauCeti.IteratedGradient E 0 = E` with `E'` is `e`, and a field with one more derivative slot
`A : E →L[ℝ] IteratedGradient E j` is sent to `A' ∘ e⁻¹` with `A'` the push-forward of the values
of `A`. -/
def LinearIsometryEquiv.iteratedGradientCongr (e : E ≃ₗᵢ[ℝ] E') :
    (j : ℕ) → TauCeti.IteratedGradient E j ≃ₗᵢ[ℝ] TauCeti.IteratedGradient E' j
  | 0 => e
  | j + 1 =>
    { toLinearEquiv := (e.toContinuousLinearEquiv.arrowCongr
        (LinearIsometryEquiv.iteratedGradientCongr e j).toContinuousLinearEquiv).toLinearEquiv
      norm_map' := fun A => by
        change ‖((LinearIsometryEquiv.iteratedGradientCongr e j :
            TauCeti.IteratedGradient E j →L[ℝ] TauCeti.IteratedGradient E' j).comp
          (A.comp (e.symm : E' →L[ℝ] E)))‖ = ‖A‖
        rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
          ContinuousLinearMap.opNorm_comp_linearIsometryEquiv] }

namespace LinearIsometryEquiv

variable (e : E ≃ₗᵢ[ℝ] E')

@[simp]
theorem iteratedGradientCongr_zero : e.iteratedGradientCongr 0 = e :=
  (rfl)

/-- The push-forward of an iterated gradient with `j + 1` derivative slots. -/
theorem iteratedGradientCongr_succ_apply (j : ℕ) (A : TauCeti.IteratedGradient E (j + 1)) :
    e.iteratedGradientCongr (j + 1) A =
      ((e.iteratedGradientCongr j : TauCeti.IteratedGradient E j →L[ℝ] _).comp
        (A.comp (e.symm : E' →L[ℝ] E)) : E' →L[ℝ] TauCeti.IteratedGradient E' j) :=
  (rfl)

/-- The pullback of an iterated gradient with `j + 1` derivative slots: `A ↦ A' ∘ e`, with `A'`
the pullback of the values of `A`. -/
theorem iteratedGradientCongr_symm_succ_apply (j : ℕ)
    (A : TauCeti.IteratedGradient E' (j + 1)) :
    (e.iteratedGradientCongr (j + 1)).symm A =
      (((e.iteratedGradientCongr j).symm : TauCeti.IteratedGradient E' j →L[ℝ] _).comp
        (A.comp (e : E →L[ℝ] E')) : E →L[ℝ] TauCeti.IteratedGradient E j) :=
  (rfl)

end LinearIsometryEquiv

end IteratedGradient

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] {ν : Measure E'} [ν.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {U : Opens E} {W : Opens E'} {e : E ≃ₗᵢ[ℝ] E'}

namespace Wkp

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
  [FiniteDimensional ℝ E'] [ν.IsAddHaarMeasure] in
private theorem measurePreserving_restrict (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) : MeasurePreserving e (μ.restrict U) (ν.restrict W) :=
  hUW ▸ he.restrict_preimage W.isOpen.measurableSet

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] [FiniteDimensional ℝ E']
  [ν.IsAddHaarMeasure] in
private theorem measurePreserving_symm (he : MeasurePreserving e μ ν) :
    MeasurePreserving e.symm ν μ :=
  MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv he

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] in
private theorem coe_eq_preimage_symm (hUW : (U : Set E) = e ⁻¹' W) :
    (W : Set E') = e.symm ⁻¹' U := by
  rw [hUW, ← preimage_comp]
  ext y
  simp

/-- The pullback `f ↦ (e.iteratedGradientCongr j).symm ∘ f ∘ e` of `Lᵖ` iterated-gradient
fields. -/
private def pullbackLp (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) (j : ℕ) :
    Lp (IteratedGradient E' j) p (ν.restrict W) →L[ℝ] Lp (IteratedGradient E j) p (μ.restrict U) :=
  (((e.iteratedGradientCongr j).symm.toLinearIsometry.toContinuousLinearMap).compLpL p
    (μ.restrict U)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ e (measurePreserving_restrict he hUW)).toContinuousLinearMap

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
  [FiniteDimensional ℝ E'] [ν.IsAddHaarMeasure] in
private theorem pullbackLp_ae (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W)
    (j : ℕ) (f : Lp (IteratedGradient E' j) p (ν.restrict W)) :
    pullbackLp he hUW j f =ᵐ[μ.restrict U] fun x => (e.iteratedGradientCongr j).symm (f (e x)) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLp
      ((e.iteratedGradientCongr j).symm.toLinearIsometry.toContinuousLinearMap)
      (Lp.compMeasurePreserving e (measurePreserving_restrict he hUW) f),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_restrict he hUW)] with x h1 h2
  exact h1.trans (congrArg (e.iteratedGradientCongr j).symm h2)

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure]
  [FiniteDimensional ℝ E'] [ν.IsAddHaarMeasure] in
private theorem norm_pullbackLp_le (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W)
    (j : ℕ) (f : Lp (IteratedGradient E' j) p (ν.restrict W)) :
    ‖pullbackLp he hUW j f‖ ≤ ‖f‖ := by
  refine (ContinuousLinearMap.norm_compLp_le _ _).trans ?_
  refine (mul_le_of_le_one_left (norm_nonneg _)
    (LinearIsometry.norm_toContinuousLinearMap_le _)).trans ?_
  exact ((Lp.compMeasurePreservingₗᵢ ℝ e (measurePreserving_restrict he hUW)).norm_map f).le

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] in
private theorem norm_fderiv_le (x : E) : ‖fderiv ℝ e x‖ ≤ 1 := by
  rw [show (⇑e) = ⇑e.toContinuousLinearEquiv from rfl, ContinuousLinearEquiv.fderiv]
  exact e.toLinearIsometry.norm_toContinuousLinearMap_le

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E'] in
private theorem adjoint_fderiv (x : E) :
    ContinuousLinearMap.adjoint (fderiv ℝ e x) = (e.symm : E' →L[ℝ] E) := by
  rw [show (⇑e) = ⇑e.toContinuousLinearEquiv from rfl, ContinuousLinearEquiv.fderiv]
  exact LinearIsometryEquiv.adjoint_eq_symm e

/-- First-order transport, `TauCeti.W1p.compMeasurePreservingL` with derivative bound `1`. -/
private def compW1p (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) :
    W1p ν W p →L[ℝ] W1p μ U p :=
  W1p.compMeasurePreservingL (M := 1) he hUW
    (e : E →L[ℝ] E').lipschitzWith.locallyLipschitz.locallyLipschitzOn fun x _ => norm_fderiv_le x

private theorem gradient_compW1p (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W)
    (u : Wkp ν W p 1) :
    iteratedGradient 0 (compW1p he hUW u : Wkp μ U p 1) =
      pullbackLp he hUW 0 (iteratedGradient 0 u) := by
  rw [iteratedGradient_zero (mu := μ) (Omega := U) (p := p) (compW1p he hUW u),
    iteratedGradient_zero u]
  refine Lp.ext ?_
  filter_upwards [W1p.gradient_compMeasurePreservingL_ae (p := p) (M := 1) he hUW
      (e : E →L[ℝ] E').lipschitzWith.locallyLipschitz.locallyLipschitzOn
      (fun x _ => norm_fderiv_le x) u,
    pullbackLp_ae he hUW 0 (W1p.gradient u)] with x h1 h2
  rw [compW1p, h1, h2, adjoint_fderiv]
  rfl

/-- The order-`k + 1` transport together with its highest-derivative formula, by recursion on
`k`; the formula at order `k + 1` is what makes the transport at order `k + 2` well defined. -/
private def compSpec (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) :
    (k : ℕ) → {T : Wkp ν W p (k + 1) → Wkp μ U p (k + 1) //
      ∀ u, iteratedGradient k (T u) = pullbackLp he hUW k (iteratedGradient k u)}
  | 0 => ⟨fun u => compW1p he hUW u, gradient_compW1p he hUW⟩
  | k + 1 => ⟨fun u => mk k ((compSpec he hUW k).1 (lowerOrder (k + 1) u))
      (pullbackLp he hUW (k + 1) (iteratedGradient (k + 1) u)) (by
        rw [(compSpec he hUW k).2]
        have h := ((hasWeakFDerivOn_iteratedGradient k u).comp_continuousLinearEquiv
          e.toContinuousLinearEquiv he (hUW ▸ mapsTo_preimage e W)).clm_comp
          (e.iteratedGradientCongr k).symm.toLinearIsometry.toContinuousLinearMap
        refine (h.congr_ae (pullbackLp_ae he hUW k _).symm).congr_ae_deriv ?_
        filter_upwards [pullbackLp_ae he hUW (k + 1) (iteratedGradient (k + 1) u)] with x hx
        rw [hx]
        rfl),
      fun u => iteratedGradient_mk _ _ _ _⟩

private theorem value_compSpec (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) :
    ∀ (k : ℕ) (u : Wkp ν W p (k + 1)), value (k + 1) ((compSpec he hUW k).1 u) =
      Lp.compMeasurePreserving e (measurePreserving_restrict he hUW) (value (k + 1) u)
  | 0, u => (value_one (mu := μ) (Omega := U) (p := p) (compW1p he hUW u)).trans <| by
    rw [value_one u]
    exact Lp.ext ((W1p.value_compMeasurePreservingL_ae (p := p) (M := 1) he hUW
      (e : E →L[ℝ] E').lipschitzWith.locallyLipschitz.locallyLipschitzOn
      (fun x _ => norm_fderiv_le x) u).trans (Lp.coeFn_compMeasurePreserving _ _).symm)
  | k + 1, u => by
    change value (k + 2) (mk k _ _ _) = _
    rw [value_mk, value_compSpec he hUW k, value_succ (k + 1) u]

private theorem lowerOrder_compSpec (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 2)) :
    lowerOrder (k + 1) ((compSpec he hUW (k + 1)).1 u) =
      (compSpec he hUW k).1 (lowerOrder (k + 1) u) :=
  lowerOrder_mk _ _ _ _

private theorem norm_compSpec_le (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) :
    ∀ (k : ℕ) (u : Wkp ν W p (k + 1)), ‖(compSpec he hUW k).1 u‖ ≤ ‖u‖
  | 0, u => by
    change ‖compW1p he hUW u‖ ≤ ‖(u : W1p ν W p)‖
    refine (ContinuousLinearMap.le_of_opNorm_le _ ?_ u).trans_eq (one_mul _)
    exact (W1p.norm_compMeasurePreservingL_le (p := p) (M := 1) he hUW
      (e : E →L[ℝ] E').lipschitzWith.locallyLipschitz.locallyLipschitzOn
      fun x _ => norm_fderiv_le x).trans_eq (max_self 1)
  | k + 1, u => by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
      norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ,
      norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u,
      lowerOrder_compSpec, (compSpec he hUW (k + 1)).2]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (norm_compSpec_le he hUW k _) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_pullbackLp_le he hUW _ _) 2)

/-- The transport as a linear map at every order, including order zero. -/
private def compₗ (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) :
    (k : ℕ) → Wkp ν W p k →ₗ[ℝ] Wkp μ U p k
  | 0 => Lp.compMeasurePreservingₗ ℝ e (measurePreserving_restrict he hUW)
  | k + 1 =>
    { toFun := (compSpec he hUW k).1
      map_add' u v := ext (k + 1) <| by
        rw [value_add, value_compSpec, value_compSpec, value_compSpec, value_add, map_add]
      map_smul' c u := ext (k + 1) <| by
        rw [value_smul, value_compSpec, value_compSpec, value_smul, RingHom.id_apply]
        exact (Lp.compMeasurePreservingₗ ℝ e (measurePreserving_restrict he hUW)).map_smul c _ }

private theorem value_compₗ (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) :
    ∀ (k : ℕ) (u : Wkp ν W p k), value k (compₗ he hUW k u) =
      Lp.compMeasurePreserving e (measurePreserving_restrict he hUW) (value k u)
  | 0, u => by
    rw [value_zero, value_zero]
    rfl
  | k + 1, u => value_compSpec he hUW k u

private theorem norm_compₗ_le (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W) :
    ∀ (k : ℕ) (u : Wkp ν W p k), ‖compₗ he hUW k u‖ ≤ ‖u‖
  | 0, u => by
    change ‖Lp.compMeasurePreserving e (measurePreserving_restrict he hUW)
      (u : Lp ℝ p (ν.restrict W))‖ ≤ _
    exact (Lp.norm_compMeasurePreserving _ _).le
  | k + 1, u => norm_compSpec_le he hUW k u

private theorem compₗ_compₗ (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W)
    (he' : MeasurePreserving e.symm ν μ) (hWU : (W : Set E') = e.symm ⁻¹' U) (k : ℕ)
    (u : Wkp μ U p k) : compₗ he hUW k (compₗ he' hWU k u) = u := by
  refine ext k (Lp.ext ?_)
  rw [value_compₗ, value_compₗ]
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving e.symm (measurePreserving_restrict he' hWU) (value k u))
      (measurePreserving_restrict he hUW),
    (measurePreserving_restrict he hUW).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving (value k u) (measurePreserving_restrict he' hWU))]
    with x h1 h2
  rw [h1, Function.comp_apply, h2, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]

/-- **Transport of `W^{k,p}` along a linear isometry.** If the linear isometry `e` carries `μ`
to `ν` and `U = e⁻¹(W)`, precomposition with `e` is a linear isometric equivalence
`W^{k,p}(W) ≃ₗᵢ[ℝ] W^{k,p}(U)` for every order `k` and every exponent `1 ≤ p ≤ ∞`. Its value and
highest derivative are `TauCeti.Wkp.value_compLinearIsometryEquiv_ae` and
`TauCeti.Wkp.iteratedGradient_compLinearIsometryEquiv_ae`. -/
def compLinearIsometryEquiv (he : MeasurePreserving e μ ν) (hUW : (U : Set E) = e ⁻¹' W)
    (k : ℕ) : Wkp ν W p k ≃ₗᵢ[ℝ] Wkp μ U p k where
  toLinearEquiv :=
    { compₗ he hUW k with
      invFun := compₗ (measurePreserving_symm he) (coe_eq_preimage_symm hUW) k
      left_inv := compₗ_compₗ (e := e.symm) _ _ he hUW k
      right_inv := compₗ_compₗ he hUW _ _ k }
  norm_map' u := le_antisymm (norm_compₗ_le he hUW k u) <| by
    change ‖u‖ ≤ ‖compₗ he hUW k u‖
    exact (congrArg norm (compₗ_compₗ (e := e.symm) _ _ he hUW k u)).symm.trans_le <|
      norm_compₗ_le (measurePreserving_symm he) (coe_eq_preimage_symm hUW) k (compₗ he hUW k u)

/-- The inverse of the transport along `e` is the transport along `e⁻¹`. -/
theorem compLinearIsometryEquiv_symm (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (he' : MeasurePreserving e.symm ν μ)
    (hWU : (W : Set E') = e.symm ⁻¹' U) (k : ℕ) :
    (compLinearIsometryEquiv (p := p) he hUW k).symm = compLinearIsometryEquiv he' hWU k :=
  (rfl)

/-- The value of `u ∘ e` is the value of `u` composed with `e`. -/
theorem value_compLinearIsometryEquiv_ae (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p k) :
    value k (compLinearIsometryEquiv he hUW k u) =ᵐ[μ.restrict U] fun x => value k u (e x) := by
  change value k (compₗ he hUW k u) =ᵐ[μ.restrict U] _
  rw [value_compₗ]
  exact Lp.coeFn_compMeasurePreserving _ _

/-- **The chain rule for the highest derivative.** The weak derivative of order `k + 1` of `u ∘ e`
at `x` is that of `u` at `e x`, pulled back by `e` in every slot; at order two it is
`e† ∘ D²u(e x) ∘ e` (`LinearIsometryEquiv.iteratedGradientCongr_symm_succ_apply`). -/
theorem iteratedGradient_compLinearIsometryEquiv_ae (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    iteratedGradient k (compLinearIsometryEquiv he hUW (k + 1) u) =ᵐ[μ.restrict U]
      fun x => (e.iteratedGradientCongr k).symm (iteratedGradient k u (e x)) := by
  change iteratedGradient k ((compSpec he hUW k).1 u) =ᵐ[μ.restrict U] _
  rw [(compSpec he hUW k).2]
  exact pullbackLp_ae he hUW k _

/-- The transport commutes with forgetting the highest derivative. -/
theorem lowerOrder_compLinearIsometryEquiv (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) (u : Wkp ν W p (k + 1)) :
    lowerOrder k (compLinearIsometryEquiv he hUW (k + 1) u) =
      compLinearIsometryEquiv he hUW k (lowerOrder k u) := by
  refine ext k ?_
  rw [← value_succ]
  change value (k + 1) (compₗ he hUW (k + 1) u) = value k (compₗ he hUW k (lowerOrder k u))
  rw [value_compₗ, value_compₗ, value_succ]

/-- The transport of a test function `φ` on `W` is the test function `φ ∘ e` on `U`. -/
theorem compLinearIsometryEquiv_ofTestFunctionₗ (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (hWU : MapsTo e.symm W U) (k : ℕ) (φ : 𝓓(W, ℝ)) :
    compLinearIsometryEquiv he hUW k (ofTestFunctionₗ (mu := ν) (p := p) k φ) =
      ofTestFunctionₗ k (e.symm.toContinuousLinearEquiv.transportTestFunction hWU φ) := by
  refine ext k (Lp.ext ?_)
  change value k (compₗ he hUW k _) =ᵐ[μ.restrict U] _
  rw [value_compₗ, value_ofTestFunctionₗ, value_ofTestFunctionₗ]
  filter_upwards [Lp.coeFn_compMeasurePreserving (testFunctionLp (mu := ν) p φ)
      (measurePreserving_restrict he hUW),
    (measurePreserving_restrict he hUW).quasiMeasurePreserving.ae
      (testFunctionLp_apply_ae (mu := ν) p φ),
    testFunctionLp_apply_ae (mu := μ) p
      (e.symm.toContinuousLinearEquiv.transportTestFunction hWU φ)] with x h1 h2 h3
  rw [h1, Function.comp_apply, h2, h3]
  exact (ContinuousLinearEquiv.transportTestFunction_apply e.symm.toContinuousLinearEquiv hWU φ
    x).symm

/-- The transport maps `W^{k,p}_0(W)` into `W^{k,p}_0(U)`. -/
theorem compLinearIsometryEquiv_mem_wkp0Submodule (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) {u : Wkp ν W p k} (hu : u ∈ wkp0Submodule ν W p k) :
    compLinearIsometryEquiv he hUW k u ∈ wkp0Submodule μ U p k := by
  have hWU : MapsTo e.symm W U := coe_eq_preimage_symm hUW ▸ mapsTo_preimage e.symm U
  refine wkp0Submodule_subset_of_isClosed k
    ((wkp0Submodule μ U p k).isClosed.preimage (compLinearIsometryEquiv he hUW k).continuous)
    (fun φ => ?_) hu
  rw [mem_preimage, compLinearIsometryEquiv_ofTestFunctionₗ he hUW hWU]
  exact ofTestFunctionₗ_mem_wkp0Submodule k _

/-- **Zero boundary values are invariant under linear isometries.** The transport `u ∘ e` lies in
`W^{k,p}_0(U)` exactly when `u` lies in `W^{k,p}_0(W)`. -/
theorem compLinearIsometryEquiv_mem_wkp0Submodule_iff (he : MeasurePreserving e μ ν)
    (hUW : (U : Set E) = e ⁻¹' W) (k : ℕ) {u : Wkp ν W p k} :
    compLinearIsometryEquiv he hUW k u ∈ wkp0Submodule μ U p k ↔ u ∈ wkp0Submodule ν W p k := by
  refine ⟨fun hu => ?_, compLinearIsometryEquiv_mem_wkp0Submodule he hUW k⟩
  simpa [← compLinearIsometryEquiv_symm he hUW (measurePreserving_symm he)
    (coe_eq_preimage_symm hUW)] using compLinearIsometryEquiv_mem_wkp0Submodule
      (measurePreserving_symm he) (coe_eq_preimage_symm hUW) k hu

end Wkp

end TauCeti
