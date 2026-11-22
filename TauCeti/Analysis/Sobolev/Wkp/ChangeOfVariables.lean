/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.Wkp.Exponent
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Linear
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.MeasureTheory.Function.Lp.Precomposition
public import TauCeti.Topology.Algebra.Module.Trace
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.FaaDiBruno
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.Normed.Affine.Isometry.Basic
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.MeasureTheory.Function.Gluing
import TauCeti.MeasureTheory.Function.Lp.Dilation
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.TendstoExponentTop
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# Changes of variables in higher-order Sobolev spaces `W^{k,p}`

This file develops changes of variables in the weak Sobolev spaces `TauCeti.Wkp` on open subsets
of a finite-dimensional real inner product space `E`. Linear changes of variables in `W^{2,p}` are
in `TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Linear`.

1. **General `Cᵏ` changes of variables in `W^{k,p}`** (`1 ≤ p ≤ ∞`): if `Φ` is a change of
   variables of order `k` from `U` into `V` (`TauCeti.Wkp.IsChangeOfVariables`) — `Cᵏ`,
   differentiable and injective on `U`, mapping `U` into `V`, with derivatives of orders `1`
   through `k` bounded by `L` and `|det DΦ| ≥ c > 0` on `U` — then precomposition with `Φ` is a
   bounded linear operator `TauCeti.Wkp.compL : Wkp mu V p k →L[ℝ] Wkp mu U p k` of norm at most
   `TauCeti.Wkp.compLBound p k L c`. For a `Cᵏ` diffeomorphism with bounded derivatives in both
   directions this gives a Banach-space isomorphism `TauCeti.Wkp.compLEquiv`. For `1 ≤ p < ∞` and
   `k = 2`, the weak Hessian obeys the chain rule
   `D²(u ∘ Φ)(x) = DΦ(x)† ∘ D²u(Φ x) ∘ DΦ(x) + ⟪∇u(Φ x), D²Φ(x)⟫` almost everywhere on `U`
   (`TauCeti.Wkp.inner_iteratedGradient_compL_ae`).
2. **Left-invertible `Cᵏ` maps** (`k : ℕ`, `1 ≤ p ≤ ∞`): when `Φ` is `Cᵏ` on `U` mapping `U` into
   `V` with `‖iteratedFDeriv ℝ i Φ x‖ ≤ L` for `1 ≤ i ≤ k` on `U`, and admits a differentiable
   left inverse `Ψ` on `V` with `‖fderiv ℝ Ψ (Φ x)‖ ≤ L'` on `U`, we have
   `(max 1 L' ^ finrank ℝ E)⁻¹ ≤ |det DΦ|` on `U` (for `k ≥ 1`) and the pushforward of `mu` on `U`
   along `Φ` is at most `max 1 L' ^ finrank ℝ E` times `mu` on `V`, giving the precomposition
   operator `TauCeti.Wkp.compOfLeftInvOnL` and the uniform norm bound
   `TauCeti.Wkp.exists_norm_comp_le`.

## The argument

For `TauCeti.Wkp.compL`, the Faà di Bruno bound `ContDiffAt.norm_iteratedFDeriv_comp_le_sum`
controls the `Lᵖ(U)` seminorms of all derivatives through order `k` on elements with `Cᵏ`
representatives. When `p < ∞`, `Cᵏ` representatives are dense
(`TauCeti.Wkp.dense_contDiffOn_representatives`), so continuous extension gives the operator and
the top-derivative bound. At `p = ∞`, smooth functions are no longer dense in `W^{k,∞}`, so
precomposition is constructed inductively on `k`: at order `0` by
`MeasureTheory.Lp.compOfMapLeSmul`, at order `1` by the weak chain rule
`TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo`, and at order `m + 2` by restricting to small
balls with relatively compact target neighbourhoods, pulling back in `W^{m+2,q}` for `1 ≤ q < ∞`
via `TauCeti.Wkp.ofExponentLEL`, passing `q → ∞` with
`TauCeti.ae_norm_le_of_eventually_nnreal_eLpNorm_le`, and gluing the local weak derivatives via
`TauCeti.exists_hasWeakFDerivOn_iSup`.

For the weak Hessian chain rule along a nonlinear change of variables `Φ` of order two
(`1 ≤ p < ∞`), the weak gradient of `u ∘ Φ` is `DΦ† (∇u ∘ Φ)`, so in an orthonormal basis `(bᵢ)`
each of its components is `⟪∇(u ∘ Φ), c⟫ = ∑ᵢ ⟪DΦ c, bᵢ⟫ ⟪∇u(Φ ·), bᵢ⟫`, a sum of products of
the `C¹` coefficients `⟪DΦ c, bᵢ⟫` with functions `⟪∇u(Φ ·), bᵢ⟫` in `W^{1,p}(U)`. Differentiating
with the product rule (`TauCeti.HasWeakLineDerivOn.contDiffOn_smul_of_ne_zero`) and using
uniqueness of weak derivatives gives the chain rule for the weak Hessian.

## Main declarations

* `TauCeti.Wkp.IsChangeOfVariables`: bundled `Cᵏ` change-of-variables hypotheses, including
  `IsChangeOfVariables.of_leftInvOn`.
* `TauCeti.Wkp.compL`, `TauCeti.Wkp.compLEquiv`: bounded precomposition and diffeomorphism
  invariance on `W^{k,p}` for `1 ≤ p ≤ ∞`.
* `TauCeti.Wkp.compOfLeftInvOnL`, `TauCeti.Wkp.exists_norm_comp_le`: precomposition and uniform
  norm bound for left-invertible `Cᵏ` maps across all orders `k : ℕ` and exponents `1 ≤ p ≤ ∞`.
* `TauCeti.Wkp.IsChangeOfVariables.w1pCompL`: the first-order change of variables
  `TauCeti.W1p.compL` along a change of variables of order at least one.
* `TauCeti.Wkp.IsChangeOfVariables.abs_det_fderiv_eq_one`: mutually inverse changes of variables
  with Jacobian determinants at least one in absolute value have Jacobian determinants of absolute
  value one.
* `TauCeti.Wkp.IsChangeOfVariables.exists_w1p0_value_ae_eq_mul_value_w1pCompL` and
  `TauCeti.Wkp.exists_lowerOrder_eq_restrictL_of_w1pCompL`: local zero boundary values move forward,
  and local `W^{2,p}` regularity moves back, along a change of variables.
* `TauCeti.Wkp.gradient_firstOrder_compL_ae`: the chain rule `∇(u ∘ Φ) = DΦ† ∇u(Φ ·)` for the
  weak gradient.
* `TauCeti.Wkp.inner_iteratedGradient_compL_ae`: the chain rule
  `D²(u ∘ Φ) = DΦ† ∘ D²u(Φ ·) ∘ DΦ + ⟪∇u(Φ ·), D²Φ⟫` for the weak Hessian along a change of
  variables `Φ` of order two.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2–§5.4.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 3.41.
* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Chapter 4.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 9.6.
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped InnerProductSpace

open scoped ENNReal ContDiff Topology

namespace TauCeti.Wkp

private theorem max_one_pos (L : ℝ) : 0 < max 1 L :=
  zero_lt_one.trans_le (le_max_left 1 L)

private theorem inv_max_one_pow_pos (L' : ℝ) (n : ℕ) : 0 < (max 1 L' ^ n)⁻¹ :=
  inv_pos.2 (pow_pos (max_one_pos L') n)

private theorem max_one_pow_mul_card_nonneg (L : ℝ) (i : ℕ) :
    0 ≤ max 1 L ^ i * (Fintype.card (OrderedFinpartition i) : ℝ) :=
  mul_nonneg (pow_nonneg (max_one_pos L).le i) (Nat.cast_nonneg _)

section Hypotheses

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {U V : Opens E} {Φ : E → E} {k : ℕ} {L c : ℝ}

/-- `Φ` is a change of variables of order `k` from `U` into `V`, with constants `L` and `c`: it is
`Cᵏ`, differentiable and injective on `U`, maps `U` into `V`, its derivatives of orders `1`
through `k` are bounded by `L` on `U`, and the absolute value of its Jacobian determinant is at
least `c > 0` on `U`. Differentiability is part of `Cᵏ` once `k ≥ 1`. -/
structure IsChangeOfVariables (k : ℕ) (U V : Opens E) (Φ : E → E) (L c : ℝ) : Prop where
  /-- `Φ` is `Cᵏ` on `U`. -/
  contDiffOn : ContDiffOn ℝ k Φ U
  /-- `Φ` is differentiable on `U`. -/
  differentiableOn : DifferentiableOn ℝ Φ U
  /-- `Φ` is injective on `U`. -/
  injOn : InjOn Φ U
  /-- `Φ` maps `U` into `V`. -/
  mapsTo : MapsTo Φ U V
  /-- The derivatives of `Φ` of orders `1` through `k` are bounded by `L` on `U`. -/
  norm_iteratedFDeriv_le : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L
  /-- The lower bound for the Jacobian is positive. -/
  pos : 0 < c
  /-- The absolute value of the Jacobian determinant of `Φ` is at least `c` on `U`. -/
  le_abs_det : ∀ x ∈ (U : Set E), c ≤ |(fderiv ℝ Φ x).det|

namespace IsChangeOfVariables

/-- A change of variables of order `k` is one of every lower order. -/
theorem mono {j : ℕ} (h : IsChangeOfVariables k U V Φ L c) (hj : j ≤ k) :
    IsChangeOfVariables j U V Φ L c where
  contDiffOn := h.contDiffOn.of_le (by exact_mod_cast hj)
  differentiableOn := h.differentiableOn
  injOn := h.injOn
  mapsTo := h.mapsTo
  norm_iteratedFDeriv_le i hi hij := h.norm_iteratedFDeriv_le i hi (hij.trans hj)
  pos := h.pos
  le_abs_det := h.le_abs_det

/-- A change of variables from `U` into `V` restricts to one from any open `U₁ ⊆ U` into any open
set `V₁` into which it maps `U₁`, with the same constants. -/
theorem mono_set {U₁ V₁ : Opens E} (h : IsChangeOfVariables k U V Φ L c) (hU : U₁ ≤ U)
    (hmaps : MapsTo Φ U₁ V₁) : IsChangeOfVariables k U₁ V₁ Φ L c where
  contDiffOn := h.contDiffOn.mono hU
  differentiableOn := h.differentiableOn.mono hU
  injOn := h.injOn.mono hU
  mapsTo := hmaps
  norm_iteratedFDeriv_le i hi hik x hx := h.norm_iteratedFDeriv_le i hi hik x (hU hx)
  pos := h.pos
  le_abs_det x hx := h.le_abs_det x (hU hx)

/-- The derivative of a change of variables of order at least one is bounded by `L`. -/
theorem norm_fderiv_le (h : IsChangeOfVariables (k + 1) U V Φ L c) :
    ∀ x ∈ (U : Set E), ‖fderiv ℝ Φ x‖ ≤ L := fun x hx => by
  simpa only [norm_iteratedFDeriv_one] using h.norm_iteratedFDeriv_le 1 le_rfl (by omega) x hx

/-- A change of variables has invertible derivative on `U`. -/
theorem det_fderiv_ne_zero (h : IsChangeOfVariables k U V Φ L c) {x : E}
    (hx : x ∈ (U : Set E)) : (fderiv ℝ Φ x).det ≠ 0 := fun h0 =>
  (h.pos.trans_le (h.le_abs_det x hx)).ne' (by rw [h0, abs_zero])

/-- The derivative of a change of variables of order `k + 1` is `Cᵏ` on `U`. -/
theorem contDiffOn_fderiv (h : IsChangeOfVariables (k + 1) U V Φ L c) :
    ContDiffOn ℝ k (fderiv ℝ Φ) U :=
  h.contDiffOn.fderiv_of_isOpen U.isOpen (by push_cast; exact le_rfl)

/-- For mutually inverse changes of variables `Φ` and `Ψ`, `DΨ(Φ x)` is a left inverse of
`DΦ(x)`. -/
theorem fderiv_comp_fderiv_eq_id {U' : Opens E} {Ψ : E → E} {k' : ℕ} {L' c' : ℝ}
    (hΦ : IsChangeOfVariables k U' U Φ L c) (hΨ : IsChangeOfVariables k' U U' Ψ L' c')
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U) {x : E} (hx : x ∈ (U' : Set E)) :
    fderiv ℝ Ψ (Φ x) ∘L fderiv ℝ Φ x = ContinuousLinearMap.id ℝ E := by
  have h := fderiv_comp_fderiv_eq_id_of_invOn hΨ.differentiableOn hΨ.mapsTo hΦ.differentiableOn
    hΨΦ hΦΨ (hΦ.mapsTo hx)
  rwa [hΨΦ hx] at h

/-- Mutually inverse changes of variables whose Jacobian determinants are at least one in absolute
value have Jacobian determinants of absolute value one. -/
theorem abs_det_fderiv_eq_one {U' : Opens E} {Ψ : E → E} {k' : ℕ} {L' : ℝ}
    (hΦ : IsChangeOfVariables k U' U Φ L 1) (hΨ : IsChangeOfVariables k' U U' Ψ L' 1)
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U) {x : E} (hx : x ∈ (U' : Set E)) :
    |(fderiv ℝ Φ x).det| = 1 := by
  have h : (fderiv ℝ Ψ (Φ x)).det * (fderiv ℝ Φ x).det = 1 := by
    rw [← ContinuousLinearMap.det_comp, fderiv_comp_fderiv_eq_id hΦ hΨ hΨΦ hΦΨ hx,
      ContinuousLinearMap.det_id]
  have h1 := hΦ.le_abs_det x hx
  have h2 := hΨ.le_abs_det (Φ x) (hΦ.mapsTo hx)
  have h3 : |(fderiv ℝ Ψ (Φ x)).det| * |(fderiv ℝ Φ x).det| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith

/-- An invertible continuous linear map `A` mapping `U` into `V` is a change of variables of every
order, with constants `‖A‖` and `|det A|`. -/
theorem continuousLinearEquiv (A : E ≃L[ℝ] E) (hA : MapsTo A U V) :
    IsChangeOfVariables k U V A ‖(A : E →L[ℝ] E)‖ |(A : E →L[ℝ] E).det| where
  contDiffOn := A.contDiff.contDiffOn
  differentiableOn := A.differentiable.differentiableOn
  injOn := A.injective.injOn
  mapsTo := hA
  norm_iteratedFDeriv_le i hi _ x _ := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hi
    rw [← norm_iteratedFDeriv_fderiv]
    have hd : fderiv ℝ A = fun _ => (A : E →L[ℝ] E) := funext fun _ => A.fderiv
    rcases n with _ | n
    · simp [hd]
    · rw [hd, iteratedFDeriv_const_of_ne n.succ_ne_zero]
      simp
  pos := abs_pos.2 (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  le_abs_det x _ := by rw [A.fderiv]

/-- A translation `x ↦ x + a` mapping `U` into `V` is a change of variables of every order, with
constants `1` and `1`. -/
theorem add_const (a : E) (hA : MapsTo (· + a) U V) :
    IsChangeOfVariables k U V (· + a) 1 1 := by
  have hd : fderiv ℝ (· + a) = fun _ : E ↦ ContinuousLinearMap.id ℝ E :=
    funext fun x ↦ by simp [fderiv_add_const]
  exact
    { contDiffOn := (contDiff_id.add contDiff_const).contDiffOn
      differentiableOn := (differentiable_id.add_const a).differentiableOn
      injOn := (add_left_injective a).injOn
      mapsTo := hA
      norm_iteratedFDeriv_le := fun i hi _ x _ ↦ by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hi
        rw [← norm_iteratedFDeriv_fderiv]
        rcases n with _ | n
        · simpa [hd] using ContinuousLinearMap.norm_id_le
        · rw [hd, iteratedFDeriv_const_of_ne n.succ_ne_zero]
          simp
      pos := one_pos
      le_abs_det := fun x _ ↦ by simp [ContinuousLinearMap.det] }

/-- Composing a change of variables `Φ` on the right with an affine isometry equivalence
`e₁ : F ≃ᵃⁱ E` and on the left with another, `e₂ : E ≃ᵃⁱ F`, gives a change of variables
`e₂ ∘ Φ ∘ e₁` with the same constants: its iterated derivatives have the same norms, and its
Jacobian determinant is that of `Φ` times that of the linear isometry `e₁ ∘ e₂`, of absolute value
one. -/
theorem affineIsometryEquiv_comp_comp {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {U' V' : Opens F} (h : IsChangeOfVariables k U V Φ L c) (e₁ : F ≃ᵃⁱ[ℝ] E) (e₂ : E ≃ᵃⁱ[ℝ] F)
    (hU : MapsTo e₁ U' U) (hV : MapsTo e₂ V V') :
    IsChangeOfVariables k U' V' (e₂ ∘ Φ ∘ e₁) L c := by
  set A := e₁.toAffineIsometry.toContinuousAffineMap
  set B := e₂.toAffineIsometry.toContinuousAffineMap
  refine ⟨B.contDiff.comp_contDiffOn (h.contDiffOn.comp A.contDiff.contDiffOn hU),
    B.differentiable.comp_differentiableOn (h.differentiableOn.comp A.differentiableOn hU),
    e₂.injective.comp_injOn (h.injOn.comp e₁.injective.injOn hU), hV.comp (h.mapsTo.comp hU),
    fun i hi hik x hx ↦ ?_, h.pos, fun x hx ↦ ?_⟩
  · rw [AffineIsometryEquiv.norm_iteratedFDeriv_comp_left _ _ _ (by omega),
      AffineIsometryEquiv.norm_iteratedFDeriv_comp_right]
    exact h.norm_iteratedFDeriv_le i hi hik (e₁ x) (hU hx)
  · have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (e₁ x)) (e₁ x) :=
      (h.differentiableOn.differentiableAt (U.isOpen.mem_nhds (hU hx))).hasFDerivAt
    have hd : HasFDerivAt (e₂ ∘ Φ ∘ e₁) (B.contLinear.comp ((fderiv ℝ Φ (e₁ x)).comp A.contLinear))
        x :=
      (B.hasFDerivAt (x := Φ (e₁ x))).comp x (hΦ.comp x (A.hasFDerivAt (x := x)))
    -- The derivative `De₂ ∘ DΦ(e₁ x) ∘ De₁` is the conjugate by the linear part of `e₁` of
    -- `w ∘ DΦ(e₁ x)`, where `w` is the linear isometry `De₁ ∘ De₂` of `E`. The linear part of an
    -- affine isometry equivalence is its linear isometry equivalence by construction (`rfl`).
    set w := e₂.linearIsometryEquiv.trans e₁.linearIsometryEquiv
    have hA : ∀ y, A.contLinear y = e₁.linearIsometryEquiv y := fun _ ↦ rfl
    have hB : ∀ y, B.contLinear y = e₂.linearIsometryEquiv y := fun _ ↦ rfl
    have hconj : (B.contLinear.comp ((fderiv ℝ Φ (e₁ x)).comp A.contLinear) : F →ₗ[ℝ] F) =
        (e₁.linearIsometryEquiv.symm.toLinearEquiv : E →ₗ[ℝ] F) ∘ₗ
          ((w.toLinearEquiv : E →ₗ[ℝ] E) ∘ₗ (fderiv ℝ Φ (e₁ x) : E →ₗ[ℝ] E)) ∘ₗ
            (e₁.linearIsometryEquiv.symm.toLinearEquiv.symm : F →ₗ[ℝ] E) := by
      ext y
      simp only [ContinuousLinearMap.toLinearMap_comp, LinearMap.coe_comp,
        ContinuousLinearMap.coe_coe, Function.comp_apply, LinearIsometryEquiv.toLinearEquiv_symm,
        LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.symm_symm, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_symm_toLinearEquiv, LinearIsometryEquiv.coe_toLinearEquiv,
        LinearEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply, hA, hB, w]
    have hw : |LinearMap.det (w.toLinearEquiv : E →ₗ[ℝ] E)| = 1 := by
      by_cases hE : FiniteDimensional ℝ E
      · rw [← LinearMap.normDet_eq_abs_det]
        exact w.toLinearIsometry.normDet_eq_one
      · rw [LinearMap.det_eq_one_of_not_module_finite hE, abs_one]
    rw [hd.fderiv, ContinuousLinearMap.det, hconj, LinearMap.det_conj, LinearMap.det_comp, abs_mul,
      hw, one_mul]
    exact h.le_abs_det (e₁ x) (hU hx)

/-- Conjugating a change of variables `Φ` by an affine isometry equivalence `e` gives a change of
variables `e⁻¹ ∘ Φ ∘ e` with the same constants. -/
theorem conj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {U' V' : Opens F}
    (h : IsChangeOfVariables k U V Φ L c) (e : F ≃ᵃⁱ[ℝ] E) (hU : MapsTo e U' U)
    (hV : MapsTo e.symm V V') : IsChangeOfVariables k U' V' (e.symm ∘ Φ ∘ e) L c :=
  h.affineIsometryEquiv_comp_comp e e.symm hU hV

/-- Composing a change of variables `Φ` on the left with an affine isometry equivalence `e` gives a
change of variables `e ∘ Φ` with the same constants. -/
theorem affineIsometryEquiv_comp {V' : Opens E} (h : IsChangeOfVariables k U V Φ L c)
    (e : E ≃ᵃⁱ[ℝ] E) (hV : MapsTo e V V') : IsChangeOfVariables k U V' (e ∘ Φ) L c :=
  h.affineIsometryEquiv_comp_comp (AffineIsometryEquiv.refl ℝ E) e (fun _ hx => hx) hV

/-- **Changes of variables on relatively compact sets.** A map that is `Cⁿ` on an open set `Ω`,
with `k ≤ n` and `1 ≤ n`, injective on `U` and mapping `U` into `V`, whose Jacobian determinant
does not vanish on the compact set `closure U ⊆ Ω`, is a change of variables of order `k` from
`U` into `V`. -/
theorem exists_of_isCompact_closure {n : WithTop ℕ∞} {Ω : Set E}
    (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ n Φ Ω) (hk : k ≤ n) (hn : 1 ≤ n) (hinj : InjOn Φ U)
    (hdet : ∀ x ∈ closure (U : Set E), (fderiv ℝ Φ x).det ≠ 0)
    (hUc : IsCompact (closure (U : Set E))) (hUΩ : closure (U : Set E) ⊆ Ω)
    (hUV : MapsTo Φ U V) : ∃ L c, IsChangeOfVariables k U V Φ L c := by
  obtain ⟨L, -, hL⟩ := (hΦ.of_le hk).exists_nonneg_bound_iteratedFDeriv_of_isOpen hΩ hUc hUΩ
  obtain ⟨c, -, hc, hcdet, -⟩ := exists_det_bounds_of_isCompact hΩ (hΦ.of_le hn) hUc hUΩ hdet
  have hUΩ' := subset_closure.trans hUΩ
  exact ⟨L, c,
    { contDiffOn := (hΦ.of_le hk).mono hUΩ'
      differentiableOn := ((hΦ.of_le hn).differentiableOn one_ne_zero).mono hUΩ'
      injOn := hinj
      mapsTo := hUV
      norm_iteratedFDeriv_le := fun i _ hik x hx ↦ hL i hik x (subset_closure hx)
      pos := hc
      le_abs_det := fun x hx ↦ hcdet x (subset_closure hx) }⟩

/-- The identity map is a change of variables of every order from `U` to itself, with constants
`1` and `1`. -/
theorem id (k : ℕ) (U : Opens E) : IsChangeOfVariables k U U _root_.id 1 1 := by
  convert add_const (k := k) (U := U) (V := U) (0 : E) (fun _ hx => by simpa using hx) using 1
  ext x
  exact (add_zero x).symm

/-- **A `Cᵏ` map with a differentiable left inverse is a change of variables.** If `k ≥ 1`, `Φ` is
`Cᵏ` on `U` with derivatives of orders `1` through `k` bounded by `L` and maps `U` into `V`, and
`Ψ` is differentiable on `V` with `Ψ (Φ x) = x` and `‖fderiv ℝ Ψ (Φ x)‖ ≤ L'` on `U`, then `Φ` is
a change of variables of order `k` with Jacobian lower bound `(max 1 L' ^ finrank ℝ E)⁻¹`. -/
theorem of_leftInvOn {Ψ : E → E} {L' : ℝ} (hk : 1 ≤ k) (hΦ : ContDiffOn ℝ k Φ U)
    (hΨ : DifferentiableOn ℝ Ψ V) (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') :
    IsChangeOfVariables k U V Φ L (max 1 L' ^ Module.finrank ℝ E)⁻¹ := by
  have hdiff : DifferentiableOn ℝ Φ U :=
    hΦ.differentiableOn (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hk)
  refine
    { contDiffOn := hΦ
      differentiableOn := hdiff
      injOn := hΨΦ.injOn
      mapsTo := hmaps
      norm_iteratedFDeriv_le := hL
      pos := inv_max_one_pow_pos L' _
      le_abs_det := fun x hx => ?_ }
  have hΦx : DifferentiableAt ℝ Φ x := (hdiff x hx).differentiableAt (U.isOpen.mem_nhds hx)
  have hΨx : DifferentiableAt ℝ Ψ (Φ x) :=
    (hΨ (Φ x) (hmaps hx)).differentiableAt (V.isOpen.mem_nhds (hmaps hx))
  have hev : Ψ ∘ Φ =ᶠ[𝓝 x] _root_.id :=
    Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds hx) fun y hy => hΨΦ hy
  exact hΦx.inv_pow_le_abs_det_fderiv_of_comp_eventuallyEq_id hΨx hev
    ((hL' x hx).trans (le_max_right 1 L'))

variable [MeasurableSpace E] [BorelSpace E] {mu : Measure E}

/-- A change of variables is almost everywhere measurable on `U`. -/
theorem aemeasurable (h : IsChangeOfVariables k U V Φ L c) : AEMeasurable Φ (mu.restrict U) :=
  h.differentiableOn.continuousOn.aemeasurable U.isOpen.measurableSet

variable [FiniteDimensional ℝ E]

/-- Precomposition with a change of variables is bounded on `Lᵖ`: the pushforward of the
restriction of `μ` to `U` is at most `c⁻¹` times its restriction to `V`. -/
theorem map_restrict_le (mu : Measure E) [mu.IsAddHaarMeasure]
    (h : IsChangeOfVariables k U V Φ L c) :
    (mu.restrict U).map Φ ≤ (ENNReal.ofReal c)⁻¹ • mu.restrict V :=
  map_restrict_le_smul_restrict_of_differentiableOn mu U.isOpen h.differentiableOn h.injOn
    h.mapsTo h.pos h.le_abs_det

/-- Almost-everywhere statements on `V` pull back along a change of variables to
almost-everywhere statements on `U`. -/
theorem ae_comp [mu.IsAddHaarMeasure] (h : IsChangeOfVariables k U V Φ L c) {P : E → Prop}
    (hP : ∀ᵐ y ∂mu.restrict V, P y) : ∀ᵐ x ∂mu.restrict U, P (Φ x) :=
  ae_comp_of_map_absolutelyContinuous h.aemeasurable
    (Measure.absolutelyContinuous_of_le_smul (h.map_restrict_le mu)) hP

end IsChangeOfVariables

end Hypotheses

/-- The constant `c^(-1/p) ∑_{i ≤ k} max 1 L ^ i · #{ordered partitions of i}` bounding the norm
of precomposition with a change of variables of order `k` and constants `L`, `c` on `W^{k,p}`. -/
def compLBound (p : ℝ≥0∞) (k : ℕ) (L c : ℝ) : ℝ :=
  c⁻¹ ^ (1 / p).toReal *
    ∑ i ∈ Finset.range (k + 1), max 1 L ^ i * (Fintype.card (OrderedFinpartition i) : ℝ)

/-- Defining formula for `compLBound`. -/
theorem compLBound_def (p : ℝ≥0∞) (k : ℕ) (L c : ℝ) :
    compLBound p k L c = c⁻¹ ^ (1 / p).toReal *
      ∑ i ∈ Finset.range (k + 1), max 1 L ^ i * (Fintype.card (OrderedFinpartition i) : ℝ) :=
  (rfl)

/-- At order `0`, `compLBound p 0 L c` reduces to the `Lᵖ` Jacobian factor
`c⁻¹ ^ (1 / p).toReal`. -/
@[simp]
theorem compLBound_zero (p : ℝ≥0∞) (L c : ℝ) : compLBound p 0 L c = c⁻¹ ^ (1 / p).toReal := by
  simp [compLBound_def, Fintype.card_unique]

/-- Advancing `compLBound` from order `k` to `k + 1` adds
`c⁻¹ ^ (1 / p).toReal * (max 1 L ^ (k + 1) * #{ordered partitions of k + 1})`. -/
theorem compLBound_succ (p : ℝ≥0∞) (k : ℕ) (L c : ℝ) :
    compLBound p (k + 1) L c = compLBound p k L c + c⁻¹ ^ (1 / p).toReal *
      (max 1 L ^ (k + 1) * (Fintype.card (OrderedFinpartition (k + 1)) : ℝ)) := by
  rw [compLBound_def, compLBound_def, Finset.sum_range_succ, mul_add]

/-- The constant `compLBound p k L c` is positive when `0 < c`. -/
theorem compLBound_pos (p : ℝ≥0∞) (k : ℕ) (L : ℝ) {c : ℝ} (hc : 0 < c) :
    0 < compLBound p k L c := by
  rw [compLBound_def]
  exact mul_pos (Real.rpow_pos_of_pos (inv_pos.2 hc) _)
    (Finset.sum_pos' (fun i _ => max_one_pow_mul_card_nonneg L i)
      ⟨0, Finset.mem_range.2 k.succ_pos, by simp [Fintype.card_unique]⟩)

/-- The constant `compLBound p k L c` is nonnegative. -/
theorem compLBound_nonneg (p : ℝ≥0∞) (k : ℕ) (L : ℝ) {c : ℝ} (hc : 0 < c) :
    0 ≤ compLBound p k L c := (compLBound_pos p k L hc).le

/-- For `0 < c ≤ 1`, `compLBound p k L c` is antitone in nonzero exponents `p`. -/
theorem compLBound_anti_left {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hpq : p ≤ q) (k : ℕ) (L : ℝ) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) : compLBound q k L c ≤ compLBound p k L c := by
  rw [compLBound_def, compLBound_def]
  refine mul_le_mul_of_nonneg_right ?_
    (Finset.sum_nonneg fun i _ => max_one_pow_mul_card_nonneg L i)
  exact Real.rpow_le_rpow_of_exponent_le (one_le_inv₀ hc0 |>.2 hc1)
    (ENNReal.toReal_mono (by simp [hp0]) (ENNReal.div_le_div_left hpq 1))

/-- For `0 < c ≤ 1` and `1 ≤ p`, `compLBound p k L c` is bounded above by its `L¹` value
`compLBound 1 k L c`. -/
theorem compLBound_le_compLBound_one {p : ℝ≥0∞} (hp : 1 ≤ p) (k : ℕ) (L : ℝ) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) : compLBound p k L c ≤ compLBound 1 k L c :=
  compLBound_anti_left one_ne_zero hp k L hc0 hc1

/-- The constant `compLBound ∞ k L c` is at least one: the exponent of `c` vanishes, and the
summand for `i = 0` is one. -/
theorem one_le_compLBound_top (k : ℕ) (L c : ℝ) : 1 ≤ compLBound ⊤ k L c := by
  rw [compLBound_def, ENNReal.div_top, ENNReal.toReal_zero, Real.rpow_zero, one_mul]
  calc (1 : ℝ) = max 1 L ^ 0 * (Fintype.card (OrderedFinpartition 0) : ℝ) := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun i => max 1 L ^ i *
        (Fintype.card (OrderedFinpartition i) : ℝ)) (fun i _ => max_one_pow_mul_card_nonneg L i)
        (Finset.mem_range.2 k.succ_pos)

open scoped NNReal in
/-- As the finite exponent `q` tends to `∞`, the constant `compLBound q k L c` tends to
`compLBound ∞ k L c`. -/
theorem tendsto_compLBound_coe_atTop (k : ℕ) (L : ℝ) {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun q : ℝ≥0 => compLBound q k L c) atTop (𝓝 (compLBound ⊤ k L c)) := by
  simp only [compLBound_def]
  rw [ENNReal.div_top, ENNReal.toReal_zero, Real.rpow_zero]
  refine (((Real.tendsto_const_rpow_inv_atTop (inv_ne_zero hc)).comp
    (NNReal.tendsto_coe_atTop.2 tendsto_id)).congr fun q => ?_).mul_const _
  rw [Function.comp_apply, id_eq, one_div, ENNReal.toReal_inv, ENNReal.coe_toReal]

section Calculus

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U V W : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {Φ Ψ : E → E} {k : ℕ} {L L' c c' : ℝ}

/-! ### The smooth case -/

section Smooth

/-- The Faà di Bruno estimate integrated over `U`: the `Lᵖ(U)` seminorm of the `i`-th derivative of
`f ∘ Φ` is controlled by the `Lᵖ(V)` seminorms of the derivatives of `f` of order at most `i`. -/
private theorem eLpNorm_iteratedFDeriv_comp_le (h : IsChangeOfVariables k U V Φ L c)
    {f : E → ℝ} (hf : ContDiffOn ℝ k f V) {i : ℕ} (hi : i ≤ k) :
    eLpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) p (mu.restrict U) ≤
      ENNReal.ofReal (max 1 L ^ i) * ∑ π : OrderedFinpartition i,
        (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal *
          eLpNorm (iteratedFDeriv ℝ π.length f) p (mu.restrict V) := by
  have hi' : ((i : ℕ) : ℕ∞ω) ≤ k := by exact_mod_cast hi
  have hfΦ : ContDiffOn ℝ k (f ∘ Φ) U := hf.comp h.contDiffOn h.mapsTo
  calc eLpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) p (mu.restrict U)
      ≤ eLpNorm (fun x => max 1 L ^ i * ∑ π : OrderedFinpartition i,
          ‖iteratedFDeriv ℝ π.length f (Φ x)‖) p (mu.restrict U) := by
        refine eLpNorm_mono_ae_real ((ContinuousOn.continuousOn_iteratedFDeriv hfΦ U.isOpen
          hi').aestronglyMeasurable U.isOpen.measurableSet) ?_
        filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
        exact ((hf.contDiffAt (V.isOpen.mem_nhds (h.mapsTo hx))).of_le
          hi').norm_iteratedFDeriv_comp_le_sum
          ((h.contDiffOn.contDiffAt (U.isOpen.mem_nhds hx)).of_le hi')
          fun j hj1 hji => h.norm_iteratedFDeriv_le j hj1 (hji.trans hi) x hx
    _ = ENNReal.ofReal (max 1 L ^ i) * eLpNorm (∑ π : OrderedFinpartition i,
          fun x => ‖iteratedFDeriv ℝ π.length f (Φ x)‖) p (mu.restrict U) := by
        rw [← Real.eNorm_of_nonneg (pow_nonneg (max_one_pos L).le i),
          ← eLpNorm_const_smul]
        congr 1
        funext x
        simp [Finset.sum_apply]
    _ ≤ ENNReal.ofReal (max 1 L ^ i) * ∑ π : OrderedFinpartition i,
          eLpNorm (fun x => ‖iteratedFDeriv ℝ π.length f (Φ x)‖) p (mu.restrict U) := by
        gcongr
        exact eLpNorm_sum_le Fact.out
    _ ≤ _ := by
        gcongr with π
        calc eLpNorm (fun x => ‖iteratedFDeriv ℝ π.length f (Φ x)‖) p (mu.restrict U)
            = eLpNorm ((fun y => ‖iteratedFDeriv ℝ π.length f y‖) ∘ Φ) p (mu.restrict U) := rfl
          _ ≤ (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal *
              eLpNorm (fun y => ‖iteratedFDeriv ℝ π.length f y‖) p (mu.restrict V) :=
            eLpNorm_comp_le_of_map_le_smul h.aemeasurable (h.map_restrict_le mu) p
          _ = _ := by
            rw [eLpNorm_norm]
            exact (ContinuousOn.continuousOn_iteratedFDeriv hf V.isOpen
              (by exact_mod_cast π.length_le.trans hi)).aestronglyMeasurable
                V.isOpen.measurableSet

/-- If `u ∈ W^{k,p}(V)` has a `Cᵏ` representative `f`, every derivative of `f ∘ Φ` through order
`k` has `Lᵖ(U)` seminorm at most `max 1 L ^ i · #{ordered partitions of i} · c^(-1/p) · ‖u‖`. -/
private theorem eLpNorm_iteratedFDeriv_comp_le_norm (h : IsChangeOfVariables k U V Φ L c)
    (u : Wkp mu V p k) {f : E → ℝ} (hf : ContDiffOn ℝ k f V)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict V] f) {i : ℕ} (hi : i ≤ k) :
    eLpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) p (mu.restrict U) ≤
      ENNReal.ofReal (max 1 L ^ i * Fintype.card (OrderedFinpartition i) *
        c⁻¹ ^ (1 / p).toReal * ‖u‖) := by
  have hmem := memLp_iteratedFDeriv_of_contDiffOn k u hf hu
  have hC : (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal = ENNReal.ofReal (c⁻¹ ^ (1 / p).toReal) := by
    rw [← ENNReal.ofReal_inv_of_pos h.pos,
      ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 h.pos.le) ENNReal.toReal_nonneg]
  have hc' : 0 ≤ c⁻¹ ^ (1 / p).toReal := by have := h.pos; positivity
  have hM : 0 ≤ max 1 L ^ i := pow_nonneg (max_one_pos L).le i
  refine (eLpNorm_iteratedFDeriv_comp_le h hf hi).trans ?_
  calc ENNReal.ofReal (max 1 L ^ i) * ∑ π : OrderedFinpartition i,
        (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal *
          eLpNorm (iteratedFDeriv ℝ π.length f) p (mu.restrict V)
      ≤ ENNReal.ofReal (max 1 L ^ i) *
          ∑ _π : OrderedFinpartition i, ENNReal.ofReal (c⁻¹ ^ (1 / p).toReal * ‖u‖) := by
        gcongr with π
        rw [hC, ENNReal.ofReal_mul hc', ← ofReal_lpNorm (hmem _ (π.length_le.trans hi))]
        gcongr
        exact lpNorm_iteratedFDeriv_le_of_contDiffOn k u hf hu _ (π.length_le.trans hi)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hM]
        congr 1
        ring

/-- **The smooth case.** If `u ∈ W^{k,p}(V)` has a `Cᵏ` representative `f`, then `f ∘ Φ`
represents an element of `W^{k,p}(U)` of norm at most `compLBound p k L c * ‖u‖`. -/
private theorem exists_comp_of_contDiffOn (h : IsChangeOfVariables k U V Φ L c)
    (u : Wkp mu V p k) {f : E → ℝ} (hf : ContDiffOn ℝ k f V)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict V] f) :
    ∃ w : Wkp mu U p k, (value k w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value k u (Φ x)) ∧
      ‖w‖ ≤ compLBound p k L c * ‖u‖ := by
  have hfΦ : ContDiffOn ℝ k (f ∘ Φ) U := hf.comp h.contDiffOn h.mapsTo
  have hbound := fun i (hi : i ≤ k) => eLpNorm_iteratedFDeriv_comp_le_norm h u hf hu hi
  have hmem : ∀ i ≤ k, MemLp (iteratedFDeriv ℝ i (f ∘ Φ)) p (mu.restrict U) := fun i hi =>
    (hbound i hi).trans_lt ENNReal.ofReal_lt_top
  obtain ⟨w, hw⟩ := exists_value_ae_eq_of_contDiffOn k hfΦ hmem
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw, h.ae_comp hu] with x hx hux
    rw [hx, Function.comp_apply, hux]
  · refine (norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k w hfΦ hw).trans ?_
    calc ∑ i ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ i (f ∘ Φ)) p (mu.restrict U)
        ≤ ∑ i ∈ Finset.range (k + 1), max 1 L ^ i * Fintype.card (OrderedFinpartition i) *
            c⁻¹ ^ (1 / p).toReal * ‖u‖ := by
          refine Finset.sum_le_sum fun i hi => ENNReal.toReal_le_of_le_ofReal ?_
            (hbound i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
          have := h.pos
          have := max_one_pow_mul_card_nonneg L i
          positivity
      _ = compLBound p k L c * ‖u‖ := by
          rw [compLBound_def, Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring

end Smooth

/-! ### Extension to all of `W^{k,p}` -/

section Extension

/-- The elements of `W^{k,p}(V)` with a representative that is `Cᵏ` on `V`. -/
private def smoothSubmodule (mu : Measure E) [mu.IsAddHaarMeasure] (V : Opens E) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (k : ℕ) : Submodule ℝ (Wkp mu V p k) where
  carrier := {u | ∃ f : E → ℝ, ContDiffOn ℝ k f V ∧ (value k u : E → ℝ) =ᵐ[mu.restrict V] f}
  add_mem' := by
    rintro u v ⟨f, hf, hu⟩ ⟨g, hg, hv⟩
    refine ⟨f + g, hf.add hg, ?_⟩
    rw [value_add]
    filter_upwards [Lp.coeFn_add (value k u) (value k v), hu, hv] with x hx hux hvx
    rw [hx, Pi.add_apply, hux, hvx, Pi.add_apply]
  zero_mem' := ⟨0, contDiffOn_const, by
    rw [← valueL_apply, map_zero]
    exact Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro a u ⟨f, hf, hu⟩
    refine ⟨a • f, hf.const_smul a, ?_⟩
    rw [value_smul]
    filter_upwards [Lp.coeFn_smul a (value k u), hu] with x hx hux
    rw [hx, Pi.smul_apply, hux, Pi.smul_apply]

private theorem denseRange_smoothSubmodule_subtype (hp : p ≠ ⊤) :
    DenseRange (smoothSubmodule mu V p k).subtype := by
  refine (dense_contDiffOn_representatives hp k).mono ?_
  rintro u ⟨f, hf, hu⟩
  exact ⟨⟨u, f, hf.of_le (by exact_mod_cast le_top), hu⟩, rfl⟩

/-- Precomposition with `Φ` on the elements with a `Cᵏ` representative. -/
private def compSmooth (h : IsChangeOfVariables k U V Φ L c) (u : smoothSubmodule mu V p k) :
    Wkp mu U p k :=
  (exists_comp_of_contDiffOn h (u : Wkp mu V p k) u.property.choose_spec.1
      u.property.choose_spec.2).choose

private theorem value_compSmooth_ae (h : IsChangeOfVariables k U V Φ L c)
    (u : smoothSubmodule mu V p k) :
    (value k (compSmooth h u) : E → ℝ) =ᵐ[mu.restrict U]
      fun x => value k (u : Wkp mu V p k) (Φ x) :=
  (exists_comp_of_contDiffOn h (u : Wkp mu V p k) u.property.choose_spec.1
    u.property.choose_spec.2).choose_spec.1

private theorem norm_compSmooth_le (h : IsChangeOfVariables k U V Φ L c)
    (u : smoothSubmodule mu V p k) :
    ‖compSmooth h u‖ ≤ compLBound p k L c * ‖(u : Wkp mu V p k)‖ :=
  (exists_comp_of_contDiffOn h (u : Wkp mu V p k) u.property.choose_spec.1
    u.property.choose_spec.2).choose_spec.2

private theorem norm_iteratedGradient_compSmooth_le (h : IsChangeOfVariables (k + 1) U V Φ L c)
    (u : smoothSubmodule mu V p (k + 1)) :
    ‖iteratedGradient k (compSmooth h u)‖ ≤
      max 1 L ^ (k + 1) * Fintype.card (OrderedFinpartition (k + 1)) *
        c⁻¹ ^ (1 / p).toReal * ‖(u : Wkp mu V p (k + 1))‖ := by
  have hf := u.property.choose_spec.1
  have hu := u.property.choose_spec.2
  have hfΦ : ContDiffOn ℝ (k + 1) (u.property.choose ∘ Φ) U := hf.comp h.contDiffOn h.mapsTo
  have hw : (value (k + 1) (compSmooth h u) : E → ℝ) =ᵐ[mu.restrict U] u.property.choose ∘ Φ :=
    (value_compSmooth_ae h u).trans (h.ae_comp hu)
  rw [norm_iteratedGradient_eq_lpNorm_of_contDiffOn k (compSmooth h u) hfΦ hw]
  refine ENNReal.toReal_le_of_le_ofReal ?_
    (eLpNorm_iteratedFDeriv_comp_le_norm h (u : Wkp mu V p (k + 1)) hf hu le_rfl)
  have := h.pos
  have := max_one_pow_mul_card_nonneg L (k + 1)
  positivity

/-- Precomposition with `Φ` on the elements with a `Cᵏ` representative, as a linear map. -/
private def compSmoothₗ (h : IsChangeOfVariables k U V Φ L c) :
    smoothSubmodule mu V p k →ₗ[ℝ] Wkp mu U p k where
  toFun := compSmooth h
  map_add' u v := by
    refine ext k (Lp.ext ?_)
    rw [value_add]
    filter_upwards [value_compSmooth_ae h (u + v), value_compSmooth_ae h u,
      value_compSmooth_ae h v, Lp.coeFn_add (value k (compSmooth h u)) (value k (compSmooth h v)),
      h.ae_comp (Lp.coeFn_add (value k (u : Wkp mu V p k)) (value k (v : Wkp mu V p k)))]
      with x h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, Submodule.coe_add, value_add, h5, Pi.add_apply]
  map_smul' a u := by
    refine ext k (Lp.ext ?_)
    rw [value_smul, RingHom.id_apply]
    filter_upwards [value_compSmooth_ae h (a • u), value_compSmooth_ae h u,
      Lp.coeFn_smul a (value k (compSmooth h u)),
      h.ae_comp (Lp.coeFn_smul a (value k (u : Wkp mu V p k)))] with x h1 h2 h3 h4
    rw [h1, h3, Pi.smul_apply, h2, Submodule.coe_smul, value_smul, h4, Pi.smul_apply]

private theorem IsChangeOfVariables.map_restrict_le' (h : IsChangeOfVariables k U V Φ L c) :
    (mu.restrict U).map Φ ≤ ENNReal.ofReal c⁻¹ • mu.restrict V :=
  ENNReal.ofReal_inv_of_pos h.pos ▸ h.map_restrict_le mu

/-- Precomposition in `W^{k,p}` for finite exponent `p < ∞`, defined by continuous extension from
`Cᵏ` representatives. -/
private def compLFinite (h : IsChangeOfVariables k U V Φ L c) (_hp : p ≠ ⊤) :
    Wkp mu V p k →L[ℝ] Wkp mu U p k :=
  (compSmoothₗ h).extendOfNorm (smoothSubmodule mu V p k).subtype

private theorem compLFinite_apply_smooth (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤)
    (u : smoothSubmodule mu V p k) :
    compLFinite h hp (u : Wkp mu V p k) = compSmooth h u :=
  LinearMap.extendOfNorm_eq (denseRange_smoothSubmodule_subtype hp)
    ⟨compLBound p k L c, norm_compSmooth_le h⟩ u

private theorem valueL_comp_compLFinite (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤) :
    (valueL k).comp (compLFinite h hp) =
      (Lp.compOfMapLeSmul ℝ h.aemeasurable ENNReal.ofReal_ne_top h.map_restrict_le').comp
        (valueL (mu := mu) (Omega := V) (p := p) k) := by
  refine DFunLike.coe_injective (Continuous.ext_on (denseRange_smoothSubmodule_subtype hp)
    ((valueL k).comp (compLFinite h hp)).continuous
    ((Lp.compOfMapLeSmul ℝ h.aemeasurable ENNReal.ofReal_ne_top h.map_restrict_le').comp
      (valueL k)).continuous ?_)
  rintro _ ⟨u, rfl⟩
  refine Lp.ext ?_
  simp only [Submodule.coe_subtype, ContinuousLinearMap.coe_comp, Function.comp_apply,
    valueL_apply, compLFinite_apply_smooth h hp]
  exact (value_compSmooth_ae h u).trans
    (Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) h.aemeasurable ENNReal.ofReal_ne_top
      h.map_restrict_le' _).symm

private theorem value_compLFinite_ae (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p k) :
    (value k (compLFinite h hp u) : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) := by
  have he := congrArg (fun T => T u) (valueL_comp_compLFinite h hp)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, valueL_apply] at he
  rw [he]
  exact Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) h.aemeasurable ENNReal.ofReal_ne_top h.map_restrict_le' _

private theorem norm_compLFinite_le (h : IsChangeOfVariables k U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p k) :
    ‖compLFinite h hp u‖ ≤ compLBound p k L c * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_smoothSubmodule_subtype hp) _
    (norm_compSmooth_le h) u

private theorem norm_iteratedGradient_compLFinite_le
    (h : IsChangeOfVariables (k + 1) U V Φ L c) (hp : p ≠ ⊤) (u : Wkp mu V p (k + 1)) :
    ‖iteratedGradient k (compLFinite h hp u)‖ ≤
      max 1 L ^ (k + 1) * Fintype.card (OrderedFinpartition (k + 1)) *
        c⁻¹ ^ (1 / p).toReal * ‖u‖ := by
  let C := max 1 L ^ (k + 1) * Fintype.card (OrderedFinpartition (k + 1)) * c⁻¹ ^ (1 / p).toReal
  have hclosed : IsClosed {b : Wkp mu V p (k + 1) |
      ‖iteratedGradientL k (compLFinite h hp b)‖ ≤ C * ‖b‖} :=
    isClosed_le (((iteratedGradientL k).comp (compLFinite h hp)).continuous.norm)
      (continuous_const.mul continuous_norm)
  rw [← iteratedGradientL_apply]
  refine (denseRange_smoothSubmodule_subtype hp).induction_on u hclosed fun v => ?_
  simp only [Submodule.coe_subtype, compLFinite_apply_smooth h hp]
  rw [iteratedGradientL_apply]
  exact norm_iteratedGradient_compSmooth_le h v

/-! ### The endpoint `p = ∞` -/

/-- First-order precomposition at `p = ∞`, built directly from the weak chain rule
`TauCeti.HasWeakFDerivOn.comp_contDiffOn_diffeo`. -/
private theorem exists_comp_top_one (h : IsChangeOfVariables 1 U V Φ L c) (u : Wkp mu V ⊤ 1) :
    ∃ w : Wkp mu U ⊤ 1,
      (value 1 w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value 1 u (Φ x)) ∧
      ‖iteratedGradient 0 w‖ ≤ max 1 L * ‖u‖ ∧
      ‖w‖ ≤ compLBound ⊤ 1 L c * ‖u‖ := by
  set u₀ : Lp ℝ ⊤ (mu.restrict U) :=
    Lp.compOfMapLeSmul ℝ h.aemeasurable ENNReal.ofReal_ne_top h.map_restrict_le' (value 1 u)
  set g₀ : E → E := fun x => (fderiv ℝ Φ x).adjoint (iteratedGradient 0 u (Φ x))
  have hweak₀ : HasWeakFDerivOn mu U u₀ (fun x => innerSL ℝ (g₀ x)) := by
    have hc0 := (hasWeakFDerivOn_value u).comp_contDiffOn_diffeo h.contDiffOn h.injOn
      (fun x hx => abs_ne_zero.1 (h.pos.trans_le (h.le_abs_det x hx)).ne') h.mapsTo
    refine (hc0.congr_ae (Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) h.aemeasurable ENNReal.ofReal_ne_top
      h.map_restrict_le' (value 1 u)).symm).congr_ae_deriv (.of_forall fun x => ?_)
    ext v
    simp [g₀, ContinuousLinearMap.adjoint_inner_left]
  have hg₀_ae : ∀ᵐ x ∂mu.restrict U, ‖g₀ x‖ ≤ max 1 L * ‖u‖ := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet,
      h.ae_comp (Lp.ae_norm_le_norm_top (iteratedGradient 0 u))] with x hxU hgu
    calc ‖g₀ x‖ ≤ ‖(fderiv ℝ Φ x).adjoint‖ * ‖iteratedGradient 0 u (Φ x)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ Φ x‖ * ‖iteratedGradient 0 u (Φ x)‖ := by
          rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ max 1 L * ‖u‖ :=
          mul_le_mul ((h.norm_fderiv_le x hxU).trans (le_max_right 1 L))
            (hgu.trans (norm_iteratedGradient_le 0 u)) (norm_nonneg _) (max_one_pos L).le
  have hg₀_mem : MemLp g₀ ⊤ (mu.restrict U) :=
    memLp_top_of_bound hweak₀.locallyIntegrableOn_gradient.aestronglyMeasurable _ hg₀_ae
  set g : Lp E ⊤ (mu.restrict U) := hg₀_mem.toLp g₀
  have hweak : HasWeakFDerivOn mu U u₀ (fun x => innerSL ℝ (g x)) :=
    hweak₀.congr_ae_deriv (by filter_upwards [hg₀_mem.coeFn_toLp] with x hx; rw [hx])
  set w : Wkp mu U ⊤ 1 := W1p.mk u₀ g hweak
  have hgn : ‖g‖ ≤ max 1 L * ‖u‖ := Lp.norm_top_le_of_ae_bound
    (mul_nonneg (max_one_pos L).le (norm_nonneg u))
    (hg₀_mem.coeFn_toLp.mp (hg₀_ae.mono fun _ hx hxy => hxy ▸ hx))
  have hu₀n : ‖u₀‖ ≤ ‖u‖ :=
    (Lp.norm_compOfMapLeSmul_le (𝕜 := ℝ) h.aemeasurable ENNReal.ofReal_ne_top h.map_restrict_le'
      (value 1 u)).trans (by simpa using norm_value_le 1 u)
  have hval : value 1 w = u₀ := (value_one w).trans (W1p.value_mk u₀ g hweak)
  have hgrad : iteratedGradient 0 w = g :=
    (iteratedGradient_zero w).trans (W1p.gradient_mk u₀ g hweak)
  have hlow : lowerOrder 0 w = u₀ := (lowerOrder_zero w).trans (W1p.value_mk u₀ g hweak)
  refine ⟨w, hval ▸ Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) h.aemeasurable ENNReal.ofReal_ne_top
    h.map_restrict_le' (value 1 u), hgrad.symm ▸ hgn, ?_⟩
  have hsum : compLBound ⊤ 1 L c = 1 + max 1 L := by simp [compLBound_succ, Fintype.card_unique]
  have hle := norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 w
  rw [hlow, hgrad] at hle
  rw [hsum, add_mul, one_mul]
  linarith

/-- On finite-measure open sets `B` and `V'`, pulling back `u ∈ W^{m+2,∞}(V')` in `W^{m+2,q}` for
`1 ≤ q < ∞` produces a weak derivative of `iteratedGradient m w_B` bounded almost everywhere by
`max 1 L ^ (m + 2) · #{ordered partitions of m + 2} · ‖u‖`. -/
private theorem exists_local_deriv_comp_top {m : ℕ} {B V' : Opens E}
    [IsFiniteMeasure (mu.restrict (B : Set E))] [IsFiniteMeasure (mu.restrict (V' : Set E))]
    (h : IsChangeOfVariables (m + 2) B V' Φ L c) (u : Wkp mu V' ⊤ (m + 2))
    (w_B : Wkp mu B ⊤ (m + 1))
    (hw_B : (value (m + 1) w_B : E → ℝ) =ᵐ[mu.restrict B] fun y => value (m + 2) u (Φ y)) :
    ∃ D_B : E → IteratedGradient E (m + 1),
      HasWeakFDerivOn mu B (iteratedGradient m w_B) D_B ∧
      ∀ᵐ y ∂mu.restrict B, ‖D_B y‖ ≤
        max 1 L ^ (m + 2) * Fintype.card (OrderedFinpartition (m + 2)) * ‖u‖ := by
  set M : ℝ := max 1 L ^ (m + 2) * Fintype.card (OrderedFinpartition (m + 2))
  have hM : 0 ≤ M := max_one_pow_mul_card_nonneg L (m + 2)
  set v₁ : Wkp mu B 1 (m + 2) :=
    compLFinite h ENNReal.one_ne_top (ofExponentLEL le_top (m + 2) u)
  have hv₁_val : (value (m + 2) v₁ : E → ℝ) =ᵐ[mu.restrict B] fun y => value (m + 2) u (Φ y) :=
    (value_compLFinite_ae h ENNReal.one_ne_top _).trans
      (h.ae_comp (value_ofExponentLEL_ae le_top (m + 2) u))
  have hlow_eq : lowerOrder (m + 1) v₁ = ofExponentLEL le_top (m + 1) w_B :=
    ext (m + 1) (Lp.ext ((value_succ (m + 1) v₁ ▸ hv₁_val).trans
      (hw_B.symm.trans (value_ofExponentLEL_ae le_top (m + 1) w_B).symm)))
  have hweak : HasWeakFDerivOn mu B (iteratedGradient m w_B) (iteratedGradient (m + 1) v₁) :=
    (hasWeakFDerivOn_iteratedGradient m v₁).congr_ae
      (hlow_eq ▸ iteratedGradient_ofExponentLEL_ae le_top m w_B)
  refine ⟨iteratedGradient (m + 1) v₁, hweak, ?_⟩
  refine ae_norm_le_of_eventually_nnreal_eLpNorm_le (a := c⁻¹ * mu.real (V' : Set E))
    (mul_nonneg hM (norm_nonneg u)) (mul_nonneg (inv_nonneg.2 h.pos.le) measureReal_nonneg)
    ((eventually_ge_atTop (1 : NNReal)).mono fun q hq => ?_)
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  set v_q : Wkp mu B q (m + 2) :=
    compLFinite h ENNReal.coe_ne_top (ofExponentLEL le_top (m + 2) u)
  have hvq_eq : ofExponentLEL (p := 1) (by exact_mod_cast hq) (m + 2) v_q = v₁ :=
    ext (m + 2) (Lp.ext ((value_ofExponentLEL_ae _ (m + 2) v_q).trans
      (((value_compLFinite_ae h ENNReal.coe_ne_top _).trans
        (h.ae_comp (value_ofExponentLEL_ae le_top (m + 2) u))).trans hv₁_val.symm)))
  have hD_ae : (iteratedGradient (m + 1) v₁ : E → _) =ᵐ[mu.restrict B]
      iteratedGradient (m + 1) v_q :=
    hvq_eq ▸ iteratedGradient_ofExponentLEL_ae (p := 1) (by exact_mod_cast hq) (m + 1) v_q
  rw [eLpNorm_congr_ae hD_ae, ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), ← Lp.norm_def]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := norm_iteratedGradient_compLFinite_le h ENNReal.coe_ne_top
    (ofExponentLEL (p := q) le_top (m + 2) u)
  have h2 := norm_ofExponentLEL_apply_le (mu := mu) (Omega := V') (p := q) le_top (m + 2) u
  have hmu : (mu V' ^ (1 / (q : ℝ≥0∞).toReal - 1 / (⊤ : ℝ≥0∞).toReal)).toReal =
      mu.real (V' : Set E) ^ (1 / (q : ℝ)) := by
    simp [← ENNReal.toReal_rpow, measureReal_def]
  have hexp : (1 / (q : ℝ≥0∞)).toReal = 1 / (q : ℝ) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.coe_toReal]
  rw [hexp] at h1
  calc ‖iteratedGradient (m + 1) v_q‖
      ≤ M * c⁻¹ ^ (1 / (q : ℝ)) * (mu.real (V' : Set E) ^ (1 / (q : ℝ)) * ‖u‖) :=
        h1.trans (mul_le_mul_of_nonneg_left (hmu ▸ h2) (by have := h.pos; positivity))
    _ = M * ‖u‖ * (c⁻¹ * mu.real (V' : Set E)) ^ (1 / (q : ℝ)) := by
        rw [Real.mul_rpow (inv_nonneg.2 h.pos.le) measureReal_nonneg]
        ring

private theorem exists_ball_deriv_comp_top {m : ℕ} (h : IsChangeOfVariables (m + 2) U V Φ L c)
    (u : Wkp mu V ⊤ (m + 2)) (w₀ : Wkp mu U ⊤ (m + 1))
    (hw₀ : (value (m + 1) w₀ : E → ℝ) =ᵐ[mu.restrict U]
      fun x => value (m + 1) (lowerOrder (m + 1) u) (Φ x)) (x : U) :
    ∃ (B : Opens E) (D_B : E → IteratedGradient E (m + 1)),
      (x : E) ∈ B ∧ B ≤ U ∧ HasWeakFDerivOn mu B (iteratedGradient m w₀) D_B ∧
      ∀ᵐ y ∂mu.restrict B, ‖D_B y‖ ≤
        max 1 L ^ (m + 2) * Fintype.card (OrderedFinpartition (m + 2)) * ‖u‖ := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (U.isOpen.mem_nhds x.property)
  set B : Opens E := ⟨Metric.ball (x : E) r, Metric.isOpen_ball⟩
  have hBU : B ≤ U := Metric.ball_subset_closedBall.trans hrU
  have hK : IsCompact (Φ '' Metric.closedBall (x : E) r) :=
    (isCompact_closedBall (x : E) r).image_of_continuousOn
      (h.differentiableOn.continuousOn.mono hrU)
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hK V.isOpen
    ((Set.image_mono hrU).trans h.mapsTo.image_subset)
  set V' : Opens E := ⟨W, hWo⟩
  have hV'V : V' ≤ V := subset_closure.trans hWV
  have : IsFiniteMeasure (mu.restrict (B : Set E)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have : IsFiniteMeasure (mu.restrict (V' : Set E)) :=
    isFiniteMeasure_restrict.2 ((measure_mono subset_closure).trans_lt hWc.measure_lt_top).ne
  have hBV' : MapsTo Φ B V' := fun y hy => hKW ⟨y, Metric.ball_subset_closedBall hy, rfl⟩
  have hw_B : (value (m + 1) (restrictL hBU (m + 1) w₀) : E → ℝ) =ᵐ[mu.restrict B]
      fun y => value (m + 2) (restrictL hV'V (m + 2) u) (Φ y) := by
    filter_upwards [value_restrictL_ae hBU (m + 1) w₀,
      ae_restrict_of_ae_restrict_of_subset hBU hw₀,
      (h.mono_set hBU hBV').ae_comp (value_restrictL_ae hV'V (m + 2) u)] with y h1 h2 h3
    rw [h1, h2, h3, value_succ (m + 1) u]
  obtain ⟨D_B, hD_weak, hD_ae⟩ := exists_local_deriv_comp_top (h.mono_set hBU hBV')
    (restrictL hV'V (m + 2) u) (restrictL hBU (m + 1) w₀) hw_B
  refine ⟨B, D_B, Metric.mem_ball_self hr, hBU,
    hD_weak.congr_ae (iteratedGradient_restrictL_ae hBU m w₀), ?_⟩
  filter_upwards [hD_ae] with y hy
  exact hy.trans (mul_le_mul_of_nonneg_left (norm_restrictL_le hV'V (m + 2) u)
    (max_one_pow_mul_card_nonneg L (m + 2)))

/-- Inductive step at order `m + 2` and exponent `p = ∞`, gluing the local weak derivatives
produced by `exists_ball_deriv_comp_top` across an open cover by balls. -/
private theorem exists_comp_top_succ_succ {m : ℕ} (h : IsChangeOfVariables (m + 2) U V Φ L c)
    (u : Wkp mu V ⊤ (m + 2)) (w₀ : Wkp mu U ⊤ (m + 1))
    (hw₀ : (value (m + 1) w₀ : E → ℝ) =ᵐ[mu.restrict U]
      fun x => value (m + 1) (lowerOrder (m + 1) u) (Φ x))
    (hw₀_norm : ‖w₀‖ ≤ compLBound ⊤ (m + 1) L c * ‖lowerOrder (m + 1) u‖) :
    ∃ w : Wkp mu U ⊤ (m + 2),
      (value (m + 2) w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value (m + 2) u (Φ x)) ∧
      ‖iteratedGradient (m + 1) w‖ ≤
        max 1 L ^ (m + 2) * Fintype.card (OrderedFinpartition (m + 2)) * ‖u‖ ∧
      ‖w‖ ≤ compLBound ⊤ (m + 2) L c * ‖u‖ := by
  set M : ℝ := max 1 L ^ (m + 2) * Fintype.card (OrderedFinpartition (m + 2))
  have hM : 0 ≤ M := max_one_pow_mul_card_nonneg L (m + 2)
  choose B D_B hxB hBU hD_weak hD_ae using exists_ball_deriv_comp_top h u w₀ hw₀
  have hsup : (⨆ x : U, B x) = U := le_antisymm (iSup_le hBU) fun y hy =>
    Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxB ⟨y, hy⟩⟩
  obtain ⟨D_fun, hweak, hD_eq⟩ := exists_hasWeakFDerivOn_iSup B D_B hD_weak
  rw [hsup] at hweak
  have hD_bound : ∀ᵐ y ∂mu.restrict U, ‖D_fun y‖ ≤ M * ‖u‖ :=
    ae_restrict_of_subset_iUnion_isOpen (fun x => (B x).isOpen)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxB ⟨y, hy⟩⟩) fun x => by
        filter_upwards [hD_eq x, hD_ae x] with y hy1 hy2
        exact hy1 ▸ hy2
  have hD_mem : MemLp D_fun ⊤ (mu.restrict U) :=
    memLp_top_of_bound hweak.locallyIntegrableOn_deriv.aestronglyMeasurable _ hD_bound
  set D : Lp (IteratedGradient E (m + 1)) ⊤ (mu.restrict U) := hD_mem.toLp D_fun
  have hDn : ‖D‖ ≤ M * ‖u‖ := Lp.norm_top_le_of_ae_bound (mul_nonneg hM (norm_nonneg u))
    (hD_mem.coeFn_toLp.mp (hD_bound.mono fun _ hy hxy => hxy ▸ hy))
  set w : Wkp mu U ⊤ (m + 2) := mk m w₀ D (hweak.congr_ae_deriv hD_mem.coeFn_toLp.symm)
  refine ⟨w, by simpa only [w, value_mk, value_succ (m + 1) u] using hw₀,
    by simpa only [w, iteratedGradient_mk] using hDn, ?_⟩
  have hlow : ‖w₀‖ ≤ compLBound ⊤ (m + 1) L c * ‖u‖ :=
    hw₀_norm.trans (mul_le_mul_of_nonneg_left (norm_lowerOrder_le (m + 1) u)
      (compLBound_nonneg ⊤ (m + 1) L h.pos))
  have hcb : compLBound ⊤ (m + 2) L c = compLBound ⊤ (m + 1) L c + M := by simp [compLBound_succ, M]
  have hle := norm_le_norm_lowerOrder_add_norm_iteratedGradient (m + 1) w
  simp only [w, lowerOrder_mk, iteratedGradient_mk] at hle
  rw [hcb, add_mul]
  linarith

private theorem exists_comp_top :
    ∀ (k : ℕ) {U V : Opens E} {L c : ℝ}, IsChangeOfVariables k U V Φ L c →
      ∀ u : Wkp mu V ⊤ k,
      ∃ w : Wkp mu U ⊤ k,
        (value k w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value k u (Φ x)) ∧
        ‖w‖ ≤ compLBound ⊤ k L c * ‖u‖ ∧
        match k, w with
        | 0, _ => True
        | m + 1, w => ‖iteratedGradient m w‖ ≤
            max 1 L ^ (m + 1) * Fintype.card (OrderedFinpartition (m + 1)) * ‖u‖
  | 0, _, _, _, _, h, u =>
      ⟨Lp.compOfMapLeSmul ℝ h.aemeasurable ENNReal.ofReal_ne_top h.map_restrict_le' u,
        by
          rw [value_zero, value_zero]
          exact Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) h.aemeasurable ENNReal.ofReal_ne_top
            h.map_restrict_le' u,
        by simpa using Lp.norm_compOfMapLeSmul_le (𝕜 := ℝ) h.aemeasurable ENNReal.ofReal_ne_top
            h.map_restrict_le' u,
        trivial⟩
  | 1, _, _, _, _, h, u =>
      let ⟨w, hw, hg, hn⟩ := exists_comp_top_one h u
      ⟨w, hw, hn, by simpa [Fintype.card_unique] using hg⟩
  | m + 2, _, _, _, _, h, u => by
      obtain ⟨w₀, hw₀, hw₀n, -⟩ := exists_comp_top (m + 1) (h.mono (Nat.le_succ (m + 1)))
        (lowerOrder (m + 1) u)
      obtain ⟨w, hw, hg, hn⟩ := exists_comp_top_succ_succ h u w₀ hw₀ hw₀n
      exact ⟨w, hw, hn, hg⟩

private theorem exists_comp (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    ∃ w : Wkp mu U p k,
      (value k w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value k u (Φ x)) ∧
      ‖w‖ ≤ compLBound p k L c * ‖u‖ := by
  by_cases hp : p = ⊤
  · subst hp
    exact let ⟨w, hw, hn, _⟩ := exists_comp_top k h u; ⟨w, hw, hn⟩
  · exact ⟨compLFinite h hp u, value_compLFinite_ae h hp u, norm_compLFinite_le h hp u⟩

private def compFun (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) : Wkp mu U p k :=
  (exists_comp h u).choose

private theorem value_compFun_ae (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    (value k (compFun h u) : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) :=
  (exists_comp h u).choose_spec.1

private theorem value_compFun (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    value k (compFun h u) =
      Lp.compOfMapLeSmul ℝ h.aemeasurable ENNReal.ofReal_ne_top h.map_restrict_le' (value k u) :=
  Lp.ext ((value_compFun_ae h u).trans
    (Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) h.aemeasurable ENNReal.ofReal_ne_top h.map_restrict_le'
      (value k u)).symm)

private theorem norm_compFun_le (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    ‖compFun h u‖ ≤ compLBound p k L c * ‖u‖ :=
  (exists_comp h u).choose_spec.2

/-- **Change of variables in `W^{k,p}`.** If `Φ` is a change of variables of order `k` from `U`
into `V` (`TauCeti.Wkp.IsChangeOfVariables`) and `1 ≤ p ≤ ∞`, then precomposition with `Φ` is a
bounded linear operator `W^{k,p}(V) →L[ℝ] W^{k,p}(U)`. Its value is `u ∘ Φ`
(`TauCeti.Wkp.value_compL_ae`), which characterizes it (`TauCeti.Wkp.compL_eq_iff`). -/
def compL (h : IsChangeOfVariables k U V Φ L c) :
    Wkp mu V p k →L[ℝ] Wkp mu U p k :=
  LinearMap.mkContinuous
    { toFun := compFun h
      map_add' := fun u v => ext k (by simp only [value_add, value_compFun, map_add])
      map_smul' := fun a u => ext k (by
        simp only [value_smul, value_compFun, map_smul, RingHom.id_apply]) }
    (compLBound p k L c) (norm_compFun_le h)

/-- The value of `compL h u` is `u ∘ Φ`, almost everywhere on `U`. -/
theorem value_compL_ae (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    (value k (compL h u) : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) :=
  value_compFun_ae h u

/-- An element of `W^{k,p}(U)` is `compL h u` exactly when its value is `u ∘ Φ` almost everywhere
on `U`. -/
theorem compL_eq_iff (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k)
    (w : Wkp mu U p k) :
    compL h u = w ↔ (value k w : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) :=
  ⟨fun hw => hw ▸ value_compL_ae h u,
    fun hw => ext k (Lp.ext ((value_compL_ae h u).trans hw.symm))⟩

/-- `compL h` increases norms by at most the factor `compLBound p k L c`. -/
theorem norm_compL_le (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    ‖compL h u‖ ≤ compLBound p k L c * ‖u‖ :=
  norm_compFun_le h u

/-- `compL h` has operator norm at most `compLBound p k L c`. -/
theorem opNorm_compL_le (h : IsChangeOfVariables k U V Φ L c) :
    ‖(compL h : Wkp mu V p k →L[ℝ] Wkp mu U p k)‖ ≤ compLBound p k L c :=
  LinearMap.mkContinuous_norm_le _ (compLBound_nonneg p k L h.pos) (norm_compFun_le h)

/-- The `Lᵖ(U)` norm of the highest weak derivative of `compL h u` is bounded by
`max 1 L ^ (k + 1) · #{ordered partitions of k + 1} · c ^ (-1/p) · ‖u‖`, for every `1 ≤ p ≤ ∞`. -/
theorem norm_iteratedGradient_compL_le (h : IsChangeOfVariables (k + 1) U V Φ L c)
    (u : Wkp mu V p (k + 1)) :
    ‖iteratedGradient k (compL h u)‖ ≤
      max 1 L ^ (k + 1) * Fintype.card (OrderedFinpartition (k + 1)) *
        c⁻¹ ^ (1 / p).toReal * ‖u‖ := by
  by_cases hp : p = ⊤
  · subst hp
    obtain ⟨w, hw, -, hg⟩ := exists_comp_top (k + 1) h u
    rw [(compL_eq_iff h u w).2 hw]
    simpa using hg
  · rw [(compL_eq_iff h u _).2 (value_compLFinite_ae h hp u)]
    exact norm_iteratedGradient_compLFinite_le h hp u

end Extension

/-! ### Compatibility -/

section Compatibility

/-- Precomposition with the identity is the identity of `W^{k,p}(U)`. -/
@[simp]
theorem compL_id (h : IsChangeOfVariables k U U _root_.id L c) (u : Wkp mu U p k) :
    compL h u = u :=
  (compL_eq_iff h u u).2 Filter.EventuallyEq.rfl

/-- Precomposition commutes with forgetting the highest weak derivative.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem lowerOrder_compL (h : IsChangeOfVariables (k + 1) U V Φ L c)
    (u : Wkp mu V p (k + 1)) :
    lowerOrder k (compL h u) = compL (h.mono k.le_succ) (lowerOrder k u) := by
  refine ((compL_eq_iff _ _ _).2 ?_).symm
  filter_upwards [value_compL_ae h u] with x hx
  rw [← value_succ, hx, value_succ]

/-- The first-order change of variables `TauCeti.W1p.compL` along a change of variables `Φ` of
order at least one: precomposition with `Φ` as a bounded operator `W^{1,p}(V) →L[ℝ] W^{1,p}(U)`. -/
abbrev IsChangeOfVariables.w1pCompL (h : IsChangeOfVariables (k + 1) U V Φ L c) (hp : p ≠ ⊤) :
    W1p mu V p →L[ℝ] W1p mu U p :=
  W1p.compL Φ hp h.differentiableOn h.injOn h.mapsTo h.norm_fderiv_le h.pos h.le_abs_det

/-- The value of `h.w1pCompL hp u` is `u ∘ Φ`, almost everywhere on `U`. -/
theorem IsChangeOfVariables.value_w1pCompL_ae (h : IsChangeOfVariables (k + 1) U V Φ L c)
    (hp : p ≠ ⊤) (u : W1p mu V p) :
    W1p.value (h.w1pCompL hp u) =ᵐ[mu.restrict U] fun x => W1p.value u (Φ x) :=
  W1p.value_compL_ae Φ hp h.differentiableOn h.injOn h.mapsTo h.norm_fderiv_le h.pos
    h.le_abs_det u

/-- If a map `Ψ`, continuous on `V` and mapping `V` into `U`, is a left inverse of `Φ` on `U`,
then `h.w1pCompL hp` maps `W^{1,p}_0(V)` into `W^{1,p}_0(U)`. -/
theorem IsChangeOfVariables.w1pCompL_mem_w1p0Submodule_of_leftInvOn
    (h : IsChangeOfVariables (k + 1) U V Φ L c) (hp : p ≠ ⊤) (hΨ : ContinuousOn Ψ V)
    (hΨmaps : MapsTo Ψ V U) (hΨΦ : LeftInvOn Ψ Φ U) {u : W1p mu V p}
    (hu : u ∈ w1p0Submodule mu V p) :
    h.w1pCompL hp u ∈ w1p0Submodule mu U p :=
  W1p.compL_mem_w1p0Submodule_of_leftInvOn Φ hp h.differentiableOn h.injOn h.mapsTo
    h.norm_fderiv_le h.pos h.le_abs_det hΨ hΨmaps hΨΦ hu

/-- Precomposition commutes with restriction to open subdomains. -/
theorem restrictL_compL {U' V' : Opens E} (h : IsChangeOfVariables k U V Φ L c)
    (hU : U' ≤ U) (hV : V' ≤ V) (hUV : MapsTo Φ U' V') (u : Wkp mu V p k) :
    restrictL hU k (compL h u) = compL (h.mono_set hU hUV) (restrictL hV k u) := by
  refine ((compL_eq_iff _ _ _).2 ?_).symm
  filter_upwards [value_restrictL_ae hU k (compL h u),
    ae_restrict_of_ae_restrict_of_subset hU (value_compL_ae h u),
    (h.mono_set hU hUV).ae_comp (value_restrictL_ae hV k u)] with x h1 h2 h3
  rw [h1, h2, h3]

/-- Precomposition commutes with lowering the integrability exponent on finite-measure domains. -/
theorem ofExponentLEL_compL {q : ℝ≥0∞} [Fact (1 ≤ q)]
    [IsFiniteMeasure (mu.restrict (U : Set E))] [IsFiniteMeasure (mu.restrict (V : Set E))]
    (h : IsChangeOfVariables k U V Φ L c) (hpq : p ≤ q) (u : Wkp mu V q k) :
    ofExponentLEL hpq k (compL h u) = compL h (ofExponentLEL hpq k u) := by
  refine ((compL_eq_iff _ _ _).2 ?_).symm
  filter_upwards [value_ofExponentLEL_ae hpq k (compL h u), value_compL_ae h u,
    h.ae_comp (value_ofExponentLEL_ae hpq k u)] with x h1 h2 h3
  rw [h1, h2, h3]

/-- **First-order chain rule in `W^{k+1,p}` for `1 ≤ p ≤ ∞`.** The weak gradient of the
first-order part of `compL h u` is `DΦ(x)* (∇u(Φ x))` almost everywhere on `U`. -/
theorem gradient_firstOrder_compL_ae (h : IsChangeOfVariables (k + 1) U V Φ L c)
    (u : Wkp mu V p (k + 1)) :
    W1p.gradient (firstOrder k (compL h u)) =ᵐ[mu.restrict U]
      fun x => (fderiv ℝ Φ x).adjoint (W1p.gradient (firstOrder k u) (Φ x)) := by
  have hc1 : ContDiffOn ℝ 1 Φ U := h.contDiffOn.of_le (by exact_mod_cast Nat.le_add_left 1 k)
  have h1 := (W1p.hasWeakFDerivOn (firstOrder k u)).comp_contDiffOn_diffeo hc1 h.injOn
    (fun x hx => abs_ne_zero.1 (h.pos.trans_le (h.le_abs_det x hx)).ne') h.mapsTo
  have heq : (W1p.value (firstOrder k (compL h u)) : E → ℝ) =ᵐ[mu.restrict U]
      fun x => W1p.value (firstOrder k u) (Φ x) := by
    simp only [value_firstOrder]
    exact value_compL_ae h u
  have h2 := (W1p.hasWeakFDerivOn (firstOrder k (compL h u))).congr_ae heq
  filter_upwards [h2.ae_eq h1] with x hx
  refine ext_inner_right ℝ fun v => ?_
  have hxv := DFunLike.congr_fun hx v
  simpa only [innerSL_apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left] using hxv

/-- **The chain rule.** The first-order part of `compL h u` is the first-order change of
variables `TauCeti.W1p.compL` of the first-order part of `u`. In particular its weak gradient is
`DΦ(x)* (∇u)(Φ x)` (`TauCeti.Wkp.gradient_firstOrder_compL_ae`).
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem firstOrder_compL (h : IsChangeOfVariables (k + 1) U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p (k + 1)) :
    firstOrder k (compL h u) = h.w1pCompL hp (firstOrder k u) := by
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [value_compL_ae h u, h.value_w1pCompL_ae hp (firstOrder k u)] with x h1 h2
  rw [h2, value_firstOrder, value_firstOrder, h1]

/-- At almost every point, the weak gradient of `d ∈ W^{1,p}(V)` pairs with every direction `f`
as `⟪D²u f, c⟫` once it does so with the vectors of an orthonormal basis. -/
private theorem ae_forall_inner_gradient_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (u : Wkp mu V p 2) (c : E) (d : W1p mu V p)
    (hd : ∀ i, (fun y => ⟪W1p.gradient d y, b i⟫_ℝ) =ᵐ[mu.restrict V]
      fun y => ⟪iteratedGradient 1 u y (b i), c⟫_ℝ) :
    ∀ᵐ y ∂mu.restrict V, ∀ f : E,
      ⟪W1p.gradient d y, f⟫_ℝ = ⟪iteratedGradient 1 u y f, c⟫_ℝ := by
  filter_upwards [ae_all_iff.2 hd] with y hy f
  have hL : (innerSL ℝ (W1p.gradient d y) : E →L[ℝ] ℝ) =
      (innerSL ℝ c).comp (iteratedGradient 1 u y) :=
    ContinuousLinearMap.coe_injective (b.toBasis.ext fun i => by
      simpa [real_inner_comm c] using hy i)
  simpa [real_inner_comm c] using congrArg (fun T => T f) hL

/-- For `u ∈ W^{2,p}(V)` and a direction `c₀`, the function `⟪∇u(Φ ·), c₀⟫` lies in `W^{1,p}(U)`,
with weak gradient components `⟪D²u(Φ x) (DΦ(x) f), c₀⟫`. -/
private theorem exists_w1p_value_eq_inner_gradient_comp (h : IsChangeOfVariables 2 U V Φ L c)
    (hp : p ≠ ⊤) (u : Wkp mu V p 2) (c₀ : E) :
    ∃ w : W1p mu U p, ∀ᵐ x ∂mu.restrict U,
      W1p.value w x = ⟪iteratedGradient 0 (lowerOrder 1 u) (Φ x), c₀⟫_ℝ ∧ ∀ f : E,
        ⟪W1p.gradient w x, f⟫_ℝ = ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), c₀⟫_ℝ := by
  obtain ⟨d, hdv, hdg⟩ := exists_w1p_value_eq_inner_gradient u c₀
  have hdg' := ae_forall_inner_gradient_eq (stdOrthonormalBasis ℝ E) u c₀ d fun i => hdg _
  refine ⟨W1p.compL Φ hp h.differentiableOn h.injOn h.mapsTo h.norm_fderiv_le h.pos h.le_abs_det d,
    ?_⟩
  filter_upwards [W1p.value_compL_ae Φ hp h.differentiableOn h.injOn h.mapsTo h.norm_fderiv_le
    h.pos h.le_abs_det d, W1p.gradient_compL_ae Φ hp h.differentiableOn h.injOn h.mapsTo
    h.norm_fderiv_le h.pos h.le_abs_det d, h.ae_comp hdv, h.ae_comp hdg'] with x h1 h2 h3 h4
  refine ⟨h1.trans h3, fun f => ?_⟩
  rw [h2, ContinuousLinearMap.adjoint_inner_left, h4]

/-- Each component `⟪∇(u ∘ Φ), c₀⟫` of the weak gradient of `u ∘ Φ` is weakly differentiable in
every direction `f`, with derivative `⟪D²u(Φ x) (DΦ(x) f), DΦ(x) c₀⟫ + ⟪∇u(Φ x), D²Φ(x) f c₀⟫`. -/
private theorem hasWeakLineDerivOn_inner_gradient_firstOrder_compL
    (h : IsChangeOfVariables 2 U V Φ L c) (hp : p ≠ ⊤) (u : Wkp mu V p 2) (c₀ f : E) :
    HasWeakLineDerivOn mu U (fun x => ⟪W1p.gradient (firstOrder 1 (compL h u)) x, c₀⟫_ℝ)
      (fun x => ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x c₀⟫_ℝ +
        ⟪iteratedGradient 0 (lowerOrder 1 u) (Φ x), fderiv ℝ (fderiv ℝ Φ) x f c₀⟫_ℝ) f := by
  set b := stdOrthonormalBasis ℝ E
  set G := iteratedGradient 0 (lowerOrder 1 u)
  have hΦ1 : ContDiffOn ℝ 1 (fderiv ℝ Φ) U := h.contDiffOn_fderiv
  -- The weak gradient of `u ∘ Φ` is `DΦ(x)† ∇u(Φ x)`.
  have hgrad : ∀ᵐ x ∂mu.restrict U,
      W1p.gradient (firstOrder 1 (compL h u)) x = (fderiv ℝ Φ x).adjoint (G (Φ x)) := by
    filter_upwards [gradient_firstOrder_compL_ae h u] with x hx
    rw [hx, gradient_firstOrder_one]
  -- In the basis `(bᵢ)`, `⟪∇(u ∘ Φ), c₀⟫ = ∑ᵢ ⟪bᵢ, DΦ c₀⟫ wᵢ` with `wᵢ = ⟪∇u(Φ ·), bᵢ⟫` in
  -- `W^{1,p}(U)`, and the coefficients `⟪bᵢ, DΦ c₀⟫` are `C¹` on `U`.
  choose w hw using fun i => exists_w1p_value_eq_inner_gradient_comp h hp u (b i)
  have hψ (i : Fin _) : ContDiffOn ℝ 1 (fun x => ⟪b i, fderiv ℝ Φ x c₀⟫_ℝ) U :=
    contDiffOn_const.inner ℝ (hΦ1.clm_apply contDiffOn_const)
  have hψd (i : Fin _) : ∀ x ∈ (U : Set E),
      fderiv ℝ (fun x => ⟪b i, fderiv ℝ Φ x c₀⟫_ℝ) x f =
        ⟪b i, fderiv ℝ (fderiv ℝ Φ) x f c₀⟫_ℝ := fun x hx => by
    have hdx : DifferentiableAt ℝ (fderiv ℝ Φ) x :=
      (hΦ1.differentiableOn one_ne_zero x hx).differentiableAt (U.isOpen.mem_nhds hx)
    rw [((hasFDerivAt_const (b i) x).inner ℝ
      (hdx.hasFDerivAt.clm_apply (hasFDerivAt_const c₀ x))).fderiv]
    simp
  have hsum := HasWeakLineDerivOn.sum (μ := mu) (Ω := U) Finset.univ fun i _ =>
    (((W1p.hasWeakFDerivOn (w i)).hasWeakLineDerivOn f).contDiffOn_smul_of_ne_zero
      (hψ i) one_ne_zero)
  refine (hsum.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [hgrad, ae_all_iff.2 hw] with x h1 h2
    rw [h1, ContinuousLinearMap.adjoint_inner_left, ← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(h2 i).1, smul_eq_mul, mul_comm]
  · filter_upwards [ae_restrict_mem U.isOpen.measurableSet, ae_all_iff.2 hw] with x hx h2
    simp only [innerSL_apply_apply, smul_eq_mul, hψd _ x hx, (h2 _).1, (h2 _).2,
      Finset.sum_add_distrib]
    rw [← b.sum_inner_mul_inner (iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f)),
      ← b.sum_inner_mul_inner (G (Φ x))]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

/-- **The chain rule for the weak Hessian.** Let `Φ` be a change of variables of order two from `U`
into `V`, and `1 ≤ p < ∞`. For `u ∈ W^{2,p}(V)`, the weak Hessian of `u ∘ Φ ∈ W^{2,p}(U)` is

`⟪D²(u ∘ Φ)(x) f, g⟫ = ⟪D²u(Φ x) (DΦ(x) f), DΦ(x) g⟫ + ⟪∇u(Φ x), D²Φ(x) f g⟫`

for almost every `x ∈ U` and all directions `f` and `g`. Here `D²u` is the weak Hessian
`TauCeti.Wkp.iteratedGradient 1 u` and `∇u` the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`; `DΦ` and `D²Φ` are the classical
derivatives. For a linear `Φ` the last term vanishes
(`TauCeti.Wkp.exists_value_ae_eq_comp_continuousLinearEquiv`). -/
theorem inner_iteratedGradient_compL_ae (h : IsChangeOfVariables 2 U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p 2) :
    ∀ᵐ x ∂mu.restrict U, ∀ f g : E,
      ⟪iteratedGradient 1 (compL h u) x f, g⟫_ℝ =
        ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x g⟫_ℝ +
          ⟪iteratedGradient 0 (lowerOrder 1 u) (Φ x), fderiv ℝ (fderiv ℝ Φ) x f g⟫_ℝ := by
  set b := stdOrthonormalBasis ℝ E
  set G := iteratedGradient 0 (lowerOrder 1 u)
  -- Uniqueness of weak derivatives identifies the entries `⟪D²(u ∘ Φ) f, c₀⟫`.
  have hentry (c₀ f : E) : (fun x => ⟪iteratedGradient 1 (compL h u) x f, c₀⟫_ℝ)
      =ᵐ[mu.restrict U] fun x => ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x c₀⟫_ℝ +
        ⟪G (Φ x), fderiv ℝ (fderiv ℝ Φ) x f c₀⟫_ℝ := by
    have h' := ((hasWeakFDerivOn_iteratedGradient 0 (compL h u)).clm_comp
      (innerSL ℝ c₀)).hasWeakLineDerivOn f
    rw [← gradient_firstOrder_one] at h'
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm _ c₀] at h'
    exact h'.ae_eq (hasWeakLineDerivOn_inner_gradient_firstOrder_compL h hp u c₀ f)
  -- Both sides are bilinear in `(f, g)`, so they agree once they agree on a basis: the right side
  -- is `⟪N x f, g⟫` for the operator `N x` below.
  set N : E → E →L[ℝ] E := fun x => (fderiv ℝ Φ x).adjoint ∘L iteratedGradient 1 u (Φ x) ∘L
    fderiv ℝ Φ x + InnerProductSpace.continuousLinearMapOfBilin
      ((ContinuousLinearMap.compL ℝ E E ℝ (innerSL ℝ (G (Φ x)))) ∘L fderiv ℝ (fderiv ℝ Φ) x)
  have hN (x f g : E) : ⟪N x f, g⟫_ℝ =
      ⟪iteratedGradient 1 u (Φ x) (fderiv ℝ Φ x f), fderiv ℝ Φ x g⟫_ℝ +
        ⟪G (Φ x), fderiv ℝ (fderiv ℝ Φ) x f g⟫_ℝ := by
    simp [N, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
      InnerProductSpace.continuousLinearMapOfBilin_apply]
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hentry (b j) (b i)] with x hx f g
  have hxN : iteratedGradient 1 (compL h u) x = N x :=
    ContinuousLinearMap.coe_injective (b.toBasis.ext fun i =>
      InnerProductSpace.ext_inner_right_basis b.toBasis fun j => by simpa [hN] using hx i j)
  rw [hxN, hN]

/-- **Functoriality.** Precomposing with `Φ` and then with `Ψ` is precomposing with `Φ ∘ Ψ`. -/
theorem compL_comp (hΦ : IsChangeOfVariables k V W Φ L c)
    (hΨ : IsChangeOfVariables k U V Ψ L' c') {L'' c'' : ℝ}
    (hΦΨ : IsChangeOfVariables k U W (Φ ∘ Ψ) L'' c'') (u : Wkp mu W p k) :
    compL hΨ (compL hΦ u) = compL hΦΨ u := by
  refine (compL_eq_iff _ _ _).2 ?_
  filter_upwards [value_compL_ae hΦΨ u, hΨ.ae_comp (value_compL_ae hΦ u)] with x h1 h2
  rw [h1, h2, Function.comp_apply]

end Compatibility

/-! ### Diffeomorphism invariance -/

section Equiv

/-- If `Ψ` maps `V` back to `U` inverse to `Φ`, precomposing with `Φ` and then with `Ψ` is the
identity of `W^{k,p}(V)`. -/
theorem compL_compL_of_rightInvOn (hΦ : IsChangeOfVariables k U V Φ L c)
    (hΨ : IsChangeOfVariables k V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V)
    (u : Wkp mu V p k) :
    compL hΨ (compL hΦ u) = u := by
  refine (compL_eq_iff _ _ _).2 ?_
  filter_upwards [hΨ.ae_comp (value_compL_ae hΦ u), ae_restrict_mem V.isOpen.measurableSet]
    with y hy hyV
  rw [hy, hΦΨ hyV]

/-- **Diffeomorphism invariance of `W^{k,p}`.** If `Φ` is a change of variables of order `k` from
`U` into `V` and `Ψ` one from `V` into `U` with `Φ ∘ Ψ = id` on `V` and `Ψ ∘ Φ = id` on `U`, then
for `1 ≤ p ≤ ∞` precomposition with `Φ` is an isomorphism of Banach spaces
`W^{k,p}(V) ≃L[ℝ] W^{k,p}(U)`, with inverse precomposition with `Ψ`. -/
def compLEquiv (hΦ : IsChangeOfVariables k U V Φ L c) (hΨ : IsChangeOfVariables k V U Ψ L' c')
    (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U) :
    Wkp mu V p k ≃L[ℝ] Wkp mu U p k :=
  ContinuousLinearEquiv.ofContinuousLinearMap (compL hΦ) (compL hΨ)
    (ContinuousLinearMap.ext (compL_compL_of_rightInvOn hΨ hΦ hΨΦ))
    (ContinuousLinearMap.ext (compL_compL_of_rightInvOn hΦ hΨ hΦΨ))

@[simp]
theorem compLEquiv_apply (hΦ : IsChangeOfVariables k U V Φ L c)
    (hΨ : IsChangeOfVariables k V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) (u : Wkp mu V p k) :
    compLEquiv hΦ hΨ hΦΨ hΨΦ u = compL hΦ u :=
  (rfl)

@[simp]
theorem compLEquiv_symm_apply (hΦ : IsChangeOfVariables k U V Φ L c)
    (hΨ : IsChangeOfVariables k V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V)
    (hΨΦ : LeftInvOn Ψ Φ U) (u : Wkp mu U p k) :
    (compLEquiv hΦ hΨ hΦΨ hΨΦ).symm u = compL hΨ u :=
  (rfl)

end Equiv

/-! ### Local transfer along a change of variables -/

section Local

/-- **Local zero boundary values along a change of variables.** Let `Φ` be a change of variables
from `Ω'` into `Ω ∩ O` with a continuous inverse `Ψ`. If `χ u ∈ W₀^{1,p}(Ω)` for every smooth `χ`
compactly supported in `O`, then `ψ (u ∘ Φ) ∈ W₀^{1,p}(Ω')` for every smooth `ψ` compactly
supported in an open `U''` that `Φ` maps into `O`. -/
theorem IsChangeOfVariables.exists_w1p0_value_ae_eq_mul_value_w1pCompL {Omega O Ω' U'' : Opens E}
    (hΦ : IsChangeOfVariables 1 Ω' (Omega ⊓ O) Φ L c) (hp : p ≠ ⊤) (hΦc : ContinuousOn Φ U'')
    (hΨ : ContinuousOn Ψ (Omega ⊓ O : Opens E)) (hΨmaps : MapsTo Ψ (Omega ⊓ O : Opens E) Ω')
    (hΨΦ : LeftInvOn Ψ Φ Ω') (hΦU'' : MapsTo Φ U'' O) {u : W1p mu Omega p}
    (hu0 : ∀ χ : E → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      ∃ v : W1p0 mu Omega p,
        W1p.value (v : W1p mu Omega p) =ᵐ[mu.restrict Omega] fun x => χ x * W1p.value u x)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U'') :
    ∃ v : W1p0 mu Ω' p, W1p.value (v : W1p mu Ω' p) =ᵐ[mu.restrict Ω'] fun x => ψ x *
      W1p.value (hΦ.w1pCompL hp (W1p.restrictL inf_le_left u)) x := by
  -- A cutoff `χ`, compactly supported in `O`, equal to one on `Φ (tsupport ψ)`.
  have hK : IsCompact (Φ '' tsupport ψ) := hψc.isCompact.image_of_continuousOn (hΦc.mono hψs)
  obtain ⟨χ, -, hχ, -, hχ1, hχc, hχs, -, -, -⟩ :=
    hK.exists_contDiff_cutoff_with_bounds O.isOpen (hΦU''.mono_left hψs).image_subset
  -- `χ u ∈ W₀^{1,p}(Ω)` restricts to `W₀^{1,p}(Ω ∩ O)` and pulls back to `W₀^{1,p}(Ω')`.
  obtain ⟨v, hv⟩ := W1p.exists_w1p0_value_ae_eq_mul_restrictL subset_rfl hu0 hχ hχc hχs
  have hvΩ' := hΦ.w1pCompL_mem_w1p0Submodule_of_leftInvOn hp hΨ hΨmaps hΨΦ v.property
  obtain ⟨w, hw⟩ := W1p.exists_w1p0_value_ae_eq_mul_of_mem_w1p0Submodule hψ hψc hvΩ'
  refine ⟨w, ?_⟩
  filter_upwards [hw, hΦ.value_w1pCompL_ae hp (v : W1p mu (Omega ⊓ O) p),
    hΦ.value_w1pCompL_ae hp (W1p.restrictL inf_le_left u), hΦ.ae_comp hv] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  by_cases hx : x ∈ tsupport ψ
  · rw [interior_subset (hχ1 ⟨x, hx, rfl⟩), one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

/-- **Pushing `W^{2,p}` forward along a change of variables.** Let `Φ` be a change of variables
from `Ω'` into `D ⊆ Ω`, and `Ψ` one of order two from `Ω ∩ V ⊆ D` into `Ω' ∩ V''` with
`Φ ∘ Ψ = id` on `Ω ∩ V`. If `u ∘ Φ` is `W^{2,p}` on `Ω' ∩ V''`, then `u` is `W^{2,p}` on
`Ω ∩ V`. -/
theorem exists_lowerOrder_eq_restrictL_of_w1pCompL {Omega D V Ω' V'' : Opens E} (hp : p ≠ ⊤)
    (hD : D ≤ Omega) (hVD : Omega ⊓ V ≤ D) (hΦ : IsChangeOfVariables 1 Ω' D Φ L c)
    (hΨ : IsChangeOfVariables 2 (Omega ⊓ V) (Ω' ⊓ V'') Ψ L' c')
    (hΦΨ : RightInvOn Ψ Φ (Omega ⊓ V : Opens E)) {u : W1p mu Omega p}
    {w : Wkp mu (Ω' ⊓ V'') p 2}
    (hw : lowerOrder 1 w = W1p.restrictL inf_le_left (hΦ.w1pCompL hp (W1p.restrictL hD u))) :
    ∃ w' : Wkp mu (Omega ⊓ V) p 2, lowerOrder 1 w' = W1p.restrictL inf_le_left u := by
  refine ⟨compL hΨ w, ?_⟩
  rw [← firstOrder_one, firstOrder_compL (k := 1) hΨ hp, firstOrder_one, hw]
  refine W1p.ext_value (Lp.ext ?_)
  have hΩ'V : ((Ω' ⊓ V'' : Opens E) : Set E) ⊆ Ω' := fun x hx => hx.1
  filter_upwards [hΨ.value_w1pCompL_ae (mu := mu) hp _,
    hΨ.ae_comp (W1p.value_restrictL_ae (mu := mu) (p := p) inf_le_left _),
    hΨ.ae_comp (ae_restrict_of_ae_restrict_of_subset hΩ'V
      (hΦ.value_w1pCompL_ae hp (W1p.restrictL hD u))),
    ae_restrict_of_ae_restrict_of_subset hVD (W1p.value_restrictL_ae hD u),
    W1p.value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u,
    ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x h1 h2 h3 h4 h5 hx
  rw [h1, h2, h3, hΦΨ hx, h4, h5]

end Local

/-! ### Left-invertible `Cᵏ` maps and uniform norm bounds -/

section LeftInvOn

private theorem map_restrict_le_of_leftInvOn (hΦ : ContinuousOn Φ U)
    (hΨ : DifferentiableOn ℝ Ψ V) (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') :
    (mu.restrict U).map Φ ≤ ENNReal.ofReal (max 1 L' ^ Module.finrank ℝ E) • mu.restrict V :=
  map_restrict_le_smul_restrict_of_leftInvOn_of_norm_fderiv_le mu
    (hΦ.aemeasurable U.isOpen.measurableSet) V.isOpen hΨ hmaps hΨΦ fun x hx =>
      (hL' x hx).trans (le_max_right 1 L')

/-- **Precomposition with a left-invertible `Cᵏ` map.** For any order `k : ℕ` and exponent
`1 ≤ p ≤ ∞`, if `Φ` is `Cᵏ` on `U` mapping `U` into `V` with derivatives of orders `1` through
`k` bounded by `L` on `U`, and `Ψ` is differentiable on `V` with `Ψ (Φ x) = x` and
`‖fderiv ℝ Ψ (Φ x)‖ ≤ L'` on `U`, then precomposition with `Φ` is a bounded linear operator
`W^{k,p}(V) →L[ℝ] W^{k,p}(U)`. At `k = 0` no differentiability of `Φ` is assumed (`C⁰` is
continuity on `U`), while for `k ≥ 1` it agrees with `compL` (`compOfLeftInvOnL_eq_compL`). -/
def compOfLeftInvOnL : ∀ {k : ℕ}, ContDiffOn ℝ k Φ U → DifferentiableOn ℝ Ψ V →
    MapsTo Φ U V → LeftInvOn Ψ Φ U →
    (∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) →
    (∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') → Wkp mu V p k →L[ℝ] Wkp mu U p k
  | 0, hΦ, hΨ, hmaps, hΨΦ, _, hL' =>
      Lp.compOfMapLeSmul ℝ (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
        ENNReal.ofReal_ne_top (map_restrict_le_of_leftInvOn hΦ.continuousOn hΨ hmaps hΨΦ hL')
  | k + 1, hΦ, hΨ, hmaps, hΨΦ, hL, hL' =>
      compL (IsChangeOfVariables.of_leftInvOn k.succ_pos hΦ hΨ hmaps hΨΦ hL hL')

/-- For `k ≥ 1`, `compOfLeftInvOnL` agrees with `compL` applied to
`IsChangeOfVariables.of_leftInvOn`. -/
theorem compOfLeftInvOnL_eq_compL (hk : 1 ≤ k) (hΦ : ContDiffOn ℝ k Φ U)
    (hΨ : DifferentiableOn ℝ Ψ V) (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') :
    compOfLeftInvOnL (mu := mu) (p := p) hΦ hΨ hmaps hΨΦ hL hL' =
      compL (IsChangeOfVariables.of_leftInvOn hk hΦ hΨ hmaps hΨΦ hL hL') := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk; rfl

/-- The value of `compOfLeftInvOnL` is `u ∘ Φ` almost everywhere on `U`. -/
theorem value_compOfLeftInvOnL_ae (hΦ : ContDiffOn ℝ k Φ U) (hΨ : DifferentiableOn ℝ Ψ V)
    (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') (u : Wkp mu V p k) :
    (value k (compOfLeftInvOnL hΦ hΨ hmaps hΨΦ hL hL' u) : E → ℝ) =ᵐ[mu.restrict U]
      fun x => value k u (Φ x) := by
  cases k with
  | zero =>
      rw [compOfLeftInvOnL, value_zero, value_zero]
      exact Lp.coeFn_compOfMapLeSmul (𝕜 := ℝ) (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet)
        ENNReal.ofReal_ne_top (map_restrict_le_of_leftInvOn hΦ.continuousOn hΨ hmaps hΨΦ hL') u
  | succ m =>
      exact value_compL_ae (IsChangeOfVariables.of_leftInvOn m.succ_pos hΦ hΨ hmaps hΨΦ hL hL') u

/-- An element of `W^{k,p}(U)` is `compOfLeftInvOnL ... u` if and only if its value agrees with
`u ∘ Φ` almost everywhere on `U`. -/
theorem compOfLeftInvOnL_eq_iff (hΦ : ContDiffOn ℝ k Φ U) (hΨ : DifferentiableOn ℝ Ψ V)
    (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') (u : Wkp mu V p k) (w : Wkp mu U p k) :
    compOfLeftInvOnL hΦ hΨ hmaps hΨΦ hL hL' u = w ↔
      (value k w : E → ℝ) =ᵐ[mu.restrict U] fun x => value k u (Φ x) :=
  ⟨fun hw => hw ▸ value_compOfLeftInvOnL_ae hΦ hΨ hmaps hΨΦ hL hL' u,
    fun hw => ext k (Lp.ext ((value_compOfLeftInvOnL_ae hΦ hΨ hmaps hΨΦ hL hL' u).trans hw.symm))⟩

/-- `compOfLeftInvOnL` increases norms by at most
`compLBound p k L (max 1 L' ^ finrank ℝ E)⁻¹`. -/
theorem norm_compOfLeftInvOnL_le (hΦ : ContDiffOn ℝ k Φ U) (hΨ : DifferentiableOn ℝ Ψ V)
    (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') (u : Wkp mu V p k) :
    ‖compOfLeftInvOnL hΦ hΨ hmaps hΨΦ hL hL' u‖ ≤
      compLBound p k L (max 1 L' ^ Module.finrank ℝ E)⁻¹ * ‖u‖ := by
  cases k with
  | zero =>
      have h := Lp.norm_compOfMapLeSmul_le (𝕜 := ℝ)
        (hΦ.continuousOn.aemeasurable U.isOpen.measurableSet) ENNReal.ofReal_ne_top
        (map_restrict_le_of_leftInvOn hΦ.continuousOn hΨ hmaps hΨΦ hL') u
      rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (pow_nonneg (max_one_pos L').le _)] at h
      simpa [compOfLeftInvOnL] using h
  | succ m =>
      exact norm_compL_le (IsChangeOfVariables.of_leftInvOn m.succ_pos hΦ hΨ hmaps hΨΦ hL hL') u

/-- The operator norm of `compOfLeftInvOnL` is bounded by
`compLBound p k L (max 1 L' ^ finrank ℝ E)⁻¹`. -/
theorem opNorm_compOfLeftInvOnL_le (hΦ : ContDiffOn ℝ k Φ U) (hΨ : DifferentiableOn ℝ Ψ V)
    (hmaps : MapsTo Φ U V) (hΨΦ : LeftInvOn Ψ Φ U)
    (hL : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L)
    (hL' : ∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') :
    ‖compOfLeftInvOnL (mu := mu) (p := p) hΦ hΨ hmaps hΨΦ hL hL'‖ ≤
      compLBound p k L (max 1 L' ^ Module.finrank ℝ E)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _
    (compLBound_nonneg p k L (inv_max_one_pow_pos L' _))
    (norm_compOfLeftInvOnL_le hΦ hΨ hmaps hΨΦ hL hL')

end LeftInvOn

end Calculus

/-- **Uniform `W^{k,p}` precomposition bound for left-invertible `Cᵏ` maps.** For a
finite-dimensional real inner product space `E`, order `k`, and derivative bounds `L` and `L'`,
there is a constant `C > 0` (depending only on `E`, `k`, `L`, and `L'`; see
`TauCeti.Wkp.norm_compOfLeftInvOnL_le` and `TauCeti.Wkp.compLBound_le_compLBound_one` for the
explicit bound `compLBound 1 k L (max 1 L' ^ finrank ℝ E)⁻¹` depending on `E` only through
`Module.finrank ℝ E`) such that for every additive Haar measure `mu`, every exponent `1 ≤ p ≤ ∞`,
open sets `U, V ⊆ E`, `Cᵏ` map `Φ : E → E` on `U` mapping `U` into `V` with derivatives of orders
`1` through `k` bounded by `L` on `U`, and differentiable left inverse `Ψ` on `V` satisfying
`‖fderiv ℝ Ψ (Φ x)‖ ≤ L'` on `U`, precomposition with `Φ` carries each `u ∈ W^{k,p}(V)` to an
element `w ∈ W^{k,p}(U)` of norm at most `C * ‖u‖` whose value agrees with `u ∘ Φ` almost
everywhere on `U`. -/
theorem exists_norm_comp_le (E : Type*) [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] (k : ℕ) (L L' : ℝ) :
    ∃ C > 0, ∀ (mu : Measure E) [mu.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)]
      {U V : Opens E} {Φ Ψ : E → E},
      ContDiffOn ℝ k Φ U → DifferentiableOn ℝ Ψ V → MapsTo Φ U V → LeftInvOn Ψ Φ U →
      (∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set E), ‖iteratedFDeriv ℝ i Φ x‖ ≤ L) →
      (∀ x ∈ (U : Set E), ‖fderiv ℝ Ψ (Φ x)‖ ≤ L') →
      ∀ u : Wkp mu V p k, ∃ w : Wkp mu U p k,
        (value k w : E → ℝ) =ᵐ[mu.restrict U] (fun x => value k u (Φ x)) ∧ ‖w‖ ≤ C * ‖u‖ := by
  set c : ℝ := (max 1 L' ^ Module.finrank ℝ E)⁻¹
  have hc0 : 0 < c := inv_max_one_pow_pos L' _
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (le_max_left 1 L'))
  refine ⟨compLBound 1 k L c, compLBound_pos 1 k L hc0,
    fun mu _ p _ {U V Φ Ψ} hΦ hΨ hmaps hΨΦ hL hL' u =>
      ⟨compOfLeftInvOnL hΦ hΨ hmaps hΨΦ hL hL' u,
        value_compOfLeftInvOnL_ae hΦ hΨ hmaps hΨΦ hL hL' u,
        (norm_compOfLeftInvOnL_le hΦ hΨ hmaps hΨΦ hL hL' u).trans
          (mul_le_mul_of_nonneg_right (compLBound_le_compLBound_one Fact.out k L hc0 hc1)
            (norm_nonneg u))⟩⟩

end TauCeti.Wkp
