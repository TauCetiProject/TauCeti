/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.ConstantCoefficient.CauchyProblem
public import TauCeti.Analysis.PDE.Parabolic.Holder.Cutoff
public import TauCeti.Analysis.PDE.Parabolic.Holder.Freezing
public import TauCeti.Analysis.PDE.Parabolic.Holder.Localization
public import TauCeti.Analysis.PDE.Parabolic.Holder.Patching

/-!
# Schauder estimates for parabolic operators with variable coefficients

Let `0 < α < 1` and let `P u = ∂ₜu - A·D_x²u - B·D_xu - C·u` be a parabolic operator whose
coefficient fields `A`, `B`, `C` lie in the bounded parabolic Hölder space `C_b^{α,α/2}` on a slab
`E × [t₀, t₁]`. This file proves the global **Schauder estimate** for `P` in the order-two space
`C_b^{2+α,1+α/2}` (`TauCeti.ParabolicC2HolderSpace`): the norm of `u` is controlled by `P u` and the
initial trace `u(·, t₀)`.

On `ℝⁿ × [0, T]` with scalar coefficients `aⁱʲ`, `bⁱ`, `c` with `λ ‖ξ‖² ≤ aⁱʲ ξᵢ ξⱼ` and Hölder
norms at most `K`,

`‖u‖_{2+α,par} ≤ C (‖P u‖_{α,par} + ‖u(·, 0)‖_{2,α})`

with `C` depending only on `α`, `λ`, `K`, the dimension and `T`
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`). Neither symmetry of
`a` nor a sign of `c` is assumed. Since `P` depends continuously on its coefficients, this estimate,
uniform along the segment from the heat operator to `P`, is the input of the method of continuity
(`IsPreconnected.surjective_iff_of_forall_norm_le`) that solves `P u = f`, `u(·, 0) = g`.

## The argument

The proof perturbs the constant-coefficient estimate
(`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL_const`). Fix a small
radius `r` and, for every point `p` of the slab, a cutoff `χ_p` equal to one on the parabolic ball
of radius `r / 4` about `p` and vanishing at distance `r` from it
(`TauCeti.ParabolicC2HolderSpace.exists_cutoff_family`). For `u` with vanishing initial trace the
localization `χ_p u` also has vanishing initial trace, and with the second-order coefficient frozen
at `p`,

`∂ₜ(χ_p u) - A(p)·D_x²(χ_p u) = P(χ_p u) + (A - A(p))·D_x²(χ_p u) + B·D_x(χ_p u) + C·(χ_p u)`

(`TauCeti.ParabolicC2HolderSpace.parabolicOperatorL_const_eq`). The three terms on the right are
estimated by

* the localization error `P(χ_p u) - χ_p P u`, of lower order in `u`
  (`exists_norm_parabolicOperatorL_mul_sub_mul_parabolicOperatorL_le`);
* the freezing error, small because `A` oscillates little on the support of `χ_p`
  (`TauCeti.ParabolicC2HolderSpace.exists_norm_spatialOperatorL_sub_const_apply_le`);
* interpolation for the lower-order terms
  (`exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le`).

Each is at most `η ‖·‖ + K_η ‖u‖_∞` for every `η > 0`, so the frozen estimate gives a bound on
`‖χ_p u‖` uniform in `p`, up to a small multiple of `‖u‖`. Patching these local bounds
(`TauCeti.ParabolicC2HolderSpace.norm_le_of_forall_eqOn_ball`) and absorbing gives
`‖u‖ ≤ C (‖P u‖ + ‖u‖_∞)` (`exists_norm_le_parabolicOperatorL_of_spatialTrace_eq_zero`).
A nonzero initial trace `g` is removed by subtracting a lift of `g`, the Cauchy heat potential on
`ℝⁿ` (`TauCeti.ParabolicC2HolderSpace.exists_norm_le_parabolicOperatorL`), and the supremum norm by
the maximum principle,
`‖u‖_∞ ≤ exp (K T) (‖u(·, 0)‖_∞ + T ‖P u‖_∞)`
(`abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le`, all in the namespace
`TauCeti.ParabolicC2HolderSpace`).

The general statements take the frozen-coefficient estimate as a hypothesis, so they apply on every
finite-dimensional space `E` and with any constant-coefficient theory supplying it.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.exists_norm_le_parabolicOperatorL_of_spatialTrace_eq_zero`: the
  estimate `‖u‖ ≤ C (‖P u‖ + ‖u‖_∞)` for vanishing initial trace, from frozen-coefficient estimates,
  with a constant uniform over slabs.
* `TauCeti.ParabolicC2HolderSpace.exists_norm_le_parabolicOperatorL`: the same with the initial
  trace, `‖u‖ ≤ C (‖P u‖ + ‖u(·, t₀)‖ + ‖u‖_∞)`, given a bounded lift of initial data.
* `TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL_add_norm_valueL`: the
  estimate on `ℝⁿ × [0, T]` for scalar coefficients, up to the supremum norm.
* `TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL`: the global Schauder
  estimate `‖u‖ ≤ C (‖P u‖ + ‖u(·, 0)‖)`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (the same localization argument for elliptic operators).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set Metric ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {t₀ t₁ : ℝ}
  {ht : t₀ < t₁}

/-- A local shortcut for bounded gradient fields, as in the file defining the order-two space. -/
local instance {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (slab (E := E) t₀ t₁ →ᵇ (E →L[ℝ] F)) := inferInstance
/-- A local shortcut for scalar operations on bounded gradient fields. -/
local instance {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (slab (E := E) t₀ t₁ →ᵇ (E →L[ℝ] F)) := inferInstance

/-! ### The estimate for general coefficient fields -/

section General

-- Reuse the operator module's Hessian shortcuts, as `Localization` does, so that the coefficient
-- fields have the instance terms the freezing and localization estimates are stated with.
attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

/-! ### Norm bounds through the four fields

Outside the file defining it, the order-two space is irreducible, and the generic triangle
inequality and operator-norm bound, whose instance arguments unfold to its definition, do not
elaborate for it. The bounds needed here are proved through the four fields of the norm
(`TauCeti.ParabolicC2HolderSpace.norm_eq`), which are continuous linear maps into spaces where
the generic lemmas apply. -/

section Fields

variable {F X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup X]
  [NormedSpace ℝ X]

/-- The triangle inequality `‖u‖ ≤ ‖u - v‖ + ‖v‖` in `C_b^{2+α,1+α/2}`. -/
private theorem norm_le_norm_sub_add_norm (u v : ParabolicC2HolderSpace α E F ht) :
    ‖u‖ ≤ ‖u - v‖ + ‖v‖ := by
  rw [norm_eq u, norm_eq (u - v), norm_eq v, map_sub, map_sub, map_sub, map_sub]
  linarith [norm_le_insert' (valueL u) (valueL v),
    norm_le_insert' (spatialFDerivL u) (spatialFDerivL v),
    norm_le_insert' (spatialSecondFDerivL u) (spatialSecondFDerivL v),
    norm_le_insert' (timeDerivL u) (timeDerivL v)]

/-- A continuous linear map `H` into `C_b^{2+α,1+α/2}` is bounded: `‖H g‖ ≤ N ‖g‖`. -/
private theorem exists_norm_apply_le_mul (H : X →L[ℝ] ParabolicC2HolderSpace α E F ht) :
    ∃ N, 0 ≤ N ∧ ∀ g, ‖H g‖ ≤ N * ‖g‖ := by
  refine ⟨‖valueL ∘L H‖ + ‖spatialFDerivL ∘L H‖ +
    (‖spatialSecondFDerivL ∘L H‖ + ‖timeDerivL ∘L H‖), by positivity, fun g ↦ ?_⟩
  rw [norm_eq (H g)]
  have h1 := (valueL ∘L H).le_opNorm g
  have h2 := (spatialFDerivL ∘L H).le_opNorm g
  have h3 := (spatialSecondFDerivL ∘L H).le_opNorm g
  have h4 := (timeDerivL ∘L H).le_opNorm g
  simp only [ContinuousLinearMap.comp_apply] at h1 h2 h3 h4
  linarith

end Fields

/-- **Freezing the second-order coefficient.** The operator with the constant coefficient `A(p)`
and no lower-order terms is `P` plus the freezing error `(A - A(p))·D_x²` and the lower-order part
`B·D_x + C` of `P`. -/
theorem parabolicOperatorL_const_eq (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := E) t₀ t₁) (ℝ →L[ℝ] ℝ)) (p : slab (E := E) t₀ t₁)
    (u : ParabolicC2HolderSpace α E ℝ ht) :
    parabolicOperatorL hα (HolderSpace.const (A p)) 0 0 u =
      parabolicOperatorL hα A B C u + spatialOperatorL hα (A - HolderSpace.const (A p)) 0 0 u +
        spatialOperatorL hα 0 B C u := by
  ext q
  simp only [parabolicOperatorL_apply, spatialOperatorL_apply, HolderSpace.add_apply,
    HolderSpace.sub_apply, HolderSpace.const_apply, HolderSpace.zero_apply,
    _root_.sub_apply, _root_.zero_apply]
  abel

/-- The cutoff-dependent quantity in the localization error bound, for a cutoff of norm at most
`M` and coefficients `‖A‖ ≤ KA`, `‖B‖ ≤ KB`. -/
private theorem localization_bound_le {M KA KB : ℝ}
    {A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] ℝ) →L[ℝ] ℝ)} (hA : ‖A‖ ≤ KA)
    (hB : ‖B‖ ≤ KB) (hα : α ≤ 1) {χ : ParabolicC2HolderSpace α E ℝ ht} (hχ : ‖χ‖ ≤ M) :
    ‖timeDerivL χ‖ + ‖A‖ * ‖spatialSecondFDerivL χ‖ +
      (‖B‖ + 2 * ‖A‖) * ‖spatialFDerivHolderL hα χ‖ ≤ M + KA * M + (KB + 2 * KA) * (24 * M) := by
  have h1 := (norm_timeDerivL_le χ).trans hχ
  have h2 := (norm_spatialSecondFDerivL_le χ).trans hχ
  have h3 : ‖spatialFDerivHolderL hα χ‖ ≤ 24 * M := by
    linarith [norm_valueHolderL_add_norm_spatialFDerivHolderL_le_mul hα χ,
      norm_nonneg (valueHolderL hα χ)]
  have hKA : 0 ≤ KA := (norm_nonneg A).trans hA
  have hKB : 0 ≤ KB := (norm_nonneg B).trans hB
  gcongr

/-- **The estimate of one localization.** Let `χ` be a cutoff with values in `[0, 1]` vanishing at
parabolic distance `r` from `p`, and let `u` have vanishing initial trace. If the operator with the
coefficient frozen at `p` satisfies the estimate with constant `S`, then the localization error
(`hloc`), the freezing error (`hfreeze`) and the lower-order terms (`hint`) are absorbed, and
`‖χ u‖ ≤ 2 S (24 M ‖P u‖ + η₁ ‖u‖ + (K₁ + C₂ + KB K₃) ‖u‖_∞)` for `‖χ‖ ≤ M`. -/
private theorem norm_mul_le_of_norm_le_parabolicOperatorL_const (hα : α ≤ 1)
    {S KB η₁ η₂ η₃ K₁ C₂ K₃ r : ℝ} (hS : 0 ≤ S) (hKB : 0 ≤ KB) (hC₂ : 0 ≤ C₂) (hK₃ : 0 ≤ K₃)
    (hη : S * η₂ + S * (KB * η₃) ≤ 1 / 2)
    {A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {Cc : HolderSpace α (slab (E := E) t₀ t₁) (ℝ →L[ℝ] ℝ)} (hB : ‖B‖ ≤ KB) (hCc : ‖Cc‖ ≤ KB)
    {p : slab (E := E) t₀ t₁}
    (hfrozen : ∀ w : ParabolicC2HolderSpace α E ℝ ht,
      w.spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩ = 0 →
        ‖w‖ ≤ S * ‖parabolicOperatorL hα (HolderSpace.const (A p)) 0 0 w‖)
    (hfreeze : ∀ w : ParabolicC2HolderSpace α E ℝ ht,
      (∀ q, r < dist q p → spatialSecondFDerivL w q = 0) →
        ‖spatialOperatorL hα (A - HolderSpace.const (A p)) 0 0 w‖ ≤
          η₂ * ‖w‖ + C₂ * ‖valueL w‖)
    (hint : ∀ w : ParabolicC2HolderSpace α E ℝ ht,
      ‖valueHolderL hα w‖ + ‖spatialFDerivHolderL hα w‖ ≤ η₃ * ‖w‖ + K₃ * ‖valueL w‖)
    {M : ℝ} {χ : ParabolicC2HolderSpace α E ℝ ht} (hχn : ‖χ‖ ≤ M) (hχmem : ∀ q, χ q ∈ Icc 0 1)
    (hχzero : ∀ q, r ≤ dist q p → χ q = 0) {u : ParabolicC2HolderSpace α E ℝ ht}
    (hloc : ‖parabolicOperatorL hα A B Cc
        ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u) -
      (ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (valueHolderL hα χ)
        (parabolicOperatorL hα A B Cc u)‖ ≤ η₁ * ‖u‖ + K₁ * ‖valueL u‖)
    (hu : u.spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩ = 0) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u‖ ≤
      2 * (S * (24 * M * ‖parabolicOperatorL hα A B Cc u‖ + η₁ * ‖u‖ +
        (K₁ + C₂ + KB * K₃) * ‖valueL u‖)) := by
  have hvu := norm_valueL_mul_le hα hχmem u
  have h0 := hfrozen _ (spatialTrace_mul_eq_zero hα (χ := χ) hu)
  rw [parabolicOperatorL_const_eq hα A B Cc] at h0
  have hPv := (norm_parabolicOperatorL_mul_le hα A B Cc χ u).trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hχn (by norm_num)) (norm_nonneg _))
    hloc)
  have hzero : ∀ q, r < dist q p → spatialSecondFDerivL
      ((ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u) q = 0 :=
    fun q hq ↦ spatialSecondFDerivL_mul_eq_zero hα (χ := χ) hχzero u hq
  -- From now on only these properties of the localization `v = χ u` are used.
  generalize (ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u = v
    at hvu h0 hPv hzero ⊢
  -- The freezing error.
  have hFz := (hfreeze v hzero).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hvu hC₂))
  -- The lower-order terms, through interpolation.
  have hLo := (show ‖spatialOperatorL hα 0 B Cc v‖ ≤
      ‖B‖ * ‖spatialFDerivHolderL hα v‖ + ‖Cc‖ * ‖valueHolderL hα v‖ by
    simpa using norm_spatialOperatorL_apply_le hα (A := 0) (B := B) (C := Cc) v).trans
    (add_le_add (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hCc (norm_nonneg _)))
  have hi := (hint v).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hvu hK₃))
  have hsum := h0.trans (mul_le_mul_of_nonneg_left (norm_add₃_le.trans
    (add_le_add_three hPv hFz hLo)) hS)
  generalize ‖spatialFDerivHolderL hα v‖ = d at hi hsum
  generalize ‖valueHolderL hα v‖ = e at hi hsum
  generalize ‖parabolicOperatorL hα A B Cc u‖ = NP at hsum ⊢
  generalize ‖valueL u‖ = NV at hsum hi ⊢
  have hv := norm_nonneg v
  generalize ‖v‖ = NW at hsum hi hv ⊢
  -- Everything is now a real inequality.
  have hKBi := mul_le_mul_of_nonneg_left hi hKB
  have hSi := mul_le_mul_of_nonneg_left hKBi hS
  refine TauCeti.le_two_mul_of_le_add_mul hv hη ?_
  nlinarith

variable [FiniteDimensional ℝ E]

/-- **The Schauder estimate from frozen-coefficient estimates.** Let `0 < α < 1`. Suppose that
the operators `∂ₜ - A(p)·D_x²` with the second-order coefficient frozen at the points `p` of the
slab satisfy a common estimate `‖w‖ ≤ S ‖∂ₜw - A(p)·D_x²w‖` for every `w` with vanishing initial
trace. Then every `u ∈ C_b^{2+α,1+α/2}` with vanishing initial trace satisfies

`‖u‖ ≤ C (‖P u‖ + ‖u‖_∞)`, where `P u = ∂ₜu - A·D_x²u - B·D_xu - C·u`.

The constant `C` depends only on `α`, the dimension, `S` and bounds `KA` on `‖A‖` and `KB` on `‖B‖`
and `‖C‖`; it is the same on every slab. -/
theorem exists_norm_le_parabolicOperatorL_of_spatialTrace_eq_zero (hα₀ : 0 < α) (hα₁ : α < 1)
    {S KA KB : ℝ} (hS : 0 ≤ S) (hKA : 0 ≤ KA) (hKB : 0 ≤ KB) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} {ht : t₀ < t₁}
      (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ))
      (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] ℝ) →L[ℝ] ℝ))
      (Cc : HolderSpace α (slab (E := E) t₀ t₁) (ℝ →L[ℝ] ℝ)),
      ‖A‖ ≤ KA → ‖B‖ ≤ KB → ‖Cc‖ ≤ KB →
      (∀ p (w : ParabolicC2HolderSpace α E ℝ ht), w.spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩ = 0 →
        ‖w‖ ≤ S * ‖parabolicOperatorL hα₁.le (HolderSpace.const (A p)) 0 0 w‖) →
      ∀ u : ParabolicC2HolderSpace α E ℝ ht, u.spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩ = 0 →
        ‖u‖ ≤ C * (‖parabolicOperatorL hα₁.le A B Cc u‖ + ‖valueL u‖) := by
  -- Interpolation for the lower-order terms.
  set η₃ := 1 / (4 * (S + 1) * (KB + 1))
  obtain ⟨K₃, hK₃⟩ := exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le
    (E := E) (F := ℝ) hα₁ (η := η₃) (by positivity)
  -- Freezing the second-order coefficient on small parabolic balls.
  set η₂ := 1 / (4 * (S + 1))
  obtain ⟨r₀, hr₀, C₂, hfreeze⟩ := exists_norm_spatialOperatorL_sub_const_apply_le
    (E := E) (F := ℝ) hα₀ hα₁.le KA.toNNReal (η := η₂) (by positivity)
  -- Cutoffs, one on the parabolic ball of radius `r₀ / 4` about each point and vanishing at
  -- distance `r₀` from it.
  obtain ⟨Mχ, hMχ, hcut⟩ := exists_cutoff_family (E := E) hα₁.le (ρ := r₀ / 2) (by positivity)
  set R := 6 + 4 * (r₀ / 2 / 2) ^ (-(α : ℝ))
  have hR : 0 ≤ R := by positivity
  -- The localization error.
  set η₁ := 1 / (4 * (R + 1) * (S + 1))
  obtain ⟨K₁, hK₁, hloc⟩ := exists_norm_parabolicOperatorL_mul_sub_mul_parabolicOperatorL_le
    (E := E) hα₁ (M := Mχ + KA * Mχ + (KB + 2 * KA) * (24 * Mχ)) (by positivity) (η := η₁)
    (by positivity)
  have hη : S * η₂ + S * (KB * η₃) ≤ 1 / 2 := by
    have h₂ : S * η₂ ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    have h₃ : S * (KB * η₃) ≤ 1 / 4 := by
      rw [show S * (KB * η₃) = S * KB / (4 * (S + 1) * (KB + 1)) by simp only [η₃]; ring,
        div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hS hKB]
    linarith
  have hη₁ : R * (2 * S) * η₁ ≤ 1 / 2 := by
    rw [show R * (2 * S) * η₁ = 2 * (R * S) / (4 * (R + 1) * (S + 1)) by simp only [η₁]; ring,
      div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hR hS]
  set Kv := K₁ + max C₂ 0 + KB * max K₃ 0
  have hKv : 0 ≤ Kv := by positivity
  refine ⟨4 * (R + 1) * (S + 1) * (24 * Mχ + Kv), by positivity,
    fun {t₀ t₁ ht} A B Cc hA hB hCc hfrozen u hu ↦ ?_⟩
  obtain ⟨χ, hχn, hχmem, hχone, hχzero⟩ := hcut t₀ t₁ ht
  have hAK : nnHolderNorm α (A : slab (E := E) t₀ t₁ → _) ≤ KA.toNNReal := by
    rw [Real.le_toNNReal_iff_coe_le hKA]
    simpa using (HolderSpace.nnHolderNorm_le A).trans hA
  -- The estimate for each localization `χ_p u`.
  have hlocal (p : slab (E := E) t₀ t₁) :
      ‖(ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα₁.le (χ p) u‖ ≤
        2 * (S * (24 * Mχ * ‖parabolicOperatorL hα₁.le A B Cc u‖ + η₁ * ‖u‖ +
          Kv * ‖valueL u‖)) := by
    exact (norm_mul_le_of_norm_le_parabolicOperatorL_const hα₁.le hS hKB (le_max_right C₂ 0)
      (le_max_right K₃ 0) hη hB hCc (hfrozen p)
      (fun w hw ↦ (hfreeze A p w hAK (by positivity) (by linarith) hw).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left C₂ 0) (norm_nonneg _))))
      (fun w ↦ (hK₃ w).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (le_max_left K₃ 0) (norm_nonneg _))))
      (hχn p) (hχmem p) (hχzero p)
      (hloc A B Cc (χ p) (localization_bound_le hA hB hα₁.le (hχn p)) u) hu)
  -- Patch the local estimates and absorb the term in `‖u‖`.
  have hpatch : ‖u‖ ≤ R * (2 * (S * (24 * Mχ * ‖parabolicOperatorL hα₁.le A B Cc u‖ +
      η₁ * ‖u‖ + Kv * ‖valueL u‖))) :=
    norm_le_of_forall_eqOn_ball (r := r₀ / 2 / 2) (by positivity) fun p ↦
      ⟨_, hlocal p, fun q hq ↦ by simp [hχone p q hq]⟩
  have hNP := norm_nonneg (parabolicOperatorL hα₁.le A B Cc u)
  have hNV := norm_nonneg (valueL u)
  have hNU := norm_nonneg u
  generalize ‖parabolicOperatorL hα₁.le A B Cc u‖ = NP at hpatch hNP ⊢
  generalize ‖valueL u‖ = NV at hpatch hNV ⊢
  generalize ‖u‖ = NU at hpatch hNU ⊢
  have h1 := TauCeti.le_two_mul_of_le_add_mul hNU hη₁ (hpatch.trans_eq (show _ =
    R * (2 * S) * (24 * Mχ * NP + Kv * NV) + R * (2 * S) * η₁ * NU by ring))
  have hVM : (0 : ℝ) ≤ 24 * Mχ := by positivity
  have e1 : 24 * Mχ * NP + Kv * NV ≤ (24 * Mχ + Kv) * (NP + NV) := by
    nlinarith [mul_nonneg hVM hNV, mul_nonneg hKv hNP]
  have e2 : R * S ≤ (R + 1) * (S + 1) := by nlinarith
  calc NU ≤ 4 * (R * S) * (24 * Mχ * NP + Kv * NV) := h1.trans_eq (by ring)
    _ ≤ 4 * ((R + 1) * (S + 1)) * ((24 * Mχ + Kv) * (NP + NV)) := by gcongr
    _ = _ := by ring

/-- **The Schauder estimate from frozen-coefficient estimates, with initial data.** Let
`0 < α < 1`, let `H` be a continuous linear map lifting each `g ∈ C_b^{2,α}` to a map with initial
trace `g`, and suppose that the frozen operators `∂ₜ - A(p)·D_x²` satisfy a common estimate
`‖w‖ ≤ S ‖∂ₜw - A(p)·D_x²w‖` for every `w` with vanishing initial trace. Then every
`u ∈ C_b^{2+α,1+α/2}` satisfies

`‖u‖ ≤ C (‖P u‖ + ‖u(·, t₀)‖ + ‖u‖_∞)`, where `P u = ∂ₜu - A·D_x²u - B·D_xu - C·u`,

with `C` depending only on `α`, the dimension, `S`, `H` and bounds `KA` on `‖A‖` and `KB` on
`‖B‖` and `‖C‖`. -/
theorem exists_norm_le_parabolicOperatorL
    (hα₀ : 0 < α) (hα₁ : α < 1) {S KA KB : ℝ} (hS : 0 ≤ S) (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (H : CkHolderSpace 2 α E ℝ →L[ℝ] ParabolicC2HolderSpace α E ℝ ht)
    (hH : ∀ g, (H g).spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩ = g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ))
      (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] ℝ) →L[ℝ] ℝ))
      (Cc : HolderSpace α (slab (E := E) t₀ t₁) (ℝ →L[ℝ] ℝ)),
      ‖A‖ ≤ KA → ‖B‖ ≤ KB → ‖Cc‖ ≤ KB →
      (∀ p (w : ParabolicC2HolderSpace α E ℝ ht), w.spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩ = 0 →
        ‖w‖ ≤ S * ‖parabolicOperatorL hα₁.le (HolderSpace.const (A p)) 0 0 w‖) →
      ∀ u : ParabolicC2HolderSpace α E ℝ ht,
        ‖u‖ ≤ C * (‖parabolicOperatorL hα₁.le A B Cc u‖ +
          ‖u.spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩‖ + ‖valueL u‖) := by
  obtain ⟨C₁, hC₁, hgen⟩ :=
    exists_norm_le_parabolicOperatorL_of_spatialTrace_eq_zero (E := E) hα₀ hα₁ hS hKA hKB
  set N := ‖H‖
  have hN : 0 ≤ N := norm_nonneg _
  obtain ⟨N₂, hN₂, hHN⟩ := exists_norm_apply_le_mul H
  set Q := 1 + KA + 24 * (KB + KB)
  have hQ : 0 ≤ Q := by positivity
  refine ⟨C₁ * (1 + Q * N + N₂) + N₂ + C₁, by positivity, fun A B Cc hA hB hCc hfrozen u ↦ ?_⟩
  -- Apply the estimate to `w = u - H g`, which has vanishing initial trace.
  set g := u.spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩
  have hw : (u - H g).spatialTrace ⟨t₀, left_mem_Icc.2 ht.le⟩ = 0 := by
    rw [spatialTrace_sub, hH, sub_self]
  have hest := hgen A B Cc hA hB hCc hfrozen (u - H g) hw
  have hP : ‖parabolicOperatorL (ht := ht) hα₁.le A B Cc‖ ≤ Q :=
    (norm_parabolicOperatorL_le hα₁.le).trans (by simp only [Q]; linarith)
  generalize parabolicOperatorL (ht := ht) hα₁.le A B Cc = P at hest hP ⊢
  -- `P (H g)` is estimated through the composition, whose domain carries no `C_b^{2+α,1+α/2}` norm.
  have hPH := ((P.comp H).le_opNorm g).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le P H) (norm_nonneg g))
  rw [ContinuousLinearMap.comp_apply] at hPH
  have hPw := (norm_sub_le (P u) (P (H g))).trans (add_le_add le_rfl (hPH.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP hN) (norm_nonneg g))))
  rw [← map_sub] at hPw
  have hVw := (norm_sub_le (valueL u) (valueL (H g))).trans
    (add_le_add le_rfl ((norm_valueL_le (H g)).trans (hHN g)))
  rw [← map_sub] at hVw
  have hu := (norm_le_norm_sub_add_norm u (H g)).trans (add_le_add
    (hest.trans (mul_le_mul_of_nonneg_left (add_le_add hPw hVw) hC₁)) (hHN g))
  have hg := norm_nonneg g
  have hNP := norm_nonneg (P u)
  have hNV := norm_nonneg (valueL u)
  generalize ‖P u‖ = NP at hu hNP ⊢
  generalize ‖valueL u‖ = NV at hu hNV ⊢
  generalize ‖g‖ = G at hu hg ⊢
  have hQN := mul_nonneg hQ hN
  nlinarith [mul_nonneg hC₁ hNP, mul_nonneg hC₁ hNV, mul_nonneg hC₁ hg, mul_nonneg hN₂ hg,
    mul_nonneg (mul_nonneg hC₁ hQN) hg, mul_nonneg (mul_nonneg hC₁ hN₂) hg,
    mul_nonneg hC₁ (mul_nonneg hQN hNP), mul_nonneg hC₁ (mul_nonneg hQN hNV),
    mul_nonneg hC₁ (mul_nonneg hN₂ hNP), mul_nonneg hC₁ (mul_nonneg hN₂ hNV),
    mul_nonneg hN₂ hNP, mul_nonneg hN₂ hNV]

end General

/-! ### Coordinate coefficients on Euclidean space -/

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0}

attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

/-- Entry bounds `|Aᵢⱼ| ≤ K` bound the quadratic form of `A` by `n² K ‖ξ‖²`. -/
private theorem toQuadraticForm'_le_of_abs_le {A : Matrix ι ι ℝ} {K : ℝ}
    (hA : ∀ i j, |A i j| ≤ K) (ξ : EuclideanSpace ℝ ι) :
    A.toQuadraticForm' ξ ≤ Fintype.card ι * Fintype.card ι * K * ‖ξ‖ ^ 2 := by
  refine (PDE.toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq A ξ).trans ?_
  gcongr
  refine (PDE.norm_matrixBilinearForm_le_sum_abs A).trans ?_
  calc ∑ i, ∑ j, |A i j| ≤ ∑ _i : ι, ∑ _j : ι, K := by gcongr with i _ j _; exact hA i j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The Euclidean operator with the constant coefficients `aⁱʲ(p)` is the operator whose
second-order coefficient field is frozen at `p`. -/
private theorem euclideanParabolicOperatorL_const_apply (hα : α ≤ 1) {hT : (0 : ℝ) < T}
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) :
    euclideanParabolicOperatorL hα
        (fun i j ↦ HolderSpace.const ((Matrix.of fun i j ↦ a i j p) i j)) 0 0 u =
      parabolicOperatorL hα (HolderSpace.const (euclideanSecondOrderCoeff a p)) 0 0 u := by
  ext q
  simp

/-- **The Schauder estimate up to the supremum norm.** Let `0 < α < 1`, `0 < λ`, `K` and `T > 0`.
There is a constant `C` such that for all coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}` on
`ℝⁿ × [0, T]` with `λ ‖ξ‖² ≤ aⁱʲ(p) ξᵢ ξⱼ` and Hölder norms at most `K`, every
`u ∈ C_b^{2+α,1+α/2}` satisfies

`‖u‖ ≤ C (‖P u‖ + ‖u(·, 0)‖ + ‖u‖_∞)`, where `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`.

No sign condition on `c` and no symmetry of `a` is needed. -/
theorem exists_norm_le_euclideanParabolicOperatorL_add_norm_valueL (hα₀ : 0 < α) (hα₁ : α < 1)
    {lam : ℝ} (hlam : 0 < lam) (K : ℝ) (hT : (0 : ℝ) < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
      (∀ p (ξ : EuclideanSpace ℝ ι),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
      (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
      ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
        ‖u‖ ≤ C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ +
          ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖ + ‖valueL u‖) := by
  set K' := max K 0
  set n : ℝ := (Fintype.card ι : ℝ)
  have hK' : 0 ≤ K' := le_max_right _ _
  have hn : 0 ≤ n := Nat.cast_nonneg _
  set KA := n * n * K'
  set KB := n * K' + K'
  have hKA : 0 ≤ KA := by positivity
  have hKB : 0 ≤ KB := by positivity
  obtain ⟨C₀, hC₀, hconst⟩ :=
    exists_norm_le_euclideanParabolicOperatorL_const (ι := ι) hα₀ hα₁ (Lam := KA) hlam
  -- The initial trace is lifted by the Cauchy heat potential.
  obtain ⟨C, hC, hgen⟩ := exists_norm_le_parabolicOperatorL
    hα₀ hα₁ (S := C₀ * (1 + T)) (by positivity) hKA hKB
    (heatCauchyPotentialL (α := α) (E := EuclideanSpace ℝ ι) (F := ℝ) hT le_rfl)
    (spatialTrace_heatCauchyPotentialL_left hT)
  refine ⟨C, hC, fun a b c hell ha hb hc u ↦ ?_⟩
  -- Bounds for the coefficient fields.
  have hA : ‖euclideanSecondOrderCoeff a‖ ≤ KA := (norm_euclideanSecondOrderCoeff_le a).trans <| by
    calc ∑ i, ∑ j, ‖a i j‖ ≤ ∑ _i : ι, ∑ _j : ι, K' := by
          gcongr with i _ j _; exact (ha i j).trans (le_max_left _ _)
      _ = KA := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, KA, n]; ring
  have hB : ‖euclideanFirstOrderCoeff b‖ ≤ KB := (norm_euclideanFirstOrderCoeff_le b).trans <| by
    calc ∑ i, ‖b i‖ ≤ ∑ _i : ι, K' := by
          gcongr with i _; exact (hb i).trans (le_max_left _ _)
      _ ≤ KB := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, KB, n]; linarith
  have hCc : ‖euclideanZerothOrderCoeff c‖ ≤ KB := (norm_euclideanZerothOrderCoeff_le c).trans
    (hc.trans ((le_max_left _ _).trans (by simp only [KB]; nlinarith)))
  -- The frozen-coefficient estimate is the constant-coefficient one.
  have hfrozen (p : slab (E := EuclideanSpace ℝ ι) 0 T)
      (w : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT)
      (hw : w.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = 0) :
      ‖w‖ ≤ C₀ * (1 + T) * ‖parabolicOperatorL hα₁.le
        (HolderSpace.const (euclideanSecondOrderCoeff a p)) 0 0 w‖ := by
    have hupper (ξ : EuclideanSpace ℝ ι) :
        (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ KA * ‖ξ‖ ^ 2 :=
      toQuadraticForm'_le_of_abs_le (fun i j ↦ by
        simpa only [Matrix.of_apply, Real.norm_eq_abs] using
          (HolderSpace.norm_apply_le (a i j) p).trans ((ha i j).trans (le_max_left _ _))) ξ
    have h := hconst (Matrix.of fun i j ↦ a i j p) (hell p) hupper T hT w
    rwa [hw, norm_zero, add_zero, euclideanParabolicOperatorL_const_apply] at h
  rw [euclideanParabolicOperatorL_def]
  exact hgen _ _ _ hA hB hCc hfrozen u

/-- **The Schauder estimate for the Cauchy problem with variable coefficients.** Let `0 < α < 1`,
`0 < λ`, `K` and `T > 0`. There is a constant `C` such that for all coefficients `aⁱʲ`, `bⁱ`, `c` in
`C_b^{α,α/2}` on `ℝⁿ × [0, T]` with `λ ‖ξ‖² ≤ aⁱʲ(p) ξᵢ ξⱼ` and Hölder norms at most `K`, every
`u ∈ C_b^{2+α,1+α/2}` satisfies

`‖u‖ ≤ C (‖P u‖ + ‖u(·, 0)‖)`, where `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`.

The constant depends only on `α`, `λ`, `K`, the dimension and `T`. The supremum norm in
`TauCeti.ParabolicC2HolderSpace.exists_norm_le_euclideanParabolicOperatorL_add_norm_valueL` is
bounded by the maximum principle, `‖u‖_∞ ≤ exp (K T) (‖u(·, 0)‖_∞ + T ‖P u‖_∞)`. -/
theorem exists_norm_le_euclideanParabolicOperatorL (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K : ℝ) (hT : (0 : ℝ) < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
      (∀ p (ξ : EuclideanSpace ℝ ι),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
      (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
      ∀ u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT,
        ‖u‖ ≤ C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ +
          ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖) := by
  obtain ⟨C, hC, h⟩ :=
    exists_norm_le_euclideanParabolicOperatorL_add_norm_valueL (ι := ι) hα₀ hα₁ hlam K hT
  set γ := max K 0
  have hγ : 0 ≤ γ := le_max_right _ _
  set Ex := Real.exp (γ * T)
  have hEx : 0 ≤ Ex := (Real.exp_pos _).le
  refine ⟨C * (1 + Ex * (1 + T)), by positivity, fun a b c hell ha hb hc u ↦ ?_⟩
  have hu := h a b c hell ha hb hc u
  -- The maximum principle bounds the supremum norm.
  have hmax : ‖valueL u‖ ≤ Ex * (‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖ +
      T * ‖euclideanParabolicOperatorL hα₁.le a b c u‖) := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
    have hp := abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα₁.le
      (fun q ξ ↦ (by positivity : 0 ≤ lam * ‖ξ‖ ^ 2).trans (hell q ξ))
      (fun q ↦ (le_abs_self _).trans ((HolderSpace.norm_apply_le c q).trans
        (hc.trans (le_max_left _ _)))) hγ u
      (fun q ↦ by simpa only [Real.norm_eq_abs] using
        HolderSpace.norm_apply_le (euclideanParabolicOperatorL hα₁.le a b c u) q)
      (fun x ↦ by simpa only [spatialTrace_apply, Real.norm_eq_abs] using
        CkHolderSpace.norm_apply_le (u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩) x) p
    rw [valueL_apply, Real.norm_eq_abs]
    have ht0 : (0 : ℝ) ≤ slabTime p := (slabTime p).2.1
    have htT : (slabTime p : ℝ) ≤ T := (slabTime p).2.2
    refine hp.trans ?_
    rw [sub_zero]
    exact mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htT hγ)) (by gcongr)
      (by positivity) hEx
  have hNP := norm_nonneg (euclideanParabolicOperatorL hα₁.le a b c u)
  have hNG := norm_nonneg (u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩)
  generalize ‖euclideanParabolicOperatorL hα₁.le a b c u‖ = NP at hu hmax hNP ⊢
  generalize ‖u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖ = NG at hu hmax hNG ⊢
  generalize ‖valueL u‖ = NV at hu hmax
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  nlinarith [mul_le_mul_of_nonneg_left hmax hC, mul_nonneg hC (mul_nonneg hEx hNP),
    mul_nonneg hC (mul_nonneg hEx hNG), mul_nonneg hC (mul_nonneg (mul_nonneg hEx hT0) hNG),
    mul_nonneg hC (mul_nonneg (mul_nonneg hEx hT0) hNP)]

end Euclidean

end TauCeti.ParabolicC2HolderSpace
