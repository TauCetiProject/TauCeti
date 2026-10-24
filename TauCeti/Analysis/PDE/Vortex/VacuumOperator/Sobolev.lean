/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.LaplacianResolvent
public import TauCeti.Analysis.PDE.Vortex.VacuumOperator.Basic
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv

/-!
# The vacuum vortex operator on the Sobolev scale

The gauge-fixed linearization `L₀` of the vortex equations at the vacuum
(`TauCeti.Vortex.vacuumOperator`) is a first-order operator with constant real coefficients
acting on fields `x = (b₁, b₂, p, q)`. This file extends `L₀` and its formal adjoint `L₀*` to
fields whose four components are complex tempered distributions on `ℂ`, so that they act on
Mathlib's `L²` Sobolev spaces `H^s` (`TemperedDistribution.MemSobolev s 2`) for every real `s`.
The complex components are the complexification of the real fields: the coefficients of `L₀` are
real, and real fields are the ones whose components are real distributions. A field lies in `H^s`
when each of its components does.

The Weitzenböck identities `L₀* L₀ = L₀ L₀* = -Δ + 1 / 4` continue to hold on tempered
distributions. With the resolvent `(-Δ + 1 / 4)⁻¹` of the Laplacian on tempered distributions
(`TemperedDistribution.laplacianResolvent`), they show that `L₀` and `L₀*` are continuous linear
automorphisms of the space of tempered fields, with inverses `L₀⁻¹ = L₀* (-Δ + 1 / 4)⁻¹` and
`(L₀*)⁻¹ = L₀ (-Δ + 1 / 4)⁻¹`. On the Sobolev scale, `L₀` maps `H^s` to `H^{s-1}`, since it has
order one, while `L₀⁻¹` maps `H^{s-1}` back to `H^s`, since the resolvent gains two derivatives and
`L₀*` loses one. Hence `L₀ : H^s → H^{s-1}` is bijective for every `s`, in particular
`H^k → H^{k-1}` for every integer `k`, and a tempered field `x` lies in `H^s` exactly when `L₀ x`
lies in `H^{s-1}`. On Schwartz fields the tempered operators agree with `vacuumOperator` and
`vacuumAdjoint`.

## Main declarations

* `TauCeti.Vortex.temperedVacuumOperator` and `TauCeti.Vortex.temperedVacuumAdjoint`: `L₀` and
  `L₀*` on fields of tempered distributions, characterized by their component formulas.
* `TauCeti.Vortex.temperedVacuumOperator_toTemperedDistribution` and
  `TauCeti.Vortex.temperedVacuumAdjoint_toTemperedDistribution`: they extend `vacuumOperator` and
  `vacuumAdjoint` from Schwartz fields.
* `TauCeti.Vortex.temperedVacuumAdjoint_temperedVacuumOperator` and
  `TauCeti.Vortex.temperedVacuumOperator_temperedVacuumAdjoint`: the Weitzenböck identities
  `L₀* L₀ = L₀ L₀* = -Δ + 1 / 4`.
* `TauCeti.Vortex.temperedVacuumOperatorEquiv` and `TauCeti.Vortex.temperedVacuumAdjointEquiv`:
  `L₀` and `L₀*` as continuous linear automorphisms of the tempered fields, with inverses given by
  `TauCeti.Vortex.temperedVacuumOperatorEquiv_symm_apply` and
  `TauCeti.Vortex.temperedVacuumAdjointEquiv_symm_apply`.
* `TauCeti.Vortex.memSobolev_temperedVacuumOperator` and
  `TauCeti.Vortex.memSobolev_temperedVacuumOperatorEquiv_symm`: `L₀ : H^s → H^{s-1}` and
  `L₀⁻¹ : H^s → H^{s+1}`.
* `TauCeti.Vortex.memSobolev_temperedVacuumOperator_iff`: `x ∈ H^s` if and only if
  `L₀ x ∈ H^{s-1}`; with the automorphism this is the bijectivity of `L₀ : H^s → H^{s-1}`. The
  same statements for `L₀*` are `TauCeti.Vortex.memSobolev_temperedVacuumAdjoint`,
  `TauCeti.Vortex.memSobolev_temperedVacuumAdjointEquiv_symm` and
  `TauCeti.Vortex.memSobolev_temperedVacuumAdjoint_iff`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845--918.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1 (the Sobolev spaces `H^s`).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open scoped SchwartzMap LineDeriv Laplacian
open Complex TemperedDistribution

/-- The derivative `∂_v` as a continuous linear map on tempered distributions on `ℂ`. -/
private abbrev D (v : ℂ) : 𝓢'(ℂ, ℂ) →L[ℂ] 𝓢'(ℂ, ℂ) := LineDeriv.lineDerivOpCLM ℂ 𝓢'(ℂ, ℂ) v

/-- The `i`-th component of a field of tempered distributions. -/
private abbrev P (i : Fin 4) : (Fin 4 → 𝓢'(ℂ, ℂ)) →L[ℂ] 𝓢'(ℂ, ℂ) := ContinuousLinearMap.proj i

/-- The vacuum operator `L₀` on fields `x = (b₁, b₂, p, q)` of complex tempered distributions on
`ℂ`, producing `(G, C, H₁, H₂)`; see the component formulas `temperedVacuumOperator_apply_zero`
through `temperedVacuumOperator_apply_three`. On Schwartz fields it is `vacuumOperator`
(`temperedVacuumOperator_toTemperedDistribution`). -/
def temperedVacuumOperator : (Fin 4 → 𝓢'(ℂ, ℂ)) →L[ℂ] (Fin 4 → 𝓢'(ℂ, ℂ)) :=
  ContinuousLinearMap.pi ![
    D 1 ∘L P 0 + D I ∘L P 1 + (1 / 2 : ℝ) • P 3,
    D I ∘L P 0 - D 1 ∘L P 1 + (1 / 2 : ℝ) • P 2,
    D 1 ∘L P 2 - D I ∘L P 3 - (1 / 2 : ℝ) • P 1,
    D I ∘L P 2 + D 1 ∘L P 3 + (1 / 2 : ℝ) • P 0]

/-- The formal adjoint `L₀*` of the vacuum operator on fields of complex tempered distributions on
`ℂ`; see the component formulas `temperedVacuumAdjoint_apply_zero` through
`temperedVacuumAdjoint_apply_three`. On Schwartz fields it is `vacuumAdjoint`
(`temperedVacuumAdjoint_toTemperedDistribution`). -/
def temperedVacuumAdjoint : (Fin 4 → 𝓢'(ℂ, ℂ)) →L[ℂ] (Fin 4 → 𝓢'(ℂ, ℂ)) :=
  ContinuousLinearMap.pi ![
    -(D 1 ∘L P 0) - D I ∘L P 1 + (1 / 2 : ℝ) • P 3,
    -(D I ∘L P 0) + D 1 ∘L P 1 - (1 / 2 : ℝ) • P 2,
    -(D 1 ∘L P 2) - D I ∘L P 3 + (1 / 2 : ℝ) • P 1,
    D I ∘L P 2 - D 1 ∘L P 3 + (1 / 2 : ℝ) • P 0]

variable (x y : Fin 4 → 𝓢'(ℂ, ℂ))

/-- The gauge component `G = ∂₁ b₁ + ∂₂ b₂ + q / 2` of `L₀`. -/
@[simp]
theorem temperedVacuumOperator_apply_zero :
    temperedVacuumOperator x 0 = ∂_{(1 : ℂ)} (x 0) + ∂_{I} (x 1) + (1 / 2 : ℝ) • x 3 :=
  (rfl)

/-- The curvature component `C = ∂₂ b₁ - ∂₁ b₂ + p / 2` of `L₀`. -/
@[simp]
theorem temperedVacuumOperator_apply_one :
    temperedVacuumOperator x 1 = ∂_{I} (x 0) - ∂_{(1 : ℂ)} (x 1) + (1 / 2 : ℝ) • x 2 :=
  (rfl)

/-- The first `∂bar` component `H₁ = ∂₁ p - ∂₂ q - b₂ / 2` of `L₀`. -/
@[simp]
theorem temperedVacuumOperator_apply_two :
    temperedVacuumOperator x 2 = ∂_{(1 : ℂ)} (x 2) - ∂_{I} (x 3) - (1 / 2 : ℝ) • x 1 :=
  (rfl)

/-- The second `∂bar` component `H₂ = ∂₂ p + ∂₁ q + b₁ / 2` of `L₀`. -/
@[simp]
theorem temperedVacuumOperator_apply_three :
    temperedVacuumOperator x 3 = ∂_{I} (x 2) + ∂_{(1 : ℂ)} (x 3) + (1 / 2 : ℝ) • x 0 :=
  (rfl)

/-- The `b₁` component `-∂₁ G - ∂₂ C + H₂ / 2` of `L₀* (G, C, H₁, H₂)`. -/
@[simp]
theorem temperedVacuumAdjoint_apply_zero :
    temperedVacuumAdjoint y 0 = -∂_{(1 : ℂ)} (y 0) - ∂_{I} (y 1) + (1 / 2 : ℝ) • y 3 :=
  (rfl)

/-- The `b₂` component `-∂₂ G + ∂₁ C - H₁ / 2` of `L₀* (G, C, H₁, H₂)`. -/
@[simp]
theorem temperedVacuumAdjoint_apply_one :
    temperedVacuumAdjoint y 1 = -∂_{I} (y 0) + ∂_{(1 : ℂ)} (y 1) - (1 / 2 : ℝ) • y 2 :=
  (rfl)

/-- The `p` component `-∂₁ H₁ - ∂₂ H₂ + C / 2` of `L₀* (G, C, H₁, H₂)`. -/
@[simp]
theorem temperedVacuumAdjoint_apply_two :
    temperedVacuumAdjoint y 2 = -∂_{(1 : ℂ)} (y 2) - ∂_{I} (y 3) + (1 / 2 : ℝ) • y 1 :=
  (rfl)

/-- The `q` component `∂₂ H₁ - ∂₁ H₂ + G / 2` of `L₀* (G, C, H₁, H₂)`. -/
@[simp]
theorem temperedVacuumAdjoint_apply_three :
    temperedVacuumAdjoint y 3 = ∂_{I} (y 2) - ∂_{(1 : ℂ)} (y 3) + (1 / 2 : ℝ) • y 0 :=
  (rfl)

/-! ### Agreement with the vacuum operator on Schwartz fields -/

/-- `temperedVacuumOperator` extends `vacuumOperator`: on the components of a real Schwartz
field `x`, viewed as complex tempered distributions, it gives the components of
`vacuumOperator x`. -/
theorem temperedVacuumOperator_toTemperedDistribution (x : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    temperedVacuumOperator
        (fun i ↦ (x.postcompCLM (ofRealCLM ∘L EuclideanSpace.proj i) : 𝓢'(ℂ, ℂ))) =
      fun i ↦ ((vacuumOperator x).postcompCLM (ofRealCLM ∘L EuclideanSpace.proj i) : 𝓢'(ℂ, ℂ)) := by
  ext1 i
  fin_cases i <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      temperedVacuumOperator_apply_zero, temperedVacuumOperator_apply_one,
      temperedVacuumOperator_apply_two, temperedVacuumOperator_apply_three,
      lineDerivOp_toTemperedDistributionCLM_postcompCLM]
    simp only [← ContinuousLinearMap.map_smul_of_tower, ← map_add, ← map_sub]
    congr 1
    ext z
    simp [div_eq_inv_mul]

/-- `temperedVacuumAdjoint` extends `vacuumAdjoint`: on the components of a real Schwartz
field `y`, viewed as complex tempered distributions, it gives the components of
`vacuumAdjoint y`. -/
theorem temperedVacuumAdjoint_toTemperedDistribution (y : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    temperedVacuumAdjoint
        (fun i ↦ (y.postcompCLM (ofRealCLM ∘L EuclideanSpace.proj i) : 𝓢'(ℂ, ℂ))) =
      fun i ↦ ((vacuumAdjoint y).postcompCLM (ofRealCLM ∘L EuclideanSpace.proj i) : 𝓢'(ℂ, ℂ)) := by
  ext1 i
  fin_cases i <;>
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      temperedVacuumAdjoint_apply_zero, temperedVacuumAdjoint_apply_one,
      temperedVacuumAdjoint_apply_two, temperedVacuumAdjoint_apply_three,
      lineDerivOp_toTemperedDistributionCLM_postcompCLM]
    simp only [← ContinuousLinearMap.map_smul_of_tower, ← map_neg, ← map_add, ← map_sub]
    congr 1
    ext z
    simp [div_eq_inv_mul]

/-! ### The Weitzenböck identities -/

/-- **The Weitzenböck identity at the vacuum** on tempered fields: `L₀* L₀ = -Δ + 1 / 4`. -/
theorem temperedVacuumAdjoint_temperedVacuumOperator :
    temperedVacuumAdjoint (temperedVacuumOperator x) = fun i ↦ -Δ (x i) + (1 / 4 : ℝ) • x i := by
  ext1 i
  fin_cases i <;>
  · simp [laplacian_eq_lineDerivOp_one_I, LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_smul,
      sub_eq_add_neg, lineDerivOp_comm _ I (1 : ℂ)]
    module

/-- The reverse Weitzenböck identity at the vacuum on tempered fields: `L₀ L₀* = -Δ + 1 / 4`. -/
theorem temperedVacuumOperator_temperedVacuumAdjoint :
    temperedVacuumOperator (temperedVacuumAdjoint y) = fun i ↦ -Δ (y i) + (1 / 4 : ℝ) • y i := by
  ext1 i
  fin_cases i <;>
  · simp [laplacian_eq_lineDerivOp_one_I, LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_smul,
      sub_eq_add_neg, lineDerivOp_comm _ I (1 : ℂ)]
    module

/-! ### The inverses of the vacuum operator and its adjoint -/

private theorem temperedVacuumOperator_temperedVacuumAdjoint_laplacianResolvent :
    temperedVacuumOperator (temperedVacuumAdjoint fun i ↦ laplacianResolvent ℂ (1 / 4) (y i)) =
      y := by
  rw [temperedVacuumOperator_temperedVacuumAdjoint]
  ext1 i
  exact neg_laplacian_laplacianResolvent_add_smul (by norm_num) (y i)

private theorem temperedVacuumAdjoint_temperedVacuumOperator_laplacianResolvent :
    temperedVacuumAdjoint (temperedVacuumOperator fun i ↦ laplacianResolvent ℂ (1 / 4) (y i)) =
      y := by
  rw [temperedVacuumAdjoint_temperedVacuumOperator]
  ext1 i
  exact neg_laplacian_laplacianResolvent_add_smul (by norm_num) (y i)

/-- The vacuum operator has trivial kernel on tempered fields. -/
theorem temperedVacuumOperator_injective : Function.Injective temperedVacuumOperator :=
  (injective_iff_map_eq_zero _).2 fun x hx ↦ funext fun i ↦
    eq_zero_of_neg_laplacian_add_smul_eq_zero (c := 1 / 4) (by norm_num) <| by
      rw [← congrFun (temperedVacuumAdjoint_temperedVacuumOperator x) i, hx, map_zero,
        Pi.zero_apply]

/-- The adjoint of the vacuum operator has trivial kernel on tempered fields. -/
theorem temperedVacuumAdjoint_injective : Function.Injective temperedVacuumAdjoint :=
  (injective_iff_map_eq_zero _).2 fun x hx ↦ funext fun i ↦
    eq_zero_of_neg_laplacian_add_smul_eq_zero (c := 1 / 4) (by norm_num) <| by
      rw [← congrFun (temperedVacuumOperator_temperedVacuumAdjoint x) i, hx, map_zero,
        Pi.zero_apply]

/-- **The vacuum operator is invertible on tempered fields**: `L₀` as a continuous linear
automorphism of the fields of tempered distributions. Its inverse is `L₀⁻¹ = L₀* (-Δ + 1 / 4)⁻¹`
(`temperedVacuumOperatorEquiv_symm_apply`). -/
def temperedVacuumOperatorEquiv : (Fin 4 → 𝓢'(ℂ, ℂ)) ≃L[ℂ] (Fin 4 → 𝓢'(ℂ, ℂ)) :=
  .equivOfInverse temperedVacuumOperator
    (temperedVacuumAdjoint ∘L .piMap fun _ ↦ laplacianResolvent ℂ (1 / 4))
    -- `ContinuousLinearMap.piMap` applies the resolvent componentwise, by definition.
    (fun _ ↦ temperedVacuumOperator_injective <|
      temperedVacuumOperator_temperedVacuumAdjoint_laplacianResolvent _)
    (fun y ↦ temperedVacuumOperator_temperedVacuumAdjoint_laplacianResolvent y)

/-- **The adjoint of the vacuum operator is invertible on tempered fields**: `L₀*` as a continuous
linear automorphism of the fields of tempered distributions. Its inverse is
`(L₀*)⁻¹ = L₀ (-Δ + 1 / 4)⁻¹` (`temperedVacuumAdjointEquiv_symm_apply`). -/
def temperedVacuumAdjointEquiv : (Fin 4 → 𝓢'(ℂ, ℂ)) ≃L[ℂ] (Fin 4 → 𝓢'(ℂ, ℂ)) :=
  .equivOfInverse temperedVacuumAdjoint
    (temperedVacuumOperator ∘L .piMap fun _ ↦ laplacianResolvent ℂ (1 / 4))
    -- `ContinuousLinearMap.piMap` applies the resolvent componentwise, by definition.
    (fun _ ↦ temperedVacuumAdjoint_injective <|
      temperedVacuumAdjoint_temperedVacuumOperator_laplacianResolvent _)
    (fun y ↦ temperedVacuumAdjoint_temperedVacuumOperator_laplacianResolvent y)

@[simp]
theorem coe_temperedVacuumOperatorEquiv : ⇑temperedVacuumOperatorEquiv = temperedVacuumOperator :=
  (rfl)

@[simp]
theorem coe_temperedVacuumAdjointEquiv : ⇑temperedVacuumAdjointEquiv = temperedVacuumAdjoint :=
  (rfl)

/-- The inverse of the vacuum operator on tempered fields is `L₀⁻¹ = L₀* (-Δ + 1 / 4)⁻¹`. -/
theorem temperedVacuumOperatorEquiv_symm_apply :
    temperedVacuumOperatorEquiv.symm y =
      temperedVacuumAdjoint fun i ↦ laplacianResolvent ℂ (1 / 4) (y i) :=
  (rfl)

/-- The inverse of the adjoint of the vacuum operator on tempered fields is
`(L₀*)⁻¹ = L₀ (-Δ + 1 / 4)⁻¹`. -/
theorem temperedVacuumAdjointEquiv_symm_apply :
    temperedVacuumAdjointEquiv.symm y =
      temperedVacuumOperator fun i ↦ laplacianResolvent ℂ (1 / 4) (y i) :=
  (rfl)

/-! ### The Sobolev scale -/

variable {s : ℝ} {x y}

/-- **The vacuum operator has order one**: `L₀` maps `H^s` to `H^{s-1}`. -/
theorem memSobolev_temperedVacuumOperator (hx : ∀ i, MemSobolev s 2 (x i)) (i : Fin 4) :
    MemSobolev (s - 1) 2 (temperedVacuumOperator x i) := by
  have hd (j : Fin 4) (v : ℂ) : MemSobolev (s - 1) 2 (∂_{v} (x j)) := (hx j).lineDerivOp
  have h₀ (j : Fin 4) : MemSobolev (s - 1) 2 ((1 / 2 : ℝ) • x j) :=
    ((hx j).mono (s' := s - 1) (by linarith)).smul_of_tower _
  fin_cases i
  exacts [((hd 0 1).add (hd 1 I)).add (h₀ 3), ((hd 0 I).sub (hd 1 1)).add (h₀ 2),
    ((hd 2 1).sub (hd 3 I)).sub (h₀ 1), ((hd 2 I).add (hd 3 1)).add (h₀ 0)]

/-- The adjoint of the vacuum operator has order one: `L₀*` maps `H^s` to `H^{s-1}`. -/
theorem memSobolev_temperedVacuumAdjoint (hy : ∀ i, MemSobolev s 2 (y i)) (i : Fin 4) :
    MemSobolev (s - 1) 2 (temperedVacuumAdjoint y i) := by
  have hd (j : Fin 4) (v : ℂ) : MemSobolev (s - 1) 2 (∂_{v} (y j)) := (hy j).lineDerivOp
  have h₀ (j : Fin 4) : MemSobolev (s - 1) 2 ((1 / 2 : ℝ) • y j) :=
    ((hy j).mono (s' := s - 1) (by linarith)).smul_of_tower _
  fin_cases i
  exacts [((hd 0 1).neg.sub (hd 1 I)).add (h₀ 3), ((hd 0 I).neg.add (hd 1 1)).sub (h₀ 2),
    ((hd 2 1).neg.sub (hd 3 I)).add (h₀ 1), ((hd 2 I).sub (hd 3 1)).add (h₀ 0)]

/-- **The inverse of the vacuum operator gains one derivative**: `L₀⁻¹` maps `H^s` to
`H^{s+1}`. -/
theorem memSobolev_temperedVacuumOperatorEquiv_symm (hy : ∀ i, MemSobolev s 2 (y i))
    (i : Fin 4) : MemSobolev (s + 1) 2 (temperedVacuumOperatorEquiv.symm y i) := by
  rw [temperedVacuumOperatorEquiv_symm_apply, show s + 1 = s + 2 - 1 by ring]
  exact memSobolev_temperedVacuumAdjoint
    (fun j ↦ (hy j).laplacianResolvent (c := 1 / 4) (by norm_num)) i

/-- The inverse of the adjoint of the vacuum operator gains one derivative: `(L₀*)⁻¹` maps `H^s`
to `H^{s+1}`. -/
theorem memSobolev_temperedVacuumAdjointEquiv_symm (hy : ∀ i, MemSobolev s 2 (y i))
    (i : Fin 4) : MemSobolev (s + 1) 2 (temperedVacuumAdjointEquiv.symm y i) := by
  rw [temperedVacuumAdjointEquiv_symm_apply, show s + 1 = s + 2 - 1 by ring]
  exact memSobolev_temperedVacuumOperator
    (fun j ↦ (hy j).laplacianResolvent (c := 1 / 4) (by norm_num)) i

/-- **The vacuum operator restricts to a bijection `H^s → H^{s-1}`**: a tempered field `x` lies in
`H^s` if and only if `L₀ x` lies in `H^{s-1}`. Since `L₀` is bijective on tempered fields
(`temperedVacuumOperatorEquiv`), it restricts to a bijection from `H^s` onto `H^{s-1}`, for every
real `s`. -/
theorem memSobolev_temperedVacuumOperator_iff :
    (∀ i, MemSobolev (s - 1) 2 (temperedVacuumOperator x i)) ↔ ∀ i, MemSobolev s 2 (x i) := by
  refine ⟨fun h i ↦ ?_, memSobolev_temperedVacuumOperator⟩
  simpa only [sub_add_cancel, ContinuousLinearEquiv.symm_apply_apply] using
    memSobolev_temperedVacuumOperatorEquiv_symm (y := temperedVacuumOperatorEquiv x) h i

/-- The adjoint of the vacuum operator restricts to a bijection `H^s → H^{s-1}`: a tempered field
`y` lies in `H^s` if and only if `L₀* y` lies in `H^{s-1}`. Since `L₀*` is bijective on tempered
fields (`temperedVacuumAdjointEquiv`), it restricts to a bijection from `H^s` onto `H^{s-1}`, for
every real `s`. -/
theorem memSobolev_temperedVacuumAdjoint_iff :
    (∀ i, MemSobolev (s - 1) 2 (temperedVacuumAdjoint y i)) ↔ ∀ i, MemSobolev s 2 (y i) := by
  refine ⟨fun h i ↦ ?_, memSobolev_temperedVacuumAdjoint⟩
  simpa only [sub_add_cancel, ContinuousLinearEquiv.symm_apply_apply] using
    memSobolev_temperedVacuumAdjointEquiv_symm (y := temperedVacuumAdjointEquiv y) h i

end TauCeti.Vortex
