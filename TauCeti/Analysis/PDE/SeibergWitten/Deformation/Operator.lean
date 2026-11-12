/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Deformation.Symbol
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The anti-self-dual deformation operator and its complex-linear part

On an oriented Euclidean four-space `V`, identify one-forms with vector fields `a : V → V` and
two-forms with two-vectors through the inner product. The first-order operator

`δ₀ a = (-d*a, √2 (da)⁺) : Ω¹ → Ω⁰ ⊕ Ω⁺`

(`TauCeti.SeibergWitten.deformationOperator`) is the contraction of the derivative of `a` with
its principal symbol `σ_ξ(b) = (⟪ξ, b⟫, √2 (ξ ∧ b)⁺)`
(`TauCeti.SeibergWitten.deformationSymbol`): in every orthonormal basis `e`,

`δ₀ a (x) = ∑ₖ σ_{eₖ} (∂_{eₖ} a (x))`

(`TauCeti.SeibergWitten.deformationOperator_eq_sum`). Its scalar component is the divergence
`-d*a = tr (Da)` and its two-form component is self-dual. The principal symbol is recovered from
the Leibniz rule `δ₀ (f a) = f δ₀ a + σ_{∇f} (a)`
(`TauCeti.SeibergWitten.deformationOperator_smul`).

Let `J` be a field of orthogonal complex structures on `V` inducing the orientation, and let
`J′ = J′(x)` be the complex structure of `ℝ ⊕ Λ⁺` that it determines at each point
(`TauCeti.SeibergWitten.deformationComplexStructure`). The **complex-linear part** of `δ₀` is

`δ_ω a = (δ₀ a - J′ δ₀ (J a)) / 2`

(`TauCeti.SeibergWitten.complexDeformationOperator`). It is complex linear,
`δ_ω (J a) = J′ (δ_ω a)`, and takes values in `ℝ ⊕ Λ⁺`. Since the symbol satisfies
`σ_ξ ∘ J = J′ ∘ σ_ξ` pointwise, the derivative of `J a` contributes `J′ δ₀ a` plus a term in which
only the derivative of `J` appears, and

`δ₀ a (x) - δ_ω a (x) = J′ δ₀ (J (a x)) (x) / 2`,

where `J (a x)` is the field `y ↦ J y (a x)` with the value of `a` at `x` frozen
(`TauCeti.SeibergWitten.deformationOperator_sub_complexDeformationOperator`). So `δ₀ - δ_ω` is an
operator of order zero, vanishing where `J` is stationary, and `δ_ω` satisfies the same Leibniz
rule as `δ₀` (`TauCeti.SeibergWitten.complexDeformationOperator_smul`): the two operators have the
same principal symbol, and the segment `δ₀ - t (δ₀ - δ_ω)`, `0 ≤ t ≤ 1`, joins them through
zeroth-order perturbations of `δ₀`. Along this homotopy the complex orientation of the determinant
line of `δ_ω` is compared with an orientation of the determinant line of `δ₀`; the determinant
lines, their Fredholm realizations and the transport are not constructed here. Everything is in
the flat model with a varying almost complex structure. The pointwise algebra of `σ` and `J′` is in
`TauCeti.Analysis.PDE.SeibergWitten.Deformation.Symbol`.

The statements involving `J` at a point `x` take a positively oriented orthonormal basis `e`
with `J x e₀ = e₁` and `J x e₂ = e₃` as a witness that `J x` is orthogonal and induces the
orientation.

## Main definitions

* `TauCeti.SeibergWitten.deformationOperator o hkl a x`: the value of `δ₀ a` at `x`.
* `TauCeti.SeibergWitten.complexDeformationOperator o hkl J a x`: the value of
  `δ_ω a = (δ₀ a - J′ δ₀ (J a)) / 2` at `x`.

## Main results

* `TauCeti.SeibergWitten.deformationOperator_eq_sum`: `δ₀ a = ∑ₖ σ_{eₖ} (∂_{eₖ} a)` in every
  orthonormal basis.
* `TauCeti.SeibergWitten.deformationOperator_fst`: the scalar component is `tr (Da)`.
* `TauCeti.SeibergWitten.hodgeStar_deformationOperator_snd`: the two-form component is self-dual.
* `TauCeti.SeibergWitten.deformationOperator_smul`: the Leibniz rule
  `δ₀ (f a) = f δ₀ a + σ_{∇f} (a)`.
* `TauCeti.SeibergWitten.complexDeformationOperator_apply_eq_deformationComplexStructure`:
  `δ_ω (J a) = J′ (δ_ω a)`.
* `TauCeti.SeibergWitten.deformationOperator_sub_complexDeformationOperator`:
  `δ₀ a - δ_ω a = J′ δ₀ (J (a x)) / 2` at `x`, an expression in the value `a x` alone.
* `TauCeti.SeibergWitten.complexDeformationOperator_smul`: the Leibniz rule
  `δ_ω (f a) = f δ_ω a + σ_{∇f} (a)`.

## References

* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
-/

public section

noncomputable section

open Module exteriorPower InnerProductSpace TensorProduct
open scoped RealInnerProductSpace Gradient

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  (o : Orientation ℝ V (Fin 4)) (hkl : 2 + 2 = finrank ℝ V)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

/-! ### The operator `δ₀` -/

/-- **The anti-self-dual deformation operator** `δ₀ a = (-d*a, √2 (da)⁺)` of a vector field
`a : V → V`, viewed as a one-form, at the point `x`: the contraction of the derivative of `a` at
`x` with the principal symbol, `δ₀ a (x) = ∑ₖ σ_{eₖ} (∂_{eₖ} a (x))` for every orthonormal basis
`e` (`deformationOperator_eq_sum`). -/
def deformationOperator (a : V → V) (x : V) : ℝ × ⋀[ℝ]^2 V :=
  lift ((deformationSymbol o hkl).compl₂ (fderiv ℝ a x : V →ₗ[ℝ] V))
    (canonicalCovariantTensor V)

/-- **`δ₀` in an orthonormal basis**: `δ₀ a (x) = ∑ₖ σ_{eₖ} (∂_{eₖ} a (x))`. -/
theorem deformationOperator_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (a : V → V) (x : V) :
    deformationOperator o hkl a x = ∑ i, deformationSymbol o hkl (e i) (fderiv ℝ a x (e i)) := by
  simp [deformationOperator, canonicalCovariantTensor_eq_sum V e]

/-- The value of `δ₀ a` at `x` depends only on the derivative of `a` at `x`. -/
theorem deformationOperator_congr_fderiv {a b : V → V} {x : V}
    (h : fderiv ℝ a x = fderiv ℝ b x) :
    deformationOperator o hkl a x = deformationOperator o hkl b x := by
  rw [deformationOperator, deformationOperator, h]

/-- `δ₀` vanishes on constant fields. -/
@[simp]
theorem deformationOperator_const (b x : V) : deformationOperator o hkl (fun _ ↦ b) x = 0 := by
  simp [deformationOperator_eq_sum o hkl (stdOrthonormalBasis ℝ V)]

/-- **The scalar component of `δ₀` is the divergence**: `-d*a = tr (Da)`. -/
theorem deformationOperator_fst (a : V → V) (x : V) :
    (deformationOperator o hkl a x).1 = LinearMap.trace ℝ V (fderiv ℝ a x : V →ₗ[ℝ] V) := by
  rw [deformationOperator_eq_sum o hkl (stdOrthonormalBasis ℝ V),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ V), Prod.fst_sum]
  simp

/-- **`δ₀` takes values in `ℝ ⊕ Λ⁺`**: its two-form component is self-dual. -/
theorem hodgeStar_deformationOperator_snd (a : V → V) (x : V) :
    o.hodgeStar hkl (deformationOperator o hkl a x).2 = (deformationOperator o hkl a x).2 := by
  rw [deformationOperator_eq_sum o hkl (stdOrthonormalBasis ℝ V), Prod.snd_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hodgeStar_deformationSymbol_snd o hkl _ _

/-- `δ₀` is additive on fields differentiable at the point. -/
theorem deformationOperator_add {a b : V → V} {x : V} (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    deformationOperator o hkl (fun y ↦ a y + b y) x =
      deformationOperator o hkl a x + deformationOperator o hkl b x := by
  simp only [deformationOperator_eq_sum o hkl (stdOrthonormalBasis ℝ V), fderiv_fun_add ha hb,
    add_apply, map_add, Finset.sum_add_distrib]

/-- `δ₀` commutes with constant multiples of fields differentiable at the point. -/
theorem deformationOperator_const_smul (c : ℝ) {a : V → V} {x : V}
    (ha : DifferentiableAt ℝ a x) :
    deformationOperator o hkl (fun y ↦ c • a y) x = c • deformationOperator o hkl a x := by
  simp only [deformationOperator_eq_sum o hkl (stdOrthonormalBasis ℝ V),
    fderiv_fun_const_smul ha, smul_apply, map_smul, Finset.smul_sum]

/-- `δ₀` commutes with negation. -/
theorem deformationOperator_neg (a : V → V) (x : V) :
    deformationOperator o hkl (fun y ↦ -a y) x = -deformationOperator o hkl a x := by
  simp only [deformationOperator_eq_sum o hkl (stdOrthonormalBasis ℝ V), fderiv_fun_neg,
    neg_apply, map_neg, Finset.sum_neg_distrib]

/-- **The Leibniz rule for `δ₀`**: `δ₀ (f a) = f δ₀ a + σ_{∇f} (a)`. The commutator of `δ₀` with
multiplication by a function `f` is the principal symbol at the covector `df`, identified with the
gradient `∇f`. -/
theorem deformationOperator_smul {f : V → ℝ} {a : V → V} {x : V} (hf : DifferentiableAt ℝ f x)
    (ha : DifferentiableAt ℝ a x) :
    deformationOperator o hkl (fun y ↦ f y • a y) x =
      f x • deformationOperator o hkl a x + deformationSymbol o hkl (∇ f x) (a x) := by
  set e := stdOrthonormalBasis ℝ V
  -- `∇f = ∑ₖ (∂_{eₖ} f) eₖ`, so the symbol terms of the product rule add up to `σ_{∇f}`.
  have hgrad : ∇ f x = ∑ i, fderiv ℝ f x (e i) • e i := by
    conv_lhs => rw [← e.sum_repr' (∇ f x)]
    simp only [gradient, real_inner_comm _ (e _), toDual_symm_apply]
  have hfa : fderiv ℝ (fun y ↦ f y • a y) x =
      f x • fderiv ℝ a x + (fderiv ℝ f x).smulRight (a x) := fderiv_smul hf ha
  simp only [deformationOperator_eq_sum o hkl e, hfa, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    Finset.sum_add_distrib, Finset.smul_sum, hgrad, map_sum, LinearMap.sum_apply,
    LinearMap.smul_apply]

/-! ### The complex-linear part `δ_ω` -/

variable (J : V → AlmostComplexStructure V)

/-- **The complex-linear part of `δ₀`** for a field `J` of almost complex structures:
`δ_ω a = (δ₀ a - J′ δ₀ (J a)) / 2` at `x`, where `J a` is the field `y ↦ J y (a y)` and `J′` is the
complex structure of `ℝ ⊕ Λ⁺` determined by `J x` (`deformationComplexStructure`). -/
def complexDeformationOperator (a : V → V) (x : V) : ℝ × ⋀[ℝ]^2 V :=
  (2⁻¹ : ℝ) • (deformationOperator o hkl a x -
    deformationComplexStructure (J x) (deformationOperator o hkl (fun y ↦ J y (a y)) x))

/-- The defining formula `δ_ω a = (δ₀ a - J′ δ₀ (J a)) / 2`. -/
theorem complexDeformationOperator_def (a : V → V) (x : V) :
    complexDeformationOperator o hkl J a x = (2⁻¹ : ℝ) • (deformationOperator o hkl a x -
      deformationComplexStructure (J x) (deformationOperator o hkl (fun y ↦ J y (a y)) x)) :=
  (rfl)

/-- Applying the field `J` pointwise to a field `a`: the derivative of `J a` is `J x ∘ Da` plus the
derivative of `J` applied to `a x`. -/
private theorem fderiv_apply_apply {a : V → V} {x : V}
    (hJ : DifferentiableAt ℝ (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) x)
    (ha : DifferentiableAt ℝ a x)
    (v : V) :
    fderiv ℝ (fun y ↦ J y (a y)) x v =
      J x (fderiv ℝ a x v) +
        fderiv ℝ (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) x v (a x) := by
  have h := fderiv_clm_apply hJ ha
  simp only [LinearMap.coe_toContinuousLinearMap'] at h
  exact congrArg (· v) h

/-- The derivative of the field `y ↦ J y b` for a fixed vector `b`. -/
private theorem fderiv_apply_const {x : V}
    (hJ : DifferentiableAt ℝ (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) x) (b v : V) :
    fderiv ℝ (fun y ↦ J y b) x v =
      fderiv ℝ (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) x v b := by
  simpa using fderiv_apply_apply J hJ (differentiableAt_const b) v

/-- The field `y ↦ J y b` for a fixed vector `b` is differentiable where `J` is. -/
private theorem differentiableAt_apply_const {x : V}
    (hJ : DifferentiableAt ℝ (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) x) (b : V) :
    DifferentiableAt ℝ (fun y ↦ J y b) x := by
  simpa using hJ.clm_apply (differentiableAt_const b)

section Frame

variable {o} {e : OrthonormalBasis (Fin 4) ℝ V} (he : e.toBasis.orientation = o) {x : V}
  (h₀ : J x (e 0) = e 1) (h₂ : J x (e 2) = e 3)
include he h₀ h₂

/-- **`δ_ω` takes values in `ℝ ⊕ Λ⁺`**: its two-form component is self-dual. -/
theorem hodgeStar_complexDeformationOperator_snd (a : V → V) :
    o.hodgeStar hkl (complexDeformationOperator o hkl J a x).2 =
      (complexDeformationOperator o hkl J a x).2 := by
  have h := hodgeStar_deformationComplexStructure_snd hkl he h₀ h₂
    (hodgeStar_deformationOperator_snd o hkl (fun y ↦ J y (a y)) x)
  rw [complexDeformationOperator_def, Prod.smul_snd, Prod.snd_sub, map_smul, map_sub, h,
    hodgeStar_deformationOperator_snd]

/-- **`δ_ω` is complex linear**: `δ_ω (J a) = J′ (δ_ω a)`, with `J′` determined by `J x`, for
every field `a`, differentiable or not. -/
theorem complexDeformationOperator_apply_eq_deformationComplexStructure (a : V → V) :
    complexDeformationOperator o hkl J (fun y ↦ J y (a y)) x =
      deformationComplexStructure (J x) (complexDeformationOperator o hkl J a x) := by
  have hJJ : (fun y ↦ J y (J y (a y))) = fun y ↦ -a y := by
    funext y
    exact (J y).apply_apply (a y)
  have hsq := deformationComplexStructure_deformationComplexStructure hkl he h₀ h₂
    (hodgeStar_deformationOperator_snd o hkl (fun y ↦ J y (a y)) x)
  rw [complexDeformationOperator_def, complexDeformationOperator_def, hJJ,
    deformationOperator_neg, map_smul, map_sub, map_neg, hsq]
  abel_nf

/-- **`δ₀ - δ_ω` has order zero**: at `x`, `δ₀ a - δ_ω a = J′ δ₀ (J (a x)) / 2`, where `J (a x)`
is the field `y ↦ J y (a x)`. The right side involves `a` only through its value `a x`, and only
the derivative of `J` enters it. -/
theorem deformationOperator_sub_complexDeformationOperator {a : V → V}
    (hJ : DifferentiableAt ℝ (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) x)
    (ha : DifferentiableAt ℝ a x) :
    deformationOperator o hkl a x - complexDeformationOperator o hkl J a x =
      (2⁻¹ : ℝ) • deformationComplexStructure (J x)
        (deformationOperator o hkl (fun y ↦ J y (a x)) x) := by
  -- `δ₀ (J a) = J′ δ₀ a + δ₀ (J (a x))`: the symbol commutes `J x` past to `J′`.
  have hsplit : deformationOperator o hkl (fun y ↦ J y (a y)) x =
      deformationComplexStructure (J x) (deformationOperator o hkl a x) +
        deformationOperator o hkl (fun y ↦ J y (a x)) x := by
    simp only [deformationOperator_eq_sum o hkl e, fderiv_apply_apply J hJ ha,
      fderiv_apply_const J hJ, map_add, map_sum, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← LinearMap.comp_apply (deformationSymbol o hkl (e i)) (J x).toLinearMap,
      deformationSymbol_comp_toLinearMap hkl he h₀ h₂, LinearMap.comp_apply]
  have hsq := deformationComplexStructure_deformationComplexStructure hkl he h₀ h₂
    (hodgeStar_deformationOperator_snd o hkl a x)
  rw [complexDeformationOperator_def, hsplit, map_add, hsq]
  module

/-- `δ₀ - δ_ω` has order zero: at `x` it only depends on the value of the field at `x`. -/
theorem deformationOperator_sub_complexDeformationOperator_congr {a b : V → V}
    (hJ : DifferentiableAt ℝ (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) x)
    (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) (hab : a x = b x) :
    deformationOperator o hkl a x - complexDeformationOperator o hkl J a x =
      deformationOperator o hkl b x - complexDeformationOperator o hkl J b x := by
  rw [deformationOperator_sub_complexDeformationOperator hkl J he h₀ h₂ hJ ha,
    deformationOperator_sub_complexDeformationOperator hkl J he h₀ h₂ hJ hb, hab]

/-- Where `J` is stationary, `δ_ω` agrees with `δ₀`. -/
theorem complexDeformationOperator_eq_deformationOperator_of_hasFDerivAt {a : V → V}
    (hJ : HasFDerivAt (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) (0 : V →L[ℝ] V →L[ℝ] V) x)
    (ha : DifferentiableAt ℝ a x) :
    complexDeformationOperator o hkl J a x = deformationOperator o hkl a x := by
  have h := deformationOperator_sub_complexDeformationOperator hkl J he h₀ h₂
    hJ.differentiableAt ha
  rw [deformationOperator_congr_fderiv o hkl (a := fun y ↦ J y (a x)) (b := fun _ ↦ (0 : V))
    (by ext v; simp [fderiv_apply_const J hJ.differentiableAt, hJ.fderiv]),
    deformationOperator_const, map_zero, smul_zero, sub_eq_zero] at h
  exact h.symm

/-- **The Leibniz rule for `δ_ω`**: `δ_ω (f a) = f δ_ω a + σ_{∇f} (a)`. So `δ_ω` has the same
principal symbol as `δ₀` (`deformationOperator_smul`). -/
theorem complexDeformationOperator_smul {f : V → ℝ} {a : V → V}
    (hJ : DifferentiableAt ℝ (fun y ↦ (J y).toLinearMap.toContinuousLinearMap) x)
    (hf : DifferentiableAt ℝ f x)
    (ha : DifferentiableAt ℝ a x) :
    complexDeformationOperator o hkl J (fun y ↦ f y • a y) x =
      f x • complexDeformationOperator o hkl J a x + deformationSymbol o hkl (∇ f x) (a x) := by
  have hfa := deformationOperator_sub_complexDeformationOperator hkl J he h₀ h₂ hJ
    (a := fun y ↦ f y • a y) (hf.smul ha)
  have h := deformationOperator_sub_complexDeformationOperator hkl J he h₀ h₂ hJ ha
  have hJfa : deformationOperator o hkl (fun y ↦ J y (f x • a x)) x =
      f x • deformationOperator o hkl (fun y ↦ J y (a x)) x := by
    simp only [AlmostComplexStructure.apply_smul]
    exact deformationOperator_const_smul o hkl _ (differentiableAt_apply_const J hJ (a x))
  rw [hJfa, deformationOperator_smul o hkl hf ha, map_smul] at hfa
  linear_combination (norm := module) f x • h - hfa

end Frame

end TauCeti.SeibergWitten
