/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.UniformConvergence
public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Full
public import TauCeti.Analysis.CStarAlgebra.Multiplier

/-!
# The canonical multipliers of the full crossed product

Let `α` be a point-norm continuous action of a locally compact group `G` on a possibly nonunital
C⋆-algebra `A`, and let `μ` be a left Haar measure on `G`. The coefficient algebra and the group
act on the twisted convolution algebra `C_c(G, A)` by the left multipliers

`(i_A(a) f)(s) = a * f(s)` and `(i_G(r) f)(s) = α r (f (r⁻¹ * s))`.

These actions are bounded for the full C⋆-seminorm, so they extend to the full crossed product
`A ⋊_α G`. Their adjoints for the pairing `(x, y) ↦ x⋆ * y` are `i_A(a⋆)` and `i_G(r⁻¹)`, which
makes them left centralizers of multipliers of `A ⋊_α G`. This gives

* the canonical coefficient map `FullCrossedProduct.coefficientMultiplier`, a ⋆-homomorphism
  `A →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)`;
* the canonical group map `FullCrossedProduct.groupMultiplier`, a group homomorphism from `G` into
  the unitary multipliers of `A ⋊_α G`.

The two maps are covariant, `i_G(r) i_A(a) = i_A(α r a) i_G(r)`, and the group map is strictly
continuous: for every `x` in the crossed product, both `r ↦ i_G(r) x` and `r ↦ x i_G(r)` are norm
continuous. Under the extension `π ⋊ U` of the integrated form of a covariant representation
`(π, U)`, the left actions of `i_A(a)` and `i_G(r)` become left multiplication by `π(a)` and
`U_r`, and their right actions become right multiplication by them.

No unit, separability, σ-finiteness or nondegeneracy is assumed.

## Main definitions

* `TauCeti.CStarAction.FullCrossedProduct.coefficientMultiplier`: the canonical coefficient map
  `A →⋆ₙₐ[ℂ] 𝓜(ℂ, A ⋊_α G)`.
* `TauCeti.CStarAction.FullCrossedProduct.groupMultiplier`: the canonical unitary group map
  `G →* unitary 𝓜(ℂ, A ⋊_α G)`.

## Main statements

* `TauCeti.CStarAction.FullCrossedProduct.groupMultiplier_mul_coefficientMultiplier`: covariance.
* `TauCeti.CStarAction.FullCrossedProduct.continuous_groupMultiplier_fst_apply` and
  `TauCeti.CStarAction.FullCrossedProduct.continuous_groupMultiplier_snd_apply`: strict continuity
  of the group map.
* `TauCeti.CStarAction.CovariantRepresentation.integratedFull_coefficientMultiplier_fst` and
  `TauCeti.CStarAction.CovariantRepresentation.integratedFull_groupMultiplier_fst`, with their
  right-action counterparts `integratedFull_coefficientMultiplier_snd` and
  `integratedFull_groupMultiplier_snd`: the extended integrated forms turn the canonical
  multipliers into the given covariant pair.

## References

* Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2 (the canonical maps `i_A` and
  `i_G` of the full crossed product into its multiplier algebra).
-/

public section

noncomputable section

open MeasureTheory UniformSpace Filter Topology
open scoped MultiplierAlgebra CStarAlgebra

namespace TauCeti.CStarAction

universe u v

variable {G : Type u} {A : Type v} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

namespace FullCrossedProduct

open FullConvolutionAlgebra ConvolutionAlgebra

/-- A linear operator on the twisted convolution algebra that is bounded for the full seminorm,
extended by continuity to the full crossed product. -/
private def extendCLM (T : ConvolutionAlgebra α μ →ₗ[ℂ] ConvolutionAlgebra α μ) (C : ℝ)
    (hT : ∀ f, fullSeminorm α μ (T f) ≤ C * fullSeminorm α μ f) :
    FullCrossedProduct α μ →L[ℂ] FullCrossedProduct α μ :=
  (((toFullStarAlgEquiv α μ : ConvolutionAlgebra α μ →ₗ[ℂ] FullConvolutionAlgebra α μ).comp
    (T.comp ((toFullStarAlgEquiv α μ).symm :
      FullConvolutionAlgebra α μ →ₗ[ℂ] ConvolutionAlgebra α μ))).mkContinuous C fun f => by
        simpa [FullConvolutionAlgebra.norm_def] using hT (ofFull f)).completion

private theorem extendCLM_of (T : ConvolutionAlgebra α μ →ₗ[ℂ] ConvolutionAlgebra α μ) (C : ℝ)
    (hT : ∀ f, fullSeminorm α μ (T f) ≤ C * fullSeminorm α μ f) (f : ConvolutionAlgebra α μ) :
    extendCLM T C hT (of α μ f) = of α μ (T f) := by
  rw [← coe_toFull_eq_of, ← coe_toFull_eq_of, extendCLM]
  exact (ContinuousLinearMap.completion_apply_coe _ _).trans (by simp [-coe_toFull_eq_of])

/-- Extended operators are adjoint for the pairing `(x, y) ↦ x⋆ * y` as soon as their integrated
forms are adjoint on the twisted convolution algebra. -/
private theorem star_extendCLM_mul {T T' : ConvolutionAlgebra α μ →ₗ[ℂ] ConvolutionAlgebra α μ}
    {C C' : ℝ} {hT : ∀ f, fullSeminorm α μ (T f) ≤ C * fullSeminorm α μ f}
    {hT' : ∀ f, fullSeminorm α μ (T' f) ≤ C' * fullSeminorm α μ f}
    (h : ∀ f g (H : Type (max u v)) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (P : CovariantRepresentation α H),
        P.integratedStarAlgHom μ (star (T' f) * g) = P.integratedStarAlgHom μ (star f * T g))
    (x y : FullCrossedProduct α μ) :
    star (extendCLM T' C' hT' x) * y = star x * extendCLM T C hT y := by
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih f =>
    induction y using induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih g =>
      rw [extendCLM_of, extendCLM_of]
      simp only [← map_star (of α μ), ← map_mul (of α μ)]
      exact of_eq_of_iff.2 (h f g)

/-- A multiplier of the full crossed product is determined by its left action on the twisted
convolution algebra. -/
private theorem multiplier_ext {m n : 𝓜(ℂ, FullCrossedProduct α μ)}
    (h : ∀ f, m.fst (of α μ f) = n.fst (of α μ f)) : m = n :=
  DoubleCentralizer.ext_fst fun x => congr($(continuousLinearMap_ext h) x)

/-! ### The coefficient map -/

/-- Left multiplication by a coefficient, extended to the full crossed product. -/
private def coefficientCLM (a : A) : FullCrossedProduct α μ →L[ℂ] FullCrossedProduct α μ :=
  extendCLM (coefficientMul (α := α) (μ := μ) a).toLinearMap ‖a‖
    (fullSeminorm_coefficientMul_le a)

private theorem coefficientCLM_of (a : A) (f : ConvolutionAlgebra α μ) :
    coefficientCLM a (of α μ f) = of α μ (coefficientMul a f) := by
  rw [coefficientCLM, extendCLM_of, ContinuousLinearMap.coe_coe]

/-- The adjoint of left multiplication by `a⋆` is left multiplication by `a`. -/
private theorem star_coefficientCLM_mul (a : A) (x y : FullCrossedProduct α μ) :
    star (coefficientCLM (star a) x) * y = star x * coefficientCLM a y :=
  star_extendCLM_mul (fun f g H _ _ _ P => by simp [map_star, mul_assoc]) x y

variable (α μ) in
/-- The canonical coefficient map `i_A` of `A` into the multiplier algebra of the full crossed
product. The multiplier `i_A(a)` acts on the left of the twisted convolution algebra by
`(i_A(a) f)(s) = a * f(s)`. -/
def coefficientMultiplier : A →⋆ₙₐ[ℂ] 𝓜(ℂ, FullCrossedProduct α μ) where
  toFun a := .ofAdjoint (coefficientCLM a) (coefficientCLM (star a)) (star_coefficientCLM_mul a)
  map_smul' c a := multiplier_ext fun f => by simp [coefficientCLM_of]
  map_zero' := multiplier_ext fun f => by simp [coefficientCLM_of]
  map_add' a b := multiplier_ext fun f => by simp [coefficientCLM_of]
  map_mul' a b := multiplier_ext fun f => by simp [coefficientCLM_of]
  map_star' a := DoubleCentralizer.ext_fst fun x => by
    simp only [DoubleCentralizer.star_ofAdjoint, DoubleCentralizer.ofAdjoint_fst]

private theorem coefficientMultiplier_fst (a : A) :
    (coefficientMultiplier α μ a).fst = coefficientCLM a :=
  DoubleCentralizer.ofAdjoint_fst

private theorem coefficientMultiplier_snd_apply (a : A) (x : FullCrossedProduct α μ) :
    (coefficientMultiplier α μ a).snd x = star (coefficientCLM (star a) (star x)) :=
  DoubleCentralizer.ofAdjoint_snd_apply x

/-- The canonical coefficient multiplier `i_A(a)` multiplies an element of the twisted
convolution algebra pointwise on the left by `a`. -/
@[simp]
theorem coefficientMultiplier_fst_of (a : A) (f : ConvolutionAlgebra α μ) :
    (coefficientMultiplier α μ a).fst (of α μ f) = of α μ (coefficientMul a f) := by
  rw [coefficientMultiplier_fst, coefficientCLM_of]

/-- The right action of the canonical coefficient multiplier `i_A(a)` on the twisted convolution
algebra is the adjoint of left multiplication by `a⋆`. -/
@[simp]
theorem coefficientMultiplier_snd_of (a : A) (f : ConvolutionAlgebra α μ) :
    (coefficientMultiplier α μ a).snd (of α μ f) =
      star (of α μ (coefficientMul (star a) (star f))) := by
  rw [coefficientMultiplier_snd_apply, ← map_star (of α μ), coefficientCLM_of]

/-! ### The group map -/

/-- Twisted left translation, extended to the full crossed product. -/
private def translateCLM (r : G) : FullCrossedProduct α μ →L[ℂ] FullCrossedProduct α μ :=
  extendCLM (translateLIE r).toLinearEquiv.toLinearMap 1 fun f => by simp

private theorem translateCLM_of (r : G) (f : ConvolutionAlgebra α μ) :
    translateCLM r (of α μ f) = of α μ (translateLIE r f) := by
  rw [translateCLM, extendCLM_of, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]

private theorem translateCLM_one : translateCLM (α := α) (μ := μ) 1 = 1 :=
  continuousLinearMap_ext fun f => by simp [translateCLM_of]

private theorem translateCLM_mul (r t : G) :
    translateCLM (α := α) (μ := μ) (r * t) = translateCLM r * translateCLM t :=
  continuousLinearMap_ext fun f => by
    simp [translateCLM_of, translateLIE_mul, LinearIsometryEquiv.coe_mul]

private theorem norm_translateCLM_apply (r : G) (x : FullCrossedProduct α μ) :
    ‖translateCLM r x‖ = ‖x‖ := by
  induction x using induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_norm
  | ih f => simp [translateCLM_of]

/-- The adjoint of translation by `r⁻¹` is translation by `r`. -/
private theorem star_translateCLM_mul (r : G) (x y : FullCrossedProduct α μ) :
    star (translateCLM r⁻¹ x) * y = star x * translateCLM r y :=
  star_extendCLM_mul (fun f g H _ _ _ P => by
    simp only [map_mul, map_star, CovariantRepresentation.integratedStarAlgHom_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, ofConv_translateLIE,
      CovariantRepresentation.integratedOperator_translate, star_mul, mul_assoc]
    rw [ContinuousLinearMap.star_eq_adjoint (P.group r⁻¹), P.isUnitary.adjoint_eq_inv, inv_inv])
    x y

/-- The multiplier with left centralizer the extended translation by `r`. -/
private def groupMultiplierAux (r : G) : 𝓜(ℂ, FullCrossedProduct α μ) :=
  .ofAdjoint (translateCLM r) (translateCLM r⁻¹) (star_translateCLM_mul r)

private theorem groupMultiplierAux_mem_unitary (r : G) :
    groupMultiplierAux (α := α) (μ := μ) r ∈ unitary 𝓜(ℂ, FullCrossedProduct α μ) := by
  rw [Unitary.mem_iff]
  constructor <;> refine DoubleCentralizer.ext_fst fun x => ?_ <;>
    simp [groupMultiplierAux, ← translateCLM_mul, translateCLM_one]

variable (α μ) in
/-- The canonical group map `i_G` of `G` into the unitary multipliers of the full crossed
product. The multiplier `i_G(r)` acts on the left of the twisted convolution algebra by twisted
left translation, `(i_G(r) f)(s) = α r (f (r⁻¹ * s))`. -/
def groupMultiplier : G →* unitary 𝓜(ℂ, FullCrossedProduct α μ) where
  toFun r := ⟨groupMultiplierAux r, groupMultiplierAux_mem_unitary r⟩
  map_one' := Subtype.ext <| DoubleCentralizer.ext_fst fun x => by
    simp [groupMultiplierAux, translateCLM_one]
  map_mul' r t := Subtype.ext <| DoubleCentralizer.ext_fst fun x => by
    simp [groupMultiplierAux, translateCLM_mul]

private theorem groupMultiplier_fst (r : G) :
    (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).fst = translateCLM r :=
  DoubleCentralizer.ofAdjoint_fst

private theorem groupMultiplier_snd_apply (r : G) (x : FullCrossedProduct α μ) :
    (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).snd x =
      star (translateCLM r⁻¹ (star x)) :=
  DoubleCentralizer.ofAdjoint_snd_apply x

/-- The canonical group multiplier `i_G(r)` acts on the twisted convolution algebra by twisted
left translation. -/
@[simp]
theorem groupMultiplier_fst_of (r : G) (f : ConvolutionAlgebra α μ) :
    (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).fst (of α μ f) =
      of α μ (translateLIE r f) := by
  rw [groupMultiplier_fst, translateCLM_of]

/-- The right action of the canonical group multiplier `i_G(r)` on the twisted convolution
algebra is the adjoint of twisted left translation by `r⁻¹`. -/
@[simp]
theorem groupMultiplier_snd_of (r : G) (f : ConvolutionAlgebra α μ) :
    (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).snd (of α μ f) =
      star (of α μ (translateLIE r⁻¹ (star f))) := by
  rw [groupMultiplier_snd_apply, ← map_star (of α μ), translateCLM_of]

/-- The canonical coefficient and group maps are covariant:
`i_G(r) i_A(a) = i_A(α r a) i_G(r)`. -/
theorem groupMultiplier_mul_coefficientMultiplier (r : G) (a : A) :
    (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)) * coefficientMultiplier α μ a =
      coefficientMultiplier α μ (α r a) * groupMultiplier α μ r :=
  multiplier_ext fun f => by
    simp [groupMultiplier_fst, translateCLM_of, translateLIE_coefficientMul]

/-- The canonical group map is strictly continuous on the left: `r ↦ i_G(r) x` is norm
continuous for every `x` in the full crossed product. -/
theorem continuous_groupMultiplier_fst_apply (x : FullCrossedProduct α μ) :
    Continuous fun r => (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).fst x := by
  simp only [groupMultiplier_fst]
  -- The extended translations are isometries, hence an equicontinuous family, so convergence of
  -- the orbits passes from the dense twisted convolution algebra to its completion.
  have hequi : Equicontinuous fun r : G => ⇑(translateCLM (α := α) (μ := μ) r) :=
    (LipschitzWith.uniformEquicontinuous _ 1 fun r =>
      (AddMonoidHomClass.isometry_of_norm (translateCLM r)
        (norm_translateCLM_apply r)).lipschitzWith).equicontinuous
  refine continuous_iff_continuousAt.2 fun r => ?_
  induction x using induction_on with
  | hp => exact hequi.isClosed_setOfPred_tendsto (translateCLM r).continuous
  | ih f =>
    simp only [ContinuousAt, translateCLM_of]
    exact (continuous_of.comp (continuous_translateLIE f)).continuousAt

/-- The canonical group map is strictly continuous on the right: `r ↦ x i_G(r)` is norm
continuous for every `x` in the full crossed product. -/
theorem continuous_groupMultiplier_snd_apply (x : FullCrossedProduct α μ) :
    Continuous fun r => (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).snd x := by
  simp only [groupMultiplier_snd_apply]
  have h := (continuous_groupMultiplier_fst_apply (α := α) (μ := μ) (star x)).comp continuous_inv
  simp only [groupMultiplier_fst] at h
  exact h.star

end FullCrossedProduct

namespace CovariantRepresentation

open FullCrossedProduct

variable {H : Type (max u v)} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (P : CovariantRepresentation α H)

/-- The extended integrated form turns the canonical coefficient multiplier `i_A(a)` into the
coefficient representation: `(π ⋊ U)(i_A(a) x) = π(a) (π ⋊ U)(x)`. -/
@[simp]
theorem integratedFull_coefficientMultiplier_fst (a : A) (x : FullCrossedProduct α μ) :
    P.integratedFull μ ((coefficientMultiplier α μ a).fst x) =
      P.coefficient a * P.integratedFull μ x := by
  induction x using induction_on with
  | hp =>
    exact isClosed_eq
      ((map_continuous (P.integratedFull μ)).comp (ContinuousLinearMap.continuous _))
      (continuous_const.mul (map_continuous _))
  | ih f => simp

/-- The extended integrated form turns the canonical group multiplier `i_G(r)` into the group
representation: `(π ⋊ U)(i_G(r) x) = U_r (π ⋊ U)(x)`. -/
@[simp]
theorem integratedFull_groupMultiplier_fst (r : G) (x : FullCrossedProduct α μ) :
    P.integratedFull μ ((groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).fst x) =
      P.group r * P.integratedFull μ x := by
  induction x using induction_on with
  | hp =>
    exact isClosed_eq
      ((map_continuous (P.integratedFull μ)).comp (ContinuousLinearMap.continuous _))
      (continuous_const.mul (map_continuous _))
  | ih f => simp

/-- The extended integrated form turns the right action of the canonical coefficient multiplier
`i_A(a)` into right multiplication by the coefficient representation:
`(π ⋊ U)(x i_A(a)) = (π ⋊ U)(x) π(a)`. -/
@[simp]
theorem integratedFull_coefficientMultiplier_snd (a : A) (x : FullCrossedProduct α μ) :
    P.integratedFull μ ((coefficientMultiplier α μ a).snd x) =
      P.integratedFull μ x * P.coefficient a := by
  have h : (coefficientMultiplier α μ a).snd x =
      star ((coefficientMultiplier α μ (star a)).fst (star x)) := by
    rw [coefficientMultiplier_snd_apply, coefficientMultiplier_fst]
  rw [h, map_star, integratedFull_coefficientMultiplier_fst]
  simp [star_mul, map_star (P.integratedFull μ), map_star P.coefficient]

/-- The extended integrated form turns the right action of the canonical group multiplier
`i_G(r)` into right multiplication by the group representation:
`(π ⋊ U)(x i_G(r)) = (π ⋊ U)(x) U_r`. -/
@[simp]
theorem integratedFull_groupMultiplier_snd (r : G) (x : FullCrossedProduct α μ) :
    P.integratedFull μ ((groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).snd x) =
      P.integratedFull μ x * P.group r := by
  have h : (groupMultiplier α μ r : 𝓜(ℂ, FullCrossedProduct α μ)).snd x =
      star ((groupMultiplier α μ r⁻¹ : 𝓜(ℂ, FullCrossedProduct α μ)).fst (star x)) := by
    rw [groupMultiplier_snd_apply, groupMultiplier_fst]
  rw [h, map_star, integratedFull_groupMultiplier_fst]
  simp [star_mul, map_star (P.integratedFull μ), ContinuousLinearMap.star_eq_adjoint (P.group r⁻¹),
    P.isUnitary.adjoint_eq_inv]

end CovariantRepresentation

end TauCeti.CStarAction
