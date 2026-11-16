/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Operator
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Reaction
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
import TauCeti.Analysis.InnerProductSpace.Trace.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# Hamilton's `#` product and the bivector-operator identity `Q(R) = 2(R² + R#)`

On the exterior square `⋀[ℝ]^2 V` of a finite-dimensional real inner product space `V`, we define
Hamilton's symmetric bilinear Lie-algebraic product `TauCeti.FourTensor.sharpBilin A B` and
`TauCeti.FourTensor.sharp A = sharpBilin A A` using the bivector Lie bracket
`TauCeti.twoVectorBracket`,
```
⟪sharpBilin A B ξ, η⟫ = (1 / 2) ∑_α ∑_β ⟪[A ω_α, B ω_β], ξ⟫ ⟪[ω_α, ω_β], η⟫.
```
We prove that `sharpBilin` and `sharp` preserve symmetry, evaluate `sharp 1 = (dim V - 2) • 1`,
and establish the polarized and quadratic bivector-operator identities
`Q(ofExteriorEnd A) = ofExteriorEnd (2 • (A * A + sharp A))` and
`toExteriorEnd (Q(r)) = 2 • (R² + R#)` for every symmetric endomorphism `A` of `⋀[ℝ]^2 V` and
every algebraic curvature tensor `r`. As immediate checks,
`Q(constantCurvature V) = 2 (dim V - 1) • constantCurvature V` and
`Q(bivectorSq e₁ e₂) = 2 • bivectorSq e₁ e₂` for an orthonormal pair `e₁, e₂` (the curvature
tensor of `S² × ℝ^(n - 2)`).

## Main definitions

* `TauCeti.FourTensor.sharpBilin` and `TauCeti.FourTensor.sharp`: Hamilton's Lie-algebraic `#`
  product on `Module.End ℝ (⋀[ℝ]^2 V)`.
* `TauCeti.FourTensor.bivectorSq`: the rank-one algebraic curvature tensor `(e₁ ∧ e₂) ⊗ (e₁ ∧ e₂)`.

## Main statements

* `TauCeti.FourTensor.inner_sharpBilin_orthonormalBasis`: basis formula for `sharpBilin`.
* `TauCeti.FourTensor.isSymmetric_sharpBilin` and `TauCeti.FourTensor.isSymmetric_sharp`:
  preservation of symmetry.
* `TauCeti.FourTensor.sharp_one`: `sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) = (dim V - 2) • 1`.
* `TauCeti.FourTensor.ofExteriorEnd_reactionBilin`, `TauCeti.FourTensor.ofExteriorEnd_reaction`,
  `TauCeti.FourTensor.toExteriorEnd_reactionTensor`, and
  `TauCeti.FourTensor.IsAlgebraicCurvature.toExteriorEnd_reactionTensor`: the operator identity
  `Q(R) = 2 (R² + R#)`.
* `TauCeti.FourTensor.reactionTensor_constantCurvature` and
  `TauCeti.FourTensor.reactionTensor_bivectorSq_of_orthonormal`: the round-sphere and
  `S² × ℝ^(n - 2)` checks.

## References

* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179, Section 4.
* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*, Ann. of
  Math. 167 (2008), 1079–1097, Section 2.
* S. Brendle and R. Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307, Section 2.
-/

public section

open exteriorPower
open LinearMap (BilinForm)
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Hamilton's `#` product -/

/-- Inner bilinear form `(β₁, β₂) ↦ ⟪[A α₁, B β₁], ξ⟫ ⟪[α₂, β₂], η⟫` on `⋀[ℝ]^2 V`. -/
private def sharpInner (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η α₁ α₂ : ⋀[ℝ]^2 V) :
    BilinForm ℝ (⋀[ℝ]^2 V) :=
  (LinearMap.mul ℝ ℝ).compl₁₂
    (((innerₗ (⋀[ℝ]^2 V)).flip ξ).comp ((twoVectorBracket (A α₁)).comp B))
    (((innerₗ (⋀[ℝ]^2 V)).flip η).comp (twoVectorBracket α₂))

private theorem sharpInner_apply (A B : Module.End ℝ (⋀[ℝ]^2 V))
    (ξ η α₁ α₂ β₁ β₂ : ⋀[ℝ]^2 V) :
    sharpInner A B ξ η α₁ α₂ β₁ β₂ =
      ⟪twoVectorBracket (A α₁) (B β₁), ξ⟫ * ⟪twoVectorBracket α₂ β₂, η⟫ := rfl

/-- Outer bilinear form `(α₁, α₂) ↦ tr_β (⟪[A α₁, B β], ξ⟫ ⟪[α₂, β], η⟫)` on `⋀[ℝ]^2 V`. -/
private def sharpOuter (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    BilinForm ℝ (⋀[ℝ]^2 V) :=
  LinearMap.mk₂ ℝ (fun α₁ α₂ ↦ bilinFormTrace (sharpInner A B ξ η α₁ α₂))
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; refine LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ?_
      simp only [LinearMap.add_apply, sharpInner_apply, map_add, inner_add_left]; ring)
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; refine LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ?_
      simp only [LinearMap.smul_apply, smul_eq_mul, sharpInner_apply, map_smul,
        real_inner_smul_left]; ring)
    (fun _ _ _ ↦ by
      rw [← map_add]; congr 1; refine LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ?_
      simp only [LinearMap.add_apply, sharpInner_apply, map_add, inner_add_left]; ring)
    (fun _ _ _ ↦ by
      rw [← map_smul]; congr 1; refine LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ?_
      simp only [LinearMap.smul_apply, smul_eq_mul, sharpInner_apply, map_smul,
        real_inner_smul_left]; ring)

private def sharpVal (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) : ℝ :=
  (1 / 2 : ℝ) * bilinFormTrace (sharpOuter A B ξ η)

private theorem sharpVal_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (⋀[ℝ]^2 V))
    (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    sharpVal A B ξ η =
      (1 / 2 : ℝ) * ∑ α, ∑ β,
        ⟪twoVectorBracket (A (e α)) (B (e β)), ξ⟫ * ⟪twoVectorBracket (e α) (e β), η⟫ := by
  simp only [sharpVal, bilinFormTrace_eq_sum _ e, sharpOuter, LinearMap.mk₂_apply, sharpInner_apply]

private theorem sharpVal_eq_sum_ιMulti {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    sharpVal A B ξ η =
      (1 / 8 : ℝ) * ∑ i, ∑ j, ∑ k, ∑ l,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
          ⟪twoVectorBracket (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b k, b l]), η⟫ := by
  have h4 :
      (∑ i, ∑ j, ∑ k, ∑ l,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
          ⟪twoVectorBracket (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b k, b l]), η⟫) =
        4 * bilinFormTrace (sharpOuter A B ξ η) := by
    calc
      _ = ∑ i, ∑ j, 2 * bilinFormTrace
            (sharpInner A B ξ η (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b i, b j])) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
            simpa only [sharpInner_apply] using
              b.sum_bilinForm_ιMulti_two
                (sharpInner A B ξ η (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b i, b j]))
      _ = 2 * (∑ i, ∑ j,
            sharpOuter A B ξ η (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b i, b j])) := by
          simp only [sharpOuter, LinearMap.mk₂_apply, Finset.mul_sum]
      _ = 4 * bilinFormTrace (sharpOuter A B ξ η) := by
          rw [b.sum_bilinForm_ιMulti_two (sharpOuter A B ξ η)]; ring
  rw [sharpVal, h4]; ring

private def sharpForm (A B : Module.End ℝ (⋀[ℝ]^2 V)) : BilinForm ℝ (⋀[ℝ]^2 V) :=
  LinearMap.mk₂ ℝ (fun ξ η ↦ sharpVal A B ξ η)
    (fun _ _ _ ↦ by simp only [sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), inner_add_right,
      add_mul, Finset.sum_add_distrib]; ring)
    (fun _ _ _ ↦ by simp only [sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)),
      real_inner_smul_right, smul_eq_mul, mul_assoc, ← Finset.mul_sum]; ring)
    (fun _ _ _ ↦ by simp only [sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), inner_add_right,
      mul_add, Finset.sum_add_distrib])
    (fun c _ _ ↦ by
      have hm (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
      simp only [sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), real_inner_smul_right,
        smul_eq_mul, hm, ← Finset.mul_sum])

/-- Hamilton's symmetric bilinear Lie-algebraic `#` product on `Module.End ℝ (⋀[ℝ]^2 V)`,
characterized in any orthonormal basis `e` of `⋀[ℝ]^2 V` by
`⟪sharpBilin A B ξ, η⟫ = (1 / 2) ∑ α β, ⟪[A (e α), B (e β)], ξ⟫ ⟪[e α, e β], η⟫`. -/
def sharpBilin :
    Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) where
  toFun A :=
    { toFun := fun B ↦
        (InnerProductSpace.toDual ℝ (⋀[ℝ]^2 V)).symm.toLinearEquiv.toLinearMap ∘ₗ
          (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ sharpForm A B)
      map_add' := fun _ _ ↦ LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
          LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply,
          LinearMap.add_apply, inner_add_left, sharpForm, LinearMap.mk₂_apply,
          sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), map_add, add_mul,
          Finset.sum_add_distrib]; ring
      map_smul' := fun _ _ ↦ LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
          LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply,
          LinearMap.smul_apply, RingHom.id_apply, real_inner_smul_left, sharpForm,
          LinearMap.mk₂_apply, sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), map_smul,
          mul_assoc, ← Finset.mul_sum]; ring }
  map_add' _ _ := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply, inner_add_left,
      sharpForm, LinearMap.mk₂_apply, sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)),
      map_add, add_mul, Finset.sum_add_distrib]; ring
  map_smul' _ _ := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearMap.coe_toContinuousLinearMap', InnerProductSpace.toDual_symm_apply,
      real_inner_smul_left, sharpForm, LinearMap.mk₂_apply,
      sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), map_smul, mul_assoc,
      ← Finset.mul_sum]; ring

/-- Hamilton's quadratic `#` operator `A# = sharpBilin A A` on `Module.End ℝ (⋀[ℝ]^2 V)`. -/
def sharp (A : Module.End ℝ (⋀[ℝ]^2 V)) : Module.End ℝ (⋀[ℝ]^2 V) :=
  sharpBilin A A

private theorem inner_sharpBilin_eq_sharpVal (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    ⟪sharpBilin A B ξ, η⟫ = sharpVal A B ξ η := by
  simp [sharpBilin, sharpForm]

/-- Evaluation of `sharpBilin A B` in any orthonormal basis of `⋀[ℝ]^2 V`. -/
theorem inner_sharpBilin_orthonormalBasis {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (⋀[ℝ]^2 V)) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    ⟪sharpBilin A B ξ, η⟫ =
      (1 / 2 : ℝ) * ∑ α, ∑ β,
        ⟪twoVectorBracket (A (e α)) (B (e β)), ξ⟫ * ⟪twoVectorBracket (e α) (e β), η⟫ := by
  rw [inner_sharpBilin_eq_sharpVal, sharpVal_eq_sum e]

/-- `sharpBilin` is symmetric in its two endomorphism arguments. -/
theorem sharpBilin_comm (A B : Module.End ℝ (⋀[ℝ]^2 V)) : sharpBilin A B = sharpBilin B A := by
  let e := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  rw [inner_sharpBilin_orthonormalBasis e, inner_sharpBilin_orthonormalBasis e]
  congr 1; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦ by
    rw [twoVectorBracket_swap (B (e α)) (A (e β)), twoVectorBracket_swap (e α) (e β),
      inner_neg_left, inner_neg_left, neg_mul_neg]

/-- The diagonal of `sharpBilin` is `sharp`. -/
@[simp]
theorem sharpBilin_self (A : Module.End ℝ (⋀[ℝ]^2 V)) : sharpBilin A A = sharp A :=
  (rfl)

/-- `sharp 0 = 0`. -/
@[simp]
theorem sharp_zero : sharp (0 : Module.End ℝ (⋀[ℝ]^2 V)) = 0 := by
  simp [sharp]

/-- `sharp (-A) = sharp A`. -/
@[simp]
theorem sharp_neg (A : Module.End ℝ (⋀[ℝ]^2 V)) : sharp (-A) = sharp A := by
  simp only [sharp, map_neg, LinearMap.neg_apply, neg_neg]

/-- `sharp (c • A) = c ^ 2 • sharp A`. -/
@[simp]
theorem sharp_smul (c : ℝ) (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    sharp (c • A) = (c ^ 2) • sharp A := by
  simp only [sharp, map_smul, LinearMap.smul_apply, smul_smul, sq]

/-- Every rank-one self-adjoint operator on `⋀[ℝ]^2 V` has vanishing `#`-square, since its image
is at most one-dimensional and hence abelian under `twoVectorBracket`. -/
theorem sharp_rankOne_self (α : ⋀[ℝ]^2 V) :
    sharp (InnerProductSpace.rankOne ℝ α α).toLinearMap = 0 := by
  refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  rw [← sharpBilin_self, inner_sharpBilin_orthonormalBasis (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V))]
  simp [InnerProductSpace.rankOne_apply]

private theorem sharpBilin_sum_expand {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (⋀[ℝ]^2 V)) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (x y : ⋀[ℝ]^2 V) :
    (∑ α, ∑ β, ⟪twoVectorBracket (A (e α)) (B (e β)), x⟫ * ⟪twoVectorBracket (e α) (e β), y⟫) =
      ∑ α, ∑ β, ∑ γ, ∑ δ,
        ⟪e γ, A (e α)⟫ * ⟪e δ, B (e β)⟫ *
          ⟪twoVectorBracket (e γ) (e δ), x⟫ * ⟪twoVectorBracket (e α) (e β), y⟫ := by
  refine Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦ ?_
  conv_lhs => rw [← e.sum_repr' (A (e α)), ← e.sum_repr' (B (e β))]
  rw [map_sum, sum_inner, Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  simp only [map_sum, LinearMap.sum_apply, sum_inner, map_smul, LinearMap.smul_apply,
    real_inner_smul_left, Finset.mul_sum]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun δ _ ↦ by ring

/-- The `#` product of two symmetric endomorphisms of `⋀[ℝ]^2 V` is symmetric. -/
theorem isSymmetric_sharpBilin {A B : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) : (sharpBilin A B).IsSymmetric := by
  let e := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  intro ξ η
  rw [real_inner_comm (sharpBilin A B η) ξ, inner_sharpBilin_orthonormalBasis e,
    inner_sharpBilin_orthonormalBasis e]
  congr 1
  rw [sharpBilin_sum_expand e A B ξ η, sharpBilin_sum_expand e A B η ξ]
  have hsym (α β γ δ) :
      ⟪e γ, A (e α)⟫ * ⟪e δ, B (e β)⟫ *
        ⟪twoVectorBracket (e γ) (e δ), ξ⟫ * ⟪twoVectorBracket (e α) (e β), η⟫ =
      ⟪e α, A (e γ)⟫ * ⟪e β, B (e δ)⟫ *
        ⟪twoVectorBracket (e α) (e β), η⟫ * ⟪twoVectorBracket (e γ) (e δ), ξ⟫ := by
    rw [← hA (e γ) (e α), real_inner_comm (A (e γ)), ← hB (e δ) (e β),
      real_inner_comm (B (e δ))]; ring
  simp_rw [hsym]
  trans ∑ α, ∑ γ, ∑ β, ∑ δ, ⟪e α, A (e γ)⟫ * ⟪e β, B (e δ)⟫ *
      ⟪twoVectorBracket (e α) (e β), η⟫ * ⟪twoVectorBracket (e γ) (e δ), ξ⟫
  · exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  trans ∑ γ, ∑ α, ∑ δ, ∑ β, ⟪e α, A (e γ)⟫ * ⟪e β, B (e δ)⟫ *
      ⟪twoVectorBracket (e α) (e β), η⟫ * ⟪twoVectorBracket (e γ) (e δ), ξ⟫
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- The `#`-square of a symmetric endomorphism of `⋀[ℝ]^2 V` is symmetric. -/
theorem isSymmetric_sharp {A : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) :
    (sharp A).IsSymmetric :=
  isSymmetric_sharpBilin hA hA

/-! ### The bivector-operator identity `Q(R) = 2(R² + R#)` -/

private theorem sum_inner_twoVectorBracket_contract {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ x y : ⋀[ℝ]^2 V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
        (⟪ιMulti ℝ 2 ![b i, b j], x⟫ * ⟪ιMulti ℝ 2 ![b k, b l], y⟫)) =
      4 * ⟪twoVectorBracket (A x) (B y), ξ⟫ := by
  have hrepr (η : ⋀[ℝ]^2 V) :
      ∑ i, ∑ j, ⟪ιMulti ℝ 2 ![b i, b j], η⟫ • ιMulti ℝ 2 ![b i, b j] = (2 : ℝ) • η := by
    simpa only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, LinearMap.smul_apply, LinearMap.id_apply] using
      LinearMap.congr_fun b.sum_rankOne_ιMulti_two η
  have hlhs :
      ⟪twoVectorBracket (A (∑ i, ∑ j, ⟪ιMulti ℝ 2 ![b i, b j], x⟫ • ιMulti ℝ 2 ![b i, b j]))
          (B (∑ k, ∑ l, ⟪ιMulti ℝ 2 ![b k, b l], y⟫ • ιMulti ℝ 2 ![b k, b l])), ξ⟫ =
      ∑ k, ∑ l, ∑ i, ∑ j,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
          (⟪ιMulti ℝ 2 ![b i, b j], x⟫ * ⟪ιMulti ℝ 2 ![b k, b l], y⟫) := by
    simp only [map_sum, LinearMap.sum_apply, sum_inner, map_smul, LinearMap.smul_apply,
      real_inner_smul_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have hswap2 (f : ι → ι → ι → ι → ℝ) :
      (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
    have h1 (i) : (∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ j, ∑ l, f i j k l := Finset.sum_comm
    have h2 (i k) : (∑ j, ∑ l, f i j k l) = ∑ l, ∑ j, f i j k l := Finset.sum_comm
    have h3 (k) : (∑ i, ∑ l, ∑ j, f i j k l) = ∑ l, ∑ i, ∑ j, f i j k l := Finset.sum_comm
    simp_rw [h1, h2]; rw [Finset.sum_comm]; simp_rw [h3]
  rw [hswap2, ← hlhs, hrepr x, hrepr y, map_smul, map_smul, map_smul, LinearMap.smul_apply,
    map_smul, real_inner_smul_left, real_inner_smul_left]; ring

/-- Reduction of `2 * ⟪sharpBilin A B ξ, z ∧ w⟫` to a single basis sum over `V`. -/
private theorem two_mul_inner_sharpBilin_ιMulti_right {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ : ⋀[ℝ]^2 V) (z w : V) :
    2 * ⟪sharpBilin A B ξ, ιMulti ℝ 2 ![z, w]⟫ =
      ∑ q, (⟪twoVectorBracket (A (ιMulti ℝ 2 ![w, b q])) (B (ιMulti ℝ 2 ![b q, z])), ξ⟫ -
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![z, b q])) (B (ιMulti ℝ 2 ![b q, w])), ξ⟫) := by
  have hsum :
      (∑ i, ∑ j, ∑ k, ∑ l,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
          ⟪twoVectorBracket (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b k, b l]),
            ιMulti ℝ 2 ![z, w]⟫) =
      ∑ q, (4 * ⟪twoVectorBracket (A (ιMulti ℝ 2 ![w, b q])) (B (ιMulti ℝ 2 ![b q, z])), ξ⟫ -
        4 * ⟪twoVectorBracket (A (ιMulti ℝ 2 ![z, b q])) (B (ιMulti ℝ 2 ![b q, w])), ξ⟫) := by
    simp_rw [inner_twoVectorBracket_ιMulti_orthonormalBasis b, Finset.mul_sum, mul_sub]
    have hcomm (f : ι → ι → ι → ι → ι → ℝ) :
        (∑ i, ∑ j, ∑ k, ∑ l, ∑ q, f i j k l q) = ∑ q, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l q := by
      have h1 (i j k) : (∑ l, ∑ q, f i j k l q) = ∑ q, ∑ l, f i j k l q := Finset.sum_comm
      have h2 (i j) : (∑ k, ∑ q, ∑ l, f i j k l q) = ∑ q, ∑ k, ∑ l, f i j k l q := Finset.sum_comm
      have h3 (i) : (∑ j, ∑ q, ∑ k, ∑ l, f i j k l q) = ∑ q, ∑ j, ∑ k, ∑ l, f i j k l q :=
        Finset.sum_comm
      simp_rw [h1, h2, h3]; exact Finset.sum_comm
    rw [hcomm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    simp only [Finset.sum_sub_distrib, sum_inner_twoVectorBracket_contract b A B ξ]
  rw [inner_sharpBilin_eq_sharpVal, sharpVal_eq_sum_ιMulti b, hsum, ← mul_assoc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Contraction of `2 • sharpBilin A B` on pure bivectors in an orthonormal basis of `V`. -/
private theorem two_mul_inner_sharpBilin_ιMulti {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {A B : Module.End ℝ (⋀[ℝ]^2 V)}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (u v z w : V) :
    2 * ⟪sharpBilin A B (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
      ((∑ p, ∑ q, ofExteriorEnd A ![u, b p, z, b q] * ofExteriorEnd B ![v, b p, w, b q]) +
        (∑ p, ∑ q, ofExteriorEnd B ![u, b p, z, b q] * ofExteriorEnd A ![v, b p, w, b q])) -
      ((∑ p, ∑ q, ofExteriorEnd A ![u, b p, w, b q] * ofExteriorEnd B ![v, b p, z, b q]) +
        (∑ p, ∑ q, ofExteriorEnd B ![u, b p, w, b q] * ofExteriorEnd A ![v, b p, z, b q])) := by
  rw [two_mul_inner_sharpBilin_ιMulti_right b]
  simp_rw [inner_twoVectorBracket_ιMulti_orthonormalBasis b, ofExteriorEnd_apply]
  have hA' (x y s t : V) :
      ⟪A (ιMulti ℝ 2 ![x, y]), ιMulti ℝ 2 ![s, t]⟫ =
        ⟪A (ιMulti ℝ 2 ![s, t]), ιMulti ℝ 2 ![x, y]⟫ := by rw [hA, real_inner_comm]
  have hB' (x y s t : V) :
      ⟪B (ιMulti ℝ 2 ![y, x]), ιMulti ℝ 2 ![t, s]⟫ =
        ⟪B (ιMulti ℝ 2 ![s, t]), ιMulti ℝ 2 ![x, y]⟫ := by
    rw [ιMulti_two_swap y x, ιMulti_two_swap t s, map_neg, inner_neg_left, inner_neg_right,
      neg_neg, hB, real_inner_comm]
  simp_rw [hA' w (b _), hA' z (b _), hB' z (b _), hB' w (b _)]
  conv_lhs => simp only [← Finset.sum_sub_distrib]; rw [Finset.sum_comm]
  conv_rhs => simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Polarized bivector-operator identity**: for symmetric endomorphisms `A, B` of `⋀[ℝ]^2 V`,
`reactionBilin V (ofExteriorEnd A) (ofExteriorEnd B)` equals
`ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + 2 • sharpBilin A B)`. -/
theorem ofExteriorEnd_reactionBilin {A B : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) :
    reactionBilin V (ofExteriorEnd A) (ofExteriorEnd B) =
      ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + (2 : ℝ) • sharpBilin A B) := by
  let b := stdOrthonormalBasis ℝ V
  have hcomp (S T : Module.End ℝ (⋀[ℝ]^2 V)) (hS : S.IsSymmetric) (u v z w : V) :
      2 * ⟪(S ∘ₗ T) (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
        ∑ p, ∑ q, ofExteriorEnd T ![u, v, b p, b q] * ofExteriorEnd S ![z, w, b p, b q] := by
    have hrepr :
        ∑ p, ∑ q, ⟪ιMulti ℝ 2 ![b p, b q], T (ιMulti ℝ 2 ![u, v])⟫ • ιMulti ℝ 2 ![b p, b q] =
          (2 : ℝ) • T (ιMulti ℝ 2 ![u, v]) := by
      simpa only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
        InnerProductSpace.rankOne_apply, LinearMap.smul_apply, LinearMap.id_apply] using
        LinearMap.congr_fun b.sum_rankOne_ιMulti_two (T (ιMulti ℝ 2 ![u, v]))
    rw [LinearMap.comp_apply, hS, ← real_inner_smul_left, ← hrepr, sum_inner]
    simp only [sum_inner, real_inner_smul_left, ofExteriorEnd_apply]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      rw [real_inner_comm (T _), real_inner_comm (S _)]
  ext m
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  rw [hm, reactionBilin_apply_orthonormalBasis b, ofExteriorEnd_apply]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, real_inner_smul_left]
  have h1 := hcomp A B hA (m 0) (m 1) (m 2) (m 3)
  have h2 := hcomp B A hB (m 0) (m 1) (m 2) (m 3)
  have h3 := two_mul_inner_sharpBilin_ιMulti b hA hB (m 0) (m 1) (m 2) (m 3)
  linarith

/-- **Bivector-operator identity** `Q(ofExteriorEnd A) = ofExteriorEnd (2 • (A * A + sharp A))`
for any symmetric endomorphism `A` of `⋀[ℝ]^2 V`. -/
theorem ofExteriorEnd_reaction {A : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) :
    reactionTensor (ofExteriorEnd A) = ofExteriorEnd ((2 : ℝ) • (A * A + sharp A)) := by
  rw [← reactionBilin_self, ofExteriorEnd_reactionBilin hA hA]
  congr 1; ext _; simp [two_smul, smul_add]

/-- On any four-tensor antisymmetric in its first pair and symmetric under pair interchange,
`toExteriorEnd (Q(r)) = 2 • (R² + R#)` with `R = toExteriorEnd r`. -/
theorem toExteriorEnd_reactionTensor {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hswap : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]) :
    toExteriorEnd (reactionTensor r) =
      (2 : ℝ) • (toExteriorEnd r * toExteriorEnd r + sharp (toExteriorEnd r)) := by
  have h₂ (u v z w : V) : r ![u, v, z, w] = -r ![u, v, w, z] := by
    rw [hswap u v z w, h₁ z w u v, hswap w z u v]
  conv_lhs => rw [← ofExteriorEnd_toExteriorEnd_of_antisymm h₁ h₂]
  rw [ofExteriorEnd_reaction (isSymmetric_toExteriorEnd hswap), toExteriorEnd_ofExteriorEnd]

/-- For every algebraic curvature tensor `r`, `toExteriorEnd (Q(r)) = 2 • (R² + R#)` with
`R = toExteriorEnd r`. -/
theorem IsAlgebraicCurvature.toExteriorEnd_reactionTensor {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    toExteriorEnd (FourTensor.reactionTensor r) =
      (2 : ℝ) • (toExteriorEnd r * toExteriorEnd r + sharp (toExteriorEnd r)) :=
  FourTensor.toExteriorEnd_reactionTensor hr.antisymm_first hr.swap_pairs

/-! ### Explicit evaluations: identity, constant curvature, and rank-one bivectors -/

private theorem sum_constantCurvature_even {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (u v z w : V) :
    (∑ p, ∑ q, constantCurvature V ![u, b p, z, b q] * constantCurvature V ![v, b p, w, b q]) =
      ((Module.finrank ℝ V : ℝ) - 2) * (⟪u, z⟫ * ⟪v, w⟫) + ⟪u, v⟫ * ⟪z, w⟫ := by
  classical
  have hp (x y : V) : ∑ i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ := by
    simpa only [real_inner_comm (b _)] using b.sum_inner_mul_inner x y
  have hdiag (p) (f : ι → ℝ) : (∑ q, ⟪b p, b q⟫ * f q) = f p := by
    simp only [b.inner_eq_ite, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
  simp only [constantCurvature_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have h1 : (∑ p, ∑ q, ⟪u, z⟫ * ⟪b p, b q⟫ * (⟪v, w⟫ * ⟪b p, b q⟫)) =
      (Module.finrank ℝ V : ℝ) * (⟪u, z⟫ * ⟪v, w⟫) := by
    have hq (p) : (∑ q, ⟪u, z⟫ * ⟪b p, b q⟫ * (⟪v, w⟫ * ⟪b p, b q⟫)) = ⟪u, z⟫ * ⟪v, w⟫ := by
      simp [b.inner_eq_ite]
    simp [hq, Module.finrank_eq_card_basis b.toBasis]
  have h2 : (∑ p, ∑ q, ⟪u, z⟫ * ⟪b p, b q⟫ * (⟪v, b q⟫ * ⟪b p, w⟫)) = ⟪u, z⟫ * ⟪v, w⟫ := by
    have hq (p) : (∑ q, ⟪u, z⟫ * ⟪b p, b q⟫ * (⟪v, b q⟫ * ⟪b p, w⟫)) =
        ⟪u, z⟫ * (⟪v, b p⟫ * ⟪b p, w⟫) := by
      simpa only [mul_assoc] using
        (by convert hdiag p (fun q ↦ ⟪u, z⟫ * (⟪v, b q⟫ * ⟪b p, w⟫)) using 2; ring)
    simp only [hq, ← Finset.mul_sum, hp]
  have h3 : (∑ p, ∑ q, ⟪u, b q⟫ * ⟪b p, z⟫ * (⟪v, w⟫ * ⟪b p, b q⟫)) = ⟪u, z⟫ * ⟪v, w⟫ := by
    have hq (p) : (∑ q, ⟪u, b q⟫ * ⟪b p, z⟫ * (⟪v, w⟫ * ⟪b p, b q⟫)) =
        ⟪v, w⟫ * (⟪u, b p⟫ * ⟪b p, z⟫) := by
      convert hdiag p (fun q ↦ ⟪v, w⟫ * (⟪u, b q⟫ * ⟪b p, z⟫)) using 2; ring
    simp only [hq, ← Finset.mul_sum, hp]; ring
  have h4 : (∑ p, ∑ q, ⟪u, b q⟫ * ⟪b p, z⟫ * (⟪v, b q⟫ * ⟪b p, w⟫)) = ⟪u, v⟫ * ⟪z, w⟫ := by
    have hsplit (p) : (∑ q, ⟪u, b q⟫ * ⟪b p, z⟫ * (⟪v, b q⟫ * ⟪b p, w⟫)) =
        (⟪b p, z⟫ * ⟪b p, w⟫) * ∑ q, ⟪u, b q⟫ * ⟪b q, v⟫ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ ↦ by rw [real_inner_comm (b q) v]; ring
    simp only [hsplit, hp, ← Finset.sum_mul]
    simpa only [real_inner_comm z, mul_comm] using congrArg (· * ⟪u, v⟫) (hp z w)
  rw [h1, h2, h3, h4]; ring

/-- `sharp 1 = (dim V - 2) • 1` on `⋀[ℝ]^2 V`, in every dimension `dim V : ℕ`. -/
theorem sharp_one :
    sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) =
      ((Module.finrank ℝ V : ℝ) - 2) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
  let b := stdOrthonormalBasis ℝ V
  refine exteriorPower.linearMap_ext_inner_ιMulti_two fun u v z w ↦ ?_
  have h2 := two_mul_inner_sharpBilin_ιMulti b (V := V) LinearMap.IsSymmetric.one
    LinearMap.IsSymmetric.one u v z w
  rw [sharpBilin_self, ofExteriorEnd_one, sum_constantCurvature_even b u v z w,
    sum_constantCurvature_even b u v w z, real_inner_comm w z] at h2
  simp only [LinearMap.smul_apply, one_apply_eq_self, real_inner_smul_left, inner_ιMulti_two]
  linarith

/-- On the constant-curvature tensor, `Q(I) = 2 (dim V - 1) • I`. -/
theorem reactionTensor_constantCurvature :
    reactionTensor (constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • constantCurvature V := by
  rw [← ofExteriorEnd_one, ofExteriorEnd_reaction LinearMap.IsSymmetric.one, sharp_one, mul_one,
    ← map_smul]
  congr 1; refine LinearMap.ext fun _ ↦ ?_
  simp only [LinearMap.smul_apply, LinearMap.add_apply, one_apply_eq_self]; module

/-- Scaling of `reactionTensor` on a constant-curvature tensor of sectional curvature `κ`. -/
theorem reactionTensor_smul_constantCurvature (κ : ℝ) :
    reactionTensor (κ • constantCurvature V) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1) * κ ^ 2) • constantCurvature V := by
  rw [reactionTensor_smul, reactionTensor_constantCurvature, smul_smul]; ring_nf

/-- The rank-one algebraic curvature tensor `(e₁ ∧ e₂) ⊗ (e₁ ∧ e₂)` associated to a pair of vectors
`e₁, e₂ : V`. For an orthonormal pair `e₁, e₂`, this is the curvature four-tensor of the product
`S² × ℝ^(dim V - 2)`. -/
def bivectorSq (e₁ e₂ : V) : FourTensor V :=
  ofExteriorEnd
    (InnerProductSpace.rankOne ℝ (ιMulti ℝ 2 ![e₁, e₂]) (ιMulti ℝ 2 ![e₁, e₂])).toLinearMap

/-- Evaluation of `bivectorSq e₁ e₂`. -/
@[simp]
theorem bivectorSq_apply (e₁ e₂ u v z w : V) :
    bivectorSq e₁ e₂ ![u, v, z, w] =
      (⟪e₁, u⟫ * ⟪e₂, v⟫ - ⟪e₁, v⟫ * ⟪e₂, u⟫) *
        (⟪e₁, z⟫ * ⟪e₂, w⟫ - ⟪e₁, w⟫ * ⟪e₂, z⟫) := by
  rw [bivectorSq, ofExteriorEnd_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, real_inner_smul_left, inner_ιMulti_two, inner_ιMulti_two]

/-- For every pair `e₁, e₂ : V`, `bivectorSq e₁ e₂` is an algebraic curvature tensor (the first
Bianchi identity holds by the Plücker relation). -/
theorem isAlgebraicCurvature_bivectorSq (e₁ e₂ : V) :
    IsAlgebraicCurvature (bivectorSq e₁ e₂) := by
  rw [bivectorSq, isAlgebraicCurvature_ofExteriorEnd_iff]
  refine ⟨fun x _ ↦ ?_, fun _ _ _ _ ↦ ?_⟩
  · simp only [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm x]; ring
  · simp only [ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      real_inner_smul_left, inner_ιMulti_two]; ring

/-- The reaction tensor of `bivectorSq e₁ e₂` is
`2 (‖e₁‖² ‖e₂‖² - ⟪e₁, e₂⟫²) • bivectorSq e₁ e₂`. -/
theorem reactionTensor_bivectorSq (e₁ e₂ : V) :
    reactionTensor (bivectorSq e₁ e₂) =
      (2 * constantCurvature V ![e₁, e₂, e₁, e₂]) • bivectorSq e₁ e₂ := by
  set α := ιMulti ℝ 2 ![e₁, e₂]
  set T := (InnerProductSpace.rankOne ℝ α α).toLinearMap
  have hTsym : T.IsSymmetric := fun x _ ↦ by
    simp only [T, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm x α]; ring
  have hTsq : T * T = constantCurvature V ![e₁, e₂, e₁, e₂] • T := LinearMap.ext fun _ ↦ by
    simp only [T, α, mul_apply_eq_comp, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, real_inner_smul_right, LinearMap.smul_apply,
      inner_ιMulti_two, constantCurvature_apply]
    rw [smul_smul, mul_comm]
  rw [bivectorSq, ofExteriorEnd_reaction hTsym, hTsq, sharp_rankOne_self α, add_zero, smul_smul,
    map_smul]

/-- For an orthonormal pair `e₁, e₂`, `Q(bivectorSq e₁ e₂) = 2 • bivectorSq e₁ e₂` (the
`S² × ℝ^(dim V - 2)` check). -/
theorem reactionTensor_bivectorSq_of_orthonormal {e₁ e₂ : V} (h : Orthonormal ℝ ![e₁, e₂]) :
    reactionTensor (bivectorSq e₁ e₂) = (2 : ℝ) • bivectorSq e₁ e₂ := by
  rw [reactionTensor_bivectorSq, constantCurvature_apply,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    show ‖e₁‖ = 1 from h.1 0, show ‖e₂‖ = 1 from h.1 1,
    show ⟪e₁, e₂⟫ = 0 from h.2 (show (0 : Fin 2) ≠ 1 by decide),
    show ⟪e₂, e₁⟫ = 0 from h.2 (show (1 : Fin 2) ≠ 0 by decide)]
  norm_num

end TauCeti.FourTensor
