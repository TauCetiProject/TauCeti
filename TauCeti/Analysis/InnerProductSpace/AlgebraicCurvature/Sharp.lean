/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Operator
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Reaction
public import TauCeti.Analysis.InnerProductSpace.BilinearForm.End
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
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
`reactionBilinear V (ofExteriorEnd A) (ofExteriorEnd B) =`
`ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + 2 • sharpBilin A B)`,
`Q(ofExteriorEnd A) = ofExteriorEnd (2 • (A * A + sharp A))`, and
`curvatureEndomorphism (Q(r)) = 2 • (R² + R#)` for every symmetric endomorphism `A` of `⋀[ℝ]^2 V`
and every algebraic curvature tensor `r`, together with the rank-one operator characterization
`curvatureEndomorphism (planeCurvature u v) = rankOne ℝ (u ∧ v) (u ∧ v)`.

## Main definitions

* `TauCeti.FourTensor.sharpBilin` and `TauCeti.FourTensor.sharp`: Hamilton's Lie-algebraic `#`
  product on `Module.End ℝ (⋀[ℝ]^2 V)`.

## Main statements

* `OrthonormalBasis.inner_sharpBilin`: basis formula for `sharpBilin`.
* `LinearMap.IsSymmetric.sharpBilin` and `LinearMap.IsSymmetric.sharp`: preservation of symmetry.
* `TauCeti.FourTensor.sharp_one`: `sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) = (dim V - 2) • 1`.
* `TauCeti.FourTensor.reactionBilinear_ofExteriorEnd`,
  `TauCeti.FourTensor.reactionTensor_ofExteriorEnd`,
  `TauCeti.FourTensor.curvatureEndomorphism_reactionTensor`, and
  `TauCeti.FourTensor.IsAlgebraicCurvature.curvatureEndomorphism_reactionTensor`: the operator
  identity `Q(R) = 2 (R² + R#)`.
* `TauCeti.FourTensor.planeCurvature_eq_ofExteriorEnd` and
  `TauCeti.FourTensor.curvatureEndomorphism_planeCurvature`: the bivector rank-one operator
  characterization of `planeCurvature u v`.

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
    { toFun := fun B ↦ bilinFormToEnd (sharpForm A B)
      map_add' := fun _ _ ↦ LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
        simp only [LinearMap.BilinForm.inner_bilinFormToEnd_left, LinearMap.add_apply,
          inner_add_left, sharpForm, LinearMap.mk₂_apply,
          sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), map_add, add_mul,
          Finset.sum_add_distrib]; ring
      map_smul' := fun _ _ ↦ LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
        simp only [LinearMap.BilinForm.inner_bilinFormToEnd_left, LinearMap.smul_apply,
          RingHom.id_apply, real_inner_smul_left, sharpForm, LinearMap.mk₂_apply,
          sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), map_smul, mul_assoc,
          ← Finset.mul_sum]; ring }
  map_add' _ _ := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      LinearMap.BilinForm.inner_bilinFormToEnd_left, inner_add_left, sharpForm,
      LinearMap.mk₂_apply, sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), map_add, add_mul,
      Finset.sum_add_distrib]; ring
  map_smul' _ _ := LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ ext_inner_right ℝ fun _ ↦ by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply,
      LinearMap.BilinForm.inner_bilinFormToEnd_left, real_inner_smul_left, sharpForm,
      LinearMap.mk₂_apply, sharpVal_eq_sum (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)), map_smul, mul_assoc,
      ← Finset.mul_sum]; ring

/-- Hamilton's quadratic `#` operator `A# = sharpBilin A A` on `Module.End ℝ (⋀[ℝ]^2 V)`. -/
def sharp (A : Module.End ℝ (⋀[ℝ]^2 V)) : Module.End ℝ (⋀[ℝ]^2 V) :=
  sharpBilin A A

private theorem inner_sharpBilin_eq_sharpVal (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    ⟪sharpBilin A B ξ, η⟫ = sharpVal A B ξ η := by
  simp [sharpBilin, sharpForm]

/-- Evaluation of `sharpBilin A B` in any orthonormal basis of `⋀[ℝ]^2 V`. -/
theorem _root_.OrthonormalBasis.inner_sharpBilin {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (⋀[ℝ]^2 V)) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    ⟪sharpBilin A B ξ, η⟫ =
      (1 / 2 : ℝ) * ∑ α, ∑ β,
        ⟪twoVectorBracket (A (e α)) (B (e β)), ξ⟫ * ⟪twoVectorBracket (e α) (e β), η⟫ := by
  rw [inner_sharpBilin_eq_sharpVal, sharpVal_eq_sum e]

/-- `sharpBilin` is symmetric in its two endomorphism arguments. -/
theorem sharpBilin_comm (A B : Module.End ℝ (⋀[ℝ]^2 V)) : sharpBilin A B = sharpBilin B A := by
  let e := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  rw [e.inner_sharpBilin, e.inner_sharpBilin]
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

/-- Quadratic expansion of `sharp` on a sum of endomorphisms. -/
theorem sharp_add (A B : Module.End ℝ (⋀[ℝ]^2 V)) :
    sharp (A + B) = sharp A + (2 : ℝ) • sharpBilin A B + sharp B := by
  simp only [sharp, map_add, LinearMap.add_apply, sharpBilin_comm B A, two_smul]
  abel

/-- Every rank-one operator `ξ ↦ ⟪α, ξ⟫ • α` on `⋀[ℝ]^2 V` has vanishing `#`-square. -/
theorem sharp_rankOne_self (α : ⋀[ℝ]^2 V) :
    sharp (InnerProductSpace.rankOne ℝ α α).toLinearMap = 0 := by
  refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  rw [← sharpBilin_self, (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)).inner_sharpBilin]
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
theorem _root_.LinearMap.IsSymmetric.sharpBilin {A B : Module.End ℝ (⋀[ℝ]^2 V)}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) : (sharpBilin A B).IsSymmetric := by
  let e := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  intro ξ η
  rw [real_inner_comm (FourTensor.sharpBilin A B η) ξ, e.inner_sharpBilin, e.inner_sharpBilin]
  congr 1
  rw [sharpBilin_sum_expand e A B ξ η, sharpBilin_sum_expand e A B η ξ]
  simp only [← Fintype.sum_prod_type']
  let ι := Fin (Module.finrank ℝ (⋀[ℝ]^2 V))
  let swapPairs : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) :=
    { toFun := fun ⟨α, β, γ, δ⟩ ↦ ⟨γ, δ, α, β⟩
      invFun := fun ⟨γ, δ, α, β⟩ ↦ ⟨α, β, γ, δ⟩
      left_inv := fun ⟨_, _, _, _⟩ ↦ rfl
      right_inv := fun ⟨_, _, _, _⟩ ↦ rfl }
  refine Fintype.sum_equiv swapPairs _ _ fun ⟨α, β, γ, δ⟩ ↦ ?_
  simp only [swapPairs, Equiv.coe_fn_mk]
  rw [← hA (e γ) (e α), real_inner_comm (A (e γ)),
    ← hB (e δ) (e β), real_inner_comm (B (e δ))]
  ring

/-- The `#`-square of a symmetric endomorphism of `⋀[ℝ]^2 V` is symmetric. -/
theorem _root_.LinearMap.IsSymmetric.sharp {A : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) :
    (sharp A).IsSymmetric :=
  hA.sharpBilin hA

/-! ### The bivector-operator identity `Q(R) = 2(R² + R#)` -/

private theorem sum_inner_twoVectorBracket_contract {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ x y : ⋀[ℝ]^2 V) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
        (⟪ιMulti ℝ 2 ![b i, b j], x⟫ * ⟪ιMulti ℝ 2 ![b k, b l], y⟫)) =
      4 * ⟪twoVectorBracket (A x) (B y), ξ⟫ := by
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
  have hswap :
      (∑ i, ∑ j, ∑ k, ∑ l,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
          (⟪ιMulti ℝ 2 ![b i, b j], x⟫ * ⟪ιMulti ℝ 2 ![b k, b l], y⟫)) =
      ∑ k, ∑ l, ∑ i, ∑ j,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j])) (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
          (⟪ιMulti ℝ 2 ![b i, b j], x⟫ * ⟪ιMulti ℝ 2 ![b k, b l], y⟫) := by
    let swapPairs : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) :=
      { toFun := fun ⟨i, j, k, l⟩ ↦ ⟨k, l, i, j⟩
        invFun := fun ⟨k, l, i, j⟩ ↦ ⟨i, j, k, l⟩
        left_inv := fun ⟨_, _, _, _⟩ ↦ rfl
        right_inv := fun ⟨_, _, _, _⟩ ↦ rfl }
    simp only [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv swapPairs _ _ fun _ ↦ rfl
  rw [hswap, ← hlhs, b.sum_inner_smul_ιMulti_two x, b.sum_inner_smul_ιMulti_two y, map_smul,
    map_smul, map_smul, LinearMap.smul_apply, map_smul, real_inner_smul_left,
    real_inner_smul_left]
  ring

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
    simp_rw [b.inner_twoVectorBracket_ιMulti, Finset.mul_sum, mul_sub]
    have hcomm :
        (∑ i, ∑ j, ∑ k, ∑ l, ∑ q,
          (⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j]))
              (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
            (⟪ιMulti ℝ 2 ![b i, b j], ιMulti ℝ 2 ![w, b q]⟫ *
              ⟪ιMulti ℝ 2 ![b k, b l], ιMulti ℝ 2 ![b q, z]⟫) -
          ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j]))
              (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
            (⟪ιMulti ℝ 2 ![b i, b j], ιMulti ℝ 2 ![z, b q]⟫ *
              ⟪ιMulti ℝ 2 ![b k, b l], ιMulti ℝ 2 ![b q, w]⟫))) =
        ∑ q, ∑ i, ∑ j, ∑ k, ∑ l,
          (⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j]))
              (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
            (⟪ιMulti ℝ 2 ![b i, b j], ιMulti ℝ 2 ![w, b q]⟫ *
              ⟪ιMulti ℝ 2 ![b k, b l], ιMulti ℝ 2 ![b q, z]⟫) -
          ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b i, b j]))
              (B (ιMulti ℝ 2 ![b k, b l])), ξ⟫ *
            (⟪ιMulti ℝ 2 ![b i, b j], ιMulti ℝ 2 ![z, b q]⟫ *
              ⟪ιMulti ℝ 2 ![b k, b l], ιMulti ℝ 2 ![b q, w]⟫)) := by
      let rot : (ι × ι × ι × ι × ι) ≃ (ι × ι × ι × ι × ι) :=
        { toFun := fun ⟨i, j, k, l, q⟩ ↦ ⟨q, i, j, k, l⟩
          invFun := fun ⟨q, i, j, k, l⟩ ↦ ⟨i, j, k, l, q⟩
          left_inv := fun ⟨_, _, _, _, _⟩ ↦ rfl
          right_inv := fun ⟨_, _, _, _, _⟩ ↦ rfl }
      simp only [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv rot _ _ fun _ ↦ rfl
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
  simp_rw [b.inner_twoVectorBracket_ιMulti, ofExteriorEnd_apply]
  have hA' (x y s t : V) :
      ⟪A (ιMulti ℝ 2 ![x, y]), ιMulti ℝ 2 ![s, t]⟫ =
        ⟪A (ιMulti ℝ 2 ![s, t]), ιMulti ℝ 2 ![x, y]⟫ := by rw [hA, real_inner_comm]
  have hB' (x y s t : V) :
      ⟪B (ιMulti ℝ 2 ![y, x]), ιMulti ℝ 2 ![t, s]⟫ =
        ⟪B (ιMulti ℝ 2 ![s, t]), ιMulti ℝ 2 ![x, y]⟫ := by
    rw [ιMulti_two_swap x y, ιMulti_two_swap s t, map_neg, inner_neg_left, inner_neg_right,
      neg_neg, hB, real_inner_comm]
  simp_rw [hA' w (b _), hA' z (b _), hB' z (b _), hB' w (b _)]
  conv_lhs => simp only [← Finset.sum_sub_distrib]; rw [Finset.sum_comm]
  conv_rhs => simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **Polarized bivector-operator identity**: for symmetric endomorphisms `A, B` of `⋀[ℝ]^2 V`,
`reactionBilinear V (ofExteriorEnd A) (ofExteriorEnd B)` equals
`ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + 2 • sharpBilin A B)`. -/
theorem reactionBilinear_ofExteriorEnd {A B : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) :
    reactionBilinear V (ofExteriorEnd A) (ofExteriorEnd B) =
      ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + (2 : ℝ) • sharpBilin A B) := by
  let b := stdOrthonormalBasis ℝ V
  have hcomp (S T : Module.End ℝ (⋀[ℝ]^2 V)) (hS : S.IsSymmetric) (u v z w : V) :
      2 * ⟪(S ∘ₗ T) (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
        ∑ p, ∑ q, ofExteriorEnd T ![u, v, b p, b q] * ofExteriorEnd S ![z, w, b p, b q] := by
    rw [LinearMap.comp_apply, hS, ← real_inner_smul_left,
      ← b.sum_inner_smul_ιMulti_two (T (ιMulti ℝ 2 ![u, v])), sum_inner]
    simp only [sum_inner, real_inner_smul_left, ofExteriorEnd_apply]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by
      rw [real_inner_comm (T _), real_inner_comm (S _)]
  refine ext_vec fun u v z w ↦ ?_
  rw [reactionBilinear_apply_orthonormalBasis b, ofExteriorEnd_apply]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, real_inner_smul_left]
  have h1 := hcomp A B hA u v z w
  have h2 := hcomp B A hB u v z w
  have h3 := two_mul_inner_sharpBilin_ιMulti b hA hB u v z w
  linarith

/-- **Bivector-operator identity** `Q(ofExteriorEnd A) = ofExteriorEnd (2 • (A * A + sharp A))`
for any symmetric endomorphism `A` of `⋀[ℝ]^2 V`. -/
theorem reactionTensor_ofExteriorEnd {A : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) :
    reactionTensor (ofExteriorEnd A) = ofExteriorEnd ((2 : ℝ) • (A * A + sharp A)) := by
  rw [← reactionBilinear_self, reactionBilinear_ofExteriorEnd hA hA]
  congr 1; ext _; simp [two_smul, smul_add]

/-- On any four-tensor antisymmetric in its first pair and symmetric under pair interchange,
`curvatureEndomorphism (Q(r)) = 2 • (R² + R#)` with `R = curvatureEndomorphism r`. -/
theorem curvatureEndomorphism_reactionTensor {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hswap : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]) :
    curvatureEndomorphism (reactionTensor r) =
      (2 : ℝ) • (curvatureEndomorphism r * curvatureEndomorphism r +
        sharp (curvatureEndomorphism r)) := by
  have h₂ (u v z w : V) : r ![u, v, z, w] = -r ![u, v, w, z] := by
    rw [hswap u v z w, h₁ z w u v, hswap w z u v]
  conv_lhs => rw [← ofExteriorEnd_curvatureEndomorphism_of_antisymm h₁ h₂]
  rw [reactionTensor_ofExteriorEnd (isSymmetric_curvatureEndomorphism_of_swap_pairs hswap),
    curvatureEndomorphism_ofExteriorEnd]

/-- On any bivector-symmetric four-tensor `r`, `curvatureEndomorphism (Q(r)) = 2 • (R² + R#)` with
`R = curvatureEndomorphism r`. -/
theorem IsBivectorSymmetric.curvatureEndomorphism_reactionTensor {r : FourTensor V}
    (hr : IsBivectorSymmetric r) :
    curvatureEndomorphism (FourTensor.reactionTensor r) =
      (2 : ℝ) • (curvatureEndomorphism r * curvatureEndomorphism r +
        sharp (curvatureEndomorphism r)) :=
  FourTensor.curvatureEndomorphism_reactionTensor hr.antisymm_first hr.swap_pairs

/-- For every algebraic curvature tensor `r`, `curvatureEndomorphism (Q(r)) = 2 • (R² + R#)` with
`R = curvatureEndomorphism r`. -/
theorem IsAlgebraicCurvature.curvatureEndomorphism_reactionTensor {r : FourTensor V}
    (hr : IsAlgebraicCurvature r) :
    curvatureEndomorphism (FourTensor.reactionTensor r) =
      (2 : ℝ) • (curvatureEndomorphism r * curvatureEndomorphism r +
        sharp (curvatureEndomorphism r)) :=
  hr.isBivectorSymmetric.curvatureEndomorphism_reactionTensor

/-! ### Explicit evaluations: identity and rank-one bivectors -/

/-- `sharp 1 = (dim V - 2) • 1` on `⋀[ℝ]^2 V`, in every dimension `dim V : ℕ`. -/
theorem sharp_one :
    sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) =
      ((Module.finrank ℝ V : ℝ) - 2) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
  have h :
      ofExteriorEnd ((2 : ℝ) • (1 * 1 + sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)))) =
        ofExteriorEnd
          ((2 * ((Module.finrank ℝ V : ℝ) - 1)) • (1 : Module.End ℝ (⋀[ℝ]^2 V))) := by
    rw [← reactionTensor_ofExteriorEnd LinearMap.IsSymmetric.one, ofExteriorEnd_one,
      reactionTensor_constantCurvature, map_smul, ofExteriorEnd_one]
  have h2 : (2 : ℝ) • (1 + sharp (1 : Module.End ℝ (⋀[ℝ]^2 V))) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
    simpa only [one_mul] using ofExteriorEnd_injective h
  have h1 : 1 + sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) =
      ((Module.finrank ℝ V : ℝ) - 1) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
    refine smul_right_injective (Module.End ℝ (⋀[ℝ]^2 V)) (two_ne_zero (α := ℝ)) ?_
    simpa only [smul_smul] using h2
  have hsub : ((Module.finrank ℝ V : ℝ) - 2) = (Module.finrank ℝ V : ℝ) - 1 - 1 := by ring
  rw [eq_sub_of_add_eq' h1, hsub]
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, sub_smul, one_smul]

/-- The rank-one plane curvature tensor `planeCurvature u v` is the four-tensor associated to
the rank-one operator `(u ∧ v) ⊗ (u ∧ v)` on `⋀[ℝ]^2 V`. -/
theorem planeCurvature_eq_ofExteriorEnd (u v : V) :
    planeCurvature u v =
      ofExteriorEnd
        (InnerProductSpace.rankOne ℝ (ιMulti ℝ 2 ![u, v])
          (ιMulti ℝ 2 ![u, v])).toLinearMap := by
  refine ext_vec fun a b c d ↦ ?_
  rw [planeCurvature_apply, ofExteriorEnd_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, real_inner_smul_left, inner_ιMulti_two, inner_ιMulti_two]

/-- The bivector endomorphism of `planeCurvature u v` is the rank-one operator
`ξ ↦ ⟪u ∧ v, ξ⟫ • (u ∧ v)`. -/
@[simp]
theorem curvatureEndomorphism_planeCurvature (u v : V) :
    curvatureEndomorphism (planeCurvature u v) =
      (InnerProductSpace.rankOne ℝ (ιMulti ℝ 2 ![u, v])
        (ιMulti ℝ 2 ![u, v])).toLinearMap := by
  rw [planeCurvature_eq_ofExteriorEnd, curvatureEndomorphism_ofExteriorEnd]

end TauCeti.FourTensor
