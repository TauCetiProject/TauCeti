/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Operator
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Reaction.Basic
public import TauCeti.Analysis.InnerProductSpace.BilinearForm.End
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
import TauCeti.Analysis.InnerProductSpace.Trace.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# Hamilton's `#` product and the bivector-operator identity `Q(R) = 2(R² + R#)`

On the exterior square `⋀[ℝ]^2 V` of a finite-dimensional real inner product space `V`, we define
Hamilton's symmetric bilinear Lie-algebraic product `TauCeti.bivectorSharpBilin A B` and
`TauCeti.bivectorSharp A = TauCeti.bivectorSharpBilin A A` using the bivector Lie bracket
`TauCeti.twoVectorBracket`,
```
⟪TauCeti.bivectorSharpBilin A B ξ, η⟫ =
  (1 / 2) ∑_α ∑_β ⟪[A ω_α, B ω_β], ξ⟫ ⟪[ω_α, ω_β], η⟫.
```
We prove that `bivectorSharpBilin` and `bivectorSharp` preserve symmetry, are equivariant under
conjugation by linear isometric equivalences, evaluate
`bivectorSharp 1 = (dim V - 2) • 1`, and establish the polarized and quadratic bivector-operator
identities
`reactionBilinear V (ofExteriorEnd A) (ofExteriorEnd B) =`
`ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + 2 • bivectorSharpBilin A B)`,
`Q(ofExteriorEnd A) = ofExteriorEnd (2 • (A * A + bivectorSharp A))`, and
`curvatureEndomorphism (Q(r)) = 2 • (R² + R#)` for every symmetric endomorphism `A` of `⋀[ℝ]^2 V`
and every bivector-symmetric four-tensor `r`.

## Main definitions

* `TauCeti.bivectorSharpBilin` and `TauCeti.bivectorSharp`: Hamilton's Lie-algebraic `#` product
  on `Module.End ℝ (⋀[ℝ]^2 V)`.

## Main statements

* `OrthonormalBasis.inner_bivectorSharpBilin`: basis formula for `TauCeti.bivectorSharpBilin`.
* `TauCeti.adjoint_bivectorSharpBilin` and `TauCeti.adjoint_bivectorSharp`: adjoint commutation
  laws.
* `LinearIsometryEquiv.bivectorSharpBilin_conj_exteriorPower_map` and
  `LinearIsometryEquiv.bivectorSharp_conj_exteriorPower_map`: frame-change conjugation laws for
  `bivectorSharpBilin` and `bivectorSharp`.
* `LinearMap.IsSymmetric.bivectorSharpBilin` and `LinearMap.IsSymmetric.bivectorSharp`:
  preservation of symmetry.
* `TauCeti.bivectorSharp_one`:
  `TauCeti.bivectorSharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) = (dim V - 2) • 1`.
* `LinearMap.IsSymmetric.reactionBilinear_ofExteriorEnd`,
  `LinearMap.IsSymmetric.reactionTensor_ofExteriorEnd`,
  `TauCeti.FourTensor.IsAlgebraicCurvatureEndomorphism`
  `.comp_add_comp_add_two_smul_bivectorSharpBilin`,
  `TauCeti.FourTensor.IsAlgebraicCurvatureEndomorphism.two_smul_mul_add_bivectorSharp`,
  `TauCeti.FourTensor.curvatureEndomorphism_reactionTensor`, and
  `TauCeti.FourTensor.IsBivectorSymmetric.curvatureEndomorphism_reactionTensor`: the operator
  identity `Q(R) = 2 (R² + R#)` and closure of `Sym²_B(⋀²V)`.

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
open scoped RealInnerProductSpace TensorProduct

noncomputable section

section SharpProduct

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Hamilton's `#` product -/

/-- Hamilton's symmetric bilinear Lie-algebraic `#` product on `Module.End ℝ (⋀[ℝ]^2 V)`,
characterized in any orthonormal basis `e` of `⋀[ℝ]^2 V` by
`⟪bivectorSharpBilin A B ξ, η⟫ = (1 / 2) ∑ α β, ⟪[A (e α), B (e β)], ξ⟫ ⟪[e α, e β], η⟫`. -/
def bivectorSharpBilin :
    Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) :=
  let C := TensorProduct.lift (twoVectorBracket (V := V))
  let mapBil := TensorProduct.mapBilinear (RingHom.id ℝ)
    (⋀[ℝ]^2 V) (⋀[ℝ]^2 V) (⋀[ℝ]^2 V) (⋀[ℝ]^2 V)
  let adj : Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) :=
    (LinearMap.adjoint : Module.End ℝ (⋀[ℝ]^2 V) ≃ₗ⋆[ℝ] Module.End ℝ (⋀[ℝ]^2 V)).toLinearMap
  (1 / 2 : ℝ) •
    ((mapBil.compr₂ ((LinearMap.llcomp ℝ (⋀[ℝ]^2 V) _ _).flip C.adjoint)).compr₂
      (LinearMap.llcomp ℝ (⋀[ℝ]^2 V) _ _ C)).compr₂ adj

/-- Basis-free expression for `TauCeti.bivectorSharpBilin A B` in terms of `TensorProduct.lift` of
`TauCeti.twoVectorBracket` and its adjoint. -/
theorem bivectorSharpBilin_eq (A B : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharpBilin A B =
      (1 / 2 : ℝ) •
        (TensorProduct.lift (twoVectorBracket (V := V)) ∘ₗ TensorProduct.map A B ∘ₗ
          LinearMap.adjoint (𝕜 := ℝ) (E := (⋀[ℝ]^2 V) ⊗[ℝ] (⋀[ℝ]^2 V)) (F := ⋀[ℝ]^2 V)
            (TensorProduct.lift twoVectorBracket)).adjoint := by
  dsimp only [bivectorSharpBilin]
  simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, LinearMap.flip_apply,
    LinearMap.llcomp_apply', TensorProduct.mapBilinear_apply, LinearEquiv.coe_toLinearMap]

/-- Hamilton's quadratic `#` operator `bivectorSharp A = bivectorSharpBilin A A` on
`Module.End ℝ (⋀[ℝ]^2 V)`. -/
def bivectorSharp (A : Module.End ℝ (⋀[ℝ]^2 V)) : Module.End ℝ (⋀[ℝ]^2 V) :=
  bivectorSharpBilin A A

/-- Evaluation of `TauCeti.bivectorSharpBilin A B` in any orthonormal basis of `⋀[ℝ]^2 V`. -/
theorem _root_.OrthonormalBasis.inner_bivectorSharpBilin {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (⋀[ℝ]^2 V)) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    ⟪bivectorSharpBilin A B ξ, η⟫ =
      (1 / 2 : ℝ) * ∑ α, ∑ β,
        ⟪twoVectorBracket (A (e α)) (B (e β)), ξ⟫ *
          ⟪twoVectorBracket (e α) (e β), η⟫ := by
  rw [bivectorSharpBilin_eq, LinearMap.smul_apply, real_inner_smul_left,
    LinearMap.adjoint_inner_left, LinearMap.comp_apply, LinearMap.comp_apply]
  have hη : (TensorProduct.lift (twoVectorBracket (V := V))).adjoint η =
      ∑ p : ι × ι, ⟪twoVectorBracket (e p.1) (e p.2), η⟫ • (e p.1 ⊗ₜ[ℝ] e p.2) := by
    conv_lhs =>
      rw [← (e.tensorProduct e).sum_repr'
        ((TensorProduct.lift (twoVectorBracket (V := V))).adjoint η)]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [OrthonormalBasis.tensorProduct_apply, LinearMap.adjoint_inner_right,
      TensorProduct.lift.tmul]
  rw [hη, map_sum, map_sum, inner_sum]
  simp only [map_smul, TensorProduct.map_tmul, TensorProduct.lift.tmul, real_inner_smul_right,
    Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦ ?_
  rw [real_inner_comm ξ, mul_comm]

/-- `TauCeti.bivectorSharpBilin` is symmetric in its two endomorphism arguments. -/
theorem bivectorSharpBilin_comm (A B : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharpBilin A B = bivectorSharpBilin B A := by
  let e := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  rw [e.inner_bivectorSharpBilin, e.inner_bivectorSharpBilin]
  congr 1; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦ by
    rw [twoVectorBracket_swap (B (e α)) (A (e β)),
      twoVectorBracket_swap (e α) (e β), inner_neg_left, inner_neg_left, neg_mul_neg]

/-- Taking the adjoint commutes with `TauCeti.bivectorSharpBilin`. -/
@[simp]
theorem adjoint_bivectorSharpBilin (A B : Module.End ℝ (⋀[ℝ]^2 V)) :
    (bivectorSharpBilin A B).adjoint = bivectorSharpBilin A.adjoint B.adjoint := by
  rw [bivectorSharpBilin_eq, bivectorSharpBilin_eq, map_smul, LinearMap.adjoint_adjoint]
  simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, TensorProduct.adjoint_map,
    LinearMap.comp_assoc]

/-- The diagonal of `TauCeti.bivectorSharpBilin` is `TauCeti.bivectorSharp`. -/
@[simp]
theorem bivectorSharpBilin_self (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharpBilin A A = bivectorSharp A :=
  (rfl)

/-- Taking the adjoint commutes with `TauCeti.bivectorSharp`. -/
@[simp]
theorem adjoint_bivectorSharp (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    (bivectorSharp A).adjoint = bivectorSharp A.adjoint :=
  adjoint_bivectorSharpBilin A A

/-- `TauCeti.bivectorSharp 0 = 0`. -/
@[simp]
theorem bivectorSharp_zero : bivectorSharp (0 : Module.End ℝ (⋀[ℝ]^2 V)) = 0 := by
  simp [bivectorSharp]

/-- `TauCeti.bivectorSharp (-A) = TauCeti.bivectorSharp A`. -/
@[simp]
theorem bivectorSharp_neg (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharp (-A) = bivectorSharp A := by
  simp only [bivectorSharp, map_neg, LinearMap.neg_apply, neg_neg]

/-- `TauCeti.bivectorSharp (c • A) = c ^ 2 • TauCeti.bivectorSharp A`. -/
@[simp]
theorem bivectorSharp_smul (c : ℝ) (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharp (c • A) = (c ^ 2) • bivectorSharp A := by
  simp only [bivectorSharp, map_smul, LinearMap.smul_apply, smul_smul, sq]

/-- Quadratic expansion of `TauCeti.bivectorSharp` on a sum of endomorphisms. -/
theorem bivectorSharp_add (A B : Module.End ℝ (⋀[ℝ]^2 V)) :
    bivectorSharp (A + B) =
      bivectorSharp A + (2 : ℝ) • bivectorSharpBilin A B + bivectorSharp B := by
  simp only [bivectorSharp, map_add, LinearMap.add_apply, bivectorSharpBilin_comm B A, two_smul]
  abel

/-- Every rank-one operator `ξ ↦ ⟪α, ξ⟫ • α` on `⋀[ℝ]^2 V` has vanishing `#`-square. -/
@[simp]
theorem bivectorSharp_rankOne_self (α : ⋀[ℝ]^2 V) :
    bivectorSharp (InnerProductSpace.rankOne ℝ α α).toLinearMap = 0 := by
  refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  rw [← bivectorSharpBilin_self, (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)).inner_bivectorSharpBilin]
  simp [InnerProductSpace.rankOne_apply]

end TauCeti

namespace LinearIsometryEquiv

/-- Conjugating two endomorphisms of `⋀[ℝ]^2 V` by the exterior square of a linear isometric
equivalence commutes with `TauCeti.bivectorSharpBilin`. -/
theorem bivectorSharpBilin_conj_exteriorPower_map {W V : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (e : W ≃ₗᵢ[ℝ] V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) :
    TauCeti.bivectorSharpBilin
        (map 2 e.symm.toLinearMap ∘ₗ A ∘ₗ map 2 e.toLinearMap)
        (map 2 e.symm.toLinearMap ∘ₗ B ∘ₗ map 2 e.toLinearMap) =
      map 2 e.symm.toLinearMap ∘ₗ TauCeti.bivectorSharpBilin A B ∘ₗ map 2 e.toLinearMap := by
  let E := map 2 e.toLinearMap
  let E' := map 2 e.symm.toLinearMap
  let CW := TensorProduct.lift (TauCeti.twoVectorBracket (V := W))
  let CV := TensorProduct.lift (TauCeti.twoVectorBracket (V := V))
  have hmap : E' ∘ₗ CV = CW ∘ₗ TensorProduct.map E' E' :=
    e.symm.toLinearIsometry.exteriorPower_map_comp_lift_twoVectorBracket
  have hcore :
      CW ∘ₗ TensorProduct.map (E' ∘ₗ A ∘ₗ E) (E' ∘ₗ B ∘ₗ E) ∘ₗ CW.adjoint =
        E' ∘ₗ (CV ∘ₗ TensorProduct.map A B ∘ₗ CV.adjoint) ∘ₗ E := by
    calc
      CW ∘ₗ TensorProduct.map (E' ∘ₗ A ∘ₗ E) (E' ∘ₗ B ∘ₗ E) ∘ₗ CW.adjoint
          = (CW ∘ₗ TensorProduct.map E' E') ∘ₗ TensorProduct.map A B ∘ₗ
              (TensorProduct.map E E ∘ₗ CW.adjoint) := by
            simp only [TensorProduct.map_comp, LinearMap.comp_assoc]
      _ = (E' ∘ₗ CV) ∘ₗ TensorProduct.map A B ∘ₗ (CV.adjoint ∘ₗ E) := by
            rw [← hmap, ← e.adjoint_lift_twoVectorBracket_comp_exteriorPower_map]
      _ = E' ∘ₗ (CV ∘ₗ TensorProduct.map A B ∘ₗ CV.adjoint) ∘ₗ E := by
            simp only [LinearMap.comp_assoc]
  have hadj := congrArg (fun T : Module.End ℝ (⋀[ℝ]^2 W) ↦ (1 / 2 : ℝ) • T.adjoint) hcore
  simpa only [TauCeti.bivectorSharpBilin_eq, CW, CV, E, E', LinearMap.adjoint_comp,
    e.adjoint_exteriorPower_map, e.symm.adjoint_exteriorPower_map, LinearIsometryEquiv.symm_symm,
    LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc] using hadj

/-- Conjugating an endomorphism of `⋀[ℝ]^2 V` by the exterior square of a linear isometric
equivalence commutes with `TauCeti.bivectorSharp`. -/
theorem bivectorSharp_conj_exteriorPower_map {W V : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (e : W ≃ₗᵢ[ℝ] V) (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    TauCeti.bivectorSharp (map 2 e.symm.toLinearMap ∘ₗ A ∘ₗ map 2 e.toLinearMap) =
      map 2 e.symm.toLinearMap ∘ₗ TauCeti.bivectorSharp A ∘ₗ map 2 e.toLinearMap :=
  e.bivectorSharpBilin_conj_exteriorPower_map A A

end LinearIsometryEquiv

namespace LinearMap.IsSymmetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The `#` product of two symmetric endomorphisms of `⋀[ℝ]^2 V` is symmetric. -/
theorem bivectorSharpBilin {A B : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric)
    (hB : B.IsSymmetric) :
    (TauCeti.bivectorSharpBilin A B).IsSymmetric :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr <| by
    simp only [IsSelfAdjoint, LinearMap.star_eq_adjoint, TauCeti.adjoint_bivectorSharpBilin,
      hA.adjoint_eq, hB.adjoint_eq]

/-- The `#`-square of a symmetric endomorphism of `⋀[ℝ]^2 V` is symmetric. -/
theorem bivectorSharp {A : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) :
    (TauCeti.bivectorSharp A).IsSymmetric :=
  hA.bivectorSharpBilin hA

end LinearMap.IsSymmetric

end SharpProduct

/-! ### The bivector-operator identity `Q(R) = 2(R² + R#)` -/

section OperatorIdentity

open TauCeti TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem inner_bivectorSharpBilin_eq_sum_ιMulti {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    ⟪bivectorSharpBilin A B ξ, η⟫ =
      (1 / 8 : ℝ) * ∑ p : ι × ι, ∑ q : ι × ι,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b p.1, b p.2]))
          (B (ιMulti ℝ 2 ![b q.1, b q.2])), ξ⟫ *
          ⟪twoVectorBracket (ιMulti ℝ 2 ![b p.1, b p.2])
            (ιMulti ℝ 2 ![b q.1, b q.2]), η⟫ := by
  let e := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  rw [e.inner_bivectorSharpBilin]
  have h := e.sum_sum_apply_mul_eq_quarter_sum_ιMulti b
    ((twoVectorBracket.compl₁₂ A B).compr₂ ((innerₗ (⋀[ℝ]^2 V)).flip ξ))
    (twoVectorBracket.compr₂ ((innerₗ (⋀[ℝ]^2 V)).flip η))
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.flip_apply,
    innerₗ_apply_apply] at h
  rw [h]
  ring

private theorem sum_inner_twoVectorBracket_contract {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ x y : ⋀[ℝ]^2 V) :
    (∑ p : ι × ι, ∑ q : ι × ι,
      ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b p.1, b p.2]))
        (B (ιMulti ℝ 2 ![b q.1, b q.2])), ξ⟫ *
        (⟪ιMulti ℝ 2 ![b p.1, b p.2], x⟫ * ⟪ιMulti ℝ 2 ![b q.1, b q.2], y⟫)) =
      4 * ⟪twoVectorBracket (A x) (B y), ξ⟫ := by
  have h := b.sum_inner_mul_inner_smul_ιMulti_two
    ((twoVectorBracket.compl₁₂ A B).compr₂ ((innerₗ (⋀[ℝ]^2 V)).flip ξ)) x y
  simp only [smul_eq_mul, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    LinearMap.flip_apply, innerₗ_apply_apply] at h
  simp only [Fintype.sum_prod_type]
  rw [← h]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- Reduction of `2 * ⟪TauCeti.bivectorSharpBilin A B ξ, z ∧ w⟫` to a single basis sum over `V`. -/
private theorem two_mul_inner_bivectorSharpBilin_ιMulti_right {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ : ⋀[ℝ]^2 V) (z w : V) :
    2 * ⟪bivectorSharpBilin A B ξ, ιMulti ℝ 2 ![z, w]⟫ =
      ∑ r, (⟪twoVectorBracket (A (ιMulti ℝ 2 ![w, b r])) (B (ιMulti ℝ 2 ![b r, z])), ξ⟫ -
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![z, b r])) (B (ιMulti ℝ 2 ![b r, w])), ξ⟫) := by
  have hsum :
      (∑ p : ι × ι, ∑ q : ι × ι,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b p.1, b p.2]))
          (B (ιMulti ℝ 2 ![b q.1, b q.2])), ξ⟫ *
          ⟪twoVectorBracket (ιMulti ℝ 2 ![b p.1, b p.2]) (ιMulti ℝ 2 ![b q.1, b q.2]),
            ιMulti ℝ 2 ![z, w]⟫) =
      ∑ r, (4 * ⟪twoVectorBracket (A (ιMulti ℝ 2 ![w, b r])) (B (ιMulti ℝ 2 ![b r, z])), ξ⟫ -
        4 * ⟪twoVectorBracket (A (ιMulti ℝ 2 ![z, b r])) (B (ιMulti ℝ 2 ![b r, w])), ξ⟫) := by
    simp_rw [b.inner_twoVectorBracket_ιMulti, Finset.mul_sum, mul_sub]
    rw [Finset.sum_comm_cycle]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    simp only [Finset.sum_sub_distrib, sum_inner_twoVectorBracket_contract b A B ξ]
  rw [inner_bivectorSharpBilin_eq_sum_ιMulti b, hsum, ← mul_assoc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Contraction of `2 • TauCeti.bivectorSharpBilin A B` on pure bivectors in an orthonormal basis
of `V`. -/
private theorem two_mul_inner_bivectorSharpBilin_ιMulti {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {A B : Module.End ℝ (⋀[ℝ]^2 V)}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (u v z w : V) :
    2 * ⟪bivectorSharpBilin A B (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
      ((∑ p, ∑ q, ofExteriorEnd A ![u, b p, z, b q] * ofExteriorEnd B ![v, b p, w, b q]) +
        (∑ p, ∑ q, ofExteriorEnd B ![u, b p, z, b q] * ofExteriorEnd A ![v, b p, w, b q])) -
      ((∑ p, ∑ q, ofExteriorEnd A ![u, b p, w, b q] * ofExteriorEnd B ![v, b p, z, b q]) +
        (∑ p, ∑ q, ofExteriorEnd B ![u, b p, w, b q] * ofExteriorEnd A ![v, b p, z, b q])) := by
  rw [two_mul_inner_bivectorSharpBilin_ιMulti_right b]
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
`ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + 2 • TauCeti.bivectorSharpBilin A B)`. -/
theorem _root_.LinearMap.IsSymmetric.reactionBilinear_ofExteriorEnd
    {A B : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    reactionBilinear V (ofExteriorEnd A) (ofExteriorEnd B) =
      ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + (2 : ℝ) • bivectorSharpBilin A B) := by
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
  have h3 := two_mul_inner_bivectorSharpBilin_ιMulti b hA hB u v z w
  linarith

/-- **Bivector-operator identity**
`Q(ofExteriorEnd A) = ofExteriorEnd (2 • (A * A + TauCeti.bivectorSharp A))` for any symmetric
endomorphism `A` of `⋀[ℝ]^2 V`. -/
theorem _root_.LinearMap.IsSymmetric.reactionTensor_ofExteriorEnd
    {A : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) :
    reactionTensor (ofExteriorEnd A) = ofExteriorEnd ((2 : ℝ) • (A * A + bivectorSharp A)) := by
  rw [← reactionBilinear_self, hA.reactionBilinear_ofExteriorEnd hA]
  congr 1; ext _; simp [two_smul, smul_add]

end OperatorIdentity

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace IsAlgebraicCurvatureEndomorphism

/-- `IsAlgebraicCurvatureEndomorphism` is closed under the polarized Hamilton reaction
`A ∘ₗ B + B ∘ₗ A + 2 • TauCeti.bivectorSharpBilin A B`. -/
theorem comp_add_comp_add_two_smul_bivectorSharpBilin {A B : Module.End ℝ (⋀[ℝ]^2 V)}
    (hA : IsAlgebraicCurvatureEndomorphism A) (hB : IsAlgebraicCurvatureEndomorphism B) :
    IsAlgebraicCurvatureEndomorphism
      (A ∘ₗ B + B ∘ₗ A + (2 : ℝ) • bivectorSharpBilin A B) := by
  rw [← isAlgebraicCurvature_ofExteriorEnd_iff,
    ← hA.isSymmetric.reactionBilinear_ofExteriorEnd hB.isSymmetric]
  exact ((isAlgebraicCurvature_ofExteriorEnd_iff A).mpr hA).reactionBilinear
    ((isAlgebraicCurvature_ofExteriorEnd_iff B).mpr hB)

/-- `IsAlgebraicCurvatureEndomorphism` is closed under Hamilton's quadratic operator
`2 • (A * A + TauCeti.bivectorSharp A)`. -/
theorem two_smul_mul_add_bivectorSharp {A : Module.End ℝ (⋀[ℝ]^2 V)}
    (hA : IsAlgebraicCurvatureEndomorphism A) :
    IsAlgebraicCurvatureEndomorphism ((2 : ℝ) • (A * A + bivectorSharp A)) := by
  rw [← isAlgebraicCurvature_ofExteriorEnd_iff, ← hA.isSymmetric.reactionTensor_ofExteriorEnd]
  exact ((isAlgebraicCurvature_ofExteriorEnd_iff A).mpr hA).reactionTensor

end IsAlgebraicCurvatureEndomorphism

/-- On any four-tensor antisymmetric in its first pair and symmetric under pair interchange,
`curvatureEndomorphism (Q(r)) = 2 • (R² + R#)` with `R = curvatureEndomorphism r`. -/
theorem curvatureEndomorphism_reactionTensor {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hswap : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]) :
    curvatureEndomorphism (reactionTensor r) =
      (2 : ℝ) • (curvatureEndomorphism r * curvatureEndomorphism r +
        bivectorSharp (curvatureEndomorphism r)) := by
  have h₂ (u v z w : V) : r ![u, v, z, w] = -r ![u, v, w, z] := by
    rw [hswap u v z w, h₁ z w u v, hswap w z u v]
  conv_lhs => rw [← ofExteriorEnd_curvatureEndomorphism_of_antisymm h₁ h₂]
  rw [(isSymmetric_curvatureEndomorphism_of_swap_pairs hswap).reactionTensor_ofExteriorEnd,
    curvatureEndomorphism_ofExteriorEnd]

/-- On any bivector-symmetric four-tensor `r`, `curvatureEndomorphism (Q(r)) = 2 • (R² + R#)` with
`R = curvatureEndomorphism r`. -/
theorem IsBivectorSymmetric.curvatureEndomorphism_reactionTensor {r : FourTensor V}
    (hr : IsBivectorSymmetric r) :
    curvatureEndomorphism (FourTensor.reactionTensor r) =
      (2 : ℝ) • (curvatureEndomorphism r * curvatureEndomorphism r +
        bivectorSharp (curvatureEndomorphism r)) :=
  FourTensor.curvatureEndomorphism_reactionTensor hr.antisymm_first hr.swap_pairs

end TauCeti.FourTensor

namespace TauCeti

open TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Explicit evaluation on the identity -/

/-- `TauCeti.bivectorSharp 1 = (dim V - 2) • 1` on `⋀[ℝ]^2 V`, in every dimension
`dim V : ℕ`. -/
@[simp]
theorem bivectorSharp_one :
    bivectorSharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) =
      ((Module.finrank ℝ V : ℝ) - 2) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
  have h :
      ofExteriorEnd ((2 : ℝ) • (1 * 1 + bivectorSharp (1 : Module.End ℝ (⋀[ℝ]^2 V)))) =
        ofExteriorEnd
          ((2 * ((Module.finrank ℝ V : ℝ) - 1)) • (1 : Module.End ℝ (⋀[ℝ]^2 V))) := by
    rw [← LinearMap.IsSymmetric.one.reactionTensor_ofExteriorEnd, ofExteriorEnd_one,
      reactionTensor_constantCurvature, map_smul, ofExteriorEnd_one]
  have h2 : (2 : ℝ) • (1 + bivectorSharp (1 : Module.End ℝ (⋀[ℝ]^2 V))) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
    simpa only [one_mul] using ofExteriorEnd_injective h
  have h1 : 1 + bivectorSharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) =
      ((Module.finrank ℝ V : ℝ) - 1) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
    refine smul_right_injective (Module.End ℝ (⋀[ℝ]^2 V)) (two_ne_zero (α := ℝ)) ?_
    simpa only [smul_smul] using h2
  have hsub : ((Module.finrank ℝ V : ℝ) - 2) = (Module.finrank ℝ V : ℝ) - 1 - 1 := by ring
  rw [eq_sub_of_add_eq' h1, hsub]
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, sub_smul, one_smul]

end TauCeti
