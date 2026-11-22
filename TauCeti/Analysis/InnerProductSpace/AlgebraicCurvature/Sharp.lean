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
Hamilton's symmetric bilinear Lie-algebraic product `Module.End.sharpBilin A B` and
`Module.End.sharp A = A.sharpBilin A` using the bivector Lie bracket `TauCeti.twoVectorBracket`,
```
⟪A.sharpBilin B ξ, η⟫ = (1 / 2) ∑_α ∑_β ⟪[A ω_α, B ω_β], ξ⟫ ⟪[ω_α, ω_β], η⟫.
```
We prove that `sharpBilin` and `sharp` preserve symmetry, are equivariant under conjugation by
linear isometric equivalences, evaluate `sharp 1 = (dim V - 2) • 1`, and establish the polarized
and quadratic bivector-operator identities
`reactionBilinear V (ofExteriorEnd A) (ofExteriorEnd B) =`
`ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + 2 • A.sharpBilin B)`,
`Q(ofExteriorEnd A) = ofExteriorEnd (2 • (A * A + A.sharp))`, and
`curvatureEndomorphism (Q(r)) = 2 • (R² + R#)` for every symmetric endomorphism `A` of `⋀[ℝ]^2 V`
and every bivector-symmetric four-tensor `r`.

## Main definitions

* `Module.End.sharpBilin` and `Module.End.sharp`: Hamilton's Lie-algebraic `#` product on
  `Module.End ℝ (⋀[ℝ]^2 V)`.

## Main statements

* `OrthonormalBasis.inner_sharpBilin`: basis formula for `Module.End.sharpBilin`.
* `LinearIsometryEquiv.sharpBilin_conj_exteriorPowerMap` and
  `LinearIsometryEquiv.sharp_conj_exteriorPowerMap`: frame-change conjugation laws for
  `sharpBilin` and `sharp`.
* `LinearMap.IsSymmetric.sharpBilin` and `LinearMap.IsSymmetric.sharp`: preservation of symmetry.
* `Module.End.sharp_one`: `Module.End.sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) = (dim V - 2) • 1`.
* `LinearMap.IsSymmetric.reactionBilinear_ofExteriorEnd`,
  `LinearMap.IsSymmetric.reactionTensor_ofExteriorEnd`,
  `TauCeti.FourTensor.curvatureEndomorphism_reactionTensor`, and
  `TauCeti.FourTensor.IsBivectorSymmetric.curvatureEndomorphism_reactionTensor`: the operator
  identity `Q(R) = 2 (R² + R#)`.

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

private abbrev bracketLift (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    (⋀[ℝ]^2 V) ⊗[ℝ] (⋀[ℝ]^2 V) →ₗ[ℝ] ⋀[ℝ]^2 V :=
  TensorProduct.lift TauCeti.twoVectorBracket

namespace Module.End

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### Hamilton's `#` product -/

/-- Hamilton's symmetric bilinear Lie-algebraic `#` product on `Module.End ℝ (⋀[ℝ]^2 V)`,
characterized in any orthonormal basis `e` of `⋀[ℝ]^2 V` by
`⟪A.sharpBilin B ξ, η⟫ = (1 / 2) ∑ α β, ⟪[A (e α), B (e β)], ξ⟫ ⟪[e α, e β], η⟫`. -/
def sharpBilin :
    Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) :=
  let C := bracketLift V
  let mapBil := TensorProduct.mapBilinear (RingHom.id ℝ)
    (⋀[ℝ]^2 V) (⋀[ℝ]^2 V) (⋀[ℝ]^2 V) (⋀[ℝ]^2 V)
  let adj : Module.End ℝ (⋀[ℝ]^2 V) →ₗ[ℝ] Module.End ℝ (⋀[ℝ]^2 V) :=
    (LinearMap.adjoint : Module.End ℝ (⋀[ℝ]^2 V) ≃ₗ⋆[ℝ] Module.End ℝ (⋀[ℝ]^2 V)).toLinearMap
  (1 / 2 : ℝ) •
    ((mapBil.compr₂ ((LinearMap.llcomp ℝ (⋀[ℝ]^2 V) _ _).flip C.adjoint)).compr₂
      (LinearMap.llcomp ℝ (⋀[ℝ]^2 V) _ _ C)).compr₂ adj

/-- Basis-free expression for `Module.End.sharpBilin A B` in terms of `TensorProduct.lift` of
`TauCeti.twoVectorBracket` and its adjoint. -/
theorem sharpBilin_eq (A B : Module.End ℝ (⋀[ℝ]^2 V)) :
    A.sharpBilin B =
      (1 / 2 : ℝ) •
        (TensorProduct.lift (TauCeti.twoVectorBracket (V := V)) ∘ₗ TensorProduct.map A B ∘ₗ
          LinearMap.adjoint (𝕜 := ℝ) (E := (⋀[ℝ]^2 V) ⊗[ℝ] (⋀[ℝ]^2 V)) (F := ⋀[ℝ]^2 V)
            (TensorProduct.lift TauCeti.twoVectorBracket)).adjoint := by
  simp only [sharpBilin]
  rfl

/-- Hamilton's quadratic `#` operator `A.sharp = A.sharpBilin A` on `Module.End ℝ (⋀[ℝ]^2 V)`. -/
def sharp (A : Module.End ℝ (⋀[ℝ]^2 V)) : Module.End ℝ (⋀[ℝ]^2 V) :=
  A.sharpBilin A

/-- Evaluation of `Module.End.sharpBilin A B` in any orthonormal basis of `⋀[ℝ]^2 V`. -/
theorem _root_.OrthonormalBasis.inner_sharpBilin {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (⋀[ℝ]^2 V)) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    ⟪A.sharpBilin B ξ, η⟫ =
      (1 / 2 : ℝ) * ∑ α, ∑ β,
        ⟪TauCeti.twoVectorBracket (A (e α)) (B (e β)), ξ⟫ *
          ⟪TauCeti.twoVectorBracket (e α) (e β), η⟫ := by
  rw [sharpBilin_eq, LinearMap.smul_apply, real_inner_smul_left,
    LinearMap.adjoint_inner_left, LinearMap.comp_apply, LinearMap.comp_apply]
  have hη : (bracketLift V).adjoint η =
      ∑ p : ι × ι, ⟪TauCeti.twoVectorBracket (e p.1) (e p.2), η⟫ • (e p.1 ⊗ₜ[ℝ] e p.2) := by
    conv_lhs => rw [← (e.tensorProduct e).sum_repr' ((bracketLift V).adjoint η)]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [OrthonormalBasis.tensorProduct_apply, LinearMap.adjoint_inner_right]
    dsimp only [bracketLift]
    rw [TensorProduct.lift.tmul]
  rw [hη, map_sum, map_sum, inner_sum]
  simp only [map_smul, TensorProduct.map_tmul, TensorProduct.lift.tmul, real_inner_smul_right,
    Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦ ?_
  rw [real_inner_comm ξ, mul_comm]

/-- `Module.End.sharpBilin` is symmetric in its two endomorphism arguments. -/
theorem sharpBilin_comm (A B : Module.End ℝ (⋀[ℝ]^2 V)) : A.sharpBilin B = B.sharpBilin A := by
  let e := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  rw [e.inner_sharpBilin, e.inner_sharpBilin]
  congr 1; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun α _ ↦ Finset.sum_congr rfl fun β _ ↦ by
    rw [TauCeti.twoVectorBracket_swap (B (e α)) (A (e β)),
      TauCeti.twoVectorBracket_swap (e α) (e β), inner_neg_left, inner_neg_left, neg_mul_neg]

/-- The diagonal of `Module.End.sharpBilin` is `Module.End.sharp`. -/
@[simp]
theorem sharpBilin_self (A : Module.End ℝ (⋀[ℝ]^2 V)) : A.sharpBilin A = A.sharp :=
  (rfl)

/-- `Module.End.sharp 0 = 0`. -/
@[simp]
theorem sharp_zero : sharp (0 : Module.End ℝ (⋀[ℝ]^2 V)) = 0 := by
  simp [sharp]

/-- `Module.End.sharp (-A) = Module.End.sharp A`. -/
@[simp]
theorem sharp_neg (A : Module.End ℝ (⋀[ℝ]^2 V)) : sharp (-A) = sharp A := by
  simp only [sharp, map_neg, LinearMap.neg_apply, neg_neg]

/-- `Module.End.sharp (c • A) = c ^ 2 • Module.End.sharp A`. -/
@[simp]
theorem sharp_smul (c : ℝ) (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    sharp (c • A) = (c ^ 2) • sharp A := by
  simp only [sharp, map_smul, LinearMap.smul_apply, smul_smul, sq]

/-- Quadratic expansion of `Module.End.sharp` on a sum of endomorphisms. -/
theorem sharp_add (A B : Module.End ℝ (⋀[ℝ]^2 V)) :
    sharp (A + B) = sharp A + (2 : ℝ) • A.sharpBilin B + sharp B := by
  simp only [sharp, map_add, LinearMap.add_apply, sharpBilin_comm B A, two_smul]
  abel

/-- Every rank-one operator `ξ ↦ ⟪α, ξ⟫ • α` on `⋀[ℝ]^2 V` has vanishing `#`-square. -/
@[simp]
theorem sharp_rankOne_self (α : ⋀[ℝ]^2 V) :
    sharp (InnerProductSpace.rankOne ℝ α α).toLinearMap = 0 := by
  refine LinearMap.ext fun ξ ↦ ext_inner_right ℝ fun η ↦ ?_
  rw [← sharpBilin_self, (stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)).inner_sharpBilin]
  simp [InnerProductSpace.rankOne_apply]

end Module.End

namespace LinearIsometryEquiv

private theorem map_comp_bracketLift {W V : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (f : W →ₗᵢ[ℝ] V) :
    map 2 f.toLinearMap ∘ₗ bracketLift W =
      bracketLift V ∘ₗ TensorProduct.map (map 2 f.toLinearMap) (map 2 f.toLinearMap) :=
  TensorProduct.ext' fun x y ↦ f.exteriorPowerMap_twoVectorBracket x y

private theorem adjoint_bracketLift_comp_map {W V : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (e : W ≃ₗᵢ[ℝ] V) :
    (bracketLift V).adjoint ∘ₗ map 2 e.toLinearMap =
      TensorProduct.map (map 2 e.toLinearMap) (map 2 e.toLinearMap) ∘ₗ
        (bracketLift W).adjoint := by
  have h : LinearMap.adjoint (map 2 e.symm.toLinearMap ∘ₗ bracketLift V) =
      LinearMap.adjoint
        (bracketLift W ∘ₗ
          TensorProduct.map (map 2 e.symm.toLinearMap) (map 2 e.symm.toLinearMap)) :=
    congrArg LinearMap.adjoint (map_comp_bracketLift e.symm.toLinearIsometry)
  simpa only [LinearMap.adjoint_comp, TensorProduct.adjoint_map,
    e.symm.adjoint_exteriorPowerMap, LinearIsometryEquiv.symm_symm] using h

/-- Conjugating two endomorphisms of `⋀[ℝ]^2 V` by the exterior square of a linear isometric
equivalence commutes with `Module.End.sharpBilin`. -/
theorem sharpBilin_conj_exteriorPowerMap {W V : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (e : W ≃ₗᵢ[ℝ] V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) :
    Module.End.sharpBilin
        (map 2 e.symm.toLinearMap ∘ₗ A ∘ₗ map 2 e.toLinearMap)
        (map 2 e.symm.toLinearMap ∘ₗ B ∘ₗ map 2 e.toLinearMap) =
      map 2 e.symm.toLinearMap ∘ₗ Module.End.sharpBilin A B ∘ₗ map 2 e.toLinearMap := by
  let E := map 2 e.toLinearMap
  let E' := map 2 e.symm.toLinearMap
  have hmap : E' ∘ₗ bracketLift V = bracketLift W ∘ₗ TensorProduct.map E' E' :=
    map_comp_bracketLift e.symm.toLinearIsometry
  have hcore :
      bracketLift W ∘ₗ TensorProduct.map (E' ∘ₗ A ∘ₗ E) (E' ∘ₗ B ∘ₗ E) ∘ₗ
          (bracketLift W).adjoint =
        E' ∘ₗ (bracketLift V ∘ₗ TensorProduct.map A B ∘ₗ (bracketLift V).adjoint) ∘ₗ E := by
    calc
      bracketLift W ∘ₗ TensorProduct.map (E' ∘ₗ A ∘ₗ E) (E' ∘ₗ B ∘ₗ E) ∘ₗ
            (bracketLift W).adjoint
          = (bracketLift W ∘ₗ TensorProduct.map E' E') ∘ₗ TensorProduct.map A B ∘ₗ
              (TensorProduct.map E E ∘ₗ (bracketLift W).adjoint) := by
            simp only [TensorProduct.map_comp, LinearMap.comp_assoc]
      _ = (E' ∘ₗ bracketLift V) ∘ₗ TensorProduct.map A B ∘ₗ ((bracketLift V).adjoint ∘ₗ E) := by
            rw [← hmap, ← adjoint_bracketLift_comp_map e]
      _ = E' ∘ₗ (bracketLift V ∘ₗ TensorProduct.map A B ∘ₗ (bracketLift V).adjoint) ∘ₗ E := by
            simp only [LinearMap.comp_assoc]
  have hadj := congrArg (fun T : Module.End ℝ (⋀[ℝ]^2 W) ↦ (1 / 2 : ℝ) • T.adjoint) hcore
  simpa only [Module.End.sharpBilin_eq, bracketLift, E, E', LinearMap.adjoint_comp,
    e.adjoint_exteriorPowerMap, e.symm.adjoint_exteriorPowerMap, LinearIsometryEquiv.symm_symm,
    LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc] using hadj

/-- Conjugating an endomorphism of `⋀[ℝ]^2 V` by the exterior square of a linear isometric
equivalence commutes with `Module.End.sharp`. -/
theorem sharp_conj_exteriorPowerMap {W V : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (e : W ≃ₗᵢ[ℝ] V) (A : Module.End ℝ (⋀[ℝ]^2 V)) :
    Module.End.sharp (map 2 e.symm.toLinearMap ∘ₗ A ∘ₗ map 2 e.toLinearMap) =
      map 2 e.symm.toLinearMap ∘ₗ Module.End.sharp A ∘ₗ map 2 e.toLinearMap :=
  e.sharpBilin_conj_exteriorPowerMap A A

end LinearIsometryEquiv

namespace LinearMap.IsSymmetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The `#` product of two symmetric endomorphisms of `⋀[ℝ]^2 V` is symmetric. -/
theorem sharpBilin {A B : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (Module.End.sharpBilin A B).IsSymmetric := by
  have hAB : (TensorProduct.map A B).IsSymmetric := fun x y ↦ by
    rw [← LinearMap.adjoint_inner_right, TensorProduct.adjoint_map, hA.adjoint_eq, hB.adjoint_eq]
  have hconj := hAB.conj_adjoint (bracketLift V)
  rw [Module.End.sharpBilin_eq, hconj.adjoint_eq]
  exact LinearMap.IsSymmetric.smul (star_trivial _) hconj

/-- The `#`-square of a symmetric endomorphism of `⋀[ℝ]^2 V` is symmetric. -/
theorem sharp {A : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) :
    (Module.End.sharp A).IsSymmetric :=
  hA.sharpBilin hA

end LinearMap.IsSymmetric

end SharpProduct

/-! ### The bivector-operator identity `Q(R) = 2(R² + R#)` -/

section OperatorIdentity

open TauCeti TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem inner_sharpBilin_eq_sum_ιMulti {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ η : ⋀[ℝ]^2 V) :
    ⟪Module.End.sharpBilin A B ξ, η⟫ =
      (1 / 8 : ℝ) * ∑ p : ι × ι, ∑ q : ι × ι,
        ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b p.1, b p.2]))
          (B (ιMulti ℝ 2 ![b q.1, b q.2])), ξ⟫ *
          ⟪twoVectorBracket (ιMulti ℝ 2 ![b p.1, b p.2])
            (ιMulti ℝ 2 ![b q.1, b q.2]), η⟫ := by
  let e := stdOrthonormalBasis ℝ (⋀[ℝ]^2 V)
  rw [e.inner_sharpBilin]
  have hinner (x y : ⋀[ℝ]^2 V) :
      (∑ β, ⟪twoVectorBracket x (B (e β)), ξ⟫ * ⟪twoVectorBracket y (e β), η⟫) =
        (1 / 2 : ℝ) * ∑ q : ι × ι,
          ⟪twoVectorBracket x (B (ιMulti ℝ 2 ![b q.1, b q.2])), ξ⟫ *
            ⟪twoVectorBracket y (ιMulti ℝ 2 ![b q.1, b q.2]), η⟫ := by
    rw [Fintype.sum_prod_type]
    exact e.sum_apply_mul_eq_half_sum_ιMulti b
      (((innerₗ (⋀[ℝ]^2 V)).flip ξ).comp ((twoVectorBracket x).comp B))
      (((innerₗ (⋀[ℝ]^2 V)).flip η).comp (twoVectorBracket y))
  simp_rw [hinner, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have houter (q : ι × ι) :
      (∑ α,
        ⟪twoVectorBracket (A (e α)) (B (ιMulti ℝ 2 ![b q.1, b q.2])), ξ⟫ *
          ⟪twoVectorBracket (e α) (ιMulti ℝ 2 ![b q.1, b q.2]), η⟫) =
        (1 / 2 : ℝ) * ∑ p : ι × ι,
          ⟪twoVectorBracket (A (ιMulti ℝ 2 ![b p.1, b p.2]))
            (B (ιMulti ℝ 2 ![b q.1, b q.2])), ξ⟫ *
            ⟪twoVectorBracket (ιMulti ℝ 2 ![b p.1, b p.2])
              (ιMulti ℝ 2 ![b q.1, b q.2]), η⟫ := by
    rw [Fintype.sum_prod_type]
    exact e.sum_apply_mul_eq_half_sum_ιMulti b
      (((innerₗ (⋀[ℝ]^2 V)).flip ξ).comp
        ((twoVectorBracket.flip (B (ιMulti ℝ 2 ![b q.1, b q.2]))).comp A))
      (((innerₗ (⋀[ℝ]^2 V)).flip η).comp
        (twoVectorBracket.flip (ιMulti ℝ 2 ![b q.1, b q.2])))
  simp_rw [houter, ← Finset.mul_sum]
  rw [Finset.sum_comm]
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

/-- Reduction of `2 * ⟪Module.End.sharpBilin A B ξ, z ∧ w⟫` to a single basis sum over `V`. -/
private theorem two_mul_inner_sharpBilin_ιMulti_right {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (A B : Module.End ℝ (⋀[ℝ]^2 V)) (ξ : ⋀[ℝ]^2 V) (z w : V) :
    2 * ⟪Module.End.sharpBilin A B ξ, ιMulti ℝ 2 ![z, w]⟫ =
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
  rw [inner_sharpBilin_eq_sum_ιMulti b, hsum, ← mul_assoc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- Contraction of `2 • Module.End.sharpBilin A B` on pure bivectors in an orthonormal basis of
`V`. -/
private theorem two_mul_inner_sharpBilin_ιMulti {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) {A B : Module.End ℝ (⋀[ℝ]^2 V)}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (u v z w : V) :
    2 * ⟪Module.End.sharpBilin A B (ιMulti ℝ 2 ![u, v]), ιMulti ℝ 2 ![z, w]⟫ =
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
`ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + 2 • A.sharpBilin B)`. -/
theorem _root_.LinearMap.IsSymmetric.reactionBilinear_ofExteriorEnd
    {A B : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    reactionBilinear V (ofExteriorEnd A) (ofExteriorEnd B) =
      ofExteriorEnd (A ∘ₗ B + B ∘ₗ A + (2 : ℝ) • A.sharpBilin B) := by
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

/-- **Bivector-operator identity** `Q(ofExteriorEnd A) = ofExteriorEnd (2 • (A * A + A.sharp))`
for any symmetric endomorphism `A` of `⋀[ℝ]^2 V`. -/
theorem _root_.LinearMap.IsSymmetric.reactionTensor_ofExteriorEnd
    {A : Module.End ℝ (⋀[ℝ]^2 V)} (hA : A.IsSymmetric) :
    reactionTensor (ofExteriorEnd A) = ofExteriorEnd ((2 : ℝ) • (A * A + A.sharp)) := by
  rw [← reactionBilinear_self, hA.reactionBilinear_ofExteriorEnd hA]
  congr 1; ext _; simp [two_smul, smul_add]

end OperatorIdentity

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- On any four-tensor antisymmetric in its first pair and symmetric under pair interchange,
`curvatureEndomorphism (Q(r)) = 2 • (R² + R#)` with `R = curvatureEndomorphism r`. -/
theorem curvatureEndomorphism_reactionTensor {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (hswap : ∀ u v z w, r ![u, v, z, w] = r ![z, w, u, v]) :
    curvatureEndomorphism (reactionTensor r) =
      (2 : ℝ) • (curvatureEndomorphism r * curvatureEndomorphism r +
        (curvatureEndomorphism r).sharp) := by
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
        (curvatureEndomorphism r).sharp) :=
  FourTensor.curvatureEndomorphism_reactionTensor hr.antisymm_first hr.swap_pairs

/-! ### Explicit evaluation on the identity -/

/-- `Module.End.sharp 1 = (dim V - 2) • 1` on `⋀[ℝ]^2 V`, in every dimension `dim V : ℕ`. -/
@[simp]
theorem _root_.Module.End.sharp_one :
    Module.End.sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) =
      ((Module.finrank ℝ V : ℝ) - 2) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
  have h :
      ofExteriorEnd ((2 : ℝ) • (1 * 1 + Module.End.sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)))) =
        ofExteriorEnd
          ((2 * ((Module.finrank ℝ V : ℝ) - 1)) • (1 : Module.End ℝ (⋀[ℝ]^2 V))) := by
    rw [← LinearMap.IsSymmetric.one.reactionTensor_ofExteriorEnd, ofExteriorEnd_one,
      reactionTensor_constantCurvature, map_smul, ofExteriorEnd_one]
  have h2 : (2 : ℝ) • (1 + Module.End.sharp (1 : Module.End ℝ (⋀[ℝ]^2 V))) =
      (2 * ((Module.finrank ℝ V : ℝ) - 1)) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
    simpa only [one_mul] using ofExteriorEnd_injective h
  have h1 : 1 + Module.End.sharp (1 : Module.End ℝ (⋀[ℝ]^2 V)) =
      ((Module.finrank ℝ V : ℝ) - 1) • (1 : Module.End ℝ (⋀[ℝ]^2 V)) := by
    refine smul_right_injective (Module.End ℝ (⋀[ℝ]^2 V)) (two_ne_zero (α := ℝ)) ?_
    simpa only [smul_smul] using h2
  have hsub : ((Module.finrank ℝ V : ℝ) - 2) = (Module.finrank ℝ V : ℝ) - 1 - 1 := by ring
  rw [eq_sub_of_add_eq' h1, hsub]
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self, sub_smul, one_smul]

end TauCeti.FourTensor
