/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Map
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Opposite
public import TauCeti.CategoryTheory.AInfinity.SingleObj
public import TauCeti.CategoryTheory.Graded.Opposite

/-!
# The opposite of an A-infinity category

The **opposite** of an `A∞` category `𝒞` on a graded linear quiver `C` is the `A∞` category on the
opposite quiver `Cᵒᵖ`, whose morphisms `op X ⟶ op Y` are the morphisms `Y ⟶ X` of `𝒞`, and whose
operations read their inputs in the reverse order.  On a composable string of homogeneous
morphisms of degrees `d₀, …, dₙ₋₁` of `Cᵒᵖ`,

`mₙᵒᵖ(x₀, …, xₙ₋₁) = (-1) ^ (∑_{i < j} dᵢ dⱼ + (n - 1).choose 2) • mₙ(xₙ₋₁, …, x₀)`,

the right-hand side being an operation of `𝒞` on the reversed string, which is composable in `C`.
In particular `m₁ᵒᵖ = m₁`, and the composition of the opposite is the composition of `𝒞` in the
reverse order with the Koszul sign: for `f : X ⟶ Y` of degree `p` and `g : Y ⟶ Z` of degree `q`
in `𝒞`, read as morphisms `op Y ⟶ op X` and `op Z ⟶ op Y` of the opposite,
`f ∘ᵒᵖ g = (-1) ^ (p * q) • g ∘ f`, the same sign as for the opposite of a DG category
(`TauCeti.dgComp_op`).

The construction is the opposite `TauCeti.AInfinityAlgebra.op` of the total `A∞` algebra of `𝒞`,
transported to the total module of morphisms of `Cᵒᵖ` along
`TauCeti.GradedLinearQuiver.opTotalHomEquiv`.  The Stasheff identities are those of the opposite
algebra, and the opposite operations are path-compatible on `Cᵒᵖ` because on homogeneous inputs
they are, up to sign, the operations of `𝒞` with their inputs reversed
(`TauCeti.GradedLinearQuiver.IsPathCompatible.reverse`).

## Main definitions

* `TauCeti.AInfinityCategory.op`: the opposite of an `A∞` category.

## Main results

* `TauCeti.AInfinityCategory.op_m_apply`: the operations of the opposite on homogeneous morphisms
  are the reversed operations of `𝒞`, with the opposite sign.
* `TauCeti.AInfinityCategory.coe_pathOperation_op_apply`: the operation of the opposite on a
  composable string is the operation of `𝒞` on the reversed string, with the opposite sign.
* `TauCeti.AInfinityCategory.homDifferential_op`: the opposite has the same differential.
* `TauCeti.AInfinityCategory.comp_op`: composition in the opposite is the Koszul-signed composition
  of `𝒞` in the reverse order.
* `TauCeti.AInfinitySingleObj.coe_pathOperation_op_aInfinityCategory_apply`: the opposite of the
  one-object `A∞` category of an `A∞` algebra has the operations of the opposite algebra.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 7.1.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2,
  for the Koszul sign convention.
-/

public section

open Opposite

namespace TauCeti

universe u v w

open GradedLinearQuiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C)

/-- The operations of the opposite on homogeneous inputs, before the opposite is assembled. -/
private theorem opMap_m_apply {n : ℕ} (d : ℕ → ℤ) (x : Fin n → TotalHom R Cᵒᵖ)
    (hx : ∀ i : Fin n, x i ∈ (totalGrading R Cᵒᵖ).piece (d i)) :
    (𝒞.op.map (opTotalHomEquiv R C)).m n x =
      negOnePowCast R (AInfinity.opExp n d) • reverseOperation (𝒞.m n) x := by
  rw [AInfinityAlgebra.map_m_apply, AInfinityAlgebra.op_m_apply _ d _ fun i ↦ ?_,
    reverseOperation_apply, map_smul]
  rw [𝒞.grading_eq, ← opTotalHomEquiv_mem_totalGrading_piece_iff, LinearEquiv.apply_symm_apply]
  exact hx i

/-- The **opposite** of an `A∞` category: the `A∞` category on the opposite quiver `Cᵒᵖ` whose
operation of arity `n` on homogeneous inputs of degrees `d` is `(-1) ^ opExp n d` times the
operation of `𝒞` on the reversed inputs.  It is the opposite of the total `A∞` algebra of `𝒞`,
transported to the total module of morphisms of `Cᵒᵖ`. -/
noncomputable def op : AInfinityCategory R Cᵒᵖ where
  __ := 𝒞.toAInfinityAlgebra.op.map (opTotalHomEquiv R C)
  grading_eq := by
    rw [AInfinityAlgebra.map_grading, AInfinityAlgebra.op_grading, 𝒞.grading_eq,
      totalGrading_map_opTotalHomEquiv]
  isPathCompatible_m_of_pos n _ := by
    have hr := (𝒞.isPathCompatible_m n).reverse
    refine isPathCompatible_of_homogeneous (fun X x d hx ↦ ?_) fun s t x d hx i j hij hne ↦ ?_
    · rw [𝒞.opMap_m_apply (fun k ↦ if h : k < n then d ⟨k, h⟩ else 0) _ fun i ↦ by simpa using hx i]
      exact Submodule.smul_mem _ _ (hr.mem_range_homInclusion X x)
    · rw [𝒞.opMap_m_apply (fun k ↦ if h : k < n then d ⟨k, h⟩ else 0) _ fun i ↦ by simpa using hx i,
        hr.eq_zero_of_ne s t x i j hij hne, smul_zero]

/-- The total `A∞` algebra of the opposite is the opposite of the total `A∞` algebra, transported
to the total module of morphisms of the opposite quiver. -/
theorem toAInfinityAlgebra_op :
    𝒞.op.toAInfinityAlgebra = 𝒞.toAInfinityAlgebra.op.map (opTotalHomEquiv R C) :=
  (rfl)

/-- **The operations of the opposite** on homogeneous morphisms of degrees `d`: the operation of
`𝒞` on the reversed inputs, with the sign `(-1) ^ opExp n d`. -/
theorem op_m_apply {n : ℕ} (d : ℕ → ℤ) (x : Fin n → TotalHom R Cᵒᵖ)
    (hx : ∀ i : Fin n, x i ∈ (totalGrading R Cᵒᵖ).piece (d i)) :
    𝒞.op.m n x = negOnePowCast R (AInfinity.opExp n d) •
      opTotalHomEquiv R C (𝒞.m n fun i ↦ (opTotalHomEquiv R C).symm (x i.rev)) := by
  rw [← reverseOperation_apply]
  exact 𝒞.opMap_m_apply d x hx

/-- **The operation of the opposite on a composable string** of homogeneous morphisms of degrees
`d` of `Cᵒᵖ` is the operation of `𝒞` on the reversed string, with the sign `(-1) ^ opExp n d`.
The `i`-th input of the reversed string is written with the objects at `i.rev.rev` rather than
`i`, since `x (i.rev)` lives in the hom module between those objects. -/
theorem coe_pathOperation_op_apply {n : ℕ} (X : Fin (n + 1) → Cᵒᵖ) (d : Fin n → ℤ)
    (x : ∀ i, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i)) :
    (𝒞.op.pathOperation X d x : homModule (R := R) (X 0) (X (Fin.last n))) =
      negOnePowCast R (AInfinity.opExp n fun k ↦ if h : k < n then d ⟨k, h⟩ else 0) •
        homProjection (unop (X (Fin.last n))) (unop (X 0))
          (𝒞.m n fun i ↦
            homInclusion (unop (X i.rev.rev.succ)) (unop (X i.rev.rev.castSucc)) (x i.rev).1) := by
  rw [coe_pathOperation_apply, 𝒞.op_m_apply (fun k ↦ if h : k < n then d ⟨k, h⟩ else 0) _
    fun i ↦ by simp, map_smul, homProjection_opTotalHomEquiv]
  simp only [opTotalHomEquiv_symm_homInclusion]

/-- **The opposite has the same differential**: the differential of `op Y ⟶ op X` is the
differential of `X ⟶ Y`. -/
@[simp]
theorem homDifferential_op (X Y : C) (f : homModule (R := R) X Y) :
    𝒞.op.homDifferential (Opposite.op Y) (Opposite.op X) f = 𝒞.homDifferential X Y f := by
  rw [homDifferential_apply, homDifferential_apply, toAInfinityAlgebra_op,
    AInfinityAlgebra.map_m_apply, AInfinityAlgebra.op_m_one, homProjection_opTotalHomEquiv]
  congr 2
  funext i
  fin_cases i
  exact opTotalHomEquiv_symm_homInclusion _ _ f

/-- **Composition in the opposite** is the composition of `𝒞` in the reverse order, with the
Koszul sign: for `f : X ⟶ Y` of degree `p` and `g : Y ⟶ Z` of degree `q`, read as morphisms
`op Y ⟶ op X` and `op Z ⟶ op Y`, their composite `op Z ⟶ op X` is `(-1) ^ (p * q) • g ∘ f`. -/
theorem comp_op {X Y Z : C} {p q : ℤ} {f : homModule (R := R) X Y} {g : homModule (R := R) Y Z}
    (hf : f ∈ (grading (R := R) X Y).piece p) (hg : g ∈ (grading (R := R) Y Z).piece q) :
    𝒞.op.comp (Opposite.op Z) (Opposite.op Y) (Opposite.op X) f g =
      negOnePowCast R (p * q) • 𝒞.comp X Y Z g f := by
  have e : (fun i ↦ (opTotalHomEquiv R C).symm
      (![homInclusion (R := R) (Opposite.op Y) (Opposite.op X) f,
        homInclusion (Opposite.op Z) (Opposite.op Y) g] i)) =
      ![homInclusion X Y f, homInclusion Y Z g] := by
    funext i
    fin_cases i <;> exact opTotalHomEquiv_symm_homInclusion _ _ _
  rw [comp_apply, comp_apply, toAInfinityAlgebra_op, AInfinityAlgebra.map_m_apply, e,
    AInfinityAlgebra.op_m_two_apply _
      (by rwa [𝒞.grading_eq, homInclusion_mem_totalGrading_piece_iff])
      (by rwa [𝒞.grading_eq, homInclusion_mem_totalGrading_piece_iff]),
    map_smul, map_smul, homProjection_opTotalHomEquiv]

end AInfinityCategory

namespace AInfinitySingleObj

variable {R : Type w} [CommRing R] {A : Type v} [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-- **The opposite of the one-object `A∞` category of an `A∞` algebra has the operations of the
opposite algebra.** -/
@[simp]
theorem coe_pathOperation_op_aInfinityCategory_apply {n : ℕ}
    (X : Fin (n + 1) → (AInfinitySingleObj 𝒜)ᵒᵖ) (d : Fin n → ℤ)
    (x : ∀ i, grHom R (X i.rev.castSucc) (X i.rev.succ) (d i)) :
    ((aInfinityCategory 𝒜).op.pathOperation X d x : A) = 𝒜.op.m n fun i ↦ (x i : A) := by
  obtain rfl : X = fun _ ↦ Opposite.op (star 𝒜) := funext fun _ ↦ unop_injective rfl
  rw [AInfinityCategory.coe_pathOperation_op_apply,
    AInfinityAlgebra.op_m_apply 𝒜 (fun k ↦ if h : k < n then d ⟨k, h⟩ else 0) _
      fun i ↦ by simp]
  simp [toAInfinityAlgebra_aInfinityCategory]

end AInfinitySingleObj

end TauCeti
