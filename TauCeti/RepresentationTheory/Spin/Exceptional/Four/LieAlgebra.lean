/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Representation
public import TauCeti.RepresentationTheory.Spin.Structure
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Characterization
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Four
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.MatrixProd
import TauCeti.RepresentationTheory.Spin.Dimension
import TauCeti.RepresentationTheory.Spin.Polarization.Faithful

/-!
# The half-spin Lie modules of `so₄`: the isomorphism `D₂ ≅ A₁ × A₁`

Let `P` be an even polarization `V = W ⊕ W'` with `dim W = 2`, over a field in which `2` is
invertible, and let `b` be a basis of `W`. The split type-`D` matrix Lie algebra `so₄` acts on
the two half-spin modules `S⁺ = ⋀ᵉᵛᵉⁿ W` and `S⁻ = ⋀ᵒᵈᵈ W`, both of dimension two, through its
quadratic Clifford realization (`TauCeti.SpinPolarizationData.typeDSpinPlusLieRep` and
`TauCeti.SpinPolarizationData.typeDSpinMinusLieRep`). This file proves that these are the
standard modules of the two factors of `sl₂ × sl₂`:

* the paired action on `S⁺ × S⁻` is faithful, and its image consists exactly of the pairs of
  trace-zero endomorphisms;
* consequently, for bases of `S⁺` and `S⁻`, sending an element of `so₄` to the matrices of its two
  half-spin actions is a Lie algebra isomorphism `so₄ ≃ sl₂ × sl₂`, under which `S⁺` is the
  standard module of the first factor and `S⁻` that of the second.

In particular each half-spin action alone has image `sl₂`; it is not faithful, since the other
factor acts on it trivially. This is the Lie-algebra counterpart of the group isomorphism
`exists_spinGroup_mulEquiv_specialLinearGroup_prod_and_halfSpin_equiv_stdSLRep_of_finrank_eq_four`
in `TauCeti`, and it is the restriction of the same matrix model of the even Clifford algebra
(`typeDHalfSpinLieEquivSlProdSl_apply_eq_evenCliffordEquivProdEnd`).

## The argument

The even structure theorem `TauCeti.SpinPolarizationData.evenCliffordEquivProdEnd` identifies the
even Clifford algebra with `End S⁺ × End S⁻`, and in matrices with `M₂ × M₂`. In this model
reversal is adjugation in both factors (`map_reverseEven_eq_adjugate_prod_of_finrank_eq_four`),
and a `2 × 2` matrix `A` has adjugate `tr A • 1 - A`. So an even element is negated by reversal
exactly when both of its half-spin actions have trace zero. Quadratic Clifford elements are negated
by reversal, which gives the trace condition. Conversely, an even element negated by reversal has
odd commutators with vectors that are fixed by reversal; in dimension four these are vectors
(`mem_range_ι_of_mem_evenOdd_one_of_reverse_eq_of_finrank_le_four`), so the element is quadratic
(`mem_quadraticLieSubalgebra_of_mem_even_of_reverse_eq_neg_of_lie_ι_mem_range_ι`). The paired
action is injective in every rank
(`TauCeti.SpinPolarizationData.typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_injective`).

## Main definitions and results

All declarations are in the namespace `TauCeti.SpinPolarizationData`.

* `trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_two` and
  `trace_typeDSpinMinusLieRep_eq_zero_of_card_eq_two`: `so₄` acts on each half-spin module by
  trace-zero endomorphisms.
* `mem_range_typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_iff_of_card_eq_two`: the image of the
  paired action consists of the pairs of trace-zero endomorphisms.
* `mem_range_typeDSpinPlusLieRep_iff_of_card_eq_two` and
  `mem_range_typeDSpinMinusLieRep_iff_of_card_eq_two`: each half-spin image is `sl₂`.
* `typeDHalfSpinLieEquivSlProdSl`: the Lie algebra isomorphism `so₄ ≃ sl₂ × sl₂` given by the
  matrices of the two half-spin actions.
* `typeDHalfSpinLieEquivSlProdSl_apply_eq_evenCliffordEquivProdEnd`: this isomorphism is the
  matrix model of the even Clifford algebra, applied to the quadratic Clifford realization.
* `typeDSpinPlusLieModuleEquivStd` and `typeDSpinMinusLieModuleEquivStd`: through this
  isomorphism, `S⁺` and `S⁻` are the standard modules of the first and second factor `sl₂`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open CliffordAlgebra Module LieAlgebra

namespace TauCeti.SpinPolarizationData

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] [Invertible (2 : K)] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Basis ι K P.W) (hline : P.line = ⊥)

/-! ### Reversal on the even Clifford algebra in dimension four -/

omit [Invertible (2 : K)] [DecidableEq ι] in
include b hline in
private theorem finrank_eq_four_of_card_eq_two (hι : Fintype.card ι = 2) : finrank K V = 4 := by
  classical
  rw [finrank_eq_card_basis (P.typeDBasis b hline), Fintype.card_sum, hι]

omit [DecidableEq ι] in
include b in
/-- In dimension four, an even Clifford element is negated by reversal exactly when it acts on both
half-spin modules by trace-zero endomorphisms: in the matrix model `M₂ × M₂`, reversal is
adjugation, and `adjugate A = tr A • 1 - A`. -/
private theorem reverseEven_eq_neg_iff_trace_eq_zero (hι : Fintype.card ι = 2) (z : even Q) :
    reverseEven Q z = -z ↔
      LinearMap.trace K (spinPlus Q P) (spinPlusAction Q P hline z) = 0 ∧
        LinearMap.trace K (spinMinus Q P) (spinMinusAction Q P hline z) = 0 := by
  have hV := P.finrank_eq_four_of_card_eq_two b hline hι
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional K P.W := b.finiteDimensional_of_finite
  have hW : finrank K P.W = 2 := by rw [finrank_eq_card_basis b, hι]
  have hplus : finrank K (spinPlus Q P) = 2 := by rw [finrank_spinPlus P, hW]; rfl
  have hminus : finrank K (spinMinus Q P) = 2 := by
    rw [finrank_spinMinus P (Submodule.finrank_eq_zero.not.1 (by omega)), hW]; rfl
  let B := Module.finBasisOfFinrankEq K (spinPlus Q P) hplus
  let B' := Module.finBasisOfFinrankEq K (spinMinus Q P) hminus
  let e := (P.evenCliffordEquivProdEnd hline).trans
    ((LinearMap.toMatrixAlgEquiv B).prodCongr (LinearMap.toMatrixAlgEquiv B'))
  have he (y : even Q) : e y = (LinearMap.toMatrix B B (spinPlusAction Q P hline y),
      LinearMap.toMatrix B' B' (spinMinusAction Q P hline y)) := by
    simp only [e, AlgEquiv.trans_apply, AlgEquiv.prodCongr_apply,
      P.evenCliffordEquivProdEnd_apply, evenSpinActionProd_apply,
      LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply,
      Equiv.prodCongr_apply, Prod.map_apply, AlgEquiv.coe_toEquiv]
  have h := map_reverseEven_eq_adjugate_prod_of_finrank_eq_four Q
    (P.nondegenerate_of_line_eq_bot hline) hV e z
  rw [← e.injective.eq_iff, h, map_neg, he, Prod.neg_mk, Prod.mk.injEq,
    Matrix.adjugate_fin_two_eq_trace_smul_one_sub, Matrix.adjugate_fin_two_eq_trace_smul_one_sub,
    sub_eq_neg_self, sub_eq_neg_self, smul_eq_zero, smul_eq_zero,
    LinearMap.trace_eq_matrix_trace K B, LinearMap.trace_eq_matrix_trace K B']
  simp

omit [DecidableEq ι] in
include b hline in
/-- In dimension four, an even Clifford element negated by reversal is quadratic: its commutator
with a vector is odd and fixed by reversal, hence a vector. -/
private theorem mem_quadraticLieSubalgebra_of_reverseEven_eq_neg (hι : Fintype.card ι = 2)
    {z : even Q} (hz : reverseEven Q z = -z) :
    (z : CliffordAlgebra Q) ∈ quadraticLieSubalgebra Q := by
  have hV := P.finrank_eq_four_of_card_eq_two b hline hι
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have hrev : reverse (z : CliffordAlgebra Q) = -z := by
    simpa using congrArg Subtype.val hz
  have hz0 : (z : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]
    exact z.property
  refine mem_quadraticLieSubalgebra_of_mem_even_of_reverse_eq_neg_of_lie_ι_mem_range_ι Q
    (P.nondegenerate_of_line_eq_bot hline) z.property hrev fun v ↦ ?_
  refine mem_range_ι_of_mem_evenOdd_one_of_reverse_eq_of_finrank_le_four Q hV.le ?_ ?_
  · rw [Ring.lie_def]
    exact Submodule.sub_mem _
      (by simpa using SetLike.mul_mem_graded hz0 (ι_mem_evenOdd_one Q v))
      (by simpa using SetLike.mul_mem_graded (ι_mem_evenOdd_one Q v) hz0)
  · rw [Ring.lie_def, map_sub, reverse.map_mul, reverse.map_mul, reverse_ι, hrev, mul_neg, neg_mul,
      sub_neg_eq_add, neg_add_eq_sub]

include b in
/-- Both half-spin actions of an element of `so₄` have trace zero, since its quadratic Clifford
realization is negated by reversal. -/
private theorem trace_typeDSpinLieRep_eq_zero_of_card_eq_two (hι : Fintype.card ι = 2)
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    LinearMap.trace K (spinPlus Q P) (P.typeDSpinPlusLieRep b hline x) = 0 ∧
      LinearMap.trace K (spinMinus Q P) (P.typeDSpinMinusLieRep b hline x) = 0 := by
  have h := P.evenSpinActionProd_typeDQuadraticEquiv b hline x
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at h
  rw [← h.1, ← h.2, ← P.reverseEven_eq_neg_iff_trace_eq_zero b hline hι]
  exact Subtype.ext (by simp)

/-! ### The image of `so₄` in `End S⁺ × End S⁻` -/

/-- Every element of `so₄` acts on the even half-spin module by an endomorphism of trace zero. -/
@[simp]
theorem trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_two (hι : Fintype.card ι = 2)
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    LinearMap.trace K (spinPlus Q P) (P.typeDSpinPlusLieRep b hline x) = 0 :=
  (P.trace_typeDSpinLieRep_eq_zero_of_card_eq_two b hline hι x).1

/-- Every element of `so₄` acts on the odd half-spin module by an endomorphism of trace zero. -/
@[simp]
theorem trace_typeDSpinMinusLieRep_eq_zero_of_card_eq_two (hι : Fintype.card ι = 2)
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    LinearMap.trace K (spinMinus Q P) (P.typeDSpinMinusLieRep b hline x) = 0 :=
  (P.trace_typeDSpinLieRep_eq_zero_of_card_eq_two b hline hι x).2

/-- **The image of `so₄` in `End S⁺ × End S⁻` is `sl(S⁺) × sl(S⁻)`.** For an even polarization
with `dim W = 2`, a pair of endomorphisms of the two half-spin modules is the pair of actions of
an element of the split type-`D` Lie algebra if and only if both have trace zero. -/
theorem mem_range_typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_iff_of_card_eq_two
    (hι : Fintype.card ι = 2) {f : Module.End K (spinPlus Q P)}
    {f' : Module.End K (spinMinus Q P)} :
    (f, f') ∈ ((P.typeDSpinPlusLieRep b hline).prod (P.typeDSpinMinusLieRep b hline)).range ↔
      LinearMap.trace K (spinPlus Q P) f = 0 ∧ LinearMap.trace K (spinMinus Q P) f' = 0 := by
  rw [LieHom.mem_range]
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun hf ↦ ?_⟩
  · rw [LieHom.prod_apply, Prod.mk.injEq] at hx
    exact hx.1 ▸ hx.2 ▸ P.trace_typeDSpinLieRep_eq_zero_of_card_eq_two b hline hι x
  have : FiniteDimensional K V := Module.finite_of_finrank_pos
    (by rw [P.finrank_eq_four_of_card_eq_two b hline hι]; omega)
  obtain ⟨z, hz⟩ := evenSpinActionProd_surjective P hline (f, f')
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at hz
  have hmem := P.mem_quadraticLieSubalgebra_of_reverseEven_eq_neg b hline hι
    ((P.reverseEven_eq_neg_iff_trace_eq_zero b hline hι z).2 (hz.1 ▸ hz.2 ▸ hf))
  set x := (P.typeDQuadraticEquiv b hline).symm ⟨z, hmem⟩
  have hx : (⟨P.typeDQuadraticEquiv b hline x,
      quadraticLieSubalgebra_le_even Q (P.typeDQuadraticEquiv b hline x).property⟩ : even Q) = z :=
    Subtype.ext (by simp [x])
  have h := P.evenSpinActionProd_typeDQuadraticEquiv b hline x
  rw [hx, evenSpinActionProd_apply, hz.1, hz.2] at h
  exact ⟨x, by rw [LieHom.prod_apply, h]⟩

/-- **The image of `so₄` in `End S⁺` is `sl(S⁺)`.** For an even polarization with `dim W = 2`, an
endomorphism of the even half-spin module is the action of an element of the split type-`D` Lie
algebra if and only if its trace vanishes. -/
theorem mem_range_typeDSpinPlusLieRep_iff_of_card_eq_two (hι : Fintype.card ι = 2)
    {f : Module.End K (spinPlus Q P)} :
    f ∈ (P.typeDSpinPlusLieRep b hline).range ↔ LinearMap.trace K (spinPlus Q P) f = 0 := by
  refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ P.trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_two b hline hι x,
    fun hf ↦ ?_⟩
  obtain ⟨x, hx⟩ :=
    (P.mem_range_typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_iff_of_card_eq_two b hline hι
      (f' := 0)).mpr ⟨hf, map_zero _⟩
  exact ⟨x, congrArg Prod.fst hx⟩

/-- **The image of `so₄` in `End S⁻` is `sl(S⁻)`.** For an even polarization with `dim W = 2`, an
endomorphism of the odd half-spin module is the action of an element of the split type-`D` Lie
algebra if and only if its trace vanishes. -/
theorem mem_range_typeDSpinMinusLieRep_iff_of_card_eq_two (hι : Fintype.card ι = 2)
    {f : Module.End K (spinMinus Q P)} :
    f ∈ (P.typeDSpinMinusLieRep b hline).range ↔ LinearMap.trace K (spinMinus Q P) f = 0 := by
  refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ P.trace_typeDSpinMinusLieRep_eq_zero_of_card_eq_two b hline hι x,
    fun hf ↦ ?_⟩
  obtain ⟨x, hx⟩ :=
    (P.mem_range_typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_iff_of_card_eq_two b hline hι
      (f := 0)).mpr ⟨map_zero _, hf⟩
  exact ⟨x, congrArg Prod.snd hx⟩

/-! ### The isomorphism `so₄ ≃ sl₂ × sl₂` -/

variable {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- The action of `so₄` on `S⁺ × S⁻`, read as pairs of matrices in bases of the two half-spin
modules. -/
private noncomputable def matrixPairLieHom (B : Basis κ K (spinPlus Q P))
    (B' : Basis κ' K (spinMinus Q P)) :
    LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ Matrix κ κ K × Matrix κ' κ' K :=
  ((LinearMap.toMatrixAlgEquiv B).toLieEquiv.toLieHom.comp (P.typeDSpinPlusLieRep b hline)).prod
    ((LinearMap.toMatrixAlgEquiv B').toLieEquiv.toLieHom.comp (P.typeDSpinMinusLieRep b hline))

private theorem matrixPairLieHom_apply (B : Basis κ K (spinPlus Q P))
    (B' : Basis κ' K (spinMinus Q P)) (x : LieAlgebra.Orthogonal.typeD ι K) :
    P.matrixPairLieHom b hline B B' x =
      (LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x),
        LinearMap.toMatrix B' B' (P.typeDSpinMinusLieRep b hline x)) :=
  rfl

/-- **`D₂ ≅ A₁ × A₁`.** For an even polarization with `dim W = 2` and bases `B` of the even
half-spin module `S⁺` and `B'` of the odd half-spin module `S⁻`, sending an element of the split
type-`D` Lie algebra `so₄` to the pair of matrices of its actions on `S⁺` and `S⁻` is a Lie algebra
isomorphism onto pairs of trace-zero matrices. Through it, `S⁺` is the standard module of the first
factor `sl₂` and `S⁻` that of the second. -/
noncomputable def typeDHalfSpinLieEquivSlProdSl (hι : Fintype.card ι = 2)
    (B : Basis κ K (spinPlus Q P)) (B' : Basis κ' K (spinMinus Q P)) :
    LieAlgebra.Orthogonal.typeD ι K ≃ₗ⁅K⁆ SpecialLinear.sl κ K × SpecialLinear.sl κ' K :=
  LieEquiv.ofBijective
    { toFun x := (⟨(P.matrixPairLieHom b hline B B' x).1, by
          rw [SpecialLinear.mem_sl_iff, matrixPairLieHom_apply, ← LinearMap.trace_eq_matrix_trace,
            P.trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_two b hline hι]⟩,
        ⟨(P.matrixPairLieHom b hline B B' x).2, by
          rw [SpecialLinear.mem_sl_iff, matrixPairLieHom_apply, ← LinearMap.trace_eq_matrix_trace,
            P.trace_typeDSpinMinusLieRep_eq_zero_of_card_eq_two b hline hι]⟩)
      map_add' x y := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
      map_smul' c x := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
      map_lie' {x y} := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp)) }
    ⟨fun x y h ↦ P.typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_injective b hline <| by
          simp only [LieHom.coe_mk, Prod.mk.injEq, Subtype.mk.injEq, matrixPairLieHom_apply,
            EmbeddingLike.apply_eq_iff_eq] at h
          rw [LieHom.prod_apply, LieHom.prod_apply, h.1, h.2],
      fun ⟨A, A'⟩ ↦ by
        have hA : LinearMap.trace K (spinPlus Q P) (Matrix.toLin B B A) = 0 := by
          rw [LinearMap.trace_eq_matrix_trace K B, LinearMap.toMatrix_toLin,
            ← SpecialLinear.mem_sl_iff]
          exact A.property
        have hA' : LinearMap.trace K (spinMinus Q P) (Matrix.toLin B' B' A') = 0 := by
          rw [LinearMap.trace_eq_matrix_trace K B', LinearMap.toMatrix_toLin,
            ← SpecialLinear.mem_sl_iff]
          exact A'.property
        obtain ⟨x, hx⟩ := (LieHom.mem_range _ _).mp
          ((P.mem_range_typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_iff_of_card_eq_two b hline
            hι).mpr ⟨hA, hA'⟩)
        rw [LieHom.prod_apply, Prod.mk.injEq] at hx
        exact ⟨x, Prod.ext (Subtype.ext (by simp [matrixPairLieHom_apply, hx.1]))
          (Subtype.ext (by simp [matrixPairLieHom_apply, hx.2]))⟩⟩

/-- The first component of the isomorphism `so₄ ≃ sl₂ × sl₂` is the matrix of the action on
`S⁺`. -/
@[simp]
theorem coe_typeDHalfSpinLieEquivSlProdSl_apply_fst (hι : Fintype.card ι = 2)
    (B : Basis κ K (spinPlus Q P)) (B' : Basis κ' K (spinMinus Q P))
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    ((P.typeDHalfSpinLieEquivSlProdSl b hline hι B B' x).1 : Matrix κ κ K) =
      LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x) :=
  -- `(rfl)`, not `rfl`: the body of `typeDHalfSpinLieEquivSlProdSl` is not `@[expose]`d.
  (rfl)

/-- The second component of the isomorphism `so₄ ≃ sl₂ × sl₂` is the matrix of the action on
`S⁻`. -/
@[simp]
theorem coe_typeDHalfSpinLieEquivSlProdSl_apply_snd (hι : Fintype.card ι = 2)
    (B : Basis κ K (spinPlus Q P)) (B' : Basis κ' K (spinMinus Q P))
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    ((P.typeDHalfSpinLieEquivSlProdSl b hline hι B B' x).2 : Matrix κ' κ' K) =
      LinearMap.toMatrix B' B' (P.typeDSpinMinusLieRep b hline x) :=
  -- `(rfl)`, not `rfl`: the body of `typeDHalfSpinLieEquivSlProdSl` is not `@[expose]`d.
  (rfl)


/-- Through the isomorphism `so₄ ≃ sl₂ × sl₂`, a pair of trace-zero matrices acts on `S⁺` by the
endomorphism with the first matrix in the basis `B`. -/
@[simp]
theorem typeDSpinPlusLieRep_typeDHalfSpinLieEquivSlProdSl_symm_apply (hι : Fintype.card ι = 2)
    (B : Basis κ K (spinPlus Q P)) (B' : Basis κ' K (spinMinus Q P))
    (p : SpecialLinear.sl κ K × SpecialLinear.sl κ' K) :
    P.typeDSpinPlusLieRep b hline ((P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').symm p) =
      Matrix.toLin B B (p.1 : Matrix κ κ K) := by
  rw [← LinearMap.toMatrix_symm, LinearEquiv.eq_symm_apply,
    ← P.coe_typeDHalfSpinLieEquivSlProdSl_apply_fst b hline hι B B', LieEquiv.apply_symm_apply]

/-- Through the isomorphism `so₄ ≃ sl₂ × sl₂`, a pair of trace-zero matrices acts on `S⁻` by the
endomorphism with the second matrix in the basis `B'`. -/
@[simp]
theorem typeDSpinMinusLieRep_typeDHalfSpinLieEquivSlProdSl_symm_apply (hι : Fintype.card ι = 2)
    (B : Basis κ K (spinPlus Q P)) (B' : Basis κ' K (spinMinus Q P))
    (p : SpecialLinear.sl κ K × SpecialLinear.sl κ' K) :
    P.typeDSpinMinusLieRep b hline ((P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').symm p) =
      Matrix.toLin B' B' (p.2 : Matrix κ' κ' K) := by
  rw [← LinearMap.toMatrix_symm, LinearEquiv.eq_symm_apply,
    ← P.coe_typeDHalfSpinLieEquivSlProdSl_apply_snd b hline hι B B', LieEquiv.apply_symm_apply]

/-- **`typeDHalfSpinLieEquivSlProdSl` restricts the matrix model of the even Clifford algebra.**
The pair of matrices of an element of `so₄` is the image of its quadratic Clifford realization
under the even structure isomorphism `even Q ≃ End S⁺ × End S⁻` followed by taking matrices in
`B` and `B'`. This is the model from which
`exists_spinGroup_mulEquiv_specialLinearGroup_prod_and_halfSpin_equiv_stdSLRep_of_finrank_eq_four`
builds `Spin₄ ≅ SL₂ × SL₂`. -/
theorem typeDHalfSpinLieEquivSlProdSl_apply_eq_evenCliffordEquivProdEnd [FiniteDimensional K V]
    (hι : Fintype.card ι = 2) (B : Basis κ K (spinPlus Q P)) (B' : Basis κ' K (spinMinus Q P))
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    (((P.typeDHalfSpinLieEquivSlProdSl b hline hι B B' x).1 : Matrix κ κ K),
        ((P.typeDHalfSpinLieEquivSlProdSl b hline hι B B' x).2 : Matrix κ' κ' K)) =
      ((P.evenCliffordEquivProdEnd hline).trans
        ((LinearMap.toMatrixAlgEquiv B).prodCongr (LinearMap.toMatrixAlgEquiv B')))
        ⟨P.typeDQuadraticEquiv b hline x,
          quadraticLieSubalgebra_le_even Q (P.typeDQuadraticEquiv b hline x).property⟩ := by
  rw [AlgEquiv.trans_apply, evenCliffordEquivProdEnd_apply,
    evenSpinActionProd_typeDQuadraticEquiv, coe_typeDHalfSpinLieEquivSlProdSl_apply_fst,
    coe_typeDHalfSpinLieEquivSlProdSl_apply_snd]
  rfl

/-! ### The half-spin modules as standard modules -/

/-- **`S⁺` is the standard module of the first factor `sl₂`.** Make `S⁺` a module over `so₄`
through its half-spin action, and `κ → K` through the first component of
`typeDHalfSpinLieEquivSlProdSl` followed by the matrix action. Then taking coordinates in `B` is
an equivalence of Lie modules. -/
noncomputable def typeDSpinPlusLieModuleEquivStd (hι : Fintype.card ι = 2)
    (B : Basis κ K (spinPlus Q P)) (B' : Basis κ' K (spinMinus Q P)) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
      LieRingModule.compLieHom _ ((SpecialLinear.sl κ K).incl.comp
        ((LieHom.fst K _ _).comp (P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').toLieHom))
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
      LieModule.compLieHom _ ((SpecialLinear.sl κ K).incl.comp
        ((LieHom.fst K _ _).comp (P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').toLieHom))
    spinPlus Q P ≃ₗ⁅K, LieAlgebra.Orthogonal.typeD ι K⁆ (κ → K) :=
  letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
    LieRingModule.compLieHom _ ((SpecialLinear.sl κ K).incl.comp
      ((LieHom.fst K _ _).comp (P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').toLieHom))
  { B.equivFun with
    map_lie' := fun {x s} ↦ by
      simp only [LieRingModule.compLieHom_apply, LieHom.coe_comp, Function.comp_apply,
        LieEquiv.coe_toLieHom, LieHom.coe_fst, LieSubalgebra.coe_incl, Matrix.lie_apply,
        Module.End.lie_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        coe_typeDHalfSpinLieEquivSlProdSl_apply_fst, Basis.equivFun_apply,
        LinearMap.toMatrix_mulVec_repr] }

/-- The Lie module equivalence `typeDSpinPlusLieModuleEquivStd` takes coordinates in `B`. -/
@[simp]
theorem typeDSpinPlusLieModuleEquivStd_apply (hι : Fintype.card ι = 2)
    (B : Basis κ K (spinPlus Q P)) (B' : Basis κ' K (spinMinus Q P)) (s : spinPlus Q P) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
      LieRingModule.compLieHom _ ((SpecialLinear.sl κ K).incl.comp
        ((LieHom.fst K _ _).comp (P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').toLieHom))
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
      LieModule.compLieHom _ ((SpecialLinear.sl κ K).incl.comp
        ((LieHom.fst K _ _).comp (P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').toLieHom))
    P.typeDSpinPlusLieModuleEquivStd b hline hι B B' s = B.equivFun s :=
  (rfl)

/-- **`S⁻` is the standard module of the second factor `sl₂`.** Make `S⁻` a module over `so₄`
through its half-spin action, and `κ' → K` through the second component of
`typeDHalfSpinLieEquivSlProdSl` followed by the matrix action. Then taking coordinates in `B'` is
an equivalence of Lie modules. -/
noncomputable def typeDSpinMinusLieModuleEquivStd (hι : Fintype.card ι = 2)
    (B : Basis κ K (spinPlus Q P)) (B' : Basis κ' K (spinMinus Q P)) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (κ' → K) :=
      LieRingModule.compLieHom _ ((SpecialLinear.sl κ' K).incl.comp
        ((LieHom.snd K _ _).comp (P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').toLieHom))
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (κ' → K) :=
      LieModule.compLieHom _ ((SpecialLinear.sl κ' K).incl.comp
        ((LieHom.snd K _ _).comp (P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').toLieHom))
    spinMinus Q P ≃ₗ⁅K, LieAlgebra.Orthogonal.typeD ι K⁆ (κ' → K) :=
  letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (κ' → K) :=
    LieRingModule.compLieHom _ ((SpecialLinear.sl κ' K).incl.comp
      ((LieHom.snd K _ _).comp (P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').toLieHom))
  { B'.equivFun with
    map_lie' := fun {x s} ↦ by
      simp only [LieRingModule.compLieHom_apply, LieHom.coe_comp, Function.comp_apply,
        LieEquiv.coe_toLieHom, LieHom.coe_snd, LieSubalgebra.coe_incl, Matrix.lie_apply,
        Module.End.lie_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        coe_typeDHalfSpinLieEquivSlProdSl_apply_snd, Basis.equivFun_apply,
        LinearMap.toMatrix_mulVec_repr] }

/-- The Lie module equivalence `typeDSpinMinusLieModuleEquivStd` takes coordinates in `B'`. -/
@[simp]
theorem typeDSpinMinusLieModuleEquivStd_apply (hι : Fintype.card ι = 2)
    (B : Basis κ K (spinPlus Q P)) (B' : Basis κ' K (spinMinus Q P)) (s : spinMinus Q P) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (κ' → K) :=
      LieRingModule.compLieHom _ ((SpecialLinear.sl κ' K).incl.comp
        ((LieHom.snd K _ _).comp (P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').toLieHom))
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (κ' → K) :=
      LieModule.compLieHom _ ((SpecialLinear.sl κ' K).incl.comp
        ((LieHom.snd K _ _).comp (P.typeDHalfSpinLieEquivSlProdSl b hline hι B B').toLieHom))
    P.typeDSpinMinusLieModuleEquivStd b hline hι B B' s = B'.equivFun s :=
  (rfl)

end TauCeti.SpinPolarizationData
