/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.SpecialLinear
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Representation
import TauCeti.Algebra.Lie.Matrix.Basis
import TauCeti.Algebra.Lie.SpecialLinear.Root.Generation
import TauCeti.LinearAlgebra.CliffordAlgebra.CliffordExteriorSquare
import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Characterization
import TauCeti.LinearAlgebra.Dimension.Basis
import TauCeti.RepresentationTheory.Spin.Exceptional.Six.HalfSpinDual

/-!
# The half-spin Lie modules of `so₆`: the isomorphism `D₃ ≅ A₃`

Let `P` be an even polarization `V = W ⊕ W'` with `dim W = 3`, over a field in which `2` is
invertible, and let `b` be a basis of `W`. The split type-`D` matrix Lie algebra `so₆` acts on
the two half-spin modules `S⁺ = ⋀ᵉᵛᵉⁿ W` and `S⁻ = ⋀ᵒᵈᵈ W`, both of dimension four, through its
quadratic Clifford realization (`TauCeti.SpinPolarizationData.typeDSpinPlusLieRep` and
`TauCeti.SpinPolarizationData.typeDSpinMinusLieRep`). This file proves that these are the
standard module of `sl₄` and its dual:

* the action on `S⁺` is faithful and its image is exactly the trace-zero endomorphisms, so in a
  basis of `S⁺` it is a Lie algebra isomorphism `so₆ ≃ sl₄`, under which `S⁺` is the standard
  module;
* `S⁻` is equivalent, as a Lie module over `so₆`, to the dual of `S⁺`; in matrices, each element
  of `so₆` acts on `S⁻` by minus the transpose of its matrix on `S⁺`. Consequently `so₆` also acts
  faithfully on `S⁻`, with image the trace-zero endomorphisms.

These are the Lie-algebra counterparts of the group isomorphism
`TauCeti.spinGroupEquivSpecialLinearGroupOfFinrankEqSix` and of the duality
`TauCeti.exists_spinMinusSubrep_equiv_dual_spinPlusSubrep_of_finrank_eq_six`. In the even monomial
basis of `S⁺` used there, the Lie element underlying the canonical Spin lift of an elementary
transvection `1 + c E_{ij}` acts by `c E_{ij}`
(`TauCeti.SpinPolarizationData.toMatrix_typeDSpinPlusLieRep_eq_single`).

## The argument

The canonical Spin lift `1 + ι w * ι u` of an elementary transvection acts on `S⁺` by the
elementary transvection `1 + c E_{ij}` in the even monomial basis
(`TauCeti.toMatrix_spinPlusAction_spinSixTransvectionLift`). Since `u` and `w` are orthogonal,
`ι w * ι u` is a quadratic Clifford element, so every off-diagonal matrix unit `E_{ij}` is the
action of an element of `so₆`. The adjacent matrix units generate `sl₄` as a Lie algebra
(`TauCeti.lieSpan_specialLinear_adjacent_single_eq_top`), so the image contains `sl₄`. Both `so₆`
and `sl₄` have dimension fifteen, which forces the image to be `sl₄` and the action to be
injective: `so₆` is identified with the quadratic Clifford elements by
`TauCeti.SpinPolarizationData.typeDQuadraticEquiv`, which have dimension `6 choose 2`
(`CliffordAlgebra.finrank_quadraticLieSubalgebra`), while `TauCeti.finrank_sl` counts `sl₄`.

The duality comes from reversal, which negates quadratic Clifford elements
(`CliffordAlgebra.reverse_eq_neg_of_mem_quadraticLieSubalgebra`) and exchanges the two simple
factors of the even Clifford algebra
(`TauCeti.exists_linearEquiv_intertwines_dual_spinPlusAction_spinMinusAction_reverseEven`).

## Main definitions and results

All declarations are in the namespace `TauCeti.SpinPolarizationData`.

* `toMatrix_typeDSpinPlusLieRep_eq_single`: the element of `so₆` realized by the bivector part of
  the canonical Spin lift of `1 + c E_{ij}` acts on `S⁺` by `c E_{ij}`.
* `typeDSpinPlusLieRep_injective_of_card_eq_three` and
  `mem_range_typeDSpinPlusLieRep_iff_of_card_eq_three`: `so₆` acts faithfully on `S⁺`, with image
  the trace-zero endomorphisms.
* `typeDSpinPlusLieEquivSl`: the resulting Lie algebra isomorphism `so₆ ≃ sl₄`, given by the matrix
  of the action on `S⁺` in a chosen basis.
* `typeDSpinPlusLieModuleEquivStd`: through this isomorphism, `S⁺` is the standard module of `sl₄`.
* `nonempty_lieModuleEquiv_dual_typeDSpinPlus_typeDSpinMinus_of_card_eq_three`: `S⁻` is the dual of
  `S⁺` as a Lie module over `so₆`.
* `exists_basis_toMatrix_typeDSpinMinusLieRep_eq_neg_transpose`: the same duality in matrix form.
* `typeDSpinMinusLieRep_injective_of_card_eq_three` and
  `mem_range_typeDSpinMinusLieRep_iff_of_card_eq_three`: `so₆` acts faithfully on `S⁻`, with image
  the trace-zero endomorphisms.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open CliffordAlgebra Module LieAlgebra
open scoped Matrix

namespace TauCeti.SpinPolarizationData

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] [Invertible (2 : K)] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [DecidableEq ι] (b : Basis ι K P.W) (hline : P.line = ⊥)

/-! ### Matrix units from transvection lifts -/

/-- **Matrix units from transvection lifts.** Number a basis of `W` by `e : ι ≃ Fin 3`. The
canonical Spin lift of the elementary transvection `1 + c E_{ij}` of `S⁺` is the Clifford element
`1 + ι w * ι u` (`TauCeti.coe_spinSixTransvectionLift`). An element of the split type-`D` Lie
algebra whose quadratic Clifford realization is the bivector part `ι w * ι u` acts on `S⁺` by the
matrix unit `c E_{ij}` in the even monomial basis. -/
theorem toMatrix_typeDSpinPlusLieRep_eq_single (e : ι ≃ Fin 3) {i j : Fin 4} (hij : i ≠ j)
    (c : K) {x : LieAlgebra.Orthogonal.typeD ι K}
    (hx : (P.typeDQuadraticEquiv b hline x : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q (spinSixTransvectionSecondVector P (b.reindex e) i j c) *
        CliffordAlgebra.ι Q (spinSixTransvectionFirstVector P (b.reindex e) i j)) :
    LinearMap.toMatrix ((b.reindex e).spinSixEvenMonomialBasis (spinPlus_def P))
        ((b.reindex e).spinSixEvenMonomialBasis (spinPlus_def P))
        (P.typeDSpinPlusLieRep b hline x) =
      Matrix.single i j c := by
  have heven : (⟨P.typeDQuadraticEquiv b hline x,
      quadraticLieSubalgebra_le_even Q (P.typeDQuadraticEquiv b hline x).property⟩ : even Q) =
      spinGroupToEven Q (spinSixTransvectionLift P hline (b.reindex e) hij c) - 1 :=
    Subtype.ext (by simp [hx])
  have h := P.evenSpinActionProd_typeDQuadraticEquiv b hline x
  rw [heven, evenSpinActionProd_apply, Prod.mk.injEq] at h
  rw [← h.1, map_sub, map_one, map_sub,
    toMatrix_spinPlusAction_spinSixTransvectionLift, LinearMap.toMatrix_one, Matrix.transvection,
    add_sub_cancel_left]

/-- The bivector part of the canonical Spin lift of an elementary transvection is the quadratic
Clifford realization of an element of the split type-`D` Lie algebra. -/
private theorem exists_typeDQuadraticEquiv_eq_ι_mul_ι (e : ι ≃ Fin 3) {i j : Fin 4}
    (hij : i ≠ j) (c : K) :
    ∃ x : LieAlgebra.Orthogonal.typeD ι K,
      (P.typeDQuadraticEquiv b hline x : CliffordAlgebra Q) =
        CliffordAlgebra.ι Q (spinSixTransvectionSecondVector P (b.reindex e) i j c) *
          CliffordAlgebra.ι Q (spinSixTransvectionFirstVector P (b.reindex e) i j) := by
  have hortho : Q.IsOrtho (spinSixTransvectionSecondVector P (b.reindex e) i j c)
      (spinSixTransvectionFirstVector P (b.reindex e) i j) := by
    rw [← QuadraticMap.isOrtho_polarBilin, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_comm]
    exact polar_spinSixTransvectionVectors_eq_zero P (b.reindex e) hij c
  have hmem : CliffordAlgebra.ι Q (spinSixTransvectionSecondVector P (b.reindex e) i j c) *
      CliffordAlgebra.ι Q (spinSixTransvectionFirstVector P (b.reindex e) i j) ∈
        quadraticLieSubalgebra Q := by
    rw [← bivector_eq_ι_mul_ι_of_isOrtho Q hortho]
    exact bivector_mem_quadraticLieSubalgebra Q _ _
  exact ⟨(P.typeDQuadraticEquiv b hline).symm ⟨_, hmem⟩, by simp⟩

/-! ### The image of `so₆` in `End S⁺` -/

/-- The even monomial basis `1, e₀e₁, e₀e₂, e₁e₂` of `S⁺`, for the basis `b` of `W` renumbered by
`Fin 3`. -/
private noncomputable abbrev monomialBasis (hι : Fintype.card ι = 3) :
    Basis (Fin 4) K (spinPlus Q P) :=
  (b.reindex (Fintype.equivFinOfCardEq hι)).spinSixEvenMonomialBasis (spinPlus_def P)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The action of `so₆` on `S⁺`, read as matrices in a basis of `S⁺`. -/
private noncomputable def matrixLieHom (B : Basis κ K (spinPlus Q P)) :
    LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ Matrix κ κ K :=
  (LinearMap.toMatrixAlgEquiv B).toLieEquiv.toLieHom.comp (P.typeDSpinPlusLieRep b hline)

private theorem matrixLieHom_apply (B : Basis κ K (spinPlus Q P))
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    P.matrixLieHom b hline B x = LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x) :=
  rfl

/-- An off-diagonal matrix unit of `sl₄` lies in the image of `so₆`, in the even monomial
basis. -/
private theorem single_mem_comap_range_matrixLieHom (hι : Fintype.card ι = 3) {i j : Fin 4}
    (hij : i ≠ j) :
    SpecialLinear.single i j hij (1 : K) ∈
      (P.matrixLieHom b hline (P.monomialBasis b hι)).range.comap
        (SpecialLinear.sl (Fin 4) K).incl := by
  obtain ⟨x, hx⟩ := P.exists_typeDQuadraticEquiv_eq_ι_mul_ι b hline
    (Fintype.equivFinOfCardEq hι) hij 1
  rw [LieSubalgebra.mem_comap, LieHom.mem_range, LieSubalgebra.coe_incl, SpecialLinear.val_single]
  exact ⟨x, P.toMatrix_typeDSpinPlusLieRep_eq_single b hline _ hij 1 hx⟩

/-- Every trace-zero matrix is the matrix, in the even monomial basis, of the action of an element
of `so₆` on `S⁺`: the image contains the adjacent matrix units, which generate `sl₄`. -/
private theorem sl_le_range_matrixLieHom (hι : Fintype.card ι = 3) :
    SpecialLinear.sl (Fin 4) K ≤ (P.matrixLieHom b hline (P.monomialBasis b hι)).range := by
  rw [← LieSubalgebra.comap_incl_eq_top, eq_top_iff,
    ← lieSpan_specialLinear_adjacent_single_eq_top 3 K, LieSubalgebra.lieSpan_le]
  rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> exact P.single_mem_comap_range_matrixLieHom b hline hι _

include b hline in
/-- The split type-`D` Lie algebra of rank three has dimension `15 = (6 choose 2)`: it is
identified with the quadratic Clifford elements of the six-dimensional space `V`. -/
private theorem finrank_typeD_of_card_eq_three (hι : Fintype.card ι = 3) :
    finrank K (LieAlgebra.Orthogonal.typeD ι K) = 15 := by
  have : Module.Free K V := Module.Free.of_basis (P.typeDBasis b hline)
  have : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  rw [(P.typeDQuadraticEquiv b hline).toLinearEquiv.finrank_eq, finrank_quadraticLieSubalgebra,
    finrank_eq_two_mul_card_of_basis_sum (P.typeDBasis b hline), hι]
  rfl

/-- The matrices in the even monomial basis of the action of `so₆` on `S⁺` are exactly the
trace-zero matrices, and the action is injective: the image contains `sl₄`, and `so₆` and `sl₄`
both have dimension fifteen. -/
private theorem range_matrixLieHom_eq_and_injective (hι : Fintype.card ι = 3) :
    (P.matrixLieHom b hline (P.monomialBasis b hι)).range = SpecialLinear.sl (Fin 4) K ∧
      Function.Injective (P.matrixLieHom b hline (P.monomialBasis b hι)) := by
  set f := P.matrixLieHom b hline (P.monomialBasis b hι)
  have hsl : finrank K (SpecialLinear.sl (Fin 4) K) = 15 := by
    rw [finrank_sl]
    rfl
  have hdim := P.finrank_typeD_of_card_eq_three b hline hι
  have hrange : f.range = SpecialLinear.sl (Fin 4) K := by
    refine (LieSubalgebra.toSubmodule_injective <|
      Submodule.eq_of_le_of_finrank_le (P.sl_le_range_matrixLieHom b hline hι) ?_).symm
    rw [LieHom.range_toSubmodule]
    exact (LinearMap.finrank_range_le f.toLinearMap).trans (hdim.trans hsl.symm).le
  refine ⟨hrange, fun x y h ↦ ?_⟩
  have hfin : finrank K (LieAlgebra.Orthogonal.typeD ι K) = finrank K f.range := by
    rw [hdim, hrange, hsl]
  have hrr : Function.Injective f.rangeRestrict :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr
      f.surjective_rangeRestrict
  exact hrr (Subtype.ext (by simpa only [LieHom.rangeRestrict_apply] using h))

/-- **`so₆` acts faithfully on the even half-spin module.** For an even polarization with
`dim W = 3`, the action of the split type-`D` Lie algebra on `S⁺` is injective. -/
theorem typeDSpinPlusLieRep_injective_of_card_eq_three (hι : Fintype.card ι = 3) :
    Function.Injective (P.typeDSpinPlusLieRep b hline) := fun x y h ↦
  (P.range_matrixLieHom_eq_and_injective b hline hι).2 <| by
    rw [matrixLieHom_apply, matrixLieHom_apply, h]

/-- Every element of `so₆` acts on the even half-spin module by an endomorphism of trace zero. -/
@[simp]
theorem trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_three (hι : Fintype.card ι = 3)
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    LinearMap.trace K (spinPlus Q P) (P.typeDSpinPlusLieRep b hline x) = 0 := by
  have hx : P.matrixLieHom b hline (P.monomialBasis b hι) x ∈ SpecialLinear.sl (Fin 4) K := by
    rw [← (P.range_matrixLieHom_eq_and_injective b hline hι).1]
    exact LieHom.mem_range_self _ x
  rw [SpecialLinear.mem_sl_iff, matrixLieHom_apply] at hx
  rw [LinearMap.trace_eq_matrix_trace K (P.monomialBasis b hι), hx]

/-- **The image of `so₆` in `End S⁺` is `sl(S⁺)`.** For an even polarization with `dim W = 3`,
an endomorphism of the even half-spin module is the action of an element of the split type-`D`
Lie algebra if and only if its trace vanishes. -/
theorem mem_range_typeDSpinPlusLieRep_iff_of_card_eq_three (hι : Fintype.card ι = 3)
    {f : Module.End K (spinPlus Q P)} :
    f ∈ (P.typeDSpinPlusLieRep b hline).range ↔ LinearMap.trace K (spinPlus Q P) f = 0 := by
  rw [LieHom.mem_range]
  refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ P.trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_three b hline hι x,
    fun hf ↦ ?_⟩
  have hA : LinearMap.toMatrix (P.monomialBasis b hι) (P.monomialBasis b hι) f ∈
      SpecialLinear.sl (Fin 4) K := by
    rw [SpecialLinear.mem_sl_iff, ← LinearMap.trace_eq_matrix_trace, hf]
  obtain ⟨x, hx⟩ := (LieHom.mem_range _ _).mp (P.sl_le_range_matrixLieHom b hline hι hA)
  rw [matrixLieHom_apply] at hx
  exact ⟨x, (LinearMap.toMatrix _ _).injective hx⟩

/-! ### The isomorphism `so₆ ≃ sl₄` -/

/-- **`D₃ ≅ A₃`.** For an even polarization with `dim W = 3` and a basis `B` of the even
half-spin module `S⁺`, sending an element of the split type-`D` Lie algebra `so₆` to the matrix
of its action on `S⁺` in the basis `B` is a Lie algebra isomorphism onto the trace-zero matrices.
Through it, `S⁺` is the standard module of `sl₄` (`typeDSpinPlusLieModuleEquivStd`). -/
noncomputable def typeDSpinPlusLieEquivSl (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) :
    LieAlgebra.Orthogonal.typeD ι K ≃ₗ⁅K⁆ SpecialLinear.sl κ K :=
  LieEquiv.ofBijective
    { toFun x := ⟨P.matrixLieHom b hline B x, by
          rw [SpecialLinear.mem_sl_iff, matrixLieHom_apply, ← LinearMap.trace_eq_matrix_trace,
            P.trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_three b hline hι]⟩
      map_add' x y := Subtype.ext (by simp)
      map_smul' c x := Subtype.ext (by simp)
      map_lie' {x y} := Subtype.ext (by simp) }
    ⟨fun x y h ↦ P.typeDSpinPlusLieRep_injective_of_card_eq_three b hline hι <|
        (LinearMap.toMatrix B B).injective <| by
          simpa only [LieHom.coe_mk, Subtype.mk.injEq, matrixLieHom_apply] using h,
      fun A ↦ by
        have hA : LinearMap.trace K (spinPlus Q P) (Matrix.toLin B B A) = 0 := by
          rw [LinearMap.trace_eq_matrix_trace K B, LinearMap.toMatrix_toLin,
            ← SpecialLinear.mem_sl_iff]
          exact A.property
        obtain ⟨x, hx⟩ := (LieHom.mem_range _ _).mp
          ((P.mem_range_typeDSpinPlusLieRep_iff_of_card_eq_three b hline hι).mpr hA)
        exact ⟨x, Subtype.ext (by simp [matrixLieHom_apply, hx])⟩⟩

/-- The isomorphism `so₆ ≃ sl₄` sends an element of `so₆` to the matrix of its action on `S⁺`. -/
@[simp]
theorem coe_typeDSpinPlusLieEquivSl_apply (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) (x : LieAlgebra.Orthogonal.typeD ι K) :
    (P.typeDSpinPlusLieEquivSl b hline hι B x : Matrix κ κ K) =
      LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x) :=
  -- `(rfl)`, not `rfl`: the body of `typeDSpinPlusLieEquivSl` is not `@[expose]`d.
  (rfl)

/-- Through the isomorphism `so₆ ≃ sl₄`, a trace-zero matrix acts on `S⁺` by the endomorphism with
that matrix in the basis `B`. -/
@[simp]
theorem typeDSpinPlusLieRep_typeDSpinPlusLieEquivSl_symm_apply (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) (A : SpecialLinear.sl κ K) :
    P.typeDSpinPlusLieRep b hline ((P.typeDSpinPlusLieEquivSl b hline hι B).symm A) =
      Matrix.toLin B B (A : Matrix κ κ K) := by
  rw [← LinearMap.toMatrix_symm, LinearEquiv.eq_symm_apply,
    ← P.coe_typeDSpinPlusLieEquivSl_apply b hline hι B, LieEquiv.apply_symm_apply]

/-- **`S⁺` is the standard module of `sl₄`.** Make `S⁺` a module over `so₆` through its half-spin
action, and `κ → K` through `typeDSpinPlusLieEquivSl` followed by the matrix action. Then taking
coordinates in `B` is an equivalence of Lie modules. -/
noncomputable def typeDSpinPlusLieModuleEquivStd (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
      LieRingModule.compLieHom _
        ((SpecialLinear.sl κ K).incl.comp (P.typeDSpinPlusLieEquivSl b hline hι B).toLieHom)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
      LieModule.compLieHom _
        ((SpecialLinear.sl κ K).incl.comp (P.typeDSpinPlusLieEquivSl b hline hι B).toLieHom)
    spinPlus Q P ≃ₗ⁅K, LieAlgebra.Orthogonal.typeD ι K⁆ (κ → K) :=
  lieModuleEquivOfToMatrix (P.typeDSpinPlusLieRep b hline)
    ((SpecialLinear.sl κ K).incl.comp (P.typeDSpinPlusLieEquivSl b hline hι B).toLieHom) B
    (P.coe_typeDSpinPlusLieEquivSl_apply b hline hι B)

/-- The Lie module equivalence `typeDSpinPlusLieModuleEquivStd` takes coordinates in `B`. -/
@[simp]
theorem typeDSpinPlusLieModuleEquivStd_apply (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) (s : spinPlus Q P) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
      LieRingModule.compLieHom _
        ((SpecialLinear.sl κ K).incl.comp (P.typeDSpinPlusLieEquivSl b hline hι B).toLieHom)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
      LieModule.compLieHom _
        ((SpecialLinear.sl κ K).incl.comp (P.typeDSpinPlusLieEquivSl b hline hι B).toLieHom)
    P.typeDSpinPlusLieModuleEquivStd b hline hι B s = B.equivFun s :=
  lieModuleEquivOfToMatrix_apply ..

/-- The inverse of the Lie module equivalence `typeDSpinPlusLieModuleEquivStd` reconstructs a
spinor from its coordinates in `B`. -/
@[simp]
theorem typeDSpinPlusLieModuleEquivStd_symm_apply (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) (v : κ → K) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
      LieRingModule.compLieHom _
        ((SpecialLinear.sl κ K).incl.comp (P.typeDSpinPlusLieEquivSl b hline hι B).toLieHom)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (κ → K) :=
      LieModule.compLieHom _
        ((SpecialLinear.sl κ K).incl.comp (P.typeDSpinPlusLieEquivSl b hline hι B).toLieHom)
    (P.typeDSpinPlusLieModuleEquivStd b hline hι B).symm v = B.equivFun.symm v :=
  lieModuleEquivOfToMatrix_symm_apply ..

/-! ### `S⁻` is the dual of `S⁺` -/

/-- Reversal of the even Clifford algebra exchanges the two half-spin modules after duality, and
negates quadratic Clifford elements: so a single linear equivalence from the dual of `S⁺` to `S⁻`
intertwines the contragredient action `φ ↦ -φ ∘ ρ⁺(x)` with `ρ⁻(x)`. -/
private theorem exists_linearEquiv_dualMap_neg_typeDSpinPlusLieRep (hι : Fintype.card ι = 3) :
    ∃ T : Module.Dual K (spinPlus Q P) ≃ₗ[K] spinMinus Q P,
      ∀ (x : LieAlgebra.Orthogonal.typeD ι K) (φ : Module.Dual K (spinPlus Q P)),
        T ((-P.typeDSpinPlusLieRep b hline x).dualMap φ) =
          P.typeDSpinMinusLieRep b hline x (T φ) := by
  have : NeZero (2 : K) := ⟨Invertible.ne_zero 2⟩
  obtain ⟨T, hT⟩ :=
    exists_linearEquiv_intertwines_dual_spinPlusAction_spinMinusAction_reverseEven P hline
      (by rw [finrank_eq_two_mul_card_of_basis_sum (P.typeDBasis b hline), hι])
  refine ⟨T, fun x φ ↦ ?_⟩
  set z : even Q := ⟨P.typeDQuadraticEquiv b hline x,
    quadraticLieSubalgebra_le_even Q (P.typeDQuadraticEquiv b hline x).property⟩
  have hz : reverseEven Q z = -z := Subtype.ext <| by
    rw [coe_reverseEven_apply, NegMemClass.coe_neg,
      reverse_eq_neg_of_mem_quadraticLieSubalgebra Q (P.typeDQuadraticEquiv b hline x).property]
  have hprod := P.evenSpinActionProd_typeDQuadraticEquiv b hline x
  rw [evenSpinActionProd_apply, Prod.mk.injEq] at hprod
  have h := hT (-z) φ
  rwa [map_neg (reverseEven Q), hz, neg_neg, hprod.2, map_neg, hprod.1] at h

/-- **The odd half-spin module of `so₆` is the dual of the even one.** For an even polarization
with `dim W = 3`, make `S⁺` and `S⁻` Lie modules over the split type-`D` Lie algebra through their
half-spin actions. Then `S⁻` is equivalent to the dual of `S⁺`, which carries the contragredient
action `⁅x, φ⁆ = -φ ∘ ρ⁺(x)`. Combined with `typeDSpinPlusLieModuleEquivStd`, `S⁻` is the dual of
the standard module of `sl₄`. -/
theorem nonempty_lieModuleEquiv_dual_typeDSpinPlus_typeDSpinMinus_of_card_eq_three
    (hι : Fintype.card ι = 3) :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
    letI : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
      LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    letI : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
      LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
    Nonempty (Module.Dual K (spinPlus Q P) ≃ₗ⁅K, LieAlgebra.Orthogonal.typeD ι K⁆
      spinMinus Q P) := by
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinPlus Q P) :=
    LieModule.compLieHom _ (P.typeDSpinPlusLieRep b hline)
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
    LieRingModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeD ι K) (spinMinus Q P) :=
    LieModule.compLieHom _ (P.typeDSpinMinusLieRep b hline)
  obtain ⟨T, hT⟩ := P.exists_linearEquiv_dualMap_neg_typeDSpinPlusLieRep b hline hι
  refine ⟨{ T with map_lie' := fun {x φ} ↦ ?_ }⟩
  have hφ : ⁅x, φ⁆ = (-P.typeDSpinPlusLieRep b hline x).dualMap φ := by
    ext s
    simp [LieRingModule.compLieHom_apply]
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe, hφ, hT,
    LieRingModule.compLieHom_apply, Module.End.lie_apply]

/-- **The odd half-spin module of `so₆` is the dual of the even one, in matrix form.** For an even
polarization with `dim W = 3` and any basis `B` of `S⁺`, there is a basis `B'` of `S⁻` in which
every element of the split type-`D` Lie algebra acts on `S⁻` by minus the transpose of its matrix
on `S⁺`. -/
theorem exists_basis_toMatrix_typeDSpinMinusLieRep_eq_neg_transpose (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) :
    ∃ B' : Basis κ K (spinMinus Q P), ∀ x : LieAlgebra.Orthogonal.typeD ι K,
      LinearMap.toMatrix B' B' (P.typeDSpinMinusLieRep b hline x) =
        -(LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x))ᵀ := by
  obtain ⟨T, hT⟩ := P.exists_linearEquiv_dualMap_neg_typeDSpinPlusLieRep b hline hι
  refine ⟨B.dualBasis.map T, fun x ↦ ?_⟩
  have hconj : T.symm.toLinearMap ∘ₗ P.typeDSpinMinusLieRep b hline x ∘ₗ T.toLinearMap =
      Module.Dual.transpose (R := K) (-P.typeDSpinPlusLieRep b hline x) :=
    LinearMap.ext fun φ ↦ T.symm_apply_eq.mpr (hT x φ).symm
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right, hconj,
    LinearMap.toMatrix_transpose, ← Matrix.transpose_neg]
  -- `rw [map_neg]` fails to match `LinearMap.toMatrix B B (-ρ⁺(x))`, so the negation is moved
  -- through the linear equivalence explicitly.
  exact congrArg Matrix.transpose (map_neg (LinearMap.toMatrix B B) _)

/-- Every element of `so₆` acts on the odd half-spin module by an endomorphism of trace zero. -/
@[simp]
theorem trace_typeDSpinMinusLieRep_eq_zero_of_card_eq_three (hι : Fintype.card ι = 3)
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    LinearMap.trace K (spinMinus Q P) (P.typeDSpinMinusLieRep b hline x) = 0 := by
  obtain ⟨B', hB'⟩ := P.exists_basis_toMatrix_typeDSpinMinusLieRep_eq_neg_transpose b hline hι
    (P.monomialBasis b hι)
  rw [LinearMap.trace_eq_matrix_trace K B', hB', Matrix.trace_neg, Matrix.trace_transpose,
    ← LinearMap.trace_eq_matrix_trace,
    P.trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_three b hline hι, neg_zero]

/-- **`so₆` acts faithfully on the odd half-spin module.** For an even polarization with
`dim W = 3`, the action of the split type-`D` Lie algebra on `S⁻` is injective. -/
theorem typeDSpinMinusLieRep_injective_of_card_eq_three (hι : Fintype.card ι = 3) :
    Function.Injective (P.typeDSpinMinusLieRep b hline) := fun x y h ↦ by
  obtain ⟨B', hB'⟩ := P.exists_basis_toMatrix_typeDSpinMinusLieRep_eq_neg_transpose b hline hι
    (P.monomialBasis b hι)
  have hxy := congrArg (LinearMap.toMatrix B' B') h
  rw [hB', hB', neg_inj, Matrix.transpose_inj, EmbeddingLike.apply_eq_iff_eq] at hxy
  exact P.typeDSpinPlusLieRep_injective_of_card_eq_three b hline hι hxy

/-- **The image of `so₆` in `End S⁻` is `sl(S⁻)`.** For an even polarization with `dim W = 3`,
an endomorphism of the odd half-spin module is the action of an element of the split type-`D`
Lie algebra if and only if its trace vanishes. -/
theorem mem_range_typeDSpinMinusLieRep_iff_of_card_eq_three (hι : Fintype.card ι = 3)
    {f : Module.End K (spinMinus Q P)} :
    f ∈ (P.typeDSpinMinusLieRep b hline).range ↔ LinearMap.trace K (spinMinus Q P) f = 0 := by
  rw [LieHom.mem_range]
  refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ P.trace_typeDSpinMinusLieRep_eq_zero_of_card_eq_three b hline hι x,
    fun hf ↦ ?_⟩
  set B := P.monomialBasis b hι
  obtain ⟨B', hB'⟩ := P.exists_basis_toMatrix_typeDSpinMinusLieRep_eq_neg_transpose b hline hι B
  -- The endomorphism of `S⁺` whose matrix is minus the transpose of that of `f`.
  set g := Matrix.toLin B B (-(LinearMap.toMatrix B' B' f)ᵀ)
  have hg : LinearMap.trace K (spinPlus Q P) g = 0 := by
    rw [LinearMap.trace_eq_matrix_trace K B, LinearMap.toMatrix_toLin, Matrix.trace_neg,
      Matrix.trace_transpose, ← LinearMap.trace_eq_matrix_trace, hf, neg_zero]
  obtain ⟨x, hx⟩ := (LieHom.mem_range _ _).mp
    ((P.mem_range_typeDSpinPlusLieRep_iff_of_card_eq_three b hline hι).mpr hg)
  refine ⟨x, (LinearMap.toMatrix B' B').injective ?_⟩
  rw [hB', hx, LinearMap.toMatrix_toLin, Matrix.transpose_neg, Matrix.transpose_transpose,
    neg_neg]

end TauCeti.SpinPolarizationData
