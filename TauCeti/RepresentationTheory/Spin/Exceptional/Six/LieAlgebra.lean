/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Representation
import Mathlib.LinearAlgebra.Matrix.Dual
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Finrank
import TauCeti.Algebra.Lie.SpecialLinear.Root.Generation
import TauCeti.LinearAlgebra.CliffordAlgebra.CliffordExteriorSquare
import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Characterization
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.SpecialLinear
import TauCeti.RepresentationTheory.Spin.Exceptional.Six.HalfSpinDual

/-!
# The half-spin Lie modules of `so₆`: the isomorphism `D₃ ≅ A₃`

Let `P` be an even polarization `V = W ⊕ W'` with `dim W = 3`, over a field in which `2` is
invertible, and let `b` be a basis of `W`. The split type-`D` matrix Lie algebra `so₆` acts on
the two half-spin modules `S⁺ = ⋀ᵉᵛᵉⁿ W` and `S⁻ = ⋀ᵒᵈᵈ W`, both of dimension four, through its
quadratic Clifford realization (`TauCeti.SpinPolarizationData.typeDSpinPlusLieRep` and
`TauCeti.SpinPolarizationData.typeDSpinMinusLieRep`). This file proves that these are the
standard module of `sl₄` and its dual:

* the action on `S⁺` is faithful and its image is exactly the trace-zero endomorphisms, so it is a
  Lie algebra isomorphism `so₆ ≃ sl(S⁺)`; in any basis of `S⁺` this is `so₆ ≃ sl₄`;
* in a suitable basis of `S⁻`, every element of `so₆` acts on `S⁻` by minus the transpose of its
  matrix on `S⁺`, that is, `S⁻` is the dual of the standard module.

These are the Lie-algebra counterparts of the group isomorphism
`TauCeti.spinGroupEquivSpecialLinearGroupOfFinrankEqSix` and of the duality
`TauCeti.exists_spinMinusSubrep_equiv_dual_spinPlusSubrep_of_finrank_eq_six`. Taking for the basis
of `S⁺` the basis `TauCeti.spinPlusFinBasisOfFinrankEqSix` used there, the Lie isomorphism below
reads matrices in the same coordinates as the group isomorphism.

## The argument

The canonical Spin lift `1 + ι w * ι u` of an elementary transvection acts on `S⁺` by the
elementary transvection `1 + E_{ij}` in the even monomial basis
(`TauCeti.toMatrix_spinPlusAction_spinSixTransvectionLift`). Since `u` and `w` are orthogonal,
`ι w * ι u` is a Clifford bivector, so every off-diagonal matrix unit `E_{ij}` is the action of an
element of `so₆`. The adjacent matrix units generate `sl₄` as a Lie algebra
(`TauCeti.lieSpan_specialLinear_adjacent_single_eq_top`), so the image contains `sl₄`. Both
`so₆ ≅ ⋀²V` and `sl₄` have dimension fifteen, which forces the image to be `sl₄` and the action to
be injective. The duality comes from reversal, which negates quadratic Clifford elements and
exchanges the two simple factors of the even Clifford algebra
(`TauCeti.exists_linearEquiv_dual_spinPlus_conj`).

## Main definitions and results

* `TauCeti.SpinPolarizationData.typeDSpinPlusLieRep_injective_of_card_eq_three`: `so₆` acts
  faithfully on `S⁺`.
* `TauCeti.SpinPolarizationData.mem_range_typeDSpinPlusLieRep_iff_of_card_eq_three`: the image of
  `so₆` in `End S⁺` is the trace-zero endomorphisms.
* `TauCeti.SpinPolarizationData.typeDSpinPlusLieEquivSl`: the resulting Lie algebra isomorphism
  `so₆ ≃ sl₄`, given by the matrix of the action on `S⁺` in a chosen basis.
* `TauCeti.SpinPolarizationData.exists_basis_toMatrix_typeDSpinMinusLieRep_eq_neg_transpose`:
  `S⁻` is the dual of `S⁺` as an `so₆`-module.

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

/-- Reversal negates the even Clifford image of a split type-`D` matrix, since it is
quadratic. -/
private theorem reverseEven_typeDToEvenLieHom (x : LieAlgebra.Orthogonal.typeD ι K) :
    reverseEven Q (P.typeDToEvenLieHom b hline x) = -P.typeDToEvenLieHom b hline x :=
  Subtype.ext <| by
    rw [coe_reverseEven_apply, NegMemClass.coe_neg, coe_typeDToEvenLieHom_apply,
      reverse_eq_neg_of_mem_quadraticLieSubalgebra Q (P.typeDQuadraticEquiv b hline x).property]

/-! ### Dimensions -/

omit [Invertible (2 : K)] [DecidableEq ι] in
include b hline in
private theorem finrank_eq_six_of_card_eq_three (hι : Fintype.card ι = 3) : finrank K V = 6 := by
  classical
  rw [finrank_eq_card_basis (P.typeDBasis b hline), Fintype.card_sum, hι]

include b hline in
/-- The split type-`D` Lie algebra of rank three has dimension `15 = (6 choose 2)`, read off from
its quadratic Clifford realization `so₆ ≅ ⋀²V`. -/
private theorem finrank_typeD_of_card_eq_three (hι : Fintype.card ι = 3) :
    finrank K (LieAlgebra.Orthogonal.typeD ι K) = 15 := by
  have : Module.Free K V := Module.Free.of_basis (P.typeDBasis b hline)
  have : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  rw [(P.typeDQuadraticEquiv b hline).toLinearEquiv.finrank_eq,
    ← (bivectorExteriorEquivQuadraticLieSubalgebra Q).finrank_eq, exteriorPower.finrank_eq,
    finrank_eq_six_of_card_eq_three P b hline hι]
  rfl

/-! ### The image of `so₆` in `End S⁺` -/

/-- The even monomial basis `1, e₀e₁, e₀e₂, e₁e₂` of `S⁺`, for the basis `b` of `W` renumbered by
`Fin 3`. -/
private noncomputable abbrev monomialBasis (hι : Fintype.card ι = 3) :
    Basis (Fin 4) K (spinPlus Q P) :=
  (b.reindex (Fintype.equivFinOfCardEq hι)).spinSixEvenMonomialBasis (spinPlus_def P)

/-- Every off-diagonal matrix unit in the even monomial basis of `S⁺` is the action of an element
of `so₆`: the bivector part `ι w * ι u` of the canonical Spin lift `1 + ι w * ι u` of the
corresponding elementary transvection. -/
private theorem exists_toMatrix_typeDSpinPlusLieRep_eq_single (hι : Fintype.card ι = 3)
    {i j : Fin 4} (hij : i ≠ j) :
    ∃ x, LinearMap.toMatrix (monomialBasis P b hι) (monomialBasis P b hι)
      (P.typeDSpinPlusLieRep b hline x) = Matrix.single i j 1 := by
  set b₃ := b.reindex (Fintype.equivFinOfCardEq hι)
  set g := spinSixTransvectionLift P hline b₃ hij 1
  have hortho : Q.IsOrtho (spinSixTransvectionSecondVector P b₃ i j 1)
      (spinSixTransvectionFirstVector P b₃ i j) := by
    rw [← QuadraticMap.isOrtho_polarBilin, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_comm]
    exact spinSixTransvectionVectors_polar P b₃ hij 1
  have hmem : (g : CliffordAlgebra Q) - 1 ∈ quadraticLieSubalgebra Q := by
    rw [coe_spinSixTransvectionLift, add_sub_cancel_left, ← bivector_eq_ι_mul_ι_of_isOrtho Q hortho]
    exact bivector_mem_quadraticLieSubalgebra Q _ _
  refine ⟨(P.typeDQuadraticEquiv b hline).symm ⟨_, hmem⟩, ?_⟩
  have heven : P.typeDToEvenLieHom b hline ((P.typeDQuadraticEquiv b hline).symm ⟨_, hmem⟩) =
      spinGroupToEven Q g - 1 :=
    Subtype.ext (by rw [coe_typeDToEvenLieHom_apply, LieEquiv.apply_symm_apply]; simp)
  rw [typeDSpinPlusLieRep_apply, heven, map_sub, map_one, map_sub,
    toMatrix_spinPlusAction_spinSixTransvectionLift, LinearMap.toMatrix_one, Matrix.transvection,
    add_sub_cancel_left]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The action of `so₆` on `S⁺`, read as matrices in a basis of `S⁺`. -/
private noncomputable def matrixLieHom (B : Basis κ K (spinPlus Q P)) :
    LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ Matrix κ κ K :=
  { (LinearMap.toMatrix B B).toLinearMap ∘ₗ (P.typeDSpinPlusLieRep b hline).toLinearMap with
    map_lie' := fun {x y} ↦ by
      simp [Ring.lie_def, LinearMap.toMatrix_mul] }

private theorem matrixLieHom_apply (B : Basis κ K (spinPlus Q P))
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    P.matrixLieHom b hline B x = LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x) := rfl

/-- Every trace-zero matrix is the matrix, in the even monomial basis, of the action of an element
of `so₆` on `S⁺`. -/
private theorem sl_le_range_matrixLieHom (hι : Fintype.card ι = 3) :
    (SpecialLinear.sl (Fin 4) K).toSubmodule ≤
      LinearMap.range (P.matrixLieHom b hline (monomialBasis P b hι)).toLinearMap := by
  have hspan : LieSubalgebra.lieSpan K (SpecialLinear.sl (Fin (3 + 1)) K)
      (Set.range (fun i : Fin 3 ↦ SpecialLinear.single i.castSucc i.succ
        (Fin.castSucc_lt_succ (i := i)).ne (1 : K)) ∪
      Set.range (fun i : Fin 3 ↦ SpecialLinear.single i.succ i.castSucc
        (Fin.castSucc_lt_succ (i := i)).ne' (1 : K))) ≤
      (P.matrixLieHom b hline (monomialBasis P b hι)).range.comap
        (SpecialLinear.sl (Fin 4) K).incl := by
    rw [LieSubalgebra.lieSpan_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · obtain ⟨x, hx⟩ := exists_toMatrix_typeDSpinPlusLieRep_eq_single P b hline hι
        (Fin.castSucc_lt_succ (i := i)).ne
      refine (LieSubalgebra.mem_comap ..).2 ((LieHom.mem_range _ _).2 ⟨x, ?_⟩)
      rw [matrixLieHom_apply, hx, LieSubalgebra.coe_incl, SpecialLinear.val_single]
    · obtain ⟨x, hx⟩ := exists_toMatrix_typeDSpinPlusLieRep_eq_single P b hline hι
        (Fin.castSucc_lt_succ (i := i)).ne'
      refine (LieSubalgebra.mem_comap ..).2 ((LieHom.mem_range _ _).2 ⟨x, ?_⟩)
      rw [matrixLieHom_apply, hx, LieSubalgebra.coe_incl, SpecialLinear.val_single]
  rw [lieSpan_specialLinear_adjacent_single_eq_top] at hspan
  intro A hA
  obtain ⟨x, hx⟩ := hspan (LieSubalgebra.mem_top (⟨A, hA⟩ : SpecialLinear.sl (Fin 4) K))
  exact ⟨x, hx⟩

omit [Invertible (2 : K)] in
private theorem finrank_sl_toSubmodule_fin_four :
    finrank K (SpecialLinear.sl (Fin 4) K).toSubmodule = 15 :=
  -- `sl` and its underlying submodule are the same subtype with the same module structure.
  (finrank_sl (n := Fin 4) (R := K)).trans (by simp)

/-- The matrices in the even monomial basis of the action of `so₆` on `S⁺` are exactly the
trace-zero matrices: the image contains them, and both have dimension fifteen. -/
private theorem range_matrixLieHom (hι : Fintype.card ι = 3) :
    LinearMap.range (P.matrixLieHom b hline (monomialBasis P b hι)).toLinearMap =
      (SpecialLinear.sl (Fin 4) K).toSubmodule := by
  refine (Submodule.eq_of_le_of_finrank_le (sl_le_range_matrixLieHom P b hline hι) ?_).symm
  have : Module.Finite K (LieAlgebra.Orthogonal.typeD ι K) :=
    Module.finite_of_finrank_pos (by rw [finrank_typeD_of_card_eq_three P b hline hι]; omega)
  rw [finrank_sl_toSubmodule_fin_four, ← finrank_typeD_of_card_eq_three P b hline hι]
  exact LinearMap.finrank_range_le _

private theorem injective_matrixLieHom (hι : Fintype.card ι = 3) :
    Function.Injective (P.matrixLieHom b hline (monomialBasis P b hι)) := by
  have : Module.Finite K (LieAlgebra.Orthogonal.typeD ι K) :=
    Module.finite_of_finrank_pos (by rw [finrank_typeD_of_card_eq_three P b hline hι]; omega)
  have h := LinearMap.finrank_range_add_finrank_ker
    (P.matrixLieHom b hline (monomialBasis P b hι)).toLinearMap
  rw [range_matrixLieHom P b hline hι, finrank_typeD_of_card_eq_three P b hline hι,
    finrank_sl_toSubmodule_fin_four] at h
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))

/-- **`so₆` acts faithfully on the even half-spin module.** For an even polarization with
`dim W = 3`, the action of the split type-`D` Lie algebra on `S⁺` is injective. -/
theorem typeDSpinPlusLieRep_injective_of_card_eq_three (hι : Fintype.card ι = 3) :
    Function.Injective (P.typeDSpinPlusLieRep b hline) := fun x y h ↦
  injective_matrixLieHom P b hline hι (by rw [matrixLieHom_apply, matrixLieHom_apply, h])

/-- Every element of `so₆` acts on the even half-spin module by an endomorphism of trace zero. -/
theorem trace_typeDSpinPlusLieRep_of_card_eq_three (hι : Fintype.card ι = 3)
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    LinearMap.trace K (spinPlus Q P) (P.typeDSpinPlusLieRep b hline x) = 0 := by
  have hx : P.matrixLieHom b hline (monomialBasis P b hι) x ∈
      (SpecialLinear.sl (Fin 4) K).toSubmodule := by
    rw [← range_matrixLieHom P b hline hι]
    exact LinearMap.mem_range_self _ x
  rw [LieSubalgebra.mem_toSubmodule, SpecialLinear.mem_sl_iff, matrixLieHom_apply] at hx
  rw [LinearMap.trace_eq_matrix_trace K (monomialBasis P b hι), hx]

/-- **The image of `so₆` in `End S⁺` is `sl(S⁺)`.** For an even polarization with `dim W = 3`,
an endomorphism of the even half-spin module is the action of an element of the split type-`D`
Lie algebra if and only if its trace vanishes. -/
theorem mem_range_typeDSpinPlusLieRep_iff_of_card_eq_three (hι : Fintype.card ι = 3)
    {f : Module.End K (spinPlus Q P)} :
    f ∈ (P.typeDSpinPlusLieRep b hline).range ↔ LinearMap.trace K (spinPlus Q P) f = 0 := by
  refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ P.trace_typeDSpinPlusLieRep_of_card_eq_three b hline hι x,
    fun hf ↦ ?_⟩
  have hA : LinearMap.toMatrix (monomialBasis P b hι) (monomialBasis P b hι) f ∈
      (SpecialLinear.sl (Fin 4) K).toSubmodule := by
    rw [LieSubalgebra.mem_toSubmodule, SpecialLinear.mem_sl_iff,
      ← LinearMap.trace_eq_matrix_trace, hf]
  obtain ⟨x, hx⟩ := sl_le_range_matrixLieHom P b hline hι hA
  rw [LieHom.coe_toLinearMap, matrixLieHom_apply] at hx
  exact ⟨x, (LinearMap.toMatrix _ _).injective hx⟩

/-! ### The isomorphism `so₆ ≃ sl₄` -/

/-- **`D₃ ≅ A₃`.** For an even polarization with `dim W = 3` and a basis `B` of the even
half-spin module `S⁺`, sending an element of the split type-`D` Lie algebra `so₆` to the matrix
of its action on `S⁺` in the basis `B` is a Lie algebra isomorphism onto the trace-zero matrices.
Through it, `S⁺` is the standard module of `sl₄`. -/
noncomputable def typeDSpinPlusLieEquivSl (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) :
    LieAlgebra.Orthogonal.typeD ι K ≃ₗ⁅K⁆ SpecialLinear.sl κ K :=
  LieEquiv.ofBijective
    { toFun x := ⟨P.matrixLieHom b hline B x, by
        rw [SpecialLinear.mem_sl_iff, matrixLieHom_apply, ← LinearMap.trace_eq_matrix_trace,
          P.trace_typeDSpinPlusLieRep_of_card_eq_three b hline hι]⟩
      map_add' x y := Subtype.ext (map_add _ x y)
      map_smul' c x := Subtype.ext (map_smul _ c x)
      map_lie' {x y} := Subtype.ext (LieHom.map_lie _ x y) }
    ⟨fun x y h ↦ P.typeDSpinPlusLieRep_injective_of_card_eq_three b hline hι <|
        (LinearMap.toMatrix B B).injective <| by
          simpa only [Subtype.ext_iff, LieHom.coe_mk, matrixLieHom_apply] using h,
      fun A ↦ by
        obtain ⟨x, hx⟩ := (P.mem_range_typeDSpinPlusLieRep_iff_of_card_eq_three b hline hι
          (f := Matrix.toLin B B A)).mpr (by
            rw [LinearMap.trace_eq_matrix_trace K B, LinearMap.toMatrix_toLin,
              ← SpecialLinear.mem_sl_iff]
            exact A.property)
        have hx' : P.typeDSpinPlusLieRep b hline x = Matrix.toLin B B A := hx
        exact ⟨x, Subtype.ext <| (matrixLieHom_apply P b hline B x).trans <| by
          rw [hx', LinearMap.toMatrix_toLin]⟩⟩

/-- The isomorphism `so₆ ≃ sl₄` sends an element of `so₆` to the matrix of its action on `S⁺`. -/
@[simp]
theorem coe_typeDSpinPlusLieEquivSl_apply (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) (x : LieAlgebra.Orthogonal.typeD ι K) :
    (P.typeDSpinPlusLieEquivSl b hline hι B x : Matrix κ κ K) =
      LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x) :=
  matrixLieHom_apply P b hline B x

/-! ### `S⁻` is the dual of `S⁺` -/

/-- **The odd half-spin module of `so₆` is the dual of the even one.** For an even polarization
with `dim W = 3` and any basis `B` of `S⁺`, there is a basis `B'` of `S⁻` in which every element of
the split type-`D` Lie algebra acts on `S⁻` by minus the transpose of its matrix on `S⁺`. Combined
with `TauCeti.SpinPolarizationData.typeDSpinPlusLieEquivSl`, `S⁻` is the dual of the standard
module of `sl₄`. -/
theorem exists_basis_toMatrix_typeDSpinMinusLieRep_eq_neg_transpose (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) :
    ∃ B' : Basis κ K (spinMinus Q P), ∀ x : LieAlgebra.Orthogonal.typeD ι K,
      LinearMap.toMatrix B' B' (P.typeDSpinMinusLieRep b hline x) =
        -(LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x))ᵀ := by
  have : NeZero (2 : K) := ⟨Invertible.ne_zero 2⟩
  obtain ⟨T, hT⟩ := exists_linearEquiv_dual_spinPlus_conj P hline
    (finrank_eq_six_of_card_eq_three P b hline hι)
  refine ⟨B.dualBasis.map T, fun x ↦ ?_⟩
  -- Reversal negates the quadratic element of `x`, so `T` intertwines the two actions up to sign.
  have hconj : T.symm.toLinearMap ∘ₗ P.typeDSpinMinusLieRep b hline x ∘ₗ T.toLinearMap =
      Module.Dual.transpose (R := K) (-P.typeDSpinPlusLieRep b hline x) := by
    refine LinearMap.ext fun φ ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_eq, Module.Dual.transpose_apply, LinearMap.comp_neg,
      ← LinearMap.dualMap_apply', map_neg, typeDSpinPlusLieRep_apply, hT,
      reverseEven_typeDToEvenLieHom, map_neg, LinearMap.neg_apply, neg_neg,
      typeDSpinMinusLieRep_apply]
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right, hconj,
    LinearMap.toMatrix_transpose, ← Matrix.transpose_neg]
  exact congrArg Matrix.transpose (map_neg (LinearMap.toMatrix B B) _)

end TauCeti.SpinPolarizationData
