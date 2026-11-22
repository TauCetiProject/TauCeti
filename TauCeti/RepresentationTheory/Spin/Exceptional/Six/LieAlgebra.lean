/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Representation
import TauCeti.Algebra.Lie.GeneralLinear.Finrank
import TauCeti.Algebra.Lie.SpecialLinear.Root.Generation
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
`so₆` and `sl₄` have dimension fifteen, which forces the image to be `sl₄` and the action to be
injective: `so₆` is identified with the quadratic Clifford elements by
`TauCeti.SpinPolarizationData.typeDQuadraticEquiv`, hence with `⋀²V` by
`CliffordAlgebra.bivectorExteriorEquivQuadraticLieSubalgebra`, while `TauCeti.finrank_sl` counts
`sl₄`. The duality comes from reversal, which negates quadratic
Clifford elements (`TauCeti.SpinPolarizationData.reverseEven_typeDToEvenLieHom`) and exchanges the
two simple factors of the even Clifford algebra
(`TauCeti.exists_linearEquiv_intertwines_dual_spinPlusAction_spinMinusAction_reverseEven`).

## Main definitions and results

* `TauCeti.SpinPolarizationData.typeDSpinPlusLieRep_injective_of_card_eq_three`: `so₆` acts
  faithfully on `S⁺`.
* `TauCeti.SpinPolarizationData.mem_range_typeDSpinPlusLieRep_iff_of_card_eq_three`: the image of
  `so₆` in `End S⁺` is the trace-zero endomorphisms.
* `TauCeti.SpinPolarizationData.typeDSpinPlusLieEquivSl`: the resulting Lie algebra isomorphism
  `so₆ ≃ sl₄`, given by the matrix of the action on `S⁺` in a chosen basis.
* `exists_linearEquiv_intertwines_dual_typeDSpinPlusLieRep_typeDSpinMinusLieRep`, in the
  namespace `TauCeti.SpinPolarizationData`: a single linear equivalence from the dual of `S⁺` to
  `S⁻` intertwines both the `so₆` actions and the Spin group actions, so `S⁻` is the dual of `S⁺`.
* `TauCeti.SpinPolarizationData.exists_basis_toMatrix_typeDSpinMinusLieRep_eq_neg_transpose`:
  the same duality in matrix form: in a suitable basis of `S⁻`, each element of `so₆` acts by minus
  the transpose of its matrix on `S⁺`.

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

/-! ### Dimensions -/

include b hline in
/-- The split type-`D` Lie algebra of rank three has dimension `15 = (6 choose 2)`, read off from
its quadratic Clifford realization `so₆ ≅ ⋀²V`. -/
private theorem finrank_typeD_of_card_eq_three (hι : Fintype.card ι = 3) :
    finrank K (LieAlgebra.Orthogonal.typeD ι K) = 15 := by
  have : Module.Free K V := Module.Free.of_basis (P.typeDBasis b hline)
  have : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  rw [(P.typeDQuadraticEquiv b hline).toLinearEquiv.finrank_eq,
    ← (bivectorExteriorEquivQuadraticLieSubalgebra Q).finrank_eq, exteriorPower.finrank_eq,
    P.finrank_eq_two_mul_card b hline, hι]
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
    exact polar_spinSixTransvectionVectors_eq_zero P b₃ hij 1
  have hmem : (g : CliffordAlgebra Q) - 1 ∈ quadraticLieSubalgebra Q := by
    rw [coe_spinSixTransvectionLift, add_sub_cancel_left, ← bivector_eq_ι_mul_ι_of_isOrtho Q hortho]
    exact bivector_mem_quadraticLieSubalgebra Q _ _
  -- The lift acts on `S⁺` by the elementary transvection `1 + E_{ij}`.
  have hlift : LinearMap.toMatrix (monomialBasis P b hι) (monomialBasis P b hι)
      (spinPlusAction Q P hline (spinGroupToEven Q g)) = Matrix.transvection i j 1 :=
    toMatrix_spinPlusAction_spinSixTransvectionLift P hline b₃ hij 1
  have heven : P.typeDToEvenLieHom b hline ((P.typeDQuadraticEquiv b hline).symm ⟨_, hmem⟩) =
      spinGroupToEven Q g - 1 :=
    Subtype.ext (by simp)
  refine ⟨(P.typeDQuadraticEquiv b hline).symm ⟨_, hmem⟩, ?_⟩
  simp [typeDSpinPlusLieRep_apply, heven, hlift, Matrix.transvection]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The action of `so₆` on `S⁺`, read as matrices in a basis of `S⁺`. -/
private noncomputable def matrixLieHom (B : Basis κ K (spinPlus Q P)) :
    LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ Matrix κ κ K :=
  (LinearMap.toMatrixAlgEquiv B).toLieEquiv.toLieHom.comp (P.typeDSpinPlusLieRep b hline)

private theorem matrixLieHom_apply (B : Basis κ K (spinPlus Q P))
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    P.matrixLieHom b hline B x = LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x) := by
  rw [matrixLieHom, LieHom.comp_apply, LieEquiv.coe_toLieHom, AlgEquiv.toLieEquiv_apply,
    LinearMap.toMatrixAlgEquiv, AlgEquiv.ofLinearEquiv_apply]

/-- An off-diagonal matrix unit of `sl₄` lies in the image of `so₆`, in the even monomial
basis. -/
private theorem single_mem_comap_range_matrixLieHom (hι : Fintype.card ι = 3) {i j : Fin 4}
    (hij : i ≠ j) :
    SpecialLinear.single i j hij (1 : K) ∈
      (P.matrixLieHom b hline (monomialBasis P b hι)).range.comap
        (SpecialLinear.sl (Fin 4) K).incl := by
  obtain ⟨x, hx⟩ := exists_toMatrix_typeDSpinPlusLieRep_eq_single P b hline hι hij
  rw [LieSubalgebra.mem_comap, LieHom.mem_range, LieSubalgebra.coe_incl, SpecialLinear.val_single]
  exact ⟨x, (matrixLieHom_apply P b hline _ x).trans hx⟩

/-- Every trace-zero matrix is the matrix, in the even monomial basis, of the action of an element
of `so₆` on `S⁺`. -/
private theorem sl_le_range_matrixLieHom (hι : Fintype.card ι = 3) :
    SpecialLinear.sl (Fin 4) K ≤ (P.matrixLieHom b hline (monomialBasis P b hι)).range := by
  rw [← LieSubalgebra.comap_incl_eq_top, eq_top_iff,
    ← lieSpan_specialLinear_adjacent_single_eq_top 3 K, LieSubalgebra.lieSpan_le]
  rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> exact single_mem_comap_range_matrixLieHom P b hline hι _

/-- The matrices in the even monomial basis of the action of `so₆` on `S⁺` are exactly the
trace-zero matrices: the image contains them, and both have dimension fifteen. -/
private theorem range_matrixLieHom (hι : Fintype.card ι = 3) :
    (P.matrixLieHom b hline (monomialBasis P b hι)).range = SpecialLinear.sl (Fin 4) K := by
  refine (LieSubalgebra.toSubmodule_injective <|
    Submodule.eq_of_le_of_finrank_le (sl_le_range_matrixLieHom P b hline hι) ?_).symm
  -- `sl` and its underlying submodule are the same subtype with the same module structure.
  change _ ≤ finrank K (SpecialLinear.sl (Fin 4) K)
  rw [finrank_sl, LieHom.range_toSubmodule]
  simpa [finrank_typeD_of_card_eq_three P b hline hι] using
    LinearMap.finrank_range_le (P.matrixLieHom b hline (monomialBasis P b hι)).toLinearMap

private theorem injective_matrixLieHom (hι : Fintype.card ι = 3) :
    Function.Injective (P.matrixLieHom b hline (monomialBasis P b hι)) := by
  set f := P.matrixLieHom b hline (monomialBasis P b hι)
  have hfin : finrank K (LieAlgebra.Orthogonal.typeD ι K) = finrank K f.range := by
    rw [finrank_typeD_of_card_eq_three P b hline hι, range_matrixLieHom P b hline hι, finrank_sl]
    simp
  have hrr : Function.Injective f.rangeRestrict :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr
      f.surjective_rangeRestrict
  exact fun x y h ↦ hrr (Subtype.ext (by simpa only [LieHom.rangeRestrict_apply] using h))

/-- **`so₆` acts faithfully on the even half-spin module.** For an even polarization with
`dim W = 3`, the action of the split type-`D` Lie algebra on `S⁺` is injective. -/
theorem typeDSpinPlusLieRep_injective_of_card_eq_three (hι : Fintype.card ι = 3) :
    Function.Injective (P.typeDSpinPlusLieRep b hline) := fun x y h ↦
  injective_matrixLieHom P b hline hι (by rw [matrixLieHom_apply, matrixLieHom_apply, h])

/-- Every element of `so₆` acts on the even half-spin module by an endomorphism of trace zero. -/
theorem trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_three (hι : Fintype.card ι = 3)
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    LinearMap.trace K (spinPlus Q P) (P.typeDSpinPlusLieRep b hline x) = 0 := by
  have hx : P.matrixLieHom b hline (monomialBasis P b hι) x ∈ SpecialLinear.sl (Fin 4) K := by
    rw [← range_matrixLieHom P b hline hι]
    exact LieHom.mem_range_self _ x
  rw [SpecialLinear.mem_sl_iff, matrixLieHom_apply] at hx
  rw [LinearMap.trace_eq_matrix_trace K (monomialBasis P b hι), hx]

/-- **The image of `so₆` in `End S⁺` is `sl(S⁺)`.** For an even polarization with `dim W = 3`,
an endomorphism of the even half-spin module is the action of an element of the split type-`D`
Lie algebra if and only if its trace vanishes. -/
theorem mem_range_typeDSpinPlusLieRep_iff_of_card_eq_three (hι : Fintype.card ι = 3)
    {f : Module.End K (spinPlus Q P)} :
    f ∈ (P.typeDSpinPlusLieRep b hline).range ↔ LinearMap.trace K (spinPlus Q P) f = 0 := by
  refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ P.trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_three b hline hι x,
    fun hf ↦ ?_⟩
  have hA : LinearMap.toMatrix (monomialBasis P b hι) (monomialBasis P b hι) f ∈
      SpecialLinear.sl (Fin 4) K := by
    rw [SpecialLinear.mem_sl_iff, ← LinearMap.trace_eq_matrix_trace, hf]
  obtain ⟨x, hx⟩ := (LieHom.mem_range _ _).mp (sl_le_range_matrixLieHom P b hline hι hA)
  rw [matrixLieHom_apply] at hx
  exact (LieHom.mem_range _ _).mpr ⟨x, (LinearMap.toMatrix _ _).injective hx⟩

/-! ### The isomorphism `so₆ ≃ sl₄` -/

/-- In any basis of `S⁺`, the matrices of the action of `so₆` are exactly the trace-zero
matrices. -/
private theorem range_matrixLieHom_eq_sl (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) :
    (P.matrixLieHom b hline B).range = SpecialLinear.sl κ K := by
  ext A
  rw [LieHom.mem_range, SpecialLinear.mem_sl_iff]
  constructor
  · rintro ⟨x, rfl⟩
    rw [matrixLieHom_apply, ← LinearMap.trace_eq_matrix_trace,
      P.trace_typeDSpinPlusLieRep_eq_zero_of_card_eq_three b hline hι]
  · intro hA
    obtain ⟨x, hx⟩ := (LieHom.mem_range _ _).mp
      ((P.mem_range_typeDSpinPlusLieRep_iff_of_card_eq_three b hline hι
        (f := Matrix.toLin B B A)).mpr
        (by rw [LinearMap.trace_eq_matrix_trace K B, LinearMap.toMatrix_toLin, hA]))
    exact ⟨x, by rw [matrixLieHom_apply, hx, LinearMap.toMatrix_toLin]⟩

/-- **`D₃ ≅ A₃`.** For an even polarization with `dim W = 3` and a basis `B` of the even
half-spin module `S⁺`, sending an element of the split type-`D` Lie algebra `so₆` to the matrix
of its action on `S⁺` in the basis `B` is a Lie algebra isomorphism onto the trace-zero matrices.
Through it, `S⁺` is the standard module of `sl₄`. -/
noncomputable def typeDSpinPlusLieEquivSl (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) :
    LieAlgebra.Orthogonal.typeD ι K ≃ₗ⁅K⁆ SpecialLinear.sl κ K :=
  (LieEquiv.ofInjective (P.matrixLieHom b hline B) fun x y h ↦
      P.typeDSpinPlusLieRep_injective_of_card_eq_three b hline hι <|
        (LinearMap.toMatrix B B).injective <| by
          rwa [matrixLieHom_apply, matrixLieHom_apply] at h).trans
    (LieEquiv.ofEq _ _ (by rw [range_matrixLieHom_eq_sl P b hline hι B]))

/-- The isomorphism `so₆ ≃ sl₄` sends an element of `so₆` to the matrix of its action on `S⁺`. -/
@[simp]
theorem coe_typeDSpinPlusLieEquivSl_apply (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) (x : LieAlgebra.Orthogonal.typeD ι K) :
    (P.typeDSpinPlusLieEquivSl b hline hι B x : Matrix κ κ K) =
      LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x) := by
  rw [typeDSpinPlusLieEquivSl, LieEquiv.trans_apply, LieEquiv.ofEq_apply]
  exact (LieEquiv.ofInjective_apply _ _ x).trans (matrixLieHom_apply P b hline B x)

/-! ### `S⁻` is the dual of `S⁺` -/

/-- **The odd half-spin module of `so₆` is the dual of the even one.** For an even polarization
with `dim W = 3`, there is a linear equivalence `T` from the dual of `S⁺` to `S⁻` that intertwines
the contragredient action `φ ↦ -φ ∘ ρ⁺(x)` of each element `x` of the split type-`D` Lie algebra
with its action `ρ⁻(x)` on `S⁻`. The same `T` also intertwines the contragredient action of the
Spin group on the dual of `S⁺` with its action on `S⁻`. -/
theorem exists_linearEquiv_intertwines_dual_typeDSpinPlusLieRep_typeDSpinMinusLieRep
    (hι : Fintype.card ι = 3) :
    ∃ T : Module.Dual K (spinPlus Q P) ≃ₗ[K] spinMinus Q P,
      (∀ (x : LieAlgebra.Orthogonal.typeD ι K) (φ : Module.Dual K (spinPlus Q P)),
        T ((-P.typeDSpinPlusLieRep b hline x).dualMap φ) =
          P.typeDSpinMinusLieRep b hline x (T φ)) ∧
      ∀ (g : spinGroup Q) (φ : Module.Dual K (spinPlus Q P)),
        T ((spinPlusAction Q P hline (spinGroupToEven Q g⁻¹)).dualMap φ) =
          spinMinusAction Q P hline (spinGroupToEven Q g) (T φ) := by
  have : NeZero (2 : K) := ⟨Invertible.ne_zero 2⟩
  obtain ⟨T, hT⟩ :=
    exists_linearEquiv_intertwines_dual_spinPlusAction_spinMinusAction_reverseEven P hline
      (by rw [P.finrank_eq_two_mul_card b hline, hι])
  refine ⟨T, fun x φ ↦ ?_, fun g φ ↦ ?_⟩
  · -- Reversal negates the even Clifford image of `x`, which supplies the sign.
    have h := hT (-P.typeDToEvenLieHom b hline x) φ
    rwa [map_neg (reverseEven Q), reverseEven_typeDToEvenLieHom, neg_neg,
      ← typeDSpinMinusLieRep_apply, map_neg, ← typeDSpinPlusLieRep_apply] at h
  · -- Reversal inverts Spin group elements.
    have h := hT (spinGroupToEven Q g⁻¹) φ
    rwa [reverseEven_spinGroupToEven, inv_inv] at h

/-- **The odd half-spin module of `so₆` is the dual of the even one, in matrix form.** For an even
polarization with `dim W = 3` and any basis `B` of `S⁺`, there is a basis `B'` of `S⁻` in which
every element of the split type-`D` Lie algebra acts on `S⁻` by minus the transpose of its matrix
on `S⁺`. Combined with `TauCeti.SpinPolarizationData.typeDSpinPlusLieEquivSl`, `S⁻` is the dual of
the standard module of `sl₄`. -/
theorem exists_basis_toMatrix_typeDSpinMinusLieRep_eq_neg_transpose (hι : Fintype.card ι = 3)
    (B : Basis κ K (spinPlus Q P)) :
    ∃ B' : Basis κ K (spinMinus Q P), ∀ x : LieAlgebra.Orthogonal.typeD ι K,
      LinearMap.toMatrix B' B' (P.typeDSpinMinusLieRep b hline x) =
        -(LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x))ᵀ := by
  obtain ⟨T, hT, -⟩ :=
    P.exists_linearEquiv_intertwines_dual_typeDSpinPlusLieRep_typeDSpinMinusLieRep b hline hι
  refine ⟨B.dualBasis.map T, fun x ↦ ?_⟩
  have hconj : T.symm.toLinearMap ∘ₗ P.typeDSpinMinusLieRep b hline x ∘ₗ T.toLinearMap =
      Module.Dual.transpose (R := K) (-P.typeDSpinPlusLieRep b hline x) :=
    LinearMap.ext fun φ ↦ T.symm_apply_eq.mpr (hT x φ).symm
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right, hconj,
    LinearMap.toMatrix_transpose, ← Matrix.transpose_neg]
  exact congrArg Matrix.transpose (map_neg (LinearMap.toMatrix B B) _)

end TauCeti.SpinPolarizationData
