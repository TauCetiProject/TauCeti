/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.Prod
public import TauCeti.RepresentationTheory.Spin.Polarization.TypeD.Representation
import TauCeti.Algebra.Lie.GeneralLinear.Finrank
import TauCeti.Algebra.Lie.SpecialLinear.Root.Generation
import TauCeti.LinearAlgebra.CliffordAlgebra.CliffordExteriorSquare
import TauCeti.LinearAlgebra.Matrix.ToLin
import TauCeti.RepresentationTheory.Spin.Dimension
import TauCeti.RepresentationTheory.Spin.Exceptional.Four.RootOperators

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
in `TauCeti`.

## The argument

In the oriented exterior basis `1, w₀, w₁, w₀ ∧ w₁` of the spinor module, the positive and negative
simple-root bivectors act by matrix units
(`TauCeti.toMatrix_spinAction_typeDSimpleRootBivector_fin_two` and its negative analogue): the
chain root pair moves between `w₀` and `w₁`, inside `S⁻`, and the fork root pair moves between
`1` and `w₀ ∧ w₁`, inside `S⁺`. Hence the image of `so₄` contains the raising and lowering matrices
of each factor, with zero in the other factor. These generate `sl₂` as a Lie algebra
(`TauCeti.lieSpan_specialLinear_adjacent_single_eq_top`), so the image contains `sl₂ × sl₂`. Both
`so₄ ≅ ⋀²V` and `sl₂ × sl₂` have dimension six, which forces the image to be `sl₂ × sl₂` and the
paired action to be injective.

## Main definitions and results

All declarations are in the namespace `TauCeti.SpinPolarizationData`.

* `typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_injective_of_card_eq_two`: `so₄` acts faithfully
  on `S⁺ × S⁻`.
* `mem_range_typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_iff_of_card_eq_two`: the image of the
  paired action consists of the pairs of trace-zero endomorphisms.
* `mem_range_typeDSpinPlusLieRep_iff_of_card_eq_two` and
  `mem_range_typeDSpinMinusLieRep_iff_of_card_eq_two`: each half-spin image is `sl₂`.
* `typeDHalfSpinLieEquivSlProdSl`: the Lie algebra isomorphism `so₄ ≃ sl₂ × sl₂` given by the
  matrices of the two half-spin actions.

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

/-! ### Dimension -/

include b hline in
/-- The split type-`D` Lie algebra of rank two has dimension `6 = (4 choose 2)`, read off from its
quadratic Clifford realization `so₄ ≅ ⋀²V`. -/
private theorem finrank_typeD_of_card_eq_two (hι : Fintype.card ι = 2) :
    finrank K (LieAlgebra.Orthogonal.typeD ι K) = 6 := by
  have : Module.Free K V := Module.Free.of_basis (P.typeDBasis b hline)
  have : Module.Finite K V := Module.Finite.of_basis (P.typeDBasis b hline)
  rw [(P.typeDQuadraticEquiv b hline).toLinearEquiv.finrank_eq,
    ← (bivectorExteriorEquivQuadraticLieSubalgebra Q).finrank_eq, exteriorPower.finrank_eq,
    finrank_eq_card_basis (P.typeDBasis b hline), Fintype.card_sum, hι]
  rfl

omit [Invertible (2 : K)] in
private theorem finrank_sl_toSubmodule_fin_two :
    finrank K (SpecialLinear.sl (Fin 2) K).toSubmodule = 3 :=
  -- `sl` and its underlying submodule are the same subtype with the same module structure.
  (finrank_sl (n := Fin 2) (R := K)).trans (by simp)

/-! ### Quadratic Clifford elements acting on the half-spin modules -/

/-- An element of `so₄` given by a quadratic Clifford element acts on `S⁺` through the spin
action of that element. -/
private theorem coe_typeDSpinPlusLieRep_symm_apply {y : CliffordAlgebra Q}
    (hy : y ∈ quadraticLieSubalgebra Q) (s : spinPlus Q P) :
    ((P.typeDSpinPlusLieRep b hline ((P.typeDQuadraticEquiv b hline).symm ⟨y, hy⟩) s :
      spinPlus Q P) : ExteriorAlgebra K P.W) = spinAction Q P y s := by
  rw [coe_typeDSpinPlusLieRep_apply, typeDSpinLieRep_apply, LieEquiv.apply_symm_apply]

/-- An element of `so₄` given by a quadratic Clifford element acts on `S⁻` through the spin
action of that element. -/
private theorem coe_typeDSpinMinusLieRep_symm_apply {y : CliffordAlgebra Q}
    (hy : y ∈ quadraticLieSubalgebra Q) (s : spinMinus Q P) :
    ((P.typeDSpinMinusLieRep b hline ((P.typeDQuadraticEquiv b hline).symm ⟨y, hy⟩) s :
      spinMinus Q P) : ExteriorAlgebra K P.W) = spinAction Q P y s := by
  rw [coe_typeDSpinMinusLieRep_apply, typeDSpinLieRep_apply, LieEquiv.apply_symm_apply]

/-! ### Restricting root matrices to the half-spin coordinates

A simple-root bivector acts on the spinor module by a matrix unit in the oriented exterior basis.
The lemmas below read off its action on a half-spin module whose basis is a subfamily of that
basis. -/

section Restrict

variable {S : Submodule K (ExteriorAlgebra K P.W)} {g : Fin 2 → Finset (Fin 2)}
  {y : CliffordAlgebra Q} {f : Module.End K S} {p q : Finset (Fin 2)}

omit [Invertible (2 : K)] in
/-- A Clifford element whose spin action is the matrix unit `single p q 1` sends the coordinate
vector at `q` to the coordinate vector at `p`, and every other coordinate vector to zero. -/
private theorem apply_basis_of_toMatrixAlgEquiv_eq_single (b₂ : Basis (Fin 2) K P.W)
    (B : Basis (Fin 2) K S)
    (hB : ∀ c, (B c : ExteriorAlgebra K P.W) = spinFourExteriorBasis P b₂ (g c))
    (hf : ∀ s, (f s : ExteriorAlgebra K P.W) = spinAction Q P y s)
    (h : LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b₂) (spinAction Q P y) =
      Matrix.single p q 1) (c : Fin 2) :
    (f (B c) : ExteriorAlgebra K P.W) = if q = g c then spinFourExteriorBasis P b₂ p else 0 := by
  have h' := congrArg (Matrix.toLinAlgEquiv (spinFourExteriorBasis P b₂)) h
  rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv] at h'
  rw [hf, hB, h', Module.Basis.toLinAlgEquiv_single_apply_basis]
  split_ifs <;> simp

omit [Invertible (2 : K)] in
/-- If both indices of the matrix unit are coordinates of the half-spin module, the restricted
action is the corresponding matrix unit. -/
private theorem toMatrix_eq_single_of_restrict (b₂ : Basis (Fin 2) K P.W)
    (B : Basis (Fin 2) K S)
    (hB : ∀ c, (B c : ExteriorAlgebra K P.W) = spinFourExteriorBasis P b₂ (g c))
    (hf : ∀ s, (f s : ExteriorAlgebra K P.W) = spinAction Q P y s)
    (h : LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b₂) (spinAction Q P y) =
      Matrix.single p q 1) (hg : Function.Injective g)
    {i j : Fin 2} (hp : g i = p) (hq : g j = q) :
    LinearMap.toMatrix B B f = Matrix.single i j 1 := by
  ext a c
  have hc : f (B c) = if j = c then B i else 0 := Subtype.ext <| by
    rw [P.apply_basis_of_toMatrixAlgEquiv_eq_single b₂ B hB hf h, ← hq, ← hp]
    by_cases hjc : j = c
    · simp [hjc, hB]
    · simp [hjc, hg.ne hjc]
  rw [LinearMap.toMatrix_apply, hc, Matrix.single_apply]
  by_cases hjc : j = c <;> simp [hjc, Finsupp.single_apply]

omit [Invertible (2 : K)] in
/-- If the column of the matrix unit is not a coordinate of the half-spin module, the restricted
action vanishes. -/
private theorem toMatrix_eq_zero_of_restrict (b₂ : Basis (Fin 2) K P.W)
    (B : Basis (Fin 2) K S)
    (hB : ∀ c, (B c : ExteriorAlgebra K P.W) = spinFourExteriorBasis P b₂ (g c))
    (hf : ∀ s, (f s : ExteriorAlgebra K P.W) = spinAction Q P y s)
    (h : LinearMap.toMatrixAlgEquiv (spinFourExteriorBasis P b₂) (spinAction Q P y) =
      Matrix.single p q 1) (hq : ∀ c, q ≠ g c) :
    LinearMap.toMatrix B B f = 0 := by
  rw [← map_zero (LinearMap.toMatrix B B)]
  congr 1
  refine B.ext fun c ↦ Subtype.ext ?_
  rw [P.apply_basis_of_toMatrixAlgEquiv_eq_single b₂ B hB hf h]
  simp [hq c]

end Restrict

/-! ### The coordinate bases of the two half-spin modules -/

section Coordinates

variable (b₂ : Basis (Fin 2) K P.W)

/-- The even coordinates `∅` and `{0, 1}` of the oriented rank-two exterior basis. -/
private def plusIndex : Fin 2 → Finset (Fin 2) := ![∅, {0, 1}]

/-- The odd coordinates `{0}` and `{1}` of the oriented rank-two exterior basis. -/
private def minusIndex : Fin 2 → Finset (Fin 2) := ![{0}, {1}]

private theorem plusIndex_injective : Function.Injective plusIndex := by
  unfold plusIndex; decide

private theorem minusIndex_injective : Function.Injective minusIndex := by
  unfold minusIndex; decide

omit [Invertible (2 : K)] in
private theorem spinFourExteriorBasis_plusIndex_mem (c : Fin 2) :
    spinFourExteriorBasis P b₂ (plusIndex c) ∈ spinPlus Q P := by
  rw [mem_spinPlus]
  fin_cases c
  · simpa [plusIndex] using Submodule.one_le.mp (one_le_evenOdd_zero _)
  · simpa [plusIndex] using ι_mul_ι_mem_evenOdd_zero (0 : QuadraticForm K P.W) (b₂ 0) (b₂ 1)

omit [Invertible (2 : K)] in
private theorem spinFourExteriorBasis_minusIndex_mem (c : Fin 2) :
    spinFourExteriorBasis P b₂ (minusIndex c) ∈ spinMinus Q P := by
  rw [mem_spinMinus]
  fin_cases c
  · simpa [minusIndex] using ι_mem_evenOdd_one (0 : QuadraticForm K P.W) (b₂ 0)
  · simpa [minusIndex] using ι_mem_evenOdd_one (0 : QuadraticForm K P.W) (b₂ 1)

omit [Invertible (2 : K)] in
include b₂ in
private theorem finrank_W_of_basis : finrank K P.W = 2 := by
  rw [finrank_eq_card_basis b₂, Fintype.card_fin]

/-- The basis `1, w₀ ∧ w₁` of `S⁺`. -/
private noncomputable def plusBasis : Basis (Fin 2) K (spinPlus Q P) :=
  have : FiniteDimensional K P.W := b₂.finiteDimensional_of_finite
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun c ↦ ⟨_, spinFourExteriorBasis_plusIndex_mem P b₂ c⟩)
    (LinearIndependent.of_comp (spinPlus Q P).subtype
      ((spinFourExteriorBasis P b₂).linearIndependent.comp _ plusIndex_injective))
    (by rw [finrank_spinPlus, finrank_W_of_basis P b₂, Fintype.card_fin]; rfl)

/-- The basis `w₀, w₁` of `S⁻`. -/
private noncomputable def minusBasis : Basis (Fin 2) K (spinMinus Q P) :=
  have : FiniteDimensional K P.W := b₂.finiteDimensional_of_finite
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun c ↦ ⟨_, spinFourExteriorBasis_minusIndex_mem P b₂ c⟩)
    (LinearIndependent.of_comp (spinMinus Q P).subtype
      ((spinFourExteriorBasis P b₂).linearIndependent.comp _ minusIndex_injective))
    (by
      have hW : P.W ≠ ⊥ := fun hW ↦ by
        have := finrank_W_of_basis P b₂
        rw [hW, finrank_bot] at this
        omega
      rw [finrank_spinMinus P hW, finrank_W_of_basis P b₂, Fintype.card_fin]; rfl)

omit [Invertible (2 : K)] in
private theorem coe_plusBasis (c : Fin 2) :
    (plusBasis P b₂ c : ExteriorAlgebra K P.W) = spinFourExteriorBasis P b₂ (plusIndex c) := by
  rw [plusBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

omit [Invertible (2 : K)] in
private theorem coe_minusBasis (c : Fin 2) :
    (minusBasis P b₂ c : ExteriorAlgebra K P.W) = spinFourExteriorBasis P b₂ (minusIndex c) := by
  rw [minusBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

end Coordinates

/-! ### The paired matrix action -/

variable {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- The action of `so₄` on `S⁺ × S⁻`, read as pairs of matrices in bases of the two half-spin
modules. -/
private noncomputable def matrixPairLieHom (B : Basis κ K (spinPlus Q P))
    (B' : Basis κ' K (spinMinus Q P)) :
    LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ Matrix κ κ K × Matrix κ' κ' K :=
  { ((LinearMap.toMatrix B B).toLinearMap ∘ₗ (P.typeDSpinPlusLieRep b hline).toLinearMap).prod
      ((LinearMap.toMatrix B' B').toLinearMap ∘ₗ (P.typeDSpinMinusLieRep b hline).toLinearMap) with
    map_lie' := fun {x y} ↦ Prod.ext (by simp [Ring.lie_def, LinearMap.toMatrix_mul])
      (by simp [Ring.lie_def, LinearMap.toMatrix_mul]) }

private theorem matrixPairLieHom_apply (B : Basis κ K (spinPlus Q P))
    (B' : Basis κ' K (spinMinus Q P)) (x : LieAlgebra.Orthogonal.typeD ι K) :
    P.matrixPairLieHom b hline B B' x =
      (LinearMap.toMatrix B B (P.typeDSpinPlusLieRep b hline x),
        LinearMap.toMatrix B' B' (P.typeDSpinMinusLieRep b hline x)) :=
  rfl

/-- The basis of `W` renumbered by `Fin 2`. -/
private noncomputable abbrev basisFinTwo (hι : Fintype.card ι = 2) : Basis (Fin 2) K P.W :=
  b.reindex (Fintype.equivFinOfCardEq hι)

/-- The paired action in the coordinate bases `1, w₀ ∧ w₁` of `S⁺` and `w₀, w₁` of `S⁻`. -/
private noncomputable abbrev coordinateLieHom (hι : Fintype.card ι = 2) :
    LieAlgebra.Orthogonal.typeD ι K →ₗ⁅K⁆ Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K :=
  P.matrixPairLieHom b hline (plusBasis P (P.basisFinTwo b hι)) (minusBasis P (P.basisFinTwo b hι))

/-- The fork root pair of `so₄` acts on `S⁺` by the raising and lowering matrices and trivially on
`S⁻`; the chain root pair acts trivially on `S⁺` and by the raising and lowering matrices on
`S⁻`. -/
private theorem coordinateLieHom_root_pairs (hι : Fintype.card ι = 2) :
    (∃ x, P.coordinateLieHom b hline hι x = (Matrix.single 0 1 1, 0)) ∧
    (∃ x, P.coordinateLieHom b hline hι x = (Matrix.single 1 0 1, 0)) ∧
    (∃ x, P.coordinateLieHom b hline hι x = (0, Matrix.single 0 1 1)) ∧
    (∃ x, P.coordinateLieHom b hline hι x = (0, Matrix.single 1 0 1)) := by
  set b₂ := P.basisFinTwo b hι
  have hplus := coe_plusBasis P b₂
  have hminus := coe_minusBasis P b₂
  have hP {y} (hy) := P.coe_typeDSpinPlusLieRep_symm_apply b hline (y := y) hy
  have hM {y} (hy) := P.coe_typeDSpinMinusLieRep_symm_apply b hline (y := y) hy
  have hpos (i : Fin 2) := toMatrix_spinAction_typeDSimpleRootBivector_fin_two P b₂ i
  have hneg (i : Fin 2) := toMatrix_spinAction_typeDSimpleNegativeRootBivector_fin_two P b₂ i
  have hmemPos (i : Fin 2) := P.typeDSimpleRootBivector_mem_quadraticLieSubalgebra b₂ (by omega) i
  have hmemNeg (i : Fin 2) :=
    P.typeDSimpleNegativeRootBivector_mem_quadraticLieSubalgebra b₂ (by omega) i
  -- The fork root pair is indexed by `1`, the chain root pair by `0`.
  refine ⟨⟨(P.typeDQuadraticEquiv b hline).symm ⟨_, hmemNeg 1⟩, ?_⟩,
    ⟨(P.typeDQuadraticEquiv b hline).symm ⟨_, hmemPos 1⟩, ?_⟩,
    ⟨(P.typeDQuadraticEquiv b hline).symm ⟨_, hmemPos 0⟩, ?_⟩,
    ⟨(P.typeDQuadraticEquiv b hline).symm ⟨_, hmemNeg 0⟩, ?_⟩⟩ <;>
  rw [matrixPairLieHom_apply, Prod.ext_iff] <;> constructor
  · exact P.toMatrix_eq_single_of_restrict b₂ _ hplus (hP _) (by simpa [plusIndex] using hneg 1)
      plusIndex_injective (i := 0) (j := 1) rfl rfl
  · exact P.toMatrix_eq_zero_of_restrict b₂ _ hminus (hM _) (by simpa using hneg 1)
      (by unfold minusIndex; decide)
  · exact P.toMatrix_eq_single_of_restrict b₂ _ hplus (hP _) (by simpa [plusIndex] using hpos 1)
      plusIndex_injective (i := 1) (j := 0) rfl rfl
  · exact P.toMatrix_eq_zero_of_restrict b₂ _ hminus (hM _) (by simpa using hpos 1)
      (by unfold minusIndex; decide)
  · exact P.toMatrix_eq_zero_of_restrict b₂ _ hplus (hP _) (by simpa using hpos 0)
      (by unfold plusIndex; decide)
  · exact P.toMatrix_eq_single_of_restrict b₂ _ hminus (hM _) (by simpa [minusIndex] using hpos 0)
      minusIndex_injective (i := 0) (j := 1) rfl rfl
  · exact P.toMatrix_eq_zero_of_restrict b₂ _ hplus (hP _) (by simpa using hneg 0)
      (by unfold plusIndex; decide)
  · exact P.toMatrix_eq_single_of_restrict b₂ _ hminus (hM _) (by simpa [minusIndex] using hneg 0)
      minusIndex_injective (i := 1) (j := 0) rfl rfl

omit [Invertible (2 : K)] in
/-- A Lie subalgebra of `sl₂` containing the raising and lowering matrices is everything. -/
private theorem eq_top_of_single_mem (S : LieSubalgebra K (SpecialLinear.sl (Fin 2) K))
    (he : SpecialLinear.single (0 : Fin 2) 1 zero_ne_one (1 : K) ∈ S)
    (hf : SpecialLinear.single (1 : Fin 2) 0 one_ne_zero (1 : K) ∈ S) : S = ⊤ := by
  rw [eq_top_iff, ← lieSpan_specialLinear_adjacent_single_eq_top (r := 1),
    LieSubalgebra.lieSpan_le]
  rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩) <;> obtain rfl := Subsingleton.elim i 0
  exacts [he, hf]

/-- Every pair of trace-zero matrices is the pair of matrices, in the coordinate bases, of the
actions of an element of `so₄` on `S⁺` and `S⁻`. -/
private theorem sl_prod_sl_le_range_coordinateLieHom (hι : Fintype.card ι = 2) :
    (SpecialLinear.sl (Fin 2) K).toSubmodule.prod (SpecialLinear.sl (Fin 2) K).toSubmodule ≤
      LinearMap.range (P.coordinateLieHom b hline hι).toLinearMap := by
  set sl₂ := SpecialLinear.sl (Fin 2) K
  let inc : sl₂ × sl₂ →ₗ⁅K⁆ Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K :=
    (sl₂.incl.comp (LieHom.fst K sl₂ sl₂)).prod (sl₂.incl.comp (LieHom.snd K sl₂ sl₂))
  set T := (P.coordinateLieHom b hline hι).range.comap inc
  obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, ⟨x₃, hx₃⟩, ⟨x₄, hx₄⟩⟩ := P.coordinateLieHom_root_pairs b hline hι
  have hmem {A : Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K} {a : sl₂ × sl₂}
      (ha : inc a = A) (x) (hx : P.coordinateLieHom b hline hι x = A) : a ∈ T :=
    (LieSubalgebra.mem_comap ..).2 ((LieHom.mem_range _ _).2 ⟨x, hx.trans ha.symm⟩)
  have hinl : T.comap (LieHom.inl K sl₂ sl₂) = ⊤ := eq_top_of_single_mem _
    (hmem (by simp [inc, SpecialLinear.val_single]) x₁ hx₁)
    (hmem (by simp [inc, SpecialLinear.val_single]) x₂ hx₂)
  have hinr : T.comap (LieHom.inr K sl₂ sl₂) = ⊤ := eq_top_of_single_mem _
    (hmem (by simp [inc, SpecialLinear.val_single]) x₃ hx₃)
    (hmem (by simp [inc, SpecialLinear.val_single]) x₄ hx₄)
  rintro ⟨A, A'⟩ ⟨hA, hA'⟩
  have h : ((⟨A, hA⟩, ⟨A', hA'⟩) : sl₂ × sl₂) ∈ T := by
    have h₁ : ((⟨A, hA⟩, 0) : sl₂ × sl₂) ∈ T :=
      (LieSubalgebra.mem_comap ..).1 (hinl ▸ LieSubalgebra.mem_top (⟨A, hA⟩ : sl₂))
    have h₂ : ((0, ⟨A', hA'⟩) : sl₂ × sl₂) ∈ T :=
      (LieSubalgebra.mem_comap ..).1 (hinr ▸ LieSubalgebra.mem_top (⟨A', hA'⟩ : sl₂))
    simpa using T.add_mem h₁ h₂
  obtain ⟨x, hx⟩ := (LieSubalgebra.mem_comap ..).1 h
  exact ⟨x, hx⟩

omit [Invertible (2 : K)] in
private theorem finrank_sl_prod_sl :
    finrank K ((SpecialLinear.sl (Fin 2) K).toSubmodule.prod
      (SpecialLinear.sl (Fin 2) K).toSubmodule) = 6 := by
  rw [(Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod, finrank_sl_toSubmodule_fin_two]

/-- The pairs of matrices, in the coordinate bases, of the actions of `so₄` on `S⁺` and `S⁻` are
exactly the pairs of trace-zero matrices: the image contains them, and both have dimension
six. -/
private theorem range_coordinateLieHom (hι : Fintype.card ι = 2) :
    LinearMap.range (P.coordinateLieHom b hline hι).toLinearMap =
      (SpecialLinear.sl (Fin 2) K).toSubmodule.prod (SpecialLinear.sl (Fin 2) K).toSubmodule := by
  refine (Submodule.eq_of_le_of_finrank_le (P.sl_prod_sl_le_range_coordinateLieHom b hline hι)
    ?_).symm
  have : Module.Finite K (LieAlgebra.Orthogonal.typeD ι K) :=
    Module.finite_of_finrank_pos (by rw [finrank_typeD_of_card_eq_two P b hline hι]; omega)
  rw [finrank_sl_prod_sl, ← finrank_typeD_of_card_eq_two P b hline hι]
  exact LinearMap.finrank_range_le _

private theorem injective_coordinateLieHom (hι : Fintype.card ι = 2) :
    Function.Injective (P.coordinateLieHom b hline hι) := by
  have : Module.Finite K (LieAlgebra.Orthogonal.typeD ι K) :=
    Module.finite_of_finrank_pos (by rw [finrank_typeD_of_card_eq_two P b hline hι]; omega)
  have h := LinearMap.finrank_range_add_finrank_ker (P.coordinateLieHom b hline hι).toLinearMap
  rw [range_coordinateLieHom P b hline hι, finrank_sl_prod_sl,
    finrank_typeD_of_card_eq_two P b hline hι] at h
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))

/-! ### The image of `so₄` in `End S⁺ × End S⁻` -/

/-- **`so₄` acts faithfully on the sum of its half-spin modules.** For an even polarization with
`dim W = 2`, an element of the split type-`D` Lie algebra is determined by its actions on `S⁺`
and `S⁻`. -/
theorem typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_injective_of_card_eq_two
    (hι : Fintype.card ι = 2) :
    Function.Injective ((P.typeDSpinPlusLieRep b hline).prod (P.typeDSpinMinusLieRep b hline)) :=
  fun x y h ↦ P.injective_coordinateLieHom b hline hι <| by
    rw [LieHom.prod_apply, LieHom.prod_apply, Prod.mk.injEq] at h
    rw [matrixPairLieHom_apply, matrixPairLieHom_apply, h.1, h.2]

/-- Every element of `so₄` acts on the even half-spin module by an endomorphism of trace zero. -/
theorem trace_typeDSpinPlusLieRep_of_card_eq_two (hι : Fintype.card ι = 2)
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    LinearMap.trace K (spinPlus Q P) (P.typeDSpinPlusLieRep b hline x) = 0 := by
  have hx : P.coordinateLieHom b hline hι x ∈ (SpecialLinear.sl (Fin 2) K).toSubmodule.prod
      (SpecialLinear.sl (Fin 2) K).toSubmodule := by
    rw [← range_coordinateLieHom P b hline hι]
    exact LinearMap.mem_range_self _ x
  have h := (Submodule.mem_prod.mp hx).1
  rw [LieSubalgebra.mem_toSubmodule, SpecialLinear.mem_sl_iff, matrixPairLieHom_apply] at h
  rw [LinearMap.trace_eq_matrix_trace K (plusBasis P (P.basisFinTwo b hι)), h]

/-- Every element of `so₄` acts on the odd half-spin module by an endomorphism of trace zero. -/
theorem trace_typeDSpinMinusLieRep_of_card_eq_two (hι : Fintype.card ι = 2)
    (x : LieAlgebra.Orthogonal.typeD ι K) :
    LinearMap.trace K (spinMinus Q P) (P.typeDSpinMinusLieRep b hline x) = 0 := by
  have hx : P.coordinateLieHom b hline hι x ∈ (SpecialLinear.sl (Fin 2) K).toSubmodule.prod
      (SpecialLinear.sl (Fin 2) K).toSubmodule := by
    rw [← range_coordinateLieHom P b hline hι]
    exact LinearMap.mem_range_self _ x
  have h := (Submodule.mem_prod.mp hx).2
  rw [LieSubalgebra.mem_toSubmodule, SpecialLinear.mem_sl_iff, matrixPairLieHom_apply] at h
  rw [LinearMap.trace_eq_matrix_trace K (minusBasis P (P.basisFinTwo b hι)), h]

/-- **The image of `so₄` in `End S⁺ × End S⁻` is `sl(S⁺) × sl(S⁻)`.** For an even polarization
with `dim W = 2`, a pair of endomorphisms of the two half-spin modules is the pair of actions of
an element of the split type-`D` Lie algebra if and only if both have trace zero. -/
theorem mem_range_typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_iff_of_card_eq_two
    (hι : Fintype.card ι = 2) {f : Module.End K (spinPlus Q P)}
    {f' : Module.End K (spinMinus Q P)} :
    (f, f') ∈ ((P.typeDSpinPlusLieRep b hline).prod (P.typeDSpinMinusLieRep b hline)).range ↔
      LinearMap.trace K (spinPlus Q P) f = 0 ∧ LinearMap.trace K (spinMinus Q P) f' = 0 := by
  rw [LieHom.mem_range]
  refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun ⟨hf, hf'⟩ ↦ ?_⟩
  · rw [LieHom.prod_apply, Prod.mk.injEq] at hx
    exact ⟨hx.1 ▸ P.trace_typeDSpinPlusLieRep_of_card_eq_two b hline hι x,
      hx.2 ▸ P.trace_typeDSpinMinusLieRep_of_card_eq_two b hline hι x⟩
  set Bp := plusBasis P (P.basisFinTwo b hι)
  set Bm := minusBasis P (P.basisFinTwo b hι)
  have hA : (LinearMap.toMatrix Bp Bp f, LinearMap.toMatrix Bm Bm f') ∈
      (SpecialLinear.sl (Fin 2) K).toSubmodule.prod (SpecialLinear.sl (Fin 2) K).toSubmodule := by
    rw [Submodule.mem_prod, LieSubalgebra.mem_toSubmodule, LieSubalgebra.mem_toSubmodule,
      SpecialLinear.mem_sl_iff, SpecialLinear.mem_sl_iff, ← LinearMap.trace_eq_matrix_trace,
      ← LinearMap.trace_eq_matrix_trace]
    exact ⟨hf, hf'⟩
  obtain ⟨x, hx⟩ := P.sl_prod_sl_le_range_coordinateLieHom b hline hι hA
  rw [LieHom.coe_toLinearMap, matrixPairLieHom_apply, Prod.mk.injEq] at hx
  exact ⟨x, by
    rw [LieHom.prod_apply, (LinearMap.toMatrix Bp Bp).injective hx.1,
      (LinearMap.toMatrix Bm Bm).injective hx.2]⟩

/-- **The image of `so₄` in `End S⁺` is `sl(S⁺)`.** For an even polarization with `dim W = 2`, an
endomorphism of the even half-spin module is the action of an element of the split type-`D` Lie
algebra if and only if its trace vanishes. -/
theorem mem_range_typeDSpinPlusLieRep_iff_of_card_eq_two (hι : Fintype.card ι = 2)
    {f : Module.End K (spinPlus Q P)} :
    f ∈ (P.typeDSpinPlusLieRep b hline).range ↔ LinearMap.trace K (spinPlus Q P) f = 0 := by
  refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ P.trace_typeDSpinPlusLieRep_of_card_eq_two b hline hι x,
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
  refine ⟨fun ⟨x, hx⟩ ↦ hx ▸ P.trace_typeDSpinMinusLieRep_of_card_eq_two b hline hι x,
    fun hf ↦ ?_⟩
  obtain ⟨x, hx⟩ :=
    (P.mem_range_typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_iff_of_card_eq_two b hline hι
      (f := 0)).mpr ⟨map_zero _, hf⟩
  exact ⟨x, congrArg Prod.snd hx⟩

/-! ### The isomorphism `so₄ ≃ sl₂ × sl₂` -/

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
            P.trace_typeDSpinPlusLieRep_of_card_eq_two b hline hι]⟩,
        ⟨(P.matrixPairLieHom b hline B B' x).2, by
          rw [SpecialLinear.mem_sl_iff, matrixPairLieHom_apply, ← LinearMap.trace_eq_matrix_trace,
            P.trace_typeDSpinMinusLieRep_of_card_eq_two b hline hι]⟩)
      map_add' x y := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
      map_smul' c x := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
      map_lie' {x y} := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp)) }
    ⟨fun x y h ↦ P.typeDSpinPlusLieRep_prod_typeDSpinMinusLieRep_injective_of_card_eq_two
        b hline hι <| by
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

end TauCeti.SpinPolarizationData
