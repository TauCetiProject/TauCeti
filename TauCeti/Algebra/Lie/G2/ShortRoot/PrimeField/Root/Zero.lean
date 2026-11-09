/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space
public import TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Diagonal
import TauCeti.Algebra.Lie.Matrix.IntegralCast
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The zero adjoint-weight space of the short-root G₂ carrier

For the short-root carrier over `𝔽₃`, the zero adjoint-weight space has dimension two.
Under the faithful tangent-matrix map it is exactly the span of the two diagonal Cartan
matrices of the seven-dimensional module. The statement uses integral torus characters,
not the eigenvalues of the Cartan matrices reduced modulo three.

Distinct module weights force a zero-weight tangent matrix to be diagonal. Differentiated
cross-product invariance then forces its seven diagonal entries to be linear combinations
of the two weight coordinates. Conversely, the brackets of opposite numbered root vectors
supply both Cartan matrices inside the actual carrier tangent space. Thus the calculation
rules out extra zero-weight tangent directions without presupposing a root-datum comparison.
No identification with an independently constructed pinned group scheme is asserted.

## Main results

* `TauCeti.G2ShortRoot.PrimeField.mem_adjointWeightSpace_one_iff_isDiag`: the zero-weight
  condition is diagonality of the tangent matrix.
* `TauCeti.G2ShortRoot.PrimeField.map_tangentMatrix_adjointWeightSpace_one_eq_span`: its matrix
  image is precisely the span of the two Cartan matrices.
* `TauCeti.G2ShortRoot.PrimeField.finrank_adjointWeightSpace_one`: its dimension is two.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a and §21.1.
* S. Garibaldi and R. M. Guralnick, *Simple groups stabilizing polynomials*, Forum of
  Mathematics Pi **3** (2015), §6.

The tangent-matrix and cross-product method is that of
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space`; the diagonal calculation uses
`TauCeti.Algebra.Lie.G2.ShortRoot.CrossProduct.Diagonal`.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A carrier tangent vector has trivial adjoint torus character exactly when its matrix
in the seven-weight basis is diagonal. -/
theorem mem_adjointWeightSpace_one_iff_isDiag
    (x : Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra)) :
    x ∈ Derivation.adjointWeightSpace weightTorusCoordinateMap.hom 1 ↔
      (tangentMatrix x).IsDiag := by
  rw [mem_adjointWeightSpace_iff]
  constructor
  · intro h i j hij
    apply h
    intro heq
    have hw : weight i = weight j := by
      funext l
      have hl := congrArg (fun χ : Multiplicative (Fin 2 →₀ ℤ) =>
        Multiplicative.toAdd χ l) heq
      simpa only [SplitTorus.toAdd_weightCharacter, toAdd_one,
        Finsupp.zero_apply, Pi.sub_apply, sub_eq_zero] using hl
    exact hij (weight_injective hw)
  · intro h i j hne
    by_cases hij : i = j
    · subst j
      exact (hne (SplitTorus.weightCharacter_eq_one_iff.mpr (by simp))).elim
    · exact h hij

private theorem tangentMatrix_eq_sum_cartanMatrix_of_isDiag
    (x : Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra))
    (hx : (tangentMatrix x).IsDiag) :
    ∃ c : Fin 2 → ZMod 3,
      tangentMatrix x = ∑ i, c i • (cartanMatrix i).map (Int.cast : ℤ → ZMod 3) := by
  let d : Fin 7 → ZMod 3 := fun i => tangentMatrix x i i
  have hd : tangentMatrix x = Matrix.diagonal d := hx.diagonal_diag.symm
  have hentry : ∀ k i j, d i * (crossOperator k i j : ZMod 3) =
      d k * (crossOperator k i j : ZMod 3) + (crossOperator k i j : ZMod 3) * d j := by
    intro k i j
    have he := congrFun (congrFun (tangentMatrix_mul_crossOperatorPrime x k) i) j
    rw [hd] at he
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal,
      ConstantMultiplication.imageStructureMatrix_def, Matrix.diagonal_apply] using he
  obtain ⟨c, hc⟩ := (diagonal_derivation_iff (isUnit_iff_ne_zero.mpr (by decide)).isRegular d).mp
    hentry
  refine ⟨c, ?_⟩
  rw [hd]
  ext a b
  by_cases hab : a = b
  · subst b
    simpa [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      cartanMatrix_apply, mul_comm] using hc a
  · simp [Matrix.sum_apply, Matrix.smul_apply, cartanMatrix_apply, hab]

private theorem cartanMatrix_mem_map_tangentMatrix_adjointWeightSpace_one (i : Fin 2) :
    (cartanMatrix i).map (Int.cast : ℤ → ZMod 3) ∈
      (Derivation.adjointWeightSpace weightTorusCoordinateMap.hom 1).map tangentMatrix := by
  let e := Derivation.cotangentLinearEquiv (R := ZMod 3) (A := carrierAlgebra) (B := ZMod 3)
  let h := e.symm ⁅e (rootVector (.inl i)), e (rootVector (.inr i))⁆
  have hm : tangentMatrix h = (cartanMatrix i).map (Int.cast : ℤ → ZMod 3) := by
    dsimp only [h, e]
    rw [tangentMatrix_symm_lie, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, tangentMatrix_rootVector, tangentMatrix_rootVector,
      rootMatrix_inl, rootMatrix_inr]
    simpa only [matrixIntCastLieHom_eq_map] using
      ((matrixIntCastLieHom (ZMod 3)).map_lie _ _).symm.trans
        (congrArg (matrixIntCastLieHom (ZMod 3)) (isSerreSystem.lie_E_F_self i))
  refine ⟨h, (mem_adjointWeightSpace_one_iff_isDiag h).mpr ?_, hm⟩
  rw [hm]
  intro a b hab
  simp [cartanMatrix_apply, hab]

/-- Under the faithful tangent-matrix map, the trivial adjoint-weight space is exactly
spanned by the two numbered Cartan matrices. -/
theorem map_tangentMatrix_adjointWeightSpace_one_eq_span :
    (Derivation.adjointWeightSpace weightTorusCoordinateMap.hom 1).map tangentMatrix =
      Submodule.span (ZMod 3)
        (Set.range fun i : Fin 2 => (cartanMatrix i).map (Int.cast : ℤ → ZMod 3)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := tangentMatrix_eq_sum_cartanMatrix_of_isDiag x
      ((mem_adjointWeightSpace_one_iff_isDiag x).mp hx)
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact cartanMatrix_mem_map_tangentMatrix_adjointWeightSpace_one i

/-- The zero adjoint-weight space of the short-root G₂ carrier over `𝔽₃` has dimension two. -/
-- Match before simplification changes the bundled carrier presentation.
@[simp↓]
theorem finrank_adjointWeightSpace_one :
    Module.finrank (ZMod 3) (Derivation.adjointWeightSpace weightTorusCoordinateMap.hom 1) = 2 := by
  have hli : LinearIndependent (ZMod 3)
      (fun i : Fin 2 => (cartanMatrix i).map (Int.cast : ℤ → ZMod 3)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 := congrFun (congrFun hc 0) 0
    have h1 := congrFun (congrFun hc 1) 1
    have hz : c 0 = 0 := by
      simpa [Fin.sum_univ_two, cartanMatrix_apply, weight_apply] using h0
    fin_cases i
    · simpa using hz
    · simpa [Fin.sum_univ_two, cartanMatrix_apply, weight_apply, hz] using h1
  rw [(Submodule.equivMapOfInjective tangentMatrix tangentMatrix_injective
    (Derivation.adjointWeightSpace weightTorusCoordinateMap.hom 1)).finrank_eq,
    map_tangentMatrix_adjointWeightSpace_one_eq_span, finrank_span_eq_card hli]
  rfl

end

end TauCeti.G2ShortRoot.PrimeField
