/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Exponential
public import TauCeti.Algebra.Lie.F4.ShortRoot.TorusAction
public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Basic

/-!
# The bracket tensor of the modular F₄ short-root ideal

The characteristic-two short-root ideal is a twenty-six-dimensional Lie algebra. Its bracket
has constant structure matrices in the distinguished weight basis. The numbered root
exponentials preserve this tensor over every commutative coefficient algebra. These polynomial
identities let the generated short-root group act by automorphisms of the bracket, and constrain
its tangent matrices to be derivations.

The root calculation uses `f4ShortRootExponential_toMatrix_mul_adjoint` and
`f4RootExponential_intertwines`. The bracket coefficients also respect the integral weight
support of `f4ShortRootAdjointMatrix`; no reduction of the character lattice modulo two is involved.

`Matrix.isDiag_of_preserves_f4ShortRootBracket_of_weight_support` shows that bracket preservation
refines the weight-block condition to diagonality over any commutative `𝔽₂`-algebra.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §12.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open scoped TensorProduct
open TauCeti.F4ShortRoot

noncomputable section

/-- The matrix of bracketing on the left with the `a`th distinguished short-root ideal vector. -/
def f4ShortRootBracketMatrix (a : Fin 26) : Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  f4ShortRootAdjointMatrix (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra)

/-- The bracket structure matrices are the restricted adjoint matrices at the ideal basis. -/
theorem f4ShortRootBracketMatrix_def (a : Fin 26) :
    f4ShortRootBracketMatrix a =
      f4ShortRootAdjointMatrix (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra) :=
  (rfl)

/-- An entry of the bracket tensor is the corresponding coefficient in the ambient
Chevalley basis. -/
@[simp] theorem f4ShortRootBracketMatrix_apply (a i j : Fin 26) :
    f4ShortRootBracketMatrix a i j =
      f4ModularChevalleyBasis.repr
        (⁅(f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra),
          (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra)⁆ :
          f4ModularChevalleyLieAlgebra)
        (f4ShortRootBasisCoordinate i) := by
  exact (congrFun (congrFun (f4ShortRootBracketMatrix_def a) i) j).trans
    (f4ShortRootAdjointMatrix_apply _ i j)

private theorem bracketMatrix_col_eq_single_of_opposite_simple
    (k : Fin 4) (a b c : Fin 26)
    (hlen : f4Length (Fin.castAdd 44 k) = 1)
    (ha : f4ShortRootWeight a = f4Root (Fin.castAdd 44 k))
    (hb : f4ShortRootWeight b = f4Root (f4OppositeRootIndex (Fin.castAdd 44 k)))
    (hc : (f4ShortRootLieIdealBasis c : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm k)) :
    (f4ShortRootBracketMatrix a).col b = Pi.single c 1 := by
  classical
  have hpos := coe_f4ShortRootLieIdealBasis_of_weight_eq_root a (Fin.castAdd 44 k) hlen ha
  have hneg := coe_f4ShortRootLieIdealBasis_of_weight_eq_root b
    (f4OppositeRootIndex (Fin.castAdd 44 k)) (by
      simpa only [f4Length_opposite] using hlen) hb
  have hbr : ⁅(f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra),
      (f4ShortRootLieIdealBasis b : f4ModularChevalleyLieAlgebra)⁆ =
        (f4ShortRootLieIdealBasis c : f4ModularChevalleyLieAlgebra) := by
    simp only [hpos, hneg, hc]
    exact (f4Modular_lie_rootVector_opposite (Fin.castAdd 44 k)).trans
      (f4ModularCoroot_castAdd k)
  ext i
  simp only [Matrix.col_apply, f4ShortRootBracketMatrix_apply, hbr]
  simp only [coe_f4ShortRootLieIdealBasis, Module.Basis.repr_self, Finsupp.single_apply,
    Pi.single_apply, f4ShortRootBasisCoordinate_injective.eq_iff, eq_comm]

/-- The bracket of the short simple-root vectors at coordinates `11` and `14` is the
simple coroot at coordinate `12`. This records the unit normalization of that bracket. -/
theorem f4ShortRootBracketMatrix_col_fourteen_eleven :
    (f4ShortRootBracketMatrix 11).col 14 = Pi.single 12 1 := by
  apply bracketMatrix_col_eq_single_of_opposite_simple 2
  · rw [f4Length_def]; decide +kernel
  · decide +kernel
  · rw [f4OppositeRootIndex_castAdd]; decide +kernel
  · rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis, coe_f4ShortRootBasis_twelve]

/-- The bracket of the short simple-root vectors at coordinates `10` and `15` is the
simple coroot at coordinate `13`. This records the second zero-weight basis vector as a bracket. -/
theorem f4ShortRootBracketMatrix_col_fifteen_ten :
    (f4ShortRootBracketMatrix 10).col 15 = Pi.single 13 1 := by
  apply bracketMatrix_col_eq_single_of_opposite_simple 3
  · rw [f4Length_def]; decide +kernel
  · decide +kernel
  · rw [f4OppositeRootIndex_castAdd]; decide +kernel
  · rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis, coe_f4ShortRootBasis_thirteen]

attribute [local instance high] Algebra.toModule

/-- A nonzero bracket coefficient adds the integral weights of its inputs. -/
theorem f4ShortRootBracketMatrix_weight_support (a i j : Fin 26)
    (hne : f4ShortRootBracketMatrix a i j ≠ 0) :
    f4ShortRootWeight i = f4ShortRootWeight j + f4ShortRootWeight a := by
  obtain ⟨b, rfl⟩ := f4ShortRootWeightIndexEquiv.symm.surjective a
  rcases b with α | k
  · rw [f4ShortRootBracketMatrix_def,
      coe_f4ShortRootLieIdealBasis_symm_inl α] at hne
    simpa only [f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl] using
      f4ShortRootAdjointMatrix_root_weight_support α i j hne
  · rw [f4ShortRootBracketMatrix_def,
      coe_f4ShortRootLieIdealBasis_symm_inr k] at hne
    simpa only [f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inr, add_zero] using
      f4ShortRootAdjointMatrix_simpleCoroot_weight_support (f4ShortSimpleIndex k) i j hne

variable {A : Type*} [CommRing A] [Algebra (ZMod 2) A]

/-- The matrix of bracketing with a scalar-extended ideal vector, via the ambient inclusion. -/
private def idealAdjointMatrix :
    A ⊗[ZMod 2] f4ShortRootLieIdeal →ₗ[A] Matrix (Fin 26) (Fin 26) A :=
  (LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
    (f4ShortRootLieIdealBasis.baseChange A)).toLinearMap.comp
      (f4ShortRootBaseChangeAdjoint.comp f4ShortRootBaseChangeInclusion)

private theorem idealAdjointMatrix_apply (x : A ⊗[ZMod 2] f4ShortRootLieIdeal) :
    idealAdjointMatrix x =
      LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootBaseChangeAdjoint (f4ShortRootBaseChangeInclusion x)) :=
  (rfl)

private theorem idealAdjointMatrix_basis (a : Fin 26) :
    idealAdjointMatrix ((f4ShortRootLieIdealBasis.baseChange A) a) =
      (f4ShortRootBracketMatrix a).map (algebraMap (ZMod 2) A) := by
  calc
    _ = idealAdjointMatrix ((1 : A) ⊗ₜ[ZMod 2] f4ShortRootLieIdealBasis a) :=
      congrArg idealAdjointMatrix
        (Module.Basis.baseChange_apply A f4ShortRootLieIdealBasis a)
    _ = _ := (idealAdjointMatrix_apply _).trans <|
      (congrArg (fun z => LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
        (f4ShortRootLieIdealBasis.baseChange A) (f4ShortRootBaseChangeAdjoint z))
        (f4ShortRootBaseChangeInclusion_tmul (1 : A) (f4ShortRootLieIdealBasis a))).trans
        (f4ShortRootBaseChangeAdjoint_toMatrix_cancel_tmul
          (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra))

private theorem imageStructureMatrix_eq_idealAdjointMatrix
    (f : Module.End A (A ⊗[ZMod 2] f4ShortRootLieIdeal)) (a : Fin 26) :
    ConstantMultiplication.imageStructureMatrix (ZMod 2) 26 f4ShortRootBracketMatrix
        (LinearMap.toMatrix (f4ShortRootLieIdealBasis.baseChange A)
          (f4ShortRootLieIdealBasis.baseChange A) f) a =
      idealAdjointMatrix (f ((f4ShortRootLieIdealBasis.baseChange A) a)) := by
  let b := f4ShortRootLieIdealBasis.baseChange A
  calc
    _ = ∑ i, b.repr (f (b a)) i • idealAdjointMatrix (b i) := by
      simp only [b, ConstantMultiplication.imageStructureMatrix_def,
        LinearMap.toMatrix_apply, idealAdjointMatrix_basis]
    _ = idealAdjointMatrix (∑ i, b.repr (f (b a)) i • b i) := by
      simp only [map_sum, map_smul]
    _ = _ := congrArg idealAdjointMatrix (b.sum_repr (f (b a)))

/-- Every numbered root exponential preserves the short-root ideal's bracket tensor after
arbitrary extension of scalars from `𝔽₂`. -/
theorem preservesBracket_rootSubgroupPoints
    (k : Fin 4 ⊕ Fin 4) (u : Multiplicative A) :
    ConstantMultiplication.Preserves (ZMod 2) 26 f4ShortRootBracketMatrix
      ((rootSubgroupPoints k A u : Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) := by
  rw [← f4ShortRootExponential_toMatrix_eq_rootSubgroupPoints k u,
    ConstantMultiplication.preserves_def]
  intro a
  let b := f4ShortRootLieIdealBasis.baseChange A
  let e := f4ShortRootExponential k (Multiplicative.toAdd u)
  let M := LinearMap.toMatrix b b e
  calc
    _ = M * idealAdjointMatrix (b a) :=
      congrArg (M * ·) (idealAdjointMatrix_basis a).symm
    _ = idealAdjointMatrix (e (b a)) * M := by
      simpa only [idealAdjointMatrix_apply, f4RootExponential_intertwines] using
        f4ShortRootExponential_toMatrix_mul_adjoint k (Multiplicative.toAdd u)
          (f4ShortRootBaseChangeInclusion (b a))
    _ = _ := congrArg (· * M) (imageStructureMatrix_eq_idealAdjointMatrix e a).symm

end

end TauCeti.DynkinType

namespace Matrix

open TauCeti TauCeti.DynkinType

universe u

/-- A bracket-preserving matrix with no entries between distinct short-root weights is
diagonal. The two zero-weight basis vectors are brackets of opposite simple-root vectors,
so their lines are preserved individually, without a reducedness or invertibility assumption. -/
theorem isDiag_of_preserves_f4ShortRootBracket_of_weight_support
    {A : Type u} [CommRing A] [Algebra (ZMod 2) A]
    (M : Matrix (Fin 26) (Fin 26) A)
    (hM : ConstantMultiplication.Preserves (ZMod 2) 26 f4ShortRootBracketMatrix M)
    (hweight : ∀ i j, f4ShortRootWeight i ≠ f4ShortRootWeight j → M i j = 0) :
    M.IsDiag := by
  have hcol (a : Fin 26) (ha : f4ShortRootWeight a ≠ 0) :
      M.col a = M a a • Pi.single a 1 := by
    ext i
    by_cases hi : i = a
    · subst i
      simp
    · have hne : f4ShortRootWeight i ≠ f4ShortRootWeight a := by
        intro h
        exact hi (f4ShortRootWeight_injOn (fun hi0 ↦ ha (h.symm.trans hi0)) ha h)
      simp only [col_apply, Pi.smul_apply, Pi.single_apply, hi, ite_false, smul_eq_mul, mul_zero]
      exact hweight i a hne
  have h12 : M.col 12 = (M 11 11 * M 14 14) • Pi.single 12 1 :=
    ConstantMultiplication.Preserves.col_eq_smul_single (ZMod 2) 26 f4ShortRootBracketMatrix
      hM (hcol 11 (by decide)) (hcol 14 (by decide))
      f4ShortRootBracketMatrix_col_fourteen_eleven
  have h13 : M.col 13 = (M 10 10 * M 15 15) • Pi.single 13 1 :=
    ConstantMultiplication.Preserves.col_eq_smul_single (ZMod 2) 26 f4ShortRootBracketMatrix
      hM (hcol 10 (by decide)) (hcol 15 (by decide))
      f4ShortRootBracketMatrix_col_fifteen_ten
  intro i j hij
  obtain ⟨s, hs⟩ : ∃ s : A, M.col j = s • Pi.single j 1 := by
    by_cases hj : f4ShortRootWeight j = 0
    · rcases (f4ShortRootWeight_eq_zero_iff j).mp hj with rfl | rfl
      · exact ⟨_, h12⟩
      · exact ⟨_, h13⟩
    · exact ⟨_, hcol j hj⟩
  simpa only [col_apply, Pi.smul_apply, Pi.single_apply, hij, ite_false, smul_eq_mul,
    mul_zero] using congrFun hs i

end Matrix
