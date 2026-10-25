/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Bracket
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Generated.Preserves
import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Generation

/-!
# Bracket invariance for the short-root F₄ carrier over 𝔽₂

The short-root carrier preserves the bracket tensor of the modular short-root ideal, as a
group scheme. The assertion holds over every commutative `𝔽₂`-algebra, including nonreduced
ones. Differentiating it shows that every carrier tangent matrix is a derivation of that
bracket. Together with the integral torus-weight support, this gives equations for computing
the carrier's root spaces; no upper bound on their dimensions is asserted here.

The proof passes the generator identities in `Modular.Bracket` through the common-kernel
construction, following the tensor-invariance argument for the short-root G₂ carrier in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PreservesTensors`. The differentiation argument
follows `TauCeti.G2ShortRoot.PrimeField.tangentMatrix_mul_crossOperatorPrime` in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Root.Space`, via
`GeneralLinear.tangentMatrix_mul_of_constantMultiplicationDefiningHopfIdeal_le`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

noncomputable section

private theorem preservesBracket_map_genericMatrix_generator_inl (k : Fin 4 ⊕ Fin 4) :
    ConstantMultiplication.Preserves (ZMod 2) 26 f4ShortRootBracketMatrix
      ((GeneralLinear.genericMatrix (ZMod 2) 26).map (generator (.inl k)).hom.toAlgHom) := by
  rw [map_genericMatrix_generator_inl, coe_rootSubgroupPoints]
  exact preservesBracket_rootSubgroupPoints k _

/-- The short-root carrier is a closed subgroup scheme of the stabilizer of the bracket
tensor of the modular short-root ideal. -/
theorem bracketDefiningHopfIdeal_le_definingIdeal :
    ConstantMultiplication.definingHopfIdeal (ZMod 2) 26 f4ShortRootBracketMatrix ≤
      definingIdeal := by
  rw [definingIdeal_eq_commonKernelHopfIdeal_generator_inl]
  exact GeneralLinear.constantMultiplicationDefiningHopfIdeal_le_commonKernelHopfIdeal
    26 (fun k ↦ generator (.inl k)) f4ShortRootBracketMatrix
      preservesBracket_map_genericMatrix_generator_inl

/-- Every matrix-valued point of the short-root carrier preserves the modular short-root
bracket, over arbitrary commutative coefficient algebras. -/
theorem preservesBracket_of_mem_points {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    {g : Matrix.GeneralLinearGroup (Fin 26) A} (hg : g ∈ points A) :
    ConstantMultiplication.Preserves (ZMod 2) 26 f4ShortRootBracketMatrix
      (g : Matrix (Fin 26) (Fin 26) A) :=
  GeneralLinear.preserves_of_mem_generatedPointsSubgroup 26 (fun k ↦ generator (.inl k))
    f4ShortRootBracketMatrix preservesBracket_map_genericMatrix_generator_inl A
    (points_eq_generatedPointsSubgroup_generator_inl A ▸ hg)

/-- Every tangent matrix of the short-root carrier is a derivation of the modular short-root
bracket: `X [eₐ, -] = [X eₐ, -] + [eₐ, -] X` in structure-matrix coordinates. -/
theorem tangentMatrix_mul_f4ShortRootBracketMatrix
    (x : Module.Dual (ZMod 2) (Bialgebra.CotangentSpace (ZMod 2)
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
        (CommHopfAlgCat.commonKernelHopfIdeal generator)))) (a : Fin 26) :
    tangentMatrix x * f4ShortRootBracketMatrix a =
      ConstantMultiplication.imageStructureMatrix (ZMod 2) 26 f4ShortRootBracketMatrix
          (tangentMatrix x) a +
        f4ShortRootBracketMatrix a * tangentMatrix x := by
  simpa only [← tangentMatrix_apply, Algebra.algebraMap_self, RingHom.coe_id,
    Matrix.map_id] using
    GeneralLinear.tangentMatrix_mul_of_constantMultiplicationDefiningHopfIdeal_le
      26 generator f4ShortRootBracketMatrix
      (definingIdeal_def ▸ bracketDefiningHopfIdeal_le_definingIdeal)
      (Derivation.cotangentLinearEquiv (B := ZMod 2) x) a

end

end TauCeti.F4ShortRoot.PrimeField
