/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Bracket
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Root.Differential
public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Tangent
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Generated.Preserves

/-!
# Bracket invariance for the short-root F₄ carrier over 𝔽₂

The short-root carrier preserves the bracket tensor of the modular short-root ideal, as a
group scheme. The assertion holds over every commutative `𝔽₂`-algebra, including nonreduced
ones. Differentiating it shows that every carrier tangent matrix is a derivation of that
bracket. Together with the integral torus-weight support, this gives equations for computing
the carrier's root spaces; no upper bound on their dimensions is asserted here.

The proof passes the generator identities in `Modular.Bracket` through the common-kernel
construction, following the tensor-invariance argument for the short-root G₂ carrier in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PreservesTensors`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

noncomputable section

private theorem exists_map_genericMatrix_generator_inr :
    ∃ s : Fin 4 → (generatorCodomain (.inr ()))ˣ,
      (GeneralLinear.genericMatrix (ZMod 2) 26).map (generator (.inr ())).hom.toAlgHom =
        ((weightTorusPoints (generatorCodomain (.inr ())) s :
          Matrix.GeneralLinearGroup (Fin 26) (generatorCodomain (.inr ()))) :
          Matrix (Fin 26) (Fin 26) (generatorCodomain (.inr ()))) := by
  let A := CommAlgCat.of (ZMod 2) (generatorCodomain (.inr ()))
  let q : HopfAlgebra.points (R := ZMod 2) (H := generatorCodomain (.inr ())) A :=
    toConv (AlgHom.id (ZMod 2) (generatorCodomain (.inr ())))
  have hid : (CommHopfAlgCat.Hom.mapPointsFunctor (generator (.inr ()))).app A q =
      toConv (generator (.inr ())).hom.toAlgHom := by
    rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
    simp only [q, AlgHom.id_comp]
    -- The categorical point wrapper retains the same underlying algebra map.
    rfl
  refine ⟨SplitTorus.pointsMulEquiv q, ?_⟩
  rw [coe_weightTorusPoints_pointsMulEquiv, hid,
    GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear,
    GeneralLinear.pointsMulEquiv_apply]

private theorem preservesBracket_map_genericMatrix_generator
    (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) :
    ConstantMultiplication.Preserves (ZMod 2) 26 f4ShortRootBracketMatrix
      ((GeneralLinear.genericMatrix (ZMod 2) 26).map (generator j).hom.toAlgHom) := by
  rcases j with k | ⟨⟩
  · rw [map_genericMatrix_generator_inl, coe_rootSubgroupPoints]
    exact f4ShortRootBracketMatrix_preserves_rootSubgroupPoints k _
  · obtain ⟨s, hs⟩ := exists_map_genericMatrix_generator_inr
    rw [hs, coe_weightTorusPoints, F4ShortRoot.coe_weightTorusPoints,
      UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
    exact f4ShortRootBracketMatrix_preserves_diagonal_torusCharacter s

/-- The short-root carrier is a closed subgroup scheme of the stabilizer of the bracket
tensor of the modular short-root ideal. -/
theorem bracketDefiningHopfIdeal_le_definingIdeal :
    ConstantMultiplication.definingHopfIdeal (ZMod 2) 26 f4ShortRootBracketMatrix ≤
      definingIdeal := by
  rw [definingIdeal_def]
  exact GeneralLinear.constantMultiplicationDefiningHopfIdeal_le_commonKernelHopfIdeal
    26 generator f4ShortRootBracketMatrix preservesBracket_map_genericMatrix_generator

/-- Every matrix-valued point of the short-root carrier preserves the modular short-root
bracket, over arbitrary commutative coefficient algebras. -/
theorem preservesBracket_of_mem_points {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    {g : Matrix.GeneralLinearGroup (Fin 26) A} (hg : g ∈ points A) :
    ConstantMultiplication.Preserves (ZMod 2) 26 f4ShortRootBracketMatrix
      (g : Matrix (Fin 26) (Fin 26) A) :=
  GeneralLinear.preserves_of_mem_generatedPointsSubgroup 26 generator
    f4ShortRootBracketMatrix preservesBracket_map_genericMatrix_generator A (points_def A ▸ hg)

/-- Every tangent matrix of the short-root carrier is a derivation of the modular short-root
bracket: `X [eₐ, -] = [X eₐ, -] + [eₐ, -] X` in structure-matrix coordinates. -/
theorem tangentMatrix_mul_bracketMatrix
    (x : Module.Dual (ZMod 2) (Bialgebra.CotangentSpace (ZMod 2)
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
        (CommHopfAlgCat.commonKernelHopfIdeal generator)))) (a : Fin 26) :
    tangentMatrix x * f4ShortRootBracketMatrix a =
      ConstantMultiplication.imageStructureMatrix (ZMod 2) 26 f4ShortRootBracketMatrix
          (tangentMatrix x) a +
        f4ShortRootBracketMatrix a * tangentMatrix x := by
  have hmem : HopfIdeal.quotientLieHom (CommHopfAlgCat.commonKernelHopfIdeal generator)
      (Derivation.cotangentLinearEquiv (B := ZMod 2) x) ∈
      HopfIdeal.lieSubalgebra (B := ZMod 2)
        (ConstantMultiplication.definingHopfIdeal (ZMod 2) 26 f4ShortRootBracketMatrix) := by
    rw [HopfIdeal.mem_lieSubalgebra_iff]
    intro y hy
    have hcarrier := (HopfIdeal.mem_lieSubalgebra_iff _ _).mp
      (HopfIdeal.quotientLieEquiv (B := ZMod 2) (CommHopfAlgCat.commonKernelHopfIdeal generator)
        (Derivation.cotangentLinearEquiv (B := ZMod 2) x)).2
    rw [HopfIdeal.quotientLieEquiv_apply_coe] at hcarrier
    exact hcarrier y (HopfIdeal.toIdeal_le_toIdeal.mpr
      (definingIdeal_def ▸ bracketDefiningHopfIdeal_le_definingIdeal) hy)
  have h := (ConstantMultiplication.mem_lieSubalgebra_definingHopfIdeal_iff
    f4ShortRootBracketMatrix _).mp hmem a
  simpa only [← tangentMatrix_apply, Algebra.algebraMap_self, RingHom.coe_id,
    Matrix.map_id] using h

end

end TauCeti.F4ShortRoot.PrimeField
