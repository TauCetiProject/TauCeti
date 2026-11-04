/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.MaximalTorus
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Tangent
import TauCeti.LinearAlgebra.Matrix.MonoidAlgebra

/-!
# The schematic centralizer of the short-root G₂ torus

The rank-two weight torus is its own scheme-theoretic centralizer in the short-root G₂
carrier over 𝔽₃. This includes infinitesimal structure: the calculation uses the universal
point over the torus coordinate algebra, not just points over infinite fields.
Consequently the trivial adjoint weight space is exactly the tangent space cut out by
the weight-torus ideal.

Distinct weights of the seven-dimensional module force a centralizing matrix to be diagonal.
The existing cross-product calculation then identifies it with a weight-torus point over
every value algebra. No identification with an independently pinned simply connected group
scheme is asserted.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* SGA 3, Exposé XI, on centralizers of diagonalizable subgroups.

The universal-point proof follows
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Centralizer` and uses the
cross-product calculation in
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.TorusCentralizer`.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti.G2ShortRoot.PrimeField

noncomputable section

private theorem isDiag_of_centralizerHopfIdeal_le_ker
    {A : Type*} [CommRing A] [Algebra (ZMod 3) A]
    (g : HopfAlgebra.points (R := ZMod 3) (H := carrierAlgebra) (CommAlgCat.of (ZMod 3) A))
    (hg : (BialgHom.centralizerHopfIdeal weightTorusCoordinateMap.hom).toIdeal ≤
      RingHom.ker g.ofConv) :
    ((pointsMulEquiv (CommAlgCat.of (ZMod 3) A) g : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A).IsDiag := by
  -- Base extension to the torus coordinate algebra supplies its universal point.
  let X := Multiplicative (Fin 2 →₀ ℤ)
  let B := A ⊗[ZMod 3] MonoidAlgebra (ZMod 3) X
  let χ : Fin 7 → X := fun i ↦ SplitTorus.weightCharacter (weight i)
  let u : WithConv (MonoidAlgebra (ZMod 3) X →ₐ[ZMod 3] B) :=
    toConv Algebra.TensorProduct.includeRight
  have hcomm := (BialgHom.centralizerHopfIdeal_le_ker_iff_commute_of_injective
    weightTorusCoordinateMap.hom g (AlgHom.id (ZMod 3) B) Function.injective_id).mp hg
  rw [AlgHom.id_comp, AlgHom.id_comp] at hcomm
  -- The torus's diagonal entries are distinct monomials, even over a finite value ring.
  have hD : ((pointsMulEquiv (CommAlgCat.of (ZMod 3) B)
        (BialgHom.mapDomain weightTorusCoordinateMap.hom u) :
        Matrix.GeneralLinearGroup (Fin 7) B) : Matrix (Fin 7) (Fin 7) B) =
      Matrix.diagonal fun i ↦ (1 : A) ⊗ₜ[ZMod 3]
        MonoidAlgebra.single (χ i) (1 : ZMod 3) := by
    rw [coe_pointsMulEquiv_eq_map_carrierGenericMatrix, BialgHom.mapDomain_apply,
      ofConv_toConv, AlgHom.coe_comp, ← Matrix.map_map,
      carrierGenericMatrix_map_weightTorusCoordinateMap, Matrix.diagonal_map (map_zero u.ofConv)]
    apply congrArg Matrix.diagonal
    funext i
    exact Algebra.TensorProduct.includeRight_apply _
  have hM : ((pointsMulEquiv (CommAlgCat.of (ZMod 3) B)
        (AlgHom.mapValue (Algebra.TensorProduct.includeLeft : A →ₐ[ZMod 3] B) g) :
        Matrix.GeneralLinearGroup (Fin 7) B) : Matrix (Fin 7) (Fin 7) B) =
      (((pointsMulEquiv (CommAlgCat.of (ZMod 3) A) g :
        Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A).map
        (Algebra.TensorProduct.includeLeft : A →ₐ[ZMod 3] B)) := by
    rw [coe_pointsMulEquiv_eq_map_carrierGenericMatrix,
      coe_pointsMulEquiv_eq_map_carrierGenericMatrix, Matrix.map_map]
    ext i j
    simp only [Matrix.map_apply, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      Function.comp_apply]
  -- Transport commutation to matrices and compare coefficients of distinct characters.
  have hm := congrArg (fun q ↦ ((pointsMulEquiv (CommAlgCat.of (ZMod 3) B) q :
    Matrix.GeneralLinearGroup (Fin 7) B) : Matrix (Fin 7) (Fin 7) B)) hcomm.eq
  simp only [map_mul, Subgroup.coe_mul, Units.val_mul] at hm
  rw [hM, hD] at hm
  intro i j hij
  exact Matrix.apply_eq_zero_of_commute_diagonal_monomial (R := ZMod 3) _ χ hm
    (weightCharacter_injective.ne (Ne.symm hij))

/-- The scheme-theoretic centralizer of the weight torus is the weight torus itself.
This is equality of Hopf ideals, not merely equality of geometric point groups. -/
-- Match the named coordinate map before simplification normalizes its bundled presentation.
@[simp↓]
theorem centralizerHopfIdeal_weightTorusCoordinateMap :
    BialgHom.centralizerHopfIdeal weightTorusCoordinateMap.hom = weightTorusDefiningIdeal := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [← HopfIdeal.mem_toIdeal, weightTorusDefiningIdeal_toIdeal]
    exact (HopfIdeal.mem_kerOfSurjective _ _).mp
      (BialgHom.centralizerHopfIdeal_le_kerOfSurjective _
        weightTorusCoordinateMap_surjective hx)
  rw [HopfIdeal.le_iff_forall_quotientPointsSubgroup_le]
  intro A
  obtain ⟨A⟩ := A
  let C := CommAlgCat.of (ZMod 3) A
  intro g hg
  have hker : (BialgHom.centralizerHopfIdeal weightTorusCoordinateMap.hom).toIdeal ≤
      RingHom.ker g.ofConv := by
    intro x hx
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ C g).mp hg x hx
  have hdiag := isDiag_of_centralizerHopfIdeal_le_ker g hker
  have hmem : pointsMulEquiv C g ∈ (weightTorusPoints A).range := by
    rw [MonoidHom.mem_range, exists_weightTorusPoints_eq_iff_isDiag]
    exact hdiag
  rw [← map_quotientPointsSubgroup_weightTorusDefiningIdeal A,
    Subgroup.mem_map_equiv] at hmem
  dsimp only [C] at hmem
  simpa only [MulEquiv.symm_apply_apply] using hmem

/-- A tangent vector has trivial adjoint character exactly when it lies in the tangent Lie
algebra of the weight torus. In particular there are no additional infinitesimal centralizer
directions. -/
theorem cotangentLinearEquiv_mem_lieSubalgebra_weightTorusDefiningIdeal_iff
    (x : Module.Dual (ZMod 3) (Bialgebra.CotangentSpace (ZMod 3) carrierAlgebra)) :
    Derivation.cotangentLinearEquiv (B := ZMod 3) x ∈ weightTorusDefiningIdeal.lieSubalgebra ↔
      x ∈ Derivation.adjointWeightSpace weightTorusCoordinateMap.hom 1 := by
  rw [← centralizerHopfIdeal_weightTorusCoordinateMap]
  exact BialgHom.cotangentLinearEquiv_mem_lieSubalgebra_centralizerHopfIdeal_iff _ x

end

end TauCeti.G2ShortRoot.PrimeField
