/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.IntegralModel.Reductive

/-!
# The standard integral model of `GL_n`

For a commutative ring `O` with an algebra map to a commutative ring `K`, the general linear
group scheme `GL_{n,O}` is a smooth affine `O`-model of `GL_{n,K}`
(`TauCeti.IntegralModel.SmoothModel.generalLinear`), and its integral points are `GL_n(O)`: a
`K`-point of `K ⊗[O] O[GL_n]` is integral exactly when its matrix is the image of an invertible
matrix over `O`, that is, when the matrix and its inverse have entries in `O`
(`TauCeti.IntegralModel.mem_integralPoints_generalLinear_iff`). When `O` is local and `K` is a
field it is a reductive model, so its integral points satisfy
`TauCeti.IntegralModel.IsHyperspecialSubgroup`.

## Main declarations

* `TauCeti.IntegralModel.SmoothModel.generalLinear`: the standard model of `GL_n`.
* `TauCeti.IntegralModel.mem_integralPoints_generalLinear_iff`: its integral points are
  `GL_n(O)`.
* `TauCeti.IntegralModel.SmoothModel.isReductive_generalLinear`: it is reductive over a local
  ring with a field `K`.
* `TauCeti.IntegralModel.SmoothModel.isHyperspecialSubgroup_generalLinear`: its integral points
  satisfy `IsHyperspecialSubgroup`.
-/

public section

open CategoryTheory

namespace TauCeti.IntegralModel.SmoothModel

universe u

section CommRing

variable (O K : Type u) [CommRing O] [CommRing K] [Algebra O K]

/-- The standard smooth model `GL_{n,O}` of `GL_{n,K}`. -/
noncomputable def generalLinear (n : ℕ) :
    SmoothModel O K (GeneralLinear.finiteTypeCoordinateHopfAlgebra K n) where
  coord := GeneralLinear.finiteTypeCoordinateHopfAlgebra O n
  smooth := (GeneralLinear.reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra
    O n).smooth
  genericFiberIso := GeneralLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso O K n

/-- The coordinate algebra of the standard model is the coordinate algebra of `GL_{n,O}`. -/
@[simp]
theorem generalLinear_coord (n : ℕ) :
    (generalLinear O K n).coord = GeneralLinear.finiteTypeCoordinateHopfAlgebra O n :=
  (rfl)

/-- The generic fiber isomorphism of the standard model is the base change isomorphism of the
coordinate algebra of `GL_n`, transported along `generalLinear_coord`. -/
@[simp]
theorem generalLinear_genericFiberIso (n : ℕ) :
    (generalLinear O K n).genericFiberIso =
      eqToIso (congrArg (FiniteTypeCommHopfAlgCat.baseChange (K := K))
        (generalLinear_coord O K n)) ≪≫
        GeneralLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso O K n := by
  -- `generalLinear_coord` holds by `rfl`, so the transport `eqToHom` is the identity.
  ext1
  exact (Category.id_comp _).symm

end CommRing

variable (O K : Type u) [CommRing O] [IsLocalRing O] [Field K] [Algebra O K]

/-- The standard model `GL_{n,O}` is a reductive model of `GL_{n,K}`. -/
theorem isReductive_generalLinear (n : ℕ) : (generalLinear O K n).IsReductive :=
  isReductive_of_reductiveCommHopfAlgPropertyOver
    (GeneralLinear.reductiveCommHopfAlgPropertyOver_finiteTypeCoordinateHopfAlgebra O n)

/-- The two selected base changes `GL_{n,K}` and `GL_{n,κ}` of the standard model are
geometrically connected. -/
theorem hasConnectedFibers_generalLinear (n : ℕ) : (generalLinear O K n).HasConnectedFibers :=
  (isReductive_generalLinear O K n).hasConnectedFibers

/-- The integral points of the standard model `GL_{n,O}` satisfy `IsHyperspecialSubgroup O`. -/
theorem isHyperspecialSubgroup_generalLinear (n : ℕ) :
    IsHyperspecialSubgroup O (generalLinear O K n).integralPoints :=
  (isReductive_generalLinear O K n).isHyperspecialSubgroup

end TauCeti.IntegralModel.SmoothModel

namespace TauCeti.IntegralModel

universe u

open TensorProduct

section IntegralPoints

variable {O K : Type u} [CommRing O] [CommRing K] [Algebra O K] (n : ℕ)

/-- The inverse base-change isomorphism of `O(GL_n)` sends the generic entry `Xᵢⱼ` over `K` to
`1 ⊗ Xᵢⱼ`. -/
private theorem coordinateHopfAlgebraBaseChangeIso_inv_hom_X (i j : Fin n) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso.{u, u} O K n).inv.hom
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv K n
          (GeneralLinear.coordinateRingMap K n (MvPolynomial.X (i, j)))) =
      1 ⊗ₜ[O] GeneralLinear.coordinateHopfAlgebraAlgEquiv O n
        (GeneralLinear.coordinateRingMap O n (MvPolynomial.X (i, j))) :=
  GeneralLinear.coordinateHopfAlgebraBaseChangeIso_inv_X O K n i j

/-- **The integral points of `GL_{n,O}` are `GL_n(O)`.** A `K`-point `q` of `K ⊗[O] O[GL_n]`
is the base change of an `O`-point exactly when its matrix, read through the identification
`K ⊗[O] O[GL_n] ≅ K[GL_n]`, is the image of an invertible matrix over `O`: the matrix and its
inverse have entries in the image of `O`. -/
theorem mem_integralPoints_generalLinear_iff
    (q : WithConv (K ⊗[O] GeneralLinear.coordinateHopfAlgebra O n →ₐ[K] K)) :
    q ∈ integralPoints O K (GeneralLinear.coordinateHopfAlgebra O n) ↔
      ∃ M : GL (Fin n) O, M.map (algebraMap O K) =
        GeneralLinear.pointToGeneralLinear n (WithConv.toConv (q.ofConv.comp
          (GeneralLinear.coordinateHopfAlgebraBaseChangeIso.{u, u} O K n).inv.hom.toAlgHom)) := by
  rw [mem_integralPoints_iff_exists]
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨GeneralLinear.pointToGeneralLinear n f, ?_⟩
    ext i j
    simp only [Matrix.GeneralLinearGroup.map_apply, GeneralLinear.pointToGeneralLinear_apply,
      AlgHom.comp_apply, BialgHom.coe_toAlgHom]
    rw [coordinateHopfAlgebraBaseChangeIso_inv_hom_X, AlgHom.pointsBaseChange_apply_tmul, one_mul]
  · rintro ⟨M, hM⟩
    refine ⟨GeneralLinear.generalLinearToPoint n M, ?_⟩
    apply WithConv.ofConv_injective
    apply GeneralLinear.coordinateHopfAlgebra_baseChange_algHom_ext
    intro i j
    have h := congrArg (fun A : GL (Fin n) K ↦ (A : Matrix (Fin n) (Fin n) K) i j) hM
    simp only [Matrix.GeneralLinearGroup.map_apply, GeneralLinear.pointToGeneralLinear_apply,
      AlgHom.comp_apply, BialgHom.coe_toAlgHom] at h
    rw [coordinateHopfAlgebraBaseChangeIso_inv_hom_X] at h
    rw [AlgHom.pointsBaseChange_apply_tmul, one_mul, GeneralLinear.generalLinearToPoint_apply, h]

end IntegralPoints

end TauCeti.IntegralModel
