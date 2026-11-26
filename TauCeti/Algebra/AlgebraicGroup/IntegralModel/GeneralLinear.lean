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
`K`-point of `GL_n` is integral exactly when its matrix is the image of an invertible matrix over
`O` (`TauCeti.IntegralModel.SmoothModel.mem_integralPoints_generalLinear_iff`). When `O → K` is
injective, this says that the matrix and its inverse have entries in `O`. The same criterion holds
for the `K`-points of `K ⊗[O] O[GL_n]`
(`TauCeti.IntegralModel.mem_integralPoints_generalLinear_iff`). When `O` is local and `K` is a
field the model is reductive, so its integral points satisfy
`TauCeti.IntegralModel.IsHyperspecialSubgroup`.

## Main declarations

* `TauCeti.IntegralModel.SmoothModel.generalLinear`: the standard model of `GL_n`.
* `TauCeti.IntegralModel.SmoothModel.mem_integralPoints_generalLinear_iff`: its integral points
  are `GL_n(O)`.
* `TauCeti.IntegralModel.mem_integralPoints_generalLinear_iff`: the same criterion for the
  integral points of `K ⊗[O] O[GL_n]`.
* `TauCeti.IntegralModel.SmoothModel.specialFiberGeneralLinearIso`: its special fiber over a local
  ring is `GL_n` over the residue field.
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

/-- **The special fiber of the standard model is `GL_n` over the residue field**: for a local
ring `O` with residue field `κ`, `κ ⊗[O] O[GL_n] ≅ κ[GL_n]`. -/
noncomputable def specialFiberGeneralLinearIso [IsLocalRing O] (n : ℕ) :
    (generalLinear O K n).specialFiber ≅
      GeneralLinear.finiteTypeCoordinateHopfAlgebra (IsLocalRing.ResidueField O) n :=
  GeneralLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso O (IsLocalRing.ResidueField O) n

/-- The special fiber isomorphism of the standard model is the base change isomorphism of the
coordinate algebra of `GL_n` to the residue field, transported along `generalLinear_coord`. -/
theorem specialFiberGeneralLinearIso_def [IsLocalRing O] (n : ℕ) :
    specialFiberGeneralLinearIso O K n =
      eqToIso (congrArg (FiniteTypeCommHopfAlgCat.baseChange (K := IsLocalRing.ResidueField O))
        (generalLinear_coord O K n)) ≪≫
        GeneralLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso O
          (IsLocalRing.ResidueField O) n := by
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

/-- **The integral points of `GL_{n,O}` are `GL_n(O)`.** A `K`-point `q` of `K ⊗[O] O[GL_n]`
is the base change of an `O`-point exactly when its matrix, read through the identification
`K ⊗[O] O[GL_n] ≅ K[GL_n]`, is the image of an invertible matrix over `O`. When `O → K` is
injective, this says that the matrix and its inverse have entries in `O`. -/
theorem mem_integralPoints_generalLinear_iff
    (q : WithConv (K ⊗[O] GeneralLinear.coordinateHopfAlgebra O n →ₐ[K] K)) :
    q ∈ integralPoints O K (GeneralLinear.coordinateHopfAlgebra O n) ↔
      ∃ M : GL (Fin n) O, M.map (algebraMap O K) =
        GeneralLinear.pointToGeneralLinear n (WithConv.toConv (q.ofConv.comp
          (GeneralLinear.coordinateHopfAlgebraBaseChangeIso.{u, u} O K n).inv.hom.toAlgHom)) := by
  rw [mem_integralPoints_iff_exists]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨_, (GeneralLinear.pointToGeneralLinear_pointsBaseChange O K n f).symm⟩
  · rintro ⟨M, hM⟩
    refine ⟨GeneralLinear.generalLinearToPoint n M, ?_⟩
    rw [← GeneralLinear.pointToGeneralLinear_generalLinearToPoint (R := O) n M,
      ← GeneralLinear.pointToGeneralLinear_pointsBaseChange] at hM
    have h := congrArg (fun p ↦ (GeneralLinear.generalLinearToPoint n p).ofConv.comp
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso.{u, u} O K n).hom.hom.toAlgHom) hM
    refine WithConv.ofConv_injective (AlgHom.ext fun x ↦ ?_)
    simpa using DFunLike.congr_fun h x

/-- `mem_integralPoints_generalLinear_iff`, transported along equalities identifying `B` and
`B'` with the coordinate Hopf algebras of `GL_n` over `O` and `K`. The finite-type coordinate
algebra of `GL_n` is such a `B`, but only propositionally outside its defining module. -/
private theorem mem_integralPoints_generalLinear_iff_of_eq {B : CommHopfAlgCat.{u} O}
    {B' : CommHopfAlgCat.{u} K} (h : B = GeneralLinear.coordinateHopfAlgebra O n)
    (h' : B' = GeneralLinear.coordinateHopfAlgebra K n) (g : WithConv (B' →ₐ[K] K)) :
    BialgHom.mapDomain (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K)) h) ≪≫
        GeneralLinear.coordinateHopfAlgebraBaseChangeIso.{u, u} O K n ≪≫
          eqToIso h'.symm).hom.hom g ∈ integralPoints O K B ↔
      ∃ M : GL (Fin n) O, M.map (algebraMap O K) = GeneralLinear.pointToGeneralLinear n
        (WithConv.toConv (g.ofConv.comp (eqToHom h'.symm).hom.toAlgHom)) := by
  subst h h'
  rw [mem_integralPoints_generalLinear_iff (O := O) (K := K) n]
  congr! 4
  refine congrArg WithConv.toConv (AlgHom.ext fun x ↦ ?_)
  simp

variable (O) in
/-- **The integral points of the standard model `GL_{n,O}` are `GL_n(O)`.** A `K`-point `g` of
`GL_n` is integral for `SmoothModel.generalLinear O K n` exactly when its matrix, read through
`GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj`, is the image of an invertible matrix over
`O`. -/
theorem SmoothModel.mem_integralPoints_generalLinear_iff
    (g : WithConv (GeneralLinear.finiteTypeCoordinateHopfAlgebra K n →ₐ[K] K)) :
    g ∈ (SmoothModel.generalLinear O K n).integralPoints ↔
      ∃ M : GL (Fin n) O, M.map (algebraMap O K) = GeneralLinear.pointToGeneralLinear n
        (WithConv.toConv (g.ofConv.comp (eqToHom
          (GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj K n).symm).hom.toAlgHom)) := by
  refine Iff.trans ?_ (mem_integralPoints_generalLinear_iff_of_eq n
    ((congrArg ObjectProperty.FullSubcategory.obj (SmoothModel.generalLinear_coord O K n)).trans
      (GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj O n))
    (GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj K n) g)
  rw [SmoothModel.mem_integralPoints_iff_mapDomain, SmoothModel.generalLinear_genericFiberIso,
    Iso.trans_hom, FiniteTypeCommHopfAlgCat.toBialgHom, ObjectProperty.FullSubcategory.comp_hom,
    GeneralLinear.finiteTypeCoordinateHopfAlgebraBaseChangeIso_hom]
  simp only [ObjectProperty.eqToHom_hom, Iso.trans_hom, eqToIso.hom, eqToHom_trans_assoc]

end IntegralPoints

end TauCeti.IntegralModel
