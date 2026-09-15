/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points

/-!
# The generic matrices of the generating coordinate maps of a toral Kostant carrier

The toral Kostant carrier is generated inside `GLₙ` by the represented root subgroups and the
represented weight torus, and a containment of closed subgroup schemes of `GLₙ` is tested on
those generators. Testing it means evaluating the ambient defining relations on the generic
matrix of each generating coordinate map, so it is useful to know that those generic matrices are
themselves represented matrices: the generic matrix of the `i`th root-subgroup coordinate map is
the divided-power exponential matrix at the universal point of `𝔾ₐ`, and the generic matrix of
the weight-torus coordinate map is the weight-diagonal matrix at the universal point of the split
torus.

Both statements are the Yoneda reading of the corresponding coordinate map: a coordinate morphism
out of `O(GLₙ)` is a matrix point of `GLₙ` over its target, its generic matrix is the matrix of
that point, and for these two coordinate maps that point is known.

## Main results

In the namespace `TauCeti.UniversalEnvelopingAlgebra`:

* `exists_map_genericMatrix_kostantRootSubgroupCoordinateMap`: the generic matrix of a
  represented root-subgroup coordinate map is a represented root-subgroup matrix.
* `exists_map_genericMatrix_weightTorusCoordinateMap`: the generic matrix of the represented
  weight-torus coordinate map is a represented weight-torus matrix.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), §1.2, for the Yoneda reading
  of a coordinate morphism as a point.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)

omit [Finite κ] in
/-- **The generic matrix of a represented root-subgroup coordinate map is a divided-power
exponential matrix.** Some point of `𝔾ₐ` over its own coordinate algebra realizes it; the proof
takes the universal one, which the existential does not record. -/
theorem exists_map_genericMatrix_kostantRootSubgroupCoordinateMap (i : I) :
    ∃ q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ]
        AdditiveGroup.coordinateHopfAlgebra ℤ),
      (GeneralLinear.genericMatrix ℤ n).map
          (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom =
        ((kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q :
          Matrix.GeneralLinearGroup (Fin n) (AdditiveGroup.coordinateHopfAlgebra ℤ)) :
          Matrix (Fin n) (Fin n) (AdditiveGroup.coordinateHopfAlgebra ℤ)) := by
  let q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ]
      AdditiveGroup.coordinateHopfAlgebra ℤ) :=
    toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))
  have hpoint := pointsMulEquiv_kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b
    (AdditiveGroup.coordinateHopfAlgebra ℤ) q
  have hpoint' : GeneralLinear.pointToGeneralLinear n
      (toConv (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom) =
      kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q := by
    refine Eq.trans ?_ hpoint
    refine congrArg (GeneralLinear.pointToGeneralLinear n) (congrArg toConv ?_)
    rw [WithConv.ofConv_toConv]
    exact (AlgHom.id_comp _).symm
  refine ⟨q, ?_⟩
  rw [GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
  exact congrArg _ hpoint'

omit [Module ℚ V] in
/-- **The generic matrix of the represented weight-torus coordinate map is a weight-diagonal
matrix.** Some point of the split torus over its own coordinate algebra realizes it; the proof
takes the universal one, which the existential does not record. -/
theorem exists_map_genericMatrix_weightTorusCoordinateMap [Fintype κ] :
    ∃ s : κ → ((DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj)ˣ,
      (GeneralLinear.genericMatrix ℤ n).map
          (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom =
        ((kostantTorusMatrix M b wt s :
          Matrix.GeneralLinearGroup (Fin n)
            (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj) :
          Matrix (Fin n) (Fin n)
            (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj) := by
  let p : HopfAlgebra.points (R := ℤ)
      (H := (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj)
      (CommAlgCat.of ℤ
        (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj) :=
    toConv (AlgHom.id ℤ
      (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj)
  refine ⟨SplitTorus.pointsMulEquiv (R := ℤ) (σ := κ) p, ?_⟩
  have hq : (CommHopfAlgCat.mapPointsFunctor
        (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt)).app
        (CommAlgCat.of ℤ
          (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj) p =
      toConv (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply, WithConv.ofConv_toConv, AlgHom.id_comp]
  rw [GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
  refine congrArg _ ?_
  rw [← GeneralLinear.pointsMulEquiv_apply, ← hq,
    GeneralLinear.mapPointsFunctor_weightTorusCoordinateMap_app,
    GeneralLinear.pointsMulEquiv_diagonalTorusPoints, kostantTorusMatrix_apply]
  refine congrArg _ ?_
  funext i
  rw [GeneralLinear.diagonalTorusCoordinates_pointsMap_weightCharacterMap wt
    (CommAlgCat.of ℤ (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj) p i]

end TauCeti.UniversalEnvelopingAlgebra
