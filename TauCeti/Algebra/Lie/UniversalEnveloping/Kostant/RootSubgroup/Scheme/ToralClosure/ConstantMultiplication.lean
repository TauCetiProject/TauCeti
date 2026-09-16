/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points

/-!
# The toral Kostant carrier inside a constant-multiplication subgroup scheme

Fix a bilinear multiplication on `ℤⁿ` given by constant structure matrices
`C : Fin n → Matrix (Fin n) (Fin n) ℤ`, and let `TauCeti.ConstantMultiplication.definingHopfIdeal`
be the Hopf ideal cutting out the subgroup scheme of `GLₙ` whose points are the invertible
matrices multiplicative for that product.

The toral Kostant carrier is the smallest closed subgroup scheme of `GLₙ` containing the
represented root subgroups and the represented weight torus, so it lies inside that subgroup
scheme as soon as its generators do. Since the defining ideal of the carrier is the largest Hopf
ideal killed by the root-subgroup and weight-torus coordinate maps, the containment of Hopf
ideals reduces to evaluating the defining relations on the generic matrix of each generating
coordinate map — equivalently, to checking multiplicativity of the divided-power exponential
matrices and of the weight-diagonal matrices over every commutative ring. On points this says
that every matrix point of the carrier is multiplicative for the product.

Only the containment is proved. Nothing here asserts that the carrier exhausts the points of the
constant-multiplication subgroup scheme, or that either group scheme is reductive or smooth.

## Main results

In the namespace `TauCeti.UniversalEnvelopingAlgebra`:

* `constantMultiplicationDefiningHopfIdeal_le_kostantToralDefiningIdeal` and
  `preserves_of_mem_kostantToralPointsSubgroup`: the containment of Hopf ideals and its
  consequence on matrix points, from the generic matrices of the generating coordinate maps.
* `constantMultiplicationDefiningHopfIdeal_le_kostantToralDefiningIdeal_of_generators` and
  `preserves_of_mem_kostantToralPointsSubgroup_of_generators`: the same two statements from
  multiplicativity of the generator matrices over every commutative ring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1, for the torus and root subgroups
  generating the Chevalley group.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.

The reduction of a containment of Hopf ideals to the generating coordinate maps is the one
carried out for a constant bilinear form in `TauCeti.SpStd`; the statements below package it once
for an arbitrary constant multiplication and an arbitrary toral Kostant carrier.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

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
variable (C : Fin n → Matrix (Fin n) (Fin n) ℤ)

/-- **The generators of the toral Kostant carrier cut out the multiplication.** If the generic
matrix of every represented root-subgroup coordinate map and of the represented weight-torus
coordinate map preserves the multiplication with structure matrices `C`, then the Hopf ideal
cutting out the subgroup scheme preserving that multiplication is contained in the toral defining
ideal. Equivalently, the toral carrier is a closed subgroup scheme of the group scheme preserving
the multiplication. -/
theorem constantMultiplicationDefiningHopfIdeal_le_kostantToralDefiningIdeal
    (hroot : ∀ i, ConstantMultiplication.Preserves ℤ n C
      ((GeneralLinear.genericMatrix ℤ n).map
        (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom))
    (htorus : ConstantMultiplication.Preserves ℤ n C
      ((GeneralLinear.genericMatrix ℤ n).map
        (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom)) :
    ConstantMultiplication.definingHopfIdeal ℤ n C ≤
      kostantToralDefiningIdeal e h ρ M hM hnil b wt := by
  rw [le_kostantToralDefiningIdeal_iff]
  refine ⟨fun i => ?_, ?_⟩
  · exact ConstantMultiplication.definingHopfIdeal_toIdeal_le_ker_of_preserves_map_genericMatrix
      ℤ n C _ (hroot i)
  · exact ConstantMultiplication.definingHopfIdeal_toIdeal_le_ker_of_preserves_map_genericMatrix
      ℤ n C _ htorus

/-- **Every matrix point of the toral Kostant carrier preserves the multiplication**, as soon as
the generic matrices of the root-subgroup and weight-torus coordinate maps do. -/
theorem preserves_of_mem_kostantToralPointsSubgroup
    (hroot : ∀ i, ConstantMultiplication.Preserves ℤ n C
      ((GeneralLinear.genericMatrix ℤ n).map
        (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom))
    (htorus : ConstantMultiplication.Preserves ℤ n C
      ((GeneralLinear.genericMatrix ℤ n).map
        (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom))
    (A : Type v) [CommRing A] {g : Matrix.GeneralLinearGroup (Fin n) A}
    (hg : g ∈ kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
    ConstantMultiplication.Preserves ℤ n C (g : Matrix (Fin n) (Fin n) A) := by
  rw [kostantToralPointsSubgroup_def] at hg
  have hsub := GeneralLinear.hopfIdealPointsSubgroup_le_of_le n
    (constantMultiplicationDefiningHopfIdeal_le_kostantToralDefiningIdeal
      e h ρ M hM hnil b wt C hroot htorus) A hg
  rw [GeneralLinear.mem_hopfIdealPointsSubgroup_iff] at hsub
  have hmem : ((GeneralLinear.pointsMulEquiv (R := ℤ) n).symm g) ∈
      CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (ConstantMultiplication.definingHopfIdeal ℤ n C) (CommAlgCat.of ℤ A) :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr hsub
  rw [ConstantMultiplication.mem_definingPointsSubgroup_iff, MulEquiv.apply_symm_apply] at hmem
  exact hmem

/-! ### The criterion on the generator matrices -/

omit [Finite κ] in
/-- The generic matrix of a represented root-subgroup coordinate map is the divided-power
exponential matrix at the universal point of `𝔾ₐ`. -/
private theorem exists_map_genericMatrix_kostantRootSubgroupCoordinateMap (i : I) :
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
  have hq : q.ofConv = AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) :=
    WithConv.ofConv_toConv _
  have hpoint := pointsMulEquiv_kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b
    (AdditiveGroup.coordinateHopfAlgebra ℤ) q
  have hpoint' : GeneralLinear.pointToGeneralLinear n
      (toConv (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom) =
      kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q := by
    refine Eq.trans ?_ hpoint
    refine congrArg (GeneralLinear.pointToGeneralLinear n) (congrArg toConv ?_)
    exact AlgHom.ext fun x => rfl
  refine ⟨q, ?_⟩
  rw [GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
  exact congrArg _ hpoint'

section Generators

omit [Module ℚ V] in
/-- The generic matrix of the represented weight-torus coordinate map is the weight-diagonal
matrix at the universal point of the split torus. -/
private theorem exists_map_genericMatrix_weightTorusCoordinateMap [Fintype κ] :
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
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
    exact congrArg toConv (AlgHom.ext fun x => rfl)
  rw [GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
  refine congrArg _ ?_
  rw [← GeneralLinear.pointsMulEquiv_apply, ← hq,
    GeneralLinear.mapPointsFunctor_weightTorusCoordinateMap_app,
    GeneralLinear.pointsMulEquiv_diagonalTorusPoints, kostantTorusMatrix_apply]
  refine congrArg _ ?_
  funext i
  rw [GeneralLinear.diagonalTorusCoordinates_pointsMap_weightCharacterMap wt
    (CommAlgCat.of ℤ (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj) p i]

/-- **The toral Kostant carrier preserves a multiplication preserved by its generators.** If
every represented root-subgroup matrix and every represented weight-torus matrix preserves the
multiplication with structure matrices `C`, over every commutative ring, then the Hopf ideal
cutting out the subgroup scheme preserving that multiplication is contained in the toral
defining ideal. -/
theorem constantMultiplicationDefiningHopfIdeal_le_kostantToralDefiningIdeal_of_generators
    (hroot : ∀ (i : I) (A : Type) [CommRing A]
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      ConstantMultiplication.Preserves ℤ n C
        ((kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q :
          Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (htorus : letI := Fintype.ofFinite κ
      ∀ (A : Type) [CommRing A] (s : κ → Aˣ),
      ConstantMultiplication.Preserves ℤ n C
        ((kostantTorusMatrix M b wt s : Matrix.GeneralLinearGroup (Fin n) A) :
          Matrix (Fin n) (Fin n) A)) :
    ConstantMultiplication.definingHopfIdeal ℤ n C ≤
      kostantToralDefiningIdeal e h ρ M hM hnil b wt := by
  refine constantMultiplicationDefiningHopfIdeal_le_kostantToralDefiningIdeal
    e h ρ M hM hnil b wt C (fun i => ?_) ?_
  · obtain ⟨q, hqm⟩ :=
      exists_map_genericMatrix_kostantRootSubgroupCoordinateMap e h ρ M hM hnil b i
    rw [hqm]
    exact hroot i _ q
  · let _ := Fintype.ofFinite κ
    obtain ⟨s, hsm⟩ := exists_map_genericMatrix_weightTorusCoordinateMap M b wt
    rw [hsm]
    exact htorus _ s

/-- **Every matrix point of the toral Kostant carrier preserves a multiplication preserved by
its generators.** -/
theorem preserves_of_mem_kostantToralPointsSubgroup_of_generators
    (hroot : ∀ (i : I) (A : Type) [CommRing A]
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      ConstantMultiplication.Preserves ℤ n C
        ((kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q :
          Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (htorus : letI := Fintype.ofFinite κ
      ∀ (A : Type) [CommRing A] (s : κ → Aˣ),
      ConstantMultiplication.Preserves ℤ n C
        ((kostantTorusMatrix M b wt s : Matrix.GeneralLinearGroup (Fin n) A) :
          Matrix (Fin n) (Fin n) A))
    (A : Type v) [CommRing A] {g : Matrix.GeneralLinearGroup (Fin n) A}
    (hg : g ∈ kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
    ConstantMultiplication.Preserves ℤ n C (g : Matrix (Fin n) (Fin n) A) := by
  refine preserves_of_mem_kostantToralPointsSubgroup e h ρ M hM hnil b wt C
    (fun i => ?_) ?_ A hg
  · obtain ⟨q, hqm⟩ :=
      exists_map_genericMatrix_kostantRootSubgroupCoordinateMap e h ρ M hM hnil b i
    rw [hqm]
    exact hroot i _ q
  · let _ := Fintype.ofFinite κ
    obtain ⟨s, hsm⟩ := exists_map_genericMatrix_weightTorusCoordinateMap M b wt
    rw [hsm]
    exact htorus _ s

end Generators

end TauCeti.UniversalEnvelopingAlgebra
