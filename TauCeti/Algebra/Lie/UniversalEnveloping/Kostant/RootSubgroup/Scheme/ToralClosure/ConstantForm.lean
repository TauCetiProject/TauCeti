/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.GenericMatrix

/-!
# The toral Kostant carrier inside a constant-form subgroup scheme

Fix a constant matrix `C : Matrix (Fin n) (Fin n) ℤ` and let
`TauCeti.ConstantForm.definingHopfIdeal` be the Hopf ideal cutting out the subgroup scheme of
`GLₙ` whose points are the invertible matrices `M` with `M C Mᵀ = C`.

The toral Kostant carrier is the smallest closed subgroup scheme of `GLₙ` containing the
represented root subgroups and the represented weight torus, so it lies inside that subgroup
scheme as soon as its generators do. Since the defining ideal of the carrier is the largest Hopf
ideal killed by the root-subgroup and weight-torus coordinate maps, the containment of Hopf ideals
reduces to evaluating the form relation on the generic matrix of each generating coordinate map —
equivalently, to checking the congruence `M C Mᵀ = C` for the divided-power exponential matrices
and for the weight-diagonal matrices over every commutative ring. On points this says that every
matrix point of the carrier fixes `C` by congruence.

Only the containment is proved. Nothing here asserts that the carrier exhausts the points of the
constant-form subgroup scheme, or that either group scheme is reductive or smooth. Nor is any
relation asserted between the congruence `M C Mᵀ = C` and the transposed congruence
`Mᵀ C M = C`, which is a different closed condition and is cut out by a different Hopf ideal.

## Main results

In the namespace `TauCeti.UniversalEnvelopingAlgebra`:

* `constantFormDefiningHopfIdeal_le_kostantToralDefiningIdeal` and
  `mul_mul_transpose_of_mem_kostantToralPointsSubgroup`: the containment of Hopf ideals and its
  consequence on matrix points, from the generic matrices of the generating coordinate maps.
* `constantFormDefiningHopfIdeal_le_kostantToralDefiningIdeal_of_generators` and
  `mul_mul_transpose_of_mem_kostantToralPointsSubgroup_of_generators`: the same two statements
  from the congruence relation for the generator matrices over every commutative ring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1, for the torus and root subgroups
  generating the Chevalley group.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.

The reduction of a containment of Hopf ideals to the generating coordinate maps is the one
carried out for a constant bilinear multiplication by
`constantMultiplicationDefiningHopfIdeal_le_kostantToralDefiningIdeal`; the statements below are
its counterpart for a constant form.
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
variable (C : Matrix (Fin n) (Fin n) ℤ)

/-- **The generators of the toral Kostant carrier cut out the form.** If the generic matrix `X` of
every represented root-subgroup coordinate map and of the represented weight-torus coordinate map
satisfies `X C Xᵀ = C`, then the Hopf ideal cutting out the subgroup scheme preserving `C` is
contained in the toral defining ideal. Equivalently, the toral carrier is a closed subgroup scheme
of the group scheme preserving `C`. -/
theorem constantFormDefiningHopfIdeal_le_kostantToralDefiningIdeal
    (hroot : ∀ i, (GeneralLinear.genericMatrix ℤ n).map
          (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom *
          C.map (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) *
          ((GeneralLinear.genericMatrix ℤ n).map
            (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom)ᵀ =
        C.map (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)))
    (htorus : (GeneralLinear.genericMatrix ℤ n).map
          (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom *
          C.map (algebraMap ℤ
            (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj) *
          ((GeneralLinear.genericMatrix ℤ n).map
            (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom)ᵀ =
        C.map (algebraMap ℤ
          (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj)) :
    ConstantForm.definingHopfIdeal ℤ n C ≤ kostantToralDefiningIdeal e h ρ M hM hnil b wt := by
  rw [le_kostantToralDefiningIdeal_iff]
  refine ⟨fun i => ?_, ?_⟩
  · exact ConstantForm.definingHopfIdeal_toIdeal_le_ker_of_map_genericMatrix_mul_mul_transpose
      ℤ n C _ (hroot i)
  · exact ConstantForm.definingHopfIdeal_toIdeal_le_ker_of_map_genericMatrix_mul_mul_transpose
      ℤ n C _ htorus

/-- **Every matrix point of the toral Kostant carrier fixes the form by congruence**, as soon as
the generic matrices of the root-subgroup and weight-torus coordinate maps do. -/
theorem mul_mul_transpose_of_mem_kostantToralPointsSubgroup
    (hroot : ∀ i, (GeneralLinear.genericMatrix ℤ n).map
          (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom *
          C.map (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)) *
          ((GeneralLinear.genericMatrix ℤ n).map
            (kostantRootSubgroupCoordinateMap e h ρ M hM i (hnil i) b).hom.toAlgHom)ᵀ =
        C.map (algebraMap ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)))
    (htorus : (GeneralLinear.genericMatrix ℤ n).map
          (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom *
          C.map (algebraMap ℤ
            (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj) *
          ((GeneralLinear.genericMatrix ℤ n).map
            (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom)ᵀ =
        C.map (algebraMap ℤ
          (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj))
    (A : Type v) [CommRing A] {g : Matrix.GeneralLinearGroup (Fin n) A}
    (hg : g ∈ kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
    (g : Matrix (Fin n) (Fin n) A) * C.map (algebraMap ℤ A) *
      (g : Matrix (Fin n) (Fin n) A)ᵀ = C.map (algebraMap ℤ A) := by
  rw [kostantToralPointsSubgroup_def] at hg
  have hsub := GeneralLinear.hopfIdealPointsSubgroup_le_of_le n
    (constantFormDefiningHopfIdeal_le_kostantToralDefiningIdeal
      e h ρ M hM hnil b wt C hroot htorus) A hg
  rw [GeneralLinear.mem_hopfIdealPointsSubgroup_iff] at hsub
  have hmem : ((GeneralLinear.pointsMulEquiv (R := ℤ) n).symm g) ∈
      CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (ConstantForm.definingHopfIdeal ℤ n C) (CommAlgCat.of ℤ A) :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr hsub
  rw [ConstantForm.mem_definingPointsSubgroup_iff, MulEquiv.apply_symm_apply] at hmem
  exact hmem

/-! ### The criterion on the generator matrices -/

section Generators

variable [Fintype κ]

/-- **The toral Kostant carrier fixes a form fixed by its generators.** If every represented
root-subgroup matrix and every represented weight-torus matrix `M` satisfies `M C Mᵀ = C`, over
every commutative ring, then the Hopf ideal cutting out the subgroup scheme preserving `C` is
contained in the toral defining ideal. -/
theorem constantFormDefiningHopfIdeal_le_kostantToralDefiningIdeal_of_generators
    (hroot : ∀ (i : I) (A : Type) [CommRing A]
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      ((kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q :
            Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) *
          C.map (algebraMap ℤ A) *
          ((kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q :
            Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ =
        C.map (algebraMap ℤ A))
    (htorus : ∀ (A : Type) [CommRing A] (s : κ → Aˣ),
      ((kostantTorusMatrix M b wt s : Matrix.GeneralLinearGroup (Fin n) A) :
            Matrix (Fin n) (Fin n) A) * C.map (algebraMap ℤ A) *
          ((kostantTorusMatrix M b wt s : Matrix.GeneralLinearGroup (Fin n) A) :
            Matrix (Fin n) (Fin n) A)ᵀ =
        C.map (algebraMap ℤ A)) :
    ConstantForm.definingHopfIdeal ℤ n C ≤ kostantToralDefiningIdeal e h ρ M hM hnil b wt := by
  refine constantFormDefiningHopfIdeal_le_kostantToralDefiningIdeal
    e h ρ M hM hnil b wt C (fun i => ?_) ?_
  · obtain ⟨q, hqm⟩ :=
      exists_map_genericMatrix_kostantRootSubgroupCoordinateMap e h ρ M hM hnil b i
    rw [hqm]
    exact hroot i _ q
  · obtain ⟨s, hsm⟩ := exists_map_genericMatrix_weightTorusCoordinateMap M b wt
    rw [hsm]
    exact htorus _ s

/-- **Every matrix point of the toral Kostant carrier fixes a form fixed by its generators.** -/
theorem mul_mul_transpose_of_mem_kostantToralPointsSubgroup_of_generators
    (hroot : ∀ (i : I) (A : Type) [CommRing A]
      (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)),
      ((kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q :
            Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) *
          C.map (algebraMap ℤ A) *
          ((kostantRootSubgroupMatrix e h ρ M hM i (hnil i) b q :
            Matrix.GeneralLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ =
        C.map (algebraMap ℤ A))
    (htorus : ∀ (A : Type) [CommRing A] (s : κ → Aˣ),
      ((kostantTorusMatrix M b wt s : Matrix.GeneralLinearGroup (Fin n) A) :
            Matrix (Fin n) (Fin n) A) * C.map (algebraMap ℤ A) *
          ((kostantTorusMatrix M b wt s : Matrix.GeneralLinearGroup (Fin n) A) :
            Matrix (Fin n) (Fin n) A)ᵀ =
        C.map (algebraMap ℤ A))
    (A : Type v) [CommRing A] {g : Matrix.GeneralLinearGroup (Fin n) A}
    (hg : g ∈ kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
    (g : Matrix (Fin n) (Fin n) A) * C.map (algebraMap ℤ A) *
      (g : Matrix (Fin n) (Fin n) A)ᵀ = C.map (algebraMap ℤ A) := by
  refine mul_mul_transpose_of_mem_kostantToralPointsSubgroup e h ρ M hM hnil b wt C
    (fun i => ?_) ?_ A hg
  · obtain ⟨q, hqm⟩ :=
      exists_map_genericMatrix_kostantRootSubgroupCoordinateMap e h ρ M hM hnil b i
    rw [hqm]
    exact hroot i _ q
  · obtain ⟨s, hsm⟩ := exists_map_genericMatrix_weightTorusCoordinateMap M b wt
    rw [hsm]
    exact htorus _ s

end Generators

end TauCeti.UniversalEnvelopingAlgebra
