/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.DeformedReflection
public import TauCeti.LinearAlgebra.GeneralLinearGroup.Congr
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.ProjectiveTensor
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.K0

/-!
# The zigzag braid complexes on the graded Grothendieck group

The braid complex `B_i = [U_i ⟶ Z]` of the zigzag algebra `Z`, with `U_i = P_i ⊗_k e_i Z` in
cohomological degree `-1`, sends the graded vertex projective `P_j` to a two-term complex of
finite graded projectives. Its Euler class in the Laurent Grothendieck group `K₀^gr(proj Z)` is

```text
[Z ⊗_Z P_j] - [U_i ⊗_Z P_j] = [P_j] - C_{ij}(q) [P_i],
```

where `C_{ij}(q)` is the graded Cartan entry: `1 + q²` on the diagonal, `q` on edges and `0`
otherwise. This is the deformed simple reflection `SimpleGraph.deformedReflection` at the unit
`q`, written in the basis of vertex-projective classes. Hence the Artin group of the graph acts
on `K₀^gr(proj Z)` with the standard generator `σ_i` acting by the Euler class of `B_i`, and this
action is conjugate, through the vertex-projective coordinates, to the deformed reflection
representation `SimpleGraph.deformedReflectionRepresentation`.
At `q = -1` the deformed reflections are the standard simple reflections of the graph Cartan
matrix `2I - A` (`SimpleGraph.deformedReflection_neg_one`).

## Main definitions

* `TauCeti.zigzagBraidK0Action`: the action of the Artin group of the graph on
  `K₀^gr(proj Z)` by deformed reflections in the vertex-projective basis.

## Main results

* `TauCeti.laurentK0_of_zigzagBraidProjectiveTensor`: `[U_i ⊗_Z P_j] = C_{ij}(q) [P_i]`.
* `TauCeti.laurentK0_of_zigzagBraidProjectiveUnitTensor`: `[Z ⊗_Z P_j] = [P_j]`.
* `TauCeti.zigzagBraidK0Action_gen_zigzagAlgebraGradedProjectiveClass`: the standard generator
  `σ_i` sends `[P_j]` to the Euler class `[Z ⊗_Z P_j] - [U_i ⊗_Z P_j]` of `B_i ⊗_Z P_j`.

## References

* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 4.6.
* M. Khovanov and P. Seidel, *Quivers, Floer cohomology, and braid group actions*, Section 2e.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u w

variable (k : Type w) {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "A" => zigzagAlgebraIntegerGrade k G
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "P" => zigzagAlgebraGradedProjective k G

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

section CommRing

variable [CommRing k]

/-! ### The terms of `B_i ⊗_Z P_j` are finite graded projectives -/

/-- The degree `-1` term `U_i ⊗_Z P_j` of `B_i ⊗_Z P_j` is a finite graded projective. -/
theorem gradedFiniteProjectiveModules_zigzagBraidProjectiveTensor (i j : V) :
    gradedFiniteProjectiveModules A (GradedModuleCat.bimoduleModuleTensorObj Γ Γ (U i) (P j)) := by
  have hP := gradedFiniteProjectiveModules_zigzagAlgebraGradedProjective k G i
  by_cases hij : i = j
  · subst hij
    exact (gradedFiniteProjectiveModules A).prop_of_iso
      (zigzagBraidProjectiveTensorSelfIso k G i).symm
      ((gradedFiniteProjectiveModules A).prop_biprod_of_isClosedUnderBinaryProducts hP
        (gradedFiniteProjectiveModules_shiftObj hP 2))
  by_cases hadj : G.Adj i j
  · exact (gradedFiniteProjectiveModules A).prop_of_iso
      (zigzagBraidProjectiveTensorAdjIso k G hadj.symm).symm
      (gradedFiniteProjectiveModules_shiftObj hP 1)
  · exact (gradedFiniteProjectiveModules A).prop_of_isZero
      (isZero_zigzagBraidProjectiveTensor k G hij hadj)

/-- The degree `0` term `Z ⊗_Z P_j` of `B_i ⊗_Z P_j` is a finite graded projective. -/
theorem gradedFiniteProjectiveModules_zigzagBraidProjectiveUnitTensor (j : V) :
    gradedFiniteProjectiveModules A
      (GradedModuleCat.bimoduleModuleTensorObj Γ Γ (zigzagGradedBimodule k G) (P j)) :=
  (gradedFiniteProjectiveModules A).prop_of_iso (zigzagBraidProjectiveUnitTensorIso k G j).symm
    (gradedFiniteProjectiveModules_zigzagAlgebraGradedProjective k G j)

/-! ### Their classes -/

/-- **`[Z ⊗_Z P_j] = [P_j]`** in `K₀^gr(proj Z)`. -/
theorem laurentK0_of_zigzagBraidProjectiveUnitTensor (j : V) :
    LaurentK0.of.{max u w} (gradedFiniteProjectiveModulesExactStructure A)
        ⟨_, gradedFiniteProjectiveModules_zigzagBraidProjectiveUnitTensor k G j⟩ =
      zigzagAlgebraGradedProjectiveClass k G j := by
  rw [zigzagAlgebraGradedProjectiveClass_def]
  exact LaurentK0.of_congr.{max u w} _
    (ObjectProperty.isoMk _ (zigzagBraidProjectiveUnitTensorIso k G j))

/-- **`[U_i ⊗_Z P_j] = C_{ij}(q) [P_i]`** in `K₀^gr(proj Z)`, where `C_{ij}(q)` is the deformed
Cartan entry `1 + q²`, `q` or `0` at `q = T 1`. -/
theorem laurentK0_of_zigzagBraidProjectiveTensor [DecidableEq V] (i j : V) :
    LaurentK0.of.{max u w} (gradedFiniteProjectiveModulesExactStructure A)
        ⟨_, gradedFiniteProjectiveModules_zigzagBraidProjectiveTensor k G i j⟩ =
      G.deformedCartanEntry (LaurentPolynomial.T 1 : LaurentPolynomial ℤ) i j •
        zigzagAlgebraGradedProjectiveClass k G i := by
  have hP := gradedFiniteProjectiveModules_zigzagAlgebraGradedProjective k G i
  rw [zigzagAlgebraGradedProjectiveClass_def]
  set Q : (gradedFiniteProjectiveModules A).FullSubcategory := ⟨P i, hP⟩
  have hshift (d : ℤ) := laurentK0_projective_of_shiftObj Q d
  by_cases hij : i = j
  · subst hij
    let Q₂ : (gradedFiniteProjectiveModules A).FullSubcategory :=
      ⟨(P i).shiftObj 2, gradedFiniteProjectiveModules_shiftObj hP 2⟩
    have : PreservesBinaryBiproduct Q Q₂ (gradedFiniteProjectiveModules A).ι :=
      preservesBinaryBiproduct_of_preservesBiproduct _ Q Q₂
    have e : (⟨_, gradedFiniteProjectiveModules_zigzagBraidProjectiveTensor k G i i⟩ :
        (gradedFiniteProjectiveModules A).FullSubcategory) ≅ Q ⊞ Q₂ :=
      ObjectProperty.isoMk _ ((zigzagBraidProjectiveTensorSelfIso k G i).trans
        ((gradedFiniteProjectiveModules A).ι.mapBiprod Q Q₂).symm)
    rw [LaurentK0.of_congr.{max u w} _ e, LaurentK0.of_conflation.{max u w} _
      (ExactStructure.conflation_biprodShortComplex
        (gradedFiniteProjectiveModulesExactStructure A).toExactStructure Q Q₂), hshift 2]
    simp [LaurentPolynomial.T_pow, add_smul]
  by_cases hadj : G.Adj i j
  · rw [LaurentK0.of_congr.{max u w} _ (ObjectProperty.isoMk _
      (Y := ⟨(P i).shiftObj 1, gradedFiniteProjectiveModules_shiftObj hP 1⟩)
      (zigzagBraidProjectiveTensorAdjIso k G hadj.symm)),
      G.deformedCartanEntry_of_adj _ hadj]
    exact hshift 1
  · have hZ := IsZero.of_full_of_faithful_of_isZero (gradedFiniteProjectiveModules A).ι
      ⟨_, gradedFiniteProjectiveModules_zigzagBraidProjectiveTensor k G i j⟩
      (isZero_zigzagBraidProjectiveTensor k G hij hadj)
    rw [← LaurentK0.ofExactK0_exactK0_of.{max u w}, ExactK0.of_eq_zero_of_isZero.{max u w} hZ]
    simp [G.deformedCartanEntry_of_not_adj _ hij hadj]

end CommRing

/-! ### The Artin group action -/

variable [Field k] [Fintype V] [DecidableEq V]

/-- **The action of the graph's Artin group on `K₀^gr(proj Z)`.** The standard generator at `i`
acts by the deformed simple reflection at `q`, in the basis of vertex-projective classes; by
`TauCeti.zigzagBraidK0Action_gen_zigzagAlgebraGradedProjectiveClass` it sends `[P_j]` to the
Euler class of the braid complex `B_i ⊗_Z P_j`. -/
def zigzagBraidK0Action :
    TauCeti.ArtinGroup G.coxeterMatrix →*
      (LaurentK0.{max u w} (gradedFiniteProjectiveModulesExactStructure A) ≃ₗ[LaurentPolynomial ℤ]
        LaurentK0.{max u w} (gradedFiniteProjectiveModulesExactStructure A)) :=
  (LinearEquiv.autCongr
    (zigzagAlgebraGradedProjectiveClassBasis k G).equivFun.symm).toMonoidHom.comp
      (G.deformedReflectionRepresentation (LaurentPolynomial.isUnit_T 1).unit)

/-- The standard generator at `i` acts by the deformed reflection at `q` in vertex-projective
coordinates. -/
theorem zigzagBraidK0Action_gen_apply (i : V)
    (x : LaurentK0.{max u w} (gradedFiniteProjectiveModulesExactStructure A)) :
    zigzagBraidK0Action k G (TauCeti.ArtinGroup.gen G.coxeterMatrix i) x =
      (zigzagAlgebraGradedProjectiveClassBasis k G).equivFun.symm
        (G.deformedReflection (LaurentPolynomial.isUnit_T 1).unit i
          ((zigzagAlgebraGradedProjectiveClassBasis k G).equivFun x)) := by
  rw [zigzagBraidK0Action, MonoidHom.comp_apply,
    SimpleGraph.deformedReflectionRepresentation_gen, MulEquiv.coe_toMonoidHom,
    LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_symm]

/-- **The braid complex acts on `K₀^gr(proj Z)` by its Euler class**: the standard generator at
`i` sends `[P_j]` to `[Z ⊗_Z P_j] - [U_i ⊗_Z P_j]`, the Euler class of `B_i ⊗_Z P_j`, whose
terms sit in cohomological degrees `0` and `-1`. -/
theorem zigzagBraidK0Action_gen_zigzagAlgebraGradedProjectiveClass (i j : V) :
    zigzagBraidK0Action k G (TauCeti.ArtinGroup.gen G.coxeterMatrix i)
        (zigzagAlgebraGradedProjectiveClass k G j) =
      LaurentK0.of.{max u w} (gradedFiniteProjectiveModulesExactStructure A)
          ⟨_, gradedFiniteProjectiveModules_zigzagBraidProjectiveUnitTensor k G j⟩ -
        LaurentK0.of.{max u w} (gradedFiniteProjectiveModulesExactStructure A)
          ⟨_, gradedFiniteProjectiveModules_zigzagBraidProjectiveTensor k G i j⟩ := by
  have hj : (zigzagAlgebraGradedProjectiveClassBasis k G).equivFun
      (zigzagAlgebraGradedProjectiveClass k G j) = Pi.single j 1 := by
    rw [Module.Basis.equivFun_apply, zigzagAlgebraGradedProjectiveClassBasis_repr_class,
      Finsupp.single_eq_pi_single]
  rw [zigzagBraidK0Action_gen_apply, hj, laurentK0_of_zigzagBraidProjectiveUnitTensor,
    laurentK0_of_zigzagBraidProjectiveTensor]
  simp only [SimpleGraph.deformedReflection_apply, SimpleGraph.deformedCartanRow_single,
    map_sub, map_smul, Basis.equivFun_symm_single, zigzagAlgebraGradedProjectiveClassBasis_apply,
    IsUnit.unit_spec]

end TauCeti
