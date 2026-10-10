/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Character
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.TensorPower
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Character
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational

/-!
# Weight multiplicities and highest-weight lines of Weyl modules

The multiplicity of a nonnegative integer weight in a Weyl module is the Kostka number
counting semistandard tableaux of that content. In particular, the highest weight, given by
the row lengths of the shape, has multiplicity one. Determinant twisting gives the same
one-dimensional highest-weight space for the rational Weyl module of every dominant weight.

The weight decomposition descends from the tensor power through its Young-symmetrizer map.
The multiplicities follow from the existing Schur character formula and independence of torus
characters. Together with the dominance bounds and irreducibility, this supplies the highest-weight
line used to compare concrete Weyl modules with highest-weight modules.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lectures 6 and 15.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter I, §5.
-/

public section

open Matrix

namespace TauCeti

universe u

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-- The integer weight spaces of a Weyl module form an internal direct sum. -/
theorem isInternal_weightSpace_weylRepOfShape (μ : YoungDiagram) :
    DirectSum.IsInternal fun l : Fin n → ℤ =>
      weightSpace (W := (weylModuleOfShape k n μ).toSubmodule) (weylRepOfShape k n μ) l := by
  classical
  let a := YoungTableau.youngSymmetrizerOver k
    (StandardYoungTableau.rowSuperstandard μ).toTableau
  let A := permTensorActionAlgHom k n μ.card a
  let q : Representation.IntertwiningMap (tensorPowerRep k n μ.card)
      (weylRepOfShape k n μ) :=
    { toLinearMap := A.codRestrict (weylModuleOfShape k n μ).toSubmodule (fun v => by
        rw [weylModuleOfShape_toSubmodule]
        exact LinearMap.mem_range.mpr ⟨v, rfl⟩)
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, weylRepOfShape_apply_coe]
        exact congrArg (fun f : Module.End k _ => f v)
          (commute_permTensorActionAlgHom_tensorPowerRep k n μ.card a g).eq }
  have hq : Function.Surjective q := by
    intro w
    have hw : w.val ∈ LinearMap.range A := by
      simpa only [weylModuleOfShape_toSubmodule] using w.property
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, Subtype.ext hv⟩
  exact isInternal_weightSpace_of_iSup_eq_top weightChar_injective
    (q.iSup_weightSpace_eq_top_of_surjective hq iSup_weightSpace_tensorPowerRep_eq_top)

/-- The dimension of a Weyl-module weight space is the number of semistandard tableaux
of the given content. The content is a natural exponent vector read as an integer weight. -/
theorem finrank_weightSpace_weylRepOfShape (μ : YoungDiagram) (d : Fin n →₀ ℕ) :
    Module.finrank k (weightSpace (W := (weylModuleOfShape k n μ).toSubmodule)
      (weylRepOfShape k n μ) (fun i => (d i : ℤ))) =
        diagramKostkaNumber μ (Finsupp.mapDomain Fin.val d) := by
  have h := Representation.coeff_eq_finrank_weightSpace_of_character_diagGL
    (W := (weylModuleOfShape k n μ).toSubmodule) (weylRepOfShape k n μ)
    (isInternal_weightSpace_weylRepOfShape k n μ).submodule_iSup_eq_top
    (diagramSchurPoly n k μ) (char_weylRepOfShape_diagonal_eq_eval_diagramSchurPoly k n μ) d
  rw [coeff_diagramSchurPoly] at h
  exact Nat.cast_injective h.symm

/-- The highest-weight space of a nonzero Weyl module is one-dimensional. -/
@[simp]
theorem finrank_weightSpace_weylRepOfShape_weightOfShape (μ : YoungDiagram)
    (hμ : μ.colLen 0 ≤ n) :
    Module.finrank k (weightSpace (W := (weylModuleOfShape k n μ).toSubmodule)
      (weylRepOfShape k n μ) (weightOfShape n μ : Fin n → ℤ)) = 1 := by
  have he : (fun i : Fin n => ((rowLenWeight n μ) i : ℤ)) =
      (weightOfShape n μ : Fin n → ℤ) := by
    ext i
    simp [rowLenWeight_apply, weightOfShape_apply]
  rw [← he, finrank_weightSpace_weylRepOfShape, mapDomain_rowLenWeight hμ,
    diagramKostkaNumber_rowLen]

/-- For every dominant integer weight, the rational Weyl module has a one-dimensional
weight space at that weight, including weights with negative entries. -/
theorem finrank_weightSpace_rationalWeylRep_self (l : DominantWeight n) :
    Module.finrank k (weightSpace (W := (weylModuleOfShape k n l.detShiftShape).toSubmodule)
      (rationalWeylRep k n l) (l : Fin n → ℤ)) = 1 := by
  rw [weightSpace_rationalWeylRep]
  have he : (l : Fin n → ℤ) - (fun _ => l.detShift) =
      (weightOfShape n l.detShiftShape : Fin n → ℤ) := by
    rw [DominantWeight.weightOfShape_detShiftShape]
    ext i
    simp [DominantWeight.shift_apply, sub_eq_add_neg]
  rw [he]
  exact finrank_weightSpace_weylRepOfShape_weightOfShape k n _ l.colLen_zero_detShiftShape_le

end TauCeti
