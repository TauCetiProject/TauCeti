/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.AlgebraicWeight.Representation
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Dual

/-!
# Contragredients of labelled coefficient representations

For an embedding-indexed dominant weight, the contragredient coefficient representation is the
coefficient representation of the pointwise dual weight. Each label is retained, and the
coordinates within each label are reversed and negated. This gives the dual coefficient
representation on the complex points of the Weil restriction as well as on the split tuple
of general linear groups.

## References

* P. Allen et al., *Potential automorphy over CM fields*, Ann. of Math. 197 (2023), §2.2.
-/

public section

namespace TauCeti.EmbeddingWeight

open Matrix

variable {ι : Type*} {n : ℕ}

/-- For a finite set of labels, the contragredient coefficient representation is equivalent to
the coefficient representation of the pointwise dual weight. -/
theorem nonempty_equiv_dual_coefficientRep [Finite ι] (a : EmbeddingWeight ι n) :
    Nonempty (a.coefficientRep.dual.Equiv a.dual.coefficientRep) := by
  let _ : ∀ i, AddCommGroup (weylModuleOfShape ℂ n (a i).detShiftShape).toSubmodule :=
    fun _ ↦ inferInstance
  let _ : ∀ i, AddCommGroup (weylModuleOfShape ℂ n (a.dual i).detShiftShape).toSubmodule :=
    fun _ ↦ inferInstance
  let _ : ∀ i, Module.Finite ℂ (weylModuleOfShape ℂ n (a i).detShiftShape).toSubmodule :=
    fun _ ↦ inferInstance
  let _ : ∀ i, Module.Free ℂ (weylModuleOfShape ℂ n (a i).detShiftShape).toSubmodule :=
    fun _ ↦ inferInstance
  have h (i : ι) : Nonempty ((rationalWeylRep ℂ n (a i)).dual.Equiv
      (rationalWeylRep ℂ n (a.dual i))) := by
    rw [EmbeddingWeight.dual_apply]
    exact nonempty_equiv_dual_rationalWeylRep (a i)
  rw [coefficientRep_eq, coefficientRep_eq]
  exact ⟨(Representation.piExternalTensorDualEquiv
    (fun i ↦ rationalWeylRep ℂ n (a i))).symm.trans
      (Representation.Equiv.piExternalTensor fun i ↦ (h i).some)⟩

open WithConv TauCeti.Algebra TauCeti.Algebra.WeilRestriction

/-- On the complex points of the Weil restriction of `GLₙ`, the dual of `Ξ_a` is equivalent
to `Ξ_{a.dual}`. -/
theorem nonempty_equiv_dual_weilRestrictionRep {F : Type*} [Field F] [NumberField F]
    (a : EmbeddingWeight (F →+* ℂ) n) :
    Nonempty (a.weilRestrictionRep.dual.Equiv a.dual.weilRestrictionRep) := by
  let _ : Algebra.Etale ℚ F := Algebra.Etale.of_isSeparable _ _
  obtain ⟨e⟩ := nonempty_equiv_dual_coefficientRep a
  refine ⟨.mk e.toLinearEquiv fun g ↦ ?_⟩
  have hinv : (fun τ : F →+* ℂ ↦ generalLinearSplitPoints ℚ F ℂ n g⁻¹ τ.toRatAlgHom) =
      (fun τ : F →+* ℂ ↦ generalLinearSplitPoints ℚ F ℂ n g τ.toRatAlgHom)⁻¹ := by
    funext τ
    simp
  rw [Representation.dual_apply, weilRestrictionRep_apply, weilRestrictionRep_apply, hinv]
  exact e.toIntertwiningMap.isIntertwining'
    (fun τ ↦ generalLinearSplitPoints ℚ F ℂ n g τ.toRatAlgHom)

end TauCeti.EmbeddingWeight
