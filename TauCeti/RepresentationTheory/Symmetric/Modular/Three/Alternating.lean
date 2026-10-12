/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Standard
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Field.ZMod

/-!
# The two-dimensional simple representation of A₃ over 𝔽₂

Restrict the standard representation of S₃ to A₃. Over 𝔽₂ it is irreducible: the
three nonzero vectors of the augmentation plane form one orbit under the three-cycle.
This gives the nontrivial simple module needed for induction from the subgroup of order
three in modular S₃ calculations. Over a field containing a primitive cube root of unity,
the same restriction splits into two lines, so the coefficient field matters.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

namespace TauCeti

private theorem augmentation_plane_nonzero_orbit :
    ∀ v w : Fin 3 → ZMod 2, (∑ i, v i) = 0 → v ≠ 0 →
      (∑ i, w i) = 0 → w ≠ 0 →
      ∃ g : alternatingGroup (Fin 3), ∀ i, v ((g : Equiv.Perm (Fin 3))⁻¹ i) = w i := by
  decide

/-- A₃ acts transitively on the nonzero vectors of the standard representation over 𝔽₂. -/
private theorem exists_standardRepresentation_comp_alternatingGroup_eq
    (v w : (augmentationSubrepresentation (ZMod 2) (Equiv.Perm (Fin 3))
      (Fin 3)).toSubmodule) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : alternatingGroup (Fin 3),
      (standardRepresentation (ZMod 2) (Fin 3)).comp
        (alternatingGroup (Fin 3)).subtype g v = w := by
  have hsum (x : (augmentationSubrepresentation (ZMod 2) (Equiv.Perm (Fin 3))
      (Fin 3)).toSubmodule) : (∑ i, (x : MonoidAlgebra (ZMod 2) (Fin 3)).coeff i) = 0 := by
    simpa using mem_augmentationSubrepresentation_iff.mp x.property
  have hne (x : (augmentationSubrepresentation (ZMod 2) (Equiv.Perm (Fin 3))
      (Fin 3)).toSubmodule) (hx : x ≠ 0) :
      (fun i ↦ (x : MonoidAlgebra (ZMod 2) (Fin 3)).coeff i) ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    exact MonoidAlgebra.coeff_eq_zero.mp (Finsupp.ext fun i ↦ congrFun h i)
  obtain ⟨g, hg⟩ := augmentation_plane_nonzero_orbit _ _ (hsum v) (hne v hv)
    (hsum w) (hne w hw)
  refine ⟨g, Subtype.ext ?_⟩
  apply MonoidAlgebra.coeff_inj.mp
  apply Finsupp.ext
  intro i
  simpa [MonoidHom.comp_apply, coe_standardRepresentation_apply,
    Representation.coeff_ofMulAction, Equiv.Perm.smul_def] using hg i

/-- The standard S₃ representation restricted to A₃ is a two-dimensional simple
representation over 𝔽₂. -/
theorem isIrreducible_standardRepresentation_comp_alternatingGroup_zmod_two :
    Representation.IsIrreducible (k := ZMod 2) ((standardRepresentation (ZMod 2) (Fin 3)).comp
      (alternatingGroup (Fin 3)).subtype) := by
  have : Nontrivial (augmentationSubrepresentation (ZMod 2) (Equiv.Perm (Fin 3))
      (Fin 3)).toSubmodule := Module.nontrivial_of_finrank_pos (by
        rw [finrank_augmentationSubrepresentation]
        decide)
  refine ⟨fun U ↦ ?_⟩
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  have hne : U.toSubmodule ≠ ⊥ := fun h ↦ hU
    (Subrepresentation.toSubmodule_injective (h.trans Subrepresentation.toSubmodule_bot.symm))
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · rw [hw]
    exact U.toSubmodule.zero_mem
  obtain ⟨g, rfl⟩ := exists_standardRepresentation_comp_alternatingGroup_eq v w hv0 hw
  exact U.apply_mem_toSubmodule g hv

end TauCeti
