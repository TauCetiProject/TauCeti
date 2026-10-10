/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.Standard
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# The standard representation of S₃ in characteristic three

In characteristic three, the constant vectors belong to the two-dimensional standard
representation of S₃. The quotient by this trivial line is the sign representation.
The maps below give the resulting exact sequence explicitly: the inclusion sends a scalar
to the constant vector, and the quotient map takes the difference of coordinates zero and one.
Over a field, this sequence determines the composition factors. Over any nontrivial
coefficient ring of characteristic three, it has no equivariant section.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

open CategoryTheory

namespace TauCeti

variable (k : Type*) [CommRing k] [CharP k 3]

/-- The constant-vector inclusion into the standard S₃ representation in characteristic three. -/
noncomputable def standardThreeTrivialInclusion :
    (Representation.trivial k (Equiv.Perm (Fin 3)) k).IntertwiningMap
      (standardRepresentation k (Fin 3)) where
  toLinearMap :=
    { toFun := fun c ↦ ⟨c • permutationSum k (Fin 3), by
        rw [toSubmodule_augmentationSubrepresentation, LinearMap.mem_ker]
        rw [map_smul, sumCoords_basis_permutationSum]
        simp only [Fintype.card_fin]
        rw [CharP.cast_eq_zero k 3, smul_zero]⟩
      map_add' := fun _ _ ↦ Subtype.ext (add_smul _ _ _)
      map_smul' := fun _ _ ↦ Subtype.ext (smul_smul _ _ _).symm }
  isIntertwining' g := by
    ext c
    simp [coe_standardRepresentation_apply]

@[simp]
theorem coe_standardThreeTrivialInclusion_apply (c : k) :
    (standardThreeTrivialInclusion k c : MonoidAlgebra k (Fin 3)) =
      c • permutationSum k (Fin 3) := (rfl)

/-- The sign quotient of the standard S₃ representation in characteristic three. -/
noncomputable def standardThreeSignQuotient :
    (standardRepresentation k (Fin 3)).IntertwiningMap
      (Representation.ofLinearCharacter (signLinearCharacter k (Fin 3))) where
  toLinearMap := ((Finsupp.lapply (R := k) (M := k) (α := Fin 3) 0 - Finsupp.lapply 1).comp
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap).comp
      (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule.subtype
  isIntertwining' g := by
    ext v
    have hv := mem_augmentationSubrepresentation_iff.mp v.2
    have hv : v.val.coeff 0 + v.val.coeff 1 + v.val.coeff 2 = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hv
    have h3 : (3 : k) = 0 := CharP.cast_eq_zero k 3
    have hs : signLinearCharacter k (Fin 3) (finRotate 3) = 1 := by
      apply Units.ext
      have h : Equiv.Perm.sign (finRotate 3) = 1 := by decide
      simp [coe_signLinearCharacter_apply, h]
    rcases Equiv.Perm.fin_three_cases g with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [LinearMap.coe_comp, LinearMap.sub_apply, Function.comp_apply,
        Finsupp.lapply_apply, LinearEquiv.coe_coe, MonoidAlgebra.coeffLinearEquiv_apply,
        Submodule.coe_subtype, coe_standardRepresentation_apply,
        Representation.ofLinearCharacter_apply]
    · simp
    · simp [Representation.coeff_ofMulAction, Equiv.Perm.smul_def,
        signLinearCharacter_swap]
    · simp [Representation.coeff_ofMulAction, Equiv.Perm.smul_def,
        Equiv.swap_apply_def, signLinearCharacter_swap]
      linear_combination v.val.coeff 0 * h3 - hv
    · simp [Representation.coeff_ofMulAction, Equiv.Perm.smul_def,
        Equiv.swap_apply_def, signLinearCharacter_swap]
      linear_combination hv - v.val.coeff 1 * h3
    · have h0 : (finRotate 3)⁻¹ (0 : Fin 3) = 2 := by decide
      have h1 : (finRotate 3)⁻¹ (1 : Fin 3) = 0 := by decide
      simp [Representation.coeff_ofMulAction, Equiv.Perm.smul_def,
        hs, h0, h1]
      linear_combination hv - v.val.coeff 0 * h3
    · have h0 : finRotate 3 (0 : Fin 3) = 1 := by decide
      have h1 : finRotate 3 (1 : Fin 3) = 2 := by decide
      simp [Representation.coeff_ofMulAction, Equiv.Perm.smul_def,
        hs, h0, h1]
      linear_combination v.val.coeff 1 * h3 - hv

@[simp]
theorem standardThreeSignQuotient_apply
    (v : (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule) :
    standardThreeSignQuotient k v = (v : MonoidAlgebra k (Fin 3)).coeff 0 - v.val.coeff 1 :=
  (rfl)

/-- The constant-vector inclusion is injective. -/
theorem standardThreeTrivialInclusion_injective :
    Function.Injective (standardThreeTrivialInclusion k) := by
  intro a b h
  have hc := congrArg (fun v : (augmentationSubrepresentation k (Equiv.Perm (Fin 3))
    (Fin 3)).toSubmodule ↦ v.val.coeff 0) h
  simpa using hc

/-- The coordinate-difference quotient onto the sign line is surjective. -/
theorem standardThreeSignQuotient_surjective :
    Function.Surjective (standardThreeSignQuotient k) := by
  intro c
  refine ⟨⟨MonoidAlgebra.single 0 c - MonoidAlgebra.single 2 c, ?_⟩, ?_⟩
  · rw [toSubmodule_augmentationSubrepresentation, LinearMap.mem_ker]
    simp
  · simp

/-- The constant vectors are precisely the kernel of the sign quotient. -/
theorem exact_standardThreeTrivialInclusion_standardThreeSignQuotient :
    Function.Exact (standardThreeTrivialInclusion k) (standardThreeSignQuotient k) := by
  intro v
  constructor
  · intro hv
    have h01 : v.val.coeff 0 - v.val.coeff 1 = 0 := by simpa using hv
    have hsum := mem_augmentationSubrepresentation_iff.mp v.2
    have hsum : v.val.coeff 0 + v.val.coeff 1 + v.val.coeff 2 = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hsum
    have h02 : v.val.coeff 2 = v.val.coeff 0 := by
      have h3 : (3 : k) = 0 := CharP.cast_eq_zero k 3
      linear_combination hsum + h01 - v.val.coeff 0 * h3
    refine ⟨v.val.coeff 0, Subtype.ext ?_⟩
    ext i
    fin_cases i <;> simp [h02, sub_eq_zero.mp h01]
  · rintro ⟨c, rfl⟩
    simp

/-- The standard S₃ module is an extension of the sign line by the trivial line. -/
noncomputable def standardThreeSequence : ShortComplex (Rep k (Equiv.Perm (Fin 3))) :=
  ShortComplex.mk (Rep.ofHom (standardThreeTrivialInclusion k))
    (Rep.ofHom (standardThreeSignQuotient k)) (by
      apply Rep.hom_ext
      ext
      simp)

/-- The first term of the standard-module sequence is the trivial line. -/
@[simp]
theorem standardThreeSequence_X₁ :
    (standardThreeSequence k).X₁ = Rep.trivial k (Equiv.Perm (Fin 3)) k := (rfl)

/-- The middle term of the standard-module sequence is the standard representation. -/
@[simp]
theorem standardThreeSequence_X₂ :
    (standardThreeSequence k).X₂ = Rep.of (standardRepresentation k (Fin 3)) := (rfl)

/-- The last term of the standard-module sequence is the sign line. -/
@[simp]
theorem standardThreeSequence_X₃ :
    (standardThreeSequence k).X₃ =
      Rep.of (Representation.ofLinearCharacter (signLinearCharacter k (Fin 3))) := (rfl)

/-- The first map of the standard-module sequence is the constant-vector inclusion. -/
@[simp]
theorem standardThreeSequence_f :
    HEq (standardThreeSequence k).f (Rep.ofHom (standardThreeTrivialInclusion k)) := (HEq.rfl)

/-- The second map of the standard-module sequence is the coordinate-difference quotient. -/
@[simp]
theorem standardThreeSequence_g :
    HEq (standardThreeSequence k).g (Rep.ofHom (standardThreeSignQuotient k)) := (HEq.rfl)

/-- The explicit sequence with middle term the standard module is short exact. -/
theorem standardThreeSequence_shortExact : (standardThreeSequence k).ShortExact := by
  dsimp only [standardThreeSequence]
  exact ShortComplex.ShortExact.mk'
    ((Rep.exact_iff_function_exact _).2
      (exact_standardThreeTrivialInclusion_standardThreeSignQuotient k))
    ((Rep.mono_iff_injective _).2 (standardThreeTrivialInclusion_injective k))
    ((Rep.epi_iff_surjective _).2 (standardThreeSignQuotient_surjective k))

/-- The sign quotient has no equivariant section over a nontrivial coefficient ring.
Thus the standard-module extension in characteristic three does not split. -/
theorem not_exists_rightInverse_standardThreeSignQuotient :
    ¬ ∃ s : (Representation.ofLinearCharacter (signLinearCharacter k (Fin 3))).IntertwiningMap
      (standardRepresentation k (Fin 3)),
      Function.RightInverse s (standardThreeSignQuotient k) := by
  let := CharP.nontrivial_of_char_ne_one (R := k) (v := 3) (by decide)
  rintro ⟨s, hs⟩
  let v := s (1 : k)
  have h0 : -v.val.coeff 0 = v.val.coeff 0 := by
    have h := congrArg (fun w : (augmentationSubrepresentation k (Equiv.Perm (Fin 3))
      (Fin 3)).toSubmodule ↦ w.val.coeff 0)
      (Representation.IntertwiningMap.isIntertwining _ _ s (Equiv.swap 1 2) 1)
    simpa [v, Representation.ofLinearCharacter_apply, signLinearCharacter_swap,
      coe_standardRepresentation_apply, Representation.coeff_ofMulAction,
      Equiv.Perm.smul_def, Equiv.swap_apply_def] using h
  have h2 : -v.val.coeff 2 = v.val.coeff 2 := by
    have h := congrArg (fun w : (augmentationSubrepresentation k (Equiv.Perm (Fin 3))
      (Fin 3)).toSubmodule ↦ w.val.coeff 2)
      (Representation.IntertwiningMap.isIntertwining _ _ s (Equiv.swap 0 1) 1)
    simpa [v, Representation.ofLinearCharacter_apply, signLinearCharacter_swap,
      coe_standardRepresentation_apply, Representation.coeff_ofMulAction,
      Equiv.Perm.smul_def, Equiv.swap_apply_def] using h
  have h3 : (3 : k) = 0 := CharP.cast_eq_zero k 3
  have hv0 : v.val.coeff 0 = 0 := by linear_combination v.val.coeff 0 * h3 + h0
  have hv2 : v.val.coeff 2 = 0 := by linear_combination v.val.coeff 2 * h3 + h2
  have hsum := mem_augmentationSubrepresentation_iff.mp v.2
  have hv1 : v.val.coeff 1 = 0 := by
    simpa [Fin.sum_univ_succ, hv0, hv2] using hsum
  have h : standardThreeSignQuotient k v = 1 := hs 1
  simp [hv0, hv1] at h

end TauCeti
