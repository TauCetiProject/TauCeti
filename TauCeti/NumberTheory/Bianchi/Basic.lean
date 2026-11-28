/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Congruence.Map

/-!
# Bianchi groups and their principal congruence subgroups

For a field `F` embedded in `ℂ`, `bianchi F ι` is the image of `SL(2, 𝓞 F)` in `PSL(2, ℂ)`.
For an ideal `I` of `𝓞 F`, `bianchiGamma F ι I` is the image of the kernel of reduction
`SL(2, 𝓞 F) → SL(2, 𝓞 F ⧸ I)`. It is normal in the Bianchi group by
`Subgroup.normal_subgroupOf_map_range`. To use the instance, rewrite the normality goal with
`bianchiGamma_def` and `bianchi_def`, then use `infer_instance`.

These algebraic constructions require no degree or signature assumption. Their classical
geometric application is to imaginary quadratic fields. Changing the field by an isomorphism
preserves the Bianchi group and transports the level of its congruence subgroup.

The congruence subgroup is defined using reduction in the special linear group. Over a quotient
ring the centre can contain scalars other than `±1`, so reduction in the projective special
linear group can have a larger kernel.
-/

public section

open Matrix NumberField
open scoped MatrixGroups

namespace TauCeti

variable (F : Type*) [Field F] (ι : F →+* ℂ)

/-- The homomorphism sending an integral special linear matrix to its complex projective class. -/
noncomputable def bianchiMap : SL(2, 𝓞 F) →* PSL(2, ℂ) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, ℂ))).comp
    (Matrix.SpecialLinearGroup.map (ι.comp (algebraMap (𝓞 F) F)))

/-- The complex projective class of an integral special linear matrix is computed entrywise. -/
theorem bianchiMap_apply (A : SL(2, 𝓞 F)) :
    bianchiMap F ι A =
      (Matrix.SpecialLinearGroup.map (ι.comp (algebraMap (𝓞 F) F)) A : PSL(2, ℂ)) := by
  rw [bianchiMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply]

/-- The Bianchi group for the embedding `ι`: the image of `SL(2, 𝓞 F)` in `PSL(2, ℂ)`. -/
noncomputable def bianchi : Subgroup PSL(2, ℂ) :=
  (bianchiMap F ι).range

/-- The Bianchi group is the range of the homomorphism on integral matrices. -/
theorem bianchi_def : bianchi F ι = (bianchiMap F ι).range := (rfl)

/-- Membership in a Bianchi group is witnessed by an integral special linear matrix. -/
@[simp] theorem mem_bianchi_iff {g : PSL(2, ℂ)} :
    g ∈ bianchi F ι ↔ ∃ A : SL(2, 𝓞 F), bianchiMap F ι A = g := by
  rw [bianchi_def, MonoidHom.mem_range]

/-- The principal congruence subgroup of a Bianchi group, obtained from the kernel of reduction
in `SL(2, 𝓞 F)`. This definition also includes the zero and unit levels. -/
noncomputable def bianchiGamma (I : Ideal (𝓞 F)) : Subgroup PSL(2, ℂ) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker.map (bianchiMap F ι)

/-- The congruence subgroup is the image of the special linear reduction kernel. -/
theorem bianchiGamma_def (I : Ideal (𝓞 F)) :
    bianchiGamma F ι I =
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk I)).ker.map
        (bianchiMap F ι) := (rfl)

/-- A projective class is in the congruence subgroup exactly when it has an integral lift
reducing to the identity. -/
@[simp] theorem mem_bianchiGamma_iff {I : Ideal (𝓞 F)} {g : PSL(2, ℂ)} :
    g ∈ bianchiGamma F ι I ↔ ∃ A : SL(2, 𝓞 F),
      Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk I) A = 1 ∧ bianchiMap F ι A = g := by
  simp only [bianchiGamma_def, Subgroup.mem_map, MonoidHom.mem_ker]

/-- The congruence condition can be tested entrywise on a lift of the projective class. -/
theorem mem_bianchiGamma_iff_exists_entries {I : Ideal (𝓞 F)} {g : PSL(2, ℂ)} :
    g ∈ bianchiGamma F ι I ↔ ∃ A : SL(2, 𝓞 F),
      (∀ i j, A i j - (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) i j ∈ I) ∧
        bianchiMap F ι A = g := by
  simp only [bianchiGamma_def, Subgroup.mem_map,
    Matrix.SpecialLinearGroup.mem_ker_map_quotientMk_iff]

/-- Every principal congruence subgroup lies in its Bianchi group. -/
theorem bianchiGamma_le (I : Ideal (𝓞 F)) : bianchiGamma F ι I ≤ bianchi F ι := by
  rw [bianchiGamma_def, bianchi_def]
  exact Subgroup.map_le_range _ _

/-- Enlarging the level ideal enlarges the principal congruence subgroup. -/
theorem bianchiGamma_mono : Monotone (bianchiGamma F ι) := by
  intro I J h
  rw [bianchiGamma_def, bianchiGamma_def]
  exact Subgroup.map_mono (Matrix.SpecialLinearGroup.ker_map_quotientMk_mono h)

/-- The principal congruence subgroup at the zero ideal is trivial. -/
@[simp] theorem bianchiGamma_bot : bianchiGamma F ι ⊥ = ⊥ := by
  have h : (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (⊥ : Ideal (𝓞 F)))).ker = ⊥ :=
    MonoidHom.ker_eq_bot _ (Matrix.SpecialLinearGroup.map_injective
      (RingEquiv.quotientBot (𝓞 F)).symm.injective)
  simp [bianchiGamma_def, h]

/-- At the unit ideal every integral matrix satisfies the congruence condition. -/
@[simp] theorem bianchiGamma_top : bianchiGamma F ι ⊤ = bianchi F ι := by
  have h : (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (⊤ : Ideal (𝓞 F)))).ker = ⊤ := by
    ext A
    simp only [Matrix.SpecialLinearGroup.mem_ker_map_quotientMk_iff,
      Submodule.mem_top, implies_true, Subgroup.mem_top]
  rw [bianchiGamma_def, h, Subgroup.map_top, bianchi_def]

section ChangeOfField

variable {F} {K : Type*} [Field K]

/-- The Bianchi homomorphism for the composite embedding factors through the induced
isomorphism on integral special linear groups. -/
theorem bianchiMap_comp_ringEquiv (e : K ≃+* F) :
    bianchiMap K (ι.comp e.toRingHom) = (bianchiMap F ι).comp
      (Matrix.SpecialLinearGroup.mapEquiv (Fin 2)
        (RingOfIntegers.mapRingEquiv e)).toMonoidHom := by
  have h : (ι.comp e.toRingHom).comp (algebraMap (𝓞 K) K) =
      (ι.comp (algebraMap (𝓞 F) F)).comp (RingOfIntegers.mapRingEquiv e) := by
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      ← RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.mapRingEquiv_apply]
  simp only [bianchiMap, MonoidHom.comp_assoc, MulEquiv.toMonoidHom_eq_coe,
    Matrix.SpecialLinearGroup.toMonoidHom_mapEquiv, Matrix.SpecialLinearGroup.map_comp_map, h]

/-- The Bianchi group is unchanged on replacing the field by an isomorphic field and composing
the embedding with that isomorphism. In particular it is invariant under field automorphisms. -/
theorem bianchi_comp_ringEquiv (e : K ≃+* F) :
    bianchi K (ι.comp e.toRingHom) = bianchi F ι := by
  rw [bianchi_def, bianchi_def, bianchiMap_comp_ringEquiv]
  exact MonoidHom.range_comp_of_surjective _ _
    (Matrix.SpecialLinearGroup.mapEquiv (Fin 2) (RingOfIntegers.mapRingEquiv e)).surjective

/-- Changing the field by an isomorphism transports the ideal defining a Bianchi congruence
subgroup. For an automorphism this is the change-of-embedding formula. -/
theorem bianchiGamma_comp_ringEquiv (e : K ≃+* F) (I : Ideal (𝓞 K)) :
    bianchiGamma K (ι.comp e.toRingHom) I =
      bianchiGamma F ι (I.map (RingOfIntegers.mapRingEquiv e)) := by
  simp only [bianchiGamma_def, bianchiMap_comp_ringEquiv, ← Subgroup.map_map,
    MulEquiv.toMonoidHom_eq_coe,
    Matrix.SpecialLinearGroup.toMonoidHom_mapEquiv,
    Matrix.SpecialLinearGroup.map_ker_map_quotientMk]

end ChangeOfField

end TauCeti
