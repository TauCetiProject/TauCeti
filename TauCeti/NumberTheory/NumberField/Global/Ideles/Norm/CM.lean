/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.Global.Ideles.GaloisAction
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
import TauCeti.NumberTheory.ClassFieldTheory.Global.Ideles.Hilbert90
import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealSubfield
import TauCeti.NumberTheory.NumberField.Global.Ideles.GaloisDescent
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Galois

/-!
# The norm-one ideles of a CM field

The kernel of the idele norm to the maximal real subfield consists of the ideles satisfying
`x * conj(x) = 1`. These are the adelic points of the norm-one torus. Division by the conjugate
is a continuous surjection onto this kernel, so pullback distinguishes characters of the torus.

The applications are those of `New.divStar_surjective`,
`New.exists_snd_div_divStar_finIdeleIncl_eq_one` and `New.AutChar.baseChange_injective` in
`Lib/ClassField/HeckeCharacter/Basic.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open IsDedekindDomain NumberField NumberField.IsCMField
open scoped AdeleGaloisAction

namespace TauCeti.GlobalNumberFields

/-- The ideles of relative norm one over the maximal real subfield. For a CM field this is the
subgroup of adelic points of its norm-one torus. -/
noncomputable def cmNormOneIdeles (E : Type) [Field E] [NumberField E] :
    Subgroup (IdeleGroup (𝓞 E) E) := (ideleNormMap (maximalRealSubfield E) E).toMonoidHom.ker

variable {E : Type} [Field E] [NumberField E]

/-- An idele belongs to `cmNormOneIdeles` exactly when its relative norm is one. -/
theorem mem_cmNormOneIdeles_iff_ideleNormMap_eq_one {x : IdeleGroup (𝓞 E) E} :
    x ∈ cmNormOneIdeles E ↔ ideleNormMap (maximalRealSubfield E) E x = 1 := (Iff.rfl)

variable [IsCMField E]

/-- The adelic points of the CM norm-one torus are exactly the ideles with `x * conj(x) = 1`. -/
@[simp]
theorem mem_cmNormOneIdeles_iff {x : IdeleGroup (𝓞 E) E} :
    x ∈ cmNormOneIdeles E ↔ x * (complexConj E • x) = 1 := by
  rw [mem_cmNormOneIdeles_iff_ideleNormMap_eq_one]
  have h := ideleExtension_ideleNormMap_of_algebraMap_norm_eq_prod (maximalRealSubfield E) E E
    ![RingEquiv.refl E, (complexConj E).toRingEquiv]
    (fun a ↦ by simpa [Fin.prod_univ_two] using algebraMap_norm_eq_mul_complexConj a) x
  rw [← (ideleExtension_injective (maximalRealSubfield E) E).eq_iff, map_one, h]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ideleExtension_self, MonoidHom.id_apply, adeleEquiv_refl]
  have hone : Units.map (RingEquiv.refl (AdeleRing (𝓞 E) E)).toMonoidHom x = x :=
    Units.ext (RingEquiv.refl_apply _ _)
  have hconj : Units.map (adeleEquiv E E (complexConj E).toRingEquiv).toMonoidHom x =
      complexConj E • x := by
    apply Units.ext
    rw [coe_idele_smul, adeleGaloisAction_apply]
    rfl
  rw [hone, hconj]

/-- Division by the complex conjugate, as a continuous homomorphism from the ideles of a CM
field to the adelic points of its norm-one torus. -/
noncomputable def ideleDivConj : IdeleGroup (𝓞 E) E →ₜ* cmNormOneIdeles E where
  toFun y := ⟨y / (complexConj E • y), mem_cmNormOneIdeles_iff_ideleNormMap_eq_one.2
    ((ideleNormMap_eq_one_iff_exists_div_smul
      (fun τ ↦ by simp [zpowers_complexConj_eq_top]) _).2 ⟨y, rfl⟩)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul, smul_mul', mul_div_mul_comm])
  continuous_toFun := by
    exact (continuous_id.div' (continuous_idele_smul (complexConj E))).subtype_mk _

/-- The image under `ideleDivConj` has underlying idele `y / conj(y)`. -/
@[simp]
theorem coe_ideleDivConj_apply (y : IdeleGroup (𝓞 E) E) :
    (ideleDivConj y : IdeleGroup (𝓞 E) E) = y / (complexConj E • y) := (rfl)

/-- Every adelic point of the CM norm-one torus is a quotient by complex conjugation. -/
theorem ideleDivConj_surjective : Function.Surjective (ideleDivConj (E := E)) := by
  intro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := (ideleNormMap_eq_one_iff_exists_div_smul (σ := complexConj E)
    (fun τ ↦ by simp [zpowers_complexConj_eq_top]) x).1
      (mem_cmNormOneIdeles_iff_ideleNormMap_eq_one.1 hx)
  exact ⟨y, Subtype.ext ((coe_ideleDivConj_apply y).trans hy)⟩

/-- Pullback along `ideleDivConj` distinguishes continuous characters of the norm-one torus. -/
theorem injective_comp_ideleDivConj {A : Type*} [Monoid A] [TopologicalSpace A] :
    Function.Injective fun χ : cmNormOneIdeles E →ₜ* A ↦ χ.comp ideleDivConj := by
  intro χ ψ h
  ext x
  obtain ⟨y, rfl⟩ := ideleDivConj_surjective x
  exact DFunLike.congr_fun h y

/-- To obtain the finite part of an adelic point of the norm-one torus, it suffices to divide
a finite idele by its conjugate. -/
theorem exists_finiteIdele_div_conj_eq (x : cmNormOneIdeles E) :
    ∃ y : (FiniteAdeleRing (𝓞 E) E)ˣ,
      y / Units.map (finiteAdeleGaloisAction (maximalRealSubfield E) E (complexConj E) : _ →* _) y =
        IdeleGroup.toFiniteIdele (𝓞 E) E x := by
  obtain ⟨y, rfl⟩ := ideleDivConj_surjective x
  refine ⟨IdeleGroup.toFiniteIdele (𝓞 E) E y, ?_⟩
  rw [coe_ideleDivConj_apply, map_div, toFiniteIdele_smul]

end TauCeti.GlobalNumberFields
