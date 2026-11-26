/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Basic
public import TauCeti.NumberTheory.NumberField.CMField.Basic
import TauCeti.FieldTheory.IsAlgClosed.AlgebraicEmbedding

/-!
# The reflex field is a CM field

Let `Φ` be a CM type on a nonempty finite product `E` of CM number fields, or more generally on a
finite-dimensional `ℚ`-algebra `E` with a complex embedding on which every automorphism `σ` of
`ℂ` commutes with complex conjugation (`TauCeti.CMType.StarCompCommute`). Its reflex field
`E* ⊆ ℂ` is a CM field.

Complex conjugation `ι` maps the type trace of `Φ` to that of the complementary type `ιΦ`, which
has the same reflex field, so `ι` restricts to an automorphism of `E*`. For `σ ∈ Aut(ℂ)` the type
trace of `σΦ` is `σ ∘ typeTrace_Φ`, and `ι(σΦ) = σ(ιΦ)`, so `σ` and `ι` agree after composing in
either order on the type traces, hence on all of `E*`. Every complex embedding of `E*` extends to
an automorphism of `ℂ`, so the restriction of `ι` is the complex conjugation of every complex
embedding of `E*`. It is not the identity, since `ιΦ ≠ Φ` and `ι` fixes `E*` pointwise only if it
preserves `Φ` (`TauCeti.CMType.mem_fixingSubgroup_reflexField_iff`). Hence `E*` is totally
complex, and CM by `TauCeti.NumberField.IsCMField.of_forall_isConj`.

## Main definitions

* `TauCeti.CMType.reflexFieldConj Φ`: complex conjugation restricted to the reflex field.

## Main results

* `TauCeti.CMType.reflexFieldConj_apply_apply`: complex conjugation on `E*` is an involution.
* `TauCeti.CMType.apply_conj_eq_conj_apply`: every `σ ∈ Aut(ℂ)` commutes with complex
  conjugation on the reflex field.
* `TauCeti.CMType.isConj_reflexFieldConj`: complex conjugation on `E*` is the conjugation of every
  complex embedding of `E*`.
* `TauCeti.CMType.isCMField_reflexField`: the reflex field is a CM field, an instance.
* `TauCeti.CMType.complexConj_reflexField_apply`: its complex conjugation is
  `TauCeti.CMType.reflexFieldConj`.
* `TauCeti.CMType.reflexField_isCMField`: the reflex field of a CM type on a nonempty finite
  product of CM number fields is a CM number field.

## References

* J. S. Milne, *Complex Multiplication*, Proposition 1.18, p.14.
-/

public section

open NumberField ComplexConjugate ComplexEmbedding

namespace TauCeti.CMType

variable {E : Type*} [CommRing E]

section FiniteEmbeddings

variable [Finite (E →+* ℂ)]

/-- Complex conjugation maps the reflex field into itself: it sends the type trace of `Φ` to that
of `ιΦ`, which has the same reflex field. -/
theorem conj_mem_reflexField (Φ : CMType E) {x : ℂ} (hx : x ∈ Φ.reflexField) :
    conj x ∈ Φ.reflexField := by
  have : Φ.reflexField ≤ Φ.reflexField.comap (Complex.conjAe.restrictScalars ℚ : ℂ →ₐ[ℚ] ℂ) :=
    reflexField_le_iff.mpr fun a ↦ by simpa using (star Φ).typeTrace_mem_reflexField a
  exact this hx

/-- **Complex conjugation on the reflex field**, the automorphism `x ↦ conj x` of `E*`. -/
noncomputable def reflexFieldConj (Φ : CMType E) : Gal(Φ.reflexField/ℚ) where
  toFun x := ⟨conj (x : ℂ), Φ.conj_mem_reflexField x.property⟩
  invFun x := ⟨conj (x : ℂ), Φ.conj_mem_reflexField x.property⟩
  left_inv x := Subtype.ext (Complex.conj_conj _)
  right_inv x := Subtype.ext (Complex.conj_conj _)
  map_mul' x y := Subtype.ext (map_mul conj (x : ℂ) y)
  map_add' x y := Subtype.ext (map_add conj (x : ℂ) y)
  commutes' r := Subtype.ext (by simp)

@[simp]
theorem coe_reflexFieldConj_apply (Φ : CMType E) (x : Φ.reflexField) :
    (Φ.reflexFieldConj x : ℂ) = conj (x : ℂ) :=
  (rfl)

/-- Complex conjugation on the reflex field is an involution. -/
@[simp]
theorem reflexFieldConj_apply_apply (Φ : CMType E) (x : Φ.reflexField) :
    Φ.reflexFieldConj (Φ.reflexFieldConj x) = x :=
  Subtype.ext (Complex.conj_conj _)

/-- Every automorphism `σ` of `ℂ` commutes with complex conjugation on the reflex field: on a type
trace both `σ ∘ ι` and `ι ∘ σ` give the type trace of `σ(ιΦ) = ι(σΦ)`. -/
theorem apply_conj_eq_conj_apply [StarCompCommute E] (Φ : CMType E) (σ : RingAut ℂ) {x : ℂ}
    (hx : x ∈ Φ.reflexField) : σ (conj x) = conj (σ x) := by
  let f : ℂ →ₐ[ℚ] ℂ := (σ : ℂ →+* ℂ).toRatAlgHom
  let c : ℂ →ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  -- Both composites are `ℚ`-algebra maps on `E*`, so it suffices to compare them on type traces.
  have h : (f.comp c).comp Φ.reflexField.val = (c.comp f).comp Φ.reflexField.val :=
    IntermediateField.algHom_ext_of_eq_adjoin ℚ Φ.reflexField_def <| by
      rintro _ ⟨a, rfl⟩
      simpa [f, c] using (congrArg (typeTrace · a) (star_smul σ Φ)).symm
  simpa [f, c] using AlgHom.congr_fun h ⟨x, hx⟩

/-- Complex conjugation on the reflex field is the conjugation of every complex embedding `ρ` of
the reflex field: `conj ∘ ρ = ρ ∘ ι`, since `ρ` extends to an automorphism of `ℂ`. -/
theorem isConj_reflexFieldConj [StarCompCommute E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (Φ : CMType E) (ρ : Φ.reflexField →+* ℂ) : IsConj ρ Φ.reflexFieldConj := by
  obtain ⟨σ, hσ⟩ := IntermediateField.exists_ringEquiv_apply_eq_of_isAlgebraic Φ.reflexField ρ
  refine RingHom.ext fun x ↦ ?_
  simpa [conjugate_coe_eq, ← hσ] using (Φ.apply_conj_eq_conj_apply σ x.property).symm

/-- Complex conjugation is not the identity on the reflex field of a CM type on a ring with a
complex embedding: it would then preserve `Φ`, whereas `ιΦ` is the complement of `Φ`. -/
theorem reflexFieldConj_ne_one [Nonempty (E →+* ℂ)] (Φ : CMType E) : Φ.reflexFieldConj ≠ 1 := by
  intro h
  have hfix : (Complex.conjAe.restrictScalars ℚ : ℂ ≃ₐ[ℚ] ℂ) ∈ Φ.reflexField.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    simpa using congrArg Subtype.val (AlgEquiv.ext_iff.mp h ⟨x, hx⟩)
  obtain ⟨φ⟩ := ‹Nonempty (E →+* ℂ)›
  have := (Φ.mem_fixingSubgroup_reflexField_iff _).mp hfix φ
  rw [show ((Complex.conjAe.restrictScalars ℚ : ℂ ≃ₐ[ℚ] ℂ) : ℂ →+* ℂ).comp φ = star φ from
    RingHom.ext fun _ ↦ by simp [RingHom.star_apply], star_mem_iff] at this
  exact (iff_not_self this.symm).elim

end FiniteEmbeddings

section FiniteDimensional

variable [Algebra ℚ E] [FiniteDimensional ℚ E] [StarCompCommute E] [Nonempty (E →+* ℂ)]

/-- The reflex field of a CM type on a finite-dimensional `ℚ`-algebra with a complex embedding,
on which automorphisms of `ℂ` commute with complex conjugation, is totally complex. -/
instance isTotallyComplex_reflexField (Φ : CMType E) : IsTotallyComplex Φ.reflexField :=
  ⟨fun w ↦ InfinitePlace.isComplex_iff.mpr <|
    (isConj_ne_one_iff (Φ.isConj_reflexFieldConj w.embedding)).mp Φ.reflexFieldConj_ne_one⟩

/-- **The reflex field is a CM field.** For a CM type on a finite-dimensional `ℚ`-algebra with a
complex embedding, on which automorphisms of `ℂ` commute with complex conjugation, such as a
nonzero finite product of CM fields, the reflex field is a CM field, with complex conjugation
`TauCeti.CMType.reflexFieldConj`. -/
instance isCMField_reflexField (Φ : CMType E) : IsCMField Φ.reflexField :=
  TauCeti.NumberField.IsCMField.of_forall_isConj _ Φ.isConj_reflexFieldConj

/-- The complex conjugation `NumberField.IsCMField.complexConj` of the CM field `E*` is
`TauCeti.CMType.reflexFieldConj`, the restriction of complex conjugation of `ℂ`. -/
@[simp]
theorem complexConj_reflexField_apply (Φ : CMType E) (x : Φ.reflexField) :
    NumberField.IsCMField.complexConj Φ.reflexField x = Φ.reflexFieldConj x :=
  Subtype.ext <| by
    simpa only [AlgHom.coe_toRingHom, IntermediateField.coe_val, coe_reflexFieldConj_apply] using
      NumberField.IsCMField.complexEmbedding_complexConj _ (Φ.reflexField.val : _ →+* ℂ) x

end FiniteDimensional

/-- **The reflex field of a CM type on a CM algebra is a CM number field.** For a nonempty finite
product `E = ∏ i, F i` of CM number fields and a CM type `Φ` on `E`, the reflex field `E*` is a
number field and a CM field. -/
theorem reflexField_isCMField {ι : Type*} [Finite ι] [Nonempty ι] (F : ι → Type*)
    [∀ i, Field (F i)] [∀ i, NumberField (F i)] [∀ i, IsCMField (F i)] (Φ : CMType (∀ i, F i)) :
    NumberField Φ.reflexField ∧ IsCMField Φ.reflexField := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨φ⟩ := (inferInstance : Nonempty (F i →+* ℂ))
  have : Nonempty ((∀ i, F i) →+* ℂ) := ⟨φ.comp (Pi.evalRingHom F i)⟩
  exact ⟨inferInstance, inferInstance⟩

end TauCeti.CMType
