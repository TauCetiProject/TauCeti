/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.FieldTheory.IntermediateField.FieldRange
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.CMField
public import TauCeti.RingTheory.IntegralClosure.Subfield

/-!
# CM or totally real fields via the complex conjugations of a normal extension of `ℚ`

Let `Ω` be a normal extension of `ℚ`, such as an algebraic closure of `ℚ`. A *complex
conjugation* of `Ω` is an automorphism `c` of `Ω` such that `ι ∘ c = conj ∘ ι` for some embedding
`ι : Ω →+* ℂ`; that is, `ComplexEmbedding.IsConj ι c`. Every embedding has exactly one such `c`,
and the set `complexConjugations Ω` of all of them is stable under conjugation by `Gal(Ω/ℚ)`.

The main result is Milne's characterization of CM fields by complex conjugations: a field `F`,
algebraic over `ℚ`, with an embedding `τ : F →+* Ω`, is totally real or CM if and only if every
product `c₁ c₂` of two complex conjugations fixes `τ(F)` pointwise. In that case each complex
conjugation `c` acts on `τ(F)` through one automorphism of `F`: the identity if `F` is totally
real, and Mathlib's `NumberField.IsCMField.complexConj F` if `F` is CM.

## Main definitions

* `TauCeti.NumberField.complexConjugations Ω`: the set of complex conjugations of `Ω`.

## Main results

* `TauCeti.NumberField.exists_isConj`: every embedding `Ω →+* ℂ` has a complex conjugation.
* `TauCeti.NumberField.inv_mul_mul_mem_complexConjugations` and
  `TauCeti.NumberField.mul_mul_inv_mem_complexConjugations`: the set of complex conjugations is
  stable under conjugation.
* `TauCeti.NumberField.apply_eq_of_isTotallyReal` and
  `TauCeti.NumberField.apply_eq_complexConj_of_isCMField`: the action of a complex conjugation on
  a totally real or CM field.
* `TauCeti.NumberField.isTotallyReal_or_isCMField_iff`: the characterization of fields that are
  totally real or CM by products of two complex conjugations.
* `TauCeti.NumberField.existsUnique_forall_mem_complexConjugations_apply_eq`: in that case all
  complex conjugations act on `τ(F)` through one automorphism of `F`.

## References

* J. S. Milne, *Complex Multiplication*, Chapter I, Proposition 1.4 and Remark 1.6.
* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding

namespace TauCeti.NumberField

variable (Ω : Type*) [Field Ω] [CharZero Ω]

/-- The **complex conjugations** of a field `Ω` of characteristic zero: the automorphisms
`c = ι⁻¹ ∘ conj ∘ ι` for the embeddings `ι : Ω →+* ℂ`, stated as `ι ∘ c = conj ∘ ι`. -/
def complexConjugations : Set Gal(Ω/ℚ) :=
  {c | ∃ ι : Ω →+* ℂ, IsConj ι c}

variable {Ω}

/-- `c` is a complex conjugation exactly when it is the conjugation of some embedding
`ι : Ω →+* ℂ`. -/
theorem mem_complexConjugations_iff {c : Gal(Ω/ℚ)} :
    c ∈ complexConjugations Ω ↔ ∃ ι : Ω →+* ℂ, IsConj ι c :=
  Iff.rfl

/-- A complex conjugation is an involution. -/
@[simp]
theorem mul_self_eq_one_of_mem_complexConjugations {c : Gal(Ω/ℚ)} (hc : c ∈ complexConjugations Ω) :
    c * c = 1 := by
  obtain ⟨ι, hι⟩ := hc
  exact AlgEquiv.ext (isConj_apply_apply hι)

/-- A complex conjugation applied twice is the identity. -/
@[simp]
theorem apply_apply_of_mem_complexConjugations {c : Gal(Ω/ℚ)} (hc : c ∈ complexConjugations Ω)
    (x : Ω) : c (c x) = x := by
  obtain ⟨ι, hι⟩ := hc
  exact isConj_apply_apply hι x

/-- A complex conjugation sending `x` to `y` sends `y` back to `x`. -/
theorem apply_eq_of_apply_eq_of_mem_complexConjugations {c : Gal(Ω/ℚ)}
    (hc : c ∈ complexConjugations Ω) {x y : Ω} (h : c x = y) : c y = x := by
  rw [← h, apply_apply_of_mem_complexConjugations hc]

/-- The set of complex conjugations is stable under conjugation by `Gal(Ω/ℚ)`: if `c` is the
conjugation of `ι`, then `g⁻¹ c g` is the conjugation of `ι ∘ g`. -/
theorem inv_mul_mul_mem_complexConjugations {c : Gal(Ω/ℚ)} (hc : c ∈ complexConjugations Ω)
    (g : Gal(Ω/ℚ)) : g⁻¹ * c * g ∈ complexConjugations Ω := by
  obtain ⟨ι, hι⟩ := hc
  exact ⟨_, hι.comp g⟩

/-- The set of complex conjugations is stable under conjugation by `Gal(Ω/ℚ)`, in the form
`g c g⁻¹`. -/
theorem mul_mul_inv_mem_complexConjugations {c : Gal(Ω/ℚ)} (hc : c ∈ complexConjugations Ω)
    (g : Gal(Ω/ℚ)) : g * c * g⁻¹ ∈ complexConjugations Ω := by
  simpa using inv_mul_mul_mem_complexConjugations hc g⁻¹

/-- **Complex conjugations on a totally real field.** Every complex conjugation fixes the image
of a totally real field pointwise. -/
theorem apply_eq_of_isTotallyReal {F : Type*} [Field F] [IsTotallyReal F] {c : Gal(Ω/ℚ)}
    (hc : c ∈ complexConjugations Ω) (τ : F →+* Ω) (x : F) : c (τ x) = τ x := by
  obtain ⟨ι, hι⟩ := hc
  apply ι.injective
  rw [hι.eq]
  exact congr($(IsTotallyReal.complexEmbedding_isReal (ι.comp τ)) x)

/-- **Complex conjugations on a CM field.** Every complex conjugation acts on the image of a CM
field `F` through the complex conjugation `NumberField.IsCMField.complexConj F` of `F`. -/
theorem apply_eq_complexConj_of_isCMField {F : Type*} [Field F] [CharZero F]
    [Algebra.IsIntegral ℚ F] [IsCMField F]
    {c : Gal(Ω/ℚ)} (hc : c ∈ complexConjugations Ω) (τ : F →+* Ω) (x : F) :
    c (τ x) = τ (IsCMField.complexConj F x) := by
  obtain ⟨ι, hι⟩ := hc
  apply ι.injective
  rw [hι.eq]
  exact (IsCMField.complexEmbedding_complexConj F (ι.comp τ) x).symm

variable [Normal ℚ Ω]

/-- **Every embedding of `Ω` into `ℂ` has a complex conjugation.** The image of `Ω` in `ℂ` is
normal over `ℚ`, hence stable under complex conjugation. -/
theorem exists_isConj (ι : Ω →+* ℂ) : ∃ c : Gal(Ω/ℚ), IsConj ι c := by
  let := ι.toAlgebra
  have : IsScalarTower ℚ Ω ℂ := .of_algebraMap_eq fun x ↦ by simp
  refine ⟨(Complex.conjAe.restrictScalars ℚ).restrictNormal Ω, RingHom.ext fun x ↦ ?_⟩
  -- Both sides unfold to `conj (ι x)` and `ι (c x)`: `conjugate ι x` is `star (ι x)`, which is
  -- `Complex.conjAe.restrictScalars ℚ (algebraMap Ω ℂ x)` for the algebra `ι.toAlgebra`.
  exact (AlgEquiv.restrictNormal_commutes (Complex.conjAe.restrictScalars ℚ) Ω x).symm

variable (Ω) in
/-- `Ω` has a complex conjugation. -/
theorem complexConjugations_nonempty : (complexConjugations Ω).Nonempty :=
  let ι : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  (exists_isConj ι.toRingHom).imp fun _ hc ↦ ⟨_, hc⟩

variable {F : Type*} [Field F] [CharZero F]

/-- If every complex conjugation `d` sends `c (τ x)` back to `τ x`, then the complex conjugation
`c` maps `τ x` into `τ(F)`. -/
private theorem apply_mem_fieldRange_of_forall_mul {τ : F →+* Ω} {c : Gal(Ω/ℚ)}
    (hc : c ∈ complexConjugations Ω) {x : F}
    (h : ∀ d ∈ complexConjugations Ω, d (c (τ x)) = τ x) :
    c (τ x) ∈ τ.toRatAlgHom.fieldRange := by
  have : IsGalois ℚ Ω := ⟨⟩
  rw [← InfiniteGalois.fixedField_fixingSubgroup τ.toRatAlgHom.fieldRange,
    IntermediateField.mem_fixedField_iff]
  intro g hg
  have hgx : g (τ x) = τ x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ ⟨x, rfl⟩
  have hginv : g⁻¹ (τ x) = τ x := g.symm_apply_eq.mpr hgx.symm
  have hc' := mul_mul_inv_mem_complexConjugations hc g
  -- The conjugate `g c g⁻¹` sends `τ x` to `g (c (τ x))`, and by involutivity of `g c g⁻¹` and
  -- `h` this is `c (τ x)`.
  have hcx : (g * c * g⁻¹) (τ x) = c (τ x) :=
    apply_eq_of_apply_eq_of_mem_complexConjugations hc' (h _ hc')
  calc g (c (τ x)) = (g * c * g⁻¹) (τ x) := by
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hginv]
    _ = c (τ x) := hcx

omit [Normal ℚ Ω] in
/-- A complex conjugation mapping `τ(F)` into itself maps it onto itself. -/
private theorem map_fieldRange_eq (τ : F →+* Ω) {c : Gal(Ω/ℚ)} (hc : c ∈ complexConjugations Ω)
    (hmem : ∀ x, c (τ x) ∈ τ.toRatAlgHom.fieldRange) :
    τ.toRatAlgHom.fieldRange.map c.toAlgHom = τ.toRatAlgHom.fieldRange := by
  refine le_antisymm (fun y hy ↦ ?_) fun y hy ↦ (IntermediateField.mem_map _).2 ⟨c y, ?_, ?_⟩
  · obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := (IntermediateField.mem_map _).1 hy
    exact hmem x
  · obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.1 hy
    exact hmem x
  · exact apply_apply_of_mem_complexConjugations hc y

/-- The automorphism of `F` through which a complex conjugation `c` acts on `τ(F)`, when it maps
`τ(F)` into itself: the restriction `τ(F) ≃ c(τ(F)) = τ(F)` of `c`, read on `F` through `τ`. -/
private noncomputable def restrictOfApplyMem (τ : F →+* Ω) {c : Gal(Ω/ℚ)}
    (hc : c ∈ complexConjugations Ω) (hmem : ∀ x, c (τ x) ∈ τ.toRatAlgHom.fieldRange) :
    Gal(F/ℚ) :=
  τ.toRatAlgHom.equivFieldRange.trans <|
    ((τ.toRatAlgHom.fieldRange.equivMap c.toAlgHom).trans
      (IntermediateField.equivOfEq (map_fieldRange_eq τ hc hmem))).trans
    τ.toRatAlgHom.equivFieldRange.symm

omit [Normal ℚ Ω] in
private theorem apply_restrictOfApplyMem (τ : F →+* Ω) {c : Gal(Ω/ℚ)}
    (hc : c ∈ complexConjugations Ω) (hmem : ∀ x, c (τ x) ∈ τ.toRatAlgHom.fieldRange) (x : F) :
    τ (restrictOfApplyMem τ hc hmem x) = c (τ x) := by
  -- read `τ` as the `ℚ`-algebra map `τ.toRatAlgHom`, to which the `equivFieldRange` lemmas apply
  simp only [restrictOfApplyMem, AlgEquiv.trans_apply, ← RingHom.toRatAlgHom_apply τ,
    AlgHom.apply_equivFieldRange_symm_apply, IntermediateField.equivOfEq_apply,
    IntermediateField.coe_equivMap_apply, AlgHom.equivFieldRange_apply_coe,
    AlgEquiv.coe_toAlgHom]

/-- **Milne's criterion (Milne, *Complex Multiplication*, I, Proposition 1.4).** A field `F`
embedded in `Ω` by `τ` (hence algebraic over `ℚ`) is totally real or CM if and only if every
product `c₁ c₂` of two complex conjugations of `Ω` fixes `τ(F)` pointwise. -/
theorem isTotallyReal_or_isCMField_iff (τ : F →+* Ω) :
    IsTotallyReal F ∨ IsCMField F ↔
      ∀ c₁ ∈ complexConjugations Ω, ∀ c₂ ∈ complexConjugations Ω, ∀ x, c₁ (c₂ (τ x)) = τ x := by
  have := Algebra.IsIntegral.of_injective τ.toRatAlgHom τ.injective
  constructor
  · rintro (hF | hF) c₁ hc₁ c₂ hc₂ x
    · rw [apply_eq_of_isTotallyReal hc₂, apply_eq_of_isTotallyReal hc₁]
    · rw [apply_eq_complexConj_of_isCMField hc₂, apply_eq_complexConj_of_isCMField hc₁,
        IsCMField.complexConj_apply_apply]
  · intro h
    obtain ⟨c₀, hc₀⟩ := complexConjugations_nonempty Ω
    have hmem x := apply_mem_fieldRange_of_forall_mul hc₀ fun d hd ↦ h d hd c₀ hc₀ x
    have hs' := apply_restrictOfApplyMem τ hc₀ hmem
    set s := restrictOfApplyMem τ hc₀ hmem
    have hs : ∀ φ : F →+* ℂ, IsConj φ s := fun φ ↦ by
      -- Extend `φ` along `τ` to an embedding `ι` of `Ω`.
      let := τ.toAlgebra
      have : IsScalarTower ℚ F Ω := .of_algebraMap_eq (R := ℚ) (S := F) (A := Ω) fun x ↦ by simp
      have : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
      obtain ⟨ι, rfl⟩ : ∃ ι : Ω →+* ℂ, ι.comp τ = φ :=
        ⟨ComplexEmbedding.lift Ω φ, ComplexEmbedding.lift_comp_algebraMap Ω φ⟩
      obtain ⟨c, hc⟩ := exists_isConj ι
      refine RingHom.ext fun x ↦ ?_
      simp only [conjugate_coe_eq, RingHom.comp_apply, RingHom.coe_coe, hs']
      rw [apply_eq_of_apply_eq_of_mem_complexConjugations hc₀ (h _ hc₀ _ ⟨ι, hc⟩ x), hc.eq,
        Complex.star_def]
    by_cases hs1 : s = 1
    · left
      exact ⟨fun w ↦ isReal_iff.mpr (isConj_one_iff.mp (hs1 ▸ hs _))⟩
    · exact Or.inr (isCMField_of_forall_isConj hs1 hs)

/-- **The common involution of a field fixed by products of complex conjugations.** If every
product `c₁ c₂` of two complex conjugations of `Ω` fixes `τ(F)` pointwise, there is exactly one
automorphism `s` of `F` through which every complex conjugation acts on `τ(F)`. By
`isTotallyReal_or_isCMField_iff` the field `F` is then totally real or CM, and `s` is the identity
(`apply_eq_of_isTotallyReal`) or `NumberField.IsCMField.complexConj F`
(`apply_eq_complexConj_of_isCMField`). -/
theorem existsUnique_forall_mem_complexConjugations_apply_eq (τ : F →+* Ω)
    (h : ∀ c₁ ∈ complexConjugations Ω, ∀ c₂ ∈ complexConjugations Ω, ∀ x, c₁ (c₂ (τ x)) = τ x) :
    ∃! s : Gal(F/ℚ), ∀ c ∈ complexConjugations Ω, ∀ x, c (τ x) = τ (s x) := by
  obtain ⟨c₀, hc₀⟩ := complexConjugations_nonempty Ω
  have hmem x := apply_mem_fieldRange_of_forall_mul hc₀ fun d hd ↦ h d hd c₀ hc₀ x
  have hs := apply_restrictOfApplyMem τ hc₀ hmem
  refine ⟨restrictOfApplyMem τ hc₀ hmem, fun c hc x ↦ ?_, fun s' hs' ↦ ?_⟩
  · -- `c₀` sends `τ (s x)` back to `τ x`, and `c c₀` fixes `τ (s x)`.
    calc c (τ x) = c (c₀ (τ (restrictOfApplyMem τ hc₀ hmem x))) := by
          rw [apply_eq_of_apply_eq_of_mem_complexConjugations hc₀ (hs x).symm]
      _ = τ (restrictOfApplyMem τ hc₀ hmem x) := h c hc c₀ hc₀ _
  · exact AlgEquiv.ext fun x ↦ τ.injective ((hs' c₀ hc₀ x).symm.trans (hs x).symm)

end TauCeti.NumberField
