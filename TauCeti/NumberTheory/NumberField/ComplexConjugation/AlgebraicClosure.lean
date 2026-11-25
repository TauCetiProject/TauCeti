/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.NumberField.CMField

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
* `TauCeti.NumberField.inv_mul_mul_mem_complexConjugations`: the set of complex conjugations is
  stable under conjugation.
* `TauCeti.NumberField.apply_eq_of_isTotallyReal` and
  `TauCeti.NumberField.apply_eq_complexConj_of_isCMField`: the action of a complex conjugation on
  a totally real or CM field.
* `TauCeti.NumberField.isTotallyReal_or_isCMField_iff`: the characterization of fields that are
  totally real or CM by products of two complex conjugations.
* `TauCeti.NumberField.isCMField_of_forall_isConj`: a field algebraic over `ℚ` with one
  automorphism conjugating every complex embedding, not the identity, is CM. Mathlib's
  `NumberField.IsCMField.of_forall_isConj` assumes that the field is Galois over `ℚ` and totally
  complex; this criterion assumes only that the field is algebraic over `ℚ` and has one
  automorphism, not the identity, conjugating every complex embedding.

## References

* J. S. Milne, *Complex Multiplication*, Chapter I, Proposition 1.4 and Remark 1.6.
* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding

namespace TauCeti.NumberField

/-- A subfield of a field algebraic over `ℚ` is algebraic over `ℚ`. -/
instance isIntegral_subfield {L : Type*} [Field L] [CharZero L] [Algebra.IsIntegral ℚ L]
    (F : Subfield L) : Algebra.IsIntegral ℚ F :=
  Algebra.IsIntegral.of_injective F.subtype.toRatAlgHom F.subtype_injective

section General

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsIntegral ℚ K]

open IntermediateField in
/-- **A field with a single nontrivial conjugation of all its complex embeddings is CM.** If `K`
is algebraic over `ℚ` and one automorphism `σ ≠ 1` of `K` satisfies `IsConj φ σ` for every
embedding `φ : K →+* ℂ`, then `K` is a CM field. Mathlib's `NumberField.IsCMField.of_forall_isConj`
proves this for `K` Galois over `ℚ` and totally complex; neither assumption is needed. -/
theorem isCMField_of_forall_isConj {σ : Gal(K/ℚ)} (hσ1 : σ ≠ 1)
    (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  have : IsTotallyComplex K := ⟨fun w ↦ isComplex_iff.mpr ((isConj_ne_one_iff (hσ _)).mp hσ1)⟩
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hσ' : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers, orderOf_isConj_two_of_ne_one (hσ φ) hσ1]
  have : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by positivity)
  let L := FixedPoints.subfield (Subgroup.zpowers σ) K
  have : IsTotallyReal L := ⟨fun w ↦ by
    obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
    dsimp only
    rw [← mk_embedding W, comap_mk, isReal_mk_iff]
    exact ComplexEmbedding.IsConj.isReal_comp
      (σ := IsGaloisGroup.mulEquivAlgEquiv (Subgroup.zpowers σ) L K ⟨σ, Subgroup.mem_zpowers σ⟩)
      (hσ W.embedding)⟩
  have : Algebra.IsQuadraticExtension L K := ⟨by
    rw [← IsGaloisGroup.card_eq_finrank (Subgroup.zpowers σ), hσ']⟩
  exact IsCMField.ofCMExtension L K

end General

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
theorem mul_self_of_mem_complexConjugations {c : Gal(Ω/ℚ)} (hc : c ∈ complexConjugations Ω) :
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
  have hc' : g * c * g⁻¹ ∈ complexConjugations Ω := by
    simpa using inv_mul_mul_mem_complexConjugations hc g⁻¹
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
  have h (z : τ.toRatAlgHom.fieldRange) : τ (τ.toRatAlgHom.equivFieldRange.symm z) = z := by
    have := AlgHom.equivFieldRange_apply_coe τ.toRatAlgHom (τ.toRatAlgHom.equivFieldRange.symm z)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  simp only [restrictOfApplyMem, AlgEquiv.trans_apply, h, IntermediateField.equivOfEq_apply,
    IntermediateField.coe_equivMap_apply, AlgHom.equivFieldRange_apply_coe,
    AlgEquiv.coe_toAlgHom, RingHom.toRatAlgHom_apply]

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

end TauCeti.NumberField
