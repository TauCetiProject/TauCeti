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
# CM or totally real fields via the complex conjugations of an algebraic closure of `ℚ`

Let `Ω` be an algebraic closure of `ℚ`. A *complex conjugation* of `Ω` is an automorphism `c`
of `Ω` such that `ι ∘ c = conj ∘ ι` for some embedding `ι : Ω →+* ℂ`; that is,
`ComplexEmbedding.IsConj ι c`. Every embedding has exactly one such `c`, and the set
`complexConjugations Ω` of all of them is stable under conjugation by `Gal(Ω/ℚ)`.

The main result is Milne's characterization of CM fields by complex conjugations: a field `F`,
algebraic over `ℚ`, with an embedding `τ : F →+* Ω`, is totally real or CM if and only if every
product `c₁ c₂` of two complex conjugations fixes `τ(F)` pointwise. In that case each complex
conjugation `c` acts on `τ(F)` through one automorphism of `F`: the identity if `F` is totally
real, and Mathlib's `NumberField.IsCMField.complexConj F` if `F` is CM.

## Main definitions

* `TauCeti.NumberField.complexConjugations Ω`: the set of complex conjugations of `Ω`.

## Main results

* `TauCeti.NumberField.exists_isConj`: every embedding `Ω →+* ℂ` has a complex conjugation.
* `TauCeti.NumberField.mul_inv_mul_mem_complexConjugations`: the set of complex conjugations is
  stable under conjugation.
* `TauCeti.NumberField.apply_eq_of_isTotallyReal` and
  `TauCeti.NumberField.apply_eq_complexConj_of_isCMField`: the action of a complex conjugation on
  a totally real or CM field.
* `TauCeti.NumberField.isTotallyReal_or_isCMField_iff`: the characterization of fields that are
  totally real or CM by products of two complex conjugations.
* `TauCeti.NumberField.isCMField_of_forall_isConj`: a field with one automorphism conjugating
  every complex embedding, not the identity, is CM. Mathlib's
  `NumberField.IsCMField.of_forall_isConj` is the special case of a Galois extension of `ℚ`.

## References

* J. S. Milne, *Complex Multiplication*, Chapter I, Proposition 1.4 and Remark 1.6.
* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding

namespace TauCeti.NumberField

section General

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsIntegral ℚ K]

open IntermediateField in
/-- **A field with a single nontrivial conjugation of all its complex embeddings is CM.** If one
automorphism `σ ≠ 1` of `K` satisfies `IsConj φ σ` for every embedding `φ : K →+* ℂ`, then `K` is a
CM field. Mathlib's `NumberField.IsCMField.of_forall_isConj` proves this for `K` Galois over `ℚ`
and totally complex; neither assumption is needed. -/
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

/-- The **complex conjugations** of an algebraic closure `Ω` of `ℚ`: the automorphisms
`c = ι⁻¹ ∘ conj ∘ ι` for the embeddings `ι : Ω →+* ℂ`, stated as `ι ∘ c = conj ∘ ι`. -/
def complexConjugations : Set Gal(Ω/ℚ) :=
  {c | ∃ ι : Ω →+* ℂ, IsConj ι c}

variable {Ω}

/-- A complex conjugation is an involution. -/
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

/-- The set of complex conjugations is stable under conjugation by `Gal(Ω/ℚ)`: if `c` is the
conjugation of `ι`, then `g⁻¹ c g` is the conjugation of `ι ∘ g`. -/
theorem mul_inv_mul_mem_complexConjugations {c : Gal(Ω/ℚ)} (hc : c ∈ complexConjugations Ω)
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

/-- If products of two complex conjugations fix `τ(F)`, then all complex conjugations agree on
`τ(F)`. -/
theorem apply_eq_apply_of_forall_mul {F : Type*} [Field F] {τ : F →+* Ω}
    (h : ∀ c₁ ∈ complexConjugations Ω, ∀ c₂ ∈ complexConjugations Ω, ∀ x, c₁ (c₂ (τ x)) = τ x)
    {c₁ c₂ : Gal(Ω/ℚ)} (hc₁ : c₁ ∈ complexConjugations Ω) (hc₂ : c₂ ∈ complexConjugations Ω)
    (x : F) : c₁ (τ x) = c₂ (τ x) := by
  conv_lhs => rw [← h c₁ hc₁ c₂ hc₂ x]
  exact apply_apply_of_mem_complexConjugations hc₁ _

variable [IsAlgClosure ℚ Ω]

/-- **Every embedding of `Ω` into `ℂ` has a complex conjugation.** The image of `Ω` in `ℂ` is
normal over `ℚ`, hence stable under complex conjugation. -/
theorem exists_isConj (ι : Ω →+* ℂ) : ∃ c : Gal(Ω/ℚ), IsConj ι c := by
  let := ι.toAlgebra
  have : IsScalarTower ℚ Ω ℂ := .of_algebraMap_eq fun x ↦ by simp
  refine ⟨(Complex.conjAe.restrictScalars ℚ).restrictNormal Ω, RingHom.ext fun x ↦ ?_⟩
  exact (AlgEquiv.restrictNormal_commutes (Complex.conjAe.restrictScalars ℚ) Ω x).symm

variable (Ω) in
/-- `Ω` has a complex conjugation. -/
theorem complexConjugations_nonempty : (complexConjugations Ω).Nonempty :=
  let ι : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  (exists_isConj ι.toRingHom).imp fun _ hc ↦ ⟨_, hc⟩

/-- **Extension of complex embeddings.** For an embedding `τ : F →+* Ω`, every embedding
`φ : F →+* ℂ` factors as `ι ∘ τ` for some `ι : Ω →+* ℂ`. -/
theorem exists_comp_eq {F : Type*} [Field F] [CharZero F] (τ : F →+* Ω) (φ : F →+* ℂ) :
    ∃ ι : Ω →+* ℂ, ι.comp τ = φ := by
  let := τ.toAlgebra
  let := φ.toAlgebra
  have : IsScalarTower ℚ F Ω := .of_algebraMap_eq (R := ℚ) (S := F) (A := Ω) fun x ↦ by simp
  have : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  exact ⟨(IsAlgClosed.lift : Ω →ₐ[F] ℂ).toRingHom, RingHom.ext fun x ↦
    (IsAlgClosed.lift : Ω →ₐ[F] ℂ).commutes x⟩

variable {F : Type*} [Field F] [CharZero F]

/-- If products of two complex conjugations fix `τ(F)`, then every complex conjugation maps
`τ(F)` into itself. -/
theorem apply_mem_fieldRange_of_forall_mul {τ : F →+* Ω}
    (h : ∀ c₁ ∈ complexConjugations Ω, ∀ c₂ ∈ complexConjugations Ω, ∀ x, c₁ (c₂ (τ x)) = τ x)
    {c : Gal(Ω/ℚ)} (hc : c ∈ complexConjugations Ω) (x : F) :
    c (τ x) ∈ τ.toRatAlgHom.fieldRange := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup τ.toRatAlgHom.fieldRange]
  intro ⟨g, hg⟩
  have hgx : g (τ x) = τ x := hg ⟨τ x, x, rfl⟩
  have hc' : g * c * g⁻¹ ∈ complexConjugations Ω := by
    simpa using mul_inv_mul_mem_complexConjugations hc g⁻¹
  change g (c (τ x)) = c (τ x)
  have := apply_eq_apply_of_forall_mul h hc' hc x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hgx, ← AlgEquiv.mul_apply g⁻¹ g, inv_mul_cancel,
    AlgEquiv.one_apply, hgx] at this
  exact this

/-- The automorphism of `F` through which a complex conjugation `c` acts on `τ(F)`, when it maps
`τ(F)` into itself. -/
private noncomputable def restrictOfApplyMem (τ : F →+* Ω) {c : Gal(Ω/ℚ)}
    (hc : c ∈ complexConjugations Ω) (hmem : ∀ x, c (τ x) ∈ τ.toRatAlgHom.fieldRange) :
    Gal(F/ℚ) :=
  let s : F →ₐ[ℚ] F := ((AlgEquiv.ofInjectiveField τ.toRatAlgHom).symm.toAlgHom.comp
    ((c.toAlgHom.comp τ.toRatAlgHom).codRestrict
      τ.toRatAlgHom.fieldRange.toSubalgebra hmem))
  have hs : ∀ x, τ (s x) = c (τ x) := fun x ↦
    congr($(AlgEquiv.apply_symm_apply (AlgEquiv.ofInjectiveField τ.toRatAlgHom)
      ⟨c (τ x), hmem x⟩).val)
  have hss : s.comp s = AlgHom.id ℚ F := AlgHom.ext fun x ↦ τ.injective <| by
    simp [hs, apply_apply_of_mem_complexConjugations hc]
  AlgEquiv.ofAlgHom s s hss hss

omit [IsAlgClosure ℚ Ω] in
private theorem apply_restrictOfApplyMem (τ : F →+* Ω) {c : Gal(Ω/ℚ)}
    (hc : c ∈ complexConjugations Ω) (hmem : ∀ x, c (τ x) ∈ τ.toRatAlgHom.fieldRange) (x : F) :
    τ (restrictOfApplyMem τ hc hmem x) = c (τ x) :=
  congr($(AlgEquiv.apply_symm_apply (AlgEquiv.ofInjectiveField τ.toRatAlgHom)
      ⟨c (τ x), hmem x⟩).val)

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
    have hmem := apply_mem_fieldRange_of_forall_mul h hc₀
    have hs' := apply_restrictOfApplyMem τ hc₀ hmem
    set s := restrictOfApplyMem τ hc₀ hmem
    have hs : ∀ φ : F →+* ℂ, IsConj φ s := fun φ ↦ by
      obtain ⟨ι, rfl⟩ := exists_comp_eq τ φ
      obtain ⟨c, hc⟩ := exists_isConj ι
      refine RingHom.ext fun x ↦ ?_
      change star (ι (τ x)) = ι (τ (s x))
      rw [hs', apply_eq_apply_of_forall_mul h hc₀ ⟨ι, hc⟩, hc.eq]
    by_cases hs1 : s = 1
    · left
      exact ⟨fun w ↦ isReal_iff.mpr (isConj_one_iff.mp (hs1 ▸ hs _))⟩
    · exact Or.inr (isCMField_of_forall_isConj hs1 hs)

end TauCeti.NumberField
