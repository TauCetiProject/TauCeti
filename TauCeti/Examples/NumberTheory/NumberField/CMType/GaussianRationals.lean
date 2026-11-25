/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.NumberTheory.NumberField.CMType.ReflexField

/-!
# CM types and the reflex field of `ℚ(i)`

This file checks the CM-type and reflex-field API of `TauCeti.CMType` on `ℚ(i)`, modelled as the
fourth cyclotomic field `CyclotomicField 4 ℚ` with its primitive fourth root of unity `ζ = i`.

On any commutative ring with a complex embedding, neither the full embedding set nor the empty set
is a CM type (`TauCeti.CMType.not_exists_coe_eq_univ`, `TauCeti.CMType.not_exists_coe_eq_empty`):
a condition asking only for at least one embedding from each conjugate pair would accept the full
set. When the embeddings are exactly `φ` and its distinct conjugate, the singleton `{φ}` is a CM
type (`TauCeti.CMType.ofPair`).

The embeddings of `ℚ(i)` are `i ↦ I` and `i ↦ -I`
(`TauCeti.GaussianRationalsCMType.eq_or_eq_star`); each singleton is a CM type
(`exists_coe_eq_singleton`), and every CM type has one element (`natCard_eq_one`). For
`Φ = {i ↦ I}` the type trace of `i` is `I` (`typeTrace_Φ_ζ`), so the reflex field is
`ℚ(I) ⊆ ℂ` (`reflexField_Φ`) and is not `ℚ` (`reflexField_Φ_ne_bot`), while the full trace of `i`
vanishes (`trace_ζ`): a reflex field defined through the full trace would be `ℚ`.
-/

public section

open NumberField Polynomial IntermediateField

namespace TauCeti.CMType

variable {E : Type*} [CommRing E]

/-- The full set of embeddings is not a CM type when `E` has an embedding: it contains every
conjugate pair entirely. -/
theorem not_exists_coe_eq_univ [Nonempty (E →+* ℂ)] :
    ¬ ∃ Φ : CMType E, (Φ : Set (E →+* ℂ)) = Set.univ := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨φ⟩ := ‹Nonempty (E →+* ℂ)›
  have h := Φ.star_mem_iff φ
  simp [← SetLike.mem_coe, hΦ] at h

/-- The empty set is not a CM type when `E` has an embedding: it misses every conjugate pair. -/
theorem not_exists_coe_eq_empty [Nonempty (E →+* ℂ)] :
    ¬ ∃ Φ : CMType E, (Φ : Set (E →+* ℂ)) = ∅ := by
  rintro ⟨Φ, hΦ⟩
  obtain ⟨φ⟩ := ‹Nonempty (E →+* ℂ)›
  have h := Φ.star_mem_iff φ
  simp [← SetLike.mem_coe, hΦ] at h

/-- If the embeddings of `E` are exactly an embedding `φ` and its distinct conjugate, then the
singleton `{φ}` is a CM type. -/
def ofPair (φ : E →+* ℂ) (hφ : star φ ≠ φ) (h : ∀ ψ : E →+* ℂ, ψ = φ ∨ ψ = star φ) :
    CMType E where
  carrier := {φ}
  star_mem_iff' ψ := by
    rcases h ψ with rfl | rfl
    · simpa using hφ
    · simpa [eq_comm] using hφ

@[simp]
theorem coe_ofPair (φ : E →+* ℂ) (hφ : star φ ≠ φ) (h : ∀ ψ : E →+* ℂ, ψ = φ ∨ ψ = star φ) :
    (ofPair φ hφ h : Set (E →+* ℂ)) = {φ} :=
  (rfl)

end TauCeti.CMType

namespace TauCeti.GaussianRationalsCMType

/-- `ℚ(i)`, as the fourth cyclotomic field. -/
abbrev K : Type := CyclotomicField 4 ℚ

instance instIsCyclotomicExtensionK : IsCyclotomicExtension {4} ℚ K :=
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  CyclotomicField.isCyclotomicExtension 4 ℚ

/-- The primitive fourth root of unity `i` of `ℚ(i)`. -/
noncomputable abbrev ζ : K := IsCyclotomicExtension.zeta 4 ℚ K

theorem isPrimitiveRoot_ζ : IsPrimitiveRoot ζ 4 := IsCyclotomicExtension.zeta_spec 4 ℚ K

theorem irreducible_cyclotomic_four : Irreducible (cyclotomic 4 ℚ) :=
  cyclotomic.irreducible_rat (by norm_num)

/-- The embedding `ℚ(i) → ℂ` sending `i` to `I`, as a `ℚ`-algebra map. -/
noncomputable def φₐ : K →ₐ[ℚ] ℂ :=
  (isPrimitiveRoot_ζ.embeddingsEquivPrimitiveRoots ℂ irreducible_cyclotomic_four).symm
    ⟨Complex.I, (mem_primitiveRoots (by norm_num)).2 Complex.isPrimitiveRoot_I⟩

/-- The embedding `ℚ(i) → ℂ` sending `i` to `I`. -/
noncomputable def φ : K →+* ℂ := φₐ.toRingHom

theorem φₐ_ζ : φₐ ζ = Complex.I := by
  have h := isPrimitiveRoot_ζ.embeddingsEquivPrimitiveRoots_apply_coe ℂ
    irreducible_cyclotomic_four φₐ
  rw [φₐ, Equiv.apply_symm_apply] at h
  exact h.symm

@[simp]
theorem φ_ζ : φ ζ = Complex.I := φₐ_ζ

theorem star_φ_ζ : star φ ζ = -Complex.I := by
  simp [RingHom.star_apply]

theorem star_φ_ne : star φ ≠ φ := fun h ↦ by
  have := congrArg (· ζ) h
  rw [star_φ_ζ, φ_ζ] at this
  exact Complex.I_ne_zero (by linear_combination -this / 2)

theorem card_ringHom : Fintype.card (K →+* ℂ) = 2 := by
  rw [Embeddings.card, IsCyclotomicExtension.finrank K irreducible_cyclotomic_four]
  decide

/-- The embeddings of `ℚ(i)` are `i ↦ I` and `i ↦ -I`. -/
theorem eq_or_eq_star (ψ : K →+* ℂ) : ψ = φ ∨ ψ = star φ := by
  classical
  by_contra h
  simp only [not_or] at h
  have h3 : ({φ, star φ, ψ} : Finset (K →+* ℂ)).card = 3 :=
    Finset.card_eq_three.2 ⟨φ, star φ, ψ, star_φ_ne.symm, Ne.symm h.1, Ne.symm h.2, rfl⟩
  have := Finset.card_le_univ ({φ, star φ, ψ} : Finset (K →+* ℂ))
  have := card_ringHom
  omega

/-- The CM type `{i ↦ I}` of `ℚ(i)`. -/
noncomputable def Φ : CMType K := CMType.ofPair φ star_φ_ne eq_or_eq_star

@[simp]
theorem coe_Φ : (Φ : Set (K →+* ℂ)) = {φ} := (rfl)

/-- **Each singleton of an embedding of `ℚ(i)` is a CM type.** -/
theorem exists_coe_eq_singleton (ψ : K →+* ℂ) : ∃ Ψ : CMType K, (Ψ : Set (K →+* ℂ)) = {ψ} := by
  rcases eq_or_eq_star ψ with rfl | rfl
  · exact ⟨Φ, coe_Φ⟩
  · refine ⟨star Φ, ?_⟩
    ext χ
    rcases eq_or_eq_star χ with rfl | rfl
    · simpa using star_φ_ne.symm
    · simpa using star_φ_ne

/-- **Every CM type of `ℚ(i)` has one embedding.** -/
theorem natCard_eq_one (Ψ : CMType K) : Nat.card Ψ = 1 := by
  have h := Ψ.two_mul_card_eq_finrank
  rw [IsCyclotomicExtension.finrank K irreducible_cyclotomic_four] at h
  have : Nat.totient 4 = 2 := by decide
  omega

/-- Neither the full embedding set nor the empty set of `ℚ(i)` is a CM type. -/
theorem not_exists_coe_eq_univ_or_empty :
    (¬ ∃ Ψ : CMType K, (Ψ : Set (K →+* ℂ)) = Set.univ) ∧
      ¬ ∃ Ψ : CMType K, (Ψ : Set (K →+* ℂ)) = ∅ :=
  have : Nonempty (K →+* ℂ) := ⟨φ⟩
  ⟨CMType.not_exists_coe_eq_univ, CMType.not_exists_coe_eq_empty⟩

/-- **The type trace of `{i ↦ I}` at `i` is `I`.** -/
@[simp]
theorem typeTrace_Φ_ζ : Φ.typeTrace ζ = Complex.I := by
  rw [CMType.typeTrace_apply, coe_Φ, finsum_mem_singleton, φ_ζ]

/-- The full trace of `i` vanishes, so a reflex field defined through the full trace over all
embeddings would be `ℚ`. -/
theorem trace_ζ : Algebra.trace ℚ K ζ = 0 := by
  have h := Φ.typeTrace_add_typeTrace_star_eq_trace ζ
  rw [CMType.typeTrace_star, typeTrace_Φ_ζ, Complex.conj_I, add_neg_cancel] at h
  exact (algebraMap ℚ ℂ).injective (by rw [← h, map_zero])

/-- **The reflex field of `{i ↦ I}` is `ℚ(I) ⊆ ℂ`.** -/
theorem reflexField_Φ : Φ.reflexField = ℚ⟮Complex.I⟯ := by
  refine le_antisymm (CMType.reflexField_le_iff.2 fun a ↦ ?_)
    (adjoin_simple_le_iff.2 (typeTrace_Φ_ζ ▸ Φ.typeTrace_mem_reflexField ζ))
  rw [CMType.typeTrace_apply, coe_Φ, finsum_mem_singleton]
  have ha : a ∈ Algebra.adjoin ℚ {ζ} := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top isPrimitiveRoot_ζ]
    trivial
  have hφa : φₐ a ∈ (Algebra.adjoin ℚ {ζ}).map φₐ := Subalgebra.mem_map.2 ⟨a, ha, rfl⟩
  rw [AlgHom.map_adjoin, Set.image_singleton, φₐ_ζ] at hφa
  exact algebra_adjoin_le_adjoin ℚ _ hφa

/-- The reflex field of `{i ↦ I}` is not `ℚ`. -/
theorem reflexField_Φ_ne_bot : Φ.reflexField ≠ ⊥ := by
  intro h
  have hI := typeTrace_Φ_ζ ▸ Φ.typeTrace_mem_reflexField ζ
  rw [h, mem_bot] at hI
  obtain ⟨q, hq⟩ := hI
  have := congrArg Complex.im hq
  simp at this

end TauCeti.GaussianRationalsCMType
