/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Four.Basic

/-!
# CM types and the reflex field of `ℚ(i)`

This file checks the CM-type and reflex-field API of `TauCeti.CMType` on `ℚ(i)`, modelled as the
fourth cyclotomic field `CyclotomicField 4 ℚ` with its primitive fourth root of unity `ζ = i`.

The embeddings of `ℚ(i)` are `i ↦ I` and `i ↦ -I`
(`TauCeti.GaussianRationalsCMType.eq_or_eq_star`); each singleton is a CM type
(`exists_coe_eq_singleton`, through `TauCeti.CMType.ofPair`), and every CM type has one element
(`natCard_eq_one`). Since `ℚ(i)` has an embedding, no CM type of `ℚ(i)` is the full embedding set
or empty (`TauCeti.CMType.coe_ne_univ`, `TauCeti.CMType.coe_ne_empty`): a condition asking only for
at least one embedding from each conjugate pair would accept the full set. For `Φ = {i ↦ I}` the
type trace of `i` is `I` (`typeTrace_Φ_ζ`), so the reflex field is `ℚ(I) ⊆ ℂ` (`reflexField_Φ`)
and is not `ℚ` (`reflexField_Φ_ne_bot`), while the full trace of `i` vanishes (`trace_ζ`), unlike
its type trace.
-/

public section

open NumberField Polynomial IntermediateField

namespace TauCeti.GaussianRationalsCMType

/-- `ℚ(i)`, as the fourth cyclotomic field. -/
abbrev K : Type := CyclotomicField 4 ℚ

local instance instIsCyclotomicExtensionK : IsCyclotomicExtension {4} ℚ K :=
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  CyclotomicField.isCyclotomicExtension 4 ℚ

/-- The primitive fourth root of unity `i` of `ℚ(i)`. -/
noncomputable abbrev ζ : K := IsCyclotomicExtension.zeta 4 ℚ K

theorem isPrimitiveRoot_ζ : IsPrimitiveRoot ζ 4 := IsCyclotomicExtension.zeta_spec 4 ℚ K

/-- The embedding `ℚ(i) → ℂ` sending `i` to `I`, as a `ℚ`-algebra map. -/
noncomputable def φₐ : K →ₐ[ℚ] ℂ :=
  (isPrimitiveRoot_ζ.embeddingsEquivPrimitiveRoots ℂ
    (cyclotomic.irreducible_rat (by norm_num))).symm
    ⟨Complex.I, (mem_primitiveRoots (by norm_num)).2 Complex.isPrimitiveRoot_I⟩

/-- The embedding `ℚ(i) → ℂ` sending `i` to `I`. -/
noncomputable def φ : K →+* ℂ := φₐ.toRingHom

theorem φₐ_ζ : φₐ ζ = Complex.I := by
  have h := isPrimitiveRoot_ζ.embeddingsEquivPrimitiveRoots_apply_coe ℂ
    (cyclotomic.irreducible_rat (by norm_num)) φₐ
  rw [φₐ, Equiv.apply_symm_apply] at h
  exact h.symm

@[simp]
theorem φ_ζ : φ ζ = Complex.I := by
  rw [φ, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, φₐ_ζ]

theorem star_φ_ζ : star φ ζ = -Complex.I := by
  simp [RingHom.star_apply]

theorem star_φ_ne_self : star φ ≠ φ := fun h ↦ by
  have := congrArg (· ζ) h
  rw [star_φ_ζ, φ_ζ] at this
  exact Complex.I_ne_zero (by linear_combination -this / 2)

theorem card_ringHom : Fintype.card (K →+* ℂ) = 2 := by
  rw [Embeddings.card, finrank_eq_two_of_isCyclotomicExtension_four]

/-- The embeddings of `ℚ(i)` are `i ↦ I` and `i ↦ -I`. -/
theorem eq_or_eq_star (ψ : K →+* ℂ) : ψ = φ ∨ ψ = star φ := by
  classical
  by_contra h
  simp only [not_or] at h
  have h3 : ({φ, star φ, ψ} : Finset (K →+* ℂ)).card = 3 :=
    Finset.card_eq_three.2 ⟨φ, star φ, ψ, star_φ_ne_self.symm, Ne.symm h.1, Ne.symm h.2, rfl⟩
  have := Finset.card_le_univ ({φ, star φ, ψ} : Finset (K →+* ℂ))
  have := card_ringHom
  omega

/-- The CM type `{i ↦ I}` of `ℚ(i)`. -/
noncomputable def Φ : CMType K := CMType.ofPair φ star_φ_ne_self eq_or_eq_star

@[simp]
theorem coe_Φ : (Φ : Set (K →+* ℂ)) = {φ} :=
  CMType.coe_ofPair _ _ _

/-- **Each singleton of an embedding of `ℚ(i)` is a CM type.** -/
theorem exists_coe_eq_singleton (ψ : K →+* ℂ) : ∃ Ψ : CMType K, (Ψ : Set (K →+* ℂ)) = {ψ} := by
  rcases eq_or_eq_star ψ with rfl | rfl
  · exact ⟨Φ, coe_Φ⟩
  · exact ⟨star Φ, by simp [Φ]⟩

/-- **Every CM type of `ℚ(i)` has one embedding.** -/
theorem natCard_eq_one (Ψ : CMType K) : Nat.card Ψ = 1 := by
  have h := Ψ.two_mul_card_eq_finrank
  rw [finrank_eq_two_of_isCyclotomicExtension_four] at h
  omega

/-! `ℚ(i)` has a complex embedding, so its CM types are neither the full embedding set
(`TauCeti.CMType.coe_ne_univ`) nor empty (`TauCeti.CMType.coe_ne_empty`). -/

example (Ψ : CMType K) : (Ψ : Set (K →+* ℂ)) ≠ Set.univ := Ψ.coe_ne_univ

example (Ψ : CMType K) : (Ψ : Set (K →+* ℂ)) ≠ ∅ := Ψ.coe_ne_empty

/-- **The type trace of `{i ↦ I}` at `i` is `I`.** -/
@[simp]
theorem typeTrace_Φ_ζ : Φ.typeTrace ζ = Complex.I := by
  rw [CMType.typeTrace_apply, coe_Φ, finsum_mem_singleton, φ_ζ]

/-- The full trace of `i` vanishes, whereas its type trace for `{i ↦ I}` is `I`
(`typeTrace_Φ_ζ`). -/
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
