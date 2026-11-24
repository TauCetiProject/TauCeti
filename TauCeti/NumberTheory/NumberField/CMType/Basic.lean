/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Data.Sym.Sym2

/-!
# CM types

A **CM type** on a commutative ring `E` is a set `Φ` of ring homomorphisms `E → ℂ` containing
exactly one embedding from each conjugate pair `{φ, conj ∘ φ}`: the conjugate `star φ` of an
embedding lies in `Φ` exactly when `φ` does not. On a CM field, or a finite product of CM fields,
a CM type is the choice of one complex extension of each real embedding of the maximal totally
real subalgebra; for an abelian variety with complex multiplication by `E` it records the
characters through which `E` acts on the tangent space.

Imposing the partition condition on an arbitrary commutative ring keeps the definition free of
the structure of `E`. It already forces every embedding to differ from its conjugate
(`TauCeti.CMType.ringHom_star_ne_self`), and CM types exist exactly when no embedding is real
(`TauCeti.CMType.nonempty_iff`), so a number field carries a CM type exactly when it is totally
complex.

## Main definitions

* `TauCeti.CMType E`: the CM types on `E`, a `SetLike` family of sets of embeddings `E →+* ℂ`.
* `star Φ`: the complementary CM type `ιΦ = {conj ∘ φ : φ ∈ Φ}`, whose embeddings are those not in
  `Φ`; this makes `CMType E` an `InvolutiveStar`.
* `TauCeti.CMType.induced Φ₀ f`: the CM type induced along `f : E₀ →+* E` by a CM type `Φ₀` on
  `E₀`, consisting of the embeddings `φ` with `φ ∘ f ∈ Φ₀`.

## Main results

* `TauCeti.CMType.star_mem_iff`: `star φ ∈ Φ ↔ φ ∉ Φ`.
* `TauCeti.CMType.coe_star_eq_image`: `ιΦ` is the image of `Φ` under conjugation.
* `TauCeti.CMType.card_ringHom_eq_two_mul`: `#Hom(E, ℂ) = 2 * #Φ`, and
  `TauCeti.CMType.two_mul_card_eq_finrank`: `2 * #Φ = [E : ℚ]` for a number field `E`.
* `TauCeti.CMType.nonempty_iff`: `E` has a CM type iff no embedding `E →+* ℂ` is real, and
  `TauCeti.CMType.nonempty_iff_isTotallyComplex`: a field has a CM type iff it is totally
  complex. In particular every CM field has a CM type.
* `TauCeti.CMType.induced_induced`, `TauCeti.CMType.star_induced`: inducing is transitive and
  commutes with conjugation.

## References

* J. S. Milne, *Complex Multiplication*, §1, Definition 1.8 and the paragraph after it, p.11.
-/

public section

open NumberField

namespace TauCeti

/-- A **CM type** on a commutative ring `E`: a set of ring homomorphisms `E →+* ℂ` containing
exactly one embedding from each conjugate pair `{φ, star φ}`, where `star φ = conj ∘ φ`. On a CM
algebra this is the choice of one complex extension of each real embedding of its maximal totally
real subalgebra. -/
structure CMType (E : Type*) [CommRing E] where
  /-- The complex embeddings selected by the type. -/
  carrier : Set (E →+* ℂ)
  /-- The conjugate of an embedding lies in the type exactly when the embedding does not. -/
  star_mem_iff' : ∀ φ : E →+* ℂ, star φ ∈ carrier ↔ φ ∉ carrier

namespace CMType

variable {E : Type*} [CommRing E]

instance : SetLike (CMType E) (E →+* ℂ) where
  coe := carrier
  coe_injective Φ Ψ h := by cases Φ; cases Ψ; congr

@[simp]
theorem mem_carrier {Φ : CMType E} {φ : E →+* ℂ} : φ ∈ Φ.carrier ↔ φ ∈ Φ :=
  Iff.rfl

@[simp]
theorem coe_mk (s : Set (E →+* ℂ)) (h : ∀ φ : E →+* ℂ, star φ ∈ s ↔ φ ∉ s) :
    ((⟨s, h⟩ : CMType E) : Set (E →+* ℂ)) = s :=
  rfl

/-- Two CM types with the same embeddings are equal. -/
@[ext]
theorem ext {Φ Ψ : CMType E} (h : ∀ φ, φ ∈ Φ ↔ φ ∈ Ψ) : Φ = Ψ :=
  SetLike.ext h

/-- The conjugate of an embedding lies in a CM type exactly when the embedding does not. -/
@[simp]
theorem star_mem_iff (Φ : CMType E) (φ : E →+* ℂ) : star φ ∈ Φ ↔ φ ∉ Φ :=
  Φ.star_mem_iff' φ

/-- No embedding is its own conjugate when `E` carries a CM type. -/
theorem ringHom_star_ne_self (Φ : CMType E) (φ : E →+* ℂ) : star φ ≠ φ := fun h ↦
  iff_not_self (h ▸ Φ.star_mem_iff φ)

/-- **Existence of CM types.** A commutative ring carries a CM type exactly when no complex
embedding is its own conjugate: choose one embedding from each conjugate pair. -/
theorem nonempty_iff : Nonempty (CMType E) ↔ ∀ φ : E →+* ℂ, star φ ≠ φ := by
  refine ⟨fun ⟨Φ⟩ ↦ Φ.ringHom_star_ne_self, fun h ↦ ?_⟩
  -- Identify each embedding with its conjugate and keep the chosen representative of each pair.
  let s : Setoid (E →+* ℂ) := Setoid.ker fun φ ↦ s(φ, star φ)
  let r : (E →+* ℂ) → (E →+* ℂ) := fun φ ↦ (Quotient.mk s φ).out
  have hr (φ : E →+* ℂ) : r φ = φ ∨ r φ = star φ := by
    have : s(r φ, star (r φ)) = s(φ, star φ) := Setoid.ker_def.mp (Quotient.mk_out (s := s) φ)
    rcases Sym2.eq_iff.mp this with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;> simp [h₁]
  have hr_star (φ : E →+* ℂ) : r (star φ) = r φ :=
    congrArg Quotient.out (Quotient.sound (s := s) (by simp [s, Sym2.eq_swap]))
  refine ⟨⟨{φ | r φ = φ}, fun φ ↦ ?_⟩⟩
  simp only [Set.mem_ofPred_eq]
  rw [hr_star]
  rcases hr φ with h₁ | h₁ <;> rw [h₁]
  · simpa using (h φ).symm
  · simpa using h φ

/-- A field carries a CM type exactly when it is totally complex. -/
theorem nonempty_iff_isTotallyComplex {K : Type*} [Field K] :
    Nonempty (CMType K) ↔ IsTotallyComplex K := by
  rw [nonempty_iff, isTotallyComplex_iff]
  refine ⟨fun h w ↦ ?_, fun h φ ↦ ?_⟩
  · rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff]
    exact h w.embedding
  · exact fun hφ ↦ @IsTotallyComplex.complexEmbedding_not_isReal K _ ⟨h⟩ φ
      (ComplexEmbedding.isReal_iff.mpr hφ)

instance {K : Type*} [Field K] [IsTotallyComplex K] : Nonempty (CMType K) :=
  nonempty_iff_isTotallyComplex.mpr inferInstance

/-! ### The complementary type -/

/-- The **complementary CM type** `ιΦ = {conj ∘ φ : φ ∈ Φ}`: its embeddings are exactly those not
in `Φ` (`TauCeti.CMType.mem_star`, `TauCeti.CMType.coe_star_eq_image`). -/
instance : InvolutiveStar (CMType E) where
  star Φ := ⟨(Φ : Set (E →+* ℂ))ᶜ, fun φ ↦ by simp⟩
  star_involutive Φ := SetLike.coe_injective (compl_compl _)

@[simp]
theorem coe_star (Φ : CMType E) : ((star Φ : CMType E) : Set (E →+* ℂ)) = (Φ : Set _)ᶜ :=
  rfl

@[simp]
theorem mem_star {Φ : CMType E} {φ : E →+* ℂ} : φ ∈ star Φ ↔ φ ∉ Φ :=
  Iff.rfl

/-- The complementary type is the image of `Φ` under conjugation, `ιΦ = {conj ∘ φ : φ ∈ Φ}`. -/
theorem coe_star_eq_image (Φ : CMType E) :
    ((star Φ : CMType E) : Set (E →+* ℂ)) = star '' (Φ : Set (E →+* ℂ)) := by
  ext φ
  refine ⟨fun h ↦ ⟨star φ, by simpa using h, star_star φ⟩, ?_⟩
  rintro ⟨ψ, hψ, rfl⟩
  simpa using hψ

/-- A CM type and its complement are different whenever `E` has a complex embedding. -/
theorem star_ne_self [Nonempty (E →+* ℂ)] (Φ : CMType E) : star Φ ≠ Φ := fun h ↦ by
  obtain ⟨φ⟩ := ‹Nonempty (E →+* ℂ)›
  have := SetLike.ext_iff.mp h φ
  simp at this

/-! ### Counting -/

/-- A CM type contains half of the complex embeddings: `#Hom(E, ℂ) = 2 * #Φ`. Both sides vanish
when there are infinitely many embeddings. -/
theorem card_ringHom_eq_two_mul (Φ : CMType E) : Nat.card (E →+* ℂ) = 2 * Nat.card Φ := by
  classical
  -- The complement of `Φ` is in bijection with `Φ` through conjugation.
  let e : ((Φ : Set (E →+* ℂ))ᶜ : Set (E →+* ℂ)) ≃ Φ :=
    { toFun φ := ⟨star φ.val, (Φ.star_mem_iff _).mpr φ.property⟩
      invFun φ := ⟨star φ.val, by simp⟩
      left_inv φ := by simp
      right_inv φ := by simp }
  rw [Nat.card_congr ((Equiv.sumCompl (· ∈ Φ)).symm.trans (Equiv.sumCongr (.refl _) e)),
    ← Nat.card_congr (Equiv.boolProdEquivSum Φ), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

/-- A CM type on a number field `K` has `[K : ℚ] / 2` embeddings. -/
theorem two_mul_card_eq_finrank {K : Type*} [Field K] [NumberField K] (Φ : CMType K) :
    2 * Nat.card Φ = Module.finrank ℚ K := by
  rw [← Φ.card_ringHom_eq_two_mul, Nat.card_eq_fintype_card, Embeddings.card]

/-! ### Induced types -/

variable {E₀ E₁ : Type*} [CommRing E₀] [CommRing E₁]

/-- The CM type **induced** along `f : E₀ →+* E` by a CM type `Φ₀` on `E₀`: the embeddings of `E`
whose composite with `f` lies in `Φ₀`. For a subalgebra `E₀ ⊆ E` these are the embeddings
restricting into `Φ₀`. -/
def induced (Φ₀ : CMType E₀) (f : E₀ →+* E) : CMType E where
  carrier := {φ | φ.comp f ∈ Φ₀}
  star_mem_iff' φ := by
    have : (star φ).comp f = star (φ.comp f) := RingHom.ext fun _ ↦ by simp [RingHom.star_apply]
    simp [this]

@[simp]
theorem mem_induced {Φ₀ : CMType E₀} {f : E₀ →+* E} {φ : E →+* ℂ} :
    φ ∈ Φ₀.induced f ↔ φ.comp f ∈ Φ₀ :=
  Iff.rfl

@[simp]
theorem induced_id (Φ : CMType E) : Φ.induced (RingHom.id E) = Φ := by
  ext; simp

/-- Inducing along `E₀ → E₁ → E` in two steps is inducing along the composite. -/
@[simp]
theorem induced_induced (Φ₀ : CMType E₀) (f : E₀ →+* E₁) (g : E₁ →+* E) :
    (Φ₀.induced f).induced g = Φ₀.induced (g.comp f) := by
  ext; simp [RingHom.comp_assoc]

/-- The type induced by the complementary type is the complement of the induced type. -/
@[simp]
theorem star_induced (Φ₀ : CMType E₀) (f : E₀ →+* E) :
    star (Φ₀.induced f) = (star Φ₀).induced f := by
  ext; simp

end CMType

end TauCeti
