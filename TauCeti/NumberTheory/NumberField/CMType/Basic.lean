/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.Algebra.Star.Basic
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.CMField
import Mathlib.Data.Sym.Sym2
import TauCeti.Algebra.Algebra.Pi

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
complex. In particular `ℚ` has no CM type.

## Main definitions

* `TauCeti.CMType E`: the CM types on `E`, a `SetLike` family of sets of embeddings `E →+* ℂ`.
* `star Φ`: the complementary CM type `ιΦ = {conj ∘ φ : φ ∈ Φ}`, whose embeddings are those not in
  `Φ`; this makes `CMType E` an `InvolutiveStar`.
* `TauCeti.CMType.ofPair φ`: the CM type `{φ}` when the embeddings are exactly `φ` and its
  distinct conjugate, as for an imaginary quadratic field.
* `TauCeti.CMType.induced Φ₀ f`: the CM type induced along `f : E₀ →+* E` by a CM type `Φ₀` on
  `E₀`, consisting of the embeddings `φ` with `φ ∘ f ∈ Φ₀`.
* `TauCeti.CMType.StarCompCommute E`: every ring endomorphism of `ℂ` commutes with complex
  conjugation on the embeddings of `E`, as on a CM field.
* The action `σΦ = {σ ∘ φ : φ ∈ Φ}` of `Aut(ℂ)` on the CM types of such an `E`.

## Main results

* `TauCeti.CMType.star_mem_iff`: `star φ ∈ Φ ↔ φ ∉ Φ`.
* `TauCeti.CMType.coe_ne_univ`, `TauCeti.CMType.coe_ne_empty`: when `E` has an embedding, a CM
  type is neither the full set of embeddings nor empty.
* `TauCeti.CMType.coe_star_eq_image`: `ιΦ` is the image of `Φ` under conjugation.
* `TauCeti.CMType.card_ringHom_eq_two_mul`: `#Hom(E, ℂ) = 2 * #Φ`, and
  `TauCeti.CMType.two_mul_card_eq_finrank`: `2 * #Φ = [E : ℚ]` for a number field `E`.
* `TauCeti.CMType.nonempty_iff`: `E` has a CM type iff no embedding `E →+* ℂ` is real, and
  `TauCeti.CMType.nonempty_iff_isTotallyComplex`: a field has a CM type iff it is totally
  complex. In particular every CM field has a CM type.
* `TauCeti.CMType.induced_induced`, `TauCeti.CMType.star_induced`: inducing is transitive and
  commutes with conjugation.
* `TauCeti.CMType.induced_algebraMap_injective`: inducing along an algebraic extension of fields
  is injective, since every complex embedding extends (`NumberField.ComplexEmbedding.lift`).
* `TauCeti.CMType.exists_induced_algebraMap_eq_iff`: the fibre criterion, a CM type on `E` is
  induced from the subextension `F` exactly when membership depends only on the restriction
  to `F`.
* `TauCeti.CMType.instStarCompCommutePi`: a finite product of rings with `StarCompCommute`, such
  as a finite product of CM fields, has it.
* `TauCeti.CMType.coe_smul`: `σΦ` is the image of `Φ` under `φ ↦ σ ∘ φ`, and
  `TauCeti.CMType.star_smul`: `ι(σΦ) = σ(ιΦ)`.

## References

* J. S. Milne, *Complex Multiplication*, §1, Definition 1.8 and the paragraph after it, p.11, and
  p.13, footnote 3.
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

/-- A CM type is not the full set of embeddings when `E` has an embedding: it would contain a
whole conjugate pair. -/
theorem coe_ne_univ [Nonempty (E →+* ℂ)] (Φ : CMType E) : (Φ : Set (E →+* ℂ)) ≠ Set.univ :=
  fun hΦ ↦ by
    obtain ⟨φ⟩ := ‹Nonempty (E →+* ℂ)›
    have h := Φ.star_mem_iff φ
    simp [← SetLike.mem_coe, hΦ] at h

/-- A CM type is not empty when `E` has an embedding: it would miss a whole conjugate pair. -/
theorem coe_ne_empty [Nonempty (E →+* ℂ)] (Φ : CMType E) : (Φ : Set (E →+* ℂ)) ≠ ∅ :=
  fun hΦ ↦ by
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

@[simp]
theorem mem_ofPair {φ : E →+* ℂ} {hφ : star φ ≠ φ} {h : ∀ ψ : E →+* ℂ, ψ = φ ∨ ψ = star φ}
    {ψ : E →+* ℂ} : ψ ∈ ofPair φ hφ h ↔ ψ = φ :=
  Iff.rfl

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

/-- `ℚ` has no CM type: its only complex embedding is real. -/
instance : IsEmpty (CMType ℚ) :=
  ⟨fun Φ ↦ Φ.ringHom_star_ne_self (Rat.castHom ℂ) (Subsingleton.elim _ _)⟩

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

/-- The complement of the CM type `{φ}` is the CM type `{star φ}`. -/
@[simp]
theorem star_ofPair (φ : E →+* ℂ) (hφ : star φ ≠ φ) (h : ∀ ψ : E →+* ℂ, ψ = φ ∨ ψ = star φ) :
    star (ofPair φ hφ h) =
      ofPair (star φ) (by simpa using hφ.symm) (fun ψ ↦ by simpa [or_comm] using h ψ) := by
  ext ψ
  rcases h ψ with rfl | rfl <;> simp [hφ.symm]

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
    simp [← RingHom.star_comp_right]

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

/-! ### The action of `Aut(ℂ)` -/

/-- Every ring endomorphism `σ` of `ℂ` commutes with complex conjugation on the complex embeddings
of `E`: `conj ∘ σ ∘ φ = σ ∘ conj ∘ φ`. This holds on a CM field
(`TauCeti.CMType.instStarCompCommuteOfIsCMField`) and makes `Aut(ℂ)` act on CM types. -/
class StarCompCommute (E : Type*) [CommRing E] : Prop where
  /-- Complex conjugation commutes with `σ` on embeddings. -/
  star_comp (σ : ℂ →+* ℂ) (φ : E →+* ℂ) : star (σ.comp φ) = σ.comp (star φ)

/-- On a CM field, complex conjugation commutes with every ring endomorphism of `ℂ` on
embeddings (`RingHom.star_comp`). -/
instance instStarCompCommuteOfIsCMField {K : Type*} [Field K] [CharZero K]
    [Algebra.IsIntegral ℚ K] [IsCMField K] : StarCompCommute K :=
  ⟨RingHom.star_comp⟩

/-- A finite product of rings on whose complex embeddings every endomorphism of `ℂ` commutes with
complex conjugation has the same property, since every complex embedding of the product factors
through a projection (`AlgHom.exists_eq_comp_piEvalAlgHom`). In particular this holds for a
finite product of CM fields. -/
instance instStarCompCommutePi {ι : Type*} [Finite ι] (F : ι → Type*) [∀ i, CommRing (F i)]
    [∀ i, StarCompCommute (F i)] : StarCompCommute (∀ i, F i) where
  star_comp σ φ := by
    obtain ⟨i, ψ, h⟩ := AlgHom.exists_eq_comp_piEvalAlgHom φ.toNatAlgHom
    obtain rfl : φ = (ψ : F i →+* ℂ).comp (Pi.evalRingHom F i) := RingHom.ext fun x ↦ by
      simpa using (AlgHom.congr_fun h x).trans (AlgHom.comp_apply ψ (Pi.evalAlgHom ℕ F i) x)
    ext x
    simpa [RingHom.star_apply, RingHom.comp_apply] using
      RingHom.congr_fun (StarCompCommute.star_comp σ (ψ : F i →+* ℂ)) (x i)

section StarCompCommute

variable [StarCompCommute E]

/-- `σ ∈ Aut(ℂ)` sends a CM type `Φ` to `σΦ = {σ ∘ φ : φ ∈ Φ}`, written as
`{ψ | σ⁻¹ ∘ ψ ∈ Φ}`. -/
instance : SMul (RingAut ℂ) (CMType E) where
  smul σ Φ :=
    { carrier := {ψ | (σ.symm : ℂ →+* ℂ).comp ψ ∈ Φ}
      star_mem_iff' ψ := by
        rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← StarCompCommute.star_comp, star_mem_iff] }

/-- `ψ ∈ σΦ` exactly when `σ⁻¹ ∘ ψ ∈ Φ`. -/
theorem mem_smul {σ : RingAut ℂ} {Φ : CMType E} {ψ : E →+* ℂ} :
    ψ ∈ σ • Φ ↔ (σ.symm : ℂ →+* ℂ).comp ψ ∈ Φ :=
  Iff.rfl

/-- The action `σΦ = {σ ∘ φ : φ ∈ Φ}` of `Aut(ℂ)` on CM types. -/
instance : MulAction (RingAut ℂ) (CMType E) where
  one_smul Φ := ext fun ψ ↦ by simp [mem_smul, RingAut.one_eq_refl]
  mul_smul σ τ Φ := ext fun ψ ↦ by
    have h : ((σ * τ).symm : ℂ →+* ℂ).comp ψ =
        (τ.symm : ℂ →+* ℂ).comp ((σ.symm : ℂ →+* ℂ).comp ψ) := by
      ext; simp [← RingAut.inv_apply]
    rw [mem_smul, mem_smul, mem_smul, h]

/-- `σ ∘ φ ∈ σΦ` exactly when `φ ∈ Φ`. -/
@[simp]
theorem comp_mem_smul_iff {σ : RingAut ℂ} {Φ : CMType E} {φ : E →+* ℂ} :
    (σ : ℂ →+* ℂ).comp φ ∈ σ • Φ ↔ φ ∈ Φ := by
  rw [mem_smul, ← RingHom.comp_assoc]
  simp

/-- As a set, `σΦ` is the image of `Φ` under `φ ↦ σ ∘ φ`. -/
theorem coe_smul (σ : RingAut ℂ) (Φ : CMType E) :
    ((σ • Φ : CMType E) : Set (E →+* ℂ)) = RingHom.comp (σ : ℂ →+* ℂ) '' (Φ : Set (E →+* ℂ)) := by
  ext ψ
  refine ⟨fun h ↦ ⟨(σ.symm : ℂ →+* ℂ).comp ψ, mem_smul.mp h, RingHom.ext fun x ↦ by simp⟩, ?_⟩
  rintro ⟨φ, hφ, rfl⟩
  exact comp_mem_smul_iff.mpr hφ

/-- Taking the complementary type commutes with the action of `Aut(ℂ)`: `ι(σΦ) = σ(ιΦ)`. -/
theorem star_smul (σ : RingAut ℂ) (Φ : CMType E) : star (σ • Φ) = σ • star Φ := by
  ext ψ
  simp only [mem_star, mem_smul]

end StarCompCommute

end CMType

/-! ### Inducing along algebraic extensions -/

namespace CMType

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

/-- Inducing along an algebraic extension of fields is injective: a CM type on `F` is recovered
from the type it induces on `E`, since every embedding of `F` extends to `E`. -/
theorem induced_algebraMap_injective :
    Function.Injective fun Φ₀ : CMType F ↦ Φ₀.induced (algebraMap F E) := by
  intro Φ₀ Φ₁ h
  ext φ₀
  simpa using SetLike.ext_iff.1 h (ComplexEmbedding.lift E φ₀)

/-- Two CM types on `F` inducing the same type along an algebraic extension `E / F` are equal. -/
@[simp]
theorem induced_algebraMap_inj {Φ₀ Φ₁ : CMType F} :
    Φ₀.induced (algebraMap F E) = Φ₁.induced (algebraMap F E) ↔ Φ₀ = Φ₁ :=
  induced_algebraMap_injective.eq_iff

/-- **The fibre criterion.** A CM type `Φ` on `E` is induced from a CM type on the subextension
`F` exactly when membership in `Φ` depends only on the restriction to `F`: two embeddings of `E`
agreeing on `F` are both in `Φ` or both outside it. -/
theorem exists_induced_algebraMap_eq_iff (Φ : CMType E) :
    (∃ Φ₀ : CMType F, Φ₀.induced (algebraMap F E) = Φ) ↔
      ∀ φ ψ : E →+* ℂ, (∀ x : F, φ (algebraMap F E x) = ψ (algebraMap F E x)) →
        (φ ∈ Φ ↔ ψ ∈ Φ) := by
  constructor
  · rintro ⟨Φ₀, rfl⟩ φ ψ h
    simp [show φ.comp (algebraMap F E) = ψ.comp (algebraMap F E) from RingHom.ext h]
  · intro h
    have key {φ ψ : E →+* ℂ} (hφψ : φ.comp (algebraMap F E) = ψ.comp (algebraMap F E)) :
        φ ∈ Φ ↔ ψ ∈ Φ :=
      h φ ψ (RingHom.congr_fun hφψ)
    -- The type on `F` consists of the embeddings whose chosen lift to `E` lies in `Φ`.
    refine ⟨⟨{φ₀ | ComplexEmbedding.lift E φ₀ ∈ Φ}, fun φ₀ ↦ ?_⟩, ?_⟩
    · -- `lift (star φ₀)` and `star (lift φ₀)` both restrict to `star φ₀`.
      have : (ComplexEmbedding.lift E (star φ₀)).comp (algebraMap F E) =
          (star (ComplexEmbedding.lift E φ₀)).comp (algebraMap F E) := by
        rw [← ComplexEmbedding.conjugate, ComplexEmbedding.conjugate_comp]
        simp
      simp only [Set.mem_ofPred_eq, key this, Φ.star_mem_iff]
    · ext φ
      exact key (ComplexEmbedding.lift_comp_algebraMap E _)

end CMType

end TauCeti
