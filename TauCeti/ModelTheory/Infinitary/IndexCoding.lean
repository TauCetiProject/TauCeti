/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Index codings

An `IndexCoding ι κ` consists of an injection into `κ` and a decoder recovering the encoded
indices. Padding extends an `ι`-indexed family to `κ` with a chosen default. In particular,
true padding preserves universal quantification and false padding preserves existence; these
are the neutral extensions used for coded infinitary conjunctions and disjunctions.

The API provides identity and composition, codings from equivalences and explicit or inferred
`Encodable` data, sum codings, the underlying embedding, and the padding composition laws.

Adapted from Cameron Freer's `Mathlib/ModelTheory/Infinitary/IndexCoding.lean` in
[cameronfreer/mathlib4](https://github.com/cameronfreer/mathlib4/blob/346a4bd3f95e8591976c91259badc6d2c300f638/Mathlib/ModelTheory/Infinitary/IndexCoding.lean).
-/

public section

universe uι uκ uμ uν

namespace TauCeti

variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} {ν : Type uν}

/-- A coding of the index type `ι` into `κ`: an injection `encode` together with a decoder
that is a left inverse on encoded values. Values outside the range of `encode` may decode to
`none` or to duplicate source branches; the padding semantics only ever relies on
`decode_encode`. -/
structure IndexCoding (ι : Type uι) (κ : Type uκ) where
  /-- The injection. -/
  encode : ι → κ
  /-- The decoder, a left inverse on encoded values. -/
  decode : κ → Option ι
  /-- Decoding recovers every encoded index. -/
  decode_encode : ∀ i, decode (encode i) = some i

namespace IndexCoding

attribute [simp] decode_encode

/-- Two codings with the same `encode` and `decode` are equal; the coherence proof is
irrelevant. -/
@[ext]
theorem ext {c₁ c₂ : IndexCoding ι κ} (he : c₁.encode = c₂.encode)
    (hd : c₁.decode = c₂.decode) : c₁ = c₂ := by
  cases c₁
  cases c₂
  cases he
  cases hd
  rfl

/-- `encode` is injective: `decode_encode` already provides a retraction. -/
theorem encode_injective (c : IndexCoding ι κ) : Function.Injective c.encode := fun i j h ↦
  Option.some_injective ι (by rw [← c.decode_encode i, h, c.decode_encode])

/-- The underlying embedding of a coding. -/
def toEmbedding (c : IndexCoding ι κ) : ι ↪ κ :=
  ⟨c.encode, c.encode_injective⟩

@[simp]
theorem toEmbedding_apply (c : IndexCoding ι κ) (i : ι) : c.toEmbedding i = c.encode i :=
  (rfl)

/-- The identity coding. -/
protected def id (ι : Type uι) : IndexCoding ι ι :=
  ⟨fun i ↦ i, some, fun _ ↦ rfl⟩

@[simp]
theorem id_encode (i : ι) : (IndexCoding.id ι).encode i = i := (rfl)

@[simp]
theorem id_decode (i : ι) : (IndexCoding.id ι).decode i = some i := (rfl)

/-- Forward composition of codings, in the `Equiv.trans` argument order: first `c₁ : ι → κ`,
then `c₂ : κ → μ`. -/
def trans (c₁ : IndexCoding ι κ) (c₂ : IndexCoding κ μ) : IndexCoding ι μ where
  encode := c₂.encode ∘ c₁.encode
  decode m := (c₂.decode m).bind c₁.decode
  decode_encode i := by simp [Function.comp, c₂.decode_encode, c₁.decode_encode]

@[simp]
theorem trans_encode (c₁ : IndexCoding ι κ) (c₂ : IndexCoding κ μ) (i : ι) :
    (c₁.trans c₂).encode i = c₂.encode (c₁.encode i) := (rfl)

@[simp]
theorem trans_decode (c₁ : IndexCoding ι κ) (c₂ : IndexCoding κ μ) (m : μ) :
    (c₁.trans c₂).decode m = (c₂.decode m).bind c₁.decode := (rfl)

/-- Composing the identity coding before a coding leaves it unchanged. -/
@[simp]
theorem id_trans (c : IndexCoding ι κ) : (IndexCoding.id ι).trans c = c := by
  refine ext rfl (funext fun k ↦ ?_)
  simp only [trans, IndexCoding.id]
  rcases c.decode k with _ | i <;> rfl

/-- Composing a coding with the identity coding leaves it unchanged. -/
@[simp]
theorem trans_id (c : IndexCoding ι κ) : c.trans (IndexCoding.id κ) = c := (rfl)

/-- Composition of index codings is associative. -/
theorem trans_assoc (c₁ : IndexCoding ι κ) (c₂ : IndexCoding κ μ) (c₃ : IndexCoding μ ν) :
    (c₁.trans c₂).trans c₃ = c₁.trans (c₂.trans c₃) := by
  refine ext rfl (funext fun m ↦ ?_)
  simpa only [trans_decode] using (Option.bind_assoc (c₃.decode m) c₂.decode c₁.decode).symm

/-- The canonical coding of the left summand into a sum. -/
def sumInl (ι : Type uι) (κ : Type uκ) : IndexCoding ι (ι ⊕ κ) :=
  ⟨Sum.inl, Sum.getLeft?, fun _ ↦ rfl⟩

/-- The canonical coding of the right summand into a sum. -/
def sumInr (ι : Type uι) (κ : Type uκ) : IndexCoding κ (ι ⊕ κ) :=
  ⟨Sum.inr, Sum.getRight?, fun _ ↦ rfl⟩

@[simp]
theorem sumInl_encode (i : ι) : (sumInl ι κ).encode i = Sum.inl i := (rfl)

@[simp]
theorem sumInl_decode (k : ι ⊕ κ) : (sumInl ι κ).decode k = k.getLeft? := (rfl)

@[simp]
theorem sumInr_encode (k : κ) : (sumInr ι κ).encode k = Sum.inr k := (rfl)

@[simp]
theorem sumInr_decode (k : ι ⊕ κ) : (sumInr ι κ).decode k = k.getRight? := (rfl)

/-- Explicit-data variant of `ofEncodable`: build the coding from a *given* encoding value
rather than by instance search. Code that stores a particular `Encodable` as data (e.g. a
coded-family presentation that must not consult ambient instances) uses this, so the compiler
enforces that the resulting syntax depends on the stored encoding. -/
def ofEncodableWith (e : Encodable ι) : IndexCoding ι ℕ :=
  letI := e
  ⟨Encodable.encode, Encodable.decode, Encodable.encodek⟩

/-- The canonical coding of an encodable type into `ℕ`. No choice is involved; a `Countable`
carrier can be upgraded noncomputably via `Encodable.ofCountable` at the call site. -/
def ofEncodable (ι : Type uι) [Encodable ι] : IndexCoding ι ℕ :=
  ofEncodableWith inferInstance

@[simp]
theorem ofEncodableWith_encode (e : Encodable ι) (i : ι) :
    (ofEncodableWith e).encode i = @Encodable.encode ι e i := (rfl)

@[simp]
theorem ofEncodableWith_decode (e : Encodable ι) (n : ℕ) :
    (ofEncodableWith e).decode n = @Encodable.decode ι e n := (rfl)

@[simp]
theorem ofEncodable_encode [Encodable ι] (i : ι) :
    (ofEncodable ι).encode i = Encodable.encode i := (rfl)

@[simp]
theorem ofEncodable_decode [Encodable ι] (n : ℕ) :
    (ofEncodable ι).decode n = Encodable.decode (α := ι) n := (rfl)

/-- The coding induced by an equivalence of carriers. Its decoder always returns the inverse
image, so padding along it never selects the default branch. -/
def ofEquiv (e : ι ≃ κ) : IndexCoding ι κ :=
  ⟨e, fun k ↦ some (e.symm k), fun i ↦ by simp⟩

@[simp]
theorem ofEquiv_encode (e : ι ≃ κ) (i : ι) : (ofEquiv e).encode i = e i := (rfl)

@[simp]
theorem ofEquiv_decode (e : ι ≃ κ) (k : κ) :
    (ofEquiv e).decode k = some (e.symm k) := (rfl)

/-- The coding induced by the identity equivalence is the identity coding. -/
@[simp]
theorem ofEquiv_refl : ofEquiv (Equiv.refl ι) = IndexCoding.id ι := by
  refine ext rfl (funext fun i ↦ ?_)
  simp [ofEquiv, IndexCoding.id]

/-- `ofEquiv` turns equivalence composition into coding composition. -/
theorem ofEquiv_trans (e₁ : ι ≃ κ) (e₂ : κ ≃ μ) :
    ofEquiv (e₁.trans e₂) = (ofEquiv e₁).trans (ofEquiv e₂) := by
  refine ext rfl (funext fun m ↦ ?_)
  simp [ofEquiv, trans]

/-- Composing the coding of an equivalence with the coding of its inverse gives the identity
coding. -/
@[simp]
theorem ofEquiv_trans_ofEquiv_symm (e : ι ≃ κ) :
    (ofEquiv e).trans (ofEquiv e.symm) = IndexCoding.id ι := by
  rw [← ofEquiv_trans, Equiv.self_trans_symm, ofEquiv_refl]

/-- Total extension of a family along a coding: decoded indices select a branch, undecodable
ones get the default. -/
def pad {β : Sort*} (c : IndexCoding ι κ) (default : β) (f : ι → β) : κ → β :=
  fun k ↦ (c.decode k).elim default f

/-- Evaluate padding using the decoder, without unfolding the coding or padding. -/
theorem pad_apply {β : Sort*} (c : IndexCoding ι κ) (default : β) (f : ι → β) (k : κ) :
    c.pad default f k = (c.decode k).elim default f := (rfl)

/-- Padding at an encoded index recovers the original branch. -/
theorem pad_encode {β : Sort*} (c : IndexCoding ι κ) (default : β) (f : ι → β) (i : ι) :
    c.pad default f (c.encode i) = f i := by
  rw [pad, c.decode_encode]; rfl

@[simp]
theorem pad_of_decode_none {β : Sort*} (c : IndexCoding ι κ) {default : β} {f : ι → β} {k : κ}
    (h : c.decode k = none) : c.pad default f k = default := by
  rw [pad, h]; rfl

@[simp]
theorem pad_of_decode_some {β : Sort*} (c : IndexCoding ι κ) {default : β} {f : ι → β} {k : κ}
    {i : ι} (h : c.decode k = some i) : c.pad default f k = f i := by
  rw [pad, h]; rfl

/-- Padding along the identity coding leaves the family unchanged. -/
@[simp]
theorem id_pad {β : Sort*} (default : β) (f : ι → β) :
    (IndexCoding.id ι).pad default f = f := (rfl)

/-- Padding along a composite coding is iterated padding with the same default. -/
theorem pad_trans {β : Sort*} (c₁ : IndexCoding ι κ) (c₂ : IndexCoding κ μ) (default : β)
    (f : ι → β) : (c₁.trans c₂).pad default f = c₂.pad default (c₁.pad default f) := by
  funext m
  simp only [pad, trans]
  rcases c₂.decode m with _ | k <;> rfl

/-- Mapping a padded family maps its default and its original branches. -/
theorem comp_pad {β γ : Sort*} (c : IndexCoding ι κ) (g : β → γ) (default : β) (f : ι → β) :
    g ∘ c.pad default f = c.pad (g default) (g ∘ f) := by
  funext k
  simp only [Function.comp_apply, pad]
  rcases c.decode k with _ | i <;> rfl

/-- Universal quantification is unchanged by padding with `True`. -/
@[simp]
theorem forall_pad_true_iff (c : IndexCoding ι κ) (p : ι → Prop) :
    (∀ k, c.pad True p k) ↔ ∀ i, p i := by
  constructor
  · intro h i
    simpa only [pad_encode] using h (c.encode i)
  · intro h k
    cases hk : c.decode k with
    | none => simp [hk]
    | some i => simpa only [pad_of_decode_some c hk] using h i

/-- Existential quantification is unchanged by padding with `False`. -/
@[simp]
theorem exists_pad_false_iff (c : IndexCoding ι κ) (p : ι → Prop) :
    (∃ k, c.pad False p k) ↔ ∃ i, p i := by
  constructor
  · rintro ⟨k, hk⟩
    cases hd : c.decode k with
    | none => simp [hd] at hk
    | some i => exact ⟨i, by simpa only [pad_of_decode_some c hd] using hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨c.encode i, by simpa only [pad_encode] using hi⟩

end IndexCoding

end TauCeti
