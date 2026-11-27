/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.AlgebraicWeight.Hodge
import TauCeti.Data.Fin.Rev

/-!
# Embedding-indexed weights of `GL n` over a number field

The weight of a regular algebraic automorphic representation of `GL n` over a number field `F`
is a family `a = (a_τ)` of dominant `GL n` weights indexed by the embeddings `τ : F → Ω` into an
algebraically closed field of characteristic zero: one weakly decreasing integer sequence
`a_{τ,1} ≥ ⋯ ≥ a_{τ,n}` per embedding, repetitions allowed.  This file develops these families as
`TauCeti.EmbeddingWeight ι n`, the functions from an index type `ι` (in practice `F →+* Ω`) to
`TauCeti.DominantWeight n`, together with the three operations the arithmetic of such weights
uses.

* **Base change.** A field extension `F'/F` restricts embeddings, and pulling a weight back along
  restriction gives `TauCeti.EmbeddingWeight.baseChange`, `(a_{F'})_τ = a_{τ|_F}`.
* **The conjugation condition.** For `F` totally real or CM with complex conjugation `c`, the
  weights of polarized representations lie in
  `(ℤⁿ)_w = {a : a_{τ,i} + a_{τ∘c,n+1-i} = w for all τ, i}`.  The predicate
  `TauCeti.EmbeddingWeight.IsConjDual c w a` states this for any index map `c`; equivalently,
  `a_{τ∘c}` is the contragredient of `a_τ` twisted by `w`
  (`TauCeti.EmbeddingWeight.isConjDual_iff_apply_eq_dual_shift`).
* **Twists.** Tensoring with an algebraic Hecke character of exponents `(b_τ)` adds `b_τ` to every
  entry of `a_τ`, `TauCeti.EmbeddingWeight.twist`; the norm character is the constant family.

The conjugation condition is the one feature of these weights that is arithmetic rather than
combinatorial, and the file records its interaction with each operation: it is preserved by base
change along restriction maps commuting with conjugation, it determines `w` once the family is
nonempty and of positive rank, it moves `w` by `w'` under a twist whose exponents satisfy
`b_τ + b_{τ∘c} = w'`, and it pairs off the Hodge–Tate numbers at `τ` and `τ∘c` so that they sum to
`w + n - 1`, a reflection about `(w + n - 1)/2`
(`TauCeti.EmbeddingWeight.IsConjDual.hodgeMultiset_apply`).  For a CM field and `Ω = ℂ`,
precomposing with complex conjugation and postcomposing with it are the same index map, so the
condition can be stated either way (`TauCeti.EmbeddingWeight.isConjDual_comp_complexConj_iff`);
the postcomposed form commutes with restriction for every extension, so base change preserves it
without any hypothesis on the extension (`TauCeti.EmbeddingWeight.IsConjDual.baseChange`).

Finally `TauCeti.EmbeddingWeight.IsExtremelyRegular` asks that the weight be extremely regular
(`TauCeti.DominantWeight.IsExtremelyRegular`) at some embedding.

## Main definitions

* `TauCeti.EmbeddingWeight`: families of dominant `GL n` weights indexed by `ι`.
* `TauCeti.EmbeddingWeight.ofAntitone`: the family with prescribed antitone coordinates.
* `TauCeti.EmbeddingWeight.baseChange`: pullback along restriction of embeddings.
* `TauCeti.EmbeddingWeight.twist`: adding an integer `b_τ` to every entry of `a_τ`.
* `TauCeti.EmbeddingWeight.IsConjDual`: membership in `(ℤⁿ)_w` for an index map `c`.
* `TauCeti.EmbeddingWeight.IsExtremelyRegular`: extreme regularity at some embedding.

## Main results

* `TauCeti.EmbeddingWeight.baseChange_baseChange`: base change is transitive in a tower.
* `TauCeti.EmbeddingWeight.IsConjDual.comp`: pullback along maps commuting with the index
  involutions preserves the conjugation condition.
* `TauCeti.EmbeddingWeight.IsConjDual.unique`: the integer `w` is determined by `a`.
* `TauCeti.EmbeddingWeight.isConjDual_twist_iff`: the conjugation condition under twists.
* `TauCeti.EmbeddingWeight.isConjDual_iff_hodgeShift_add`: the conjugation condition in terms of
  paired Hodge–Tate coordinates.
* `TauCeti.EmbeddingWeight.IsConjDual.hodgeMultiset_apply`: the Hodge–Tate numbers at conjugate
  embeddings.
* `TauCeti.EmbeddingWeight.isConjDual_comp_complexConj_iff`: for a CM field, precomposition and
  postcomposition with complex conjugation give the same condition.
* `TauCeti.EmbeddingWeight.IsExtremelyRegular.baseChange`: extreme regularity survives base change
  along algebraic extensions.

## References

* T. Barnet-Lamb, T. Gee, D. Geraghty and R. Taylor, *Potential automorphy and change of
  weight*, Ann. of Math. 179 (2014), §2.1.
-/

public section

namespace TauCeti

open NumberField

/-- An **embedding-indexed weight** of `GL n`: a dominant weight `a_τ` for each index `τ : ι`.
For a number field `F` and an algebraically closed field `Ω` of characteristic zero, the index is
`F →+* Ω`, and these are the weights `(ℤⁿ)^{Hom(F,Ω),+}` of regular algebraic representations of
`GL n` over `F`. -/
abbrev EmbeddingWeight (ι : Type*) (n : ℕ) : Type _ := ι → DominantWeight n

namespace EmbeddingWeight

variable {ι ι' : Type*} {n : ℕ}

/-- The embedding-indexed weight with prescribed coordinates `a τ i`, which must be antitone in
`i` for each `τ`. -/
def ofAntitone (a : ι → Fin n → ℤ) (ha : ∀ τ, Antitone (a τ)) : EmbeddingWeight ι n :=
  fun τ => ⟨a τ, ha τ⟩

@[simp]
theorem ofAntitone_apply_coe (a : ι → Fin n → ℤ) (ha : ∀ τ, Antitone (a τ)) (τ : ι) :
    (ofAntitone a ha τ).val = a τ :=
  (rfl)

/-- Two embedding-indexed weights are equal when all their coordinates agree. -/
protected theorem ext {a b : EmbeddingWeight ι n} (h : ∀ τ i, (a τ).val i = (b τ).val i) : a = b :=
  funext fun τ => Subtype.ext (funext (h τ))

protected theorem ext_iff {a b : EmbeddingWeight ι n} : a = b ↔ ∀ τ i, (a τ).val i = (b τ).val i :=
  ⟨fun h _ _ => h ▸ rfl, EmbeddingWeight.ext⟩

/-- The contragredient weight, obtained by negating and reversing the coordinates separately
at each label. -/
def dual (a : EmbeddingWeight ι n) : EmbeddingWeight ι n := fun τ ↦ (a τ).dual

@[simp]
theorem dual_apply (a : EmbeddingWeight ι n) (τ : ι) : a.dual τ = (a τ).dual :=
  (rfl)

@[simp]
theorem dual_dual (a : EmbeddingWeight ι n) : a.dual.dual = a :=
  funext fun τ ↦ by simp

/-! ### Base change -/

section BaseChange

variable {F F' F'' Ω : Type*} [CommRing F] [CommRing F'] [CommRing F''] [CommRing Ω]
  [Algebra F F'] [Algebra F' F''] [Algebra F F''] [IsScalarTower F F' F'']

variable (F') in
/-- **Base change** of a weight along `F → F'`: the weight at `τ : F' → Ω` is the weight at the
restriction `τ|_F`. -/
def baseChange (a : EmbeddingWeight (F →+* Ω) n) : EmbeddingWeight (F' →+* Ω) n :=
  fun τ => a (τ.comp (algebraMap F F'))

@[simp]
theorem baseChange_apply (a : EmbeddingWeight (F →+* Ω) n) (τ : F' →+* Ω) :
    a.baseChange F' τ = a (τ.comp (algebraMap F F')) :=
  (rfl)

@[simp]
theorem baseChange_dual (a : EmbeddingWeight (F →+* Ω) n) :
    a.dual.baseChange F' = (a.baseChange F').dual :=
  (rfl)

/-- Base change along the identity preserves every coordinate. -/
@[simp]
theorem baseChange_self (a : EmbeddingWeight (F →+* Ω) n) : a.baseChange F = a := by
  ext τ : 1
  simp [Algebra.algebraMap_self]

/-- Base change in two steps is base change along the composite extension. -/
@[simp]
theorem baseChange_baseChange (a : EmbeddingWeight (F →+* Ω) n) :
    (a.baseChange F').baseChange F'' = a.baseChange F'' := by
  ext τ : 1
  simp [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]

end BaseChange

/-! ### Twists -/

/-- The **twist** of a weight by integers `b_τ`, adding `b_τ` to every entry of `a_τ`.  Tensoring
with an algebraic Hecke character of exponents `(b_τ)` twists the weight in this way; tensoring
with the `t`-th power of the norm is the twist by the constant `-t`. -/
def twist (a : EmbeddingWeight ι n) (b : ι → ℤ) : EmbeddingWeight ι n := fun τ => (a τ).shift (b τ)

@[simp]
theorem twist_apply (a : EmbeddingWeight ι n) (b : ι → ℤ) (τ : ι) :
    a.twist b τ = (a τ).shift (b τ) :=
  (rfl)

@[simp]
theorem dual_twist (a : EmbeddingWeight ι n) (b : ι → ℤ) :
    (a.twist b).dual = a.dual.twist (-b) :=
  funext fun τ ↦ by simp

@[simp]
theorem twist_zero (a : EmbeddingWeight ι n) : a.twist 0 = a := by
  ext τ : 1
  simp

@[simp]
theorem twist_twist (a : EmbeddingWeight ι n) (b b' : ι → ℤ) :
    (a.twist b).twist b' = a.twist (b + b') := by
  ext τ : 1
  simp

/-- Base change of a twist is the twist of the base change by the restricted exponents. -/
@[simp]
theorem baseChange_twist {F F' Ω : Type*} [CommRing F] [CommRing F'] [CommRing Ω] [Algebra F F']
    (a : EmbeddingWeight (F →+* Ω) n) (b : (F →+* Ω) → ℤ) :
    (a.twist b).baseChange F' = (a.baseChange F').twist fun τ => b (τ.comp (algebraMap F F')) := by
  ext τ : 1
  simp

/-! ### The conjugation condition -/

/-- An embedding-indexed weight **lies in `(ℤⁿ)_w`** for the index map `c` when
`a_{τ,i} + a_{c τ, n + 1 - i} = w` for every `τ` and `i`: the weight at `c τ` is the
contragredient of the weight at `τ`, twisted by `w`.  For a totally real or CM field, `c` is
precomposition with complex conjugation; the condition is stated for any index map. -/
def IsConjDual (a : EmbeddingWeight ι n) (c : ι → ι) (w : ℤ) : Prop :=
  ∀ τ i, (a τ).val i + (a (c τ)).val i.rev = w

theorem isConjDual_iff (a : EmbeddingWeight ι n) (c : ι → ι) (w : ℤ) :
    a.IsConjDual c w ↔ ∀ τ i, (a τ).val i + (a (c τ)).val i.rev = w :=
  Iff.rfl

/-- The conjugation condition says that the weight at `c τ` is the contragredient of the weight
at `τ`, twisted by `w`. -/
theorem isConjDual_iff_apply_eq_dual_shift (a : EmbeddingWeight ι n) (c : ι → ι) (w : ℤ) :
    a.IsConjDual c w ↔ ∀ τ, a (c τ) = (a τ).dual.shift w := by
  refine forall_congr' fun τ => ⟨fun h => Subtype.ext (funext fun i => ?_), fun h i => ?_⟩
  · have := h i.rev
    simp only [Fin.rev_rev] at this
    simp only [DominantWeight.shift_apply, DominantWeight.dual_apply]
    omega
  · simp [h]

theorem IsConjDual.apply_eq {a : EmbeddingWeight ι n} {c : ι → ι} {w : ℤ}
    (h : a.IsConjDual c w) (τ : ι) : a (c τ) = (a τ).dual.shift w :=
  (a.isConjDual_iff_apply_eq_dual_shift c w).1 h τ

/-- In rank one the conjugation condition reads `a_τ + a_{c τ} = w`. -/
theorem isConjDual_iff_of_rank_one (a : EmbeddingWeight ι 1) (c : ι → ι) (w : ℤ) :
    a.IsConjDual c w ↔ ∀ τ, (a τ).val 0 + (a (c τ)).val 0 = w := by
  simp [isConjDual_iff, Fin.forall_fin_one]

/-- The integer `w` with `a ∈ (ℤⁿ)_w` is determined by `a`, as soon as there is an embedding and
the rank is positive. -/
theorem IsConjDual.unique [Nonempty ι] [NeZero n] {a : EmbeddingWeight ι n} {c : ι → ι}
    {w w' : ℤ} (h : a.IsConjDual c w) (h' : a.IsConjDual c w') : w = w' := by
  inhabit ι
  exact (h default 0).symm.trans (h' default 0)

/-- Pulling back along a map `f` that intertwines the index maps `c'` and `c` preserves the
conjugation condition. -/
theorem IsConjDual.comp {a : EmbeddingWeight ι n} {c : ι → ι} {w : ℤ} (h : a.IsConjDual c w)
    {f : ι' → ι} {c' : ι' → ι'} (hf : ∀ τ, f (c' τ) = c (f τ)) :
    IsConjDual (a ∘ f) c' w := fun τ i => by
  simpa [hf] using h (f τ) i

theorem isConjDual_zero (c : ι → ι) : (0 : EmbeddingWeight ι n).IsConjDual c 0 := by
  simp [isConjDual_iff]

theorem IsConjDual.add {a b : EmbeddingWeight ι n} {c : ι → ι} {w w' : ℤ}
    (ha : a.IsConjDual c w) (hb : b.IsConjDual c w') : (a + b).IsConjDual c (w + w') :=
  fun τ i => by
    simp only [Pi.add_apply, DominantWeight.add_apply]
    linarith [ha τ i, hb τ i]

/-- Twisting by exponents with `b_τ + b_{c τ} = w'` moves the conjugation condition from `w` to
`w + w'`; for the `t`-th power of the norm, `b = -t` and `w' = -2t`. -/
theorem isConjDual_twist_iff (a : EmbeddingWeight ι n) {c : ι → ι} {w w' : ℤ} {b : ι → ℤ}
    (hb : ∀ τ, b τ + b (c τ) = w') :
    (a.twist b).IsConjDual c (w + w') ↔ a.IsConjDual c w := by
  refine forall_congr' fun τ => forall_congr' fun i => ?_
  simp only [twist_apply, DominantWeight.shift_apply]
  have := hb τ
  omega

/-- The conjugation condition holds exactly when the Hodge–Tate coordinates at conjugate labels
sum to `w + n - 1` in opposite positions. -/
theorem isConjDual_iff_hodgeShift_add (a : EmbeddingWeight ι n) (c : ι → ι) (w : ℤ) :
    a.IsConjDual c w ↔
      ∀ τ i, (a τ).hodgeShift i + (a (c τ)).hodgeShift i.rev = w + (n : ℤ) - 1 := by
  simp only [isConjDual_iff, DominantWeight.hodgeShift_apply, Fin.natCast_val_rev]
  exact forall₂_congr fun τ i => by omega

/-- The Hodge–Tate numbers at conjugate embeddings pair off to sum to `w + n - 1`, so they are
reflections of each other about `(w + n - 1)/2`: `HT_{c τ}(a) = {w + n - 1 - h : h ∈ HT_τ(a)}`. -/
theorem IsConjDual.hodgeMultiset_apply {a : EmbeddingWeight ι n} {c : ι → ι} {w : ℤ}
    (h : a.IsConjDual c w) (τ : ι) :
    (a (c τ)).hodgeMultiset = (a τ).hodgeMultiset.map (fun x => w + ((n : ℤ) - 1) - x) := by
  rw [h.apply_eq, DominantWeight.hodgeMultiset_shift, DominantWeight.hodgeMultiset_dual,
    Multiset.map_map]
  congr 1
  funext x
  simp only [Function.comp_apply]
  ring

section Complex

open ComplexEmbedding

variable {F K : Type*} [Field F] [Field K]

/-- Over `ℂ`, conjugating the target of embeddings commutes with restriction, so base change
preserves the conjugation condition for `ComplexEmbedding.conjugate`, for every extension. -/
theorem IsConjDual.baseChange [Algebra F K] {a : EmbeddingWeight (F →+* ℂ) n} {w : ℤ}
    (h : a.IsConjDual conjugate w) : (a.baseChange K).IsConjDual conjugate w :=
  h.comp fun τ => conjugate_comp τ (algebraMap F K)

/-- For a CM field and complex coefficients, precomposing embeddings with complex conjugation is
the same as postcomposing them with it, so the two forms of the conjugation condition agree. -/
theorem isConjDual_comp_complexConj_iff [CharZero K] [IsCMField K] [Algebra.IsIntegral ℚ K]
    (a : EmbeddingWeight (K →+* ℂ) n) (w : ℤ) :
    a.IsConjDual (fun τ => τ.comp (IsCMField.complexConj K : K →+* K)) w ↔
      a.IsConjDual conjugate w := by
  have : (fun τ : K →+* ℂ => τ.comp (IsCMField.complexConj K : K →+* K)) = conjugate :=
    funext fun τ => Eq.symm (IsCMField.isConj_complexConj K τ)
  rw [this]

end Complex

/-! ### Extreme regularity -/

/-- An embedding-indexed weight is **extremely regular** when it is extremely regular
(`TauCeti.DominantWeight.IsExtremelyRegular`) at some embedding. -/
def IsExtremelyRegular (a : EmbeddingWeight ι n) : Prop := ∃ τ, (a τ).IsExtremelyRegular

theorem isExtremelyRegular_iff (a : EmbeddingWeight ι n) :
    a.IsExtremelyRegular ↔ ∃ τ, (a τ).IsExtremelyRegular :=
  Iff.rfl

/-- In rank one every weight with a nonempty index is extremely regular. -/
theorem isExtremelyRegular_of_rank_one [Nonempty ι] (a : EmbeddingWeight ι 1) :
    a.IsExtremelyRegular :=
  ⟨Classical.arbitrary ι, DominantWeight.isExtremelyRegular_of_subsingleton _⟩

/-- With no embeddings the existential condition fails, whatever the rank. -/
theorem not_isExtremelyRegular_of_isEmpty [IsEmpty ι] (a : EmbeddingWeight ι n) :
    ¬ a.IsExtremelyRegular :=
  fun ⟨τ, _⟩ => isEmptyElim τ

/-- Extreme regularity is invariant under twists. -/
@[simp]
theorem isExtremelyRegular_twist_iff (a : EmbeddingWeight ι n) (b : ι → ℤ) :
    (a.twist b).IsExtremelyRegular ↔ a.IsExtremelyRegular := by
  simp [isExtremelyRegular_iff]

/-- Pulling back along a surjection preserves extreme regularity. -/
theorem IsExtremelyRegular.comp {a : EmbeddingWeight ι n} (h : a.IsExtremelyRegular)
    {f : ι' → ι} (hf : Function.Surjective f) : IsExtremelyRegular (a ∘ f) := by
  obtain ⟨τ, hτ⟩ := h
  obtain ⟨τ', rfl⟩ := hf τ
  exact ⟨τ', hτ⟩

/-- A witness to extreme regularity after pullback gives a witness at its image label. Unlike
preservation by pullback (`IsExtremelyRegular.comp`), this needs no surjectivity. -/
theorem IsExtremelyRegular.of_comp {a : EmbeddingWeight ι n} {f : ι' → ι}
    (h : IsExtremelyRegular (a ∘ f)) : a.IsExtremelyRegular := by
  obtain ⟨τ, hτ⟩ := h
  exact ⟨f τ, hτ⟩

/-- Extreme regularity survives base change along an algebraic extension, since every embedding
into an algebraically closed field extends. -/
theorem IsExtremelyRegular.baseChange {F F' Ω : Type*} [Field F] [Field F'] [Field Ω]
    [IsAlgClosed Ω] [Algebra F F'] [Algebra.IsAlgebraic F F'] {a : EmbeddingWeight (F →+* Ω) n}
    (h : a.IsExtremelyRegular) : (a.baseChange F').IsExtremelyRegular := by
  refine h.comp fun τ => ?_
  let := τ.toAlgebra
  exact ⟨(IsAlgClosed.lift : F' →ₐ[F] Ω), (IsAlgClosed.lift : F' →ₐ[F] Ω).comp_algebraMap⟩

end EmbeddingWeight

end TauCeti
