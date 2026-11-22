/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Bicartesian

/-!
# The `3 × 3` lemma for exact categories

A commutative `3 × 3` diagram in an additive category is recorded as a short complex of short
complexes `D : ShortComplex (ShortComplex C)`. Its three objects `D.X₁`, `D.X₂`, `D.X₃` are the
top, middle and bottom rows, and its two morphisms `D.f`, `D.g` are maps of rows; the three
columns are `D.map ShortComplex.π₁`, `D.map ShortComplex.π₂` and `D.map ShortComplex.π₃`.
Every row and every column therefore has zero composite.

This file proves the `3 × 3` lemma for the conflations of an exact structure `E`, intrinsically,
using only Quillen's axioms and no ambient abelian category. Suppose that all three columns are
conflations.

* If the middle row is a conflation, then the top row is a conflation exactly when the bottom
  row is.
* If the top and bottom rows are conflations, then so is the middle row.

The second statement needs the middle row to have zero composite; in the formalization this is
part of the data of the short complex `D.X₂`.

## Implementation notes

Both statements are reduced to the cokernel `Q` of the composite inflation from the top left
corner to the centre of the diagram, using the Noether conflations through `Q` with `Q` prescribed
in advance (`TauCeti.ExactStructure.exists_conflation_of_conflation_comp`). The bottom row is
then obtained by exchanging two quotients of `Q`, and the middle row as a base change of the bottom
row along a bicartesian square, followed by the converse of the Noether conflation. The statement
for the top row follows from the one for the bottom row in the opposite exact category.

## Main results

* `TauCeti.ExactStructure.conflation_of_conflation_comp`: a map whose composite with an
  inflation is an inflation, with induced map on cokernels an inflation, is itself an inflation
  with the expected cokernel.
* `TauCeti.ExactStructure.exists_conflation_comp_of_conflation`: exchanging the quotients of an
  object by two admissible subobjects, `(Q/A')/A ≅ (Q/A)/A'`.
* `TauCeti.ExactStructure.conflation_X₃_of_conflation_X₁` and
  `TauCeti.ExactStructure.conflation_X₁_of_conflation_X₃`: either outer row of a `3 × 3` diagram
  with conflation columns and middle row forces the other one.
* `TauCeti.ExactStructure.conflation_X₁_iff_conflation_X₃`: the two previous statements together.
* `TauCeti.ExactStructure.conflation_X₂_of_conflation_X₁_of_conflation_X₃`: conflation columns
  and outer rows force the middle row to be a conflation.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>. Corollary 3.6 is the `3 × 3` lemma. As there, the proofs
  rest on the Noether isomorphism (Lemma 3.5) and on bicartesian squares (Proposition 2.12).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ExactStructure

variable [HasZeroObject C] [HasBinaryBiproducts C] (E : ExactStructure C)

/-- **The converse of the Noether conflation.** Let `X ⟶ Y ⟶ Z` be a conflation with maps `i`,
`p`, let `j : Y ⟶ W` be such that `i ≫ j` is an inflation with cokernel `c : W ⟶ Q`, and let
`α : Z ⟶ Q` be the induced map on cokernels. If `α` is an inflation with cokernel `β : Q ⟶ V`,
then `j` is an inflation with cokernel `c ≫ β`. -/
theorem conflation_of_conflation_comp {X Y Z W Q V : C} {i : X ⟶ Y} {p : Y ⟶ Z}
    {hip : i ≫ p = 0} (h₁ : E.Conflation (ShortComplex.mk i p hip)) {j : Y ⟶ W} {c : W ⟶ Q}
    {hc : (i ≫ j) ≫ c = 0} (h₂ : E.Conflation (ShortComplex.mk (i ≫ j) c hc)) {α : Z ⟶ Q}
    {β : Q ⟶ V} {hαβ : α ≫ β = 0} (h₃ : E.Conflation (ShortComplex.mk α β hαβ))
    (hα : j ≫ c = p ≫ α) :
    E.Conflation (ShortComplex.mk j (c ≫ β) (by rw [reassoc_of% hα, hαβ, comp_zero])) := by
  -- The kernel `K` of the composite deflation `c ≫ β` receives `j`; comparing the conflations
  -- `X ⟶ Y ⟶ Z` and `X ⟶ K ⟶ Z` by the short five lemma shows that `Y ≅ K`.
  obtain ⟨K, k, r, s, hk, hsr, hK, hS, hkr, hsk⟩ := E.exists_conflation_comp' h₃ h₂
  have hpairK := E.isKernelCokernelPair _ hK
  have : Mono k := hpairK.mono_f
  have : Mono α := (E.isKernelCokernelPair _ h₃).mono_f
  have hj : j ≫ c ≫ β = 0 := by rw [reassoc_of% hα, hαβ, comp_zero]
  obtain ⟨m, hm⟩ : ∃ m : Y ⟶ K, m ≫ k = j := ⟨_, hpairK.lift_f j hj⟩
  let φ : ShortComplex.mk i p hip ⟶ ShortComplex.mk s r hsr :=
    { τ₁ := 𝟙 X
      τ₂ := m
      τ₃ := 𝟙 Z
      comm₁₂ := by
        rw [← cancel_mono k]
        simp [hm, hsk]
      comm₂₃ := by
        rw [← cancel_mono α]
        simp [← hkr, reassoc_of% hm, hα] }
  have : IsIso m := E.isIso₂_of_conflation_of_isIso₁₃ φ h₁ hS
  exact E.conflation_of_iso (S := ShortComplex.mk k (c ≫ β) hk)
    (ShortComplex.isoMk (asIso m).symm (Iso.refl _) (Iso.refl _) (by simp [← hm]) (by simp)) hK

/-- **Exchanging two quotients.** Let `A ⟶ Q ⟶ U` and `A' ⟶ Q ⟶ B` be conflations, with maps
`a`, `b` and `a'`, `b'`, and suppose that the composite `a' ≫ b : A' ⟶ U` is an inflation with
cokernel `p : U ⟶ V`. Then `a ≫ b' : A ⟶ B` is an inflation, and its cokernel is `V`, through a map
`q : B ⟶ V` with `b' ≫ q = b ≫ p`. In the classical notation, `(Q/A')/A ≅ (Q/A)/A'`. -/
theorem exists_conflation_comp_of_conflation {A A' B U V Q : C} {a : A ⟶ Q} {b : Q ⟶ U}
    {hab : a ≫ b = 0} (h₁ : E.Conflation (ShortComplex.mk a b hab)) {a' : A' ⟶ Q} {b' : Q ⟶ B}
    {hab' : a' ≫ b' = 0} (h₂ : E.Conflation (ShortComplex.mk a' b' hab')) {p : U ⟶ V}
    {hp : (a' ≫ b) ≫ p = 0} (h₃ : E.Conflation (ShortComplex.mk (a' ≫ b) p hp)) :
    ∃ (q : B ⟶ V) (hq : (a ≫ b') ≫ q = 0),
      E.Conflation (ShortComplex.mk (a ≫ b') q hq) ∧ b' ≫ q = b ≫ p := by
  -- The kernel `K` of `b ≫ p : Q ⟶ V` is an extension of `A'` by `A`, split by `a'`.
  obtain ⟨K, k, r, s, hk, hsr, hK, hS, hkr, hsk⟩ := E.exists_conflation_comp' h₃ h₁
  have hpairK := E.isKernelCokernelPair _ hK
  have : Mono (a' ≫ b) := (E.isKernelCokernelPair _ h₃).mono_f
  obtain ⟨σ, hσ⟩ : ∃ σ : A' ⟶ K, σ ≫ k = a' :=
    ⟨_, hpairK.lift_f a' (by rw [← Category.assoc]; exact hp)⟩
  have hσr : σ ≫ r = 𝟙 _ := by
    rw [← cancel_mono (a' ≫ b), Category.assoc, ← hkr, reassoc_of% hσ, Category.id_comp]
  subst hσ
  obtain ⟨ρ, hsρ, hσρ, hid⟩ : ∃ ρ : K ⟶ A, s ≫ ρ = 𝟙 _ ∧ σ ≫ ρ = 0 ∧
      ρ ≫ s + r ≫ σ = 𝟙 _ := by
    let spl := (E.isKernelCokernelPair _ hS).splittingOfSection σ hσr
    have hs : spl.s = σ := IsKernelCokernelPair.splittingOfSection_s _ _ _
    refine ⟨spl.r, spl.f_r, ?_, ?_⟩
    · rw [← hs]
      exact spl.s_r
    · rw [← hs]
      exact spl.id
  have hsplit : E.Conflation (ShortComplex.mk σ ρ hσρ) :=
    E.conflation_of_splitting
      { r := r
        s := s
        f_r := hσr
        s_g := hsρ
        id := by rw [add_comm]; exact hid }
  -- Dividing `K ⟶ Q ⟶ V` by `A'` gives the required conflation.
  obtain ⟨α, β, hαβ, hT, hα, hβ⟩ := E.exists_conflation_of_conflation_comp hsplit hK h₂
  have hα' : α = a ≫ b' := by
    rw [← hsk, Category.assoc, hα, reassoc_of% hsρ]
  subst hα'
  exact ⟨β, hαβ, hT, hβ⟩

variable {E}

/-- **The `3 × 3` lemma, top to bottom.** In a `3 × 3` diagram whose three columns and middle
row are conflations, if the top row is a conflation then so is the bottom row. -/
theorem conflation_X₃_of_conflation_X₁ {D : ShortComplex (ShortComplex C)}
    (h₁ : E.Conflation (D.map ShortComplex.π₁)) (h₂ : E.Conflation (D.map ShortComplex.π₂))
    (h₃ : E.Conflation (D.map ShortComplex.π₃)) (hX₁ : E.Conflation D.X₁)
    (hX₂ : E.Conflation D.X₂) : E.Conflation D.X₃ := by
  -- Unfold the columns to their three components.
  replace h₁ : E.Conflation (ShortComplex.mk D.f.τ₁ D.g.τ₁ (D.map ShortComplex.π₁).zero) := h₁
  replace h₂ : E.Conflation (ShortComplex.mk D.f.τ₂ D.g.τ₂ (D.map ShortComplex.π₂).zero) := h₂
  have : Epi D.g.τ₁ := (E.isKernelCokernelPair _ h₁).epi_g
  have : Epi D.X₁.g := (E.isKernelCokernelPair _ hX₁).epi_g
  -- `Q` is a cokernel of the composite inflation from the top left corner to the centre.
  obtain ⟨Q, c, hc, hQ⟩ := (ConflationClass.isInflation_iff _ (D.f.τ₁ ≫ D.X₂.f)).1
    (E.isInflation_comp D.f.τ₁ D.X₂.f (E.isInflation_f h₁) (E.isInflation_f hX₂))
  have : Epi c := (E.isKernelCokernelPair _ hQ).epi_g
  have hc' : (D.X₁.f ≫ D.f.τ₂) ≫ c = 0 := by rw [← D.f.comm₁₂]; exact hc
  have hQ' : E.Conflation (ShortComplex.mk (D.X₁.f ≫ D.f.τ₂) c hc') :=
    E.conflation_of_iso (S := ShortComplex.mk (D.f.τ₁ ≫ D.X₂.f) c hc)
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [D.f.comm₁₂])
        (by simp)) hQ
  -- The two Noether conflations `A'' ⟶ Q ⟶ C` and `C' ⟶ Q ⟶ B''` through `Q`.
  obtain ⟨α₁, β₁, hαβ₁, hI, hα₁, hβ₁⟩ := E.exists_conflation_of_conflation_comp h₁ hX₂ hQ
  obtain ⟨α₂, β₂, hαβ₂, hII, hα₂, hβ₂⟩ := E.exists_conflation_of_conflation_comp hX₁ h₂ hQ'
  have : Epi β₂ := (E.isKernelCokernelPair _ hII).epi_g
  have e₁ : α₂ ≫ β₁ = D.f.τ₃ := by
    rw [← cancel_epi D.X₁.g, ← reassoc_of% hα₂, hβ₁, D.f.comm₂₃]
  have e₂ : α₁ ≫ β₂ = D.X₃.f := by
    rw [← cancel_epi D.g.τ₁, ← reassoc_of% hα₁, hβ₂, ← D.g.comm₁₂]
  have e₃ : β₂ ≫ D.X₃.g = β₁ ≫ D.g.τ₃ := by
    rw [← cancel_epi c, reassoc_of% hβ₂, reassoc_of% hβ₁, D.g.comm₂₃]
  -- The third column is `C' ⟶ Q ⟶ C ⟶ C''`; exchanging the quotients of `Q` by `A''` and by `C'`
  -- gives the bottom row.
  have h₃' : E.Conflation (ShortComplex.mk (α₂ ≫ β₁) D.g.τ₃
      (by rw [e₁]; exact (D.map ShortComplex.π₃).zero)) :=
    E.conflation_of_iso (S := D.map ShortComplex.π₃)
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [e₁]) (by simp)) h₃
  obtain ⟨q, hq₀, hT, hq⟩ := E.exists_conflation_comp_of_conflation hI hII h₃'
  refine E.conflation_of_iso ?_ hT
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [e₂])
    (by simp [← cancel_epi β₂, hq, e₃])

/-- **The `3 × 3` lemma, bottom to top.** In a `3 × 3` diagram whose three columns and middle
row are conflations, if the bottom row is a conflation then so is the top row. -/
theorem conflation_X₁_of_conflation_X₃ {D : ShortComplex (ShortComplex C)}
    (h₁ : E.Conflation (D.map ShortComplex.π₁)) (h₂ : E.Conflation (D.map ShortComplex.π₂))
    (h₃ : E.Conflation (D.map ShortComplex.π₃)) (hX₃ : E.Conflation D.X₃)
    (hX₂ : E.Conflation D.X₂) : E.Conflation D.X₁ := by
  -- The opposite diagram, with rows `D.X₃.op`, `D.X₂.op`, `D.X₁.op`, has the opposite columns
  -- in reverse order.
  have z₁ : D.f.τ₁ ≫ D.g.τ₁ = 0 := (D.map ShortComplex.π₁).zero
  have z₂ : D.f.τ₂ ≫ D.g.τ₂ = 0 := (D.map ShortComplex.π₂).zero
  have z₃ : D.f.τ₃ ≫ D.g.τ₃ = 0 := (D.map ShortComplex.π₃).zero
  let D' : ShortComplex (ShortComplex Cᵒᵖ) :=
    ShortComplex.mk (ShortComplex.opMap D.g) (ShortComplex.opMap D.f) (by
      ext <;> simp [z₁, z₂, z₃])
  exact (E.op_conflation_op_iff D.X₁).1
    (conflation_X₃_of_conflation_X₁ (D := D') ((E.op_conflation_op_iff _).2 h₃)
      ((E.op_conflation_op_iff _).2 h₂) ((E.op_conflation_op_iff _).2 h₁)
      ((E.op_conflation_op_iff _).2 hX₃) ((E.op_conflation_op_iff _).2 hX₂))

/-- **The `3 × 3` lemma for the outer rows.** In a `3 × 3` diagram whose three columns and middle
row are conflations, the top row is a conflation exactly when the bottom row is. -/
theorem conflation_X₁_iff_conflation_X₃ {D : ShortComplex (ShortComplex C)}
    (h₁ : E.Conflation (D.map ShortComplex.π₁)) (h₂ : E.Conflation (D.map ShortComplex.π₂))
    (h₃ : E.Conflation (D.map ShortComplex.π₃)) (hX₂ : E.Conflation D.X₂) :
    E.Conflation D.X₁ ↔ E.Conflation D.X₃ :=
  ⟨fun hX₁ => conflation_X₃_of_conflation_X₁ h₁ h₂ h₃ hX₁ hX₂,
    fun hX₃ => conflation_X₁_of_conflation_X₃ h₁ h₂ h₃ hX₃ hX₂⟩

/-- **The `3 × 3` lemma for the middle row.** In a `3 × 3` diagram whose three columns and outer
rows are conflations, the middle row is a conflation. The middle row has zero composite because
it is a short complex; this hypothesis does not follow from commutativity of the diagram. -/
theorem conflation_X₂_of_conflation_X₁_of_conflation_X₃ {D : ShortComplex (ShortComplex C)}
    (h₁ : E.Conflation (D.map ShortComplex.π₁)) (h₂ : E.Conflation (D.map ShortComplex.π₂))
    (h₃ : E.Conflation (D.map ShortComplex.π₃)) (hX₁ : E.Conflation D.X₁)
    (hX₃ : E.Conflation D.X₃) : E.Conflation D.X₂ := by
  -- Unfold the columns to their three components.
  replace h₁ : E.Conflation (ShortComplex.mk D.f.τ₁ D.g.τ₁ (D.map ShortComplex.π₁).zero) := h₁
  replace h₂ : E.Conflation (ShortComplex.mk D.f.τ₂ D.g.τ₂ (D.map ShortComplex.π₂).zero) := h₂
  have hpair₁ := E.isKernelCokernelPair _ h₁
  have : Epi D.g.τ₁ := hpair₁.epi_g
  have : Epi D.X₁.g := (E.isKernelCokernelPair _ hX₁).epi_g
  -- `Q` is a cokernel of the composite inflation from the top left corner to the centre.
  obtain ⟨Q, c, hc, hQ⟩ := (ConflationClass.isInflation_iff _ (D.X₁.f ≫ D.f.τ₂)).1
    (E.isInflation_comp D.X₁.f D.f.τ₂ (E.isInflation_f hX₁) (E.isInflation_f h₂))
  have hpairQ := E.isKernelCokernelPair _ hQ
  have : Epi c := hpairQ.epi_g
  have hc' : (D.f.τ₁ ≫ D.X₂.f) ≫ c = 0 := by rw [D.f.comm₁₂]; exact hc
  have hQ' : E.Conflation (ShortComplex.mk (D.f.τ₁ ≫ D.X₂.f) c hc') :=
    E.conflation_of_iso (S := ShortComplex.mk (D.X₁.f ≫ D.f.τ₂) c hc)
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [D.f.comm₁₂])
        (by simp)) hQ
  -- The Noether conflation `C' ⟶ Q ⟶ B''`, and the maps `A'' ⟶ Q ⟶ C` induced by the middle
  -- row.
  obtain ⟨α₂, β₂, hαβ₂, hII, hα₂, hβ₂⟩ := E.exists_conflation_of_conflation_comp hX₁ h₂ hQ
  obtain ⟨α₁, hα₁⟩ : ∃ α₁ : D.X₃.X₁ ⟶ Q, D.g.τ₁ ≫ α₁ = D.X₂.f ≫ c :=
    ⟨_, hpair₁.g_desc (D.X₂.f ≫ c) (by rw [← Category.assoc]; exact hc')⟩
  have hz : (D.X₁.f ≫ D.f.τ₂) ≫ D.X₂.g = 0 := by
    rw [← D.f.comm₁₂, Category.assoc, D.X₂.zero, comp_zero]
  obtain ⟨β₁, hβ₁⟩ : ∃ β₁ : Q ⟶ D.X₂.X₃, c ≫ β₁ = D.X₂.g := ⟨_, hpairQ.g_desc D.X₂.g hz⟩
  have e₁ : α₂ ≫ β₁ = D.f.τ₃ := by
    rw [← cancel_epi D.X₁.g, ← reassoc_of% hα₂, hβ₁, D.f.comm₂₃]
  have e₂ : α₁ ≫ β₂ = D.X₃.f := by
    rw [← cancel_epi D.g.τ₁, reassoc_of% hα₁, hβ₂, ← D.g.comm₁₂]
  have e₃ : β₂ ≫ D.X₃.g = β₁ ≫ D.g.τ₃ := by
    rw [← cancel_epi c, reassoc_of% hβ₂, reassoc_of% hβ₁, D.g.comm₂₃]
  have e₄ : α₁ ≫ β₁ = 0 := by
    rw [← cancel_epi D.g.τ₁, reassoc_of% hα₁, hβ₁, D.X₂.zero, comp_zero]
  -- The square `Q ⟶ C`, `Q ⟶ B''`, `C ⟶ C''`, `B'' ⟶ C''` is a pullback, so `A'' ⟶ Q ⟶ C` is the
  -- base change of the bottom row along `C ⟶ C''`.
  let φ : ShortComplex.mk α₂ β₂ hαβ₂ ⟶ D.map ShortComplex.π₃ :=
    { τ₁ := 𝟙 _
      τ₂ := β₁
      τ₃ := D.X₃.g
      comm₁₂ := by simp [e₁]
      comm₂₃ := by simp [e₃] }
  have sq : IsPullback β₁ β₂ D.g.τ₃ D.X₃.g := E.isPullback_of_conflation_of_isIso₁ φ hII h₃
  have hB := E.conflation_baseChange hX₃ sq.flip
  rw [baseChange_def] at hB
  have hα₁' : α₁ = baseChangeι D.X₃ sq.flip :=
    sq.flip.hom_ext (by rw [baseChangeι_fst, e₂]) (by rw [baseChangeι_snd, e₄])
  subst hα₁'
  refine E.conflation_of_iso ?_ (E.conflation_of_conflation_comp h₁ hQ' hB hα₁.symm)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [hβ₁])

end ExactStructure

end TauCeti
