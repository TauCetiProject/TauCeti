/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Envelope.Quotient
public import TauCeti.CategoryTheory.Monoidal.Envelope.Mat.Basic
public import TauCeti.CategoryTheory.Monoidal.Envelope.Karoubi.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Mat
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Karoubi

/-!
# Tensor ideals in additive and idempotent envelopes

A tensor ideal extends entrywise to the additive envelope and by underlying morphisms to the
idempotent completion. These extensions are tensor ideals for the induced monoidal structures:
whiskering matrices tensors each entry with an identity-matrix entry, while whiskering formal
summands tensors with the idempotent of the summand, not the identity of its ambient object.

Consequently `I.mat.karoubi` is the canonical tensor ideal in `Karoubi (Mat_ C)`. Its quotient
uses the existing `MonoidalQuotient` construction. A morphism vanishes in that quotient exactly
when every entry of its underlying matrix belongs to `I`. This is the extension needed to form
semisimplifications after adjoining finite sums and images of idempotents.

## References

* F. M. Goodman and H. Wenzl, *Ideals in the Temperley–Lieb category*, Sections 1–3.
-/

public section

open CategoryTheory CategoryTheory.Idempotents MonoidalCategory

namespace TauCeti.MonoidalIdeal

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- Extend a tensor ideal entrywise to the additive envelope. -/
def mat [MonoidalPreadditive C] (I : MonoidalIdeal C) : MonoidalIdeal (Mat_ C) where
  toMorphismIdeal := I.toMorphismIdeal.mat
  whiskerLeft_mem M _ _ _ hf := by
    rw [MorphismIdeal.mem_mat_hom] at hf ⊢
    intro p q
    rw [Mat_.whiskerLeft_apply]
    exact I.tensorHom_mem_left _ (hf p.2 q.2)
  whiskerRight_mem M hf := by
    rw [MorphismIdeal.mem_mat_hom] at hf ⊢
    intro p q
    rw [Mat_.whiskerRight_apply]
    exact I.tensorHom_mem_right _ (hf p.1 q.1)

/-- Forgetting tensor stability commutes with extension to matrices. -/
@[simp]
theorem mat_toMorphismIdeal [MonoidalPreadditive C] (I : MonoidalIdeal C) :
    I.mat.toMorphismIdeal = I.toMorphismIdeal.mat := (rfl)

/-- Extend a tensor ideal to the idempotent completion. -/
def karoubi (I : MonoidalIdeal C) : MonoidalIdeal (Karoubi C) where
  toMorphismIdeal := I.toMorphismIdeal.karoubi
  whiskerLeft_mem P _ _ _ hf := by
    rw [MorphismIdeal.mem_karoubi_hom] at hf ⊢
    rw [Karoubi.whiskerLeft_f]
    exact I.tensorHom_mem_left P.p hf
  whiskerRight_mem Q hf := by
    rw [MorphismIdeal.mem_karoubi_hom] at hf ⊢
    rw [Karoubi.whiskerRight_f]
    exact I.tensorHom_mem_right Q.p hf

/-- Forgetting tensor stability commutes with extension to formal summands. -/
@[simp]
theorem karoubi_toMorphismIdeal (I : MonoidalIdeal C) :
    I.karoubi.toMorphismIdeal = I.toMorphismIdeal.karoubi := (rfl)

-- The membership lemmas compose with the existing quotient zero-detection API.
example [MonoidalPreadditive C] (I : MonoidalIdeal C)
    {P Q : Karoubi (Mat_ C)} {f : P ⟶ Q} :
    (toMonoidalQuotient I.mat.karoubi).map f = 0 ↔
      ∀ i j, f.f i j ∈ I.hom (P.X.X i) (Q.X.X j) := by
  simp

end TauCeti.MonoidalIdeal
