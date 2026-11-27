/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.CategoryTheory.ObjectProperty.Extensions

/-!
# Morphisms inducing bijections on Ext with fixed coefficients

Let `F` be an object of an abelian category.

* `CategoryTheory.IsExtEquivFor F α`: a morphism `α : X' ⟶ X` is an *equivalence for `F`* if
  precomposition with `α` is bijective on `Extⁿ(-, F)` for every `n`. Such morphisms compose and
  satisfy two out of three, and the first map of a short exact sequence is an equivalence for `F`
  exactly when `Ext*(-, F)` vanishes on the third term
  (`CategoryTheory.isExtEquivFor_iff_of_shortExact`).
* The objects on which `Ext*(-, F)` vanishes form a closed class
  (`CategoryTheory.isClosedClass_forall_subsingleton_ext`, for
  `CategoryTheory.ObjectProperty.IsClosedClass`).

Both facts are read off the contravariant long exact Ext sequence of a short exact sequence.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, files
  `src/Lib/Cohomology/Etale/Basic.lean` (declarations `New.Variety.IsCohomEquiv`,
  `New.Variety.IsCohomEquiv.of_isIso`, `New.Variety.IsCohomEquiv.comp_iff`),
  `src/Lib/Cohomology/Etale/BijectiveComparisons.lean` (`New.Variety.IsClosedClass`) and
  `src/Lib/General/Algebra/LongExactSequences.lean` (`New.Variety.isCohomEquiv_iff_subsingleton`);
  Apache 2.0, Copyright 2026 Anthropic, PBC. The statements are adapted from these declarations
  and stated for an arbitrary abelian category.
-/

public section

open CategoryTheory Limits Abelian

universe t

namespace CategoryTheory

/-! ### Equivalences for a coefficient object -/

section IsExtEquivFor

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasExt.{t} 𝒜] (F : 𝒜)

/-- A morphism `α : X' ⟶ X` is an *equivalence for* `F` if precomposition with `α` is a bijection
`Extⁿ(X, F) ⟶ Extⁿ(X', F)` for every `n`. -/
def IsExtEquivFor {X X' : 𝒜} (α : X' ⟶ X) : Prop :=
  ∀ n : ℕ, Function.Bijective ((Ext.mk₀ α).precomp F (zero_add n))

variable {F} {X X' X'' : 𝒜}

/-- An isomorphism is an equivalence for every coefficient object. -/
lemma isExtEquivFor_of_isIso (α : X' ⟶ X) [IsIso α] : IsExtEquivFor F α := fun n ↦ by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨(Ext.mk₀ (inv α)).precomp F (zero_add n), fun x ↦ ?_, fun x ↦ ?_⟩ <;>
  simp only [Ext.precomp, Ext.bilinearComp_apply_apply,
    Ext.mk₀_comp_mk₀_assoc, IsIso.inv_hom_id, IsIso.hom_inv_id, Ext.mk₀_id_comp]

/-- Equivalences for `F` compose. -/
lemma IsExtEquivFor.comp {α' : X'' ⟶ X'} {α : X' ⟶ X} (h' : IsExtEquivFor F α')
    (h : IsExtEquivFor F α) : IsExtEquivFor F (α' ≫ α) := fun n ↦ by
  rw [Ext.precomp_mk₀_comp]
  exact (h' n).comp (h n)

/-- If `α'` is an equivalence for `F`, then `α' ≫ α` is one exactly when `α` is. -/
lemma IsExtEquivFor.comp_iff_right {α' : X'' ⟶ X'} (h' : IsExtEquivFor F α') (α : X' ⟶ X) :
    IsExtEquivFor F (α' ≫ α) ↔ IsExtEquivFor F α :=
  forall_congr' fun n ↦ by rw [Ext.precomp_mk₀_comp]; exact (h' n).of_comp_iff' _

/-- If `α` is an equivalence for `F`, then `α' ≫ α` is one exactly when `α'` is. -/
lemma IsExtEquivFor.comp_iff_left (α' : X'' ⟶ X') {α : X' ⟶ X} (h : IsExtEquivFor F α) :
    IsExtEquivFor F (α' ≫ α) ↔ IsExtEquivFor F α' :=
  forall_congr' fun n ↦ by rw [Ext.precomp_mk₀_comp]; exact Function.Bijective.of_comp_iff _ (h n)

variable {S : ShortComplex 𝒜}

/-- If `Ext*(S.X₃, F)` vanishes, the first map of the short exact sequence `S` is an equivalence
for `F`, by the long exact sequence in the first variable. -/
private lemma isExtEquivFor_of_shortExact (hS : S.ShortExact)
    (h : ∀ n, Subsingleton (Ext.{t} S.X₃ F n)) : IsExtEquivFor F S.f := fun n ↦ by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := Ext.contravariant_sequence_exact₂ hS F x hx
    rw [Subsingleton.elim z 0, Ext.comp_zero]
  · exact Ext.contravariant_sequence_exact₁ hS F x (add_comm 1 n) (Subsingleton.elim _ _)

/-- If the first map of the short exact sequence `S` is an equivalence for `F`, then
`Ext*(S.X₃, F)` vanishes: precomposition with `S.g` is then injective, and its composite with the
bijective precomposition with `S.f` is zero. -/
private lemma subsingleton_ext_of_isExtEquivFor (hS : S.ShortExact) (h : IsExtEquivFor F S.f)
    (n : ℕ) : Subsingleton (Ext.{t} S.X₃ F n) := by
  have hinj := hS.precomp_mk₀_g_injective F (n := n) fun m _ ↦ (h m).2
  refine ⟨fun x x' ↦ hinj ((h n).1 ?_)⟩
  simp [Ext.mk₀_comp_mk₀_assoc, S.zero]

/-- The first map of a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is an equivalence for `F`
exactly when `Extⁿ(X₃, F)` vanishes for every `n`. -/
lemma isExtEquivFor_iff_of_shortExact (hS : S.ShortExact) :
    IsExtEquivFor F S.f ↔ ∀ n, Subsingleton (Ext.{t} S.X₃ F n) :=
  ⟨subsingleton_ext_of_isExtEquivFor hS, isExtEquivFor_of_shortExact hS⟩

/-- The objects `X` with `Extⁿ(X, F) = 0` for every `n` form a closed class. -/
instance isClosedClass_forall_subsingleton_ext :
    ObjectProperty.IsClosedClass fun X : 𝒜 ↦ ∀ n, Subsingleton (Ext.{t} X F n) where
  prop_of_isZero hX n := TauCeti.subsingleton_ext_of_isZero_left hX F n
  prop_X₂_iff_prop_X₃ {S} hS h₁ := by
    -- The long exact sequence makes `Extⁿ(S.X₃, F) ⟶ Extⁿ(S.X₂, F)` bijective.
    have hb (n : ℕ) : Function.Bijective ((Ext.mk₀ S.g).precomp F (zero_add n)) :=
      ⟨hS.precomp_mk₀_g_injective F fun m _ y ↦ ⟨0, @Subsingleton.elim _ (h₁ m) _ _⟩,
        fun x ↦ Ext.contravariant_sequence_exact₂ hS F x (@Subsingleton.elim _ (h₁ n) _ _)⟩
    exact forall_congr' fun n ↦ ⟨fun _ ↦ (hb n).1.subsingleton,
      fun _ ↦ (Equiv.ofBijective _ (hb n)).symm.subsingleton⟩

end IsExtEquivFor

end CategoryTheory
