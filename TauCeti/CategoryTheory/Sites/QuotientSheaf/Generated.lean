/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.QuotientSheaf.Represented

/-!
# Quotient sheaves of pre-relations that locally generate a kernel pair

Let `s t : R ⟶ U` be a pre-relation on an object `U` of a site `(C, J)` and `q : U ⟶ M` an
invariant morphism, `t ≫ q = s ≫ q`. The criterion
`TauCeti.CategoryTheory.quotientSheaf.isIso_desc_of_isLocallySurjective` (Stacks, Lemma 39.20.3
(03C5)) asks that `h_R ⟶ h_U ×_{h_M} h_U` be locally surjective. For a pre-relation that is not
reflexive, such as the pair `(𝟙, σ)` given by an automorphism `σ` of `U`, this fails: the diagonal
points of `U ×_M U` do not come from `R`. The quotient sheaf nevertheless identifies them, since it
identifies each point with itself.

This file proves the variant in which the points `(a, b)` of `U ×_M U` are only required to be,
`J`-locally, either diagonal or related by `R` in one of the two directions: in terms of
morphisms, the sieve `quotientSheaf.relSieve s t a b` of `g` with `g ≫ a = g ≫ b`, or
`g ≫ a = r ≫ t` and `g ≫ b = r ≫ s` for some `r`, or the same with `a` and `b` exchanged, is
`J`-covering whenever `a ≫ q = b ≫ q`. Under this hypothesis and the local surjectivity of
`h_U ⟶ h_M`, the factorisation `U/R ⟶ h_M` of `q` is an isomorphism
(`quotientSheaf.isIso_desc_of_relSieve_mem`).

## Main definitions

* `TauCeti.CategoryTheory.quotientSheaf.relSieve s t a b`: the sieve along which two points `a`,
  `b` of `U` become equal or related by `R`.

## Main results

* `TauCeti.CategoryTheory.quotientSheaf.uliftYoneda_map_π_eq_of_relSieve_mem`: if
  `relSieve s t a b` is `J`-covering, the classes of `a` and `b` in `U/R` agree.
* `TauCeti.CategoryTheory.quotientSheaf.isIso_desc_of_relSieve_mem`: the criterion above.
* `TauCeti.CategoryTheory.quotientSheaf.isoOfRelSieveMem`: the resulting isomorphism
  `U/R ≅ h_M`.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable {R U M : C} (s t : R ⟶ U)

/-- The sieve of the morphisms `g : T' ⟶ T` along which two points `a b : T ⟶ U` become equal,
`g ≫ a = g ≫ b`, or related by the pre-relation `(t, s)` in either direction: `g ≫ a = r ≫ t` and
`g ≫ b = r ≫ s`, or `g ≫ b = r ≫ t` and `g ≫ a = r ≫ s`, for some `r : T' ⟶ R`. -/
def quotientSheaf.relSieve {T : C} (a b : T ⟶ U) : Sieve T where
  arrows T' g := g ≫ a = g ≫ b ∨ (∃ r : T' ⟶ R, r ≫ t = g ≫ a ∧ r ≫ s = g ≫ b) ∨
    ∃ r : T' ⟶ R, r ≫ t = g ≫ b ∧ r ≫ s = g ≫ a
  downward_closed := by
    rintro T' T'' g (h | ⟨r, h₁, h₂⟩ | ⟨r, h₁, h₂⟩) f
    · exact Or.inl (by simp [h])
    · exact Or.inr (Or.inl ⟨f ≫ r, by simp [h₁], by simp [h₂]⟩)
    · exact Or.inr (Or.inr ⟨f ≫ r, by simp [h₁], by simp [h₂]⟩)

/-- Membership in `quotientSheaf.relSieve s t a b`. -/
@[simp]
theorem quotientSheaf.mem_relSieve {T T' : C} (a b : T ⟶ U) (g : T' ⟶ T) :
    quotientSheaf.relSieve s t a b g ↔ g ≫ a = g ≫ b ∨
      (∃ r : T' ⟶ R, r ≫ t = g ≫ a ∧ r ≫ s = g ≫ b) ∨
        ∃ r : T' ⟶ R, r ≫ t = g ≫ b ∧ r ≫ s = g ≫ a :=
  Iff.rfl

/-- The pullback of `quotientSheaf.relSieve s t a b` along `g` is the sieve of the points `g ≫ a`
and `g ≫ b`. -/
@[simp]
theorem quotientSheaf.pullback_relSieve {T T' : C} (a b : T ⟶ U) (g : T' ⟶ T) :
    Sieve.pullback g (quotientSheaf.relSieve s t a b) =
      quotientSheaf.relSieve s t (g ≫ a) (g ≫ b) := by
  ext
  simp

variable [J.Subcanonical] [HasSheafify J (Type (max v w))]

variable {s t}

/-- If the sieve along which two points `a b : T ⟶ U` become equal or related by the pre-relation
is `J`-covering, then `a` and `b` have the same class in the quotient sheaf `U/R`. -/
theorem quotientSheaf.uliftYoneda_map_π_eq_of_relSieve_mem {T : C} {a b : T ⟶ U}
    (h : quotientSheaf.relSieve s t a b ∈ J T) :
    J.uliftYoneda.{w}.map a ≫ quotientSheaf.π J s t =
      J.uliftYoneda.{w}.map b ≫ quotientSheaf.π J s t := by
  have hsep := ((isSheaf_iff_isSheaf_of_type J _).1
    (quotientSheaf.{w} J s t).property).isSeparated _ h
  have key : ∀ (x y : T ⟶ U) {T' : C} (g : T' ⟶ T) (r : T' ⟶ R), r ≫ t = g ≫ x →
      r ≫ s = g ≫ y → J.uliftYoneda.{w}.map (g ≫ x) ≫ quotientSheaf.π J s t =
        J.uliftYoneda.{w}.map (g ≫ y) ≫ quotientSheaf.π J s t := by
    intro x y T' g r hx hy
    simp [← hx, ← hy, quotientSheaf.condition]
  apply J.uliftYonedaEquiv.injective
  refine hsep.ext fun T' g hg ↦ ?_
  simp only [GrothendieckTopology.uliftYonedaEquiv_naturality, ← Functor.map_comp_assoc]
  rcases hg with hg | ⟨r, h₁, h₂⟩ | ⟨r, h₁, h₂⟩
  · rw [hg]
  · rw [key a b g r h₁ h₂]
  · rw [key b a g r h₁ h₂]

/-- **Quotient by a pre-relation that locally generates the kernel pair.** Let `q : U ⟶ M` be
invariant for the pre-relation `(t, s)`, with `h_U ⟶ h_M` `J`-locally surjective. If for any two
points `a, b` of `U` with `a ≫ q = b ≫ q`, `J`-locally, `a = b` or `(a, b)` comes from `R` in one
of the two directions, then the factorisation `U/R ⟶ h_M` of `q` is an isomorphism. -/
theorem quotientSheaf.isIso_desc_of_relSieve_mem {q : U ⟶ M} (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : ∀ ⦃T : C⦄ (a b : T ⟶ U), a ≫ q = b ≫ q → quotientSheaf.relSieve s t a b ∈ J T) :
    IsIso (quotientSheaf.desc (J.uliftYoneda.{w}.map q)
      (quotientSheaf.uliftYoneda_map_condition hq)) := by
  refine quotientSheaf.isIso_desc_of_epi _ _ (J.hom_ext_uliftYoneda fun T κ ↦ ?_)
  let a := J.fullyFaithfulUliftYoneda.{w}.preimage (κ ≫ pullback.fst _ _)
  let b := J.fullyFaithfulUliftYoneda.{w}.preimage (κ ≫ pullback.snd _ _)
  have ha : J.uliftYoneda.{w}.map a = κ ≫ pullback.fst _ _ :=
    J.fullyFaithfulUliftYoneda.map_preimage _
  have hb : J.uliftYoneda.{w}.map b = κ ≫ pullback.snd _ _ :=
    J.fullyFaithfulUliftYoneda.map_preimage _
  have hab : a ≫ q = b ≫ q := J.fullyFaithfulUliftYoneda.{w}.map_injective (by
    simp [ha, hb, pullback.condition])
  rw [← Category.assoc, ← Category.assoc, ← ha, ← hb]
  exact quotientSheaf.uliftYoneda_map_π_eq_of_relSieve_mem (hR a b hab)

/-- **Quotient by a pre-relation that locally generates the kernel pair.** Under the hypotheses of
`quotientSheaf.isIso_desc_of_relSieve_mem`, the quotient sheaf `U/R` is `h_M`. -/
noncomputable def quotientSheaf.isoOfRelSieveMem {q : U ⟶ M} (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : ∀ ⦃T : C⦄ (a b : T ⟶ U), a ≫ q = b ≫ q → quotientSheaf.relSieve s t a b ∈ J T) :
    quotientSheaf.{w} J s t ≅ J.uliftYoneda.{w}.obj M :=
  have := quotientSheaf.isIso_desc_of_relSieve_mem hq hU hR
  asIso (quotientSheaf.desc (J.uliftYoneda.{w}.map q)
    (quotientSheaf.uliftYoneda_map_condition hq))

/-- The isomorphism `quotientSheaf.isoOfRelSieveMem` is the factorisation of `q` through the
quotient sheaf. -/
@[simp]
theorem quotientSheaf.isoOfRelSieveMem_hom {q : U ⟶ M} (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : ∀ ⦃T : C⦄ (a b : T ⟶ U), a ≫ q = b ≫ q → quotientSheaf.relSieve s t a b ∈ J T) :
    (quotientSheaf.isoOfRelSieveMem hq hU hR).hom =
      quotientSheaf.desc (J.uliftYoneda.{w}.map q)
        (quotientSheaf.uliftYoneda_map_condition hq) := by
  rfl

/-- The projection onto the quotient sheaf, followed by `quotientSheaf.isoOfRelSieveMem`, is the
map `h q`. -/
@[reassoc]
theorem quotientSheaf.π_isoOfRelSieveMem_hom {q : U ⟶ M} (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : ∀ ⦃T : C⦄ (a b : T ⟶ U), a ≫ q = b ≫ q → quotientSheaf.relSieve s t a b ∈ J T) :
    quotientSheaf.π J s t ≫ (quotientSheaf.isoOfRelSieveMem hq hU hR).hom =
      J.uliftYoneda.{w}.map q :=
  quotientSheaf.π_desc _ _

/-- The map `h q : h_U ⟶ h_M`, followed by the inverse of `quotientSheaf.isoOfRelSieveMem`, is the
projection onto the quotient sheaf. -/
@[reassoc (attr := simp)]
theorem quotientSheaf.uliftYoneda_map_isoOfRelSieveMem_inv {q : U ⟶ M} (hq : t ≫ q = s ≫ q)
    (hU : Sheaf.IsLocallySurjective (J.uliftYoneda.{w}.map q))
    (hR : ∀ ⦃T : C⦄ (a b : T ⟶ U), a ≫ q = b ≫ q → quotientSheaf.relSieve s t a b ∈ J T) :
    J.uliftYoneda.{w}.map q ≫ (quotientSheaf.isoOfRelSieveMem hq hU hR).inv =
      quotientSheaf.π J s t :=
  (Iso.comp_inv_eq _).2 (quotientSheaf.π_isoOfRelSieveMem_hom hq hU hR).symm

end TauCeti.CategoryTheory
