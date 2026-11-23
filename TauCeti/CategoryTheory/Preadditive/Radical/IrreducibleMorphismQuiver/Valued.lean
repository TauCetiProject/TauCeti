/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.ValuedTranslation
public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.Translation
public import TauCeti.CategoryTheory.Preadditive.Radical.Valuation

/-!
# The valued quiver of irreducible morphisms

Let `C` be a `k`-linear category with binary biproducts and `P` a property of its objects. The
vertices of `TauCeti.IrreducibleMorphismQuiver k P` are the isomorphism classes of indecomposable
objects satisfying `P`. This file equips them with the structure of a *valued* quiver in the sense
of `TauCeti/Combinatorics/Quiver/ValuedTranslation.lean`: the pair `(a_{MN}, b_{MN})` of
dimensions of the space `Irr(M, N)` of irreducible morphisms between representatives over the
residue division rings of `N` and of `M` (`TauCeti.irreducibleMorphismValuation`) values one arrow
`[M] ⟶ [N]` when both of its entries are positive, and there is no arrow otherwise. When the
representatives have local endomorphism rings and `Irr(M, N)` is finite-dimensional, this means
there is an arrow exactly when an irreducible morphism `M ⟶ N` exists
(`TauCeti.IrreducibleMorphismQuiver.isSome_valuationMatrix_iff`). This is the valued quiver
`TauCeti.ValuedQuiver (TauCeti.IrreducibleMorphismQuiver.valuationMatrix k P)`; the vertex of the
valued quiver at a class `a` is `TauCeti.ValuedQuiver.of a`.

An Auslander-Reiten translation `T` on the objects satisfying `P` defines a partial translation
`TauCeti.ARTranslation.valuedTranslation T` of this valued quiver: it is defined exactly at the
non-projective classes and is injective there. The final result,
`TauCeti.ARTranslation.isValuedTranslationQuiver_iff`, reduces the condition of a valued
translation quiver to an identity of valuation matrices along the translation, which is how the
valued Auslander-Reiten quiver of a finite-dimensional algebra is shown to be a valued
translation quiver in `TauCeti/Algebra/Category/ModuleCat/AuslanderReiten/ValuedQuiver.lean`.

## Main definitions

* `TauCeti.IrreducibleMorphismQuiver.valuationMatrix k P`: the valuation of `Irr(M, N)` between
  representatives, when both of its entries are positive.
* `TauCeti.ARTranslation.valuedTranslation T`: the partial translation of the valued quiver.

## Main results

* `TauCeti.IrreducibleMorphismQuiver.valuationMatrix_eq_some_iff`: the valuation matrix records
  the valuation of `Irr(M, N)`.
* `TauCeti.IrreducibleMorphismQuiver.isSome_valuationMatrix_iff`: between classes with local
  endomorphism rings and finite-dimensional `Irr(M, N)`, there is an arrow exactly when an
  irreducible morphism exists.
* `TauCeti.ARTranslation.isValuedTranslationQuiver_iff`: the condition of a valued translation
  quiver for the translation of `T`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section VII.1.
-/

public section

open CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasBinaryBiproducts C]

namespace TauCeti

namespace IrreducibleMorphismQuiver

variable (k : Type w) [Ring k] [Linear k C] (P : ObjectProperty C)

/-- **The valuation matrix of the quiver of irreducible morphisms**: at a pair of classes, the
valuation `(a, b)` of the space of irreducible morphisms between their representatives, as a pair
of positive integers, when both entries are positive, and `none` otherwise. -/
noncomputable def valuationMatrix (a b : IrreducibleMorphismQuiver k P) : Option (ℕ+ × ℕ+) :=
  if h : 0 < (irreducibleMorphismValuation k a.representative b.representative).1 ∧
      0 < (irreducibleMorphismValuation k a.representative b.representative).2 then
    some (⟨_, h.1⟩, ⟨_, h.2⟩)
  else none

variable {k P}

/-- **The valuation matrix records the valuation**: it takes the value `p` exactly when the
valuation of the space of irreducible morphisms between representatives is `p`. -/
theorem valuationMatrix_eq_some_iff {a b : IrreducibleMorphismQuiver k P} {p : ℕ+ × ℕ+} :
    valuationMatrix k P a b = some p ↔
      irreducibleMorphismValuation k a.representative b.representative =
        ((p.1 : ℕ), (p.2 : ℕ)) := by
  unfold valuationMatrix
  split_ifs with h
  · rw [Option.some_inj, Prod.ext_iff, Prod.ext_iff, ← PNat.coe_inj, ← PNat.coe_inj, PNat.mk_coe,
      PNat.mk_coe]
  · refine iff_of_false (by simp) fun hp ↦ h ?_
    rw [hp]
    exact ⟨p.1.pos, p.2.pos⟩

/-- The valuation matrix is undefined exactly when an entry of the valuation vanishes. -/
theorem valuationMatrix_eq_none_iff {a b : IrreducibleMorphismQuiver k P} :
    valuationMatrix k P a b = none ↔
      ¬ (0 < (irreducibleMorphismValuation k a.representative b.representative).1 ∧
        0 < (irreducibleMorphismValuation k a.representative b.representative).2) := by
  unfold valuationMatrix
  split_ifs with h
  · exact iff_of_false (by simp) (not_not.2 h)
  · exact iff_of_true rfl h

/-- If the valuation at `(a', b')` is the valuation at `(a, b)` with its two entries exchanged,
so is the valuation matrix. -/
theorem valuationMatrix_eq_map_swap {a b a' b' : IrreducibleMorphismQuiver k P}
    (h : irreducibleMorphismValuation k a'.representative b'.representative =
      (irreducibleMorphismValuation k a.representative b.representative).swap) :
    valuationMatrix k P a' b' = (valuationMatrix k P a b).map Prod.swap := by
  cases hab : valuationMatrix k P a b with
  | none =>
    rw [valuationMatrix_eq_none_iff] at hab
    rw [Option.map_none, valuationMatrix_eq_none_iff, h, Prod.fst_swap, Prod.snd_swap, and_comm]
    exact hab
  | some p =>
    rw [valuationMatrix_eq_some_iff] at hab
    rw [Option.map_some, valuationMatrix_eq_some_iff, h, hab]
    rfl

/-- **There is an arrow exactly when an irreducible morphism exists**, between classes whose
representatives have local endomorphism rings and a finite-dimensional space of irreducible
morphisms. -/
theorem isSome_valuationMatrix_iff {k : Type w} [CommRing k] [Linear k C]
    {a b : IrreducibleMorphismQuiver k P} [IsLocalRing (End a.representative)]
    [IsLocalRing (End b.representative)]
    [Module.Finite k (irreducibleMorphismSpace k a.representative b.representative)] :
    (valuationMatrix k P a b).isSome ↔
      ∃ f : a.representative ⟶ b.representative, IsIrreducibleMorphism f := by
  rw [← not_iff_not, Option.not_isSome_iff_eq_none, valuationMatrix_eq_none_iff,
    irreducibleMorphismValuation_fst_pos_iff, irreducibleMorphismValuation_snd_pos_iff, and_self]

end IrreducibleMorphismQuiver

namespace ARTranslation

open IrreducibleMorphismQuiver

variable {k : Type w} [Ring k] [Linear k C] {P : ObjectProperty C} (T : ARTranslation P)

/-- **The translation of the valued quiver of irreducible morphisms** defined by an
Auslander-Reiten translation: the partial translation `TauCeti.ARTranslation.translate` of the
isomorphism classes, defined exactly at the non-projective classes and injective there. -/
noncomputable def valuedTranslation :
    ValuedQuiver (valuationMatrix k P) ≃. ValuedQuiver (valuationMatrix k P) where
  toFun z := (T.translate z.vertex).map ValuedQuiver.of
  invFun x := by
    classical
    exact if h : ∃ z, T.translate z = some x.vertex then some (.of h.choose) else none
  inv z x := by
    classical
    constructor
    · -- `invFun x = some z` is an equation between a `dite` and `some z`; the ascription
      -- unfolds the coercion of the structure field so that `split_ifs` can see the `dite`.
      intro (hz : _ = some z)
      split_ifs at hz with h
      obtain rfl := Option.some_injective _ hz
      rw [h.choose_spec, Option.map_some]
    · intro hx
      simp only [Option.map_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      have h : ∃ z', T.translate z' = some y := ⟨z.vertex, hy⟩
      rw [dite_eq_left_of_eq_true (eq_true h), T.eq_of_translate_eq_some h.choose_spec hy]

/-- The translation of the valued quiver is the translation of the classes, read on vertices. -/
theorem valuedTranslation_apply (z : ValuedQuiver (valuationMatrix k P)) :
    T.valuedTranslation z = (T.translate z.vertex).map ValuedQuiver.of :=
  (rfl)

/-- The translation of the valued quiver sends `z` to `x` exactly when the Auslander-Reiten
translation sends the class of `z` to that of `x`. -/
@[simp]
theorem valuedTranslation_eq_some_iff {z x : ValuedQuiver (valuationMatrix k P)} :
    T.valuedTranslation z = some x ↔ T.translate z.vertex = some x.vertex := by
  rw [valuedTranslation_apply, Option.map_eq_some_iff]
  exact ⟨fun ⟨_, hy, hyx⟩ ↦ hyx ▸ hy, fun h ↦ ⟨x.vertex, h, rfl⟩⟩

/-- **The condition of a valued translation quiver for an Auslander-Reiten translation**: the
valued quiver of irreducible morphisms is a valued translation quiver for the translation of `T`
exactly when, whenever `T` translates the class `m` to `t`, the valuation from `t` to every class
`x` is the valuation from `x` to `m` with its two entries exchanged. -/
theorem isValuedTranslationQuiver_iff :
    IsValuedTranslationQuiver (ValuedQuiver.valuation (valuationMatrix k P)) T.valuedTranslation ↔
      ∀ ⦃m t : IrreducibleMorphismQuiver k P⦄, T.translate m = some t →
        ∀ x, valuationMatrix k P t x = (valuationMatrix k P x m).map Prod.swap := by
  rw [ValuedQuiver.isValuedTranslationQuiver_iff]
  refine ⟨fun h m t hmt x ↦ ?_, fun h z x hzx w ↦ ?_⟩
  · exact h (z := .of m) (x := .of t) ((T.valuedTranslation_eq_some_iff).2 hmt) (.of x)
  · exact h ((T.valuedTranslation_eq_some_iff).1 hzx) w.vertex

end ARTranslation

end TauCeti
