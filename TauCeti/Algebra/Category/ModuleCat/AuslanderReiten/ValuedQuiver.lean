/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Quiver
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Sequence
public import TauCeti.Algebra.Category.ModuleCat.KrullSchmidt
public import TauCeti.CategoryTheory.AlmostSplit.Residue
public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.Valued

/-!
# The valued Auslander–Reiten quiver of a finite-dimensional algebra

Let `A` be a finite-dimensional algebra over a field `k`. Its **valued Auslander–Reiten quiver**
has as vertices the isomorphism classes of finitely generated indecomposable `A`-modules, one
arrow `[M] ⟶ [N]` exactly when there is an irreducible morphism `M ⟶ N`, valued by the pair
`(a_{MN}, b_{MN})` of dimensions of `Irr(M, N)` over the residue division rings of `N` and of `M`,
and the partial translation `τ`, the Auslander–Reiten translate, defined exactly on the
non-projective vertices. In Tau Ceti it is the valued quiver
`TauCeti.ValuedQuiver (TauCeti.IrreducibleMorphismQuiver.valuationMatrix k P)` for the property
`P` of being finitely generated, with the translation
`(ModuleCat.arTranslation k A).valuedTranslation`. That its arrows are exactly the pairs of classes
admitting an irreducible morphism is `TauCeti.IrreducibleMorphismQuiver.isSome_valuationMatrix_iff`,
whose hypotheses are instances here.

The main theorem, `ModuleCat.isValuedTranslationQuiver_valuedTranslation`, is the **valued mesh**:
this valued quiver is a valued translation quiver. For a non-projective vertex `[M]` with
translate `[τ M]` and every vertex `[X]`, there is an arrow `[τ M] ⟶ [X]` exactly when there is an
arrow `[X] ⟶ [M]`, and its valuation is that of `[X] ⟶ [M]` with the two entries exchanged
(`ModuleCat.irreducibleMorphismValuation_eq_swap_of_translate_eq_some`). Both are read off the
almost-split sequence `0 ⟶ τ M ⟶ E ⟶ M ⟶ 0` of `ModuleCat.exists_isAlmostSplit_arTranslate`,
through the multiplicity of `X` in a decomposition of `E` into indecomposables
(`CategoryTheory.ShortComplex.IsAlmostSplit.irreducibleMorphismValuation_snd_eq_fst`) and the
isomorphism of the residue division rings of `τ M` and `M`
(`CategoryTheory.ShortComplex.IsAlmostSplit.irreducibleMorphismValuation_fst_eq_snd`).

Over a field the arrows of the unvalued quiver of irreducible morphisms count `k`-dimensions
(`TauCeti.IrreducibleMorphismQuiver.card_arrows`), and
`TauCeti.finrank_residueOp_mul_irreducibleMorphismValuation_snd` compares these with the
valuations; the `k`-dimensional mesh `ModuleCat.card_arrows_eq_card_arrows_of_translate_eq_some`
is the shadow of the valued one. No algebraic closedness is assumed.

## Main results

* `ModuleCat.irreducibleMorphismValuation_eq_swap_of_translate_eq_some`: the valuation of
  `Irr(τ M, X)` is the valuation of `Irr(X, M)` with its two entries exchanged.
* `ModuleCat.isValuedTranslationQuiver_valuedTranslation`: **the valued Auslander–Reiten quiver
  is a valued translation quiver.**

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section VII.1, Propositions VII.1.3 and VII.1.5.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti TauCeti.IrreducibleMorphismQuiver
open scoped ModuleCat.Algebra

universe u v w

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

variable {k A} in
/-- **The valuation under the Auslander–Reiten translation**: if the translation sends the class
`m` to `t`, then for every class `x` the valuation of `Irr(t, x)` is the valuation of `Irr(x, m)`
with its two entries exchanged, between representatives. -/
theorem irreducibleMorphismValuation_eq_swap_of_translate_eq_some
    {m t : IrreducibleMorphismQuiver k fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M}
    (h : (arTranslation.{u, v, w} k A).translate m = some t)
    (x : IrreducibleMorphismQuiver k fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M) :
    irreducibleMorphismValuation k t.representative x.representative =
      (irreducibleMorphismValuation k x.representative m.representative).swap := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  -- The representative of `m` is non-projective, so it ends an almost-split sequence.
  have hp : ¬ Projective m.representative := fun hp ↦ by
    rw [← (arTranslation.{u, v, w} k A).translate_eq_none_iff] at hp
    simp [hp] at h
  obtain ⟨E, i, p, hip, hE, hS⟩ := exists_isAlmostSplit_arTranslate k m.representative
    m.representative_property.2 hp
  rw [← IrreducibleMorphismQuiver.of_representative m, (arTranslation k A).translate_of _ _ hp,
    Option.some.injEq] at h
  subst h
  -- Replace the left-hand end `τ M` of the sequence by the representative of its class.
  let e := representativeIso (P := fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M) k
    ((arTranslation k A).prop_obj _ m.representative_property.1)
    (((arTranslation k A).indecomposable_obj_iff _ _ m.representative_property.2).mpr hp) ≪≫
    eqToIso (arTranslation_obj k A _ _)
  have hS' : (ShortComplex.mk (e.hom ≫ i) p (by simp [hip])).IsAlmostSplit :=
    ShortComplex.isAlmostSplit_of_iso (S₁ := ShortComplex.mk i p hip)
      (ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _)) hS
  -- Decompose the middle term into indecomposables, which have local endomorphism rings.
  obtain ⟨n, P, hP, ⟨eE⟩⟩ := exists_indecomposable_iso_biproduct E
  have (j : Fin n) : Module.Finite A (P j) :=
    Module.Finite.of_surjective (eE.hom ≫ biproduct.π P j).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have (j : Fin n) : IsLocalRing (End (P j)) := isLocalRing_end_of_indecomposable (R := k) (hP j)
  have : Module.Finite k (End m.representative) := .equiv End.linearEquiv.symm
  exact hS'.irreducibleMorphismValuation_X₁_eq_swap k P eE x.representative

/-- **The valued mesh: the valued Auslander–Reiten quiver of a finite-dimensional algebra is a
valued translation quiver.** For a non-projective vertex `[M]` with translate `[τ M]` and every
vertex `[X]`, there is an arrow `[τ M] ⟶ [X]` exactly when there is an arrow `[X] ⟶ [M]`, and its
valuation is that of `[X] ⟶ [M]` with the two entries exchanged. -/
theorem isValuedTranslationQuiver_valuedTranslation :
    IsValuedTranslationQuiver
      (ValuedQuiver.valuation
        (valuationMatrix k fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M))
      (arTranslation.{u, v, w} k A).valuedTranslation :=
  (ARTranslation.isValuedTranslationQuiver_iff _).2 fun _ _ h x ↦
    valuationMatrix_eq_map_swap (irreducibleMorphismValuation_eq_swap_of_translate_eq_some h x)

end ModuleCat
