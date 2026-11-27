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
# The valued Auslander–Reiten quiver of an Artin algebra

Let `A` be an Artin algebra over a commutative Artinian ring `R`. Its **valued Auslander–Reiten
quiver** has as vertices the isomorphism classes of finitely generated indecomposable
`A`-modules. An arrow `[M] ⟶ [N]` exists exactly when there is an irreducible morphism
`M ⟶ N` and is valued by the dimensions of `Irr(M, N)` over the residue division rings of `N`
and `M`. The partial translation `τ`, the Auslander–Reiten translate, is defined exactly on the
non-projective vertices. In Tau Ceti it is the valued quiver
`TauCeti.ValuedQuiver (TauCeti.IrreducibleMorphismQuiver.valuationMatrix R P)` for the property
`P` of being finitely generated, with the translation
`(ModuleCat.arTranslation R A E hE).valuedTranslation`, where `E` is a Matlis dualizing module
with condition `hE`. The arrow criterion is
`TauCeti.IrreducibleMorphismQuiver.isSome_valuationMatrix_iff`, whose hypotheses are instances here.

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
  University Press (1995), Section VII.1, Propositions VII.1.3 and VII.1.5 and Lemma VII.1.4.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti TauCeti.IrreducibleMorphismQuiver
open scoped ModuleCat.Algebra

universe u v w

variable (R : Type u) (A : Type v) [CommRing R] [IsArtinianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]
  (E : Type u) [AddCommGroup E] [Module R E] [Module.Injective R E]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

variable {R A E hE} in
/-- If the Auslander–Reiten translation sends the class `m` to `t`, then for every class `x`
the valuation of `Irr(t, x)` is the valuation of `Irr(x, m)` with its two entries exchanged. -/
theorem irreducibleMorphismValuation_eq_swap_of_translate_eq_some
    {m t : IrreducibleMorphismQuiver R fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M}
    (h : (arTranslation.{u, v, w} R A E hE).translate m = some t)
    (x : IrreducibleMorphismQuiver R fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M) :
    irreducibleMorphismValuation R t.representative x.representative =
      (irreducibleMorphismValuation R x.representative m.representative).swap := by
  have : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨hp, ⟨e⟩⟩ := ((arTranslation R A E hE).translate_of_eq_some_of_iff (k := R)
    m.representative_property.1 m.representative_property.2
    t.representative_property.1 t.representative_property.2).mp
      (by rw [of_representative m, of_representative t]; exact h)
  obtain ⟨Y, i, p, hip, hY, hS⟩ := exists_isAlmostSplit_arTranslate R E hE m.representative
    m.representative_property.2 hp
  -- Transport the left-hand end to the chosen representative of its class.
  let e₁ := (eqToIso (arTranslation_obj R A E hE _ _)).symm ≪≫ e
  have hS' : (ShortComplex.mk (e₁.inv ≫ i) p (by simp [hip])).IsAlmostSplit :=
    ShortComplex.isAlmostSplit_of_iso (S₁ := ShortComplex.mk i p hip)
      (ShortComplex.isoMk e₁ (Iso.refl _) (Iso.refl _)) hS
  obtain ⟨n, P, hP, ⟨eY⟩⟩ := exists_indecomposable_iso_biproduct Y
  have (j : Fin n) : Module.Finite A (P j) :=
    Module.Finite.of_surjective (eY.hom ≫ biproduct.π P j).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have (j : Fin n) : IsLocalRing (End (P j)) := isLocalRing_end_of_indecomposable (R := R) (hP j)
  have : Module.Finite R (End m.representative) := .equiv End.linearEquiv.symm
  exact hS'.irreducibleMorphismValuation_X₁_eq_swap R P eY x.representative

/-- The valued Auslander–Reiten quiver of an Artin algebra is a valued translation quiver.
An arrow into a non-projective vertex has a corresponding arrow out of its translate,
with the two entries of its valuation exchanged. -/
theorem isValuedTranslationQuiver_valuedTranslation :
    IsValuedTranslationQuiver
      (ValuedQuiver.valuation
        (valuationMatrix R fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M))
      (arTranslation.{u, v, w} R A E hE).valuedTranslation :=
  (ARTranslation.isValuedTranslationQuiver_iff _).2 fun _ _ h x ↦
    valuationMatrix_eq_map_swap (irreducibleMorphismValuation_eq_swap_of_translate_eq_some h x)

end ModuleCat
