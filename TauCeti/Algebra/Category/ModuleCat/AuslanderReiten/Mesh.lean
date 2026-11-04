/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Quiver
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Sequence
public import TauCeti.Algebra.Category.ModuleCat.Radical
public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.AlmostSplit
import TauCeti.CategoryTheory.Preadditive.Indecomposable

/-!
# The mesh of the Auslander–Reiten quiver of a finite-dimensional algebra

Let `A` be a finite-dimensional algebra over a field `k`, and consider the quiver of irreducible
morphisms of its finitely generated modules, with the partial Auslander–Reiten translation
`ModuleCat.arTranslation` on its vertices. For a non-projective vertex `[M]`, with translate
`[τ M]`, there are equally many arrows `[X] ⟶ [M]` and `[τ M] ⟶ [X]` for every vertex `[X]`
(`ModuleCat.card_arrows_eq_card_arrows_of_translate_eq_some`). This is the mesh relation of the
Auslander–Reiten quiver, read off the almost-split sequence `0 ⟶ τ M ⟶ E ⟶ M ⟶ 0` given by
`ModuleCat.exists_isAlmostSplit_arTranslate`: both counts are the dimension of the morphisms
between `X` and the middle term `E` modulo the radical, in the two directions.

These two dimensions agree by `ModuleCat.finrank_quotient_jacobsonRadicalSubmodule_comm`, in
`TauCeti/Algebra/Category/ModuleCat/Radical.lean`.

The counts are dimensions over `k`. Write `D_X` for the residue division ring of `End X` and `μ`
for the multiplicity of `X` as a summand of the middle term `E`. The finer, valued mesh relation
says that `irr(X, M)` and `irr(τ M, X)` both have dimension `μ` over `D_X`; the relation proved here
is its `k`-dimensional form, obtained by multiplying by `dim_k D_X`. Over an algebraically closed
field `D_X = k`, so the counts are the numbers of arrows of the Auslander–Reiten quiver. Over
other fields they are not the valuations of the valued (species) Auslander–Reiten quiver, which
need the `D_X`-module structure of `irr`. No algebraic closedness is assumed.

## Main results

* `ModuleCat.card_arrows_eq_card_arrows_of_translate_eq_some`: the mesh relation
  `#([X] ⟶ [M]) = #([τ M] ⟶ [X])`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), V.5 and VII.1.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006), IV.4.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti
open scoped ModuleCat.Algebra

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

variable (k A)

/-- **The mesh of the Auslander–Reiten quiver** of a finite-dimensional algebra: if the
Auslander–Reiten translation sends the vertex `m` to `t`, then for every vertex `x` there are
equally many arrows `x ⟶ m` and `t ⟶ x`. Both counts are read off the almost-split sequence
ending at a representative of `m`. -/
theorem card_arrows_eq_card_arrows_of_translate_eq_some
    {m t : IrreducibleMorphismQuiver k fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M}
    (h : (arTranslation.{u, v, w} k A).translate m = some t)
    (x : IrreducibleMorphismQuiver k fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M) :
    Nat.card (x ⟶ m) = Nat.card (t ⟶ x) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  -- The representative of `m` is non-projective, so it ends an almost-split sequence.
  have hp : ¬ Projective m.representative := fun hp ↦ by
    rw [← (arTranslation.{u, v, w} k A).translate_eq_none_iff] at hp
    simp [hp] at h
  obtain ⟨E, i, p, hip, hE, hS⟩ := exists_isAlmostSplit_arTranslate k m.representative
    m.representative_property.2 hp
  have : IsLocalRing (End (arTranslate k m.representative)) :=
    isLocalRing_end_of_indecomposable (R := k) hS.isLeftAlmostSplit_f.indecomposable
  -- The translate of `m` is the class of the initial term of the sequence.
  rw [← IrreducibleMorphismQuiver.of_representative m, (arTranslation k A).translate_of _ _ hp,
    Option.some.injEq] at h
  subst h
  have hA : Module.Finite A (arTranslate k m.representative) := inferInstance
  have hmesh := IrreducibleMorphismQuiver.card_arrows_of_almostSplit_right_eq_left (k := k)
    (P := fun M : ModuleCat.{max u v w} A ↦ Module.Finite A M) hS hA
    m.representative_property.1 x.representative_property.1 x.representative_property.2
    (finrank_quotient_jacobsonRadicalSubmodule_comm k x.representative E)
  rw [IrreducibleMorphismQuiver.of_representative x,
    IrreducibleMorphismQuiver.of_representative m] at hmesh
  -- The two descriptions of the class of `τ M` agree, since `arTranslation` is `arTranslate`.
  convert hmesh using 3
  exact (IrreducibleMorphismQuiver.of_eq_of_iff _ _ _ _).2 ⟨eqToIso (arTranslation_obj k A _ _)⟩

end ModuleCat
