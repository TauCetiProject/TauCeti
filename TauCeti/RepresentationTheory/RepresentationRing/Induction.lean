/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.Induction.FiniteDimensionalProjection
public import TauCeti.RepresentationTheory.RepresentationRing.Restriction

/-!
# Induction is a homomorphism of modules over the representation ring

For a finite-index subgroup `S ≤ G` over a field `k`, inducing a finite-dimensional representation
is the functor `TauCeti.indFDRepFunctor : FDRep k S ⥤ FDRep k G`. This file passes that functor to
the representation rings of `TauCeti/RepresentationTheory/RepresentationRing/Basic.lean`:

`TauCeti.repRingInd k S : R(S) →+ R(G)`.

It is a homomorphism of **additive groups** only, and unavoidably so: induction does not preserve
the tensor product, and it does not send the trivial representation of `S` to the trivial
representation of `G` -- it sends it to the permutation representation on `G ⧸ S`, of dimension
`S.index`. The structure it *does* carry is one level down. Restriction makes `R(S)` an
`R(G)`-algebra (`TauCeti.repRingRes`), and with respect to that structure induction is
`R(G)`-linear:

`Ind (x · Res y) = (Ind x) · y`,

which is `TauCeti.repRingInd_mul_repRingRes`. This is Frobenius reciprocity in its module form, and
it is the projection formula `TauCeti.indFDRepProjection` of
`TauCeti/RepresentationTheory/Induction/FiniteDimensionalProjection.lean` read on isomorphism
classes: the representation-level isomorphism `Ind_S^G (A ⊗ Res_S^G B) ≅ (Ind_S^G A) ⊗ B` becomes
an identity of classes, and both sides of the displayed equation are additive in each variable, so
the two classes generate the general case. Its immediate consequence is that the image of induction
is an **ideal** of `R(G)`, `TauCeti.repRingIndIdeal` -- the object the Artin and Brauer induction
theorems are statements about.

On characters everything is as expected: the character of an induced virtual representation is the
induced class function of its character (`TauCeti.repRingCharacter_repRingInd`), so the square
formed by the two character homomorphisms, induction on `R(S)` and `TauCeti.indClassFun` commutes.

## Implementation notes

`TauCeti.repRingInd` and `TauCeti.repRingCharacter_repRingInd` leave the field and the group in
independent universes, exactly as `TauCeti.repRingRes` does. `TauCeti.repRingInd_mul_repRingRes`
and `TauCeti.repRingIndIdeal` do not: both are stated with `G` in the universe of `k`. That is a
restriction of the current proof route rather than of the statements — it is inherited from
`TauCeti.indFDRepProjection`, which is built from the `Rep`-level `TauCeti.indProjection`, and the
same caveat is recorded there.

## Main definitions

* `TauCeti.repRingInd`: induction from a finite-index subgroup, as an additive homomorphism of
  representation rings.
* `TauCeti.repRingIndIdeal`: its image, as an ideal of the representation ring of the ambient
  group, for `G` in the universe of `k`.

## Main statements

* `TauCeti.repRingInd_of`: induction sends the class of a representation to the class of the
  induced representation.
* `TauCeti.repRingInd_mul_repRingRes`: **the projection formula on the representation ring**,
  `Ind (x · Res y) = (Ind x) · y`; induction is a homomorphism of `R(G)`-modules.
* `TauCeti.repRingCharacter_repRingInd`: the character of an induced virtual representation is the
  induced class function of its character.
* `TauCeti.mem_repRingIndIdeal_iff`: membership in that ideal is being induced.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part II, §§9-10.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u v

section Definition

variable {k : Type u} {G : Type v} [Field k] [Group G] {S : Subgroup G} [S.FiniteIndex]

/-- **Induction of representations, on the representation ring**: the additive homomorphism
`R(S) →+ R(G)` attached to a finite-index subgroup `S ≤ G`, sending the class of a representation of
`S` to the class of the representation it induces.

It is *not* a ring homomorphism; `TauCeti.repRingInd_mul_repRingRes` is the structure it does
preserve. -/
noncomputable def repRingInd (k : Type u) [Field k] {G : Type v} [Group G] (S : Subgroup G)
    [S.FiniteIndex] : repRing k S →+ repRing k G :=
  SplitK0.map (indFDRepFunctor (k := k) (S := S))

/-- Induction sends the class of a representation to the class of the induced representation. -/
@[simp]
theorem repRingInd_of (A : FDRep k S) :
    repRingInd k S (SplitK0.of A) = SplitK0.of (indFDRep (k := k) (G := G) A) :=
  (SplitK0.map_of _ A).trans (congrArg SplitK0.of (indFDRepFunctor_obj A))

/-- **The character of an induced virtual representation is the induced class function of its
character**: the square formed by `TauCeti.repRingCharacter` on `R(S)` and on `R(G)`,
`TauCeti.repRingInd` and `TauCeti.indClassFun` commutes. -/
@[simp]
theorem repRingCharacter_repRingInd (x : repRing k S) :
    repRingCharacter k G (repRingInd k S x) = indClassFun S (repRingCharacter k S x) := by
  have h := DFunLike.congr_fun (SplitK0.hom_ext
    (f := (repRingCharacter k G).toAddMonoidHom.comp (repRingInd k S))
    (g := (indClassFunAddHom S).comp (repRingCharacter k S).toAddMonoidHom)
    fun A => by simp [indClassFun_ofFDRep_character]) x
  simpa using h

end Definition

section Projection

variable {k G : Type u} [Field k] [Group G] {S : Subgroup G} [S.FiniteIndex]

/-- **The projection formula on the representation ring**, `Ind (x · Res y) = (Ind x) · y`:
induction is a homomorphism of modules over `R(G)`, where `R(S)` is an `R(G)`-module through
restriction. This is Frobenius reciprocity in its module form, and its immediate consequence is
that the image of induction is an ideal, `TauCeti.repRingIndIdeal`. -/
@[simp]
theorem repRingInd_mul_repRingRes (x : repRing k S) (y : repRing k G) :
    repRingInd k S (x * repRingRes k S.subtype y) = repRingInd k S x * y := by
  have key : ∀ (A : FDRep k S) (B : FDRep k G),
      repRingInd k S (SplitK0.of A * repRingRes k S.subtype (SplitK0.of B))
        = repRingInd k S (SplitK0.of A) * SplitK0.of B := fun A B => by
    rw [repRingRes_of, SplitK0.of_mul_of, repRingInd_of, repRingInd_of, SplitK0.of_mul_of,
      SplitK0.of_congr (indFDRepProjection A B)]
  have hA : ∀ (A : FDRep k S) (z : repRing k G),
      repRingInd k S (SplitK0.of A * repRingRes k S.subtype z)
        = repRingInd k S (SplitK0.of A) * z := fun A =>
    DFunLike.congr_fun (SplitK0.hom_ext (f := (repRingInd k S).comp
        ((AddMonoidHom.mulLeft (SplitK0.of A)).comp
          ((repRingRes k S.subtype : repRing k G →+* repRing k S) :
            repRing k G →+ repRing k S)))
      (g := AddMonoidHom.mulLeft (repRingInd k S (SplitK0.of A))) (key A))
  exact DFunLike.congr_fun (SplitK0.hom_ext
    (f := (repRingInd k S).comp (AddMonoidHom.mulRight (repRingRes k S.subtype y)))
    (g := (AddMonoidHom.mulRight y).comp (repRingInd k S)) fun A => hA A y) x

/-- **The image of induction is an ideal of the representation ring** of the ambient group, by the
projection formula. This is the object the Artin and Brauer induction theorems are statements
about: they assert that a multiple of `1`, respectively `1` itself, lies in the ideal generated by
the images of a family of subgroups. -/
noncomputable def repRingIndIdeal (k : Type u) [Field k] {G : Type u} [Group G] (S : Subgroup G)
    [S.FiniteIndex] : Ideal (repRing k G) where
  carrier := Set.range (repRingInd k S)
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ x y⟩
  zero_mem' := ⟨0, map_zero _⟩
  smul_mem' := by
    rintro y _ ⟨x, rfl⟩
    exact ⟨x * repRingRes k S.subtype y, by
      rw [repRingInd_mul_repRingRes, smul_eq_mul, mul_comm]⟩

/-- Membership in `TauCeti.repRingIndIdeal` is being induced. -/
@[simp]
theorem mem_repRingIndIdeal_iff {z : repRing k G} :
    z ∈ repRingIndIdeal k S ↔ ∃ x : repRing k S, repRingInd k S x = z :=
  Iff.rfl

end Projection

end TauCeti
