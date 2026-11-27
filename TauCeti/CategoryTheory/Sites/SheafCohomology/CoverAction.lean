/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.SheafCohomology.Pullback

/-!
# Endomorphisms of a cover acting on sheaf cohomology

Let `P : Sheaf J Ab ⥤ Sheaf K Ab` be a functor between categories of abelian sheaves on sites
`(C, J)` and `(D, K)`, together with an isomorphism `ε : ℤ_K ≅ P ℤ_J` between the constant sheaves.
The motivating case is the inverse image `p⁻¹` along a morphism `p : Y → X`, where `(C, J)` and
`(D, K)` are the sites of `X` and `Y`. An endomorphism `a : Y → Y` with `p ∘ a = p` gives an exact
inverse image `A = a⁻¹ : Sheaf K Ab ⥤ Sheaf K Ab` and an isomorphism `c : P ⋙ A ≅ P`, the
composite `a⁻¹ p⁻¹ ≅ (p ∘ a)⁻¹ = p⁻¹`.

From such a pair `(A, c)` this file builds the induced map
`Sheaf.H.coverAction P ε A c G n : Hⁿ(D, P G) →+ Hⁿ(D, P G)`, written `a^♮` in de Jong–van der
Put, §3.6. It is the cohomology pullback `Sheaf.H.pullback` along `A` followed by the map induced
by `c` on coefficients. The comparison `ℤ_K ⟶ A ℤ_K` it needs is the one transported from `c`
through `ε`, that is `ℤ_K ≅ P ℤ_J ≅ A (P ℤ_J) ≅ A ℤ_K`. With this choice every law below
follows from the composition rules of `Sheaf.H.pullback`, without separate coherence data for the
constant sheaves.

The map reverses composition: for a second pair `(B, d)`, the composite pair
`(A ⋙ B, P ⋙ A ⋙ B ≅ P ⋙ B ≅ P)` acts by the action of `(B, d)` after that of `(A, c)`. For an
endomorphism `a` this says `(a ∘ b)^♮ = b^♮ ∘ a^♮`, since `(a ∘ b)⁻¹ ≅ a⁻¹ ⋙ b⁻¹`,
i.e. take `A = a⁻¹` and `B = b⁻¹`.

## Main declarations

* `CategoryTheory.Sheaf.H.coverAction`: the map `Hⁿ(D, P G) →+ Hⁿ(D, P G)` induced by `(A, c)`.
* `CategoryTheory.Sheaf.H.coverAction_comp_apply`: the composite pair acts by the composite map.
* `CategoryTheory.Sheaf.H.coverAction_congr`: isomorphic pairs act in the same way.
* `CategoryTheory.Sheaf.H.coverAction_id`: the identity pair acts by the identity.
* `CategoryTheory.Sheaf.H.coverAction_naturality`, `CategoryTheory.Sheaf.H.coverAction_δ`:
  naturality in the coefficient sheaf and compatibility with connecting homomorphisms.

## References

* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*, Documenta Math.
  1 (1996), §3.6.
-/

public section

open CategoryTheory Abelian Limits AddCommGrpCat

universe w w₂

namespace CategoryTheory.Sheaf.H

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {D : Type*} [Category* D] {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  (P : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})
  (ε : (constantSheaf K AddCommGrpCat.{w}).obj (of (ULift ℤ)) ≅
    P.obj ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))))

noncomputable section

/-- The map `a^♮ : Hⁿ(D, P G) →+ Hⁿ(D, P G)` induced by an exact additive functor
`A : Sheaf K Ab ⥤ Sheaf K Ab` and an isomorphism `c : P ⋙ A ≅ P`: the cohomology pullback along
`A`, followed by `c` on coefficients. The comparison `ℤ_K ⟶ A ℤ_K` of the pullback is
`ℤ_K ≅ P ℤ_J ≅ A (P ℤ_J) ≅ A ℤ_K`, built from `ε` and `c`. -/
def coverAction (A : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}) [A.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A] (c : P ⋙ A ≅ P)
    (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) : H (P.obj G) n →+ H (P.obj G) n :=
  (H.map (c.hom.app G) n).comp (pullback A (ε.hom ≫ c.inv.app _ ≫ A.map ε.inv) (P.obj G) n)

variable (A : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}) [A.Additive]
  [PreservesFiniteLimits A] [PreservesFiniteColimits A] (c : P ⋙ A ≅ P)

/-- `a^♮ x` is the image under `c` of the cohomology pullback of `x` along `A`. -/
lemma coverAction_apply (G : Sheaf J AddCommGrpCat.{w}) {n : ℕ} (x : H (P.obj G) n) :
    coverAction P ε A c G n x =
      H.map (c.hom.app G) n (pullback A (ε.hom ≫ c.inv.app _ ≫ A.map ε.inv) (P.obj G) n x) :=
  (rfl)

/-- **The action reverses composition.** The composite pair `(A ⋙ B, P ⋙ A ⋙ B ≅ P)` acts by
the action of `(B, d)` after that of `(A, c)`. -/
lemma coverAction_comp_apply (B : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})
    [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B] (d : P ⋙ B ≅ P)
    (G : Sheaf J AddCommGrpCat.{w}) {n : ℕ} (x : H (P.obj G) n) :
    coverAction P ε (A ⋙ B) ((Functor.associator P A B).symm ≪≫ Functor.isoWhiskerRight c B ≪≫ d)
        G n x =
      coverAction P ε B d G n (coverAction P ε A c G n x) := by
  have hκ : ε.hom ≫ ((Functor.associator P A B).symm ≪≫ Functor.isoWhiskerRight c B ≪≫ d).inv.app
        ((constantSheaf J AddCommGrpCat.{w}).obj (of (ULift ℤ))) ≫ (A ⋙ B).map ε.inv =
      (ε.hom ≫ d.inv.app _ ≫ B.map ε.inv) ≫ B.map (ε.hom ≫ c.inv.app _ ≫ A.map ε.inv) := by
    simp
  rw [coverAction_apply, coverAction_apply, coverAction_apply, hκ, pullback_comp_apply,
    pullback_naturality, ← H.map_comp_apply]
  simp

/-- **Isomorphic pairs act in the same way**: transporting `c` along an isomorphism `φ : A ≅ A'`
of exact functors does not change the action. -/
lemma coverAction_congr {A' : Sheaf K AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}}
    [A'.Additive] [PreservesFiniteLimits A'] [PreservesFiniteColimits A'] (φ : A ≅ A')
    (c' : P ⋙ A' ≅ P) (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    coverAction P ε A (Functor.isoWhiskerLeft P φ ≪≫ c') G n = coverAction P ε A' c' G n := by
  ext x
  have hκ : (ε.hom ≫ (Functor.isoWhiskerLeft P φ ≪≫ c').inv.app _ ≫ A.map ε.inv) ≫
      φ.hom.app _ = ε.hom ≫ c'.inv.app _ ≫ A'.map ε.inv := by
    simp
  rw [coverAction_apply, coverAction_apply, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, H.map_comp_apply, map_app_pullback, hκ]

/-- The identity pair acts by the identity. -/
@[simp]
lemma coverAction_id (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    coverAction P ε (𝟭 _) (Functor.rightUnitor P) G n = AddMonoidHom.id _ := by
  ext x
  have hκ : ε.hom ≫ (Functor.rightUnitor P).inv.app _ ≫ (𝟭 _).map ε.inv = 𝟙 _ := by
    simp
  rw [AddMonoidHom.id_apply, coverAction_apply, hκ, pullback_id_apply]
  exact H.map_id_apply x

/-- The action is natural in the coefficient sheaf. -/
lemma coverAction_naturality {G₁ G₂ : Sheaf J AddCommGrpCat.{w}} (f : G₁ ⟶ G₂) {n : ℕ}
    (x : H (P.obj G₁) n) :
    coverAction P ε A c G₂ n (H.map (P.map f) n x) =
      H.map (P.map f) n (coverAction P ε A c G₁ n x) := by
  rw [coverAction_apply, coverAction_apply, pullback_naturality, ← H.map_comp_apply,
    ← H.map_comp_apply]
  congr 2
  exact c.hom.naturality f

/-- The action commutes with the connecting homomorphisms of a short exact sequence of abelian
sheaves on `(C, J)` whose image under `P` is short exact. -/
lemma coverAction_δ [P.PreservesZeroMorphisms] {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : (S.map P).ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : H (P.obj S.X₃) n₀) :
    coverAction P ε A c S.X₁ n₁ (H.δ hS n₀ n₁ h x) =
      H.δ hS n₀ n₁ h (coverAction P ε A c S.X₃ n₀ x) :=
  map_pullback_δ A _ hS hS
    { τ₁ := c.hom.app S.X₁
      τ₂ := c.hom.app S.X₂
      τ₃ := c.hom.app S.X₃
      comm₁₂ := (c.hom.naturality S.f).symm
      comm₂₃ := (c.hom.naturality S.g).symm } n₀ n₁ h x

end

end CategoryTheory.Sheaf.H
