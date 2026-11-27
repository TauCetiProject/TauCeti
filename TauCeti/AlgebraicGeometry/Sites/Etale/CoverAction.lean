/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import TauCeti.AlgebraicGeometry.Sites.Etale.Pseudofunctor
public import TauCeti.AlgebraicGeometry.Sites.Etale.Pullback
public import TauCeti.CategoryTheory.Sites.SheafCohomology.CoverAction

/-!
# Automorphisms of a cover act on étale cohomology

Let `p : Y ⟶ X` be a morphism of schemes and `F` an abelian sheaf on the small étale site of `X`.
An endomorphism `a : Y ⟶ Y` over `X`, that is with `a ≫ p = p`, acts on the étale cohomology
`Hⁿ(Y, p⁻¹ F)`: pull back along `a`, then identify `a⁻¹ p⁻¹ F` with `(a ≫ p)⁻¹ F = p⁻¹ F`
(de Jong–van der Put, §3.6). This is `AlgebraicGeometry.Scheme.Hom.smallEtaleCoverAction`, the
map `a^♮`, an instance of the general construction `CategoryTheory.Sheaf.H.coverAction`.

The coefficient identification is `AlgebraicGeometry.Scheme.Hom.smallEtalePullbackOverIso`, the
isomorphism `p⁻¹ ⋙ a⁻¹ ≅ p⁻¹` adjoint to base change along the factorization `p = a ≫ p`. Its
cocycle identity comes from the associativity of base change on small étale sites
(`AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeComp_associativity`), so the action reverses
composition: `(a ≫ b)^♮ = a^♮ ∘ b^♮`, that is `(b ∘ a)^♮ = a^♮ ∘ b^♮`. Hence the automorphisms of
`Y` over `X` act through the opposite group
(`AlgebraicGeometry.Scheme.Hom.smallEtaleCoverActionHom`). Composed with an anti-homomorphism
into these automorphisms, such as `σ ↦ Spec σ` for a Galois group, this is a left action.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.smallEtalePullbackOverIso p a ha`: the isomorphism
  `p⁻¹ ⋙ a⁻¹ ≅ p⁻¹` of inverse images on small étale sheaves, for `ha : a ≫ p = p`.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleCoverAction p a ha F n`: the map
  `a^♮ : Hⁿ(Y, p⁻¹ F) →+ Hⁿ(Y, p⁻¹ F)`.
* `AlgebraicGeometry.Scheme.Hom.smallEtalePullbackOverIso_eq_sheafPullbackComp'`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleCoverAction_eq_coverAction`: the two definitions in
  terms of `CategoryTheory.Functor.sheafPullbackComp'` and `CategoryTheory.Sheaf.H.coverAction`.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleCoverAction_comp`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleCoverAction_id`: `(a ≫ b)^♮ = a^♮ ∘ b^♮` and
  `(𝟙 Y)^♮ = id`.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleCoverAction_naturality`,
  `AlgebraicGeometry.Scheme.Hom.smallEtaleCoverAction_δ`: naturality in `F` and compatibility
  with the connecting homomorphisms of short exact sequences of sheaves on `X`.
* `AlgebraicGeometry.Scheme.Hom.smallEtaleCoverActionHom p F n`: the automorphisms of `Y` over
  `X` act on `Hⁿ(Y, p⁻¹ F)` through the opposite group.

## References

* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*, Documenta Math.
  1 (1996), §3.6.
-/

public section

universe w u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

noncomputable section

/-- For an endomorphism `a` of `Y` with `a ≫ p = p`, the isomorphism `p⁻¹ ⋙ a⁻¹ ≅ p⁻¹` between
inverse images of small étale sheaves. It is adjoint to base change along the factorization
`p = a ≫ p` (`AlgebraicGeometry.Scheme.Hom.smallEtaleBaseChangeComp`). -/
def smallEtalePullbackOverIso (a : Y ⟶ Y) (ha : a ≫ p = p) (A : Type*) [Category* A]
    [(p.smallEtalePushforward A).IsRightAdjoint] [(a.smallEtalePushforward A).IsRightAdjoint] :
    p.smallEtalePullback A ⋙ a.smallEtalePullback A ≅ p.smallEtalePullback A :=
  Functor.sheafPullbackComp' (smallEtaleBaseChangeComp a p p ha.symm).symm A _ _ _

/-- `smallEtalePullbackOverIso` is the composition isomorphism of inverse images adjoint to the
inverse of `smallEtaleBaseChangeComp a p p ha.symm`. -/
lemma smallEtalePullbackOverIso_eq_sheafPullbackComp' (a : Y ⟶ Y) (ha : a ≫ p = p)
    (A : Type*) [Category* A] [(p.smallEtalePushforward A).IsRightAdjoint]
    [(a.smallEtalePushforward A).IsRightAdjoint] :
    p.smallEtalePullbackOverIso a ha A =
      Functor.sheafPullbackComp' (smallEtaleBaseChangeComp a p p ha.symm).symm A _ _ _ :=
  (rfl)

variable [HasExt.{w} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u})]

/-- **Automorphisms of a cover act on étale cohomology.** For a morphism of schemes `p : Y ⟶ X`,
an abelian sheaf `F` on the small étale site of `X` and an endomorphism `a` of `Y` over `X`, the
map `a^♮ : Hⁿ(Y, p⁻¹ F) →+ Hⁿ(Y, p⁻¹ F)`: the cohomology pullback along `a`, followed by the
identification `a⁻¹ p⁻¹ F ≅ p⁻¹ F` of `smallEtalePullbackOverIso` (de Jong–van der Put, §3.6).
The constant sheaf `ℤ` on `Y` is identified with `p⁻¹ ℤ` through
`smallEtalePullbackConstantSheafIso`. -/
def smallEtaleCoverAction (a : Y ⟶ Y) (ha : a ≫ p = p)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H ((p.smallEtalePullback AddCommGrpCat.{u}).obj F) n →+
      Sheaf.H ((p.smallEtalePullback AddCommGrpCat.{u}).obj F) n :=
  Sheaf.H.coverAction (p.smallEtalePullback AddCommGrpCat.{u})
    (p.smallEtalePullbackConstantSheafIso AddCommGrpCat.{u} (AddCommGrpCat.of (ULift ℤ))).symm
    (a.smallEtalePullback AddCommGrpCat.{u}) (p.smallEtalePullbackOverIso a ha _) F n

/-- `a^♮` is the general action `CategoryTheory.Sheaf.H.coverAction` of the pair
`(a⁻¹, smallEtalePullbackOverIso p a ha)`. -/
lemma smallEtaleCoverAction_eq_coverAction (a : Y ⟶ Y) (ha : a ≫ p = p)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    p.smallEtaleCoverAction a ha F n =
      Sheaf.H.coverAction (p.smallEtalePullback AddCommGrpCat.{u})
        (p.smallEtalePullbackConstantSheafIso AddCommGrpCat.{u} (AddCommGrpCat.of (ULift ℤ))).symm
        (a.smallEtalePullback AddCommGrpCat.{u}) (p.smallEtalePullbackOverIso a ha _) F n :=
  (rfl)

variable (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})

/-- **The action reverses composition**: `(a ≫ b)^♮ = a^♮ ∘ b^♮`. Pulling back along `a ≫ b`
first pulls back along `b`, then along `a`. -/
theorem smallEtaleCoverAction_comp (a b : Y ⟶ Y) (ha : a ≫ p = p) (hb : b ≫ p = p) (n : ℕ) :
    p.smallEtaleCoverAction (a ≫ b) (by rw [Category.assoc, hb, ha]) F n =
      (p.smallEtaleCoverAction a ha F n).comp (p.smallEtaleCoverAction b hb F n) := by
  ext x
  have hc := Functor.sheafPullbackComp'_assoc (smallEtaleBaseChangeComp b p p hb.symm).symm
    (smallEtaleBaseChangeComp a b).symm (smallEtaleBaseChangeComp a p p ha.symm).symm
    (smallEtaleBaseChangeComp (a ≫ b) p p (by rw [Category.assoc, hb, ha])).symm
    AddCommGrpCat.{u} (smallEtaleTopology X) (smallEtaleTopology Y) (smallEtaleTopology Y)
    (smallEtaleTopology Y) (smallEtaleBaseChangeComp_associativity a b p (a ≫ b) p p rfl hb.symm
      (by rw [Category.assoc, hb, ha]) ha.symm)
  rw [AddMonoidHom.comp_apply, smallEtaleCoverAction_eq_coverAction,
    smallEtaleCoverAction_eq_coverAction, smallEtaleCoverAction_eq_coverAction,
    smallEtalePullbackOverIso_eq_sheafPullbackComp',
    smallEtalePullbackOverIso_eq_sheafPullbackComp',
    smallEtalePullbackOverIso_eq_sheafPullbackComp', ← Sheaf.H.coverAction_comp_apply, ← hc,
    Sheaf.H.coverAction_congr]

/-- The identity of `Y` acts by the identity. -/
@[simp]
theorem smallEtaleCoverAction_id (n : ℕ) :
    p.smallEtaleCoverAction (𝟙 Y) (Category.id_comp p) F n = AddMonoidHom.id _ := by
  have hc := Functor.sheafPullbackComp'_eq_isoWhiskerLeft_sheafPullbackId'
    (smallEtaleBaseChangeComp (𝟙 Y) p p (Category.id_comp p).symm).symm
    (smallEtaleBaseChangeId Y) AddCommGrpCat.{u} (smallEtaleTopology X) (smallEtaleTopology Y)
    (smallEtaleBaseChangeComp_id_comp p (Category.id_comp p).symm)
  rw [smallEtaleCoverAction_eq_coverAction, smallEtalePullbackOverIso_eq_sheafPullbackComp', hc,
    Sheaf.H.coverAction_congr, Sheaf.H.coverAction_id]

/-- `(a ≫ b)^♮ x = a^♮ (b^♮ x)`. -/
theorem smallEtaleCoverAction_comp_apply (a b : Y ⟶ Y) (ha : a ≫ p = p) (hb : b ≫ p = p)
    {n : ℕ} (x : Sheaf.H ((p.smallEtalePullback AddCommGrpCat.{u}).obj F) n) :
    p.smallEtaleCoverAction (a ≫ b) (by rw [Category.assoc, hb, ha]) F n x =
      p.smallEtaleCoverAction a ha F n (p.smallEtaleCoverAction b hb F n x) := by
  rw [smallEtaleCoverAction_comp p F a b ha hb, AddMonoidHom.comp_apply]

/-- The action is natural in the coefficient sheaf on `X`. -/
theorem smallEtaleCoverAction_naturality (a : Y ⟶ Y) (ha : a ≫ p = p)
    {F₁ F₂ : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}} (f : F₁ ⟶ F₂) {n : ℕ}
    (x : Sheaf.H ((p.smallEtalePullback AddCommGrpCat.{u}).obj F₁) n) :
    p.smallEtaleCoverAction a ha F₂ n
        (Sheaf.H.map ((p.smallEtalePullback AddCommGrpCat.{u}).map f) n x) =
      Sheaf.H.map ((p.smallEtalePullback AddCommGrpCat.{u}).map f) n
        (p.smallEtaleCoverAction a ha F₁ n x) :=
  Sheaf.H.coverAction_naturality _ _ _ _ f x

/-- The action commutes with the connecting homomorphisms of a short exact sequence of abelian
sheaves on `X`, pulled back to `Y`. -/
theorem smallEtaleCoverAction_δ (a : Y ⟶ Y) (ha : a ≫ p = p)
    {S : ShortComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})} (hS : S.ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (x : Sheaf.H ((p.smallEtalePullback AddCommGrpCat.{u}).obj S.X₃) n₀) :
    p.smallEtaleCoverAction a ha S.X₁ n₁
        (Sheaf.H.δ (hS.map_of_exact (p.smallEtalePullback AddCommGrpCat.{u})) n₀ n₁ h x) =
      Sheaf.H.δ (hS.map_of_exact (p.smallEtalePullback AddCommGrpCat.{u})) n₀ n₁ h
        (p.smallEtaleCoverAction a ha S.X₃ n₀ x) :=
  Sheaf.H.coverAction_δ _ _ _ _ _ n₀ n₁ h x

/-- **The automorphisms of `Y` over `X` act on `Hⁿ(Y, p⁻¹ F)`**, through the opposite group,
since `(a ≫ b)^♮ = a^♮ ∘ b^♮`. The automorphism `g` acts by `g.asIso.hom.left^♮`. -/
def smallEtaleCoverActionHom (n : ℕ) :
    (Aut (Over.mk p))ᵐᵒᵖ →*
      AddMonoid.End (Sheaf.H ((p.smallEtalePullback AddCommGrpCat.{u}).obj F) n) where
  toFun g := p.smallEtaleCoverAction g.unop.asIso.hom.left (Over.w g.unop.asIso.hom) F n
  map_one' := by
    simp only [MulOpposite.unop_one, Aut.one_asIso, Iso.refl_hom, Over.id_left]
    exact smallEtaleCoverAction_id p F n
  map_mul' g h := by
    simp only [MulOpposite.unop_mul, Aut.mul_asIso, Iso.trans_hom, Over.comp_left]
    exact smallEtaleCoverAction_comp p F _ _ _ _ n

/-- An automorphism `g` of `Y` over `X` acts by `g.asIso.hom.left^♮`. -/
@[simp]
theorem smallEtaleCoverActionHom_apply (n : ℕ) (g : (Aut (Over.mk p))ᵐᵒᵖ)
    (x : Sheaf.H ((p.smallEtalePullback AddCommGrpCat.{u}).obj F) n) :
    p.smallEtaleCoverActionHom F n g x =
      p.smallEtaleCoverAction g.unop.asIso.hom.left (Over.w g.unop.asIso.hom) F n x :=
  (rfl)

end

end AlgebraicGeometry.Scheme.Hom
