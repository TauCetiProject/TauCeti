/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.Simultaneous.Basic
import TauCeti.CategoryTheory.Aut.Representable

/-!
# Forgetful projections between simultaneous moduli schemes

If a moduli problem `𝒬` is relatively representable and `𝒫` and `(𝒬, 𝒫)` are represented by
elliptic families, the map forgetting the `𝒬`-structure is, up to isomorphism, the representing
morphism of `𝒬` over the universal `𝒫`-family. Thus every isomorphism-invariant property of that
representing morphism holds for the forgetful map. In particular, a finite étale rigidifying
problem gives finite étale projections from the scheme of two rigidifications to the scheme of
one rigidification. This conclusion does not require rigidity of `𝒫`; rigidity is used separately
to make the pair of projections a monomorphism.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Chapter 4,
  proof of Theorem 4.7.0.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.ModuliProblem

namespace RelRepData

variable {B : Scheme.{u}} {P Q : ModuliProblem B} (D : Q.RelRepData)
  {U V : EllObj B} (R : P.RepresentableBy U) (S : (Q ⊗ P).RepresentableBy V)

/-- Under the canonical comparison of representing families, forgetting the first structure is
exactly the projection from the relative representing scheme. -/
theorem eq_uniqueUpToIso_hom_comp_baseChangeFunctorHom (a : V ⟶ U)
    (ha : R.homEquiv a = (S.homEquiv (𝟙 V)).2) :
    a = (S.uniqueUpToIso (D.tensorRepresentableBy R)).hom ≫
      U.baseChangeFunctorHom (D.rep U) := by
  apply R.homEquiv.injective
  rw [ha]
  have h := congrArg Prod.snd (S.homEquiv_uniqueUpToIso_hom (D.tensorRepresentableBy R))
  simpa only [tensorRepresentableBy_homEquiv] using h.symm

/-- A forgetful projection from a simultaneous moduli scheme has every isomorphism-invariant
property of the relative representing morphism for the forgotten structure. No stability under
composition or base change is needed. -/
theorem mem_base_of_forget_fst {W : MorphismProperty Scheme.{u}} [W.RespectsIso]
    (a : V ⟶ U) (ha : R.homEquiv a = (S.homEquiv (𝟙 V)).2)
    (h : W (D.rep U).hom) : W a.base := by
  rw [D.eq_uniqueUpToIso_hom_comp_baseChangeFunctorHom R S a ha, EllObj.comp_base,
    EllObj.baseChangeFunctorHom_base]
  exact (W.cancel_left_of_respectsIso _ _).mpr h

section Swap

variable {U V : EllObj B} (R : P.RepresentableBy U) (S : (P ⊗ Q).RepresentableBy V)

/-- Forgetting the second structure has every isomorphism-invariant property of its relative
representing morphism. -/
theorem mem_base_of_forget_snd {W : MorphismProperty Scheme.{u}} [W.RespectsIso]
    (a : V ⟶ U) (ha : R.homEquiv a = (S.homEquiv (𝟙 V)).1)
    (h : W (D.rep U).hom) : W a.base := by
  apply D.mem_base_of_forget_fst R (S.ofIso (β_ P Q)) a _ h
  -- The cartesian braiding interchanges the two universal structures.
  convert ha using 1
  rfl

end Swap

section Triple

variable {Q₁ Q₂ : ModuliProblem B} {V V₁ V₂ : EllObj B}
  (S : (P ⊗ (Q₁ ⊗ Q₂)).RepresentableBy V)
  (R₁ : (P ⊗ Q₁).RepresentableBy V₁) (R₂ : (P ⊗ Q₂).RepresentableBy V₂)

/-- Forgetting the last structure in a triple has the properties of the relative representing
morphism of that structure over the universal family with the first two structures. -/
theorem mem_base_of_forget_right (D₂ : Q₂.RelRepData)
    {W : MorphismProperty Scheme.{u}} [W.RespectsIso] (a₁ : V ⟶ V₁)
    (ha₁ : R₁.homEquiv a₁ = (P ◁ fst Q₁ Q₂).app (op V) (S.homEquiv (𝟙 V)))
    (h : W (D₂.rep V₁).hom) : W a₁.base := by
  apply D₂.mem_base_of_forget_snd R₁ (S.ofIso (α_ P Q₁ Q₂).symm) a₁ _ h
  -- The associator regroups the universal triple as a pair and its last structure.
  convert ha₁ using 1
  rfl

/-- Forgetting the middle structure in a triple has the properties of its relative representing
morphism over the universal family with the first and last structures. -/
theorem mem_base_of_forget_middle (D₁ : Q₁.RelRepData)
    {W : MorphismProperty Scheme.{u}} [W.RespectsIso] (a₂ : V ⟶ V₂)
    (ha₂ : R₂.homEquiv a₂ = (P ◁ snd Q₁ Q₂).app (op V) (S.homEquiv (𝟙 V)))
    (h : W (D₁.rep V₂).hom) : W a₂.base := by
  apply D₁.mem_base_of_forget_right
    (S.ofIso (whiskerLeftIso P (β_ Q₁ Q₂))) R₂ a₂ _ h
  -- Interchanging the last two structures turns this into the last-factor projection.
  convert ha₂ using 1
  rfl

end Triple

end RelRepData

end TauCeti.AlgebraicGeometry.ModuliProblem
