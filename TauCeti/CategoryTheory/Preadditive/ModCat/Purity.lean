/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic
import TauCeti.CategoryTheory.Preadditive.ModCat.FiniteFree

/-!
# Pure epimorphisms of modules over preadditive categories

A pure epimorphism lifts maps from finitely presented modules. For a short exact sequence,
purity of the quotient map can also be tested by squares into the kernel inclusion.
The two square-lifting results use the formulation of Mathlib's
`CategoryTheory.IsCardinalPure.exists_of_commSq` with algebraic finiteness hypotheses.

See B. Stenström, *Purity in functor categories*, §2, pp. 353–354, for the lifting
definition, and §3, p. 355, for finite presentations in additive functor categories.
-/

public section

universe v u

open CategoryTheory Limits

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {L M : ModCat.{v} C}

/-- A morphism is a pure epimorphism if every map from a finitely presented module lifts
along it. Such a morphism is epic by `IsPureEpi.epi`. -/
structure IsPureEpi (p : L ⟶ M) : Prop where
  /-- Maps from finitely presented modules lift along a pure epimorphism. -/
  lift ⦃P : ModCat.{v} C⦄ (hP : IsFinitelyPresentedFunctor P.obj) (f : P ⟶ M) :
    ∃ g : P ⟶ L, g ≫ p = f

/-- A pure epimorphism is epic because maps from representables lift along it. -/
theorem IsPureEpi.epi {p : L ⟶ M} (hp : IsPureEpi p) : Epi p := by
  have : M.obj.Additive := (additiveFunctor_iff _).1 M.property
  apply (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι.epi_of_epi_map
  refine p.hom.epi_of_preadditiveYoneda_lifts fun Y f ↦ ?_
  obtain ⟨g, hg⟩ := hp.lift (isFinitelyPresentedFunctor_preadditiveYoneda_obj Y)
    (ObjectProperty.homMk f : (yoneda C).obj Y ⟶ M)
  exact ⟨g.hom, congrArg (fun k ↦ k.hom) hg⟩

/-- A morphism is a pure epimorphism if and only if every map from a finitely presented
module lifts along it. -/
theorem isPureEpi_iff {p : L ⟶ M} :
    IsPureEpi p ↔
      ∀ ⦃P : ModCat.{v} C⦄, IsFinitelyPresentedFunctor P.obj →
        ∀ f : P ⟶ M, ∃ g : P ⟶ L, g ≫ p = f :=
  ⟨fun hp _ hP f ↦ hp.lift hP f, fun h ↦ ⟨h⟩⟩

/-- A split epimorphism is pure. -/
theorem IsPureEpi.of_isSplitEpi (p : L ⟶ M) [IsSplitEpi p] : IsPureEpi p where
  lift {_} _ f := ⟨f ≫ section_ p, by simp⟩

/-- The composite of two pure epimorphisms is pure. -/
theorem IsPureEpi.comp {N : ModCat.{v} C} {p : L ⟶ M} {q : M ⟶ N}
    (hp : IsPureEpi p) (hq : IsPureEpi q) : IsPureEpi (p ≫ q) where
  lift {_} hP f := by
    obtain ⟨g, hg⟩ := hq.lift hP f
    obtain ⟨k, hk⟩ := hp.lift hP g
    exact ⟨k, by rw [← Category.assoc, hk, hg]⟩

/-- If `S.g` is pure and `S.f` is its kernel, a square into `S.f` admits a lift of its left
leg across the top morphism when its cokernel is finitely presented. -/
theorem IsPureEpi.exists_of_commSq {S : ShortComplex (ModCat.{v} C)} (hp : IsPureEpi S.g)
    (hS : S.Exact) [Mono S.f] {U V : ModCat.{v} C} {d : U ⟶ V}
    (hQ : IsFinitelyPresentedFunctor (cokernel d).obj)
    {a : U ⟶ S.X₁} {b : V ⟶ S.X₂} (sq : CommSq d a b S.f) :
    ∃ c : V ⟶ S.X₁, d ≫ c = a := by
  have hd : d ≫ (b ≫ S.g) = 0 := by rw [sq.w_assoc, S.zero, comp_zero]
  obtain ⟨l, hl⟩ := hp.lift hQ (cokernel.desc d (b ≫ S.g) hd)
  let b' := cokernel.π d ≫ l
  have hb'g : b' ≫ S.g = b ≫ S.g := by simp [b', hl]
  have hdb' : d ≫ b' = 0 := by simp [b']
  obtain ⟨c, hc⟩ := hS.lift' (b - b') (by simp [Preadditive.sub_comp, hb'g])
  refine ⟨c, (cancel_mono S.f).mp ?_⟩
  simp [hc, Preadditive.comp_sub, hdb', sq.w]

/-- In a short exact sequence, the quotient map is pure if and only if every commutative
square from a morphism between finitely presented modules into the kernel inclusion admits
a lift of its left leg across the top morphism. -/
theorem _root_.CategoryTheory.ShortComplex.ShortExact.isPureEpi_iff_exists_of_commSq
    {S : ShortComplex (ModCat.{v} C)} (hS : S.ShortExact) :
    IsPureEpi S.g ↔
      ∀ ⦃U V : ModCat.{v} C⦄, IsFinitelyPresentedFunctor U.obj → IsFinitelyPresentedFunctor V.obj →
        ∀ ⦃d : U ⟶ V⦄ ⦃a : U ⟶ S.X₁⦄ ⦃b : V ⟶ S.X₂⦄, CommSq d a b S.f →
          ∃ c : V ⟶ S.X₁, d ≫ c = a := by
  have : Mono S.f := hS.mono_f
  constructor
  · intro hp U V hU hV d a b sq
    let I := (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι
    have hQ : IsFinitelyPresentedFunctor (cokernel d).obj :=
      IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork
        (isColimitCoforkMapOfIsColimit' I (cokernel.condition d) (cokernelIsCokernel d))
        hU.isFinitelyGeneratedFunctor hV
    exact hp.exists_of_commSq hS.exact hQ sq
  · intro h
    have : Epi S.g := hS.epi_g
    refine ⟨fun {P} hP f ↦ ?_⟩
    obtain ⟨U, V, hU, hV, d, q, hq, ⟨hq'⟩⟩ :=
      isFinitelyPresentedFunctor_iff_exists_finiteFree_presentation.mp hP
    have := projective_of_isFiniteFree hV
    have : Epi q := by simpa only [CokernelCofork.π_ofπ] using Cofork.IsColimit.epi hq'
    obtain ⟨b, hb⟩ := Projective.factors (q ≫ f) S.g
    obtain ⟨a, ha⟩ := hS.exact.lift' (d ≫ b) (by simp [Category.assoc, hb, reassoc_of% hq])
    obtain ⟨c, hc⟩ := h (isFinitelyPresentedFunctor_of_isFiniteFree hU)
      (isFinitelyPresentedFunctor_of_isFiniteFree hV) (CommSq.mk ha.symm)
    have hkill : d ≫ (b - c ≫ S.f) = 0 := by
      simp [Preadditive.comp_sub, ← Category.assoc, hc, ha]
    obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' hq' _ hkill
    rw [CokernelCofork.π_ofπ] at hg
    refine ⟨g, (cancel_epi q).mp ?_⟩
    calc
      q ≫ g ≫ S.g = (b - c ≫ S.f) ≫ S.g := by rw [← Category.assoc, hg]
      _ = b ≫ S.g := by simp [Preadditive.sub_comp, S.zero]
      _ = q ≫ f := hb

end TauCeti.ModCat
