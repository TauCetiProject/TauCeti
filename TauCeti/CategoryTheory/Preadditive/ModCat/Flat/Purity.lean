/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.Basic
import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.Factorization

/-!
# Pure epimorphisms of modules over preadditive categories

A pure epimorphism lifts maps from finitely presented modules. Every epimorphism onto a
flat module is pure, and a pure quotient of a flat module is flat. For a short exact
sequence, purity can also be tested by squares into its kernel inclusion.

See B. Stenström, *Purity in functor categories*, §2, pp. 353–354, for the lifting
definition and the flatness criterion, and §3, p. 355, for finite presentations in
additive functor categories.
-/

public section

universe v u

open CategoryTheory Limits

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {L M : ModCat.{v} C}

/-- A pure epimorphism is an epimorphism along which every map from a finitely presented
module lifts. -/
structure IsPureEpi (p : L ⟶ M) : Prop where
  /-- The underlying morphism is an epimorphism. -/
  epi : Epi p
  /-- Maps from finitely presented modules lift along a pure epimorphism. -/
  lift ⦃P : ModCat.{v} C⦄ (hP : IsFinitelyPresentedFunctor P.obj) (f : P ⟶ M) :
    ∃ g : P ⟶ L, g ≫ p = f

/-- A split epimorphism is pure. -/
theorem IsPureEpi.of_isSplitEpi (p : L ⟶ M) [IsSplitEpi p] : IsPureEpi p where
  epi := inferInstance
  lift {_} _ f := ⟨f ≫ section_ p, by simp⟩

/-- Every epimorphism onto a flat module is pure. -/
theorem Flat.isPureEpi [M.Flat] (p : L ⟶ M) [Epi p] : IsPureEpi p where
  epi := inferInstance
  lift {_} hP f := by
    obtain ⟨Q, hQ, a, b, hab⟩ := Flat.exists_factorization_of_isFinitelyPresentedFunctor hP f
    have := projective_of_isFiniteFree hQ
    obtain ⟨b', hb'⟩ := Projective.factors b p
    exact ⟨a ≫ b', by simp [hb', hab]⟩

/-- A pure quotient of a flat module is flat. -/
theorem IsPureEpi.flat {p : L ⟶ M} (hp : IsPureEpi p) [L.Flat] : M.Flat := by
  apply flat_iff_forall_exists_factorization.mpr
  intro P hP f
  obtain ⟨g, hg⟩ := hp.lift hP f
  obtain ⟨Q, hQ, a, b, hab⟩ := Flat.exists_factorization_of_isFinitelyPresentedFunctor hP g
  exact ⟨Q, hQ, a, b ≫ p, by simp [← Category.assoc, hab, hg]⟩

/-- If `S.g` is pure and `S.f` is its kernel, a square into `S.f` admits a lift of its left
leg across the top morphism when its source is finitely generated and its target is finitely
presented. -/
theorem IsPureEpi.exists_of_commSq {S : ShortComplex (ModCat.{v} C)} (hp : IsPureEpi S.g)
    (hS : S.Exact) [Mono S.f] {U V : ModCat.{v} C}
    (hU : IsFinitelyGeneratedFunctor U.obj) (hV : IsFinitelyPresentedFunctor V.obj)
    {d : U ⟶ V} {a : U ⟶ S.X₁} {b : V ⟶ S.X₂} (sq : CommSq d a b S.f) :
    ∃ c : V ⟶ S.X₁, d ≫ c = a := by
  let I := (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι
  have hQ : IsFinitelyPresentedFunctor (cokernel d).obj :=
    IsFinitelyPresentedFunctor.of_isColimit_cokernelCofork
      (isColimitCoforkMapOfIsColimit' I (cokernel.condition d) (cokernelIsCokernel d)) hU hV
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
theorem isPureEpi_iff_exists_of_commSq {S : ShortComplex (ModCat.{v} C)} (hS : S.ShortExact) :
    IsPureEpi S.g ↔
      ∀ ⦃U V : ModCat.{v} C⦄, IsFinitelyPresentedFunctor U.obj → IsFinitelyPresentedFunctor V.obj →
        ∀ ⦃d : U ⟶ V⦄ ⦃a : U ⟶ S.X₁⦄ ⦃b : V ⟶ S.X₂⦄, CommSq d a b S.f →
          ∃ c : V ⟶ S.X₁, d ≫ c = a := by
  have : Mono S.f := hS.mono_f
  constructor
  · intro hp U V hU hV d a b sq
    exact hp.exists_of_commSq hS.exact hU.isFinitelyGeneratedFunctor hV sq
  · intro h
    have : Epi S.g := hS.epi_g
    refine ⟨inferInstance, fun {P} hP f ↦ ?_⟩
    obtain ⟨U, V, hU, hV, d, q, hq, ⟨hq'⟩⟩ :=
      isFinitelyPresentedFunctor_iff_exists_finiteFree_presentation.mp hP
    have := projective_of_isFiniteFree hV
    have : Epi q := Cofork.IsColimit.epi hq'
    obtain ⟨b, hb⟩ := Projective.factors (q ≫ f) S.g
    obtain ⟨a, ha⟩ := hS.exact.lift' (d ≫ b) (by simp [Category.assoc, hb, reassoc_of% hq])
    obtain ⟨c, hc⟩ := h (isFinitelyPresentedFunctor_of_isFiniteFree hU)
      (isFinitelyPresentedFunctor_of_isFiniteFree hV) (CommSq.mk ha.symm)
    have hkill : d ≫ (b - c ≫ S.f) = 0 := by
      simp [Preadditive.comp_sub, ← Category.assoc, hc, ha]
    obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' hq' _ hkill
    have hg' : q ≫ g = b - c ≫ S.f := hg
    refine ⟨g, (cancel_epi q).mp ?_⟩
    calc
      q ≫ g ≫ S.g = (b - c ≫ S.f) ≫ S.g := by rw [← Category.assoc, hg']
      _ = b ≫ S.g := by simp [Preadditive.sub_comp, S.zero]
      _ = q ≫ f := hb

end TauCeti.ModCat
