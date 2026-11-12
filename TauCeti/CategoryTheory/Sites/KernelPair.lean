/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Kernel pairs of covering morphisms become coequalizers of sheaves

Let `J` be a subcanonical Grothendieck topology on a category `C`, and let `q : X ⟶ Y` be a
morphism which generates a covering sieve of `Y`, with kernel pair `p₁ p₂ : R ⟶ X`. A `J`-sheaf of
types `P` satisfies the sheaf condition for the single morphism `q`, so `P(Y) ⟶ P(X) ⇉ P(R)` is an
equalizer. By the Yoneda lemma for sheaves, this says that the image of `R ⇉ X ⟶ Y` under the
Yoneda embedding `J.yoneda` into `J`-sheaves is a coequalizer
(`IsKernelPair.isColimitYonedaCofork`).

In other words, `Y` represents the quotient sheaf of `X` by the equivalence relation `R`. For
schemes and the fppf topology, this says that the base of an fppf covering morphism represents the
fppf quotient sheaf of its source by its kernel pair. This is how quotients of schemes by finite
group actions and by finite locally free equivalence relations are shown to represent fppf
quotient sheaves.

## Main definitions

* `CategoryTheory.IsKernelPair.isColimitYonedaCofork`: the Yoneda image of the cofork
  `R ⇉ X ⟶ Y` is a colimit in `J`-sheaves.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé IV, §3, and Exposé V,
  §4.
-/

public section

universe v u

open Opposite CategoryTheory Limits

namespace CategoryTheory.IsKernelPair

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]
  {R X Y : C} {p₁ p₂ : R ⟶ X} {q : X ⟶ Y}

/-- If `q : X ⟶ Y` generates a covering sieve of `Y` and `p₁ p₂ : R ⟶ X` is its kernel pair, the
Yoneda embedding into `J`-sheaves sends `R ⇉ X ⟶ Y` to a coequalizer. Thus `Y` represents the
quotient sheaf of `X` by the equivalence relation `R`. -/
noncomputable def isColimitYonedaCofork (h : IsKernelPair q p₁ p₂)
    (hq : Sieve.generate (Presieve.singleton q) ∈ J Y) :
    IsColimit (Cofork.ofπ (J.yoneda.map q) (by simp only [← Functor.map_comp, h.w]) :
      Cofork (J.yoneda.map p₁) (J.yoneda.map p₂)) :=
  Cofork.IsColimit.mk' _ fun s ↦ by
    let P := s.pt.obj
    have hsheaf : Presieve.IsSheafFor P (Presieve.singleton q) :=
      ((isSheaf_iff_isSheaf_of_type J P).mp s.pt.property).isSheafFor _ hq
    -- the element of `P(X)` corresponding to `s.π`; it is invariant under the kernel pair
    have hx : P.map p₁.op (J.yonedaEquiv s.π) = P.map p₂.op (J.yonedaEquiv s.π) := by
      rw [GrothendieckTopology.yonedaEquiv_naturality,
        GrothendieckTopology.yonedaEquiv_naturality, s.condition]
    have hy := Presieve.isSheafFor_singleton.mp hsheaf (J.yonedaEquiv s.π) fun a b hab ↦ by
      obtain ⟨l, rfl, rfl⟩ : ∃ l, l ≫ p₁ = a ∧ l ≫ p₂ = b :=
        ⟨h.lift a b hab, h.lift_fst a b hab, h.lift_snd a b hab⟩
      simp only [op_comp, Functor.map_comp, types_comp_apply, hx]
    refine ⟨J.yonedaEquiv.symm hy.choose, ?_, fun {m} hm ↦ ?_⟩
    · rw [Cofork.π_ofπ, GrothendieckTopology.yonedaEquiv_symm_naturality_left, hy.choose_spec.1,
        Equiv.symm_apply_apply]
    · rw [Cofork.π_ofπ] at hm
      rw [Equiv.eq_symm_apply]
      refine hy.unique ?_ hy.choose_spec.1
      rw [GrothendieckTopology.yonedaEquiv_naturality, hm]

end CategoryTheory.IsKernelPair
