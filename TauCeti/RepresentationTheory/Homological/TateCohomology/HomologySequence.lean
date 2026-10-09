/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Linear

/-!
# Consequences of the long exact sequence in Tate cohomology

Let `G` be a finite group and `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` a short exact sequence of representations
of `G`. Mathlib provides the connecting homomorphism `TateCohomology.δ` and the exactness of the
long exact sequence at the terms `Ĥⁿ(G, X₁)` (`TateCohomology.exact₁`) and `Ĥⁿ(G, X₃)`
(`TateCohomology.exact₃`). This file adds the exactness at `Ĥⁿ(G, X₂)`
(`TateCohomology.exact₂`, in the same namespace as its two Mathlib siblings) and records how the
vanishing of the Tate cohomology of `X₃` controls the map induced by `X₁ ⟶ X₂`: if `Ĥⁿ(G, X₃)`
vanishes the induced map is surjective in degree `n` and injective in degree `n + 1`, and
conversely surjectivity in degree `n` together with injectivity in degree `n + 1` forces
`Ĥⁿ(G, X₃)` to vanish. These are the two halves of the argument that a morphism of
representations inducing isomorphisms in three consecutive degrees on every subgroup induces
isomorphisms in every degree. Likewise, vanishing of the Tate cohomology of two of the three terms,
in the degrees the long exact sequence connects, forces it for the third, and vanishing of the
Tate cohomology of `X₂` in two consecutive degrees makes the connecting map bijective.

Finally, for a `3 × 3` diagram of representations with short exact rows and columns, the two
composites of connecting maps between opposite corners differ by a sign. This is the sign rule
relating the compatibility of the cup product with connecting maps in its two variables.

## Main statements

* `TateCohomology.exact₂`: exactness of `Ĥⁿ(G, X₁) ⟶ Ĥⁿ(G, X₂) ⟶ Ĥⁿ(G, X₃)`.
* `TauCeti.TateCohomology.map_f_surjective_of_isZero_X₃`,
  `TauCeti.TateCohomology.map_f_injective_of_isZero_X₃`: vanishing of the Tate cohomology of `X₃`
  makes the map induced by `X₁ ⟶ X₂` surjective in that degree and injective in the next.
* `TauCeti.TateCohomology.isZero_X₃_of_surjective_of_injective`: the converse, from two
  consecutive degrees.
* `TauCeti.TateCohomology.isZero_X₂_of_isZero_X₁_of_isZero_X₃`,
  `TauCeti.TateCohomology.isZero_X₃_of_isZero_X₂_of_isZero_X₁`,
  `TauCeti.TateCohomology.isZero_X₁_of_isZero_X₃_of_isZero_X₂`: two-out-of-three for the
  vanishing of Tate cohomology along a short exact sequence.
* `TauCeti.TateCohomology.δ_comp_δ_eq_neg`: the connecting maps of a `3 × 3` diagram of
  representations with short exact rows and columns anticommute.
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] {S : ShortComplex (Rep k G)}
  (hS : S.ShortExact)
include hS

/-- Exactness of `Ĥⁿ(G, X₁) ⟶ Ĥⁿ(G, X₂) ⟶ Ĥⁿ(G, X₃)`, the middle term of the long exact
sequence in Tate cohomology of a short exact sequence of representations. -/
theorem _root_.TateCohomology.exact₂ (n : ℤ) :
    (ShortComplex.mk ((tateCohomologyFunctor n).map S.f) ((tateCohomologyFunctor n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact :=
  (_root_.TateCohomology.map_tateComplexFunctor_shortExact hS).homology_exact₂ n

/-- If `Ĥⁿ(G, X₃) = 0`, the map `Ĥⁿ(G, X₁) ⟶ Ĥⁿ(G, X₂)` induced by `X₁ ⟶ X₂` is surjective. -/
theorem map_f_surjective_of_isZero_X₃ (n : ℤ) (h : IsZero (tateCohomology S.X₃ n)) :
    Function.Surjective ((tateCohomologyFunctor n).map S.f) := by
  rw [← ModuleCat.epi_iff_surjective]
  exact (_root_.TateCohomology.exact₂ hS n).epi_f (h.eq_zero_of_tgt _)

/-- If `Ĥᵐ(G, X₃) = 0`, the map `Ĥⁿ(G, X₁) ⟶ Ĥⁿ(G, X₂)` induced by `X₁ ⟶ X₂` is injective in
the next degree `n = m + 1`. -/
theorem map_f_injective_of_isZero_X₃ (m n : ℤ) (hmn : m + 1 = n)
    (h : IsZero (tateCohomology S.X₃ m)) :
    Function.Injective ((tateCohomologyFunctor n).map S.f) := by
  subst hmn
  rw [← ModuleCat.mono_iff_injective]
  exact (_root_.TateCohomology.exact₁ hS m).mono_g (h.eq_zero_of_src _)

/-- If the map induced by `X₁ ⟶ X₂` on Tate cohomology is surjective in degree `m` and injective
in degree `n = m + 1`, then `Ĥᵐ(G, X₃) = 0`. -/
theorem isZero_X₃_of_surjective_of_injective (m n : ℤ) (hmn : m + 1 = n)
    (hsurj : Function.Surjective ((tateCohomologyFunctor m).map S.f))
    (hinj : Function.Injective ((tateCohomologyFunctor n).map S.f)) :
    IsZero (tateCohomology S.X₃ m) := by
  subst hmn
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    ((_root_.TateCohomology.map_tateComplexFunctor_shortExact hS).exactAt_X₃ m
      ((ModuleCat.epi_iff_surjective _).2 hsurj) fun j hj ↦ ?_)
  -- `hj : (ComplexShape.up ℤ).Rel m j`, which is `m + 1 = j`.
  obtain rfl : m + 1 = j := hj
  exact (ModuleCat.mono_iff_injective _).2 hinj

/-- If `Ĥⁿ(G, X₁) = 0` and `Ĥⁿ(G, X₃) = 0`, then `Ĥⁿ(G, X₂) = 0`. -/
theorem isZero_X₂_of_isZero_X₁_of_isZero_X₃ (n : ℤ) (h₁ : IsZero (tateCohomology S.X₁ n))
    (h₃ : IsZero (tateCohomology S.X₃ n)) : IsZero (tateCohomology S.X₂ n) :=
  (_root_.TateCohomology.exact₂ hS n).isZero_of_both_isZero h₁ h₃

/-- If `Ĥᵐ(G, X₂) = 0` and `Ĥⁿ(G, X₁) = 0` in the next degree `n = m + 1`, then
`Ĥᵐ(G, X₃) = 0`. -/
theorem isZero_X₃_of_isZero_X₂_of_isZero_X₁ (m n : ℤ) (hmn : m + 1 = n)
    (h₂ : IsZero (tateCohomology S.X₂ m)) (h₁ : IsZero (tateCohomology S.X₁ n)) :
    IsZero (tateCohomology S.X₃ m) := by
  subst hmn
  exact (_root_.TateCohomology.exact₃ hS m).isZero_of_both_isZero h₂ h₁

/-- If `Ĥᵐ(G, X₃) = 0` and `Ĥⁿ(G, X₂) = 0` in the next degree `n = m + 1`, then
`Ĥⁿ(G, X₁) = 0`. -/
theorem isZero_X₁_of_isZero_X₃_of_isZero_X₂ (m n : ℤ) (hmn : m + 1 = n)
    (h₃ : IsZero (tateCohomology S.X₃ m)) (h₂ : IsZero (tateCohomology S.X₂ n)) :
    IsZero (tateCohomology S.X₁ n) := by
  subst hmn
  exact (_root_.TateCohomology.exact₁ hS m).isZero_of_both_isZero h₃ h₂

/-- If `Ĥⁿ(G, X₂) = 0` and `Ĥⁿ⁺¹(G, X₂) = 0`, the connecting map
`Ĥⁿ(G, X₃) ⟶ Ĥⁿ⁺¹(G, X₁)` is bijective. -/
theorem δ_bijective_of_isZero_X₂ (n : ℤ) (h₀ : IsZero (tateCohomology S.X₂ n))
    (h₁ : IsZero (tateCohomology S.X₂ (n + 1))) :
    Function.Bijective (_root_.TateCohomology.δ hS n) :=
  ConcreteCategory.bijective_of_isIso
    ((_root_.TateCohomology.map_tateComplexFunctor_shortExact hS).δIso n (n + 1) rfl h₀ h₁).hom

omit hS

/-- **The connecting maps of a `3 × 3` diagram anticommute in Tate cohomology.** Let `D` be a
`3 × 3` diagram of representations, presented as a short complex `D.X₁ ⟶ D.X₂ ⟶ D.X₃` of short
complexes, all of whose rows `D.Xᵢ` and columns `D.map π_j` are short exact. Then the two composites
of connecting maps `Ĥⁿ(G, X₃₃) ⟶ Ĥⁿ⁺²(G, X₁₁)`, through the third row and the first column, and
through the third column and the first row, differ by a sign. -/
theorem δ_comp_δ_eq_neg (D : ShortComplex (ShortComplex (Rep k G)))
    (h₁ : D.X₁.ShortExact) (h₂ : D.X₂.ShortExact) (h₃ : D.X₃.ShortExact)
    (h₁' : (D.map ShortComplex.π₁).ShortExact) (h₂' : (D.map ShortComplex.π₂).ShortExact)
    (h₃' : (D.map ShortComplex.π₃).ShortExact) (n : ℤ) :
    _root_.TateCohomology.δ h₃ n ≫ _root_.TateCohomology.δ h₁' (n + 1) =
      -(_root_.TateCohomology.δ h₃' n ≫ _root_.TateCohomology.δ h₁ (n + 1)) := by
  -- The image of `D` under the Tate complex functor, a `3 × 3` diagram of cochain complexes.
  let F := (tateComplexFunctor k G).mapShortComplex
  let D' := ShortComplex.mk (F.map D.f) (F.map D.g) (by
    rw [← F.map_comp, D.zero]
    apply ShortComplex.hom_ext <;> exact (tateComplexFunctor k G).map_zero _ _)
  exact HomologicalComplex.HomologySequence.δ_comp_δ_eq_neg D'
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact h₁)
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact h₂)
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact h₃)
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact h₁')
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact h₂')
    (_root_.TateCohomology.map_tateComplexFunctor_shortExact h₃') n (n + 1) (n + 1 + 1) rfl rfl

end TauCeti.TateCohomology
