/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearMap.Comp

/-!
# Maps compatible with a perfect pairing are split injections

Let `p : U →ₗ U' →ₗ W` and `q : V →ₗ V' →ₗ W'` be bilinear maps, `φ : W →ₗ W'` a linear map and
`a : U →ₗ V`, `b : U' →ₗ V'` linear maps compatible with the pairings, in the sense that
`q (a x) (b y) = φ (p x y)`, i.e. `q.compl₁₂ a b = p.compr₂ φ`. If `p` is perfect (`p` is
bijective onto `U' →ₗ W` and `p.flip` is injective) and `φ` is an isomorphism, then `a` and `b`
are injective and the range of `a` has the complement

  `{v | ∀ y, q v (b y) = 0} = ker (q.compl₂ b)`,

the annihilator of the range of `b` in the first argument of `q`. No hypothesis on `q` is needed.

This is the linear algebra behind the classical argument that a multiplicative map
`f : A → B` of graded algebras satisfying Poincaré duality, which is an isomorphism in the top
degree `n`, is a split injection in every degree: take `U = Aⁱ`, `U' = Aⁿ⁻ⁱ`, `V = Bⁱ`, `V' = Bⁿ⁻ⁱ`,
let `p` and `q` be the products into the top degree, `a` and `b` the components of `f`, and `φ`
the component of `f` in degree `n`. Then `Bⁱ = f(Aⁱ) ⊕ f(Aⁿ⁻ⁱ)^⊥`. For scalar pairings
(`W = W'` the base ring) and `φ = c • id` with `c` a unit, this is the familiar form
`q (a x) (b y) = c * p x y`. The equivariant version, where the decomposition is one of
subrepresentations, is `Representation.IntertwiningMap.isCompl_range_ker_lcomp_comp`.

## Main results

* `LinearMap.injective_left_of_compl₁₂_eq_compr₂`,
  `LinearMap.injective_right_of_compl₁₂_eq_compr₂`: the maps `a` and `b` are injective.
* `LinearMap.isCompl_range_ker_compl₂_of_compl₁₂_eq_compr₂`: the range of `a` and the
  annihilator `ker (q.compl₂ b)` are complementary.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), conclusion of the proof of
  Theorem 9.6.
-/

public section

namespace LinearMap

open Function

section CommSemiring

variable {R U U' V V' W W' : Type*} [CommSemiring R]
  [AddCommMonoid U] [Module R U] [AddCommMonoid U'] [Module R U']
  [AddCommMonoid V] [Module R V] [AddCommMonoid V'] [Module R V']
  [AddCommMonoid W] [Module R W] [AddCommMonoid W'] [Module R W']
  {p : U →ₗ[R] U' →ₗ[R] W} {q : V →ₗ[R] V' →ₗ[R] W'} {a : U →ₗ[R] V} {b : U' →ₗ[R] V'}

/-- If `q (a x) (b y) = φ (p x y)` with `p` and `φ` injective, then `a` is injective. -/
theorem injective_left_of_compl₁₂_eq_compr₂ {φ : W →ₗ[R] W'} (h : q.compl₁₂ a b = p.compr₂ φ)
    (hp : Injective p) (hφ : Injective φ) : Injective a := by
  have hcomp : q.compl₂ b ∘ₗ a = p.compr₂ φ := ext₂ fun x y ↦ by simpa using congr_fun₂ h x y
  refine Injective.of_comp (f := q.compl₂ b) ?_
  rw [← coe_comp, hcomp]
  exact injective_compr₂_of_injective p φ hp hφ

/-- If `q (a x) (b y) = φ (p x y)` with `p.flip` and `φ` injective, then `b` is injective. -/
theorem injective_right_of_compl₁₂_eq_compr₂ {φ : W →ₗ[R] W'} (h : q.compl₁₂ a b = p.compr₂ φ)
    (hp : Injective p.flip) (hφ : Injective φ) : Injective b :=
  injective_left_of_compl₁₂_eq_compr₂ (q := q.flip) (a := b) (b := a)
    (ext₂ fun y x ↦ by simpa using congr_fun₂ h x y) hp hφ

end CommSemiring

section CommRing

variable {R U U' V V' W W' : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup U'] [Module R U']
  [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']
  [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
  {p : U →ₗ[R] U' →ₗ[R] W} {q : V →ₗ[R] V' →ₗ[R] W'} {a : U →ₗ[R] V} {b : U' →ₗ[R] V'}

/-- **Splitting along a perfect pairing.** If `q (a x) (b y) = φ (p x y)`, where `p` is bijective
onto `U' →ₗ W` and `φ` is a linear isomorphism, then the range of `a` is complementary to the
annihilator `{v | ∀ y, q v (b y) = 0}` of the range of `b`. -/
theorem isCompl_range_ker_compl₂_of_compl₁₂_eq_compr₂ {φ : W ≃ₗ[R] W'}
    (h : q.compl₁₂ a b = p.compr₂ φ.toLinearMap) (hp : Bijective p) :
    IsCompl (range a) (ker (q.compl₂ b)) := by
  -- `y ↦ q · (b y)` after `a` is `p` followed by `φ`, which is bijective.
  have hcomp : q.compl₂ b ∘ₗ a = p.compr₂ φ.toLinearMap :=
    ext₂ fun x y ↦ by simpa using congr_fun₂ h x y
  refine (bijective_comp_iff.1 ?_).2.1
  rw [hcomp]
  exact bijective_compr₂_of_equiv p φ hp

end CommRing

end LinearMap
