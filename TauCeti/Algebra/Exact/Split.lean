/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Splitting maps of a split exact sequence

Let `M --f--> N --g--> P` be an exact pair of linear maps. If `f` is injective and `l` is a right
inverse of `g`, then `(x, y) ↦ f x + l y` is a bijection `M × P → N`
(`Function.Exact.bijective_coprod_of_comp_eq_id`). Dually, if `g` is surjective and `l` is a left
inverse of `f`, then `y ↦ (l y, g y)` is a bijection `N → M × P`
(`Function.Exact.bijective_prod_of_comp_eq_id`).

Both are read off from Mathlib's `Function.Exact.splitSurjectiveEquiv` and
`Function.Exact.splitInjectiveEquiv`, whose underlying linear equivalences are
`LinearEquiv.ofBijective` of these maps (up to `symm`); the lemmas record this once so that callers
do not depend on how those equivalences are built.
-/

public section

namespace Function.Exact

variable {R M N P : Type*} [Semiring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- If `M --f--> N --g--> P` is exact, `f` is injective and `l` is a right inverse of `g`, then
`(x, y) ↦ f x + l y` is a bijection `M × P → N`. -/
theorem bijective_coprod_of_comp_eq_id (h : Exact f g) (hf : Injective f) {l : P →ₗ[R] N}
    (hl : g ∘ₗ l = LinearMap.id) : Bijective (f.coprod l) :=
  -- `f.coprod l` is by definition `f ∘ₗ fst + l ∘ₗ snd`, the map Mathlib inverts.
  (h.splitSurjectiveEquiv hf ⟨l, hl⟩).val.symm.bijective

/-- If `M --f--> N --g--> P` is exact, `g` is surjective and `l` is a left inverse of `f`, then
`y ↦ (l y, g y)` is a bijection `N → M × P`. -/
theorem bijective_prod_of_comp_eq_id (h : Exact f g) (hg : Surjective g) {l : N →ₗ[R] M}
    (hl : l ∘ₗ f = LinearMap.id) : Bijective (l.prod g) :=
  (h.splitInjectiveEquiv hg ⟨l, hl⟩).val.bijective

end Function.Exact
