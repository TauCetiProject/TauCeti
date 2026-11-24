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

These are the bijectivity statements behind Mathlib's `Function.Exact.splitSurjectiveEquiv` and
`Function.Exact.splitInjectiveEquiv`, which prove them inside their definitions.
-/

public section

namespace Function.Exact

variable {R M N P : Type*} [Semiring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P}

/-- If `M --f--> N --g--> P` is exact, `f` is injective and `l` is a right inverse of `g`, then
`(x, y) ↦ f x + l y` is a bijection `M × P → N`. -/
theorem bijective_coprod_of_comp_eq_id (h : Exact f g) (hf : Injective f) {l : P →ₗ[R] N}
    (hl : g ∘ₗ l = LinearMap.id) : Bijective (f.coprod l) := by
  have hgl (y : P) : g (l y) = y := LinearMap.congr_fun hl y
  refine ⟨fun a b hab ↦ ?_, fun z ↦ ?_⟩
  · rw [LinearMap.coprod_apply, LinearMap.coprod_apply] at hab
    have h₂ : a.2 = b.2 := by simpa [h.apply_apply_eq_zero, hgl] using congr(g $hab)
    exact Prod.ext (hf (by rwa [h₂, add_left_inj] at hab)) h₂
  · obtain ⟨x, hx⟩ := (h (z - l (g z))).1 (by simp [hgl])
    exact ⟨(x, g z), by simp [hx]⟩

/-- If `M --f--> N --g--> P` is exact, `g` is surjective and `l` is a left inverse of `f`, then
`y ↦ (l y, g y)` is a bijection `N → M × P`. -/
theorem bijective_prod_of_comp_eq_id (h : Exact f g) (hg : Surjective g) {l : N →ₗ[R] M}
    (hl : l ∘ₗ f = LinearMap.id) : Bijective (l.prod g) := by
  have hlf (x : M) : l (f x) = x := LinearMap.congr_fun hl x
  refine ⟨fun a b hab ↦ ?_, fun ⟨x, y⟩ ↦ ?_⟩
  · simp only [LinearMap.prod_apply, Function.prod_apply, Prod.mk.injEq] at hab
    obtain ⟨c, hc⟩ := (h (a - b)).1 (by simp [hab.2])
    -- Applying the left inverse `l` to `f c = a - b` gives `c = l a - l b = 0`.
    have hc₀ : c = 0 := by simpa [hlf, hab.1] using congr(l $hc)
    rw [← sub_eq_zero, ← hc, hc₀, map_zero]
  · obtain ⟨z, rfl⟩ := hg y
    exact ⟨f x + z - f (l z), by simp [hlf, h.apply_apply_eq_zero]⟩

end Function.Exact
