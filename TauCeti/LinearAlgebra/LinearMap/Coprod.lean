/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Prod

/-!
# Bijectivity of a coproduct of linear maps

The linear map `f.coprod g : M₁ × M₂ → M`, `(a, b) ↦ f a + g b`, is bijective exactly when `f`
and `g` are injective and their ranges are complementary submodules of `M`. This is the linear
algebra behind recognising an internal direct sum decomposition `M = range f ⊕ range g`, and
behind inverse-function-theorem arguments whose differential has the form `(a, b) ↦ f a + g b`.
-/

public section

namespace LinearMap

variable {R M₁ M₂ M : Type*} [Semiring R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [AddCommGroup M] [Module R M]

/-- The map `(a, b) ↦ f a + g b` is bijective exactly when `f` and `g` are injective and the
ranges of `f` and `g` are complementary. -/
theorem bijective_coprod_iff {f : M₁ →ₗ[R] M} {g : M₂ →ₗ[R] M} :
    Function.Bijective (f.coprod g) ↔
      Function.Injective f ∧ Function.Injective g ∧ IsCompl (range f) (range g) := by
  refine ⟨fun h ↦ ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_, ⟨?_, ?_⟩⟩, fun ⟨hf, hg, hc⟩ ↦ ⟨?_, ?_⟩⟩
  · simpa using congrArg Prod.fst (h.1 (a₁ := (a, 0)) (a₂ := (b, 0)) (by simpa using hab))
  · simpa using congrArg Prod.snd (h.1 (a₁ := (0, a)) (a₂ := (0, b)) (by simpa using hab))
  · -- A common value `f a = g b` gives `f.coprod g (a, -b) = 0`, so `a = 0`.
    rw [Submodule.disjoint_def]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have ha : a = 0 := congrArg Prod.fst (h.1 (a₁ := (a, -b)) (a₂ := 0) (by simp [hb]))
    simp [ha]
  · rw [codisjoint_iff, ← range_coprod, range_eq_top]
    exact h.2
  · rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    have hk : (a, b) ∈ ker (f.coprod g) := hab
    rw [ker_coprod_of_disjoint_range f g hc.disjoint] at hk
    exact Prod.ext ((injective_iff_map_eq_zero f).1 hf a hk.1)
      ((injective_iff_map_eq_zero g).1 hg b hk.2)
  · rw [← range_eq_top, range_coprod, hc.sup_eq_top]

end LinearMap
