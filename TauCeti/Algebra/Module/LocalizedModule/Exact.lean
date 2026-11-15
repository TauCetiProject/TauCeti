/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# The five lemma for localizations of modules

Consider a commutative ladder of `R`-modules with exact rows

```
M₁ --f₁--> M₂ --f₂--> M₃ --f₃--> M₄ --f₄--> M₅
|          |          |          |          |
i₁         i₂         i₃         i₄         i₅
v          v          v          v          v
N₁ --g₁--> N₂ --g₂--> N₃ --g₃--> N₄ --g₄--> N₅
```

If the four outer vertical maps are localizations at a submonoid `S`, then so is the middle one
(`IsLocalizedModule.of_exact`). Localization is exact, so the localized top row maps to the bottom
row by a ladder whose outer maps are isomorphisms, and the five lemma applies; the elements of `S`
act invertibly on `N₃` by the five lemma for the ladder given by multiplication by `s` on the
bottom row.

This is how the localization property of a long exact sequence of cohomology groups propagates
from the outer terms to the middle one: for instance, for a quasi-coherent sheaf on a
quasi-compact quasi-separated scheme it propagates along the Mayer–Vietoris sequence.

The degenerate case of a map between zero modules is recorded as
`IsLocalizedModule.of_subsingleton`.
-/

public section

namespace IsLocalizedModule

section CommSemiring

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

/-- A linear map between zero modules is a localization at every submonoid. -/
theorem of_subsingleton {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module R M]
    [Module R N] [Subsingleton M] [Subsingleton N] (f : M →ₗ[R] N) : IsLocalizedModule S f where
  map_units _ := isUnit_of_subsingleton _
  surj _ := ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩
  exists_of_eq _ := ⟨1, Subsingleton.elim _ _⟩

end CommSemiring

variable {R : Type*} [CommRing R] (S : Submonoid R)

variable {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : Type*}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R M₅]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄] [AddCommGroup N₅]
  [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄] [Module R N₅]
  {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {f₃ : M₃ →ₗ[R] M₄} {f₄ : M₄ →ₗ[R] M₅}
  {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃} {g₃ : N₃ →ₗ[R] N₄} {g₄ : N₄ →ₗ[R] N₅}
  {i₁ : M₁ →ₗ[R] N₁} {i₂ : M₂ →ₗ[R] N₂} {i₃ : M₃ →ₗ[R] N₃} {i₄ : M₄ →ₗ[R] N₄}
  {i₅ : M₅ →ₗ[R] N₅}

/-- **The five lemma for localizations.** In a commutative ladder of modules with exact rows
`M₁ → M₂ → M₃ → M₄ → M₅` and `N₁ → N₂ → N₃ → N₄ → N₅`, if the four outer vertical maps are
localizations at `S`, then so is the middle one `i₃ : M₃ → N₃`. -/
theorem of_exact (hc₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (hc₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂)
    (hc₃ : g₃ ∘ₗ i₃ = i₄ ∘ₗ f₃) (hc₄ : g₄ ∘ₗ i₄ = i₅ ∘ₗ f₄)
    (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃) (hf₃ : Function.Exact f₃ f₄)
    (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)
    [IsLocalizedModule S i₁] [IsLocalizedModule S i₂] [IsLocalizedModule S i₄]
    [IsLocalizedModule S i₅] : IsLocalizedModule S i₃ := by
  -- Each `s ∈ S` acts bijectively on `N₃`: apply the five lemma to multiplication by `s`.
  have hu (s : S) : IsUnit (algebraMap R (Module.End R N₃) s) := by
    rw [Module.End.isUnit_iff]
    have hb₁ := (Module.End.isUnit_iff _).mp (map_units i₁ s)
    have hb₂ := (Module.End.isUnit_iff _).mp (map_units i₂ s)
    have hb₄ := (Module.End.isUnit_iff _).mp (map_units i₄ s)
    have hb₅ := (Module.End.isUnit_iff _).mp (map_units i₅ s)
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      g₁ g₂ g₃ g₄ g₁ g₂ g₃ g₄ _ _ _ _ _ (by ext; simp) (by ext; simp) (by ext; simp)
      (by ext; simp) hg₁ hg₂ hg₃ hg₁ hg₂ hg₃ hb₁.2 hb₂ hb₄ hb₅.1
  -- Compare the localized top row with the bottom row.
  let l₁ := LocalizedModule.mkLinearMap S M₁
  let l₂ := LocalizedModule.mkLinearMap S M₂
  let l₃ := LocalizedModule.mkLinearMap S M₃
  let l₄ := LocalizedModule.mkLinearMap S M₄
  let l₅ := LocalizedModule.mkLinearMap S M₅
  let ψ₃ := lift S l₃ i₃ hu
  have hψ₃ : ψ₃ ∘ₗ l₃ = i₃ := lift_comp S l₃ i₃ hu
  have hbij : Function.Bijective ψ₃ := by
    refine LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (map S l₁ l₂ f₁) (map S l₂ l₃ f₂) (map S l₃ l₄ f₃) (map S l₄ l₅ f₄) g₁ g₂ g₃ g₄
      (linearEquiv S l₁ i₁).toLinearMap (linearEquiv S l₂ i₂).toLinearMap ψ₃
      (linearEquiv S l₄ i₄).toLinearMap (linearEquiv S l₅ i₅).toLinearMap ?_ ?_ ?_ ?_
      (LocalizedModule.map_exact S f₁ f₂ hf₁) (LocalizedModule.map_exact S f₂ f₃ hf₂)
      (LocalizedModule.map_exact S f₃ f₄ hf₃) hg₁ hg₂ hg₃
      (linearEquiv S l₁ i₁).surjective (linearEquiv S l₂ i₂).bijective
      (linearEquiv S l₄ i₄).bijective (linearEquiv S l₅ i₅).injective
    · refine linearMap_ext S l₁ i₂ ?_
      ext x
      simpa using congr($hc₁ x)
    · refine ext S l₂ hu ?_
      ext x
      simpa [← hψ₃] using congr($hc₂ x)
    · refine linearMap_ext S l₃ i₄ ?_
      ext x
      simpa [← hψ₃] using congr($hc₃ x)
    · refine linearMap_ext S l₄ i₅ ?_
      ext x
      simpa using congr($hc₄ x)
  rw [← hψ₃]
  exact (comp_iff_of_bijective_left S ψ₃ hbij).mpr inferInstance

end IsLocalizedModule
