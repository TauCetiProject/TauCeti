/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Composites of semilinear maps

Forgetting scalar compatibility commutes with composition of semilinear maps
(`LinearMap.toAddMonoidHom_comp`). Composites of injective or surjective semilinear maps are
injective or surjective (`LinearMap.injective_comp`, `LinearMap.surjective_comp`); these restate
`Function.Injective.comp` and `Function.Surjective.comp` for the coercion of `g.comp f`, so that
they can be passed where a proof about exactly this coercion is expected. Composing with an
injective map on the left or a surjective map on the right kills no nonzero map
(`LinearMap.comp_eq_zero_iff_of_injective`, `LinearMap.comp_eq_zero_iff_of_surjective`).
Pasting a commutative square onto a factorization gives a factorization
(`LinearMap.comp_comp_eq_comp_comp_of_comp_eq`).
A homotopy between maps of modules with square-zero differentials transfers the property of
commuting with the differentials from one map to the other
(`LinearMap.comp_eq_comp_of_comp_add_comp_eq_add`).
-/

public section

namespace LinearMap

variable {R S T M N P : Type*} [Semiring R] [Semiring S] [Semiring T]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module S N] [Module T P]
  {σ : R →+* S} {τ : S →+* T} {υ : R →+* T} [RingHomCompTriple σ τ υ]

/-- The additive map underlying a composite is the composite of the underlying additive maps. -/
@[simp] theorem toAddMonoidHom_comp (g : N →ₛₗ[τ] P) (f : M →ₛₗ[σ] N) :
    (g.comp f : M →ₛₗ[υ] P).toAddMonoidHom =
      g.toAddMonoidHom.comp f.toAddMonoidHom := rfl

/-- A composite of injective semilinear maps is injective, stated for the coercion of `g.comp f`. -/
theorem injective_comp {g : N →ₛₗ[τ] P} {f : M →ₛₗ[σ] N} (hg : Function.Injective g)
    (hf : Function.Injective f) : Function.Injective (g.comp f : M →ₛₗ[υ] P) :=
  hg.comp hf

/-- A composite of surjective semilinear maps is surjective, stated for the coercion of
`g.comp f`. -/
theorem surjective_comp {g : N →ₛₗ[τ] P} {f : M →ₛₗ[σ] N} (hg : Function.Surjective g)
    (hf : Function.Surjective f) : Function.Surjective (g.comp f : M →ₛₗ[υ] P) :=
  hg.comp hf

/-- Postcomposing with an injective semilinear map sends only the zero map to zero. -/
theorem comp_eq_zero_iff_of_injective {g : N →ₛₗ[τ] P} (hg : Function.Injective g)
    (f : M →ₛₗ[σ] N) : (g.comp f : M →ₛₗ[υ] P) = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ext fun x ↦ hg ?_, fun h ↦ by simp [h]⟩
  simpa using LinearMap.congr_fun h x

/-- Precomposing with a surjective semilinear map sends only the zero map to zero. -/
theorem comp_eq_zero_iff_of_surjective {f : M →ₛₗ[σ] N} (hf : Function.Surjective f)
    (g : N →ₛₗ[τ] P) : (g.comp f : M →ₛₗ[υ] P) = 0 ↔ g = 0 := by
  refine ⟨fun h ↦ ext fun y ↦ ?_, fun h ↦ by simp [h]⟩
  obtain ⟨x, rfl⟩ := hf y
  simpa using LinearMap.congr_fun h x

section Paste

variable {R U V W V' W' Y : Type*} [Semiring R] [AddCommMonoid U] [AddCommMonoid V]
  [AddCommMonoid W] [AddCommMonoid V'] [AddCommMonoid W'] [AddCommMonoid Y] [Module R U]
  [Module R V] [Module R W] [Module R V'] [Module R W'] [Module R Y]

/-- **Pasting a commutative square onto a factorization.** If `ψ ∘ y = g ∘ q` and the square
`b ∘ ψ = ψ' ∘ a` commutes, then `ψ' ∘ (a ∘ y) = (b ∘ g) ∘ q`: a lift of `g ∘ q` along `ψ`,
followed by `a`, is a lift of `(b ∘ g) ∘ q` along `ψ'`. -/
theorem comp_comp_eq_comp_comp_of_comp_eq {ψ : V →ₗ[R] W} {ψ' : V' →ₗ[R] W'} {a : V →ₗ[R] V'}
    {b : W →ₗ[R] W'} (h : b ∘ₗ ψ = ψ' ∘ₗ a) {y : U →ₗ[R] V} {g : Y →ₗ[R] W} {q : U →ₗ[R] Y}
    (hy : ψ ∘ₗ y = g ∘ₗ q) : ψ' ∘ₗ (a ∘ₗ y) = (b ∘ₗ g) ∘ₗ q := by
  rw [← comp_assoc, ← h, comp_assoc, hy, comp_assoc]

end Paste

section Homotopy

variable {R V W : Type*} [Semiring R] [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]

/-- **A homotopy transfers the chain-map property.** Let `d₀` and `d₁` be differentials,
`d₀ ∘ d₀ = 0` and `d₁ ∘ d₁ = 0`, and let `F` commute with them. If
`d₁ ∘ K + K ∘ d₀ = F + G` for some `K`, then `G` commutes with them as well. -/
theorem comp_eq_comp_of_comp_add_comp_eq_add {d₀ : V →ₗ[R] V} {d₁ : W →ₗ[R] W}
    (h₀ : d₀ ∘ₗ d₀ = 0) (h₁ : d₁ ∘ₗ d₁ = 0) {K F G : V →ₗ[R] W} (hF : d₁ ∘ₗ F = F ∘ₗ d₀)
    (hK : d₁ ∘ₗ K + K ∘ₗ d₀ = F + G) : d₁ ∘ₗ G = G ∘ₗ d₀ := by
  -- Solve the homotopy identity for `G` and use `d ∘ d = 0` on both sides.
  obtain rfl : G = d₁ ∘ₗ K + K ∘ₗ d₀ - F := by rw [hK, add_sub_cancel_left]
  rw [comp_sub, sub_comp, comp_add, add_comp, ← comp_assoc K d₁ d₁, h₁, zero_comp,
    comp_assoc d₀ d₀ K, h₀, comp_zero, zero_add, add_zero, hF, comp_assoc]

end Homotopy

end LinearMap
