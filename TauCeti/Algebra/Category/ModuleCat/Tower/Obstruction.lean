/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.ProZero
public import TauCeti.Algebra.Category.ModuleCat.Tower.Reduction

/-!
# Comparing adically complete modules with inverse limits

Let `M` be an `I`-adically complete module. A levelwise injective comparison
`reduction I M → G` that is exact at `G` with obstruction tower `H` induces a bijection
`M → lim G` whenever `H.lim = ⊥`, in particular when `H` is pro-zero. The reduction tower
has terms `M / Iⁿ⁺¹ M`. These comparisons specialize
`TauCeti.ModuleTower.limMap_bijective_of_lim_eq_bot` from `Tower.Exact` and
`TauCeti.ModuleTower.limMap_bijective_of_isProZero` from `Tower.ProZero`.

For scalar-multiplication obstructions, the levelwise obstruction maps take values in a module
`Q` and commute with the transitions on `G` and multiplication by `f` on `Q`. If a fixed power
`f ^ k` annihilates `Q`, every compatible obstruction family satisfies
`qₙ = f ^ k • qₙ₊ₖ = 0`. Surjectivity of the obstruction maps is not required. The resulting
bijection `M → lim G` is the complete-source form of
`TauCeti.ModuleTower.limMap_bijective_of_pow_smul_eq_zero` from `Tower.ProZero`.

These are the algebraic inverse-limit comparisons used for sections on infinitesimal
neighbourhoods: the obstruction lies in a cohomology module, and the connecting maps between
successive obstructions are multiplication by the defining equation. The geometric exact
sequences are separate inputs.

The mathematical reference is the bounded-cohomology-obstruction step in the proof of Stacks,
Lemma 52.12.7 (0EII).
-/

public section

open CategoryTheory Opposite

universe u v

namespace TauCeti.ModuleTower

variable {R : Type u} [CommRing R]

/-- If an `I`-adically complete module's reduction injects levelwise into a tower with an exact
obstruction tower whose limit vanishes, the induced map from the module to that tower's limit
is bijective. -/
theorem limMap_comp_toLimReduction_bijective_of_lim_eq_bot
    {M : Type v} [AddCommGroup M] [Module R M] (I : Ideal R)
    [IsAdicComplete I M] {G H : ModuleTower.{v} R}
    (i : reduction I M ⟶ G) (δ : G ⟶ H)
    (hi : ∀ n, Function.Injective (i.app (op n)).hom)
    (hex : ∀ n, Function.Exact (i.app (op n)).hom (δ.app (op n)).hom)
    (hH : H.lim = ⊥) :
    Function.Bijective (limMap i ∘ₗ toLimReduction I M) :=
  (limMap_bijective_of_lim_eq_bot i δ hi hex hH).comp (toLimReduction_bijective I M)

/-- If an `I`-adically complete module's reduction injects levelwise into a tower with an exact
pro-zero obstruction tower, the induced map from the module to that tower's limit is bijective. -/
theorem limMap_comp_toLimReduction_bijective_of_isProZero
    {M : Type v} [AddCommGroup M] [Module R M] (I : Ideal R)
    [IsAdicComplete I M] {G H : ModuleTower.{v} R}
    (i : reduction I M ⟶ G) (δ : G ⟶ H)
    (hi : ∀ n, Function.Injective (i.app (op n)).hom)
    (hex : ∀ n, Function.Exact (i.app (op n)).hom (δ.app (op n)).hom)
    (hH : H.IsProZero) :
    Function.Bijective (limMap i ∘ₗ toLimReduction I M) :=
  limMap_comp_toLimReduction_bijective_of_lim_eq_bot I i δ hi hex (lim_eq_bot_of_isProZero hH)

variable {Q : Type v} [AddCommGroup Q] [Module R Q]

/-- Let `iₙ : M / Iⁿ⁺¹ M → Gₙ` be compatible injections whose obstructions lie in a
uniformly `f`-power-annihilated module and transition by multiplication by `f`. If `M` is
`I`-adically complete, the canonical map `M → lim Gₙ` is bijective. This is the complete
module form of the bounded-obstruction comparison for sections of thickenings. -/
theorem limMap_comp_toLimReduction_bijective_of_pow_smul_eq_zero
    {M : Type v} [AddCommGroup M] [Module R M] (I : Ideal R) (f : R)
    [IsAdicComplete I M] {G : ModuleTower.{v} R}
    (i : reduction I M ⟶ G) (δ : ∀ n, G.obj (op n) →ₗ[R] Q)
    (hi : ∀ n, Function.Injective (i.app (op n)).hom)
    (hex : ∀ n, Function.Exact (i.app (op n)).hom (δ n))
    (hδ : ∀ n x, δ n (G.transition n x) = f • δ (n + 1) x)
    (hQ : ∃ k : ℕ, ∀ x : Q, f ^ k • x = 0) :
    Function.Bijective (limMap i ∘ₗ toLimReduction I M) :=
  (limMap_bijective_of_pow_smul_eq_zero i f δ hi hex hδ hQ).comp
    (toLimReduction_bijective I M)

end TauCeti.ModuleTower
