/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.ProZero
public import TauCeti.Algebra.Category.ModuleCat.Tower.Reduction

/-!
# Inverse limits with pro-zero obstructions

A levelwise injective comparison `F → G` that is exact at `G` with obstruction tower `H`
induces a bijection on inverse limits whenever `H` has vanishing limit, in particular when
`H` is pro-zero. For an `I`-adically complete module, this identifies the module itself with
the limit of any such comparison out of its reduction tower.

In the scalar case, suppose `Fₙ → Gₙ → Q` is exact, the first map is injective, and the maps to
`Q` commute with the transitions on `G` and multiplication by `f` on `Q`. If a fixed power of `f`
annihilates `Q`, then `lim F → lim G` is bijective. Surjectivity of `Gₙ → Q` is not
required: an obstruction in a compatible family is divisible, compatibly, by arbitrarily
large powers of `f`, and hence vanishes.

For `Fₙ = M / fⁿ⁺¹ M`, this identifies the completion of `M` with `lim G`. If `M` is
already complete, it identifies `M` itself with that limit. These are the algebraic
inverse-limit comparisons used for sections on infinitesimal neighbourhoods: the obstruction
lies in a cohomology module, and the connecting maps between successive obstructions are
multiplication by the defining equation. The geometric exact sequences are separate inputs.

The argument follows the bounded-cohomology-obstruction step in the proof of Stacks,
Lemma 52.12.7 (0EII). It reuses the exactness of inverse limits and the vanishing of limits
of pro-zero towers, rather than constructing limits of representatives.
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

/-- Let `iₙ : M / fⁿ⁺¹ M → Gₙ` be compatible injections whose obstructions lie in a
uniformly `f`-power-annihilated module and transition by multiplication by `f`. If `M` is
`(f)`-adically complete, the canonical map `M → lim Gₙ` is bijective. This is the complete
module form of the bounded-obstruction comparison for sections of thickenings. -/
theorem limMap_comp_toLimReduction_bijective_of_pow_smul_eq_zero
    {M : Type v} [AddCommGroup M] [Module R M] (f : R)
    [IsAdicComplete (Ideal.span {f}) M] {G : ModuleTower.{v} R}
    (i : reduction (Ideal.span {f}) M ⟶ G) (δ : G ⟶ smulTower Q f)
    (hi : ∀ n, Function.Injective (i.app (op n)).hom)
    (hex : ∀ n, Function.Exact (i.app (op n)).hom (δ.app (op n)).hom)
    (hQ : ∃ k : ℕ, ∀ x : Q, f ^ k • x = 0) :
    Function.Bijective (limMap i ∘ₗ toLimReduction (Ideal.span {f}) M) :=
  limMap_comp_toLimReduction_bijective_of_isProZero (Ideal.span {f}) i δ hi hex
    ((isProZero_smulTower_iff f).2 hQ)

end TauCeti.ModuleTower
