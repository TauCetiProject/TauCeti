/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZMod.Injective
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Quotient
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.FourLemma

/-!
# Tate's duality maps through a normal subgroup of finite index, by dimension shifting

Let `G` be a compact topological group, `V` a normal subgroup of finite index, and `N` a discrete
`G`-module with `N ≃+ ZMod n` and `H²(G, N) ≃+ ZMod n`, on which `V` acts trivially. For a finite
discrete `G`-module `M` write `M' = InternalHom G M N` for its dual and
`αᵢ : Hⁱ(G, M) → Hom(H²⁻ⁱ(G, M'), H²(G, N))`, `i = 0, 1, 2`, for Tate's duality maps
(`TauCeti.ContCohomology.dualityMap0`, `dualityMap1`, `dualityMap2`).

This file proves that **Tate's duality on the coinduced modules gives Tate's duality on every
finite module killed by `n` on which `V` acts trivially**
(`TauCeti.ContCohomology.dualityMap0_bijective_of_bijective_discreteCoind`,
`dualityMap1_bijective_of_injective_discreteCoind`,
`dualityMap2_bijective_of_bijective_discreteCoind`): if `α₀`, `α₁` are bijective and `α₂` is
injective on `Coind_V^G A` for every such `A`, then `α₀` and `α₂` are bijective on every such `A`;
and if `α₀` is bijective and `α₁` injective on `Coind_V^G A` for
every such `A`, then so is `α₁` on every such `A` once `H¹(G, A')` is finite. Over a
local field `K`, with `V = G_L` for a finite Galois extension `L/K` containing the `n`-th roots of
unity and `N = μₙ`, this is the step of local Tate duality that passes from the coinduced modules,
whose duality is that of `G_L` by Shapiro's lemma, to all finite Galois modules killed by `n` that
become trivial over `L`.

The class `𝒞` of finite discrete `G`-modules killed by `n` on which `V` acts trivially is closed
under the two operations the argument needs: the cokernel `Coind_V^G A ⧸ A` of the unit of
coinduction (`TauCeti.ContCohomology.CoindQuotient.smul_eq_self_of_forall_smul_eq_self`, using
normality of `V`), and the dual `A'`, since `V` acts trivially on `N`. The argument runs in two
passes over `𝒞`, along the short exact sequence `0 → A → Coind_V^G A → C → 0` of the unit
(`TauCeti.ContCohomology.coindShortExact`), whose dual sequence exists for all coefficients
(`TauCeti.ContCohomology.precomp_coindShortExact_inclDistribMulActionHom_surjective`).

* **Injectivity, degree by degree.** `α₀` is injective on `A` because it is on `Coind_V^G A` and
  `H⁰` is left exact (`TauCeti.ContCohomology.dualityMap0_injective_of_injective`). Injectivity of
  `αᵢ` on the cokernel `C`, which lies in `𝒞`, then gives injectivity of `αᵢ₊₁` on `A` by the four
  lemma along the ladder of the sequence
  (`TauCeti.ContCohomology.DiscreteShortExact.dualityMap1_injective_left`,
  `DiscreteShortExact.dualityMap2_injective_left`); the Baer hypothesis on `H²(G, N)` holds since
  `ℤ/nℤ` is self-injective.
* **Bijectivity, by counting.** On `A ∈ 𝒞` with dual `A' ∈ 𝒞`, injectivity of `αᵢ` on `A` and of
  `α₂₋ᵢ` on `A'` forces `|Hⁱ(G, A)| = |H²⁻ⁱ(G, A')|`, so that `αᵢ` is bijective
  (`TauCeti.ContCohomology.dualityMap0_bijective_of_injective_of_addEquiv_zmod` and its
  companions). Finiteness of `H¹(G, A')` is the one input of the count not supplied by the
  argument itself: `H⁰` is a subgroup of a finite module, and `H²(G, A')` embeds by `α₂` into the
  finite group `Hom(H⁰(G, A''), H²(G, N))`.

## Main results

* `TauCeti.ContCohomology.dualityMap0_bijective_of_bijective_discreteCoind`,
  `dualityMap1_bijective_of_injective_discreteCoind` and
  `dualityMap2_bijective_of_bijective_discreteCoind`: Tate's duality on the finite modules killed
  by `n` on which `V` acts trivially, from Tate's duality on their coinduced modules (in degree
  `1`, only `α₀` bijective and `α₁` injective there, together with the finiteness of `H¹` of the
  dual).

## References

* J.-P. Serre, *Galois Cohomology*, Ch. II, §5.2, proof of Theorem 2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.2.6).
-/

public section

namespace TauCeti.ContCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {V : Subgroup G} [V.Normal] [V.FiniteIndex]
  {N : Type u} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction G N] [ContinuousSMul G N] {n : ℕ} [NeZero n]

section

variable (e : N ≃+ ZMod n) (e₂ : H2 G N ≃+ ZMod n) (hN : ∀ v ∈ V, ∀ y : N, v • y = y)
  (hcoind₁ : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A], (∀ a : A, n • a = 0) →
    (∀ v ∈ V, ∀ a : A, v • a = a) →
    Function.Bijective (dualityMap0 G (DiscreteCoind G V A) N) ∧
      Function.Injective (dualityMap1 G (DiscreteCoind G V A) N))
  (hcoind : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A], (∀ a : A, n • a = 0) →
    (∀ v ∈ V, ∀ a : A, v • a = a) →
    Function.Bijective (dualityMap0 G (DiscreteCoind G V A) N) ∧
      Function.Bijective (dualityMap1 G (DiscreteCoind G V A) N) ∧
        Function.Injective (dualityMap2 G (DiscreteCoind G V A) N))
  (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] [Finite A] (hA : ∀ a : A, n • a = 0)
  (hAV : ∀ v ∈ V, ∀ a : A, v • a = a)

omit [CompactSpace G] [V.FiniteIndex] [NeZero n] [Finite A] in
include hA hAV in
/-- The class of finite modules killed by `n` on which `V` acts trivially is closed under the
cokernel `Coind_V^G A ⧸ A` of the unit of coinduction. -/
private theorem nsmul_eq_zero_and_smul_eq_self_coindQuotient :
    (∀ c : CoindQuotient G V A, n • c = 0) ∧ ∀ v ∈ V, ∀ c : CoindQuotient G V A, v • c = c :=
  ⟨(coindShortExact G V A).nsmul_eq_zero_right (DiscreteCoind.nsmul_eq_zero hA),
    fun _ hv ↦ CoindQuotient.smul_eq_self_of_forall_smul_eq_self (fun u a ↦ hAV u u.2 a) hv⟩

include e₂ hcoind₁ hA hAV in
/-- Injectivity of `α₀` and `α₁`, which needs only `α₀` bijective and `α₁` injective on the
coinduced modules; the proof runs over the whole class of finite modules killed by `n` on which
`V` acts trivially, since the cokernel of the unit is used. -/
private theorem dualityMap_injective_le_one_of_injective_discreteCoind :
    Function.Injective (dualityMap0 G A N) ∧ Function.Injective (dualityMap1 G A N) := by
  obtain ⟨_, hH2⟩ := Module.Baer.exists_module_of_addEquiv_zmod e₂
  -- injectivity of `α₀` on `𝒞`, from `A ↪ Coind_V^G A`
  have h₀ : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A], (∀ a : A, n • a = 0) →
      (∀ v ∈ V, ∀ a : A, v • a = a) → Function.Injective (dualityMap0 G A N) :=
    fun A _ _ _ _ _ _ hA hAV ↦
      dualityMap0_injective_of_injective DiscreteCoind.unit_injective (hcoind₁ A hA hAV).1.1
  -- injectivity of `α₁` on `A`, by the four lemma along `0 → A → Coind_V^G A → C → 0`
  exact ⟨h₀ A hA hAV,
    (coindShortExact G V A).dualityMap1_injective_left
      (precomp_coindShortExact_inclDistribMulActionHom_surjective G V A)
      (DiscreteCoind.nsmul_eq_zero hA) hH2 (hcoind₁ A hA hAV).1.2
      (h₀ _ (nsmul_eq_zero_and_smul_eq_self_coindQuotient A hA hAV).1
        (nsmul_eq_zero_and_smul_eq_self_coindQuotient A hA hAV).2) (hcoind₁ A hA hAV).2⟩

include e₂ hcoind hA hAV in
/-- Injectivity of the three duality maps at once. -/
private theorem dualityMap_injective_of_bijective_discreteCoind :
    Function.Injective (dualityMap0 G A N) ∧ Function.Injective (dualityMap1 G A N) ∧
      Function.Injective (dualityMap2 G A N) := by
  obtain ⟨_, hH2⟩ := Module.Baer.exists_module_of_addEquiv_zmod e₂
  have hcoind₁ := fun (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
      [DistribMulAction G A] [ContinuousSMul G A] [Finite A] (hA : ∀ a : A, n • a = 0)
      (hAV : ∀ v ∈ V, ∀ a : A, v • a = a) ↦
    And.intro (hcoind A hA hAV).1 (hcoind A hA hAV).2.1.1
  -- injectivity of `α₂` on `A`, by the four lemma along `0 → A → Coind_V^G A → C → 0`
  exact ⟨(dualityMap_injective_le_one_of_injective_discreteCoind e₂ hcoind₁ A hA hAV).1,
    (dualityMap_injective_le_one_of_injective_discreteCoind e₂ hcoind₁ A hA hAV).2,
    (coindShortExact G V A).dualityMap2_injective_left
      (precomp_coindShortExact_inclDistribMulActionHom_surjective G V A)
      (DiscreteCoind.nsmul_eq_zero hA) hH2 (hcoind A hA hAV).2.1.2
      (dualityMap_injective_le_one_of_injective_discreteCoind e₂ hcoind₁ _
        (nsmul_eq_zero_and_smul_eq_self_coindQuotient A hA hAV).1
        (nsmul_eq_zero_and_smul_eq_self_coindQuotient A hA hAV).2).2
      (hcoind A hA hAV).2.2⟩

include e₂ hN hcoind hA hAV in
/-- Injectivity of the three duality maps on the dual `A' = InternalHom G A N`, which lies in the
same class as `A` since `V` acts trivially on `N`. -/
private theorem dualityMap_injective_internalHom_of_bijective_discreteCoind [Finite N] :
    Function.Injective (dualityMap0 G (InternalHom G A N) N) ∧
      Function.Injective (dualityMap1 G (InternalHom G A N) N) ∧
        Function.Injective (dualityMap2 G (InternalHom G A N) N) :=
  dualityMap_injective_of_bijective_discreteCoind e₂ hcoind _
    (InternalHom.nsmul_eq_zero_of_domain hA)
    fun v hv φ ↦ InternalHom.smul_eq_self_iff.2 fun a ↦ by rw [hAV v hv, hN v hv]

include e e₂ hN hA hAV

include hcoind in
/-- **Tate's duality map `α₀` through a normal subgroup of finite index.** Let `G` be a compact
group, `V` a normal subgroup of finite index, and `N` a discrete `G`-module on which `V` acts
trivially, with `N ≃+ ZMod n` and `H²(G, N) ≃+ ZMod n`. Suppose that for every finite discrete
`G`-module `A` killed by `n` on which `V` acts trivially, Tate's duality maps `α₀`, `α₁` are
bijective and `α₂` is injective on the coinduced module `Coind_V^G A`. Then
`α₀ : H⁰(G, A) → Hom(H²(G, A'), H²(G, N))` is bijective on every such `A`. -/
theorem dualityMap0_bijective_of_bijective_discreteCoind :
    Function.Bijective (dualityMap0 G A N) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  exact dualityMap0_bijective_of_injective_of_addEquiv_zmod e e₂ hA
    (dualityMap_injective_internalHom_of_bijective_discreteCoind e₂ hN hcoind A hA hAV).2.2
    (dualityMap_injective_of_bijective_discreteCoind e₂ hcoind A hA hAV).1

include hcoind₁ in
/-- **Tate's duality map `α₁` through a normal subgroup of finite index.** With `G`, `V`, `N` as
in `TauCeti.ContCohomology.dualityMap0_bijective_of_bijective_discreteCoind`, suppose that for
every finite discrete `G`-module `A` killed by `n` on which `V` acts trivially, `α₀` is bijective
and `α₁` is injective on the coinduced module `Coind_V^G A`. If moreover `H¹(G, A')` is finite, then
`α₁ : H¹(G, A) → Hom(H¹(G, A'), H²(G, N))` is bijective on every such `A`. -/
theorem dualityMap1_bijective_of_injective_discreteCoind [Finite (H1 G (InternalHom G A N))] :
    Function.Bijective (dualityMap1 G A N) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  exact dualityMap1_bijective_of_injective_of_addEquiv_zmod e e₂ hA
    (dualityMap_injective_le_one_of_injective_discreteCoind e₂ hcoind₁ _
      (InternalHom.nsmul_eq_zero_of_domain hA)
      fun v hv φ ↦ InternalHom.smul_eq_self_iff.2 fun a ↦ by rw [hAV v hv, hN v hv]).2
    (dualityMap_injective_le_one_of_injective_discreteCoind e₂ hcoind₁ A hA hAV).2

include hcoind in
/-- **Tate's duality map `α₂` through a normal subgroup of finite index**: under the hypotheses of
`TauCeti.ContCohomology.dualityMap0_bijective_of_bijective_discreteCoind`,
`α₂ : H²(G, A) → Hom(H⁰(G, A'), H²(G, N))` is bijective. -/
theorem dualityMap2_bijective_of_bijective_discreteCoind :
    Function.Bijective (dualityMap2 G A N) := by
  have : Finite N := Finite.of_equiv _ e.symm.toEquiv
  exact dualityMap2_bijective_of_injective_of_addEquiv_zmod e e₂ hA
    (dualityMap_injective_internalHom_of_bijective_discreteCoind e₂ hN hcoind A hA hAV).1
    (dualityMap_injective_of_bijective_discreteCoind e₂ hcoind A hA hAV).2.2

end

end TauCeti.ContCohomology
