/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.TraceShortExact
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.FourLemma
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Coeffaceable
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Devissage

/-!
# Dévissage of Tate's duality maps for a pro-`p` group

Let `G` be a pro-`p` group and `N` a discrete `G`-module which is a `ℤ/nℤ`-module satisfying Baer's
criterion, such that `H²(G, N)` satisfies Baer's criterion over `ℤ/nℤ` as well. For a finite
discrete `G`-module `M` write `M' = InternalHom G M N` for its `N`-dual, and
`αᵢ : Hⁱ(G, M) → Hom(H²⁻ⁱ(G, M'), H²(G, N))`, `i = 0, 1, 2`, for Tate's duality maps
(`TauCeti.ContCohomology.dualityMap0`, `dualityMap1`, `dualityMap2`). This file runs Tate's
dévissage argument: if `α₀` is surjective and `α₁` injective on every discrete `G`-module of order
`p` with trivial action killed by `n`, then the same holds on every finite `p`-primary discrete
`G`-module killed by `n` (`TauCeti.IsProP.dualityMap0_surjective_dualityMap1_injective`), and
likewise for `α₁` surjective and `α₂` injective
(`TauCeti.IsProP.dualityMap1_surjective_dualityMap2_injective`); the two dévissages run side by
side in `TauCeti.IsProP.dualityMap0_surjective_dualityMap1_bijective_dualityMap2_injective`, from
a base case stating all three properties at once. The induction is
`TauCeti.IsProP.finite_pPrimary_induction` along the trivial filtration, and the inductive step
is the four lemmas along a short exact sequence `0 → A → B → C → 0` killed by `n`
(`TauCeti.ContCohomology.DiscreteShortExact.dualityMap0_surjective` and its companions), whose
`N`-dual sequence exists because `N` is Baer, and whose `Hom(-, H²(G, N))`-dual bottom row is exact
because `H²(G, N)` is Baer. The four lemmas pair off: surjectivity of `α₀` and injectivity of `α₁`
on the two ends of an extension give both on its middle, and so do surjectivity of `α₁` and
injectivity of `α₂`.

For an infinite profinite pro-`p` group, `α₀` is moreover injective
(`TauCeti.IsProP.dualityMap0_injective`): `H⁰` is co-effaceable, the trace from a coinduced module
along a deep enough open subgroup vanishing on invariants
(`TauCeti.IsProP.exists_isOpen_trace_eq_zero_of_mem_H0`), and `α₁` is injective on the kernel of
the trace by the dévissage of `α₀` surjective and `α₁` injective, so only those two base cases are
needed. Together with the dévissage this gives all three maps at once
(`TauCeti.IsProP.dualityMap0_bijective_dualityMap1_bijective_dualityMap2_injective`): `α₀` and `α₁`
bijective, `α₂` injective.

The two instances of this argument are the coefficient system of a Demushkin group: `N = 𝔽_p`
with `n = p`, where `H²(G, 𝔽_p)` is an `𝔽_p`-vector space, and the twisted coefficients
`N = I(χ)/pⁱ` of the canonical character with `n = pⁱ`, where `H²(G, I(χ)/pⁱ) ≅ ℤ/pⁱ` is
self-injective. The remaining half of Tate's duality, the bijectivity of `α₂`, is a counting
argument on top of this dévissage that uses the double duality of `M` with respect to `N`, and is
not part of this file.

## Main results

* `TauCeti.IsProP.dualityMap0_surjective_dualityMap1_injective`,
  `TauCeti.IsProP.dualityMap1_surjective_dualityMap2_injective`: the two dévissages of Tate's
  duality maps, from the trivial modules of order `p` to every finite `p`-primary module killed
  by `n`.
* `TauCeti.IsProP.dualityMap0_surjective_dualityMap1_bijective_dualityMap2_injective`: the two
  dévissages combined, from a base case stating the three properties at once.
* `TauCeti.IsProP.dualityMap0_injective`: for an infinite profinite pro-`p` group, `α₀` is injective
  on every such module; and
  `TauCeti.IsProP.dualityMap0_bijective_dualityMap1_bijective_dualityMap2_injective`, the combined
  dévissage for such a group, where `α₀` is bijective.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.1.
-/

public section

namespace TauCeti

open ContCohomology

universe u v

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (hG : IsProP p G) {n : ℕ}
  (N : Type v) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction G N]
  [ContinuousSMul G N] [Module (ZMod n) N] (hN : Module.Baer (ZMod n) N)
  (hH2 : Module.Baer (ZMod n) (H2 G N))

include hG hN hH2

section SurjectiveInjective

variable (h : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
    (∀ (g : G) (a : A), g • a = a) → (∀ a : A, n • a = 0) →
    Function.Surjective (dualityMap0 G A N) ∧ Function.Injective (dualityMap1 G A N))
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M] [Finite M] (hM : IsPPrimaryTorsion p M) (hMn : ∀ m : M, n • m = 0)

include h hM hMn

/-- **The dévissage of `α₀` surjective and `α₁` injective.** Let `G` be a pro-`p` group and `N` a
discrete `G`-module which is a Baer `ℤ/nℤ`-module with `H²(G, N)` a Baer `ℤ/nℤ`-module. If Tate's
duality maps `α₀` and `α₁` into `H²(G, N)` are respectively surjective and injective on every
discrete `G`-module of order `p` with trivial action killed by `n`, then they are so on every finite
`p`-primary discrete `G`-module `M` killed by `n`: the pair of properties passes through extensions
by the four lemmas `DiscreteShortExact.dualityMap0_surjective` and `dualityMap1_injective`. -/
theorem IsProP.dualityMap0_surjective_dualityMap1_injective :
    Function.Surjective (dualityMap0 G M N) ∧ Function.Injective (dualityMap1 G M N) := by
  -- The motive quantifies over finiteness, which the duality maps need to be stated and which the
  -- induction principle does not carry in its zero case.
  refine hG.finite_pPrimary_induction
    (motive := fun M _ _ _ _ _ ↦ ∀ [Finite M], (∀ x : M, n • x = 0) →
      Function.Surjective (dualityMap0 G M N) ∧ Function.Injective (dualityMap1 G M N))
    (fun M _ _ _ _ _ _ _ _ ↦ ?_) (fun A _ _ _ _ _ _ hA htrivA _ hAn ↦ h A hA htrivA hAn)
    (fun A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ _ _ _ _ hA hC _ hB ↦ ?_) M hM hMn
  · -- the zero module: both sides of each duality map are trivial
    exact ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  · -- the extension step: two of the four lemmas along `0 → A → B → C → 0`
    obtain ⟨h₀A, h₁A⟩ := hA (S.nsmul_eq_zero_left hB)
    obtain ⟨h₀C, h₁C⟩ := hC (S.nsmul_eq_zero_right hB)
    have hsurj := S.precomp_inclDistribMulActionHom_surjective_of_baer N hN hB
    exact ⟨S.dualityMap0_surjective hsurj hB hH2 h₀A h₀C h₁A,
      S.dualityMap1_injective hsurj hB hH2 h₀C h₁A h₁C⟩

variable [CompactSpace G] [TotallyDisconnectedSpace G] [Infinite G]

/-- **Injectivity of `α₀` for an infinite pro-`p` group.** Under the hypotheses of the dévissage
of `α₀` surjective and `α₁` injective, if `G` is an infinite profinite pro-`p` group, then Tate's
duality map `α₀ : H⁰(G, M) → Hom(H²(G, M'), H²(G, N))` is injective on every finite `p`-primary
discrete `G`-module `M` killed by `n`: the trace `Coind_V^G M → M` along a deep enough open
subgroup `V` vanishes on invariants, and `α₁` is injective on its kernel. -/
theorem IsProP.dualityMap0_injective : Function.Injective (dualityMap0 G M N) := by
  obtain ⟨V, _, hV, htr⟩ := hG.exists_isOpen_trace_eq_zero_of_mem_H0 M hM
  obtain ⟨k, hk⟩ := hM.exists_pow_smul_eq_zero
  have hcoind : ∀ f : DiscreteCoind G V M, n • f = 0 := DiscreteCoind.nsmul_eq_zero hMn
  refine (DiscreteCoind.traceShortExact G V M hV).dualityMap0_injective_of_explicitCoeff0_eq_zero
    ((DiscreteCoind.traceShortExact G V M hV).precomp_inclDistribMulActionHom_surjective_of_baer
      N hN hcoind) ?_
    (hG.dualityMap0_surjective_dualityMap1_injective N hN hH2 h (DiscreteCoind.traceKer G V M)
      (isPPrimaryTorsion_iff.2 fun f ↦
        ⟨k, Subtype.ext (by simpa using DiscreteCoind.nsmul_eq_zero hk f.1)⟩)
      fun f ↦ Subtype.ext (by simpa using hcoind f)).2
  refine AddMonoidHom.ext fun f ↦ Subtype.ext ?_
  rw [coe_explicitCoeff0, AddMonoidHom.zero_apply, DiscreteShortExact.projDistribMulActionHom_apply,
    DiscreteCoind.traceShortExact_proj]
  exact htr f f.2

end SurjectiveInjective

section InjectiveSurjective

variable (h : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
    (∀ (g : G) (a : A), g • a = a) → (∀ a : A, n • a = 0) →
    Function.Surjective (dualityMap1 G A N) ∧ Function.Injective (dualityMap2 G A N))
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M] [Finite M] (hM : IsPPrimaryTorsion p M) (hMn : ∀ m : M, n • m = 0)

include h hM hMn

/-- **The dévissage of `α₁` surjective and `α₂` injective.** Under the hypotheses of the dévissage,
if Tate's duality maps `α₁` and `α₂` into `H²(G, N)` are respectively surjective and injective on
every discrete `G`-module of order `p` with trivial action killed by `n`, then they are so on every
finite `p`-primary discrete `G`-module `M` killed by `n`: the pair of properties passes through
extensions by the four lemmas `DiscreteShortExact.dualityMap1_surjective` and
`dualityMap2_injective`. -/
theorem IsProP.dualityMap1_surjective_dualityMap2_injective :
    Function.Surjective (dualityMap1 G M N) ∧ Function.Injective (dualityMap2 G M N) := by
  refine hG.finite_pPrimary_induction
    (motive := fun M _ _ _ _ _ ↦ ∀ [Finite M], (∀ x : M, n • x = 0) →
      Function.Surjective (dualityMap1 G M N) ∧ Function.Injective (dualityMap2 G M N))
    (fun M _ _ _ _ _ _ _ _ ↦ ?_) (fun A _ _ _ _ _ _ hA htrivA _ hAn ↦ h A hA htrivA hAn)
    (fun A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S _ _ _ _ _ hA hC _ hB ↦ ?_) M hM hMn
  · -- the zero module: both sides of each duality map are trivial
    exact ⟨fun _ ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  · -- the extension step: two of the four lemmas along `0 → A → B → C → 0`
    obtain ⟨h₁A, h₂A⟩ := hA (S.nsmul_eq_zero_left hB)
    obtain ⟨h₁C, h₂C⟩ := hC (S.nsmul_eq_zero_right hB)
    have hsurj := S.precomp_inclDistribMulActionHom_surjective_of_baer N hN hB
    exact ⟨S.dualityMap1_surjective hsurj hB hH2 h₁A h₁C h₂A,
      S.dualityMap2_injective hsurj hB hH2 h₁C h₂A h₂C⟩

end InjectiveSurjective

section Combined

variable (h : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A], Nat.card A = p →
    (∀ (g : G) (a : A), g • a = a) → (∀ a : A, n • a = 0) →
    Function.Surjective (dualityMap0 G A N) ∧ Function.Bijective (dualityMap1 G A N) ∧
      Function.Injective (dualityMap2 G A N))
  (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M] [Finite M] (hM : IsPPrimaryTorsion p M) (hMn : ∀ m : M, n • m = 0)

include h hM hMn

/-- **The two dévissages of Tate's duality maps, side by side.** Under the hypotheses of the
dévissage, if on every discrete `G`-module of order `p` with trivial action killed by `n` Tate's
duality maps `α₀`, `α₁`, `α₂` into `H²(G, N)` are respectively surjective, bijective and injective,
then they are so on every finite `p`-primary discrete `G`-module `M` killed by `n`. -/
theorem IsProP.dualityMap0_surjective_dualityMap1_bijective_dualityMap2_injective :
    Function.Surjective (dualityMap0 G M N) ∧ Function.Bijective (dualityMap1 G M N) ∧
      Function.Injective (dualityMap2 G M N) :=
  have ⟨h₀, h₁⟩ := hG.dualityMap0_surjective_dualityMap1_injective N hN hH2
    (fun A _ _ _ _ _ _ hA htrivA hAn ↦ (h A hA htrivA hAn).imp_right fun h ↦ h.1.1) M hM hMn
  have ⟨h₁', h₂⟩ := hG.dualityMap1_surjective_dualityMap2_injective N hN hH2
    (fun A _ _ _ _ _ _ hA htrivA hAn ↦ (h A hA htrivA hAn).2.imp_left fun h ↦ h.2) M hM hMn
  ⟨h₀, ⟨h₁, h₁'⟩, h₂⟩

variable [CompactSpace G] [TotallyDisconnectedSpace G] [Infinite G]

/-- **The dévissage of Tate's duality maps for an infinite pro-`p` group.** Under the hypotheses of
`IsProP.dualityMap0_surjective_dualityMap1_bijective_dualityMap2_injective`, if `G` is an infinite
profinite pro-`p` group, then on every finite `p`-primary discrete `G`-module `M` killed by `n`,
`α₀` and `α₁` are bijective and `α₂` is injective: `α₀` is moreover injective by
`IsProP.dualityMap0_injective`. -/
theorem IsProP.dualityMap0_bijective_dualityMap1_bijective_dualityMap2_injective :
    Function.Bijective (dualityMap0 G M N) ∧ Function.Bijective (dualityMap1 G M N) ∧
      Function.Injective (dualityMap2 G M N) :=
  have hd := hG.dualityMap0_surjective_dualityMap1_bijective_dualityMap2_injective N hN hH2 h M
    hM hMn
  ⟨⟨hG.dualityMap0_injective N hN hH2
    (fun A _ _ _ _ _ _ hA htrivA hAn ↦ (h A hA htrivA hAn).imp_right fun h ↦ h.1.1) M hM hMn,
    hd.1⟩, hd.2⟩

end Combined

end TauCeti
