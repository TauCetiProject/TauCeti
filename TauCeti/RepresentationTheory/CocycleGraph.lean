/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span

/-!
# Equivariant graph submodules for cocycles obeying linear relations

Let `O` be a Noetherian commutative ring, `G` a monoid, `A` a finite `O`-algebra, `M` an
`O`-module annihilated by an element `a : O`, `u : G →* A` a monoid homomorphism, and
`ρ : G →* Module.End O M` an `O`-linear representation.

Suppose `c : G → M` is a `1`-cocycle (`c (g * h) = c g + ρ g (c h)`) that obeys every `O`-linear
relation among the elements `u g - 1` (`∑ θ g • (u g - 1) = 0 → ∑ θ g • c g = 0`). By the
Artin–Rees lemma applied to the principal ideal `(a)` and the span of the `u g - 1` inside `A`,
there exist `k : ℕ` and a `G`-invariant `O`-submodule `Y ≤ A × M` (where `g` acts by left
multiplication by `u g` on `A` and by `ρ g` on `M`) such that `Y` is the graph of a partial
linear map (its first projection is injective) and `(u g - 1 + a ^ k • v, c g) ∈ Y` for all
`g : G` and `v : A` (`TauCeti.exists_graph_submodule_of_cocycle`).

## Main definitions and results

* `TauCeti.cocycleRelSubmodule`: the `O`-submodule of `1`-cocycles `G → M` for `ρ` that obey all
  `O`-linear relations among the elements `u g - 1`.
* `TauCeti.exists_graph_submodule_of_cocycle`: Artin–Rees extension of a cocycle in
  `cocycleRelSubmodule` to an equivariant graph submodule `Y ≤ A × M` containing
  `(u g - 1 + a ^ k • v, c g)`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/New/Congruences/LocalLoss/Basic.lean`
(`New.Selmer.ribetCocyclesIn`, `New.Selmer.ribetCocycles.exists_graph_subrepresentation`).
-/

public section

namespace TauCeti

open Finsupp LinearMap Submodule
open scoped Pointwise

variable {O G A M : Type*} [CommRing O] [Monoid G] [Ring A] [Algebra O A]
  [AddCommGroup M] [Module O M]

/-- The `O`-submodule of `1`-cocycles `c : G → M` for `ρ : G →* Module.End O M` that obey every
`O`-linear relation among the elements `u g - 1` (`g : G`). -/
def cocycleRelSubmodule (u : G →* A) (ρ : G →* Module.End O M) : Submodule O (G → M) where
  carrier := {c : G → M | (∀ g h : G, c (g * h) = c g + ρ g (c h)) ∧
    ∀ θ : G →₀ O, linearCombination O (fun g : G ↦ u g - 1) θ = 0 →
      linearCombination O c θ = 0}
  zero_mem' := ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩
  add_mem' {c₁ c₂} h₁ h₂ :=
    ⟨fun g h ↦ by simp [h₁.left g h, h₂.left g h, add_add_add_comm],
      fun θ hθ ↦ by
        have e₁ : ∑ x ∈ θ.support, θ x • c₁ x = 0 := h₁.right θ hθ
        have e₂ : ∑ x ∈ θ.support, θ x • c₂ x = 0 := h₂.right θ hθ
        change ∑ x ∈ θ.support, θ x • (c₁ x + c₂ x) = 0
        simp [smul_add, Finset.sum_add_distrib, e₁, e₂]⟩
  smul_mem' s {c} hc :=
    ⟨fun g h ↦ by simp [hc.left g h, smul_add],
      fun θ hθ ↦ by
        have e : ∑ x ∈ θ.support, θ x • c x = 0 := hc.right θ hθ
        change ∑ x ∈ θ.support, θ x • (s • c x) = 0
        simp [smul_comm _ s, ← Finset.smul_sum, e]⟩

/-- For a Noetherian ring `O`, a finitely generated `O`-algebra `A`, and an `O`-module `M`
annihilated by `a : O`, every cocycle `c ∈ cocycleRelSubmodule u ρ` extends via Artin–Rees to a
`G`-invariant `O`-submodule `Y ≤ A × M` whose first projection is injective and which contains
`(u g - 1 + a ^ k • v, c g)` for all `g : G` and `v : A`. -/
theorem exists_graph_submodule_of_cocycle [IsNoetherianRing O] [Module.Finite O A]
    (u : G →* A) (ρ : G →* Module.End O M) {a : O} (ha : ∀ m : M, a • m = 0)
    {c : G → M} (hc : c ∈ cocycleRelSubmodule u ρ) :
    ∃ (k : ℕ) (Y : Submodule O (A × M)),
      (∀ (g : G) (y : A × M), y ∈ Y → (u g * y.fst, ρ g y.snd) ∈ Y) ∧
      (∀ y ∈ Y, y.fst = 0 → y.snd = 0) ∧
      ∀ (g : G) (v : A), (u g - 1 + a ^ k • v, c g) ∈ Y := by
  let L : (G →₀ O) →ₗ[O] A := linearCombination O fun g ↦ u g - 1
  let C : (G →₀ O) →ₗ[O] M := linearCombination O c
  obtain ⟨h_coc, h_ker : ∀ θ : G →₀ O, L θ = 0 → C θ = 0⟩ := hc
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ n ≥ k,
      a ^ n • (⊤ : Submodule O A) ⊓ LinearMap.range L =
        a ^ (n - k) • (a ^ k • (⊤ : Submodule O A) ⊓ LinearMap.range L) := by
    simpa only [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] using
      (Ideal.span {a}).exists_pow_inf_eq_pow_smul (LinearMap.range L)
  let N : (G →₀ O) × A →ₗ[O] A × M := (L.prod C).coprod (a ^ (k + 1) • inl O A M)
  let shift (g : G) : Module.End O ((G →₀ O) × A) :=
    prodMap (Finsupp.lsum O fun h ↦ Finsupp.lsingle (g * h) - Finsupp.lsingle g)
      (LinearMap.mulLeft O (u g))
  have h_shift (g : G) (z : (G →₀ O) × A) :
      (u g * (N z).fst, ρ g (N z).snd) = N (shift g z) := by
    let act : Module.End O (A × M) := prodMap (LinearMap.mulLeft O (u g)) (ρ g)
    change (act ∘ₗ N) z = (N ∘ₗ shift g) z
    refine LinearMap.congr_fun ?_ z
    ext <;> simp [act, N, L, C, shift, h_coc, mul_sub]
  refine ⟨k + 1, LinearMap.range N, ?_, ?_, fun g v ↦ ⟨(Finsupp.single g 1, v), by simp [N, L, C]⟩⟩
  · rintro g _ ⟨z, rfl⟩
    exact ⟨shift g z, (h_shift g z).symm⟩
  · rintro _ ⟨⟨θ, v⟩, rfl⟩ (h_fst : (N (θ, v)).fst = 0)
    have hv : L θ = a ^ (k + 1) • -v := by simpa [N, add_eq_zero_iff_eq_neg] using h_fst
    have h_mem : L θ ∈ a ^ (k + 1) • (⊤ : Submodule O A) ⊓ LinearMap.range L :=
      ⟨⟨-v, Submodule.mem_top, hv.symm⟩, LinearMap.mem_range_self L θ⟩
    rw [hk (k + 1) k.le_succ] at h_mem
    obtain ⟨w, ⟨-, η, hw : L η = w⟩, hη : a ^ (k + 1 - k) • w = L θ⟩ := h_mem
    have h_snd : C θ = 0 := by simpa [ha (C η)] using h_ker (a • η - θ) (by simp [← hη, hw])
    simpa [N] using h_snd

end TauCeti
