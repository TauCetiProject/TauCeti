/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Kähler differentials of quotients of the dual numbers

Let `k` be a field in which `2 ≠ 0` and let `ψ : k[ε]/(ε²) → S` be a surjective `k`-algebra map.
The Kähler differentials `Ω[S⁄k]` are spanned by `d(ψ ε)`, and `2 ψ(ε) d(ψ ε) = d(ψ(ε²)) = 0`,
so `ψ ε` kills `Ω[S⁄k]`. In particular, when `ψ ε ≠ 0`, `Ω[S⁄k]` has no free quotient of nonzero
rank. Taking `ψ` to be the identity, this applies to `k[ε]/(ε²)` itself.

In characteristic `2` this fails: `a + bε ↦ b` is a derivation of `k[ε]/(ε²)`.

## Main results

* `TauCeti.DualNumber.map_eps_smul_kaehlerDifferential_eq_zero_of_surjective`: `ψ ε` kills
  `Ω[S⁄k]`.
* `TauCeti.DualNumber.not_surjective_kaehlerDifferential_to_pi_of_surjective`: if `ψ ε ≠ 0`, no
  `S`-linear map `Ω[S⁄k] → S^d` with `d ≠ 0` is surjective.
-/

public section

open KaehlerDifferential

namespace TauCeti.DualNumber

variable {k S : Type*} [Field k] [CommRing S] [Algebra k S]

/-- If `ψ : k[ε]/(ε²) → S` is a surjective `k`-algebra map and `2 ≠ 0` in `k`, then `ψ ε` kills
the Kähler differentials `Ω[S⁄k]`: they are spanned by `d(ψ ε)`, and `2 ψ(ε) d(ψ ε) = d(ψ ε²)`
vanishes. -/
theorem map_eps_smul_kaehlerDifferential_eq_zero_of_surjective (h2 : (2 : k) ≠ 0)
    (ψ : DualNumber k →ₐ[k] S) (hψ : Function.Surjective ψ) (ω : Ω[S⁄k]) :
    ψ DualNumber.eps • ω = 0 := by
  set e := ψ DualNumber.eps
  -- `e • d e = 0`: twice it is `d (e²) = 0`, and `2` is invertible.
  have hee : e • D k S e = 0 := by
    have h : (2 : k) • (e • D k S e) = 0 := by
      rw [two_smul, ← Derivation.leibniz, ← map_mul, DualNumber.eps_mul_eps, map_zero,
        Derivation.map_zero]
    simpa [h2] using h
  -- Every `d s` is a multiple of `d e`.
  have hspan : ∀ s : S, D k S s ∈ Submodule.span S {D k S e} := fun s ↦ by
    obtain ⟨a, rfl⟩ := hψ s
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a, DualNumber.inr_eq_smul_eps,
      ← TrivSqZeroExt.algebraMap_eq_inl]
    simpa using Submodule.smul_of_tower_mem _ a.snd (Submodule.mem_span_singleton_self _)
  have hω : ω ∈ Submodule.span S {D k S e} := by
    have := span_range_derivation k S ▸ Submodule.mem_top (x := ω)
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hspan) this
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hω
  rw [smul_comm, hee, smul_zero]

/-- If `ψ : k[ε]/(ε²) → S` is a surjective `k`-algebra map with `ψ ε ≠ 0` and `2 ≠ 0` in `k`, then
there is no surjective `S`-linear map `Ω[S⁄k] → S^d` with `d ≠ 0`. -/
theorem not_surjective_kaehlerDifferential_to_pi_of_surjective (h2 : (2 : k) ≠ 0)
    (ψ : DualNumber k →ₐ[k] S) (hψ : Function.Surjective ψ) (hε : ψ DualNumber.eps ≠ 0)
    {d : ℕ} (hd : d ≠ 0) (g : Ω[S⁄k] →ₗ[S] (Fin d → S)) : ¬ Function.Surjective g := by
  intro hg
  obtain ⟨ω, hω⟩ := hg fun _ ↦ 1
  have := congrFun (congrArg g
    (map_eps_smul_kaehlerDifferential_eq_zero_of_surjective h2 ψ hψ ω))
    ⟨0, Nat.pos_of_ne_zero hd⟩
  rw [map_smul, hω, map_zero] at this
  exact hε (by simpa using this)

end TauCeti.DualNumber
