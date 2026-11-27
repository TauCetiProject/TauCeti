/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# A ring acting faithfully on a finitely generated module

Let `M` be a finitely generated module over a semiring `A`, and let a semiring `Γ` act faithfully
on `M` by `A`-linear maps, for instance `Γ = Module.End A M` acting by evaluation. If
`m₁, …, mₖ` generate `M` over `A`, the map `γ ↦ (γ • m₁, …, γ • mₖ)` embeds `Γ` into `Mᵏ` as a
`Γ`-module (`TauCeti.exists_injective_pi_of_faithfulSMul`): an element of `Γ` killing the
generators kills `M`, since it acts `A`-linearly.

## Main results

* `TauCeti.exists_injective_pi_of_faithfulSMul`: a semiring acting faithfully and `A`-linearly on
  a finitely generated `A`-module `M` embeds into a finite power of `M`.
-/

public section

namespace TauCeti

variable (A Γ M : Type*) [Semiring A] [Semiring Γ] [AddCommMonoid M] [Module A M] [Module Γ M]
  [SMulCommClass Γ A M] [FaithfulSMul Γ M] [Module.Finite A M]

include A in
/-- **A ring acting faithfully on a finitely generated module embeds into a finite power of it.**
If `Γ` acts faithfully and `A`-linearly on a finitely generated `A`-module `M`, then `Γ` embeds
into some `Mᵏ` as a `Γ`-module, by `γ ↦ (γ • m₁, …, γ • mₖ)` for generators `mᵢ` of `M`. -/
theorem exists_injective_pi_of_faithfulSMul :
    ∃ (k : ℕ) (f : Γ →ₗ[Γ] (Fin k → M)), Function.Injective f := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  refine ⟨k, LinearMap.pi fun i ↦ LinearMap.toSpanSingleton Γ M (s i), fun γ γ' h ↦ ?_⟩
  -- The `A`-linear maps `γ • ·` and `γ' • ·` agree on the generators `s i`.
  let φ := DistribSMul.toLinearMap A M (S := Γ)
  have h' : φ γ = φ γ' := LinearMap.ext_on_range hs fun i ↦ by simpa [φ] using congrFun h i
  exact FaithfulSMul.eq_of_smul_eq_smul fun m ↦ LinearMap.congr_fun h' m

end TauCeti
