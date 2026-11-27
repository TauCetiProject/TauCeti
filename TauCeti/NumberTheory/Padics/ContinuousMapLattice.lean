/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Module
public import TauCeti.Topology.Algebra.Module.ContinuousMapLocalization

/-!
# Continuous maps from a compact space into `V` land in a lattice

Let `V` be a topological `ℚ_p`-vector space and `T ⊆ V` an open `ℤ_p`-submodule, for instance the
`ℤ_p`-span of a basis of a finite-dimensional Hausdorff `V`. Then `T` absorbs `V`: `pⁿ • v ∈ T`
for `n` large, since `pⁿ → 0` in `ℚ_p`. For a compact space `X`, every continuous `f : X → V`
lands in `p^{-n} T` for a single `n`, so `C(X, V) = ⋃ₙ C(X, p^{-n} T)`, and the inclusion
`C(X, T) → C(X, V)` identifies `C(X, V)` with `ℚ_p ⊗[ℤ_p] C(X, T)`. With `X = Gⁱ` this is the
equality `Cⁱ(G, V) = Cⁱ(G, T) ⊗ ℚ_p` of continuous cochains for a finite free `ℤ_p`-module `T` and
`V = T ⊗ ℚ_p` (Rubin, *Euler Systems*, Appendix B, §2, Proposition 2.4, printed p. 152).

## Main results

* `TauCeti.exists_padicInt_pow_smul_mem`: an open `ℤ_p`-submodule absorbs `V`.
* `TauCeti.exists_padicInt_pow_smul_apply_mem_of_compactSpace`: a continuous map from a compact
  space lands in `p^{-n} T` for one `n`.
* `TauCeti.isBaseChange_padic_compLeftContinuous_subtypeL`:
  `C(X, V) = ℚ_p ⊗[ℤ_p] C(X, T)`.

The `ℤ_p`-span of a `ℚ_p`-basis of a finite-dimensional Hausdorff `V` is open
(`Module.Basis.isOpen_span_padicInt`), so the results apply to it.
-/

public section

open Filter Topology

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
  [IsScalarTower ℤ_[p] ℚ_[p] V] [TopologicalSpace V] [ContinuousSMul ℚ_[p] V]

/-- An open `ℤ_[p]`-submodule `T` of a topological `ℚ_[p]`-module absorbs every vector:
`pⁿ • v ∈ T` for some `n`. -/
theorem exists_padicInt_pow_smul_mem {T : Submodule ℤ_[p] V} (hT : IsOpen (T : Set V)) (v : V) :
    ∃ n : ℕ, (p : ℤ_[p]) ^ n • v ∈ T := by
  have h : Tendsto (fun n : ℕ ↦ (p : ℚ_[p]) ^ n • v) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (Padic.norm_p_lt_one (p := p))).smul_const v
  obtain ⟨n, hn⟩ := (h.eventually (hT.mem_nhds T.zero_mem)).exists
  exact ⟨n, by simpa [← algebraMap_smul ℚ_[p]] using hn⟩

/-- `exists_padicInt_pow_smul_mem` in the form taken by the localization lemmas: an open
`ℤ_[p]`-submodule absorbs `V` along the powers of `p`. -/
private theorem exists_mem_powers_smul_mem {T : Submodule ℤ_[p] V} (hT : IsOpen (T : Set V))
    (v : V) : ∃ s ∈ Submonoid.powers (p : ℤ_[p]), s • v ∈ T :=
  let ⟨n, hn⟩ := exists_padicInt_pow_smul_mem hT v
  ⟨_, ⟨n, rfl⟩, hn⟩

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A continuous map from a compact space into a topological `ℚ_[p]`-module `V` lands in
`p^{-n} T` for a single `n`, for every open `ℤ_[p]`-submodule `T` of `V`. -/
theorem exists_padicInt_pow_smul_apply_mem_of_compactSpace {T : Submodule ℤ_[p] V}
    (hT : IsOpen (T : Set V)) (f : C(X, V)) : ∃ n : ℕ, ∀ x, (p : ℤ_[p]) ^ n • f x ∈ T := by
  obtain ⟨s, ⟨n, rfl⟩, h⟩ := exists_smul_apply_mem_of_compactSpace (Submonoid.powers (p : ℤ_[p]))
    T hT (exists_mem_powers_smul_mem hT) f
  exact ⟨n, h⟩

/-- For an open `ℤ_[p]`-submodule `T` of a topological `ℚ_[p]`-vector space `V` and a compact
space `X`, the inclusion `C(X, T) → C(X, V)` identifies `C(X, V)` with `ℚ_[p] ⊗[ℤ_[p]] C(X, T)`. -/
theorem isBaseChange_padic_compLeftContinuous_subtypeL [IsTopologicalAddGroup V]
    {T : Submodule ℤ_[p] V} (hT : IsOpen (T : Set V)) :
    IsBaseChange ℚ_[p] (T.subtypeL.compLeftContinuous ℤ_[p] X : C(X, T) →ₗ[ℤ_[p]] C(X, V)) := by
  have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine isBaseChange_compLeftContinuous_subtypeL (nonZeroDivisors ℤ_[p]) T ℚ_[p] hT fun v ↦ ?_
  obtain ⟨s, hs, h⟩ := exists_mem_powers_smul_mem hT v
  exact ⟨s, powers_le_nonZeroDivisors_of_noZeroDivisors hp hs, h⟩

end TauCeti
