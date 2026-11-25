/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Module.FiniteDimension
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
* `TauCeti.mem_span_range_basis_padicInt_iff`: the `ℤ_p`-span of a `ℚ_p`-basis is the set of
  vectors whose coordinates have norm at most `1`.
* `TauCeti.isOpen_span_range_basis_padicInt`: the `ℤ_p`-span of a `ℚ_p`-basis of a
  finite-dimensional Hausdorff topological vector space is open, so the results apply to it.
-/

public section

open Filter Topology

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
  [IsScalarTower ℤ_[p] ℚ_[p] V] [TopologicalSpace V] [ContinuousSMul ℚ_[p] V]

/-- `ℤ_[p]` acts continuously on a topological `ℚ_[p]`-module through `ℚ_[p]`. -/
instance instContinuousConstSMulPadicInt : ContinuousConstSMul ℤ_[p] V where
  continuous_const_smul c := by
    simpa only [algebraMap_smul] using
      (continuous_const_smul (algebraMap ℤ_[p] ℚ_[p] c) : Continuous fun v : V ↦ _)

/-- An open `ℤ_[p]`-submodule `T` of a topological `ℚ_[p]`-module absorbs every vector:
`pⁿ • v ∈ T` for some `n`. -/
theorem exists_padicInt_pow_smul_mem {T : Submodule ℤ_[p] V} (hT : IsOpen (T : Set V)) (v : V) :
    ∃ n : ℕ, (p : ℤ_[p]) ^ n • v ∈ T := by
  have h : Tendsto (fun n : ℕ ↦ (p : ℚ_[p]) ^ n • v) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (Padic.norm_p_lt_one (p := p))).smul_const v
  obtain ⟨n, hn⟩ := (h.eventually (hT.mem_nhds T.zero_mem)).exists
  exact ⟨n, by simpa [← algebraMap_smul ℚ_[p]] using hn⟩

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- A continuous map from a compact space into a topological `ℚ_[p]`-module `V` lands in
`p^{-n} T` for a single `n`, for every open `ℤ_[p]`-submodule `T` of `V`. -/
theorem exists_padicInt_pow_smul_apply_mem_of_compactSpace {T : Submodule ℤ_[p] V}
    (hT : IsOpen (T : Set V)) (f : C(X, V)) : ∃ n : ℕ, ∀ x, (p : ℤ_[p]) ^ n • f x ∈ T := by
  obtain ⟨s, ⟨n, rfl⟩, h⟩ :=
    exists_smul_apply_mem_of_compactSpace (Submonoid.powers (p : ℤ_[p])) T hT
      (fun v ↦ let ⟨n, hn⟩ := exists_padicInt_pow_smul_mem hT v; ⟨_, ⟨n, rfl⟩, hn⟩) f
  exact ⟨n, h⟩

/-- For an open `ℤ_[p]`-submodule `T` of a topological `ℚ_[p]`-vector space `V` and a compact
space `X`, the inclusion `C(X, T) → C(X, V)` identifies `C(X, V)` with `ℚ_[p] ⊗[ℤ_[p]] C(X, T)`. -/
theorem isBaseChange_padic_compLeftContinuous_subtypeL [IsTopologicalAddGroup V]
    {T : Submodule ℤ_[p] V} (hT : IsOpen (T : Set V)) :
    IsBaseChange ℚ_[p] (T.subtypeL.compLeftContinuous ℤ_[p] X : C(X, T) →ₗ[ℤ_[p]] C(X, V)) :=
  isBaseChange_compLeftContinuous_subtypeL (nonZeroDivisors ℤ_[p]) T ℚ_[p] hT
    fun v ↦ let ⟨n, hn⟩ := exists_padicInt_pow_smul_mem hT v
      ⟨_, pow_mem (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
        n, hn⟩

omit [TopologicalSpace V] [ContinuousSMul ℚ_[p] V] in
/-- A vector lies in the `ℤ_[p]`-span of a `ℚ_[p]`-basis exactly when all its coordinates have
norm at most `1`. -/
theorem mem_span_range_basis_padicInt_iff {ι : Type*} (b : Module.Basis ι ℚ_[p] V) (v : V) :
    v ∈ Submodule.span ℤ_[p] (Set.range b) ↔ ∀ i, ‖b.repr v i‖ ≤ 1 := by
  rw [b.mem_span_iff_repr_mem ℤ_[p]]
  refine forall_congr' fun i ↦ ⟨?_, fun h ↦ ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨x, hx⟩
  exact hx ▸ x.norm_le_one

/-- The `ℤ_[p]`-span of a `ℚ_[p]`-basis of a finite-dimensional Hausdorff topological vector
space is open. -/
theorem isOpen_span_range_basis_padicInt [IsTopologicalAddGroup V] [T2Space V] {ι : Type*}
    [Finite ι] (b : Module.Basis ι ℚ_[p] V) :
    IsOpen (Submodule.span ℤ_[p] (Set.range b) : Set V) := by
  have := Module.Finite.of_basis b
  have h : (Submodule.span ℤ_[p] (Set.range b) : Set V) =
      ⋂ i, (b.coord i) ⁻¹' Metric.closedBall 0 1 := by
    ext v
    simp [mem_span_range_basis_padicInt_iff]
  rw [h]
  exact isOpen_iInter_of_finite fun i ↦
    (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).preimage
      (LinearMap.continuous_of_finiteDimensional _)

end TauCeti
