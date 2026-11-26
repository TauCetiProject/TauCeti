/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.ColengthDvd
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import TauCeti.RingTheory.Length.Determinant

/-!
# Colength bounds and lengths

Over a noetherian domain `O` of Krull dimension at most one, for instance a discrete valuation
ring, a colength bound `M ⊸_z N` (`Submodule.ColengthDvd M N z`) with `z ≠ 0` and `M` finitely
generated bounds the length of `M / (M ∩ N)` by the length of `O / (z)`.

For generators `Φ₁, …, Φₙ` of `M`, the matrix `m` given by the hypothesis carries them into `N`,
so `M / (M ∩ N)` is a quotient of the cokernel of the transpose of `m` on `Oⁿ`. That cokernel has
length `ord_O (det m)` (`Matrix.length_quotient_range_mulVecLin_eq_ord_det`), which is at most
`ord_O z = length (O / (z))` since `det m ∣ z`.

## Main results

* `Submodule.ColengthDvd.length_quotient_le`: `length (M / (M ∩ N)) ≤ length (O / (z))`.
* `Module.End.IsOntoUpToColength.exists_length_quotient_le`: for an endomorphism `y` onto `M` modulo
  `p ^ n` up to colength `c`, the length of `M / (y (M) + p ^ n M)` is at most `l` times the length
  of `O / (p)` for some natural number `l ≤ c`.

## References

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC) at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
`grh/src/New/Reduction/Lattices/Colength.lean` (`New.ColengthDvd.relLength_le`,
`New.IsOntoUpToColength.exists_relLength_le`), stated there over a discrete valuation ring and
proved through the Smith normal form.
-/

public section

open Matrix Pointwise

namespace Submodule

variable {O V : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Ring.KrullDimLE 1 O]
  [AddCommGroup V] [Module O V] {M N : Submodule O V} {z : O}

/-- **A colength bound bounds a length.** Over a noetherian domain of dimension at most one, for
instance a discrete valuation ring, let `M` be finitely generated and let the colength of `N` in
`M` divide `z ≠ 0` (`N ≤ M` is not assumed). Then `M / (M ∩ N)` has length at most that of
`O / (z)`. -/
theorem ColengthDvd.length_quotient_le (hMN : ColengthDvd M N z) (hM : M.FG) (hz : z ≠ 0) :
    Module.length O (M ⧸ N.comap M.subtype) ≤ Module.length O (O ⧸ Ideal.span {z}) := by
  obtain ⟨n, Φ, rfl⟩ := fg_iff_exists_fin_generating_family.1 hM
  obtain ⟨m, hm_det, hm_mem⟩ := colengthDvd_iff.1 hMN n Φ fun i ↦ subset_span ⟨i, rfl⟩
  have hdet : mᵀ.det ≠ 0 := by
    rw [det_transpose]
    rintro h
    exact hz (zero_dvd_iff.1 (h ▸ hm_det))
  -- the linear combinations of the generators, followed by the quotient map
  let comb : (Fin n → O) →ₗ[O] span O (Set.range Φ) :=
    (Fintype.linearCombination O Φ).codRestrict _ fun v ↦ by
      rw [Fintype.linearCombination_apply]
      exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span ⟨i, rfl⟩)
  have hcomb : Function.Surjective comb := by
    rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := (Fintype.range_linearCombination O Φ ▸ hx : x ∈ LinearMap.range _)
    exact ⟨v, rfl⟩
  let π := (N.comap (span O (Set.range Φ)).subtype).mkQ ∘ₗ comb
  -- the rows of `m` are sent into `N`
  have hker : LinearMap.range mᵀ.mulVecLin ≤ LinearMap.ker π := by
    rintro _ ⟨v, rfl⟩
    have : ∑ k, (v ᵥ* m) k • Φ k = ∑ i, v i • ∑ k, m i k • Φ k := by
      simp only [vecMul, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    simpa [π, comb, Fintype.linearCombination_apply, this] using
      sum_mem fun i _ ↦ N.smul_mem (v i) (hm_mem i)
  have hπ : Function.Surjective ((LinearMap.range mᵀ.mulVecLin).liftQ π hker) := by
    rw [← LinearMap.range_eq_top, range_liftQ, LinearMap.range_eq_top]
    exact (mkQ_surjective _).comp hcomb
  calc Module.length O (span O (Set.range Φ) ⧸ N.comap (span O (Set.range Φ)).subtype)
      ≤ Module.length O ((Fin n → O) ⧸ LinearMap.range mᵀ.mulVecLin) :=
        Module.length_le_of_surjective _ hπ
    _ = Ring.ord O m.det := by
        rw [length_quotient_range_mulVecLin_eq_ord_det _ hdet, det_transpose]
    _ ≤ Ring.ord O z := Ring.ord_le_ord_of_dvd hm_det
    _ = Module.length O (O ⧸ Ideal.span {z}) := by rw [Ring.ord]

/-- Over a noetherian domain of dimension at most one, for instance a discrete valuation ring, let
`M` be finitely generated, `p ≠ 0`, and let the endomorphism `y` be onto `M` modulo `p ^ n` up to
colength `c`. Then for some natural number `l ≤ c` the length of `M / (y (M) + p ^ n M)` is at
most `l` times the length of `O / (p)`. -/
theorem _root_.Module.End.IsOntoUpToColength.exists_length_quotient_le {p : O} {n : ℕ}
    {y : Module.End O V} {c : ℝ} (h_onto : y.IsOntoUpToColength M p n c) (hM : M.FG) (hp : p ≠ 0) :
    ∃ l : ℕ, l ≤ c ∧ Module.length O (M ⧸ (M.map y ⊔ p ^ n • M).comap M.subtype) ≤
      l * Module.length O (O ⧸ Ideal.span {p}) := by
  obtain ⟨-, l, hl, hl_dvd⟩ := Module.End.isOntoUpToColength_iff.1 h_onto
  refine ⟨l, hl, (hl_dvd.length_quotient_le hM (pow_ne_zero l hp)).trans_eq ?_⟩
  rw [← Ring.ord, Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hp), nsmul_eq_mul, Ring.ord]

end Submodule
