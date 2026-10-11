/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Teichmuller
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# The `(p, [ϖ])`-adic topology depends only on the radical of `(ϖ)`

Let `R` be a commutative ring and `ϖ, ϖ' : R`. If `ϖ` and `ϖ'` generate ideals with the same
radical, that is, each divides a power of the other, then the Teichmüller representatives `[ϖ]` and
`[ϖ']` divide powers of each other in `𝕎 R`. The ideals `(p, [ϖ])` and `(p, [ϖ'])` of `𝕎 R` then
have the same radical, so they define the same adic topology. For the ring of integers `𝒪_F` of a
nonarchimedean field `F`, any two pseudouniformisers satisfy this hypothesis, so the topology of
`A_inf = W(𝒪_F)` does not depend on the choice of pseudouniformiser.

## Main results

* `WittVector.teichmuller_mem_radical_span_singleton` : `[ϖ]` lies in the radical of `([ϖ'])`
  when `ϖ` lies in the radical of `(ϖ')`.
* `WittVector.radical_span_p_teichmuller_eq` : `(p, [ϖ])` and `(p, [ϖ'])` have the same radical
  when `(ϖ)` and `(ϖ')` do.
* `TauCeti.WittVector.isAdic_span_p_teichmuller_iff` : a topology on `𝕎 R` is `(p, [ϖ])`-adic
  exactly when it is `(p, [ϖ'])`-adic.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017, §3.1.
-/

public section

namespace WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] {ϖ ϖ' : R}

/-- If `ϖ` lies in the radical of `(ϖ')`, then `[ϖ]` lies in the radical of `([ϖ'])`:
`ϖ' ∣ ϖ ^ n` gives `[ϖ'] ∣ [ϖ] ^ n`. -/
theorem teichmuller_mem_radical_span_singleton (h : ϖ ∈ (Ideal.span {ϖ'}).radical) :
    teichmuller p ϖ ∈ (Ideal.span {teichmuller p ϖ'}).radical := by
  obtain ⟨n, hn⟩ := h
  rw [Ideal.mem_span_singleton] at hn
  exact ⟨n, Ideal.mem_span_singleton.mpr (map_pow (teichmuller p) ϖ n ▸ map_dvd _ hn)⟩

/-- If `ϖ` lies in the radical of `(ϖ')`, then `(p, [ϖ])` lies in the radical of `(p, [ϖ'])`. -/
private theorem span_p_teichmuller_le_radical (h : ϖ ∈ (Ideal.span {ϖ'}).radical) :
    Ideal.span {(p : WittVector p R), teichmuller p ϖ} ≤
      (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}).radical := by
  rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨Ideal.le_radical (Ideal.subset_span (by simp)),
    Ideal.radical_mono (Ideal.span_mono (by simp)) (teichmuller_mem_radical_span_singleton h)⟩

/-- **The radical of `(p, [ϖ])` depends only on the radical of `(ϖ)`.** If `ϖ` and `ϖ'` generate
ideals of `R` with the same radical, then `(p, [ϖ])` and `(p, [ϖ'])` have the same radical
in `𝕎 R`. -/
theorem radical_span_p_teichmuller_eq (h : (Ideal.span {ϖ}).radical = (Ideal.span {ϖ'}).radical) :
    (Ideal.span {(p : WittVector p R), teichmuller p ϖ}).radical =
      (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}).radical :=
  le_antisymm
    (Ideal.radical_le_radical_iff.mpr <| span_p_teichmuller_le_radical <|
      h.le <| Ideal.le_radical <| Ideal.mem_span_singleton_self ϖ)
    (Ideal.radical_le_radical_iff.mpr <| span_p_teichmuller_le_radical <|
      h.ge <| Ideal.le_radical <| Ideal.mem_span_singleton_self ϖ')

end WittVector

namespace TauCeti.WittVector

open _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [TopologicalSpace (WittVector p R)]
  {ϖ ϖ' : R}

/-- **The `(p, [ϖ])`-adic topology depends only on the radical of `(ϖ)`.** If `ϖ` and `ϖ'`
generate ideals of `R` with the same radical, then a topology on `𝕎 R` is the `(p, [ϖ])`-adic one
exactly when it is the `(p, [ϖ'])`-adic one. -/
theorem isAdic_span_p_teichmuller_iff
    (h : (Ideal.span {ϖ}).radical = (Ideal.span {ϖ'}).radical) :
    IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}) ↔
      IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}) :=
  ⟨fun hI ↦ IsAdic.of_radical_eq hI (Submodule.fg_span (by simp)) (Submodule.fg_span (by simp))
      (radical_span_p_teichmuller_eq h),
    fun hI ↦ IsAdic.of_radical_eq hI (Submodule.fg_span (by simp)) (Submodule.fg_span (by simp))
      (radical_span_p_teichmuller_eq h.symm)⟩

end TauCeti.WittVector
