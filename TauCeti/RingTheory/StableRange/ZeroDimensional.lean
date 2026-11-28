/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import TauCeti.RingTheory.StableRange
import TauCeti.RingTheory.KrullDimension.Zero

/-!
# Stable range one for zero-dimensional rings

`TauCeti.hasStableRangeLE_one_of_krullDimLE_zero` gives stable range one for every
zero-dimensional commutative ring, including non-Noetherian rings. It uses
`Ideal.span_singleton_sup_nilradical_colon_eq_top` to choose the coefficient that shortens
a unimodular pair.
-/

public section

namespace TauCeti

/-- A commutative ring of Krull dimension at most zero has Bass stable range at most one. -/
theorem hasStableRangeLE_one_of_krullDimLE_zero (R : Type*) [CommRing R]
    [Ring.KrullDimLE 0 R] : HasStableRangeLE R 1 := by
  refine hasStableRangeLE_one_iff.mpr fun a b x y hab ↦ ?_
  let J := (nilradical R).colon (Ideal.span {a})
  have hone : 1 ∈ Ideal.span {a} ⊔ J :=
    (Ideal.eq_top_iff_one _).mp (Ideal.span_singleton_sup_nilradical_colon_eq_top a)
  obtain ⟨u, hu, c, hc, huc⟩ := Submodule.mem_sup.mp hone
  refine ⟨c, by_contra fun hunit ↦ ?_⟩
  obtain ⟨P, hP, hac⟩ := exists_max_ideal_of_mem_nonunits hunit
  have hPrime := hP.isPrime
  have hca : c * a ∈ P := nilradical_le_prime P (Ideal.mem_colon_span_singleton.mp hc)
  have haP : a ∈ P := (hPrime.mem_or_mem hca).elim
    (fun hcP ↦ (P.add_mem_iff_left (P.mul_mem_left b hcP)).mp hac) id
  have huP : u ∈ P := (Ideal.span_singleton_le_iff_mem P).mpr haP hu
  have hcP : c ∉ P :=
    fun hcP ↦ hP.ne_top (P.eq_top_iff_one.mpr (huc ▸ P.add_mem huP hcP))
  have hbP : b ∈ P :=
    (hPrime.mem_or_mem ((P.add_mem_iff_right haP).mp hac)).resolve_right hcP
  exact hP.ne_top (P.eq_top_iff_one.mpr (hab ▸
    P.add_mem (P.mul_mem_right x haP) (P.mul_mem_right y hbP)))

end TauCeti
