/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.QuantumDimension
public import TauCeti.RingTheory.TraceFunctional.Radical

/-!
# Trace radicals in the Temperley–Lieb tower

For an unnormalized Markov trace, strand inclusion pulls back the later trace radical
exactly to the earlier one. Consequently it induces injective algebra maps between the
trace-radical quotients. This is purely algebraic: no positivity or invertibility of the
loop parameter is required.

The Jones–Wenzl projection belongs to the trace radical precisely when its quantum
dimension vanishes, provided the quantum integers used in its construction are units.
These are the negligible projections killed in the positive Jones quotients.

The radical and quotient trace are the general constructions `LinearMap.traceRadical`
and `LinearMap.quotientTrace`; this file supplies their tower-specific properties.
The strand maps here start at one strand, as does `TemperleyLieb.strandIncl`.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.3–4.5.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
-/

public section

namespace TauCeti.TemperleyLieb.IsMarkovTrace

variable {R : Type*} [CommRing R] {δ : R}
  {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  (htr : IsMarkovTrace R δ tr)

/-- Strand inclusion pulls back the trace radical exactly, even at zero loop parameter. -/
@[simp]
theorem comap_traceRadical_strandIncl (n : ℕ) :
    Ideal.comap (strandIncl (R := R) (δ := δ) (n := n))
      ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2))) =
        (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1)) := by
  ext x
  simp only [Ideal.mem_comap, LinearMap.mem_traceRadical]
  constructor
  · intro hx y
    have hz := hx (strandIncl y * e δ (Fin.last n))
    simpa only [← mul_assoc, ← map_mul, htr.map_strandIncl_mul_e_last] using hz
  · intro hx
    let f := tr (n + 2) ∘ₗ LinearMap.mulLeft R (strandIncl x)
    have hf : f = 0 := by
      refine LinearMap.ext_on (span_strandIncl_union_strandIncl_mul_e_last_mul_eq_top n) ?_
      rintro _ (⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
      · simp only [f, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply]
        rw [← map_mul, htr.map_strandIncl, hx a, mul_zero]
      · simp only [f, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply]
        rw [← mul_assoc, ← mul_assoc, ← map_mul,
          htr.map_strandIncl_mul_e_last_mul, mul_assoc, hx (a * b)]
    exact fun y ↦ LinearMap.congr_fun hf y

/-- Strand inclusion preserves and reflects trace-radical membership. -/
theorem strandIncl_mem_traceRadical_iff {n : ℕ} (x : TemperleyLieb R δ (n + 1)) :
    strandIncl x ∈ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)) ↔
      x ∈ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1)) := by
  rw [← Ideal.mem_comap, htr.comap_traceRadical_strandIncl]

/-- The strand map on the quotients by the multiplication-pairing radicals.
These are algebraic quotients; no norm or star structure is asserted here. -/
def quotientStrandIncl (n : ℕ) :
    TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1)) →ₐ[R]
      TemperleyLieb R δ (n + 2) ⧸ (tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)) :=
  Ideal.quotientMapₐ _ strandIncl (htr.comap_traceRadical_strandIncl n).ge

/-- The induced strand map is computed by including any representative. -/
@[simp]
theorem quotientStrandIncl_mk (n : ℕ) (x : TemperleyLieb R δ (n + 1)) :
    htr.quotientStrandIncl n
      (Ideal.Quotient.mk ((tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) x) =
        Ideal.Quotient.mk ((tr (n + 2)).traceRadical (htr.map_mul_comm (n + 2)))
          (strandIncl x) := by
  exact Ideal.quotient_map_mkₐ _ _ _

/-- All strand maps between trace-radical quotients are injective. -/
theorem quotientStrandIncl_injective (n : ℕ) :
    Function.Injective (htr.quotientStrandIncl n) :=
  Ideal.quotientMap_injective' (H := (htr.comap_traceRadical_strandIncl n).ge)
    (htr.comap_traceRadical_strandIncl n).le

/-- The quotient traces retain the unnormalized strand-inclusion factor `δ`. -/
@[simp]
theorem quotientTrace_quotientStrandIncl (n : ℕ)
    (x : TemperleyLieb R δ (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    (tr (n + 2)).quotientTrace (htr.map_mul_comm (n + 2)) (htr.quotientStrandIncl n x) =
      δ * (tr (n + 1)).quotientTrace (htr.map_mul_comm (n + 1)) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [htr.quotientStrandIncl_mk, LinearMap.quotientTrace_mk, htr.map_strandIncl]

/-- A Jones–Wenzl projection is negligible exactly when its next quantum integer vanishes.
No invertibility assumption is imposed on that next quantum integer. -/
theorem jonesWenzl_mem_traceRadical_iff {n : ℕ}
    (h : ∀ k ∈ Finset.Icc 1 n, IsUnit (qInt R δ k)) :
    jonesWenzl δ n ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔
      qInt R δ (n + 1) = 0 := by
  rw [LinearMap.mem_traceRadical]
  constructor
  · intro hf
    have hz := hf 1
    simpa only [mul_one, htr.map_jonesWenzl n h] using hz
  · intro hz y
    rw [jonesWenzl_mul h, map_smul, htr.map_jonesWenzl n h, hz, smul_zero]

end TauCeti.TemperleyLieb.IsMarkovTrace
