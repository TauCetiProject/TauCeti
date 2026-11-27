/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Discriminant.Stickelberger
import TauCeti.NumberTheory.NumberField.Quadratic.PeriodAlgebra
import TauCeti.NumberTheory.QuadraticOrder.Reduction

/-!
# Unit congruences in imaginary quadratic fields

Let `K` be an imaginary quadratic field (`[IsTotallyComplex K]`, `finrank ℚ K = 2`) of
discriminant `D = discr K < 0`. Transporting `QuadraticAlgebra.ker_unitsMap_quotient_span_natCast`
along the period-algebra presentation `exists_ringOfIntegers_periodAlgEquiv` shows that the kernel
of `(𝓞 K)ˣ →* (𝓞 K ⧸ (N))ˣ` is `⊤` at `N = 1`, `Subgroup.zpowers (-1)` at `N = 2`, and `⊥` for
`3 ≤ N` (`ker_unitsMap_ringOfIntegers_quotient_span_natCast`), uniformly for all imaginary
quadratic fields including `D = -4` and `D = -3`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section

open Module NumberField Polynomial
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K]

/-- Transport of `QuadraticAlgebra.ker_unitsMap_quotient_span_natCast` along a `ℤ`-algebra
isomorphism `𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b` of negative discriminant. -/
private theorem ker_unitsMap_ringOfIntegers_quotient_span_natCast_of_algEquiv {a b : ℤ}
    (e : 𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b) (hd : QuadraticAlgebra.discr a b < 0)
    {N : ℕ} (hN : N ≠ 0) :
    (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) :
        𝓞 K →* 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})).ker =
      if N = 1 then ⊤ else if N = 2 then Subgroup.zpowers (-1) else ⊥ := by
  have hker := QuadraticAlgebra.ker_unitsMap_quotient_span_natCast hd hN
  let A := QuadraticAlgebra ℤ a b
  let eu : (𝓞 K)ˣ ≃* Aˣ := Units.mapEquiv e.toRingEquiv.toMulEquiv
  have hcomap :
      (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) :
          𝓞 K →* 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})).ker =
        (Units.map (Ideal.Quotient.mk (Ideal.span {(N : A)}) :
          A →* A ⧸ Ideal.span {(N : A)})).ker.comap eu.toMonoidHom := by
    ext u
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, Units.ext_iff, Units.coe_map,
      MonoidHom.coe_ofClass, Units.val_one,
      ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨fun ⟨w, hw⟩ ↦ ⟨e w, by simpa [eu] using congrArg e hw⟩,
      fun ⟨w, hw⟩ ↦ ⟨e.symm w, by simpa [eu] using congrArg e.symm hw⟩⟩
  rw [hcomap, hker]
  split_ifs with h1 h2
  · exact Subgroup.comap_top _
  · have heu : eu (-1) = -1 := Units.ext (by simp [eu])
    ext u
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_zpowers_iff]
    refine ⟨fun ⟨k, hk⟩ ↦ ⟨k, eu.injective (by simpa [heu] using hk)⟩,
      fun ⟨k, hk⟩ ↦ ⟨k, by simpa [heu] using congrArg eu hk⟩⟩
  · exact MonoidHom.ker_eq_bot_iff _ |>.mpr eu.injective

/-- **Kernel of `(𝓞 K)ˣ →* (𝓞 K ⧸ (N))ˣ` in an imaginary quadratic field**: for `N ≠ 0`, the
units of `𝓞 K` congruent to `1` modulo `(N)` form `⊤` at `N = 1`, `Subgroup.zpowers (-1)` at
`N = 2`, and `⊥` for `3 ≤ N`. -/
theorem ker_unitsMap_ringOfIntegers_quotient_span_natCast [NumberField K] [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) {N : ℕ} (hN : N ≠ 0) :
    (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) :
        𝓞 K →* 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})).ker =
      if N = 1 then ⊤ else if N = 2 then Subgroup.zpowers (-1) else ⊥ := by
  obtain ⟨e⟩ := exists_ringOfIntegers_periodAlgEquiv hK
  exact ker_unitsMap_ringOfIntegers_quotient_span_natCast_of_algEquiv e
    ((discr_neg_periodCoeff (discr K) (discr_emod_four_eq_zero_or_one K)).symm ▸
      IsTotallyComplex.discr_lt_zero hK) hN

end TauCeti.NumberField
