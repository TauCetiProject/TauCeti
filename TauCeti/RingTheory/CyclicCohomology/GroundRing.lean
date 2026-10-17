/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import Mathlib.Algebra.Regular.SMul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.BigOperators

/-!
# Cyclic cohomology of the ground ring

This file computes the cyclic cohomology `HCⁿ(R; M)` of a commutative ring `R`, viewed as an
algebra over itself, with coefficients in an `R`-module `M`: it vanishes in odd degrees, and in
even degrees it is `M` as soon as `2` acts injectively on `M`. In particular `HC²ᵏ(ℂ) ≅ ℂ` and
`HC²ᵏ⁺¹(ℂ) = 0`, the base case against which the periodicity operator, the pairings with K-theory
and the comparison with the `(b, B)` bicomplex are normalized.

Every `n`-cochain of `R` is the product cochain `(a₀, …, aₙ) ↦ (a₀ ⋯ aₙ) • z` with
`z = φ(1, …, 1)` (Mathlib's `MultilinearMap.mkPiRing`). Such a cochain is cyclic exactly when
`(-1)ⁿ • z = z`, and its Hochschild coboundary is `0` in even degree and the product cochain of
`z` in odd degree, because all `n + 2` faces of `(1, …, 1)` equal `(1, …, 1)`. Hence:

* in odd degree the only cyclic cocycle is `0`, so `HCⁿ(R; M) = 0` with no hypothesis on `M`;
* in even degree every cyclic cochain is a cocycle, and the coboundaries come from the odd cyclic
  cochains, whose values `z` satisfy `z = -z`. If `2` is a nonzerodivisor on `M` these vanish, and
  `[φ] ↦ φ(1, …, 1)` identifies `HCⁿ(R; M)` with `M`; the class of the product cochain
  `(a₀, …, aₙ) ↦ (a₀ ⋯ aₙ) • z` corresponds to `z`.

Without the hypothesis on `2` the identification fails: in positive even degree the coboundaries
are the product cochains of the `2`-torsion elements of `M`, so for instance `HCⁿ(ℤ/2; ℤ/2) = 0`
for every positive even `n`.

## Main definitions

* `TauCeti.mkPiRingCyclicCocycle`: in even degree, the product cochain of `z` as a cyclic cocycle.
* `TauCeti.cyclicCohomology.groundRingEquiv`: in even degree, `HCⁿ(R; M) ≃ₗ[R] M` when `2` is a
  nonzerodivisor on `M`.

## Main results

* `TauCeti.mkPiRing_mem_cyclicCochains_iff`: the product cochain of `z` is cyclic iff
  `(-1)ⁿ • z = z`.
* `TauCeti.hochschildCoboundary_mkPiRing`: the Hochschild coboundary of a product cochain.
* `TauCeti.cyclicCocycles_eq_bot_of_odd`, `TauCeti.cyclicCocycles_eq_top_of_even`: the cyclic
  cocycles of `R` in odd and even degree.
* `TauCeti.cyclicCoboundaries_eq_bot_of_even`: there are no nonzero even cyclic coboundaries.
* `TauCeti.cyclicCohomology.subsingleton_of_odd`: `HCⁿ(R; M) = 0` in odd degree.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.1.
-/

public section

noncomputable section

namespace TauCeti

open MultilinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/-! ### Product cochains -/

/-- The product cochain `(a₀, …, aₙ) ↦ (a₀ ⋯ aₙ) • z` is cyclic exactly when `(-1)ⁿ • z = z`. -/
theorem mkPiRing_mem_cyclicCochains_iff (z : M) :
    MultilinearMap.mkPiRing R (Fin (n + 1)) z ∈ cyclicCochains R R M n ↔
      (-1 : ℤ) ^ n • z = z := by
  rw [mem_cyclicCochains_iff]
  refine ⟨fun h ↦ by simpa using (h fun _ ↦ 1).symm, fun h a ↦ ?_⟩
  simp only [mkPiRing_apply, Function.comp_apply, Equiv.prod_comp, smul_comm ((-1 : ℤ) ^ n), h]

/-- The Hochschild coboundary of the product cochain of `z` is `0` in even degree and the product
cochain of `z` in odd degree. -/
theorem hochschildCoboundary_mkPiRing (z : M) :
    hochschildCoboundary R R M n (MultilinearMap.mkPiRing R (Fin (n + 1)) z) =
      MultilinearMap.mkPiRing R (Fin (n + 2)) (if Even n then 0 else z) := by
  rw [← mkPiRing_apply_one_eq_self (hochschildCoboundary R R M n _), mkPiRing_eq_iff,
    hochschildCoboundary_apply]
  simp only [hochschildFace_const_one, mkPiRing_apply, Finset.prod_const_one, one_smul]
  rw [← Finset.sum_smul, Fin.sum_neg_one_pow]
  by_cases hn : Even n <;> simp [hn, Nat.even_add]

/-- Every cochain of `R` is the product cochain of its value at `(1, …, 1)`. -/
private theorem exists_eq_mkPiRing (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) :
    ∃ z, φ = MultilinearMap.mkPiRing R (Fin (n + 1)) z :=
  ⟨_, (mkPiRing_apply_one_eq_self φ).symm⟩

/-- If `2` is a nonzerodivisor on `M`, every odd-degree cyclic cochain of `R` is `0`. -/
theorem cyclicCochains_eq_bot_of_odd (h2 : IsSMulRegular M (2 : R)) (hn : Odd n) :
    cyclicCochains R R M n = ⊥ := by
  refine eq_bot_iff.2 fun φ hφ ↦ ?_
  obtain ⟨z, rfl⟩ := exists_eq_mkPiRing φ
  rw [mkPiRing_mem_cyclicCochains_iff, hn.neg_one_pow, neg_one_smul] at hφ
  have hz : (2 : R) • z = (2 : R) • 0 := by
    rw [two_smul, smul_zero, ← neg_add_cancel z, hφ]
  rw [h2 hz, mkPiRing_zero]
  exact zero_mem _

/-! ### Cyclic cocycles and coboundaries -/

/-- In odd degree the only cyclic cocycle of `R` is `0`. -/
theorem cyclicCocycles_eq_bot_of_odd (hn : Odd n) : cyclicCocycles R R M n = ⊥ := by
  refine eq_bot_iff.2 fun φ hφ ↦ ?_
  rw [mem_cyclicCocycles_iff] at hφ
  obtain ⟨z, hz⟩ := exists_eq_mkPiRing (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M)
  simp only [hz, hochschildCoboundary_mkPiRing, Nat.not_even_iff_odd.2 hn, ↓reduceIte,
    mkPiRing_eq_zero_iff] at hφ
  rw [Submodule.mem_bot, ← Submodule.coe_eq_zero, hz, hφ, mkPiRing_zero]

/-- In even degree every cyclic cochain of `R` is a cocycle. -/
theorem cyclicCocycles_eq_top_of_even (hn : Even n) : cyclicCocycles R R M n = ⊤ := by
  refine eq_top_iff.2 fun φ _ ↦ ?_
  obtain ⟨z, hz⟩ := exists_eq_mkPiRing (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M)
  simp only [mem_cyclicCocycles_iff, hz, hochschildCoboundary_mkPiRing, hn, ↓reduceIte,
    mkPiRing_zero]

/-- If `2` is a nonzerodivisor on `M`, there are no nonzero even-degree cyclic coboundaries
of `R`. -/
theorem cyclicCoboundaries_eq_bot_of_even (h2 : IsSMulRegular M (2 : R)) (hn : Even n) :
    cyclicCoboundaries R R M n = ⊥ := by
  cases n with
  | zero => exact cyclicCoboundaries_zero R R M
  | succ n =>
    have hodd : Odd n := Nat.not_even_iff_odd.1 (Nat.even_add_one.1 hn)
    rw [cyclicCoboundaries_succ, LinearMap.range_eq_bot]
    ext φ : 1
    have hφ : φ = 0 :=
      Submodule.coe_eq_zero.1 ((Submodule.mem_bot R).1 (cyclicCochains_eq_bot_of_odd h2 hodd ▸ φ.2))
    rw [hφ, _root_.map_zero, LinearMap.zero_apply]

variable (R) in
/-- In even degree, the product cochain `(a₀, …, aₙ) ↦ (a₀ ⋯ aₙ) • z` as a cyclic cocycle of `R`. -/
def mkPiRingCyclicCocycle (hn : Even n) : M →ₗ[R] cyclicCocycles R R M n :=
  LinearMap.codRestrict _
    ((MultilinearMap.piRingEquiv (R := R) (M₂ := M) (ι := Fin (n + 1))).toLinearMap.codRestrict
      (cyclicCochains R R M n) fun z ↦
        (mkPiRing_mem_cyclicCochains_iff z).2 (by rw [hn.neg_one_pow, one_smul]))
    fun _ ↦ by rw [cyclicCocycles_eq_top_of_even hn]; exact Submodule.mem_top

/-- The underlying cochain of `mkPiRingCyclicCocycle` is the product cochain. -/
@[simp]
theorem coe_mkPiRingCyclicCocycle_apply (hn : Even n) (z : M) :
    (((mkPiRingCyclicCocycle R hn z : cyclicCocycles R R M n) : cyclicCochains R R M n) :
        MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) =
      MultilinearMap.mkPiRing R (Fin (n + 1)) z :=
  (rfl)

/-- In even degree, every cyclic cocycle of `R` is the product cochain of its value at
`(1, …, 1)`. -/
theorem mkPiRingCyclicCocycle_apply_one (hn : Even n) (φ : cyclicCocycles R R M n) :
    mkPiRingCyclicCocycle R hn ((φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) fun _ ↦ 1) =
      φ := by
  ext : 2
  exact mkPiRing_apply_one_eq_self _

/-! ### Cyclic cohomology -/

namespace cyclicCohomology

/-- The odd-degree cyclic cohomology of `R` vanishes. -/
theorem subsingleton_of_odd (hn : Odd n) : Subsingleton (cyclicCohomology R R M n) := by
  have : Subsingleton (cyclicCocycles R R M n) := by
    rw [cyclicCocycles_eq_bot_of_odd hn]
    infer_instance
  exact (mk_surjective R R M n).subsingleton

/-- If `2` is a nonzerodivisor on `M`, the even-degree cyclic cohomology `HCⁿ(R; M)` of `R` is
`M`: the class of the product cochain `(a₀, …, aₙ) ↦ (a₀ ⋯ aₙ) • z` corresponds to `z`, and
the class of a cocycle `φ` to `φ(1, …, 1)`. -/
def groundRingEquiv (h2 : IsSMulRegular M (2 : R)) (hn : Even n) :
    cyclicCohomology R R M n ≃ₗ[R] M :=
  (LinearEquiv.ofBijective (mk R R M n ∘ₗ mkPiRingCyclicCocycle R hn) ⟨by
    refine (injective_iff_map_eq_zero _).2 fun z hz ↦ ?_
    rw [LinearMap.comp_apply, mk_eq_zero_iff, cyclicCoboundaries_eq_bot_of_even h2 hn,
      Submodule.mem_bot, ← Submodule.coe_eq_zero, coe_mkPiRingCyclicCocycle_apply,
      mkPiRing_eq_zero_iff] at hz
    exact hz, fun x ↦ by
    obtain ⟨φ, rfl⟩ := mk_surjective R R M n x
    refine ⟨(φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) fun _ ↦ 1, ?_⟩
    rw [LinearMap.comp_apply, mkPiRingCyclicCocycle_apply_one]⟩).symm

/-- The inverse of `groundRingEquiv` sends `z` to the class of the product cochain of `z`. -/
@[simp]
theorem groundRingEquiv_symm_apply (h2 : IsSMulRegular M (2 : R)) (hn : Even n) (z : M) :
    (groundRingEquiv h2 hn).symm z = mk R R M n (mkPiRingCyclicCocycle R hn z) :=
  (rfl)

/-- The equivalence `groundRingEquiv` evaluates a cyclic cocycle at `(1, …, 1)`. -/
@[simp]
theorem groundRingEquiv_mk (h2 : IsSMulRegular M (2 : R)) (hn : Even n)
    (φ : cyclicCocycles R R M n) :
    groundRingEquiv h2 hn (mk R R M n φ) =
      (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) fun _ ↦ 1 := by
  rw [← LinearEquiv.eq_symm_apply, groundRingEquiv_symm_apply, mkPiRingCyclicCocycle_apply_one]

end cyclicCohomology

end TauCeti
