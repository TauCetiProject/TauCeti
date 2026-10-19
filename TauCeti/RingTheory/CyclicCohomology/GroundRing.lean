/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Cyclic cohomology of the ground ring

For a commutative ring `R` and an `R`-module `M`, this file computes the cyclic cohomology
`HCⁿ(R; M)` of `R` regarded as an algebra over itself. Every `M`-valued `n`-cochain on `R` is a
product cochain `(a₀, …, aₙ) ↦ (a₀ ⋯ aₙ) • m` (Mathlib's `MultilinearMap.mkPiRing`). Every
Hochschild face preserves the product of the entries, so the Hochschild coboundary of the
product cochain is `(∑ᵢ (-1)ⁱ) • (a₀ ⋯ aₙ₊₁) • m`: it vanishes in even degree and is the product
cochain of the same `m` in odd degree. Rotating the entries does not change their product, so the
product cochain is cyclic exactly when `(-1)ⁿ • m = m`.

Consequently:

* in odd degree there are no nonzero cyclic cocycles, and `HCⁿ(R; M) = 0`;
* in even degree every cochain is a cyclic cocycle, and `m ↦ [(a₀ ⋯ aₙ) • m]` maps `M` onto
  `HCⁿ(R; M)`. In degree zero it is injective; in positive even degree its kernel is the
  `2`-torsion of `M`, the values of cyclic cochains of the preceding odd degree.

So `HC²ᵏ(R; M) ≅ M` whenever multiplication by `2` is injective on `M`, for instance
`HC²ᵏ(ℂ) ≅ ℂ` and `HC²ᵏ⁺¹(ℂ) = 0`. Over a general commutative ring,
`HC²ᵏ⁺²(R; M) ≅ M ⧸ M[2]` where `M[2]` is the `2`-torsion submodule.

This is the full cyclic theory of the ground ring. It contrasts with the reduced theory of
`TauCeti.RingTheory.CyclicCohomology.Reduced`, whose complex for the ground ring is zero.

## Main definitions

* `TauCeti.cyclicCohomology.mkPiRing`: the class in even degree of the product cochain of `m`.
* `TauCeti.cyclicCohomology.selfEquiv`: `M ≃ HCⁿ(R; M)` for even `n` when `M` has no `2`-torsion.
* `TauCeti.cyclicCohomology.selfQuotEquiv`: `M ⧸ M[2] ≃ HCⁿ(R; M)` for even `n ≠ 0`.

## Main results

* `TauCeti.hochschildCoboundary_mkPiRing_of_even`, `TauCeti.hochschildCoboundary_mkPiRing_of_odd`:
  the Hochschild coboundary of a product cochain.
* `TauCeti.mkPiRing_mem_cyclicCochains_iff`: the product cochain of `m` is cyclic exactly when
  `(-1)ⁿ • m = m`.
* `TauCeti.cyclicCocycles_self_of_even`, `TauCeti.cyclicCocycles_self_of_odd`: the cyclic cocycles
  of the ground ring are all cochains in even degree and zero in odd degree.
* `TauCeti.isZero_cyclicCohomology_self_of_odd`: `HCⁿ(R; M) = 0` for odd `n`.
* `TauCeti.cyclicCohomology.mkPiRing_surjective`, `TauCeti.cyclicCohomology.ker_mkPiRing`: the
  class map is surjective, with kernel the `2`-torsion of `M` in positive even degree.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.1.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace TauCeti

universe u

variable (R : Type u) (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

/-! ### Product cochains -/

private theorem hochschildCoboundary_mkPiRing (n : ℕ) (m : M) :
    hochschildCoboundary R R M n (MultilinearMap.mkPiRing R (Fin (n + 1)) m) =
      if Even n then 0 else MultilinearMap.mkPiRing R (Fin (n + 2)) m := by
  ext
  simp only [hochschildCoboundary_apply, MultilinearMap.mkPiRing_apply, prod_hochschildFace,
    ← Finset.sum_smul]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (-1 : ℤ) ^ i) (n + 2), neg_one_geom_sum]
  split_ifs <;> simp_all [Nat.even_add_one]

/-- In even degree the Hochschild coboundary of a product cochain on the ground ring vanishes. -/
@[simp]
theorem hochschildCoboundary_mkPiRing_of_even (hn : Even n) (m : M) :
    hochschildCoboundary R R M n (MultilinearMap.mkPiRing R (Fin (n + 1)) m) = 0 := by
  simp [hochschildCoboundary_mkPiRing, hn]

/-- In odd degree the Hochschild coboundary of the product cochain
`(a₀, …, aₙ) ↦ (a₀ ⋯ aₙ) • m` is the product cochain `(a₀, …, aₙ₊₁) ↦ (a₀ ⋯ aₙ₊₁) • m`. -/
@[simp]
theorem hochschildCoboundary_mkPiRing_of_odd (hn : Odd n) (m : M) :
    hochschildCoboundary R R M n (MultilinearMap.mkPiRing R (Fin (n + 1)) m) =
      MultilinearMap.mkPiRing R (Fin (n + 2)) m := by
  simp [hochschildCoboundary_mkPiRing, Nat.not_even_iff_odd.2 hn]

/-- In even degree the Hochschild coboundary of every cochain on the ground ring vanishes. -/
theorem hochschildCoboundary_self_of_even (hn : Even n)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) :
    hochschildCoboundary R R M n φ = 0 := by
  rw [← φ.mkPiRing_apply_one_eq_self, hochschildCoboundary_mkPiRing_of_even R M hn]

/-- In odd degree the Hochschild coboundary of a cochain on the ground ring is the product
cochain of its value at `(1, …, 1)`. -/
theorem hochschildCoboundary_self_of_odd (hn : Odd n)
    (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) :
    hochschildCoboundary R R M n φ =
      MultilinearMap.mkPiRing R (Fin (n + 2)) (φ fun _ ↦ 1) := by
  rw [← φ.mkPiRing_apply_one_eq_self, hochschildCoboundary_mkPiRing_of_odd R M hn]
  simp

variable {R M} in
/-- The product cochain `(a₀, …, aₙ) ↦ (a₀ ⋯ aₙ) • m` is cyclic exactly when
`(-1)ⁿ • m = m`. -/
theorem mkPiRing_mem_cyclicCochains_iff {m : M} :
    MultilinearMap.mkPiRing R (Fin (n + 1)) m ∈ cyclicCochains R R M n ↔
      (-1 : ℤ) ^ n • m = m := by
  rw [mem_cyclicCochains_iff]
  refine ⟨fun h ↦ ?_, fun h a ↦ ?_⟩
  · simpa using (h fun _ ↦ 1).symm
  · rw [MultilinearMap.mkPiRing_apply, MultilinearMap.mkPiRing_apply, smul_comm, h]
    exact congrArg (· • m) (Equiv.prod_comp (finRotate (n + 1)).symm a)

variable {R M} in
/-- In odd degree the product cochain of `m` is cyclic exactly when `2 • m = 0`. -/
theorem mkPiRing_mem_cyclicCochains_iff_of_odd (hn : Odd n) {m : M} :
    MultilinearMap.mkPiRing R (Fin (n + 1)) m ∈ cyclicCochains R R M n ↔ (2 : R) • m = 0 := by
  rw [mkPiRing_mem_cyclicCochains_iff, hn.neg_one_pow, neg_one_smul, neg_eq_iff_add_eq_zero,
    ← two_smul R m]

/-! ### Cyclic cocycles -/

/-- In even degree every cochain on the ground ring is cyclic. -/
theorem cyclicCochains_self_of_even (hn : Even n) : cyclicCochains R R M n = ⊤ := by
  refine eq_top_iff.2 fun φ _ ↦ ?_
  rw [← φ.mkPiRing_apply_one_eq_self, mkPiRing_mem_cyclicCochains_iff, hn.neg_one_pow, one_smul]

/-- In even degree every cyclic cochain on the ground ring is a cocycle. -/
theorem cyclicCocycles_self_of_even (hn : Even n) : cyclicCocycles R R M n = ⊤ := by
  refine eq_top_iff.2 fun φ _ ↦ ?_
  rw [mem_cyclicCocycles_iff, hochschildCoboundary_self_of_even R M hn]

/-- In odd degree the ground ring has no nonzero cyclic cocycles. -/
theorem cyclicCocycles_self_of_odd (hn : Odd n) : cyclicCocycles R R M n = ⊥ := by
  refine eq_bot_iff.2 fun φ hφ ↦ ?_
  rw [mem_cyclicCocycles_iff, hochschildCoboundary_self_of_odd R M hn,
    MultilinearMap.mkPiRing_eq_zero_iff] at hφ
  rw [Submodule.mem_bot, ← Subtype.coe_inj,
    ← (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M).mkPiRing_apply_one_eq_self,
    hφ, MultilinearMap.mkPiRing_zero, ZeroMemClass.coe_zero]

/-- The cyclic cohomology of the ground ring vanishes in odd degree. -/
theorem isZero_cyclicCohomology_self_of_odd (hn : Odd n) :
    IsZero (cyclicCohomology R R M n) := by
  have h (φ : cyclicCocycles R R M n) : φ = 0 :=
    Subtype.ext ((Submodule.eq_bot_iff _).1 (cyclicCocycles_self_of_odd R M hn) φ φ.2)
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun x y ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := cyclicCohomology.mk_surjective R R M n x
  obtain ⟨ψ, rfl⟩ := cyclicCohomology.mk_surjective R R M n y
  rw [h φ, h ψ]

/-! ### Even degree -/

/-- The product cochain of `m` in even degree, as a cyclic cocycle. -/
private def mkPiRingCocycle (hn : Even n) : M →ₗ[R] cyclicCocycles R R M n :=
  ((MultilinearMap.piRingEquiv (R := R) (ι := Fin (n + 1))).toLinearMap.codRestrict
    (cyclicCochains R R M n) fun _ ↦ by simp [cyclicCochains_self_of_even R M hn]).codRestrict
    (cyclicCocycles R R M n) fun _ ↦ by simp [cyclicCocycles_self_of_even R M hn]

private theorem coe_mkPiRingCocycle (hn : Even n) (m : M) :
    ((mkPiRingCocycle R M hn m : cyclicCochains R R M n) :
      MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) = MultilinearMap.mkPiRing R (Fin (n + 1)) m :=
  (rfl)

private theorem mkPiRingCocycle_apply_one (hn : Even n) (φ : cyclicCocycles R R M n) :
    mkPiRingCocycle R M hn
        ((φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) fun _ ↦ 1) = φ :=
  Subtype.ext <| Subtype.ext <| MultilinearMap.mkPiRing_apply_one_eq_self _

private theorem mkPiRingCocycle_surjective (hn : Even n) :
    Function.Surjective (mkPiRingCocycle R M hn) := fun φ ↦
  ⟨(φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) fun _ ↦ 1,
    mkPiRingCocycle_apply_one R M hn φ⟩

namespace cyclicCohomology

/-- For even `n`, the class in `HCⁿ(R; M)` of the product cochain
`(a₀, …, aₙ) ↦ (a₀ ⋯ aₙ) • m`. -/
def mkPiRing (n : ℕ) (hn : Even n) : M →ₗ[R] cyclicCohomology R R M n :=
  mk R R M n ∘ₗ mkPiRingCocycle R M hn

/-- `mkPiRing R M n hn m` is the class of the product cochain of `m`. -/
theorem mkPiRing_apply (hn : Even n) (m : M) :
    mkPiRing R M n hn m =
      mk R R M n ⟨⟨MultilinearMap.mkPiRing R (Fin (n + 1)) m,
        by simp [cyclicCochains_self_of_even R M hn]⟩,
        by simp [cyclicCocycles_self_of_even R M hn]⟩ :=
  (rfl)

/-- In even degree the class of a cyclic cocycle `φ` is the class of the product cochain of its
value `φ(1, …, 1)`. -/
theorem mk_eq_mkPiRing (hn : Even n) (φ : cyclicCocycles R R M n) :
    mk R R M n φ =
      mkPiRing R M n hn ((φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) fun _ ↦ 1) := by
  rw [mkPiRing, LinearMap.comp_apply, mkPiRingCocycle_apply_one]

/-- In even degree every cyclic cohomology class of the ground ring is the class of a product
cochain. -/
theorem mkPiRing_surjective (hn : Even n) : Function.Surjective (mkPiRing R M n hn) :=
  (mk_surjective R R M n).comp (mkPiRingCocycle_surjective R M hn)

variable {R M} in
/-- In positive even degree the class of the product cochain of `m` vanishes exactly when
`2 • m = 0`: the coboundaries are the product cochains of `2`-torsion elements, which are cyclic
in the preceding odd degree. -/
theorem mkPiRing_eq_zero_iff (hn : Even n) (hn₀ : n ≠ 0) {m : M} :
    mkPiRing R M n hn m = 0 ↔ (2 : R) • m = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn₀
  have hk : Odd k := by simpa [Nat.even_add_one] using hn
  rw [mkPiRing, LinearMap.comp_apply, mk_eq_zero_iff, mem_cyclicCoboundaries_succ_iff,
    ← mkPiRing_mem_cyclicCochains_iff_of_odd hk]
  constructor
  · rintro ⟨ψ, hψ⟩
    have h := congrArg Subtype.val hψ
    rw [coe_cyclicHochschildCoboundary_apply, hochschildCoboundary_self_of_odd R M hk,
      coe_mkPiRingCocycle, MultilinearMap.mkPiRing_eq_iff] at h
    rw [← h,
      (ψ : MultilinearMap R (fun _ : Fin (k + 1) ↦ R) M).mkPiRing_apply_one_eq_self]
    exact ψ.2
  · intro hm
    exact ⟨⟨_, hm⟩, Subtype.ext <| by
      rw [coe_cyclicHochschildCoboundary_apply, hochschildCoboundary_mkPiRing_of_odd R M hk,
        coe_mkPiRingCocycle]⟩

/-- In positive even degree the kernel of the class map is the `2`-torsion of `M`. -/
theorem ker_mkPiRing (hn : Even n) (hn₀ : n ≠ 0) :
    LinearMap.ker (mkPiRing R M n hn) = Submodule.torsionBy R M 2 := by
  ext m
  rw [LinearMap.mem_ker, mkPiRing_eq_zero_iff hn hn₀, Submodule.mem_torsionBy_iff]

/-- In degree zero the class map is injective. -/
theorem mkPiRing_zero_injective : Function.Injective (mkPiRing R M 0 even_zero) :=
  (mk_zero_injective R R M).comp fun _ _ h ↦ MultilinearMap.mkPiRing_eq_iff.1
    (congrArg (fun φ : cyclicCocycles R R M 0 ↦ (φ : cyclicCochains R R M 0).1) h)

/-- In even degree the class map is injective when `M` has no `2`-torsion. -/
theorem mkPiRing_injective (hn : Even n) (h2 : IsSMulRegular M (2 : R)) :
    Function.Injective (mkPiRing R M n hn) := by
  rcases eq_or_ne n 0 with rfl | hn₀
  · exact mkPiRing_zero_injective R M
  · rw [← LinearMap.ker_eq_bot, ker_mkPiRing R M hn hn₀, ← isSMulRegular_iff_torsionBy_eq_bot]
    exact h2

/-- If multiplication by `2` is injective on `M`, then `HCⁿ(R; M) ≅ M` in every even degree `n`,
by the class of the product cochain. In particular `HC²ᵏ(ℂ) ≅ ℂ`. -/
def selfEquiv (hn : Even n) (h2 : IsSMulRegular M (2 : R)) :
    M ≃ₗ[R] cyclicCohomology R R M n :=
  LinearEquiv.ofBijective (mkPiRing R M n hn)
    ⟨mkPiRing_injective R M hn h2, mkPiRing_surjective R M hn⟩

/-- `selfEquiv` sends `m` to the class of its product cochain. -/
@[simp]
theorem selfEquiv_apply (hn : Even n) (h2 : IsSMulRegular M (2 : R)) (m : M) :
    selfEquiv R M hn h2 m = mkPiRing R M n hn m :=
  (rfl)

/-- The inverse of `selfEquiv` evaluates a representing cocycle at `(1, …, 1)`. -/
@[simp]
theorem selfEquiv_symm_mk (hn : Even n) (h2 : IsSMulRegular M (2 : R))
    (φ : cyclicCocycles R R M n) :
    (selfEquiv R M hn h2).symm (mk R R M n φ) =
      (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) fun _ ↦ 1 := by
  rw [LinearEquiv.symm_apply_eq, selfEquiv_apply, mk_eq_mkPiRing R M hn]

/-- In positive even degree `HCⁿ(R; M)` is the quotient of `M` by its `2`-torsion, by the class
of the product cochain. -/
def selfQuotEquiv (hn : Even n) (hn₀ : n ≠ 0) :
    (M ⧸ Submodule.torsionBy R M 2) ≃ₗ[R] cyclicCohomology R R M n :=
  (Submodule.quotEquivOfEq _ _ (ker_mkPiRing R M hn hn₀).symm).trans
    ((mkPiRing R M n hn).quotKerEquivOfSurjective (mkPiRing_surjective R M hn))

/-- `selfQuotEquiv` sends the class of `m` to the class of its product cochain. -/
@[simp]
theorem selfQuotEquiv_mk (hn : Even n) (hn₀ : n ≠ 0) (m : M) :
    selfQuotEquiv R M hn hn₀ (Submodule.Quotient.mk m) = mkPiRing R M n hn m :=
  by
    simp only [selfQuotEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
    exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ m

/-- The inverse of `selfQuotEquiv` sends a represented cohomology class to the quotient class of
the representing cocycle's value at `(1, …, 1)`. -/
@[simp]
theorem selfQuotEquiv_symm_mk (hn : Even n) (hn₀ : n ≠ 0)
    (φ : cyclicCocycles R R M n) :
    (selfQuotEquiv R M hn hn₀).symm (mk R R M n φ) =
      Submodule.Quotient.mk
        ((φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ R) M) fun _ ↦ 1) := by
  rw [LinearEquiv.symm_apply_eq, selfQuotEquiv_mk, mk_eq_mkPiRing R M hn]

end cyclicCohomology

end TauCeti
