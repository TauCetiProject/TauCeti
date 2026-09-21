/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Roots of unity do not leave an integrally closed subring

If `R` is integrally closed in `A`, then `R` and `A` have the same `n`-th roots of unity for every
`n ≠ 0`: an `n`-th root of unity `x` of `A` satisfies `x ^ n = 1`, so it is integral over `R` and
therefore comes from `R`, and its inverse `x ^ (n - 1)` comes from `R` as well.

The typical use is `R` a valuation ring and `A` its fraction field, where it says that all roots of
unity of the field are already units of the valuation ring.

## Main results

* `TauCeti.IsIntegrallyClosedIn.rootsOfUnityMulEquiv`: the inclusion `R → A` restricts to an
  isomorphism `μ_n(R) ≃* μ_n(A)`.
-/

public section

namespace TauCeti.IsIntegrallyClosedIn

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [IsIntegrallyClosedIn R A]
variable (n : ℕ) [NeZero n]

theorem restrictRootsOfUnity_bijective :
    Function.Bijective (restrictRootsOfUnity (algebraMap R A) n) := by
  have hinj : Function.Injective (algebraMap R A) := IsIntegralClosure.algebraMap_injective R R A
  refine ⟨fun x y h => Subtype.ext (Units.map_injective hinj (congrArg Subtype.val h)), fun ξ => ?_⟩
  have hξ : ((ξ : Aˣ) : A) ^ n = 1 := (mem_rootsOfUnity' n _).1 ξ.2
  obtain ⟨y, hy⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow
    (R := R) (A := A) (NeZero.pos n) (hξ ▸ isIntegral_one)
  have hyn : y ^ n = 1 := hinj (by rw [map_pow, hy, hξ, map_one])
  refine ⟨⟨(IsUnit.of_pow_eq_one hyn (NeZero.ne n)).unit, (mem_rootsOfUnity' n _).2 (by simpa)⟩, ?_⟩
  exact Subtype.ext (Units.ext (by simpa using hy))

/-- If `R` is integrally closed in `A`, the inclusion `R → A` identifies the `n`-th roots of unity
of `R` with those of `A`. -/
noncomputable def rootsOfUnityMulEquiv : rootsOfUnity n R ≃* rootsOfUnity n A :=
  MulEquiv.ofBijective (restrictRootsOfUnity (algebraMap R A) n)
    (restrictRootsOfUnity_bijective R A n)

@[simp] theorem coe_rootsOfUnityMulEquiv (x : rootsOfUnity n R) :
    ((rootsOfUnityMulEquiv R A n x : Aˣ) : A) = algebraMap R A ((x : Rˣ) : R) := by
  simp [rootsOfUnityMulEquiv]

end TauCeti.IsIntegrallyClosedIn
