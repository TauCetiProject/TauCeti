/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Roots of unity of a valued field are integral

For a valued field `K` and a nonzero `n`, an `n`-th root of unity of `K` has valuation one, so it
is a unit of the ring of integers `𝒪[K]`. The inclusion `𝒪[K] → K` therefore identifies the
`n`-th roots of unity of `𝒪[K]` with those of `K`.

## Main definitions

* `TauCeti.integerRootsOfUnityEquivRootsOfUnity`: the `n`-th roots of unity in `𝒪[K]` are those
  in `K`.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K]

private theorem restrictRootsOfUnity_integer_bijective (n : ℕ) [NeZero n] :
    Function.Bijective (restrictRootsOfUnity (Subring.subtype 𝒪[K]) n) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity n K ↦ ((z : Kˣ) : K)) huv
  · intro z
    have hzpow : ((z : Kˣ) : K) ^ n = 1 :=
      (mem_rootsOfUnity' n (z : Kˣ)).mp z.prop
    have hvpow : valuation K ((z : Kˣ) : K) ^ n = 1 := by
      rw [← map_pow, hzpow, map_one]
    have hv : valuation K ((z : Kˣ) : K) = 1 :=
      (pow_eq_one_iff_of_nonneg zero_le (NeZero.ne n)).mp hvpow
    have hzmem : ((z : Kˣ) : K) ∈ 𝒪[K] :=
      (Valuation.mem_integer_iff (valuation K) _).mpr hv.le
    let x : 𝒪[K] := ⟨((z : Kˣ) : K), hzmem⟩
    have hxunit : IsUnit x :=
      (Valuation.integer.integers (valuation K)).isUnit_of_one' hv
    let u : 𝒪[K]ˣ := hxunit.unit
    have huK : ((u : 𝒪[K]) : K) = ((z : Kˣ) : K) := by
      rw [hxunit.unit_spec]
    have hupow : u ^ n = 1 := by
      apply Units.ext
      apply Subtype.ext
      simpa only [Units.val_pow_eq_pow_val, Units.val_one, Subring.coe_pow, Subring.coe_one,
        huK] using hzpow
    let w : rootsOfUnity n 𝒪[K] := ⟨u, hupow⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact huK

/-- For nonzero `n`, the `n`-th roots of unity in the ring of integers `𝒪[K]` of a valued field
are identified with the `n`-th roots of unity in `K`. -/
noncomputable def integerRootsOfUnityEquivRootsOfUnity (K : Type*) [Field K] [ValuativeRel K]
    (n : ℕ) [NeZero n] : rootsOfUnity n 𝒪[K] ≃* rootsOfUnity n K :=
  MulEquiv.ofBijective (restrictRootsOfUnity (Subring.subtype 𝒪[K]) n)
    (restrictRootsOfUnity_integer_bijective n)

/-- The comparison of roots of unity is the inclusion `𝒪[K] → K`. -/
@[simp]
theorem integerRootsOfUnityEquivRootsOfUnity_apply (n : ℕ) [NeZero n]
    (u : rootsOfUnity n 𝒪[K]) :
    ((integerRootsOfUnityEquivRootsOfUnity K n u : Kˣ) : K) = ((u : 𝒪[K]ˣ) : 𝒪[K]) := by
  rw [integerRootsOfUnityEquivRootsOfUnity, MulEquiv.ofBijective_apply,
    restrictRootsOfUnity_coe_apply, Subring.coe_subtype]

/-- The inverse comparison of roots of unity views a root of unity of `K` as an integer. -/
@[simp]
theorem integerRootsOfUnityEquivRootsOfUnity_symm_apply (n : ℕ) [NeZero n]
    (z : rootsOfUnity n K) :
    ((((integerRootsOfUnityEquivRootsOfUnity K n).symm z : 𝒪[K]ˣ) : 𝒪[K]) : K) =
      ((z : Kˣ) : K) := by
  rw [← integerRootsOfUnityEquivRootsOfUnity_apply, MulEquiv.apply_symm_apply]

end TauCeti
