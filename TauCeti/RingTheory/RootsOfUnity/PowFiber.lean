/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The fibres of `u ↦ u ^ m` are the orbits of the `m`-th roots of unity

In a commutative group with zero `M` (for instance a field), the group `rootsOfUnity m M` acts on
`M` by multiplication. For `m ≠ 0`, two elements have the same `m`-th power exactly when they lie
in the same orbit: if `u ^ m = v ^ m` with `u ≠ 0` then `v / u` is an `m`-th root of unity, and if
`u = 0` then `v = 0` as well. So the map `u ↦ u ^ m` identifies the orbit set of this action with
the set of `m`-th powers.

The action is free away from `0`, whose stabilizer is the whole roots-of-unity group. This is the
algebraic half of the local model `u ↦ u ^ m` for the quotient of a disc by a finite rotation
group: the orbit map of the rotation action is the power map.

## Main declarations

* `TauCeti.pow_eq_pow_iff_exists_rootsOfUnity_smul`: `u ^ m = v ^ m` iff `v = ζ • u` for some
  `ζ` in `rootsOfUnity m M`.
* `TauCeti.orbitRel_rootsOfUnity_apply`: the orbit relation of the action is the kernel of
  `u ↦ u ^ m`.
* `TauCeti.preimage_image_pow_eq`: an invariant set is saturated for `u ↦ u ^ m`.
* `TauCeti.stabilizer_rootsOfUnity_of_ne_zero`, `TauCeti.stabilizer_rootsOfUnity_zero`: the
  stabilizer is trivial away from `0` and everything at `0`.
-/

public section

namespace TauCeti

open MulAction

variable {M : Type*} {m : ℕ}

private theorem rootsOfUnity_smul_eq_mul [CommMonoid M]
    (ζ : rootsOfUnity m M) (u : M) : ζ • u = ((ζ : Mˣ) : M) * u := by
  rw [Subgroup.smul_def, Units.smul_def, smul_eq_mul]

/-- Multiplication by an `m`-th root of unity does not change the `m`-th power. -/
@[simp]
theorem rootsOfUnity_smul_pow [CommMonoid M]
    (ζ : rootsOfUnity m M) (u : M) : (ζ • u) ^ m = u ^ m := by
  simp only [rootsOfUnity_smul_eq_mul, mul_pow, ← Units.val_pow_eq_pow_val,
    (mem_rootsOfUnity m _).mp ζ.2, Units.val_one, one_mul]

/-- For `m ≠ 0`, two elements have the same `m`-th power exactly when one is obtained from the
other by multiplication with an `m`-th root of unity. -/
theorem pow_eq_pow_iff_exists_rootsOfUnity_smul [CommGroupWithZero M]
    (hm : m ≠ 0) {u v : M} :
    u ^ m = v ^ m ↔ ∃ ζ : rootsOfUnity m M, ζ • u = v := by
  refine ⟨fun h ↦ ?_, fun ⟨ζ, hζ⟩ ↦ hζ ▸ (rootsOfUnity_smul_pow ζ u).symm⟩
  rcases eq_or_ne u 0 with rfl | hu
  · refine ⟨1, ?_⟩
    rw [zero_pow hm, eq_comm, pow_eq_zero_iff hm] at h
    rw [h, one_smul]
  · have hv : v ≠ 0 := by
      rintro rfl
      exact hu (pow_eq_zero_iff hm |>.mp (h.trans (zero_pow hm)))
    refine ⟨⟨Units.mk0 (v / u) (div_ne_zero hv hu), ?_⟩, ?_⟩
    · simp only [mem_rootsOfUnity', Units.val_mk0, div_pow, h,
        div_self (pow_ne_zero m hv)]
    · simp only [rootsOfUnity_smul_eq_mul, Units.val_mk0, div_mul_cancel₀ v hu]

/-- For `m ≠ 0`, the orbit relation of the `m`-th roots of unity acting by multiplication is the
relation of having the same `m`-th power. -/
theorem orbitRel_rootsOfUnity_apply [CommGroupWithZero M] (hm : m ≠ 0) {u v : M} :
    orbitRel (rootsOfUnity m M) M u v ↔ u ^ m = v ^ m := by
  rw [orbitRel_apply, mem_orbit_iff, eq_comm (a := u ^ m),
    pow_eq_pow_iff_exists_rootsOfUnity_smul hm]

/-- For `m ≠ 0`, a set invariant under the `m`-th roots of unity is the full preimage of its
image under `u ↦ u ^ m`. -/
theorem preimage_image_pow_eq [CommGroupWithZero M]
    (hm : m ≠ 0) (s : SubMulAction (rootsOfUnity m M) M) :
    (· ^ m) ⁻¹' ((· ^ m) '' (s : Set M)) = s := by
  refine Set.Subset.antisymm (fun v ⟨u, hu, huv⟩ ↦ ?_) (Set.subset_preimage_image _ _)
  obtain ⟨ζ, rfl⟩ := (pow_eq_pow_iff_exists_rootsOfUnity_smul hm).mp huv
  exact s.smul_mem ζ hu

/-- Multiplication by the `m`-th roots of unity is free away from `0`. -/
@[simp]
theorem stabilizer_rootsOfUnity_of_ne_zero [CommMonoidWithZero M] [IsCancelMulZero M]
    {u : M} (hu : u ≠ 0) :
    stabilizer (rootsOfUnity m M) u = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ ↦ ?_
  rw [mem_stabilizer_iff, rootsOfUnity_smul_eq_mul] at hζ
  exact Subtype.ext <| Units.ext <| by
    simpa using mul_right_cancel₀ hu (hζ.trans (one_mul u).symm)

/-- Every `m`-th root of unity fixes `0`. -/
@[simp]
theorem stabilizer_rootsOfUnity_zero [CommMonoidWithZero M] :
    stabilizer (rootsOfUnity m M) (0 : M) = ⊤ :=
  Subgroup.eq_top_iff' _ |>.mpr fun ζ ↦ mem_stabilizer_iff.mpr (by
    rw [rootsOfUnity_smul_eq_mul, mul_zero])

end TauCeti
