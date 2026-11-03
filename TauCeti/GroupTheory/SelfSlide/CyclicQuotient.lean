/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.Index
public import TauCeti.Algebra.Module.Primitive
import Mathlib.Tactic.Linarith

/-!
# Cyclic quotients for a nonprimitive slide class

Let `f : H →+ ℤ` be a surjective integral coordinate and suppose `f h = d > 0`.
Two different cyclic quotients are useful in finite-cover arguments for dynamical torsion:

* `f.invMulCastZMod d k`, namely `f` modulo `k` multiplied by the inverse of `d`,
  sends `h` to `1` when `k`
  is coprime to `d`. Its kernel meets the multiples of `h` exactly at the multiples of `k h`.
* `f.castZMod (d * k)` sends `h` to `d`, for every `k`. Its kernel has the same
  intersection with the multiples of `h`, but its index is `d * k`, not `k`.

Both maps kill torsion, since they factor through `ℤ`. For a nontorsion class in a
finitely generated abelian group, `TauCeti.exists_integral_coordinate_of_notMem_torsion`
constructs such a coordinate with `d` equal to the divisibility of the class in the
torsion-free quotient. The coprime cover cutoffs exhaust all finite potential drops.
The example `H = ℤ × ZMod 2`, `h = (2, 1)` shows that both families apply without
assuming the slide class is primitive or the group is torsion free.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  §3 (finite cyclic covers in the self-slide argument).
-/

public section

noncomputable section

namespace AddMonoidHom

variable {H : Type*} [AddCommGroup H] (f : H →+ ℤ)

/-- Reduce an integer-valued additive homomorphism modulo `n`. -/
def castZMod (n : ℕ) : H →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp f

/-- Multiply reduction modulo `k` by the inverse of `d` in `ZMod k`.
This sends a class of coordinate `d` to `1` when `d` and `k` are coprime. -/
def invMulCastZMod (d k : ℕ) : H →+ ZMod k :=
  (AddMonoidHom.mulLeft ((d : ZMod k)⁻¹)).comp (f.castZMod k)

@[simp]
theorem castZMod_apply (n : ℕ) (x : H) :
    f.castZMod n x = (f x : ZMod n) := (rfl)

@[simp]
theorem invMulCastZMod_apply (d k : ℕ) (x : H) :
    f.invMulCastZMod d k x = (d : ZMod k)⁻¹ * (f x : ZMod k) := (rfl)

/-- Reduction modulo `n` is onto whenever the integral coordinate is onto. -/
theorem castZMod_surjective (n : ℕ) (hf : Function.Surjective f) :
    Function.Surjective (f.castZMod n) :=
  ZMod.intCast_surjective.comp hf

variable (d k : ℕ)

/-- The normalized reduction is onto when the normalizing coefficient is invertible. -/
theorem invMulCastZMod_surjective (hf : Function.Surjective f)
    (hdk : d.Coprime k) : Function.Surjective (f.invMulCastZMod d k) := by
  have hu : IsUnit (d : ZMod k) := (ZMod.isUnit_iff_coprime d k).2 hdk
  intro y
  obtain ⟨x, hx⟩ := (ZMod.intCast_surjective.comp hf) ((d : ZMod k) * y)
  dsimp only [Function.comp_apply] at hx
  exact ⟨x, by simp [hx, ← mul_assoc, ZMod.inv_mul_of_unit _ hu]⟩

/-- An element lies in the reduction kernel exactly when its coordinate is divisible
by the modulus. -/
theorem mem_ker_castZMod_iff (n : ℕ) (x : H) :
    x ∈ (f.castZMod n).ker ↔ (n : ℤ) ∣ f x := by
  rw [mem_ker, castZMod_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- For coprime degrees, an element lies in the stabilization kernel exactly when its
coordinate is divisible by `k`. -/
theorem mem_ker_invMulCastZMod_iff (hdk : d.Coprime k) (x : H) :
    x ∈ (f.invMulCastZMod d k).ker ↔ (k : ℤ) ∣ f x := by
  rw [mem_ker, invMulCastZMod_apply,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hu := (ZMod.isUnit_iff_coprime d k).2 hdk
  constructor
  · intro hx
    have heq := congrArg ((d : ZMod k) * ·) hx
    simpa only [← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul, mul_zero] using heq
  · intro hx
    simp [hx]

variable {d k} {h : H}

/-- A slide of integral coordinate `d` maps to `d` in the norm-elimination quotient. -/
theorem castZMod_apply_of_eq (hh : f h = d) :
    f.castZMod (d * k) h = d := by simp [hh]

/-- A slide of integral coordinate `d` maps to `1` in the coprime stabilization quotient. -/
theorem invMulCastZMod_apply_of_eq (hh : f h = d) (hdk : d.Coprime k) :
    f.invMulCastZMod d k h = 1 := by
  simp only [invMulCastZMod_apply, hh, Int.cast_natCast]
  exact ZMod.inv_mul_of_unit _ ((ZMod.isUnit_iff_coprime d k).2 hdk)

/-- The norm-elimination quotient retains exactly the `k`-divisible iterates of the slide.
The integer multiplier may be negative. -/
theorem zsmul_mem_ker_castZMod_iff (hh : f h = d) (hd : d ≠ 0) (n : ℤ) :
    n • h ∈ (f.castZMod (d * k)).ker ↔ (k : ℤ) ∣ n := by
  rw [mem_ker_castZMod_iff, map_zsmul, hh, zsmul_eq_mul, Int.cast_id,
    Nat.cast_mul, mul_comm n]
  exact mul_dvd_mul_iff_left (by exact_mod_cast hd)

/-- The stabilization quotient retains exactly the `k`-divisible iterates of the slide. -/
theorem zsmul_mem_ker_invMulCastZMod_iff (hh : f h = d)
    (hdk : d.Coprime k) (n : ℤ) :
    n • h ∈ (f.invMulCastZMod d k).ker ↔ (k : ℤ) ∣ n := by
  rw [mem_ker_invMulCastZMod_iff f d k hdk, map_zsmul, hh, zsmul_eq_mul]
  exact hdk.symm.isCoprime.dvd_mul_right_iff

/-- The ordinary nonnegative iterates retained by norm elimination are exactly those
whose multiplicity is divisible by `k`. -/
theorem nsmul_mem_ker_castZMod_iff (hh : f h = d) (hd : d ≠ 0) (n : ℕ) :
    n • h ∈ (f.castZMod (d * k)).ker ↔ k ∣ n := by
  simpa only [natCast_zsmul, Int.natCast_dvd_natCast] using
    f.zsmul_mem_ker_castZMod_iff (k := k) hh hd (n : ℤ)

/-- The ordinary nonnegative iterates retained by stabilization are exactly those
whose multiplicity is divisible by `k`. -/
theorem nsmul_mem_ker_invMulCastZMod_iff (hh : f h = d)
    (hdk : d.Coprime k) (n : ℕ) :
    n • h ∈ (f.invMulCastZMod d k).ker ↔ k ∣ n := by
  simpa only [natCast_zsmul, Int.natCast_dvd_natCast] using
    f.zsmul_mem_ker_invMulCastZMod_iff hh hdk (n : ℤ)

/-- Reduction of a surjective integral coordinate modulo `n` has kernel of index `n`. -/
theorem index_ker_castZMod (n : ℕ) (hf : Function.Surjective f) :
    (f.castZMod n).ker.index = n := by
  rw [AddSubgroup.index_ker, range_eq_top.2 (f.castZMod_surjective n hf)]
  simp

/-- The stabilization cover has degree `k`. -/
theorem index_ker_invMulCastZMod (hf : Function.Surjective f)
    (hdk : d.Coprime k) : (f.invMulCastZMod d k).ker.index = k := by
  rw [AddSubgroup.index_ker,
    range_eq_top.2 (f.invMulCastZMod_surjective d k hf hdk)]
  simp

/-- Reduction modulo `n` kills the entire torsion subgroup. -/
theorem torsion_le_ker_castZMod (n : ℕ) :
    AddCommGroup.torsion H ≤ (f.castZMod n).ker := by
  intro x hx
  have hf : f x = 0 := (isOfFinAddOrder_iff_eq_zero _).1 (f.isOfFinAddOrder hx)
  simp [mem_ker, hf]

/-- Stabilization quotients kill the entire torsion subgroup of the deck group. -/
theorem torsion_le_ker_invMulCastZMod :
    AddCommGroup.torsion H ≤ (f.invMulCastZMod d k).ker := by
  intro x hx
  have hf : f x = 0 := (isOfFinAddOrder_iff_eq_zero _).1 (f.isOfFinAddOrder hx)
  simp [mem_ker, hf]

/-- For an additive real-valued potential `N` with `N h > 0` and a positive `d`, the
coprime stabilization cutoffs `N (k • h)` with `k ≥ 2` exceed any prescribed real bound. -/
theorem exists_coprime_lt_map_nsmul {H : Type*} [AddCommGroup H] (N : H →+ ℝ)
    {h : H} (hh : 0 < N h) {d : ℕ} (hd : 0 < d) (C : ℝ) :
    ∃ k : ℕ, d.Coprime k ∧ 2 ≤ k ∧ C < N (k • h) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (C / N h))
  refine ⟨1 + m * d, ?_, ?_, ?_⟩
  · simp
  · have hm1 : 1 < m := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hm)
    nlinarith
  · rw [map_nsmul, nsmul_eq_mul]
    have hCm : C / N h < m := lt_of_le_of_lt (le_max_right _ _) hm
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    apply (div_lt_iff₀ hh).1
    nlinarith

end AddMonoidHom

namespace TauCeti

/-- The class `(2,1)` has divisibility exactly two in the quotient by the full torsion
subgroup, even though it is not twice any element of `ℤ × ZMod 2`. -/
example (n : ℕ) :
    (∃ x : (ℤ × ZMod 2) ⧸ AddCommGroup.torsion (ℤ × ZMod 2),
      QuotientAddGroup.mk' _ (2, 1) = n • x) ↔ n ∣ 2 := by
  have hker : AddCommGroup.torsion (ℤ × ZMod 2) =
      (AddMonoidHom.fst ℤ (ZMod 2)).ker := by
    ext x
    simp [AddCommGroup.mem_torsion, IsOfFinAddOrder.prod_iff,
      isOfFinAddOrder_iff_eq_zero, isOfFinAddOrder_of_finite, AddSubgroup.mem_prod]
  let e := QuotientAddGroup.liftEquiv _ (φ := AddMonoidHom.fst ℤ (ZMod 2))
    (fun z => ⟨(z, 0), rfl⟩) hker
  have he (x : ℤ × ZMod 2) : e (QuotientAddGroup.mk' _ x) = x.1 := by
    exact QuotientAddGroup.liftEquiv_mk _ _ hker x
  have hp : IsPrimitive (e.symm 1) :=
    isPrimitive_def.2 ⟨e.toAddMonoidHom.toIntLinearMap, by simp⟩
  have hclass : QuotientAddGroup.mk' _ ((2, 1) : ℤ × ZMod 2) = 2 • e.symm 1 := by
    apply e.injective
    rw [he, map_nsmul, e.apply_symm_apply]
    norm_num
  rw [hclass]
  exact hp.exists_eq_nsmul_iff_dvd 2 n

/-- The class `(2,1)` is not primitive in the torsion-free quotient. Its norm-elimination
cover nevertheless detects multiples exactly by their multiplicities, for every `k`. -/
example (k n : ℕ) :
    n • ((2, 1) : ℤ × ZMod 2) ∈
      ((AddMonoidHom.fst ℤ (ZMod 2)).castZMod (2 * k)).ker ↔ k ∣ n :=
  (AddMonoidHom.fst ℤ (ZMod 2)).nsmul_mem_ker_castZMod_iff
    (by rfl) (by decide) n

/-- For the class `(2,1)`, every odd-degree stabilization quotient sends the class to `1`. -/
example (k : ℕ) (hk : Odd k) :
    (AddMonoidHom.fst ℤ (ZMod 2)).invMulCastZMod 2 k (2, 1) = 1 := by
  apply (AddMonoidHom.fst ℤ (ZMod 2)).invMulCastZMod_apply_of_eq (by rfl)
  exact Nat.coprime_two_left.2 hk

/-- The norm-elimination cover for `(2,1)` has degree `2 k`, retaining the factor of two
coming from divisibility in the torsion-free quotient. -/
example (k : ℕ) :
    ((AddMonoidHom.fst ℤ (ZMod 2)).castZMod (2 * k)).ker.index = 2 * k :=
  (AddMonoidHom.fst ℤ (ZMod 2)).index_ker_castZMod (2 * k) (fun n => ⟨(n, 0), rfl⟩)

end TauCeti
