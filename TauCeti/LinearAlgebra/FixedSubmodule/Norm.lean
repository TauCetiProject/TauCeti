/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation
public import TauCeti.GroupTheory.Perm.Cycle.Enumeration
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# Integral cyclic sums of coordinate permutations

For a permutation `σ` and an exponent `k` with `σ ^ k = 1`, summing the first `k`
coordinate permutations gives a map to the fixed lattice. On a cycle of length `l`
its coordinate is `k / l` times the sum of the input coordinates on that cycle.
Consequently its integral image consists exactly of the fixed vectors whose cycle
coordinates are divisible by these multiplicities. Its index is their product.

In diagram folding this distinguishes full sums from distinct-orbit sums: even when
the fixed lattice has an orbit-indicator basis, full sums need not generate it.
No characteristic-zero or connectedness assumption on the diagram is involved.

The fixed coordinates and orbit basis are those of
`Equiv.Perm.permutationFixedEquiv` and `Equiv.Perm.permutationFixedBasis`.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.
-/

public noncomputable section

open Function Finset

namespace Equiv.Perm

variable {I : Type*} [Fintype I] (σ : Perm I)

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The full cyclic sum, valued in the actual fixed submodule of the coordinate permutation.
The exponent may be any multiple of the permutation order, including zero. -/
def permutationNorm (k : ℕ) (hk : σ ^ k = 1) :
    (I → M) →ₗ[R] (LinearEquiv.funCongrLeft R M σ).toLinearMap.fixedSubmodule :=
  (∑ r ∈ range k, LinearMap.funLeft R M (σ ^ r)).codRestrict _ fun v ↦ by
    apply LinearMap.mem_fixedSubmodule_iff.mpr
    funext i
    -- `funCongrLeft` precomposes by `σ`; cyclic shifting leaves the full sum unchanged.
    suffices h : (∑ r ∈ range k, v ((σ ^ r) (σ i))) =
        ∑ r ∈ range k, v ((σ ^ r) i) by
      simpa only [LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
        LinearMap.funLeft_apply, LinearMap.sum_apply, Finset.sum_apply] using h
    have hstep (r : ℕ) : (σ ^ (r + 1)) i = (σ ^ r) (σ i) := by
      rw [pow_succ, Perm.mul_apply]
    simp only [← hstep]
    cases k with
    | zero => simp
    | succ n =>
      rw [sum_range_succ' (fun r ↦ v ((σ ^ r) i)),
        sum_range_succ (fun r ↦ v ((σ ^ (r + 1)) i)), hk]
      simp

omit [Fintype I] in
/-- The ambient coordinates of the full cyclic sum are the literal sums over `k` iterates. -/
@[simp]
theorem permutationNorm_apply (k : ℕ) (hk : σ ^ k = 1) (v : I → M) (i : I) :
    (σ.permutationNorm (R := R) k hk v).val i = ∑ r ∈ range k, v ((σ ^ r) i) := by
  simp only [permutationNorm, LinearMap.codRestrict_apply, LinearMap.sum_apply,
    Finset.sum_apply, LinearMap.funLeft_apply]

open Classical in
/-- Each fixed coordinate is the distinct-cycle sum multiplied by the stabilizer multiplicity. -/
theorem permutationNorm_apply_eq_nsmul_sum_cycle (k : ℕ) (hk : σ ^ k = 1) (v : I → M) (i : I) :
    (σ.permutationNorm (R := R) k hk v).val i =
      (k / minimalPeriod σ i) • ∑ j with σ.SameCycle i j, v j :=
  (σ.permutationNorm_apply k hk v i).trans
    (σ.sum_range_pow_eq_nsmul_sum_cycle v i (by
      simp only [IsPeriodicPt, IsFixedPt, ← coe_pow, hk, Perm.one_apply]))

open Classical in
/-- In cycle coordinates, the full cyclic sum is the distinct-cycle sum multiplied by
its stabilizer multiplicity. -/
@[simp]
theorem permutationFixedEquiv_symm_permutationNorm (k : ℕ) (hk : σ ^ k = 1)
    (v : I → M) (c : Quotient (SameCycle.setoid σ)) :
    (permutationFixedEquiv (R := R) (M := M) σ).symm (σ.permutationNorm k hk v) c =
      (k / minimalPeriod σ c.out) • ∑ j with σ.SameCycle c.out j, v j := by
  rw [permutationFixedEquiv_symm_apply_out, permutationNorm_apply_eq_nsmul_sum_cycle]

omit [Fintype I] in
/-- The full-sum image in the integral fixed lattice is given by cyclewise divisibility.
This includes exponent zero: then only the zero vector is in the image. -/
theorem mem_range_permutationNorm_iff [Finite I] (k : ℕ) (hk : σ ^ k = 1)
    (v : (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule) :
    v ∈ LinearMap.range (σ.permutationNorm (R := ℤ) (M := ℤ) k hk) ↔
      ∀ c : Quotient (SameCycle.setoid σ),
        ((k / minimalPeriod σ c.out : ℕ) : ℤ) ∣
          (permutationFixedEquiv (R := ℤ) (M := ℤ) σ).symm v c := by
  classical
  let _ := Fintype.ofFinite I
  constructor
  · rintro ⟨x, rfl⟩ c
    rw [permutationFixedEquiv_symm_permutationNorm, nsmul_eq_mul]
    exact dvd_mul_right _ _
  · intro hv
    choose w hw using hv
    let x : I → ℤ := fun i ↦
      if i = (Quotient.mk (SameCycle.setoid σ) i).out then
        w (Quotient.mk _ i) else 0
    refine ⟨x, ?_⟩
    apply (permutationFixedEquiv (R := ℤ) (M := ℤ) σ).symm.injective
    funext c
    have hsum : ∑ j with σ.SameCycle c.out j, x j = w c :=
      sum_cycle_representative σ w c
    rw [permutationFixedEquiv_symm_permutationNorm, hsum, nsmul_eq_mul, ← hw c]

open Classical in
/-- The index of the full-sum image in the integral fixed lattice is the product of the
cycle multiplicities, not in general one. The empty coordinate type gives the empty product. -/
theorem index_range_permutationNorm (k : ℕ) (hk : σ ^ k = 1) :
    (LinearMap.range (σ.permutationNorm (R := ℤ) (M := ℤ) k hk)).toAddSubgroup.index =
      ∏ c : Quotient (SameCycle.setoid σ), k / minimalPeriod σ c.out := by
  classical
  let e := permutationFixedEquiv (R := ℤ) (M := ℤ) σ
  let H := AddSubgroup.pi _root_.Set.univ fun c : Quotient (SameCycle.setoid σ) ↦
    AddSubgroup.zmultiples ((k / minimalPeriod σ c.out : ℕ) : ℤ)
  have hrange : (LinearMap.range (σ.permutationNorm (R := ℤ) (M := ℤ) k hk)).toAddSubgroup =
      H.comap e.symm.toAddMonoidHom := by
    ext v
    rw [Submodule.mem_toAddSubgroup, mem_range_permutationNorm_iff]
    simp only [AddSubgroup.mem_comap, H, AddSubgroup.mem_pi, _root_.Set.mem_univ, forall_const,
      Int.mem_zmultiples_iff, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, e]
  rw [hrange, AddSubgroup.index_comap_of_surjective H e.symm.surjective,
    AddSubgroup.index_pi]
  simp only [Int.index_zmultiples, Int.natAbs_natCast]

end Equiv.Perm
