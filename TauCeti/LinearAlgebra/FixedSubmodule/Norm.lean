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

open Classical in
/-- A sum over complete periods repeats the distinct-cycle sum with multiplicity `k / l`. -/
theorem sum_range_pow_eq_nsmul_sum_cycle {M : Type*} [AddCommMonoid M]
    (v : I → M) {k : ℕ} (hk : σ ^ k = 1) (i : I) :
    ∑ r ∈ range k, v ((σ ^ r) i) =
      (k / minimalPeriod σ i) • ∑ j with σ.SameCycle i j, v j := by
  classical
  have hp : IsPeriodicPt σ k i := by
    simp only [IsPeriodicPt, IsFixedPt, ← coe_pow, hk, Perm.one_apply]
  have hd := hp.minimalPeriod_dvd
  have hblock (n : ℕ) :
      ∑ r ∈ range (minimalPeriod σ i * n), v ((σ ^ r) i) =
        n • ∑ r ∈ range (minimalPeriod σ i), v ((σ ^ r) i) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, sum_range_add, ih, succ_nsmul]
      congr 1
      apply sum_congr rfl
      intro r hr
      congr 1
      simp only [coe_pow]
      rw [Nat.add_comm, iterate_add_apply, iterate_mul,
        (isPeriodicPt_minimalPeriod σ i).isFixedPt.iterate n]
  conv_lhs => rw [← Nat.mul_div_cancel' hd]
  rw [hblock, σ.sum_range_minimalPeriod]

variable {R M : Type*} [Semiring R] [AddCancelCommMonoid M] [Module R M]

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
    have hshift := sum_range_succ' (fun r ↦ v ((σ ^ r) i)) k
    rw [sum_range_succ, hk] at hshift
    simp only [pow_zero, Perm.one_apply] at hshift
    have hstep (r : ℕ) : (σ ^ (r + 1)) i = (σ ^ r) (σ i) := by
      rw [pow_succ, Perm.mul_apply]
    simp only [hstep] at hshift
    exact (add_right_cancel hshift).symm

omit [Fintype I] in
/-- The ambient coordinates of the full cyclic sum are the literal sums over `k` iterates. -/
@[simp]
theorem permutationNorm_apply (k : ℕ) (hk : σ ^ k = 1) (v : I → M) (i : I) :
    (σ.permutationNorm (R := R) k hk v).val i = ∑ r ∈ range k, v ((σ ^ r) i) := by
  simp only [permutationNorm, LinearMap.codRestrict_apply, LinearMap.sum_apply,
    Finset.sum_apply, LinearMap.funLeft_apply]

open Classical in
/-- Each fixed coordinate is the distinct-cycle sum multiplied by the stabilizer multiplicity. -/
theorem permutationNorm_apply_eq_sum_cycle (k : ℕ) (hk : σ ^ k = 1) (v : I → M) (i : I) :
    (σ.permutationNorm (R := R) k hk v).val i =
      (k / minimalPeriod σ i) • ∑ j with σ.SameCycle i j, v j :=
  (σ.permutationNorm_apply k hk v i).trans
    (σ.sum_range_pow_eq_nsmul_sum_cycle v hk i)

omit [Fintype I] in
/-- The full-sum image in the integral fixed lattice is given by cyclewise divisibility.
This includes exponent zero: then only the zero vector is in the image. -/
theorem mem_range_permutationNorm_iff [Finite I] (k : ℕ) (hk : σ ^ k = 1)
    (v : (LinearEquiv.funCongrLeft ℤ ℤ σ).toLinearMap.fixedSubmodule) :
    v ∈ LinearMap.range (σ.permutationNorm (R := ℤ) (M := ℤ) k hk) ↔
      ∀ c : Quotient (SameCycle.setoid σ),
        ((k / minimalPeriod σ c.out : ℕ) : ℤ) ∣ v.val c.out := by
  classical
  let _ := Fintype.ofFinite I
  constructor
  · rintro ⟨x, rfl⟩ c
    rw [permutationNorm_apply_eq_sum_cycle, nsmul_eq_mul]
    exact dvd_mul_right _ _
  · intro hv
    choose w hw using hv
    let x : I → ℤ := fun i ↦
      if i = (Quotient.mk (SameCycle.setoid σ) i).out then
        w (Quotient.mk _ i) else 0
    refine ⟨x, ?_⟩
    apply (permutationFixedEquiv (R := ℤ) (M := ℤ) σ).symm.injective
    funext c
    suffices h : (σ.permutationNorm k hk x).val c.out = v.val c.out by
      simpa only [← permutationFixedEquiv_symm_apply σ _ c.out, Quotient.out_eq] using h
    have hsum : ∑ j with σ.SameCycle c.out j, x j = w c := by
      rw [sum_eq_single c.out]
      · simp only [x, Quotient.out_eq, ite_true]
      · intro j hj hne
        have hjc : Quotient.mk (SameCycle.setoid σ) j = c :=
          (Quotient.sound (mem_filter.mp hj).2.symm).trans (Quotient.out_eq c)
        simp only [x, hjc, ite_eq_right hne]
      · intro hnot
        exact False.elim (hnot (mem_filter.mpr ⟨mem_univ _, SameCycle.refl σ _⟩))
    rw [permutationNorm_apply_eq_sum_cycle, hsum, nsmul_eq_mul, ← hw c]

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
      Int.mem_zmultiples_iff]
    apply forall_congr'
    intro c
    -- Forgetting linearity does not change the inverse coordinate map.
    have he : e.symm.toAddMonoidHom v c = v.val c.out := by
      rw [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe]
      simpa only [Quotient.out_eq] using permutationFixedEquiv_symm_apply σ v c.out
    rw [he]
  rw [hrange, AddSubgroup.index_comap_of_surjective H e.symm.surjective,
    AddSubgroup.index_pi]
  simp only [Int.index_zmultiples, Int.natAbs_natCast]

end Equiv.Perm
