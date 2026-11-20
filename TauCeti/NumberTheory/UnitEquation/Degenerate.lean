/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Basic.Finite.Defs
public import TauCeti.NumberTheory.UnitEquation.Nondegenerate

import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Pi
import TauCeti.Algebra.Polynomial.Laurent.Detection

/-!
# Degenerate solutions of linear unit equations

A solution `y` of `∑ αᵢ yᵢ = 1` is degenerate when some nonempty subsum `∑ i ∈ I, αᵢ yᵢ`
vanishes. Counting arguments for unit equations treat the degenerate solutions separately from the
nondegenerate ones, and this file proves the two descriptions of the degenerate locus they use.

*Subsum hyperplanes.* Over a commutative semiring `R`, if all `αᵢ` are nonzero, the degenerate
solutions lie in at most `2 ^ n` proper submodules of `Rⁿ`, namely the kernels of the linear forms
`y ↦ ∑ i ∈ I, αᵢ yᵢ` over nonempty `I`
(`TauCeti.exists_finset_submodule_of_not_isNondegenerateSolution`). A bound for the number of
proper subspaces containing all solutions therefore only has to handle the nondegenerate ones.

*Translates of one-parameter subgroups.* Let `K` be a field. A vector `k : ι → ℤ` defines the
one-parameter subgroup `t ↦ (t ^ kᵢ)ᵢ` of the torus `(Kˣ)ᶥ`; it is nontrivial when `k ≠ 0`. For any
point `x`, write `t ↦ (xᵢ t ^ kᵢ)ᵢ` for the curve obtained by scaling the coordinates of `x`; when
every `xᵢ` is nonzero it is the translate through `x` of this subgroup, a curve in the torus. The
results below are stated for these coordinate scalings of an arbitrary `x`, and only their
interpretation as torus translates needs the coordinates of `x` to be nonzero.

Bounds for points of small height on a subvariety `X` of a torus, such as Schmidt's, only count the
points of `X` lying on no torus coset of positive dimension contained in `X`. To count nondegenerate
solutions of `∑ αᵢ yᵢ = 1` in this way, one needs that these cosets consist of degenerate solutions.
Since every such coset contains a translate of a nontrivial one-parameter subgroup, it suffices to
prove this for those translates.

If the linear form `∑ αᵢ yᵢ` is constant on the curve `t ↦ (xᵢ t ^ kᵢ)ᵢ` at infinitely many
`t`, and `k ≠ 0`, then the indices `i` with `kᵢ` equal to a fixed nonzero exponent form a nonempty
set `I` whose subsum vanishes identically on the curve: the coefficients of the monomial
`t ^ c` in the Laurent polynomial `∑ αᵢ xᵢ t ^ kᵢ` sum to zero for every `c ≠ 0`
(`TauCeti.sum_filter_eq_ite_of_forall_sum_mul_zpow_eq`). Hence no point of such a curve is a
nondegenerate solution. Conversely, if a solution `x` has a vanishing subsum over `I`, then the
curve through `x` with exponent `1` on `I` and `0` elsewhere lies in the hyperplane; this direction
holds over any division semiring. Over an infinite field, a solution is therefore degenerate exactly
when it lies on such a curve with `k ≠ 0` contained in the hyperplane. For solutions with nonzero
coordinates, these curves are the translates of nontrivial one-parameter subgroups.

## Main results

* `TauCeti.exists_finset_submodule_of_not_isNondegenerateSolution`: for nonzero coefficients, at
  most `2 ^ n` proper subspaces contain every degenerate solution of `∑ αᵢ yᵢ = 1`.
* `TauCeti.exists_forall_sum_mul_mul_zpow_eq_zero`: if `∑ αᵢ xᵢ t ^ kᵢ = d` for infinitely many
  `t` and `k ≠ 0`, some nonempty subsum `∑ i ∈ I, αᵢ xᵢ t ^ kᵢ` vanishes for every `t`.
* `TauCeti.not_isNondegenerateSolution_of_forall_sum_mul_mul_zpow_eq_one`: if `k ≠ 0`, no point of
  the curve `t ↦ (xᵢ t ^ kᵢ)ᵢ` lying in the hyperplane `∑ αᵢ yᵢ = 1` at infinitely many parameters
  is a nondegenerate solution.
* `TauCeti.exists_ne_zero_forall_sum_mul_mul_zpow_eq_one`: over a division semiring, a degenerate
  solution `x` lies on a curve `t ↦ (xᵢ t ^ kᵢ)ᵢ`, `k ≠ 0`, contained in the hyperplane.
* `TauCeti.not_isNondegenerateSolution_iff_exists_forall_sum_mul_mul_zpow_eq_one`: over an
  infinite field, the two conditions are equivalent.

## References

* W. M. Schmidt, *Heights of points on subvarieties of `𝔾ₘⁿ`*, in Number Theory (Paris, 1993–1994),
  London Math. Soc. Lecture Note Ser. 235, Cambridge Univ. Press, 1996, 157–187.
* J.-H. Evertse, H. P. Schlickewei, W. M. Schmidt, *Linear equations in variables which lie in a
  multiplicative group*, Ann. of Math. 155 (2002), 807–836, Sections 7 and 11.
-/

public section

open Finset

namespace TauCeti

section SubsumHyperplane

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- **Degenerate solutions lie in boundedly many subsum hyperplanes.** If all `αᵢ` are nonzero,
there are at most `2 ^ n` proper submodules of `Rⁿ`, `n` the number of unknowns, such that every
solution of `∑ αᵢ yᵢ = 1` that is not nondegenerate lies in one of them. They are the kernels of the
linear forms `y ↦ ∑ i ∈ I, αᵢ yᵢ` for nonempty `I`. -/
theorem exists_finset_submodule_of_not_isNondegenerateSolution {α : ι → R}
    (hα : ∀ i, α i ≠ 0) :
    ∃ T : Finset (Submodule R (ι → R)), T.card ≤ 2 ^ Fintype.card ι ∧ (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ y : ι → R, ∑ i, α i * y i = 1 → ¬ IsNondegenerateSolution α y → ∃ V ∈ T, y ∈ V := by
  classical
  -- The linear form `y ↦ ∑ i ∈ I, αᵢ yᵢ`.
  let f : Finset ι → (ι → R) →ₗ[R] R := fun I ↦ ∑ i ∈ I, α i • LinearMap.proj i
  have hf : ∀ I y, f I y = ∑ i ∈ I, α i * y i := fun I y ↦ by
    simp [f, LinearMap.sum_apply]
  refine ⟨(univ.filter Finset.Nonempty).image fun I ↦ LinearMap.ker (f I), ?_, ?_, ?_⟩
  · calc _ ≤ (univ.filter Finset.Nonempty : Finset (Finset ι)).card := card_image_le
      _ ≤ (univ : Finset (Finset ι)).card := card_filter_le _ _
      _ = 2 ^ Fintype.card ι := by rw [card_univ, Fintype.card_finset]
  · simp only [mem_image, mem_filter, mem_univ, true_and]
    rintro _ ⟨I, ⟨j, hj⟩, rfl⟩ htop
    -- The form takes the value `αⱼ ≠ 0` at the `j`-th basis vector.
    have hj0 := hf I (Pi.single j 1)
    rw [LinearMap.ker_eq_top.mp htop] at hj0
    exact hα j (by simpa [Pi.single_apply, hj] using hj0.symm)
  · intro y h1 hy
    obtain ⟨I, hI, hI0⟩ : ∃ I : Finset ι, I.Nonempty ∧ ∑ i ∈ I, α i * y i = 0 := by
      simpa [isNondegenerateSolution_iff, h1] using hy
    exact ⟨_, mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ I, hI⟩),
      LinearMap.mem_ker.mpr ((hf I y).trans hI0)⟩

end SubsumHyperplane

section TorusTranslate

variable {K ι : Type*} [Fintype ι] {α x : ι → K}

section DivisionSemiring

variable [DivisionSemiring K]

/-- **Degenerate solutions lie on coordinate-scaling curves in the hyperplane.** If
`∑ αᵢ xᵢ = 1` and `x` is not a nondegenerate solution, then there is `k ≠ 0`, with entries `0`
and `1`, such that `∑ αᵢ xᵢ t ^ kᵢ = 1` for every `t`. When every `xᵢ` is nonzero, the curve
`t ↦ (xᵢ t ^ kᵢ)ᵢ` is the translate through `x` of a nontrivial one-parameter subgroup. -/
theorem exists_ne_zero_forall_sum_mul_mul_zpow_eq_one (h1 : ∑ i, α i * x i = 1)
    (h : ¬ IsNondegenerateSolution α x) :
    ∃ k : ι → ℤ, k ≠ 0 ∧ ∀ t : K, ∑ i, α i * (x i * t ^ k i) = 1 := by
  classical
  obtain ⟨I, ⟨j, hj⟩, hI0⟩ : ∃ I : Finset ι, I.Nonempty ∧ ∑ i ∈ I, α i * x i = 0 := by
    simpa [isNondegenerateSolution_iff, h1] using h
  -- Scale the coordinates in the vanishing subsum by `t` and keep the others.
  refine ⟨fun i ↦ if i ∈ I then 1 else 0, Function.ne_iff.mpr ⟨j, by simp [hj]⟩, fun t ↦ ?_⟩
  rw [← sum_add_sum_compl I] at h1 ⊢
  rw [hI0, zero_add] at h1
  have hIt : ∑ i ∈ I, α i * (x i * t ^ (if i ∈ I then 1 else 0 : ℤ)) = 0 :=
    calc ∑ i ∈ I, α i * (x i * t ^ (if i ∈ I then 1 else 0 : ℤ))
        = ∑ i ∈ I, α i * x i * t := sum_congr rfl fun i hi ↦ by simp [hi, mul_assoc]
      _ = 0 := by rw [← sum_mul, hI0, zero_mul]
  rw [hIt, zero_add, ← h1]
  exact sum_congr rfl fun i hi ↦ by simp [mem_compl.mp hi]

end DivisionSemiring

variable [Field K]

/-- **A linear form constant on a coordinate-scaling curve has a vanishing subsum.**
If `∑ αᵢ xᵢ t ^ kᵢ = d` for infinitely many `t` and `k ≠ 0`, then there is a nonempty set `I` of
indices such that `∑ i ∈ I, αᵢ xᵢ t ^ kᵢ = 0` for every `t`. One can take for `I` the indices at
which `k` takes a given nonzero value. No coordinate of `x` needs to be nonzero; when all are, the
curve `t ↦ (xᵢ t ^ kᵢ)ᵢ` is the translate through `x` of a one-parameter subgroup. -/
theorem exists_forall_sum_mul_mul_zpow_eq_zero {k : ι → ℤ} (hk : k ≠ 0) {d : K} {S : Set K}
    (hS : S.Infinite) (h : ∀ t ∈ S, ∑ i, α i * (x i * t ^ k i) = d) :
    ∃ I : Finset ι, I.Nonempty ∧ ∀ t : K, ∑ i ∈ I, α i * (x i * t ^ k i) = 0 := by
  classical
  obtain ⟨j, hj : k j ≠ 0⟩ := Function.ne_iff.mp hk
  refine ⟨({i | k i = k j} : Finset ι), ⟨j, by simp⟩, fun t ↦ ?_⟩
  -- The coefficients of the nonconstant monomial `t ^ k j` sum to zero.
  have h0 : ∑ i with k i = k j, α i * x i = 0 := by
    simpa [hj] using sum_filter_eq_ite_of_forall_sum_mul_zpow_eq (c := fun i ↦ α i * x i) hS
      (fun t ht ↦ by simpa only [mul_assoc] using h t ht) (k j)
  calc ∑ i with k i = k j, α i * (x i * t ^ k i)
      = ∑ i with k i = k j, α i * x i * t ^ k j :=
        sum_congr rfl fun i hi ↦ by rw [(mem_filter.mp hi).2, mul_assoc]
    _ = 0 := by rw [← sum_mul, h0, zero_mul]

/-- **Coordinate-scaling curves in the hyperplane consist of degenerate solutions.**
If `k ≠ 0` and `∑ αᵢ xᵢ t ^ kᵢ = 1` for infinitely many `t`, then for every `t` the point
`(xᵢ t ^ kᵢ)ᵢ` is not a nondegenerate solution of `∑ αᵢ yᵢ = 1`. In particular, when every `xᵢ` is
nonzero, this applies to the translate through `x` of a nontrivial one-parameter subgroup. -/
theorem not_isNondegenerateSolution_of_forall_sum_mul_mul_zpow_eq_one {k : ι → ℤ} (hk : k ≠ 0)
    {S : Set K} (hS : S.Infinite) (h : ∀ t ∈ S, ∑ i, α i * (x i * t ^ k i) = 1) (t : K) :
    ¬ IsNondegenerateSolution α fun i ↦ x i * t ^ k i := fun hnd ↦ by
  obtain ⟨I, hI, hI0⟩ := exists_forall_sum_mul_mul_zpow_eq_zero hk hS h
  exact hnd.subsum_ne_zero hI (hI0 t)

/-- **Degenerate solutions are those on coordinate-scaling curves in the hyperplane.** Over an
infinite field, a solution `x` of `∑ αᵢ xᵢ = 1` is not nondegenerate exactly when, for some
`k ≠ 0`, the curve `t ↦ (xᵢ t ^ kᵢ)ᵢ` satisfies `∑ αᵢ xᵢ t ^ kᵢ = 1` for every `t ≠ 0`. When every
`xᵢ` is nonzero, this curve is the translate through `x` of the one-parameter subgroup with
exponents `k`. -/
theorem not_isNondegenerateSolution_iff_exists_forall_sum_mul_mul_zpow_eq_one [Infinite K]
    (h1 : ∑ i, α i * x i = 1) :
    ¬ IsNondegenerateSolution α x ↔
      ∃ k : ι → ℤ, k ≠ 0 ∧ ∀ t : K, t ≠ 0 → ∑ i, α i * (x i * t ^ k i) = 1 := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk, h⟩ ↦ ?_⟩
  · obtain ⟨k, hk, hkt⟩ := exists_ne_zero_forall_sum_mul_mul_zpow_eq_one h1 h
    exact ⟨k, hk, fun t _ ↦ hkt t⟩
  · simpa using not_isNondegenerateSolution_of_forall_sum_mul_mul_zpow_eq_one hk
      (Set.finite_singleton (0 : K)).infinite_compl h 1

end TorusTranslate

end TauCeti
