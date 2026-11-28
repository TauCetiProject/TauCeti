/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Regular.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Linear maps that are diagonal in a pair of bases

Let `b` and `b'` be bases of `M` and `N` indexed by the same type, and let `g : M →ₗ[R] N` send
each basis vector `b i` to a scalar multiple `w i • b' i`. Over a commutative semiring, the
coordinates of `g x` in `b'` are those of `x` in `b` multiplied by the weights `w`. Hence `g` is
injective exactly when every weight is left regular (multiplication by it is injective), its range
consists of the vectors whose `i`-th coordinate is divisible by `w i`, and `g` is surjective
exactly when every weight is a unit. No finiteness of the index type is needed.

A map sending each `b i` to `w i • b' (σ i)` for a permutation `σ` of the indices is of this form
for the reindexed basis `b'.reindex σ.symm`.

## Main results

* `Module.Basis.repr_apply_eq_mul_of_apply_eq_smul`: the coordinates of `g x` are `w i` times
  those of `x`.
* `Module.Basis.injective_iff_forall_isLeftRegular_of_apply_eq_smul`: `g` is injective if and only
  if every weight is left regular.
* `Module.Basis.mem_range_iff_of_apply_eq_smul`: `y` is in the range of `g` if and only if each
  coordinate `b'.repr y i` is divisible by `w i`.
* `Module.Basis.surjective_iff_forall_isUnit_of_apply_eq_smul`: `g` is surjective if and only if
  every weight is a unit.
-/

public section

namespace Module.Basis

variable {ι R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] (b : Basis ι R M) (b' : Basis ι R N) {g : M →ₗ[R] N} {w : ι → R}

/-- If a linear map sends each basis vector `b i` to `w i • b' i`, then the `i`-th coordinate of
`g x` in `b'` is `w i` times the `i`-th coordinate of `x` in `b`. -/
theorem repr_apply_eq_mul_of_apply_eq_smul (hg : ∀ i, g (b i) = w i • b' i) (x : M) (i : ι) :
    b'.repr (g x) i = w i * b.repr x i := by
  have key : Finsupp.lapply i ∘ₗ b'.repr.toLinearMap ∘ₗ g =
      w i • (Finsupp.lapply i ∘ₗ b.repr.toLinearMap) :=
    b.ext fun j => by
      rcases eq_or_ne j i with rfl | hji
      · simp [hg]
      · simp [hg, hji]
  simpa using LinearMap.congr_fun key x

/-- A linear map sending each basis vector `b i` to `w i • b' i` is injective if and only if
every weight `w i` is left regular. -/
theorem injective_iff_forall_isLeftRegular_of_apply_eq_smul (hg : ∀ i, g (b i) = w i • b' i) :
    Function.Injective g ↔ ∀ i, IsLeftRegular (w i) := by
  refine ⟨fun h i a c hac => ?_, fun h x y hxy => b.ext_elem fun i => h i ?_⟩
  · have hgac : g (a • b i) = g (c • b i) := by
      simp only [map_smul, hg, smul_smul, mul_comm _ (w i)]
      exact congrArg (· • b' i) hac
    simpa using congrArg (fun x => b.repr x i) (h hgac)
  · simpa [b.repr_apply_eq_mul_of_apply_eq_smul b' hg] using congrArg (fun z => b'.repr z i) hxy

/-- A vector `y` lies in the range of a linear map sending each basis vector `b i` to
`w i • b' i` if and only if each coordinate `b'.repr y i` is divisible by `w i`. -/
theorem mem_range_iff_of_apply_eq_smul (hg : ∀ i, g (b i) = w i • b' i) (y : N) :
    y ∈ LinearMap.range g ↔ ∀ i, w i ∣ b'.repr y i := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨x, rfl⟩ i
    rw [b.repr_apply_eq_mul_of_apply_eq_smul b' hg]
    exact dvd_mul_right _ _
  · rw [← b'.linearCombination_repr y, Finsupp.linearCombination_apply]
    refine Submodule.finsuppSum_mem _ _ (b'.repr y) _ fun i _ => ?_
    obtain ⟨a, ha⟩ := h i
    exact ⟨a • b i, by rw [map_smul, hg, smul_smul, ha, mul_comm]⟩

/-- A linear map sending each basis vector `b i` to `w i • b' i` is surjective if and only if
every weight `w i` is a unit. -/
theorem surjective_iff_forall_isUnit_of_apply_eq_smul (hg : ∀ i, g (b i) = w i • b' i) :
    Function.Surjective g ↔ ∀ i, IsUnit (w i) := by
  rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
  simp_rw [b.mem_range_iff_of_apply_eq_smul b' hg]
  exact ⟨fun h i => isUnit_of_dvd_one (by simpa using h (b' i) i), fun h _ i => (h i).dvd⟩

end Module.Basis
