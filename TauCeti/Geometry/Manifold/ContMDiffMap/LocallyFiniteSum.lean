/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-!
# Locally finite sums of operators into `C^n` functions

Let `Pᵢ` be linear maps from a module `V` into the `C^n` functions on a manifold `M` with values in
a normed algebra `A`, such that for every `f` the supports of the outputs `Pᵢ f` form a locally
finite family. Then `f ↦ ∑ᶠ i, Pᵢ f` is again a linear map into the `C^n` functions
(`ContMDiffMap.locallyFiniteSum`): the sum is smooth because near every point only finitely many
terms are nonzero. Such sums glue operators along a partition of unity, and patch local operators
built in charts into operators on `M`.

The operators are linear over any commutative semiring `R` acting on the `C^n` functions through an
algebra structure, which covers both the scalar field of `M` and the complex scalars acting on
complex-valued functions on a real manifold.

## Main results

* `ContMDiffMap.locallyFiniteSum`: the locally finite sum `f ↦ ∑ᶠ i, Pᵢ f` of linear maps into
  the `C^n` functions.
* `ContMDiffMap.locallyFiniteSum_apply_eq_sum`: at a point of a compact set `K`, the sum is the
  finite sum over the indices whose output supports `Sᵢ` meet `K`.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [ContMDiffRing 𝓘(𝕜, A) n A]
  {R : Type*} [CommSemiring R] [Algebra R C^n⟮I, M; 𝓘(𝕜, A), A⟯]
  {V : Type*} [AddCommMonoid V] [Module R V] {ι : Type*}

/-- The **locally finite sum** `f ↦ ∑ᶠ i, Pᵢ f` of linear maps `Pᵢ` into the `C^n` functions on `M`,
when for every `f` the supports of the outputs `Pᵢ f` form a locally finite family. -/
def locallyFiniteSum (P : ι → V →ₗ[R] C^n⟮I, M; 𝓘(𝕜, A), A⟯)
    (hP : ∀ f, LocallyFinite fun i ↦ Function.support (P i f)) :
    V →ₗ[R] C^n⟮I, M; 𝓘(𝕜, A), A⟯ :=
  -- The sum of the outputs, a `C^n` function since their supports are locally finite.
  let F (f : V) : C^n⟮I, M; 𝓘(𝕜, A), A⟯ :=
    ⟨fun x ↦ ∑ᶠ i, P i f x, contMDiff_finsum (fun i ↦ (P i f).contMDiff) (hP f)⟩
  { toFun := F
    map_add' f g := by
      ext x
      simp only [F, ContMDiffMap.coeFn_mk, map_add, ContMDiffMap.coe_add, Pi.add_apply]
      exact finsum_add_distrib ((hP f).point_finite x) ((hP g).point_finite x)
    map_smul' c f := by
      ext x
      -- Evaluate the scalar multiple while `F f` still has the type of `C^n` maps.
      rw [RingHom.id_apply, Algebra.smul_def, ContMDiffMap.coe_mul, Pi.mul_apply]
      simp only [F, ContMDiffMap.coeFn_mk, map_smul, Algebra.smul_def, ContMDiffMap.coe_mul,
        Pi.mul_apply]
      exact (mul_finsum' _ _ ((hP f).point_finite x)).symm }

variable {P : ι → V →ₗ[R] C^n⟮I, M; 𝓘(𝕜, A), A⟯}
  {hP : ∀ f, LocallyFinite fun i ↦ Function.support (P i f)}

/-- A locally finite sum of operators is evaluated pointwise as a `finsum`. -/
@[simp]
theorem locallyFiniteSum_apply (f : V) (x : M) :
    locallyFiniteSum P hP f x = ∑ᶠ i, P i f x :=
  (rfl)

/-- At a point of a compact set `K`, a locally finite sum of operators with outputs supported in
the sets `Sᵢ` is the finite sum over the indices with `Sᵢ` meeting `K`. -/
theorem locallyFiniteSum_apply_eq_sum {S : ι → Set M} (hS : LocallyFinite S)
    (hsupp : ∀ i f, tsupport (P i f) ⊆ S i) {K : Set M} (hK : IsCompact K) (f : V) {x : M}
    (hx : x ∈ K) :
    locallyFiniteSum P hP f x =
      ∑ i ∈ (hS.finite_nonempty_inter_compact hK).toFinset, P i f x :=
  finsum_eq_sum_of_support_subset _ fun i hi ↦
    (hS.finite_nonempty_inter_compact hK).mem_toFinset.2 ⟨x, hsupp i f (subset_tsupport _ hi), hx⟩

end ContMDiffMap
