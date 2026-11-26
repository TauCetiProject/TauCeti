/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Continuous linear maps on products and Pi types

This file collects supplementary results about continuous linear maps on indexed products `ι → R`.

## Main results

* `ContinuousLinearMap.eq_smul_id_of_unique`: every continuous linear endomorphism of a
  one-coordinate space `ι → R` over a topological commutative semiring `R` with continuous scalar
  multiplication is a scalar multiple of the identity.
* `ContinuousLinearMap.update_proj_apply`: the family `Function.update (fun m ↦ proj m) i α`,
  which replaces the projection to the coordinate `i` by `α`, evaluates at `j` and `v` to the
  coordinate `j` of `Function.update v i (α v)`.
* `ContinuousLinearMap.pi_ext_one`: a continuous linear map on a finite coordinate space `ι → R`
  is determined by its values at the coordinate vectors `Pi.single i 1`.
* `ContinuousLinearMap.mem_ker_pi_proj_comp`: a vector lies in the kernel of the coordinates of
  `q` labelled by a set `t` exactly when these coordinates of `q` vanish at it.
-/

public section

namespace ContinuousLinearMap

section CommSemiring

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- Every continuous linear endomorphism of a one-coordinate space `ι → R` is a scalar multiple of
the identity. -/
theorem eq_smul_id_of_unique {ι : Type*} [Unique ι] [ContinuousConstSMul R R]
    (T : (ι → R) →L[R] (ι → R)) :
    T = T (fun _ ↦ 1) default • ContinuousLinearMap.id R (ι → R) := by
  ext v i
  have hv : v = v default • (fun _ : ι ↦ (1 : R)) := by
    ext j
    simp [Unique.eq_default j]
  conv_lhs => rw [hv]
  simp [Unique.eq_default i, mul_comm]

end CommSemiring

/-- Evaluating the family `Function.update (fun m ↦ proj m) i α`, which replaces the projection to
the coordinate `i` by the continuous linear map `α`, at `j` and `v` gives the coordinate `j` of
`Function.update v i (α v)`. With `ContinuousLinearMap.coe_pi'`, `simp` uses it to evaluate
`pi (Function.update (fun m ↦ proj m) i α) v`. -/
@[simp]
theorem update_proj_apply {ι R : Type*} [DecidableEq ι] [Semiring R]
    {φ : ι → Type*} [∀ m, TopologicalSpace (φ m)] [∀ m, AddCommMonoid (φ m)] [∀ m, Module R (φ m)]
    (i : ι) (α : (∀ m, φ m) →L[R] φ i) (j : ι) (v : ∀ m, φ m) :
    Function.update (fun m ↦ proj m) i α j v = Function.update v i (α v) j :=
  Function.apply_update (fun _ g ↦ g v) (fun m ↦ proj m) i α j

/-- A continuous linear map on a finite coordinate space `ι → R` is determined by its values at the
coordinate vectors `Pi.single i 1`. -/
theorem pi_ext_one {ι R M : Type*} [Finite ι] [DecidableEq ι] [Semiring R] [TopologicalSpace R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] {f g : (ι → R) →L[R] M}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g :=
  coe_injective (LinearMap.pi_ext' fun i ↦ LinearMap.ext_ring (h i))

section Pi

variable {R M ι : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {φ : ι → Type*} [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)]

/-- A vector lies in the kernel of the coordinates of `q` labelled by a set `t` exactly when
these coordinates of `q` vanish at it. -/
theorem mem_ker_pi_proj_comp {q : M →L[R] ∀ i, φ i} {t : Set ι} {v : M} :
    v ∈ (pi fun i : t ↦ (proj (i : ι)).comp q).ker ↔ ∀ i ∈ t, q v i = 0 := by
  rw [LinearMap.mem_ker, funext_iff, Subtype.forall]
  simp only [coe_coe, pi_apply, comp_apply, proj_apply, Pi.zero_apply]

end Pi

end ContinuousLinearMap
