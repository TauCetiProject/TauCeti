/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.GradedModule
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.LinearAlgebra.Graded.LinearMap

/-!
# Differential graded left modules

Let `d` be a differential on an internally `ℤ`-graded `R`-algebra `𝒜` on a carrier `A`, in the
sense of `TauCeti.IsDGAlgebra`.  A **differential graded left module** over it is an `A`-module `M`
with an internal `ℤ`-grading `ℳ` for which the action adds degrees, together with an `R`-linear
differential `dM` of degree `+1`, in the sense of `TauCeti.LinearMap.IsHomogeneous`, which squares
to zero and satisfies the graded Leibniz rule

`dM (a • x) = d a • x + (-1) ^ |a| • (a • dM x)`.

Only a homogeneous scalar `a` is constrained by the Leibniz axiom, because the sign depends on its
degree alone; this is the exact shape of `TauCeti.IsDGAlgebra.leibniz`, and indeed a differential
graded algebra is a differential graded left module over itself.  Decomposing a scalar into
homogeneous components removes the hypothesis whenever the sign is multiplied by something that
vanishes: the differential of `a • x` is `d a • x` as soon as `x` is a cycle, so a cycle acts on
cycles and the cycles of `A` carry the boundaries of `M` into themselves.

The grading is stored internally, as a family `ℳ : ℤ → Submodule R M` with Mathlib's
`DirectSum.Decomposition ℳ` and `SetLike.GradedSMul 𝒜 ℳ`.  This matches the presentation of
`TauCeti.IsDGAlgebra`, so the action is the given `A`-action on `M` and no signed totalization
intervenes.  The ground ring acts through the algebra, `IsScalarTower R A M`: the `R`-module
structure which carries the grading and the linearity of `dM` is the restriction of the `A`-action
along `algebraMap R A`, so there is only one action of `R` in play.

## Handedness

The handedness is part of the name: this file defines the left interface and says nothing about
the right one, whose Leibniz rule `dM (x • a) = dM x • a + (-1) ^ |x| • (x • d a)` is a separate
axiom system, on an `Aᵐᵒᵖ`-module.  Turning one into the other needs the sign-twisted graded
opposite `a *ᵒᵖ b = (-1) ^ (|a| * |b|) • (b * a)`.  The unsigned `MulOpposite` will not do:
with `a *ᵒᵖ b = b * a` the Leibniz rule for `*ᵒᵖ` asks for
`d (b * a) = b * d a + (-1) ^ |a| • (d b * a)`, while the rule in `A` gives
`d (b * a) = d b * a + (-1) ^ |b| • (b * d a)`.  So no reduction between the two handednesses is
claimed here.  The left handedness is the one Mathlib's `Module A M` gives directly, and the one
whose Leibniz sign depends on the same factor as `TauCeti.IsDGAlgebra.leibniz`, which is what lets
a differential graded algebra be a module over itself with no twist.

## Main definitions

* `TauCeti.IsDGLeftModule`: the differential graded left module axioms on an internally `ℤ`-graded
  module over a differential graded algebra and an `R`-linear endomorphism of its carrier.

## Main results

* `TauCeti.IsDGLeftModule.map_decompose`: the differential commutes with the homogeneous
  projections of the grading, `dM (x_p) = (dM x)_{p + 1}`; in particular the homogeneous components
  of a cycle are cycles and those of a boundary are boundaries.
* `TauCeti.IsDGLeftModule.leibniz_of_map_eq_zero`: the Leibniz rule for an arbitrary scalar against
  a cycle, with no sign and no homogeneity hypothesis.
* `TauCeti.IsDGLeftModule.smul_mem_range_of_map_eq_zero`: a cycle of `A` carries a boundary of `M`
  to a boundary, and `TauCeti.IsDGLeftModule.map_smul_mem_range_of_map_eq_zero`: a boundary of `A`
  carries a cycle of `M` to a boundary.
* `TauCeti.IsDGAlgebra.isDGLeftModule`: **a differential graded algebra is a differential graded
  left module over itself.**
* `TauCeti.isDGLeftModule_zero`: a graded module with zero differential over a graded algebra with
  zero differential is a differential graded left module.

The specializations of these results to the algebra acting on itself are in
`TauCeti.Algebra.Homology.DG.Algebra.SelfModule`, and the cycles, boundaries and cohomology module
are built on this file in `TauCeti.Algebra.Homology.DG.Module.Cohomology`.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open DirectSum

namespace TauCeti

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

/-- A **differential graded left module** over the differential graded algebra `(𝒜, d)`: an
internally `ℤ`-graded `A`-module `ℳ` on a carrier `M`, whose action adds degrees, with an `R`-linear
map `dM` which raises degree by one, squares to zero, and satisfies the graded Leibniz rule on a
homogeneous scalar.  The sign `(-1) ^ p` is `Int.negOnePow p`, acting through the units of `ℤ`. -/
structure IsDGLeftModule [IsScalarTower R A M] (h : IsDGAlgebra 𝒜 d) (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M) : Prop where
  /-- The differential raises the degree by one. -/
  isHomogeneous : LinearMap.IsHomogeneous dM ℳ ℳ 1
  /-- The differential squares to zero. -/
  sq_zero (x : M) : dM (dM x) = 0
  /-- The graded Leibniz rule for a scalar of degree `p`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : M,
    dM (a • x) = d a • x + p.negOnePow • (a • dM x)

/-- **A differential graded algebra is a differential graded left module over itself.**  The Leibniz
rule is the one of the algebra, read through `smul_eq_mul`. -/
theorem IsDGAlgebra.isDGLeftModule (h : IsDGAlgebra 𝒜 d) : IsDGLeftModule h 𝒜 d where
  isHomogeneous := LinearMap.isHomogeneous_def.mpr fun _ _ ha ↦ h.map_mem ha
  sq_zero := h.sq_zero
  leibniz ha b := by simpa only [smul_eq_mul] using h.leibniz ha b

variable {h : IsDGAlgebra 𝒜 d} {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}

namespace IsDGLeftModule

/-- The differential of a differential graded left module commutes with the homogeneous projections
of the grading, up to the shift by one that it applies to degrees. -/
theorem map_decompose (hM : IsDGLeftModule h ℳ dM) (p : ℤ) (x : M) :
    dM (decompose ℳ x p : M) = (decompose ℳ (dM x) (p + 1) : M) :=
  DirectSum.map_decompose_shift ℳ ℳ dM (· + 1) (add_left_injective 1)
    (fun _ _ hy ↦ hM.isHomogeneous.map_mem hy) p x

/-- Every homogeneous projection of a boundary is again a boundary. -/
theorem decompose_mem_range (hM : IsDGLeftModule h ℳ dM) {x : M} (hx : x ∈ LinearMap.range dM)
    (p : ℤ) : (decompose ℳ x p : M) ∈ LinearMap.range dM := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(decompose ℳ y (p - 1) : M), ?_⟩
  have key := hM.map_decompose (p - 1) y
  rw [sub_add_cancel p (1 : ℤ)] at key
  exact key

/-- The homogeneous components of a cycle are cycles. -/
theorem map_decompose_eq_zero (hM : IsDGLeftModule h ℳ dM) {x : M} (hx : dM x = 0) (p : ℤ) :
    dM (decompose ℳ x p : M) = 0 := by
  rw [hM.map_decompose, hx, DirectSum.decompose_zero, DirectSum.zero_apply,
    ZeroMemClass.coe_zero]

/-- The Leibniz rule against a cycle: the sign disappears with the term it multiplies, so the
scalar need not be homogeneous. -/
theorem leibniz_of_map_eq_zero (hM : IsDGLeftModule h ℳ dM) (a : A) {x : M} (hx : dM x = 0) :
    dM (a • x) = d a • x := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_smul, map_sum]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hM.leibniz (SetLike.coe_mem _) x, hx, smul_zero, smul_zero, add_zero]

/-- A cycle of the algebra acts on a cycle of the module to give a cycle. -/
theorem map_smul_eq_zero_of_map_eq_zero (hM : IsDGLeftModule h ℳ dM) {a : A} {x : M}
    (ha : d a = 0) (hx : dM x = 0) : dM (a • x) = 0 := by
  rw [hM.leibniz_of_map_eq_zero a hx, ha, zero_smul]

/-- A homogeneous cycle of the algebra acting on a differential is, up to the sign of its degree,
the differential of the action. -/
theorem smul_map_eq_negOnePow_smul_map_smul (hM : IsDGLeftModule h ℳ dM) {p : ℤ} {a : A}
    (ha : a ∈ 𝒜 p) (hda : d a = 0) (x : M) :
    a • dM x = p.negOnePow • dM (a • x) := by
  simp only [hM.leibniz ha x, hda, zero_smul, zero_add, smul_smul, Int.units_mul_self, one_smul]

/-- A cycle of the algebra carries a boundary of the module to a boundary.  Componentwise this is
the Leibniz rule read backwards: `a • dM x = (-1) ^ |a| * dM (a • x)` for a homogeneous cycle `a`.
-/
theorem smul_mem_range_of_map_eq_zero (hM : IsDGLeftModule h ℳ dM) {a : A} (ha : d a = 0) {y : M}
    (hy : y ∈ LinearMap.range dM) : a • y ∈ LinearMap.range dM := by
  classical
  obtain ⟨x, rfl⟩ := hy
  rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_smul]
  refine Submodule.sum_mem _ fun p _ => ⟨p.negOnePow • ((decompose 𝒜 a p : A) • x), ?_⟩
  rw [Units.smul_def, map_zsmul, ← Units.smul_def]
  exact (hM.smul_map_eq_negOnePow_smul_map_smul (SetLike.coe_mem _)
    (h.isDGLeftModule.map_decompose_eq_zero ha p) x).symm

/-- A boundary of the algebra carries a cycle of the module to a boundary: `d a • x` is the
differential of `a • x`. -/
theorem map_smul_mem_range_of_map_eq_zero (hM : IsDGLeftModule h ℳ dM) (a : A) {x : M}
    (hx : dM x = 0) : d a • x ∈ LinearMap.range dM :=
  ⟨a • x, hM.leibniz_of_map_eq_zero a hx⟩

end IsDGLeftModule

/-- A graded module with zero differential over a graded algebra with zero differential is a
differential graded left module. -/
theorem isDGLeftModule_zero (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] :
    IsDGLeftModule (isDGAlgebra_zero 𝒜) ℳ (0 : M →ₗ[R] M) where
  isHomogeneous := LinearMap.isHomogeneous_zero ℳ ℳ 1
  sq_zero _ := rfl
  leibniz := fun _ _ => by simp

end TauCeti
