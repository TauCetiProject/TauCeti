/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Algebra.Defs
public import TauCeti.Algebra.Homology.DG.Module.Defs

/-!
# Curved differential graded left modules

A curved differential graded left module over a curved differential graded algebra `(A, d, w)`
has a degree-one differential satisfying the graded Leibniz rule

`dM (a • x) = d a • x + (-1) ^ |a| • (a • dM x)`

and the curvature equation `dM (dM x) = -(w • x)`.

The curvature `w` is stored in the right-module convention `d (d a) = a * w - w * a`, under which
a right curved module satisfies `dM (dM x) = x * w`. A left module is the same thing as a right
module over the Koszul-signed graded opposite, whose curvature is `-op w`; reading the
right-module square there gives the left-module square `-(w • x)`, not `w • x`. This comparison
is `TauCeti.isCurvedDGLeftModule_iff_gradedOppositeRight`. In Positselski's convention, with
curvature `h = -w`, the left-module equation is his `d² (m) = h * m`.

## Main definitions

* `TauCeti.IsCurvedDGLeftModule`: the curved differential graded left-module axioms.

## Main results

* `TauCeti.IsCurvedDGLeftModule.map_curvature_smul`: the curvature action commutes with the
  module differential.
* `TauCeti.IsCurvedDGLeftModule.toIsDGLeftModule_of_curvature_eq_zero`: zero curvature turns a
  curved left module into an ordinary differential graded left module.
* `TauCeti.isCurvedDGLeftModule_zero_iff`: the curved and ordinary notions agree at curvature
  zero.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 6.2.
  His curvature is the negative of the right-module curvature used here.
-/

public section

open DirectSum

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}

/-- A **curved differential graded left module** over the curved differential graded algebra
`(𝒜, d, w)`. Its differential raises degree by one, obeys the left graded Leibniz rule, and
squares to minus left multiplication by the curvature: the curvature `w` is stored in the
right-module convention, and the left-module square carries the opposite sign. -/
structure IsCurvedDGLeftModule [IsScalarTower R A M] (h : IsCurvedDGAlgebra 𝒜 d w)
    (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] (dM : M →ₗ[R] M) : Prop where
  /-- The differential raises degree by one. -/
  isHomogeneous : LinearMap.IsHomogeneous dM ℳ ℳ 1
  /-- The graded left Leibniz rule for a scalar of degree `p`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : M,
    dM (a • x) = d a • x + p.negOnePow • (a • dM x)
  /-- The differential squares to minus left multiplication by the curvature. -/
  sq_eq (x : M) : dM (dM x) = -(w • x)

variable {h : IsCurvedDGAlgebra 𝒜 d w} {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}

namespace IsCurvedDGLeftModule

/-- The differential of a curved differential graded left module commutes with homogeneous
projections, up to its degree-one shift. -/
@[simp]
theorem map_decompose (hM : IsCurvedDGLeftModule h ℳ dM) (p : ℤ) (x : M) :
    dM (decompose ℳ x p : M) = (decompose ℳ (dM x) (p + 1) : M) :=
  DirectSum.map_decompose_shift ℳ ℳ dM (· + 1) (add_left_injective 1)
    (fun _ _ hy ↦ hM.isHomogeneous.map_mem hy) p x

/-- The left Leibniz rule against a module element killed by the differential. The signed term
vanishes, so the scalar need not be homogeneous. -/
theorem leibniz_of_map_eq_zero (hM : IsCurvedDGLeftModule h ℳ dM) (a : A) {x : M}
    (hx : dM x = 0) : dM (a • x) = d a • x := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a, Finset.sum_smul, map_sum]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 a, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [hM.leibniz (SetLike.coe_mem _) x, hx, smul_zero, smul_zero, add_zero]

/-- The curvature action commutes with the module differential: the curvature is a cycle of even
degree. -/
theorem map_curvature_smul (hM : IsCurvedDGLeftModule h ℳ dM) (x : M) :
    dM (w • x) = w • dM x := by
  rw [hM.leibniz h.curvature_mem x, h.map_curvature, zero_smul, zero_add,
    Int.negOnePow_even 2 even_two, one_smul]

/-- A curved differential graded left module whose curvature is zero is an ordinary differential
graded left module. -/
theorem toIsDGLeftModule_of_curvature_eq_zero (hM : IsCurvedDGLeftModule h ℳ dM) (hw : w = 0) :
    IsDGLeftModule (h.toIsDGAlgebra_of_curvature_eq_zero hw) ℳ dM where
  isHomogeneous := hM.isHomogeneous
  sq_zero x := by rw [hM.sq_eq, hw, zero_smul, neg_zero]
  leibniz := hM.leibniz

end IsCurvedDGLeftModule

variable {hDG : IsDGAlgebra 𝒜 d}

/-- An ordinary differential graded left module is a curved one with curvature zero. -/
theorem IsDGLeftModule.isCurvedDGLeftModule_zero (hM : IsDGLeftModule hDG ℳ dM) :
    IsCurvedDGLeftModule hDG.isCurvedDGAlgebra_zero ℳ dM where
  isHomogeneous := hM.isHomogeneous
  leibniz := hM.leibniz
  sq_eq x := by rw [hM.sq_zero, zero_smul, neg_zero]

/-- **Zero curvature.** Curved differential graded left modules over an algebra of curvature
zero are exactly ordinary differential graded left modules. -/
theorem isCurvedDGLeftModule_zero_iff :
    IsCurvedDGLeftModule hDG.isCurvedDGAlgebra_zero ℳ dM ↔ IsDGLeftModule hDG ℳ dM :=
  ⟨fun hM ↦ hM.toIsDGLeftModule_of_curvature_eq_zero rfl,
    IsDGLeftModule.isCurvedDGLeftModule_zero⟩

end TauCeti
