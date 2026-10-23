/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowerAlgebra.Augmentation
public import TauCeti.RingTheory.DividedPowerAlgebra.Homogeneous
import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The direct-sum grading of the divided power algebra

For a module `M` over a commutative semiring `R`, the homogeneous pieces `Γ^d_R(M)` of
`DividedPowerAlgebra R M` (see `DividedPowerAlgebra.homogeneousSubmodule`) form an internal
direct sum: every element is uniquely a finite sum of homogeneous elements. Together with the
multiplicativity of the pieces this makes `DividedPowerAlgebra R M` an `ℕ`-graded `R`-algebra, in
which `dp R d m` has degree `d`. In particular `DirectSum.decomposeLinearEquiv` identifies
`DividedPowerAlgebra R M` with `⨁ d, Γ^d_R(M)`, and its inverse is the sum map.

No freeness, finiteness or characteristic hypothesis is imposed. The degree-zero projection of
the grading is the augmentation followed by the structure map `R → Γ_R(M)`.

## Main declarations

* `DividedPowerAlgebra.isInternal_homogeneousSubmodule`: the homogeneous pieces form an internal
  direct sum.
* `DividedPowerAlgebra.instGradedAlgebra`: the resulting `ℕ`-graded algebra structure.
* `DividedPowerAlgebra.decompose_dp`: `dp R d m` is homogeneous of degree `d`.
* `DividedPowerAlgebra.coe_decompose_apply_zero`: the degree-zero component is
  `algebraMap R _ ∘ augmentation R M`.

## Implementation notes

Directness cannot be obtained by dividing by factorials: over `ZMod 2`, `dp 1 1 ^ 2 = 0` while
`dp 2 1 ≠ 0`. Instead, giving the generator `dp R n m` the weight `n` defines an algebra map
`DividedPowerAlgebra R M → (DividedPowerAlgebra R M)[X]`, `dp R n m ↦ dp R n m • X ^ n`, through
the universal property `DividedPowerAlgebra.lift'`. It is multiplication by `X ^ d` on the
degree-`d` piece, so the `X ^ d`-coefficient of its value recovers the degree-`d` component of a
sum of homogeneous elements.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  III §§1–2][Roby-1963]
* The ambient `DividedPowerAlgebra`, its generators and `lift'` are the Mathlib formalization by
  Antoine Chambert-Loir and María Inés de Frutos-Fernández.
-/

public section

noncomputable section

namespace DividedPowerAlgebra

open Polynomial

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The algebra map recording the grading: it sends `dp R n m` to the monomial
`dp R n m • X ^ n`, so the `X ^ d`-coefficient of its value is the degree-`d` component. -/
private def weightMap : DividedPowerAlgebra R M →ₐ[R] (DividedPowerAlgebra R M)[X] :=
  lift' (f := fun nm ↦ monomial nm.1 (dp R nm.1 nm.2))
    (fun m ↦ by simp [dp_zero])
    (fun n r m ↦ by rw [dp_smul, smul_monomial])
    (fun n p m ↦ by rw [monomial_mul_monomial, dp_mul, smul_monomial])
    (fun n u v ↦ by
      rw [dp_add, map_sum]
      refine Finset.sum_congr rfl fun ⟨k, l⟩ hk ↦ ?_
      dsimp only
      rw [monomial_mul_monomial, Finset.mem_antidiagonal.mp hk])

private theorem weightMap_dp (n : ℕ) (m : M) :
    weightMap (dp R n m) = monomial n (dp R n m) :=
  lift'_apply_dp ..

/-- On the degree-`d` piece, `weightMap` is multiplication by `X ^ d`. -/
private theorem weightMap_of_mem {d : ℕ} {x : DividedPowerAlgebra R M}
    (hx : x ∈ homogeneousSubmodule (R := R) (M := M) d) :
    weightMap x = monomial d x := by
  induction hx using homogeneousSubmodule_induction with
  | prod_dp l hl =>
      subst hl
      induction l with
      | nil => simp
      | cons nm l ih => simp [map_mul, weightMap_dp, ih, monomial_mul_monomial]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => rw [map_smul, hx, smul_monomial]

/-- The `X ^ e`-coefficient of `weightMap` applied to a sum of homogeneous elements is its
degree-`e` term. -/
private theorem coeff_weightMap_coeLinearMap
    (y : DirectSum ℕ fun d ↦ homogeneousSubmodule (R := R) (M := M) d) (e : ℕ) :
    (weightMap (DirectSum.coeLinearMap _ y)).coeff e = y e := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | of d z =>
      rw [DirectSum.coeLinearMap_of, weightMap_of_mem z.2, coeff_monomial]
      by_cases h : d = e
      · subst h
        simp
      · simp [h, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add y z hy hz => simp [hy, hz]

/-- Every element of the divided power algebra is a sum of homogeneous elements. -/
private theorem iSup_homogeneousSubmodule_eq_top :
    ⨆ d, homogeneousSubmodule (R := R) (M := M) d = ⊤ := by
  rw [eq_top_iff]
  intro x hx
  clear hx
  induction x using DividedPowerAlgebra.induction_on with
  | C r => exact Submodule.mem_iSup_of_mem 0 (SetLike.algebraMap_mem_graded _ r)
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | dp x n m hx =>
      refine Submodule.iSup_induction _
        (motive := fun x ↦ x * dp R n m ∈ ⨆ d, homogeneousSubmodule (R := R) (M := M) d) hx
        (fun d x hx ↦ ?_) (by simp) (fun x y hx hy ↦ ?_)
      · exact Submodule.mem_iSup_of_mem (d + n)
          (mul_mem_homogeneousSubmodule hx (dp_mem_homogeneousSubmodule n m))
      · rw [add_mul]
        exact Submodule.add_mem _ hx hy

/-- The homogeneous pieces of the divided power algebra form an internal direct sum: the sum
map `⨁ d, Γ^d_R(M) → Γ_R(M)` is bijective. -/
theorem isInternal_homogeneousSubmodule :
    DirectSum.IsInternal (homogeneousSubmodule (R := R) (M := M)) := by
  refine ⟨fun y z h ↦ ?_, ?_⟩
  · ext e
    rw [← coeff_weightMap_coeLinearMap, ← coeff_weightMap_coeLinearMap]
    exact congrArg (fun x ↦ (weightMap x).coeff e) h
  · exact (LinearMap.range_eq_top
      (f := DirectSum.coeLinearMap (homogeneousSubmodule (R := R) (M := M)))).mp
      (by rw [DirectSum.range_coeLinearMap, iSup_homogeneousSubmodule_eq_top])

/-- The divided power algebra is an `ℕ`-graded algebra, with degree-`d` piece
`homogeneousSubmodule R M d`. -/
instance instGradedAlgebra : GradedAlgebra (homogeneousSubmodule (R := R) (M := M)) where
  __ := isInternal_homogeneousSubmodule.chooseDecomposition
  __ := instGradedMonoid

/-- The divided-power generator `dp R d m` is homogeneous of degree `d`. -/
@[simp]
theorem decompose_dp (d : ℕ) (m : M) :
    DirectSum.decompose (homogeneousSubmodule (R := R) (M := M)) (dp R d m) =
      DirectSum.of _ d ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ :=
  DirectSum.decompose_of_mem _ _

/-- The degree-zero component of an element is its augmentation, viewed in `Γ_R(M)` through the
structure map. Thus the degree-zero projection `GradedRing.projZeroRingHom` is the identity on
scalars and kills every positive homogeneous piece. -/
@[simp]
theorem coe_decompose_apply_zero (x : DividedPowerAlgebra R M) :
    (DirectSum.decompose (homogeneousSubmodule (R := R) (M := M)) x 0 : DividedPowerAlgebra R M) =
      algebraMap R _ (augmentation R M x) := by
  induction x using DividedPowerAlgebra.induction_on with
  | C r =>
      rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        DirectSum.decompose_of_mem_same]
      exact SetLike.algebraMap_mem_graded (homogeneousSubmodule (R := R) (M := M)) r
  | add x y hx hy => simp [hx, hy]
  | dp x n m hx =>
      -- Pass to the degree-zero projection, which is multiplicative.
      rw [← GradedRing.projZeroRingHom_apply] at hx ⊢
      rw [map_mul, hx, map_mul, map_mul, GradedRing.projZeroRingHom_apply, decompose_dp,
        augmentation_dp]
      rcases eq_or_ne n 0 with rfl | hn
      · simp [dp_zero]
      · simp [hn, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hn)]

end DividedPowerAlgebra
