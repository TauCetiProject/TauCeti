/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Cyclic.Affine
public import Mathlib.RepresentationTheory.Homological.FiniteCyclic

/-!
# Norm and difference maps for a periodic additive automorphism

The partial norms of an additive automorphism are additive endomorphisms
`AddEquiv.cyclicNormHom`. The difference endomorphisms `AddEquiv.oneSubPow` use the convention
`1 - A^k`, suited to translation conjugacy and fixed-point equations for affine actions.

For a periodic automorphism, these maps are the differentials of Mathlib's cyclic short
complexes `Rep.FiniteCyclicGroup.normHomCompSub` and `Rep.FiniteCyclicGroup.subCompNormHom`,
with the difference differential negated. The comparison lemmas identify the actual maps, not
just their kernels or ranges. Both composites vanish. No new short complex or cohomology
carrier is introduced.

In period two the maps are `1 + A` and `1 - A`. All results hold for arbitrary additive
commutative groups, including groups with 2-torsion; no division by two is involved.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter VI, §2, for the periodic cyclic resolution.
-/

public section

open CategoryTheory

namespace AddEquiv

variable {T : Type*} [AddCommGroup T]

/-- The partial cyclic norm as an additive endomorphism, with no periodicity assumption. -/
def cyclicNormHom (A : T ≃+ T) (k : ℕ) : T →+ T where
  toFun := A.partialNorm k
  map_zero' := A.partialNorm_zero_right k
  map_add' := A.partialNorm_add k

/-- Evaluating the bundled partial norm gives the translation accumulated by an affine iterate. -/
@[simp]
theorem cyclicNormHom_apply (A : T ≃+ T) (k : ℕ) (x : T) :
    A.cyclicNormHom k x = A.partialNorm k x := (rfl)

/-- The empty partial norm is the zero endomorphism. -/
@[simp]
theorem cyclicNormHom_zero (A : T ≃+ T) : A.cyclicNormHom 0 = 0 := by
  ext x
  simp

/-- The partial norm for one iterate is the identity endomorphism. -/
@[simp]
theorem cyclicNormHom_one (A : T ≃+ T) : A.cyclicNormHom 1 = AddMonoidHom.id T := by
  ext x
  simp

/-- The difference from the `k`-th power of an additive automorphism. -/
def oneSubPow (A : T ≃+ T) (k : ℕ) : T →+ T :=
  AddMonoidHom.id T - (A.toIntLinearEquiv ^ k).toLinearMap.toAddMonoidHom

/-- The difference endomorphism sends `x` to `x - A^k x`. -/
@[simp]
theorem oneSubPow_apply (A : T ≃+ T) (k : ℕ) (x : T) :
    A.oneSubPow k x = x - (⇑A)^[k] x := by
  simp [oneSubPow, LinearEquiv.coe_pow]

/-- The difference from the zeroth power vanishes. -/
@[simp]
theorem oneSubPow_zero (A : T ≃+ T) : A.oneSubPow 0 = 0 := by
  ext x
  simp

/-- The norm for two iterates is `1 + A`, also in the presence of 2-torsion. -/
@[simp]
theorem cyclicNormHom_two (A : T ≃+ T) :
    A.cyclicNormHom 2 = AddMonoidHom.id T + A.toAddMonoidHom := by
  ext x
  simp [partialNorm_succ]

/-- The difference for one iterate is `1 - A`. -/
@[simp]
theorem oneSubPow_one (A : T ≃+ T) :
    A.oneSubPow 1 = AddMonoidHom.id T - A.toAddMonoidHom := by
  ext x
  simp

section Periodic

variable {m : ℕ} [NeZero m] (A : T ≃+ T) (hA : (⇑A)^[m] = id)

/-- The norm differential of Mathlib's cyclic short complexes is the bundled partial norm. -/
theorem cyclicRep_norm_toAddMonoidHom :
    (A.cyclicRep hA).norm.asHom.hom.toLinearMap.toAddMonoidHom = A.cyclicNormHom m := by
  ext x
  rw [cyclicNormHom_apply, partialNorm_def]
  exact A.cyclicRep_norm_apply hA x

/-- Mathlib's cyclic difference differential is the negative of the `1 - A` convention. -/
theorem cyclicRep_applyAsHom_sub_toAddMonoidHom :
    (Rep.applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap.toAddMonoidHom =
      -A.oneSubPow 1 := by
  ext x
  calc
    _ = A x - x := A.cyclicRep_applyAsHom_sub_apply hA x
    _ = _ := by simp

include hA in
/-- For a periodic automorphism, `1 - A` annihilates the cyclic norm.
This is the zero-composite law of Mathlib's norm-then-difference short complex. -/
theorem oneSubPow_comp_cyclicNormHom :
    (A.oneSubPow 1).comp (A.cyclicNormHom m) = 0 := by
  ext x
  have hx : (Rep.applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap
      ((A.cyclicRep hA).norm.asHom.hom.toLinearMap x) = 0 :=
    congrArg (fun f ↦ f x)
      (Rep.FiniteCyclicGroup.normHomCompSub (A.cyclicRep hA) (.ofAdd 1)).zero
  rw [cyclicRep_applyAsHom_sub_apply, cyclicRep_norm_apply, ← partialNorm_def] at hx
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, oneSubPow_apply,
    Function.iterate_one, cyclicNormHom_apply, sub_eq_zero] using (sub_eq_zero.mp hx).symm

include hA in
/-- For a periodic automorphism, the cyclic norm annihilates `1 - A`.
This is the zero-composite law of Mathlib's difference-then-norm short complex. -/
theorem cyclicNormHom_comp_oneSubPow :
    (A.cyclicNormHom m).comp (A.oneSubPow 1) = 0 := by
  ext x
  have hx : (A.cyclicRep hA).norm.asHom.hom.toLinearMap
      ((Rep.applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap x) = 0 :=
    congrArg (fun f ↦ f x)
      (Rep.FiniteCyclicGroup.subCompNormHom (A.cyclicRep hA) (.ofAdd 1)).zero
  rw [cyclicRep_applyAsHom_sub_apply, cyclicRep_norm_apply, ← partialNorm_def,
    partialNorm_sub] at hx
  simpa only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, oneSubPow_apply,
    Function.iterate_one, cyclicNormHom_apply, partialNorm_sub, sub_eq_zero] using
      (sub_eq_zero.mp hx).symm

end Periodic

end AddEquiv
