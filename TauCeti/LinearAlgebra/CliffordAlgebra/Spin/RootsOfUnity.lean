/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel

/-!
# The square roots of unity in the Spin group

A scalar `ζ` with `ζ ^ 2 = 1` is a product of two invertible vectors as soon as the quadratic form
takes a unit value, so the group `μ₂(R) = rootsOfUnity 2 R` maps into the Spin group by its
scalars. This file packages that map as the homomorphism `rootsOfUnityToSpin` and identifies its
image: over a field in which `2` is invertible, for a finite-dimensional nondegenerate form, the
image of `μ₂(K)` is exactly the kernel of the Spin action on `SO(Q)`, so that
`μ₂(K) → Spin(Q) → SO(Q)` is exact at `Spin(Q)` and its first map is injective. The inclusion is
natural along quadratic isometries and along extension of scalars.

The hypothesis that `Q` takes a unit value is what puts the scalars into Mathlib's
closure-defined Lipschitz group, and it cannot be dropped: on a zero-dimensional space that group,
and hence the Spin group, is trivial.

## Main definitions

* `CliffordAlgebra.rootsOfUnityToSpin`: the inclusion `μ₂(R) →* Spin(Q)` by scalars.

## Main results

* `CliffordAlgebra.rootsOfUnityToSpin_injective`: the inclusion is injective when `2` is
  invertible.
* `CliffordAlgebra.range_rootsOfUnityToSpin`: over a field, for a finite-dimensional
  nondegenerate form, its image is the kernel of `spinToSpecialOrthogonal`.
* `CliffordAlgebra.mulExact_rootsOfUnityToSpin_spinToSpecialOrthogonal`: the sequence
  `μ₂(K) → Spin(Q) → SO(Q)` is exact at `Spin(Q)`.
* `QuadraticMap.Isometry.spinGroupMap_comp_rootsOfUnityToSpin`,
  `CliffordAlgebra.spinGroupBaseChange_comp_rootsOfUnityToSpin` and their pointwise forms
  `QuadraticMap.Isometry.spinGroupMap_rootsOfUnityToSpin` and
  `CliffordAlgebra.spinGroupBaseChange_rootsOfUnityToSpin`: naturality along isometries and along
  extension of scalars.

## References

See N. Bourbaki, *Algèbre*, Chapitre 9, §9, and T. Y. Lam, *Introduction to Quadratic Forms over
Fields* (2005), Chapter V, §5.
-/

public section

namespace CliffordAlgebra

open TauCeti
open scoped TensorProduct

universe u v w

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The inclusion of the square roots of unity `μ₂(R)` into the Spin group as scalars, for a
quadratic form taking a unit value. -/
def rootsOfUnityToSpin (Q : QuadraticForm R M) (hQ : ∃ v, IsUnit (Q v)) :
    rootsOfUnity 2 R →* spinGroup Q where
  toFun ζ := ⟨algebraMap R (CliffordAlgebra Q) ((ζ : Rˣ) : R),
    algebraMap_mem_spinGroup_of_isUnit Q hQ.choose hQ.choose_spec
      ((mem_rootsOfUnity' 2 (ζ : Rˣ)).mp ζ.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' ζ η := Subtype.ext (by simp)

/-- The Clifford value of the image of a square root of unity is that scalar. -/
@[simp]
theorem coe_rootsOfUnityToSpin_apply (Q : QuadraticForm R M) (hQ : ∃ v, IsUnit (Q v))
    (ζ : rootsOfUnity 2 R) :
    (rootsOfUnityToSpin Q hQ ζ : CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) ((ζ : Rˣ) : R) :=
  (rfl)

variable [Invertible (2 : R)]

/-- The inclusion of `μ₂(R)` into the Spin group is injective when `2` is invertible. -/
theorem rootsOfUnityToSpin_injective (Q : QuadraticForm R M) (hQ : ∃ v, IsUnit (Q v)) :
    Function.Injective (rootsOfUnityToSpin Q hQ) := fun ζ η h ↦
  Subtype.ext <| Units.ext <| algebraMap_injective Q <| by
    simpa only [coe_rootsOfUnityToSpin_apply] using congrArg Subtype.val h

/-- A square root of unity acts trivially on the quadratic space. -/
@[simp]
theorem spinToSpecialOrthogonal_rootsOfUnityToSpin (Q : QuadraticForm R M)
    (hQ : ∃ v, IsUnit (Q v)) (ζ : rootsOfUnity 2 R) :
    spinToSpecialOrthogonal Q (rootsOfUnityToSpin Q hQ ζ) = 1 :=
  MonoidHom.mem_ker.mp
    (mem_ker_spinToSpecialOrthogonal_of_coe_eq_algebraMap Q _ (coe_rootsOfUnityToSpin_apply Q hQ ζ))

/-- The image of `μ₂(R)` lies in the kernel of the Spin action. -/
theorem range_rootsOfUnityToSpin_le_ker (Q : QuadraticForm R M) (hQ : ∃ v, IsUnit (Q v)) :
    (rootsOfUnityToSpin Q hQ).range ≤ (spinToSpecialOrthogonal Q).ker := by
  rintro _ ⟨ζ, rfl⟩
  exact spinToSpecialOrthogonal_rootsOfUnityToSpin Q hQ ζ

end CommRing

section Field

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- Over a field, the inclusion of `μ₂(K)` sends the square root `-1` to the canonical scalar
`-1` of the Spin group. -/
theorem rootsOfUnityToSpin_eq_negOne (Q : QuadraticForm K V) (hQ : ∃ v, IsUnit (Q v))
    {ζ : rootsOfUnity 2 K} (hζ : ((ζ : Kˣ) : K) = -1) :
    rootsOfUnityToSpin Q hQ ζ =
      spinGroup.negOne Q (by rintro rfl; obtain ⟨v, hv⟩ := hQ; simp at hv) :=
  Subtype.ext (by simp [hζ])

variable [FiniteDimensional K V] [Invertible (2 : K)]

/-- For a finite-dimensional nondegenerate quadratic form over a field in which `2` is invertible,
the image of `μ₂(K)` in the Spin group is exactly the kernel of the Spin action on `SO(Q)`. -/
theorem range_rootsOfUnityToSpin (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hQv : ∃ v, IsUnit (Q v)) :
    (rootsOfUnityToSpin Q hQv).range = (spinToSpecialOrthogonal Q).ker := by
  refine le_antisymm (range_rootsOfUnityToSpin_le_ker Q hQv) fun x hx ↦ ?_
  have : Nontrivial V := by
    obtain ⟨v, hv⟩ := hQv
    refine ⟨⟨v, 0, fun h ↦ ?_⟩⟩
    simp [h] at hv
  rcases (mem_ker_spinToSpecialOrthogonal_iff Q hQ x).mp hx with rfl | rfl
  · exact Subgroup.one_mem _
  · have hneg : (-1 : Kˣ) ∈ rootsOfUnity 2 K := (mem_rootsOfUnity 2 _).mpr (by simp)
    exact ⟨⟨-1, hneg⟩, rootsOfUnityToSpin_eq_negOne Q hQv (by simp)⟩

/-- For a finite-dimensional nondegenerate quadratic form over a field in which `2` is invertible,
the sequence `μ₂(K) → Spin(Q) → SO(Q)` is exact at `Spin(Q)`. -/
theorem mulExact_rootsOfUnityToSpin_spinToSpecialOrthogonal (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hQv : ∃ v, IsUnit (Q v)) :
    Function.MulExact (rootsOfUnityToSpin Q hQv) (spinToSpecialOrthogonal Q) := by
  rw [MonoidHom.mulExact_iff, range_rootsOfUnityToSpin Q hQ hQv]

end Field

section BaseChange

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Invertible (2 : R)]

/-- Extension of scalars of Spin groups carries the inclusion of `μ₂(R)` to the inclusion of
`μ₂(A)`, precomposed with the induced map `μ₂(R) → μ₂(A)`. -/
theorem spinGroupBaseChange_comp_rootsOfUnityToSpin (Q : QuadraticForm R M)
    (hQ : ∃ v, IsUnit (Q v)) :
    (spinGroupBaseChange (A := A) Q).comp (rootsOfUnityToSpin Q hQ) =
      (rootsOfUnityToSpin (Q.baseChange A) (QuadraticForm.exists_isUnit_baseChange hQ)).comp
        (restrictRootsOfUnity (algebraMap R A) 2) := by
  ext ζ
  simp only [MonoidHom.comp_apply, coe_spinGroupBaseChange_apply, coe_rootsOfUnityToSpin_apply,
    AlgHom.commutes, restrictRootsOfUnity_coe_apply,
    IsScalarTower.algebraMap_apply R A (CliffordAlgebra (Q.baseChange A))]

/-- Extension of scalars of Spin groups sends the image of a square root of unity to the image of
its image in `μ₂(A)`. -/
@[simp]
theorem spinGroupBaseChange_rootsOfUnityToSpin (Q : QuadraticForm R M) (hQ : ∃ v, IsUnit (Q v))
    (ζ : rootsOfUnity 2 R) :
    spinGroupBaseChange (A := A) Q (rootsOfUnityToSpin Q hQ ζ) =
      rootsOfUnityToSpin (Q.baseChange A) (QuadraticForm.exists_isUnit_baseChange hQ)
        (restrictRootsOfUnity (algebraMap R A) 2 ζ) :=
  DFunLike.congr_fun (spinGroupBaseChange_comp_rootsOfUnityToSpin Q hQ) ζ

end BaseChange

end CliffordAlgebra

namespace QuadraticMap.Isometry

open CliffordAlgebra

universe u v w

variable {R : Type u} {M₁ : Type v} {M₂ : Type w} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}

/-- A Spin-group map induced by a quadratic isometry carries the inclusion of `μ₂(R)` for the
source form to that for the target form. -/
theorem spinGroupMap_comp_rootsOfUnityToSpin (f : Q₁ →qᵢ Q₂) (hQ₁ : ∃ v, IsUnit (Q₁ v)) :
    f.spinGroupMap.comp (rootsOfUnityToSpin Q₁ hQ₁) =
      rootsOfUnityToSpin Q₂ (f.exists_isUnit_apply hQ₁) := by
  ext ζ
  simp only [MonoidHom.comp_apply, coe_spinGroupMap_apply, coe_rootsOfUnityToSpin_apply,
    AlgHom.commutes]

/-- A Spin-group map induced by a quadratic isometry fixes each square root of unity. -/
@[simp]
theorem spinGroupMap_rootsOfUnityToSpin (f : Q₁ →qᵢ Q₂) (hQ₁ : ∃ v, IsUnit (Q₁ v))
    (ζ : rootsOfUnity 2 R) :
    f.spinGroupMap (rootsOfUnityToSpin Q₁ hQ₁ ζ) =
      rootsOfUnityToSpin Q₂ (f.exists_isUnit_apply hQ₁) ζ :=
  DFunLike.congr_fun (spinGroupMap_comp_rootsOfUnityToSpin f hQ₁) ζ

end QuadraticMap.Isometry
