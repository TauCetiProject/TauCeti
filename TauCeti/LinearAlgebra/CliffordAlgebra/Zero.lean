/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even

/-!
# Clifford algebras of zero-dimensional modules

The Clifford algebra of a subsingleton module consists only of scalars. This file records the
canonical algebra equivalence with the coefficient ring and the resulting elementary behavior of
the grading and reversal. These statements let low-dimensional Clifford-group calculations handle
dimension zero without choosing a concrete model for the zero module.

The equivalence generalizes Mathlib's `CliffordAlgebraRing.equiv` from its concrete zero quadratic
form on `Unit` to any subsingleton module.

## Main results

* `CliffordAlgebra.equivOfSubsingleton` identifies a zero-dimensional Clifford algebra with its
  coefficient ring.
* `CliffordAlgebra.even_eq_top_of_subsingleton` says that every element is even.
* `CliffordAlgebra.reverse_eq_self_of_subsingleton` says that reversal is the identity.
* `CliffordAlgebra.zeroVectorNormalizer` packages the units whose twisted conjugation preserves
  the vector range, and `zeroVectorNormalizerEquivUnits` identifies this normalizer with all scalar
  units in dimension zero.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- The Clifford algebra of a quadratic form on a subsingleton module is canonically isomorphic
to the coefficient ring. -/
noncomputable def equivOfSubsingleton [Subsingleton M] : CliffordAlgebra Q ≃ₐ[R] R :=
  (equivOfIsometry <| QuadraticMap.IsometryEquiv.mk
    (LinearEquiv.ofSubsingleton M Unit) fun x => by
      rw [Subsingleton.elim x 0, map_zero]
      simp).trans CliffordAlgebraRing.equiv

/-- The inverse zero-dimensional Clifford equivalence is the scalar inclusion. -/
@[simp]
theorem equivOfSubsingleton_symm_apply [Subsingleton M] (r : R) :
    (equivOfSubsingleton Q).symm r = algebraMap R (CliffordAlgebra Q) r := by
  apply (equivOfSubsingleton Q).injective
  simp

/-- Every vector has zero image in the Clifford algebra of a subsingleton module. -/
@[simp]
theorem ι_eq_zero_of_subsingleton [Subsingleton M] (x : M) : ι Q x = 0 := by
  rw [Subsingleton.elim x 0, map_zero]

/-- Every element of a zero-dimensional Clifford algebra is even. -/
theorem even_eq_top_of_subsingleton [Subsingleton M] : even Q = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact (even Q).algebraMap_mem r
  | ι x => rw [ι_eq_zero_of_subsingleton]; exact (even Q).zero_mem
  | mul x y hx hy => exact (even Q).mul_mem hx hy
  | add x y hx hy => exact (even Q).add_mem hx hy

/-- Reversal is the identity on a zero-dimensional Clifford algebra. -/
@[simp]
theorem reverse_eq_self_of_subsingleton [Subsingleton M] (x : CliffordAlgebra Q) :
    reverse x = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact reverse.commutes r
  | ι x => simp
  | mul x y hx hy =>
      rw [reverse.map_mul, hx, hy]
      apply (equivOfSubsingleton Q).injective
      simp only [map_mul, mul_comm]
  | add x y hx hy => rw [reverse.map_add, hx, hy]

/-- Units of a zero-dimensional Clifford algebra are canonically scalar units. -/
noncomputable def unitsEquivOfSubsingleton [Subsingleton M] :
    (CliffordAlgebra Q)ˣ ≃* Rˣ :=
  Units.mapEquiv (equivOfSubsingleton Q).toMulEquiv

/-- The scalar-unit equivalence agrees with the units map induced by the Clifford equivalence. -/
theorem unitsEquivOfSubsingleton_apply [Subsingleton M] (x : (CliffordAlgebra Q)ˣ) :
    (unitsEquivOfSubsingleton Q).toMonoidHom x =
      Units.map (equivOfSubsingleton Q).toMonoidHom x := by
  rfl

/-- Units whose twisted conjugation preserves the Clifford vector range in dimension zero.

The predicate is the classical Clifford normalizer condition, specialized to a subsingleton
module.  It is kept as an explicit subgroup so that the comparison with the scalar unit group is
visible, rather than replacing the normalizer by its known carrier. -/
def zeroVectorNormalizer [Subsingleton M] : Subgroup (CliffordAlgebra Q)ˣ where
  carrier := {x | ∀ m, involute (Q := Q) (x : CliffordAlgebra Q) * ι Q m *
      (x⁻¹ : (CliffordAlgebra Q)ˣ) ∈ LinearMap.range (ι Q)}
  one_mem' := by
    intro m
    simp [Subsingleton.elim m 0]
  mul_mem' := by
    intro x y hx hy m
    simp [Subsingleton.elim m 0]
  inv_mem' := by
    intro x hx m
    simp [Subsingleton.elim m 0]

/-- Membership in the dimension-zero vector normalizer is twisted vector preservation. -/
theorem mem_zeroVectorNormalizer_iff [Subsingleton M] (x : (CliffordAlgebra Q)ˣ) :
    x ∈ zeroVectorNormalizer Q ↔ ∀ m, involute (Q := Q) (x : CliffordAlgebra Q) * ι Q m *
      (x⁻¹ : (CliffordAlgebra Q)ˣ) ∈ LinearMap.range (ι Q) :=
  Iff.rfl

/-- In dimension zero every Clifford unit preserves the vector range. -/
@[simp]
theorem zeroVectorNormalizer_eq_top [Subsingleton M] :
    zeroVectorNormalizer Q = ⊤ := by
  rw [eq_top_iff]
  intro x _ m
  simp [Subsingleton.elim m 0]

/-- The dimension-zero vector normalizer is the full scalar unit group. -/
noncomputable def zeroVectorNormalizerEquivUnits [Subsingleton M] :
    zeroVectorNormalizer Q ≃* Rˣ :=
  ((MulEquiv.subgroupCongr (zeroVectorNormalizer_eq_top Q)).trans Subgroup.topEquiv).trans
    (unitsEquivOfSubsingleton Q)

/-- The scalar coordinate of the dimension-zero normalizer equivalence. -/
@[simp]
theorem zeroVectorNormalizerEquivUnits_apply [Subsingleton M]
    (x : zeroVectorNormalizer Q) :
    (zeroVectorNormalizerEquivUnits Q x : Rˣ) =
      Units.map (equivOfSubsingleton Q).toMonoidHom (x : (CliffordAlgebra Q)ˣ) := by
  simp only [zeroVectorNormalizerEquivUnits, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.topEquiv_apply]
  exact unitsEquivOfSubsingleton_apply Q _

end CliffordAlgebra

end
