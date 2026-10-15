/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Zero
public import TauCeti.RingTheory.RootsOfUnity.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Basic

/-!
# The even unitary group in dimension zero

For a quadratic form on a zero-dimensional module, the Clifford algebra is the coefficient ring,
every Clifford element is even, and reversal is the identity. Consequently the even unitary group
is exactly the group `μ₂` of square roots of unity in the coefficient ring.

This is the dimension-zero boundary of the low-rank identification of Spin with the even unitary
group: Mathlib's Lipschitz-defined Spin group is trivial in dimension zero, whereas the even
unitary carrier generally has the two scalar elements `1` and `-1`.

## Main results

* `CliffordAlgebra.evenUnitaryGroupEquivRootsOfUnityOfSubsingleton` identifies the even unitary
  group with `rootsOfUnity 2 K`.
* `CliffordAlgebra.range_spinGroup_toUnits_eq_bot_of_subsingleton` records that the Spin image is
  trivial in dimension zero.
* `CliffordAlgebra.range_spinGroup_toUnits_ne_evenUnitaryGroup_of_subsingleton` shows that these
  groups differ in characteristic not two.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [CommRing K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

private noncomputable def unitsEquivOfSubsingleton [Subsingleton V] :
    (CliffordAlgebra Q)ˣ ≃* Kˣ :=
  Units.mapEquiv (equivOfSubsingleton Q).toMulEquiv

private theorem map_evenUnitaryGroup_unitsEquivOfSubsingleton [Subsingleton V] :
    (evenUnitaryGroup Q).map (unitsEquivOfSubsingleton Q).toMonoidHom = rootsOfUnity 2 K := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_rootsOfUnity]
    apply Units.ext
    -- Expose the value of `Units.map`, whose coercion is definitionally the algebra equivalence.
    change (equivOfSubsingleton Q (x : CliffordAlgebra Q)) ^ 2 = 1
    rw [pow_two, ← map_mul]
    calc
      equivOfSubsingleton Q ((x : CliffordAlgebra Q) * x) =
          equivOfSubsingleton Q (reverse (x : CliffordAlgebra Q) * x) := by
        rw [reverse_eq_self_of_subsingleton]
      _ = equivOfSubsingleton Q 1 := by
        rw [evenUnitaryGroup.reverse_mul_self Q ⟨x, hx⟩]
      _ = 1 := map_one _
  · intro hu
    let x : (CliffordAlgebra Q)ˣ := (unitsEquivOfSubsingleton Q).symm u
    refine ⟨x, ?_, (unitsEquivOfSubsingleton Q).apply_symm_apply u⟩
    -- Remove the `SetLike` coercion introduced by membership in the mapped subgroup.
    change x ∈ evenUnitaryGroup Q
    rw [evenUnitaryGroup.mem_iff_reverse_mul_self_eq_one]
    constructor
    · simp [even_eq_top_of_subsingleton Q]
    · rw [reverse_eq_self_of_subsingleton Q]
      apply (equivOfSubsingleton Q).injective
      have hx : Units.map (equivOfSubsingleton Q).toMonoidHom x = u :=
        (unitsEquivOfSubsingleton Q).apply_symm_apply u
      have hxval : equivOfSubsingleton Q (x : CliffordAlgebra Q) = (u : K) :=
        congrArg Units.val hx
      rw [map_mul, map_one, hxval]
      have hu' : u ^ 2 = 1 := (mem_rootsOfUnity 2 u).mp hu
      simpa only [pow_two, Units.val_mul, Units.val_one] using congrArg Units.val hu'

/-- In dimension zero, the even unitary group of a Clifford algebra is the group of square roots
of unity in the coefficient ring. Under this equivalence, an even unitary Clifford element is
sent to its scalar value. -/
noncomputable def evenUnitaryGroupEquivRootsOfUnityOfSubsingleton [Subsingleton V] :
    evenUnitaryGroup Q ≃* rootsOfUnity 2 K :=
  ((unitsEquivOfSubsingleton Q).subgroupMap (evenUnitaryGroup Q)).trans <|
    MulEquiv.subgroupCongr (map_evenUnitaryGroup_unitsEquivOfSubsingleton Q)

/-- The dimension-zero equivalence sends an even unitary element to its value under the canonical
scalar equivalence of Clifford algebras. -/
@[simp]
theorem coe_evenUnitaryGroupEquivRootsOfUnityOfSubsingleton_apply [Subsingleton V]
    (x : evenUnitaryGroup Q) :
    ((evenUnitaryGroupEquivRootsOfUnityOfSubsingleton Q x : rootsOfUnity 2 K) : Kˣ) =
      Units.map (equivOfSubsingleton Q).toMonoidHom (x : (CliffordAlgebra Q)ˣ) := by
  rfl

/-- In dimension zero and characteristic not two, the even unitary group has two elements. -/
theorem card_evenUnitaryGroup_of_subsingleton [Subsingleton V] [IsDomain K]
    (h2 : (2 : K) ≠ 0) :
    Nat.card (evenUnitaryGroup Q) = 2 := by
  rw [Nat.card_congr (evenUnitaryGroupEquivRootsOfUnityOfSubsingleton Q).toEquiv]
  exact TauCeti.card_rootsOfUnity_two h2

/-- In dimension zero, Mathlib's Lipschitz-defined Spin group has trivial image among Clifford
units. -/
theorem range_spinGroup_toUnits_eq_bot_of_subsingleton [Subsingleton V] :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range = ⊥ := by
  rw [range_spinGroup_toUnits, lipschitzGroup_eq_bot, bot_inf_eq]

/-- In dimension zero and characteristic not two, the Spin image is strictly smaller than the
even unitary group. This is the boundary obstruction to extending the positive-dimensional
low-rank identification to dimension zero. -/
theorem range_spinGroup_toUnits_ne_evenUnitaryGroup_of_subsingleton [Subsingleton V]
    (h2 : (2 : K) ≠ 0) :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range ≠ evenUnitaryGroup Q := by
  intro h
  have hroots : rootsOfUnity 2 K ≠ ⊥ :=
    TauCeti.rootsOfUnity_eq_bot_iff.not.mpr (not_not.mpr ⟨-1, .neg_one_of_two_ne_zero h2⟩)
  rw [← Subgroup.nontrivial_iff_ne_bot] at hroots
  have := (evenUnitaryGroupEquivRootsOfUnityOfSubsingleton Q).toEquiv.nontrivial
  rw [Subgroup.nontrivial_iff_ne_bot, ← h] at this
  exact this (range_spinGroup_toUnits_eq_bot_of_subsingleton Q)

end CliffordAlgebra

end
