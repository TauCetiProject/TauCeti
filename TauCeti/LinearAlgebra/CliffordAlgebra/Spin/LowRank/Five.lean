/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Four
-- Private: the Clifford-group characterization of the Lipschitz group, the reversal calculus on
-- odd elements in dimension five, the volume element, the orthogonal basis, the vanishing of
-- central vectors and the dichotomy for a vector plus a central element are used only inside the
-- proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.CliffordGroup
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Five
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# The Spin group in dimensions one to five

For a nondegenerate quadratic space of dimension between one and five over a field of
characteristic not two, Mathlib's `spinGroup` fills the even unitary carrier `U(C₀, σ)`. Dimensions
at most four are `TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Four.lean`; this file adds
dimension five and assembles the range.

In dimension five an even unitary unit `x` still conjugates each vector `ι Q v` to an odd,
reverse-fixed element `y = x * ι Q v * x⁻¹`, but now such an element is a vector plus a multiple
of the volume element `ω` of an orthogonal basis
(`CliffordAlgebra.mem_range_ι_sup_span_of_mem_evenOdd_one_of_reverse_eq_of_length_eq_five`),
`y = ι Q w + c • ω`. The square of `y` is the scalar `Q v`, and `ω` is central with scalar square,
so the cross term `2 c • (ω * ι Q w)` is a scalar: either `c = 0`, or `ι Q w` is a multiple of the
central `ω`, hence central, hence zero, in which case `y = c • ω` is itself central and equals
`ι Q v`. Either way `y` is a vector, so `x` lies in the classical Clifford group, which is the
Lipschitz group (`CliffordAlgebra.mem_lipschitzGroup_of_involute_act_ι_mem_range_ι`).

Dimension five is where the identification stops: in dimension six the even unitary group is
strictly larger than the Spin group
(`TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/Basic.lean`),
the volume element being then reverse-antisymmetric and anticommuting with the vectors.

## Main results

* `CliffordAlgebra.evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_five`: for a nondegenerate
  form in dimension five, every even unitary Clifford unit is Lipschitz.
* `CliffordAlgebra.evenUnitaryGroup_le_lipschitzGroup`: for a nondegenerate form in dimension
  between one and five, every even unitary Clifford unit is Lipschitz.
* `CliffordAlgebra.range_spinGroup_toUnits_eq_evenUnitaryGroup`: for a nondegenerate form in
  dimension between one and five, the Spin image and the even unitary carrier coincide.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

open Module

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [Invertible (2 : K)]
  {Q : QuadraticForm K V}

/-- **In dimension five, the even unitary carrier lies in the Lipschitz group.** -/
theorem evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_five (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : finrank K V = 5) : evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨l, hl, hlen, hspan, haniso⟩ := hQ.exists_list_pairwise_isOrtho
  rw [hV] at hlen
  -- The volume element `ω` of the basis is central with nonzero scalar square.
  set ω : CliffordAlgebra Q := (l.map (ι Q)).prod
  have hcenter : ∀ z, Commute ω z := fun z =>
    (Subalgebra.mem_center_iff.mp
      (prod_map_ι_mem_center_of_odd_length hl (by rw [hlen]; decide) hspan) z).symm
  have hsq : ω * ω = algebraMap K _ ((-1 : K) ^ l.length.choose 2 * (l.map Q).prod) :=
    prod_map_ι_sq_scalar hl
  have hs : (-1 : K) ^ l.length.choose 2 * (l.map Q).prod ≠ 0 :=
    neg_one_pow_choose_two_mul_prod_map_ne_zero haniso
  -- A vector proportional to the central `ω` commutes with two orthogonal basis vectors, so it
  -- vanishes.
  have h0 : 0 < l.length := by omega
  have h1 : 1 < l.length := by omega
  have hu₁ : Q l[0] ≠ 0 := haniso _ (List.getElem_mem h0)
  have hu₂ : Q l[1] ≠ 0 := haniso _ (List.getElem_mem h1)
  have hu₁u₂ : Q.IsOrtho l[0] l[1] := List.pairwise_iff_getElem.mp hl 0 1 h0 h1 zero_lt_one
  have hcentral : ∀ {w : V} (t : K), ι Q w = t • ω → w = 0 := fun t ht =>
    eq_zero_of_commute_ι_of_isOrtho hu₁ hu₂ hu₁u₂
      (by rw [ht]; exact (hcenter _).symm.smul_right t)
      (by rw [ht]; exact (hcenter _).symm.smul_right t)
  intro x hx
  refine mem_lipschitzGroup_of_involute_act_ι_mem_range_ι Q hQ hQ.exists_isUnit fun m => ?_
  have hxe : (x : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    have h := evenUnitaryGroup.mem_even Q hx
    rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule] at h
  have hxie : ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    have h := evenUnitaryGroup.mem_even Q (inv_mem hx)
    rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule] at h
  rw [involute_eq_of_mem_even hxe]
  -- The conjugate of a vector by an even unit is odd.
  have hodd : (x : CliffordAlgebra Q) * ι Q m * ↑x⁻¹ ∈ evenOdd Q 1 := by
    have h : (x : CliffordAlgebra Q) * ι Q m ∈ evenOdd Q 1 :=
      zero_add (1 : ZMod 2) ▸ SetLike.mul_mem_graded hxe (ι_mem_evenOdd_one Q m)
    exact add_zero (1 : ZMod 2) ▸ SetLike.mul_mem_graded h hxie
  -- Reversal inverts an even unitary unit, so it fixes the conjugate.
  have hrev : reverse ((x : CliffordAlgebra Q) * ι Q m *
        ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) =
      (x : CliffordAlgebra Q) * ι Q m * ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
    have hxr : reverse (x : CliffordAlgebra Q) = ↑x⁻¹ := evenUnitaryGroup.reverse_eq_inv Q ⟨x, hx⟩
    have hxir : reverse ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = x := by
      rw [← hxr, reverse_reverse]
    simp only [reverse.map_mul, reverse_ι, hxr, hxir, mul_assoc]
  -- So the conjugate is `ι Q w + c • ω`, and its square is the scalar `Q m`.
  obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := Submodule.mem_sup.mp
    (mem_range_ι_sup_span_of_mem_evenOdd_one_of_reverse_eq_of_length_eq_five hl hspan hlen hodd
      hrev)
  obtain ⟨w, rfl⟩ := hy₁
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy₂
  have hysq : (ι Q w + c • ω) * (ι Q w + c • ω) = algebraMap K _ (Q m) := by
    rw [hy]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc (ι Q m), ι_sq_scalar, Algebra.commutes, ← mul_assoc, Units.mul_inv, one_mul]
  rcases eq_zero_or_exists_ι_eq_smul_of_mul_self_eq_algebraMap (hcenter (ι Q w)) hsq hs hysq with
    hc | ⟨t, ht⟩
  · -- `c = 0`: the conjugate is the vector `ι Q w`.
    rw [← hy, hc, zero_smul, add_zero]
    exact LinearMap.mem_range_self _ w
  · -- `ι Q w` is a multiple of `ω`, so `w = 0` and the conjugate `c • ω` is central: it is `ι Q m`.
    rw [hcentral t ht, map_zero, zero_add] at hy
    have hm : ι Q m = c • ω := by
      calc ι Q m = ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
            ((x : CliffordAlgebra Q) * ι Q m * ↑x⁻¹) * x := by
            simp [mul_assoc]
        _ = ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * (c • ω) * x := by rw [hy]
        _ = c • ω := by
            rw [mul_smul_comm, smul_mul_assoc, (hcenter _).symm.eq, mul_assoc, Units.inv_mul,
              mul_one]
    rw [← hy, ← hm]
    exact LinearMap.mem_range_self _ m

/-- **Spin is the even unitary group in dimensions one to five.** For a nondegenerate quadratic
space of dimension between one and five, the even unitary carrier lies in the Lipschitz group.
Dimension zero is excluded, and the exclusion is not decoration: there the Lipschitz group is
trivial while the even unitary carrier is `μ₂`. The bound five is sharp, by
`CliffordAlgebra.not_evenUnitaryGroup_le_lipschitzGroup_of_six_le_finrank`. -/
theorem evenUnitaryGroup_le_lipschitzGroup (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hV0 : 0 < finrank K V) (hV : finrank K V ≤ 5) : evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  have : FiniteDimensional K V := Module.finite_of_finrank_pos hV0
  rcases hV.lt_or_eq with h | h
  · exact evenUnitaryGroup_le_lipschitzGroup_of_finrank_le_four Q hQ hV0 (Nat.le_of_lt_succ h)
  · exact evenUnitaryGroup_le_lipschitzGroup_of_finrank_eq_five Q hQ h

/-- For a nondegenerate quadratic space of dimension between one and five, the Spin group fills
the even unitary carrier inside Clifford units. -/
-- Not `@[simp]`: `range_spinGroup_toUnits` already simplifies the left-hand side.
theorem range_spinGroup_toUnits_eq_evenUnitaryGroup (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV0 : 0 < finrank K V) (hV : finrank K V ≤ 5) :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range = evenUnitaryGroup Q := by
  rw [range_spinGroup_toUnits]
  exact inf_eq_right.mpr (evenUnitaryGroup_le_lipschitzGroup Q hQ hV0 hV)

end CliffordAlgebra
