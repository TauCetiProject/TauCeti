/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.EvenUnitary
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.Algebra.Field.Conic
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import Mathlib.Tactic.Module

/-!
# The Spin group is strictly smaller than the even unitary group in dimension six

For a nondegenerate quadratic form in dimensions one to five, the Spin group is the whole even
unitary group `U(C₀, σ)` of the Clifford algebra: every even Clifford unit `x` with
`reverse x * x = 1` lies in the Lipschitz group. The sibling files prove this in dimensions one
and two. This file shows that the equality stops in dimension six, where `U(C₀, σ)` is a unitary
group of degree four and the Spin group is only its reduced-norm-one subgroup, and that, for
nondegenerate forms over infinite fields in which `2 ≠ 0`, it fails in every dimension from six
on.

The witness is explicit. Let `v₁, …, vₙ` be pairwise orthogonal anisotropic vectors, where `n`
is even and `n.choose 2` is odd (that is, `n ≡ 2 (mod 4)`), and let `ω = ι v₁ ⋯ ι vₙ` be their
volume element. It is even, it anticommutes with each of the `ι vᵢ`, its reverse is `-ω`, and its
square is the scalar `-(Q v₁ ⋯ Q vₙ)`. Hence `x = a + b • ω` is an even unit with
`reverse x * x = a² + b² ∏ Q vᵢ`, so `x ∈ U(C₀, σ)` as soon as `a² + b² ∏ Q vᵢ = 1`. Twisted
conjugation by `x` sends each of the listed vectors `v` to `(a² - b² ∏ Q vᵢ) • v + 2ab • ω v`, and
once `n ≥ 3` the element `ω v` is not a vector: any anisotropic `u ⟂ v` among the list would commute
with it, forcing it to be proportional to `u`, and two orthogonal choices of `u` leave only `0`.
Since the Lipschitz group preserves the vectors under twisted conjugation, `x` is not in it
whenever `a b ≠ 0`. Over an infinite field in which `2 ≠ 0` the conic `a² + δ b² = 1` always has
such a point. The smallest admissible length is `n = 6`, which is the dimension-six application.

The witness only uses the listed orthogonal anisotropic vectors, not a basis, so it lives in the
Clifford algebra of every nondegenerate form of dimension at least six, and the theorems about it
carry no hypothesis on the ambient dimension. (In a larger space `ω` commutes with a further
orthogonal vector rather than anticommuting with it; only the listed vectors are used.) The same
computation is why dimension two is different: `n = 2` also has `n ≡ 2 (mod 4)`, but there `ω v` is
a multiple of the other basis vector, and indeed the Spin group fills the even unitary group in
dimension two.

The dimension-six identification `Spin(Q) ≅ SU(C₀, σ)` and the strictness `SU ≠ U` are classical;
see M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15, and
H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.

## Main results

* `CliffordAlgebra.exists_mem_evenUnitaryGroup_coe_eq_algebraMap_add_smul_prod_map_ι`: for `ω`
  the volume element of an orthogonal list of even length with odd `n.choose 2`, in any quadratic
  module over a commutative ring containing it, `a + b • ω` is an even unitary unit when
  `a² + b² ∏ Q vᵢ = 1`.
* `CliffordAlgebra.notMem_lipschitzGroup_of_mem_evenUnitaryGroup_of_coe_eq`: such a unit with
  `a b ≠ 0` is not in the Lipschitz group once the list is anisotropic of length at least three.
* `CliffordAlgebra.range_spinGroup_toUnits_ne_evenUnitaryGroup_of_six_le_finrank`: over an
  infinite field in which `2 ≠ 0`, the Spin group of a nondegenerate form of dimension at least six
  is a proper subgroup of the even unitary group.
* `CliffordAlgebra.exists_spinGroup_ne_evenUnitaryGroup_finrank_six`: the split rational witness,
  a nondegenerate form on `Fin 6 → ℚ` whose Spin group is a proper subgroup of its even unitary
  group.

The conic point is `TauCeti.exists_sq_add_sq_mul_eq_one` (`TauCeti/Algebra/Field/Conic.lean`),
and the fact that `ω v` is not a vector is `CliffordAlgebra.prod_map_ι_mul_ι_notMem_range_ι`
(`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement.lean`).
-/

public section

open Module

namespace CliffordAlgebra

universe u v

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-! ### Auxiliary volume-element computations -/

/-- Both products of `a + b • ω` with `a - b • ω`, for `ω` squaring to the scalar `s`. -/
private theorem algebraMap_add_smul_mul_algebraMap_sub_smul {ω : CliffordAlgebra Q} {s : R}
    (hsq : ω * ω = algebraMap R _ s) (a b : R) :
    (algebraMap R _ a + b • ω) * (algebraMap R _ a - b • ω) =
        algebraMap R (CliffordAlgebra Q) (a ^ 2 - b ^ 2 * s) ∧
      (algebraMap R _ a - b • ω) * (algebraMap R _ a + b • ω) =
        algebraMap R (CliffordAlgebra Q) (a ^ 2 - b ^ 2 * s) := by
  constructor <;>
  · simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, sub_mul, mul_sub,
      smul_mul_smul_comm, one_mul, mul_one, hsq, smul_smul]
    module

/-- Twisted conjugation of a vector by `a + b • ω`, for `ω` anticommuting with the vector and
squaring to the scalar `s`. -/
private theorem algebraMap_add_smul_mul_ι_mul_algebraMap_sub_smul {ω : CliffordAlgebra Q} {s : R}
    (hsq : ω * ω = algebraMap R _ s) {v : M} (hv : ω * ι Q v = -(ι Q v * ω)) (a b : R) :
    (algebraMap R _ a + b • ω) * ι Q v * (algebraMap R _ a - b • ω) =
      (a ^ 2 + b ^ 2 * s) • ι Q v + (2 * a * b) • (ω * ι Q v) := by
  have hvω : ι Q v * ω = -(ω * ι Q v) := by rw [hv, neg_neg]
  have h1 : ι Q v * (algebraMap R _ a - b • ω) = (algebraMap R _ a + b • ω) * ι Q v := by
    rw [mul_sub, add_mul, ← Algebra.commutes, mul_smul_comm, smul_mul_assoc, hvω, smul_neg,
      sub_neg_eq_add]
  rw [mul_assoc, h1, ← mul_assoc]
  simp only [Algebra.algebraMap_eq_smul_one, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hsq, smul_smul]
  module

variable {l : List M}

/-! ### The witness `a + b • ω` built from an orthogonal list of length `≡ 2 (mod 4)` -/

/-- **The even unitary units `a + b • ω` built from an orthogonal list of even length with odd
`n.choose 2`.** For `ω` the volume element of such a list (its length is `≡ 2 (mod 4)`), in any
quadratic module over a commutative ring containing the list, `a + b • ω` is an even unitary unit as
soon as `a² + b² ∏ Q vᵢ = 1`. Neither anisotropy nor a field is needed at this stage; both enter
only when the unit is shown to lie outside the Lipschitz group. -/
theorem exists_mem_evenUnitaryGroup_coe_eq_algebraMap_add_smul_prod_map_ι
    (hl : l.Pairwise Q.IsOrtho) (heven : Even l.length) (hodd : Odd (l.length.choose 2)) {a b : R}
    (hab : a ^ 2 + b ^ 2 * (l.map Q).prod = 1) :
    ∃ x : (CliffordAlgebra Q)ˣ, x ∈ evenUnitaryGroup Q ∧
      (x : CliffordAlgebra Q) = algebraMap R _ a + b • (l.map (ι Q)).prod := by
  -- `ω` is even, `reverse ω = -ω` and `ω² = -∏ Q vᵢ`, so `a + b • ω` is an even unit with inverse
  -- `a - b • ω` and reverse norm `a² + b² ∏ Q vᵢ = 1`.
  have hsq : (l.map (ι Q)).prod * (l.map (ι Q)).prod = algebraMap R _ (-(l.map Q).prod) := by
    rw [prod_map_ι_sq_scalar hl, hodd.neg_one_pow, neg_one_mul]
  have hrev : reverse (l.map (ι Q)).prod = -(l.map (ι Q)).prod := by
    rw [reverse_prod_map_ι_of_pairwise_isOrtho hl, hodd.neg_one_pow, neg_one_smul]
  obtain ⟨h₁, h₂⟩ := algebraMap_add_smul_mul_algebraMap_sub_smul hsq a b
  have hnorm : a ^ 2 - b ^ 2 * -(l.map Q).prod = 1 := by rw [← hab]; ring
  rw [hnorm, map_one] at h₁ h₂
  refine ⟨⟨algebraMap R _ a + b • (l.map (ι Q)).prod, algebraMap R _ a - b • (l.map (ι Q)).prod,
    h₁, h₂⟩, ?_, rfl⟩
  rw [evenUnitaryGroup.mem_iff_reverse_mul_self_eq_one, Units.val_mk]
  refine ⟨?_, ?_⟩
  · have hω : (l.map (ι Q)).prod ∈ even Q := by
      have h := prod_map_ι_mem_evenOdd (Q := Q) l
      rw [heven.natCast_zmod_two] at h
      rwa [← Subalgebra.mem_toSubmodule, even_toSubmodule]
    exact (even Q).add_mem ((even Q).algebraMap_mem a) ((even Q).smul_mem hω b)
  · rw [map_add, map_smul, reverse.commutes, hrev, smul_neg, ← sub_eq_add_neg, h₂]

end CommRing

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {l : List V}

section Invertible

variable [Invertible (2 : K)]

/-! ### The witness is not in the Lipschitz group -/

/-- **An even unitary unit `a + b • ω` with `a b ≠ 0` is not in the Lipschitz group**, for `ω` the
volume element of an orthogonal anisotropic list of even length at least three with odd
`n.choose 2`. Length two is genuinely excluded: there `ω` sends each member of the list to a
multiple of the other. The list need not span: the witness lives in the Clifford algebra of any
quadratic space containing it. -/
theorem notMem_lipschitzGroup_of_mem_evenUnitaryGroup_of_coe_eq (hl : l.Pairwise Q.IsOrtho)
    (heven : Even l.length) (hodd : Odd (l.length.choose 2)) (h3 : 3 ≤ l.length)
    (haniso : ∀ v ∈ l, Q v ≠ 0) {x : (CliffordAlgebra Q)ˣ}
    (hx : x ∈ evenUnitaryGroup Q)
    {a b : K} (hcoe : (x : CliffordAlgebra Q) = algebraMap K _ a + b • (l.map (ι Q)).prod)
    (ha : a ≠ 0) (hb : b ≠ 0) : x ∉ lipschitzGroup Q := by
  -- Twisted conjugation by `x` sends a member `v` of the list to `(a² + b² ω²) • v + 2ab • ω v`,
  -- and `ω v` is not a vector (`prod_map_ι_mul_ι_notMem_range_ι`), whereas the Lipschitz group
  -- preserves the vectors (`lipschitzGroup.involute_act_ι_mem_range_ι`).
  intro hxL
  obtain ⟨v, hv⟩ := List.exists_mem_of_length_pos (l := l) (by omega)
  have hsq : (l.map (ι Q)).prod * (l.map (ι Q)).prod = algebraMap K _ (-(l.map Q).prod) := by
    rw [prod_map_ι_sq_scalar hl, hodd.neg_one_pow, neg_one_mul]
  have hrev : reverse (l.map (ι Q)).prod = -(l.map (ι Q)).prod := by
    rw [reverse_prod_map_ι_of_pairwise_isOrtho hl, hodd.neg_one_pow, neg_one_smul]
  -- `x` is even, so its involute is itself, and its inverse is its reverse `a - b • ω`.
  have hinvol : involute (x : CliffordAlgebra Q) = x := by
    rw [hcoe, map_add, map_smul, involute.commutes, involute_prod_map_ι, heven.neg_one_pow,
      one_smul]
  have hinv : ((x⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      algebraMap K _ a - b • (l.map (ι Q)).prod := by
    have h := evenUnitaryGroup.reverse_eq_inv Q ⟨x, hx⟩
    dsimp only at h
    rw [← h, hcoe, map_add, map_smul, reverse.commutes, hrev, smul_neg, ← sub_eq_add_neg]
  have hmem := lipschitzGroup.involute_act_ι_mem_range_ι hxL v
  rw [hinvol, hinv, hcoe, algebraMap_add_smul_mul_ι_mul_algebraMap_sub_smul hsq
    (prod_map_ι_mul_ι_of_even_length hl heven (Submodule.subset_span hv))] at hmem
  have hsub : (2 * a * b) • ((l.map (ι Q)).prod * ι Q v) ∈ LinearMap.range (ι Q) := by
    have h := (LinearMap.range (ι Q)).sub_mem hmem
      (Submodule.smul_mem _ (a ^ 2 + b ^ 2 * -(l.map Q).prod) (LinearMap.mem_range_self (ι Q) v))
    rwa [add_sub_cancel_left] at h
  exact prod_map_ι_mul_ι_notMem_range_ι hl heven h3 haniso hv
    ((Submodule.smul_mem_iff _ (mul_ne_zero (mul_ne_zero (Invertible.ne_zero (2 : K)) ha) hb)).mp
      hsub)

/-- **Given an orthogonal anisotropic list of even length at least three with odd `n.choose 2`, the
even unitary group is not contained in the Lipschitz group** as soon as `a² + b² ∏ Q vᵢ = 1` has a
solution with `a b ≠ 0`, the witness being `a + b • ω` for `ω` the volume element of the list. -/
theorem not_evenUnitaryGroup_le_lipschitzGroup_of_sq_add_sq_mul_eq_one (hl : l.Pairwise Q.IsOrtho)
    (heven : Even l.length) (hodd : Odd (l.length.choose 2)) (h3 : 3 ≤ l.length)
    (haniso : ∀ v ∈ l, Q v ≠ 0) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ^ 2 + b ^ 2 * (l.map Q).prod = 1) : ¬ evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  intro hle
  obtain ⟨x, hx, hcoe⟩ :=
    exists_mem_evenUnitaryGroup_coe_eq_algebraMap_add_smul_prod_map_ι hl heven hodd hab
  exact notMem_lipschitzGroup_of_mem_evenUnitaryGroup_of_coe_eq hl heven hodd h3 haniso hx hcoe
    ha hb (hle hx)

end Invertible

/-! ### Infinite fields with `2 ≠ 0`: every nondegenerate form of dimension at least six -/

section Infinite

variable [Infinite K] [NeZero (2 : K)] (Q : QuadraticForm K V)

/-- **Over an infinite field in which `2 ≠ 0`, the even unitary group of a nondegenerate quadratic
form of dimension at least six is not contained in the Lipschitz group.** The witness is `a + b • ω`
for `ω` the volume element of six members of an orthogonal basis, six being the smallest length
`≡ 2 (mod 4)` that is at least three. -/
theorem not_evenUnitaryGroup_le_lipschitzGroup_of_six_le_finrank (hQ : Q.Nondegenerate)
    (hV : 6 ≤ finrank K V) : ¬ evenUnitaryGroup Q ≤ lipschitzGroup Q := by
  -- Six members of an orthogonal anisotropic basis have `∏ Q vᵢ = δ`, and the conic
  -- `a² + b² δ = 1` has a point with `a b ≠ 0` (`TauCeti.exists_sq_add_sq_mul_eq_one`).
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨l, hl, hlen, -, haniso⟩ := hQ.exists_list_pairwise_isOrtho
  have hl' : (l.take 6).Pairwise Q.IsOrtho := hl.sublist (List.take_sublist 6 l)
  have hlen' : (l.take 6).length = 6 := by rw [List.length_take]; omega
  obtain ⟨a, b, ha, hb, hab⟩ := TauCeti.exists_sq_add_sq_mul_eq_one ((l.take 6).map Q).prod
  exact not_evenUnitaryGroup_le_lipschitzGroup_of_sq_add_sq_mul_eq_one hl'
    (by rw [hlen']; decide) (by rw [hlen']; decide) (by omega)
    (fun v hv => haniso v (List.mem_of_mem_take hv)) ha hb hab

/-- **Over an infinite field in which `2 ≠ 0`, the Spin group of a nondegenerate quadratic form of
dimension at least six is a proper subgroup of the even unitary group inside Clifford units.**
This is where the low-rank identification of Spin with the even unitary group stops. -/
theorem range_spinGroup_toUnits_ne_evenUnitaryGroup_of_six_le_finrank (hQ : Q.Nondegenerate)
    (hV : 6 ≤ finrank K V) :
    (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range ≠ evenUnitaryGroup Q := by
  intro h
  refine not_evenUnitaryGroup_le_lipschitzGroup_of_six_le_finrank Q hQ hV ?_
  rw [← h, range_spinGroup_toUnits]
  exact inf_le_left

end Infinite

/-! ### The split rational witness -/

/-- **A split rational witness: the diagonal form `⟨1, -1, 1, -1, 1, -1⟩` on `Fin 6 → ℚ`**, the
diagonalisation of the split form `H ⟂ H ⟂ H`, is a nondegenerate form of dimension six whose Spin
group is a proper subgroup of its even unitary group. This is the classical example where
`U(C₀, σ) ≅ GL₄(ℚ)` and `Spin(Q) ≅ SL₄(ℚ)`. -/
theorem exists_spinGroup_ne_evenUnitaryGroup_finrank_six :
    ∃ Q : QuadraticForm ℚ (Fin 6 → ℚ), Q.Nondegenerate ∧
      (spinGroup.toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ).range ≠ evenUnitaryGroup Q := by
  have hw : ∀ i : Fin 6, IsRegular ((![1, -1, 1, -1, 1, -1] : Fin 6 → ℚ) i) := by
    intro i
    exact isRegular_iff_ne_zero.mpr (by fin_cases i <;> norm_num)
  refine ⟨QuadraticMap.weightedSumSquares ℚ ![1, -1, 1, -1, 1, -1],
    QuadraticMap.nondegenerate_weightedSumSquares hw, ?_⟩
  exact range_spinGroup_toUnits_ne_evenUnitaryGroup_of_six_le_finrank _
    (QuadraticMap.nondegenerate_weightedSumSquares hw) (by rw [finrank_fin_fun])

end CliffordAlgebra
