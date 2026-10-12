/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.KerReduction

/-!
# Torsion of order prime to the residue characteristic in the formal group

Let `I` be an adic ideal of a complete Hausdorff linearly topologised ring `O`. To first order the
Weierstrass formal group law is addition, so multiplication by `n` on the group `Ê(I)` of
formal-group parameters is multiplication by `n` to first order: if `t ∈ I ^ k`, then
`[n] t ≡ n t (mod I ^ (2 k))`. When `n` is a unit of `O`, a nonzero parameter `t` therefore cannot
satisfy `[n] t = 0`: from `t ∈ I ^ k` one gets `n t ∈ I ^ (2 k)`, so `t ∈ I ^ (k + 1)`, and `t` lies
in every power of `I`, which meet in `0`. This is Silverman AEC IV.3.2(b).

Through the identification `Ê(𝔪_u) ≃ E₁(F_u)` of the formal group with the kernel of reduction
over the completion of a Dedekind domain at a height-one prime `u`, it follows that `E₁(F_u)`
has no nonzero point of order `n` for any `n` outside `u`: the reduction modulo `u` of a nonzero
point of order prime to the residue characteristic is not the point at infinity. This is the
kernel half of the injectivity of reduction on prime-to-`p` torsion (Silverman AEC VII.3.1).

## Main results

* `WeierstrassCurve.FormalGroupPoint.coe_nsmul_sub_natCast_mul_mem`: `[n] t ≡ n t (mod I ^ (2 k))`
  for a parameter `t ∈ I ^ k`.
* `WeierstrassCurve.FormalGroupPoint.eq_zero_of_nsmul_eq_zero`: `Ê(I)` has no nonzero `n`-torsion
  when `n` is a unit of `O`.
* `WeierstrassCurve.eq_zero_of_mem_kerReduction_of_nsmul_eq_zero`: the kernel of reduction
  `E₁(F_u)` has no nonzero `n`-torsion when `n ∉ u`.
* `WeierstrassCurve.valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero`: so a
  nonzero point of `E(F_u)` of order prime to `u` has integral coordinates.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.3.2 and VII.3.1.
-/

public section

namespace WeierstrassCurve

namespace FormalGroupPoint

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]
  {W : WeierstrassCurve O} {I : Ideal O} [Fact (IsAdic I)]

/-- **Multiplication by `n` on the formal group is multiplication by `n` to first order**: for a
parameter `t ∈ I ^ k`, the parameter of `n • t` agrees with `n * t` modulo `I ^ (2 * k)`. -/
theorem coe_nsmul_sub_natCast_mul_mem {k : ℕ} {P : FormalGroupPoint W I} (hP : (P : O) ∈ I ^ k)
    (n : ℕ) :
    ((n • P : FormalGroupPoint W I) : O) - n * P ∈ I ^ (2 * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hle : I ^ (2 * k) ≤ I ^ k := Ideal.pow_le_pow_right (by omega)
    -- the parameter of `n • P` stays in `I ^ k`
    have hn : ((n • P : FormalGroupPoint W I) : O) ∈ I ^ k := by
      simpa using Ideal.add_mem _ (hle ih) (Ideal.mul_mem_left _ (n : O) hP)
    have h := W.formalAddEval_sub_add_mem (Fact.out : IsAdic I) hn hP
    rw [succ_nsmul, coe_add]
    convert Ideal.add_mem _ h ih using 1
    push_cast
    ring

/-- **The formal group has no torsion of unit order** (Silverman AEC IV.3.2(b)): if `n` is a unit
of `O`, the only parameter `t ∈ I` with `n • t = 0` in `Ê(I)` is `t = 0`. -/
theorem eq_zero_of_nsmul_eq_zero {n : ℕ} (hn : IsUnit (n : O)) {P : FormalGroupPoint W I}
    (h : n • P = 0) : P = 0 := by
  -- `P` lies in every power of `I`
  have hmem : ∀ k, (P : O) ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using P.property
    | succ k ih =>
      have hnP : (n : O) * P ∈ I ^ (2 * (k + 1)) := by
        simpa [h] using coe_nsmul_sub_natCast_mul_mem ih n
      have hle : I ^ (2 * (k + 1)) ≤ I ^ (k + 1 + 1) := Ideal.pow_le_pow_right (by omega)
      simpa [← mul_assoc] using Ideal.mul_mem_left _ (↑hn.unit⁻¹ : O) (hle hnP)
  -- and the powers of `I` meet in `0`, as `O` is Hausdorff in its `I`-adic topology
  have hH : IsHausdorff I O := (Fact.out : IsAdic I).isHausdorff_iff.mpr inferInstance
  refine FormalGroupPoint.ext (hH.haus _ fun k ↦ ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ k) (hmem k)

end FormalGroupPoint

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "m_u" => IsLocalRing.maximalIdeal O_u

local instance : IsLinearTopology O_u O_u :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸ Ideal.isLinearTopology m_u

local instance : Fact (IsAdic m_u) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩

variable (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- **The kernel of reduction has no torsion prime to the residue characteristic** (Silverman AEC
VII.3.1): a point of `E₁(F_u)` killed by an integer `n ∉ u` is the point at infinity. -/
theorem eq_zero_of_mem_kerReduction_of_nsmul_eq_zero {n : ℕ} (hn : (n : A) ∉ u.asIdeal)
    {P : (C.baseChange F_u).toAffine.Point} (hP : P ∈ C.kerReduction u) (h : n • P = 0) :
    P = 0 := by
  -- `n` is a unit of the completed valuation ring
  have hunit : IsUnit (n : O_u) := by
    rw [← map_natCast (algebraMap A O_u),
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
      HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact hn
  set e := C.formalPointAddEquivKerReduction u
  have hQ : n • e.symm ⟨P, hP⟩ = 0 := by
    rw [← map_nsmul, AddEquiv.map_eq_zero_iff]
    exact Subtype.ext h
  simpa using congrArg Subtype.val
    (e.symm.map_eq_zero_iff.mp (FormalGroupPoint.eq_zero_of_nsmul_eq_zero hunit hQ))

open scoped Classical in
/-- **Torsion of order prime to the residue characteristic is integral**: a nonzero point of
`E(F_u)` killed by an integer `n ∉ u` does not lie in the kernel of reduction, so both of its
coordinates are integral at `u`. -/
theorem valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero {n : ℕ}
    (hn : (n : A) ∉ u.asIdeal) {P : (C.baseChange F_u).toAffine.Point} (hP : P ≠ 0)
    (h : n • P = 0) :
    Valued.v (Affine.Point.xCoord P) ≤ 1 ∧ Valued.v (Affine.Point.yCoord P) ≤ 1 :=
  C.valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_notMem_range u fun hmem ↦
    hP (C.eq_zero_of_mem_kerReduction_of_nsmul_eq_zero u hn
      (C.range_formalPointHomAdicCompletion_eq_kerReduction u ▸ hmem) h)

end WeierstrassCurve
