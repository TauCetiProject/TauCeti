/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Torsion.Free
public import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.PowerSeries.InverseFunction

/-!
# The filtration of the elliptic formal group by powers of the ideal

Let `I` be an adic ideal of a complete linearly topologised ring `O`, and let `Ê(I)` be the group
of parameters in `I` under the Weierstrass formal group law. The points with parameter in `I ^ k`
form a subgroup `Ê(I ^ k)`, and these subgroups decrease with `k`. Since the group law is
`t₁ + t₂` to first order, the parameter modulo `I ^ (k + 1)` is an additive map
`Ê(I ^ k) → I ^ k ⧸ I ^ (k + 1)` with kernel `Ê(I ^ (k + 1))`, for `k ≥ 1`. So the successive
quotients of the filtration have the orders of the successive quotients of the powers of `I`
(Silverman AEC IV.3.2(a)), and `[Ê(I) : Ê(I ^ k)] = [I : I ^ k]`.

Over a complete discrete valuation ring `O` with maximal ideal `𝔪`, multiplication by an integer
`n ≠ 0` of valuation `e` is an isomorphism `Ê(𝔪 ^ k) ≅ Ê(𝔪 ^ (k + e))` as soon as `e < k`. With
the inverse function theorem for integral power series
(`PowerSeries.bijOn_eval₂_maximalIdeal_pow`), applied to the multiplication series, one gets
its exact image and injectivity on these parameters. Consequently
`[Ê(𝔪 ^ k) : n Ê(𝔪 ^ k)] = #(O ⧸ 𝔪) ^ e`, and `Ê(𝔪 ^ k)` has no
nonzero `n`-torsion. This is the formal-group input to the index of `n E(K)` for an elliptic curve
over a local field `K` at a place dividing `n`.

## Main definitions

* `WeierstrassCurve.FormalGroupPoint.filtration`: the subgroup `Ê(I ^ k)` of `Ê(I)`.

## Main results

* `WeierstrassCurve.FormalGroupPoint.relIndex_filtration`: for `1 ≤ j ≤ k`, the index of
  `Ê(I ^ k)` in `Ê(I ^ j)` is the index of `I ^ k` in `I ^ j`.
* `WeierstrassCurve.FormalGroupPoint.index_filtration`: `[Ê(I) : Ê(I ^ k)] = [I : I ^ k]`.
* `WeierstrassCurve.FormalGroupPoint.map_nsmul_filtration`: over a complete discrete valuation
  ring, `n Ê(𝔪 ^ k) = Ê(𝔪 ^ (k + e))` when `(n) = 𝔪 ^ e` and `e < k`.
* `WeierstrassCurve.FormalGroupPoint.nsmul_filtration_injective`: under the same hypotheses,
  multiplication by `n` is injective on `Ê(𝔪 ^ k)`.
* `WeierstrassCurve.FormalGroupPoint.index_range_nsmul_filtration`: under the same hypotheses,
  `[Ê(𝔪 ^ k) : n Ê(𝔪 ^ k)] = #(O ⧸ 𝔪) ^ e`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.3.2, IV.6.4 and VII.6.3.
-/

public section

open IsLocalRing PowerSeries

namespace WeierstrassCurve.FormalGroupPoint

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]

section Filtration

variable (W : WeierstrassCurve O) (I : Ideal O) [Fact (IsAdic I)]

/-- The subgroup `Ê(I ^ k)` of the formal group `Ê(I)`: the points whose parameter lies in
`I ^ k`. -/
def filtration (k : ℕ) : AddSubgroup (FormalGroupPoint W I) where
  carrier := {P | (P : O) ∈ I ^ k}
  zero_mem' := by simp
  add_mem' {P Q} hP hQ := by
    simpa using W.formalAddEval_mem (Fact.out : IsAdic I) hP hQ
  neg_mem' {P} hP := by
    simpa using W.formalInverseEval_mem P.hasEval hP

variable {W I}

@[simp]
theorem mem_filtration {k : ℕ} {P : FormalGroupPoint W I} :
    P ∈ filtration W I k ↔ (P : O) ∈ I ^ k := Iff.rfl

@[simp]
theorem filtration_zero : filtration W I 0 = ⊤ := by
  ext P
  simp

@[simp]
theorem filtration_one : filtration W I 1 = ⊤ := by
  ext P
  simpa using P.property

theorem filtration_antitone : Antitone (filtration W I) :=
  fun _ _ hjk _ hP ↦ Ideal.pow_le_pow_right hjk hP

/-- For `k ≥ 1`, the parameter modulo `I ^ (k + 1)`, an additive map on `Ê(I ^ k)` because the
group law is `t₁ + t₂` modulo `I ^ (2 k)`. -/
private noncomputable def gradedHom {k : ℕ} (hk : k ≠ 0) :
    filtration W I k →+ (I ^ k).toAddSubgroup ⧸
      (I ^ (k + 1)).toAddSubgroup.addSubgroupOf (I ^ k).toAddSubgroup where
  toFun P := QuotientAddGroup.mk ⟨((P : FormalGroupPoint W I) : O), P.2⟩
  map_zero' := by simp [coe_zero, AddSubgroup.mem_addSubgroupOf]
  map_add' P Q := by
    rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have h := W.formalAddEval_sub_add_mem (Fact.out : IsAdic I) P.2 Q.2
    have hle : I ^ (2 * k) ≤ I ^ (k + 1) := Ideal.pow_le_pow_right (by omega)
    simpa [neg_add_eq_sub] using neg_mem (hle h)

private theorem gradedHom_surjective {k : ℕ} (hk : k ≠ 0) :
    Function.Surjective (gradedHom (W := W) (I := I) hk) := by
  intro x
  obtain ⟨⟨t, ht⟩, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact ⟨⟨⟨t, Ideal.pow_le_self hk ht⟩, ht⟩, rfl⟩

private theorem ker_gradedHom {k : ℕ} (hk : k ≠ 0) :
    (gradedHom (W := W) (I := I) hk).ker =
      (filtration W I (k + 1)).addSubgroupOf (filtration W I k) := by
  ext P
  simp [gradedHom, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

/-- **The successive quotients of the filtration** (Silverman AEC IV.3.2(a)): for `k ≥ 1`, the
index of `Ê(I ^ (k + 1))` in `Ê(I ^ k)` is the index of `I ^ (k + 1)` in `I ^ k`. -/
theorem relIndex_filtration_succ {k : ℕ} (hk : k ≠ 0) :
    (filtration W I (k + 1)).relIndex (filtration W I k) =
      (I ^ (k + 1)).toAddSubgroup.relIndex (I ^ k).toAddSubgroup := by
  rw [AddSubgroup.relIndex, ← ker_gradedHom (W := W) hk, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (gradedHom_surjective hk), AddSubgroup.card_top,
    AddSubgroup.relIndex, AddSubgroup.index]

/-- For `1 ≤ j ≤ k`, the index of `Ê(I ^ k)` in `Ê(I ^ j)` is the index of `I ^ k` in `I ^ j`. -/
theorem relIndex_filtration {j k : ℕ} (hj : j ≠ 0) (hjk : j ≤ k) :
    (filtration W I k).relIndex (filtration W I j) =
      (I ^ k).toAddSubgroup.relIndex (I ^ j).toAddSubgroup := by
  induction k, hjk using Nat.le_induction with
  | base => simp [AddSubgroup.relIndex_self]
  | succ k hjk ih =>
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (filtration_antitone (Nat.le_succ k))
      (filtration_antitone hjk), relIndex_filtration_succ (by omega), ih,
      AddSubgroup.relIndex_mul_relIndex _ _ _ (Ideal.pow_le_pow_right (Nat.le_succ k))
        (Ideal.pow_le_pow_right hjk)]

/-- For `k ≥ 1`, the index of `Ê(I ^ k)` in `Ê(I)` is the index of `I ^ k` in `I`. -/
theorem index_filtration {k : ℕ} (hk : k ≠ 0) :
    (filtration W I k).index = (I ^ k).toAddSubgroup.relIndex I.toAddSubgroup := by
  rw [← AddSubgroup.relIndex_top_right, ← filtration_one (W := W),
    relIndex_filtration one_ne_zero (Nat.one_le_iff_ne_zero.mpr hk), pow_one]

end Filtration

section NSMul

variable [IsDomain O] [IsDiscreteValuationRing O] {W : WeierstrassCurve O}
  [Fact (IsAdic (maximalIdeal O))]

/-- **`n Ê(𝔪 ^ k) = Ê(𝔪 ^ (k + e))`**: over a complete discrete valuation ring, if `(n) = 𝔪 ^ e`
with `e < k`, multiplication by `n` carries `Ê(𝔪 ^ k)` onto `Ê(𝔪 ^ (k + e))`. -/
theorem map_nsmul_filtration {n e k : ℕ} (hn : Ideal.span {(n : O)} = maximalIdeal O ^ e)
    (hek : e < k) :
    (filtration W (maximalIdeal O) k).map (nsmulAddMonoidHom n) =
      filtration W (maximalIdeal O) (k + e) := by
  have h := bijOn_eval₂_maximalIdeal_pow ((formalGroup W).constantCoeff_nsmulSeries n)
    (by simpa using hn) hek
  ext Q
  constructor
  · rintro ⟨P, hP, rfl⟩
    simpa only [mem_filtration, nsmulAddMonoidHom_apply, coe_nsmul, SetLike.mem_coe]
      using h.mapsTo hP
  · intro hQ
    obtain ⟨t, ht, htQ⟩ := h.surjOn hQ
    let P : FormalGroupPoint W (maximalIdeal O) :=
      ⟨t, Ideal.pow_le_self (by omega) ht⟩
    exact ⟨P, ht, FormalGroupPoint.ext (by simpa only [nsmulAddMonoidHom_apply,
      coe_nsmul] using htQ)⟩

/-- **`Ê(𝔪 ^ k)` has no nonzero `n`-torsion**: over a complete discrete valuation ring, if
`(n) = 𝔪 ^ e` with `e < k`, multiplication by `n` is injective on `Ê(𝔪 ^ k)`. -/
theorem nsmul_filtration_injective {n e k : ℕ} (hn : Ideal.span {(n : O)} = maximalIdeal O ^ e)
    (hek : e < k) :
    Function.Injective (fun P : filtration W (maximalIdeal O) k ↦ n • P) := by
  have h := bijOn_eval₂_maximalIdeal_pow ((formalGroup W).constantCoeff_nsmulSeries n)
    (by simpa using hn) hek
  intro P Q hPQ
  have hcoords := congrArg
    (fun T : filtration W (maximalIdeal O) k ↦ ((T : FormalGroupPoint W (maximalIdeal O)) : O)) hPQ
  simp only [AddSubgroup.coe_nsmul, coe_nsmul] at hcoords
  exact Subtype.ext (FormalGroupPoint.ext (h.injOn P.property Q.property hcoords))

/-- **The index of `n Ê(𝔪 ^ k)` in `Ê(𝔪 ^ k)`**: over a complete discrete valuation ring, if
`(n) = 𝔪 ^ e` with `e < k`, then `[Ê(𝔪 ^ k) : n Ê(𝔪 ^ k)] = #(O ⧸ 𝔪) ^ e`. -/
theorem index_range_nsmul_filtration {n e k : ℕ}
    (hn : Ideal.span {(n : O)} = maximalIdeal O ^ e) (hek : e < k) :
    (nsmulAddMonoidHom (α := filtration W (maximalIdeal O) k) n).range.index =
      Nat.card (ResidueField O) ^ e := by
  rw [← AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range, map_nsmul_filtration hn hek,
    ← AddSubgroup.relIndex, relIndex_filtration (by omega) (by omega),
    TauCeti.IsDiscreteValuationRing.relIndex_maximalIdeal_pow_add]

end NSMul

end WeierstrassCurve.FormalGroupPoint
