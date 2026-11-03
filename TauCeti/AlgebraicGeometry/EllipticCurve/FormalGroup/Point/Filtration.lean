/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Torsion.Free
public import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.PowerSeries.Evaluation
import TauCeti.RingTheory.PowerSeries.Rescale

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
`c = ϖ ^ (k - 1)` for a uniformizer `ϖ`, the points of `Ê(𝔪 ^ k)` are the parameters `c s` with
`s ∈ 𝔪`, and the multiplication series satisfies `[n](c X) = n c · g(X)` for a series
`g(X) = X + ⋯` with coefficients in `O` (`PowerSeries.exists_rescale_eq_C_mul`, which needs only
`n ∣ c`). Evaluating `g` and its compositional inverse on `𝔪` shows that `s ↦ g(s)` is a
bijection of `𝔪`. Consequently `[Ê(𝔪 ^ k) : n Ê(𝔪 ^ k)] = #(O ⧸ 𝔪) ^ e`, and `Ê(𝔪 ^ k)` has no
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

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- A parameter in the maximal ideal is evaluable. -/
private theorem hasEval_of_mem {s : O} (hs : s ∈ maximalIdeal O) : HasEval s :=
  (Fact.out : IsAdic (maximalIdeal O)).isTopologicallyNilpotent_of_mem hs

/-- **Multiplication by `n` deep in the formal group**: for `c` divisible by `n`, there is a series
`g(X) = X + ⋯` with `[n](c s) = n c g(s)` at every parameter `c s` with `s ∈ 𝔪`. -/
private theorem exists_coe_nsmul_eq (n : ℕ) {c : O} (hc : (n : O) ∣ c) :
    ∃ g : O⟦X⟧, constantCoeff g = 0 ∧ IsUnit (coeff 1 g) ∧
      ∀ (P : FormalGroupPoint W (maximalIdeal O)) {s : O} (hs : s ∈ maximalIdeal O),
        (P : O) = c * s →
          ((n • P : FormalGroupPoint W (maximalIdeal O)) : O) =
            n * c * aeval (hasEval_of_mem hs) g := by
  have hf1 : coeff 1 ((formalGroup W).nsmulSeries n) = n :=
    (formalGroup W).coeff_one_nsmulSeries n
  obtain ⟨g, hg0, hg1, hfg⟩ :=
    exists_rescale_eq_C_mul ((formalGroup W).constantCoeff_nsmulSeries n) (hf1 ▸ hc)
  refine ⟨g, hg0, hg1 ▸ isUnit_one, fun P s hs hP ↦ ?_⟩
  have hcs : HasEval (c • s) := by
    rw [smul_eq_mul, ← hP]
    exact P.hasEval
  -- evaluate `[n](c X) = n c · g(X)` at `s`
  have h := aeval_rescale (hasEval_of_mem hs) c hcs ((formalGroup W).nsmulSeries n)
  rw [hfg, map_mul, aeval_C] at h
  simpa [hf1, coe_nsmul, coe_aeval, ← hP] using h.symm

/-- The setup shared by `map_nsmul_filtration` and `nsmul_filtration_injective`: if `(n) = 𝔪 ^ e`
with `e < k`, take for `c` the `(k - 1)`-st power of a uniformizer, which `n` divides. Then
`𝔪 ^ k = c 𝔪`, `𝔪 ^ (k + e) = n c 𝔪`, and `[n](c s) = n c g(s)` for `s ∈ 𝔪` and a series
`g(X) = X + ⋯` (`exists_coe_nsmul_eq`). -/
private theorem exists_nsmul_filtration_eq {n e k : ℕ}
    (hn : Ideal.span {(n : O)} = maximalIdeal O ^ e) (hek : e < k) :
    ∃ (c : O) (g : O⟦X⟧), maximalIdeal O ^ k = Ideal.span {c} * maximalIdeal O ∧
      maximalIdeal O ^ (k + e) = Ideal.span {(n : O) * c} * maximalIdeal O ∧
      constantCoeff g = 0 ∧ IsUnit (coeff 1 g) ∧
      ∀ (P : FormalGroupPoint W (maximalIdeal O)) {s : O} (hs : s ∈ maximalIdeal O),
        (P : O) = c * s →
          ((n • P : FormalGroupPoint W (maximalIdeal O)) : O) =
            n * c * aeval (hasEval_of_mem hs) g := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpow (j : ℕ) : maximalIdeal O ^ j = Ideal.span {ϖ ^ j} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hnc : (n : O) ∣ ϖ ^ (k - 1) := by
    rw [← Ideal.span_singleton_le_span_singleton, hn, hpow]
    exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (by omega))
  obtain ⟨g, hg0, hg1, hng⟩ := exists_coe_nsmul_eq (W := W) n hnc
  refine ⟨ϖ ^ (k - 1), g, ?_, ?_, hg0, hg1, hng⟩
  · rw [← hpow, ← pow_succ, Nat.sub_add_cancel (by omega)]
  · rw [← Ideal.span_singleton_mul_span_singleton, hn, ← hpow, mul_assoc, ← pow_succ, ← pow_add]
    congr 1
    omega

/-- **`n Ê(𝔪 ^ k) = Ê(𝔪 ^ (k + e))`**: over a complete discrete valuation ring, if `(n) = 𝔪 ^ e`
with `e < k`, multiplication by `n` carries `Ê(𝔪 ^ k)` onto `Ê(𝔪 ^ (k + e))`. -/
theorem map_nsmul_filtration {n e k : ℕ} (hn : Ideal.span {(n : O)} = maximalIdeal O ^ e)
    (hek : e < k) :
    (filtration W (maximalIdeal O) k).map (nsmulAddMonoidHom n) =
      filtration W (maximalIdeal O) (k + e) := by
  -- the parameters of `Ê(𝔪 ^ k)` are the `c s` with `s ∈ 𝔪`, and those of `Ê(𝔪 ^ (k + e))` are
  -- the `n c s` with `s ∈ 𝔪`
  obtain ⟨c, g, hk, hke, hg0, hg1, hng⟩ := exists_nsmul_filtration_eq (W := W) hn hek
  ext Q
  constructor
  · rintro ⟨P, hP, rfl⟩
    rw [SetLike.mem_coe, mem_filtration, hk, Ideal.mem_span_singleton_mul] at hP
    obtain ⟨s, hs, hPs⟩ := hP
    rw [mem_filtration, nsmulAddMonoidHom_apply, hng P hs hPs.symm, hke]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
      (aeval_mem_of_constantCoeff_eq_zero _ hg0 hs)
  · intro hQ
    rw [mem_filtration, hke, Ideal.mem_span_singleton_mul] at hQ
    obtain ⟨s', hs', hQs⟩ := hQ
    -- solve `g(s) = s'` with the compositional inverse of `g`
    set ginv := g.substInvOfIsUnit hg1
    have hginv0 : constantCoeff ginv = 0 := constantCoeff_substInvOfIsUnit _ _
    set s := aeval (hasEval_of_mem hs') ginv
    have hs : s ∈ maximalIdeal O := aeval_mem_of_constantCoeff_eq_zero _ hginv0 hs'
    have hgs : aeval (hasEval_of_mem hs) g = s' := by
      have h := congrArg (aeval (R := O) (hasEval_of_mem hs'))
        (subst_substInvOfIsUnit_right g hg0 hg1)
      rwa [aeval_subst (HasSubst.of_constantCoeff_zero hginv0)
        (continuous_aeval (hasEval_of_mem hs')) (hasEval_of_mem hs), aeval_X] at h
    have hcs : c * s ∈ maximalIdeal O ^ k := by
      rw [hk]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self c) hs
    let P : FormalGroupPoint W (maximalIdeal O) :=
      ⟨c * s, Ideal.pow_le_self (by omega) hcs⟩
    refine ⟨P, hcs, FormalGroupPoint.ext ?_⟩
    rw [nsmulAddMonoidHom_apply, hng P hs rfl, hgs, hQs]

/-- **`Ê(𝔪 ^ k)` has no nonzero `n`-torsion**: over a complete discrete valuation ring, if
`(n) = 𝔪 ^ e` with `e < k`, multiplication by `n` is injective on `Ê(𝔪 ^ k)`. -/
theorem nsmul_filtration_injective {n e k : ℕ} (hn : Ideal.span {(n : O)} = maximalIdeal O ^ e)
    (hek : e < k) :
    Function.Injective (fun P : filtration W (maximalIdeal O) k ↦ n • P) := by
  obtain ⟨c, g, hk, hke, hg0, hg1, hng⟩ := exists_nsmul_filtration_eq (W := W) hn hek
  have hnc0 : (n : O) * c ≠ 0 := by
    rintro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul] at hke
    exact pow_ne_zero _ (IsDiscreteValuationRing.not_a_field O) hke
  refine (injective_iff_map_eq_zero
    (nsmulAddMonoidHom (α := filtration W (maximalIdeal O) k) n)).mpr fun P hP ↦ ?_
  have hP2 : ((P : FormalGroupPoint W (maximalIdeal O)) : O) ∈
      Ideal.span {c} * maximalIdeal O := by
    rw [← hk]
    exact P.2
  obtain ⟨s, hs, hPs⟩ := Ideal.mem_span_singleton_mul.mp hP2
  -- `n c g(s) = 0`, so `g(s) = 0`
  have hgs : aeval (hasEval_of_mem hs) g = 0 := by
    have h := congrArg (fun Q : filtration W (maximalIdeal O) k ↦
      ((Q : FormalGroupPoint W (maximalIdeal O)) : O)) hP
    simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero,
      coe_zero] at h
    rw [hng _ hs hPs.symm] at h
    exact (mul_eq_zero.mp h).resolve_left hnc0
  -- and `s` is the value of the compositional inverse of `g` at `g(s) = 0`
  have hs0 : s = 0 := by
    have hgs' : HasEval (aeval (hasEval_of_mem hs) g) :=
      hasEval_of_mem (aeval_mem_of_constantCoeff_eq_zero _ hg0 hs)
    have h := congrArg (aeval (R := O) (hasEval_of_mem hs))
      (subst_substInvOfIsUnit_left g hg0 hg1)
    rw [aeval_subst (HasSubst.of_constantCoeff_zero hg0) (continuous_aeval _) hgs',
      aeval_X] at h
    obtain ⟨b, hb⟩ := exists_aeval_eq_mul_of_constantCoeff_eq_zero hgs'
      (constantCoeff_substInvOfIsUnit g hg1)
    rw [← h, hb, hgs, zero_mul]
  ext
  simp [← hPs, hs0]

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
