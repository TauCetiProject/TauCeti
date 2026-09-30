/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Span
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Abelianization
import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries
import Mathlib.FieldTheory.Finiteness

/-!
# The degree-one graded piece of a free pro-`p` group

Let `F = freeProP p X` be the free pro-`p` group on a finite linearly ordered type `X`, with
canonical generators `x_i = freeProP.of i`. The degree-one graded piece
`gr_1(F) = λ_1(F) ⧸ λ_2(F)` of the lower `p`-series is an `𝔽_p`-vector space with basis

  `π x'_i` for `i ∈ X`, and `[x'_i, x'_j]` for `i < j`,

the `p`-power classes and the brackets of the generator classes `x'_i ∈ gr_0(F)`. So
`gr_1(F) ≅ 𝔽_p^X ⊕ Λ²(𝔽_p^X)` has dimension `#X + (#X choose 2)`.

The basis is the degree-one family `TauCeti.degreeOneFamily` of the canonical generators, indexed
by `X ⊕ {(i, j) : i < j}`, so its coordinates split a class in `gr_1(F)` into its `p`-power part,
with one coefficient per generator, and its commutator part, with one coefficient per unordered
pair of generators. These coordinates are what reading off the class of a relator of a pro-`p`
group presented on the generators `x_i` requires. The results hold for any universe of `X`; the
two finite `p`-groups of `p`-class two used as detecting groups for this degree-one basis are
`ℤ/p²` and the Heisenberg group over `𝔽_p`.

In every degree `j`, the iterated `p`-power classes `π^j x'_i ∈ gr_j(F)` of the generators are
linearly independent, detected in the cyclic groups `ℤ/pʲ⁺¹` of `p`-class `j + 1` through the
exponent sums modulo `p ^ (j + 1)` (`TauCeti.freeProP.exponentSumZModPow`): the graded map induced
by the `i`-th of these characters reads off the coefficient of `π^j x'_i`, and on the class of an
element of `λ_j(F)` it detects whether `p ^ (j + 1)` divides the `i`-th exponent sum. For `j = 1`
the classes `π x'_i` are the `p`-power part of the basis above. They span the tails of the
successive approximation of relators in normal form.

At `p = 2` the bracket `[x'_0, x'_1]` in `gr_1(freeProP 2 (Fin 2))` is therefore nonzero, and the
degree-zero power-defect formula shows that the `2`-power operator on this free pro-`2` group is
not additive.

## Main definitions

* `TauCeti.freeProP.degreeZeroBasis`: the basis `x'_i` of `gr_0(F)` formed by the generator classes.
* `TauCeti.freeProP.degreeOneBasis`: the basis `π x'_i`, `[x'_i, x'_j]` (`i < j`) of `gr_1(F)`.

## Main results

* `TauCeti.freeProP.linearIndependent_degreeOneFamily_of`: the family is linearly independent.
* `TauCeti.freeProP.dvd_exponentSum_of_mem_pLowerCentralSeries`: the exponent sums of an element
  of `λ_k(F)` are divisible by `p ^ k`.
* `TauCeti.freeProP.padicPow_mem_pLowerCentralSeries_iff`: a `p`-adic power `x_i ^ a` of a
  free generator lies in `λ_k(F)` exactly when `p ^ k` divides `a` in `ℤ_p`.
* `TauCeti.freeProP.mem_topologicalClosure_closure_singleton_inf_pLowerCentralSeries_iff`: the
  resulting description of `closure ⟨x_i⟩ ∩ λ_k(F)`.
* `TauCeti.freeProP.gradedMap_exponentSumZModPow_gradedMk_eq_zero_iff`: the graded map induced on
  `gr_k(F)` by the `i`-th exponent sum modulo `p ^ (k + 1)` kills the class of `y ∈ λ_k(F)` exactly
  when `p ^ (k + 1)` divides the `i`-th exponent sum of `y`.
* `TauCeti.freeProP.linearIndependent_gradedPowIter_gradedMkZero_of`: the classes `π^j x'_i` are
  linearly independent in `gr_j(F)`, for every `j`.
* `TauCeti.freeProP.finrank_gradedPiece_one`: `dim gr_1(F) = #X + (#X choose 2)`;
  `TauCeti.freeProP.natCard_gradedPiece_one`: so `gr_1(F)` has `p ^ (#X + (#X choose 2))` elements.
* `TauCeti.gradedBracket_freeProP_two_ne_zero`: the bracket of the two generator classes of
  `freeProP 2 (Fin 2)` is nonzero.
* `TauCeti.gradedPow_freeProP_two_not_additive`: the `2`-power operator is not additive in degree
  zero on `freeProP 2 (Fin 2)`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §1 and §3.
-/

public section

namespace TauCeti

open Subgroup Submodule
open scoped commutatorElement

universe u

/-! ### The detecting groups

The lower `p`-series of a finite discrete group is its abstract lower `p`-central series, so the
computations below are transported from `TauCeti.HeisenbergGroup.pLowerCentralSeries_top_two_eq_bot`
along a group isomorphism, which lets the detecting groups live in any universe. The cyclic
detecting groups `ℤ/pⁿ` are handled in the same way by
`MulEquiv.pLowerCentralSeries_eq_bot_multiplicative_zmod_pow` and
`MulEquiv.gradedPowIter_gradedMkZero_ne_zero_multiplicative_zmod_pow`. -/

section Detecting

variable {p : ℕ} {H : Type u} [Group H] [TopologicalSpace H] [DiscreteTopology H]

/-- A discrete group isomorphic to the Heisenberg group over `ZMod p` has `p`-class at most two. -/
theorem _root_.MulEquiv.pLowerCentralSeries_two_eq_bot_heisenbergGroup
    (e : H ≃* HeisenbergGroup (ZMod p)) : pLowerCentralSeries p H 2 = ⊥ := by
  let : TopologicalSpace (HeisenbergGroup (ZMod p)) := ⊥
  have : DiscreteTopology (HeisenbergGroup (ZMod p)) := ⟨rfl⟩
  rw [← Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective,
    e.map_pLowerCentralSeries_eq_of_discreteTopology, pLowerCentralSeries_eq_of_discreteTopology,
    HeisenbergGroup.pLowerCentralSeries_top_two_eq_bot]

/-- In a discrete group isomorphic to the Heisenberg group over `ZMod p`, the `p`-power classes of
the two standard generators `(1, 0, 0)` and `(0, 1, 0)` vanish: their `p`-th powers are trivial. -/
theorem _root_.MulEquiv.gradedPow_gradedMkZero_eq_zero_heisenbergGroup
    (e : H ≃* HeisenbergGroup (ZMod p)) {a : HeisenbergGroup (ZMod p)} (ha : a.z = 0)
    (ha' : a.x * a.y = 0) : gradedPow p H 0 (gradedMkZero p H (e.symm a)) = 0 := by
  have hpow : a ^ p = 1 := by
    rw [HeisenbergGroup.pow_eq]
    ext <;> simp [ha, ha', nsmul_eq_mul]
  rw [gradedPow_gradedMkZero, gradedMk_eq_zero_iff, Subgroup.coe_mk, ← map_pow, hpow, map_one]
  exact one_mem _

variable [Fact p.Prime]

/-- In a discrete group isomorphic to the Heisenberg group over `𝔽_p`, the bracket of the classes
of the two standard generators `(1, 0, 0)` and `(0, 1, 0)` is nonzero. -/
theorem _root_.MulEquiv.gradedBracket_gradedMkZero_ne_zero_heisenbergGroup
    (e : H ≃* HeisenbergGroup (ZMod p)) :
    gradedBracket p H 0 0 (gradedMkZero p H (e.symm ⟨1, 0, 0⟩))
      (gradedMkZero p H (e.symm ⟨0, 1, 0⟩)) ≠ 0 := by
  rw [gradedBracket_gradedMkZero, ne_eq, gradedMk_eq_zero_iff, Subgroup.coe_mk]
  simp only [Nat.reduceAdd]
  rw [e.pLowerCentralSeries_two_eq_bot_heisenbergGroup, Subgroup.mem_bot,
    ← map_commutatorElement, e.symm.map_eq_one_iff, HeisenbergGroup.commutatorElement_eq]
  intro h
  have hz := congrArg HeisenbergGroup.z h
  simp only [mul_one, mul_zero, HeisenbergGroup.one_z] at hz
  exact one_ne_zero ((sub_zero (1 : ZMod p)).symm.trans hz)

end Detecting

/-! ### Exponent sums along the lower `p`-series

The character `TauCeti.freeProP.exponentSumZModPow (k + 1) i` of the `i`-th exponent sum modulo
`p ^ (k + 1)` takes values in the discrete cyclic group `ℤ/pᵏ⁺¹`, whose lower `p`-series stops at
`λ_{k+1} = 1`. So the graded map it induces on `gr_k(F)` detects the divisibility of the `i`-th
exponent sum by `p ^ (k + 1)`, and it reads off the coefficient of `π^k x'_i`. -/

namespace freeProP

section ExponentSum

variable {p : ℕ} [Fact p.Prime] {X : Type u}

/-- **Exponent sums along the lower `p`-series**: the exponent sums of an element of `λ_k(F)` are
divisible by `p ^ k`. -/
theorem dvd_exponentSum_of_mem_pLowerCentralSeries {k : ℕ} {y : freeProP p X}
    (hy : y ∈ pLowerCentralSeries p (freeProP p X) k) (i : X) :
    (p : ℤ_[p]) ^ k ∣ (exponentSum p X y).toAdd i := by
  rw [← exponentSumZModPow_eq_one_iff]
  have h := (exponentSumZModPow p X k i).toMonoidHom.map_pLowerCentralSeries_le
    (exponentSumZModPow p X k i).continuous k ⟨y, hy, rfl⟩
  rwa [MulEquiv.ulift.pLowerCentralSeries_eq_bot_multiplicative_zmod_pow, Subgroup.mem_bot] at h

/-- A `p`-adic power of a free generator lies in the `k`-th lower `p`-series subgroup exactly when
its exponent is divisible by `p ^ k` in `ℤ_p`. -/
@[simp]
theorem padicPow_mem_pLowerCentralSeries_iff (i : X) (a : ℤ_[p]) (k : ℕ) :
    (isProP_freeProP p X).padicPow (of i) a ∈ pLowerCentralSeries p (freeProP p X) k ↔
      (p : ℤ_[p]) ^ k ∣ a := by
  classical
  constructor
  · intro h
    simpa only [exponentSum_padicPow_of, toAdd_ofAdd, Pi.single_eq_same] using
      dvd_exponentSum_of_mem_pLowerCentralSeries h i
  · rintro ⟨b, rfl⟩
    rw [(isProP_freeProP p X).padicPow_mul, ← Nat.cast_pow,
      (isProP_freeProP p X).padicPow_natCast]
    have hpow := pow_pow_mem_pLowerCentralSeries
      (mem_pLowerCentralSeries_zero p (of i : freeProP p X)) k
    rw [zero_add] at hpow
    exact (isProP_freeProP p X).padicPow_mem (isClosed_pLowerCentralSeries k)
      hpow b

/-- The intersection of the closed procyclic subgroup generated by `x_i` with `λ_k(F)` consists
exactly of the `p`-adic powers `x_i ^ a` whose exponent is divisible by `p ^ k`. -/
theorem mem_topologicalClosure_closure_singleton_inf_pLowerCentralSeries_iff
    (i : X) (y : freeProP p X) (k : ℕ) :
    y ∈ (Subgroup.closure {of i}).topologicalClosure ⊓
        pLowerCentralSeries p (freeProP p X) k ↔
      ∃ a : ℤ_[p], (p : ℤ_[p]) ^ k ∣ a ∧ (isProP_freeProP p X).padicPow (of i) a = y := by
  rw [Subgroup.mem_inf, (isProP_freeProP p X).mem_topologicalClosure_closure_singleton_iff]
  constructor
  · rintro ⟨⟨a, rfl⟩, ha⟩
    exact ⟨a, (padicPow_mem_pLowerCentralSeries_iff i a k).1 ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, rfl⟩, (padicPow_mem_pLowerCentralSeries_iff i a k).2 ha⟩

/-- **Detecting divisibility on a graded piece**: the graded map induced on `gr_k(F)` by the
`i`-th exponent sum modulo `p ^ (k + 1)` kills the class of `y ∈ λ_k(F)` exactly when `p ^ (k + 1)`
divides the `i`-th exponent sum of `y`. -/
theorem gradedMap_exponentSumZModPow_gradedMk_eq_zero_iff {k : ℕ} (i : X)
    (y : pLowerCentralSeries p (freeProP p X) k) :
    gradedMap p (exponentSumZModPow p X (k + 1) i).toMonoidHom
      (exponentSumZModPow p X (k + 1) i).continuous k (gradedMk p (freeProP p X) k y) = 0 ↔
      (p : ℤ_[p]) ^ (k + 1) ∣ (exponentSum p X (y : freeProP p X)).toAdd i := by
  rw [gradedMap_gradedMk, gradedMk_eq_zero_iff, Subgroup.coe_mk,
    MulEquiv.ulift.pLowerCentralSeries_eq_bot_multiplicative_zmod_pow, Subgroup.mem_bot,
    ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass, exponentSumZModPow_eq_one_iff]

/-- The graded map induced by the `i`-th exponent sum modulo `p ^ (k + 1)` sends `π^k x'_i` to
the class `π^k` of the standard generator of `ℤ/pᵏ⁺¹`. -/
theorem gradedMap_exponentSumZModPow_gradedPowIter_gradedMkZero_of_self (k : ℕ) (i : X) :
    gradedMap p (exponentSumZModPow p X (k + 1) i).toMonoidHom
      (exponentSumZModPow p X (k + 1) i).continuous k
        (gradedPowIter p (freeProP p X) k (gradedMkZero p (freeProP p X) (of i))) =
      gradedPowIter p _ k (gradedMkZero p _ (MulEquiv.ulift.symm (Multiplicative.ofAdd 1))) := by
  rw [gradedMap_gradedPowIter, gradedMap_gradedMkZero, ContinuousMonoidHom.coe_toMonoidHom,
    MonoidHom.coe_ofClass, exponentSumZModPow_of_self]

/-- The graded map induced by the `i`-th exponent sum modulo `p ^ (k + 1)` does not kill
`π^k x'_i`: the class `π^k` of the standard generator of `ℤ/pᵏ⁺¹` is nonzero. -/
theorem gradedMap_exponentSumZModPow_gradedPowIter_gradedMkZero_of_self_ne_zero (k : ℕ) (i : X) :
    gradedMap p (exponentSumZModPow p X (k + 1) i).toMonoidHom
      (exponentSumZModPow p X (k + 1) i).continuous k
        (gradedPowIter p (freeProP p X) k (gradedMkZero p (freeProP p X) (of i))) ≠ 0 := by
  rw [gradedMap_exponentSumZModPow_gradedPowIter_gradedMkZero_of_self]
  exact MulEquiv.ulift.gradedPowIter_gradedMkZero_ne_zero_multiplicative_zmod_pow

/-- The graded map induced by the `i`-th exponent sum modulo `p ^ (k + 1)` kills `π^k x'_j` for
`j ≠ i`. -/
theorem gradedMap_exponentSumZModPow_gradedPowIter_gradedMkZero_of_of_ne (k : ℕ) {i j : X}
    (hij : j ≠ i) :
    gradedMap p (exponentSumZModPow p X (k + 1) i).toMonoidHom
      (exponentSumZModPow p X (k + 1) i).continuous k
        (gradedPowIter p (freeProP p X) k (gradedMkZero p (freeProP p X) (of j))) = 0 := by
  rw [gradedMap_gradedPowIter, gradedMap_gradedMkZero, ContinuousMonoidHom.coe_toMonoidHom,
    MonoidHom.coe_ofClass, exponentSumZModPow_of_of_ne p X _ hij, gradedMkZero_one,
    gradedPowIter_zero_right]

end ExponentSum

end freeProP

/-! ### The basis of `gr_1` of a free pro-`p` group -/

namespace freeProP

variable (p : ℕ) [Fact p.Prime] (X : Type u) [Finite X] [LinearOrder X]

/-- **Spanning**: the `p`-power classes and the brackets of the generator classes span
`gr_1(freeProP p X)`. -/
theorem span_range_degreeOneFamily_of_eq_top :
    span (ZMod p) (Set.range (degreeOneFamily p (of : X → freeProP p X))) = ⊤ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  span_range_degreeOneFamily_eq_top
    ((isTopologicallyFinitelyGenerated_freeProP p X).isOpen_pLowerCentralSeries Fact.out 2)
    (topologicalClosure_closure_range_of_eq_top p X)

omit [Finite X] in
/-- A linear relation among the degree-one family of the generators of `freeProP p X` maps to
the same relation among the degree-one family of any family `y : X → H` in a pro-`p` group `H`. -/
private theorem sum_smul_degreeOneFamily_eq_zero [Fintype X] {H : Type u} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
    (hH : IsProP p H)
    (y : X → H) {c : X ⊕ {ij : X × X // ij.1 < ij.2} → ZMod p}
    (hc : ∑ k, c k • degreeOneFamily p (of : X → freeProP p X) k = 0) :
    ∑ k, c k • degreeOneFamily p y k = 0 := by
  have hcomp : ⇑(lift hH y).toMonoidHom ∘ of = y := funext fun x ↦ by simp [lift_of]
  have h := congrArg ((gradedMap p (lift hH y).toMonoidHom (lift hH y).continuous 1).toZModLinearMap
    p) hc
  simpa only [map_sum, map_smul, map_zero, AddMonoidHom.coe_toZModLinearMap,
    gradedMap_degreeOneFamily, hcomp] using h

/-- **Linear independence**: the `p`-power classes `π x'_i` and the brackets `[x'_i, x'_j]` for
`i < j` of the generator classes are linearly independent in `gr_1(freeProP p X)`. The
coefficient of `π x'_i` is read off in `ℤ/p²`, and the coefficient of `[x'_i, x'_j]` in the
Heisenberg group over `𝔽_p`. -/
theorem linearIndependent_degreeOneFamily_of :
    LinearIndependent (ZMod p) (degreeOneFamily p (of : X → freeProP p X)) := by
  classical
  cases nonempty_fintype X
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rintro (i | ⟨⟨i, j⟩, hij⟩)
  · -- The coefficient of `π x'_i`: send `x_i` to the generator of `ℤ/p²` and the others to `1`.
    let e : ULift.{u} (Multiplicative (ZMod (p ^ (1 + 1)))) ≃*
        Multiplicative (ZMod (p ^ (1 + 1))) :=
      MulEquiv.ulift
    have hP : IsProP p (ULift.{u} (Multiplicative (ZMod (p ^ (1 + 1))))) :=
      ((isProP_iff_isPGroup.mp (isProP_multiplicative_zmod_pow p (1 + 1))).of_equiv
        e.symm).isProP
    have h := sum_smul_degreeOneFamily_eq_zero p X hP
      (fun k ↦ if k = i then e.symm (Multiplicative.ofAdd 1) else 1) hc
    rw [Fintype.sum_eq_single (Sum.inl i)] at h
    · refine (smul_eq_zero_iff_left ?_).mp h
      rw [degreeOneFamily_inl]
      simpa using e.gradedPowIter_gradedMkZero_ne_zero_multiplicative_zmod_pow
    · intro k hk
      refine smul_eq_zero_of_right _ ?_
      rcases k with k | ⟨⟨k, l⟩, hkl⟩
      · have hki : k ≠ i := fun h ↦ hk (by rw [h])
        rw [degreeOneFamily_inl]
        simp [hki]
      · rw [degreeOneFamily_inr, gradedBracket_gradedMkZero, gradedMk_eq_zero_iff, Subgroup.coe_mk,
          commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)]
        exact one_mem _
  · -- The coefficient of `[x'_i, x'_j]`: send `x_i, x_j` to the standard generators of the
    -- Heisenberg group over `𝔽_p` and the others to `1`.
    let : TopologicalSpace (ULift.{u} (HeisenbergGroup (ZMod p))) := ⊥
    have : DiscreteTopology (ULift.{u} (HeisenbergGroup (ZMod p))) := ⟨rfl⟩
    let e : ULift.{u} (HeisenbergGroup (ZMod p)) ≃* HeisenbergGroup (ZMod p) := MulEquiv.ulift
    have hP : IsProP p (ULift.{u} (HeisenbergGroup (ZMod p))) :=
      ((HeisenbergGroup.isPGroup_zmod p).of_equiv e.symm).isProP
    let y : X → ULift.{u} (HeisenbergGroup (ZMod p)) := fun k ↦
      if k = i then e.symm ⟨1, 0, 0⟩ else if k = j then e.symm ⟨0, 1, 0⟩ else 1
    have hpow (k : X) : gradedPow p _ 0 (gradedMkZero p _ (y k)) = 0 := by
      simp only [y]
      split_ifs
      · exact e.gradedPow_gradedMkZero_eq_zero_heisenbergGroup rfl (mul_zero _)
      · exact e.gradedPow_gradedMkZero_eq_zero_heisenbergGroup rfl (zero_mul _)
      · rw [gradedMkZero_one, gradedPow_zero]
    have h := sum_smul_degreeOneFamily_eq_zero p X hP y hc
    rw [Fintype.sum_eq_single (Sum.inr ⟨(i, j), hij⟩)] at h
    · refine (smul_eq_zero_iff_left ?_).mp h
      rw [degreeOneFamily_inr]
      simpa [y, hij.ne'] using e.gradedBracket_gradedMkZero_ne_zero_heisenbergGroup
    · intro k hk
      refine smul_eq_zero_of_right _ ?_
      rcases k with k | ⟨⟨k, l⟩, hkl⟩
      · rw [degreeOneFamily_inl, hpow]
      · rw [degreeOneFamily_inr]
        -- Unless `(k, l) = (i, j)`, one of `y k`, `y l` is `1` and its class is `0`.
        have hzero : y k = 1 ∨ y l = 1 := by
          by_cases hki : k = i
          · right
            have hlj : l ≠ j := fun hlj ↦ hk (by subst hki hlj; rfl)
            have hli : l ≠ i := (hki ▸ hkl).ne'
            simp [y, hli, hlj]
          · by_cases hkj : k = j
            · right
              have hli : l ≠ i := (hij.trans (hkj ▸ hkl)).ne'
              have hlj : l ≠ j := (hkj ▸ hkl).ne'
              simp [y, hli, hlj]
            · left
              simp [y, hki, hkj]
        rcases hzero with h | h
        · rw [h, gradedMkZero_one, map_zero, AddMonoidHom.zero_apply]
        · rw [h, gradedMkZero_one, map_zero]

omit [Finite X] [LinearOrder X] in
/-- **The iterated `p`-powers of the generator classes are linearly independent**: for every `j`,
the classes `π^j x'_i ∈ gr_j(freeProP p X)` of the `p ^ j`-th powers of the generators are linearly
independent. The coefficient of `π^j x'_i` is read off in `ℤ/pʲ⁺¹`, by sending `x_i` to the
generator and the other generators to `1`. -/
theorem linearIndependent_gradedPowIter_gradedMkZero_of (j : ℕ) :
    LinearIndependent (ZMod p)
      fun i : X ↦ gradedPowIter p (freeProP p X) j (gradedMkZero p (freeProP p X) (of i)) := by
  classical
  refine linearIndependent_iff'.mpr fun s c hc i hi ↦ ?_
  have h := congrArg ((gradedMap p (exponentSumZModPow p X (j + 1) i).toMonoidHom
    (exponentSumZModPow p X (j + 1) i).continuous j).toZModLinearMap p) hc
  rw [map_sum, map_zero, Finset.sum_eq_single_of_mem i hi fun k _ hk ↦ by
    rw [map_smul, AddMonoidHom.coe_toZModLinearMap,
      gradedMap_exponentSumZModPow_gradedPowIter_gradedMkZero_of_of_ne j hk, smul_zero],
    map_smul, AddMonoidHom.coe_toZModLinearMap] at h
  exact (smul_eq_zero_iff_left
    (gradedMap_exponentSumZModPow_gradedPowIter_gradedMkZero_of_self_ne_zero j i)).mp h

/-- **The standard basis of `gr_1` of a free pro-`p` group of finite rank**: the `p`-power classes
`π x'_i` for `i ∈ X` and the brackets `[x'_i, x'_j]` for `i < j` of the generator classes,
indexed by `X ⊕ {ij : X × X // ij.1 < ij.2}`. -/
noncomputable def degreeOneBasis :
    Module.Basis (X ⊕ {ij : X × X // ij.1 < ij.2}) (ZMod p) (gradedPiece p (freeProP p X) 1) :=
  Module.Basis.mk (linearIndependent_degreeOneFamily_of p X)
    (span_range_degreeOneFamily_of_eq_top p X).ge

@[simp]
theorem degreeOneBasis_apply (k : X ⊕ {ij : X × X // ij.1 < ij.2}) :
    degreeOneBasis p X k = degreeOneFamily p (of : X → freeProP p X) k :=
  Module.Basis.mk_apply _ _ k

omit [LinearOrder X] in
/-- **The generator classes span `gr_0` of a free pro-`p` group of finite rank.** -/
theorem span_gradedMkZero_image_range_of_eq_top :
    span (ZMod p) (gradedMkZero p (freeProP p X) '' Set.range of) = ⊤ :=
  span_gradedMkZero_image_eq_top
    ((isTopologicallyFinitelyGenerated_freeProP p X).isOpen_pLowerCentralSeries Fact.out 1)
    (topologicalClosure_closure_range_of_eq_top p X)

omit [LinearOrder X] in
/-- **The basis of `gr_0` of a free pro-`p` group of finite rank** formed by the classes
`x'_i = ⟦x_i⟧` of the generators: the basis `TauCeti.freeProP.frattiniQuotientBasis` of the
Frattini quotient `F ⧸ Φ(F)`, transported along `gr_0(F) ≅ F ⧸ λ_1(F) = F ⧸ Φ(F)`. -/
noncomputable def degreeZeroBasis : Module.Basis X (ZMod p) (gradedPiece p (freeProP p X) 0) :=
  (frattiniQuotientBasis p X).map <| AddEquiv.toLinearEquiv (R := ZMod p)
    ((gradedPieceZeroEquiv p (freeProP p X)).trans (MulEquiv.toAdditive
      (QuotientGroup.quotientMulEquivOfEq (pLowerCentralSeries_one_eq_proPFrattini Fact.out)))).symm
    (ZMod.map_smul _)

omit [LinearOrder X] in
@[simp]
theorem degreeZeroBasis_apply (i : X) :
    degreeZeroBasis p X i = gradedMkZero p (freeProP p X) (of i) := by
  rw [degreeZeroBasis, Module.Basis.map_apply, AddEquiv.coe_toLinearEquiv, AddEquiv.symm_apply_eq]
  -- The identification `gr_0(F) ≅ F ⧸ Φ(F)` carries `x'_i` to the class `⟦x_i⟧`.
  simp

omit [Finite X] in
/-- **The dimension of `gr_1` of a free pro-`p` group of finite rank** is `#X + (#X choose 2)`:
`gr_1(F) ≅ 𝔽_p^X ⊕ Λ²(𝔽_p^X)`. -/
theorem finrank_gradedPiece_one [Fintype X] :
    Module.finrank (ZMod p) (gradedPiece p (freeProP p X) 1) =
      Fintype.card X + (Fintype.card X).choose 2 := by
  rw [Module.finrank_eq_card_basis (degreeOneBasis p X), Fintype.card_sum, Fintype.card_subtype,
    Fintype.card_product_filter_lt]

omit [LinearOrder X] in
/-- The degree-one graded piece of the free pro-`p` group on a finite type `X` has
`p ^ (#X + (#X choose 2))` elements. -/
@[simp]
theorem natCard_gradedPiece_one :
    Nat.card (gradedPiece p (freeProP p X) 1) = p ^ (Nat.card X + (Nat.card X).choose 2) := by
  have := Fintype.ofFinite X
  -- The degree-one basis is indexed through a linear order on `X`; any one will do.
  let _ := LinearOrder.lift' (Fintype.equivFin X) (Fintype.equivFin X).injective
  have := (isTopologicallyFinitelyGenerated_freeProP p X).finite_gradedPiece (Fact.out : p.Prime) 1
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, finrank_gradedPiece_one,
    Nat.card_eq_fintype_card]

end freeProP

/-! ### The dyadic failure of additivity -/

/-- In the free pro-`2` group of rank two, the bracket of the two canonical generator
classes is nonzero in degree one. -/
theorem gradedBracket_freeProP_two_ne_zero
    (x y : gradedPiece 2 (freeProP 2 (Fin 2)) 0)
    (hx : x = gradedMk 2 _ 0 ⟨freeProP.of (p := 2) (0 : Fin 2), by simp⟩)
    (hy : y = gradedMk 2 _ 0 ⟨freeProP.of (p := 2) (1 : Fin 2), by simp⟩) :
    gradedBracket 2 (freeProP 2 (Fin 2)) 0 0 x y ≠ 0 := by
  subst hx hy
  have h := (freeProP.degreeOneBasis 2 (Fin 2)).ne_zero (Sum.inr ⟨(0, 1), by decide⟩)
  rw [freeProP.degreeOneBasis_apply, degreeOneFamily_inr] at h
  rw [gradedMk_zero, gradedMk_zero, Subgroup.coe_mk, Subgroup.coe_mk]
  exact h

/-- The `2`-power operator fails additivity on the two canonical generator classes of
the free pro-`2` group of rank two. -/
theorem gradedPow_add_freeProP_two_ne
    (x y : gradedPiece 2 (freeProP 2 (Fin 2)) 0)
    (hx : x = gradedMk 2 _ 0 ⟨freeProP.of (p := 2) (0 : Fin 2), by simp⟩)
    (hy : y = gradedMk 2 _ 0 ⟨freeProP.of (p := 2) (1 : Fin 2), by simp⟩) :
    gradedPow 2 (freeProP 2 (Fin 2)) 0 (x + y) ≠
      gradedPow 2 (freeProP 2 (Fin 2)) 0 x + gradedPow 2 (freeProP 2 (Fin 2)) 0 y := by
  intro h
  apply gradedBracket_freeProP_two_ne_zero x y hx hy
  rw [gradedPow_add_zero_of_two rfl] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

/-- The degree-zero `2`-power operator of the free pro-`2` group of rank two is not additive. -/
theorem gradedPow_freeProP_two_not_additive :
    ¬ ∀ x y : gradedPiece 2 (freeProP 2 (Fin 2)) 0,
      gradedPow 2 (freeProP 2 (Fin 2)) 0 (x + y) =
        gradedPow 2 (freeProP 2 (Fin 2)) 0 x + gradedPow 2 (freeProP 2 (Fin 2)) 0 y := by
  intro h
  exact gradedPow_add_freeProP_two_ne _ _ rfl rfl (h _ _)

end TauCeti
