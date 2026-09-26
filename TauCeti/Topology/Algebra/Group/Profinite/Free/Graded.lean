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
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries

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
two finite `p`-groups of `p`-class two used as detecting groups are `ℤ/p²` and the Heisenberg
group over `𝔽_p`.

At `p = 2` the bracket `[x'_0, x'_1]` in `gr_1(freeProP 2 (Fin 2))` is therefore nonzero, and the
degree-zero power-defect formula shows that the `2`-power operator on this free pro-`2` group is
not additive.

## Main definitions

* `TauCeti.freeProP.degreeOneBasis`: the basis `π x'_i`, `[x'_i, x'_j]` (`i < j`) of `gr_1(F)`.

## Main results

* `TauCeti.freeProP.linearIndependent_degreeOneFamily_of`: the family is linearly independent.
* `TauCeti.freeProP.finrank_gradedPiece_one`: `dim gr_1(F) = #X + (#X choose 2)`.
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

/-! ### The two detecting groups

The lower `p`-series of a finite discrete group is its abstract lower `p`-central series, so the
computations below are transported from
`Subgroup.top_pLowerCentralSeries_eq_range_powMonoidHom` and
`TauCeti.HeisenbergGroup.pLowerCentralSeries_top_two_eq_bot` along a group isomorphism, which
lets the detecting groups live in any universe. -/

section Detecting

variable {p : ℕ}

/-- **The cyclic group `ℤ/p²` has `p`-class at most two** (for `p > 0` it has order `p ^ 2`). -/
theorem top_pLowerCentralSeries_multiplicative_zmod_sq_two_eq_bot :
    (⊤ : Subgroup (Multiplicative (ZMod (p ^ 2)))).pLowerCentralSeries p 2 = ⊥ := by
  rw [Subgroup.top_pLowerCentralSeries_eq_range_powMonoidHom, MonoidHom.range_eq_bot_iff]
  refine MonoidHom.ext fun x ↦ ?_
  rw [powMonoidHom_apply, MonoidHom.one_apply, ← ofAdd_toAdd x, ← ofAdd_nsmul, nsmul_eq_mul,
    ZMod.natCast_self, zero_mul, ofAdd_zero]

variable {H : Type u} [Group H] [TopologicalSpace H] [DiscreteTopology H]

/-- A discrete group isomorphic to `ℤ/p²` has `p`-class at most two. -/
theorem _root_.MulEquiv.pLowerCentralSeries_two_eq_bot_multiplicative_zmod_sq
    (e : H ≃* Multiplicative (ZMod (p ^ 2))) : pLowerCentralSeries p H 2 = ⊥ := by
  rw [← Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective,
    e.map_pLowerCentralSeries_eq_of_discreteTopology, pLowerCentralSeries_eq_of_discreteTopology,
    top_pLowerCentralSeries_multiplicative_zmod_sq_two_eq_bot]

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

/-- The `p`-th power of the generator of `ℤ/p²` is nontrivial. -/
theorem ofAdd_one_pow_ne_one : (Multiplicative.ofAdd (1 : ZMod (p ^ 2))) ^ p ≠ 1 := by
  have hp : p.Prime := Fact.out
  rw [← ofAdd_nsmul, ne_eq, ofAdd_eq_one, nsmul_one, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd hp.pos h
  nlinarith [hp.two_le]

/-- In a discrete group isomorphic to `ℤ/p²`, the `p`-power class of the generator is nonzero. -/
theorem _root_.MulEquiv.gradedPow_gradedMkZero_ne_zero_multiplicative_zmod_sq
    (e : H ≃* Multiplicative (ZMod (p ^ 2))) :
    gradedPow p H 0 (gradedMkZero p H (e.symm (Multiplicative.ofAdd 1))) ≠ 0 := by
  rw [gradedPow_gradedMkZero, ne_eq, gradedMk_eq_zero_iff, Subgroup.coe_mk]
  simp only [Nat.reduceAdd]
  rw [e.pLowerCentralSeries_two_eq_bot_multiplicative_zmod_sq, Subgroup.mem_bot,
    ← map_pow, e.symm.map_eq_one_iff]
  exact ofAdd_one_pow_ne_one

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
    let e : ULift.{u} (Multiplicative (ZMod (p ^ 2))) ≃* Multiplicative (ZMod (p ^ 2)) :=
      MulEquiv.ulift
    have hP : IsProP p (ULift.{u} (Multiplicative (ZMod (p ^ 2)))) :=
      ((isProP_iff_isPGroup.mp (isProP_multiplicative_zmod_pow p 2)).of_equiv e.symm).isProP
    have h := sum_smul_degreeOneFamily_eq_zero p X hP
      (fun k ↦ if k = i then e.symm (Multiplicative.ofAdd 1) else 1) hc
    rw [Fintype.sum_eq_single (Sum.inl i)] at h
    · refine (smul_eq_zero_iff_left ?_).mp h
      rw [degreeOneFamily_inl]
      simpa using e.gradedPow_gradedMkZero_ne_zero_multiplicative_zmod_sq
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

omit [Finite X] in
/-- **The dimension of `gr_1` of a free pro-`p` group of finite rank** is `#X + (#X choose 2)`:
`gr_1(F) ≅ 𝔽_p^X ⊕ Λ²(𝔽_p^X)`. -/
theorem finrank_gradedPiece_one [Fintype X] :
    Module.finrank (ZMod p) (gradedPiece p (freeProP p X) 1) =
      Fintype.card X + (Fintype.card X).choose 2 := by
  rw [Module.finrank_eq_card_basis (degreeOneBasis p X), Fintype.card_sum, Fintype.card_subtype,
    Fintype.card_product_filter_lt]

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
