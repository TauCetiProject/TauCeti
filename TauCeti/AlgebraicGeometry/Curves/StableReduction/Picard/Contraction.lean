/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Contraction
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Torsion

/-!
# The Picard group under contraction of a `(-1)`-index

Let `e` be a `(-1)`-index of a numerical type `T` and let `T'` be the contracted numerical type
`TauCeti.NumericalType.contract`, with components those of `T` other than `e`, weights `w'ᵢ` and
intersection numbers `a'ᵢⱼ = aᵢⱼ + aᵢₑaⱼₑ / wₑ`. The map of multidegrees

`p(d)ⱼ = dⱼ (wⱼ / w'ⱼ) + dₑ (aₑⱼ / w'ⱼ)`

carries the multidegree of each component `i ≠ e` of `T` to that of `i` in `T'`, and the
multidegree of `e` to zero. It therefore descends to a homomorphism `Pic(T) → Pic(T')`, which is
injective and whose cokernel is killed by `2`, since each ratio `wⱼ / w'ⱼ` is `1` or `2`
([Stacks, Lemma 55.4.4](https://stacks.math.columbia.edu/tag/0C7J)).

This reduces questions about the torsion of `Pic(T)` to minimal numerical types: the `ℓ`-torsion
of `Pic(T)` has dimension at most that of `Pic(T')`. It also shows that the Picard group of a
numerical type of nonpositive genus is infinite cyclic
([Stacks, Lemma 55.4.5](https://stacks.math.columbia.edu/tag/0C7K)): such a type with more than
one component is not minimal, and contracting a `(-1)`-index preserves the genus.

## Main definitions

* `TauCeti.NumericalType.contractMultidegree`: the map of multidegrees `p` above.
* `TauCeti.NumericalType.picContract`: the induced homomorphism `Pic(T) → Pic(T')`.

## Main results

* `TauCeti.NumericalType.picContract_injective`: `Pic(T) → Pic(T')` is injective.
* `TauCeti.NumericalType.two_smul_mem_range_picContract`: its cokernel is killed by `2`.
* `TauCeti.NumericalType.finrank_torsion_le_contract`: `dim Pic(T)[ℓ] ≤ dim Pic(T')[ℓ]` for
  every prime `ℓ`.
* `TauCeti.NumericalType.nonempty_pic_linearEquiv_int`: if the genus of `T` is at most zero,
  then `Pic(T) ≅ ℤ`.

## References

The map `p` and the proofs of injectivity and of the bound on the cokernel follow
[Stacks, Lemma 55.4.4](https://stacks.math.columbia.edu/tag/0C7J), and the induction on the number
of components that of [Stacks, Lemma 55.4.5](https://stacks.math.columbia.edu/tag/0C7K), in
[Stacks, Section 55.4](https://stacks.math.columbia.edu/tag/0C7G).
-/

public section

namespace TauCeti

namespace NumericalType

open Finset Matrix

universe u

variable {T : NumericalType.{u}} {e : T.Component} (he : T.IsMinusOneIndex e)

/-! ### The map of multidegrees -/

/-- The contracted weight `w'ⱼ` divides `aₑⱼ`, since it divides `wⱼ`. -/
private lemma contractWeight_dvd_intersection (j : {i // i ≠ e}) :
    (T.contractWeight e j : ℤ) ∣ T.intersection e j :=
  (contractWeight_dvd_weight (e := e) j).trans (T.weight_dvd_intersection e j)

/-- The map of multidegrees `p(d)ⱼ = dⱼ (wⱼ / w'ⱼ) + dₑ (aₑⱼ / w'ⱼ)` from a numerical type to its
contraction along the `(-1)`-index `e`. It sends the multidegree of every component `i ≠ e` to the
multidegree of `i` in the contraction and the multidegree of `e` to zero; see
`TauCeti.NumericalType.contractMultidegree_vecMul_weightedIntersection`. -/
def contractMultidegree : (T.Component → ℤ) →ₗ[ℤ] (T.contract he).Component → ℤ :=
  LinearMap.pi fun j : {i // i ≠ e} ↦
    ((T.weight j : ℤ) / T.contractWeight e j) • LinearMap.proj (R := ℤ) (j : T.Component) +
      (T.intersection e j / T.contractWeight e j) • LinearMap.proj (R := ℤ) e

/-- The coordinates of `TauCeti.NumericalType.contractMultidegree`. -/
lemma contractMultidegree_apply (d : T.Component → ℤ) (j : {i // i ≠ e}) :
    T.contractMultidegree he d j = (T.weight j : ℤ) / T.contractWeight e j * d j +
      T.intersection e j / T.contractWeight e j * d e :=
  (rfl)

/-- The coordinates of `TauCeti.NumericalType.contractMultidegree` with the exact divisions by
`w'ⱼ` cleared: `p(d)ⱼ w'ⱼ = dⱼwⱼ + dₑaₑⱼ`. -/
lemma contractMultidegree_mul_contractWeight (d : T.Component → ℤ)
    (j : {i // i ≠ e}) :
    T.contractMultidegree he d j * T.contractWeight e j =
      d j * T.weight j + d e * T.intersection e j := by
  obtain ⟨a, ha⟩ := contractWeight_dvd_weight (e := e) j
  obtain ⟨b, hb⟩ := contractWeight_dvd_intersection (e := e) j
  rw [contractMultidegree_apply, ha, hb, Int.mul_ediv_cancel_left _ (by positivity),
    Int.mul_ediv_cancel_left _ (by positivity)]
  ring

/-- Two multidegrees of the contraction agree once their coordinates agree after multiplication by
the weights `w'ⱼ`; this clears the exact divisions in `contractMultidegree`. -/
private lemma eq_of_mul_contractWeight {x y : {i // i ≠ e} → ℤ}
    (h : ∀ j, x j * T.contractWeight e j = y j * T.contractWeight e j) : x = y :=
  funext fun j ↦ mul_right_cancel₀ (by positivity) (h j)

/-- The map of multidegrees sends the multidegree of a component `i ≠ e` to the multidegree of
`i` in the contraction. -/
lemma contractMultidegree_row (i : {i // i ≠ e}) :
    T.contractMultidegree he (T.weightedIntersection i) = (T.contract he).weightedIntersection i :=
  eq_of_mul_contractWeight fun j ↦ by
    have hj := (T.contract he).weightedIntersection_mul_weight i j
    have hie := Int.ediv_mul_cancel (T.weight_dvd_intersection i e)
    have hcontract := T.weight_mul_contractIntersection i j
    rw [contract_weight, contract_intersection] at hj
    rw [contractMultidegree_mul_contractWeight, hj, weightedIntersection_apply,
      weightedIntersection_apply, Int.ediv_mul_cancel (T.weight_dvd_intersection i j),
      T.intersection_comm e j]
    refine mul_left_cancel₀ (a := (T.weight e : ℤ)) (by positivity) ?_
    linear_combination (T.intersection j e) * hie - hcontract

/-- The map of multidegrees kills the multidegree of the contracted component `e`. -/
lemma contractMultidegree_row_self :
    T.contractMultidegree he (T.weightedIntersection e) = 0 :=
  eq_of_mul_contractWeight fun j ↦ by
    have hself : T.weightedIntersection e e = -1 := by
      rw [weightedIntersection_apply, (T.isMinusOneIndex_iff.mp he).2,
        Int.neg_ediv_self _ (by positivity)]
    have hj := T.weightedIntersection_mul_weight e j
    rw [contractMultidegree_mul_contractWeight, hself, hj]
    -- `0 j` is the zero multidegree of the contraction evaluated at `j`.
    exact (by ring : _ = (0 : ℤ)).trans (zero_mul _).symm

/-- The map of multidegrees intertwines the weighted intersection matrices: the image of a
combination `v` of the multidegrees of the components of `T` is the same combination, with the
coefficient of `e` dropped, of the multidegrees of the components of the contraction. -/
lemma contractMultidegree_vecMul_weightedIntersection (v : T.Component → ℤ) :
    T.contractMultidegree he (v ᵥ* T.weightedIntersection) =
      (fun i : {i // i ≠ e} ↦ v i) ᵥ* (T.contract he).weightedIntersection := by
  -- The vector-matrix product of the contraction is indexed by its own component type, so its
  -- expansion as a sum is applied by unification rather than by rewriting.
  refine Eq.trans ?_ (vecMul_eq_sum _ _).symm
  rw [vecMul_eq_sum, map_sum, ← Finset.add_sum_erase _ _ (mem_univ e), map_smul,
    contractMultidegree_row_self, smul_zero, zero_add,
    Finset.sum_subtype (p := (· ≠ e)) (univ.erase e) (by simp)]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, contractMultidegree_row]

/-- A multidegree killed by the map of multidegrees is principal: it is a multiple of the
multidegree of `e`. -/
lemma mem_principalDivisors_of_contractMultidegree_eq_zero {d : T.Component → ℤ}
    (hd : T.contractMultidegree he d = 0) : d ∈ T.principalDivisors := by
  refine T.mem_principalDivisors_iff.mpr ⟨Pi.single e (-d e), funext fun j ↦ ?_⟩
  rw [single_vecMul, Pi.smul_apply, row_apply, smul_eq_mul, weightedIntersection_apply]
  by_cases hj : j = e
  · subst hj
    rw [(T.isMinusOneIndex_iff.mp he).2, Int.neg_ediv_self _ (by positivity)]
    ring
  · -- Away from `e`, the vanishing of `p(d)ⱼ w'ⱼ = dⱼwⱼ + dₑaₑⱼ` determines `dⱼ`.
    have h0 : T.contractMultidegree he d ⟨j, hj⟩ = 0 := congrFun hd ⟨j, hj⟩
    have h := T.contractMultidegree_mul_contractWeight he d ⟨j, hj⟩
    rw [h0, zero_mul] at h
    obtain ⟨c, hc⟩ := T.weight_dvd_intersection e j
    rw [hc, Int.mul_ediv_cancel_left _ (by positivity)]
    rw [hc] at h
    refine mul_left_cancel₀ (a := (T.weight j : ℤ)) (by positivity) ?_
    linear_combination h

/-! ### The homomorphism of Picard groups -/

/-- The principal multidegrees of `T` map to principal multidegrees of its contraction. -/
lemma principalDivisors_le_comap_contractMultidegree :
    T.principalDivisors ≤ (T.contract he).principalDivisors.comap (T.contractMultidegree he) := by
  intro d hd
  obtain ⟨v, rfl⟩ := T.mem_principalDivisors_iff.mp hd
  rw [Submodule.mem_comap, contractMultidegree_vecMul_weightedIntersection]
  exact (T.contract he).mem_principalDivisors_iff.mpr ⟨_, rfl⟩

/-- The homomorphism `Pic(T) → Pic(T')` from the Picard group of a numerical type to that of its
contraction along a `(-1)`-index, induced by `TauCeti.NumericalType.contractMultidegree`
([Stacks, Lemma 55.4.4](https://stacks.math.columbia.edu/tag/0C7J)). -/
def picContract : T.Pic →ₗ[ℤ] (T.contract he).Pic :=
  Submodule.mapQ _ _ (T.contractMultidegree he)
    (T.principalDivisors_le_comap_contractMultidegree he)

/-- The homomorphism of Picard groups on the class of a multidegree. -/
@[simp]
lemma picContract_mk (d : T.Component → ℤ) :
    T.picContract he (Submodule.Quotient.mk d) =
      Submodule.Quotient.mk (T.contractMultidegree he d) :=
  (rfl)

/-- The homomorphism `Pic(T) → Pic(T')` is injective
([Stacks, Lemma 55.4.4](https://stacks.math.columbia.edu/tag/0C7J)). -/
theorem picContract_injective : Function.Injective (T.picContract he) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H d =>
    rw [picContract_mk, Submodule.Quotient.mk_eq_zero,
      (T.contract he).mem_principalDivisors_iff] at hx
    obtain ⟨v', hv'⟩ := hx
    -- Extend `v'` by zero at `e`: the combination `v` of multidegrees of `T` has the same image
    -- as `d`, so `d - v` is killed by the map of multidegrees.
    set v : T.Component → ℤ := Function.extend Subtype.val v' 0 with hv
    have hrestrict : (fun i : {i // i ≠ e} ↦ v i) = v' :=
      funext fun i ↦ Subtype.val_injective.extend_apply v' 0 i
    have hker : T.contractMultidegree he (d - v ᵥ* T.weightedIntersection) = 0 := by
      rw [map_sub, contractMultidegree_vecMul_weightedIntersection, hrestrict]
      exact sub_eq_zero_of_eq hv'.symm
    have hmem := T.mem_principalDivisors_of_contractMultidegree_eq_zero he hker
    rw [Submodule.Quotient.mk_eq_zero]
    simpa using T.principalDivisors.add_mem hmem (T.mem_principalDivisors_iff.mpr ⟨v, rfl⟩)

/-- The cokernel of `Pic(T) → Pic(T')` is killed by `2`: twice every class of the contraction
comes from `Pic(T)` ([Stacks, Lemma 55.4.4](https://stacks.math.columbia.edu/tag/0C7J)). -/
theorem two_smul_mem_range_picContract (y : (T.contract he).Pic) :
    (2 : ℤ) • y ∈ LinearMap.range (T.picContract he) := by
  induction y using Submodule.Quotient.induction_on with
  | H d' =>
    -- `d'` is a multidegree of the contraction, a function on the components other than `e`.
    let d'' : {i // i ≠ e} → ℤ := d'
    -- Each ratio `wⱼ / w'ⱼ` is `2` when the weight is halved and `1` otherwise.
    let d : T.Component → ℤ := fun i ↦
      if h : i = e then 0
      else if T.ContractHalvesWeight e (⟨i, h⟩ : {i // i ≠ e}) then d'' ⟨i, h⟩
      else 2 * d'' ⟨i, h⟩
    refine ⟨Submodule.Quotient.mk d, ?_⟩
    rw [picContract_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    refine eq_of_mul_contractWeight fun j ↦ ?_
    -- Scalar multiplication on the multidegrees of the contraction is pointwise.
    have h2 : ((2 : ℤ) • d') j = 2 * d'' j := (rfl)
    rw [contractMultidegree_mul_contractWeight, h2]
    by_cases hj : T.ContractHalvesWeight e j
    · simp only [d, j.2, hj, ↓reduceDIte, ↓reduceIte, zero_mul, add_zero]
      rw [← two_mul_contractWeight hj]
      ring
    · simp only [d, j.2, hj, ↓reduceDIte, ↓reduceIte, zero_mul, add_zero,
        contractWeight_of_not hj]

/-! ### Consequences -/

/-- The `ℓ`-torsion of `Pic(T)` has dimension at most that of `Pic(T')`, for every prime `ℓ`.
This reduces bounds on the prime torsion of Picard groups of numerical types to minimal numerical
types. -/
theorem finrank_torsion_le_contract (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank (ZMod ℓ) (T.torsion ℓ) ≤
      Module.finrank (ZMod ℓ) ((T.contract he).torsion ℓ) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let f : T.torsion ℓ →+ (T.contract he).torsion ℓ :=
    ((T.picContract he).toAddMonoidHom.comp (T.torsion ℓ).subtype).codRestrict _ fun x ↦ by
      rw [AddSubgroup.torsionBy.nsmul_iff]
      have hx : ℓ • (x : T.Pic) = 0 := AddSubgroup.torsionBy.nsmul_iff.mp x.property
      simpa only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, LinearMap.toAddMonoidHom_coe,
        map_nsmul, map_zero] using congrArg (T.picContract he) hx
  refine LinearMap.finrank_le_finrank_of_injective (f := f.toZModLinearMap ℓ) fun x y hxy ↦ ?_
  exact Subtype.ext (T.picContract_injective he (congrArg Subtype.val hxy))

/-- The Picard group of a numerical type of nonpositive genus is torsion-free. -/
private lemma isTorsionFree_pic_of_arithmeticGenus_nonpos {n : ℕ} :
    ∀ T : NumericalType.{u}, Fintype.card T.Component = n → T.arithmeticGenus ≤ 0 →
      Module.IsTorsionFree ℤ T.Pic := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hn hg
  rcases Nat.lt_or_ge 1 (Fintype.card T.Component) with hcard | hcard
  · -- With more than one component, `T` is not minimal: contract a `(-1)`-index.
    have hmin : ¬ T.IsMinimal := fun hT ↦ by
      have := hT.one_le_arithmeticGenus hcard
      omega
    obtain ⟨e, he⟩ : ∃ e, T.IsMinusOneIndex e := by
      simpa [isMinimal_iff] using hmin
    have hcard' : Fintype.card (T.contract he).Component < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (p := (· ≠ e)) (x := e) (by simp)
    have := ih _ hcard' (T.contract he) rfl ((arithmeticGenus_contract he).trans_le hg)
    exact (T.picContract_injective he).moduleIsTorsionFree _ (map_smul _)
  · -- With a single component, the intersection matrix vanishes and `Pic(T)` is `ℤ`.
    have h1 : Fintype.card T.Component = 1 := le_antisymm hcard Fintype.card_pos
    have hbot : T.principalDivisors = ⊥ := by
      rw [eq_bot_iff]
      intro d hd
      obtain ⟨v, rfl⟩ := T.mem_principalDivisors_iff.mp hd
      have hzero : T.weightedIntersection = 0 := by
        ext i j
        simp [T.intersection_eq_zero_of_card_eq_one h1 i j]
      simp [hzero]
    exact (Submodule.quotEquivOfEqBot _ hbot).injective.moduleIsTorsionFree _ (map_smul _)

/-- The Picard group of a numerical type of genus at most zero is infinite cyclic
([Stacks, Lemma 55.4.5](https://stacks.math.columbia.edu/tag/0C7K)). -/
theorem nonempty_pic_linearEquiv_int (T : NumericalType.{u}) (hg : T.arithmeticGenus ≤ 0) :
    Nonempty (T.Pic ≃ₗ[ℤ] ℤ) := by
  have := isTorsionFree_pic_of_arithmeticGenus_nonpos T rfl hg
  exact ⟨(Module.finBasisOfFinrankEq ℤ T.Pic T.finrank_pic).equivFun.trans
    (LinearEquiv.funUnique (Fin 1) ℤ ℤ)⟩

end NumericalType

end TauCeti
