/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import TauCeti.Analysis.VonNeumannAlgebra.Group.Basic
import TauCeti.GroupTheory.FreeGroup.Conjugacy.Infinite

/-!
# The center of a group von Neumann algebra and the Murray–von Neumann ICC factor theorem

Let `Γ` be a group with measurable multiplication and measurable singletons on its counting-measure
space (in particular any discrete group `[DiscreteMeasurableSpace Γ]`, countable or uncountable).

Conjugating an operator `x ∈ groupVonNeumannAlgebra Γ` by a left regular unitary `λ_k` conjugates
its Fourier coefficients: `c_g(λ_k * x * λ_{k⁻¹}) = c_{k⁻¹ * g * k}(x)`
(`TauCeti.groupVonNeumannCoeff_leftRegular_conj`). Because Fourier coefficients separate elements of
`groupVonNeumannAlgebra Γ`, an element `x ∈ groupVonNeumannAlgebra Γ` belongs to the commutant
`(groupVonNeumannAlgebra Γ).commutant` if and only if `groupVonNeumannCoeff x` is constant on the
conjugacy classes of `Γ` (`TauCeti.mem_commutant_groupVonNeumannAlgebra_iff`).

Comparing this conjugacy-invariance with the square-summability of `groupVonNeumannCoeff x` yields
**Murray and von Neumann's ICC factor criterion** (`TauCeti.isFactor_groupVonNeumannAlgebra_iff`):
`groupVonNeumannAlgebra Γ` is a factor if and only if every nonidentity element of `Γ` has an
infinite conjugacy class. As immediate consequences:

* `TauCeti.not_isFactor_groupVonNeumannAlgebra_of_isMulCommutative`: for a nontrivial commutative
  group, `groupVonNeumannAlgebra Γ` is not a factor.
* `TauCeti.isFactor_groupVonNeumannAlgebra_of_isFreeGroup` and
  `TauCeti.isFactor_groupVonNeumannAlgebra_freeGroup`: for any nonabelian free group (in particular
  `FreeGroup α` with `[Nontrivial α]`), `groupVonNeumannAlgebra` is a factor.

## References

* F. J. Murray and J. von Neumann, *On rings of operators. IV*, Ann. of Math. (2) **44** (1943),
  716–808, Lemma 5.3.4.
* J. Peterson, *Notes on von Neumann Algebras* (2013), Theorem 5.1.6.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Proposition 1.3.7.
-/

public section

open MeasureTheory VonNeumannAlgebra
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- Finite-sum linearity of `groupVonNeumannCoeff`. -/
theorem groupVonNeumannCoeff_sum {Γ ι : Type*} [One Γ] [MeasurableSpace Γ]
    [MeasurableSingletonClass Γ] (s : Finset ι)
    (f : ι → Lp ℂ 2 (Measure.count : Measure Γ) →L[ℂ] Lp ℂ 2 (Measure.count : Measure Γ))
    (g : Γ) :
    groupVonNeumannCoeff (∑ i ∈ s, f i) g = ∑ i ∈ s, groupVonNeumannCoeff (f i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

section Center

variable {Γ : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]

/-- Conjugating `x ∈ groupVonNeumannAlgebra Γ` by `λ_k` shifts its `g`-th Fourier coefficient to
`k⁻¹ * g * k`. -/
theorem groupVonNeumannCoeff_leftRegular_conj
    {x : Lp ℂ 2 (Measure.count : Measure Γ) →L[ℂ] Lp ℂ 2 (Measure.count : Measure Γ)}
    (hx : x ∈ groupVonNeumannAlgebra Γ) (k g : Γ) :
    groupVonNeumannCoeff
      ((Measure.count : Measure Γ).leftRegular ℂ ℂ 2 k * x *
        (Measure.count : Measure Γ).leftRegular ℂ ℂ 2 k⁻¹) g =
      groupVonNeumannCoeff x (k⁻¹ * g * k) := by
  rw [groupVonNeumannCoeff_def, mul_apply_eq_comp, mul_apply_eq_comp,
    leftRegular_countHilbertBasis, mul_one,
    (Measure.isUnitary_leftRegular Measure.count).inner_map_right,
    leftRegular_countHilbertBasis, apply_countHilbertBasis_eq_rightRegular hx k⁻¹, inv_inv,
    (Measure.isUnitary_rightRegular Measure.count).inner_map_right,
    rightRegular_countHilbertBasis, inv_inv, groupVonNeumannCoeff_def]

/-- **Center characterization of `groupVonNeumannAlgebra Γ`.** An operator
`x ∈ groupVonNeumannAlgebra Γ` lies in `(groupVonNeumannAlgebra Γ).commutant` if and only if its
Fourier coefficients are constant on conjugacy classes of `Γ`. -/
theorem mem_commutant_groupVonNeumannAlgebra_iff
    {x : Lp ℂ 2 (Measure.count : Measure Γ) →L[ℂ] Lp ℂ 2 (Measure.count : Measure Γ)}
    (hx : x ∈ groupVonNeumannAlgebra Γ) :
    x ∈ (groupVonNeumannAlgebra Γ).commutant ↔
      ∀ g h : Γ, IsConj g h → groupVonNeumannCoeff x g = groupVonNeumannCoeff x h := by
  refine ⟨fun hx' g h hgh => ?_, fun hconj => ?_⟩
  · obtain ⟨k, rfl⟩ := isConj_iff.1 hgh
    have hcomm : (Measure.count : Measure Γ).leftRegular ℂ ℂ 2 k * x =
        x * (Measure.count : Measure Γ).leftRegular ℂ ℂ 2 k :=
      mem_commutant_groupVonNeumannAlgebra_iff_leftRegular.1 hx' k
    have hconj_eq :
        (Measure.count : Measure Γ).leftRegular ℂ ℂ 2 k * x *
          (Measure.count : Measure Γ).leftRegular ℂ ℂ 2 k⁻¹ = x := by
      rw [hcomm, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have hcoeff := groupVonNeumannCoeff_leftRegular_conj hx k (k * g * k⁻¹)
    have hkg : k⁻¹ * (k * g * k⁻¹) * k = g := by group
    rw [hconj_eq, hkg] at hcoeff
    exact hcoeff.symm
  · refine mem_commutant_groupVonNeumannAlgebra_iff_leftRegular.2 fun k => ?_
    let lk := (Measure.count : Measure Γ).leftRegular ℂ ℂ 2 k
    let lki := (Measure.count : Measure Γ).leftRegular ℂ ℂ 2 k⁻¹
    have hconj_mem : lk * x * lki ∈ groupVonNeumannAlgebra Γ :=
      (groupVonNeumannAlgebra Γ).mul_mem
        ((groupVonNeumannAlgebra Γ).mul_mem (leftRegular_mem_groupVonNeumannAlgebra k) hx)
        (leftRegular_mem_groupVonNeumannAlgebra k⁻¹)
    have hconj_eq : lk * x * lki = x := by
      refine eq_of_groupVonNeumannCoeff_eq hconj_mem hx fun g => ?_
      rw [groupVonNeumannCoeff_leftRegular_conj hx k g]
      exact hconj (k⁻¹ * g * k) g (isConj_iff.2 ⟨k, by group⟩)
    calc lk * x = (lk * x * lki) * lk := by
          simp only [lk, lki, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
      _ = x * lk := by rw [hconj_eq]

/-- The `x`-th Fourier coefficient of a finite sum of left regular unitaries over `s` is the
indicator of `x ∈ s`. -/
@[simp]
theorem groupVonNeumannCoeff_sum_leftRegular [DecidableEq Γ] (s : Finset Γ) (x : Γ) :
    groupVonNeumannCoeff
      (∑ h ∈ s, (Measure.count : Measure Γ).leftRegular ℂ ℂ 2 h) x =
      if x ∈ s then 1 else 0 := by
  rw [groupVonNeumannCoeff_sum]
  by_cases hx : x ∈ s
  · simp only [hx, ↓reduceIte]
    exact (Finset.sum_eq_single x (fun h _ hne => groupVonNeumannCoeff_leftRegular_of_ne hne.symm)
      (fun hxs => absurd hx hxs)).trans (groupVonNeumannCoeff_leftRegular_self x)
  · simp only [hx, ↓reduceIte]
    refine Finset.sum_eq_zero fun h hh => groupVonNeumannCoeff_leftRegular_of_ne ?_
    rintro rfl
    exact hx hh

variable (Γ) in
/-- **The ICC factor theorem** (Murray–von Neumann). The group von Neumann algebra
`groupVonNeumannAlgebra Γ` is a factor if and only if every conjugacy class of `Γ` other than `{1}`
is infinite. No countability of `Γ` is assumed. -/
theorem isFactor_groupVonNeumannAlgebra_iff :
    (groupVonNeumannAlgebra Γ).IsFactor ↔ ∀ g : Γ, g ≠ 1 → {h : Γ | IsConj g h}.Infinite := by
  rw [isFactor_def]
  refine ⟨fun ⟨_, hcenter⟩ g hg => ?_, fun hicc => ⟨?_, fun x hx hx' => ?_⟩⟩
  · by_contra hfin
    rw [Set.not_infinite] at hfin
    classical
    let z := ∑ h ∈ hfin.toFinset, (Measure.count : Measure Γ).leftRegular ℂ ℂ 2 h
    have hz : z ∈ groupVonNeumannAlgebra Γ :=
      sum_mem fun h _ => leftRegular_mem_groupVonNeumannAlgebra h
    have hz_coeff (x : Γ) :
        groupVonNeumannCoeff z x = if IsConj g x then 1 else 0 := by
      simpa only [z, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using
        groupVonNeumannCoeff_sum_leftRegular hfin.toFinset x
    have hz' : z ∈ (groupVonNeumannAlgebra Γ).commutant :=
      (mem_commutant_groupVonNeumannAlgebra_iff hz).2 fun x y hxy => by
        have hiff : IsConj g x ↔ IsConj g y := ⟨fun h => h.trans hxy, fun h => h.trans hxy.symm⟩
        simp only [hz_coeff, hiff]
    obtain ⟨c, hzc⟩ := hcenter z hz hz'
    have hc0 : c = 0 := by
      have h1 := congr_arg (fun w => groupVonNeumannCoeff w 1) hzc
      simpa [hz_coeff, hg] using h1.symm
    have hg_eq := congr_arg (fun w => groupVonNeumannCoeff w g) hzc
    rw [hz_coeff, hc0, zero_smul, groupVonNeumannCoeff_zero] at hg_eq
    simp only [IsConj.refl g, ↓reduceIte, one_ne_zero] at hg_eq
  · intro h10
    have h := congr_arg (fun w => groupVonNeumannCoeff w 1) h10
    simp only [groupVonNeumannCoeff_one_one, groupVonNeumannCoeff_zero, one_ne_zero] at h
  · refine ⟨groupVonNeumannCoeff x 1, eq_of_groupVonNeumannCoeff_eq hx
      ((groupVonNeumannAlgebra Γ).toStarSubalgebra.smul_mem
        (groupVonNeumannAlgebra Γ).one_mem _) fun g => ?_⟩
    by_cases hg : g = 1
    · subst hg
      simp
    · rw [groupVonNeumannCoeff_smul, groupVonNeumannCoeff_one_of_ne hg, mul_zero]
      have : Infinite {h : Γ // IsConj g h} := (hicc g hg).to_subtype
      have hconst (h : {h : Γ // IsConj g h}) :
          groupVonNeumannCoeff x h.1 = groupVonNeumannCoeff x g :=
        ((mem_commutant_groupVonNeumannAlgebra_iff hx).1 hx' g h.1 h.2).symm
      have hsum : Summable fun _ : {h : Γ // IsConj g h} => ‖groupVonNeumannCoeff x g‖ ^ 2 :=
        ((summable_norm_sq_groupVonNeumannCoeff x).comp_injective Subtype.val_injective).congr
          fun h => by simp [hconst h]
      exact norm_eq_zero.1 (sq_eq_zero_iff.1 ((summable_const_iff _).1 hsum))

end Center

/-! ### Abelian and free-group corollaries -/

/-- For a nontrivial commutative group, `groupVonNeumannAlgebra Γ` is not a factor. -/
theorem not_isFactor_groupVonNeumannAlgebra_of_isMulCommutative (Γ : Type*) [Group Γ]
    [Nontrivial Γ] [IsMulCommutative Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
    [MeasurableSingletonClass Γ] :
    ¬ (groupVonNeumannAlgebra Γ).IsFactor := by
  rw [isFactor_groupVonNeumannAlgebra_iff]
  push Not
  obtain ⟨g, hg⟩ := exists_ne (1 : Γ)
  refine ⟨g, hg, (Set.finite_singleton g).subset fun h hh => ?_⟩
  obtain ⟨k, rfl⟩ := isConj_iff.1 hh
  rw [Set.mem_singleton_iff, isMulCommutative_iff.1 ‹_› k g]
  group

/-- The group von Neumann algebra of a nonabelian free group is a factor. -/
theorem isFactor_groupVonNeumannAlgebra_of_isFreeGroup (Γ : Type*) [Group Γ] [IsFreeGroup Γ]
    [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
    (h : ¬ IsMulCommutative Γ) :
    (groupVonNeumannAlgebra Γ).IsFactor :=
  (isFactor_groupVonNeumannAlgebra_iff Γ).2 fun _ => IsFreeGroup.infinite_setOf_isConj h

/-- When `α` has at least two elements, `groupVonNeumannAlgebra (FreeGroup α)` is a factor. -/
theorem isFactor_groupVonNeumannAlgebra_freeGroup (α : Type*) [Nontrivial α]
    [MeasurableSpace (FreeGroup α)] [MeasurableMul (FreeGroup α)]
    [MeasurableSingletonClass (FreeGroup α)] :
    (groupVonNeumannAlgebra (FreeGroup α)).IsFactor :=
  (isFactor_groupVonNeumannAlgebra_iff (FreeGroup α)).2 fun _ => FreeGroup.infinite_setOf_isConj

end TauCeti
