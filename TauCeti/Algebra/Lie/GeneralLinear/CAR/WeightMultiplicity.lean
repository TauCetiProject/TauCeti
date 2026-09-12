/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.CAR.HighestWeight
import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
import TauCeti.Algebra.Lie.GeneralLinear.CAR.Occupation
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.Dimension.FixedSubmodule
import TauCeti.RingTheory.Idempotents.Eigenvalue

/-!
# The top-weight multiplicity of the CAR module

For the left regular action of `gl_N` on the Clifford algebra of the trace form, this file computes
the dimension of the half-staircase Cartan weight space.  The positive-pair occupation elements
`pᵢⱼ`, `i < j`, are commuting idempotents, and this weight space is their common fixed space.

Each additional fixed-point condition halves the dimension.  Indeed, left multiplication by the
lowering generator `dⱼᵢ` exchanges the `pᵢⱼ = 1` piece with the `pᵢⱼ = 0` piece; on those pieces
its inverse is left multiplication by `1/2 dᵢⱼ`.  Iterating over the `choose N 2` positive pairs
and using the total Clifford dimension `2 ^ N²` gives

`2 ^ (N² - choose N 2) = 2 ^ (N * (N + 1) / 2)`.

The converse fixed-point characterization is obtained row by row.  Once the lower rows are fixed,
the diagonal equation at row `i` says that the sum of the remaining commuting upper occupation
idempotents has its maximal eigenvalue, so every one of them fixes the vector.

## Main result

* `TauCeti.finrank_weightSpace_glHalfStaircase_car`: the half-staircase weight space has dimension
  `2 ^ (N * (N + 1) / 2)`.

## References

* D. Panyushev, *The exterior algebra and "spin" of an orthogonal g-module*, Transform. Groups 6
  (2001), Proposition 2.4 and Example 2.5(1).
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open scoped BigOperators TauCeti

namespace TauCeti

open CliffordAlgebra LieModule Module

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Classical.decEq

noncomputable section

private noncomputable abbrev carAlgebra (K : Type*) [Field K] (N : ℕ) :=
  CliffordAlgebra (traceQuadraticForm K (Fin N))

private noncomputable abbrev carGenerator (K : Type*) [Field K] {N : ℕ}
    (i j : Fin N) : carAlgebra K N :=
  ι (traceQuadraticForm K (Fin N)) (Matrix.single i j 1)

private theorem commute_carOccupationElement_carGenerator
    {K : Type*} [Field K] {N : ℕ} {i j k l : Fin N}
    (hforward : (k, l) ≠ (i, j)) (hreverse : (k, l) ≠ (j, i)) :
    Commute (carOccupationElement (K := K) i j) (carGenerator K k l) := by
  classical
  have hfirst : ¬(j = k ∧ l = i) := by
    rintro ⟨rfl, rfl⟩
    exact hreverse rfl
  have hsecond : ¬(i = k ∧ l = j) := by
    rintro ⟨rfl, rfl⟩
    exact hforward rfl
  rw [carOccupationElement_def]
  apply Commute.smul_left
  rw [Commute]
  calc
    (carGenerator K i j * carGenerator K j i) * carGenerator K k l =
        carGenerator K i j * (carGenerator K j i * carGenerator K k l) := mul_assoc _ _ _
    _ = carGenerator K i j * (-(carGenerator K k l * carGenerator K j i)) := by
      rw [traceQuadraticForm_ι_single_mul_ι_single_comm_of_not_paired
        j i k l 1 1 hsecond]
    _ = -(carGenerator K i j * carGenerator K k l) * carGenerator K j i := by
      simp [mul_assoc]
    _ = -(-(carGenerator K k l * carGenerator K i j)) * carGenerator K j i := by
      rw [traceQuadraticForm_ι_single_mul_ι_single_comm_of_not_paired
        i j k l 1 1 hfirst]
    _ = carGenerator K k l * (carGenerator K i j * carGenerator K j i) := by
      simp [mul_assoc]

private noncomputable def carOccupationEnd
    {K : Type*} [Field K] {N : ℕ}
    (a : ↥(carPositiveRootPairs (Fin N))) : Module.End K (carAlgebra K N) :=
  Module.toModuleEnd K (carAlgebra K N)
    (carOccupationElement (K := K) a.1.1 a.1.2)

private noncomputable def carLoweringEnd
    {K : Type*} [Field K] {N : ℕ}
    (a : ↥(carPositiveRootPairs (Fin N))) : Module.End K (carAlgebra K N) :=
  Module.toModuleEnd K (carAlgebra K N) (carGenerator K a.1.2 a.1.1)

private noncomputable def carScaledRaisingEnd
    {K : Type*} [Field K] {N : ℕ}
    (a : ↥(carPositiveRootPairs (Fin N))) : Module.End K (carAlgebra K N) :=
  Module.toModuleEnd K (carAlgebra K N) ((2 : K)⁻¹ • carGenerator K a.1.1 a.1.2)

private theorem carOccupationElement_mul_carGenerator_snd
    {K : Type*} [Field K] {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    carOccupationElement (K := K) i j * carGenerator K j i = 0 := by
  classical
  rw [carOccupationElement_def, smul_mul_assoc, mul_assoc]
  simp [carGenerator, hij.symm]

private theorem carOccupationElement_mul_carGenerator_fst
    {K : Type*} [Field K] [Invertible (2 : K)] {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    carOccupationElement (K := K) i j * carGenerator K i j = carGenerator K i j := by
  rw [carOccupationElement_swap (K := K) j i, sub_mul, one_mul,
    carOccupationElement_mul_carGenerator_snd hij.symm, sub_zero]

private theorem carPositiveRootPair_ne_reverse {N : ℕ}
    (a b : ↥(carPositiveRootPairs (Fin N))) :
    (a.1.1, a.1.2) ≠ (b.1.2, b.1.1) := by
  intro h
  have ha : a.1.1 < a.1.2 := mem_carPositiveRootPairs.mp a.2
  have hb : b.1.1 < b.1.2 := mem_carPositiveRootPairs.mp b.2
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  exact lt_asymm ha (hfst ▸ hsnd ▸ hb)

private theorem pow_card_mul_finrank_carOccupationFixed
    {K : Type*} [Field K] [Invertible (2 : K)] (N : ℕ) :
    2 ^ (carPositiveRootPairs (Fin N)).card *
        finrank K ((⨅ a ∈ Finset.univ,
          (carOccupationEnd (K := K) (N := N) a).fixedSubmodule) :
            Submodule K (carAlgebra K N)) =
      finrank K (carAlgebra K N) := by
  let P := ↥(carPositiveRootPairs (Fin N))
  let p : P → Module.End K (carAlgebra K N) := carOccupationEnd
  let u : P → Module.End K (carAlgebra K N) := carLoweringEnd
  let v : P → Module.End K (carAlgebra K N) := carScaledRaisingEnd
  -- Apply the generic fixed-submodule halving theorem to every positive root pair.
  have hcard : (carPositiveRootPairs (Fin N)).card = Fintype.card P := by simp [P]
  rw [hcard]
  suffices 2 ^ Fintype.card P * finrank K
      ((⨅ a ∈ Finset.univ, (p a).fixedSubmodule) : Submodule K (carAlgebra K N)) =
      finrank K (carAlgebra K N) by
    simpa only [P, p] using this
  rw [← Finset.card_univ]
  apply pow_card_mul_finrank_iInf_fixedSubmodule p Finset.univ (u := u) (v := v)
  · intro a ha
    exact (isIdempotentElem_carOccupationElement (K := K)
      (ne_of_lt (mem_carPositiveRootPairs.mp a.2))).map
        (Module.toModuleEnd K (carAlgebra K N))
  · intro a ha b hb hab
    exact (commute_carOccupationElement (K := K)).map
      (Module.toModuleEnd K (carAlgebra K N))
  · intro a ha i hi hia
    apply (commute_carOccupationElement_carGenerator (K := K)
      (i := i.1.1) (j := i.1.2) (k := a.1.2) (l := a.1.1) ?_ ?_).map
        (Module.toModuleEnd K (carAlgebra K N))
    · exact (carPositiveRootPair_ne_reverse i a).symm
    · intro h
      apply hia
      apply Subtype.ext
      exact (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)).symm
  · intro a ha i hi hia
    have hcomm := ((commute_carOccupationElement_carGenerator (K := K)
      (i := i.1.1) (j := i.1.2) (k := a.1.1) (l := a.1.2) ?_ ?_).smul_right
        (2 : K)⁻¹).map (Module.toModuleEnd K (carAlgebra K N))
    · exact hcomm
    · intro h
      apply hia
      exact Subtype.ext h.symm
    · exact carPositiveRootPair_ne_reverse a i
  · intro a ha x hx
    dsimp only [p, u, carOccupationEnd, carLoweringEnd] at hx ⊢
    simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, smul_eq_mul] at hx ⊢
    rw [← mul_assoc, carOccupationElement_mul_carGenerator_snd
      (ne_of_lt (mem_carPositiveRootPairs.mp a.2)), zero_mul]
  · intro a ha x hx
    dsimp only [p, v, carOccupationEnd, carScaledRaisingEnd] at hx ⊢
    simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, smul_eq_mul] at hx ⊢
    rw [← mul_assoc, mul_smul_comm,
      carOccupationElement_mul_carGenerator_fst
        (ne_of_lt (mem_carPositiveRootPairs.mp a.2))]
  · intro a ha x hx
    dsimp only [p, u, v, carOccupationEnd, carLoweringEnd, carScaledRaisingEnd] at hx ⊢
    simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, smul_eq_mul] at hx ⊢
    simpa [← mul_assoc, carOccupationElement_def] using hx
  · intro a ha x hx
    dsimp only [p, u, v, carOccupationEnd, carLoweringEnd, carScaledRaisingEnd] at hx ⊢
    simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, smul_eq_mul] at hx ⊢
    rw [← mul_assoc, mul_smul_comm]
    rw [← carOccupationElement_def]
    rw [carOccupationElement_swap]
    simp [sub_mul, hx]

private theorem choose_two_add_upperTriangle (N : ℕ) :
    N.choose 2 + N * (N + 1) / 2 = N * N := by
  rw [Nat.choose_two_right]
  apply Nat.mul_right_cancel (by norm_num : 0 < 2)
  rw [Nat.add_mul, Nat.div_mul_cancel (Nat.even_mul_pred_self N).two_dvd,
    Nat.div_mul_cancel (Nat.even_mul_succ_self N).two_dvd]
  by_cases hN : N = 0
  · simp [hN]
  · rw [← Nat.mul_add]
    have hsum : N - 1 + (N + 1) = 2 * N := by omega
    rw [hsum]
    ring

private theorem finrank_carOccupationFixed
    {K : Type*} [Field K] [Invertible (2 : K)] (N : ℕ) :
    finrank K ((⨅ a ∈ Finset.univ,
      (carOccupationEnd (K := K) (N := N) a).fixedSubmodule) :
        Submodule K (carAlgebra K N)) =
      2 ^ (N * (N + 1) / 2) := by
  have hpairs : (carPositiveRootPairs (Fin N)).card = N.choose 2 := by
    have heq : carPositiveRootPairs (Fin N) =
        {ij ∈ (Finset.univ : Finset (Fin N)).product
          (Finset.univ : Finset (Fin N)) |
          ij.1 < ij.2} := by
      ext ⟨i, j⟩
      rw [mem_carPositiveRootPairs]
      simp
    rw [heq]
    simpa using
      (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin N))))
  have htotal : finrank K (carAlgebra K N) = 2 ^ (N * N) := by
    simpa using finrank_cliffordAlgebra_traceQuadraticForm K (Fin N)
  have hdim := pow_card_mul_finrank_carOccupationFixed (K := K) N
  rw [hpairs, htotal, ← choose_two_add_upperTriangle N, pow_add] at hdim
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hdim

private theorem sum_positive_diagonal_scalar
    {K : Type*} [Field K] [CharZero K] {N : ℕ} (i : Fin N) :
    (∑ k : Fin N, if k < i then (0 : K)
      else if k = i then (2 : K)⁻¹ else 1) = glHalfStaircase K N i := by
  have hcount : (Finset.univ.filter fun k : Fin N => i < k).card = Fin.rev i := by
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    simp only [Fin.rev, Fin.val_mk]
    omega
  calc
    (∑ k : Fin N, if k < i then (0 : K)
        else if k = i then (2 : K)⁻¹ else 1) =
        ∑ k : Fin N, ((if i < k then (1 : K) else 0) +
          if k = i then (2 : K)⁻¹ else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rcases lt_trichotomy k i with hki | rfl | hik
      · simp [hki, ne_of_lt hki, not_lt_of_ge hki.le]
      · simp
      · simp [hik, ne_of_gt hik, not_lt_of_ge hik.le]
    _ = ((Finset.univ.filter fun k : Fin N => i < k).card : K) + (2 : K)⁻¹ := by
      rw [Finset.sum_add_distrib]
      simp
    _ = ((Fin.rev i : ℕ) : K) + (2 : K)⁻¹ := by rw [hcount]
    _ = glHalfStaircase K N i := by
      rw [show (2 : K)⁻¹ = 1 / 2 by norm_num]
      exact Fin.natCast_rev_add_one_div_two_eq_glHalfStaircase i

private theorem carOccupationElement_mul_eq_self_of_mem_commonFixed
    {K : Type*} [Field K] {N : ℕ} {x : carAlgebra K N}
    (hx : x ∈ (⨅ a ∈ Finset.univ,
      (carOccupationEnd (K := K) (N := N) a).fixedSubmodule))
    {a b : Fin N} (hab : a < b) :
    carOccupationElement (K := K) a b * x = x := by
  simp only [Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] at hx
  have h := hx
    (⟨(a, b), mem_carPositiveRootPairs.mpr hab⟩ :
      ↥(carPositiveRootPairs (Fin N))) (Finset.mem_univ _)
  simpa [carOccupationEnd, Module.toModuleEnd_apply,
    DistribSMul.toLinearMap_apply, smul_eq_mul] using h

private theorem matrix_single_self_eq_classical
    {K : Type*} [Field K] {N : ℕ} (i : Fin N) :
    Matrix.single i i (1 : K) =
      @Matrix.single (Fin N) (Fin N) K (Classical.decEq _) (Classical.decEq _) _ i i 1 := by
  ext a b
  simp [Matrix.single_apply]

private theorem diagonal_lie_eq_glHalfStaircase_smul_of_occupation_fixed
    {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)] {N : ℕ}
    (x : carAlgebra K N)
    (hfixed : ∀ {a b : Fin N}, a < b →
      carOccupationElement (K := K) a b * x = x) (i : Fin N) :
    ⁅Matrix.single i i (1 : K), x⁆ = glHalfStaircase K N i • x := by
  rw [car_lie_def]
  have hterm (k : Fin N) :
      (if k < i then 1 - carOccupationElement (K := K) k i
        else carOccupationElement (K := K) i k) * x =
      (if k < i then (0 : K) else if k = i then (2 : K)⁻¹ else 1) • x := by
    rcases lt_trichotomy k i with hki | rfl | hik
    · simp only [hki, ↓reduceIte, sub_mul, one_mul, hfixed hki, sub_self, zero_smul]
    · simp [carOccupationElement_self]
    · simp only [not_lt_of_ge hik.le, ne_of_gt hik, ↓reduceIte, hfixed hik, one_smul]
  calc
    glCliffordHom (Matrix.single i i (1 : K)) * x =
        (∑ k : Fin N, if k < i then 1 - carOccupationElement (K := K) k i
          else carOccupationElement (K := K) i k) * x :=
      congrArg (fun z => z * x)
        (by
          rw [matrix_single_self_eq_classical]
          exact glCliffordHom_single_self_eq_sum_positive_occupation
            (K := K) (n := Fin N) i)
    _ = ∑ k : Fin N, (if k < i then 1 - carOccupationElement (K := K) k i
          else carOccupationElement (K := K) i k) * x := by rw [Finset.sum_mul]
    _ = ∑ k : Fin N, (if k < i then (0 : K)
          else if k = i then (2 : K)⁻¹ else 1) • x := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hterm k
    _ = glHalfStaircase K N i • x := by
      rw [← Finset.sum_smul, sum_positive_diagonal_scalar]

private theorem sum_upper_occupation_smul_eq_card_smul
    {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)] {N : ℕ}
    {x : carAlgebra K N} (i : Fin N)
    (hdiag : ⁅Matrix.single i i (1 : K), x⁆ = glHalfStaircase K N i • x)
    (hlower : ∀ {k : Fin N}, k < i →
      carOccupationElement (K := K) k i * x = x) :
    (∑ k ∈ Finset.Ioi i, carOccupationElement (K := K) i k) • x =
      ((Finset.Ioi i).card : K) • x := by
  have hterm (k : Fin N) :
      (if k < i then 1 - carOccupationElement (K := K) k i
        else carOccupationElement (K := K) i k) * x =
      if i < k then carOccupationElement (K := K) i k * x
      else if k = i then (2 : K)⁻¹ • x else 0 := by
    rcases lt_trichotomy k i with hki | rfl | hik
    · simp [hki, ne_of_lt hki, not_lt_of_ge hki.le, hlower hki, sub_mul]
    · simp [carOccupationElement_self]
    · simp [hik, not_lt_of_ge hik.le]
  rw [car_lie_def, matrix_single_self_eq_classical,
    glCliffordHom_single_self_eq_sum_positive_occupation,
    Finset.sum_mul, Finset.sum_congr rfl fun k _ => hterm k] at hdiag
  have hsum :
      (∑ k : Fin N, if i < k then carOccupationElement (K := K) i k * x
        else if k = i then (2 : K)⁻¹ • x else 0) =
      (∑ k ∈ Finset.Ioi i, carOccupationElement (K := K) i k * x) +
        (2 : K)⁻¹ • x := by
    rw [Finset.sum_ite]
    rw [Finset.filter_lt_eq_Ioi]
    simp [Finset.sum_ite_eq']
  rw [hsum, ← Finset.sum_mul] at hdiag
  rw [← Fin.natCast_rev_add_one_div_two_eq_glHalfStaircase (F := K) i,
    add_smul] at hdiag
  have hcard : (Finset.Ioi i).card = Fin.rev i := by
    rw [Fin.card_Ioi]
    simp only [Fin.rev, Fin.val_mk]
    omega
  rw [hcard]
  norm_num at hdiag
  simpa [smul_eq_mul] using hdiag

private theorem commonFixed_le_glHalfStaircase_weightSpace
    {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)] (N : ℕ) :
    (⨅ a ∈ Finset.univ,
      (carOccupationEnd (K := K) (N := N) a).fixedSubmodule) ≤
      LieModule.weightSpace (carAlgebra K N)
        ((glWeightEquiv K (Fin N) (glHalfStaircase K N) :
          Module.Dual K (diagonalCartan K (Fin N))) :
            diagonalCartan K (Fin N) → K) := by
  intro x hx
  apply (mem_weightSpace_glWeightEquiv_iff (glHalfStaircase K N) x).2
  exact diagonal_lie_eq_glHalfStaircase_smul_of_occupation_fixed x fun hab =>
    carOccupationElement_mul_eq_self_of_mem_commonFixed hx hab

private theorem glHalfStaircase_weightSpace_le_commonFixed
    {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)] (N : ℕ) :
    LieModule.weightSpace (carAlgebra K N)
        ((glWeightEquiv K (Fin N) (glHalfStaircase K N) :
          Module.Dual K (diagonalCartan K (Fin N))) :
            diagonalCartan K (Fin N) → K) ≤
      (⨅ a ∈ Finset.univ,
        (carOccupationEnd (K := K) (N := N) a).fixedSubmodule) := by
  intro x hx
  have hdiag := (mem_weightSpace_glWeightEquiv_iff (glHalfStaircase K N) x).1 hx
  have hrows : ∀ m : ℕ, m < N → ∀ i : Fin N, i.val = m →
      ∀ j : Fin N, i < j → carOccupationElement (K := K) i j * x = x := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm i him j hij
        have hlower {k : Fin N} (hki : k < i) :
            carOccupationElement (K := K) k i * x = x := by
          exact ih k.val (him ▸ hki) k.isLt k rfl i hki
        have hsum := sum_upper_occupation_smul_eq_card_smul i (hdiag i) hlower
        let t := Finset.Ioi i
        let p : Fin N → carAlgebra K N := fun k => carOccupationElement (K := K) i k
        have hp : ∀ k ∈ t, IsIdempotentElem (p k) := by
          intro k hk
          have hik : i < k := by simpa [t] using hk
          exact isIdempotentElem_carOccupationElement (K := K)
            (ne_of_lt hik)
        have hcomm : (t : Set (Fin N)).Pairwise fun k l => Commute (p k) (p l) := by
          intro k hk l hl hkl
          exact commute_carOccupationElement (K := K)
        have heigen : (∑ k ∈ t, p k) • x = (t.card : K) • x := by
          simpa [t, p] using hsum
        have hj : j ∈ t := by simpa [t] using hij
        have := t.smul_eq_self_of_sum_smul_eq_card_smul p hp hcomm heigen hj
        simpa [p, smul_eq_mul] using this
  simp only [Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff]
  intro a ha
  rcases a with ⟨⟨i, j⟩, hij⟩
  have hij' : i < j := mem_carPositiveRootPairs.mp hij
  have hfix := hrows i.val i.isLt i rfl j hij'
  simpa [carOccupationEnd, Module.toModuleEnd_apply,
    DistribSMul.toLinearMap_apply, smul_eq_mul] using hfix

private theorem glHalfStaircase_weightSpace_eq_commonFixed
    {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)] (N : ℕ) :
    LieModule.weightSpace (carAlgebra K N)
        ((glWeightEquiv K (Fin N) (glHalfStaircase K N) :
          Module.Dual K (diagonalCartan K (Fin N))) :
            diagonalCartan K (Fin N) → K) =
      (⨅ a ∈ Finset.univ,
        (carOccupationEnd (K := K) (N := N) a).fixedSubmodule) := by
  apply le_antisymm
  · exact glHalfStaircase_weightSpace_le_commonFixed N
  · exact commonFixed_le_glHalfStaircase_weightSpace N

/-- The half-staircase weight space in the left regular CAR module has dimension
`2 ^ (N * (N + 1) / 2)`. -/
@[simp]
theorem finrank_weightSpace_glHalfStaircase_car
    {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)] (N : ℕ) :
    finrank K (LieModule.weightSpace
      (CliffordAlgebra (traceQuadraticForm K (Fin N)))
      ((glWeightEquiv K (Fin N) (glHalfStaircase K N) :
        Module.Dual K (diagonalCartan K (Fin N))) :
          diagonalCartan K (Fin N) → K)) =
      2 ^ (N * (N + 1) / 2) := by
  have heq := glHalfStaircase_weightSpace_eq_commonFixed (K := K) N
  calc
    finrank K (LieModule.weightSpace (carAlgebra K N)
        ((glWeightEquiv K (Fin N) (glHalfStaircase K N) :
          Module.Dual K (diagonalCartan K (Fin N))) :
            diagonalCartan K (Fin N) → K)) =
        finrank K ((⨅ a ∈ Finset.univ,
          (carOccupationEnd (K := K) (N := N) a).fixedSubmodule) :
            Submodule K (carAlgebra K N)) :=
      congrArg (fun S : Submodule K (carAlgebra K N) => finrank K S) heq
    _ = 2 ^ (N * (N + 1) / 2) := finrank_carOccupationFixed N

end

end TauCeti
