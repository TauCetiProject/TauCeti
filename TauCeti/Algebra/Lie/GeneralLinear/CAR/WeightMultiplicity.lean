/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.CAR.WeightSpectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.Lie.GeneralLinear.CAR.Occupation
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
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

private def commonFixed {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ι → Module.End K V) (s : Finset ι) : Submodule K V where
  carrier := {x | ∀ i ∈ s, p i x = x}
  zero_mem' i hi := by simp
  add_mem' {x y} hx hy i hi := by rw [map_add, hx i hi, hy i hi]
  smul_mem' c x hx i hi := by rw [map_smul, hx i hi]

@[simp]
private theorem mem_commonFixed {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    {p : ι → Module.End K V} {s : Finset ι} {x : V} :
    x ∈ commonFixed p s ↔ ∀ i ∈ s, p i x = x :=
  Iff.rfl

private theorem commonFixed_empty {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (p : ι → Module.End K V) : commonFixed p ∅ = ⊤ := by
  ext x
  simp

private theorem two_mul_finrank_commonFixed_insert
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι]
    (p : ι → Module.End K V) (s : Finset ι) (a : ι) (ha : a ∉ s)
    (hpa : IsIdempotentElem (p a))
    (hcomm : ∀ i ∈ s, Commute (p i) (p a))
    (u v : Module.End K V)
    (huS : ∀ i ∈ s, Commute (p i) u)
    (hvS : ∀ i ∈ s, Commute (p i) v)
    (hu0 : ∀ x, p a x = x → p a (u x) = 0)
    (hv1 : ∀ x, p a x = 0 → p a (v x) = v x)
    (hvu : ∀ x, p a x = x → v (u x) = x)
    (huv : ∀ x, p a x = 0 → u (v x) = x) :
    2 * finrank K (commonFixed p (insert a s)) = finrank K (commonFixed p s) := by
  let S := commonFixed p s
  let A := commonFixed p (insert a s)
  let B : Submodule K V := S ⊓ LinearMap.ker (p a)
  have hAS : A ≤ S := by
    intro x hx
    exact fun i hi => hx i (Finset.mem_insert_of_mem hi)
  have hAfix : ∀ x ∈ A, p a x = x := by
    intro x hx
    exact hx a (Finset.mem_insert_self a s)
  have hsup : A ⊔ B = S := by
    apply le_antisymm
    · exact sup_le hAS inf_le_left
    · intro x hx
      have hpxS : p a x ∈ S := by
        intro i hi
        calc
          p i (p a x) = p a (p i x) :=
            LinearMap.congr_fun (hcomm i hi).eq x
          _ = p a x := congrArg (p a) (hx i hi)
      have hrestS : x - p a x ∈ S := S.sub_mem hx hpxS
      have hpxA : p a x ∈ A := by
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact congrArg (fun f : Module.End K V => f x) hpa.eq
        · exact hpxS i hi
      have hrestB : x - p a x ∈ B := by
        refine ⟨hrestS, ?_⟩
        change p a (x - p a x) = 0
        rw [map_sub]
        exact sub_eq_zero.mpr (congrArg (fun f : Module.End K V => f x) hpa.eq).symm
      rw [← add_sub_cancel (p a x) x]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hpxA) (Submodule.mem_sup_right hrestB)
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hfix := hAfix x hx.1
    have hzero : p a x = 0 := LinearMap.mem_ker.mp hx.2.2
    change x = 0
    rw [← hfix, hzero]
  let U : A →ₗ[K] B :=
    (u.domRestrict A).codRestrict B fun x => by
      refine ⟨?_, LinearMap.mem_ker.mpr (hu0 x (hAfix x x.2))⟩
      intro i hi
      change p i (u x) = u x
      calc
        p i (u x) = u (p i x) := LinearMap.congr_fun (huS i hi).eq x
        _ = u x := congrArg u (x.2 i (Finset.mem_insert_of_mem hi))
  let W : B →ₗ[K] A :=
    (v.domRestrict B).codRestrict A fun x => by
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hv1 x (LinearMap.mem_ker.mp x.2.2)
      · change p i (v x) = v x
        calc
          p i (v x) = v (p i x) := LinearMap.congr_fun (hvS i hi).eq x
          _ = v x := congrArg v (x.2.1 i hi)
  let e : A ≃ₗ[K] B := LinearEquiv.ofLinearMap U W (by
    ext x
    change u (v (x : V)) = x
    exact huv x (LinearMap.mem_ker.mp x.2.2)) (by
    ext x
    change v (u (x : V)) = x
    exact hvu x (hAfix x x.2))
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, hinf, finrank_bot, add_zero] at hrank
  calc
    2 * finrank K A = finrank K A + finrank K A := two_mul _
    _ = finrank K A + finrank K B := by rw [e.finrank_eq]
    _ = finrank K S := hrank.symm

private theorem pow_card_mul_finrank_commonFixed
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (p : ι → Module.End K V) (t : Finset ι)
    (hp : ∀ a ∈ t, IsIdempotentElem (p a))
    (hcomm : (t : Set ι).Pairwise fun a b => Commute (p a) (p b))
    (u v : ι → Module.End K V)
    (huS : ∀ a ∈ t, ∀ i ∈ t, i ≠ a → Commute (p i) (u a))
    (hvS : ∀ a ∈ t, ∀ i ∈ t, i ≠ a → Commute (p i) (v a))
    (hu0 : ∀ a ∈ t, ∀ x, p a x = x → p a (u a x) = 0)
    (hv1 : ∀ a ∈ t, ∀ x, p a x = 0 → p a (v a x) = v a x)
    (hvu : ∀ a ∈ t, ∀ x, p a x = x → v a (u a x) = x)
    (huv : ∀ a ∈ t, ∀ x, p a x = 0 → u a (v a x) = x) :
    2 ^ t.card * finrank K (commonFixed p t) = finrank K V := by
  classical
  induction t using Finset.induction with
  | empty =>
      rw [commonFixed_empty]
      simp
  | @insert a s ha ih =>
      have hrec : 2 * finrank K (commonFixed p (insert a s)) =
          finrank K (commonFixed p s) :=
        two_mul_finrank_commonFixed_insert p s a ha (hp a (by simp))
          (fun i hi => hcomm (by simp [hi]) (by simp) (by
            exact fun hia => ha (hia ▸ hi))) (u a) (v a)
          (fun i hi => huS a (by simp) i (by simp [hi]) (by
            exact fun hia => ha (hia ▸ hi)))
          (fun i hi => hvS a (by simp) i (by simp [hi]) (by
            exact fun hia => ha (hia ▸ hi)))
          (hu0 a (by simp)) (hv1 a (by simp)) (hvu a (by simp)) (huv a (by simp))
      have ih' := ih (fun b hb => hp b (by simp [hb]))
        (hcomm.mono (by simp))
        (fun b hb i hi hne => huS b (by simp [hb]) i (by simp [hi]) hne)
        (fun b hb i hi hne => hvS b (by simp [hb]) i (by simp [hi]) hne)
        (fun b hb => hu0 b (by simp [hb]))
        (fun b hb => hv1 b (by simp [hb]))
        (fun b hb => hvu b (by simp [hb]))
        (fun b hb => huv b (by simp [hb]))
      rw [Finset.card_insert_of_notMem ha, pow_succ]
      calc
        2 ^ s.card * 2 * finrank K (commonFixed p (insert a s)) =
            2 ^ s.card * (2 * finrank K (commonFixed p (insert a s))) :=
          Nat.mul_assoc _ _ _
        _ = 2 ^ s.card * finrank K (commonFixed p s) := by rw [hrec]
        _ = finrank K V := ih'

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
  change ((2 : K)⁻¹ • (carGenerator K i j * carGenerator K j i)) *
      carGenerator K k l =
    carGenerator K k l *
      ((2 : K)⁻¹ • (carGenerator K i j * carGenerator K j i))
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
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

private theorem carOccupationElement_mul_carGenerator_fst
    {K : Type*} [Field K] [CharZero K] {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    carOccupationElement (K := K) i j * carGenerator K i j = carGenerator K i j := by
  classical
  have hcar : carGenerator K i j * carGenerator K j i +
      carGenerator K j i * carGenerator K i j = (2 : K) • 1 := by
    simpa [carGenerator, Algebra.smul_def] using
      (traceQuadraticForm_ι_single_mul_ι_single_add_swap
        (R := K) i j j i 1 1)
  have hsq : carGenerator K i j * carGenerator K i j = 0 := by
    simp [carGenerator, hij]
  rw [carOccupationElement_def, smul_mul_assoc, mul_assoc]
  calc
    (2 : K)⁻¹ • (carGenerator K i j *
        (carGenerator K j i * carGenerator K i j)) =
      (2 : K)⁻¹ • (carGenerator K i j *
        ((2 : K) • 1 - carGenerator K i j * carGenerator K j i)) := by
        rw [show carGenerator K j i * carGenerator K i j =
            (2 : K) • 1 - carGenerator K i j * carGenerator K j i by
          rw [eq_sub_iff_add_eq]
          simpa [add_comm] using hcar]
    _ = (2 : K)⁻¹ • ((2 : K) • carGenerator K i j) := by
      rw [mul_sub, ← mul_assoc, hsq, zero_mul, sub_zero]
      simp
    _ = carGenerator K i j := by
      rw [smul_smul]
      simp

private theorem carOccupationElement_mul_carGenerator_snd
    {K : Type*} [Field K] {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    carOccupationElement (K := K) i j * carGenerator K j i = 0 := by
  classical
  rw [carOccupationElement_def, smul_mul_assoc, mul_assoc]
  simp [carGenerator, hij.symm]

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
    {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)] (N : ℕ) :
    2 ^ (carPositiveRootPairs (Fin N)).card *
        finrank K (commonFixed (carOccupationEnd (K := K) (N := N)) Finset.univ) =
      finrank K (carAlgebra K N) := by
  let P := ↥(carPositiveRootPairs (Fin N))
  let p : P → Module.End K (carAlgebra K N) := carOccupationEnd
  let u : P → Module.End K (carAlgebra K N) := carLoweringEnd
  let v : P → Module.End K (carAlgebra K N) := carScaledRaisingEnd
  rw [show (carPositiveRootPairs (Fin N)).card = Fintype.card P by simp [P]]
  change 2 ^ Fintype.card P * finrank K (commonFixed p Finset.univ) =
      finrank K (carAlgebra K N)
  rw [← Finset.card_univ]
  apply pow_card_mul_finrank_commonFixed p Finset.univ (u := u) (v := v)
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
    change ((2 : K)⁻¹ • carGenerator K a.1.1 a.1.2) *
        (carGenerator K a.1.2 a.1.1 * x) = x
    simpa [← mul_assoc, carOccupationElement_def] using hx
  · intro a ha x hx
    dsimp only [p, u, v, carOccupationEnd, carLoweringEnd, carScaledRaisingEnd] at hx ⊢
    simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, smul_eq_mul] at hx ⊢
    change carGenerator K a.1.2 a.1.1 *
        (((2 : K)⁻¹ • carGenerator K a.1.1 a.1.2) * x) = x
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
    {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)] (N : ℕ) :
    finrank K (commonFixed (carOccupationEnd (K := K) (N := N)) Finset.univ) =
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
    rw [CliffordAlgebra.finrank_eq_two_pow, Module.finrank_matrix]
    simp
  have hdim := pow_card_mul_finrank_carOccupationFixed (K := K) N
  rw [hpairs, htotal, ← choose_two_add_upperTriangle N, pow_add] at hdim
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hdim

private theorem smul_eq_self_of_sum_smul_eq_card_smul
    {K A ι : Type*} [Field K] [CharZero K] [Ring A]
    [Module K A] [SMulCommClass A K A]
    (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsIdempotentElem (p i))
    (hcomm : (s : Set ι).Pairwise fun i j => Commute (p i) (p j))
    {x : A} (heigen : (∑ i ∈ s, p i) • x = (s.card : K) • x)
    {a : ι} (ha : a ∈ s) : p a • x = x := by
  classical
  let y := (1 - p a) • x
  have hpa := hp a ha
  have hpa_y : p a • y = 0 := by
    dsimp only [y]
    rw [← mul_smul, mul_sub, mul_one, hpa.eq, sub_self, zero_smul]
  have hsumcomm : Commute (∑ i ∈ s, p i) (1 - p a) := by
    apply Commute.sum_left
    intro i hi
    rcases eq_or_ne i a with rfl | hia
    · change p i * (1 - p i) = (1 - p i) * p i
      rw [mul_sub, sub_mul, mul_one, one_mul, hpa.eq]
    · change p i * (1 - p a) = (1 - p a) * p i
      rw [mul_sub, sub_mul, mul_one, one_mul, hcomm hi ha hia]
  have hsum_y : (∑ i ∈ s, p i) • y = (s.card : K) • y := by
    dsimp only [y]
    calc
      (∑ i ∈ s, p i) • ((1 - p a) • x) =
          (1 - p a) • ((∑ i ∈ s, p i) • x) := by
        rw [← mul_smul, ← mul_smul, hsumcomm.eq]
      _ = (1 - p a) • ((s.card : K) • x) := by rw [heigen]
      _ = (s.card : K) • ((1 - p a) • x) := smul_comm _ _ _
  have hrest_y : (∑ i ∈ s.erase a, p i) • y = (s.card : K) • y := by
    rw [← Finset.sum_erase_add _ _ ha, add_smul, hpa_y] at hsum_y
    simpa using hsum_y
  by_contra hfix
  have hy : y ≠ 0 := by
    intro hy
    apply hfix
    dsimp only [y] at hy
    rw [sub_smul, one_smul, sub_eq_zero] at hy
    exact hy.symm
  obtain ⟨m, hm, hcast⟩ := (s.erase a).exists_eq_natCast_of_sum_smul_eq_smul p
    (fun i hi => hp i (Finset.mem_of_mem_erase hi))
    (hcomm.mono fun i hi => Finset.mem_of_mem_erase hi) hy hrest_y
  have hcard : s.card = m := Nat.cast_injective (R := K) hcast
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  rw [Finset.card_erase_of_mem ha] at hm
  omega

private theorem mem_weightSpace_glWeightEquiv_iff
    {K M n : Type*} [Field K] [Fintype n] [DecidableEq n]
    [AddCommGroup M] [Module K M] [LieRingModule (Matrix n n K) M]
    [LieModule K (Matrix n n K) M]
    (mu : n → K) (x : M) :
    x ∈ LieModule.weightSpace M
        ((glWeightEquiv K n mu : Module.Dual K (diagonalCartan K n)) :
          diagonalCartan K n → K) ↔
      ∀ i : n, ⁅Matrix.single i i (1 : K), x⁆ = mu i • x := by
  constructor
  · intro hx i
    have h := (LieModule.mem_weightSpace _ _).mp hx
      ⟨Matrix.single i i (1 : K), single_self_mem_diagonalCartan i 1⟩
    rw [LieSubalgebra.coe_bracket_of_module, glWeightEquiv_apply] at h
    simpa [Matrix.single_apply, Finset.sum_ite_eq] using h
  · intro hx
    rw [LieModule.mem_weightSpace]
    intro A
    rw [LieSubalgebra.coe_bracket_of_module, glWeightEquiv_apply]
    have hA := (diagonalCartanBasis K n).sum_repr A
    have hsingle (i : n) : Matrix.single i i ((A : Matrix n n K) i i) =
        (A : Matrix n n K) i i • Matrix.single i i (1 : K) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    calc
      ⁅(A : Matrix n n K), x⁆ =
          ∑ i : n, ⁅Matrix.single i i ((A : Matrix n n K) i i), x⁆ := by
        conv_lhs => rw [← hA]
        simp [diagonalCartanBasis_apply, diagonalCartanBasis_repr_apply, sum_lie]
      _ = ∑ i : n, (A : Matrix n n K) i i • ⁅Matrix.single i i (1 : K), x⁆ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsingle, smul_lie]
      _ = ∑ i : n, (A : Matrix n n K) i i • (mu i • x) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hx i]
      _ = ∑ i : n, (mu i * (A : Matrix n n K) i i) • x := by
        simp [smul_smul, mul_comm]
      _ = (∑ i : n, mu i * (A : Matrix n n K) i i) • x := by
        rw [Finset.sum_smul]

private theorem sum_positive_diagonal_scalar
    {K : Type*} [Field K] [CharZero K] {N : ℕ} (i : Fin N) :
    (∑ k : Fin N, if k < i then (0 : K)
      else if k = i then (2 : K)⁻¹ else 1) = glHalfStaircase K N i := by
  rw [glHalfStaircase_apply]
  have hcount : (Finset.univ.filter fun k : Fin N => i < k).card = N - 1 - i := by
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
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
    _ = ((N - 1 - i : ℕ) : K) + (2 : K)⁻¹ := by rw [hcount]
    _ = (N : K) - 1 / 2 - (i : ℕ) := by
      have hi : i + 1 ≤ N := i.isLt
      rw [Nat.cast_sub (Nat.le_sub_of_add_le hi),
        Nat.cast_sub (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt i.isLt))]
      norm_num
      ring

private theorem card_Ioi_add_inv_two_eq_glHalfStaircase
    {K : Type*} [Field K] [CharZero K] {N : ℕ} (i : Fin N) :
    ((Finset.Ioi i).card : K) + (2 : K)⁻¹ = glHalfStaircase K N i := by
  rw [Fin.card_Ioi, glHalfStaircase_apply]
  have hi : i + 1 ≤ N := i.isLt
  rw [Nat.cast_sub (Nat.le_sub_of_add_le hi),
    Nat.cast_sub (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt i.isLt))]
  norm_num
  ring

private theorem carOccupationElement_mul_eq_self_of_mem_commonFixed
    {K : Type*} [Field K] {N : ℕ} {x : carAlgebra K N}
    (hx : x ∈ commonFixed (carOccupationEnd (K := K) (N := N)) Finset.univ)
    {a b : Fin N} (hab : a < b) :
    carOccupationElement (K := K) a b * x = x := by
  have h := hx
    (⟨(a, b), mem_carPositiveRootPairs.mpr hab⟩ :
      ↥(carPositiveRootPairs (Fin N))) (Finset.mem_univ _)
  simpa [carOccupationEnd, Module.toModuleEnd_apply,
    DistribSMul.toLinearMap_apply, smul_eq_mul] using h

private theorem glCliffordHom_single_self_eq_sum_positive_local
    {K : Type*} [Field K] [Invertible (2 : K)] {N : ℕ} (i : Fin N) :
    glCliffordHom (K := K) (n := Fin N) (Matrix.single i i 1) =
      ∑ k : Fin N, if k < i then 1 - carOccupationElement (K := K) k i
        else carOccupationElement (K := K) i k := by
  let E : Matrix (Fin N) (Fin N) K :=
    @Matrix.single (Fin N) (Fin N) K (Classical.decEq _) (Classical.decEq _) _ i i 1
  have hE : Matrix.single i i (1 : K) = E := by
    ext a b
    simp [E, Matrix.single_apply]
  rw [hE]
  exact glCliffordHom_single_self_eq_sum_positive_occupation (K := K) (n := Fin N) i

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
        (glCliffordHom_single_self_eq_sum_positive_local (K := K) i)
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
  rw [car_lie_def, glCliffordHom_single_self_eq_sum_positive_local,
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
  rw [← card_Ioi_add_inv_two_eq_glHalfStaircase, add_smul] at hdiag
  simpa [smul_eq_mul] using add_right_cancel hdiag

private theorem commonFixed_le_glHalfStaircase_weightSpace
    {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)] (N : ℕ) :
    commonFixed (carOccupationEnd (K := K) (N := N)) Finset.univ ≤
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
      commonFixed (carOccupationEnd (K := K) (N := N)) Finset.univ := by
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
          exact isIdempotentElem_carOccupationElement (K := K)
            (ne_of_lt (show i < k by simpa [t] using hk))
        have hcomm : (t : Set (Fin N)).Pairwise fun k l => Commute (p k) (p l) := by
          intro k hk l hl hkl
          exact commute_carOccupationElement (K := K)
        have heigen : (∑ k ∈ t, p k) • x = (t.card : K) • x := by
          simpa [t, p] using hsum
        have hj : j ∈ t := by simpa [t] using hij
        have := smul_eq_self_of_sum_smul_eq_card_smul t p hp hcomm heigen hj
        simpa [p, smul_eq_mul] using this
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
      commonFixed (carOccupationEnd (K := K) (N := N)) Finset.univ := by
  apply le_antisymm
  · exact glHalfStaircase_weightSpace_le_commonFixed N
  · exact commonFixed_le_glHalfStaircase_weightSpace N

/-- The half-staircase weight space in the left regular CAR module has dimension
`2 ^ (N * (N + 1) / 2)`. -/
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
        finrank K (commonFixed (carOccupationEnd (K := K) (N := N)) Finset.univ) :=
      congrArg (fun S : Submodule K (carAlgebra K N) => finrank K S) heq
    _ = 2 ^ (N * (N + 1) / 2) := finrank_carOccupationFixed N

end

end TauCeti
