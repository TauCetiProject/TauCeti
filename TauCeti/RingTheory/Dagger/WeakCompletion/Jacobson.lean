/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import TauCeti.RingTheory.Dagger.WeakCompletion.Quotient
import Mathlib.Algebra.MvPolynomial.Nilpotent
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# The Jacobson radical and units of a weak completion

For any commutative ring `O`, parameter `π : O`, and finitely generated `O`-algebra `S`, the image
of `π` in the Monsky–Washnitzer weak completion `S†` lies in the Jacobson radical of `S†`.

The point is that the geometric series `(1 - π z)⁻¹ = ∑_{m ≥ 0} (π z)^m` of an overconvergent
expansion `z = ∑_{j ≥ 0} πʲ Pⱼ(x)` with `deg Pⱼ ≤ c (j + 1)` remains overconvergent: shifting by
the factor `π` gives `π z = ∑_{k ≥ 1} πᵏ Pₖ₋₁(x)` with homogeneous degree bound `c k`, so the
Cauchy recurrence `R₀ = 1`, `Rₙ₊₁ = ∑_{j ≤ n} Pⱼ Rₙ₋ⱼ` produces polynomials of total degree at
most `c n ≤ c (n + 1)` whose `π`-adic series solves `(1 - π z) u = 1` inside the degree-growth set.

Consequently, reduction modulo any positive power `πⁿ⁺¹` is a local homomorphism, and an element
of `S†` is a unit if and only if its reduction modulo `π` is a unit of `S ⧸ π S`. In particular,
while `O → O†` is bijective if and only if `O` is `π`-adically complete, in at least one variable
`1 ± π Xᵢ` are invertible in `O[X]†`, so `O[X] → O[X]†` is bijective if and only if `π` is
nilpotent.

Nothing here requires `O` to be noetherian, a valuation ring, or `π`-adically complete.

## Main results

* `TauCeti.Dagger.exists_mul_eq_one_weakCompletionSet`: `1 - π z` has an inverse in
  `weakCompletionSet π x` whenever `z ∈ weakCompletionSet π x`.
* `TauCeti.Dagger.weakCompletion.algebraMap_mem_jacobson` and
  `TauCeti.Dagger.weakCompletion.span_algebraMap_le_jacobson`: `algebraMap O S† π` lies in the
  Jacobson radical of `S†`.
* `TauCeti.Dagger.weakCompletion.isLocalHom_eval_succ` and
  `TauCeti.Dagger.weakCompletion.isUnit_iff_eval_one`: reduction modulo `πⁿ⁺¹` is a local
  homomorphism, so an element of `S†` is a unit iff its image in `S ⧸ π S` is a unit.
* `TauCeti.Dagger.weakCompletion.of_self_bijective_iff`: `O → O†` is bijective iff `O` is
  `π`-adically complete.
* `TauCeti.Dagger.weakCompletion.of_mvPolynomial_bijective_iff`: for nonempty finite `σ`,
  `O[X_σ] → O[X_σ]†` is bijective iff `π` is nilpotent.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §2, Theorem 2.1.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23 (1986),
  §2, (2.1).
-/

public section

namespace TauCeti.Dagger

open Finset MvPolynomial

section GeometricSeries

variable {O S ι : Type*} [CommRing O] [CommRing S] [Algebra O S]

/-- Recursive polynomial coefficients for the formal geometric inverse `u = 1 + (π z) u` of
`1 - π z`, when `z` has expansion polynomials `P`. -/
private noncomputable def geomPoly (P : ℕ → MvPolynomial ι O) : ℕ → MvPolynomial ι O
  | 0 => 1
  | n + 1 =>
    ∑ j ∈ (range (n + 1)).attach,
      P j.1 *
        have : n - j.1 < n + 1 := Nat.lt_succ_of_le (Nat.sub_le n j.1)
        geomPoly P (n - j.1)

private theorem geomPoly_zero (P : ℕ → MvPolynomial ι O) : geomPoly P 0 = 1 := by
  rw [geomPoly]

private theorem geomPoly_succ (P : ℕ → MvPolynomial ι O) (n : ℕ) :
    geomPoly P (n + 1) = ∑ j ∈ range (n + 1), P j * geomPoly P (n - j) := by
  rw [geomPoly]
  exact sum_attach (range (n + 1)) fun k ↦ P k * geomPoly P (n - k)

private theorem totalDegree_geomPoly_le {P : ℕ → MvPolynomial ι O} {c : ℕ}
    (hP : ∀ j, (P j).totalDegree ≤ c * (j + 1)) :
    ∀ n, (geomPoly P n).totalDegree ≤ c * n
  | 0 => by simp [geomPoly_zero]
  | n + 1 => by
    rw [geomPoly_succ]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j hj ↦ ?_)
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hsum : j + 1 + (n - j) = n + 1 := by omega
    have ih : (geomPoly P (n - j)).totalDegree ≤ c * (n - j) :=
      have : n - j < n + 1 := Nat.lt_succ_of_le (Nat.sub_le n j)
      totalDegree_geomPoly_le hP (n - j)
    refine (totalDegree_mul _ _).trans ((add_le_add (hP j) ih).trans ?_)
    rw [← mul_add, hsum]

private theorem geomPoly_eq_ite_add_sum_antidiagonal (P : ℕ → MvPolynomial ι O) (m : ℕ) :
    geomPoly P m =
      (if m = 0 then 1 else 0) +
        ∑ ab ∈ antidiagonal m, (Nat.casesOn ab.1 0 P) * geomPoly P ab.2 := by
  rcases m with _ | n
  · simp [geomPoly_zero]
  · simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      sum_range_succ' (fun i ↦ Nat.casesOn i 0 P * geomPoly P (n + 1 - i)), geomPoly_succ]
    simp

/-- For any `z` in the degree-growth set of `x`, `1 - π z` has a multiplicative inverse in the same
degree-growth set. -/
theorem exists_mul_eq_one_weakCompletionSet (π : O) {x : ι → S} {z : piAdicCompletion π S}
    (hz : z ∈ weakCompletionSet π x) :
    ∃ u ∈ weakCompletionSet π x,
      (1 - algebraMap O (piAdicCompletion π S) π * z) * u = 1 := by
  obtain ⟨c, P, hP, hz⟩ := mem_weakCompletionSet_iff.mp hz
  let Q : ℕ → MvPolynomial ι O := fun j ↦ Nat.casesOn j 0 P
  have hdeg (n : ℕ) : (geomPoly P n).totalDegree ≤ c * (n + 1) :=
    (totalDegree_geomPoly_le hP n).trans (Nat.mul_le_mul_left c (Nat.le_succ n))
  obtain ⟨u, hu, hue⟩ := exists_mem_weakCompletionSet_of_degree_le π x (geomPoly P) hdeg
  refine ⟨u, hu, ?_⟩
  suffices hfix : 1 + algebraMap O (piAdicCompletion π S) π * z * u = u by
    linear_combination -hfix
  apply AdicCompletion.ext_evalₐ
  intro k
  set e : S ⧸ Ideal.span {algebraMap O S π} ^ k :=
    Ideal.Quotient.mk (Ideal.span {algebraMap O S π} ^ k) (algebraMap O S π) with he
  have hek : e ^ k = 0 := by
    rw [he, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.subset_span rfl) k
  have hπz : AdicCompletion.evalₐ _ k (algebraMap O (piAdicCompletion π S) π * z) =
      ∑ m ∈ range k, e ^ m *
        Ideal.Quotient.mk (Ideal.span {algebraMap O S π} ^ k) (aeval x (Q m)) := by
    rw [map_mul, IsScalarTower.algebraMap_apply O S (piAdicCompletion π S), AlgHom.commutes,
      Ideal.Quotient.algebraMap_eq, hz k, ← map_mul, mul_sum]
    have hshift :
        Ideal.Quotient.mk (Ideal.span {algebraMap O S π} ^ k)
          (∑ j ∈ range k, algebraMap O S π * (algebraMap O S π ^ j * aeval x (P j))) =
        ∑ m ∈ range (k + 1), e ^ m *
          Ideal.Quotient.mk (Ideal.span {algebraMap O S π} ^ k) (aeval x (Q m)) := by
      rw [sum_range_succ']
      simp [Q, ← he, pow_succ', mul_assoc]
    rw [hshift, sum_range_succ, hek, zero_mul, add_zero]
  rw [map_add, map_one, map_mul, hπz, hue k]
  simp only [map_sum, map_mul, map_pow, ← he]
  rw [TauCeti.sum_range_pow_mul_mul_sum_range_pow_mul_of_pow_eq_zero hek]
  rcases k with _ | k
  · have : Subsingleton (S ⧸ Ideal.span {algebraMap O S π} ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Subsingleton.elim _ _
  · have hone : (1 : S ⧸ Ideal.span {algebraMap O S π} ^ (k + 1)) =
        ∑ m ∈ range (k + 1), e ^ m *
          (if m = 0 then (1 : S ⧸ Ideal.span {algebraMap O S π} ^ (k + 1)) else 0) := by
      simp
    rw [hone, ← sum_add_distrib]
    refine sum_congr rfl fun m _ ↦ ?_
    rw [← mul_add, geomPoly_eq_ite_add_sum_antidiagonal P m]
    congr 1
    simp [Q, apply_ite]

end GeometricSeries

namespace weakCompletion

variable {O : Type*} [CommRing O] (π : O) {S : Type*} [CommRing S] [Algebra O S]
  [Algebra.FiniteType O S]

/-- Every element of the form `1 - π z` in a weak completion is a unit. -/
theorem isUnit_one_sub_algebraMap_mul (z : weakCompletion π S) :
    IsUnit (1 - algebraMap O (weakCompletion π S) π * z) := by
  classical
  obtain ⟨g, hg⟩ := Algebra.FiniteType.out (R := O) (A := S)
  have hx : Algebra.adjoin O (Set.range ((↑) : g → S)) = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using hg
  have hz : (z : piAdicCompletion π S) ∈ weakCompletionSet π ((↑) : g → S) := by
    rw [← coe_weakCompletion π _ hx]
    exact z.property
  obtain ⟨u, hu, hmul⟩ := exists_mul_eq_one_weakCompletionSet π hz
  have hu' : u ∈ weakCompletion π S := by
    rw [← SetLike.mem_coe, coe_weakCompletion π _ hx]
    exact hu
  refine IsUnit.of_mul_eq_one ⟨u, hu'⟩ (Subtype.ext ?_)
  simpa using hmul

/-- Every element of the form `1 + π z` in a weak completion is a unit. -/
theorem isUnit_one_add_algebraMap_mul (z : weakCompletion π S) :
    IsUnit (1 + algebraMap O (weakCompletion π S) π * z) := by
  simpa [sub_neg_eq_add] using isUnit_one_sub_algebraMap_mul π (-z)

variable (S) in
/-- The image of the parameter `π` lies in the Jacobson radical of the weak completion `S†`. -/
theorem algebraMap_mem_jacobson :
    algebraMap O (weakCompletion π S) π ∈ Ring.jacobson (weakCompletion π S) :=
  Ring.mem_jacobson_iff.mpr fun z ↦ by
    simpa [add_comm] using isUnit_one_add_algebraMap_mul π z

variable (S) in
/-- The principal ideal generated by `π` in `S†` is contained in the Jacobson radical of `S†`. -/
theorem span_algebraMap_le_jacobson :
    Ideal.span {algebraMap O (weakCompletion π S) π} ≤ Ring.jacobson (weakCompletion π S) :=
  (Ring.jacobson (weakCompletion π S)).span_singleton_le_iff_mem.mpr (algebraMap_mem_jacobson π S)

/-- Reduction modulo any positive power `πⁿ⁺¹` is a local ring homomorphism on `S†`. -/
instance isLocalHom_eval_succ (n : ℕ) : IsLocalHom (eval π (n + 1) (S := S)).toRingHom := by
  rw [RingHom.isLocalHom_iff_ker_le_jacobson (eval_surjective π (n + 1))]
  have hker : RingHom.ker (eval π (n + 1) (S := S)).toRingHom =
      RingHom.ker (eval π (n + 1) (S := S)) := rfl
  rw [hker, ker_eval]
  exact (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans (span_algebraMap_le_jacobson π S)

/-- An element of `S†` is a unit if and only if its reduction modulo `πⁿ⁺¹` is a unit. -/
theorem isUnit_iff_eval_succ (n : ℕ) (z : weakCompletion π S) :
    IsUnit z ↔ IsUnit (eval π (n + 1) z) :=
  (isUnit_map_iff (eval π (n + 1) (S := S)).toRingHom z).symm

/-- An element of `S†` is a unit if and only if its reduction modulo `π` is a unit in
`S ⧸ π S`. -/
theorem isUnit_iff_eval_one (z : weakCompletion π S) :
    IsUnit z ↔ IsUnit (eval π 1 z) :=
  isUnit_iff_eval_succ π 0 z

/-- The image of `s : S` in `S†` is a unit if and only if the residue class of `s` modulo `π` is
a unit in `S ⧸ π S`. -/
theorem isUnit_of_iff (s : S) :
    IsUnit (of π S s) ↔ IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap O S π}) s) := by
  rw [isUnit_iff_eval_one, eval_of]
  let e := Ideal.quotEquivOfEq (pow_one (Ideal.span {algebraMap O S π}))
  exact ⟨fun h ↦ by simpa [e] using h.map e, fun h ↦ by simpa [e] using h.map e.symm⟩

/-- For the base ring itself, the weak completion `O†` is the entire `π`-adic completion `Ô`. -/
theorem weakCompletion_self_eq_top : weakCompletion π O = ⊤ := by
  rw [eq_top_iff]
  intro z _
  have hgen : Algebra.adjoin O (Set.range (Empty.elim : Empty → O)) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    exact algebraMap_mem _ a
  rw [mem_weakCompletion_iff π hgen]
  let I : Ideal O := Ideal.span {algebraMap O O π}
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I O z
  -- Set `b 0 = 0` and `b (k + 1) = f.val (k + 1)`, then telescope consecutive differences.
  let b : ℕ → O := fun k ↦ if k = 0 then 0 else f.val k
  have hstep (j : ℕ) : ∃ a : O, b (j + 1) - b j = π ^ j * a := by
    rcases j with _ | j
    · exact ⟨f.val 1, by simp [b]⟩
    · have htr := SModEq.sub_mem.mp (f.property (Nat.le_succ (j + 1))).symm
      rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Algebra.algebraMap_self, RingHom.id_apply, Ideal.mem_span_singleton] at htr
      obtain ⟨a, ha⟩ := htr
      exact ⟨a, by simpa [b] using ha⟩
  choose a ha using hstep
  refine ⟨0, fun j ↦ MvPolynomial.C (a j), fun j ↦ by simp, fun k ↦ ?_⟩
  rw [AdicCompletion.evalₐ_mk]
  rcases k with _ | k
  · have : Subsingleton (O ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Subsingleton.elim _ _
  · have hsum : ∀ m, ∑ j ∈ range m, (algebraMap O O π) ^ j * aeval Empty.elim (C (a j)) = b m := by
      intro m
      induction m with
      | zero => simp [b]
      | succ m ih =>
        rw [sum_range_succ, ih]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, aeval_C]
        linear_combination -(ha m)
    rw [hsum (k + 1)]
    simp [b]

/-- If `S` is `π`-adically complete, the canonical map `S → S†` is bijective. -/
theorem of_bijective_of_isAdicComplete [IsAdicComplete (Ideal.span {algebraMap O S π}) S] :
    Function.Bijective (of π S) := by
  have hbij := AdicCompletion.of_bijective (Ideal.span {algebraMap O S π}) S
  refine ⟨(of_injective_iff π).mpr inferInstance, fun z ↦ ?_⟩
  obtain ⟨s, hs⟩ := hbij.2 (z : piAdicCompletion π S)
  exact ⟨s, Subtype.ext ((coe_of π s).trans hs)⟩

/-- For the base ring `O` itself, `O → O†` is bijective if and only if `O` is `π`-adically
complete. -/
theorem of_self_bijective_iff :
    Function.Bijective (of π O) ↔ IsAdicComplete (Ideal.span {π}) O := by
  refine ⟨fun h ↦ ?_, fun _ ↦ by
    have : IsAdicComplete (Ideal.span {algebraMap O O π}) O := by simpa
    exact of_bijective_of_isAdicComplete π⟩
  have hI : Ideal.span {algebraMap O O π} = Ideal.span {π} := by simp
  rw [← hI, ← AdicCompletion.of_bijective_iff]
  have htop := weakCompletion_self_eq_top π
  refine ⟨fun a b hab ↦ h.1 (Subtype.ext ((coe_of π a).trans (hab.trans (coe_of π b).symm))),
    fun z ↦ ?_⟩
  obtain ⟨a, ha⟩ := h.2 ⟨z, htop.symm ▸ Algebra.mem_top⟩
  exact ⟨a, (coe_of π a).symm.trans (congrArg Subtype.val ha)⟩

/-- If `π` is nilpotent in `O`, then `S → S†` is bijective for every finitely generated
`O`-algebra `S`. -/
theorem of_bijective_of_isNilpotent {π : O} (hπ : IsNilpotent π) :
    Function.Bijective (of π S) := by
  obtain ⟨n, hn⟩ := hπ
  have hpow : Ideal.span {algebraMap O S π} ^ n = ⊥ := by
    rw [Ideal.span_singleton_pow, ← map_pow, hn, map_zero, Ideal.span_singleton_eq_bot]
  have hpow' : Ideal.span {algebraMap O (weakCompletion π S) π} ^ n = ⊥ := by
    rw [Ideal.span_singleton_pow, ← map_pow, hn, map_zero, Ideal.span_singleton_eq_bot]
  refine ⟨(of_injective_iff π).mpr ⟨fun s hs ↦ ?_⟩, fun z ↦ ?_⟩
  · have hsn := hs n
    simpa [hpow, SModEq.zero] using hsn
  · obtain ⟨s, hs⟩ := exists_sub_mem_span_pow π z n
    rw [hpow', Ideal.mem_bot, sub_eq_zero] at hs
    exact ⟨s, hs.symm⟩

/-- For a nonempty finite index type `σ`, the canonical map `O[X_σ] → O[X_σ]†` is bijective if
and only if `π` is nilpotent in `O`. -/
theorem of_mvPolynomial_bijective_iff {σ : Type*} [Nonempty σ] [Finite σ] :
    Function.Bijective (of π (MvPolynomial σ O)) ↔ IsNilpotent π := by
  refine ⟨fun hbij ↦ ?_, of_bijective_of_isNilpotent⟩
  obtain ⟨i⟩ := ‹Nonempty σ›
  let e := AlgEquiv.ofBijective (of π (MvPolynomial σ O)) hbij
  have hu : IsUnit (of π (MvPolynomial σ O) (1 + MvPolynomial.C π * MvPolynomial.X i)) := by
    rw [map_add, map_one, map_mul, MvPolynomial.C_eq_algebraMap, AlgHom.commutes]
    exact isUnit_one_add_algebraMap_mul π _
  have hu' : IsUnit (1 + MvPolynomial.C π * (MvPolynomial.X i : MvPolynomial σ O)) := by
    rw [← e.symm_apply_apply (1 + MvPolynomial.C π * MvPolynomial.X i),
      AlgEquiv.ofBijective_apply]
    exact hu.map e.symm
  have h10 : Finsupp.single i 1 ≠ (0 : σ →₀ ℕ) := Finsupp.single_ne_zero.mpr one_ne_zero
  have hnil := (MvPolynomial.isUnit_iff.mp hu').2 (Finsupp.single i 1) h10
  have hc :
      (1 + MvPolynomial.C π * (MvPolynomial.X i : MvPolynomial σ O)).coeff (Finsupp.single i 1) =
        π := by
    classical
    simp [MvPolynomial.coeff_one, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, h10.symm]
  rwa [hc] at hnil

end weakCompletion

end TauCeti.Dagger
