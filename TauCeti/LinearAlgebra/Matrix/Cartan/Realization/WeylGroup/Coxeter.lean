/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.GroupTheory.Coxeter.Inversion
public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.WeylGroup.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import TauCeti.GroupTheory.Coxeter.Dihedral
import TauCeti.GroupTheory.Coxeter.Geometric.Basic
import TauCeti.GroupTheory.Coxeter.Parabolic
import TauCeti.GroupTheory.Coxeter.StrongExchange

/-!
# The Weyl group of a generalized Cartan realization as a Coxeter group

Let `A` be a generalized Cartan matrix (`aᵢᵢ = 2`, `aᵢⱼ ≤ 0` for `i ≠ j`, and `aᵢⱼ = 0 ↔ aⱼᵢ = 0`)
and let `R` be a realization of `A` over a field `K` of characteristic zero. This file proves
Kac's Lemma 3.11 and Proposition 3.13 without assuming symmetrizability of `A`, finiteness of `I`,
or finite-dimensionality of `H`:

* `R.coxeterToWeyl : (cartanCoxeterMatrix A).Group →* R.weylGroup` is an isomorphism
  (`R.coxeterEquivWeyl`), making `R.weylGroup` into a `CoxeterSystem` for `cartanCoxeterMatrix A`
  (`R.weylCoxeterSystem`) whose Coxeter length agrees with `R.length`
  (`R.weylCoxeterSystem_length_eq`);
* the sign of `w(αᵢ)` characterizes right descents (`w • αᵢ ∈ Q₊ ↔ ¬ IsRightDescent w i` and
  `-(w • αᵢ) ∈ Q₊ ↔ IsRightDescent w i`), so `R.rootLatticeAction` is faithful on `Q`;
* for **real roots** `Φ^re = W · {αᵢ}` (`R.realRoots`), both the **real coroot**
  `(w αᵢ)^∨ = w(hᵢ)` (`R.realCoroot`) and the **real reflection** `s_{w αᵢ} = w sᵢ w⁻¹`
  (`R.realReflection`) are independent of the presentation `α = w(αᵢ)`, and reflections are
  attached exclusively to real roots;
* rank-one and rank-two realizations specialize to order `2` (`A₁`), `DihedralGroup 4` of order `8`
  (`B₂`), and the infinite dihedral group `DihedralGroup 0` (affine `A₁⁽¹⁾`).

## Main definitions

* `TauCeti.CartanRealization.coxeterEquivWeyl`, `TauCeti.CartanRealization.weylCoxeterSystem`.
* `TauCeti.CartanRealization.realRoots`, `TauCeti.CartanRealization.realCoroot`,
  `TauCeti.CartanRealization.realReflection`.
* `TauCeti.CartanRealization.dihedralGroupMulEquivWeyl`.

## Main results

* `TauCeti.CartanRealization.weylCoxeterSystem_length_eq`,
  `TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple`.
* `TauCeti.CartanRealization.length_mul_weylSimple_lt_iff`,
  `TauCeti.CartanRealization.length_mul_weylSimple_eq_add_one_iff`,
  `TauCeti.CartanRealization.rootLatticeAction_injective`.
* `TauCeti.CartanRealization.realCoroot_smul_root`, `TauCeti.CartanRealization.realCoroot_smul`,
  `TauCeti.CartanRealization.realReflection_smul_root`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §§3.7, 3.11, 3.13 and Proposition 5.1.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge University Press, 1990, §5.4.
-/

public section

open Module

namespace TauCeti.CartanRealization

/-! ### Coordinate reflections on the free `ℤ`-module `I →₀ ℤ` -/

section CoordRepresentation

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ}

section Prelim

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

private theorem rootLinearCombination_injective :
    Function.Injective (Finsupp.linearCombination ℤ R.root) :=
  (R.root_linearIndependent.restrict_scalars' ℤ).finsuppLinearCombination_injective

/-- An integral combination of simple roots lies in `R.posRootCone` iff its coordinates are
nonnegative. -/
private theorem rootLinearCombination_mem_posRootCone_iff (x : I →₀ ℤ) :
    Finsupp.linearCombination ℤ R.root x ∈ R.posRootCone ↔ 0 ≤ x := by
  let castNat : (I →₀ ℕ) →+ (I →₀ ℤ) := Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)
  have hcast_apply (y : I →₀ ℕ) (i : I) : castNat y i = (y i : ℤ) := by simp [castNat]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rw [R.posRootCone_def] at hx
    have hex : ∀ φ ∈ Submodule.span ℕ (Set.range R.root),
        ∃ y : I →₀ ℕ, Finsupp.linearCombination ℤ R.root (castNat y) = φ := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem _ h => obtain ⟨i, rfl⟩ := h; exact ⟨Finsupp.single i 1, by simp [castNat]⟩
      | zero => exact ⟨0, by simp⟩
      | add _ _ _ _ ih₁ ih₂ =>
        obtain ⟨y₁, hy₁⟩ := ih₁; obtain ⟨y₂, hy₂⟩ := ih₂
        exact ⟨y₁ + y₂, by rw [map_add, map_add, hy₁, hy₂]⟩
      | smul n _ _ ih => obtain ⟨y, hy⟩ := ih; exact ⟨n • y, by rw [map_nsmul, map_nsmul, hy]⟩
    obtain ⟨y, hy⟩ := hex _ hx
    rw [← R.rootLinearCombination_injective hy]
    intro i; rw [hcast_apply]; exact Nat.cast_nonneg (y i)
  · let y : I →₀ ℕ := x.mapRange Int.toNat rfl
    have hyx : castNat y = x := by ext i; rw [hcast_apply]; exact Int.toNat_of_nonneg (hx i)
    rw [← hyx]
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ ih₁ ih₂ => rw [map_add, map_add]; exact add_mem ih₁ ih₂
    | single i n =>
      have hsingle : castNat (Finsupp.single i n) = Finsupp.single i (n : ℤ) := by simp [castNat]
      rw [hsingle, Finsupp.linearCombination_single, natCast_zsmul]
      exact Submodule.smul_mem _ n (R.root_mem_posRootCone i)

end Prelim

/-- The simple coordinate reflection `x ↦ x - (∑ⱼ xⱼ A i j) eᵢ` on `I →₀ ℤ`. -/
private noncomputable def coordReflection (A : Matrix I I ℤ) (hdiag : ∀ i, A i i = 2) (i : I) :
    (I →₀ ℤ) ≃ₗ[ℤ] (I →₀ ℤ) :=
  Module.reflection (x := Finsupp.single i (1 : ℤ)) (f := Finsupp.linearCombination ℤ (A i))
    (by simp [hdiag i])

private theorem coordReflection_apply {A : Matrix I I ℤ} (hdiag : ∀ i, A i i = 2) (i : I)
    (x : I →₀ ℤ) :
    coordReflection A hdiag i x = x - Finsupp.linearCombination ℤ (A i) x • Finsupp.single i 1 :=
  Module.reflection_apply x _

private theorem coordReflection_single_self {A : Matrix I I ℤ} (hdiag : ∀ i, A i i = 2) (i : I) :
    coordReflection A hdiag i (Finsupp.single i 1) = -Finsupp.single i 1 :=
  Module.reflection_apply_self _

private theorem coordReflection_single {A : Matrix I I ℤ} (hdiag : ∀ i, A i i = 2) (i j : I) :
    coordReflection A hdiag i (Finsupp.single j 1) =
      Finsupp.single j 1 - A i j • Finsupp.single i 1 := by
  rw [coordReflection_apply, Finsupp.linearCombination_single, one_smul]

omit [CharZero K] in
private theorem rootLinearCombination_coordReflection
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hdiag : ∀ i, A i i = 2) (i : I)
    (x : I →₀ ℤ) :
    Finsupp.linearCombination ℤ R.root (coordReflection A hdiag i x) =
      R.simpleReflection (mapIntCast_diag hdiag) i (Finsupp.linearCombination ℤ R.root x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | single j c =>
    have hAij : (A.map (Int.cast : ℤ → K)) i j • R.root i = A i j • R.root i := by
      rw [Matrix.map_apply]; exact Int.cast_smul_eq_zsmul K (A i j) (R.root i)
    rw [← Finsupp.smul_single_one j c, map_smul, map_smul, map_zsmul, map_zsmul]
    congr 1
    rw [coordReflection_single, map_sub, map_zsmul, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, one_smul, one_smul, simpleReflection_root, hAij]

private theorem isLiftable_coordReflection
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    (cartanCoxeterMatrix A).IsLiftable (coordReflection A hdiag) := by
  intro i j
  have hpow (m : ℕ) (x : I →₀ ℤ) :
      Finsupp.linearCombination ℤ R.root
          (((coordReflection A hdiag i * coordReflection A hdiag j) ^ m) x) =
        ((R.simpleReflection (mapIntCast_diag hdiag) i *
          R.simpleReflection (mapIntCast_diag hdiag) j) ^ m)
          (Finsupp.linearCombination ℤ R.root x) := by
    induction m generalizing x with
    | zero => simp
    | succ m ih =>
      simp only [pow_succ', mul_apply_eq_comp, R.rootLinearCombination_coordReflection hdiag, ih]
  refine LinearEquiv.ext fun x ↦ R.rootLinearCombination_injective ?_
  rw [hpow, R.simpleReflection_mul_simpleReflection_pow hdiag hzero i j, one_apply_eq_self,
    one_apply_eq_self]

/-- The integral reflection representation of `(cartanCoxeterMatrix A).Group` on `I →₀ ℤ`. -/
private noncomputable def coordRep
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    (cartanCoxeterMatrix A).Group →* ((I →₀ ℤ) ≃ₗ[ℤ] (I →₀ ℤ)) :=
  (cartanCoxeterMatrix A).toCoxeterSystem.lift
    ⟨coordReflection A hdiag, R.isLiftable_coordReflection hdiag hzero⟩

variable (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

private theorem coordRep_simple (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.coordRep hdiag hzero ((cartanCoxeterMatrix A).simple i) = coordReflection A hdiag i :=
  (cartanCoxeterMatrix A).toCoxeterSystem.lift_apply_simple _ i

private theorem coordRep_mul_simple_single (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (g : (cartanCoxeterMatrix A).Group) (i : I) :
    R.coordRep hdiag hzero (g * (cartanCoxeterMatrix A).simple i) (Finsupp.single i 1) =
      -R.coordRep hdiag hzero g (Finsupp.single i 1) := by
  rw [map_mul, mul_apply_eq_comp, R.coordRep_simple hdiag hzero, coordReflection_single_self,
    map_neg]

private theorem rootLinearCombination_coordRep (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (g : (cartanCoxeterMatrix A).Group) (x : I →₀ ℤ) :
    Finsupp.linearCombination ℤ R.root (R.coordRep hdiag hzero g x) =
      R.coxeterToWeyl hdiag hzero g • Finsupp.linearCombination ℤ R.root x := by
  induction g using (cartanCoxeterMatrix A).toCoxeterSystem.simple_induction generalizing x with
  | one => simp
  | simple i =>
    rw [CoxeterMatrix.toCoxeterSystem_simple, R.coordRep_simple, R.coxeterToWeyl_simple,
      weylSimple_smul, R.rootLinearCombination_coordReflection]
  | mul g₁ g₂ ih₁ ih₂ => rw [map_mul, mul_apply_eq_comp, ih₁, ih₂, map_mul, mul_smul]

/-! #### Rank-two alternating coordinates and Kac's sign-length theorem -/

private def rankTwoCoeffs (a b : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 =>
    let p := rankTwoCoeffs a b k
    if Even k then (p.1, b * p.1 - p.2) else (a * p.2 - p.1, p.2)

private theorem coordRep_wordProd_alternatingWord (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) (k : ℕ) :
    R.coordRep hdiag hzero
        ((cartanCoxeterMatrix A).toCoxeterSystem.wordProd (CoxeterSystem.alternatingWord i j k))
        (Finsupp.single i 1) =
      (rankTwoCoeffs (-A i j) (-A j i) k).1 • Finsupp.single i 1 +
        (rankTwoCoeffs (-A i j) (-A j i) k).2 • Finsupp.single j 1 := by
  induction k with
  | zero => simp [CoxeterSystem.alternatingWord, rankTwoCoeffs]
  | succ k ih =>
    rw [CoxeterSystem.alternatingWord_succ', CoxeterSystem.wordProd_cons, map_mul,
      mul_apply_eq_comp, ih]
    by_cases hk : Even k
    · simp only [rankTwoCoeffs, hk, ↓reduceIte, CoxeterMatrix.toCoxeterSystem_simple,
        R.coordRep_simple, map_add, map_zsmul, coordReflection_single hdiag j i,
        coordReflection_single_self hdiag j]
      module
    · simp only [rankTwoCoeffs, hk, ↓reduceIte, CoxeterMatrix.toCoxeterSystem_simple,
        R.coordRep_simple, map_add, map_zsmul, coordReflection_single_self hdiag i,
        coordReflection_single hdiag i j]
      module

private theorem rankTwoCoeffs_nonneg_of_four_le {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 4 ≤ a * b) (k : ℕ) :
    0 ≤ (rankTwoCoeffs a b k).1 ∧ 0 ≤ (rankTwoCoeffs a b k).2 := by
  have ha1 : 1 ≤ a := by nlinarith
  have hb1 : 1 ≤ b := by nlinarith
  suffices hinv : ∀ n,
      if Even n then
        1 ≤ (rankTwoCoeffs a b n).1 ∧ 0 ≤ (rankTwoCoeffs a b n).2 ∧
          2 * (rankTwoCoeffs a b n).2 < b * (rankTwoCoeffs a b n).1
      else
        1 ≤ (rankTwoCoeffs a b n).1 ∧ 1 ≤ (rankTwoCoeffs a b n).2 ∧
          2 * (rankTwoCoeffs a b n).1 < a * (rankTwoCoeffs a b n).2 by
    have hk := hinv k; split_ifs at hk <;> omega
  intro n
  induction n with
  | zero => simp only [Even.zero, ↓reduceIte, rankTwoCoeffs, mul_zero, mul_one]; omega
  | succ n ih =>
    by_cases hn : Even n
    · have hn' : ¬ Even (n + 1) := by simp only [Nat.even_iff] at *; omega
      simp only [hn, ↓reduceIte] at ih
      simp only [hn', ↓reduceIte, rankTwoCoeffs, hn]
      obtain ⟨hx, hy, hlt⟩ := ih
      exact ⟨hx, by omega, by nlinarith⟩
    · have hn' : Even (n + 1) := by simp only [Nat.even_iff] at *; omega
      simp only [hn, ↓reduceIte] at ih
      simp only [hn', ↓reduceIte, rankTwoCoeffs, hn]
      obtain ⟨hx, hy, hlt⟩ := ih
      exact ⟨by omega, by omega, by nlinarith⟩

private theorem rankTwoCoeffs_nonneg_of_le_three {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a * b ≤ 3) {k : ℕ} (hk : k < coxeterOrder (a * b)) :
    0 ≤ (rankTwoCoeffs a b k).1 ∧ 0 ≤ (rankTwoCoeffs a b k).2 := by
  have hm0 : 0 ≤ a * b := mul_nonneg ha hb
  rcases (by omega : a * b = 0 ∨ a * b = 1 ∨ a * b = 2 ∨ a * b = 3) with h0 | h1 | h2 | h3
  · rw [h0, coxeterOrder_zero] at hk
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp [rankTwoCoeffs, hb]
  · rw [h1, coxeterOrder_one] at hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;>
      simp [rankTwoCoeffs, hb, h1]
  · rw [h2, coxeterOrder_two] at hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
      simp [rankTwoCoeffs, hb, h2]
  · rw [h3, coxeterOrder_three] at hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rankTwoCoeffs, hb, h3, mul_two, Nat.even_iff]

private theorem exists_nonneg_coordRep_of_mem_parabolic_pair (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) {i j : I}
    {v : (cartanCoxeterMatrix A).Group}
    (hv : v ∈ (cartanCoxeterMatrix A).toCoxeterSystem.parabolic {i, j})
    (hvi : ¬ (cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent v i) :
    ∃ x y : ℤ, 0 ≤ x ∧ 0 ≤ y ∧
      R.coordRep hdiag hzero v (Finsupp.single i 1) =
        x • Finsupp.single i 1 + y • Finsupp.single j 1 := by
  let cs := (cartanCoxeterMatrix A).toCoxeterSystem
  have hlen := cs.not_isRightDescent_iff.mp hvi
  have hword : cs.wordProd (CoxeterSystem.alternatingWord i j (cs.length v)) = v := by
    refine (cs.wordProd_alternatingWord_eq_of_mem_parabolic_pair hv).elim id fun h ↦ ?_
    rcases hk : cs.length v with - | k
    · simp [cs.length_eq_zero_iff.mp hk, CoxeterSystem.alternatingWord]
    · rw [hk, CoxeterSystem.alternatingWord_succ, CoxeterSystem.wordProd_concat] at h
      have hle := cs.length_wordProd_le (CoxeterSystem.alternatingWord i j k)
      rw [CoxeterSystem.length_alternatingWord] at hle
      rw [← h, cs.simple_mul_simple_cancel_right, h] at hlen; omega
  have hred : cs.IsReduced (CoxeterSystem.alternatingWord j i (cs.length v + 1)) := by
    rw [CoxeterSystem.IsReduced, CoxeterSystem.alternatingWord_succ,
      CoxeterSystem.wordProd_concat, hword, hlen, List.concat_eq_append, List.length_append,
      CoxeterSystem.length_alternatingWord, List.length_singleton]
  have hk : cs.length v < cartanCoxeterMatrix A i j ∨ cartanCoxeterMatrix A i j = 0 := by
    by_contra hcon
    rw [not_or, not_lt, ← (cartanCoxeterMatrix A).symmetric j i] at hcon
    exact cs.not_isReduced_alternatingWord j i hcon.2 (by omega) hred
  rcases eq_or_ne i j with rfl | hij
  · simp only [cartanCoxeterMatrix_self, Nat.lt_one_iff, one_ne_zero, or_false] at hk
    rw [cs.length_eq_zero_iff.mp hk, map_one, one_apply_eq_self]
    exact ⟨1, 0, zero_le_one, le_rfl, by simp⟩
  rw [← hword, R.coordRep_wordProd_alternatingWord hdiag hzero]
  have ha : 0 ≤ -A i j := neg_nonneg.mpr (hoff i j hij)
  have hb : 0 ≤ -A j i := neg_nonneg.mpr (hoff j i hij.symm)
  have hprod : (-A i j) * (-A j i) = A i j * A j i := neg_mul_neg _ _
  rcases le_or_gt (A i j * A j i) 3 with hle | hgt
  · have hM := cartanCoxeterMatrix_of_ne_of_le A hij hle
    have hpos : 0 < cartanCoxeterMatrix A i j := by
      have hm0 : 0 ≤ A i j * A j i := hprod ▸ mul_nonneg ha hb
      have hmem : A i j * A j i ∈ ({0, 1, 2, 3} : Set ℤ) := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; omega
      have := two_le_coxeterOrder hmem; omega
    obtain ⟨hx, hy⟩ := rankTwoCoeffs_nonneg_of_le_three ha hb (hprod.symm ▸ hle)
      (by rw [hprod, ← hM]; exact hk.resolve_right hpos.ne')
    exact ⟨_, _, hx, hy, rfl⟩
  · obtain ⟨hx, hy⟩ := rankTwoCoeffs_nonneg_of_four_le ha hb (by rw [hprod]; omega) (cs.length v)
    exact ⟨_, _, hx, hy, rfl⟩

private theorem coordRep_single_nonneg (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {g : (cartanCoxeterMatrix A).Group} {i : I}
    (h : ¬ (cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent g i) :
    0 ≤ R.coordRep hdiag hzero g (Finsupp.single i 1) := by
  let cs := (cartanCoxeterMatrix A).toCoxeterSystem
  induction hn : cs.length g using Nat.strong_induction_on generalizing g i with
  | _ n ih =>
    rcases eq_or_ne g 1 with rfl | hg
    · simp
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hg
    obtain ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, -⟩ := cs.existsUnique_isMinimalCosetRep_mul {i, j} g
    dsimp only at hu hv huv; subst huv
    have hu' := cs.isMinimalCosetRep_iff.mp hu
    have hlen := cs.length_mul_of_isMinimalCosetRep hu hv
    have hv₁ : v ≠ 1 := by rintro rfl; exact hu' j (by simp) (by simpa using hj)
    have hvpos : 0 < cs.length v := Nat.pos_of_ne_zero (mt cs.length_eq_zero_iff.mp hv₁)
    have hvi : ¬ cs.IsRightDescent v i := fun hd ↦ h <| by
      rw [CoxeterSystem.IsRightDescent] at hd ⊢
      rw [mul_assoc, cs.length_mul_of_isMinimalCosetRep hu
        (mul_mem hv (cs.simple_mem_parabolic (by simp))), hlen]; omega
    obtain ⟨x, y, hx, hy, hxy⟩ :=
      R.exists_nonneg_coordRep_of_mem_parabolic_pair hdiag hoff hzero hv hvi
    rw [map_mul, mul_apply_eq_comp, hxy, map_add, map_zsmul, map_zsmul]
    exact add_nonneg (smul_nonneg hx (ih _ (by omega) (hu' i (by simp)) rfl))
      (smul_nonneg hy (ih _ (by omega) (hu' j (by simp)) rfl))

private theorem coordRep_single_pos (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {g : (cartanCoxeterMatrix A).Group} {i : I}
    (h : ¬ (cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent g i) :
    0 < R.coordRep hdiag hzero g (Finsupp.single i 1) :=
  lt_of_le_of_ne (R.coordRep_single_nonneg hdiag hoff hzero h)
    ((map_ne_zero_iff _ (R.coordRep hdiag hzero g).injective).mpr
      (Finsupp.single_ne_zero.mpr one_ne_zero)).symm

private theorem coordRep_single_neg (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {g : (cartanCoxeterMatrix A).Group} {i : I}
    (h : (cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent g i) :
    R.coordRep hdiag hzero g (Finsupp.single i 1) < 0 := by
  have hpos := R.coordRep_single_pos hdiag hoff hzero
    ((cartanCoxeterMatrix A).toCoxeterSystem.isRightDescent_iff_not_isRightDescent_mul.mp h)
  rwa [CoxeterMatrix.toCoxeterSystem_simple, R.coordRep_mul_simple_single, neg_pos] at hpos

private theorem coordRep_injective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Injective (R.coordRep hdiag hzero) := by
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦ by_contra fun hg₁ ↦ ?_
  obtain ⟨i, hi⟩ := (cartanCoxeterMatrix A).toCoxeterSystem.exists_rightDescent_of_ne_one hg₁
  have hneg := R.coordRep_single_neg hdiag hoff hzero hi
  rw [hg, one_apply_eq_self] at hneg
  exact (Finsupp.single_nonneg.mpr zero_le_one).not_gt hneg

/-! ### Kac's Proposition 3.13 and Lemma 3.11: the Weyl group as a Coxeter system -/

/-- **Kac, Proposition 3.13 (injectivity)**: `R.coxeterToWeyl` is injective for any generalized
Cartan matrix over a characteristic-zero field. -/
theorem coxeterToWeyl_injective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Injective (R.coxeterToWeyl hdiag hzero) := by
  refine (injective_iff_map_eq_one _).mpr fun g hg ↦
    R.coordRep_injective hdiag hoff hzero <| LinearEquiv.ext fun x ↦ ?_
  refine R.rootLinearCombination_injective ?_
  rw [R.rootLinearCombination_coordRep, hg, one_smul, map_one, one_apply_eq_self]

/-- **Kac, Proposition 3.13**: `R.coxeterToWeyl` is bijective. -/
theorem coxeterToWeyl_bijective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Bijective (R.coxeterToWeyl hdiag hzero) :=
  ⟨R.coxeterToWeyl_injective hdiag hoff hzero, R.coxeterToWeyl_surjective hdiag hzero⟩

/-- **The Weyl group isomorphism with the Coxeter group** (Kac, Proposition 3.13). -/
noncomputable def coxeterEquivWeyl (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    (cartanCoxeterMatrix A).Group ≃* R.weylGroup (mapIntCast_diag hdiag) :=
  MulEquiv.ofBijective (R.coxeterToWeyl hdiag hzero) (R.coxeterToWeyl_bijective hdiag hoff hzero)

@[simp]
theorem coxeterEquivWeyl_apply (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (g : (cartanCoxeterMatrix A).Group) :
    R.coxeterEquivWeyl hdiag hoff hzero g = R.coxeterToWeyl hdiag hzero g := (rfl)

theorem coxeterEquivWeyl_simple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.coxeterEquivWeyl hdiag hoff hzero ((cartanCoxeterMatrix A).simple i) =
      R.weylSimple (mapIntCast_diag hdiag) i :=
  R.coxeterToWeyl_simple hdiag hzero i

@[simp]
theorem coxeterEquivWeyl_symm_weylSimple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    (R.coxeterEquivWeyl hdiag hoff hzero).symm (R.weylSimple (mapIntCast_diag hdiag) i) =
      (cartanCoxeterMatrix A).simple i :=
  (R.coxeterEquivWeyl hdiag hoff hzero).symm_apply_eq.mpr
    (R.coxeterEquivWeyl_simple hdiag hoff hzero i).symm

/-- **The Coxeter system structure on `R.weylGroup`** with Coxeter matrix `cartanCoxeterMatrix A`
and simple generators `R.weylSimple`. -/
noncomputable def weylCoxeterSystem (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    CoxeterSystem (cartanCoxeterMatrix A) (R.weylGroup (mapIntCast_diag hdiag)) :=
  ⟨(R.coxeterEquivWeyl hdiag hoff hzero).symm⟩

@[simp]
theorem weylCoxeterSystem_simple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    (R.weylCoxeterSystem hdiag hoff hzero).simple i =
      R.weylSimple (mapIntCast_diag hdiag) i := by
  rw [weylCoxeterSystem, CoxeterSystem.simple, MulEquiv.symm_symm]
  exact R.coxeterEquivWeyl_simple hdiag hoff hzero i

@[simp]
theorem coe_weylCoxeterSystem_wordProd (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (ω : List I) :
    ((R.weylCoxeterSystem hdiag hoff hzero).wordProd ω : Dual K H ≃ₗ[K] Dual K H) =
      (ω.map (R.simpleReflection (mapIntCast_diag hdiag))).prod := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [(R.weylCoxeterSystem hdiag hoff hzero).wordProd_cons, Subgroup.coe_mul,
      R.weylCoxeterSystem_simple, coe_weylSimple, ih, List.map_cons, List.prod_cons]

/-- **Coxeter length agrees with generator word length `R.length`** on `R.weylGroup`. -/
@[simp]
theorem weylCoxeterSystem_length_eq (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (mapIntCast_diag hdiag)) :
    (R.weylCoxeterSystem hdiag hoff hzero).length w = R.length (mapIntCast_diag hdiag) w := by
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  refine le_antisymm ?_ ?_
  · obtain ⟨ω, hlen, hprod⟩ := R.exists_list_length_eq (mapIntCast_diag hdiag) w
    have hword : cs.wordProd ω = w :=
      Subtype.ext ((R.coe_weylCoxeterSystem_wordProd hdiag hoff hzero ω).trans hprod)
    rw [← hlen, ← hword]; exact cs.length_wordProd_le ω
  · obtain ⟨ω, hred, rfl⟩ := cs.exists_isReduced w
    rw [hred.eq]
    exact R.length_le_of_prod_eq (mapIntCast_diag hdiag)
      (R.coe_weylCoxeterSystem_wordProd hdiag hoff hzero ω).symm

/-- **Exact dihedral orders in `R.weylGroup`**: `sᵢ * sⱼ` has exact order
`cartanCoxeterMatrix A i j` (`0` when infinite). -/
@[simp]
theorem orderOf_weylSimple_mul_weylSimple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    orderOf (R.weylSimple (mapIntCast_diag hdiag) i * R.weylSimple (mapIntCast_diag hdiag) j) =
      cartanCoxeterMatrix A i j := by
  rw [← R.weylCoxeterSystem_simple hdiag hoff hzero, ← R.weylCoxeterSystem_simple hdiag hoff hzero]
  exact (R.weylCoxeterSystem hdiag hoff hzero).orderOf_simple_mul_simple i j

/-- Simple reflections for distinct indices are distinct in `R.weylGroup`. -/
theorem weylSimple_injective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Injective (R.weylSimple (mapIntCast_diag hdiag)) := by
  have h : R.weylSimple (mapIntCast_diag hdiag) = (R.weylCoxeterSystem hdiag hoff hzero).simple :=
    funext fun i ↦ (R.weylCoxeterSystem_simple hdiag hoff hzero i).symm
  rw [h]; exact (R.weylCoxeterSystem hdiag hoff hzero).simple_injective

private theorem length_weylCoxeterSystem_eq (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (g : (cartanCoxeterMatrix A).Group) :
    (R.weylCoxeterSystem hdiag hoff hzero).length (R.coxeterEquivWeyl hdiag hoff hzero g) =
      (cartanCoxeterMatrix A).toCoxeterSystem.length g := by
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  let cs₀ := (cartanCoxeterMatrix A).toCoxeterSystem
  have hword (ω : List I) :
      R.coxeterEquivWeyl hdiag hoff hzero (cs₀.wordProd ω) = cs.wordProd ω := by
    induction ω with
    | nil => simp
    | cons i ω ih =>
      rw [cs₀.wordProd_cons, cs.wordProd_cons, map_mul, ih,
        CoxeterMatrix.toCoxeterSystem_simple, R.coxeterEquivWeyl_simple, R.weylCoxeterSystem_simple]
  refine le_antisymm ?_ ?_
  · obtain ⟨ω, hred, rfl⟩ := cs₀.exists_isReduced g
    rw [hred.eq, hword]; exact cs.length_wordProd_le ω
  · obtain ⟨ω, hred, hw⟩ := cs.exists_isReduced (R.coxeterEquivWeyl hdiag hoff hzero g)
    have hg : cs₀.wordProd ω = g :=
      (R.coxeterEquivWeyl hdiag hoff hzero).injective ((hword ω).trans hw.symm)
    rw [hw, hred.eq, ← hg]; exact cs₀.length_wordProd_le ω

private theorem isRightDescent_weylCoxeterSystem_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (g : (cartanCoxeterMatrix A).Group) (i : I) :
    (R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent
        (R.coxeterEquivWeyl hdiag hoff hzero g) i ↔
      (cartanCoxeterMatrix A).toCoxeterSystem.IsRightDescent g i := by
  rw [CoxeterSystem.IsRightDescent, CoxeterSystem.IsRightDescent, R.weylCoxeterSystem_simple,
    CoxeterMatrix.toCoxeterSystem_simple, ← R.coxeterEquivWeyl_simple hdiag hoff hzero i,
    ← map_mul, R.length_weylCoxeterSystem_eq, R.length_weylCoxeterSystem_eq]

/-- **Kac, Lemma 3.11 (positive form)**: `w(αᵢ)` lies in the positive root cone `Q₊` if and only if
`i` is not a right descent of `w`. -/
theorem smul_root_mem_posRootCone_iff_not_isRightDescent (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (mapIntCast_diag hdiag)) (i : I) :
    w • R.root i ∈ R.posRootCone ↔
      ¬ (R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent w i := by
  obtain ⟨g, rfl⟩ := (R.coxeterEquivWeyl hdiag hoff hzero).surjective w
  rw [R.isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero g i, coxeterEquivWeyl_apply]
  have hroot : R.coxeterToWeyl hdiag hzero g • R.root i =
      Finsupp.linearCombination ℤ R.root (R.coordRep hdiag hzero g (Finsupp.single i 1)) := by
    rw [R.rootLinearCombination_coordRep, Finsupp.linearCombination_single, one_smul]
  rw [hroot, R.rootLinearCombination_mem_posRootCone_iff]
  refine ⟨fun hnonneg hd ↦ hnonneg.not_gt (R.coordRep_single_neg hdiag hoff hzero hd),
    fun hd ↦ (R.coordRep_single_pos hdiag hoff hzero hd).le⟩

/-- **Kac, Lemma 3.11 (negative form)**: `-w(αᵢ)` lies in `Q₊` if and only if `i` is a right
descent of `w`. -/
theorem neg_smul_root_mem_posRootCone_iff_isRightDescent (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (mapIntCast_diag hdiag)) (i : I) :
    -(w • R.root i) ∈ R.posRootCone ↔
      (R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent w i := by
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  have hneg : -(w • R.root i) = (w * R.weylSimple (mapIntCast_diag hdiag) i) • R.root i := by
    rw [mul_smul, weylSimple_smul, simpleReflection_root_self, smul_neg]
  rw [hneg, R.smul_root_mem_posRootCone_iff_not_isRightDescent hdiag hoff hzero,
    ← R.weylCoxeterSystem_simple hdiag hoff hzero i,
    ← cs.isRightDescent_iff_not_isRightDescent_mul]

/-- **Kac, Lemma 3.11 (length decrease)**: `ℓ(w sᵢ) < ℓ(w)` if and only if `-w(αᵢ) ∈ Q₊`. -/
theorem length_mul_weylSimple_lt_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (mapIntCast_diag hdiag)) (i : I) :
    R.length (mapIntCast_diag hdiag) (w * R.weylSimple (mapIntCast_diag hdiag) i) <
        R.length (mapIntCast_diag hdiag) w ↔
      -(w • R.root i) ∈ R.posRootCone := by
  rw [R.neg_smul_root_mem_posRootCone_iff_isRightDescent hdiag hoff hzero,
    CoxeterSystem.IsRightDescent, R.weylCoxeterSystem_simple, R.weylCoxeterSystem_length_eq,
    R.weylCoxeterSystem_length_eq]

/-- **Kac, Lemma 3.11 (length increase)**: `ℓ(w sᵢ) = ℓ(w) + 1` if and only if `w(αᵢ) ∈ Q₊`. -/
theorem length_mul_weylSimple_eq_add_one_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (mapIntCast_diag hdiag)) (i : I) :
    R.length (mapIntCast_diag hdiag) (w * R.weylSimple (mapIntCast_diag hdiag) i) =
        R.length (mapIntCast_diag hdiag) w + 1 ↔
      w • R.root i ∈ R.posRootCone := by
  rw [R.smul_root_mem_posRootCone_iff_not_isRightDescent hdiag hoff hzero,
    (R.weylCoxeterSystem hdiag hoff hzero).not_isRightDescent_iff, R.weylCoxeterSystem_simple,
    R.weylCoxeterSystem_length_eq, R.weylCoxeterSystem_length_eq]

/-- A Weyl group element fixing every simple root has no right descents and is therefore `1`. -/
theorem eq_one_of_forall_smul_root_eq (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {w : R.weylGroup (mapIntCast_diag hdiag)} (hw : ∀ i, w • R.root i = R.root i) : w = 1 := by
  by_contra hw₁
  obtain ⟨i, hi⟩ := (R.weylCoxeterSystem hdiag hoff hzero).exists_rightDescent_of_ne_one hw₁
  have hpos : w • R.root i ∈ R.posRootCone := (hw i).symm ▸ R.root_mem_posRootCone i
  exact ((R.smul_root_mem_posRootCone_iff_not_isRightDescent hdiag hoff hzero w i).mp hpos) hi

/-- **Faithfulness on the root lattice `Q`**: `R.rootLatticeAction` is injective, even when `A` is
singular and `H` is an enlarged realization. -/
theorem rootLatticeAction_injective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Injective (R.rootLatticeAction hdiag) := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦
    R.eq_one_of_forall_smul_root_eq hdiag hoff hzero fun i ↦ ?_
  simpa using congrArg Subtype.val (DFunLike.congr_fun hw ⟨R.root i, R.root_mem_rootLattice i⟩)

end CoordRepresentation

/-! ### Real roots, real coroots and real reflections -/

section RealRootsBasic

variable {I K H : Type*} [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hdiag : ∀ i, A i i = 2)

/-- The **real roots** `Φ^re = W · {αᵢ}` of the realization. -/
def realRoots : Set (Dual K H) :=
  {α | ∃ (w : R.weylGroup (mapIntCast_diag hdiag)) (i : I), w • R.root i = α}

theorem mem_realRoots_iff {α : Dual K H} :
    α ∈ R.realRoots hdiag ↔
      ∃ (w : R.weylGroup (mapIntCast_diag hdiag)) (i : I), w • R.root i = α := Iff.rfl

@[simp]
theorem root_mem_realRoots (i : I) : R.root i ∈ R.realRoots hdiag := ⟨1, i, one_smul _ _⟩

theorem smul_root_mem_realRoots (w : R.weylGroup (mapIntCast_diag hdiag)) (i : I) :
    w • R.root i ∈ R.realRoots hdiag := ⟨w, i, rfl⟩

@[simp]
theorem smul_mem_realRoots_iff (w : R.weylGroup (mapIntCast_diag hdiag)) {α : Dual K H} :
    w • α ∈ R.realRoots hdiag ↔ α ∈ R.realRoots hdiag := by
  have hmaps (u : R.weylGroup (mapIntCast_diag hdiag)) {β : Dual K H}
      (hβ : β ∈ R.realRoots hdiag) : u • β ∈ R.realRoots hdiag := by
    obtain ⟨v, i, rfl⟩ := hβ; exact ⟨u * v, i, (mul_smul u v (R.root i)).symm⟩
  exact ⟨fun h ↦ by simpa using hmaps w⁻¹ h, hmaps w⟩

@[simp]
theorem neg_mem_realRoots_iff {α : Dual K H} :
    -α ∈ R.realRoots hdiag ↔ α ∈ R.realRoots hdiag := by
  have hmaps {β : Dual K H} (hβ : β ∈ R.realRoots hdiag) : -β ∈ R.realRoots hdiag := by
    obtain ⟨w, i, rfl⟩ := hβ
    refine ⟨w * R.weylSimple (mapIntCast_diag hdiag) i, i, ?_⟩
    rw [mul_smul, weylSimple_smul, simpleReflection_root_self, smul_neg]
  exact ⟨fun h ↦ by simpa using hmaps h, hmaps⟩

theorem realRoots_subset_rootLattice : R.realRoots hdiag ⊆ R.rootLattice := by
  rintro _ ⟨w, i, rfl⟩; exact R.smul_mem_rootLattice hdiag w (R.root_mem_rootLattice i)

/-- Every real root is nonzero. -/
theorem ne_zero_of_mem_realRoots {α : Dual K H} (hα : α ∈ R.realRoots hdiag) : α ≠ 0 := by
  obtain ⟨w, i, rfl⟩ := hα
  exact (map_ne_zero_iff w.1 w.1.injective).mpr (R.root_linearIndependent.ne_zero i)

/-- **The real coroot `α^∨ ∈ H`** attached to a real root `α ∈ R.realRoots`: if `α = w(αᵢ)`, then
`α^∨ = w(hᵢ)`, independently of the choice of `(w, i)`. -/
noncomputable def realCoroot {α : Dual K H} (hα : α ∈ R.realRoots hdiag) : H :=
  R.corootAction (mapIntCast_diag hdiag) hα.choose (R.coroot hα.choose_spec.choose)

/-- Every real root evaluates to `2` on its real coroot. -/
@[simp]
theorem apply_realCoroot_self {α : Dual K H} (hα : α ∈ R.realRoots hdiag) :
    α (R.realCoroot hdiag hα) = 2 := by
  have h : (hα.choose • R.root hα.choose_spec.choose) (R.realCoroot hdiag hα) = 2 := by
    rw [realCoroot, R.smul_apply_corootAction, R.root_coroot, Matrix.map_apply, hdiag,
      Int.cast_ofNat]
  exact (congrFun (congrArg DFunLike.coe hα.choose_spec.choose_spec.symm)
    (R.realCoroot hdiag hα)).trans h

/-- **The reflection `s_α ∈ R.weylGroup` attached to a real root `α ∈ R.realRoots`** (not defined
for imaginary roots): if `α = w(αᵢ)`, then `s_α = w sᵢ w⁻¹`. -/
noncomputable def realReflection {α : Dual K H}
    (hα : α ∈ R.realRoots hdiag) : R.weylGroup (mapIntCast_diag hdiag) :=
  hα.choose * R.weylSimple (mapIntCast_diag hdiag) hα.choose_spec.choose * hα.choose⁻¹

/-- `s_α` acts on `Dual K H` by the reflection formula `φ ↦ φ - φ(α^∨) • α`. -/
theorem realReflection_smul {α : Dual K H} (hα : α ∈ R.realRoots hdiag) (φ : Dual K H) :
    R.realReflection hdiag hα • φ = φ - φ (R.realCoroot hdiag hα) • α := by
  rw [realReflection, R.conj_weylSimple_smul, realCoroot, hα.choose_spec.choose_spec]

@[simp]
theorem realReflection_smul_self {α : Dual K H} (hα : α ∈ R.realRoots hdiag) :
    R.realReflection hdiag hα • α = -α := by
  rw [R.realReflection_smul hdiag hα α, R.apply_realCoroot_self, two_smul, sub_add_cancel_left]

@[simp]
theorem realReflection_mul_self {α : Dual K H} (hα : α ∈ R.realRoots hdiag) :
    R.realReflection hdiag hα * R.realReflection hdiag hα = 1 := by
  dsimp only [realReflection]
  set w := hα.choose
  set s := R.weylSimple (mapIntCast_diag hdiag) hα.choose_spec.choose
  calc (w * s * w⁻¹) * (w * s * w⁻¹)
      = w * (s * s) * w⁻¹ := by simp [mul_assoc]
    _ = 1 := by simp [s]

end RealRootsBasic

section RealRootsCoxeter

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Every real root is either positive or negative.** -/
theorem mem_posRootCone_or_neg_mem_posRootCone_of_mem_realRoots (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots hdiag) : α ∈ R.posRootCone ∨ -α ∈ R.posRootCone := by
  obtain ⟨w, i, rfl⟩ := hα
  by_cases hd : (R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent w i
  · exact Or.inr ((R.neg_smul_root_mem_posRootCone_iff_isRightDescent hdiag hoff hzero w i).mpr hd)
  · exact Or.inl ((R.smul_root_mem_posRootCone_iff_not_isRightDescent hdiag hoff hzero w i).mpr hd)

/-- If `w₁(αᵢ) = w₂(αⱼ)`, then strong exchange gives `w₁ sᵢ w₁⁻¹ = w₂ sⱼ w₂⁻¹`. -/
private theorem conj_weylSimple_eq_of_smul_root_eq (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {w₁ w₂ : R.weylGroup (mapIntCast_diag hdiag)} {i j : I}
    (hw : w₁ • R.root i = w₂ • R.root j) :
    w₁ * R.weylSimple (mapIntCast_diag hdiag) i * w₁⁻¹ =
      w₂ * R.weylSimple (mapIntCast_diag hdiag) j * w₂⁻¹ := by
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  let u := w₁⁻¹ * w₂
  have huj : u • R.root j = R.root i := by simp [u, mul_smul, ← hw]
  have huinv_i : u⁻¹ • R.root i = R.root j := by rw [← huj, inv_smul_smul]
  have hnd_uj : ¬ cs.IsRightDescent u j :=
    (R.smul_root_mem_posRootCone_iff_not_isRightDescent hdiag hoff hzero u j).mp
      (huj ▸ R.root_mem_posRootCone i)
  have hnd_uinv_i : ¬ cs.IsRightDescent u⁻¹ i :=
    (R.smul_root_mem_posRootCone_iff_not_isRightDescent hdiag hoff hzero u⁻¹ i).mp
      (huinv_i ▸ R.root_mem_posRootCone j)
  have hd_siu_j : cs.IsRightDescent (cs.simple i * u) j := by
    rw [← R.neg_smul_root_mem_posRootCone_iff_isRightDescent hdiag hoff hzero,
      R.weylCoxeterSystem_simple, mul_smul, huj, weylSimple_smul, simpleReflection_root_self,
      neg_neg]
    exact R.root_mem_posRootCone i
  have hlen_usj : cs.length (u * cs.simple j) = cs.length u + 1 :=
    cs.not_isRightDescent_iff.mp hnd_uj
  have hlen_siu : cs.length (cs.simple i * u) = cs.length u + 1 := by
    have h₁ := cs.not_isRightDescent_iff.mp hnd_uinv_i
    have h₂ : (u⁻¹ * cs.simple i)⁻¹ = cs.simple i * u := by simp
    rw [← h₂, cs.length_inv, h₁, cs.length_inv]
  have hlen_both : cs.length (cs.simple i * u * cs.simple j) = cs.length u := by
    have := cs.isRightDescent_iff.mp hd_siu_j; omega
  have hcomm : cs.simple i * u = u * cs.simple j :=
    cs.simple_mul_eq_mul_simple_of_length_eq hlen_both (hlen_siu.trans hlen_usj.symm)
  rw [R.weylCoxeterSystem_simple, R.weylCoxeterSystem_simple] at hcomm
  have hconj_u : u * R.weylSimple (mapIntCast_diag hdiag) j * u⁻¹ =
      R.weylSimple (mapIntCast_diag hdiag) i := by rw [← hcomm, mul_inv_cancel_right]
  rw [← hconj_u]; simp [u, mul_assoc]

/-- If `w₁(αᵢ) = w₂(αⱼ)`, comparing the reflection formulas against `Dual K H` gives
`w₁(hᵢ) = w₂(hⱼ)`. -/
private theorem corootAction_coroot_eq_of_smul_root_eq (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {w₁ w₂ : R.weylGroup (mapIntCast_diag hdiag)} {i j : I}
    (hw : w₁ • R.root i = w₂ • R.root j) :
    R.corootAction (mapIntCast_diag hdiag) w₁ (R.coroot i) =
      R.corootAction (mapIntCast_diag hdiag) w₂ (R.coroot j) := by
  have hconj := R.conj_weylSimple_eq_of_smul_root_eq hdiag hoff hzero hw
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  have hφ : (w₁ * R.weylSimple (mapIntCast_diag hdiag) i * w₁⁻¹) • φ =
      (w₂ * R.weylSimple (mapIntCast_diag hdiag) j * w₂⁻¹) • φ := by rw [hconj]
  rw [R.conj_weylSimple_smul, R.conj_weylSimple_smul, ← hw, sub_right_inj] at hφ
  have hsub : (φ (R.corootAction (mapIntCast_diag hdiag) w₁ (R.coroot i)) -
      φ (R.corootAction (mapIntCast_diag hdiag) w₂ (R.coroot j))) • (w₁ • R.root i) = 0 :=
    (sub_smul _ _ (w₁ • R.root i)).trans (by rw [hφ, sub_self])
  rw [← map_sub] at hsub
  exact (smul_eq_zero.mp hsub).resolve_right (R.ne_zero_of_mem_realRoots hdiag ⟨w₁, i, rfl⟩)

theorem realCoroot_eq_of_smul_root (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots hdiag)
    {w : R.weylGroup (mapIntCast_diag hdiag)} {i : I} (hw : w • R.root i = α) :
    R.realCoroot hdiag hα = R.corootAction (mapIntCast_diag hdiag) w (R.coroot i) :=
  R.corootAction_coroot_eq_of_smul_root_eq hdiag hoff hzero
    (hα.choose_spec.choose_spec.trans hw.symm)

/-- `(w αᵢ)^∨ = w(hᵢ)`, independently of the presentation of the real root. -/
@[simp]
theorem realCoroot_smul_root (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (mapIntCast_diag hdiag)) (i : I)
    (hα : w • R.root i ∈ R.realRoots hdiag := R.smul_root_mem_realRoots hdiag w i) :
    R.realCoroot hdiag hα = R.corootAction (mapIntCast_diag hdiag) w (R.coroot i) :=
  R.realCoroot_eq_of_smul_root hdiag hoff hzero hα rfl

@[simp]
theorem realCoroot_root (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.realCoroot hdiag (R.root_mem_realRoots hdiag i) = R.coroot i := by
  simpa using R.realCoroot_eq_of_smul_root hdiag hoff hzero (R.root_mem_realRoots hdiag i)
    (one_smul _ _)

/-- **Equivariance of real coroots**: `(w • α)^∨ = w(α^∨)`. -/
theorem realCoroot_smul (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (mapIntCast_diag hdiag)) {α : Dual K H} (hα : α ∈ R.realRoots hdiag) :
    R.realCoroot hdiag ((R.smul_mem_realRoots_iff hdiag w).mpr hα) =
      R.corootAction (mapIntCast_diag hdiag) w (R.realCoroot hdiag hα) := by
  obtain ⟨u, i, rfl⟩ := hα
  rw [R.realCoroot_smul_root hdiag hoff hzero u i, ← mul_apply_eq_comp, ← map_mul]
  exact R.realCoroot_eq_of_smul_root hdiag hoff hzero _ (mul_smul w u (R.root i))

theorem realReflection_eq_of_smul_root (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots hdiag)
    {w : R.weylGroup (mapIntCast_diag hdiag)} {i : I} (hw : w • R.root i = α) :
    R.realReflection hdiag hα = w * R.weylSimple (mapIntCast_diag hdiag) i * w⁻¹ :=
  R.conj_weylSimple_eq_of_smul_root_eq hdiag hoff hzero
    (hα.choose_spec.choose_spec.trans hw.symm)

@[simp]
theorem realReflection_smul_root (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (mapIntCast_diag hdiag)) (i : I)
    (hα : w • R.root i ∈ R.realRoots hdiag := R.smul_root_mem_realRoots hdiag w i) :
    R.realReflection hdiag hα = w * R.weylSimple (mapIntCast_diag hdiag) i * w⁻¹ :=
  R.realReflection_eq_of_smul_root hdiag hoff hzero hα rfl

@[simp]
theorem realReflection_root (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.realReflection hdiag (R.root_mem_realRoots hdiag i) =
      R.weylSimple (mapIntCast_diag hdiag) i := by
  simpa using R.realReflection_eq_of_smul_root hdiag hoff hzero (R.root_mem_realRoots hdiag i)
    (one_smul _ _)

/-- Every real reflection is a Coxeter reflection in `R.weylCoxeterSystem`. -/
theorem isReflection_realReflection (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    {α : Dual K H} (hα : α ∈ R.realRoots hdiag) :
    (R.weylCoxeterSystem hdiag hoff hzero).IsReflection (R.realReflection hdiag hα) :=
  ⟨hα.choose, hα.choose_spec.choose, by rw [R.weylCoxeterSystem_simple, realReflection]⟩

end RealRootsCoxeter

/-! ### Rank-one and rank-two Weyl groups (`A₁`, `B₂`, and affine `A₁⁽¹⁾`) -/

section RankOneAndTwo

/-- **Rank-one Weyl group (`|I| = 1`, e.g. type `A₁`)**: the Weyl group has cardinality `2`. -/
theorem card_weylGroup_of_unique {I K H : Type*} [Unique I] [Field K] [CharZero K]
    [AddCommGroup H] [Module K H] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ i, A i i = 2) :
    Nat.card (R.weylGroup hdiag) = 2 := by
  let s := R.weylSimple hdiag default
  have hmem (w : R.weylGroup hdiag) : w = 1 ∨ w = s := by
    induction w using R.weylGroup_induction with
    | one => exact Or.inl rfl
    | simple i => rw [Subsingleton.elim i default]; exact Or.inr rfl
    | mul u v ihu ihv =>
      rcases ihu with rfl | rfl <;> rcases ihv with rfl | rfl <;>
        simp [s, R.weylSimple_mul_self]
  have hf : Function.Bijective (fun b : Bool ↦ if b then s else 1) := by
    refine ⟨fun b₁ b₂ h ↦ ?_, fun w ↦ (hmem w).elim (⟨false, ·.symm⟩) (⟨true, ·.symm⟩)⟩
    cases b₁ <;> cases b₂
    · rfl
    · exact absurd h.symm (R.weylSimple_ne_one hdiag default)
    · exact absurd h (R.weylSimple_ne_one hdiag default)
    · rfl
  rw [← Nat.card_congr (Equiv.ofBijective _ hf)]; simp

/-- **Rank-one minimal realization (`A₁`, `s(ω) = -ω`)**: on the dual of a minimal rank-one
realization over a characteristic-zero field, the unique simple reflection acts by `-id` on every
weight (in particular negating the fundamental weight `ω`). -/
theorem simpleReflection_eq_neg_of_isMinimal {I K H : Type*} [Unique I] [Field K] [CharZero K]
    [AddCommGroup H] [Module K H] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ i, A i i = 2) (hmin : R.IsMinimal)
    (φ : Dual K H) : R.simpleReflection hdiag default φ = -φ := by
  have hspan (h : H) : h = (2⁻¹ * R.root default h) • R.coroot default := by
    let z : H := h - (2⁻¹ * R.root default h) • R.coroot default
    have hz_center : z ∈ R.cartanCenter := by
      rw [R.mem_cartanCenter_iff]; intro i; rw [Subsingleton.elim i default]
      dsimp only [z]
      rw [map_sub, map_smul, R.root_coroot, hdiag default, smul_eq_mul, mul_right_comm,
        inv_mul_cancel₀ two_ne_zero, one_mul, sub_self]
    obtain ⟨c, hc⟩ := (R.mem_corootSpan_iff z).mp
      (R.isMinimal_iff_cartanCenter_le_corootSpan.mp hmin hz_center)
    have hcz : z = c default • R.coroot default := by
      rw [← hc, corootMap_apply, Fintype.sum_unique]
    have hc0 : c default = 0 := by
      have hr := (R.mem_cartanCenter_iff z).mp hz_center default
      rw [hcz, map_smul, R.root_coroot, hdiag default, smul_eq_mul, mul_eq_zero] at hr
      exact hr.resolve_right two_ne_zero
    have hz0 : z = 0 := by rw [hcz, hc0, zero_smul]
    exact sub_eq_zero.mp hz0
  ext h
  rw [R.simpleReflection_apply_apply, hspan h, map_smul, simpleCoreflection_coroot_self,
    smul_neg, map_neg, ← hspan h, LinearMap.neg_apply]

/-- **Type `A₁` check (`CartanMatrix.A 1`)**: the Weyl group has order `2`. -/
theorem card_weylGroup_A_one {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.A 1).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (mapIntCast_diag fun i ↦ congrFun (CartanMatrix.A_diag 1) i)) = 2 :=
  R.card_weylGroup_of_unique _

/-- **Rank-two Weyl groups are dihedral**: for any generalized Cartan matrix on `{i, j}`,
`R.weylGroup` is isomorphic to `DihedralGroup (cartanCoxeterMatrix A i j)` — finite of order
`2 * mᵢⱼ` when `aᵢⱼ aⱼᵢ ≤ 3`, and the infinite dihedral group `DihedralGroup 0` when
`aᵢⱼ aⱼᵢ ≥ 4`. -/
noncomputable def dihedralGroupMulEquivWeyl {I K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hdiag : ∀ k, A k k = 2) (hoff : ∀ k l, k ≠ l → A k l ≤ 0)
    (hzero : ∀ k l, A k l = 0 ↔ A l k = 0) {i j : I} (hpair : ∀ k : I, k = i ∨ k = j) :
    DihedralGroup (cartanCoxeterMatrix A i j) ≃* R.weylGroup (mapIntCast_diag hdiag) := by
  have hrange : ({R.weylSimple (mapIntCast_diag hdiag) i,
      R.weylSimple (mapIntCast_diag hdiag) j} : Set _) =
      Set.range (R.weylSimple (mapIntCast_diag hdiag)) := by
    ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    refine ⟨fun h ↦ h.elim (fun h ↦ ⟨i, h.symm⟩) (fun h ↦ ⟨j, h.symm⟩), fun ⟨k, hk⟩ ↦ ?_⟩
    rcases hpair k with rfl | rfl
    · exact Or.inl hk.symm
    · exact Or.inr hk.symm
  exact TauCeti.dihedralGroupMulEquiv (R.weylSimple_mul_self _ i) (R.weylSimple_mul_self _ j)
    (R.weylSimple_ne_one _ i) (R.weylSimple_ne_one _ j)
    (R.orderOf_weylSimple_mul_weylSimple hdiag hoff hzero i j)
    (by rw [hrange, R.closure_range_weylSimple])

/-- **Type `B₂` Coxeter entry**: `a₀₁ a₁₀ = (-2)(-1) = 2`, so `m₀₁ = 4` (not `3`). -/
@[simp]
theorem cartanCoxeterMatrix_B_two : cartanCoxeterMatrix (CartanMatrix.B 2) 0 1 = 4 := by
  have hprod : CartanMatrix.B 2 0 1 * CartanMatrix.B 2 1 0 = 2 := by
    rw [CartanMatrix.B_two]; decide
  rw [cartanCoxeterMatrix_of_ne_of_le (CartanMatrix.B 2) (by decide) (by omega), hprod,
    coxeterOrder_two]

/-- **Type `B₂` Weyl group**: isomorphic to `DihedralGroup 4`. -/
noncomputable def dihedralGroupFourEquivWeylBTwo {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    DihedralGroup 4 ≃* R.weylGroup (mapIntCast_diag (CartanMatrix.B_diag 2)) :=
  (by rw [cartanCoxeterMatrix_B_two] :
      DihedralGroup 4 ≃* DihedralGroup (cartanCoxeterMatrix (CartanMatrix.B 2) 0 1)).trans <|
    R.dihedralGroupMulEquivWeyl (CartanMatrix.B_diag 2) (CartanMatrix.B_off_diag_nonpos 2)
      (by rw [CartanMatrix.B_two]; simp [Fin.forall_fin_two])
      (i := 0) (j := 1) (fun k ↦ by fin_cases k <;> simp)

/-- **Type `B₂` cardinality check**: `|W(B₂)| = 8`. -/
theorem card_weylGroup_B_two {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (mapIntCast_diag (CartanMatrix.B_diag 2))) = 8 := by
  rw [← Nat.card_congr (R.dihedralGroupFourEquivWeylBTwo).toEquiv, DihedralGroup.nat_card]

/-- **Affine `A₁⁽¹⁾` Coxeter entry**: for `A = !![2, -2; -2, 2]`, `a₀₁ a₁₀ = 4`, so `m₀₁ = 0`
(encoding `∞`). -/
@[simp]
theorem cartanCoxeterMatrix_affine_A_one :
    cartanCoxeterMatrix !![(2 : ℤ), -2; -2, 2] 0 1 = 0 :=
  cartanCoxeterMatrix_of_ne_of_lt !![(2 : ℤ), -2; -2, 2] (by decide) (by decide)

/-- **Affine `A₁⁽¹⁾` Weyl group**: isomorphic to the infinite dihedral group `DihedralGroup 0`. -/
noncomputable def dihedralGroupZeroEquivWeylAffineAOne {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    DihedralGroup 0 ≃*
      R.weylGroup (mapIntCast_diag (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) :=
  (by rw [cartanCoxeterMatrix_affine_A_one] :
      DihedralGroup 0 ≃*
        DihedralGroup (cartanCoxeterMatrix !![(2 : ℤ), -2; -2, 2] 0 1)).trans <|
    R.dihedralGroupMulEquivWeyl (by decide) (by simp [Fin.forall_fin_two])
      (by simp [Fin.forall_fin_two]) (i := 0) (j := 1) (fun k ↦ by fin_cases k <;> simp)

/-- **Affine `A₁⁽¹⁾` infinite-order check**: `s₀ s₁` has infinite order (`orderOf = 0`). -/
theorem orderOf_weylSimple_mul_affine_A_one {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    orderOf (R.weylSimple (mapIntCast_diag (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 0 *
        R.weylSimple (mapIntCast_diag (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 1) = 0 := by
  rw [R.orderOf_weylSimple_mul_weylSimple (by decide) (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two]) 0 1, cartanCoxeterMatrix_affine_A_one]

/-- The Weyl group of affine `A₁⁽¹⁾` is infinite. -/
instance instInfiniteWeylGroupAffineAOne {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    Infinite (R.weylGroup (mapIntCast_diag (A := !![(2 : ℤ), -2; -2, 2]) (by decide))) :=
  Infinite.of_injective _ R.dihedralGroupZeroEquivWeylAffineAOne.injective

/-- **Affine `A₁⁽¹⁾` translation check**: `(s₀ s₁)(α₁) = α₁ - 2 • (α₀ + α₁)` (`= α₁ - 2δ` for the
null root `δ = α₀ + α₁`). -/
theorem weylSimple_zero_mul_one_root_one_affine_A_one {K H : Type*} [Field K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    (R.weylSimple (mapIntCast_diag (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 0 *
        R.weylSimple (mapIntCast_diag (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 1) • R.root 1 =
      R.root 1 - (2 : K) • (R.root 0 + R.root 1) := by
  rw [mul_smul, weylSimple_smul, weylSimple_smul, simpleReflection_root_self, map_neg,
    simpleReflection_root]
  have h01 : ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) 0 1 = -2 := by simp
  rw [h01]; module

end RankOneAndTwo

end TauCeti.CartanRealization
