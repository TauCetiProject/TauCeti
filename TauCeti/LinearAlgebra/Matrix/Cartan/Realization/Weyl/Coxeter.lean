/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Length
public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Matrix
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl.Basic
import TauCeti.GroupTheory.Coxeter.Basic
import TauCeti.GroupTheory.Coxeter.Dihedral
import TauCeti.GroupTheory.Coxeter.Geometric.Basic
import TauCeti.GroupTheory.Coxeter.Length

/-!
# The Weyl group of a Kac–Moody realization is a Coxeter group

Let `A : Matrix I I ℤ` be a generalized Cartan matrix (`A i i = 2`, `A i j ≤ 0` for `i ≠ j`, and
`A i j = 0 ↔ A j i = 0`) and let `R : CartanRealization (A.map Int.cast) H` be a realization of
`A` over a field `K`. No symmetrizability, nonsingularity, finiteness of `I`, or finite
dimensionality of `H` is assumed.

The simple reflections satisfy the Coxeter relations of
`TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A` over any field
(`TauCeti.CartanRealization.pow_simpleReflection_mul_simpleReflection_eq_one`), so the homomorphism
`TauCeti.CartanRealization.coxeterHom` from the Coxeter group corestricts to a surjection onto the
Weyl group. Using Mathlib's Chebyshev formulas for powers of a product of two reflections
(`Module.reflection_mul_reflection_pow_apply_self`), this file proves Kac's **Lemma 3.11** and
**Proposition 3.13** over any field of characteristic zero:

* `ℓ(w sᵢ) < ℓ(w)` if and only if `-w(αᵢ) ∈ Q₊`, and `ℓ(w sᵢ) = ℓ(w) + 1` if and only if
  `w(αᵢ) ∈ Q₊`;
* the surjection `(coxeterMatrixOfGeneralizedCartanMatrix A).Group →* R.weylGroup _` is an
  isomorphism of groups, equipping `R.weylGroup _` with a `CoxeterSystem` whose Coxeter length
  agrees with `R.weylLength _`;
* the action of `R.weylGroup _` on the root lattice `Q` is faithful even when `A` is singular or
  `H` has central directions, and any two characteristic-zero realizations of `A` have canonically
  isomorphic Weyl groups matching simple reflections index-by-index.

## Main definitions

* `TauCeti.CartanRealization.weylCoxeterHom`: the corestriction of
  `TauCeti.CartanRealization.coxeterHom` to the Weyl group, over any field.
* `TauCeti.CartanRealization.weylCoxeterEquiv`,
  `TauCeti.CartanRealization.weylCoxeterSystem`: the Coxeter group isomorphism and `CoxeterSystem`
  on `R.weylGroup _` in characteristic zero.
* `TauCeti.CartanRealization.weylGroupEquiv`: the canonical isomorphism between the Weyl groups of
  any two characteristic-zero realizations of `A`.

## Main results

* `TauCeti.CartanRealization.weylCoxeterHom_surjective`,
  `TauCeti.CartanRealization.weylCoxeterHom_injective`: the Coxeter group maps onto the Weyl group
  over any field, and injectively in characteristic zero.
* `TauCeti.CartanRealization.weylLength_mul_weylSimple_lt_iff`,
  `TauCeti.CartanRealization.weylLength_mul_weylSimple_eq_add_one_iff`: Kac's Lemma 3.11.
* `TauCeti.CartanRealization.weylCoxeterSystem_length`: Coxeter length equals `R.weylLength _`.
* `TauCeti.CartanRealization.rootLatticeAction_injective`: `W` acts faithfully on `Q`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §§3.7–3.13 (Lemma 3.11 and Proposition 3.13).
-/

public section

open Module Polynomial.Chebyshev

namespace TauCeti

namespace CartanRealization

/-! ### The Coxeter group onto the Weyl group and rank-two positivity over an arbitrary field -/

/-- Closed-form Chebyshev evaluation of `((if Even m then 1 else sⱼ) * (sᵢ * sⱼ) ^ (m / 2)) αᵢ`. -/
private theorem alternating_simpleReflection_apply_root {I K H : Type*} [Field K] [AddCommGroup H]
    [Module K H] {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hdiag : ∀ i, A i i = 2) (i j : I) (m : ℕ) :
    let hd := diag_map_intCast (K := K) hdiag
    let c := A i j * A j i
    let aZ : ℤ := (S ℤ (m / 2 : ℕ)).eval (c - 2) + (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
    let bS : ℤ := if Even m then (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
      else (S ℤ (m / 2 : ℕ)).eval (c - 2)
    (((if Even m then 1 else R.simpleReflection hd j) *
        (R.simpleReflection hd i * R.simpleReflection hd j) ^ (m / 2)) (R.root i)) =
      (aZ : K) • R.root i + ((bS * -A j i : ℤ) : K) • R.root j := by
  intro hd c aZ bS
  have hfi : (Dual.eval K H (R.coroot i)) (R.root i) = 2 := by simp [hdiag i]
  have hfj : (Dual.eval K H (R.coroot j)) (R.root j) = 2 := by simp [hdiag j]
  have htK : ((c - 2 : ℤ) : K) =
      (Dual.eval K H (R.coroot i)) (R.root j) *
        (Dual.eval K H (R.coroot j)) (R.root i) - 2 := by
    simp [c, R.root_coroot]
  have hS1 : (S K (m / 2 : ℕ)).eval ((c - 2 : ℤ) : K) =
      (((S ℤ (m / 2 : ℕ)).eval (c - 2) : ℤ) : K) :=
    (Polynomial.Chebyshev.algebraMap_eval_S (c - 2) (m / 2 : ℕ)).symm
  have hS2 : (S K (((m / 2 : ℕ) : ℤ) - 1)).eval ((c - 2 : ℤ) : K) =
      (((S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2) : ℤ) : K) :=
    (Polynomial.Chebyshev.algebraMap_eval_S (c - 2) (((m / 2 : ℕ) : ℤ) - 1)).symm
  have hg : -(Dual.eval K H (R.coroot j) (R.root i)) = ((-A j i : ℤ) : K) := by
    simp [R.root_coroot]
  rw [R.simpleReflection_eq_reflection hd i hfi, R.simpleReflection_eq_reflection hd j hfj]
  by_cases hm_even : Even m
  · simp only [hm_even, ↓reduceIte, one_mul, bS]
    rw [Module.reflection_mul_reflection_pow_apply_self hfi hfj (m / 2) ((c - 2 : ℤ) : K) htK,
      hS1, hS2, hg]
    simp only [aZ, Int.cast_add, Int.cast_mul, Int.cast_neg]
  · simp only [hm_even, ↓reduceIte, bS]
    rw [Module.reflection_mul_reflection_mul_reflection_pow_apply_self hfi hfj (m / 2)
      ((c - 2 : ℤ) : K) htK, hS1, hS2, hg]
    simp only [aZ, Int.cast_add, Int.cast_mul, Int.cast_neg]

section ArbitraryField

variable {I K H : Type*} [DecidableEq I] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- The canonical group homomorphism from the Coxeter group of
`TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A` onto `R.weylGroup`, sending each generator to
`R.weylSimple _ i`: the corestriction of `TauCeti.CartanRealization.coxeterHom` to its range. -/
noncomputable def weylCoxeterHom (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    (coxeterMatrixOfGeneralizedCartanMatrix A).Group →* R.weylGroup (diag_map_intCast hdiag) :=
  (R.coxeterHom (diag_map_intCast hdiag) hzero).codRestrict _ fun g ↦
    R.range_coxeterHom (diag_map_intCast hdiag) hzero ▸ MonoidHom.mem_range.mpr ⟨g, rfl⟩

@[simp]
theorem coe_weylCoxeterHom (hdiag : ∀ i, A i i = 2) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (g : (coxeterMatrixOfGeneralizedCartanMatrix A).Group) :
    (R.weylCoxeterHom hdiag hzero g : Dual K H ≃ₗ[K] Dual K H) =
      R.coxeterHom (diag_map_intCast hdiag) hzero g := (rfl)

@[simp]
theorem weylCoxeterHom_simple (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.weylCoxeterHom hdiag hzero ((coxeterMatrixOfGeneralizedCartanMatrix A).simple i) =
      R.weylSimple (diag_map_intCast hdiag) i :=
  Subtype.ext <| by rw [coe_weylCoxeterHom, coxeterHom_simple, coe_weylSimple]

@[simp]
theorem weylCoxeterHom_wordProd (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (l : List I) :
    R.weylCoxeterHom hdiag hzero
        ((coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.wordProd l) =
      (l.map (R.weylSimple (diag_map_intCast hdiag))).prod := by
  rw [CoxeterSystem.wordProd, map_list_prod, List.map_map]
  exact congrArg List.prod (congrArg (fun f ↦ l.map f)
    (funext (R.weylCoxeterHom_simple hdiag hzero)))

/-- `weylCoxeterHom` is surjective onto `R.weylGroup`. -/
theorem weylCoxeterHom_surjective (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Surjective (R.weylCoxeterHom hdiag hzero) := fun w ↦ by
  obtain ⟨l, rfl⟩ := R.exists_word_prod_eq (diag_map_intCast hdiag) w
  exact ⟨(coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.wordProd l,
    R.weylCoxeterHom_wordProd hdiag hzero l⟩

/-- In a rank-two standard parabolic subgroup `⟨sᵢ, sⱼ⟩`, an element `v` for which `i` is not a
right descent sends `αᵢ` to a natural combination `a • αᵢ + b • αⱼ`. -/
private theorem exists_apply_root_eq_nsmul_of_mem_parabolic_pair
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) {i j : I} (hij : i ≠ j)
    {v : (coxeterMatrixOfGeneralizedCartanMatrix A).Group}
    (hv : v ∈ (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.parabolic {i, j})
    (hdesc : ¬(coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.IsRightDescent v i) :
    ∃ a b : ℕ,
      ((R.weylCoxeterHom hdiag hzero v :
          Dual K H ≃ₗ[K] Dual K H) (R.root i)) = a • R.root i + b • R.root j := by
  let cs₀ := (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem
  let m := cs₀.length v
  let hd := diag_map_intCast (K := K) hdiag
  let c := A i j * A j i
  have hnonneg : 0 ≤ c := mul_nonneg_of_nonpos_of_nonpos (hoff i j hij) (hoff j i hij.symm)
  have hv_eq : cs₀.wordProd (CoxeterSystem.alternatingWord i j m) = v :=
    cs₀.wordProd_alternatingWord_eq_of_mem_parabolic_pair_of_not_isRightDescent hv hdesc
  have hm_lt : c ≤ 3 → m < coxeterOrder c := fun hle ↦ by
    have hM : coxeterMatrixOfGeneralizedCartanMatrix A i j = coxeterOrder c :=
      coxeterMatrixOfGeneralizedCartanMatrix_apply_of_lt_four A hij
        (lt_of_le_of_lt hle (by norm_num))
    have hne0 : coxeterMatrixOfGeneralizedCartanMatrix A i j ≠ 0 := by
      rw [Ne, coxeterMatrixOfGeneralizedCartanMatrix_apply_eq_zero_iff A hij hnonneg]
      omega
    rw [← hM]
    exact cs₀.length_lt_of_mem_parabolic_pair_of_not_isRightDescent hne0 hv hdesc
  let aZ : ℤ := (S ℤ (m / 2 : ℕ)).eval (c - 2) + (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
  let bS : ℤ := if Even m then (S ℤ (((m / 2 : ℕ) : ℤ) - 1)).eval (c - 2)
    else (S ℤ (m / 2 : ℕ)).eval (c - 2)
  have ha : 0 ≤ aZ := chebyshevS_add_sub_one_eval_sub_two_nonneg (c := c) fun hle ↦ by
    have := hm_lt hle
    omega
  have hb : 0 ≤ bS := by
    dsimp only [bS]
    split_ifs with he
    · exact chebyshevS_sub_one_eval_sub_two_nonneg (c := c) fun hle ↦ by
        have := hm_lt hle
        omega
    · exact chebyshevS_eval_sub_two_nonneg (c := c) fun hle ↦ by
        have := hm_lt hle
        rw [Nat.even_iff] at he
        omega
  have hbZ : 0 ≤ bS * -A j i := mul_nonneg hb (neg_nonneg.mpr (hoff j i hij.symm))
  have ha_eq : (aZ.toNat : ℤ) = aZ := Int.toNat_of_nonneg ha
  have hb_eq : ((bS * -A j i).toNat : ℤ) = bS * -A j i := Int.toNat_of_nonneg hbZ
  have hval : (R.weylCoxeterHom hdiag hzero v : Dual K H ≃ₗ[K] Dual K H) =
      (if Even m then 1 else R.simpleReflection hd j) *
        (R.simpleReflection hd i * R.simpleReflection hd j) ^ (m / 2) := by
    have hprod : ((CoxeterSystem.alternatingWord i j m).map (R.weylSimple hd)).prod =
        R.weylCoxeterHom hdiag hzero v := by
      rw [← R.weylCoxeterHom_wordProd hdiag hzero, hv_eq]
    rw [← (R.prod_map_weylSimple_eq_iff hd _ _).mp hprod,
      TauCeti.prod_map_alternatingWord (R.simpleReflection hd) i j m]
  refine ⟨aZ.toNat, (bS * -A j i).toNat, ?_⟩
  rw [hval, R.alternating_simpleReflection_apply_root hdiag i j m,
    Int.cast_smul_eq_zsmul K aZ (R.root i), Int.cast_smul_eq_zsmul K (bS * -A j i) (R.root j),
    ← natCast_zsmul, ← natCast_zsmul, ha_eq, hb_eq]

/-- Key induction of Kac's Lemma 3.11: if `i` is not a right descent of `w` in the presented
Coxeter group, then `w(αᵢ) ∈ Q₊` (over any field `K`!). -/
private theorem apply_root_mem_posRootCone_of_not_isRightDescent
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) {w : (coxeterMatrixOfGeneralizedCartanMatrix A).Group}
    {i : I}
    (hwi : ¬(coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.IsRightDescent w i) :
    ((R.weylCoxeterHom hdiag hzero w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) ∈
      R.posRootCone := by
  let cs₀ := (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem
  induction hlen : cs₀.length w using Nat.strong_induction_on generalizing w i with
  | _ n ih =>
    rcases eq_or_ne w 1 with rfl | hw1
    · simpa using R.root_mem_posRootCone i
    obtain ⟨j, hwj⟩ := cs₀.exists_rightDescent_of_ne_one hw1
    have hij : i ≠ j := fun h ↦ hwi (h ▸ hwj)
    obtain ⟨p, ⟨hu, hv, hmul⟩, -⟩ := cs₀.existsUnique_isMinimalCosetRep_mul {i, j} w
    rcases p with ⟨u, v⟩
    dsimp only at hu hv hmul; subst hmul
    have hv1 : v ≠ 1 := fun hv0 ↦ by
      rw [hv0, mul_one] at hwj
      exact cs₀.isMinimalCosetRep_iff.mp hu j (by simp) hwj
    have hv_pos : 0 < cs₀.length v := Nat.pos_of_ne_zero (mt cs₀.length_eq_zero_iff.mp hv1)
    have hadd := cs₀.length_mul_of_isMinimalCosetRep hu hv
    have hvi : ¬cs₀.IsRightDescent v i := fun hd ↦ hwi <| by
      rw [CoxeterSystem.IsRightDescent, mul_assoc,
        cs₀.length_mul_of_isMinimalCosetRep hu
          (mul_mem hv (cs₀.simple_mem_parabolic (by simp))), hadd]
      exact Nat.add_lt_add_left hd _
    obtain ⟨a, b, hab⟩ :=
      R.exists_apply_root_eq_nsmul_of_mem_parabolic_pair hdiag hoff hzero hij hv hvi
    have hu_cone {k : I} (hk : k ∈ ({i, j} : Set I)) :
        ((R.weylCoxeterHom hdiag hzero u : Dual K H ≃ₗ[K] Dual K H) (R.root k)) ∈
          R.posRootCone :=
      ih (cs₀.length u) (by omega) (cs₀.isMinimalCosetRep_iff.mp hu k hk) rfl
    rw [map_mul, Subgroup.coe_mul, mul_apply_eq_comp, hab, map_add, map_nsmul, map_nsmul]
    exact add_mem (Submodule.smul_mem _ a (hu_cone (by simp)))
      (Submodule.smul_mem _ b (hu_cone (by simp)))

end ArbitraryField

/-! ### Kac's Lemma 3.11 and the Coxeter presentation in characteristic zero -/

section CoxeterPresentation

variable {I K H : Type*} [DecidableEq I] [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

private theorem isRightDescent_toCoxeterSystem_iff
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : (coxeterMatrixOfGeneralizedCartanMatrix A).Group) (i : I) :
    (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.IsRightDescent w i ↔
      -((R.weylCoxeterHom hdiag hzero w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) ∈
        R.posRootCone := by
  let cs₀ := (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem
  have hne : ((R.weylCoxeterHom hdiag hzero w :
      Dual K H ≃ₗ[K] Dual K H) (R.root i)) ≠ 0 :=
    (map_ne_zero_iff _ (LinearEquiv.injective _)).mpr (R.root_linearIndependent.ne_zero i)
  refine ⟨fun hd ↦ ?_, fun hneg ↦ ?_⟩
  · have hnd : ¬cs₀.IsRightDescent (w * cs₀.simple i) i :=
      cs₀.isRightDescent_iff_not_isRightDescent_mul.mp hd
    have hpos := R.apply_root_mem_posRootCone_of_not_isRightDescent hdiag hoff hzero hnd
    dsimp only [cs₀] at hpos
    rw [CoxeterMatrix.toCoxeterSystem_simple, map_mul, R.weylCoxeterHom_simple, Subgroup.coe_mul,
      mul_apply_eq_comp, coe_weylSimple, simpleReflection_root_self, map_neg] at hpos
    exact hpos
  · by_contra hnd
    have hpos := R.apply_root_mem_posRootCone_of_not_isRightDescent hdiag hoff hzero hnd
    exact hne (R.isPointed_posRootCone _ hpos hneg)

/-- `weylCoxeterHom` is injective over any field of characteristic zero. -/
theorem weylCoxeterHom_injective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Injective (R.weylCoxeterHom hdiag hzero) := by
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦ ?_
  by_contra hw1
  obtain ⟨i, hd⟩ :=
    (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.exists_rightDescent_of_ne_one hw1
  have hneg := (R.isRightDescent_toCoxeterSystem_iff hdiag hoff hzero w i).mp hd
  rw [hw, Subgroup.coe_one, one_apply_eq_self] at hneg
  exact R.root_linearIndependent.ne_zero i
    (R.isPointed_posRootCone _ (R.root_mem_posRootCone i) hneg)

/-- **Kac's Proposition 3.13 (group isomorphism form).** The presented Coxeter group of
`TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A` maps isomorphically onto the Weyl group
`R.weylGroup _`. -/
noncomputable def weylCoxeterEquiv (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    (coxeterMatrixOfGeneralizedCartanMatrix A).Group ≃* R.weylGroup (diag_map_intCast hdiag) :=
  MulEquiv.ofBijective (R.weylCoxeterHom hdiag hzero)
    ⟨R.weylCoxeterHom_injective hdiag hoff hzero, R.weylCoxeterHom_surjective hdiag hzero⟩

@[simp]
theorem weylCoxeterEquiv_simple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.weylCoxeterEquiv hdiag hoff hzero ((coxeterMatrixOfGeneralizedCartanMatrix A).simple i) =
      R.weylSimple (diag_map_intCast hdiag) i :=
  R.weylCoxeterHom_simple hdiag hzero i

@[simp]
theorem weylCoxeterEquiv_symm_weylSimple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    (R.weylCoxeterEquiv hdiag hoff hzero).symm (R.weylSimple (diag_map_intCast hdiag) i) =
      (coxeterMatrixOfGeneralizedCartanMatrix A).simple i :=
  (R.weylCoxeterEquiv hdiag hoff hzero).symm_apply_eq.mpr
    (R.weylCoxeterEquiv_simple hdiag hoff hzero i).symm

/-- **Kac's Proposition 3.13 (`CoxeterSystem` form).** The Weyl group of a realization of a
generalized Cartan matrix over a characteristic-zero field forms a `CoxeterSystem` with Coxeter
matrix `TauCeti.coxeterMatrixOfGeneralizedCartanMatrix A` and simple reflections
`R.weylSimple _`. -/
noncomputable def weylCoxeterSystem (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    CoxeterSystem (coxeterMatrixOfGeneralizedCartanMatrix A)
      (R.weylGroup (diag_map_intCast hdiag)) :=
  (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.map
    (R.weylCoxeterEquiv hdiag hoff hzero)

@[simp]
theorem weylCoxeterSystem_simple (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    (R.weylCoxeterSystem hdiag hoff hzero).simple i =
      R.weylSimple (diag_map_intCast hdiag) i :=
  R.weylCoxeterEquiv_simple hdiag hoff hzero i

@[simp]
theorem weylCoxeterSystem_wordProd (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (l : List I) :
    (R.weylCoxeterSystem hdiag hoff hzero).wordProd l =
      (l.map (R.weylSimple (diag_map_intCast hdiag))).prod := by
  rw [weylCoxeterSystem, CoxeterSystem.wordProd_map]
  exact R.weylCoxeterHom_wordProd hdiag hzero l

/-- The Coxeter length of `R.weylCoxeterSystem` agrees with the generator word length
`R.weylLength`. -/
@[simp]
theorem weylCoxeterSystem_length (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) :
    (R.weylCoxeterSystem hdiag hoff hzero).length w =
      R.weylLength (diag_map_intCast hdiag) w := by
  let cs := R.weylCoxeterSystem hdiag hoff hzero
  refine le_antisymm ?_ ?_
  · obtain ⟨l, hl, hprod⟩ := R.exists_length_eq_weylLength (diag_map_intCast hdiag) w
    rw [← hl, ← hprod, ← R.weylCoxeterSystem_wordProd hdiag hoff hzero l]
    exact cs.length_wordProd_le l
  · obtain ⟨ω, hred, rfl⟩ := cs.exists_isReduced w
    rw [hred.eq]
    exact R.weylLength_le_of_prod_eq (diag_map_intCast hdiag)
      (R.weylCoxeterSystem_wordProd hdiag hoff hzero ω).symm

/-- **Kac's Lemma 3.11 (right-descent form).** Index `i` is a right descent of `w` if and only if
`-w(αᵢ) ∈ Q₊`. -/
theorem isRightDescent_weylCoxeterSystem_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I) :
    (R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent w i ↔
      -((w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) ∈ R.posRootCone := by
  let e := R.weylCoxeterEquiv hdiag hoff hzero
  obtain ⟨u, rfl⟩ : ∃ u, e u = w := ⟨e.symm w, e.apply_symm_apply w⟩
  have hdesc : (R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent (e u) i ↔
      (coxeterMatrixOfGeneralizedCartanMatrix A).toCoxeterSystem.IsRightDescent u i := by
    rw [CoxeterSystem.IsRightDescent, CoxeterSystem.IsRightDescent,
      CoxeterMatrix.toCoxeterSystem_simple, R.weylCoxeterSystem_simple,
      ← R.weylCoxeterEquiv_simple hdiag hoff hzero, ← map_mul, weylCoxeterSystem,
      CoxeterSystem.length_map, CoxeterSystem.length_map]
  exact hdesc.trans (R.isRightDescent_toCoxeterSystem_iff hdiag hoff hzero u i)

/-- **Kac's Lemma 3.11 (right-ascent form).** Index `i` is not a right descent of `w` if and only
if `w(αᵢ) ∈ Q₊`. -/
theorem not_isRightDescent_weylCoxeterSystem_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I) :
    ¬(R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent w i ↔
      (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.posRootCone := by
  rw [(R.weylCoxeterSystem hdiag hoff hzero).isRightDescent_iff_not_isRightDescent_mul,
    not_not, R.isRightDescent_weylCoxeterSystem_iff, R.weylCoxeterSystem_simple]
  simp [mul_apply_eq_comp]

end CoxeterPresentation

/-! ### `[DecidableEq I]`-free consequences and realization independence -/

section Consequences

variable {I K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Kac's Lemma 3.11 (`weylLength` descent form)**: `ℓ(w sᵢ) < ℓ(w) ↔ -w(αᵢ) ∈ Q₊`. -/
theorem weylLength_mul_weylSimple_lt_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I) :
    R.weylLength (diag_map_intCast hdiag) (w * R.weylSimple (diag_map_intCast hdiag) i) <
        R.weylLength (diag_map_intCast hdiag) w ↔
      -((w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) ∈ R.posRootCone := by
  classical
  rw [← R.weylCoxeterSystem_length hdiag hoff hzero, ← R.weylCoxeterSystem_length hdiag hoff hzero,
    ← R.weylCoxeterSystem_simple hdiag hoff hzero]
  exact R.isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero w i

/-- **Kac's Lemma 3.11 (`weylLength` ascent form)**: `ℓ(w sᵢ) = ℓ(w) + 1 ↔ w(αᵢ) ∈ Q₊`. -/
theorem weylLength_mul_weylSimple_eq_add_one_iff (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I) :
    R.weylLength (diag_map_intCast hdiag) (w * R.weylSimple (diag_map_intCast hdiag) i) =
        R.weylLength (diag_map_intCast hdiag) w + 1 ↔
      (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.posRootCone := by
  classical
  rw [← R.weylCoxeterSystem_length hdiag hoff hzero, ← R.weylCoxeterSystem_length hdiag hoff hzero,
    ← R.weylCoxeterSystem_simple hdiag hoff hzero,
    ← (R.weylCoxeterSystem hdiag hoff hzero).not_isRightDescent_iff]
  exact R.not_isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero w i

/-- **Sign dichotomy of `W`-translates of simple roots**: for every `w ∈ W` and `i : I`, either
`w(αᵢ) ∈ Q₊` or `-w(αᵢ) ∈ Q₊`. -/
theorem apply_root_mem_posRootCone_or_neg_mem_posRootCone (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0)
    (w : R.weylGroup (diag_map_intCast hdiag)) (i : I) :
    (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) ∈ R.posRootCone ∨
      -((w : Dual K H ≃ₗ[K] Dual K H) (R.root i)) ∈ R.posRootCone := by
  classical
  by_cases hd : (R.weylCoxeterSystem hdiag hoff hzero).IsRightDescent w i
  · exact Or.inr ((R.isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero w i).mp hd)
  · exact Or.inl ((R.not_isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero w i).mp hd)

/-- **The action of the Weyl group on the root lattice `Q` is faithful**, even when `A` is
singular or `H` has central directions. -/
theorem rootLatticeAction_injective (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    Function.Injective (R.rootLatticeAction (diag_map_intCast hdiag)) := by
  classical
  refine (injective_iff_map_eq_one _).mpr fun w hw ↦ ?_
  by_contra hw1
  obtain ⟨i, hd⟩ :=
    (R.weylCoxeterSystem hdiag hoff hzero).exists_rightDescent_of_ne_one hw1
  have hneg := (R.isRightDescent_weylCoxeterSystem_iff hdiag hoff hzero w i).mp hd
  have hfix : (w : Dual K H ≃ₗ[K] Dual K H) (R.root i) = R.root i := by
    have hi := congrArg Subtype.val congr($(hw) ⟨R.root i, R.root_mem_rootLattice i⟩)
    simpa using hi
  rw [hfix] at hneg
  exact R.root_linearIndependent.ne_zero i
    (R.isPointed_posRootCone _ (R.root_mem_posRootCone i) hneg)

/-- **Realization independence of the Weyl group.** Any two realizations of the same generalized
Cartan matrix `A` over fields of characteristic zero (even of different dimensions or over
different scalar fields) have canonically isomorphic Weyl groups matching simple reflections
index-by-index. -/
noncomputable def weylGroupEquiv {K' H' : Type*} [Field K'] [CharZero K'] [AddCommGroup H']
    [Module K' H'] (R' : CartanRealization (A.map (Int.cast : ℤ → K')) H')
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    R.weylGroup (diag_map_intCast hdiag) ≃* R'.weylGroup (diag_map_intCast hdiag) := by
  classical
  exact (R.weylCoxeterEquiv hdiag hoff hzero).symm.trans (R'.weylCoxeterEquiv hdiag hoff hzero)

@[simp]
theorem weylGroupEquiv_weylSimple {K' H' : Type*} [Field K'] [CharZero K'] [AddCommGroup H']
    [Module K' H'] (R' : CartanRealization (A.map (Int.cast : ℤ → K')) H')
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i : I) :
    R.weylGroupEquiv R' hdiag hoff hzero (R.weylSimple (diag_map_intCast hdiag) i) =
      R'.weylSimple (diag_map_intCast hdiag) i := by
  simp [weylGroupEquiv]

@[simp]
theorem weylGroupEquiv_self (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    R.weylGroupEquiv R hdiag hoff hzero = MulEquiv.refl _ :=
  MulEquiv.toMonoidHom_injective <| R.weylGroup_hom_ext (diag_map_intCast hdiag) fun i ↦ by
    simp

@[simp]
theorem weylGroupEquiv_symm {K' H' : Type*} [Field K'] [CharZero K'] [AddCommGroup H']
    [Module K' H'] (R' : CartanRealization (A.map (Int.cast : ℤ → K')) H')
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    (R.weylGroupEquiv R' hdiag hoff hzero).symm = R'.weylGroupEquiv R hdiag hoff hzero :=
  MulEquiv.toMonoidHom_injective <| R'.weylGroup_hom_ext (diag_map_intCast hdiag) fun i ↦ by
    simp [MulEquiv.symm_apply_eq]

@[simp]
theorem weylGroupEquiv_trans {K' H' K'' H'' : Type*} [Field K'] [CharZero K'] [AddCommGroup H']
    [Module K' H'] [Field K''] [CharZero K''] [AddCommGroup H''] [Module K'' H'']
    (R' : CartanRealization (A.map (Int.cast : ℤ → K')) H')
    (R'' : CartanRealization (A.map (Int.cast : ℤ → K'')) H'')
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    (R.weylGroupEquiv R' hdiag hoff hzero).trans (R'.weylGroupEquiv R'' hdiag hoff hzero) =
      R.weylGroupEquiv R'' hdiag hoff hzero :=
  MulEquiv.toMonoidHom_injective <| R.weylGroup_hom_ext (diag_map_intCast hdiag) fun i ↦ by
    simp

theorem weylGroupEquiv_map {H' : Type*} [AddCommGroup H'] [Module K H'] (e : H ≃ₗ[K] H')
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    R.weylGroupEquiv (R.map e) hdiag hoff hzero =
      R.mapWeylGroupEquiv (diag_map_intCast hdiag) e :=
  MulEquiv.toMonoidHom_injective <| R.weylGroup_hom_ext (diag_map_intCast hdiag) fun i ↦ by
    simp

theorem weylGroupEquiv_restrict (M : Submodule K H) (hc : R.corootSpan ≤ M)
    (hs : M ⊔ R.cartanCenter = ⊤) (hdiag : ∀ i, A i i = 2)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    R.weylGroupEquiv (R.restrict M hc hs) hdiag hoff hzero =
      R.restrictWeylGroupEquiv (diag_map_intCast hdiag) M hc hs :=
  MulEquiv.toMonoidHom_injective <| R.weylGroup_hom_ext (diag_map_intCast hdiag) fun i ↦ by
    simp

@[simp]
theorem weylLength_weylGroupEquiv {K' H' : Type*} [Field K'] [CharZero K'] [AddCommGroup H']
    [Module K' H'] (R' : CartanRealization (A.map (Int.cast : ℤ → K')) H')
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (w : R.weylGroup (diag_map_intCast hdiag)) :
    R'.weylLength (diag_map_intCast hdiag) (R.weylGroupEquiv R' hdiag hoff hzero w) =
      R.weylLength (diag_map_intCast hdiag) w :=
  R.weylLength_equiv (diag_map_intCast hdiag) (diag_map_intCast hdiag)
    (R.weylGroupEquiv R' hdiag hoff hzero) (R.weylGroupEquiv_weylSimple R' hdiag hoff hzero) w

end Consequences

/-- When the index type, scalar field, and ambient space lie in a common universe, the Weyl group
carries an `IsCoxeterGroup` proof. -/
theorem isCoxeterGroup_weylGroup.{u} {I K H : Type u} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) :
    IsCoxeterGroup (R.weylGroup (diag_map_intCast hdiag)) := by
  classical
  exact ⟨I, (coxeterMatrixOfGeneralizedCartanMatrix A), ⟨R.weylCoxeterSystem hdiag hoff hzero⟩⟩

/-! ### Rank-one Weyl groups and concrete checks in type `A₁` and in empty rank -/

section RankOne

/-- **Rank-one element dichotomy (`|I| = 1`)**: every element of the Weyl group of a rank-one
realization is either `1` or the unique simple reflection `R.weylSimple hdiag default`. -/
theorem eq_one_or_weylSimple_of_unique {I K H : Type*} [Unique I] [Field K]
    [AddCommGroup H] [Module K H] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ i, A i i = 2) (w : R.weylGroup hdiag) :
    w = 1 ∨ w = R.weylSimple hdiag default := by
  refine R.weylGroup_induction hdiag (P := fun w ↦ w = 1 ∨ w = R.weylSimple hdiag default)
    (Or.inl rfl)
    (fun i ↦ Or.inr (congrArg (R.weylSimple hdiag) (Subsingleton.elim i default))) ?_ w
  rintro u v (rfl | rfl) (rfl | rfl) <;> simp

/-- **Rank-one Weyl group (`|I| = 1`, e.g. type `A₁`)**: over any field, the Weyl group has
cardinality `2`. -/
theorem card_weylGroup_of_unique {I K H : Type*} [Unique I] [Field K]
    [AddCommGroup H] [Module K H] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ i, A i i = 2) :
    Nat.card (R.weylGroup hdiag) = 2 := by
  let s := R.weylSimple hdiag default
  have hf : Function.Bijective (fun b : Bool ↦ if b then s else 1) := by
    refine ⟨fun b₁ b₂ h ↦ ?_,
      fun w ↦ (R.eq_one_or_weylSimple_of_unique hdiag w).elim (⟨false, ·.symm⟩) (⟨true, ·.symm⟩)⟩
    cases b₁ <;> cases b₂
    · rfl
    · exact absurd h.symm (R.weylSimple_ne_one hdiag default)
    · exact absurd h (R.weylSimple_ne_one hdiag default)
    · rfl
  rw [← Nat.card_congr (Equiv.ofBijective _ hf)]
  simp

/-- **Rank-one minimal realization (`A₁`, `s(ω) = -ω`)**: on the dual of a minimal rank-one
realization over a field of characteristic not `2`, the unique simple reflection acts by `-id` on
every weight (in particular negating the fundamental weight `ω`). -/
theorem simpleReflection_eq_neg_of_isMinimal {I K H : Type*} [Unique I] [Field K] [NeZero (2 : K)]
    [AddCommGroup H] [Module K H] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ i, A i i = 2) (hmin : R.IsMinimal)
    (φ : Dual K H) : R.simpleReflection hdiag default φ = -φ := by
  classical
  have hunit : IsUnit A := ⟨⟨A, Matrix.of fun _ _ ↦ (2 : K)⁻¹,
    by ext i j; rw [Subsingleton.elim i default, Subsingleton.elim j default]
       simp [Matrix.mul_apply, hdiag, two_ne_zero],
    by ext i j; rw [Subsingleton.elim i default, Subsingleton.elim j default]
       simp [Matrix.mul_apply, hdiag, two_ne_zero]⟩, rfl⟩
  have htop : R.corootSpan = ⊤ := (R.isMinimal_iff_corootSpan_eq_top hunit).mp hmin
  ext h
  obtain ⟨c, hc⟩ := (R.mem_corootSpan_iff h).mp (htop ▸ Submodule.mem_top)
  rw [← hc, corootMap_apply, Fintype.sum_unique, R.simpleReflection_apply_apply, map_smul,
    simpleCoreflection_coroot_self, smul_neg, map_neg, LinearMap.neg_apply]

/-- **Type `A₁` check (`CartanMatrix.A 1`)**: over any field, the Weyl group has order `2`. -/
theorem card_weylGroup_A_one {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.A 1).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (diag_map_intCast fun i ↦ congrFun (CartanMatrix.A_diag 1) i)) = 2 :=
  R.card_weylGroup_of_unique _

end RankOne

section Examples

/-- Type `A₁`: the Weyl group is generated by a single involution `s₀`, so every element is `1`
or `s₀`, and `s₀` has order `2`. -/
example {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.A 1).map (Int.cast : ℤ → K)) H) :
    let hd := diag_map_intCast (K := K) (fun i ↦ by rw [CartanMatrix.A_one]; fin_cases i; rfl)
    orderOf (R.weylSimple hd 0) = 2 ∧
      ∀ w : R.weylGroup hd, w = 1 ∨ w = R.weylSimple hd 0 := by
  intro hd
  exact ⟨R.orderOf_weylSimple hd 0, R.eq_one_or_weylSimple_of_unique hd⟩

/-- Empty index set: the Weyl group is trivial and every element has word length `0`. -/
example {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((0 : Matrix (Fin 0) (Fin 0) ℤ).map (Int.cast : ℤ → K)) H) :
    let hdiag : ∀ i : Fin 0, (0 : Matrix (Fin 0) (Fin 0) ℤ) i i = 2 := isEmptyElim
    ∀ w : R.weylGroup (diag_map_intCast hdiag),
      R.weylLength (diag_map_intCast hdiag) w = 0 := by
  intro hdiag w
  simp [Subsingleton.elim w 1]

end Examples

end CartanRealization

end TauCeti
