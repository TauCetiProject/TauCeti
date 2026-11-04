/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Coefficients
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.ExtEuler.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Matrix
public import TauCeti.Algebra.Category.GradedModuleCat.Ext.EulerAdmissible
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.ProjectiveCover
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.PowerSeries

/-!
# Unbounded formal-power-series Cartan–Poincaré identities and linearity criteria

Let `A` be a finite-dimensional nonnegatively graded algebra over a field `k`, let `Sᵢ` be an
exhaustive family of finite-dimensional graded simples concentrated in internal degree zero, and
let `C` be the graded Cartan matrix in a projective basis of classes `[A eᵢ]` and the simple-class
basis `[Sⱼ]`.

Over an algebra of infinite global dimension (such as `k[ε]/(ε²)` with `deg ε > 0`, an exterior
algebra, or a Koszul algebra of infinite global dimension), neither `IsGradedEulerAdmissibleOn` nor
a uniform cohomological bound `IsGradedExtBoundedBy` holds. Nevertheless:

1. Because `A` is nonnegatively graded, every entry of `C` is supported in nonnegative powers of `q`
   (`TauCeti.coeff_gradedCartanMatrix_eq_zero_of_neg`), so coefficientwise truncation embeds `C`
   into `Matrix I I (PowerSeries ℤ)`.
2. Whenever the `Sᵢ` admit finite-term minimal graded projective resolutions (or linear
   resolutions), every pair of finite graded modules is ordinarily `TauCeti.IsEulerAdmissible` on
   each fixed internal target shift, and the Alexander-graded Euler formal power series `E_ps` of
   `TauCeti.bigradedExtPoincarePowerSeriesMatrix` satisfies
   `C_psᵀ * E_ps = diagonal (fun i ↦ dim_k(eᵢ • (Sᵢ)₀))`.
3. Comparing this identity with `C_psᵀ * P_tot(-q) = diagonal (fun i ↦ dim_k(eᵢ • (Sᵢ)₀))` over the
   integral domain `PowerSeries ℤ`, where `P_tot(-q)` is the matrix of Maslov-graded Euler formal
   power series `Bigraded.maslovEulerPowerSeries`, cancels `C_psᵀ` on the left and proves that
   **simultaneous linearity of the minimal resolutions of the `Sᵢ` is equivalent to the unbounded
   total-Ext Cartan–Poincaré identity**, with no cohomological global-dimension hypothesis.
4. When the `Sᵢ` admit linear graded projective resolutions, `E_ps` coincides with the signed
   diagonal Ext formal power-series matrix `P_diag(-q)`, giving
   `C_psᵀ * P_diag(-q) = diagonal (fun i ↦ dim_k(eᵢ • (Sᵢ)₀))` and, when all diagonal idempotent
   dimensions equal `1`, `P_diag(-q) = (C_psᵀ)⁻¹` in `Matrix I I (PowerSeries ℤ)`.

## Main results

* `TauCeti.coeff_gradedCartanMatrix_eq_zero_of_neg`: over a nonnegatively graded algebra, all
  negative-degree Laurent coefficients of the graded Cartan matrix vanish.
* `TauCeti.gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal`: the unbounded
  formal-power-series identity `C_psᵀ * E_ps = diagonal (fun i ↦ dim_k(eᵢ • (Sᵢ)₀))` for minimal
  resolutions.
* `TauCeti.forall_isLinear_iff_cartan_poincare_maslovEulerPowerSeries` and
  `TauCeti.forall_exists_isLinear_iff_cartan_poincare_maslovEulerPowerSeries`: linearity of the
  resolutions of the graded simples is equivalent to the formal-power-series Cartan–Poincaré
  identity for the total Ext Poincaré series, without finite global dimension.
* `TauCeti.gradedCartanMatrix_trunc_transpose_mul_diagonalExtPowerSeries_eq_diagonal`,
  `TauCeti.gradedCartanMatrix_trunc_transpose_mul_diagonalExtPowerSeries_eq_diagonal_finrank_end`,
  and `TauCeti.diagonalExtPowerSeries_eq_inv_gradedCartanMatrix_trunc_transpose`: the unbounded
  diagonal Ext formal-power-series Cartan–Poincaré identity and matrix-inverse formula.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11.
* L. Positselski, *The correspondence between Hilbert series of quadratically dual algebras does
  not imply their having the Koszul property*, *Funct. Anal. Appl.* **29** (1995), 213--217.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, *Journal of Combinatorial Theory,
  Series A* **185** (2022), Section 2.2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open scoped Matrix Pointwise

universe uk uA uI uJ

section NonnegCartan

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  [Module.Finite k A] {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {I : Type uI} {J : Type uJ} [Fintype J] [Finite I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis J (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  {f : A} (hf : IsIdempotentElem f)
  (hF : (Ideal.span {f} : Ideal A).IsHomogeneous 𝒜) (j : J)
  (hj : bP j = LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {f}) hF,
      gradedFiniteProjectiveModules_ofIdeal_span_singleton hf hF⟩)

include hj in
/-- Over a nonnegatively graded finite-dimensional algebra, every negative-degree Laurent
coefficient of a column `[A f]` of the graded Cartan matrix in the simple-class basis vanishes
(without assuming unit idempotent multiplicity `dim_k(eᵢ • (Sᵢ)₀) = 1`). -/
theorem coeff_gradedCartanMatrix_eq_zero_of_neg (hneg : ∀ p < 0, 𝒜 p = ⊥) (i : I)
    (hconc : ∀ p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) {p : ℤ} (hp : p < 0) :
    (gradedCartanMatrix 𝒜 bP
      (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS) i j).coeff p = 0 := by
  have hmul := finrank_smul_simple_piece_zero_mul_coeff_gradedCartanMatrix
    S he he₀ hne hself hS bP hf hF j hj i hconc p
  have hbot : cornerSubmodule k (e i) f ⊓ 𝒜 p = ⊥ := by simp [hneg p hp]
  rw [hbot, Module.finrank_zero_of_subsingleton (M := ↥(⊥ : Submodule k A)), Nat.cast_zero] at hmul
  have hpos : (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) ≠ 0 :=
    ne_of_gt (Int.natCast_pos.mpr
      ((S i).obj.finrank_smul_piece_zero_pos_of_concentrated (e i) hconc (hself i)))
  exact (mul_eq_zero.mp hmul).resolve_left hpos

end NonnegCartan

section SliceDescent

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]

private def shiftSliceExtEulerInvariant
    (hadm : IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (Y : (gradedFiniteModules 𝒜).FullSubcategory) :
    ExactK0.AdditiveInvariant (gradedFiniteModulesExactStructure 𝒜).toExactStructure (ℤ → ℤ) where
  obj X a :=
    extEuler.{uA} k (hadm.isEulerAdmissible X.property (gradedFiniteModules_shiftPow Y.property a))
  map_conflation {C} hC := by
    have hC' : (C.map (gradedFiniteModules 𝒜).ι).ShortExact :=
      (gradedFiniteModulesExactStructure_conflation_iff C).mp hC
    funext a
    exact extEuler_shortExact₁ hC' (((GradedModuleCat.shift 𝒜) ^ a).functor.obj Y.obj)
      (hadm.isEulerAdmissible C.X₁.property (gradedFiniteModules_shiftPow Y.property a))
      (hadm.isEulerAdmissible C.X₂.property (gradedFiniteModules_shiftPow Y.property a))
      (hadm.isEulerAdmissible C.X₃.property (gradedFiniteModules_shiftPow Y.property a))

private def shiftSliceExtEulerHom
    (hadm : IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (Y : (gradedFiniteModules 𝒜).FullSubcategory) :
    LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜) →+ (ℤ → ℤ) :=
  (ExactK0.lift.{uA} (shiftSliceExtEulerInvariant hadm Y)).comp
    (LaurentK0.ofExactK0.{uA} (gradedFiniteModulesExactStructure 𝒜)).symm.toAddMonoidHom

private lemma shiftSliceExtEulerHom_of
    (hadm : IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (Y X : (gradedFiniteModules 𝒜).FullSubcategory) (a : ℤ) :
    shiftSliceExtEulerHom hadm Y (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜) X) a =
      extEuler.{uA} k
        (hadm.isEulerAdmissible X.property (gradedFiniteModules_shiftPow Y.property a)) := by
  rw [shiftSliceExtEulerHom, ← LaurentK0.ofExactK0_exactK0_of, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply, ExactK0.lift_of]
  rfl

private lemma shiftSliceExtEulerHom_T_one_smul
    (hadm : IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (Y : (gradedFiniteModules 𝒜).FullSubcategory)
    (z : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) (a : ℤ) :
    shiftSliceExtEulerHom hadm Y ((T 1 : LaurentPolynomial ℤ) • z) a =
      shiftSliceExtEulerHom hadm Y z (a - 1) := by
  let E := gradedFiniteModulesExactStructure 𝒜
  obtain ⟨x, rfl⟩ : ∃ x, LaurentK0.ofExactK0.{uA} E x = z :=
    ⟨(LaurentK0.ofExactK0.{uA} E).symm z, by simp⟩
  let lhs : ExactK0.{uA} E.toExactStructure →+ (ℤ → ℤ) :=
    { toFun := fun y ↦ shiftSliceExtEulerHom hadm Y
        ((T 1 : LaurentPolynomial ℤ) • LaurentK0.ofExactK0.{uA} E y)
      map_zero' := by simp
      map_add' := fun x₁ x₂ ↦ by simp [map_add, smul_add] }
  let rhs : ExactK0.{uA} E.toExactStructure →+ (ℤ → ℤ) :=
    { toFun := fun y b ↦ shiftSliceExtEulerHom hadm Y (LaurentK0.ofExactK0.{uA} E y) (b - 1)
      map_zero' := by ext; simp
      map_add' := fun x₁ x₂ ↦ by ext; simp [map_add] }
  have hmaps : lhs = rhs := ExactK0.hom_ext fun X ↦ by
    funext b
    simp only [lhs, rhs, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LaurentK0.ofExactK0_exactK0_of,
      LaurentK0.T_one_smul_of]
    rw [shiftSliceExtEulerHom_of, shiftSliceExtEulerHom_of]
    have hiso :
        extEuler.{uA} k (hadm.isEulerAdmissible (E.shift.functor.obj X).property
          (gradedFiniteModules_shiftPow Y.property b)) =
        extEuler.{uA} k ((hadm.isEulerAdmissible X.property
          (gradedFiniteModules_shiftPow Y.property (b - 1))).congr
          fun n ↦ (gradedExtShiftSourceEquiv k (GradedModuleCat.shift 𝒜) X.obj Y.obj n b).symm) :=
      extEuler_of_iso _ _ (gradedFiniteModulesExactStructureShiftFunctorCompιIso.app X)
        (Iso.refl _)
    exact hiso.trans (extEuler_congr k
      (fun n ↦ (gradedExtShiftSourceEquiv k (GradedModuleCat.shift 𝒜) X.obj Y.obj n b).symm) _)
  exact congrFun (DFunLike.congr_fun hmaps x) a

private lemma shiftSliceExtEulerHom_T_smul
    (hadm : IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (Y : (gradedFiniteModules 𝒜).FullSubcategory)
    (d : ℤ) (z : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) (a : ℤ) :
    shiftSliceExtEulerHom hadm Y ((T d : LaurentPolynomial ℤ) • z) a =
      shiftSliceExtEulerHom hadm Y z (a - d) := by
  induction d using Int.induction_on generalizing a with
  | zero => simp
  | succ n ih =>
    have hadd : (T ((n : ℤ) + 1) : LaurentPolynomial ℤ) = T 1 * T n := by
      rw [← T_add, add_comm]
    rw [hadd, mul_smul, shiftSliceExtEulerHom_T_one_smul, ih]
    ring_nf
  | pred n ih =>
    have hstep := shiftSliceExtEulerHom_T_one_smul hadm Y
      ((T (-(n : ℤ) - 1) : LaurentPolynomial ℤ) • z) (a + 1)
    have hmul : (T 1 : LaurentPolynomial ℤ) • (T (-(n : ℤ) - 1) : LaurentPolynomial ℤ) • z =
        (T (-(n : ℤ) - 1 + 1) : LaurentPolynomial ℤ) • z := by
      rw [← mul_smul, ← T_add, add_comm]
    rw [hmul, sub_add_cancel, add_sub_cancel_right, ih] at hstep
    exact hstep.symm.trans (by ring_nf)

private lemma shiftSliceExtEulerHom_smul
    (hadm : IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (Y : (gradedFiniteModules 𝒜).FullSubcategory)
    (p : LaurentPolynomial ℤ) (z : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) (a : ℤ) :
    shiftSliceExtEulerHom hadm Y (p • z) a =
      p.coeff.sum fun d c ↦ c * shiftSliceExtEulerHom hadm Y z (a - d) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [add_smul, map_add, Pi.add_apply, hp, hq, AddMonoidAlgebra.coeff_add,
      Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)]
  | C_mul_T d c =>
    rw [mul_smul, laurentPolynomialC_smul, map_zsmul, Pi.smul_apply, smul_eq_mul,
      shiftSliceExtEulerHom_T_smul, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.sum_single_index (zero_mul _)]

private lemma shiftSliceExtEulerHom_smul_eq_coeff_mul
    (hadm : IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (Y : (gradedFiniteModules 𝒜).FullSubcategory)
    (p : LaurentPolynomial ℤ) (hp : ∀ d < 0, p.coeff d = 0)
    (z : LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))
    (hz : ∀ b < 0, shiftSliceExtEulerHom hadm Y z b = 0)
    (Q : PowerSeries ℤ)
    (hQ : ∀ b : ℕ, PowerSeries.coeff b Q = shiftSliceExtEulerHom hadm Y z b) (a : ℕ) :
    shiftSliceExtEulerHom hadm Y (p • z) a =
      PowerSeries.coeff a ((p.trunc : PowerSeries ℤ) * Q) := by
  classical
  rw [shiftSliceExtEulerHom_smul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  let U : Finset ℤ := (Finset.range (a + 1)).map ⟨Nat.cast, Nat.cast_injective⟩
  have hvanish : ∀ d ∉ U, p.coeff d * shiftSliceExtEulerHom hadm Y z ((a : ℤ) - d) = 0 := by
    intro d hd
    by_cases hd0 : d < 0
    · rw [hp d hd0, zero_mul]
    · by_cases hda : (a : ℤ) - d < 0
      · rw [hz _ hda, mul_zero]
      · exfalso
        apply hd
        rw [Finset.mem_map]
        exact ⟨d.toNat, Finset.mem_range.mpr (by omega), Int.toNat_of_nonneg (not_lt.mp hd0)⟩
  have h1 : p.coeff.sum (fun d c ↦ c * shiftSliceExtEulerHom hadm Y z ((a : ℤ) - d)) =
      ∑ d ∈ p.coeff.support ∪ U, p.coeff d * shiftSliceExtEulerHom hadm Y z ((a : ℤ) - d) := by
    rw [Finsupp.sum]
    refine Finset.sum_subset Finset.subset_union_left fun d _ hd ↦ ?_
    rw [Finsupp.notMem_support_iff.mp hd, zero_mul]
  have h2 : (∑ d ∈ U, p.coeff d * shiftSliceExtEulerHom hadm Y z ((a : ℤ) - d)) =
      ∑ d ∈ p.coeff.support ∪ U, p.coeff d * shiftSliceExtEulerHom hadm Y z ((a : ℤ) - d) :=
    Finset.sum_subset Finset.subset_union_right fun d _ hd ↦ hvanish d hd
  rw [h1, ← h2, Finset.sum_map]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hma : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hsub : (a : ℤ) - (m : ℤ) = ((a - m : ℕ) : ℤ) := by omega
  rw [Function.Embedding.coeFn_mk, Polynomial.coeff_coe, coeff_trunc, hsub, ← hQ (a - m)]

end SliceDescent

section CartanPowerSeries

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Fintype I] [DecidableEq I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) ≠ 0)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include hI hbP in
private theorem cartan_eulerPowerSeries_eq_diagonal_aux
    (hadm : IsEulerAdmissibleOn.{uA} k (gradedFiniteModules 𝒜) (gradedFiniteModules 𝒜))
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj)
    (hP : ∀ i j, Bigraded.HasEulerPowerSeries
      (bigradedExtPoincarePowerSeries k (GradedModuleCat.shift 𝒜) (h i j)))
    (hz : ∀ l j {b : ℤ}, b < 0 →
      ∀ ha : IsEulerAdmissible.{uA} k (S l).obj
        (((GradedModuleCat.shift 𝒜) ^ b).functor.obj (S j).obj),
        extEuler.{uA} k ha = 0) :
    ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p ↦ (p.trunc : PowerSeries ℤ))ᵀ *
      Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries (hP i j)) =
      Matrix.diagonal fun i ↦
        PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) := by
  set bM := gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS
  refine Matrix.ext fun i j ↦ PowerSeries.ext fun a ↦ ?_
  have hcol := congrArg (fun z ↦ shiftSliceExtEulerHom hadm (S j) z (a : ℤ))
    (gradedCartanMap_basis_apply_eq_sum 𝒜 bP bM i)
  rw [map_sum, Finset.sum_apply] at hcol
  -- Rewrite the right-hand side of `hcol` into the `(i, j)` coefficient of `C_psᵀ * E_ps`.
  have hrhs : (∑ l, shiftSliceExtEulerHom hadm (S j)
        (gradedCartanMatrix 𝒜 bP bM l i • bM l) (a : ℤ)) =
      PowerSeries.coeff a
        ((((gradedCartanMatrix 𝒜 bP bM).map fun p ↦ (p.trunc : PowerSeries ℤ))ᵀ *
          Matrix.of fun l m ↦ Bigraded.eulerPowerSeries (hP l m)) i j) := by
    rw [Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
      gradedSimpleClassBasisOfNeZero_apply]
    exact shiftSliceExtEulerHom_smul_eq_coeff_mul hadm (S j)
      (gradedCartanMatrix 𝒜 bP bM l i)
      (fun d hd ↦ coeff_gradedCartanMatrix_eq_zero_of_neg S he he₀ hne hself hS bP
        (he i) (hI i) i (hbP i) hneg l (hconc l) hd)
      (LaurentK0.of _ (S l))
      (fun b hb ↦ by
        rw [shiftSliceExtEulerHom_of]
        exact hz l j hb _)
      (Bigraded.eulerPowerSeries (hP l j))
      (fun b ↦ (coeff_eulerPowerSeries_bigradedExtPoincarePowerSeries (h l j) (hP l j) b _).trans
        (shiftSliceExtEulerHom_of hadm (S j) (S l) b).symm) a
  -- Evaluate the left-hand side of `hcol` by projectivity of `A eᵢ`.
  have hlhs : shiftSliceExtEulerHom hadm (S j) (gradedCartanMap 𝒜 (bP i)) (a : ℤ) =
      PowerSeries.coeff a
        (Matrix.diagonal
          (fun m ↦ PowerSeries.C (Module.finrank k ↥(e m • (S m).obj.grading.piece 0) : ℤ))
          i j) := by
    have := GradedModuleCat.projective_ofIdeal_span_singleton (he i) (hI i)
    rw [hbP i, gradedCartanMap_of, shiftSliceExtEulerHom_of, extEuler_projective,
      (GradedModuleCat.homShiftPowEquiv 𝒜 _ (S j).obj (a : ℤ)).finrank_eq,
      (GradedModuleCat.ofIdealSpanSingletonHomEquiv (he i) (he₀ i) (hI i) _).finrank_eq,
      InternalGrading.shift_piece]
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [Nat.cast_zero, neg_zero, add_zero]
      simp only [Matrix.diagonal_apply]
      split_ifs with hij
      · subst hij
        simp
      · rw [map_zero]
        have h0 := congrArg (fun f : LaurentPolynomial ℤ ↦ f.coeff 0) (hne hij)
        rwa [GradedModuleCat.coeff_smulGradedDimension, AddMonoidAlgebra.coeff_zero,
          Finsupp.zero_apply] at h0
    · have hbot : (S j).obj.grading.piece (0 + -(a : ℤ)) = ⊥ :=
        hconc j _ (by omega)
      have hsmul : e i • (⊥ : Submodule k (S j).obj) = ⊥ :=
        (Submodule.eq_bot_iff _).mpr (by rintro _ ⟨x, hx, rfl⟩; simp at hx; simp [hx])
      rw [hbot, hsmul, Module.finrank_zero_of_subsingleton, Nat.cast_zero]
      simp only [Matrix.diagonal_apply]
      split_ifs with hij
      · rw [PowerSeries.coeff_C, ite_eq_right ha0]
      · rw [map_zero]
  exact hrhs.symm.trans (hcol.symm.trans hlhs)

include hbP in
/-- **The unbounded Cartan–Euler formal power-series identity.** Over a finite-dimensional
nonnegatively graded algebra, let `Sᵢ` be an exhaustive degree-zero simple family with chosen
finite-term minimal resolutions `rᵢ`. Then `C_psᵀ * E_ps = diagonal (fun i ↦ dim_k(eᵢ • (Sᵢ)₀))`,
where `C_ps` truncates each entry of the graded Cartan matrix into `PowerSeries ℤ` and `E_ps` takes
the Alexander-graded Euler formal power series of each entry of the full Ext Poincaré matrix. No
cohomological global-dimension bound is assumed. -/
theorem gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite k ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj :=
      fun i j ↦ GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S j).obj) :
    ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p ↦ (p.trunc : PowerSeries ℤ))ᵀ *
      Matrix.of (fun i j ↦ Bigraded.eulerPowerSeries
        ((hr i).hasEulerPowerSeries_bigradedExtPoincarePowerSeries
          (fun p hp ↦ hconc i p hp.ne) (hconc j) (h i j))) =
      Matrix.diagonal fun i ↦
        PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) :=
  cartan_eulerPowerSeries_eq_diagonal_aux S he he₀ hI hne hself hS bP hbP
    (isEulerAdmissibleOn_gradedFiniteModules_of_isMinimal S hS hconc r hr)
    hneg hconc h
    (fun i j ↦ (hr i).hasEulerPowerSeries_bigradedExtPoincarePowerSeries
      (fun p hp ↦ hconc i p hp.ne) (hconc j) (h i j))
    (fun l j _ hb ha ↦ (hr l).extEuler_shiftPow_eq_zero_of_lt (c := 0)
      (fun p hp ↦ hconc l p hp.ne) (hconc j) hb ha)

include hbP in
/-- **Linearity is the unbounded Cartan–Poincaré identity for the total Ext Poincaré series.** Let
`P` be `TauCeti.bigradedExtPoincarePowerSeriesMatrix` of the `Sᵢ`, and apply
`Bigraded.maslovEulerPowerSeries` entrywise to obtain `P_tot(-q)`, whose `(i, j)` entry has `n`-th
coefficient `(-1)ⁿ dim_k (⨁ p, Extⁿ(Sᵢ, Sⱼ{p}))`. Chosen minimal resolutions with
finite-dimensional terms are all linear if and only if
`C_psᵀ * P_tot(-q) = diagonal (fun i ↦ dim_k(eᵢ • (Sᵢ)₀))`. No uniform cohomological Ext bound is
needed. -/
theorem forall_isLinear_iff_cartan_poincare_maslovEulerPowerSeries
    (r : ∀ i, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading)
    [∀ i n, Module.Finite k ((r i).X n)] (hr : ∀ i, (r i).IsMinimal)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj :=
      fun i j ↦ GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S j).obj) :
    (∀ i, (r i).IsLinear) ↔
      ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
          fun p ↦ (p.trunc : PowerSeries ℤ))ᵀ *
        (bigradedExtPoincarePowerSeriesMatrix (fun i ↦ (S i).obj) h).map
          Bigraded.maslovEulerPowerSeries =
        Matrix.diagonal fun i ↦
          PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) := by
  set Cps := ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
    fun p ↦ (p.trunc : PowerSeries ℤ))ᵀ
  have key := gradedCartanMatrix_trunc_transpose_mul_eulerPowerSeries_eq_diagonal
    S he he₀ hI hne hself hS bP hbP r hr hneg hconc h
  have hiff (i j : I) :
      Bigraded.eulerPowerSeries
          ((hr i).hasEulerPowerSeries_bigradedExtPoincarePowerSeries
            (fun p hp ↦ hconc i p hp.ne) (hconc j) (h i j)) =
        Bigraded.maslovEulerPowerSeries
          (bigradedExtPoincarePowerSeriesMatrix (fun m ↦ (S m).obj) h i j) ↔
      ∀ (n : ℕ) (p : ℤ), (n : ℤ) ≠ p →
        (PowerSeries.coeff n
          (bigradedExtPoincarePowerSeriesMatrix (fun m ↦ (S m).obj) h i j)).coeff p = 0 := by
    simp only [bigradedExtPoincarePowerSeriesMatrix_apply]
    exact Bigraded.eulerPowerSeries_eq_maslovEulerPowerSeries_iff
      ((hr i).hasEulerPowerSeries_bigradedExtPoincarePowerSeries
        (fun p hp ↦ hconc i p hp.ne) (hconc j) (h i j))
      (fun n p ↦ by
        rw [coeff_coeff_bigradedExtPoincarePowerSeries]
        exact Int.natCast_nonneg _)
      (fun n p hpn ↦ (hr i).coeff_coeff_bigradedExtPoincarePowerSeries_eq_zero_of_lt
        (fun q hq ↦ hconc i q hq.ne) (hconc j) (h i j) (by omega))
  rw [forall_isLinear_iff_diagonal_bigradedExtPoincarePowerSeriesMatrix S hS hconc h r hr hneg]
  constructor
  · intro hdiag
    rw [← key]
    congr 1
    exact Matrix.ext fun i j ↦ ((hiff i j).2 (hdiag i j)).symm
  · intro hid i j
    have hdet : Cps.det ≠ 0 := by
      intro h0
      have hprod := congrArg Matrix.det key
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_diagonal] at hprod
      refine Finset.prod_ne_zero_iff.mpr (fun m _ ↦ ?_) hprod.symm
      intro hC0
      have hpos : (0 : ℤ) < Module.finrank k ↥(e m • (S m).obj.grading.piece 0) :=
        Int.natCast_pos.mpr
          ((S m).obj.finrank_smul_piece_zero_pos_of_concentrated (e m) (hconc m) (hself m))
      have hm0 := congrArg (PowerSeries.constantCoeff) hC0
      simp only [PowerSeries.constantCoeff_C, map_zero] at hm0
      omega
    have hreg := (Matrix.isRegular_of_isLeftRegular_det
      (isRegular_iff_ne_zero.mpr hdet).left).left (hid.trans key.symm)
    exact (hiff i j).1 (congrFun (congrFun hreg i) j).symm

include hbP in
/-- **Linearity is the unbounded Cartan–Poincaré identity over a semisimple degree-zero part.** Over
a finite-dimensional nonnegatively graded algebra with semisimple degree-zero part, every member of
an exhaustive degree-zero simple family admits a linear graded projective resolution if and only if
`C_psᵀ * P_tot(-q) = diagonal (fun i ↦ dim_k(eᵢ • (Sᵢ)₀))` in `Matrix I I (PowerSeries ℤ)`. No
chosen resolutions or cohomological global-dimension bounds appear in the statement. -/
theorem forall_exists_isLinear_iff_cartan_poincare_maslovEulerPowerSeries
    [IsSemisimpleRing (𝒜 0)]
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (h : ∀ i j, IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj :=
      fun i j ↦ GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S j).obj) :
    (∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear) ↔
      ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
          fun p ↦ (p.trunc : PowerSeries ℤ))ᵀ *
        (bigradedExtPoincarePowerSeriesMatrix (fun i ↦ (S i).obj) h).map
          Bigraded.maslovEulerPowerSeries =
        Matrix.diagonal fun i ↦
          PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) := by
  classical
  choose r hr hfinite using fun i ↦
    GradedProjectiveResolution.exists_isMinimal_of_finite hneg (S i).obj
  let _ (i : I) (n : ℕ) : Module.Finite k ((r i).X n) := hfinite i n
  rw [← forall_isLinear_iff_cartan_poincare_maslovEulerPowerSeries
    S he he₀ hI hne hself hS bP hbP r hr hneg hconc h]
  constructor
  · intro hlin i
    apply ((hr i).isLinear_iff_subsingleton_ext_shiftObj_simple hneg).2
    intro N _ _ hNzero n p hnp
    obtain ⟨r', hr'⟩ := hlin i
    exact hr'.subsingleton_ext_shiftObj_of_ne hNzero n p hnp
  · exact fun hlin i ↦ ⟨r i, hlin i⟩

include hbP in
/-- **The unbounded diagonal-Ext Cartan–Poincaré formal power-series identity.** Suppose `A` is
nonnegatively graded and every member of the exhaustive degree-zero simple family `Sᵢ` admits a
linear graded projective resolution (possibly of infinite length, with no minimality or semisimple
degree-zero assumption). Let `P_diag` be the formal power-series matrix with `(i, j)` entry
`∑ n, dim_k Extⁿ(Sᵢ, Sⱼ{n}) tⁿ`. Then
`C_psᵀ * P_diag(-q) = diagonal (fun i ↦ dim_k(eᵢ • (Sᵢ)₀))`. -/
theorem gradedCartanMatrix_trunc_transpose_mul_diagonalExtPowerSeries_eq_diagonal
    (hlin : ∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p ↦ (p.trunc : PowerSeries ℤ))ᵀ *
      Matrix.of (fun i j ↦ PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.mk fun n ↦
          (Module.finrank k
            (GradedExt.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj n n) : ℤ))) =
      Matrix.diagonal fun i ↦
        PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) := by
  classical
  choose r hr using fun i ↦ hlin i
  let h (i j : I) :
      IsGradedExtInternallyFinite.{uA} k (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj :=
    GradedModuleCat.isGradedExtInternallyFinite_of_moduleFinite (S i).obj (S j).obj
  have key := cartan_eulerPowerSeries_eq_diagonal_aux S he he₀ hI hne hself hS bP hbP
    (isEulerAdmissibleOn_gradedFiniteModules_of_isLinear S hS hconc hlin)
    hneg hconc h
    (fun i j ↦ (hr i).hasEulerPowerSeries_bigradedExtPoincarePowerSeries (hconc j) (h i j))
    (fun l j _ hb ha ↦ (hr l).extEuler_shiftPow_eq_zero_of_neg (hconc j) hb ha)
  convert key using 2
  refine Matrix.ext fun i j ↦ ?_
  rw [Matrix.of_apply, Matrix.of_apply,
    (hr i).eulerPowerSeries_bigradedExtPoincarePowerSeries_eq (hconc j) (h i j)]

include hbP in
/-- **The division-endomorphism correction to the unbounded Cartan–Poincaré identity.** When the
idempotent projectives `A eᵢ` cover the degree-zero simples `Sᵢ`, the diagonal entries of the
formal-power-series Cartan–Poincaré identity are the constants `dim_k End_A(Sᵢ)`. -/
theorem gradedCartanMatrix_trunc_transpose_mul_diagonalExtPowerSeries_eq_diagonal_finrank_end
    [∀ i, IsSimpleModule A (S i).obj]
    {f : ∀ i, (Ideal.span {e i} : Ideal A) →ₗ[A] (S i).obj}
    (hf : ∀ i, IsProjectiveCover (f i))
    (hlin : ∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    ((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasisOfNeZero S he he₀ hne hself hS)).map
        fun p ↦ (p.trunc : PowerSeries ℤ))ᵀ *
      Matrix.of (fun i j ↦ PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.mk fun n ↦
          (Module.finrank k
            (GradedExt.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj n n) : ℤ))) =
      Matrix.diagonal fun i ↦
        PowerSeries.C (Module.finrank k (Module.End A (S i).obj) : ℤ) := by
  rw [gradedCartanMatrix_trunc_transpose_mul_diagonalExtPowerSeries_eq_diagonal
    S he he₀ hI hne hself hS bP hbP hlin hneg hconc]
  congr 1
  funext i
  have hcov := congrArg (fun p : LaurentPolynomial ℤ ↦ p.coeff 0)
    ((S i).obj.smulGradedDimension_eq_C_finrank_end_of_isProjectiveCover (he i) (hconc i) (hf i))
  simp only [GradedModuleCat.coeff_smulGradedDimension, ← single_eq_C,
    AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hcov
  rw [hcov]

end CartanPowerSeries

section UnitDiagonal

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [Module.Finite k A]
  [HasExt.{uA} (GradedModuleCat.{uA} 𝒜)]
  {I : Type uI} [Fintype I] [DecidableEq I]
  (S : I → (gradedFiniteModules 𝒜).FullSubcategory) {e : I → A}
  (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hI : ∀ i, (Ideal.span {e i} : Ideal A).IsHomogeneous 𝒜)
  (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)
  (hself : ∀ i, (S i).obj.smulGradedDimension (e i) = 1)
  (hS : IsExhaustiveGradedSimpleFamily S)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    ⟨GradedModuleCat.ofIdeal 𝒜 (Ideal.span {e i}) (hI i),
      gradedFiniteProjectiveModules_ofIdeal_span_singleton (he i) (hI i)⟩)

include hbP in
/-- **The unbounded diagonal Ext Poincaré power-series matrix at `-t` is the inverse of the
transposed graded Cartan matrix**: `P_diag(-t) = (C_psᵀ)⁻¹` in `Matrix I I (PowerSeries ℤ)`, with
no uniform cohomological vanishing bound on Ext. -/
theorem diagonalExtPowerSeries_eq_inv_gradedCartanMatrix_trunc_transpose
    (hlin : ∀ i, ∃ r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (S i).obj.grading,
      r.IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥)
    (hconc : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥) :
    Matrix.of (fun i j ↦ PowerSeries.rescale (-1 : ℤ)
        (PowerSeries.mk fun n ↦
          (Module.finrank k
            (GradedExt.{uA} (GradedModuleCat.shift 𝒜) (S i).obj (S j).obj n n) : ℤ))) =
      (((gradedCartanMatrix 𝒜 bP (gradedSimpleClassBasis S he he₀ hne hself hS)).map
        fun p ↦ (p.trunc : PowerSeries ℤ))ᵀ)⁻¹ := by
  have hone (i : I) :
      PowerSeries.C (Module.finrank k ↥(e i • (S i).obj.grading.piece 0) : ℤ) = 1 := by
    have hi := congrArg (fun p : LaurentPolynomial ℤ ↦ p.coeff 0) (hself i)
    simp only [GradedModuleCat.coeff_smulGradedDimension, coeff_one, ite_true] at hi
    rw [hi, map_one]
  have hbasis : gradedSimpleClassBasis S he he₀ hne hself hS =
      gradedSimpleClassBasisOfNeZero S he he₀ hne (fun i ↦ (hself i).symm ▸ one_ne_zero) hS :=
    DFunLike.ext _ _ fun i ↦ by simp
  exact (Matrix.inv_eq_right_inv (by
    rw [hbasis]
    simpa only [hone, Matrix.diagonal_one] using
      gradedCartanMatrix_trunc_transpose_mul_diagonalExtPowerSeries_eq_diagonal
        S he he₀ hI hne (fun i ↦ (hself i).symm ▸ one_ne_zero) hS bP hbP hlin hneg hconc)).symm

end UnitDiagonal

end TauCeti
