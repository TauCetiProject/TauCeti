/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.RingTheory.Huber.WeightedEval.Hom
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PDeriv
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Rename

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.GaussValuation
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.NonUnit
import TauCeti.RingTheory.MvPowerSeries.Derivative
import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic

/-!
# Restricted power-series rings `A⟨T₁, …, T_N⟩` and coefficient plus subrings

Over a nonarchimedean commutative ring `A`, `TauCeti.Huber.tateSeries N A` is the ring of
restricted power series in `N` variables — the specialization of
`TauCeti.Huber.weightedRestrictedSubring` to the trivial weight family `Tᵢ = {1}`, with coordinate
variables `TauCeti.Huber.tateSeries.X` and coefficientwise subring
`TauCeti.Huber.tateSeriesPlus N A Aplus`. When `A` is complete and Hausdorff, `tateSeries N A` is
complete and Hausdorff, so `TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` identifies
`restrictedMvPowerSeriesCompletion N A` with `tateSeries N A` while retaining termwise formal
partial derivatives `MvPowerSeries.pderiv` and formal Jacobian determinants
`TauCeti.Huber.tateSeries.jacobian`.

For a Huber pair `S = (A, A⁺)`, `TauCeti.Huber.tateSeriesPair N A S` is the uncompleted unit-weight
Huber pair `S.weighted isWeightFamily_one_weight`, whose plus ring equals
`tateSeriesPlus N A S.plus` (`TauCeti.Huber.tateSeriesPair_plus`) and maps under
`(restrictedMvPowerSeriesCompletionEquiv N A).symm` onto `S.polydiscPlus N`
(`TauCeti.Huber.map_symm_tateSeriesPlus_eq_polydiscPlus`).

## Main definitions

* `TauCeti.Huber.tateSeries` and `TauCeti.Huber.tateSeries.X`: `A⟨T₁, …, T_N⟩` and coordinate `Tᵢ`.
* `TauCeti.Huber.tateSeries.pderiv`: formal partial derivative `∂/∂Tⱼ` on `tateSeries N A`.
* `TauCeti.Huber.tateSeries.jacobianMatrix` and `TauCeti.Huber.tateSeries.jacobian`: the formal
  `N × N` Jacobian matrix `(∂Fᵢ/∂Tⱼ)` and its determinant in `tateSeries N A`.
* `TauCeti.Huber.tateSeries.renameAlgHom`, `TauCeti.Huber.tateSeries.castSuccAlgHom`, and
  `TauCeti.Huber.tateSeries.mapRingHom`: variable renaming, `N ↪ N + 1` inclusion, and base change.
* `TauCeti.Huber.tateSeriesPlus` and `TauCeti.Huber.tateSeriesPair`: the coefficientwise subring
  `A⁺⟨T₁, …, T_N⟩` and Huber pair `(A⟨T⟩, A⁺⟨T⟩)`.

## Main results

* `TauCeti.Huber.mem_tateSeriesPlus_iff`: `f ∈ tateSeriesPlus N A Aplus` iff every coefficient of
  `f` lies in `Aplus`.
* `TauCeti.Huber.tateSeries.pderiv_mem_tateSeriesPlus` and
  `TauCeti.Huber.tateSeries.jacobian_mem_tateSeriesPlus`: `∂/∂Tⱼ` and formal Jacobians preserve
  `tateSeriesPlus`.
* `TauCeti.Huber.map_symm_tateSeriesPlus_eq_polydiscPlus`: comparison with `S.polydiscPlus N`.
* `TauCeti.Huber.exists_pow_smul_mem_tateSeriesPlus`: rescaling into an open subring by `ϖ ^ m`.
* `TauCeti.Huber.isWeightBounded_one_weight_of_mem_plus` and
  `TauCeti.Huber.tateSeriesPlus_map_le_of_continuous`: weight-boundedness of tuples in a plus ring
  and preservation of `tateSeriesPlus` under continuous ring homomorphisms.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Example 5.54, Proposition 5.49, and Example 7.57.
* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, Vieweg (1996), §1.7.
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343v3, §6 and §24.
-/

public section

open Topology UniformSpace

namespace TauCeti.Huber

section Nonarchimedean

variable (N : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The ring `A⟨T₁, …, T_N⟩` of restricted power series**, defined as
`TauCeti.Huber.weightedRestrictedSubring` at the trivial weight family `Tᵢ = {1}`. Over a complete
Hausdorff base `A` it is canonically isomorphic to the completed Tate algebra
`TauCeti.Huber.restrictedMvPowerSeriesCompletion N A`, while as a subring of
`MvPowerSeries (Fin N) A` it carries termwise formal partial derivatives. -/
abbrev tateSeries : Type _ :=
  weightedRestrictedSubring (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight

/-- **The `i`-th coordinate variable `Tᵢ ∈ A⟨T₁, …, T_N⟩`.** -/
noncomputable def tateSeries.X (i : Fin N) : tateSeries N A :=
  weightedX (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight i

/-- **The subring `A⁺⟨T₁, …, T_N⟩` of restricted power series whose coefficients all lie in
`Aplus`.** -/
abbrev tateSeriesPlus (Aplus : Subring A) : Subring (tateSeries N A) :=
  weightedSubring (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight Aplus

variable {N A}

theorem tateSeries.X_eq_weightedX (i : Fin N) :
    tateSeries.X N A i = weightedX (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight i :=
  (rfl)

@[simp]
theorem tateSeries.coe_X (i : Fin N) :
    (tateSeries.X N A i : MvPowerSeries (Fin N) A) = MvPowerSeries.X i := by
  rw [tateSeries.X_eq_weightedX, coe_weightedX]

theorem tateSeries.coe_algebraMap (a : A) :
    (algebraMap A (tateSeries N A) a : MvPowerSeries (Fin N) A) = MvPowerSeries.C a := by
  rw [algebraMap_weightedRestrictedSubring, coe_weightedC]

/-- A pseudouniformiser of `A` remains a pseudouniformiser in `tateSeries N A` via `algebraMap`. -/
theorem tateSeries.isPseudoUniformizer_algebraMap {ϖ : A} (hϖ : IsPseudoUniformizer ϖ) :
    IsPseudoUniformizer (algebraMap A (tateSeries N A) ϖ) := by
  rw [algebraMap_weightedRestrictedSubring]
  exact hϖ.map (continuous_weightedC isWeightFamily_one_weight)

/-- Under the canonical inclusion into the completion `restrictedMvPowerSeriesCompletion N A`,
`tateSeries.X N A i` is `Pair.polydiscVar N A i`. -/
@[simp]
theorem tateSeries.coe_X_completion (i : Fin N) :
    ((tateSeries.X N A i : tateSeries N A) : restrictedMvPowerSeriesCompletion N A) =
      Pair.polydiscVar N A i := by
  rw [tateSeries.X_eq_weightedX]

/-- Over a nonzero base ring, no coordinate variable `Tᵢ` is a unit of `A⟨T₁, …, T_N⟩`. -/
theorem tateSeries.not_isUnit_X [Nontrivial A] (i : Fin N) :
    ¬IsUnit (tateSeries.X N A i) :=
  not_isUnit_weightedX i

/-- **Formal partial derivative `∂/∂Tⱼ` on `tateSeries N A`.** -/
noncomputable def tateSeries.pderiv (j : Fin N) :
    tateSeries N A →ₗ[A] tateSeries N A where
  toFun f := ⟨MvPowerSeries.pderiv j (f : MvPowerSeries (Fin N) A),
    mem_weightedRestrictedSubring.mpr
      ((mem_weightedRestrictedSubring.mp f.2).pderiv_one_weight j)⟩
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.pderiv j) _ _)
  map_smul' a f := Subtype.ext <| by
    simp only [RingHom.id_apply, Algebra.smul_def, MulMemClass.coe_mul, tateSeries.coe_algebraMap]
    rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul,
      (MvPowerSeries.pderiv j).map_smul]

@[simp]
theorem tateSeries.coe_pderiv (j : Fin N) (f : tateSeries N A) :
    (tateSeries.pderiv j f : MvPowerSeries (Fin N) A) =
      MvPowerSeries.pderiv j (f : MvPowerSeries (Fin N) A) := (rfl)

@[simp]
theorem tateSeries.pderiv_weightedC (j : Fin N) (a : A) :
    tateSeries.pderiv j
        (weightedC (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight a) = 0 :=
  Subtype.ext <| by
    rw [tateSeries.coe_pderiv, coe_weightedC, MvPowerSeries.pderiv_C, ZeroMemClass.coe_zero]

theorem tateSeries.pderiv_algebraMap (j : Fin N) (a : A) :
    tateSeries.pderiv j (algebraMap A (tateSeries N A) a) = 0 := by
  rw [algebraMap_weightedRestrictedSubring, tateSeries.pderiv_weightedC]

@[simp]
theorem tateSeries.pderiv_one (j : Fin N) :
    tateSeries.pderiv j (1 : tateSeries N A) = 0 :=
  Subtype.ext <| by rw [tateSeries.coe_pderiv, OneMemClass.coe_one, MvPowerSeries.pderiv_one,
    ZeroMemClass.coe_zero]

theorem tateSeries.pderiv_mul (j : Fin N) (f g : tateSeries N A) :
    tateSeries.pderiv j (f * g) = f * tateSeries.pderiv j g + g * tateSeries.pderiv j f :=
  Subtype.ext ((MvPowerSeries.pderiv j).leibniz (f : MvPowerSeries (Fin N) A) g)

theorem tateSeries.pderiv_pow (j : Fin N) (f : tateSeries N A) (m : ℕ) :
    tateSeries.pderiv j (f ^ m) = m • (f ^ (m - 1) * tateSeries.pderiv j f) :=
  Subtype.ext <| by
    have h := Derivation.leibniz_pow (MvPowerSeries.pderiv j) (f : MvPowerSeries (Fin N) A) m
    simp [tateSeries.coe_pderiv, h, nsmul_eq_mul, mul_left_comm]

theorem tateSeries.pderiv_X (j i : Fin N) :
    tateSeries.pderiv j (tateSeries.X N A i) = Pi.single (M := fun _ ↦ tateSeries N A) i 1 j :=
  Subtype.ext <| by
    rw [tateSeries.coe_pderiv, tateSeries.coe_X, MvPowerSeries.pderiv_X]
    by_cases hij : i = j <;> simp [hij]

@[simp]
theorem tateSeries.pderiv_X_self (i : Fin N) :
    tateSeries.pderiv i (tateSeries.X N A i) = 1 := by
  rw [tateSeries.pderiv_X, Pi.single_eq_same]

theorem tateSeries.pderiv_X_of_ne {j i : Fin N} (h : i ≠ j) :
    tateSeries.pderiv j (tateSeries.X N A i) = 0 := by
  rw [tateSeries.pderiv_X, Pi.single_eq_of_ne h.symm]

/-- **Coefficientwise characterization of `tateSeriesPlus`:** a restricted series lies in
`tateSeriesPlus N A Aplus` if and only if all of its coefficients belong to `Aplus`. -/
theorem mem_tateSeriesPlus_iff {Aplus : Subring A} {f : tateSeries N A} :
    f ∈ tateSeriesPlus N A Aplus ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin N) A) ∈ Aplus := by
  simp [mem_weightedSubring, mem_weightedNhd, weightMul_one_weight]

@[simp]
theorem tateSeriesPlus_top : tateSeriesPlus N A ⊤ = ⊤ := by
  ext f; simp

theorem algebraMap_mem_tateSeriesPlus_iff {Aplus : Subring A} {a : A} :
    algebraMap A (tateSeries N A) a ∈ tateSeriesPlus N A Aplus ↔ a ∈ Aplus := by
  rw [algebraMap_weightedRestrictedSubring, weightedC_mem_weightedSubring]

theorem tateSeries.X_mem_tateSeriesPlus (Aplus : Subring A) (i : Fin N) :
    tateSeries.X N A i ∈ tateSeriesPlus N A Aplus := by
  simpa [tateSeries.X_eq_weightedX] using
    weightedC_mul_weightedX_mem_weightedSubring (T := fun _ : Fin N ↦ ({1} : Set A))
      (hT := isWeightFamily_one_weight) (R := Aplus) (i := i) (Set.mem_singleton (1 : A))

/-- Formal partial differentiation preserves `tateSeriesPlus`. -/
theorem tateSeries.pderiv_mem_tateSeriesPlus {Aplus : Subring A} {f : tateSeries N A}
    (hf : f ∈ tateSeriesPlus N A Aplus) (j : Fin N) :
    tateSeries.pderiv j f ∈ tateSeriesPlus N A Aplus := by
  rw [mem_tateSeriesPlus_iff] at hf ⊢
  exact MvPowerSeries.coeff_pderiv_mem hf j

section Jacobian

/-- **The formal Jacobian matrix `(∂Fᵢ/∂Tⱼ)` of an `N`-tuple of restricted series.** -/
noncomputable def tateSeries.jacobianMatrix (F : Fin N → tateSeries N A) :
    Matrix (Fin N) (Fin N) (tateSeries N A) :=
  Matrix.of fun i j ↦ tateSeries.pderiv j (F i)

@[simp]
theorem tateSeries.jacobianMatrix_apply (F : Fin N → tateSeries N A) (i j : Fin N) :
    tateSeries.jacobianMatrix F i j = tateSeries.pderiv j (F i) :=
  (rfl)

/-- **The formal Jacobian determinant `det(∂Fᵢ/∂Tⱼ) ∈ A⟨T₁, …, T_N⟩`.** -/
noncomputable def tateSeries.jacobian (F : Fin N → tateSeries N A) : tateSeries N A :=
  (tateSeries.jacobianMatrix F).det

theorem tateSeries.jacobian_def (F : Fin N → tateSeries N A) :
    tateSeries.jacobian F = (tateSeries.jacobianMatrix F).det :=
  (rfl)

/-- Coercing `tateSeries.jacobian F` to `MvPowerSeries (Fin N) A` computes the determinant of the
power-series Jacobian matrix `(MvPowerSeries.pderiv j (F i))`. -/
@[simp]
theorem tateSeries.coe_jacobian (F : Fin N → tateSeries N A) :
    (tateSeries.jacobian F : MvPowerSeries (Fin N) A) =
      (Matrix.of fun i j ↦ MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) A)).det := by
  rw [tateSeries.jacobian_def, ← Subring.subtype_apply, RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1

/-- If each equation `F i` has coefficients in `Aplus`, then so does `tateSeries.jacobian F`. -/
theorem tateSeries.jacobian_mem_tateSeriesPlus {Aplus : Subring A} {F : Fin N → tateSeries N A}
    (hF : ∀ i, F i ∈ tateSeriesPlus N A Aplus) :
    tateSeries.jacobian F ∈ tateSeriesPlus N A Aplus := by
  let Jplus : Matrix (Fin N) (Fin N) (tateSeriesPlus N A Aplus) :=
    Matrix.of fun i j ↦ ⟨tateSeries.pderiv j (F i), tateSeries.pderiv_mem_tateSeriesPlus (hF i) j⟩
  have hdet : ((Jplus.det : tateSeriesPlus N A Aplus) : tateSeries N A) =
      tateSeries.jacobian F := by
    rw [← Subring.subtype_apply, RingHom.map_det, RingHom.mapMatrix_apply, tateSeries.jacobian_def]
    congr 1
  exact hdet ▸ Jplus.det.2

@[simp]
theorem tateSeries.jacobian_fin_zero (F : Fin 0 → tateSeries 0 A) :
    tateSeries.jacobian F = 1 := by
  rw [tateSeries.jacobian_def]
  exact Matrix.det_isEmpty

@[simp]
theorem tateSeries.jacobian_fin_one (F : Fin 1 → tateSeries 1 A) :
    tateSeries.jacobian F = tateSeries.pderiv 0 (F 0) := by
  rw [tateSeries.jacobian_def, Matrix.det_fin_one, tateSeries.jacobianMatrix_apply]

end Jacobian

/-- **Variable renaming `A⟨T₁, …, T_N⟩ →ₐ[A] A⟨T₁, …, T_M⟩` along an embedding `Fin N ↪ Fin M`.** -/
noncomputable def tateSeries.renameAlgHom {M : ℕ} (e : Fin N ↪ Fin M) :
    tateSeries N A →ₐ[A] tateSeries M A :=
  weightedRenameAlgHom e isWeightFamily_one_weight isWeightFamily_one_weight fun _ ↦ subset_rfl

@[simp]
theorem tateSeries.coe_renameAlgHom {M : ℕ} (e : Fin N ↪ Fin M) (f : tateSeries N A) :
    (tateSeries.renameAlgHom e f : MvPowerSeries (Fin M) A) =
      MvPowerSeries.rename e (f : MvPowerSeries (Fin N) A) := by
  rw [tateSeries.renameAlgHom, weightedRenameAlgHom_apply, coe_weightedRename]

/-- `tateSeries.renameAlgHom e` is continuous. -/
theorem tateSeries.continuous_renameAlgHom {M : ℕ} (e : Fin N ↪ Fin M) :
    Continuous (tateSeries.renameAlgHom (A := A) e) := by
  have h : (tateSeries.renameAlgHom (A := A) e : tateSeries N A → tateSeries M A) =
      weightedRename e isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ subset_rfl) :=
    funext fun f ↦ weightedRenameAlgHom_apply e _ _ _ f
  exact h ▸ continuous_weightedRename e isWeightFamily_one_weight isWeightFamily_one_weight
    fun _ ↦ subset_rfl

@[simp]
theorem tateSeries.renameAlgHom_X {M : ℕ} (e : Fin N ↪ Fin M) (i : Fin N) :
    tateSeries.renameAlgHom e (tateSeries.X N A i) = tateSeries.X M A (e i) := by
  rw [tateSeries.renameAlgHom, weightedRenameAlgHom_apply, tateSeries.X, tateSeries.X]
  exact weightedRename_weightedX (T := fun _ : Fin N ↦ ({1} : Set A))
    (S := fun _ : Fin M ↦ ({1} : Set A)) (hT := isWeightFamily_one_weight)
    (hS := isWeightFamily_one_weight) e (fun _ ↦ subset_rfl) i

/-- **The identity law:** renaming along `Function.Embedding.refl` is the identity algebra
homomorphism. -/
@[simp]
theorem tateSeries.renameAlgHom_id :
    tateSeries.renameAlgHom (A := A) (Function.Embedding.refl (Fin N)) =
      AlgHom.id A (tateSeries N A) :=
  AlgHom.ext fun f ↦ by
    rw [AlgHom.id_apply, tateSeries.renameAlgHom, weightedRenameAlgHom_apply]
    exact RingHom.congr_fun (weightedRename_id isWeightFamily_one_weight) f

/-- **The composition law:** composing two variable renamings equals renaming along the composite
embedding. -/
@[simp]
theorem tateSeries.renameAlgHom_comp {M K : ℕ} (e₁ : Fin N ↪ Fin M) (e₂ : Fin M ↪ Fin K) :
    (tateSeries.renameAlgHom (A := A) e₂).comp (tateSeries.renameAlgHom e₁) =
      tateSeries.renameAlgHom (e₁.trans e₂) :=
  AlgHom.ext fun f ↦ by
    simp only [AlgHom.comp_apply, tateSeries.renameAlgHom, weightedRenameAlgHom_apply]
    exact (RingHom.congr_fun (weightedRename_comp e₁ e₂ isWeightFamily_one_weight
      isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ subset_rfl)
      (fun _ ↦ subset_rfl)) f).symm

/-- Variable renaming along `e : Fin N ↪ Fin M` preserves `tateSeriesPlus`. -/
theorem tateSeries.renameAlgHom_mem_tateSeriesPlus {M : ℕ} (e : Fin N ↪ Fin M)
    {Aplus : Subring A} {f : tateSeries N A} (hf : f ∈ tateSeriesPlus N A Aplus) :
    tateSeries.renameAlgHom e f ∈ tateSeriesPlus M A Aplus := by
  classical
  rw [mem_tateSeriesPlus_iff] at hf ⊢
  intro ν
  rw [tateSeries.coe_renameAlgHom]
  by_cases hdom : ν ∈ Set.range (Finsupp.mapDomain e)
  · obtain ⟨μ, rfl⟩ := hdom
    rw [← Finsupp.embDomain_eq_mapDomain e, MvPowerSeries.coeff_embDomain_rename]
    exact hf μ
  · rw [MvPowerSeries.coeff_rename_eq_zero e _ hdom]
    exact Aplus.zero_mem

/-- Partial differentiation at an embedded variable commutes with `tateSeries.renameAlgHom`. -/
@[simp]
theorem tateSeries.pderiv_renameAlgHom_apply {M : ℕ} (e : Fin N ↪ Fin M) (j : Fin N)
    (f : tateSeries N A) :
    tateSeries.pderiv (e j) (tateSeries.renameAlgHom e f) =
      tateSeries.renameAlgHom e (tateSeries.pderiv j f) := by
  apply Subtype.ext
  rw [tateSeries.coe_pderiv, tateSeries.coe_renameAlgHom, tateSeries.coe_renameAlgHom,
    tateSeries.coe_pderiv, MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.pderiv_subst (MvPowerSeries.HasSubst.X_comp e) _ (e j), Finset.sum_eq_single j]
  · simp [Function.comp_apply, MvPowerSeries.pderiv_X_self]
  · intro i _ hij
    simp [Function.comp_apply, MvPowerSeries.pderiv_X_of_ne (e.injective.ne hij)]
  · exact fun hj ↦ absurd (Finset.mem_univ j) hj

/-- Partial differentiation at a variable outside `Set.range e` annihilates
`tateSeries.renameAlgHom e f`. -/
theorem tateSeries.pderiv_renameAlgHom_of_notMem_range {M : ℕ} (e : Fin N ↪ Fin M) {m : Fin M}
    (hm : m ∉ Set.range e) (f : tateSeries N A) :
    tateSeries.pderiv m (tateSeries.renameAlgHom e f) = 0 := by
  apply Subtype.ext
  rw [tateSeries.coe_pderiv, tateSeries.coe_renameAlgHom, ZeroMemClass.coe_zero,
    MvPowerSeries.rename_eq_subst,
    MvPowerSeries.pderiv_subst (MvPowerSeries.HasSubst.X_comp e) _ m]
  exact Finset.sum_eq_zero fun j _ ↦ by
    simp [Function.comp_apply, MvPowerSeries.pderiv_X_of_ne (fun h ↦ hm ⟨j, h⟩)]

/-- **Inclusion `A⟨T₁, …, T_N⟩ →ₐ[A] A⟨T₁, …, T_N, S⟩` of the first `N` variables.** -/
noncomputable abbrev tateSeries.castSuccAlgHom :
    tateSeries N A →ₐ[A] tateSeries (N + 1) A :=
  tateSeries.renameAlgHom Fin.castSuccEmb

/-- A series depending only on the first `N` variables has zero derivative with respect to the last
variable `S = T_N`. -/
@[simp]
theorem tateSeries.pderiv_castSuccAlgHom_last (f : tateSeries N A) :
    tateSeries.pderiv (Fin.last N) (tateSeries.castSuccAlgHom f) = 0 :=
  tateSeries.pderiv_renameAlgHom_of_notMem_range Fin.castSuccEmb
    (by rintro ⟨i, hi⟩; exact Fin.castSucc_ne_last i hi) f

section Map

variable {B : Type*} [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B] {φ : A →+* B}

/-- **Coefficientwise functoriality on `tateSeries N`:** a continuous ring homomorphism
`φ : A →+* B` induces a continuous ring homomorphism `tateSeries N A →+* tateSeries N B`. -/
noncomputable def tateSeries.mapRingHom (hφ : Continuous φ) :
    tateSeries N A →+* tateSeries N B :=
  weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight fun _ ↦ by simp

@[simp]
theorem tateSeries.coe_mapRingHom (hφ : Continuous φ) (f : tateSeries N A) :
    (tateSeries.mapRingHom hφ f : MvPowerSeries (Fin N) B) =
      MvPowerSeries.map φ (f : MvPowerSeries (Fin N) A) :=
  coe_weightedMap hφ _ f

/-- `tateSeries.mapRingHom hφ` is continuous. -/
theorem tateSeries.continuous_mapRingHom (hφ : Continuous φ) :
    Continuous (tateSeries.mapRingHom (N := N) hφ) :=
  continuous_weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight fun _ ↦ by simp

@[simp]
theorem tateSeries.mapRingHom_weightedC (hφ : Continuous φ) (a : A) :
    tateSeries.mapRingHom (N := N) hφ
        (weightedC (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight a) =
      weightedC (fun _ : Fin N ↦ ({1} : Set B)) isWeightFamily_one_weight (φ a) :=
  weightedMap_weightedC hφ _ a

theorem tateSeries.mapRingHom_algebraMap (hφ : Continuous φ) (a : A) :
    tateSeries.mapRingHom (N := N) hφ (algebraMap A (tateSeries N A) a) =
      algebraMap B (tateSeries N B) (φ a) := by
  rw [algebraMap_weightedRestrictedSubring, algebraMap_weightedRestrictedSubring,
    tateSeries.mapRingHom_weightedC]

@[simp]
theorem tateSeries.mapRingHom_X (hφ : Continuous φ) (i : Fin N) :
    tateSeries.mapRingHom hφ (tateSeries.X N A i) = tateSeries.X N B i :=
  weightedMap_weightedX hφ _ i

/-- **The identity law:** the map induced by `RingHom.id A` is the identity ring homomorphism. -/
@[simp]
theorem tateSeries.mapRingHom_id :
    tateSeries.mapRingHom (N := N) (φ := RingHom.id A)
        (by simpa only [RingHom.coe_id] using continuous_id) =
      RingHom.id (tateSeries N A) :=
  weightedMap_id isWeightFamily_one_weight

/-- **The composition law:** composing two coefficientwise maps equals the map induced by the
composite ring homomorphism. -/
@[simp]
theorem tateSeries.mapRingHom_comp {C : Type*} [CommRing C] [TopologicalSpace C]
    [NonarchimedeanRing C] {ψ : B →+* C} (hφ : Continuous φ) (hψ : Continuous ψ) :
    (tateSeries.mapRingHom (N := N) hψ).comp (tateSeries.mapRingHom hφ) =
      tateSeries.mapRingHom (φ := ψ.comp φ)
        (by simpa only [RingHom.coe_comp] using hψ.comp hφ) :=
  (weightedMap_comp hφ hψ isWeightFamily_one_weight isWeightFamily_one_weight
    isWeightFamily_one_weight _ _).symm

/-- If `φ` maps `Aplus` into `Bplus`, then `tateSeries.mapRingHom hφ` maps
`tateSeriesPlus N A Aplus` into `tateSeriesPlus N B Bplus`. -/
theorem tateSeries.mapRingHom_mem_tateSeriesPlus (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hAB : ∀ a ∈ Aplus, φ a ∈ Bplus) {f : tateSeries N A}
    (hf : f ∈ tateSeriesPlus N A Aplus) :
    tateSeries.mapRingHom hφ f ∈ tateSeriesPlus N B Bplus := by
  rw [mem_tateSeriesPlus_iff] at hf ⊢
  exact fun ν ↦ by rw [tateSeries.coe_mapRingHom, MvPowerSeries.coeff_map]; exact hAB _ (hf ν)

/-- Formal partial differentiation commutes with `tateSeries.mapRingHom`. -/
@[simp]
theorem tateSeries.pderiv_mapRingHom (hφ : Continuous φ) (j : Fin N) (f : tateSeries N A) :
    tateSeries.pderiv j (tateSeries.mapRingHom hφ f) =
      tateSeries.mapRingHom hφ (tateSeries.pderiv j f) := by
  apply Subtype.ext; ext ν; simp [MvPowerSeries.coeff_pderiv]

/-- The formal Jacobian matrix commutes entrywise with `tateSeries.mapRingHom`. -/
@[simp]
theorem tateSeries.jacobianMatrix_mapRingHom (hφ : Continuous φ) (F : Fin N → tateSeries N A) :
    tateSeries.jacobianMatrix (fun i ↦ tateSeries.mapRingHom hφ (F i)) =
      (tateSeries.jacobianMatrix F).map (tateSeries.mapRingHom hφ) := by
  ext i j
  simp

/-- The formal Jacobian determinant commutes with `tateSeries.mapRingHom`. -/
@[simp]
theorem tateSeries.jacobian_mapRingHom (hφ : Continuous φ) (F : Fin N → tateSeries N A) :
    tateSeries.jacobian (fun i ↦ tateSeries.mapRingHom hφ (F i)) =
      tateSeries.mapRingHom hφ (tateSeries.jacobian F) := by
  rw [tateSeries.jacobian_def, tateSeries.jacobianMatrix_mapRingHom, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, tateSeries.jacobian_def]

end Map

/-- **Rescaling a restricted series into an open subring:** if `ϖ` is topologically nilpotent and
`Aplus` is an open subring of `A`, then every `f : tateSeries N A` satisfies
`ϖ ^ m • f ∈ tateSeriesPlus N A Aplus` for some `m : ℕ`. -/
theorem exists_pow_smul_mem_tateSeriesPlus {Aplus : Subring A}
    (hopen : IsOpen (Aplus : Set A)) {ϖ : A} (hϖ : IsTopologicallyNilpotent ϖ)
    (f : tateSeries N A) :
    ∃ m : ℕ, ϖ ^ m • f ∈ tateSeriesPlus N A Aplus := by
  obtain ⟨m, hm⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent
    (hϖ.map (continuous_weightedC isWeightFamily_one_weight))
    (isOpen_weightedSubring isWeightFamily_one_weight hopen) f
  refine ⟨m, ?_⟩
  rw [Algebra.smul_def, mul_comm, algebraMap_weightedRestrictedSubring, map_pow]
  exact hm

end Nonarchimedean

section HuberPair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- **The uncompleted unit-weight restricted power-series Huber pair `(A⟨T⟩, A⁺⟨T⟩)`** over a Huber
pair `S = (A, A⁺)`. -/
noncomputable def tateSeriesPair (N : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] (S : Pair A) : Pair (tateSeries N A) :=
  S.weighted (k := N) isWeightFamily_one_weight

/-- The plus ring of `tateSeriesPair N A S` is `tateSeriesPlus N A S.plus` on the nose, with no
integral closure needed. -/
@[simp]
theorem tateSeriesPair_plus (N : ℕ) (S : Pair A) :
    (tateSeriesPair N A S).plus = tateSeriesPlus N A S.plus :=
  Pair.weighted_plus_one_weight S

/-- **Comparison with `Pair.polydiscPlus`:** when `tateSeries N A` is complete and Hausdorff, the
inverse completion equivalence `(restrictedMvPowerSeriesCompletionEquiv N A).symm` maps
`tateSeriesPlus N A S.plus` onto `S.polydiscPlus N`. -/
theorem map_symm_tateSeriesPlus_eq_polydiscPlus (N : ℕ) (S : Pair A)
    [CompleteSpace (tateSeries N A)] [T0Space (tateSeries N A)] :
    (tateSeriesPlus N A S.plus).map
        ((restrictedMvPowerSeriesCompletionEquiv N A).symm :
          tateSeries N A →+* restrictedMvPowerSeriesCompletion N A) =
      S.polydiscPlus N := by
  dsimp only [tateSeriesPlus]
  rw [← S.map_polydiscPlus_equiv N, Subring.map_map]
  ext x; simp

omit [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] in
/-- A tuple of elements in the plus ring `Bplus.plus` is unit-weight bounded along any ring
homomorphism `φ : A →+* B`. -/
theorem isWeightBounded_one_weight_of_mem_plus {N : ℕ} {B : Type*} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] (φ : A →+* B) (Bplus : Pair B)
    {u : Fin N → B} (hu : ∀ i, u i ∈ Bplus.plus) :
    IsWeightBounded φ (fun _ : Fin N ↦ ({1} : Set A)) u :=
  (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun i ↦
    Bplus.isRingOfIntegralElements.isPowerBounded_of_mem (hu i)

/-- A continuous ring homomorphism `tateSeries N A →+* B` mapping `Aplus.plus` (via constants) and
every coordinate `tateSeries.X N A i` into `Bplus.plus` carries all of
`tateSeriesPlus N A Aplus.plus` into `Bplus.plus`. -/
theorem tateSeriesPlus_map_le_of_continuous {N : ℕ} {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsHuberRing B] (Aplus : Pair A) (Bplus : Pair B)
    {ψ : tateSeries N A →+* B} (hψ : Continuous ψ)
    (hA : ∀ a ∈ Aplus.plus, ψ (algebraMap A (tateSeries N A) a) ∈ Bplus.plus)
    (hX : ∀ i, ψ (tateSeries.X N A i) ∈ Bplus.plus) :
    (tateSeriesPlus N A Aplus.plus).map ψ ≤ Bplus.plus := by
  rw [Subring.map_le_iff_le_comap]
  exact le_trans (Pair.weighted_plus_one_weight (k := N) Aplus).symm.le
    (Aplus.weighted_plus_le_comap isWeightFamily_one_weight Bplus hψ
      (fun a ha ↦ by simpa only [← algebraMap_weightedRestrictedSubring] using hA a ha)
      (fun i t ht ↦ by
        obtain rfl : t = 1 := Set.mem_singleton_iff.mp ht
        simpa only [map_one, one_mul, ← tateSeries.X_eq_weightedX] using hX i))

end HuberPair

end TauCeti.Huber

end
