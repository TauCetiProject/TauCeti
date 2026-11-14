/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PDeriv
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Rename

import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.GaussValuation
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.NonUnit
import TauCeti.RingTheory.MvPowerSeries.Derivative

/-!
# Restricted power-series rings `A⟨T₁, …, T_N⟩` and coefficient plus subrings

Over a nonarchimedean commutative ring `A`, `TauCeti.Huber.tateSeries N A` is the ring of
restricted power series in `N` variables — the specialization of
`TauCeti.Huber.weightedRestrictedSubring` to the trivial weight family `Tᵢ = {1}`, with coordinate
variables `TauCeti.Huber.tateSeries.X` and coefficientwise subring
`TauCeti.Huber.tateSeriesPlus N A Aplus` consisting of restricted series whose coefficients lie in
`Aplus`.

When `A` is complete and Hausdorff, `tateSeries N A` is already complete and Hausdorff
(`TauCeti.Huber.completeSpace_weightedRestrictedSubring_one_weight`,
`TauCeti.Huber.t0Space_weightedRestrictedSubring_one_weight`), so
`TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv` identifies the completed polydisc ring
`restrictedMvPowerSeriesCompletion N A` with `tateSeries N A`. Working directly on `tateSeries N A`
retains access to formal partial derivatives `MvPowerSeries.pderiv` on the underlying power series,
which preserve restrictedness (`TauCeti.Huber.IsWeightedRestricted.pderiv_one_weight`) and carry
`tateSeriesPlus N A Aplus` into itself.

For a Huber pair `S = (A, A⁺)`, `TauCeti.Huber.tateSeriesPair N A S` is the uncompleted unit-weight
Huber pair `S.weighted isWeightFamily_one_weight`, whose plus ring equals
`tateSeriesPlus N A S.plus` with no integral closure needed
(`TauCeti.Huber.tateSeriesPair_plus`). When `tateSeries N A` is complete and Hausdorff, the inverse
completion comparison `(restrictedMvPowerSeriesCompletionEquiv N A).symm` maps
`tateSeriesPlus N A S.plus` onto `S.polydiscPlus N`
(`TauCeti.Huber.map_symm_tateSeriesPlus_eq_polydiscPlus`) and sends each `tateSeries.X N A i` to
`Pair.polydiscVar N A i`.

## Main definitions

* `TauCeti.Huber.tateSeries`: the restricted power-series ring `A⟨T₁, …, T_N⟩` at unit weights.
* `TauCeti.Huber.tateSeries.X`: the `i`-th coordinate variable `Tᵢ ∈ A⟨T₁, …, T_N⟩`.
* `TauCeti.Huber.tateSeries.pderiv`: formal partial derivative `∂/∂Tⱼ` on `tateSeries N A`.
* `TauCeti.Huber.tateSeries.renameAlgHom` and `TauCeti.Huber.tateSeries.castSuccAlgHom`: variable
  renaming along `Fin N ↪ Fin M` and inclusion of the first `N` variables into `N + 1` variables.
* `TauCeti.Huber.tateSeries.mapRingHom`: coefficientwise continuous ring homomorphism
  `tateSeries N A →+* tateSeries N B` induced by a continuous ring homomorphism `A →+* B`.
* `TauCeti.Huber.tateSeriesPlus`: the subring `A⁺⟨T₁, …, T_N⟩` of restricted series with
  coefficients in a subring `A⁺ ⊆ A`.
* `TauCeti.Huber.tateSeriesPair`: the Huber pair `(A⟨T⟩, A⁺⟨T⟩)` attached to a Huber pair
  `S = (A, A⁺)`.

## Main results

* `TauCeti.Huber.mem_tateSeriesPlus_iff` and `TauCeti.Huber.tateSeriesPlus_eq_weightedSubring`:
  `f ∈ tateSeriesPlus N A Aplus` iff every coefficient of `f` lies in `Aplus`.
* `TauCeti.Huber.tateSeries.pderiv_mem_tateSeriesPlus`: `∂/∂Tⱼ` preserves `tateSeriesPlus`.
* `TauCeti.Huber.map_symm_tateSeriesPlus_eq_polydiscPlus`: `(restrictedMvPowerSeriesCompletionEquiv
  N A).symm` identifies `tateSeriesPlus N A S.plus` with `S.polydiscPlus N`.
* `TauCeti.Huber.exists_pow_smul_mem_tateSeriesPlus`: over a Huber ring with a topologically
  nilpotent element `ϖ` and an open subring `Aplus`, every restricted series is scaled into
  `tateSeriesPlus` by a power of `ϖ`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Example 5.54, Proposition 5.49, and Example 7.57.
* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, Vieweg (1996), §1.7.
* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343v3, §6 and §24.
-/

public section

open Filter Topology UniformSpace

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
noncomputable def tateSeriesPlus (Aplus : Subring A) : Subring (tateSeries N A) :=
  (MvPowerSeries.map Aplus.subtype).range.comap (Subring.subtype _)

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
    dsimp only
    have hsmul : ((a • f : tateSeries N A) : MvPowerSeries (Fin N) A) =
        a • (f : MvPowerSeries (Fin N) A) := by
      rw [Algebra.smul_def, MulMemClass.coe_mul, tateSeries.coe_algebraMap,
        MvPowerSeries.smul_eq_C_mul]
    have hsmul' : ((a • ⟨MvPowerSeries.pderiv j (f : MvPowerSeries (Fin N) A),
          mem_weightedRestrictedSubring.mpr
            ((mem_weightedRestrictedSubring.mp f.2).pderiv_one_weight j)⟩ : tateSeries N A) :
        MvPowerSeries (Fin N) A) = a • MvPowerSeries.pderiv j (f : MvPowerSeries (Fin N) A) := by
      rw [Algebra.smul_def, MulMemClass.coe_mul, tateSeries.coe_algebraMap,
        MvPowerSeries.smul_eq_C_mul]
    rw [RingHom.id_apply, hsmul, hsmul', (MvPowerSeries.pderiv j).map_smul]

@[simp]
theorem tateSeries.coe_pderiv (j : Fin N) (f : tateSeries N A) :
    (tateSeries.pderiv j f : MvPowerSeries (Fin N) A) =
      MvPowerSeries.pderiv j (f : MvPowerSeries (Fin N) A) :=
  (rfl)

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
  rw [tateSeriesPlus, Subring.mem_comap, Subring.subtype_apply, RingHom.mem_range]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨g, hg⟩ ν
    rw [← hg, MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff ν g).2
  · let g : MvPowerSeries (Fin N) Aplus :=
      fun ν ↦ ⟨MvPowerSeries.coeff ν (f : MvPowerSeries (Fin N) A), h ν⟩
    refine ⟨g, MvPowerSeries.ext fun ν ↦ ?_⟩
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_apply]
    rfl

/-- **`tateSeriesPlus N A Aplus` coincides with `weightedSubring` at the trivial weight `{1}`.** -/
theorem tateSeriesPlus_eq_weightedSubring (Aplus : Subring A) :
    tateSeriesPlus N A Aplus =
      weightedSubring (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight Aplus := by
  ext f
  simp [mem_tateSeriesPlus_iff, mem_weightedSubring, mem_weightedNhd, weightMul_one_weight]

@[simp]
theorem tateSeriesPlus_top : tateSeriesPlus N A ⊤ = ⊤ := by
  ext f
  simp [mem_tateSeriesPlus_iff]

@[simp]
theorem weightedC_mem_tateSeriesPlus_iff {Aplus : Subring A} {a : A} :
    weightedC (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight a ∈
        tateSeriesPlus N A Aplus ↔ a ∈ Aplus := by
  rw [tateSeriesPlus_eq_weightedSubring, weightedC_mem_weightedSubring]

theorem algebraMap_mem_tateSeriesPlus_iff {Aplus : Subring A} {a : A} :
    algebraMap A (tateSeries N A) a ∈ tateSeriesPlus N A Aplus ↔ a ∈ Aplus := by
  rw [algebraMap_weightedRestrictedSubring, weightedC_mem_tateSeriesPlus_iff]

@[simp]
theorem tateSeries.X_mem_tateSeriesPlus (Aplus : Subring A) (i : Fin N) :
    tateSeries.X N A i ∈ tateSeriesPlus N A Aplus := by
  simpa [tateSeriesPlus_eq_weightedSubring, tateSeries.X_eq_weightedX] using
    weightedC_mul_weightedX_mem_weightedSubring (T := fun _ : Fin N ↦ ({1} : Set A))
      (hT := isWeightFamily_one_weight) (R := Aplus) (i := i) (Set.mem_singleton (1 : A))

/-- Formal partial differentiation preserves `tateSeriesPlus`. -/
theorem tateSeries.pderiv_mem_tateSeriesPlus {Aplus : Subring A} {f : tateSeries N A}
    (hf : f ∈ tateSeriesPlus N A Aplus) (j : Fin N) :
    tateSeries.pderiv j f ∈ tateSeriesPlus N A Aplus := by
  rw [mem_tateSeriesPlus_iff] at hf ⊢
  exact MvPowerSeries.coeff_pderiv_mem hf j

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
      weightedRename e isWeightFamily_one_weight isWeightFamily_one_weight
        (fun _ ↦ subset_rfl) :=
    funext fun f ↦ weightedRenameAlgHom_apply e _ _ _ f
  rw [h]
  exact continuous_weightedRename e isWeightFamily_one_weight isWeightFamily_one_weight
    fun _ ↦ subset_rfl

@[simp]
theorem tateSeries.renameAlgHom_X {M : ℕ} (e : Fin N ↪ Fin M) (i : Fin N) :
    tateSeries.renameAlgHom e (tateSeries.X N A i) = tateSeries.X M A (e i) := by
  rw [tateSeries.renameAlgHom, weightedRenameAlgHom_apply, tateSeries.X, tateSeries.X]
  exact weightedRename_weightedX (T := fun _ : Fin N ↦ ({1} : Set A))
    (S := fun _ : Fin M ↦ ({1} : Set A)) (hT := isWeightFamily_one_weight)
    (hS := isWeightFamily_one_weight) e (fun _ ↦ subset_rfl) i

/-- Variable renaming along `e : Fin N ↪ Fin M` preserves `tateSeriesPlus`. -/
theorem tateSeries.renameAlgHom_mem_tateSeriesPlus {M : ℕ} (e : Fin N ↪ Fin M)
    {Aplus : Subring A} {f : tateSeries N A} (hf : f ∈ tateSeriesPlus N A Aplus) :
    tateSeries.renameAlgHom e f ∈ tateSeriesPlus M A Aplus := by
  rw [mem_tateSeriesPlus_iff] at hf ⊢
  intro ν
  rw [tateSeries.coe_renameAlgHom]
  classical
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
  have ha : MvPowerSeries.HasSubst (MvPowerSeries.X (R := A) ∘ e) :=
    MvPowerSeries.HasSubst.X_comp e
  rw [tateSeries.coe_pderiv, tateSeries.coe_renameAlgHom, tateSeries.coe_renameAlgHom,
    tateSeries.coe_pderiv, MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.pderiv_subst ha _ (e j), Finset.sum_eq_single j]
  · simp [Function.comp_apply, MvPowerSeries.pderiv_X_self]
  · intro i _ hij
    have heij : e i ≠ e j := e.injective.ne hij
    simp [Function.comp_apply, MvPowerSeries.pderiv_X_of_ne heij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Partial differentiation at a variable outside `Set.range e` annihilates
`tateSeries.renameAlgHom e f`. -/
theorem tateSeries.pderiv_renameAlgHom_of_notMem_range {M : ℕ} (e : Fin N ↪ Fin M) {m : Fin M}
    (hm : m ∉ Set.range e) (f : tateSeries N A) :
    tateSeries.pderiv m (tateSeries.renameAlgHom e f) = 0 := by
  apply Subtype.ext
  have ha : MvPowerSeries.HasSubst (MvPowerSeries.X (R := A) ∘ e) :=
    MvPowerSeries.HasSubst.X_comp e
  rw [tateSeries.coe_pderiv, tateSeries.coe_renameAlgHom, ZeroMemClass.coe_zero,
    MvPowerSeries.rename_eq_subst, MvPowerSeries.pderiv_subst ha _ m]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have hne : e j ≠ m := fun h ↦ hm ⟨j, h⟩
  simp [Function.comp_apply, MvPowerSeries.pderiv_X_of_ne hne]

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

/-- **Coefficientwise functoriality on `tateSeries N`:** a continuous ring homomorphism
`φ : A →+* B` induces a continuous ring homomorphism `tateSeries N A →+* tateSeries N B`. -/
noncomputable def tateSeries.mapRingHom {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) :
    tateSeries N A →+* tateSeries N B :=
  weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight
    fun _ ↦ by simp

@[simp]
theorem tateSeries.coe_mapRingHom {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) (f : tateSeries N A) :
    (tateSeries.mapRingHom hφ f : MvPowerSeries (Fin N) B) =
      MvPowerSeries.map φ (f : MvPowerSeries (Fin N) A) :=
  coe_weightedMap hφ _ f

/-- `tateSeries.mapRingHom hφ` is continuous. -/
theorem tateSeries.continuous_mapRingHom {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) :
    Continuous (tateSeries.mapRingHom (N := N) hφ) :=
  continuous_weightedMap hφ isWeightFamily_one_weight isWeightFamily_one_weight
    fun _ ↦ by simp

@[simp]
theorem tateSeries.mapRingHom_weightedC {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) (a : A) :
    tateSeries.mapRingHom (N := N) hφ
        (weightedC (fun _ : Fin N ↦ ({1} : Set A)) isWeightFamily_one_weight a) =
      weightedC (fun _ : Fin N ↦ ({1} : Set B)) isWeightFamily_one_weight (φ a) :=
  Subtype.ext (by simp [MvPowerSeries.map_C])

theorem tateSeries.mapRingHom_algebraMap {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) (a : A) :
    tateSeries.mapRingHom (N := N) hφ (algebraMap A (tateSeries N A) a) =
      algebraMap B (tateSeries N B) (φ a) := by
  rw [algebraMap_weightedRestrictedSubring, algebraMap_weightedRestrictedSubring,
    tateSeries.mapRingHom_weightedC]

@[simp]
theorem tateSeries.mapRingHom_X {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) (i : Fin N) :
    tateSeries.mapRingHom hφ (tateSeries.X N A i) = tateSeries.X N B i :=
  Subtype.ext (by simp)

/-- If `φ` maps `Aplus` into `Bplus`, then `tateSeries.mapRingHom hφ` maps
`tateSeriesPlus N A Aplus` into `tateSeriesPlus N B Bplus`. -/
theorem tateSeries.mapRingHom_mem_tateSeriesPlus {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) {Aplus : Subring A}
    {Bplus : Subring B} (hAB : ∀ a ∈ Aplus, φ a ∈ Bplus) {f : tateSeries N A}
    (hf : f ∈ tateSeriesPlus N A Aplus) :
    tateSeries.mapRingHom hφ f ∈ tateSeriesPlus N B Bplus := by
  rw [mem_tateSeriesPlus_iff] at hf ⊢
  intro ν
  rw [tateSeries.coe_mapRingHom, MvPowerSeries.coeff_map]
  exact hAB _ (hf ν)

/-- Formal partial differentiation commutes with `tateSeries.mapRingHom`. -/
@[simp]
theorem tateSeries.pderiv_mapRingHom {B : Type*} [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {φ : A →+* B} (hφ : Continuous φ) (j : Fin N) (f : tateSeries N A) :
    tateSeries.pderiv j (tateSeries.mapRingHom hφ f) =
      tateSeries.mapRingHom hφ (tateSeries.pderiv j f) := by
  apply Subtype.ext
  ext ν
  simp [MvPowerSeries.coeff_pderiv]

/-- **Rescaling a restricted series into an open subring:** if `ϖ` is topologically nilpotent and
`Aplus` is an open subring of `A`, then every `f : tateSeries N A` satisfies
`ϖ ^ m • f ∈ tateSeriesPlus N A Aplus` for some `m : ℕ`. -/
theorem exists_pow_smul_mem_tateSeriesPlus {Aplus : Subring A}
    (hopen : IsOpen (Aplus : Set A)) {ϖ : A} (hϖ : IsTopologicallyNilpotent ϖ)
    (f : tateSeries N A) :
    ∃ m : ℕ, ϖ ^ m • f ∈ tateSeriesPlus N A Aplus := by
  classical
  let U : OpenAddSubgroup A := ⟨Aplus.toAddSubgroup, hopen⟩
  have hbad := (mem_weightedRestrictedSubring.mp f.2).finite_coeff_notMem U
  have hnhds : (Aplus : Set A) ∈ nhds (0 : A) := hopen.mem_nhds Aplus.zero_mem
  have hev : ∀ ν : hbad.toFinset, ∀ᶠ m in atTop,
      ϖ ^ m * MvPowerSeries.coeff ν.1 (f : MvPowerSeries (Fin N) A) ∈ Aplus := fun ν ↦ by
    have hlim : Tendsto (fun m ↦ ϖ ^ m * MvPowerSeries.coeff ν.1 (f : MvPowerSeries (Fin N) A))
        atTop (nhds 0) := by
      simpa using hϖ.mul_const (MvPowerSeries.coeff ν.1 (f : MvPowerSeries (Fin N) A))
    exact hlim.eventually hnhds
  obtain ⟨m, hm⟩ := ((Filter.eventually_all.mpr hev).and (hϖ.eventually hnhds)).exists
  refine ⟨m, mem_tateSeriesPlus_iff.mpr fun ν ↦ ?_⟩
  rw [Algebra.smul_def, MulMemClass.coe_mul, tateSeries.coe_algebraMap, MvPowerSeries.coeff_C_mul]
  by_cases hν : ν ∈ hbad.toFinset
  · exact hm.1 ⟨ν, hν⟩
  · have hmemU : MvPowerSeries.coeff ν (f : MvPowerSeries (Fin N) A) ∈
        weightMul (fun _ : Fin N ↦ ({1} : Set A)) ν U.toAddSubgroup :=
      not_not.mp fun h ↦ hν (hbad.mem_toFinset.mpr h)
    rw [weightMul_one_weight] at hmemU
    have hmemAplus : MvPowerSeries.coeff ν (f : MvPowerSeries (Fin N) A) ∈ Aplus := hmemU
    rcases m.eq_zero_or_pos with rfl | _
    · simpa using hmemAplus
    · exact Aplus.mul_mem hm.2 hmemAplus

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
    (tateSeriesPair N A S).plus = tateSeriesPlus N A S.plus := by
  rw [tateSeriesPair, Pair.weighted_plus_one_weight, tateSeriesPlus_eq_weightedSubring]

/-- **Comparison with `Pair.polydiscPlus`:** when `tateSeries N A` is complete and Hausdorff, the
inverse completion equivalence `(restrictedMvPowerSeriesCompletionEquiv N A).symm` maps
`tateSeriesPlus N A S.plus` onto `S.polydiscPlus N`. -/
theorem map_symm_tateSeriesPlus_eq_polydiscPlus (N : ℕ) (S : Pair A)
    [CompleteSpace (tateSeries N A)] [T0Space (tateSeries N A)] :
    (tateSeriesPlus N A S.plus).map
        ((restrictedMvPowerSeriesCompletionEquiv N A).symm :
          tateSeries N A →+* restrictedMvPowerSeriesCompletion N A) =
      S.polydiscPlus N := by
  rw [tateSeriesPlus_eq_weightedSubring, ← S.map_polydiscPlus_equiv N, Subring.map_map]
  ext x
  simp

end HuberPair

/-! ### Sanity checks for `tateSeries.X` and `tateSeriesPlus` -/

section Checks

-- `tateSeries_X_coe`: as a power series, `Tᵢ` is `MvPowerSeries.X i`.
example {N : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] (i : Fin N) :
    (tateSeries.X N A i : MvPowerSeries (Fin N) A) = MvPowerSeries.X i :=
  tateSeries.coe_X i

-- `tateSeries_X_own_coefficient`: over `ℚ_[2]` in two variables, `coeff (single 0 1) (X 0) = 1`.
example [Fact (Nat.Prime 2)] :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
      (tateSeries.X 2 ℚ_[2] 0 : MvPowerSeries (Fin 2) ℚ_[2]) = 1 := by
  simp

-- `tateSeries_X_other_coefficient`: `coeff (single 1 1) (X 0) = 0`.
example [Fact (Nat.Prime 2)] :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
      (tateSeries.X 2 ℚ_[2] 0 : MvPowerSeries (Fin 2) ℚ_[2]) = 0 := by
  rw [tateSeries.coe_X, MvPowerSeries.coeff_X, ite_eq_right_iff]
  intro h
  have h0 := congrArg (fun ν : Fin 2 →₀ ℕ ↦ ν 0) h
  simp at h0

-- `tateSeries_X_sum_constant`: `coeff 0 (X 0 + X 1) = 0`.
example [Fact (Nat.Prime 2)] :
    MvPowerSeries.coeff 0
      ((tateSeries.X 2 ℚ_[2] 0 + tateSeries.X 2 ℚ_[2] 1 : tateSeries 2 ℚ_[2]) :
        MvPowerSeries (Fin 2) ℚ_[2]) = 0 := by
  simp

-- `tateSeries_X_not_isUnit`: over a nonzero `A`, `Tᵢ` is not a unit of `A⟨T⟩`.
example {N : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] [Nontrivial A]
    (i : Fin N) : ¬IsUnit (tateSeries.X N A i) :=
  tateSeries.not_isUnit_X i

-- `tateSeriesPlus_constant` & `tateSeriesPlus_inverse_constant`: over `(ℚ_[p], ℤ_[p])`, `p` lies in
-- `ℤ_[p]⟨T⟩` whereas `p⁻¹` does not.
example (p : ℕ) [hp : Fact p.Prime] (N : ℕ) :
    algebraMap ℚ_[p] (tateSeries N ℚ_[p]) p ∈ tateSeriesPlus N ℚ_[p] (_root_.PadicInt.subring p) ∧
      algebraMap ℚ_[p] (tateSeries N ℚ_[p]) (p : ℚ_[p])⁻¹ ∉
        tateSeriesPlus N ℚ_[p] (_root_.PadicInt.subring p) := by
  rw [algebraMap_mem_tateSeriesPlus_iff, algebraMap_mem_tateSeriesPlus_iff]
  refine ⟨natCast_mem (_root_.PadicInt.subring p) p, fun h ↦ ?_⟩
  have hnorm : ‖((p : ℚ_[p])⁻¹)‖ ≤ 1 := h
  rw [norm_inv, _root_.Padic.norm_p, inv_inv] at hnorm
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  linarith

end Checks

end TauCeti.Huber

end
