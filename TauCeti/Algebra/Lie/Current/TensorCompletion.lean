/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.HahnModule
public import TauCeti.Algebra.Category.ModuleCat.Tower.Quotient

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# The inverse limit of current order quotients

The compatible-family completion of tensor currents `R((t)) ⊗[R] V` is the space of
`V`-valued Laurent series, including when `V` is not finitely generated. The comparison
is a linear homeomorphism and sends the family of classes of a tensor current to its
coefficient series. Its filtration is exactly the Laurent lattice filtration.

Each order quotient agrees with the corresponding quotient of vector-valued series:
density supplies surjectivity, and coefficientwise vanishing supplies injectivity.
The complete Hausdorff lattice topology then identifies the compatible families with
series. No basis, freeness or finite-generation hypothesis is required.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3.1, for the order topology
  and finite-dimensional current comparison.
-/

public section

noncomputable section

open Filter Topology
open scoped TensorProduct LaurentSeries

namespace TauCeti.CurrentAlgebra

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

-- Match the coefficientwise scalar action of tensor currents.
attribute [local instance 1100] HahnSeries.instAlgebra

/-- The current order filtration decreases on natural-number cutoffs. -/
theorem orderSubmodule_natCast_antitone :
    Antitone (fun n : ℕ ↦ orderSubmodule R V (n : ℤ)) :=
  fun _ _ h ↦ orderSubmodule_antitone R V (by exact_mod_cast h)

/-- The tower of current modules modulo the decreasing order filtration. Its indices are
cofinal among all integer cutoffs. -/
abbrev currentOrderTower : ModuleTower R :=
  ModuleTower.quotients (fun n : ℕ ↦ orderSubmodule R V (n : ℤ))
    (orderSubmodule_natCast_antitone R V)

/-- The coefficient map induces an equivalence on every order quotient, even for nonfree
coefficient modules. -/
def orderQuotientHahnModuleEquiv (N : ℕ) :
    (currentOrderTower R V).obj (Opposite.op N) ≃ₗ[R]
      (_root_.HahnModule ℤ R V ⧸ HahnModule.lattice R V N) := by
  let f := (HahnModule.lattice R V N).mkQ.comp
    ((_root_.HahnModule.tensorProductToHahnModule ℤ R V).restrictScalars R)
  have hker : LinearMap.ker f = orderSubmodule R V N := by
    ext u
    simp [f]
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      have hU : {y | y - x ∈ HahnModule.lattice R V N} ∈ 𝓝 x := by
        rw [← nhds_translation_sub x]
        exact preimage_mem_comap (HahnModule.lattice_mem_nhds_zero R V N)
      obtain ⟨_, hu, u, rfl⟩ := mem_closure_iff_nhds.mp
        (denseRange_tensorProductToHahnModule R V x) _ hU
      exact ⟨u, (Submodule.Quotient.eq _).mpr hu⟩
  exact ModuleTower.quotientsLiftEquiv _ _ N f hker hsurj

/-- On representatives the quotient comparison is the coefficient map. -/
@[simp]
theorem orderQuotientHahnModuleEquiv_mk (N : ℕ) (u : currentAlgebra R V) :
    orderQuotientHahnModuleEquiv R V N
      (ModuleTower.quotientsπ _ (orderSubmodule_natCast_antitone R V) N u) =
      Submodule.Quotient.mk (_root_.HahnModule.tensorProductToHahnModule ℤ R V u) := by
  exact ModuleTower.quotientsLiftEquiv_quotientsπ _ _ N _ _ _ u

/-- The class of a vector-valued Laurent series in the tensor-current quotient at order `N`.
This is the inverse of the coefficient comparison on quotients. -/
def hahnModuleOrderClass (N : ℕ) :
    _root_.HahnModule ℤ R V →ₗ[R] (currentOrderTower R V).obj (Opposite.op N) :=
  (orderQuotientHahnModuleEquiv R V N).symm.toLinearMap.comp
    (HahnModule.lattice R V N).mkQ

/-- The quotient comparison sends a series' order class to its Laurent lattice class. -/
@[simp]
theorem orderQuotientHahnModuleEquiv_hahnModuleOrderClass (N : ℕ)
    (x : _root_.HahnModule ℤ R V) :
    orderQuotientHahnModuleEquiv R V N (hahnModuleOrderClass R V N x) =
      Submodule.Quotient.mk x := by
  simp [hahnModuleOrderClass]

/-- The order class of a tensor's coefficient series is its tensor-current class. -/
@[simp]
theorem hahnModuleOrderClass_tensor (N : ℕ) (u : currentAlgebra R V) :
    hahnModuleOrderClass R V N (_root_.HahnModule.tensorProductToHahnModule ℤ R V u) =
      ModuleTower.quotientsπ _ (orderSubmodule_natCast_antitone R V) N u := by
  apply (orderQuotientHahnModuleEquiv R V N).injective
  simp

/-- Taking a lower order class commutes with the quotient transition. -/
@[simp]
theorem transitionOfLE_hahnModuleOrderClass {M N : ℕ} (h : M ≤ N)
    (x : _root_.HahnModule ℤ R V) :
    (currentOrderTower R V).transitionOfLE h (hahnModuleOrderClass R V N x) =
      hahnModuleOrderClass R V M x := by
  apply (orderQuotientHahnModuleEquiv R V M).injective
  obtain ⟨u, hu⟩ := ModuleTower.quotientsπ_surjective _
    (orderSubmodule_natCast_antitone R V) N (hahnModuleOrderClass R V N x)
  have hx : _root_.HahnModule.tensorProductToHahnModule ℤ R V u - x ∈
      HahnModule.lattice R V N := by
    apply (Submodule.Quotient.eq _).mp
    simpa using
      congrArg (orderQuotientHahnModuleEquiv R V N) hu
  rw [← hu, ModuleTower.transitionOfLE_quotientsπ, orderQuotientHahnModuleEquiv_mk]
  simpa using
    (Submodule.Quotient.eq (HahnModule.lattice R V M)).mpr
      (HahnModule.lattice_antitone R V (by exact_mod_cast h) hx)

/-- A series has zero order class exactly when its coefficients below the cutoff vanish. -/
@[simp]
theorem hahnModuleOrderClass_eq_zero_iff (N : ℕ) (x : _root_.HahnModule ℤ R V) :
    hahnModuleOrderClass R V N x = 0 ↔ x ∈ HahnModule.lattice R V N := by
  rw [← (orderQuotientHahnModuleEquiv R V N).map_eq_zero_iff]
  simp

/-- A vector-valued Laurent series gives compatible classes in all tensor-current order
quotients. -/
def hahnModuleToOrderCompletion : _root_.HahnModule ℤ R V →ₗ[R] (currentOrderTower R V).lim :=
  (currentOrderTower R V).limLift (fun n ↦ hahnModuleOrderClass R V n) fun n ↦ by
    ext x
    -- The tower transition is the quotient factor map.
    rw [← ModuleTower.transitionOfLE_succ]
    exact transitionOfLE_hahnModuleOrderClass R V (Nat.le_succ n) x

/-- The `n`th coordinate of the comparison is the order-`n` class. -/
@[simp]
theorem coe_hahnModuleToOrderCompletion_apply (n : ℕ) (x : _root_.HahnModule ℤ R V) :
    (hahnModuleToOrderCompletion R V x : (currentOrderTower R V).Product) n =
      hahnModuleOrderClass R V n x :=
  (currentOrderTower R V).coe_limLift_apply _ _ x n

/-- The compatible classes of a tensor current are those of its coefficient series. -/
@[simp]
theorem hahnModuleToOrderCompletion_tensor (u : currentAlgebra R V) :
    hahnModuleToOrderCompletion R V (_root_.HahnModule.tensorProductToHahnModule ℤ R V u) =
      ModuleTower.toLimQuotients _ (orderSubmodule_natCast_antitone R V) u := by
  apply (currentOrderTower R V).lim_ext
  intro n
  rw [ModuleTower.limπ_apply, coe_hahnModuleToOrderCompletion_apply, hahnModuleOrderClass_tensor,
    ← LinearMap.comp_apply, ModuleTower.limπ_comp_toLimQuotients]

/-- The compatible-class map preserves and reflects the Laurent lattice topology. -/
theorem isInducing_hahnModuleToOrderCompletion :
    IsInducing (hahnModuleToOrderCompletion R V) := by
  apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
  apply (HahnModule.hasBasis_nhds_zero_lattice R V).eq_of_same_basis
  have hpre (n : ℕ) :
      (hahnModuleToOrderCompletion R V) ⁻¹'
          (LinearMap.ker ((currentOrderTower R V).limπ n) : Set _) =
        (HahnModule.lattice R V n : Set _) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, ModuleTower.limπ_apply,
      coe_hahnModuleToOrderCompletion_apply, hahnModuleOrderClass_eq_zero_iff]
  exact ((currentOrderTower R V).hasBasis_nhds_zero.comap
    (hahnModuleToOrderCompletion R V)).to_hasBasis
    (fun n _ ↦ ⟨(n : ℤ), trivial, by rw [hpre]⟩)
    (fun N _ ↦ ⟨N.toNat, trivial, by
      rw [hpre]
      exact HahnModule.lattice_antitone R V (by omega)⟩)

/-- The compatible-class map is injective and preserves the additive uniformity. -/
theorem isUniformEmbedding_hahnModuleToOrderCompletion :
    IsUniformEmbedding (hahnModuleToOrderCompletion R V) where
  toIsUniformInducing := AddMonoidHom.isUniformInducing_of_isInducing
    (isInducing_hahnModuleToOrderCompletion R V)
  injective := (isInducing_hahnModuleToOrderCompletion R V).isEmbedding.injective

/-- Every compatible family of current order classes is represented by a unique
vector-valued Laurent series. -/
theorem hahnModuleToOrderCompletion_bijective :
    Function.Bijective (hahnModuleToOrderCompletion R V) := by
  refine ⟨(isUniformEmbedding_hahnModuleToOrderCompletion R V).injective, ?_⟩
  have hd : DenseRange (hahnModuleToOrderCompletion R V) :=
    DenseRange.of_comp (g := _root_.HahnModule.tensorProductToHahnModule ℤ R V) <| by
      convert ModuleTower.denseRange_toLimQuotients _ (orderSubmodule_natCast_antitone R V)
      exact funext (hahnModuleToOrderCompletion_tensor R V)
  have hc := (isUniformEmbedding_hahnModuleToOrderCompletion R V).isClosedEmbedding.isClosed_range
  intro x
  exact hc.closure_subset (hd x)

/-- The compatible-family completion of tensor currents is canonically linearly
homeomorphic to the module of vector-valued Laurent series. -/
def orderCompletionEquivHahnModule :
    (currentOrderTower R V).lim ≃L[R] _root_.HahnModule ℤ R V where
  toLinearEquiv := (LinearEquiv.ofBijective (hahnModuleToOrderCompletion R V)
    (hahnModuleToOrderCompletion_bijective R V)).symm
  continuous_toFun := (isInducing_hahnModuleToOrderCompletion R V).continuous_iff.mpr (by
    convert (continuous_id : Continuous (id : (currentOrderTower R V).lim → _)) using 1
    apply funext
    intro x
    exact (LinearEquiv.ofBijective (hahnModuleToOrderCompletion R V)
      (hahnModuleToOrderCompletion_bijective R V)).apply_symm_apply x)
  continuous_invFun := (isInducing_hahnModuleToOrderCompletion R V).continuous

/-- The inverse comparison sends a series to its compatible order classes. -/
@[simp]
theorem orderCompletionEquivHahnModule_symm_apply (x : _root_.HahnModule ℤ R V) :
    (orderCompletionEquivHahnModule R V).symm x = hahnModuleToOrderCompletion R V x :=
  (rfl)

/-- The inverse-limit comparison agrees with the canonical coefficient map on tensor currents. -/
@[simp]
theorem orderCompletionEquivHahnModule_toLimQuotients (u : currentAlgebra R V) :
    orderCompletionEquivHahnModule R V
        (ModuleTower.toLimQuotients _ (orderSubmodule_natCast_antitone R V) u) =
      _root_.HahnModule.tensorProductToHahnModule ℤ R V u := by
  apply (orderCompletionEquivHahnModule R V).symm.injective
  simp

/-- The order-`n` filtration on the inverse limit is exactly the Laurent lattice filtration. -/
@[simp]
theorem orderCompletionEquivHahnModule_mem_lattice_iff (n : ℕ)
    (x : (currentOrderTower R V).lim) :
    orderCompletionEquivHahnModule R V x ∈ HahnModule.lattice R V n ↔
      (currentOrderTower R V).limπ n x = 0 := by
  rw [← hahnModuleOrderClass_eq_zero_iff, ← coe_hahnModuleToOrderCompletion_apply,
    ← ModuleTower.limπ_apply]
  have h := (orderCompletionEquivHahnModule R V).symm_apply_apply x
  rw [orderCompletionEquivHahnModule_symm_apply] at h
  rw [h]

/-- Below a cutoff, coefficients of a completed current are read from any representative of
its class at that cutoff. In particular the zeroth stage fixes the entire negative tail. -/
theorem coeff_orderCompletionEquivHahnModule {n : ℕ} {i : ℤ} (hi : i < n)
    (x : (currentOrderTower R V).lim) (u : currentAlgebra R V)
    (hu : ModuleTower.quotientsπ _ (orderSubmodule_natCast_antitone R V) n u =
      (currentOrderTower R V).limπ n x) :
    ((_root_.HahnModule.of R).symm (orderCompletionEquivHahnModule R V x)).coeff i =
      coeff R V i u := by
  have he := (orderCompletionEquivHahnModule R V).symm_apply_apply x
  rw [orderCompletionEquivHahnModule_symm_apply] at he
  have hclass : hahnModuleOrderClass R V n (orderCompletionEquivHahnModule R V x) =
      hahnModuleOrderClass R V n (_root_.HahnModule.tensorProductToHahnModule ℤ R V u) := by
    rw [← coe_hahnModuleToOrderCompletion_apply, ← ModuleTower.limπ_apply, he,
      hahnModuleOrderClass_tensor, hu]
  have hmem : orderCompletionEquivHahnModule R V x -
      _root_.HahnModule.tensorProductToHahnModule ℤ R V u ∈ HahnModule.lattice R V n :=
    (hahnModuleOrderClass_eq_zero_iff R V n _).mp (by simp [hclass])
  simpa only [HahnModule.of_symm_sub, HahnSeries.coeff_sub,
    _root_.HahnModule.coeff_tensorProductToHahnModule, sub_eq_zero] using
    (HahnModule.mem_lattice_iff R V).mp hmem i hi

end TauCeti.CurrentAlgebra
