/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Logic.Equiv.List
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Principal stages, boxes, and second countability of restricted products

A principal stage `Πʳ i, [R i, A i]_[𝓟 Sᶜ]` of a restricted product consists of the families whose
coordinates outside `S` lie in the reference sets `A i`. Reading off the unrestricted coordinates
on `S` together with the restricted coordinates outside `S` identifies that stage with the plain
product `(∀ i : S, R i) × (∀ i : {i // i ∉ S}, A i)` as a topological space
(`restrictedProductPrincipalComplHomeo`) and, when the reference sets are closed under
multiplication or addition, as a topological group or monoid
(`restrictedProductPrincipalComplMulEquiv`, `addRestrictedProductPrincipalComplAddEquiv`).

When `S : Set ι` is cofinite (`cofinite ≤ 𝓟 S`) and `A i` is open for every `i ∈ S`, the canonical
inclusion `Πʳ i, [R i, A i]_[𝓟 S] → Πʳ i, [R i, A i]` into the cofinite restricted product is an
open embedding (`isOpenEmbedding_restrictedProduct_inclusion_principal`); openness at the finitely
many indices outside `S` is not needed, improving Mathlib's
`RestrictedProduct.isOpenEmbedding_inclusion_principal`.

Coordinate boxes `restrictedProductBox A 𝓕 C = {x | ∀ i, x i ∈ C i}` are open in the cofinite
restricted product when every `C i` is open and `A i ⊆ C i` cofinitely
(`isOpen_restrictedProductBox`), and—when `A i` is open cofinitely—the open boxes agreeing
cofinitely with `A i` form a topological basis (`isTopologicalBasis_openRestrictedProductBoxes`).

Over a countable index type with second-countable factors, every principal stage
`Πʳ i, [R i, A i]_[𝓟 S]` is second countable
(`instSecondCountableTopologyRestrictedProductPrincipal`), and when cofinitely many reference sets
`A i` are open so is the cofinite restricted product `Πʳ i, [R i, A i]`
(`secondCountableTopology_restrictedProduct`, `instSecondCountableTopologyRestrictedProduct`).

## References

* N. Bourbaki, *General Topology*.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §3.3.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter Set Topology
open scoped RestrictedProduct

universe u v w

section PrincipalOpenEmbedding

variable {ι : Type u} {R : ι → Type v} {A : ∀ i, Set (R i)} [∀ i, TopologicalSpace (R i)]

/-- On a cofinite principal stage `Πʳ i, [R i, A i]_[𝓟 T]`, requiring coordinates in a set `S` to
belong to `A i` cuts out an open subset whenever `A i` is open for every `i ∈ S`. -/
theorem isOpen_forall_mem_of_principal_of_forall_mem {S T : Set ι} (hT : cofinite ≤ 𝓟 T)
    (hA : ∀ i ∈ S, IsOpen (A i)) :
    IsOpen {x : Πʳ i, [R i, A i]_[𝓟 T] | ∀ i ∈ S, x i ∈ A i} := by
  have hfin : (S ∩ Tᶜ).Finite :=
    (mem_cofinite.mp (le_principal_iff.mp hT)).inter_of_right S
  convert (isOpen_set_pi hfin fun i hi ↦ hA i hi.1).preimage
    RestrictedProduct.continuous_coe using 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_inter_iff, mem_compl_iff]
  refine ⟨fun hx i hi ↦ hx i hi.1, fun hx i hiS ↦ ?_⟩
  by_cases hiT : i ∈ T
  · exact x.2 hiT
  · exact hx i ⟨hiS, hiT⟩

/-- In a cofinite restricted product `Πʳ i, [R i, A i]`, requiring coordinates in `S` to belong to
`A i` cuts out an open set whenever `A i` is open for every `i ∈ S`. -/
theorem isOpen_forall_mem_restrictedProduct_of_forall_mem {S : Set ι}
    (hA : ∀ i ∈ S, IsOpen (A i)) :
    IsOpen {x : Πʳ i, [R i, A i] | ∀ i ∈ S, x i ∈ A i} :=
  isOpen_restrictedProduct_iff.mpr fun _ hT ↦
    isOpen_forall_mem_of_principal_of_forall_mem hT hA

/-- For a cofinite set `S` (`cofinite ≤ 𝓟 S`), the inclusion of the principal stage
`Πʳ i, [R i, A i]_[𝓟 S]` into `Πʳ i, [R i, A i]` is an open embedding as soon as `A i` is open for
every `i ∈ S`; openness at the finitely many indices outside `S` is not needed. -/
theorem isOpenEmbedding_restrictedProduct_inclusion_principal {S : Set ι} (hS : cofinite ≤ 𝓟 S)
    (hA : ∀ i ∈ S, IsOpen (A i)) :
    IsOpenEmbedding (RestrictedProduct.inclusion R A hS) where
  toIsEmbedding := RestrictedProduct.isEmbedding_inclusion_principal hS
  isOpen_range := by
    rw [RestrictedProduct.range_inclusion]
    exact isOpen_forall_mem_restrictedProduct_of_forall_mem hA

end PrincipalOpenEmbedding

section Box

variable {ι : Type u} {R : ι → Type v}

/-- The coordinate box `{x | ∀ i, x i ∈ C i}` in a restricted product `Πʳ i, [R i, A i]_[𝓕]`. -/
def restrictedProductBox (A : ∀ i, Set (R i)) (𝓕 : Filter ι) (C : ∀ i, Set (R i)) :
    Set (Πʳ i, [R i, A i]_[𝓕]) :=
  {x | ∀ i, x i ∈ C i}

/-- Explicit set-builder formula for `restrictedProductBox`. -/
theorem restrictedProductBox_def (A : ∀ i, Set (R i)) (𝓕 : Filter ι) (C : ∀ i, Set (R i)) :
    restrictedProductBox A 𝓕 C = {x | ∀ i, x i ∈ C i} :=
  (rfl)

@[simp, grind =]
theorem mem_restrictedProductBox {A : ∀ i, Set (R i)} {𝓕 : Filter ι} {C : ∀ i, Set (R i)}
    {x : Πʳ i, [R i, A i]_[𝓕]} :
    x ∈ restrictedProductBox A 𝓕 C ↔ ∀ i, x i ∈ C i :=
  Iff.rfl

@[simp]
theorem restrictedProductBox_univ (A : ∀ i, Set (R i)) (𝓕 : Filter ι) :
    restrictedProductBox A 𝓕 (fun _ ↦ Set.univ) = Set.univ := by
  ext
  simp

@[simp]
theorem restrictedProductBox_inter (A : ∀ i, Set (R i)) (𝓕 : Filter ι)
    (C₁ C₂ : ∀ i, Set (R i)) :
    restrictedProductBox A 𝓕 C₁ ∩ restrictedProductBox A 𝓕 C₂ =
      restrictedProductBox A 𝓕 (fun i ↦ C₁ i ∩ C₂ i) := by
  ext x
  simp [forall_and]

@[simp]
theorem preimage_inclusion_restrictedProductBox {A : ∀ i, Set (R i)} {𝓕 𝓖 : Filter ι}
    (h : 𝓕 ≤ 𝓖) (C : ∀ i, Set (R i)) :
    RestrictedProduct.inclusion R A h ⁻¹' restrictedProductBox A 𝓕 C =
      restrictedProductBox A 𝓖 C :=
  (rfl)

@[simp]
theorem preimage_coe_univ_pi (A : ∀ i, Set (R i)) (𝓕 : Filter ι) (C : ∀ i, Set (R i)) :
    ((↑) : Πʳ i, [R i, A i]_[𝓕] → ∀ i, R i) ⁻¹' Set.univ.pi C =
      restrictedProductBox A 𝓕 C := by
  ext
  simp

variable [∀ i, TopologicalSpace (R i)]

/-- In a cofinite restricted product, a box `∏ᵢ C i` is open whenever every `C i` is open and
`A i ⊆ C i` for all but finitely many `i`. -/
theorem isOpen_restrictedProductBox {A C : ∀ i, Set (R i)} (hC : ∀ i, IsOpen (C i))
    (hAC : ∀ᶠ i in cofinite, A i ⊆ C i) :
    IsOpen (restrictedProductBox A cofinite C) := by
  refine isOpen_restrictedProduct_iff.mpr fun T hT ↦ ?_
  have hfin : ({i | A i ⊆ C i} ∩ T)ᶜ.Finite :=
    mem_cofinite.mp (hAC.and (le_principal_iff.mp hT))
  convert (isOpen_set_pi hfin fun i _ ↦ hC i).preimage RestrictedProduct.continuous_coe using 1
  ext y
  simp only [preimage_inclusion_restrictedProductBox, mem_restrictedProductBox, mem_preimage,
    Set.mem_pi]
  refine ⟨fun hy i _ ↦ hy i, fun hy i ↦ ?_⟩
  by_cases hi : i ∈ {i | A i ⊆ C i} ∩ T
  · exact hi.1 (y.2 hi.2)
  · exact hy i hi

/-- The collection of open coordinate boxes in `Πʳ i, [R i, A i]` that agree with `A i` at all but
finitely many indices. -/
def openRestrictedProductBoxes (A : ∀ i, Set (R i)) : Set (Set (Πʳ i, [R i, A i])) :=
  {B | ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧
    B = restrictedProductBox A cofinite C}

@[simp]
theorem mem_openRestrictedProductBoxes {A : ∀ i, Set (R i)} {B : Set (Πʳ i, [R i, A i])} :
    B ∈ openRestrictedProductBoxes A ↔
      ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧ (∀ᶠ i in cofinite, C i = A i) ∧
        B = restrictedProductBox A cofinite C :=
  Iff.rfl

/-- When cofinitely many reference sets `A i` are open, the open coordinate boxes agreeing
cofinitely with `A i` form a topological basis of `Πʳ i, [R i, A i]`. -/
theorem isTopologicalBasis_openRestrictedProductBoxes {A : ∀ i, Set (R i)}
    (hA : ∀ᶠ i in cofinite, IsOpen (A i)) :
    TopologicalSpace.IsTopologicalBasis (openRestrictedProductBoxes A) := by
  classical
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨C, hC, hCA, rfl⟩
    exact isOpen_restrictedProductBox hC (hCA.mono fun _ h ↦ h.symm.subset)
  · intro x W hxW hW
    let S : Set ι := {i | IsOpen (A i) ∧ x i ∈ A i}
    have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr (hA.and x.2)
    let x' : Πʳ i, [R i, A i]_[𝓟 S] := ⟨x, eventually_principal.mpr fun i hi ↦ hi.2⟩
    have hx'W : x' ∈ RestrictedProduct.inclusion R A hS ⁻¹' W := hxW
    obtain ⟨V, hV, hVx'⟩ := RestrictedProduct.isEmbedding_coe_of_principal.isOpen_iff.mp
      (hW.preimage (RestrictedProduct.continuous_inclusion hS))
    have hx'V : (x' : ∀ i, R i) ∈ V := by
      rw [← Set.mem_preimage, hVx']
      exact hx'W
    obtain ⟨I, u, hu, hIV⟩ := isOpen_pi_iff.mp hV x' hx'V
    let C : ∀ i, Set (R i) := fun i ↦
      if i ∈ I then (if i ∈ S then u i ∩ A i else u i)
      else (if i ∈ S then A i else Set.univ)
    have hCopen : ∀ i, IsOpen (C i) := fun i ↦ by
      dsimp only [C]
      split_ifs with hiI hiS hiS'
      · exact (hu i hiI).1.inter hiS.1
      · exact (hu i hiI).1
      · exact hiS'.1
      · exact isOpen_univ
    have hCA : ∀ᶠ i in cofinite, C i = A i := by
      filter_upwards [I.finite_toSet.compl_mem_cofinite, hA, x.2] with i hiI hiA hxi
      have hiS : i ∈ S := ⟨hiA, hxi⟩
      simp [C, Finset.mem_coe.not.mp hiI, hiS]
    refine ⟨restrictedProductBox A cofinite C, ⟨C, hCopen, hCA, rfl⟩, fun i ↦ ?_, fun y hy ↦ ?_⟩
    · dsimp only [C]
      split_ifs with hiI hiS hiS'
      · exact ⟨(hu i hiI).2, hiS.2⟩
      · exact (hu i hiI).2
      · exact hiS'.2
      · trivial
    · have hyS : ∀ i ∈ S, y i ∈ A i := fun i hiS ↦ by
        have hyi := hy i
        dsimp only [C] at hyi
        split_ifs at hyi with hiI
        · exact hyi.2
        · exact hyi
      let y' : Πʳ i, [R i, A i]_[𝓟 S] := ⟨y, eventually_principal.mpr hyS⟩
      have hy'V : (y' : ∀ i, R i) ∈ V := hIV fun i hiI ↦ by
        have hyi := hy i
        dsimp only [C] at hyi
        rw [ite_eq_left (Finset.mem_coe.mp hiI)] at hyi
        split_ifs at hyi
        · exact hyi.1
        · exact hyi
      have hy'W : y' ∈ RestrictedProduct.inclusion R A hS ⁻¹' W := by
        rw [← hVx']
        exact hy'V
      exact hy'W

end Box

section SecondCountable

variable {ι : Type u} {R : ι → Type v} {A : ∀ i, Set (R i)}
variable [Countable ι] [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]

/-- Every principal stage `Πʳ i, [R i, A i]_[𝓟 S]` over a countable index type with
second-countable factors is second countable. -/
instance instSecondCountableTopologyRestrictedProductPrincipal (S : Set ι) :
    SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 S]) :=
  RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology

/-- Over a countable index type with second-countable factors, `Πʳ i, [R i, A i]` is second
countable whenever cofinitely many reference sets `A i` are open. -/
theorem secondCountableTopology_restrictedProduct (hA : ∀ᶠ i in cofinite, IsOpen (A i)) :
    SecondCountableTopology (Πʳ i, [R i, A i]) := by
  classical
  let hfin : {i | ¬ IsOpen (A i)}.Finite := eventually_cofinite.mp hA
  let S₀ : Finset ι := hfin.toFinset
  let Idx := {F : Finset ι // S₀ ⊆ F}
  have hF : ∀ F : Idx, (cofinite : Filter ι) ≤ 𝓟 (F.1 : Set ι)ᶜ := fun F ↦
    le_principal_iff.mpr F.1.finite_toSet.compl_mem_cofinite
  have hemb : ∀ F : Idx, IsOpenEmbedding (RestrictedProduct.inclusion R A (hF F)) := by
    intro F
    refine isOpenEmbedding_restrictedProduct_inclusion_principal (hF F) fun i hi ↦ ?_
    by_contra hnot
    exact hi (F.2 (hfin.mem_toFinset.mpr hnot))
  let U : Idx → Set (Πʳ i, [R i, A i]) := fun F ↦
    Set.range (RestrictedProduct.inclusion R A (hF F))
  have : ∀ F : Idx, SecondCountableTopology (U F) := fun F ↦
    (hemb F).toIsEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun F ↦ (hemb F).isOpen_range) (eq_univ_iff_forall.mpr fun x ↦ ?_)
  let hx : {i | x i ∉ A i}.Finite := eventually_cofinite.mp x.2
  let F : Idx := ⟨S₀ ∪ hx.toFinset, Finset.subset_union_left⟩
  refine mem_iUnion.mpr ⟨F, ?_⟩
  rw [RestrictedProduct.range_inclusion]
  intro i hi
  by_contra hxi
  exact hi (Finset.mem_coe.mpr (Finset.mem_union_right _ (hx.mem_toFinset.mpr hxi)))

instance instSecondCountableTopologyRestrictedProduct [hA : Fact (∀ i, IsOpen (A i))] :
    SecondCountableTopology (Πʳ i, [R i, A i]) :=
  secondCountableTopology_restrictedProduct (.of_forall hA.out)

instance instSecondCountableTopologyRestrictedProductSetLike
    {S : ι → Type*} [∀ i, SetLike (S i) (R i)] {B : ∀ i, S i}
    [hB : Fact (∀ i, IsOpen (B i : Set (R i)))] :
    SecondCountableTopology (Πʳ i, [R i, B i]) :=
  secondCountableTopology_restrictedProduct (.of_forall hB.out)

end SecondCountable

section PrincipalDecomposition

variable {ι : Type u} {R : ι → Type v}

/-- The homeomorphism between a principal stage `Πʳ i, [R i, A i]_[𝓟 Sᶜ]` and the product
`(∀ i : S, R i) × (∀ i : {i // i ∉ S}, A i)`, coordinatewise the identity in both directions. -/
noncomputable def restrictedProductPrincipalComplHomeo [∀ i, TopologicalSpace (R i)]
    (A : ∀ i, Set (R i)) (S : Set ι) :
    (Πʳ i, [R i, A i]_[𝓟 Sᶜ]) ≃ₜ (∀ i : S, R i) × (∀ i : {i // i ∉ S}, A i) where
  toFun x := (fun i ↦ x i.1, fun j ↦ ⟨x j.1, eventually_principal.mp x.2 j.1 j.2⟩)
  invFun p :=
    letI := Classical.decPred (· ∈ S)
    ⟨fun i ↦ if h : i ∈ S then p.1 ⟨i, h⟩ else (p.2 ⟨i, h⟩ : R i),
      eventually_principal.mpr fun i hi ↦ by
        dsimp only
        rw [dite_eq_right hi]
        exact (p.2 ⟨i, hi⟩).2⟩
  left_inv x := by
    let _ := Classical.decPred (· ∈ S)
    ext i
    by_cases hi : i ∈ S
    · exact dite_eq_left hi
    · exact dite_eq_right hi
  right_inv p := by
    ext i
    · dsimp only
      exact dite_eq_left i.2
    · dsimp only
      exact dite_eq_right i.2
  continuous_toFun :=
    (continuous_pi fun i ↦ RestrictedProduct.continuous_eval i.1).prodMk
      (continuous_pi fun j ↦ (RestrictedProduct.continuous_eval j.1).subtype_mk _)
  continuous_invFun := by
    let _ := Classical.decPred (· ∈ S)
    refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun i ↦ ?_
    by_cases hi : i ∈ S
    · have h : (fun x : Πʳ j, [R j, A j]_[𝓟 Sᶜ] ↦ x i) ∘
          (fun p : (∀ j : S, R j) × (∀ j : {j // j ∉ S}, A j) ↦
            (⟨fun j ↦ if h : j ∈ S then p.1 ⟨j, h⟩ else (p.2 ⟨j, h⟩ : R j),
              eventually_principal.mpr fun j hj ↦ by
                dsimp only; rw [dite_eq_right hj]; exact (p.2 ⟨j, hj⟩).2⟩ :
              Πʳ j, [R j, A j]_[𝓟 Sᶜ])) =
          fun p ↦ p.1 ⟨i, hi⟩ := by
        ext p
        exact dite_eq_left hi
      rw [h]
      exact (continuous_apply (⟨i, hi⟩ : S)).comp continuous_fst
    · have h : (fun x : Πʳ j, [R j, A j]_[𝓟 Sᶜ] ↦ x i) ∘
          (fun p : (∀ j : S, R j) × (∀ j : {j // j ∉ S}, A j) ↦
            (⟨fun j ↦ if h : j ∈ S then p.1 ⟨j, h⟩ else (p.2 ⟨j, h⟩ : R j),
              eventually_principal.mpr fun j hj ↦ by
                dsimp only; rw [dite_eq_right hj]; exact (p.2 ⟨j, hj⟩).2⟩ :
              Πʳ j, [R j, A j]_[𝓟 Sᶜ])) =
          fun p ↦ (p.2 ⟨i, hi⟩ : R i) := by
        ext p
        exact dite_eq_right hi
      rw [h]
      exact continuous_subtype_val.comp
        ((continuous_apply (⟨i, hi⟩ : {j // j ∉ S})).comp continuous_snd)

@[simp]
theorem restrictedProductPrincipalComplHomeo_fst_apply [∀ i, TopologicalSpace (R i)]
    (A : ∀ i, Set (R i)) (S : Set ι) (x : Πʳ i, [R i, A i]_[𝓟 Sᶜ]) (i : S) :
    (restrictedProductPrincipalComplHomeo A S x).1 i = x i.1 :=
  (rfl)

@[simp]
theorem restrictedProductPrincipalComplHomeo_snd_coe_apply [∀ i, TopologicalSpace (R i)]
    (A : ∀ i, Set (R i)) (S : Set ι) (x : Πʳ i, [R i, A i]_[𝓟 Sᶜ]) (j : {i // i ∉ S}) :
    ((restrictedProductPrincipalComplHomeo A S x).2 j : R j.1) = x j.1 :=
  (rfl)

@[simp]
theorem restrictedProductPrincipalComplHomeo_symm_apply_of_mem [∀ i, TopologicalSpace (R i)]
    (A : ∀ i, Set (R i)) (S : Set ι)
    (p : (∀ i : S, R i) × (∀ i : {i // i ∉ S}, A i)) {i : ι} (hi : i ∈ S) :
    (restrictedProductPrincipalComplHomeo A S).symm p i = p.1 ⟨i, hi⟩ := by
  have h := restrictedProductPrincipalComplHomeo_fst_apply A S
    ((restrictedProductPrincipalComplHomeo A S).symm p) ⟨i, hi⟩
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

@[simp]
theorem restrictedProductPrincipalComplHomeo_symm_apply_of_notMem [∀ i, TopologicalSpace (R i)]
    (A : ∀ i, Set (R i)) (S : Set ι)
    (p : (∀ i : S, R i) × (∀ i : {i // i ∉ S}, A i)) {i : ι} (hi : i ∉ S) :
    (restrictedProductPrincipalComplHomeo A S).symm p i = p.2 ⟨i, hi⟩ := by
  have h := restrictedProductPrincipalComplHomeo_snd_coe_apply A S
    ((restrictedProductPrincipalComplHomeo A S).symm p) ⟨i, hi⟩
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-- When `A i ⊆ C i` outside `S`, the preimage of `restrictedProductBox A (𝓟 Sᶜ) C` under
`(restrictedProductPrincipalComplHomeo A S).symm` is `(Set.univ.pi fun i : S ↦ C i) ×ˢ Set.univ`. -/
theorem restrictedProductPrincipalComplHomeo_symm_preimage_box [∀ i, TopologicalSpace (R i)]
    (A : ∀ i, Set (R i)) (S : Set ι) {C : ∀ i, Set (R i)} (hAC : ∀ i ∉ S, A i ⊆ C i) :
    (restrictedProductPrincipalComplHomeo A S).symm ⁻¹' restrictedProductBox A (𝓟 Sᶜ) C =
      (Set.univ.pi fun i : S ↦ C i.1) ×ˢ Set.univ := by
  ext p
  simp only [mem_preimage, mem_restrictedProductBox, mem_prod, Set.mem_pi, mem_univ,
    forall_true_left, and_true]
  refine ⟨fun h i ↦ ?_, fun h i ↦ ?_⟩
  · simpa [restrictedProductPrincipalComplHomeo_symm_apply_of_mem A S p i.2] using h i.1
  · by_cases hi : i ∈ S
    · rw [restrictedProductPrincipalComplHomeo_symm_apply_of_mem A S p hi]
      exact h ⟨i, hi⟩
    · rw [restrictedProductPrincipalComplHomeo_symm_apply_of_notMem A S p hi]
      exact hAC i hi (p.2 ⟨i, hi⟩).2

variable {G : ι → Type v} {K : ι → Type w}
variable [∀ i, TopologicalSpace (G i)] [∀ i, Mul (G i)]
variable [∀ i, SetLike (K i) (G i)] [∀ i, MulMemClass (K i) (G i)]

/-- The topological multiplicative equivalence between a principal stage
`Πʳ i, [G i, B i]_[𝓟 Sᶜ]` and `(∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i)`. -/
@[to_additive addRestrictedProductPrincipalComplAddEquiv
/-- The topological additive equivalence between a principal stage
`Πʳ i, [G i, B i]_[𝓟 Sᶜ]` and `(∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i)`. -/]
noncomputable def restrictedProductPrincipalComplMulEquiv (B : ∀ i, K i) (S : Set ι) :
    (Πʳ i, [G i, B i]_[𝓟 Sᶜ]) ≃ₜ* (∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i) where
  __ := restrictedProductPrincipalComplHomeo (fun i ↦ (B i : Set (G i))) S
  map_mul' _ _ := rfl

@[to_additive (attr := simp) addRestrictedProductPrincipalComplAddEquiv_toHomeomorph]
theorem restrictedProductPrincipalComplMulEquiv_toHomeomorph (B : ∀ i, K i) (S : Set ι) :
    (restrictedProductPrincipalComplMulEquiv B S).toHomeomorph =
      restrictedProductPrincipalComplHomeo (fun i ↦ (B i : Set (G i))) S :=
  (rfl)

@[to_additive (attr := simp) addRestrictedProductPrincipalComplAddEquiv_fst_apply]
theorem restrictedProductPrincipalComplMulEquiv_fst_apply (B : ∀ i, K i) (S : Set ι)
    (x : Πʳ i, [G i, B i]_[𝓟 Sᶜ]) (i : S) :
    (restrictedProductPrincipalComplMulEquiv B S x).1 i = x i.1 :=
  (rfl)

@[to_additive (attr := simp) addRestrictedProductPrincipalComplAddEquiv_snd_coe_apply]
theorem restrictedProductPrincipalComplMulEquiv_snd_coe_apply (B : ∀ i, K i) (S : Set ι)
    (x : Πʳ i, [G i, B i]_[𝓟 Sᶜ]) (j : {i // i ∉ S}) :
    ((restrictedProductPrincipalComplMulEquiv B S x).2 j : G j.1) = x j.1 :=
  (rfl)

@[to_additive (attr := simp) addRestrictedProductPrincipalComplAddEquiv_symm_apply_of_mem]
theorem restrictedProductPrincipalComplMulEquiv_symm_apply_of_mem (B : ∀ i, K i) (S : Set ι)
    (p : (∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i)) {i : ι} (hi : i ∈ S) :
    (restrictedProductPrincipalComplMulEquiv B S).symm p i = p.1 ⟨i, hi⟩ :=
  restrictedProductPrincipalComplHomeo_symm_apply_of_mem (fun j ↦ (B j : Set (G j))) S p hi

@[to_additive (attr := simp) addRestrictedProductPrincipalComplAddEquiv_symm_apply_of_notMem]
theorem restrictedProductPrincipalComplMulEquiv_symm_apply_of_notMem (B : ∀ i, K i) (S : Set ι)
    (p : (∀ i : S, G i) × (∀ i : {i // i ∉ S}, B i)) {i : ι} (hi : i ∉ S) :
    (restrictedProductPrincipalComplMulEquiv B S).symm p i = p.2 ⟨i, hi⟩ :=
  restrictedProductPrincipalComplHomeo_symm_apply_of_notMem (fun j ↦ (B j : Set (G j))) S p hi

section PrincipalPieceInclusion

variable {M : ι → Type v} {L : ι → Type w}
variable [∀ i, TopologicalSpace (M i)] [∀ i, Monoid (M i)]
variable [∀ i, SetLike (L i) (M i)] [∀ i, SubmonoidClass (L i) (M i)]

/-- For a finite index set `S : Finset ι`, the canonical monoid homomorphism embedding the product
`(∀ i : S, M i) × (∀ i : {i // i ∉ S}, B i)` into `Πʳ i, [M i, B i]` as the principal piece
`{x | ∀ i ∉ S, x i ∈ B i}`. -/
@[to_additive addRestrictedProductPrincipalPieceInclusion
/-- For a finite index set `S : Finset ι`, the canonical additive monoid homomorphism embedding the
product `(∀ i : S, M i) × (∀ i : {i // i ∉ S}, B i)` into `Πʳ i, [M i, B i]` as the principal piece
`{x | ∀ i ∉ S, x i ∈ B i}`. -/]
noncomputable def restrictedProductPrincipalPieceInclusion (B : ∀ i, L i) (S : Finset ι) :
    (∀ i : S, M i.1) × (∀ j : {i // i ∉ S}, B j.1) →* Πʳ i, [M i, B i] where
  toFun p :=
    RestrictedProduct.inclusion M (fun i ↦ (B i : Set (M i)))
      (le_principal_iff.mpr S.finite_toSet.compl_mem_cofinite)
      ((restrictedProductPrincipalComplMulEquiv B (S : Set ι)).symm p)
  map_one' := by ext i; simp
  map_mul' _ _ := by ext i; simp

@[to_additive coe_addRestrictedProductPrincipalPieceInclusion]
theorem coe_restrictedProductPrincipalPieceInclusion (B : ∀ i, L i) (S : Finset ι) :
    (restrictedProductPrincipalPieceInclusion B S :
      (∀ i : S, M i.1) × (∀ j : {i // i ∉ S}, B j.1) → Πʳ i, [M i, B i]) =
      RestrictedProduct.inclusion M (fun i ↦ (B i : Set (M i)))
        (le_principal_iff.mpr S.finite_toSet.compl_mem_cofinite) ∘
        (restrictedProductPrincipalComplMulEquiv B (S : Set ι)).symm :=
  (rfl)

@[to_additive (attr := simp) addRestrictedProductPrincipalPieceInclusion_apply_of_mem]
theorem restrictedProductPrincipalPieceInclusion_apply_of_mem (B : ∀ i, L i) (S : Finset ι)
    (p : (∀ i : S, M i.1) × (∀ j : {i // i ∉ S}, B j.1)) {i : ι} (hi : i ∈ S) :
    restrictedProductPrincipalPieceInclusion B S p i = p.1 ⟨i, hi⟩ :=
  restrictedProductPrincipalComplMulEquiv_symm_apply_of_mem B (S : Set ι) p hi

@[to_additive (attr := simp) addRestrictedProductPrincipalPieceInclusion_apply_of_notMem]
theorem restrictedProductPrincipalPieceInclusion_apply_of_notMem (B : ∀ i, L i) (S : Finset ι)
    (p : (∀ i : S, M i.1) × (∀ j : {i // i ∉ S}, B j.1)) {i : ι} (hi : i ∉ S) :
    restrictedProductPrincipalPieceInclusion B S p i = p.2 ⟨i, hi⟩ :=
  restrictedProductPrincipalComplMulEquiv_symm_apply_of_notMem B (S : Set ι) p hi

@[to_additive range_addRestrictedProductPrincipalPieceInclusion]
theorem range_restrictedProductPrincipalPieceInclusion (B : ∀ i, L i) (S : Finset ι) :
    Set.range (restrictedProductPrincipalPieceInclusion B S) =
      {x : Πʳ i, [M i, B i] | ∀ i ∉ S, x i ∈ B i} := by
  rw [coe_restrictedProductPrincipalPieceInclusion, Set.range_comp, EquivLike.range_eq_univ,
    Set.image_univ, RestrictedProduct.range_inclusion]
  rfl

@[to_additive preimage_addRestrictedProductPrincipalPieceInclusion_box]
theorem preimage_restrictedProductPrincipalPieceInclusion_box (B : ∀ i, L i) (S : Finset ι)
    {C : ∀ i, Set (M i)} (hBC : ∀ i ∉ S, (B i : Set (M i)) ⊆ C i) :
    restrictedProductPrincipalPieceInclusion B S ⁻¹'
      restrictedProductBox (fun i ↦ (B i : Set (M i))) cofinite C =
        (Set.univ.pi fun i : S ↦ C i.1) ×ˢ Set.univ :=
  restrictedProductPrincipalComplHomeo_symm_preimage_box (fun i ↦ (B i : Set (M i))) (S : Set ι) hBC

@[to_additive isOpenEmbedding_addRestrictedProductPrincipalPieceInclusion]
theorem isOpenEmbedding_restrictedProductPrincipalPieceInclusion (B : ∀ i, L i) (S : Finset ι)
    (hB : ∀ i ∉ S, IsOpen (B i : Set (M i))) :
    IsOpenEmbedding (restrictedProductPrincipalPieceInclusion B S) :=
  (isOpenEmbedding_restrictedProduct_inclusion_principal
    (le_principal_iff.mpr S.finite_toSet.compl_mem_cofinite) hB).comp
    (restrictedProductPrincipalComplMulEquiv B (S : Set ι)).symm.toHomeomorph.isOpenEmbedding

end PrincipalPieceInclusion

end PrincipalDecomposition

end TauCeti
