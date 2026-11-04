/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Chevalley.Basic
public import TauCeti.LinearAlgebra.RootSystem.HomInvariance
public import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# Universal property, symmetries, and transport of full-Cartan Chevalley Lie algebras

This file develops the universal property and functorial symmetries of
`RootPairing.ChevalleyLieAlgebra c` over arbitrary cocharacter lattices `Y`, without assuming any
splitting of `Y` into central and coroot summands:

* **Sign twists** (`RootPairing.ChevalleyConstants.twist`,
  `RootPairing.ChevalleyLieAlgebra.twistLieEquiv`): rescaling root vectors by signs `s : ι → ℤˣ`
  invariant under root opposition `i ↦ P.reflectionPerm i i` transforms `c` into an isomorphic
  Chevalley structure-constant table `c.twist s hs`.
* **Cartan-pairing transport** (`RootPairing.ChevalleyConstants.reindex`): any bijection
  `e : ι ≃ ι₂` matching Cartan pairings `P₂.pairing (e i) (e j) = P.pairing i j` transports `c` to
  a table on `P₂`, even when the ambient lattices `(X, Y)` and `(X₂, Y₂)` have different ranks or
  toral extensions.
* **Universal property** (`RootPairing.ChevalleyLieAlgebra.liftLieHom`): a `ℤ`-Lie algebra
  homomorphism out of `ChevalleyLieAlgebra c` is uniquely determined by an abelian Cartan map
  `γ : Y →ₗ[ℤ] L` and root images `r : ι → L` satisfying the Cartan weight and Chevalley bracket
  relations.
* **Chevalley involution** (`RootPairing.ChevalleyLieAlgebra.chevalleyInvolution`): the involutive
  automorphism `H_y ↦ -H_y`, `eᵢ ↦ -e_{-i}`.
* **Covariant functoriality** (`RootPairing.ChevalleyLieAlgebra.mapLieHom`,
  `RootPairing.ChevalleyLieAlgebra.mapLieEquiv`,
  `RootPairing.ChevalleyLieAlgebra.equivOfRootPairingEquiv`): functorial maps induced by compatible
  cocharacter homomorphisms `γ : Y →ₗ[ℤ] Y₂` (covering central extensions, central isogenies, and
  quotients by central tori) and by root-pairing equivalences `g : P.Equiv P₂`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016), §§1--3.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.1--4.2.
* M. Demazure, *SGA III, Exposé XXI, Données Radicielles*.
-/

public section

open Module Set

namespace RootPairing

namespace ChevalleyConstants

section Twist

variable {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
  {P : RootPairing ι ℤ X Y}

open scoped Classical in
private noncomputable def twistConst (P : RootPairing ι ℤ X Y) (N : ι → ι → ℤ) (s : ι → ℤˣ)
    (i j : ι) : ℤ :=
  if h : ∃ k, P.root k = P.root i + P.root j then
    ((s i * s j * s h.choose : ℤˣ) : ℤ) * N i j
  else 0

omit [Finite ι] in
private theorem twistConst_of_root_eq_add {N : ι → ι → ℤ} {s : ι → ℤˣ} {i j k : ι}
    (hk : P.root k = P.root i + P.root j) :
    twistConst P N s i j = ((s i * s j * s k : ℤˣ) : ℤ) * N i j := by
  classical
  have hex : ∃ m, P.root m = P.root i + P.root j := ⟨k, hk⟩
  have hchoose : hex.choose = k := P.root.injective (hex.choose_spec.trans hk.symm)
  rw [twistConst, dite_eq_left hex, hchoose]

omit [Finite ι] in
private theorem twistConst_of_notMem_range {N : ι → ι → ℤ} {s : ι → ℤˣ} {i j : ι}
    (hnot : P.root i + P.root j ∉ range P.root) :
    twistConst P N s i j = 0 := by
  classical
  exact dite_eq_right fun ⟨k, hk⟩ ↦ hnot ⟨k, hk⟩

private theorem tripleRootCoeff_twistConst (c : P.ChevalleyConstants) (s : ι → ℤˣ)
    (hs : ∀ i, s (P.reflectionPerm i i) = s i) (i j k l : ι) :
    P.tripleRootCoeff (twistConst P c.structConst s) i j k l =
      ((s i * s j * s k * s l : ℤˣ) : ℤ) * P.tripleRootCoeff c.structConst i j k l := by
  classical
  by_cases hjk0 : P.root j + P.root k = 0
  · rw [P.tripleRootCoeff_of_add_eq_zero _ hjk0, P.tripleRootCoeff_of_add_eq_zero _ hjk0]
    by_cases hli : l = i
    · subst hli
      have hkj : k = P.reflectionPerm j j :=
        P.root_eq_neg_iff.mp (add_eq_zero_iff_eq_neg.mp (by rw [add_comm]; exact hjk0))
      have hunit : s l * s j * s k * s l = 1 := by
        rw [hkj, hs j]
        calc s l * s j * s j * s l
            = (s l * s l) * (s j * s j) := by ext; simp only [Units.val_mul]; ring
          _ = 1 := by rw [Int.units_mul_self, Int.units_mul_self, one_mul]
      rw [ite_eq_left rfl, hunit, Units.val_one, one_mul]
    · rw [ite_eq_right hli, mul_zero]
  · by_cases hex : ∃ m, P.root m = P.root j + P.root k
    · obtain ⟨m, hm⟩ := hex
      rw [P.tripleRootCoeff_of_root_eq_add _ hm, P.tripleRootCoeff_of_root_eq_add _ hm]
      by_cases hlm : P.root l = P.root i + P.root m
      · rw [ite_eq_left hlm, ite_eq_left hlm, twistConst_of_root_eq_add hlm,
          twistConst_of_root_eq_add hm]
        have hunit : (s i * s m * s l) * (s j * s k * s m) = s i * s j * s k * s l := by
          calc (s i * s m * s l) * (s j * s k * s m)
              = (s i * s j * s k * s l) * (s m * s m) := by
                ext; simp only [Units.val_mul]; ring
            _ = s i * s j * s k * s l := by rw [Int.units_mul_self, mul_one]
        calc (((s i * s m * s l : ℤˣ) : ℤ) * c.structConst i m) *
              (((s j * s k * s m : ℤˣ) : ℤ) * c.structConst j k)
            = (((s i * s m * s l) * (s j * s k * s m) : ℤˣ) : ℤ) *
                (c.structConst i m * c.structConst j k) := by
              simp only [Units.val_mul]; ring
          _ = ((s i * s j * s k * s l : ℤˣ) : ℤ) * (c.structConst i m * c.structConst j k) := by
              rw [hunit]
      · rw [ite_eq_right hlm, ite_eq_right hlm, mul_zero]
    · have hnot : P.root j + P.root k ∉ range P.root := fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩
      rw [P.tripleRootCoeff_of_notMem_of_add_ne_zero _ hnot hjk0,
        P.tripleRootCoeff_of_notMem_of_add_ne_zero _ hnot hjk0, mul_zero]

/-- **Sign twist of Chevalley structure constants.** Given signs `s : ι → ℤˣ` invariant under root
opposition `i ↦ P.reflectionPerm i i`, rescaling `eᵢ` by `s i` replaces `Nᵢⱼ` on a root sum
`αₖ = αᵢ + αⱼ` by `(s i * s j * s k) * Nᵢⱼ`. -/
noncomputable def twist (c : P.ChevalleyConstants) (s : ι → ℤˣ)
    (hs : ∀ i, s (P.reflectionPerm i i) = s i) : P.ChevalleyConstants where
  structConst := twistConst P c.structConst s
  structConst_eq_zero_of_notMem_range _ _ hnot := twistConst_of_notMem_range hnot
  structConst_swap i j := by
    by_cases hex : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hex
      have hk' : P.root k = P.root j + P.root i := by rw [add_comm]; exact hk
      rw [twistConst_of_root_eq_add hk', twistConst_of_root_eq_add hk, c.structConst_swap i j,
        mul_comm (s j) (s i), mul_neg]
    · have hnot₁ : P.root i + P.root j ∉ range P.root := fun ⟨k, hk⟩ ↦ hex ⟨k, hk⟩
      have hnot₂ : P.root j + P.root i ∉ range P.root := by rwa [add_comm]
      rw [twistConst_of_notMem_range hnot₂, twistConst_of_notMem_range hnot₁, neg_zero]
  natAbs_structConst {i j k} hk := by
    rw [twistConst_of_root_eq_add hk, Int.natAbs_mul, Int.units_natAbs, one_mul,
      c.natAbs_structConst hk]
  structConst_reflectionPerm i j := by
    by_cases hex : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hex
      have hk' : P.root (P.reflectionPerm k k) =
          P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) := by
        rw [root_reflectionPerm, root_reflectionPerm, root_reflectionPerm, reflection_apply_self,
          reflection_apply_self, reflection_apply_self, hk]
        abel
      rw [twistConst_of_root_eq_add hk', twistConst_of_root_eq_add hk, hs i, hs j, hs k,
        c.structConst_reflectionPerm, mul_neg]
    · have hnot : P.root i + P.root j ∉ range P.root := fun ⟨k, hk⟩ ↦ hex ⟨k, hk⟩
      have hnot' : P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) ∉
          range P.root := by
        rintro ⟨k, hk⟩
        refine hex ⟨P.reflectionPerm k k, ?_⟩
        simp only [root_reflectionPerm, reflection_apply_self] at hk ⊢
        rw [hk, neg_add, neg_neg, neg_neg]
      rw [twistConst_of_notMem_range hnot', twistConst_of_notMem_range hnot, neg_zero]
  coroot_jacobi {i j k} h0 := by
    have hi : P.root (P.reflectionPerm i i) = P.root j + P.root k := by
      rw [root_reflectionPerm, reflection_apply_self]
      calc -P.root i = P.root i + P.root j + P.root k - P.root i := by rw [h0, zero_sub]
        _ = P.root j + P.root k := by abel
    have hj : P.root (P.reflectionPerm j j) = P.root k + P.root i := by
      rw [root_reflectionPerm, reflection_apply_self]
      calc -P.root j = P.root i + P.root j + P.root k - P.root j := by rw [h0, zero_sub]
        _ = P.root k + P.root i := by abel
    have hk : P.root (P.reflectionPerm k k) = P.root i + P.root j := by
      rw [root_reflectionPerm, reflection_apply_self]
      calc -P.root k = P.root i + P.root j + P.root k - P.root k := by rw [h0, zero_sub]
        _ = P.root i + P.root j := by abel
    rw [twistConst_of_root_eq_add hi, twistConst_of_root_eq_add hj, twistConst_of_root_eq_add hk,
      hs i, hs j, hs k]
    have hcomm₁ : s j * s k * s i = s i * s j * s k := by ext; simp only [Units.val_mul]; ring
    have hcomm₂ : s k * s i * s j = s i * s j * s k := by ext; simp only [Units.val_mul]; ring
    rw [hcomm₁, hcomm₂, mul_smul, mul_smul, mul_smul, ← smul_add, ← smul_add,
      c.coroot_jacobi h0, smul_zero]
  root_jacobi i j k l := by
    rw [tripleRootCoeff_twistConst c s hs i j k l, tripleRootCoeff_twistConst c s hs j k i l,
      tripleRootCoeff_twistConst c s hs k i j l]
    have hc₁ : s j * s k * s i * s l = s i * s j * s k * s l := by
      ext; simp only [Units.val_mul]; ring
    have hc₂ : s k * s i * s j * s l = s i * s j * s k * s l := by
      ext; simp only [Units.val_mul]; ring
    rw [hc₁, hc₂, ← mul_add, ← mul_add, c.root_jacobi i j k l, mul_zero]

theorem twist_structConst_of_root_eq_add (c : P.ChevalleyConstants) (s : ι → ℤˣ)
    (hs : ∀ i, s (P.reflectionPerm i i) = s i) {i j k : ι}
    (hk : P.root k = P.root i + P.root j) :
    (c.twist s hs).structConst i j = ((s i * s j * s k : ℤˣ) : ℤ) * c.structConst i j :=
  twistConst_of_root_eq_add hk

end Twist

section Reindex

variable {ι ι₂ X Y X₂ Y₂ : Type*} [Finite ι] [Finite ι₂]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X₂] [AddCommGroup Y₂]
  {P : RootPairing ι ℤ X Y} {P₂ : RootPairing ι₂ ℤ X₂ Y₂}

omit [Finite ι] [Finite ι₂] in
private theorem pairingIn_eq_of_pairing (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairing (e i) (e j) = P.pairing i j) (a b : ι) :
    P₂.pairingIn ℤ (e a) (e b) = P.pairingIn ℤ a b :=
  FaithfulSMul.algebraMap_injective ℤ ℤ <|
    (P₂.algebraMap_pairingIn ℤ (e a) (e b)).trans
      ((he a b).trans (P.algebraMap_pairingIn ℤ a b).symm)

omit [Finite ι₂] in
private theorem tripleRootCoeff_comp_symm (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairing (e i) (e j) = P.pairing i j) (N : ι → ι → ℤ) (i j k l : ι) :
    P₂.tripleRootCoeff (fun a b ↦ N (e.symm a) (e.symm b)) (e i) (e j) (e k) (e l) =
      P.tripleRootCoeff N i j k l := by
  classical
  have heIn := pairingIn_eq_of_pairing e he
  by_cases hjk0 : P.root j + P.root k = 0
  · have hjk0₂ : P₂.root (e j) + P₂.root (e k) = 0 :=
      (root_add_eq_zero_iff_of_pairingIn e heIn j k).mpr hjk0
    rw [P₂.tripleRootCoeff_of_add_eq_zero _ hjk0₂, P.tripleRootCoeff_of_add_eq_zero _ hjk0,
      he i j, e.injective.eq_iff]
  · have hjk0₂ : P₂.root (e j) + P₂.root (e k) ≠ 0 :=
      mt (root_add_eq_zero_iff_of_pairingIn e heIn j k).mp hjk0
    by_cases hex : ∃ m, P.root m = P.root j + P.root k
    · obtain ⟨m, hm⟩ := hex
      have hm₂ : P₂.root (e m) = P₂.root (e j) + P₂.root (e k) :=
        (root_eq_add_iff_of_pairingIn e heIn m j k).mpr hm
      rw [P₂.tripleRootCoeff_of_root_eq_add _ hm₂, P.tripleRootCoeff_of_root_eq_add _ hm,
        root_eq_add_iff_of_pairingIn e heIn l i m]
      simp
    · have hnot : P.root j + P.root k ∉ range P.root := fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩
      have hnot₂ : P₂.root (e j) + P₂.root (e k) ∉ range P₂.root := by
        rintro ⟨m₂, hm₂⟩
        obtain ⟨m, rfl⟩ := e.surjective m₂
        exact hex ⟨m, (root_eq_add_iff_of_pairingIn e heIn m j k).mp hm₂⟩
      rw [P₂.tripleRootCoeff_of_notMem_of_add_ne_zero _ hnot₂ hjk0₂,
        P.tripleRootCoeff_of_notMem_of_add_ne_zero _ hnot hjk0]

/-- **Transport of Chevalley structure constants along Cartan-matching root bijections.** Any
bijection `e : ι ≃ ι₂` preserving integer Cartan pairings transports `c : P.ChevalleyConstants` to
`P₂.ChevalleyConstants`, with no assumption relating the ambient lattices `(X, Y)` and `(X₂, Y₂)`
beyond their root-coroot pairings. -/
def reindex (c : P.ChevalleyConstants) (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairing (e i) (e j) = P.pairing i j) : P₂.ChevalleyConstants where
  structConst i₂ j₂ := c.structConst (e.symm i₂) (e.symm j₂)
  structConst_eq_zero_of_notMem_range i₂ j₂ hnot := by
    have heIn := pairingIn_eq_of_pairing e he
    refine c.structConst_eq_zero_of_notMem_range _ _ fun ⟨k, hk⟩ ↦ hnot ⟨e k, ?_⟩
    simpa using (root_eq_add_iff_of_pairingIn e heIn k (e.symm i₂) (e.symm j₂)).mpr hk
  structConst_swap i₂ j₂ := c.structConst_swap _ _
  natAbs_structConst {i₂ j₂ k₂} hk₂ := by
    have heIn := pairingIn_eq_of_pairing e he
    obtain ⟨i, rfl⟩ := e.surjective i₂
    obtain ⟨j, rfl⟩ := e.surjective j₂
    obtain ⟨k, rfl⟩ := e.surjective k₂
    have hk : P.root k = P.root i + P.root j :=
      (root_eq_add_iff_of_pairingIn e heIn k i j).mp hk₂
    simpa [chainBotCoeff_eq_of_pairingIn e heIn i j] using c.natAbs_structConst hk
  structConst_reflectionPerm i₂ j₂ := by
    have heIn := pairingIn_eq_of_pairing e he
    obtain ⟨i, rfl⟩ := e.surjective i₂
    obtain ⟨j, rfl⟩ := e.surjective j₂
    simp only [← map_reflectionPerm_of_pairingIn e heIn, Equiv.symm_apply_apply]
    exact c.structConst_reflectionPerm i j
  coroot_jacobi {i₂ j₂ k₂} h0₂ := by
    have heIn := pairingIn_eq_of_pairing e he
    obtain ⟨i, rfl⟩ := e.surjective i₂
    obtain ⟨j, rfl⟩ := e.surjective j₂
    obtain ⟨k, rfl⟩ := e.surjective k₂
    simp only [Equiv.symm_apply_apply]
    have h0 : P.root i + P.root j + P.root k = 0 :=
      (root_add_add_eq_zero_iff_of_pairingIn e heIn i j k).mp h0₂
    have hmem : c.structConst j k • P₂.coroot (e i) + c.structConst k i • P₂.coroot (e j) +
        c.structConst i j • P₂.coroot (e k) ∈ P₂.corootSpan ℤ :=
      Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self _)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self _))))
        (Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self _)))
    refine P₂.eq_zero_of_mem_corootSpan_of_forall_root'_eq_zero hmem fun r₂ ↦ ?_
    obtain ⟨r, rfl⟩ := e.surjective r₂
    have hpair := congrArg (P.root' r) (c.coroot_jacobi h0)
    simpa only [map_add, map_zsmul, map_zero, root_coroot_eq_pairing, he] using hpair
  root_jacobi i₂ j₂ k₂ l₂ := by
    obtain ⟨i, rfl⟩ := e.surjective i₂
    obtain ⟨j, rfl⟩ := e.surjective j₂
    obtain ⟨k, rfl⟩ := e.surjective k₂
    obtain ⟨l, rfl⟩ := e.surjective l₂
    rw [tripleRootCoeff_comp_symm e he, tripleRootCoeff_comp_symm e he,
      tripleRootCoeff_comp_symm e he]
    exact c.root_jacobi i j k l

@[simp]
theorem reindex_structConst_apply (c : P.ChevalleyConstants) (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairing (e i) (e j) = P.pairing i j) (i j : ι) :
    (c.reindex e he).structConst (e i) (e j) = c.structConst i j := by
  simp [reindex]

@[simp]
theorem reindex_structConst_symm (c : P.ChevalleyConstants) (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairing (e i) (e j) = P.pairing i j) (i₂ j₂ : ι₂) :
    (c.reindex e he).structConst i₂ j₂ = c.structConst (e.symm i₂) (e.symm j₂) :=
  (rfl)

end Reindex

end ChevalleyConstants

/-! ## Universal property and functoriality of `ChevalleyLieAlgebra` -/

namespace ChevalleyLieAlgebra

variable {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
  {P : RootPairing ι ℤ X Y} (c : P.ChevalleyConstants)

/-- The unique `ℤ`-linear map out of `ChevalleyLieAlgebra c` with prescribed values `γ` on `Y` and
`r` on the root vectors. -/
noncomputable def liftLinear {M : Type*} [AddCommGroup M] (γ : Y →ₗ[ℤ] M) (r : ι → M) :
    ChevalleyLieAlgebra c →ₗ[ℤ] M :=
  (γ.coprod (Finsupp.linearCombination ℤ r)) ∘ₗ (equivProd c).toLinearMap

@[simp]
theorem liftLinear_cartan {M : Type*} [AddCommGroup M] (γ : Y →ₗ[ℤ] M) (r : ι → M) (y : Y) :
    liftLinear c γ r (cartan c y) = γ y := by
  simp [liftLinear]

@[simp]
theorem liftLinear_root {M : Type*} [AddCommGroup M] (γ : Y →ₗ[ℤ] M) (r : ι → M) (i : ι) :
    liftLinear c γ r (root c i) = r i := by
  simp [liftLinear]

/-- **Universal property of `ChevalleyLieAlgebra c`.** Any `ℤ`-linear Cartan map `γ : Y →ₗ[ℤ] L`
and root-vector family `r : ι → L` in a Lie ring `L` satisfying the Cartan-Cartan, Cartan-root,
opposite-root, root-sum, and non-root bracket relations extend uniquely to a `ℤ`-Lie algebra
homomorphism `ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ L`. -/
noncomputable def liftLieHom {L : Type*} [LieRing L]
    (γ : Y →ₗ[ℤ] L) (r : ι → L)
    (hcc : ∀ y z, ⁅γ y, γ z⁆ = 0)
    (hcr : ∀ y i, ⁅γ y, r i⁆ = P.toLinearMap (P.root i) y • r i)
    (hopp : ∀ {i j}, P.root i + P.root j = 0 → ⁅r i, r j⁆ = γ (P.coroot i))
    (hsum : ∀ {i j k}, P.root k = P.root i + P.root j → ⁅r i, r j⁆ = c.structConst i j • r k)
    (hzero : ∀ {i j}, P.root i + P.root j ∉ range P.root → P.root i + P.root j ≠ 0 →
      ⁅r i, r j⁆ = 0) :
    ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ L :=
  let f := liftLinear c γ r
  let lhs : ChevalleyLieAlgebra c →ₗ[ℤ] ChevalleyLieAlgebra c →ₗ[ℤ] L :=
    LinearMap.mk₂ ℤ (fun x y ↦ f ⁅x, y⁆)
      (fun x y z ↦ by rw [add_lie, map_add])
      (fun r x y ↦ by rw [zsmul_lie, map_smul])
      (fun x y z ↦ by rw [lie_add, map_add])
      (fun r x y ↦ by rw [lie_zsmul, map_smul])
  let rhs : ChevalleyLieAlgebra c →ₗ[ℤ] ChevalleyLieAlgebra c →ₗ[ℤ] L :=
    LinearMap.mk₂ ℤ (fun x y ↦ ⁅f x, f y⁆)
      (fun x y z ↦ by rw [map_add, add_lie])
      (fun r x y ↦ by rw [map_smul, zsmul_lie])
      (fun x y z ↦ by rw [map_add, lie_add])
      (fun r x y ↦ by rw [map_smul, lie_zsmul])
  { f with
    map_lie' := fun {x y} ↦ by
      have key : lhs = rhs := by
        refine linearMap_ext (fun y₁ ↦ linearMap_ext (fun y₂ ↦ ?_) fun j ↦ ?_)
          fun i ↦ linearMap_ext (fun y₂ ↦ ?_) fun j ↦ ?_ <;>
          simp only [LinearMap.mk₂_apply, lhs, rhs, f, liftLinear_cartan, liftLinear_root]
        · rw [cartan_lie_cartan, map_zero, hcc]
        · rw [cartan_lie_root, map_smul, liftLinear_root, hcr]
        · rw [root_lie_cartan, map_neg, map_smul, liftLinear_root, ← lie_skew (r i) (γ y₂), hcr]
        · rw [root_lie_root]
          by_cases h0 : P.root i + P.root j = 0
          · rw [rootBracket_of_add_eq_zero c h0, liftLinear_cartan, hopp h0]
          · by_cases hex : ∃ k, P.root k = P.root i + P.root j
            · obtain ⟨k, hk⟩ := hex
              rw [rootBracket_of_root_eq_add c hk, map_smul, liftLinear_root, hsum hk]
            · have hnot : P.root i + P.root j ∉ range P.root := fun ⟨k, hk⟩ ↦ hex ⟨k, hk⟩
              rw [rootBracket_of_notMem_of_add_ne_zero c hnot h0, map_zero, hzero hnot h0]
      exact congr($key x y) }

@[simp]
theorem liftLieHom_cartan {L : Type*} [LieRing L]
    (γ : Y →ₗ[ℤ] L) (r : ι → L) (hcc) (hcr) (hopp) (hsum) (hzero) (y : Y) :
    liftLieHom c γ r hcc hcr hopp hsum hzero (cartan c y) = γ y := by
  change liftLinear c γ r (cartan c y) = γ y
  exact liftLinear_cartan c γ r y

@[simp]
theorem liftLieHom_root {L : Type*} [LieRing L]
    (γ : Y →ₗ[ℤ] L) (r : ι → L) (hcc) (hcr) (hopp) (hsum) (hzero) (i : ι) :
    liftLieHom c γ r hcc hcr hopp hsum hzero (root c i) = r i := by
  change liftLinear c γ r (root c i) = r i
  exact liftLinear_root c γ r i

variable {c} in
theorem lieHom_ext {L : Type*} [LieRing L]
    {f g : ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ L}
    (hc : ∀ y, f (cartan c y) = g (cartan c y))
    (hr : ∀ i, f (root c i) = g (root c i)) : f = g := by
  ext x
  exact LinearMap.congr_fun (linearMap_ext hc hr) x

/-- **The Chevalley involution** of `ChevalleyLieAlgebra c`: the involutive Lie automorphism
sending `H_y ↦ -H_y` and `eᵢ ↦ -e_{-i}`. -/
noncomputable def chevalleyInvolution : ChevalleyLieAlgebra c ≃ₗ⁅ℤ⁆ ChevalleyLieAlgebra c := by
  let φ : ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ ChevalleyLieAlgebra c :=
    liftLieHom c (-cartan c) (fun i ↦ -root c (P.reflectionPerm i i))
      (fun y z ↦ by simp)
      (fun y i ↦ by simp)
      (fun {i j} h0 ↦ by
        have h0' : P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) = 0 := by
          rw [root_reflectionPerm, root_reflectionPerm, reflection_apply_self,
            reflection_apply_self, ← neg_add_rev, add_comm (P.root j), h0, neg_zero]
        simp [root_lie_root_of_add_eq_zero c h0'])
      (fun {i j k} hk ↦ by
        have hk' : P.root (P.reflectionPerm k k) =
            P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) := by
          rw [root_reflectionPerm, root_reflectionPerm, root_reflectionPerm, reflection_apply_self,
            reflection_apply_self, reflection_apply_self, hk]
          abel
        simp [root_lie_root_of_root_eq_add c hk', c.structConst_reflectionPerm])
      (fun {i j} hnot hne ↦ by
        have hnot' : P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) ∉
            range P.root := by
          rintro ⟨k, hk⟩
          refine hnot ⟨P.reflectionPerm k k, ?_⟩
          rw [root_reflectionPerm, reflection_apply_self]
          rw [root_reflectionPerm, reflection_apply_self, root_reflectionPerm,
            reflection_apply_self] at hk
          rw [hk]; abel
        have hne' : P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) ≠ 0 := by
          intro h0
          apply hne
          rw [root_reflectionPerm, root_reflectionPerm, reflection_apply_self,
            reflection_apply_self] at h0
          calc P.root i + P.root j = -(-P.root i + -P.root j) := by abel
            _ = 0 := by rw [h0, neg_zero]
        simp [root_lie_root_of_notMem_of_add_ne_zero c hnot' hne'])
  have hinv : φ.comp φ = LieHom.id := by
    refine lieHom_ext (fun y ↦ by simp [φ]) fun i ↦ ?_
    have hneg : P.reflectionPerm (P.reflectionPerm i i) (P.reflectionPerm i i) = i :=
      P.indexNeg.neg_neg i
    simp [φ, hneg]
  exact { toLieHom := φ, invFun := φ, left_inv := fun x ↦ congr($hinv x),
          right_inv := fun x ↦ congr($hinv x) }

@[simp]
private theorem coe_lieEquiv_mk {L₁ L₂ : Type*} [LieRing L₁] [LieRing L₂]
    (f : L₁ →ₗ⁅ℤ⁆ L₂) (g hl hr) (x : L₁) :
    ({ toLieHom := f, invFun := g, left_inv := hl, right_inv := hr } : L₁ ≃ₗ⁅ℤ⁆ L₂) x = f x :=
  rfl

@[simp]
theorem chevalleyInvolution_cartan (y : Y) :
    chevalleyInvolution c (cartan c y) = -cartan c y := by
  simp [chevalleyInvolution]

@[simp]
theorem chevalleyInvolution_root (i : ι) :
    chevalleyInvolution c (root c i) = -root c (P.reflectionPerm i i) := by
  simp [chevalleyInvolution]

@[simp]
theorem chevalleyInvolution_apply_apply (x : ChevalleyLieAlgebra c) :
    chevalleyInvolution c (chevalleyInvolution c x) = x :=
  (chevalleyInvolution c).left_inv x

/-- **Lie isomorphism induced by a sign twist** `s : ι → ℤˣ` invariant under root opposition,
sending `H_y ↦ H_y` and `eᵢ ↦ s(i) • eᵢ`. -/
noncomputable def twistLieEquiv (s : ι → ℤˣ) (hs : ∀ i, s (P.reflectionPerm i i) = s i) :
    ChevalleyLieAlgebra (c.twist s hs) ≃ₗ⁅ℤ⁆ ChevalleyLieAlgebra c := by
  let c' := c.twist s hs
  let toHom : ChevalleyLieAlgebra c' →ₗ⁅ℤ⁆ ChevalleyLieAlgebra c :=
    liftLieHom c' (cartan c) (fun i ↦ (s i : ℤ) • root c i)
      (fun y z ↦ by simp)
      (fun y i ↦ by rw [lie_smul, cartan_lie_root, smul_comm])
      (fun {i j} h0 ↦ by
        have hji : j = P.reflectionPerm i i :=
          P.root_eq_neg_iff.mp (add_eq_zero_iff_eq_neg.mp (by rw [add_comm]; exact h0))
        have h1 : (s i : ℤ) * (s j : ℤ) = 1 := by
          rw [hji, hs i, ← Units.val_mul, Int.units_mul_self, Units.val_one]
        rw [smul_lie, lie_smul, smul_smul, h1, one_smul, root_lie_root_of_add_eq_zero c h0])
      (fun {i j k} hk ↦ by
        rw [smul_lie, lie_smul, root_lie_root_of_root_eq_add c hk,
          c.twist_structConst_of_root_eq_add s hs hk]
        have hunit : (s i : ℤ) * (s j : ℤ) * c.structConst i j =
            (((s i * s j * s k : ℤˣ) : ℤ) * c.structConst i j) * (s k : ℤ) := by
          calc (s i : ℤ) * (s j : ℤ) * c.structConst i j
              = ((s i : ℤ) * (s j : ℤ) * ((s k * s k : ℤˣ) : ℤ)) * c.structConst i j := by
                rw [Int.units_mul_self, Units.val_one, mul_one]
            _ = (((s i * s j * s k : ℤˣ) : ℤ) * c.structConst i j) * (s k : ℤ) := by
                simp only [Units.val_mul]; ring
        rw [smul_smul, smul_smul, smul_smul, hunit])
      (fun {i j} hnot hne ↦ by
        rw [smul_lie, lie_smul, root_lie_root_of_notMem_of_add_ne_zero c hnot hne, smul_zero,
          smul_zero])
  let invHom : ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ ChevalleyLieAlgebra c' :=
    liftLieHom c (cartan c') (fun i ↦ (s i : ℤ) • root c' i)
      (fun y z ↦ by simp)
      (fun y i ↦ by rw [lie_smul, cartan_lie_root, smul_comm])
      (fun {i j} h0 ↦ by
        have hji : j = P.reflectionPerm i i :=
          P.root_eq_neg_iff.mp (add_eq_zero_iff_eq_neg.mp (by rw [add_comm]; exact h0))
        have h1 : (s i : ℤ) * (s j : ℤ) = 1 := by
          rw [hji, hs i, ← Units.val_mul, Int.units_mul_self, Units.val_one]
        rw [smul_lie, lie_smul, smul_smul, h1, one_smul, root_lie_root_of_add_eq_zero c' h0])
      (fun {i j k} hk ↦ by
        rw [smul_lie, lie_smul, root_lie_root_of_root_eq_add c' hk,
          c.twist_structConst_of_root_eq_add s hs hk]
        have hunit : (s i : ℤ) * (s j : ℤ) * (((s i * s j * s k : ℤˣ) : ℤ) * c.structConst i j) =
            c.structConst i j * (s k : ℤ) := by
          have h1 : ((s i * s i : ℤˣ) : ℤ) = 1 := by rw [Int.units_mul_self, Units.val_one]
          have h2 : ((s j * s j : ℤˣ) : ℤ) = 1 := by rw [Int.units_mul_self, Units.val_one]
          simp only [Units.val_mul] at h1 h2 ⊢
          calc (s i : ℤ) * (s j : ℤ) * ((s i : ℤ) * (s j : ℤ) * (s k : ℤ) * c.structConst i j)
              = ((s i : ℤ) * (s i : ℤ)) * ((s j : ℤ) * (s j : ℤ)) *
                  (c.structConst i j * (s k : ℤ)) := by ring
            _ = c.structConst i j * (s k : ℤ) := by rw [h1, h2, one_mul, one_mul]
        rw [smul_smul, smul_smul, smul_smul, hunit])
      (fun {i j} hnot hne ↦ by
        rw [smul_lie, lie_smul, root_lie_root_of_notMem_of_add_ne_zero c' hnot hne, smul_zero,
          smul_zero])
  have hleft : invHom.comp toHom = LieHom.id := by
    refine lieHom_ext (fun y ↦ by simp [toHom, invHom]) fun i ↦ ?_
    have h1 : (s i : ℤ) * (s i : ℤ) = 1 := by
      rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
    simp [toHom, invHom, smul_smul, h1]
  have hright : toHom.comp invHom = LieHom.id := by
    refine lieHom_ext (fun y ↦ by simp [toHom, invHom]) fun i ↦ ?_
    have h1 : (s i : ℤ) * (s i : ℤ) = 1 := by
      rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
    simp [toHom, invHom, smul_smul, h1]
  exact { toLieHom := toHom, invFun := invHom, left_inv := fun x ↦ congr($hleft x),
          right_inv := fun x ↦ congr($hright x) }

@[simp]
theorem twistLieEquiv_cartan (s : ι → ℤˣ) (hs : ∀ i, s (P.reflectionPerm i i) = s i) (y : Y) :
    twistLieEquiv c s hs (cartan (c.twist s hs) y) = cartan c y := by
  simp [twistLieEquiv]

@[simp]
theorem twistLieEquiv_root (s : ι → ℤˣ) (hs : ∀ i, s (P.reflectionPerm i i) = s i) (i : ι) :
    twistLieEquiv c s hs (root (c.twist s hs) i) = (s i : ℤ) • root c i := by
  simp [twistLieEquiv]

@[simp]
theorem twistLieEquiv_symm_cartan (s : ι → ℤˣ) (hs : ∀ i, s (P.reflectionPerm i i) = s i) (y : Y) :
    (twistLieEquiv c s hs).symm (cartan c y) = cartan (c.twist s hs) y :=
  (twistLieEquiv c s hs).symm_apply_eq.mpr (twistLieEquiv_cartan c s hs y).symm

@[simp]
theorem twistLieEquiv_symm_root (s : ι → ℤˣ) (hs : ∀ i, s (P.reflectionPerm i i) = s i) (i : ι) :
    (twistLieEquiv c s hs).symm (root c i) = (s i : ℤ) • root (c.twist s hs) i := by
  rw [(twistLieEquiv c s hs).symm_apply_eq, map_smul, twistLieEquiv_root, smul_smul]
  have h1 : (s i : ℤ) * (s i : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  rw [h1, one_smul]

section Map

variable {ι₂ X₂ Y₂ : Type*} [Finite ι₂] [AddCommGroup X₂] [AddCommGroup Y₂]
  {P₂ : RootPairing ι₂ ℤ X₂ Y₂} (c₂ : P₂.ChevalleyConstants)

/-- **Covariant functoriality of `ChevalleyLieAlgebra`.** A cocharacter map `γ : Y →ₗ[ℤ] Y₂` and a
root-index bijection `e : ι ≃ ι₂` preserving root evaluations, coroots, and Chevalley structure
constants induce a `ℤ`-Lie algebra homomorphism `ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ ChevalleyLieAlgebra c₂`
(covering central extensions, central isogenies, and quotients by central tori without splitting
`Y` or `Y₂`). -/
noncomputable def mapLieHom (γ : Y →ₗ[ℤ] Y₂) (e : ι ≃ ι₂)
    (hpair : ∀ i y, P₂.toLinearMap (P₂.root (e i)) (γ y) = P.toLinearMap (P.root i) y)
    (hcoroot : ∀ i, γ (P.coroot i) = P₂.coroot (e i))
    (hconst : ∀ i j, P.root i + P.root j ∈ range P.root →
      c₂.structConst (e i) (e j) = c.structConst i j) :
    ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ ChevalleyLieAlgebra c₂ := by
  have heIn : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j :=
    ChevalleyConstants.pairingIn_eq_of_pairing e fun i j ↦ by
      have h := hpair i (P.coroot j)
      rwa [hcoroot j, P₂.root_coroot_eq_pairing, P.root_coroot_eq_pairing] at h
  exact liftLieHom c (cartan c₂ ∘ₗ γ) (fun i ↦ root c₂ (e i))
    (fun y z ↦ by simp)
    (fun y i ↦ by simp [hpair])
    (fun {i j} h0 ↦ by
      have h0₂ := (root_add_eq_zero_iff_of_pairingIn e heIn i j).mpr h0
      simp [root_lie_root_of_add_eq_zero c₂ h0₂, hcoroot])
    (fun {i j k} hk ↦ by
      have hk₂ := (root_eq_add_iff_of_pairingIn e heIn k i j).mpr hk
      rw [root_lie_root_of_root_eq_add c₂ hk₂, hconst i j ⟨k, hk⟩])
    (fun {i j} hnot hne ↦ by
      have hnot₂ : P₂.root (e i) + P₂.root (e j) ∉ range P₂.root := by
        rintro ⟨k₂, hk₂⟩
        obtain ⟨k, rfl⟩ := e.surjective k₂
        exact hnot ⟨k, (root_eq_add_iff_of_pairingIn e heIn k i j).mp hk₂⟩
      have hne₂ := mt (root_add_eq_zero_iff_of_pairingIn e heIn i j).mp hne
      exact root_lie_root_of_notMem_of_add_ne_zero c₂ hnot₂ hne₂)

@[simp]
theorem mapLieHom_cartan (γ : Y →ₗ[ℤ] Y₂) (e : ι ≃ ι₂) (hpair) (hcoroot) (hconst) (y : Y) :
    mapLieHom c c₂ γ e hpair hcoroot hconst (cartan c y) = cartan c₂ (γ y) := by
  simp [mapLieHom]

@[simp]
theorem mapLieHom_root (γ : Y →ₗ[ℤ] Y₂) (e : ι ≃ ι₂) (hpair) (hcoroot) (hconst) (i : ι) :
    mapLieHom c c₂ γ e hpair hcoroot hconst (root c i) = root c₂ (e i) := by
  simp [mapLieHom]

/-- **Lie algebra equivalence induced by a cocharacter isomorphism** `γ : Y ≃ₗ[ℤ] Y₂` and a
root-index bijection `e : ι ≃ ι₂`. -/
noncomputable def mapLieEquiv (γ : Y ≃ₗ[ℤ] Y₂) (e : ι ≃ ι₂)
    (hpair : ∀ i y, P₂.toLinearMap (P₂.root (e i)) (γ y) = P.toLinearMap (P.root i) y)
    (hcoroot : ∀ i, γ (P.coroot i) = P₂.coroot (e i))
    (hconst : ∀ i j, P.root i + P.root j ∈ range P.root →
      c₂.structConst (e i) (e j) = c.structConst i j) :
    ChevalleyLieAlgebra c ≃ₗ⁅ℤ⁆ ChevalleyLieAlgebra c₂ := by
  have heIn : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j :=
    ChevalleyConstants.pairingIn_eq_of_pairing e fun i j ↦ by
      have h := hpair i (P.coroot j)
      rwa [hcoroot j, P₂.root_coroot_eq_pairing, P.root_coroot_eq_pairing] at h
  let f := mapLieHom c c₂ γ.toLinearMap e hpair hcoroot hconst
  let g := mapLieHom c₂ c γ.symm.toLinearMap e.symm
    (fun i₂ y₂ ↦ by
      have h := hpair (e.symm i₂) (γ.symm y₂)
      simpa using h.symm)
    (fun i₂ ↦ γ.injective (by simp [hcoroot]))
    (fun i₂ j₂ ⟨k₂, hk₂⟩ ↦ by
      obtain ⟨i, rfl⟩ := e.surjective i₂
      obtain ⟨j, rfl⟩ := e.surjective j₂
      obtain ⟨k, rfl⟩ := e.surjective k₂
      have hk := (root_eq_add_iff_of_pairingIn e heIn k i j).mp hk₂
      simpa using (hconst i j ⟨k, hk⟩).symm)
  have hleft : g.comp f = LieHom.id :=
    lieHom_ext (fun y ↦ by simp [f, g]) fun i ↦ by simp [f, g]
  have hright : f.comp g = LieHom.id :=
    lieHom_ext (fun y₂ ↦ by simp [f, g]) fun i₂ ↦ by simp [f, g]
  exact { toLieHom := f, invFun := g, left_inv := fun x ↦ congr($hleft x),
          right_inv := fun x ↦ congr($hright x) }

@[simp]
theorem mapLieEquiv_cartan (γ : Y ≃ₗ[ℤ] Y₂) (e : ι ≃ ι₂) (hpair) (hcoroot) (hconst) (y : Y) :
    mapLieEquiv c c₂ γ e hpair hcoroot hconst (cartan c y) = cartan c₂ (γ y) := by
  simp [mapLieEquiv]

@[simp]
theorem mapLieEquiv_root (γ : Y ≃ₗ[ℤ] Y₂) (e : ι ≃ ι₂) (hpair) (hcoroot) (hconst) (i : ι) :
    mapLieEquiv c c₂ γ e hpair hcoroot hconst (root c i) = root c₂ (e i) := by
  simp [mapLieEquiv]

/-- **Transport of `ChevalleyLieAlgebra` along a root-pairing equivalence `g : P.Equiv P₂`**,
acting on Cartan vectors via `g.coweightEquiv.symm` and on root vectors via `g.indexEquiv`. -/
noncomputable def equivOfRootPairingEquiv (g : P.Equiv P₂) :
    ChevalleyLieAlgebra c ≃ₗ⁅ℤ⁆
      ChevalleyLieAlgebra (c.reindex g.indexEquiv fun _ _ ↦ g.toHom.pairing) :=
  mapLieEquiv c _ g.coweightEquiv.symm g.indexEquiv
    (fun i y ↦ by
      have htr := LinearMap.congr_fun
        (Hom.weight_coweight_transpose_apply P P₂ (g.coweightEquiv.symm y) g.toHom) (P.root i)
      rw [LinearMap.dualMap_apply, Hom.root_weightMap_apply] at htr
      simpa [Equiv.coweightEquiv_apply] using htr)
    (fun i ↦ g.coweightEquiv.injective <| by
      rw [LinearEquiv.apply_symm_apply, Equiv.coweightEquiv_apply,
        Hom.coroot_coweightMap_apply P P₂ _ g.toHom, Equiv.symm_apply_apply])
    (fun _ _ _ ↦ by simp)

@[simp]
theorem equivOfRootPairingEquiv_cartan (g : P.Equiv P₂) (y : Y) :
    equivOfRootPairingEquiv c g (cartan c y) = cartan _ (g.coweightEquiv.symm y) := by
  simp [equivOfRootPairingEquiv]

@[simp]
theorem equivOfRootPairingEquiv_root (g : P.Equiv P₂) (i : ι) :
    equivOfRootPairingEquiv c g (root c i) = root _ (g.indexEquiv i) := by
  simp [equivOfRootPairingEquiv]

end Map

end ChevalleyLieAlgebra

end RootPairing
