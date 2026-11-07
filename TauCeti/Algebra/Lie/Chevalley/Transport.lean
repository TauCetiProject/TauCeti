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

* **Sign twists** (`ChevalleyConstants.twist`, `ChevalleyLieAlgebra.twistLieEquiv`): rescaling root
  vectors by opposition-invariant signs `s : ι → ℤˣ`.
* **Cartan-pairing transport** (`ChevalleyConstants.reindex`): transporting structure constants
  along any bijection `e : ι ≃ ι₂` matching integer Cartan pairings.
* **Universal property & Chevalley involution** (`ChevalleyLieAlgebra.liftLieHom`,
  `ChevalleyLieAlgebra.chevalleyInvolution`): universal maps out of `ChevalleyLieAlgebra c` and the
  automorphism `H_y ↦ -H_y`, `eᵢ ↦ -e_{-i}`.
* **Covariant functoriality** (`ChevalleyLieAlgebra.mapLieHom`, `ChevalleyLieAlgebra.mapLieEquiv`,
  `ChevalleyLieAlgebra.equivOfRootPairingEquiv`): maps induced by compatible cocharacter maps
  `γ : Y →ₗ[ℤ] Y₂` and root-pairing equivalences.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016), §§1--3.
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
  if h : ∃ k, P.root k = P.root i + P.root j then ((s i * s j * s h.choose : ℤˣ) : ℤ) * N i j
  else 0

omit [Finite ι] in
private theorem twistConst_of_root_eq_add {N : ι → ι → ℤ} {s : ι → ℤˣ} {i j k : ι}
    (hk : P.root k = P.root i + P.root j) :
    twistConst P N s i j = ((s i * s j * s k : ℤˣ) : ℤ) * N i j := by
  classical
  have hex : ∃ m, P.root m = P.root i + P.root j := ⟨k, hk⟩
  rw [twistConst, dite_eq_left hex, P.root.injective (hex.choose_spec.trans hk.symm)]

omit [Finite ι] in
private theorem twistConst_of_notMem_range {N : ι → ι → ℤ} {s : ι → ℤˣ} {i j : ι}
    (hnot : P.root i + P.root j ∉ range P.root) : twistConst P N s i j = 0 := by
  classical exact dite_eq_right fun ⟨k, hk⟩ ↦ hnot ⟨k, hk⟩

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
        P.root_eq_neg_iff.mp (add_eq_zero_iff_eq_neg.mp (add_comm (P.root j) (P.root k) ▸ hjk0))
      have hunit : s l * s j * s k * s l = 1 := by
        rw [hkj, hs j, (by ac_rfl : s l * s j * s j * s l = (s l * s l) * (s j * s j)),
          Int.units_mul_self, Int.units_mul_self, one_mul]
      rw [ite_eq_left rfl, hunit, Units.val_one, one_mul]
    · rw [ite_eq_right hli, mul_zero]
  · by_cases hex : ∃ m, P.root m = P.root j + P.root k
    · obtain ⟨m, hm⟩ := hex
      rw [P.tripleRootCoeff_of_root_eq_add _ hm, P.tripleRootCoeff_of_root_eq_add _ hm]
      by_cases hlm : P.root l = P.root i + P.root m
      · rw [ite_eq_left hlm, ite_eq_left hlm, twistConst_of_root_eq_add hlm,
          twistConst_of_root_eq_add hm]
        have hunit : (s i * s m * s l) * (s j * s k * s m) = s i * s j * s k * s l := by
          rw [(by ac_rfl : (s i * s m * s l) * (s j * s k * s m) =
            (s i * s j * s k * s l) * (s m * s m)), Int.units_mul_self, mul_one]
        rw [← hunit]; simp only [Units.val_mul]; ring
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
  structConst_eq_zero_of_notMem_range _ _ := twistConst_of_notMem_range
  structConst_swap i j := by
    by_cases hex : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hex
      rw [twistConst_of_root_eq_add (hk.trans (add_comm (P.root i) (P.root j))),
        twistConst_of_root_eq_add hk, c.structConst_swap i j, mul_comm (s j) (s i), mul_neg]
    · have hnot : P.root i + P.root j ∉ range P.root := fun ⟨k, hk⟩ ↦ hex ⟨k, hk⟩
      rw [twistConst_of_notMem_range (add_comm (P.root i) (P.root j) ▸ hnot),
        twistConst_of_notMem_range hnot, neg_zero]
  natAbs_structConst {i j k} hk := by
    rw [twistConst_of_root_eq_add hk, Int.natAbs_mul, Int.units_natAbs, one_mul,
      c.natAbs_structConst hk]
  structConst_reflectionPerm i j := by
    by_cases hex : ∃ k, P.root k = P.root i + P.root j
    · obtain ⟨k, hk⟩ := hex
      have hk' : P.root (P.reflectionPerm k k) =
          P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) := by
        simp only [root_reflectionPerm, reflection_apply_self]; rw [hk]; abel
      rw [twistConst_of_root_eq_add hk', twistConst_of_root_eq_add hk, hs i, hs j, hs k,
        c.structConst_reflectionPerm, mul_neg]
    · have hnot : P.root i + P.root j ∉ range P.root := fun ⟨k, hk⟩ ↦ hex ⟨k, hk⟩
      rw [twistConst_of_notMem_range (mt (P.root_reflectionPerm_add_mem_range_iff i j).mp hnot),
        twistConst_of_notMem_range hnot, neg_zero]
  coroot_jacobi {i j k} h0 := by
    have h1 : P.root j + P.root k + P.root i = 0 := by rw [← h0]; abel
    have h2 : P.root k + P.root i + P.root j = 0 := by rw [← h0]; abel
    rw [twistConst_of_root_eq_add (root_reflectionPerm_self_eq_add_of_add_add_eq_zero h0),
      twistConst_of_root_eq_add (root_reflectionPerm_self_eq_add_of_add_add_eq_zero h1),
      twistConst_of_root_eq_add (root_reflectionPerm_self_eq_add_of_add_add_eq_zero h2),
      hs i, hs j, hs k,
      (by ac_rfl : s j * s k * s i = s i * s j * s k),
      (by ac_rfl : s k * s i * s j = s i * s j * s k),
      mul_smul, mul_smul, mul_smul, ← smul_add, ← smul_add, c.coroot_jacobi h0, smul_zero]
  root_jacobi i j k l := by
    rw [tripleRootCoeff_twistConst c s hs i j k l, tripleRootCoeff_twistConst c s hs j k i l,
      tripleRootCoeff_twistConst c s hs k i j l,
      (by ac_rfl : s j * s k * s i * s l = s i * s j * s k * s l),
      (by ac_rfl : s k * s i * s j * s l = s i * s j * s k * s l),
      ← mul_add, ← mul_add, c.root_jacobi i j k l, mul_zero]

theorem twist_structConst_of_root_eq_add (c : P.ChevalleyConstants) (s : ι → ℤˣ)
    (hs : ∀ i, s (P.reflectionPerm i i) = s i) {i j k : ι}
    (hk : P.root k = P.root i + P.root j) :
    (c.twist s hs).structConst i j = ((s i * s j * s k : ℤˣ) : ℤ) * c.structConst i j :=
  twistConst_of_root_eq_add hk

/-- Twisting twice by the same opposition-invariant sign function recovers the original table. -/
@[simp]
theorem twist_twist (c : P.ChevalleyConstants) (s : ι → ℤˣ)
    (hs : ∀ i, s (P.reflectionPerm i i) = s i) : (c.twist s hs).twist s hs = c := by
  refine ext_of_mem_range fun i j ⟨k, hk⟩ ↦ ?_
  rw [twist_structConst_of_root_eq_add _ s hs hk, twist_structConst_of_root_eq_add _ s hs hk,
    ← mul_assoc, ← Units.val_mul,
    (by ac_rfl : (s i * s j * s k) * (s i * s j * s k) = (s i * s i) * (s j * s j) * (s k * s k))]
  simp [Int.units_mul_self]

end Twist

section Reindex

variable {ι ι₂ X Y X₂ Y₂ : Type*} [Finite ι] [Finite ι₂]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X₂] [AddCommGroup Y₂]
  {P : RootPairing ι ℤ X Y} {P₂ : RootPairing ι₂ ℤ X₂ Y₂}

omit [Finite ι₂] in
private theorem tripleRootCoeff_comp_symm (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairing (e i) (e j) = P.pairing i j) (N : ι → ι → ℤ) (i j k l : ι) :
    P₂.tripleRootCoeff (fun a b ↦ N (e.symm a) (e.symm b)) (e i) (e j) (e k) (e l) =
      P.tripleRootCoeff N i j k l := by
  classical
  have heIn (a b : ι) : P₂.pairingIn ℤ (e a) (e b) = P.pairingIn ℤ a b := by simp [he]
  by_cases hjk0 : P.root j + P.root k = 0
  · rw [P₂.tripleRootCoeff_of_add_eq_zero _
        ((root_add_eq_zero_iff_of_pairingIn e heIn j k).mpr hjk0),
      P.tripleRootCoeff_of_add_eq_zero _ hjk0, he i j, e.injective.eq_iff]
  · have hjk0₂ := mt (root_add_eq_zero_iff_of_pairingIn e heIn j k).mp hjk0
    by_cases hex : ∃ m, P.root m = P.root j + P.root k
    · obtain ⟨m, hm⟩ := hex
      rw [P₂.tripleRootCoeff_of_root_eq_add _ ((root_eq_add_iff_of_pairingIn e heIn m j k).mpr hm),
        P.tripleRootCoeff_of_root_eq_add _ hm, root_eq_add_iff_of_pairingIn e heIn l i m]; simp
    · have hnot : P.root j + P.root k ∉ range P.root := fun ⟨m, hm⟩ ↦ hex ⟨m, hm⟩
      rw [P₂.tripleRootCoeff_of_notMem_of_add_ne_zero _
          (mt (root_add_mem_range_iff_of_pairingIn e heIn j k).mp hnot) hjk0₂,
        P.tripleRootCoeff_of_notMem_of_add_ne_zero _ hnot hjk0]

/-- **Transport of Chevalley structure constants along Cartan-matching root bijections.** Any
bijection `e : ι ≃ ι₂` preserving integer Cartan pairings transports `c : P.ChevalleyConstants` to
`P₂.ChevalleyConstants`, with no assumption relating the ambient lattices `(X, Y)` and `(X₂, Y₂)`
beyond their root-coroot pairings. -/
def reindex (c : P.ChevalleyConstants) (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairing (e i) (e j) = P.pairing i j) : P₂.ChevalleyConstants where
  structConst i₂ j₂ := c.structConst (e.symm i₂) (e.symm j₂)
  structConst_eq_zero_of_notMem_range i₂ j₂ hnot := by
    have heIn (a b : ι) : P₂.pairingIn ℤ (e a) (e b) = P.pairingIn ℤ a b := by simp [he]
    refine c.structConst_eq_zero_of_notMem_range _ _ fun hmem ↦ hnot ?_
    simpa using (root_add_mem_range_iff_of_pairingIn e heIn (e.symm i₂) (e.symm j₂)).mpr hmem
  structConst_swap i₂ j₂ := c.structConst_swap _ _
  natAbs_structConst {i₂ j₂ k₂} hk₂ := by
    have heIn (a b : ι) : P₂.pairingIn ℤ (e a) (e b) = P.pairingIn ℤ a b := by simp [he]
    obtain ⟨i, rfl⟩ := e.surjective i₂; obtain ⟨j, rfl⟩ := e.surjective j₂
    obtain ⟨k, rfl⟩ := e.surjective k₂
    simpa [chainBotCoeff_eq_of_pairingIn e heIn i j] using
      c.natAbs_structConst ((root_eq_add_iff_of_pairingIn e heIn k i j).mp hk₂)
  structConst_reflectionPerm i₂ j₂ := by
    have heIn (a b : ι) : P₂.pairingIn ℤ (e a) (e b) = P.pairingIn ℤ a b := by simp [he]
    obtain ⟨i, rfl⟩ := e.surjective i₂; obtain ⟨j, rfl⟩ := e.surjective j₂
    simp only [← map_reflectionPerm_of_pairingIn e heIn, Equiv.symm_apply_apply]
    exact c.structConst_reflectionPerm i j
  coroot_jacobi {i₂ j₂ k₂} h0₂ := by
    have heIn (a b : ι) : P₂.pairingIn ℤ (e a) (e b) = P.pairingIn ℤ a b := by simp [he]
    obtain ⟨i, rfl⟩ := e.surjective i₂; obtain ⟨j, rfl⟩ := e.surjective j₂
    obtain ⟨k, rfl⟩ := e.surjective k₂
    simp only [Equiv.symm_apply_apply]
    have h0 := (root_add_add_eq_zero_iff_of_pairingIn e heIn i j k).mp h0₂
    have hc (x) : P₂.coroot x ∈ P₂.corootSpan ℤ := Submodule.subset_span (mem_range_self _)
    refine P₂.eq_zero_of_mem_corootSpan_of_forall_root'_eq_zero
      (add_mem (add_mem (Submodule.smul_mem _ _ (hc _)) (Submodule.smul_mem _ _ (hc _)))
        (Submodule.smul_mem _ _ (hc _))) fun r₂ ↦ ?_
    obtain ⟨r, rfl⟩ := e.surjective r₂
    simpa only [map_add, map_zsmul, map_zero, root_coroot_eq_pairing, he] using
      congrArg (P.root' r) (c.coroot_jacobi h0)
  root_jacobi i₂ j₂ k₂ l₂ := by
    obtain ⟨i, rfl⟩ := e.surjective i₂; obtain ⟨j, rfl⟩ := e.surjective j₂
    obtain ⟨k, rfl⟩ := e.surjective k₂; obtain ⟨l, rfl⟩ := e.surjective l₂
    simpa only [tripleRootCoeff_comp_symm e he] using c.root_jacobi i j k l

theorem reindex_structConst_apply (c : P.ChevalleyConstants) (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairing (e i) (e j) = P.pairing i j) (i j : ι) :
    (c.reindex e he).structConst (e i) (e j) = c.structConst i j := by simp [reindex]

@[simp]
theorem reindex_structConst_symm (c : P.ChevalleyConstants) (e : ι ≃ ι₂)
    (he : ∀ i j, P₂.pairing (e i) (e j) = P.pairing i j) (i₂ j₂ : ι₂) :
    (c.reindex e he).structConst i₂ j₂ = c.structConst (e.symm i₂) (e.symm j₂) := by rfl

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
    liftLinear c γ r (cartan c y) = γ y := by simp [liftLinear]

@[simp]
theorem liftLinear_root {M : Type*} [AddCommGroup M] (γ : Y →ₗ[ℤ] M) (r : ι → M) (i : ι) :
    liftLinear c γ r (root c i) = r i := by simp [liftLinear]

/-- **Universal property of `ChevalleyLieAlgebra c`.** Any `ℤ`-linear Cartan map `γ : Y →ₗ[ℤ] L`
and root-vector family `r : ι → L` in a Lie ring `L` satisfying the Cartan-Cartan, Cartan-root,
opposite-root, root-sum, and non-root bracket relations extend uniquely to a `ℤ`-Lie algebra
homomorphism `ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ L`. -/
noncomputable def liftLieHom {L : Type*} [LieRing L] (γ : Y →ₗ[ℤ] L) (r : ι → L)
    (hcc : ∀ y z, ⁅γ y, γ z⁆ = 0)
    (hcr : ∀ y i, ⁅γ y, r i⁆ = P.toLinearMap (P.root i) y • r i)
    (hopp : ∀ {i j}, P.root i + P.root j = 0 → ⁅r i, r j⁆ = γ (P.coroot i))
    (hsum : ∀ {i j k}, P.root k = P.root i + P.root j → ⁅r i, r j⁆ = c.structConst i j • r k)
    (hzero : ∀ {i j}, P.root i + P.root j ∉ range P.root → P.root i + P.root j ≠ 0 →
      ⁅r i, r j⁆ = 0) :
    ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ L :=
  let f := liftLinear c γ r
  let lhs := LinearMap.mk₂ ℤ (fun x y : ChevalleyLieAlgebra c ↦ f ⁅x, y⁆)
    (fun _ _ _ ↦ by rw [add_lie, map_add]) (fun _ _ _ ↦ by rw [zsmul_lie, map_smul])
    (fun _ _ _ ↦ by rw [lie_add, map_add]) (fun _ _ _ ↦ by rw [lie_zsmul, map_smul])
  let rhs := LinearMap.mk₂ ℤ (fun x y : ChevalleyLieAlgebra c ↦ ⁅f x, f y⁆)
    (fun _ _ _ ↦ by rw [map_add, add_lie]) (fun _ _ _ ↦ by rw [map_smul, zsmul_lie])
    (fun _ _ _ ↦ by rw [map_add, lie_add]) (fun _ _ _ ↦ by rw [map_smul, lie_zsmul])
  { toLinearMap := f
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
      simpa [lhs, rhs] using congr($key x y) }

@[simp]
theorem liftLieHom_cartan {L : Type*} [LieRing L] (γ : Y →ₗ[ℤ] L) (r : ι → L)
    (hcc) (hcr) (hopp) (hsum) (hzero) (y : Y) :
    liftLieHom c γ r hcc hcr hopp hsum hzero (cartan c y) = γ y := by
  exact liftLinear_cartan c γ r y

@[simp]
theorem liftLieHom_root {L : Type*} [LieRing L] (γ : Y →ₗ[ℤ] L) (r : ι → L)
    (hcc) (hcr) (hopp) (hsum) (hzero) (i : ι) :
    liftLieHom c γ r hcc hcr hopp hsum hzero (root c i) = r i := by
  exact liftLinear_root c γ r i

variable {c} in
theorem lieHom_ext {L : Type*} [LieRing L] {f g : ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ L}
    (hc : ∀ y, f (cartan c y) = g (cartan c y)) (hr : ∀ i, f (root c i) = g (root c i)) : f = g :=
  LieHom.ext fun x ↦ LinearMap.congr_fun (linearMap_ext hc hr) x

/-- **The Chevalley involution** of `ChevalleyLieAlgebra c`: the involutive Lie automorphism
sending `H_y ↦ -H_y` and `eᵢ ↦ -e_{-i}`. -/
noncomputable def chevalleyInvolution : ChevalleyLieAlgebra c ≃ₗ⁅ℤ⁆ ChevalleyLieAlgebra c := by
  let φ : ChevalleyLieAlgebra c →ₗ⁅ℤ⁆ ChevalleyLieAlgebra c :=
    liftLieHom c (-cartan c) (fun i ↦ -root c (P.reflectionPerm i i))
      (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
      (fun {i j} h0 ↦ by
        have h0' : P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) = 0 := by
          simp [← neg_add_rev, add_comm (P.root j), h0]
        simp [root_lie_root_of_add_eq_zero c h0'])
      (fun {i j k} hk ↦ by
        have hk' : P.root (P.reflectionPerm k k) =
            P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) := by
          simp only [root_reflectionPerm, reflection_apply_self]; rw [hk]; abel
        simp [root_lie_root_of_root_eq_add c hk', c.structConst_reflectionPerm])
      (fun {i j} hnot hne ↦ by
        have hne' : P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) ≠ 0 := fun h0 ↦
          hne (by simpa [← neg_add_rev, add_comm] using h0)
        simp [root_lie_root_of_notMem_of_add_ne_zero c
          (mt (P.root_reflectionPerm_add_mem_range_iff i j).mp hnot) hne'])
  have hneg (i : ι) : P.reflectionPerm (P.reflectionPerm i i) (P.reflectionPerm i i) = i :=
    P.indexNeg.neg_neg i
  have hinv : φ.comp φ = LieHom.id :=
    lieHom_ext (by simp [φ]) fun i ↦ by simp [φ, hneg i]
  exact { toLieHom := φ, invFun := φ, left_inv := fun x ↦ congr($hinv x),
          right_inv := fun x ↦ congr($hinv x) }

@[simp]
private theorem coe_lieEquiv_mk {L₁ L₂ : Type*} [LieRing L₁] [LieRing L₂]
    (f : L₁ →ₗ⁅ℤ⁆ L₂) (g hl hr) (x : L₁) :
    ({ toLieHom := f, invFun := g, left_inv := hl, right_inv := hr } : L₁ ≃ₗ⁅ℤ⁆ L₂) x = f x := rfl

@[simp]
theorem chevalleyInvolution_cartan (y : Y) : chevalleyInvolution c (cartan c y) = -cartan c y := by
  simp [chevalleyInvolution]

@[simp]
theorem chevalleyInvolution_root (i : ι) :
    chevalleyInvolution c (root c i) = -root c (P.reflectionPerm i i) := by
  simp [chevalleyInvolution]

@[simp]
theorem chevalleyInvolution_apply_apply (x : ChevalleyLieAlgebra c) :
    chevalleyInvolution c (chevalleyInvolution c x) = x :=
  (chevalleyInvolution c).left_inv x

private theorem units_val_sq (u : ℤˣ) : (u : ℤ) * (u : ℤ) = 1 := by
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

variable {c} in
private noncomputable def twistLieHomOfEq {c₁ c₂ : P.ChevalleyConstants} (s : ι → ℤˣ)
    (hs : ∀ i, s (P.reflectionPerm i i) = s i) (hc : c₁ = c₂.twist s hs) :
    ChevalleyLieAlgebra c₁ →ₗ⁅ℤ⁆ ChevalleyLieAlgebra c₂ :=
  liftLieHom c₁ (cartan c₂) (fun i ↦ (s i : ℤ) • root c₂ i)
    (fun _ _ ↦ by simp)
    (fun _ _ ↦ by rw [lie_smul, cartan_lie_root, smul_comm])
    (fun {i j} h0 ↦ by
      have hji := P.root_eq_neg_iff.mp
        (add_eq_zero_iff_eq_neg.mp (add_comm (P.root i) (P.root j) ▸ h0))
      rw [smul_lie, lie_smul, smul_smul, hji, hs i, units_val_sq, one_smul,
        root_lie_root_reflectionPerm])
    (fun {i j k} hk ↦ by
      rw [smul_lie, lie_smul, root_lie_root_of_root_eq_add c₂ hk, hc,
        c₂.twist_structConst_of_root_eq_add s hs hk, smul_smul, smul_smul, smul_smul]
      congr 1
      calc (s i : ℤ) * (s j : ℤ) * c₂.structConst i j
          = (s i : ℤ) * (s j : ℤ) * ((s k : ℤ) * (s k : ℤ)) * c₂.structConst i j := by
            rw [units_val_sq, mul_one]
        _ = (((s i * s j * s k : ℤˣ) : ℤ) * c₂.structConst i j) * (s k : ℤ) := by
            simp only [Units.val_mul]; ring)
    (fun {_ _} hnot hne ↦ by
      rw [smul_lie, lie_smul, root_lie_root_of_notMem_of_add_ne_zero c₂ hnot hne, smul_zero,
        smul_zero])

/-- **Lie isomorphism induced by a sign twist** `s : ι → ℤˣ` invariant under root opposition,
sending `H_y ↦ H_y` and `eᵢ ↦ s(i) • eᵢ`. -/
noncomputable def twistLieEquiv (s : ι → ℤˣ) (hs : ∀ i, s (P.reflectionPerm i i) = s i) :
    ChevalleyLieAlgebra (c.twist s hs) ≃ₗ⁅ℤ⁆ ChevalleyLieAlgebra c := by
  let toHom := twistLieHomOfEq (c₁ := c.twist s hs) (c₂ := c) s hs rfl
  let invHom := twistLieHomOfEq (c₁ := c) (c₂ := c.twist s hs) s hs (c.twist_twist s hs).symm
  have hleft : invHom.comp toHom = LieHom.id :=
    lieHom_ext (by simp [toHom, invHom, twistLieHomOfEq])
      fun i ↦ by simp [toHom, invHom, twistLieHomOfEq, smul_smul]
  have hright : toHom.comp invHom = LieHom.id :=
    lieHom_ext (by simp [toHom, invHom, twistLieHomOfEq])
      fun i ↦ by simp [toHom, invHom, twistLieHomOfEq, smul_smul]
  exact { toLieHom := toHom, invFun := invHom, left_inv := fun x ↦ congr($hleft x),
          right_inv := fun x ↦ congr($hright x) }

@[simp]
theorem twistLieEquiv_cartan (s : ι → ℤˣ) (hs : ∀ i, s (P.reflectionPerm i i) = s i) (y : Y) :
    twistLieEquiv c s hs (cartan (c.twist s hs) y) = cartan c y := by
  simp [twistLieEquiv, twistLieHomOfEq]

@[simp]
theorem twistLieEquiv_root (s : ι → ℤˣ) (hs : ∀ i, s (P.reflectionPerm i i) = s i) (i : ι) :
    twistLieEquiv c s hs (root (c.twist s hs) i) = (s i : ℤ) • root c i := by
  simp [twistLieEquiv, twistLieHomOfEq]

@[simp]
theorem twistLieEquiv_symm_cartan (s : ι → ℤˣ) (hs : ∀ i, s (P.reflectionPerm i i) = s i) (y : Y) :
    (twistLieEquiv c s hs).symm (cartan c y) = cartan (c.twist s hs) y :=
  (twistLieEquiv c s hs).symm_apply_eq.mpr (twistLieEquiv_cartan c s hs y).symm

@[simp]
theorem twistLieEquiv_symm_root (s : ι → ℤˣ) (hs : ∀ i, s (P.reflectionPerm i i) = s i) (i : ι) :
    (twistLieEquiv c s hs).symm (root c i) = (s i : ℤ) • root (c.twist s hs) i := by
  rw [(twistLieEquiv c s hs).symm_apply_eq, map_smul, twistLieEquiv_root, smul_smul, units_val_sq,
    one_smul]

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
  have heIn (i j : ι) : P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j := by
    simpa [hcoroot j, P₂.root_coroot_eq_pairing, P.root_coroot_eq_pairing] using
      hpair i (P.coroot j)
  exact liftLieHom c (cartan c₂ ∘ₗ γ) (fun i ↦ root c₂ (e i))
    (fun _ _ ↦ by simp) (fun _ _ ↦ by simp [hpair])
    (fun {i j} h0 ↦ by
      simp [root_lie_root_of_add_eq_zero c₂ ((root_add_eq_zero_iff_of_pairingIn e heIn i j).mpr h0),
        hcoroot])
    (fun {i j k} hk ↦ by
      rw [root_lie_root_of_root_eq_add c₂ ((root_eq_add_iff_of_pairingIn e heIn k i j).mpr hk),
        hconst i j ⟨k, hk⟩])
    (fun {i j} hnot hne ↦ root_lie_root_of_notMem_of_add_ne_zero c₂
      (mt (root_add_mem_range_iff_of_pairingIn e heIn i j).mp hnot)
      (mt (root_add_eq_zero_iff_of_pairingIn e heIn i j).mp hne))

@[simp]
theorem mapLieHom_cartan (γ : Y →ₗ[ℤ] Y₂) (e : ι ≃ ι₂) (hpair) (hcoroot) (hconst) (y : Y) :
    mapLieHom c c₂ γ e hpair hcoroot hconst (cartan c y) = cartan c₂ (γ y) := by simp [mapLieHom]

@[simp]
theorem mapLieHom_root (γ : Y →ₗ[ℤ] Y₂) (e : ι ≃ ι₂) (hpair) (hcoroot) (hconst) (i : ι) :
    mapLieHom c c₂ γ e hpair hcoroot hconst (root c i) = root c₂ (e i) := by simp [mapLieHom]

/-- **Lie algebra equivalence induced by a cocharacter isomorphism** `γ : Y ≃ₗ[ℤ] Y₂` and a
root-index bijection `e : ι ≃ ι₂`. -/
noncomputable def mapLieEquiv (γ : Y ≃ₗ[ℤ] Y₂) (e : ι ≃ ι₂)
    (hpair : ∀ i y, P₂.toLinearMap (P₂.root (e i)) (γ y) = P.toLinearMap (P.root i) y)
    (hcoroot : ∀ i, γ (P.coroot i) = P₂.coroot (e i))
    (hconst : ∀ i j, P.root i + P.root j ∈ range P.root →
      c₂.structConst (e i) (e j) = c.structConst i j) :
    ChevalleyLieAlgebra c ≃ₗ⁅ℤ⁆ ChevalleyLieAlgebra c₂ := by
  have heIn (i j : ι) : P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j := by
    simpa [hcoroot j, P₂.root_coroot_eq_pairing, P.root_coroot_eq_pairing] using
      hpair i (P.coroot j)
  let f := mapLieHom c c₂ γ.toLinearMap e hpair hcoroot hconst
  let g := mapLieHom c₂ c γ.symm.toLinearMap e.symm
    (fun i₂ y₂ ↦ by simpa using (hpair (e.symm i₂) (γ.symm y₂)).symm)
    (fun i₂ ↦ γ.injective (by simp [hcoroot]))
    (fun i₂ j₂ hmem₂ ↦ by
      obtain ⟨i, rfl⟩ := e.surjective i₂; obtain ⟨j, rfl⟩ := e.surjective j₂
      simpa using (hconst i j ((root_add_mem_range_iff_of_pairingIn e heIn i j).mp hmem₂)).symm)
  have hleft : g.comp f = LieHom.id := lieHom_ext (by simp [f, g]) (by simp [f, g])
  have hright : f.comp g = LieHom.id := lieHom_ext (by simp [f, g]) (by simp [f, g])
  exact { toLieHom := f, invFun := g, left_inv := fun x ↦ congr($hleft x),
          right_inv := fun x ↦ congr($hright x) }

@[simp]
theorem mapLieEquiv_cartan (γ : Y ≃ₗ[ℤ] Y₂) (e : ι ≃ ι₂) (hpair) (hcoroot) (hconst) (y : Y) :
    mapLieEquiv c c₂ γ e hpair hcoroot hconst (cartan c y) = cartan c₂ (γ y) := by
  simp [mapLieEquiv]

@[simp]
theorem mapLieEquiv_root (γ : Y ≃ₗ[ℤ] Y₂) (e : ι ≃ ι₂) (hpair) (hcoroot) (hconst) (i : ι) :
    mapLieEquiv c c₂ γ e hpair hcoroot hconst (root c i) = root c₂ (e i) := by simp [mapLieEquiv]

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
