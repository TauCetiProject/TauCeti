/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Invariance of crystallographic root relations under matching Cartan pairings

In a finite crystallographic root pairing in characteristic zero, polarization on `P.rootSpan ℤ` is
injective (`RootPairing.exists_coroot_ne`), so integer root relations are detected by coroot
pairings (`sum_zsmul_root_eq_zero_iff`) regardless of central toral directions. Any `e : ι ≃ ι₂`
matching `pairingIn ℤ` therefore preserves and reflects integer root relations, intertwines
`reflectionPerm`, and preserves linear independence, reducedness, `chainTopCoeff`, and
`chainBotCoeff`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace RootPairing

open Function Set

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Over the ambient coefficient ring `R` itself, `P.pairingIn R` agrees with `P.pairing`. -/
@[simp] theorem pairingIn_eq_pairing (P : RootPairing ι R M N) (i j : ι) :
    P.pairingIn R i j = P.pairing i j := by simpa using P.algebraMap_pairingIn R i j

/-- Rewrites `P₂.pairingIn R (e i) (e j) = P.pairing i j` into agreement of `pairingIn R`. -/
theorem pairingIn_eq_of_pairingIn_eq_pairing {ι₂ S M₂ N₂ : Type*} [CommRing S] [Algebra R S]
    [AddCommGroup M₂] [Module S M₂] [AddCommGroup N₂] [Module S N₂]
    {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ S M₂ N₂} [P₂.IsValuedIn R]
    {e : ι → ι₂} (he : ∀ i j, P₂.pairingIn R (e i) (e j) = P.pairing i j) (i j : ι) :
    P₂.pairingIn R (e i) (e j) = P.pairingIn R i j := by rw [he, pairingIn_eq_pairing]

/-- Rewrites `P₂.pairing (e i) (e j) = P.pairing i j` into agreement of `pairingIn R`. -/
theorem pairingIn_eq_of_pairing_eq {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₂] [Module R N₂] {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ R M₂ N₂}
    {e : ι → ι₂} (he : ∀ i j, P₂.pairing (e i) (e j) = P.pairing i j) (i j : ι) :
    P₂.pairingIn R (e i) (e j) = P.pairingIn R i j :=
  pairingIn_eq_of_pairingIn_eq_pairing (fun a b ↦ (P₂.pairingIn_eq_pairing _ _).trans (he a b)) i j

/-- Compatibility of root functionals and coroots along `γ` implies agreement of `pairingIn R`. -/
theorem pairingIn_eq_of_toLinearMap_of_map_coroot {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂]
    [Module R M₂] [AddCommGroup N₂] [Module R N₂] {P : RootPairing ι R M N}
    {P₂ : RootPairing ι₂ R M₂ N₂} {γ : N →ₗ[R] N₂} {e : ι → ι₂}
    (hpair : ∀ i y, P₂.toLinearMap (P₂.root (e i)) (γ y) = P.toLinearMap (P.root i) y)
    (hcoroot : ∀ i, γ (P.coroot i) = P₂.coroot (e i)) (i j : ι) :
    P₂.pairingIn R (e i) (e j) = P.pairingIn R i j :=
  pairingIn_eq_of_pairing_eq (fun a b ↦ by
    simpa [hcoroot b, root_coroot_eq_pairing] using hpair a (P.coroot b)) i j

/-- Evaluates `f k hk` at the unique `k` with `P.root k = P.root i + P.root j`, or `0` otherwise. -/
noncomputable def rootSumElim {α : Type*} [Zero α] (P : RootPairing ι R M N) (i j : ι)
    (f : (k : ι) → P.root k = P.root i + P.root j → α) : α := open Classical in
  if h : P.root i + P.root j ∈ range P.root then f h.choose h.choose_spec else 0

/-- On `P.root k = P.root i + P.root j`, `P.rootSumElim i j f` evaluates to `f k hk`. -/
theorem rootSumElim_of_root_eq_add {α : Type*} [Zero α] (P : RootPairing ι R M N) {i j k : ι}
    (hk : P.root k = P.root i + P.root j) (f : (m : ι) → P.root m = P.root i + P.root j → α) :
    P.rootSumElim i j f = f k hk := by
  classical
  have hmem : P.root i + P.root j ∈ range P.root := ⟨k, hk⟩
  cases P.root.injective (hmem.choose_spec.trans hk.symm); exact dite_eq_left hmem

/-- When `P.root i + P.root j ∉ range P.root`, `P.rootSumElim i j f` vanishes. -/
@[simp] theorem rootSumElim_of_notMem_range {α : Type*} [Zero α] (P : RootPairing ι R M N) {i j : ι}
    (hnot : P.root i + P.root j ∉ range P.root)
    (f : (m : ι) → P.root m = P.root i + P.root j → α) : P.rootSumElim i j f = 0 := by
  classical exact dite_eq_right hnot

/-- When `P.root i + P.root j = 0`, `P.rootSumElim i j f` vanishes. -/
theorem rootSumElim_of_add_eq_zero {α : Type*} [Zero α] [NeZero (2 : R)] (P : RootPairing ι R M N)
    {i j : ι} (h0 : P.root i + P.root j = 0) (f : (m : ι) → P.root m = P.root i + P.root j → α) :
    P.rootSumElim i j f = 0 :=
  P.rootSumElim_of_notMem_range (fun ⟨m, hm⟩ ↦ P.ne_zero m (hm.trans h0)) f

/-- When three roots sum to zero, the opposite of the first equals the sum of the other two. -/
theorem root_reflectionPerm_self_eq_add_of_add_add_eq_zero {P : RootPairing ι R M N} {i j k : ι}
    (h : P.root i + P.root j + P.root k = 0) :
    P.root (P.reflectionPerm i i) = P.root j + P.root k := by
  rw [P.root_reflectionPerm, P.reflection_apply_self, neg_eq_iff_add_eq_zero, ← add_assoc, h]

/-- Negating all three indices via `reflectionPerm` preserves a root sum `αₖ = αᵢ + αⱼ`. -/
theorem root_reflectionPerm_self_eq_add_of_root_eq_add {P : RootPairing ι R M N} {i j k : ι}
    (h : P.root k = P.root i + P.root j) : P.root (P.reflectionPerm k k) =
      P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) := by
  simp only [root_reflectionPerm, reflection_apply_self]; rw [h, neg_add]

/-- Negating two roots via `reflectionPerm` preserves membership of their sum in `range P.root`. -/
theorem root_reflectionPerm_add_mem_range_iff (P : RootPairing ι R M N) (i j : ι) :
    P.root (P.reflectionPerm i i) + P.root (P.reflectionPerm j j) ∈ range P.root ↔
      P.root i + P.root j ∈ range P.root := by
  simpa only [root_reflectionPerm, reflection_apply_self, ← neg_add] using
    (P.neg_mem_range_root_iff (x := P.root i + P.root j))

section SinglePairing

variable [CharZero R] [IsDomain R] (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic]

/-- An element of `P.rootSpan ℤ` annihilated by every coroot functional vanishes. -/
theorem eq_zero_of_mem_rootSpan_of_forall_coroot'_eq_zero {x : M} (hx : x ∈ P.rootSpan ℤ)
    (h : ∀ i, P.coroot' i x = 0) : x = 0 := by
  cases nonempty_fintype ι; by_contra hx0
  obtain ⟨i, hi⟩ := P.exists_coroot_ne ℤ (x := ⟨x, hx⟩) (Subtype.coe_ne_coe.mp hx0)
  exact hi <| FaithfulSMul.algebraMap_injective ℤ R <| by
    rw [algebraMap_coroot'In_apply, h i, map_zero]

/-- An integer linear combination of roots vanishes iff its pairings with all coroots vanish. -/
theorem sum_zsmul_root_eq_zero_iff {κ : Type*} [Fintype κ] (c : κ → ℤ) (idx : κ → ι) :
    ∑ a : κ, c a • P.root (idx a) = 0 ↔ ∀ s : ι, ∑ a : κ, c a * P.pairingIn ℤ (idx a) s = 0 := by
  have hmem : ∑ a : κ, c a • P.root (idx a) ∈ P.rootSpan ℤ :=
    Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self _))
  have hpair (s : ι) : P.coroot' s (∑ a : κ, c a • P.root (idx a)) =
      ((∑ a : κ, c a * P.pairingIn ℤ (idx a) s : ℤ) : R) := by
    rw [map_sum, Int.cast_sum]; refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [LinearMap.map_smul_of_tower, root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ]
    simp [zsmul_eq_mul]
  exact ⟨fun h0 s ↦ Int.cast_eq_zero.mp (by rw [← hpair s, h0, map_zero]), fun hs ↦
    P.eq_zero_of_mem_rootSpan_of_forall_coroot'_eq_zero hmem fun s ↦ by simp [hpair s, hs s]⟩

/-- An integer linear combination of coroots vanishes iff its pairings with all roots vanish. -/
theorem sum_zsmul_coroot_eq_zero_iff {κ : Type*} [Fintype κ] (c : κ → ℤ) (idx : κ → ι) :
    ∑ a : κ, c a • P.coroot (idx a) = 0 ↔ ∀ s : ι, ∑ a : κ, c a * P.pairingIn ℤ s (idx a) = 0 := by
  have hflip (a s : ι) : P.flip.pairingIn ℤ a s = P.pairingIn ℤ s a :=
    FaithfulSMul.algebraMap_injective ℤ R (by rw [algebraMap_pairingIn, algebraMap_pairingIn]; rfl)
  simpa only [flip_root, hflip] using P.flip.sum_zsmul_root_eq_zero_iff c idx

/-- A three-term `ℤ`-combination of coroots vanishes iff its pairings with all roots vanish. -/
theorem zsmul_add_zsmul_add_zsmul_coroot_eq_zero_iff (a b c : ℤ) (i j k : ι) :
    a • P.coroot i + b • P.coroot j + c • P.coroot k = 0 ↔
      ∀ s : ι, a * P.pairingIn ℤ s i + b * P.pairingIn ℤ s j + c * P.pairingIn ℤ s k = 0 := by
  simpa [Fin.sum_univ_three, add_assoc] using P.sum_zsmul_coroot_eq_zero_iff ![a, b, c] ![i, j, k]

end SinglePairing

variable {ι₂ S M₂ N₂ : Type*} [CharZero R] [IsDomain R] [CommRing S] [CharZero S] [IsDomain S]
  [AddCommGroup M₂] [Module S M₂] [AddCommGroup N₂] [Module S N₂]
  {P : RootPairing ι R M N} {P₂ : RootPairing ι₂ S M₂ N₂}
  [Finite ι] [P.IsCrystallographic] [P₂.IsCrystallographic]
  (e : ι ≃ ι₂) (he : ∀ i j, P₂.pairingIn ℤ (e i) (e j) = P.pairingIn ℤ i j)

include he

/-- A bijection matching integer Cartan pairings preserves and reflects integer root relations. -/
theorem sum_zsmul_root_eq_zero_iff_of_pairingIn {κ : Type*} [Fintype κ] (c : κ → ℤ) (idx : κ → ι) :
    ∑ a : κ, c a • P₂.root (e (idx a)) = 0 ↔ ∑ a : κ, c a • P.root (idx a) = 0 := by
  let _ : Finite ι₂ := Finite.of_equiv ι e
  rw [P₂.sum_zsmul_root_eq_zero_iff, P.sum_zsmul_root_eq_zero_iff]
  exact ⟨fun h s ↦ by simpa [he] using h (e s), fun h s₂ ↦ by
    obtain ⟨s, rfl⟩ := e.surjective s₂; simpa [he] using h s⟩

/-- Three-term integer linear relations among roots are preserved and reflected by `e`. -/
theorem zsmul_add_zsmul_add_zsmul_root_eq_zero_iff_of_pairingIn (a b c : ℤ) (i j k : ι) :
    a • P₂.root (e i) + b • P₂.root (e j) + c • P₂.root (e k) = 0 ↔
      a • P.root i + b • P.root j + c • P.root k = 0 := by
  simpa [Fin.sum_univ_three, add_assoc] using
    sum_zsmul_root_eq_zero_iff_of_pairingIn e he ![a, b, c] ![i, j, k]

/-- Opposition of roots `α + β = 0` is preserved and reflected by `e`. -/
theorem root_add_eq_zero_iff_of_pairingIn (i j : ι) :
    P₂.root (e i) + P₂.root (e j) = 0 ↔ P.root i + P.root j = 0 := by
  simpa using zsmul_add_zsmul_add_zsmul_root_eq_zero_iff_of_pairingIn e he 1 1 0 i j i

/-- Root-sum identities `γ = α + β` are preserved and reflected by `e`. -/
theorem root_eq_add_iff_of_pairingIn (k i j : ι) :
    P₂.root (e k) = P₂.root (e i) + P₂.root (e j) ↔ P.root k = P.root i + P.root j := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := P.root k)]
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    zsmul_add_zsmul_add_zsmul_root_eq_zero_iff_of_pairingIn e he (-1) (-1) 1 i j k

/-- Membership of `α + β` in the root set is preserved and reflected by `e`. -/
theorem root_add_mem_range_iff_of_pairingIn (i j : ι) :
    P₂.root (e i) + P₂.root (e j) ∈ range P₂.root ↔ P.root i + P.root j ∈ range P.root :=
  ⟨fun ⟨k₂, hk₂⟩ ↦ let ⟨k, hk⟩ := e.surjective k₂
    ⟨k, (root_eq_add_iff_of_pairingIn e he k i j).mp (hk ▸ hk₂)⟩,
   fun ⟨k, hk⟩ ↦ ⟨e k, (root_eq_add_iff_of_pairingIn e he k i j).mpr hk⟩⟩

/-- Zero-sum root triples `α + β + γ = 0` are preserved and reflected by `e`. -/
theorem root_add_add_eq_zero_iff_of_pairingIn (i j k : ι) :
    P₂.root (e i) + P₂.root (e j) + P₂.root (e k) = 0 ↔ P.root i + P.root j + P.root k = 0 := by
  simpa using zsmul_add_zsmul_add_zsmul_root_eq_zero_iff_of_pairingIn e he 1 1 1 i j k

/-- Root-string step relations `γ = β + z • α` are preserved and reflected by `e`. -/
theorem root_eq_add_zsmul_iff_of_pairingIn (k j i : ι) (z : ℤ) :
    P₂.root (e k) = P₂.root (e j) + z • P₂.root (e i) ↔ P.root k = P.root j + z • P.root i := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := P.root k)]
  simpa [sub_eq_add_neg, neg_smul, add_assoc, add_comm, add_left_comm] using
    zsmul_add_zsmul_add_zsmul_root_eq_zero_iff_of_pairingIn e he 1 (-1) (-z) k j i

/-- A bijection of root indices preserving integer Cartan pairings commutes with reflections. -/
theorem map_reflectionPerm_of_pairingIn (i j : ι) :
    e (P.reflectionPerm i j) = P₂.reflectionPerm (e i) (e j) := by
  apply P₂.root.injective
  have h1 : P.root (P.reflectionPerm i j) = P.root j + (-P.pairingIn ℤ j i) • P.root i := by
    rw [root_reflectionPerm, P.reflection_apply_root' ℤ, neg_smul, sub_eq_add_neg]
  rw [(root_eq_add_zsmul_iff_of_pairingIn e he _ j i (-P.pairingIn ℤ j i)).mpr h1, ← he j i,
    root_reflectionPerm, P₂.reflection_apply_root' ℤ, neg_smul, sub_eq_add_neg]

/-- A pairing-preserving bijection preserves and reflects pairwise linear independence of roots. -/
theorem linearIndependent_root_iff_of_pairingIn (i j : ι) :
    LinearIndependent S ![P₂.root (e i), P₂.root (e j)] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  let _ : Finite ι₂ := Finite.of_equiv ι e
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive S M₂ := .of_isPerfPair P₂.toLinearMap
  simp [P₂.linearIndependent_iff_coxeterWeightIn_ne_four ℤ,
    P.linearIndependent_iff_coxeterWeightIn_ne_four ℤ, coxeterWeightIn, he]

/-- Finite crystallographic root pairings with matching `pairingIn ℤ` are simultaneously reduced. -/
theorem isReduced_iff_of_pairingIn : P₂.IsReduced ↔ P.IsReduced := by
  let _ : Finite ι₂ := Finite.of_equiv ι e
  simp only [isReduced_iff', root_eq_neg_iff]
  refine ⟨fun h i j hij hdep ↦ e.injective ((h (e i) (e j) (e.injective.ne hij)
      (mt (linearIndependent_root_iff_of_pairingIn e he i j).mp hdep)).trans
      (map_reflectionPerm_of_pairingIn e he j j).symm), fun h i₂ j₂ hij hdep ↦ ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective i₂; obtain ⟨j, rfl⟩ := e.surjective j₂
  rw [← map_reflectionPerm_of_pairingIn e he j j]
  exact congrArg e (h i j (by rintro rfl; exact hij rfl)
    (mt (linearIndependent_root_iff_of_pairingIn e he i j).mpr hdep))

/-- A pairing-preserving bijection of root indices preserves ascending root-string lengths. -/
theorem chainTopCoeff_eq_of_pairingIn (i j : ι) : letI : Finite ι₂ := Finite.of_equiv ι e
    P₂.chainTopCoeff (e i) (e j) = P.chainTopCoeff i j := by
  let _ : Finite ι₂ := Finite.of_equiv ι e
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h₂ := (linearIndependent_root_iff_of_pairingIn e he i j).mpr h
    have hmem (n : ℕ) : P₂.root (e j) + n • P₂.root (e i) ∈ range P₂.root ↔
        P.root j + n • P.root i ∈ range P.root := by
      simp only [← natCast_zsmul]
      exact ⟨fun ⟨k₂, hk₂⟩ ↦ let ⟨k, hk⟩ := e.surjective k₂
        ⟨k, (root_eq_add_zsmul_iff_of_pairingIn e he k j i n).mp (hk ▸ hk₂)⟩,
       fun ⟨k, hk⟩ ↦ ⟨e k, (root_eq_add_zsmul_iff_of_pairingIn e he k j i n).mpr hk⟩⟩
    exact le_antisymm ((P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mp
      ((hmem _).mp ((P₂.root_add_nsmul_mem_range_iff_le_chainTopCoeff h₂).mpr le_rfl)))
      ((P₂.root_add_nsmul_mem_range_iff_le_chainTopCoeff h₂).mp
        ((hmem _).mpr ((P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr le_rfl)))
  · rw [chainTopCoeff_of_not_linearIndependent
      (mt (linearIndependent_root_iff_of_pairingIn e he i j).mp h),
      chainTopCoeff_of_not_linearIndependent h]

/-- A pairing-preserving bijection of root indices preserves descending root-string lengths. -/
theorem chainBotCoeff_eq_of_pairingIn (i j : ι) : letI : Finite ι₂ := Finite.of_equiv ι e
    P₂.chainBotCoeff (e i) (e j) = P.chainBotCoeff i j := by
  let _ : Finite ι₂ := Finite.of_equiv ι e
  rw [← P₂.chainTopCoeff_reflectionPerm_left, ← P.chainTopCoeff_reflectionPerm_left,
    ← map_reflectionPerm_of_pairingIn e he, chainTopCoeff_eq_of_pairingIn e he]

end RootPairing
