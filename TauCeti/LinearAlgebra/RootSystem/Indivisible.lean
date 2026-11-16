/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.Chamber
import Mathlib.LinearAlgebra.RootSystem.BaseChange
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import TauCeti.LinearAlgebra.RootSystem.Flip

/-!
# Indivisible roots of a root pairing

Defines `RootPairing.IsIndivisible`, `P.indivisiblePairing`, `P.indivisibleWeylGroupEquiv`,
`P.indivisibleBaseOf`, and `RootPairing.exists_weylGroup_root'_pos_iff` (Bourbaki, VI, §1, no. 3–4).
-/

public section

open Function Set Submodule

namespace RootPairing

section CommRing
variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section Anisotropic
variable (P : RootPairing ι R M N) [Fintype ι] [IsDomain R] [P.IsAnisotropic]
theorem weylGroupToPerm_injective_of_isAnisotropic : Function.Injective P.weylGroupToPerm :=
  fun _ _ h ↦ inv_mul_eq_one.mp <| weylGroup.eq_one_of_forall_smul_root_eq fun i ↦ by
    rw [P.weylGroup_apply_root, map_mul, map_inv, _root_.Equiv.Perm.mul_apply,
      _root_.Equiv.Perm.inv_def, h, _root_.Equiv.symm_apply_apply]
theorem finite_weylGroup_of_isAnisotropic : Finite P.weylGroup :=
  Finite.of_injective P.weylGroupToPerm P.weylGroupToPerm_injective_of_isAnisotropic
end Anisotropic

section Proportional
variable {P : RootPairing ι R M N} [Finite ι] [CharZero R] [IsDomain R]
private theorem coroot_eq_smul_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.coroot i = t • P.coroot j :=
  have := Module.IsReflexive.of_isPerfPair P.toLinearMap
  have := Module.IsReflexive.of_isPerfPair P.flip.toLinearMap
  have : HasUniqueDiv M := .of_isTorsionFree R M; have : HasUniqueDiv N := .of_isTorsionFree R N
  P.coroot_eq_smul_coroot_iff.mpr h
theorem reflection_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.reflection j = P.reflection i := by
  ext x; simp only [reflection_apply, sub_right_inj, h, smul_smul]
  congr 1; rw [mul_comm]; simp [coroot', P.coroot_eq_smul_of_root_eq_smul h]
theorem coreflection_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.coreflection j = P.coreflection i :=
  (P.flip.reflection_eq_of_root_eq_smul (P.coroot_eq_smul_of_root_eq_smul h)).symm
theorem reflectionPerm_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.reflectionPerm j = P.reflectionPerm i := by
  ext k; refine P.root.injective ?_
  rw [P.root_reflectionPerm, P.root_reflectionPerm, P.reflection_eq_of_root_eq_smul h]
theorem weylGroup.ofIdx_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    weylGroup.ofIdx P j = weylGroup.ofIdx P i :=
  weylGroup.ext fun x ↦ by
    rw [weylGroup.ofIdx_smul, weylGroup.ofIdx_smul, Equiv.reflection_smul, Equiv.reflection_smul,
      P.reflection_eq_of_root_eq_smul h]
end Proportional

section Indivisible
variable (P : RootPairing ι R M N)
/-- A root of `P` is *indivisible* if it is not twice another root of `P`. -/
def IsIndivisible (i : ι) : Prop := ∀ j : ι, P.root i ≠ (2 : R) • P.root j
theorem isIndivisible_iff {i : ι} : P.IsIndivisible i ↔ ∀ j : ι, P.root i ≠ (2 : R) • P.root j :=
  Iff.rfl
variable {P} in
theorem IsIndivisible.reflectionPerm {k : ι} (hk : P.IsIndivisible k) (i : ι) :
    P.IsIndivisible (P.reflectionPerm i k) := fun j hj ↦
  hk (P.reflectionPerm i j) <| by
    have h1 := congrArg (P.reflection i) hj
    rwa [← P.root_reflectionPerm, P.reflectionPerm_self, map_smul, ← P.root_reflectionPerm] at h1
variable {P} in
theorem IsIndivisible.neg {k : ι} (hk : P.IsIndivisible k) :
    P.IsIndivisible (P.reflectionPerm k k) := hk.reflectionPerm k
/-- The root pairing obtained by restricting `P` to its indivisible roots. -/
def indivisiblePairing : RootPairing {i : ι // P.IsIndivisible i} R M N where
  toLinearMap := P.toLinearMap
  isPerfPair_toLinearMap := P.isPerfPair_toLinearMap
  root := ⟨fun i ↦ P.root i.1, fun _ _ h ↦ Subtype.ext (P.root.injective h)⟩
  coroot := ⟨fun i ↦ P.coroot i.1, fun _ _ h ↦ Subtype.ext (P.coroot.injective h)⟩
  root_coroot_two i := P.root_coroot_two i.1
  reflectionPerm i := ⟨fun j ↦ ⟨P.reflectionPerm i.1 j.1, j.2.reflectionPerm i.1⟩,
    fun j ↦ ⟨P.reflectionPerm i.1 j.1, j.2.reflectionPerm i.1⟩,
    fun j ↦ Subtype.ext (P.reflectionPerm_self i.1 j.1),
    fun j ↦ Subtype.ext (P.reflectionPerm_self i.1 j.1)⟩
  reflectionPerm_root i j := P.reflectionPerm_root i.1 j.1
  reflectionPerm_coroot i j := P.reflectionPerm_coroot i.1 j.1
@[simp] theorem indivisiblePairing_toLinearMap : P.indivisiblePairing.toLinearMap = P.toLinearMap :=
  (rfl)
@[simp] theorem indivisiblePairing_root (a) : P.indivisiblePairing.root a = P.root a.1 := (rfl)
@[simp] theorem indivisiblePairing_coroot (a) :
    P.indivisiblePairing.coroot a = P.coroot a.1 := (rfl)
@[simp] theorem indivisiblePairing_root' (a) : P.indivisiblePairing.root' a = P.root' a.1 := (rfl)
@[simp] theorem indivisiblePairing_coroot' (a) :
    P.indivisiblePairing.coroot' a = P.coroot' a.1 := (rfl)
@[simp] theorem indivisiblePairing_pairing (a b) :
    P.indivisiblePairing.pairing a b = P.pairing a.1 b.1 := (rfl)
@[simp] theorem indivisiblePairing_reflection (a) :
    P.indivisiblePairing.reflection a = P.reflection a.1 := (rfl)
@[simp] theorem indivisiblePairing_coreflection (a) :
    P.indivisiblePairing.coreflection a = P.coreflection a.1 := (rfl)
@[simp] theorem coe_indivisiblePairing_reflectionPerm (a b) :
    (P.indivisiblePairing.reflectionPerm a b : ι) = P.reflectionPerm a.1 b.1 := (rfl)
instance {S : Type*} [CommRing S] [Algebra S R] [P.IsValuedIn S] :
    P.indivisiblePairing.IsValuedIn S := ⟨fun a b ↦ P.exists_value a.1 b.1⟩
private theorem exists_weylGroup_smul_eq (w : P.indivisiblePairing.weylGroup) :
    ∃ w' : P.weylGroup, ∀ x : M, w' • x = w • x := by
  obtain ⟨g, hg⟩ := w; induction hg using weylGroup.induction with
  | mem a => exact ⟨weylGroup.ofIdx P a.1, fun _ ↦ rfl⟩
  | one => exact ⟨1, fun _ ↦ rfl⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    obtain ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ := ih₁, ih₂
    exact ⟨w₁ * w₂, fun x ↦ by rw [mul_smul, hw₁, hw₂]; rfl⟩

section Crystallographic
variable [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]
omit [Finite ι] [IsDomain R] [P.IsCrystallographic] in
private theorem not_linearIndependent_of_root_eq_smul {i j : ι} {c : R}
    (h : P.root i = c • P.root j) : ¬ LinearIndependent R ![P.root i, P.root j] := fun hli ↦
  one_ne_zero ((LinearIndependent.pair_iff.mp hli 1 (-c) (by simp [h])).1)
theorem not_linearIndependent_root_iff {i j : ι} :
    ¬ LinearIndependent R ![P.root i, P.root j] ↔
      i = j ∨ P.root i = -P.root j ∨ P.root j = (2 : R) • P.root i ∨
        P.root i = (2 : R) • P.root j ∨ P.root j = (-2 : R) • P.root i ∨
        P.root i = (-2 : R) • P.root j := by
  have := Module.IsReflexive.of_isPerfPair P.toLinearMap
  have := Module.IsReflexive.of_isPerfPair P.flip.toLinearMap
  refine ⟨fun hdep ↦ ?_, fun h ↦ ?_⟩
  · set a := P.pairingIn ℤ i j; set b := P.pairingIn ℤ j i
    have h4 : a * b = 4 := (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hdep
    have hb2 : 1 ≤ b ^ 2 := (eq_or_ne b 0).elim (fun hb ↦ by simp [hb] at h4) sq_pos_of_ne_zero
    have hprod : a ^ 2 * b ^ 2 = 16 := by linear_combination (a * b + 4) * h4
    have : -4 ≤ a := by nlinarith
    have : a ≤ 4 := by nlinarith
    have hc : (a = 2 ∧ b = 2) ∨ (a = -2 ∧ b = -2) ∨ (a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1) ∨
        (a = -1 ∧ b = -4) ∨ (a = -4 ∧ b = -1) := by interval_cases a <;> omega
    rcases hc with h | h | h | h | h | h
    exacts [.inl ((P.pairingIn_two_two_iff ℤ i j).mp h),
      .inr (.inl ((P.pairingIn_neg_two_neg_two_iff ℤ i j).mp h)),
      .inr (.inr (.inl ((P.pairingIn_one_four_iff ℤ i j).mp h))),
      .inr (.inr (.inr (.inl ((P.pairingIn_one_four_iff ℤ j i).mp h.symm)))),
      .inr (.inr (.inr (.inr (.inl ((P.pairingIn_neg_one_neg_four_iff ℤ i j).mp h))))),
      .inr (.inr (.inr (.inr (.inr ((P.pairingIn_neg_one_neg_four_iff ℤ j i).mp h.symm)))))]
  · rcases h with rfl | h | h | h | h | h
    exacts [P.not_linearIndependent_of_root_eq_smul (one_smul R _).symm,
      P.not_linearIndependent_of_root_eq_smul (h.trans (neg_one_smul R _).symm),
      mt LinearIndependent.pair_symm_iff.mp (P.not_linearIndependent_of_root_eq_smul h),
      P.not_linearIndependent_of_root_eq_smul h,
      mt LinearIndependent.pair_symm_iff.mp (P.not_linearIndependent_of_root_eq_smul h),
      P.not_linearIndependent_of_root_eq_smul h]
/-- The sub-pairing of indivisible roots of a finite crystallographic root pairing is reduced. -/
instance instIsReducedIndivisiblePairing : P.indivisiblePairing.IsReduced where
  eq_or_eq_neg a b hdep := by
    rcases P.not_linearIndependent_root_iff.mp hdep with h | h | h | h | h | h
    exacts [.inl (congrArg P.indivisiblePairing.root (Subtype.ext h)), .inr h, (b.2 a.1 h).elim,
      (a.2 b.1 h).elim, (b.2 (P.reflectionPerm a.1 a.1) (by simpa [neg_smul] using h)).elim,
      (a.2 (P.reflectionPerm b.1 b.1) (by simpa [neg_smul] using h)).elim]
theorem isIndivisible_or_exists_root_eq_two_smul (i : ι) :
    P.IsIndivisible i ∨ ∃ j : ι, P.IsIndivisible j ∧ P.root i = (2 : R) • P.root j := by
  have := Module.IsReflexive.of_isPerfPair P.toLinearMap
  by_cases hi : P.IsIndivisible i
  · exact .inl hi
  · obtain ⟨j, hj⟩ := not_forall.mp hi; rw [not_not] at hj
    refine .inr ⟨j, fun k hk ↦ ?_, hj⟩
    have hik : P.root i = (4 : R) • P.root k := by rw [hj, hk, smul_smul]; norm_num
    have hne (c d : R) (hcd : c ≠ d) (heq : c • P.root k = d • P.root k) : False :=
      hcd (smul_left_injective R (P.ne_zero k) heq)
    rcases P.not_linearIndependent_root_iff.mp (P.not_linearIndependent_of_root_eq_smul hik) with
      rfl | h | h | h | h | h
    exacts [hne 1 4 (by norm_num) (by simpa using hik),
      hne 4 (-1) (by norm_num) (by rw [← hik, h, neg_one_smul]),
      hne 1 8 (by norm_num) (by (conv_lhs => rw [one_smul, h, hik, smul_smul]); norm_num),
      hne 4 2 (by norm_num) (hik.symm.trans h),
      hne 1 (-8) (by norm_num) (by (conv_lhs => rw [one_smul, h, hik, smul_smul]); norm_num),
      hne 4 (-2) (by norm_num) (hik.symm.trans h)]
private theorem exists_indivisible_weylGroup_smul_eq (w : P.weylGroup) :
    ∃ w₀ : P.indivisiblePairing.weylGroup, ∀ x : M, w₀ • x = w • x := by
  obtain ⟨g, hg⟩ := w; induction hg using weylGroup.induction with
  | mem i =>
    rcases P.isIndivisible_or_exists_root_eq_two_smul i with hi | ⟨j, hj, hij⟩
    · exact ⟨weylGroup.ofIdx P.indivisiblePairing ⟨i, hi⟩, fun _ ↦ rfl⟩
    · exact ⟨weylGroup.ofIdx P.indivisiblePairing ⟨j, hj⟩, fun x ↦ by
        simp [weylGroup.ofIdx_smul, Equiv.reflection_smul, P.reflection_eq_of_root_eq_smul hij]⟩
  | one => exact ⟨1, fun _ ↦ rfl⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    obtain ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ := ih₁, ih₂
    exact ⟨w₁ * w₂, fun x ↦ by rw [mul_smul, hw₁, hw₂]; rfl⟩
/-- Canonical isomorphism between `P.indivisiblePairing.weylGroup` and `P.weylGroup`. -/
noncomputable def indivisibleWeylGroupEquiv : P.indivisiblePairing.weylGroup ≃* P.weylGroup where
  toFun w := (P.exists_weylGroup_smul_eq w).choose
  invFun w := (P.exists_indivisible_weylGroup_smul_eq w).choose
  left_inv w := weylGroup.ext fun x ↦
    ((P.exists_indivisible_weylGroup_smul_eq _).choose_spec x).trans
      ((P.exists_weylGroup_smul_eq w).choose_spec x)
  right_inv w := weylGroup.ext fun x ↦
    ((P.exists_weylGroup_smul_eq _).choose_spec x).trans
      ((P.exists_indivisible_weylGroup_smul_eq w).choose_spec x)
  map_mul' u v := weylGroup.ext fun x ↦ by
    rw [(P.exists_weylGroup_smul_eq (u * v)).choose_spec x, mul_smul, mul_smul,
      (P.exists_weylGroup_smul_eq v).choose_spec x,
      (P.exists_weylGroup_smul_eq u).choose_spec (v • x)]
@[simp] theorem indivisibleWeylGroupEquiv_smul (w : P.indivisiblePairing.weylGroup) (x : M) :
    P.indivisibleWeylGroupEquiv w • x = w • x := (P.exists_weylGroup_smul_eq w).choose_spec x
@[simp] theorem indivisibleWeylGroupEquiv_symm_smul (w : P.weylGroup) (x : M) :
    (P.indivisibleWeylGroupEquiv.symm w) • x = w • x := by
  simpa using (P.indivisibleWeylGroupEquiv_smul (P.indivisibleWeylGroupEquiv.symm w) x).symm
@[simp] theorem indivisibleWeylGroupEquiv_ofIdx (a : {i : ι // P.IsIndivisible i}) :
    P.indivisibleWeylGroupEquiv (weylGroup.ofIdx P.indivisiblePairing a) =
      weylGroup.ofIdx P a.1 := weylGroup.ext fun x ↦ P.indivisibleWeylGroupEquiv_smul _ x
theorem coe_weylGroupToPerm_indivisibleWeylGroupEquiv
    (w : P.indivisiblePairing.weylGroup) (a : {i : ι // P.IsIndivisible i}) :
    (P.indivisiblePairing.weylGroupToPerm w a : ι) =
      P.weylGroupToPerm (P.indivisibleWeylGroupEquiv w) a.1 :=
  P.root.injective <| by
    rw [← P.indivisiblePairing_root, ← P.indivisiblePairing.weylGroup_apply_root,
      ← P.weylGroup_apply_root, P.indivisibleWeylGroupEquiv_smul, P.indivisiblePairing_root]
@[simp] theorem coweightEquiv_indivisibleWeylGroupEquiv (w : P.indivisiblePairing.weylGroup) :
    (P.indivisibleWeylGroupEquiv w : P.Aut).coweightEquiv =
      (w : P.indivisiblePairing.Aut).coweightEquiv := by
  ext y; refine P.isPerfPair_toLinearMap.bijective_right.1 <| LinearMap.ext fun x ↦ ?_
  rw [LinearMap.flip_apply, LinearMap.flip_apply,
    ← (P.indivisibleWeylGroupEquiv w : P.Aut).toLinearMap_weightEquiv x y,
    ← P.indivisiblePairing_toLinearMap,
    ← (w : P.indivisiblePairing.Aut).toLinearMap_weightEquiv x y]
  exact congrArg (P.indivisiblePairing.toLinearMap · y) (P.indivisibleWeylGroupEquiv_smul w x)
end Crystallographic
end Indivisible
end CommRing

section OrderedField
variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic]
private theorem indivisibleBaseOf_coroot_mem_or_neg_mem {s : Set {i : ι // P.IsIndivisible i}}
    (hli : LinearIndepOn R P.indivisiblePairing.root s)
    (hsp : ∀ a, P.indivisiblePairing.root a ∈ AddSubmonoid.closure (P.indivisiblePairing.root '' s)
      ∨ -P.indivisiblePairing.root a ∈ AddSubmonoid.closure (P.indivisiblePairing.root '' s))
    (a : {i : ι // P.IsIndivisible i}) :
    P.indivisiblePairing.coroot a ∈ AddSubmonoid.closure (P.indivisiblePairing.coroot '' s) ∨
      -P.indivisiblePairing.coroot a ∈ AddSubmonoid.closure (P.indivisiblePairing.coroot '' s) := by
  let P₀ := P.indivisiblePairing; let _ := P₀.indexNeg
  have : Fintype {i : ι // P.IsIndivisible i} := Fintype.ofFinite _
  let Q := P₀.restrictScalars' R
  have : Q.IsCrystallographic := ⟨fun a b ↦ (P₀.exists_value (S := ℤ) a b).imp fun _ hz ↦
    hz.trans (by simpa using (P₀.restrictScalars_pairing (K := R) a b).symm)⟩
  have : Q.IsReduced := ⟨fun a b hdep ↦ (IsReduced.eq_or_eq_neg (P := P₀) a b fun hli' ↦ hdep <| by
    rw [← LinearMap.linearIndependent_iff (span R (range P₀.root)).subtype
      (LinearMap.ker_eq_bot.mpr (injective_subtype _))]
    convert hli' using 1; ext k; fin_cases k <;> rfl).imp Subtype.ext Subtype.ext⟩
  have himg : P₀.root '' s = (span R (range P₀.root)).subtype '' (Q.root '' s) := by
    rw [← Set.image_comp]; rfl
  have hspQ (c) : Q.root c ∈ AddSubmonoid.closure (Q.root '' s) ∨
      -Q.root c ∈ AddSubmonoid.closure (Q.root '' s) := by
    have hmap (u : span R (range P₀.root)) (hu : (u : M) ∈ AddSubmonoid.closure (P₀.root '' s)) :
        u ∈ AddSubmonoid.closure (Q.root '' s) := by
      rw [himg, ← AddMonoidHom.map_mclosure] at hu; obtain ⟨w, hw, hwu⟩ := hu
      exact Subtype.ext hwu ▸ hw
    exact (hsp c).imp (hmap (Q.root c)) (hmap (-Q.root c))
  have hcimg : P₀.coroot '' s = (span R (range P₀.coroot)).subtype '' (Q.coroot '' s) := by
    rw [← Set.image_comp]; rfl
  rw [hcimg, ← AddMonoidHom.map_mclosure]
  exact (Q.coroot_mem_or_neg_mem_closure_of_root s
    (LinearIndepOn.of_comp (span R (range P₀.root)).subtype hli) hspQ a).imp
    (fun hc ↦ ⟨Q.coroot a, hc, rfl⟩) (fun hc ↦ ⟨-Q.coroot a, hc, rfl⟩)
/-- Base of `P.indivisiblePairing` cut out by a regular coweight `v`. -/
noncomputable def indivisibleBaseOf (v : N) (hv : ∀ i : ι, P.root' i v ≠ 0) :
    P.indivisiblePairing.Base := by
  let P₀ := P.indivisiblePairing; let _ := P₀.indexNeg
  have : Fintype {i : ι // P.IsIndivisible i} := Fintype.ofFinite _
  let f : Module.Dual R M := P₀.flip.toPerfPair v
  let s := IsAddIndecomposable.baseOf P₀.root (f : M →+ R)
  have hli : LinearIndepOn R P₀.root s := P₀.linearIndepOn_root_baseOf' f fun a ↦ hv a.1
  have hsp (a) :=
    IsAddIndecomposable.mem_or_neg_mem_closure_baseOf P₀.root (f : M →+ R) a (hv a.1) (by simp)
  exact ⟨(toFinite s).toFinset, by rwa [Finite.coe_toFinset],
    by rwa [Finite.coe_toFinset, P₀.linearIndepOn_coroot_iff],
    fun a ↦ by rw [Finite.coe_toFinset]; exact hsp a,
    fun a ↦ by rw [Finite.coe_toFinset]; exact P.indivisibleBaseOf_coroot_mem_or_neg_mem hli hsp a⟩
theorem root'_pos_of_mem_indivisibleBaseOf {v : N} {hv : ∀ i : ι, P.root' i v ≠ 0}
    {a : {i : ι // P.IsIndivisible i}} (ha : a ∈ (P.indivisibleBaseOf v hv).support) :
    0 < P.root' a.1 v := by
  simp only [indivisibleBaseOf, Finite.mem_toFinset] at ha; exact ha.1
@[simp] theorem indivisibleBaseOf_isPos_iff {v : N} (hv : ∀ i : ι, P.root' i v ≠ 0)
    (a : {i : ι // P.IsIndivisible i}) :
    (P.indivisibleBaseOf v hv).IsPos a ↔ 0 < P.root' a.1 v :=
  have hsupp : ∀ c ∈ (P.indivisibleBaseOf v hv).support, 0 < P.indivisiblePairing.root' c v :=
    fun _ hc ↦ P.root'_pos_of_mem_indivisibleBaseOf hc
  ⟨root'_pos_of_isPos hsupp, fun ha ↦
    by_contra fun hna ↦ ha.not_gt (root'_neg_of_not_isPos hsupp hna)⟩
omit [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
private theorem autFlip_symm_mem_weylGroup {g : P.indivisiblePairing.flip.Aut}
    (hg : g ∈ P.indivisiblePairing.flip.weylGroup) :
    (Equiv.autFlip P.indivisiblePairing).symm g ∈ P.indivisiblePairing.weylGroup := by
  induction hg using weylGroup.induction with
  | mem a =>
    rw [(Equiv.autFlip P.indivisiblePairing).symm_apply_eq.mpr (Equiv.autFlip_reflection a).symm]
    exact (weylGroup.ofIdx P.indivisiblePairing a).2
  | one => simp
  | mul _ _ _ _ ih₁ ih₂ => rw [map_mul]; exact mul_mem ih₁ ih₂
theorem exists_weylGroup_root'_pos_iff {x v : N}
    (hx : ∀ i : ι, P.root' i x ≠ 0) (hv : ∀ i : ι, P.root' i v ≠ 0) :
    ∃ w : P.weylGroup, ∀ i : ι, 0 < P.root' i x ↔ 0 < P.root' (P.weylGroupToPerm w i) v := by
  let P₀ := P.indivisiblePairing; let b := P.indivisibleBaseOf v hv
  have : Fintype {i : ι // P.IsIndivisible i} := Fintype.ofFinite _
  have : Finite P₀.flip.weylGroup := P₀.flip.finite_weylGroup_of_isAnisotropic
  obtain ⟨u, hu⟩ := exists_mem_dominantChamber_of_finite_weylGroup P₀.flip b.flip x
  have hu_open : u • x ∈ openDominantChamber P₀.flip b.flip :=
    mem_openDominantChamber_of_isRegularWeight P₀.flip b.flip hu
      ((isRegularWeight_smul P₀.flip u x).mpr ((isRegularWeight_iff P₀.flip x).mpr fun a ↦ hx a.1))
  let w₀ : P₀.weylGroup := ⟨(Equiv.autFlip P₀).symm u.1, P.autFlip_symm_mem_weylGroup u.2⟩
  let w : P.weylGroup := P.indivisibleWeylGroupEquiv w₀
  have hkey (a : {i : ι // P.IsIndivisible i}) :
      0 < P.root' a.1 x ↔ 0 < P.root' (P.weylGroupToPerm w a.1) v := by
    have hperm : P₀.weylGroupToPerm w₀ a = P₀.flip.weylGroupToPerm u a := by
      rw [weylGroupToPerm_apply, weylGroupToPerm_apply]
      exact (congrFun (congrArg DFunLike.coe (Equiv.indexEquiv_autFlip _)) a).symm.trans
        (by rw [MulEquiv.apply_symm_apply])
    have hux : P₀.root' (P₀.flip.weylGroupToPerm u a) (u • x) = P.root' a.1 x :=
      P₀.flip.coroot'_weylGroupToPerm_smul u a x
    have hdom : ∀ c ∈ b.support, 0 < P₀.root' c (u • x) := fun c hc ↦
      (mem_openDominantChamber P₀.flip b.flip (u • x)).mp hu_open c (by rwa [Base.flip_support])
    rw [← hux, ← hperm, ← P.coe_weylGroupToPerm_indivisibleWeylGroupEquiv w₀ a,
      ← P.indivisibleBaseOf_isPos_iff hv (P₀.weylGroupToPerm w₀ a)]
    exact ⟨fun hp ↦ by_contra fun hn ↦ hp.not_gt (root'_neg_of_not_isPos hdom hn),
      root'_pos_of_isPos hdom⟩
  refine ⟨w, fun i ↦ ?_⟩
  rcases P.isIndivisible_or_exists_root_eq_two_smul i with hi | ⟨j, hj, hij⟩
  · exact hkey ⟨i, hi⟩
  · have h1 : P.root' i x = 2 * P.root' j x := by simp [root', hij]
    have h2 : P.root' (P.weylGroupToPerm w i) v = 2 * P.root' (P.weylGroupToPerm w j) v := by
      simp [root', hij, smul_comm (w : P.Aut) (2 : R)]
    rw [h1, h2, mul_pos_iff_of_pos_left two_pos, mul_pos_iff_of_pos_left two_pos]
    exact hkey ⟨j, hj⟩
end OrderedField
end RootPairing
