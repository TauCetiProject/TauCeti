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
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.RootSystem.BaseChange
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import TauCeti.LinearAlgebra.RootSystem.Basic
import TauCeti.LinearAlgebra.RootSystem.CoweightLattice
import TauCeti.LinearAlgebra.RootSystem.Flip
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Indivisible roots of a root pairing

Non-reduced crystallographic root pairings (of type `BC_n`, such as the relative root system of a
non-split reductive group) contain proportional roots `α` and `2 α`, so reduced root-system base
and chamber theory does not apply to `P` directly; moreover, in a root datum the roots and coroots
need not span the ambient weight and coweight modules (`¬ P.IsRootSystem`).

Restricting `P` to its *indivisible* roots (`P.IsIndivisible`, those not of the form `2 β`)
produces a reduced root pairing `P.indivisiblePairing` on `{i : ι // P.IsIndivisible i}` without
assuming `P.IsRootSystem`. By the classification of linearly dependent roots in a finite
crystallographic pairing (`P.not_linearIndependent_root_iff`: equal, opposite, or `±2` multiples),
every root is either indivisible or twice an indivisible root
(`P.isIndivisible_or_exists_root_eq_two_smul`). Because proportional roots define the same
reflection and coreflection (`P.reflection_eq_of_root_eq_smul`,
`P.coreflection_eq_of_root_eq_smul`), `P.indivisiblePairing.weylGroup` is then canonically
isomorphic to `P.weylGroup` (`P.indivisibleWeylGroupEquiv`), acting identically on weights and
coweights.

Over a linearly ordered field, any regular coweight `v` (`∀ i, P.root' i v ≠ 0`) cuts out a base
`P.indivisibleBaseOf v hv` of `P.indivisiblePairing`. Applying Weyl transitivity on dominant
chambers to `P.indivisiblePairing.flip` and lifting back along `P.indivisibleWeylGroupEquiv` then
gives Weyl transitivity on regular sign chambers of `P` itself (`P.exists_weylGroup_root'_pos_iff`).

## Main definitions

* `RootPairing.IsIndivisible`: a root `i` is indivisible if `P.root i ≠ 2 • P.root j` for all `j`.
* `RootPairing.indivisiblePairing`: the sub-pairing of `P` on `{i : ι // P.IsIndivisible i}`.
* `RootPairing.indivisibleWeylGroupEquiv`: the canonical Weyl group isomorphism
  `P.indivisiblePairing.weylGroup ≃* P.weylGroup`.
* `RootPairing.indivisibleBaseOf`: the base of `P.indivisiblePairing` cut out by a regular coweight.

## Main results

* `RootPairing.instIsReducedIndivisiblePairing`: `P.indivisiblePairing` is reduced.
* `RootPairing.isIndivisible_or_exists_root_eq_two_smul`: every root is either indivisible or twice
  an indivisible root.
* `RootPairing.exists_weylGroup_root'_pos_iff`: the Weyl group acts transitively on the sign
  chambers cut out by regular coweights.
* `RootPairing.exists_mem_corootSpan_of_forall_reflectionPerm`: any family obeying the reflection
  law `d (s_i j) = d j - ⟨j, i∨⟩ d i` is realized on every root by a vector in `P.corootSpan R`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter VI, §1, nos. 3–4.
-/

public section

open Function Set Submodule

namespace RootPairing

section CommRing
variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

section Indivisible
variable (P : RootPairing ι R M N)
/-- A root of `P` is *indivisible* if it is not twice another root of `P`. -/
def IsIndivisible (i : ι) : Prop := ∀ j : ι, P.root i ≠ (2 : R) • P.root j

/-- Unfolding characterization of `RootPairing.IsIndivisible`. -/
theorem isIndivisible_iff {i : ι} : P.IsIndivisible i ↔ ∀ j : ι, P.root i ≠ (2 : R) • P.root j :=
  Iff.rfl

variable {P} in
/-- Indivisibility of a root is preserved by every root-index reflection. -/
theorem IsIndivisible.reflectionPerm {k : ι} (hk : P.IsIndivisible k) (i : ι) :
    P.IsIndivisible (P.reflectionPerm i k) := fun j hj ↦
  hk (P.reflectionPerm i j) <| by
    have h1 := congrArg (P.reflection i) hj
    rwa [← P.root_reflectionPerm, P.reflectionPerm_self, map_smul, ← P.root_reflectionPerm] at h1

variable {P} in
/-- The negative `P.reflectionPerm k k` of an indivisible root `k` is indivisible. -/
theorem IsIndivisible.neg {k : ι} (hk : P.IsIndivisible k) :
    P.IsIndivisible (P.reflectionPerm k k) := hk.reflectionPerm k

/-- The root pairing obtained by restricting `P` to its indivisible roots. -/
def indivisiblePairing : RootPairing {i : ι // P.IsIndivisible i} R M N where
  toLinearMap := P.toLinearMap
  isPerfPair_toLinearMap := P.isPerfPair_toLinearMap
  root := ⟨fun i ↦ P.root i.val, fun _ _ h ↦ Subtype.ext (P.root.injective h)⟩
  coroot := ⟨fun i ↦ P.coroot i.val, fun _ _ h ↦ Subtype.ext (P.coroot.injective h)⟩
  root_coroot_two i := P.root_coroot_two i.val
  reflectionPerm i := ⟨fun j ↦ ⟨P.reflectionPerm i.val j.val, j.property.reflectionPerm i.val⟩,
    fun j ↦ ⟨P.reflectionPerm i.val j.val, j.property.reflectionPerm i.val⟩,
    fun j ↦ Subtype.ext (P.reflectionPerm_self i.val j.val),
    fun j ↦ Subtype.ext (P.reflectionPerm_self i.val j.val)⟩
  reflectionPerm_root i j := P.reflectionPerm_root i.val j.val
  reflectionPerm_coroot i j := P.reflectionPerm_coroot i.val j.val

/-- `P.indivisiblePairing` has the same ambient bilinear pairing as `P`. -/
@[simp] theorem indivisiblePairing_toLinearMap : P.indivisiblePairing.toLinearMap = P.toLinearMap :=
  (rfl)
/-- The root of an indivisible index in `P.indivisiblePairing` is its root in `P`. -/
@[simp] theorem indivisiblePairing_root (a) : P.indivisiblePairing.root a = P.root a.val := (rfl)
/-- The coroot of an indivisible index in `P.indivisiblePairing` is its coroot in `P`. -/
@[simp] theorem indivisiblePairing_coroot (a) :
    P.indivisiblePairing.coroot a = P.coroot a.val := (rfl)
/-- The root functional of `a` in `P.indivisiblePairing` agrees with that in `P`. -/
@[simp] theorem indivisiblePairing_root' (a) : P.indivisiblePairing.root' a = P.root' a.val := (rfl)
/-- The coroot functional of `a` in `P.indivisiblePairing` agrees with that in `P`. -/
@[simp] theorem indivisiblePairing_coroot' (a) :
    P.indivisiblePairing.coroot' a = P.coroot' a.val := (rfl)
/-- The pairing of two indivisible indices in `P.indivisiblePairing` agrees with `P.pairing`. -/
@[simp] theorem indivisiblePairing_pairing (a b) :
    P.indivisiblePairing.pairing a b = P.pairing a.val b.val := (rfl)
/-- The reflection in `a` for `P.indivisiblePairing` is `P.reflection a.val`. -/
@[simp] theorem indivisiblePairing_reflection (a) :
    P.indivisiblePairing.reflection a = P.reflection a.val := (rfl)
/-- The coreflection in `a` for `P.indivisiblePairing` is `P.coreflection a.val`. -/
@[simp] theorem indivisiblePairing_coreflection (a) :
    P.indivisiblePairing.coreflection a = P.coreflection a.val := (rfl)
/-- Coercing `P.indivisiblePairing.reflectionPerm a b` to `ι` gives
`P.reflectionPerm a.val b.val`. -/
@[simp] theorem coe_indivisiblePairing_reflectionPerm (a b) :
    (P.indivisiblePairing.reflectionPerm a b : ι) = P.reflectionPerm a.val b.val := (rfl)
/-- `P.indivisiblePairing` inherits `IsValuedIn S` from `P` (in particular crystallography). -/
instance {S : Type*} [CommRing S] [Algebra S R] [P.IsValuedIn S] :
    P.indivisiblePairing.IsValuedIn S := ⟨fun a b ↦ P.exists_value a.val b.val⟩
private theorem exists_weylGroup_smul_eq (w : P.indivisiblePairing.weylGroup) :
    ∃ w' : P.weylGroup, ∀ x : M, w' • x = w • x := by
  obtain ⟨g, hg⟩ := w; induction hg using weylGroup.induction with
  | mem a => exact ⟨weylGroup.ofIdx P a.val, fun _ ↦ rfl⟩
  | one => exact ⟨1, fun _ ↦ rfl⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    obtain ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ := ih₁, ih₂
    exact ⟨w₁ * w₂, fun x ↦ by rw [mul_smul, hw₁, hw₂]; rfl⟩

section Crystallographic
variable [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]

/-- The sub-pairing of indivisible roots of a finite crystallographic root pairing is reduced. -/
instance instIsReducedIndivisiblePairing : P.indivisiblePairing.IsReduced where
  eq_or_eq_neg a b hdep := by
    rcases P.not_linearIndependent_root_iff.mp hdep with h | h | h | h | h | h
    exacts [.inl (congrArg P.indivisiblePairing.root (Subtype.ext h)), .inr h,
      (b.property a.val h).elim, (a.property b.val h).elim,
      (b.property (P.reflectionPerm a.val a.val) (by simpa [neg_smul] using h)).elim,
      (a.property (P.reflectionPerm b.val b.val) (by simpa [neg_smul] using h)).elim]

/-- Every root of a finite crystallographic root pairing over a domain of characteristic zero is
either indivisible or twice an indivisible root (Bourbaki, Ch. VI, §1, no. 3). -/
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
    have hdep : ¬ LinearIndependent R ![P.root i, P.root k] := fun hli ↦
      one_ne_zero (LinearIndependent.pair_iff.mp hli 1 (-4) (by simp [hik])).1
    rcases P.not_linearIndependent_root_iff.mp hdep with rfl | h | h | h | h | h
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
/-- Canonical isomorphism between `P.indivisiblePairing.weylGroup` and `P.weylGroup`, characterized
by preserving the action on the weight space `M`. -/
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
/-- `P.indivisibleWeylGroupEquiv w` acts on weights in `M` identically to `w`. -/
@[simp] theorem indivisibleWeylGroupEquiv_smul (w : P.indivisiblePairing.weylGroup) (x : M) :
    P.indivisibleWeylGroupEquiv w • x = w • x := (P.exists_weylGroup_smul_eq w).choose_spec x
/-- `P.indivisibleWeylGroupEquiv.symm w` acts on weights in `M` identically to `w`. -/
@[simp] theorem indivisibleWeylGroupEquiv_symm_smul (w : P.weylGroup) (x : M) :
    (P.indivisibleWeylGroupEquiv.symm w) • x = w • x := by
  simpa using (P.indivisibleWeylGroupEquiv_smul (P.indivisibleWeylGroupEquiv.symm w) x).symm
/-- `P.indivisibleWeylGroupEquiv` maps the reflection in an indivisible root `a` to the reflection
in `a.val` in `P.weylGroup`. -/
@[simp] theorem indivisibleWeylGroupEquiv_ofIdx (a : {i : ι // P.IsIndivisible i}) :
    P.indivisibleWeylGroupEquiv (weylGroup.ofIdx P.indivisiblePairing a) =
      weylGroup.ofIdx P a.val := weylGroup.ext fun x ↦ P.indivisibleWeylGroupEquiv_smul _ x
/-- `P.indivisibleWeylGroupEquiv` intertwines the root-index permutation actions on indivisible
roots. -/
theorem coe_weylGroupToPerm_indivisibleWeylGroupEquiv
    (w : P.indivisiblePairing.weylGroup) (a : {i : ι // P.IsIndivisible i}) :
    (P.indivisiblePairing.weylGroupToPerm w a : ι) =
      P.weylGroupToPerm (P.indivisibleWeylGroupEquiv w) a.val :=
  P.root.injective <| by
    rw [← P.indivisiblePairing_root, ← P.indivisiblePairing.weylGroup_apply_root,
      ← P.weylGroup_apply_root, P.indivisibleWeylGroupEquiv_smul, P.indivisiblePairing_root]
/-- `P.indivisibleWeylGroupEquiv` preserves the linear action on the coweight space `N`. -/
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
  have hli : LinearIndepOn R P₀.root s := P₀.linearIndepOn_root_baseOf' f fun a ↦ hv a.val
  have hsp (a) :=
    IsAddIndecomposable.mem_or_neg_mem_closure_baseOf P₀.root (f : M →+ R) a (hv a.val) (by simp)
  exact ⟨(toFinite s).toFinset, by rwa [Finite.coe_toFinset],
    by rwa [Finite.coe_toFinset, P₀.linearIndepOn_coroot_iff],
    fun a ↦ by rw [Finite.coe_toFinset]; exact hsp a,
    fun a ↦ by rw [Finite.coe_toFinset]; exact P.indivisibleBaseOf_coroot_mem_or_neg_mem hli hsp a⟩
/-- Every simple root in `P.indivisibleBaseOf v hv` pairs positively with `v`. -/
theorem root'_pos_of_mem_indivisibleBaseOf {v : N} {hv : ∀ i : ι, P.root' i v ≠ 0}
    {a : {i : ι // P.IsIndivisible i}} (ha : a ∈ (P.indivisibleBaseOf v hv).support) :
    0 < P.root' a.val v := by
  simp only [indivisibleBaseOf, Finite.mem_toFinset] at ha; exact ha.1

/-- An indivisible root is positive with respect to `P.indivisibleBaseOf v hv` if and only if it
pairs positively with `v`. -/
@[simp] theorem indivisibleBaseOf_isPos_iff {v : N} (hv : ∀ i : ι, P.root' i v ≠ 0)
    (a : {i : ι // P.IsIndivisible i}) :
    (P.indivisibleBaseOf v hv).IsPos a ↔ 0 < P.root' a.val v :=
  have hsupp : ∀ c ∈ (P.indivisibleBaseOf v hv).support, 0 < P.indivisiblePairing.root' c v :=
    fun _ hc ↦ P.root'_pos_of_mem_indivisibleBaseOf hc
  ⟨root'_pos_of_isPos hsupp, fun ha ↦
    by_contra fun hna ↦ ha.not_gt (root'_neg_of_not_isPos hsupp hna)⟩

/-- **Weyl transitivity on regular sign chambers**: for any two regular coweights `x, v : N` of a
finite crystallographic root pairing (reduced or non-reduced), some element `w ∈ P.weylGroup`
carries the `x`-positive roots onto the `v`-positive roots via `P.weylGroupToPerm w`
(Bourbaki, Ch. VI, §1, no. 5). -/
theorem exists_weylGroup_root'_pos_iff {x v : N}
    (hx : ∀ i : ι, P.root' i x ≠ 0) (hv : ∀ i : ι, P.root' i v ≠ 0) :
    ∃ w : P.weylGroup, ∀ i : ι, 0 < P.root' i x ↔ 0 < P.root' (P.weylGroupToPerm w i) v := by
  let P₀ := P.indivisiblePairing; let b := P.indivisibleBaseOf v hv
  have : Fintype {i : ι // P.IsIndivisible i} := Fintype.ofFinite _
  have : Finite P₀.flip.weylGroup := P₀.flip.finite_weylGroup_of_isAnisotropic
  obtain ⟨u, hu⟩ := exists_mem_dominantChamber_of_finite_weylGroup P₀.flip b.flip x
  have hu_open : u • x ∈ openDominantChamber P₀.flip b.flip :=
    mem_openDominantChamber_of_isRegularWeight P₀.flip b.flip hu
      ((isRegularWeight_smul P₀.flip u x).mpr
        ((isRegularWeight_iff P₀.flip x).mpr fun a ↦ hx a.val))
  let w₀ : P₀.weylGroup :=
    ⟨(Equiv.autFlip P₀).symm u.val, Equiv.autFlip_symm_mem_weylGroup_iff.mpr u.property⟩
  let w : P.weylGroup := P.indivisibleWeylGroupEquiv w₀
  have hkey (a : {i : ι // P.IsIndivisible i}) :
      0 < P.root' a.val x ↔ 0 < P.root' (P.weylGroupToPerm w a.val) v := by
    have hperm : P₀.weylGroupToPerm w₀ a = P₀.flip.weylGroupToPerm u a := by
      rw [weylGroupToPerm_apply, weylGroupToPerm_apply]
      exact (congrFun (congrArg DFunLike.coe (Equiv.indexEquiv_autFlip _)) a).symm.trans
        (by rw [MulEquiv.apply_symm_apply])
    have hux : P₀.root' (P₀.flip.weylGroupToPerm u a) (u • x) = P.root' a.val x :=
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

/-- Any family `d : ι → R` obeying the reflection law
`d (P.reflectionPerm i j) = d j - P.pairing j i * d i` is realized on every root by a vector in the
coroot span `P.corootSpan R`. -/
theorem exists_mem_corootSpan_of_forall_reflectionPerm {v : N} (hv : ∀ i : ι, P.root' i v ≠ 0)
    {d : ι → R} (hd : ∀ i j : ι, d (P.reflectionPerm i j) = d j - P.pairing j i * d i) :
    ∃ y ∈ P.corootSpan R, ∀ i : ι, P.root' i y = d i := by
  have := Fintype.ofFinite ι
  let b₀ := P.indivisibleBaseOf v hv
  have hli_supp : LinearIndependent R (fun a : b₀.support ↦ P.root a.val.val) := by
    simpa [LinearIndepOn, funext P.indivisiblePairing_root] using b₀.linearIndepOn_root
  let B := Module.Basis.span hli_supp
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (B.constr R (fun a : b₀.support ↦ d a.val.val))
  obtain ⟨⟨y, hy⟩, hy_eq⟩ :=
    P.bijective_toDualRootSpan_corootSpan.surjective (g ∘ₗ (P.rootSpan R).subtype)
  have hy_supp (a : b₀.support) : P.root' a.val.val y = d a.val.val := by
    have h1 : P.toDualRootSpan y ⟨P.root a.val.val, (P.rootSpanMem R a.val.val).property⟩ =
        g (P.root a.val.val) :=
      congr($hy_eq ⟨P.root a.val.val, (P.rootSpanMem R a.val.val).property⟩)
    have hB : (B a : M) = P.root a.val.val :=
      congrArg Subtype.val (Module.Basis.span_apply hli_supp a)
    simpa [root'] using h1.trans (by simpa [hB, B.constr_basis] using congr($hg (B a)))
  have hy_ind (i : ι) (hi : P.IsIndivisible i) : P.root' i y = d i :=
    b₀.induction_reflect ⟨i, hi⟩ (p := fun c ↦ P.root' c.val y = d c.val)
      (fun a ih ↦ by
        have h := hd a.val a.val; rw [P.pairing_same] at h
        rw [P.coe_indivisiblePairing_reflectionPerm a a, P.root'_reflectionPerm_self,
          LinearMap.neg_apply, ih]; linarith)
      (fun a ha ↦ hy_supp ⟨a, ha⟩) fun a s ih hs ↦ by
        have hr : P.root' (P.reflectionPerm s.val a.val) y =
            P.root' a.val y - P.pairing a.val s.val * P.root' s.val y := by
          simp [root', P.root_reflectionPerm, P.reflection_apply, P.root_coroot'_eq_pairing]
        rw [P.coe_indivisiblePairing_reflectionPerm s a, hr, ih, hy_supp ⟨s, hs⟩, hd s.val a.val]
  refine ⟨y, hy, fun j ↦ (P.isIndivisible_or_exists_root_eq_two_smul j).elim (hy_ind j) ?_⟩
  rintro ⟨i, hi, hij⟩
  have hperm : P.reflectionPerm i j = P.reflectionPerm j j := P.root.injective <| by
    rw [P.root_reflectionPerm, hij, map_smul, P.reflection_apply_self, smul_neg,
      ← hij, P.root_reflectionPerm, P.reflection_apply_self]
  have hpair : P.pairing j i = 4 := by
    rw [← P.root_coroot'_eq_pairing, hij, map_smul, P.root_coroot'_eq_pairing, P.pairing_same]
    norm_num
  have hneg := hd j j; rw [P.pairing_same] at hneg
  have h2 := hd i j; rw [hperm, hpair] at h2
  have hdj : P.root' j y = 2 * P.root' i y := by simp [root', hij]
  rw [hdj, hy_ind i hi]; linarith
end OrderedField
end RootPairing
