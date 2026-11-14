/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.SimplyLaced
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Realization
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
import Mathlib.Data.Finset.NoncommProd
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# The orthogonal orbit-sum fold of a simply laced root system

Let `P` be a finite reduced crystallographic root system over a linearly ordered field `K`, `b` a
simply laced base of `P`, and `σ` an automorphism of `P` that permutes `b.support` and whose
simple-root orbits are pairwise orthogonal:
`∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0`.

Following Stembridge's note *Folding by automorphisms*, this file proves that the distinct
root-orbit sums `P.foldedIndices σ` form a reduced crystallographic root system on
`LinearMap.fixedSubmodule σ.weightMap` and its `K`-linear dual, with simple roots given by the
simple-orbit sums (`RootPairing.orthogonalOrbitSumRealization`). Along the way it establishes:

1. `RootPairing.coroot'_eq_of_mem_orbitIndices`: on any `σ`-fixed weight `x`, the evaluation
   `P.coroot' j x` is constant along `P.orbitIndices σ i`.
2. `RootPairing.orthogonalProd` and `RootPairing.simpleOrbitWeyl`: commuting products of
   pairwise-orthogonal reflections, which for a simple orbit `P.orbitIndices σ i` commute with `σ`
   and act on `LinearMap.fixedSubmodule σ.weightMap` as reflection in `P.orbitSum σ i`.
3. `RootPairing.exists_weylGroup_comm_and_mem_support_of_isPos`: height descent showing every
   `b`-positive root lies in the orbit of `b.support` under the centralizer of `σ` in `P.weylGroup`.
4. `RootPairing.isOrthogonal_of_mem_orbitIndices` (Stembridge's Claim 4): every `σ`-orbit of roots
   is pairwise orthogonal, giving `RootPairing.orbitSum_simplyLacedForm_self` (`2 * |O|`) and the
   general commuting block reflection `RootPairing.orbitWeyl`.
5. `OrbitSumRealization.coroot'_orbitSum`, `OrbitSumRealization.coe_reflection_orbitSum`,
   `OrbitSumRealization.pairingIn_orbitSum`, and `OrbitSumRealization.pairing_orbitSum_eq_div`:
   coroot, reflection, and oriented Cartan formulas on any orbit-sum realization of `(P, b, σ)`.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, Claims 1 and 4, pp. 1–2.
-/

public section

namespace RootPairing

open Finset Function Set TauCeti

/-! ### Coroot constancy along orbits on fixed weights -/

section CorootConstancy

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {σ : P.Aut}

/-- On a `σ`-fixed weight `x`, the coroot functionals `P.coroot' j` take the same value at every
member `j` of the `σ`-orbit of `i`. -/
theorem coroot'_eq_of_mem_orbitIndices {i j : ι} (hj : j ∈ P.orbitIndices σ i)
    {x : M} (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    P.coroot' j x = P.coroot' i x := by
  have hfix : σ • x = x := LinearMap.mem_fixedSubmodule_iff.mp hx
  rcases (mem_orbitIndices_iff_exists_pow (P := P)).mp hj with ⟨k, rfl⟩
  clear hj
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    have hsmul := P.coroot'_smul σ (σ.indexEquiv ((σ.indexEquiv ^ k) i)) x
    rw [hfix, _root_.Equiv.symm_apply_apply] at hsmul
    exact hsmul.trans ih

end CorootConstancy

/-! ### Commuting products of orthogonal reflections -/

section OrthogonalProd

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- The product in `P.weylGroup` of the reflections `weylGroup.ofIdx P j` over a finset `s` of
pairwise-orthogonal root indices. -/
noncomputable def orthogonalProd (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    P.weylGroup :=
  s.noncommProd (fun j ↦ weylGroup.ofIdx P j) fun _ hj _ hk hjk ↦
    weylGroup.commute_ofIdx_of_isOrthogonal P (hs hj hk hjk)

@[simp]
theorem orthogonalProd_empty (hs : ((∅ : Finset ι) : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalProd ∅ hs = 1 := by
  symm; exact (Finset.noncommProd_empty _ _).symm

theorem orthogonalProd_cons {a : ι} {s : Finset ι} (ha : a ∉ s)
    (hs : ((Finset.cons a s ha : Finset ι) : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalProd (Finset.cons a s ha) hs =
      weylGroup.ofIdx P a *
        P.orthogonalProd s (hs.mono fun _ h ↦ Finset.mem_cons.mpr (Or.inr h)) :=
  Finset.noncommProd_cons s a (fun j ↦ weylGroup.ofIdx P j) ha _

/-- A product of pairwise-orthogonal reflections subtracts the orthogonal projections onto each root
in `s` independently. -/
theorem orthogonalProd_smul (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) (x : M) :
    P.orthogonalProd s hs • x = x - ∑ j ∈ s, P.coroot' j x • P.root j := by
  induction s using Finset.cons_induction with
  | empty => rw [orthogonalProd_empty, one_smul, Finset.sum_empty, sub_zero]
  | cons a s ha ih =>
    rw [orthogonalProd_cons, mul_smul, ih (hs.mono fun _ h ↦ Finset.mem_cons.mpr (Or.inr h)),
      weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply]
    have hkill : P.coroot' a (∑ j ∈ s, P.coroot' j x • P.root j) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have horth := hs (Finset.mem_cons.mpr (Or.inr hj)) (Finset.mem_cons_self a s)
        (fun hja ↦ ha (hja ▸ hj))
      rw [map_smul, root_coroot'_eq_pairing, horth.1, smul_zero]
    rw [map_sub, hkill, sub_zero, Finset.sum_cons]
    abel

@[simp]
theorem orthogonalProd_mul_self (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalProd s hs * P.orthogonalProd s hs = 1 := by
  refine weylGroup.eq_one_of_smul_eq_self fun x ↦ ?_
  rw [mul_smul, orthogonalProd_smul, orthogonalProd_smul]
  have hterm (j : ι) (hj : j ∈ s) :
      P.coroot' j (x - ∑ k ∈ s, P.coroot' k x • P.root k) • P.root j =
        -(P.coroot' j x • P.root j) := by
    classical
    rw [map_sub, map_sum, Finset.sum_eq_single j]
    · rw [map_smul, root_coroot'_eq_pairing, pairing_same, smul_eq_mul,
        show P.coroot' j x - P.coroot' j x * 2 = -P.coroot' j x by ring, neg_smul]
    · exact fun k hk hkj ↦ by rw [map_smul, root_coroot'_eq_pairing, (hs hk hj hkj).1, smul_zero]
    · exact fun hnot ↦ absurd hj hnot
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, sub_neg_eq_add, sub_add_cancel]

/-- Every automorphism `g` whose index permutation maps `s` into `s` commutes with
`P.orthogonalProd s hs`. -/
theorem orthogonalProd_comm_aut (s : Finset ι) (hs : (s : Set ι).Pairwise P.IsOrthogonal)
    (g : P.Aut) (hg : ∀ j ∈ s, g.indexEquiv j ∈ s) :
    (P.orthogonalProd s hs : P.Aut) * g = g * (P.orthogonalProd s hs : P.Aut) := by
  classical
  have hs_img : s.image g.indexEquiv = s := Finset.eq_of_subset_of_card_le
    (Finset.image_subset_iff.mpr hg)
    (by rw [Finset.card_image_of_injective _ g.indexEquiv.injective])
  apply Equiv.weightHom_injective P
  rw [map_mul, map_mul]
  ext x
  change P.orthogonalProd s hs • (g • x) = g • (P.orthogonalProd s hs • x)
  rw [orthogonalProd_smul, orthogonalProd_smul, smul_sub]
  congr 1
  have hmap : g • ∑ j ∈ s, P.coroot' j x • P.root j =
      ∑ j ∈ s, P.coroot' j x • P.root (g.indexEquiv j) := by
    change g.weightMap (∑ j ∈ s, P.coroot' j x • P.root j) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, Hom.root_weightMap_apply P P j g.toHom]
  rw [hmap]
  conv_lhs => rw [← hs_img, Finset.sum_image fun _ _ _ _ h ↦ g.indexEquiv.injective h]
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [P.coroot'_smul g (g.indexEquiv j) x, _root_.Equiv.symm_apply_apply]

/-- If `s` consists of pairwise-orthogonal simple roots of `b`, then `P.orthogonalProd s hs`
keeps every `b`-positive root outside `s` positive. -/
theorem isPos_weylGroupToPerm_orthogonalProd [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] {b : P.Base}
    {s : Finset ι} (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsub : s ⊆ b.support)
    {r : ι} (hr : b.IsPos r) (hr_not : r ∉ s) :
    b.IsPos (P.weylGroupToPerm (P.orthogonalProd s hs) r) := by
  induction s using Finset.cons_induction with
  | empty => simpa [orthogonalProd_empty] using hr
  | cons a s ha ih =>
    have hs' : (s : Set ι).Pairwise P.IsOrthogonal :=
      hs.mono fun _ h ↦ Finset.mem_cons.mpr (Or.inr h)
    have hsub' : s ⊆ b.support := fun _ h ↦ hsub (Finset.mem_cons.mpr (Or.inr h))
    have hr_not_s : r ∉ s := fun h ↦ hr_not (Finset.mem_cons.mpr (Or.inr h))
    have hr_ne_a : r ≠ a := fun h ↦ hr_not (h ▸ Finset.mem_cons_self a s)
    rw [orthogonalProd_cons, weylGroupToPerm_ofIdx_mul_apply]
    refine (ih hs' hsub' hr_not_s).reflectionPerm (hsub (Finset.mem_cons_self a s)) fun heq ↦ ?_
    have hfix_a : P.weylGroupToPerm (P.orthogonalProd s hs') a = a := P.root.injective <| by
      rw [← P.weylGroup_apply_root, orthogonalProd_smul, sub_eq_self]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have horth := hs (Finset.mem_cons_self a s) (Finset.mem_cons.mpr (Or.inr hj))
        (fun haj ↦ ha (haj ▸ hj))
      rw [root_coroot'_eq_pairing, horth.1, zero_smul]
    have hrr : P.weylGroupToPerm (P.orthogonalProd s hs')
        (P.weylGroupToPerm (P.orthogonalProd s hs') r) = r := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, orthogonalProd_mul_self, map_one,
        Equiv.Perm.one_apply]
    exact hr_ne_a (hrr ▸ (congrArg (P.weylGroupToPerm (P.orthogonalProd s hs')) heq).trans hfix_a)

end OrthogonalProd

/-! ### Simple-orbit orthogonality and block reflections -/

section SimpleOrbit

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] (b : P.Base) (σ : P.Aut)

/-- Pairwise orthogonality of simple orbits at the orbit representative `i ∈ b.support` extends to
every pair of distinct elements of `P.orbitIndices σ i`. -/
theorem isOrthogonal_of_mem_orbitIndices_of_mem_support
    (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal := by
  intro j hj k hk hjk
  have hj_orb : P.orbitIndices σ j = P.orbitIndices σ i := orbitIndices_eq_of_mem hj
  have hk_orb : P.orbitIndices σ k = P.orbitIndices σ i := orbitIndices_eq_of_mem hk
  exact ⟨horth j (b.orbitIndices_subset_support hσ hi hj) k (hj_orb.symm ▸ hk) hjk,
    horth k (b.orbitIndices_subset_support hσ hi hk) j (hk_orb.symm ▸ hj) hjk.symm⟩

/-- **The commuting block reflection of a simple orbit.** For `i ∈ b.support`, the reflections in
the roots of `P.orbitIndices σ i` commute, and their product in `P.weylGroup` commutes with `σ`. -/
noncomputable def simpleOrbitWeyl (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) : P.weylGroup :=
  P.orthogonalProd (P.orbitIndices σ i)
    (P.isOrthogonal_of_mem_orbitIndices_of_mem_support b σ hσ horth hi)

@[simp]
theorem simpleOrbitWeyl_mul_self (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    P.simpleOrbitWeyl b σ hσ horth hi * P.simpleOrbitWeyl b σ hσ horth hi = 1 :=
  P.orthogonalProd_mul_self _ _

theorem simpleOrbitWeyl_comm_aut (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    (P.simpleOrbitWeyl b σ hσ horth hi : P.Aut) * σ =
      σ * (P.simpleOrbitWeyl b σ hσ horth hi : P.Aut) :=
  P.orthogonalProd_comm_aut _ _ σ fun _ hj ↦ indexEquiv_mem_orbitIndices_iff.mpr hj

theorem simpleOrbitWeyl_smul_of_mem_fixedSubmodule
    (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) {x : M} (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    P.simpleOrbitWeyl b σ hσ horth hi • x = x - P.coroot' i x • P.orbitSum σ i := by
  rw [simpleOrbitWeyl, orthogonalProd_smul, orbitSum_def, Finset.smul_sum]
  exact congrArg (x - ·) (Finset.sum_congr rfl fun j hj ↦ by
    rw [coroot'_eq_of_mem_orbitIndices hj hx])

end SimpleOrbit

/-! ### Simply laced pairing with orbit sums -/

section SimplyLacedOrbitForm

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem]
  (b : P.Base) (σ : P.Aut)

/-- Under `b.simplyLacedForm`, pairing a `σ`-fixed weight `x` with `P.orbitSum σ r` multiplies
`P.coroot' r x` by the orbit size `#(P.orbitIndices σ r)`. -/
theorem simplyLacedForm_apply_orbitSum_of_mem_fixedSubmodule
    (hsl : b.cartanMatrix.IsSimplyLaced) {x : M} (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap)
    (r : ι) :
    (b.simplyLacedForm hsl).form x (P.orbitSum σ r) =
      (#(P.orbitIndices σ r) : R) * P.coroot' r x := by
  rw [orbitSum_def, map_sum]
  have hconst (j : ι) (hj : j ∈ P.orbitIndices σ r) :
      (b.simplyLacedForm hsl).form x (P.root j) = P.coroot' r x := by
    rw [b.simplyLacedForm_apply_root hsl, coroot'_eq_of_mem_orbitIndices hj hx]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

private theorem orbitSum_simplyLacedForm_self_of_pairwise (hsl : b.cartanMatrix.IsSimplyLaced)
    {r : ι} (hpair : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal) :
    (b.simplyLacedForm hsl).form (P.orbitSum σ r) (P.orbitSum σ r) =
      2 * (#(P.orbitIndices σ r) : R) := by
  classical
  rw [P.simplyLacedForm_apply_orbitSum_of_mem_fixedSubmodule b σ hsl
    (P.orbitSum_mem_fixedSubmodule σ r) r, orbitSum_def, map_sum, Finset.sum_eq_single r]
  · rw [root_coroot'_eq_pairing, pairing_same, mul_comm]
  · exact fun j hj hjr ↦ by
      rw [root_coroot'_eq_pairing, (hpair hj (self_mem_orbitIndices P σ r) hjr).1]
  · exact fun hnot ↦ absurd (self_mem_orbitIndices P σ r) hnot

end SimplyLacedOrbitForm

/-! ### Orbit-sum root embedding and unordered field helpers -/

section UnorderedField

variable {ι K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem] (b : P.Base) (σ : P.Aut)

omit [Finite ι] [P.IsRootSystem] in
private def foldedRootEmb :
    P.foldedIndices σ ↪ LinearMap.fixedSubmodule σ.weightMap where
  toFun u := ⟨(u : M), by
    obtain ⟨r, hr⟩ := mem_foldedIndices.mp u.2
    exact hr ▸ P.orbitSum_mem_fixedSubmodule σ r⟩
  inj' _ _ h := Subtype.ext (congrArg (fun x : LinearMap.fixedSubmodule σ.weightMap ↦ (x : M)) h)

private theorem foldedRoot_span_eq_top (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) :
    Submodule.span K (range (P.foldedRootEmb σ)) = ⊤ := by
  rw [eq_top_iff, ← (b.fixedSubmoduleBasis hσ).span_eq]
  refine Submodule.span_mono fun _ ⟨O, hO⟩ ↦ hO ▸ ?_
  exact ⟨⟨P.orbitSum σ (O.out : ι), P.orbitSum_mem_foldedIndices σ _⟩,
    Subtype.ext (b.coe_fixedSubmoduleBasis hσ O).symm⟩

private theorem linearIndepOn_foldedBase (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) :
    LinearIndepOn K (P.foldedRootEmb σ)
      {u : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (u : M)} := by
  let idxMap : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) → P.foldedIndices σ :=
    fun O ↦ ⟨P.orbitSum σ (O.out : ι), P.orbitSum_mem_foldedIndices σ _⟩
  have hcomp : P.foldedRootEmb σ ∘ idxMap = b.fixedSubmoduleBasis hσ :=
    funext fun O ↦ Subtype.ext (b.coe_fixedSubmoduleBasis hσ O).symm
  have hli_comp : LinearIndependent K (P.foldedRootEmb σ ∘ idxMap) :=
    hcomp.symm ▸ (b.fixedSubmoduleBasis hσ).linearIndependent
  have hinj : Injective idxMap :=
    Function.Injective.of_comp (f := P.foldedRootEmb σ) hli_comp.injective
  have hrange : range idxMap =
      {u : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (u : M)} := by
    ext u
    refine ⟨fun ⟨O, hO⟩ ↦ hO ▸ ⟨O.out, O.out.2, rfl⟩, fun ⟨j, hj, hju⟩ ↦ ?_⟩
    let O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ)) := Quotient.mk _ ⟨j, hj⟩
    have hsc : Equiv.Perm.SameCycle σ.indexEquiv (O.out : ι) j :=
      (b.sameCycle_supportPerm_iff hσ).mp (Quotient.exact (Quotient.out_eq O))
    exact ⟨O, Subtype.ext ((orbitSum_eq_of_mem (mem_orbitIndices.mpr hsc.symm)).trans hju)⟩
  exact hrange ▸ (linearIndepOn_range_iff hinj _).mpr hli_comp

end UnorderedField

/-! ### Height descent and Stembridge's Claim 4 -/

section Ordered

variable {ι K M N : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem]
  (b : P.Base) (σ : P.Aut)

private theorem height_weylGroupToPerm_simpleOrbitWeyl
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) (r : ι) :
    (b.height (P.weylGroupToPerm (P.simpleOrbitWeyl b σ hσ horth hi) r) : K) =
      (b.height r : K) - (b.simplyLacedForm hsl).form (P.root r) (P.orbitSum σ i) := by
  calc (b.height (P.weylGroupToPerm (P.simpleOrbitWeyl b σ hσ horth hi) r) : K)
      = heightLinearMap P b
          (P.root r - ∑ j ∈ P.orbitIndices σ i, P.coroot' j (P.root r) • P.root j) := by
        rw [← heightLinearMap_root P b, ← P.weylGroup_apply_root, simpleOrbitWeyl,
          orthogonalProd_smul]
    _ = (b.height r : K) - ∑ j ∈ P.orbitIndices σ i, P.coroot' j (P.root r) := by
        rw [map_sub, heightLinearMap_root, map_sum]
        refine congrArg ((b.height r : K) - ·) (Finset.sum_congr rfl fun j hj ↦ ?_)
        rw [map_smul, heightLinearMap_simpleRoot P b ⟨j, b.orbitIndices_subset_support hσ hi hj⟩,
          smul_eq_mul, mul_one]
    _ = (b.height r : K) - (b.simplyLacedForm hsl).form (P.root r) (P.orbitSum σ i) := by
        rw [orbitSum_def, map_sum]
        exact congrArg ((b.height r : K) - ·)
          (Finset.sum_congr rfl fun j _ ↦ (b.simplyLacedForm_apply_root hsl _ _).symm)

private theorem exists_mem_support_pos_form_orbitSum_of_isPos
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    {r : ι} (hr : b.IsPos r) :
    ∃ i ∈ b.support, 0 < (b.simplyLacedForm hsl).form (P.root r) (P.orbitSum σ i) := by
  set B := b.simplyLacedForm hsl
  have hu_pos : 0 < B.form (P.orbitSum σ r) (P.orbitSum σ r) :=
    b.posDef_simplyLacedForm hsl (P.orbitSum σ r) (orbitSum_ne_zero hσ r)
  obtain ⟨c, hc⟩ := (mem_posRootCone P b).mp (orbitSum_mem_posRootCone hσ hr)
  obtain ⟨i, hi, hipos⟩ : ∃ i ∈ b.support, 0 < B.form (P.orbitSum σ r) (P.root i) := by
    by_contra! hle
    have hnonpos : B.form (P.orbitSum σ r) (∑ j ∈ b.support, c j • P.root j) ≤ 0 := by
      rw [map_sum]
      exact Finset.sum_nonpos fun i hi ↦ by rw [map_nsmul]; exact nsmul_nonpos (hle i hi) (c i)
    exact not_lt_of_ge (hc ▸ hnonpos) hu_pos
  have hprod : 0 < (#(P.orbitIndices σ i) : K) * B.form (P.orbitSum σ r) (P.root i) :=
    mul_pos (Nat.cast_pos.mpr (card_orbitIndices_pos P σ i)) hipos
  have heq : (#(P.orbitIndices σ i) : K) * B.form (P.orbitSum σ r) (P.root i) =
      (#(P.orbitIndices σ r) : K) * B.form (P.root r) (P.orbitSum σ i) := by
    calc (#(P.orbitIndices σ i) : K) * B.form (P.orbitSum σ r) (P.root i)
        = B.form (P.orbitSum σ r) (P.orbitSum σ i) := by
          rw [b.simplyLacedForm_apply_root hsl,
            P.simplyLacedForm_apply_orbitSum_of_mem_fixedSubmodule b σ hsl
              (P.orbitSum_mem_fixedSubmodule σ r) i]
      _ = B.form (P.orbitSum σ i) (P.orbitSum σ r) := B.symm.eq _ _
      _ = (#(P.orbitIndices σ r) : K) * B.form (P.orbitSum σ i) (P.root r) := by
          rw [P.simplyLacedForm_apply_orbitSum_of_mem_fixedSubmodule b σ hsl
            (P.orbitSum_mem_fixedSubmodule σ i) r, ← b.simplyLacedForm_apply_root hsl]
      _ = (#(P.orbitIndices σ r) : K) * B.form (P.root r) (P.orbitSum σ i) :=
          congrArg ((#(P.orbitIndices σ r) : K) * ·) (B.symm.eq (P.orbitSum σ i) (P.root r))
  exact ⟨i, hi, pos_of_mul_pos_right (heq ▸ hprod) (Nat.cast_nonneg _)⟩

/-- **Height descent to a simple orbit.** Every `b`-positive root `r` is the image of some simple
root `i ∈ b.support` under an element `w : P.weylGroup` commuting with `σ`. -/
theorem exists_weylGroup_comm_and_mem_support_of_isPos
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r : ι} (hr : b.IsPos r) :
    ∃ w : P.weylGroup, (w : P.Aut) * σ = σ * (w : P.Aut) ∧
      ∃ i ∈ b.support, P.weylGroupToPerm w i = r := by
  generalize hn : (b.height r).natAbs = n
  induction n using Nat.strongRecOn generalizing r with
  | ind n ih =>
    obtain ⟨i, hi, hpos⟩ := P.exists_mem_support_pos_form_orbitSum_of_isPos b σ hsl hσ hr
    by_cases hmem : r ∈ P.orbitIndices σ i
    · exact ⟨1, by simp, r, b.orbitIndices_subset_support hσ hi hmem, rfl⟩
    · let w_i := P.simpleOrbitWeyl b σ hσ horth hi
      set r' := P.weylGroupToPerm w_i r
      have hr'_pos : b.IsPos r' := P.isPos_weylGroupToPerm_orthogonalProd
        (P.isOrthogonal_of_mem_orbitIndices_of_mem_support b σ hσ horth hi)
        (b.orbitIndices_subset_support hσ hi) hr hmem
      have hlt_K : (b.height r' : K) < (b.height r : K) := by
        rw [P.height_weylGroupToPerm_simpleOrbitWeyl b σ hsl hσ horth hi r]; linarith
      have hlt_Z : b.height r' < b.height r := Int.cast_lt.mp hlt_K
      have hr'_nonneg : 0 ≤ b.height r' := b.isPos_iff'.mp hr'_pos
      obtain ⟨w', hw'_comm, i₀, hi₀, hw'i₀⟩ := ih _ (by lia) hr'_pos rfl
      refine ⟨w_i * w', ?_, i₀, hi₀, ?_⟩
      · calc ((w_i * w' : P.weylGroup) : P.Aut) * σ
            = (w_i : P.Aut) * ((w' : P.Aut) * σ) := by rw [Subgroup.coe_mul, mul_assoc]
          _ = ((w_i : P.Aut) * σ) * (w' : P.Aut) := by rw [hw'_comm, mul_assoc]
          _ = σ * ((w_i * w' : P.weylGroup) : P.Aut) := by
              rw [P.simpleOrbitWeyl_comm_aut b σ hσ horth hi, Subgroup.coe_mul, mul_assoc]
      · rw [map_mul, Equiv.Perm.mul_apply, hw'i₀]
        change P.weylGroupToPerm (w_i * w_i) r = r
        rw [P.simpleOrbitWeyl_mul_self b σ hσ horth hi, map_one, Equiv.Perm.one_apply]

/-- **Stembridge's Claim 4.** When `P` is simply laced over an ordered field and the simple
`σ`-orbits are pairwise orthogonal, **every** `σ`-orbit `P.orbitIndices σ r` is pairwise
orthogonal. -/
theorem isOrthogonal_of_mem_orbitIndices
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) :
    (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal := by
  have hpos_case {s : ι} (hs : b.IsPos s) :
      (P.orbitIndices σ s : Set ι).Pairwise P.IsOrthogonal := by
    obtain ⟨w, hw_comm, i, hi, hwi⟩ :=
      P.exists_weylGroup_comm_and_mem_support_of_isPos b σ hsl hσ horth hs
    have hcomm_idx (z : ι) : (w : P.Aut).indexEquiv (σ.indexEquiv z) =
        σ.indexEquiv ((w : P.Aut).indexEquiv z) :=
      congrArg (fun g : P.Aut ↦ g.indexEquiv z) hw_comm
    have himg {k : ι} (hk : k ∈ P.orbitIndices σ s) :
        (w : P.Aut).indexEquiv.symm k ∈ P.orbitIndices σ i := by
      rw [mem_orbitIndices] at hk ⊢
      have hsymm (z : ι) : (w : P.Aut).indexEquiv.symm (σ.indexEquiv z) =
          σ.indexEquiv ((w : P.Aut).indexEquiv.symm z) :=
        (w : P.Aut).indexEquiv.injective <| by
          rw [_root_.Equiv.apply_symm_apply, hcomm_idx, _root_.Equiv.apply_symm_apply]
      have hws : (w : P.Aut).indexEquiv.symm s = i := by
        rw [← hwi, weylGroupToPerm_apply, _root_.Equiv.symm_apply_apply]
      exact hws ▸ hk.map hsymm
    intro j hj k hk hjk
    have horth_i := P.isOrthogonal_of_mem_orbitIndices_of_mem_support b σ hσ horth hi
      (himg hj) (himg hk) (mt (congrArg (w : P.Aut).indexEquiv) (by simpa using hjk))
    refine ⟨?_, ?_⟩
    · have hp := (w : P.Aut).toHom.pairing (i := (w : P.Aut).indexEquiv.symm j)
        (j := (w : P.Aut).indexEquiv.symm k)
      simpa [_root_.Equiv.apply_symm_apply] using hp.trans horth_i.1
    · have hp := (w : P.Aut).toHom.pairing (i := (w : P.Aut).indexEquiv.symm k)
        (j := (w : P.Aut).indexEquiv.symm j)
      simpa [_root_.Equiv.apply_symm_apply] using hp.trans horth_i.2
  by_cases hr : b.IsPos r
  · exact hpos_case hr
  · have hr_neg : b.IsPos (P.reflectionPerm r r) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b r).mpr ((mem_negRoots P b r).mpr hr)
    have hneg_orb := hpos_case hr_neg
    intro j hj k hk hjk
    have hmap {z : ι} (hz : z ∈ P.orbitIndices σ r) :
        P.reflectionPerm z z ∈ P.orbitIndices σ (P.reflectionPerm r r) := by
      rw [mem_orbitIndices] at hz ⊢
      exact hz.map (g := fun x ↦ P.reflectionPerm x x) fun x ↦
        (σ.toHom.indexEquiv_reflectionPerm x x).symm
    have hne : P.reflectionPerm j j ≠ P.reflectionPerm k k := fun h ↦
      hjk (by rw [← P.reflectionPerm_reflectionPerm_self j, h,
        P.reflectionPerm_reflectionPerm_self])
    have horth_neg := hneg_orb (hmap hj) (hmap hk) hne
    have hpair_neg (x y : ι) :
        P.pairing (P.reflectionPerm x x) (P.reflectionPerm y y) = P.pairing x y := by
      simp only [← root_coroot'_eq_pairing, root_reflectionPerm, reflection_apply_self,
        coroot'_reflectionPerm_self, LinearMap.neg_apply, map_neg, neg_neg]
    exact ⟨(hpair_neg j k).symm.trans horth_neg.1, (hpair_neg k j).symm.trans horth_neg.2⟩

/-- Distinct roots in any `σ`-orbit have zero Cartan pairing. -/
theorem pairing_eq_zero_of_mem_orbitIndices
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r j k : ι} (hj : j ∈ P.orbitIndices σ r) (hk : k ∈ P.orbitIndices σ r) (hjk : j ≠ k) :
    P.pairing j k = 0 :=
  (P.isOrthogonal_of_mem_orbitIndices b σ hsl hσ horth r hj hk hjk).1

/-- Distinct roots in any `σ`-orbit have zero integer Cartan pairing. -/
theorem pairingIn_eq_zero_of_mem_orbitIndices
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r j k : ι} (hj : j ∈ P.orbitIndices σ r) (hk : k ∈ P.orbitIndices σ r) (hjk : j ≠ k) :
    P.pairingIn ℤ j k = 0 := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [algebraMap_pairingIn, map_zero]
  exact P.pairing_eq_zero_of_mem_orbitIndices b σ hsl hσ horth hj hk hjk

/-- **Squared length of every orbit sum.** Under `b.simplyLacedForm`, the squared length of
`P.orbitSum σ r` is `2 * #(P.orbitIndices σ r)` for every root `r`. -/
theorem orbitSum_simplyLacedForm_self
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) :
    (b.simplyLacedForm hsl).form (P.orbitSum σ r) (P.orbitSum σ r) =
      2 * (#(P.orbitIndices σ r) : K) :=
  P.orbitSum_simplyLacedForm_self_of_pairwise b σ hsl
    (P.isOrthogonal_of_mem_orbitIndices b σ hsl hσ horth r)

/-- **The commuting block reflection of an arbitrary root orbit.** -/
noncomputable def orbitWeyl
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) : P.weylGroup :=
  P.orthogonalProd (P.orbitIndices σ r) (P.isOrthogonal_of_mem_orbitIndices b σ hsl hσ horth r)

theorem orbitWeyl_eq_simpleOrbitWeyl
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    P.orbitWeyl b σ hsl hσ horth i = P.simpleOrbitWeyl b σ hσ horth hi := by
  rw [orbitWeyl, simpleOrbitWeyl]

theorem orbitWeyl_comm_aut
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι) :
    (P.orbitWeyl b σ hsl hσ horth r : P.Aut) * σ =
      σ * (P.orbitWeyl b σ hsl hσ horth r : P.Aut) :=
  P.orthogonalProd_comm_aut _ _ σ fun _ hj ↦ indexEquiv_mem_orbitIndices_iff.mpr hj

theorem orbitWeyl_smul_of_mem_fixedSubmodule
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι)
    {x : M} (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    P.orbitWeyl b σ hsl hσ horth r • x = x - P.coroot' r x • P.orbitSum σ r := by
  rw [orbitWeyl, orthogonalProd_smul, orbitSum_def, Finset.smul_sum]
  exact congrArg (x - ·) (Finset.sum_congr rfl fun j hj ↦ by
    rw [coroot'_eq_of_mem_orbitIndices hj hx])

/-! ### Reducedness of the orbit-sum system -/

private theorem root_mem_orbitIndices_of_sum_orthogonal
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s i : ι} (hi : i ∈ b.support) {a : ι → ℕ}
    (ha_supp : P.root s = ∑ m ∈ P.orbitIndices σ i, a m • P.root m) :
    s ∈ P.orbitIndices σ i := by
  classical
  have horth_i := P.isOrthogonal_of_mem_orbitIndices_of_mem_support b σ hσ horth hi
  have hsq_K : (∑ m ∈ P.orbitIndices σ i, (a m * a m : ℕ) : K) * 2 = 2 := by
    calc (∑ m ∈ P.orbitIndices σ i, (a m * a m : ℕ) : K) * 2
        = ∑ m ∈ P.orbitIndices σ i,
            (b.simplyLacedForm hsl).form (P.root s) (a m • P.root m) := by
          push_cast; rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m hm ↦ ?_
          rw [ha_supp, map_nsmul, b.simplyLacedForm_apply_root hsl, map_sum,
            Finset.sum_eq_single m]
          · rw [map_nsmul, root_coroot'_eq_pairing, pairing_same]; simp [nsmul_eq_mul]; ring
          · exact fun l hl hlm ↦ by
              rw [map_nsmul, root_coroot'_eq_pairing, (horth_i hl hm hlm).1, nsmul_zero]
          · exact fun hnot ↦ absurd hm hnot
      _ = (b.simplyLacedForm hsl).form (P.root s) (P.root s) := by rw [← map_sum, ← ha_supp]
      _ = 2 := b.simplyLacedForm_apply_root_self hsl s
  have hsq : ∑ m ∈ P.orbitIndices σ i, a m * a m = 1 :=
    by exact_mod_cast (show (∑ m ∈ P.orbitIndices σ i, (a m * a m : ℕ) : K) = 1 by linarith)
  obtain ⟨m₀, hm₀, ham₀⟩ : ∃ m₀ ∈ P.orbitIndices σ i, a m₀ * a m₀ ≠ 0 := by
    by_contra! hall; have := Finset.sum_eq_zero hall; omega
  have ha_other (m : ι) (hm : m ∈ P.orbitIndices σ i) (hmm₀ : m ≠ m₀) : a m = 0 := by
    have hrest := (Finset.add_sum_erase _ (fun l ↦ a l * a l) hm₀).trans hsq
    have h0 : ∑ l ∈ (P.orbitIndices σ i).erase m₀, a l * a l = 0 := by omega
    have hml := Finset.sum_eq_zero_iff.mp h0 m (Finset.mem_erase.mpr ⟨hmm₀, hm⟩)
    nlinarith
  have ham₀_one : a m₀ = 1 := by
    rw [Finset.sum_eq_single m₀ (fun m hm hmm₀ ↦ by rw [ha_other m hm hmm₀, zero_mul])
      (fun hnot ↦ absurd hm₀ hnot)] at hsq; nlinarith
  have hs_eq : s = m₀ := P.root.injective <| by
    rw [ha_supp, Finset.sum_eq_single m₀ (fun m hm hmm₀ ↦ by rw [ha_other m hm hmm₀, zero_smul])
      (fun hnot ↦ absurd hm₀ hnot), ham₀_one, one_smul]
  exact hs_eq ▸ hm₀

private theorem orbitSum_eq_smul_simple_of_isPos
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s i : ι} (hs : b.IsPos s) (hi : i ∈ b.support) {c : K}
    (heq : P.orbitSum σ s = c • P.orbitSum σ i) : c = 1 := by
  classical
  have hs_mem : s ∈ P.orbitIndices σ s := self_mem_orbitIndices P σ s
  have hrest_cone : ∑ k ∈ (P.orbitIndices σ s).erase s, P.root k ∈ posRootCone P b :=
    sum_mem fun k hk ↦ root_mem_posRootCone_of_mem_posRoots P b ((mem_posRoots P b k).mpr
      ((isPos_iff_of_mem_orbitIndices hσ (Finset.mem_of_mem_erase hk)).mpr hs))
  obtain ⟨a, -, ha⟩ := exists_root_eq_sum_nat_of_mem_posRoots P b ((mem_posRoots P b s).mpr hs)
  obtain ⟨d, hd⟩ := (mem_posRootCone P b).mp hrest_cone
  have hsub_i := b.orbitIndices_subset_support hσ hi
  have hcomb : ∑ m ∈ b.support,
      (((a m + d m : ℕ) : K) - if m ∈ P.orbitIndices σ i then c else 0) • P.root m = 0 := by
    have lhs_eq : ∑ m ∈ b.support, ((a m + d m : ℕ) : K) • P.root m = P.orbitSum σ s := by
      simp_rw [Nat.cast_smul_eq_nsmul, add_smul, Finset.sum_add_distrib, ← ha, ← hd, orbitSum_def,
        Finset.add_sum_erase _ _ hs_mem]
    have rhs_eq : ∑ m ∈ b.support, (if m ∈ P.orbitIndices σ i then c else 0) • P.root m =
        c • P.orbitSum σ i := by
      simp_rw [ite_smul, zero_smul, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub_i,
        orbitSum_def, Finset.smul_sum]
    simp_rw [sub_smul, Finset.sum_sub_distrib, lhs_eq, rhs_eq, heq, sub_self]
  have hcoeff := linearIndepOn_iff'.mp b.linearIndepOn_root b.support _ (fun _ h ↦ h) hcomb
  have ha_supp : P.root s = ∑ m ∈ P.orbitIndices σ i, a m • P.root m := by
    rw [ha, ← Finset.sum_subset hsub_i]
    intro m hm hmi; have hm0 := hcoeff m hm
    simp only [hmi, ite_false, sub_zero, Nat.cast_eq_zero, add_eq_zero] at hm0
    rw [hm0.1, zero_smul]
  have horb_eq : P.orbitSum σ s = P.orbitSum σ i :=
    orbitSum_eq_of_mem (P.root_mem_orbitIndices_of_sum_orthogonal b σ hsl hσ horth hi ha_supp)
  have hzero : (1 - c) • P.orbitSum σ i = 0 := by rw [sub_smul, one_smul, ← heq, horb_eq, sub_self]
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right (orbitSum_ne_zero hσ i))).symm

/-- **Proportional orbit sums differ by a sign.** If one root-orbit sum is a `K`-scalar multiple of
another, the scalar is `1` or `-1`. -/
theorem eq_one_or_neg_one_of_orbitSum_eq_smul
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r₁ r₂ : ι} {c : K} (heq : P.orbitSum σ r₂ = c • P.orbitSum σ r₁) :
    c = 1 ∨ c = -1 := by
  have hpos₁ {t₁ : ι} (ht₁ : b.IsPos t₁) (t₂ : ι) {c' : K}
      (hc' : P.orbitSum σ t₂ = c' • P.orbitSum σ t₁) : c' = 1 ∨ c' = -1 := by
    obtain ⟨w, hw_comm, i, hi, hwi⟩ :=
      P.exists_weylGroup_comm_and_mem_support_of_isPos b σ hsl hσ horth ht₁
    have hwinv_comm (z : ι) : (w⁻¹ : P.weylGroup).val.indexEquiv (σ.indexEquiv z) =
        σ.indexEquiv ((w⁻¹ : P.weylGroup).val.indexEquiv z) := by
      have hcomm_z : (w : P.Aut).indexEquiv (σ.indexEquiv _) =
          σ.indexEquiv ((w : P.Aut).indexEquiv _) :=
        congrArg (fun g : P.Aut ↦ g.indexEquiv ((w⁻¹ : P.weylGroup).val.indexEquiv z)) hw_comm
      apply (w : P.Aut).indexEquiv.injective
      change P.weylGroupToPerm (w * w⁻¹) (σ.indexEquiv z) =
        (w : P.Aut).indexEquiv (σ.indexEquiv ((w⁻¹ : P.weylGroup).val.indexEquiv z))
      rw [mul_inv_cancel, map_one, Equiv.Perm.one_apply, hcomm_z]
      change σ.indexEquiv z = σ.indexEquiv (P.weylGroupToPerm (w * w⁻¹) z)
      rw [mul_inv_cancel, map_one, Equiv.Perm.one_apply]
    have htrans := congrArg (w⁻¹ : P.weylGroup).val.weightMap hc'
    rw [weightMap_orbitSum _ hwinv_comm, map_smul, weightMap_orbitSum _ hwinv_comm] at htrans
    have hwi' : (w⁻¹ : P.weylGroup).val.indexEquiv t₁ = i := by
      rw [← hwi]; change P.weylGroupToPerm (w⁻¹ * w) i = i; simp
    rw [hwi'] at htrans
    set s := (w⁻¹ : P.weylGroup).val.indexEquiv t₂
    by_cases hs : b.IsPos s
    · exact Or.inl (P.orbitSum_eq_smul_simple_of_isPos b σ hsl hσ horth hs hi htrans)
    · have hs_neg : b.IsPos (P.reflectionPerm s s) :=
        (isPos_reflectionPerm_self_iff_mem_negRoots P b s).mpr ((mem_negRoots P b s).mpr hs)
      have htrans_neg : P.orbitSum σ (P.reflectionPerm s s) = (-c') • P.orbitSum σ i := by
        rw [orbitSum_reflectionPerm_self, htrans, neg_smul]
      exact Or.inr (neg_eq_iff_eq_neg.mp
        (P.orbitSum_eq_smul_simple_of_isPos b σ hsl hσ horth hs_neg hi htrans_neg))
  by_cases hr₁ : b.IsPos r₁
  · exact hpos₁ hr₁ r₂ heq
  · have hr₁_neg : b.IsPos (P.reflectionPerm r₁ r₁) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b r₁).mpr ((mem_negRoots P b r₁).mpr hr₁)
    have heq_neg : P.orbitSum σ r₂ = (-c) • P.orbitSum σ (P.reflectionPerm r₁ r₁) := by
      rw [orbitSum_reflectionPerm_self, smul_neg, neg_smul, neg_neg, heq]
    exact (hpos₁ hr₁_neg r₂ heq_neg).imp neg_eq_iff_eq_neg.mp neg_inj.mp |> Or.symm

/-! ### Construction of the orthogonal orbit-sum fold -/

private noncomputable def foldedCorootFun (hsl : b.cartanMatrix.IsSimplyLaced)
    (u : P.foldedIndices σ) : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) :=
  (2 / (b.simplyLacedForm hsl).form (u : M) (u : M)) •
    (((b.simplyLacedForm hsl).form.flip (u : M)).comp
      (LinearMap.fixedSubmodule σ.weightMap).subtype)

private theorem foldedCorootFun_orbitSum_apply
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.foldedCorootFun b σ hsl ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ x =
      P.coroot' r (x : M) := by
  have hcard : (#(P.orbitIndices σ r) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (card_orbitIndices_pos P σ r).ne'
  change (2 / (b.simplyLacedForm hsl).form (P.orbitSum σ r) (P.orbitSum σ r)) *
    (b.simplyLacedForm hsl).form (x : M) (P.orbitSum σ r) = P.coroot' r (x : M)
  rw [P.orbitSum_simplyLacedForm_self b σ hsl hσ horth r,
    P.simplyLacedForm_apply_orbitSum_of_mem_fixedSubmodule b σ hsl x.2 r]
  field_simp

private noncomputable def foldedCorootEmb
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    P.foldedIndices σ ↪ Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) where
  toFun := P.foldedCorootFun b σ hsl
  inj' u₁ u₂ heq := by
    set B := b.simplyLacedForm hsl
    have hpos_form (u : P.foldedIndices σ) : 0 < B.form (u : M) (u : M) :=
      b.posDef_simplyLacedForm hsl (u : M) fun h ↦ zero_notMem_foldedIndices hσ (h ▸ u.2)
    set c₁ := 2 / B.form (u₁ : M) (u₁ : M)
    set c₂ := 2 / B.form (u₂ : M) (u₂ : M)
    have hc₁ : 0 < c₁ := div_pos two_pos (hpos_form u₁)
    have hc₂ : 0 < c₂ := div_pos two_pos (hpos_form u₂)
    let d : LinearMap.fixedSubmodule σ.weightMap :=
      c₁ • P.foldedRootEmb σ u₁ - c₂ • P.foldedRootEmb σ u₂
    have hd_eval : P.foldedCorootFun b σ hsl u₁ d - P.foldedCorootFun b σ hsl u₂ d = 0 := by
      rw [heq, sub_self]
    have hd_quad : B.form (d : M) (d : M) = 0 := by
      change c₁ * B.form (d : M) (u₁ : M) - c₂ * B.form (d : M) (u₂ : M) = 0 at hd_eval
      change B.form (c₁ • (u₁ : M) - c₂ • (u₂ : M)) (d : M) = 0
      rw [map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← B.symm.eq (d : M) (u₁ : M),
        ← B.symm.eq (d : M) (u₂ : M)]
      exact hd_eval
    have hd_zero : (d : M) = 0 :=
      by_contra fun hne ↦ (b.posDef_simplyLacedForm hsl (d : M) hne).ne' hd_quad
    have hprop : (u₂ : M) = (c₁ / c₂) • (u₁ : M) := by
      have hsub : c₁ • (u₁ : M) = c₂ • (u₂ : M) := sub_eq_zero.mp hd_zero
      rw [div_eq_inv_mul, mul_smul, hsub, inv_smul_smul₀ hc₂.ne']
    obtain ⟨r₁, hr₁⟩ := mem_foldedIndices.mp u₁.2
    obtain ⟨r₂, hr₂⟩ := mem_foldedIndices.mp u₂.2
    rw [← hr₁, ← hr₂] at hprop
    rcases P.eq_one_or_neg_one_of_orbitSum_eq_smul b σ hsl hσ horth hprop with hc_eq | hc_eq
    · rw [hc_eq, one_smul] at hprop
      exact Subtype.ext (hr₁.symm.trans (hprop.symm.trans hr₂))
    · exfalso; have := div_pos hc₁ hc₂; linarith

private theorem foldedPair_self
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (u : P.foldedIndices σ) :
    Module.Dual.eval K (LinearMap.fixedSubmodule σ.weightMap)
      (P.foldedRootEmb σ u) (P.foldedCorootEmb b σ hsl hσ horth u) = 2 := by
  obtain ⟨r, hr⟩ := mem_foldedIndices.mp u.2
  have hu : u = ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ := Subtype.ext hr.symm
  subst hu
  change P.foldedCorootFun b σ hsl _ (P.foldedRootEmb σ _) = 2
  rw [P.foldedCorootFun_orbitSum_apply b σ hsl hσ horth r]
  change P.coroot' r (P.orbitSum σ r) = 2
  rw [orbitSum_def, map_sum, Finset.sum_eq_single r]
  · rw [root_coroot'_eq_pairing, pairing_same]
  · exact fun j hj hjr ↦ by
      rw [root_coroot'_eq_pairing, P.pairing_eq_zero_of_mem_orbitIndices b σ hsl hσ horth hj
        (self_mem_orbitIndices P σ r) hjr]
  · exact fun hnot ↦ absurd (self_mem_orbitIndices P σ r) hnot

private theorem foldedPreReflection_mapsTo
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (u : P.foldedIndices σ) :
    MapsTo (Module.preReflection (P.foldedRootEmb σ u)
      ((Module.Dual.eval K (LinearMap.fixedSubmodule σ.weightMap)).flip
        (P.foldedCorootEmb b σ hsl hσ horth u)))
      (range (P.foldedRootEmb σ)) (range (P.foldedRootEmb σ)) := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨r, hr⟩ := mem_foldedIndices.mp u.2
  obtain ⟨t, ht⟩ := mem_foldedIndices.mp v.2
  have hu : u = ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ := Subtype.ext hr.symm
  subst hu
  let w_r := P.orbitWeyl b σ hsl hσ horth r
  have hcomm (z : ι) : (w_r : P.Aut).indexEquiv (σ.indexEquiv z) =
      σ.indexEquiv ((w_r : P.Aut).indexEquiv z) :=
    congrArg (fun g : P.Aut ↦ g.indexEquiv z) (P.orbitWeyl_comm_aut b σ hsl hσ horth r)
  refine ⟨⟨P.orbitSum σ (P.weylGroupToPerm w_r t), P.orbitSum_mem_foldedIndices σ _⟩,
    Subtype.ext ?_⟩
  change P.orbitSum σ (P.weylGroupToPerm w_r t) =
    (v : M) - P.foldedCorootFun b σ hsl _ (P.foldedRootEmb σ v) • P.orbitSum σ r
  rw [P.foldedCorootFun_orbitSum_apply b σ hsl hσ horth r]
  change P.orbitSum σ (P.weylGroupToPerm w_r t) = (v : M) - P.coroot' r (v : M) • P.orbitSum σ r
  rw [← ht, ← P.orbitWeyl_smul_of_mem_fixedSubmodule b σ hsl hσ horth r
    (P.orbitSum_mem_fixedSubmodule σ t)]
  exact (weightMap_orbitSum (w_r : P.Aut) hcomm t).symm

private theorem foldedPair_exists_int
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (u v : P.foldedIndices σ) :
    ∃ z : ℤ, z = Module.Dual.eval K (LinearMap.fixedSubmodule σ.weightMap)
      (P.foldedRootEmb σ u) (P.foldedCorootEmb b σ hsl hσ horth v) := by
  obtain ⟨r, hr⟩ := mem_foldedIndices.mp u.2
  obtain ⟨t, ht⟩ := mem_foldedIndices.mp v.2
  have hv : v = ⟨P.orbitSum σ t, P.orbitSum_mem_foldedIndices σ t⟩ := Subtype.ext ht.symm
  subst hv
  refine ⟨∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k t, ?_⟩
  change _ = P.foldedCorootFun b σ hsl _ (P.foldedRootEmb σ u)
  rw [P.foldedCorootFun_orbitSum_apply b σ hsl hσ horth t]
  change _ = P.coroot' t (u : M)
  rw [← hr, orbitSum_def, map_sum, Int.cast_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by
    rw [root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ, algebraMap_int_eq, eq_intCast]

private noncomputable def foldedPairing
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    RootPairing (P.foldedIndices σ) K (LinearMap.fixedSubmodule σ.weightMap)
      (Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :=
  have : Module.Finite K (LinearMap.fixedSubmodule σ.weightMap) :=
    .of_basis (b.fixedSubmoduleBasis hσ)
  have : Module.Free K (LinearMap.fixedSubmodule σ.weightMap) :=
    .of_basis (b.fixedSubmoduleBasis hσ)
  RootPairing.mk'' (Module.Dual.eval K (LinearMap.fixedSubmodule σ.weightMap))
    (P.foldedRootEmb σ) (P.foldedCorootEmb b σ hsl hσ horth)
    (P.foldedPair_self b σ hsl hσ horth) (P.foldedPreReflection_mapsTo b σ hsl hσ horth)
    (P.foldedRoot_span_eq_top b σ hσ)

private instance isRootSystem_foldedPairing
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    (P.foldedPairing b σ hsl hσ horth).IsRootSystem := by
  have : Module.Finite K (LinearMap.fixedSubmodule σ.weightMap) :=
    .of_basis (b.fixedSubmoduleBasis hσ)
  have : Module.Free K (LinearMap.fixedSubmodule σ.weightMap) :=
    .of_basis (b.fixedSubmoduleBasis hσ)
  dsimp only [foldedPairing]
  exact RootPairing.isRootSystem_mk'' (P.foldedPair_exists_int b σ hsl hσ horth)

private instance isCrystallographic_foldedPairing
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    (P.foldedPairing b σ hsl hσ horth).IsCrystallographic :=
  ⟨P.foldedPair_exists_int b σ hsl hσ horth⟩

private instance isReduced_foldedPairing
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    (P.foldedPairing b σ hsl hσ horth).IsReduced where
  eq_or_eq_neg u v hdep := by
    rw [LinearIndependent.pair_iff, not_forall] at hdep
    obtain ⟨a, ha⟩ := hdep; rw [not_forall] at ha
    obtain ⟨c, hac⟩ := ha; rw [not_imp] at hac
    obtain ⟨hac_zero, hac_ne⟩ := hac
    have ha_ne : a ≠ 0 := by
      rintro rfl; rw [zero_smul, zero_add] at hac_zero
      have hv0 : (v : M) = 0 := congrArg (fun x : LinearMap.fixedSubmodule σ.weightMap ↦ (x : M))
        ((smul_eq_zero.mp hac_zero).resolve_left fun hc0 ↦ hac_ne ⟨rfl, hc0⟩)
      exact zero_notMem_foldedIndices hσ (hv0 ▸ v.2)
    have hu_smul : (u : M) = (-c / a) • (v : M) := by
      have hv0 : a • (u : M) + c • (v : M) = 0 :=
        congrArg (fun x : LinearMap.fixedSubmodule σ.weightMap ↦ (x : M)) hac_zero
      have hval : a • (u : M) = (-c) • (v : M) := by
        rw [neg_smul, eq_neg_of_add_eq_zero_left hv0]
      calc (u : M) = a⁻¹ • (a • (u : M)) := (inv_smul_smul₀ ha_ne _).symm
        _ = (-c / a) • (v : M) := by rw [hval, smul_smul, div_eq_inv_mul]
    obtain ⟨r₁, hr₁⟩ := mem_foldedIndices.mp v.2
    obtain ⟨r₂, hr₂⟩ := mem_foldedIndices.mp u.2
    rw [← hr₁, ← hr₂] at hu_smul
    rcases P.eq_one_or_neg_one_of_orbitSum_eq_smul b σ hsl hσ horth hu_smul with h1 | h1
    · left; apply Subtype.ext; change (u : M) = (v : M)
      rw [← hr₁, ← hr₂, hu_smul, h1, one_smul]
    · right; apply Subtype.ext; change (u : M) = -(v : M)
      rw [← hr₁, ← hr₂, hu_smul, h1, neg_one_smul]

omit [P.IsCrystallographic] [P.IsReduced] in
private theorem foldedBase_mem_closure_of_isPos
    (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support) {r : ι} (hr : b.IsPos r) :
    P.foldedRootEmb σ ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ ∈
      AddSubmonoid.closure (P.foldedRootEmb σ ''
        {u : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (u : M)}) := by
  classical
  set x := P.foldedRootEmb σ ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
  obtain ⟨c, hc⟩ := (mem_posRootCone P b).mp (orbitSum_mem_posRootCone hσ hr)
  have hrepr (O : Quotient (Equiv.Perm.SameCycle.setoid (b.supportPerm hσ))) :
      (b.fixedSubmoduleBasis hσ).repr x O = (c (O.out : ι) : K) := by
    conv_lhs => rw [← Quotient.out_eq O]
    rw [b.fixedSubmoduleBasis_repr hσ x O.out, ← Module.Basis.equivFun_apply]
    change b.toWeightBasis.equivFun (P.orbitSum σ r) O.out = _
    have hbasis_sum : P.orbitSum σ r = ∑ j : b.support, c (j : ι) • b.toWeightBasis j := by
      rw [hc, ← Finset.sum_coe_sort b.support]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [b.toWeightBasis_apply]
    rw [hbasis_sum, map_sum, Finset.sum_apply, Finset.sum_eq_single O.out]
    · rw [map_nsmul, Pi.smul_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, nsmul_eq_mul, mul_one]
    · exact fun j _ hjO ↦ by
        rw [map_nsmul, Pi.smul_apply, Module.Basis.equivFun_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne hjO.symm, nsmul_zero]
    · exact fun hnot ↦ absurd (Finset.mem_univ O.out) hnot
  rw [← (b.fixedSubmoduleBasis hσ).sum_repr x]
  refine sum_mem fun O _ ↦ ?_
  rw [hrepr O, Nat.cast_smul_eq_nsmul]
  refine nsmul_mem (AddSubmonoid.subset_closure ?_) (c (O.out : ι))
  exact ⟨⟨P.orbitSum σ (O.out : ι), P.orbitSum_mem_foldedIndices σ _⟩, ⟨O.out, O.out.2, rfl⟩,
    Subtype.ext (b.coe_fixedSubmoduleBasis hσ O).symm⟩

private noncomputable def foldedBase
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    (P.foldedPairing b σ hsl hσ horth).Base :=
  Base.mk' (P.foldedPairing b σ hsl hσ horth)
    {u : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (u : M)}
    (P.linearIndepOn_foldedBase b σ hσ) fun u ↦ by
      obtain ⟨r, hr⟩ := mem_foldedIndices.mp u.2
      have hu : u = ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ := Subtype.ext hr.symm
      subst hu
      by_cases hr_pos : b.IsPos r
      · exact Or.inl (P.foldedBase_mem_closure_of_isPos b σ hσ hr_pos)
      · right
        have hr_neg : b.IsPos (P.reflectionPerm r r) :=
          (isPos_reflectionPerm_self_iff_mem_negRoots P b r).mpr ((mem_negRoots P b r).mpr hr_pos)
        have hneg_eq : -(P.foldedRootEmb σ ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩) =
            P.foldedRootEmb σ
              ⟨P.orbitSum σ (P.reflectionPerm r r), P.orbitSum_mem_foldedIndices σ _⟩ :=
          Subtype.ext (orbitSum_reflectionPerm_self P σ r).symm
        change -(P.foldedRootEmb σ _) ∈ _
        exact hneg_eq ▸ P.foldedBase_mem_closure_of_isPos b σ hσ hr_neg

/-- **Stembridge's Claim 1 (the orthogonal orbit-sum fold).** For a finite reduced crystallographic
root system `P` over a linearly ordered field `K`, a simply laced base `b`, and an automorphism `σ`
permuting `b.support` whose simple-root orbits are pairwise orthogonal, the distinct orbit sums
`P.foldedIndices σ` form a reduced crystallographic root system on
`LinearMap.fixedSubmodule σ.weightMap` and its `K`-linear dual, with simple roots given by the
simple-orbit sums. -/
noncomputable def orthogonalOrbitSumRealization
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    P.OrbitSumRealization b σ where
  pairing := P.foldedPairing b σ hsl hσ horth
  base := P.foldedBase b σ hsl hσ horth
  rootSystem := inferInstance
  reduced := inferInstance
  crystallographic := inferInstance
  evaluation _ _ := rfl
  root_eq _ := rfl
  base_eq u := by simp [foldedBase, Base.mk']

/-! ### Coroot, reflection, and oriented Cartan formulas on any realization -/

namespace OrbitSumRealization

variable {P b σ}

/-- In any orbit-sum realization of an orthogonal simply laced fold, the folded coroot functional
of `P.orbitSum σ r` acts on fixed weights as `P.coroot' r`. -/
theorem coroot'_orbitSum (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot' ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ x =
      P.coroot' r (x : M) := by
  obtain rfl : F = P.orthogonalOrbitSumRealization b σ hsl hσ horth := Subsingleton.elim _ _
  exact P.foldedCorootFun_orbitSum_apply b σ hsl hσ horth r x

/-- In any orbit-sum realization of an orthogonal simply laced fold, the folded reflection in
`P.orbitSum σ r` acts on `LinearMap.fixedSubmodule σ.weightMap` as the commuting block reflection
`P.orbitWeyl b σ hsl hσ horth r`. -/
theorem coe_reflection_orbitSum (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (F.pairing.reflection ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ x : M) =
      P.orbitWeyl b σ hsl hσ horth r • (x : M) := by
  rw [reflection_apply, Submodule.coe_sub, Submodule.coe_smul, F.coe_root,
    F.coroot'_orbitSum hsl hσ horth r x,
    P.orbitWeyl_smul_of_mem_fixedSubmodule b σ hsl hσ horth r x.2]

/-- **Folded Cartan pairing formula.** Pairing `P.orbitSum σ r` with the folded coroot of
`P.orbitSum σ s` sums `P.pairing k s` over `k ∈ P.orbitIndices σ r`. -/
theorem pairing_orbitSum (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r s : ι) :
    F.pairing.pairing ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
      ⟨P.orbitSum σ s, P.orbitSum_mem_foldedIndices σ s⟩ =
      ∑ k ∈ P.orbitIndices σ r, P.pairing k s := by
  rw [← root_coroot'_eq_pairing, F.coroot'_orbitSum hsl hσ horth s, F.coe_root]
  change P.coroot' s (P.orbitSum σ r) = ∑ k ∈ P.orbitIndices σ r, P.pairing k s
  rw [orbitSum_def, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ P.root_coroot'_eq_pairing s k

/-- **Folded integer Cartan pairing formula.** -/
theorem pairingIn_orbitSum (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r s : ι) :
    F.pairing.pairingIn ℤ ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
      ⟨P.orbitSum σ s, P.orbitSum_mem_foldedIndices σ s⟩ =
      ∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k s := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [algebraMap_pairingIn, F.pairing_orbitSum hsl hσ horth r s, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ (P.algebraMap_pairingIn ℤ k s).symm

/-- **Stembridge's oriented Cartan formula (equation (3)).** The folded pairing of `P.orbitSum σ r`
with the folded coroot of `P.orbitSum σ s` equals the double sum of `P.pairing k l` over both
orbits divided by `#(P.orbitIndices σ s)` (the size of the coroot orbit `s`). -/
theorem pairing_orbitSum_eq_div (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r s : ι) :
    F.pairing.pairing ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
      ⟨P.orbitSum σ s, P.orbitSum_mem_foldedIndices σ s⟩ =
      (∑ k ∈ P.orbitIndices σ r, ∑ l ∈ P.orbitIndices σ s, P.pairing k l) /
        (#(P.orbitIndices σ s) : K) := by
  have hcard : (#(P.orbitIndices σ s) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (card_orbitIndices_pos P σ s).ne'
  rw [F.pairing_orbitSum hsl hσ horth r s, eq_div_iff hcard]
  calc (∑ k ∈ P.orbitIndices σ r, P.pairing k s) * (#(P.orbitIndices σ s) : K)
      = (#(P.orbitIndices σ s) : K) * P.coroot' s (P.orbitSum σ r) := by
        rw [mul_comm, orbitSum_def, map_sum]; rfl
    _ = (b.simplyLacedForm hsl).form (P.orbitSum σ r) (P.orbitSum σ s) :=
        (P.simplyLacedForm_apply_orbitSum_of_mem_fixedSubmodule b σ hsl
          (P.orbitSum_mem_fixedSubmodule σ r) s).symm
    _ = ∑ l ∈ P.orbitIndices σ s, ∑ k ∈ P.orbitIndices σ r, P.pairing k l := by
        rw [orbitSum_def (i := s), map_sum]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [b.simplyLacedForm_apply_root hsl _ l, orbitSum_def, map_sum]
        exact Finset.sum_congr rfl fun k _ ↦ P.root_coroot'_eq_pairing l k
    _ = ∑ k ∈ P.orbitIndices σ r, ∑ l ∈ P.orbitIndices σ s, P.pairing k l := Finset.sum_comm

end OrbitSumRealization

end Ordered

end RootPairing
