/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Realization
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.LinearAlgebra.RootSystem.Height
import TauCeti.LinearAlgebra.RootSystem.HomInvariance
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Basic
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Hom

/-!
# Orthogonal diagram folding and existence of orbit-sum realizations

Let `(P, b)` be a finite reduced crystallographic root pairing over a characteristic-zero domain
and `σ : P.Aut` an automorphism permuting `b.support` whose simple orbits are pairwise orthogonal:
for every `i ∈ b.support` and every `j ∈ P.orbitIndices σ i` with `i ≠ j`, `P.pairing i j = 0`.
This covers both the based diagram automorphisms of simply laced irreducible root systems other
than the reversal of `A₂ₙ` and component-permuting automorphisms of arbitrary semisimple root
systems.

For any root orbit whose members are pairwise orthogonal, the reflections in its constituent roots
commute (`RootPairing.weylGroup.commute_ofIdx_of_isOrthogonal`), so their product defines an
involution `RootPairing.orbitBlockReflection` in `P.weylGroup` that commutes with `σ` and acts on
the fixed space `LinearMap.fixedSubmodule σ.weightMap` as the reflection in `P.orbitSum σ k` with
coroot functional `x ↦ P.coroot' k (x : M)`. Descending `b.height` along the simple-orbit block
reflections via positivity of `(P.posRootForm ℤ).posForm` on nonzero orbit sums shows that every
root lies in the orbit of a simple root under the subgroup of `P.weylGroup` commuting with `σ`.
Consequently:
* **every** root orbit of `σ` is pairwise orthogonal
  (`RootPairing.orbitIndices_pairwise_isOrthogonal`);
* distinct root orbits never share the same orbit sum (`RootPairing.orbitSum_eq_orbitSum_iff`);
* on any `F : P.OrbitSumRealization b σ`, the coroot functional of `P.foldedIndex σ k` is the
  restriction of `P.coroot' k`, the folded Cartan integer is
  `∑ l ∈ P.orbitIndices σ j, P.pairingIn ℤ l k`, and the folded reflection agrees on the fixed
  space with `orbitBlockReflection`;
* over any characteristic-zero field, when `[P.IsRootSystem]`, the unique orbit-sum realization
  exists (`RootPairing.orthogonalOrbitSumRealization`).

## Main definitions

* `RootPairing.orthogonalReflectionProd`: the product in `P.weylGroup` of the reflections in a
  pairwise orthogonal finite set of root indices.
* `RootPairing.orbitBlockReflection`: the block reflection across a pairwise orthogonal `σ`-orbit.
* `RootPairing.orthogonalOrbitSumRealization`: the orbit-sum realization of an orthogonal fold over
  a characteristic-zero field.

## Main results

* `RootPairing.orbitIndices_pairwise_isOrthogonal`: orthogonality of simple orbits propagates to all
  root orbits.
* `RootPairing.orbitSum_eq_orbitSum_iff`: under simple-orbit orthogonality, two roots have the same
  orbit sum if and only if they lie in the same `σ`-orbit.
* `RootPairing.OrbitSumRealization.coroot'_foldedIndex_apply`,
  `RootPairing.OrbitSumRealization.pairingIn_foldedIndex`, and
  `RootPairing.OrbitSumRealization.coe_reflection_foldedIndex`: explicit formulas for coroots,
  Cartan integers, and reflections of any orthogonal orbit-sum realization.
* `RootPairing.rootForm_orbitSum_self`: under simple-orbit orthogonality, the squared canonical
  length of `P.orbitSum σ k` is `#(P.orbitIndices σ k) • P.RootForm (P.root k) (P.root k)`.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, Claims 1–2 and §2.
-/

public section

namespace RootPairing

open Finset Function Module Set Submodule TauCeti

section OrthogonalProd

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- The product in `P.weylGroup` of the reflections in a pairwise orthogonal finite set `s` of root
indices. Because orthogonal roots have commuting reflections, this product is independent of any
ordering of `s`. -/
noncomputable def orthogonalReflectionProd (s : Finset ι)
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) : P.weylGroup :=
  s.noncommProd (weylGroup.ofIdx P)
    (show (s : Set ι).Pairwise (Commute on weylGroup.ofIdx P) from
      fun _ hi _ hj hij ↦ weylGroup.commute_ofIdx_of_isOrthogonal P (hs hi hj hij))

variable {P}

@[simp]
theorem orthogonalReflectionProd_empty
    (hs : ((∅ : Finset ι) : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalReflectionProd ∅ hs = 1 :=
  Finset.noncommProd_empty _ _

theorem orthogonalReflectionProd_cons {a : ι} {t : Finset ι} (ha : a ∉ t)
    (hs : (Finset.cons a t ha : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalReflectionProd (Finset.cons a t ha) hs =
      weylGroup.ofIdx P a *
        P.orthogonalReflectionProd t (hs.mono fun _ h ↦ mem_cons_of_mem h) :=
  Finset.noncommProd_cons _ _ _ _ _

theorem orthogonalReflectionProd_smul {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) (x : M) :
    P.orthogonalReflectionProd s hs • x = x - ∑ j ∈ s, P.coroot' j x • P.root j := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [orthogonalReflectionProd_empty, one_smul, Finset.sum_empty, sub_zero]
  | cons a t ha ih =>
    have ht : (t : Set ι).Pairwise P.IsOrthogonal := hs.mono fun _ h ↦ mem_cons_of_mem h
    rw [orthogonalReflectionProd_cons ha hs, mul_smul, ih ht, weylGroup.ofIdx_smul,
      Equiv.reflection_smul, reflection_apply, map_sub, map_sum]
    have hzero : ∑ i ∈ t, P.coroot' a (P.coroot' i x • P.root i) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by
        have horth := hs (mem_cons_self a t) (mem_cons_of_mem hi)
          (ne_of_mem_of_not_mem hi ha).symm
        rw [map_smul, root_coroot'_eq_pairing, horth.2, smul_zero]
    rw [hzero, sub_zero, Finset.sum_cons, sub_sub, add_comm]

theorem coroot'_orthogonalReflectionProd_smul_of_mem {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) {k : ι} (hk : k ∈ s) (x : M) :
    P.coroot' k (P.orthogonalReflectionProd s hs • x) = -P.coroot' k x := by
  classical
  rw [orthogonalReflectionProd_smul, map_sub, map_sum,
    Finset.sum_eq_single k (fun j hj hjk ↦ by
      rw [map_smul, root_coroot'_eq_pairing, (hs hj hk hjk).1, smul_zero])
      (fun hk' ↦ False.elim (hk' hk)),
    map_smul, root_coroot'_eq_pairing, pairing_same, smul_eq_mul]
  ring

theorem coroot'_orthogonalReflectionProd_smul_of_forall {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) {a : ι}
    (ha : ∀ j ∈ s, P.IsOrthogonal a j) (x : M) :
    P.coroot' a (P.orthogonalReflectionProd s hs • x) = P.coroot' a x := by
  rw [orthogonalReflectionProd_smul, map_sub, map_sum,
    Finset.sum_eq_zero (fun j hj ↦ by
      rw [map_smul, root_coroot'_eq_pairing, (ha j hj).2, smul_zero]),
    sub_zero]

theorem weylGroupToPerm_orthogonalReflectionProd_of_forall {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) {a : ι}
    (ha : ∀ j ∈ s, P.IsOrthogonal a j) :
    P.weylGroupToPerm (P.orthogonalReflectionProd s hs) a = a := by
  refine P.root.injective ?_
  rw [← P.weylGroup_apply_root, orthogonalReflectionProd_smul,
    Finset.sum_eq_zero (fun j hj ↦ by
      rw [root_coroot'_eq_pairing, (ha j hj).1, zero_smul]),
    sub_zero]

@[simp]
theorem orthogonalReflectionProd_mul_self {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    P.orthogonalReflectionProd s hs * P.orthogonalReflectionProd s hs = 1 := by
  refine weylGroup.ext fun x ↦ ?_
  rw [mul_smul, one_smul, orthogonalReflectionProd_smul]
  have hsum : ∑ j ∈ s, P.coroot' j (P.orthogonalReflectionProd s hs • x) • P.root j =
      -∑ j ∈ s, P.coroot' j x • P.root j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [coroot'_orthogonalReflectionProd_smul_of_mem hs hj, neg_smul]
  rw [hsum, orthogonalReflectionProd_smul, sub_neg_eq_add, sub_add_cancel]

@[simp]
theorem orthogonalReflectionProd_inv {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) :
    (P.orthogonalReflectionProd s hs)⁻¹ = P.orthogonalReflectionProd s hs :=
  inv_eq_iff_mul_eq_one.mpr (orthogonalReflectionProd_mul_self hs)

theorem isPos_weylGroupToPerm_orthogonalReflectionProd [Finite ι] [CharZero R] [IsDomain R]
    [P.IsCrystallographic] [P.IsReduced] {b : P.Base} {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsupp : (s : Set ι) ⊆ b.support) {m : ι}
    (hm : b.IsPos m) (hms : m ∉ s) :
    b.IsPos (P.weylGroupToPerm (P.orthogonalReflectionProd s hs) m) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [orthogonalReflectionProd_empty, map_one]
    exact hm
  | cons a t ha ih =>
    have ht : (t : Set ι).Pairwise P.IsOrthogonal := hs.mono fun _ h ↦ mem_cons_of_mem h
    have htsupp : (t : Set ι) ⊆ b.support :=
      Set.Subset.trans (fun _ h ↦ mem_cons_of_mem h) hsupp
    have hmt : m ∉ t := fun h ↦ hms (mem_cons_of_mem h)
    have ha_supp : a ∈ b.support := hsupp (mem_cons_self a t)
    have ha_orth : ∀ j ∈ t, P.IsOrthogonal a j := fun j hj ↦
      hs (mem_cons_self a t) (mem_cons_of_mem hj) (ne_of_mem_of_not_mem hj ha).symm
    rw [orthogonalReflectionProd_cons ha hs, weylGroupToPerm_ofIdx_mul_apply]
    refine (ih ht htsupp hmt).reflectionPerm ha_supp fun heq ↦ hms ?_
    have hfix := weylGroupToPerm_orthogonalReflectionProd_of_forall ht ha_orth
    have hinj := (P.weylGroupToPerm (P.orthogonalReflectionProd t ht)).injective
      (heq.trans hfix.symm)
    exact hinj ▸ mem_cons_self a t

theorem height_weylGroupToPerm_orthogonalReflectionProd [CharZero R] [P.IsCrystallographic]
    {b : P.Base} {s : Finset ι} (hs : (s : Set ι).Pairwise P.IsOrthogonal)
    (hsupp : (s : Set ι) ⊆ b.support) (m : ι) :
    b.height (P.weylGroupToPerm (P.orthogonalReflectionProd s hs) m) =
      b.height m - ∑ j ∈ s, P.pairingIn ℤ m j := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [orthogonalReflectionProd_empty, map_one, Finset.sum_empty, sub_zero]
    rfl
  | cons a t ha ih =>
    have ht : (t : Set ι).Pairwise P.IsOrthogonal := hs.mono fun _ h ↦ mem_cons_of_mem h
    have htsupp : (t : Set ι) ⊆ b.support :=
      Set.Subset.trans (fun _ h ↦ mem_cons_of_mem h) hsupp
    have ha_supp : a ∈ b.support := hsupp (mem_cons_self a t)
    have ha_orth : ∀ j ∈ t, P.IsOrthogonal a j := fun j hj ↦
      hs (mem_cons_self a t) (mem_cons_of_mem hj) (ne_of_mem_of_not_mem hj ha).symm
    rw [orthogonalReflectionProd_cons ha hs, weylGroupToPerm_ofIdx_mul_apply,
      b.height_reflectionPerm_of_mem_support ha_supp, ih ht htsupp, Finset.sum_cons]
    have hpair : P.pairingIn ℤ (P.weylGroupToPerm (P.orthogonalReflectionProd t ht) m) a =
        P.pairingIn ℤ m a := by
      apply FaithfulSMul.algebraMap_injective ℤ R
      rw [algebraMap_pairingIn, algebraMap_pairingIn, ← root_coroot'_eq_pairing,
        ← P.weylGroup_apply_root, coroot'_orthogonalReflectionProd_smul_of_forall ht ha_orth,
        root_coroot'_eq_pairing]
    rw [hpair]
    ring

end OrthogonalProd

/-! ### Block reflections across `σ`-orbits -/

section BlockReflection

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] (σ : P.Aut)

/-- The product of reflections across a pairwise orthogonal `σ`-orbit `P.orbitIndices σ k`. -/
noncomputable def orbitBlockReflection (k : ι)
    (hO : (P.orbitIndices σ k : Set ι).Pairwise P.IsOrthogonal) : P.weylGroup :=
  P.orthogonalReflectionProd (P.orbitIndices σ k) hO

theorem orbitBlockReflection_def (k : ι)
    (hO : (P.orbitIndices σ k : Set ι).Pairwise P.IsOrthogonal) :
    P.orbitBlockReflection σ k hO = P.orthogonalReflectionProd (P.orbitIndices σ k) hO := by
  rw [orbitBlockReflection]

variable {P σ}

theorem coroot'_eq_of_mem_orbitIndices_of_weightMap_eq {k j : ι}
    (hj : j ∈ P.orbitIndices σ k) {x : M} (hx : σ.weightMap x = x) :
    P.coroot' j x = P.coroot' k x := by
  obtain ⟨n, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hj
  clear hj
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    have hstep := σ.coroot'_weightEquiv ((σ.indexEquiv ^ m) k) x
    rw [Equiv.weightEquiv_apply, hx] at hstep
    exact hstep.trans ih

theorem orbitBlockReflection_smul {k : ι}
    (hO : (P.orbitIndices σ k : Set ι).Pairwise P.IsOrthogonal) (x : M) :
    P.orbitBlockReflection σ k hO • x = x - ∑ j ∈ P.orbitIndices σ k, P.coroot' j x • P.root j :=
  orthogonalReflectionProd_smul hO x

theorem orbitBlockReflection_smul_of_weightMap_eq {k : ι}
    (hO : (P.orbitIndices σ k : Set ι).Pairwise P.IsOrthogonal) {x : M}
    (hx : σ.weightMap x = x) :
    P.orbitBlockReflection σ k hO • x = x - P.coroot' k x • P.orbitSum σ k := by
  rw [orbitBlockReflection_smul, orbitSum_def, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j hj ↦ by
    rw [coroot'_eq_of_mem_orbitIndices_of_weightMap_eq hj hx]

@[simp]
theorem orbitBlockReflection_mul_self {k : ι}
    (hO : (P.orbitIndices σ k : Set ι).Pairwise P.IsOrthogonal) :
    P.orbitBlockReflection σ k hO * P.orbitBlockReflection σ k hO = 1 :=
  orthogonalReflectionProd_mul_self hO

@[simp]
theorem orbitBlockReflection_inv {k : ι}
    (hO : (P.orbitIndices σ k : Set ι).Pairwise P.IsOrthogonal) :
    (P.orbitBlockReflection σ k hO)⁻¹ = P.orbitBlockReflection σ k hO :=
  orthogonalReflectionProd_inv hO

/-- Every block reflection across a pairwise orthogonal `σ`-orbit is fixed by conjugation by `σ`. -/
@[simp]
theorem weylGroupEquiv_orbitBlockReflection {k : ι}
    (hO : (P.orbitIndices σ k : Set ι).Pairwise P.IsOrthogonal) :
    σ.weylGroupEquiv (P.orbitBlockReflection σ k hO) = P.orbitBlockReflection σ k hO := by
  refine weylGroup.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := σ.weightEquiv.surjective x
  rw [σ.weylGroupEquiv_smul, orbitBlockReflection_smul, map_sub, map_sum,
    orbitBlockReflection_smul]
  congr 1
  have hterm (j : ι) : σ.weightEquiv (P.coroot' j y • P.root j) =
      P.coroot' (σ.indexEquiv j) (σ.weightEquiv y) • P.root (σ.indexEquiv j) := by
    rw [map_smul, σ.coroot'_weightEquiv, Equiv.weightEquiv_apply,
      Hom.root_weightMap_apply P P j σ.toHom]
  simp_rw [hterm]
  have hmap := map_orbitIndices σ (τ := σ) (fun _ ↦ rfl) k
  rw [orbitIndices_indexEquiv] at hmap
  conv_rhs => rw [← hmap, Finset.sum_map]
  rfl

omit [Finite ι] in
theorem indexEquiv_weylGroupToPerm_of_weylGroupEquiv_eq {w : P.weylGroup}
    (hw : σ.weylGroupEquiv w = w) (m : ι) :
    σ.indexEquiv (P.weylGroupToPerm w m) = P.weylGroupToPerm w (σ.indexEquiv m) := by
  have h := _root_.Equiv.congr_fun (σ.weylGroupToPerm_weylGroupEquiv w) (σ.indexEquiv m)
  rw [hw, _root_.Equiv.permCongr_apply, _root_.Equiv.symm_apply_apply] at h
  exact h.symm

theorem smul_orbitSum_of_weylGroupEquiv_eq {w : P.weylGroup}
    (hw : σ.weylGroupEquiv w = w) (m : ι) :
    w • P.orbitSum σ m = P.orbitSum σ (P.weylGroupToPerm w m) := by
  change (w : P.Aut).weightMap (P.orbitSum σ m) = P.orbitSum σ ((w : P.Aut).indexEquiv m)
  exact weightMap_orbitSum (w : P.Aut) (σ := σ) (τ := σ)
    (fun j ↦ (indexEquiv_weylGroupToPerm_of_weylGroupEquiv_eq hw j).symm) m

end BlockReflection

/-! ### Propagation of orthogonality and injectivity of orbit sums -/

section AllOrbitsOrthogonal

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] {b : P.Base} {σ : P.Aut}

omit [P.IsCrystallographic] in
/-- When every non-self iterate in the simple orbit `P.orbitIndices σ i` has zero pairing with `i`,
the entire orbit is pairwise orthogonal. -/
theorem orbitIndices_pairwise_isOrthogonal_of_mem_support
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal := by
  intro j₁ hj₁ j₂ hj₂ hne
  obtain ⟨n, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hj₁
  have hj₂' : ((σ.indexEquiv ^ n).symm j₂) ∈ P.orbitIndices σ i := by
    obtain ⟨m, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hj₂
    rw [mem_orbitIndices]
    exact ⟨(m : ℤ) - (n : ℤ), by
      rw [sub_eq_neg_add, zpow_add, zpow_neg, zpow_natCast, zpow_natCast]
      rfl⟩
  have hne' : i ≠ (σ.indexEquiv ^ n).symm j₂ := fun heq ↦
    hne (by simpa using congrArg (σ.indexEquiv ^ n) heq)
  have hpair : P.pairing ((σ.indexEquiv ^ n) i) j₂ =
      P.pairing i ((σ.indexEquiv ^ n).symm j₂) := by
    have hpow : ∀ k (x y : ι), P.pairing ((σ.indexEquiv ^ k) x) ((σ.indexEquiv ^ k) y) =
        P.pairing x y := fun k ↦ by
      induction k with
      | zero => intro x y; rfl
      | succ l ih =>
        intro x y
        rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, σ.toHom.pairing, ih]
    simpa using hpow n i ((σ.indexEquiv ^ n).symm j₂)
  have hz : P.pairing ((σ.indexEquiv ^ n) i) j₂ = 0 := hpair.trans (horth i hi _ hj₂' hne')
  exact ⟨hz, P.pairing_eq_zero_iff'.mp hz⟩

omit [IsDomain R] b in
/-- Sum of Cartan integers `∑ l ∈ O_j, P.pairingIn ℤ l m` is independent of the representative
`m ∈ O_k`, so summing over `m ∈ O_k` multiplies by `#(O_k)`. -/
theorem sum_orbitIndices_sum_pairingIn (j k : ι) :
    ∑ m ∈ P.orbitIndices σ k, ∑ l ∈ P.orbitIndices σ j, P.pairingIn ℤ l m =
      (#(P.orbitIndices σ k) : ℤ) * ∑ l ∈ P.orbitIndices σ j, P.pairingIn ℤ l k := by
  have hcol (m : ι) (hm : m ∈ P.orbitIndices σ k) :
      ∑ l ∈ P.orbitIndices σ j, P.pairingIn ℤ l m =
        ∑ l ∈ P.orbitIndices σ j, P.pairingIn ℤ l k := by
    obtain ⟨n, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hm
    clear hm
    induction n with
    | zero => rfl
    | succ r ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ← ih]
      have hmap := map_orbitIndices σ (τ := σ) (fun _ ↦ rfl) j
      rw [orbitIndices_indexEquiv] at hmap
      conv_lhs => rw [← hmap, Finset.sum_map]
      exact Finset.sum_congr rfl fun l _ ↦ σ.toHom.pairingIn_indexEquiv ℤ _ _
  rw [Finset.sum_congr rfl hcol, Finset.sum_const, nsmul_eq_mul]

omit [IsDomain R] b in
/-- Reindexing `∑ l ∈ O_k, ∑ j ∈ O_i, P.pairingIn ℤ l j` along `σ` relates the row and column orbit
sums of Cartan integers. -/
theorem card_orbitIndices_mul_sum_pairingIn (i k : ι) :
    (#(P.orbitIndices σ i) : ℤ) * ∑ l ∈ P.orbitIndices σ k, P.pairingIn ℤ l i =
      (#(P.orbitIndices σ k) : ℤ) * ∑ j ∈ P.orbitIndices σ i, P.pairingIn ℤ k j := by
  have hrow (l : ι) (hl : l ∈ P.orbitIndices σ k) :
      ∑ j ∈ P.orbitIndices σ i, P.pairingIn ℤ l j =
        ∑ j ∈ P.orbitIndices σ i, P.pairingIn ℤ k j := by
    obtain ⟨n, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hl
    clear hl
    induction n with
    | zero => rfl
    | succ r ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ← ih]
      have hmap := map_orbitIndices σ (τ := σ) (fun _ ↦ rfl) i
      rw [orbitIndices_indexEquiv] at hmap
      conv_lhs => rw [← hmap, Finset.sum_map]
      exact Finset.sum_congr rfl fun j _ ↦ σ.toHom.pairingIn_indexEquiv ℤ _ _
  rw [← sum_orbitIndices_sum_pairingIn k i, Finset.sum_comm,
    Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul]

omit [IsDomain R] [Finite ι] b σ in
private theorem two_mul_rootForm_root [Fintype ι] (x : M) (j : ι) :
    2 * P.RootForm x (P.root j) = P.coroot' j x * P.RootForm (P.root j) (P.root j) :=
  (P.posRootForm ℤ).toInvariantForm.two_mul_apply_root x j

omit [IsDomain R] b in
/-- Helper turning positivity of `(P.posRootForm ℤ).posForm z (P.rootSpanMem ℤ i)` into positivity
of `∑ l ∈ O_k, P.pairingIn ℤ l i`. -/
private theorem sum_pairingIn_pos_of_posForm_pos [Fintype ι] {k i : ι}
    (hform_pos : 0 < (P.posRootForm ℤ).posForm
      (∑ l ∈ P.orbitIndices σ k, P.rootSpanMem ℤ l) (P.rootSpanMem ℤ i)) :
    0 < ∑ l ∈ P.orbitIndices σ k, P.pairingIn ℤ l i := by
  set z : P.rootSpan ℤ := ∑ l ∈ P.orbitIndices σ k, P.rootSpanMem ℤ l
  have htwo : 0 < 2 * (P.posRootForm ℤ).posForm z (P.rootSpanMem ℤ i) := by omega
  have hval : 2 * P.RootForm (z : M) (P.root i) =
      algebraMap ℤ R (∑ l ∈ P.orbitIndices σ k, P.pairingIn ℤ l i) *
        P.RootForm (P.root i) (P.root i) := by
    rw [two_mul_rootForm_root (z : M) i]
    congr 1
    have hzc : (z : M) = ∑ l ∈ P.orbitIndices σ k, P.root l := by
      rw [Submodule.coe_sum]
    rw [hzc, map_sum, map_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by
      rw [root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ]
  obtain ⟨s, hs_pos, hs_eq⟩ := (P.posRootForm ℤ).exists_pos_eq i
  have halg : algebraMap ℤ R (2 * (P.posRootForm ℤ).posForm z (P.rootSpanMem ℤ i)) =
      algebraMap ℤ R ((∑ l ∈ P.orbitIndices σ k, P.pairingIn ℤ l i) * s) := by
    rw [map_mul, map_ofNat, P.algebraMap_posRootForm_posForm ℤ z (P.rootSpanMem ℤ i)]
    change 2 * P.RootForm (z : M) (P.root i) = _
    rw [hval, map_mul, hs_eq]
    rfl
  rw [FaithfulSMul.algebraMap_injective ℤ R halg] at htwo
  exact pos_of_mul_pos_left htwo hs_pos.le

/-- Every positive root `k` has strictly positive pairing sum against some simple `σ`-orbit. -/
theorem exists_mem_support_pos_sum_pairingIn
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) {k : ι} (hk : b.IsPos k) :
    ∃ i ∈ b.support, 0 < ∑ j ∈ P.orbitIndices σ i, P.pairingIn ℤ k j := by
  classical
  cases nonempty_fintype ι
  let z : P.rootSpan ℤ := ∑ l ∈ P.orbitIndices σ k, P.rootSpanMem ℤ l
  have hz_coe : (z : M) = P.orbitSum σ k := by
    rw [Submodule.coe_sum, orbitSum_def]
  have hz_ne : z ≠ 0 := fun h ↦ orbitSum_ne_zero hσ k (hz_coe ▸ congrArg Subtype.val h)
  have hpos := P.posRootForm_posForm_pos_of_ne_zero ℤ hz_ne
  obtain ⟨c, hc⟩ := (mem_posRootCone P b).mp (orbitSum_mem_posRootCone hσ hk)
  have hcz : z = ∑ i ∈ b.support, c i • P.rootSpanMem ℤ i := by
    apply Subtype.ext
    rw [hz_coe, hc, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      (Submodule.coe_smul_of_tower (c i) (P.rootSpanMem ℤ i)).symm
  have hpos_sum : ∑ _ ∈ b.support, (0 : ℤ) <
      ∑ j ∈ b.support, (P.posRootForm ℤ).posForm z (c j • P.rootSpanMem ℤ j) := by
    rw [Finset.sum_const_zero, ← map_sum, ← hcz]
    exact hpos
  obtain ⟨i, hi, hipos⟩ := Finset.exists_lt_of_sum_lt hpos_sum
  rw [LinearMap.map_smul_of_tower] at hipos
  have hform_pos : 0 < (P.posRootForm ℤ).posForm z (P.rootSpanMem ℤ i) := by
    by_contra hle
    exact not_lt_of_ge (nsmul_nonpos (not_lt.mp hle) (c i)) hipos
  have hpair_pos := sum_pairingIn_pos_of_posForm_pos hform_pos
  have hcard_i : (0 : ℤ) < #(P.orbitIndices σ i) :=
    Nat.cast_pos.mpr (orbitIndices_nonempty P σ i).card_pos
  have hcard_k : (0 : ℤ) < #(P.orbitIndices σ k) :=
    Nat.cast_pos.mpr (orbitIndices_nonempty P σ k).card_pos
  refine ⟨i, hi, ?_⟩
  have hmul : 0 < (#(P.orbitIndices σ k) : ℤ) * ∑ j ∈ P.orbitIndices σ i, P.pairingIn ℤ k j := by
    rw [← card_orbitIndices_mul_sum_pairingIn]
    exact mul_pos hcard_i hpair_pos
  exact pos_of_mul_pos_right hmul hcard_k.le

variable [P.IsReduced]

/-- Positive-root case of `exists_weylGroup_eq_and_mem_support`, proved by strong induction on
`b.height`. -/
private theorem exists_weylGroup_eq_and_mem_support_of_isPos
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    ∀ n : ℕ, ∀ m : ι, b.IsPos m → (b.height m).natAbs = n →
      ∃ w : P.weylGroup, σ.weylGroupEquiv w = w ∧
        ∃ i ∈ b.support, P.weylGroupToPerm w m = i := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro m hm hn
    by_cases hmem : ∃ i ∈ b.support, m ∈ P.orbitIndices σ i
    · obtain ⟨i, hi, hmi⟩ := hmem
      exact ⟨1, map_one _, m, orbitIndices_subset_support hσ hi hmi, by simp⟩
    · obtain ⟨i, hi, hsum_pos⟩ := exists_mem_support_pos_sum_pairingIn hσ hm
      have hO := orbitIndices_pairwise_isOrthogonal_of_mem_support horth hi
      have hms : m ∉ P.orbitIndices σ i := fun h ↦ hmem ⟨i, hi, h⟩
      let w₀ := P.orbitBlockReflection σ i hO
      let m' := P.weylGroupToPerm w₀ m
      have hm' : b.IsPos m' := isPos_weylGroupToPerm_orthogonalReflectionProd hO
        (orbitIndices_subset_support hσ hi) hm hms
      have hht' : b.height m' = b.height m - ∑ j ∈ P.orbitIndices σ i, P.pairingIn ℤ m j :=
        height_weylGroupToPerm_orthogonalReflectionProd hO (orbitIndices_subset_support hσ hi) m
      have hpos_m : 0 < b.height m := b.isPos_iff.mp hm
      have hpos_m' : 0 < b.height m' := b.isPos_iff.mp hm'
      obtain ⟨w₁, hw₁, i₀, hi₀, hwi₀⟩ := ih _ (by omega) m' hm' rfl
      refine ⟨w₁ * w₀, ?_, i₀, hi₀, ?_⟩
      · rw [map_mul, hw₁, weylGroupEquiv_orbitBlockReflection]
      · rw [map_mul, Equiv.Perm.mul_apply]
        exact hwi₀

/-- Under simple-orbit orthogonality, every root is carried into `b.support` by an element of
`P.weylGroup` fixed by `σ.weylGroupEquiv`. -/
theorem exists_weylGroup_eq_and_mem_support
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) :
    ∃ w : P.weylGroup, σ.weylGroupEquiv w = w ∧ ∃ i ∈ b.support, P.weylGroupToPerm w k = i := by
  by_cases hk : b.IsPos k
  · exact exists_weylGroup_eq_and_mem_support_of_isPos hσ horth _ k hk rfl
  · have hkneg : b.IsPos (P.reflectionPerm k k) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b k).mpr ((mem_negRoots P b k).mpr hk)
    obtain ⟨w, hw, i, hi, hwi⟩ :=
      exists_weylGroup_eq_and_mem_support_of_isPos hσ horth _ (P.reflectionPerm k k) hkneg rfl
    have hO := orbitIndices_pairwise_isOrthogonal_of_mem_support horth hi
    let w₀ := P.orbitBlockReflection σ i hO
    refine ⟨w₀ * w, ?_, i, hi, ?_⟩
    · rw [map_mul, weylGroupEquiv_orbitBlockReflection, hw]
    · apply P.root.injective
      rw [← P.weylGroup_apply_root, mul_smul, P.weylGroup_apply_root]
      have hroot_wk : P.root (P.weylGroupToPerm w k) = -P.root i := by
        have := P.weylGroup_apply_root w (P.reflectionPerm k k)
        rw [hwi, root_reflectionPerm, reflection_apply_self, smul_neg, neg_eq_iff_eq_neg] at this
        rw [← P.weylGroup_apply_root, this]
      rw [hroot_wk, smul_neg, orbitBlockReflection_smul,
        Finset.sum_eq_single i (fun j hj hji ↦ by
          rw [root_coroot'_eq_pairing, (hO hj (self_mem_orbitIndices P σ i) hji).2, zero_smul])
          (fun hi' ↦ False.elim (hi' (self_mem_orbitIndices P σ i))),
        root_coroot'_eq_pairing, pairing_same]
      module

/-- **All root orbits are pairwise orthogonal.** If `σ` permutes `b.support` and every simple orbit
is pairwise orthogonal, then every `σ`-orbit of roots is pairwise orthogonal. -/
theorem orbitIndices_pairwise_isOrthogonal
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) :
    (P.orbitIndices σ k : Set ι).Pairwise P.IsOrthogonal := by
  obtain ⟨w, hw, i, hi, hwk⟩ := exists_weylGroup_eq_and_mem_support hσ horth k
  have hO := orbitIndices_pairwise_isOrthogonal_of_mem_support horth hi
  have hmap := map_orbitIndices (w : P.Aut) (σ := σ) (τ := σ)
    (fun j ↦ (indexEquiv_weylGroupToPerm_of_weylGroupEquiv_eq hw j).symm) k
  change (P.orbitIndices σ k).map (P.weylGroupToPerm w).toEmbedding =
    P.orbitIndices σ (P.weylGroupToPerm w k) at hmap
  rw [hwk] at hmap
  intro j₁ hj₁ j₂ hj₂ hne
  have hj₁' : P.weylGroupToPerm w j₁ ∈ P.orbitIndices σ i :=
    hmap ▸ Finset.mem_map_of_mem _ hj₁
  have hj₂' : P.weylGroupToPerm w j₂ ∈ P.orbitIndices σ i :=
    hmap ▸ Finset.mem_map_of_mem _ hj₂
  have horth' := hO hj₁' hj₂' ((P.weylGroupToPerm w).injective.ne hne)
  exact ⟨by simpa using ((w : P.Aut).toHom.pairing (i := j₁) (j := j₂)).symm.trans horth'.1,
    by simpa using ((w : P.Aut).toHom.pairing (i := j₂) (j := j₁)).symm.trans horth'.2⟩

theorem coroot'_orbitSum_self
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) :
    P.coroot' k (P.orbitSum σ k) = 2 := by
  have hO := orbitIndices_pairwise_isOrthogonal hσ horth k
  rw [orbitSum_def, map_sum,
    Finset.sum_eq_single k (fun j hj hjk ↦ by
      rw [root_coroot'_eq_pairing, (hO hj (self_mem_orbitIndices P σ k) hjk).1])
      (fun hk ↦ False.elim (hk (self_mem_orbitIndices P σ k))),
    root_coroot'_eq_pairing, pairing_same]

/-- In a reduced root pairing, any positive root `k` that is a natural combination of a pairwise
orthogonal subset `s ⊆ b.support` already belongs to `s`. -/
private theorem mem_of_isPos_of_root_eq_sum_nsmul {s : Finset ι}
    (hs : (s : Set ι).Pairwise P.IsOrthogonal) (hsupp : (s : Set ι) ⊆ b.support)
    {k : ι} (hk : b.IsPos k) {c : ι → ℕ} (hc : P.root k = ∑ m ∈ s, c m • P.root m) :
    k ∈ s := by
  classical
  have hne : ∑ m ∈ s, c m • P.root m ≠ 0 := hc ▸ P.ne_zero k
  obtain ⟨m₀, hm₀, hcm₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  replace hcm₀ : c m₀ ≠ 0 := fun h ↦ hcm₀ (by rw [h, zero_smul])
  by_contra hks
  have hk_ne : k ≠ m₀ := fun hkm ↦ hks (hkm ▸ hm₀)
  have hpos_ref : b.IsPos (P.reflectionPerm m₀ k) := hk.reflectionPerm (hsupp hm₀) hk_ne
  obtain ⟨d, hd⟩ := (mem_posRootCone P b).mp
    ((mem_posRoots_iff_root_mem_posRootCone P b).mp ((mem_posRoots P b _).mpr hpos_ref))
  have hcor : P.coroot' m₀ (P.root k) = (2 * c m₀ : ℕ) := by
    rw [hc, map_sum, Finset.sum_eq_single m₀ (fun m hm hne' ↦ by
        rw [map_nsmul, root_coroot'_eq_pairing, (hs hm hm₀ hne').1, nsmul_zero])
        (fun h ↦ False.elim (h hm₀)),
      map_nsmul, root_coroot'_eq_pairing, pairing_same, Nat.cast_mul, Nat.cast_ofNat,
      nsmul_eq_mul, mul_comm]
  have href : P.root (P.reflectionPerm m₀ k) =
      ∑ m ∈ b.support,
        ((if m ∈ s then (c m : R) else 0) - if m = m₀ then (2 * c m₀ : R) else 0) • P.root m := by
    rw [root_reflectionPerm, reflection_apply, hcor, hc]
    have hsub : s ⊆ b.support := hsupp
    have hm₀_supp : m₀ ∈ b.support := hsupp hm₀
    simp_rw [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr hsub, Finset.sum_ite_eq']
    simp only [hm₀_supp, ↓reduceIte, Nat.cast_smul_eq_nsmul, Nat.cast_mul, Nat.cast_ofNat]
  have hdiff : ∑ m ∈ b.support,
      ((d m : R) - ((if m ∈ s then (c m : R) else 0) -
        if m = m₀ then (2 * c m₀ : R) else 0)) • P.root m = 0 := by
    trans (∑ m ∈ b.support, (d m : R) • P.root m) -
      ∑ m ∈ b.support, ((if m ∈ s then (c m : R) else 0) -
        if m = m₀ then (2 * c m₀ : R) else 0) • P.root m
    · rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ ↦ sub_smul _ _ _
    · simp_rw [Nat.cast_smul_eq_nsmul (R := R)]
      rw [← hd, ← href, sub_self]
  have hm₀_eq := linearIndepOn_iff'.mp b.linearIndepOn_root b.support _ subset_rfl hdiff
    m₀ (hsupp hm₀)
  simp only [hm₀, ↓reduceIte] at hm₀_eq
  have hnat : (d m₀ + c m₀ : R) = 0 := by linear_combination hm₀_eq
  have hnat' : d m₀ + c m₀ = 0 := by exact_mod_cast hnat
  omega

/-- If a positive root `k` has orbit sum proportional to the orbit sum of a simple root `i₀`, then
`k` lies in the `σ`-orbit of `i₀`. -/
theorem mem_orbitIndices_of_isPos_of_orbitSum_eq_smul
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i₀ k : ι} (hi₀ : i₀ ∈ b.support) (hk : b.IsPos k) {r : R}
    (heq : P.orbitSum σ k = r • P.orbitSum σ i₀) :
    k ∈ P.orbitIndices σ i₀ := by
  classical
  have hcone (l : ι) (hl : b.IsPos l) : P.root l ∈ posRootCone P b :=
    (mem_posRoots_iff_root_mem_posRootCone P b).mp ((mem_posRoots P b l).mpr hl)
  let f : ι → ι → ℕ := fun l ↦
    if hl : b.IsPos l then ((mem_posRootCone P b).mp (hcone l hl)).choose else 0
  have hf (l : ι) (hl : l ∈ P.orbitIndices σ k) :
      P.root l = ∑ m ∈ b.support, f l m • P.root m := by
    have hlpos : b.IsPos l := (isPos_iff_of_mem_orbitIndices hσ hl).mpr hk
    dsimp only [f]
    split_ifs
    exact ((mem_posRootCone P b).mp (hcone l hlpos)).choose_spec
  have hlhs : P.orbitSum σ k =
      ∑ m ∈ b.support, (∑ l ∈ P.orbitIndices σ k, (f l m : R)) • P.root m := by
    rw [orbitSum_def, Finset.sum_congr rfl (fun l hl ↦ hf l hl)]
    simp_rw [← Nat.cast_smul_eq_nsmul (R := R), Finset.sum_smul]
    exact Finset.sum_comm
  have hrhs : r • P.orbitSum σ i₀ =
      ∑ m ∈ b.support, (if m ∈ P.orbitIndices σ i₀ then r else 0) • P.root m := by
    have hsub : P.orbitIndices σ i₀ ⊆ b.support := orbitIndices_subset_support hσ hi₀
    simp_rw [ite_smul, zero_smul, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub,
      ← Finset.smul_sum, ← orbitSum_def]
  have hdiff : ∑ m ∈ b.support,
      ((∑ l ∈ P.orbitIndices σ k, (f l m : R)) -
        if m ∈ P.orbitIndices σ i₀ then r else 0) • P.root m = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← hlhs, ← hrhs, heq, sub_self]
  have hzero_out {m : ι} (hm : m ∈ b.support) (hm_not : m ∉ P.orbitIndices σ i₀) : f k m = 0 := by
    have hm_eq := linearIndepOn_iff'.mp b.linearIndepOn_root b.support _ subset_rfl hdiff m hm
    simp only [hm_not, ↓reduceIte, sub_zero] at hm_eq
    have hsum_nat : ∑ l ∈ P.orbitIndices σ k, f l m = 0 := by exact_mod_cast hm_eq
    exact Finset.sum_eq_zero_iff.mp hsum_nat k (self_mem_orbitIndices P σ k)
  have hroot_k : P.root k = ∑ m ∈ P.orbitIndices σ i₀, f k m • P.root m := by
    rw [hf k (self_mem_orbitIndices P σ k)]
    exact (Finset.sum_subset (orbitIndices_subset_support hσ hi₀) fun m hm hm_not ↦ by
      rw [hzero_out hm hm_not, zero_smul]).symm
  exact mem_of_isPos_of_root_eq_sum_nsmul
    (orbitIndices_pairwise_isOrthogonal_of_mem_support horth hi₀)
    (orbitIndices_subset_support hσ hi₀) hk hroot_k

/-- **Distinct root orbits have distinct orbit sums** under simple-orbit orthogonality. -/
theorem orbitSum_eq_orbitSum_iff
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {j k : ι} :
    P.orbitSum σ j = P.orbitSum σ k ↔ k ∈ P.orbitIndices σ j := by
  refine ⟨fun heq ↦ ?_, fun hmem ↦ (orbitSum_eq_of_mem hmem).symm⟩
  obtain ⟨w, hw, i₀, hi₀, hwj⟩ := exists_weylGroup_eq_and_mem_support hσ horth j
  have heq' : P.orbitSum σ (P.weylGroupToPerm w k) = (1 : R) • P.orbitSum σ i₀ := by
    rw [one_smul, ← hwj, ← smul_orbitSum_of_weylGroupEquiv_eq hw,
      ← smul_orbitSum_of_weylGroupEquiv_eq hw, heq]
  have hk'_pos : b.IsPos (P.weylGroupToPerm w k) := by
    rw [← orbitSum_mem_posRootCone_iff hσ, heq', one_smul]
    exact orbitSum_mem_posRootCone hσ (b.isPos_of_mem_support hi₀)
  have hmem' := mem_orbitIndices_of_isPos_of_orbitSum_eq_smul hσ horth hi₀ hk'_pos heq'
  rw [← hwj] at hmem'
  have hmap := map_orbitIndices (w : P.Aut) (σ := σ) (τ := σ)
    (fun m ↦ (indexEquiv_weylGroupToPerm_of_weylGroupEquiv_eq hw m).symm) j
  change (P.orbitIndices σ j).map (P.weylGroupToPerm w).toEmbedding =
    P.orbitIndices σ (P.weylGroupToPerm w j) at hmap
  rw [← hmap, Finset.mem_map_equiv] at hmem'
  simpa using hmem'

theorem foldedIndex_eq_foldedIndex_iff
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {j k : ι} :
    P.foldedIndex σ j = P.foldedIndex σ k ↔ k ∈ P.orbitIndices σ j := by
  rw [Subtype.ext_iff, coe_foldedIndex, coe_foldedIndex, orbitSum_eq_orbitSum_iff hσ horth]

/-- Under simple-orbit orthogonality, the squared canonical length of an orbit sum `P.orbitSum σ k`
is `#(P.orbitIndices σ k)` times the squared canonical length of `P.root k`. -/
theorem rootForm_orbitSum_self [Fintype ι]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) :
    P.RootForm (P.orbitSum σ k) (P.orbitSum σ k) =
      #(P.orbitIndices σ k) • P.RootForm (P.root k) (P.root k) := by
  have hO := orbitIndices_pairwise_isOrthogonal hσ horth k
  have hlen (j : ι) (hj : j ∈ P.orbitIndices σ k) :
      P.RootForm (P.root j) (P.root j) = P.RootForm (P.root k) (P.root k) := by
    obtain ⟨n, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hj
    clear hj
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ← Hom.root_weightMap_apply P P _ σ.toHom,
        σ.toHom.rootForm_weightMap, ih]
  have horth_form {j₁ j₂ : ι} (hj₁ : j₁ ∈ P.orbitIndices σ k) (hj₂ : j₂ ∈ P.orbitIndices σ k)
      (hne : j₁ ≠ j₂) : P.RootForm (P.root j₁) (P.root j₂) = 0 := by
    have htwo := two_mul_rootForm_root (P := P) (P.root j₁) j₂
    rw [root_coroot'_eq_pairing, (hO hj₁ hj₂ hne).1, zero_mul, mul_eq_zero] at htwo
    exact htwo.resolve_left two_ne_zero
  rw [orbitSum_def, map_sum]
  calc ∑ j₁ ∈ P.orbitIndices σ k, (P.RootForm (∑ j₂ ∈ P.orbitIndices σ k, P.root j₂)) (P.root j₁)
      = ∑ j₁ ∈ P.orbitIndices σ k, P.RootForm (P.root j₁) (P.root j₁) :=
        Finset.sum_congr rfl fun j₁ hj₁ ↦ by
          rw [map_sum, LinearMap.sum_apply,
            Finset.sum_eq_single j₁ (fun j₂ hj₂ hne ↦ horth_form hj₂ hj₁ hne)
              (fun h ↦ False.elim (h hj₁))]
    _ = #(P.orbitIndices σ k) • P.RootForm (P.root k) (P.root k) := by
        rw [Finset.sum_congr rfl hlen, Finset.sum_const]

end AllOrbitsOrthogonal

/-! ### Coroot, Cartan-integer, and reflection formulas on an orbit-sum realization -/

section RealizationFormulas

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} {σ : P.Aut}

namespace OrbitSumRealization

variable (F : P.OrbitSumRealization b σ)

theorem foldedIndex_mem_support_base_iff
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) :
    P.foldedIndex σ k ∈ F.base.support ↔ k ∈ b.support := by
  refine ⟨fun hk ↦ ?_, F.foldedIndex_mem_support_base⟩
  obtain ⟨i, hi, hik⟩ := (F.base_eq _).mp hk
  rw [coe_foldedIndex] at hik
  exact orbitIndices_subset_support hσ hi ((orbitSum_eq_orbitSum_iff hσ horth).mp hik)

theorem coroot_foldedIndex_eq
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) :
    F.pairing.coroot (P.foldedIndex σ k) =
      (P.coroot' k).comp (LinearMap.fixedSubmodule σ.weightMap).subtype := by
  have : IsReflexive R (LinearMap.fixedSubmodule σ.weightMap) :=
    .of_isPerfPair F.pairing.toLinearMap
  have hrefl_eq : (F.pairing.reflection (P.foldedIndex σ k) :
      LinearMap.fixedSubmodule σ.weightMap → LinearMap.fixedSubmodule σ.weightMap) =
      preReflection (F.pairing.root (P.foldedIndex σ k))
        (F.pairing.coroot (P.foldedIndex σ k)) := by
    ext x
    rw [reflection_apply, preReflection_apply, F.coroot'_eq_coroot]
  refine Dual.eq_of_preReflection_mapsTo (finite_range F.pairing.root)
    F.rootSystem.span_root_eq_top
    ((F.evaluation _ _).symm.trans (F.pairing.root_coroot_two (P.foldedIndex σ k)))
    (hrefl_eq ▸ F.pairing.mapsTo_reflection_root (P.foldedIndex σ k))
    (by
      change P.coroot' k (F.pairing.root (P.foldedIndex σ k) : M) = 2
      rw [F.coe_root_foldedIndex, coroot'_orbitSum_self hσ horth]) ?_
  rintro _ ⟨γ, rfl⟩
  obtain ⟨m, rfl⟩ := P.foldedIndex_surjective σ γ
  have hO := orbitIndices_pairwise_isOrthogonal hσ horth k
  let w := P.orbitBlockReflection σ k hO
  refine ⟨P.foldedIndex σ (P.weylGroupToPerm w m), Subtype.ext ?_⟩
  rw [F.coe_root_foldedIndex, ← smul_orbitSum_of_weylGroupEquiv_eq
    (weylGroupEquiv_orbitBlockReflection hO),
    orbitBlockReflection_smul_of_weightMap_eq hO (P.weightMap_orbitSum_self σ m),
    preReflection_apply, Submodule.coe_sub, Submodule.coe_smul, F.coe_root_foldedIndex,
    LinearMap.comp_apply, Submodule.coe_subtype, F.coe_root_foldedIndex, F.coe_root_foldedIndex]

@[simp]
theorem coroot_foldedIndex_apply
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot (P.foldedIndex σ k) x = P.coroot' k (x : M) := by
  rw [F.coroot_foldedIndex_eq hσ horth]
  rfl

theorem coroot'_foldedIndex_apply
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot' (P.foldedIndex σ k) x = P.coroot' k (x : M) := by
  rw [F.coroot'_eq_coroot, F.coroot_foldedIndex_apply hσ horth]

theorem pairing_foldedIndex
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (j k : ι) :
    F.pairing.pairing (P.foldedIndex σ j) (P.foldedIndex σ k) =
      ∑ l ∈ P.orbitIndices σ j, P.pairing l k := by
  rw [← root_coroot'_eq_pairing, F.coroot'_foldedIndex_apply hσ horth, F.coe_root_foldedIndex,
    orbitSum_def, map_sum]
  exact Finset.sum_congr rfl fun l _ ↦ root_coroot'_eq_pairing P k l

theorem pairingIn_foldedIndex
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (j k : ι) :
    F.pairing.pairingIn ℤ (P.foldedIndex σ j) (P.foldedIndex σ k) =
      ∑ l ∈ P.orbitIndices σ j, P.pairingIn ℤ l k := by
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [algebraMap_pairingIn, F.pairing_foldedIndex hσ horth, map_sum]
  exact Finset.sum_congr rfl fun l _ ↦ (P.algebraMap_pairingIn ℤ l k).symm

/-- Multiplying the folded Cartan integer `⟨β_j, β_k^∨⟩` by `#(O_k)` gives the total sum of
Cartan integers between the orbits `O_j` and `O_k`. -/
theorem card_orbitIndices_mul_pairingIn_foldedIndex
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (j k : ι) :
    (#(P.orbitIndices σ k) : ℤ) *
        F.pairing.pairingIn ℤ (P.foldedIndex σ j) (P.foldedIndex σ k) =
      ∑ m ∈ P.orbitIndices σ k, ∑ l ∈ P.orbitIndices σ j, P.pairingIn ℤ l m := by
  rw [F.pairingIn_foldedIndex hσ horth, sum_orbitIndices_sum_pairingIn]

@[simp]
theorem coe_reflection_foldedIndex
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (F.pairing.reflection (P.foldedIndex σ k) x : M) =
      P.orbitBlockReflection σ k (orbitIndices_pairwise_isOrthogonal hσ horth k) • (x : M) := by
  rw [reflection_apply, Submodule.coe_sub, Submodule.coe_smul,
    F.coroot'_foldedIndex_apply hσ horth, F.coe_root_foldedIndex,
    orbitBlockReflection_smul_of_weightMap_eq _ (LinearMap.mem_fixedSubmodule_iff.mp x.2)]

@[simp]
theorem reflectionPerm_foldedIndex
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k m : ι) :
    F.pairing.reflectionPerm (P.foldedIndex σ k) (P.foldedIndex σ m) =
      P.foldedIndex σ
        (P.weylGroupToPerm
          (P.orbitBlockReflection σ k (orbitIndices_pairwise_isOrthogonal hσ horth k)) m) := by
  apply F.pairing.root.injective
  apply Subtype.ext
  rw [root_reflectionPerm, F.coe_reflection_foldedIndex hσ horth, F.coe_root_foldedIndex,
    F.coe_root_foldedIndex, smul_orbitSum_of_weylGroupEquiv_eq
      (weylGroupEquiv_orbitBlockReflection _)]

end OrbitSumRealization

end RealizationFormulas

/-! ### Existence of the orthogonal orbit-sum realization over a characteristic-zero field -/

section Existence

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- Embedding of `P.foldedIndices σ` into `LinearMap.fixedSubmodule σ.weightMap`. -/
private noncomputable def foldedRootEmb (σ : P.Aut) :
    P.foldedIndices σ ↪ LinearMap.fixedSubmodule σ.weightMap where
  toFun β := ⟨(β : M), by
    obtain ⟨i, hi⟩ := mem_foldedIndices.mp β.2
    exact hi ▸ P.orbitSum_mem_fixedSubmodule σ i⟩
  inj' β₁ β₂ h := Subtype.ext (congrArg (fun x : LinearMap.fixedSubmodule σ.weightMap ↦ (x : M)) h)

omit [CharZero K] [P.IsCrystallographic] [P.IsReduced] in
@[simp]
private theorem coe_foldedRootEmb (σ : P.Aut) (β : P.foldedIndices σ) :
    (P.foldedRootEmb σ β : M) = (β : M) :=
  rfl

/-- Candidate coroot functional on `LinearMap.fixedSubmodule σ.weightMap` for an orthogonal fold. -/
private noncomputable def foldedCorootFun (σ : P.Aut) (β : P.foldedIndices σ) :
    Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) :=
  (P.coroot' (surjInv (P.foldedIndex_surjective σ) β)).comp
    (LinearMap.fixedSubmodule σ.weightMap).subtype

private theorem foldedCorootFun_foldedIndex {b : P.Base} {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (k : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.foldedCorootFun σ (P.foldedIndex σ k) x = P.coroot' k (x : M) := by
  have hrep : P.foldedIndex σ (surjInv (P.foldedIndex_surjective σ) (P.foldedIndex σ k)) =
      P.foldedIndex σ k := surjInv_eq (P.foldedIndex_surjective σ) _
  have hmem := (foldedIndex_eq_foldedIndex_iff hσ horth).mp hrep.symm
  exact coroot'_eq_of_mem_orbitIndices_of_weightMap_eq hmem
    (LinearMap.mem_fixedSubmodule_iff.mp x.2)

private theorem two_mul_rootForm_orbitSum [Fintype ι] {b : P.Base} {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (x : LinearMap.fixedSubmodule σ.weightMap) (k : ι) :
    2 * P.RootForm (x : M) (P.orbitSum σ k) =
      P.coroot' k (x : M) * P.RootForm (P.orbitSum σ k) (P.orbitSum σ k) := by
  have hx := LinearMap.mem_fixedSubmodule_iff.mp x.2
  have hconst (j : ι) (hj : j ∈ P.orbitIndices σ k) :
      P.RootForm (x : M) (P.root j) = P.RootForm (x : M) (P.root k) := by
    obtain ⟨n, rfl⟩ := mem_orbitIndices_iff_exists_pow.mp hj
    clear hj
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ← Hom.root_weightMap_apply P P _ σ.toHom]
      conv_lhs => rw [← hx, σ.toHom.rootForm_weightMap]
      exact ih
  have hsum : P.RootForm (x : M) (P.orbitSum σ k) =
      #(P.orbitIndices σ k) • P.RootForm (x : M) (P.root k) := by
    rw [orbitSum_def, map_sum, Finset.sum_congr rfl hconst, Finset.sum_const]
  have htwo := two_mul_rootForm_root (P := P) (x : M) k
  rw [hsum, rootForm_orbitSum_self hσ horth, nsmul_eq_mul, nsmul_eq_mul]
  linear_combination (#(P.orbitIndices σ k) : K) * htwo

private noncomputable def foldedCorootEmb {b : P.Base} {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    P.foldedIndices σ ↪ Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) where
  toFun := P.foldedCorootFun σ
  inj' β₁ β₂ h := by
    cases nonempty_fintype ι
    obtain ⟨k₁, rfl⟩ := P.foldedIndex_surjective σ β₁
    obtain ⟨k₂, rfl⟩ := P.foldedIndex_surjective σ β₂
    have h₁₂ : P.coroot' k₂ (P.orbitSum σ k₁) = 2 := by
      have := LinearMap.congr_fun h (P.foldedRootEmb σ (P.foldedIndex σ k₁))
      rw [foldedCorootFun_foldedIndex P hσ horth, foldedCorootFun_foldedIndex P hσ horth,
        coe_foldedRootEmb, coe_foldedIndex] at this
      exact this.symm.trans (coroot'_orbitSum_self hσ horth k₁)
    have h₂₁ : P.coroot' k₁ (P.orbitSum σ k₂) = 2 := by
      have := LinearMap.congr_fun h (P.foldedRootEmb σ (P.foldedIndex σ k₂))
      rw [foldedCorootFun_foldedIndex P hσ horth, foldedCorootFun_foldedIndex P hσ horth,
        coe_foldedRootEmb, coe_foldedIndex] at this
      exact this.trans (coroot'_orbitSum_self hσ horth k₂)
    have hf₁₂ : P.RootForm (P.orbitSum σ k₁) (P.orbitSum σ k₂) =
        P.RootForm (P.orbitSum σ k₂) (P.orbitSum σ k₂) := by
      have ht := two_mul_rootForm_orbitSum P hσ horth
        (P.foldedRootEmb σ (P.foldedIndex σ k₁)) k₂
      rw [coe_foldedRootEmb, coe_foldedIndex, h₁₂, mul_right_inj' two_ne_zero] at ht
      exact ht
    have hsymm : P.RootForm (P.orbitSum σ k₂) (P.orbitSum σ k₁) =
        P.RootForm (P.orbitSum σ k₁) (P.orbitSum σ k₂) := by
      simpa using P.rootForm_symmetric.eq (P.orbitSum σ k₂) (P.orbitSum σ k₁)
    have hf₂₁ : P.RootForm (P.orbitSum σ k₁) (P.orbitSum σ k₂) =
        P.RootForm (P.orbitSum σ k₁) (P.orbitSum σ k₁) := by
      have ht := two_mul_rootForm_orbitSum P hσ horth
        (P.foldedRootEmb σ (P.foldedIndex σ k₂)) k₁
      rw [coe_foldedRootEmb, coe_foldedIndex, hsymm, h₂₁, mul_right_inj' two_ne_zero] at ht
      exact ht
    let d : P.rootSpan ℤ :=
      ∑ l ∈ P.orbitIndices σ k₁, P.rootSpanMem ℤ l - ∑ l ∈ P.orbitIndices σ k₂, P.rootSpanMem ℤ l
    have hd_coe : (d : M) = P.orbitSum σ k₁ - P.orbitSum σ k₂ := by
      rw [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_sum, orbitSum_def, orbitSum_def]
    have hd_zero : (P.posRootForm ℤ).posForm d d = 0 := by
      apply FaithfulSMul.algebraMap_injective ℤ K
      rw [map_zero, P.algebraMap_posRootForm_posForm ℤ d d]
      change P.RootForm (d : M) (d : M) = 0
      simp only [hd_coe, map_sub, LinearMap.sub_apply, hsymm, ← hf₂₁, ← hf₁₂]
      ring
    have hd_eq : (d : M) = 0 := congrArg Subtype.val (P.posRootForm_posForm_anisotropic ℤ d hd_zero)
    rw [hd_coe, sub_eq_zero] at hd_eq
    exact Subtype.ext (by rw [coe_foldedIndex, coe_foldedIndex, hd_eq])

omit [CharZero K] [P.IsCrystallographic] [P.IsReduced] in
/-- Shared fiberwise decomposition of a `σ`-orbit-constant combination of `b.support` into
`foldedRootEmb` over a semiring `S`. -/
private theorem exists_sum_foldedRootEmb_eq {S : Type*} [Semiring S] [Module S M] [SMul S K]
    [IsScalarTower S K M] {b : P.Base} {σ : P.Aut} [DecidableEq (P.foldedIndices σ)]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    {x : LinearMap.fixedSubmodule σ.weightMap} {c : ι → S}
    (hc : (x : M) = ∑ k ∈ b.support, c k • P.root k)
    (hconst : ∀ {i j : ι}, i ∈ b.support → j ∈ P.orbitIndices σ i → c j = c i) :
    ∃ d : P.foldedIndices σ → S,
      x = ∑ γ ∈ b.support.image (P.foldedIndex σ), d γ • P.foldedRootEmb σ γ := by
  classical
  let d : P.foldedIndices σ → S := fun γ ↦
    if h : ∃ i ∈ b.support, P.foldedIndex σ i = γ then c h.choose else 0
  refine ⟨d, Subtype.ext ?_⟩
  rw [Submodule.coe_sum, hc,
    ← Finset.sum_fiberwise_of_maps_to (g := P.foldedIndex σ)
      (fun i hi ↦ Finset.mem_image_of_mem _ hi)]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hγ
  have hfib : b.support.filter (fun m ↦ P.foldedIndex σ m = P.foldedIndex σ i₀) =
      P.orbitIndices σ i₀ := by
    ext m
    simp only [Finset.mem_filter, Subtype.ext_iff, coe_foldedIndex]
    exact ⟨fun ⟨hm, hmi⟩ ↦ (orbitSum_eq_orbitSum_iff_of_mem_support hσ hi₀ hm).mp hmi.symm,
      fun hm ↦ ⟨orbitIndices_subset_support hσ hi₀ hm, orbitSum_eq_of_mem hm⟩⟩
  have hd : d (P.foldedIndex σ i₀) = c i₀ := by
    dsimp only [d]
    split_ifs with hex
    · have hval := congrArg Subtype.val hex.choose_spec.2
      rw [coe_foldedIndex, coe_foldedIndex] at hval
      exact hconst hi₀ ((orbitSum_eq_orbitSum_iff_of_mem_support hσ hi₀ hex.choose_spec.1).mp
        hval.symm)
    · exact False.elim (hex ⟨i₀, hi₀, rfl⟩)
  rw [hfib, Submodule.coe_smul_of_tower, coe_foldedRootEmb, coe_foldedIndex, hd,
    orbitSum_def, Finset.smul_sum]
  exact Finset.sum_congr rfl fun m hm ↦ by rw [hconst hi₀ hm]

omit [CharZero K] [P.IsCrystallographic] [P.IsReduced] in
private theorem span_foldedRootEmb_eq_top [P.IsRootSystem] (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) :
    span K (range (P.foldedRootEmb σ)) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  have hspan_supp : (x : M) ∈ span K (P.root '' b.support) := by
    have htop : span K (P.root '' b.support) = ⊤ := by
      rw [eq_top_iff, ← IsRootSystem.span_root_eq_top (P := P), span_le,
        ← span_span_of_tower (R := ℤ)]
      rintro _ ⟨k, rfl⟩
      exact subset_span (b.root_mem_span_int k)
    rw [htop]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' K).mp hspan_supp
  obtain ⟨d, rfl⟩ := exists_sum_foldedRootEmb_eq P hσ hc.symm fun {i j} hi hj ↦
    eq_of_mem_orbitIndices_of_sum_smul_root_eq hσ
      (LinearMap.mem_fixedSubmodule_iff.mp x.2) hc.symm hi hj
  exact sum_mem fun γ _ ↦ Submodule.smul_mem _ _ (subset_span (mem_range_self γ))

private theorem foldedRootEmb_isReduced (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (β₁ β₂ : P.foldedIndices σ)
    (hdep : ¬LinearIndependent K ![P.foldedRootEmb σ β₁, P.foldedRootEmb σ β₂]) :
    P.foldedRootEmb σ β₁ = P.foldedRootEmb σ β₂ ∨
      P.foldedRootEmb σ β₁ = -P.foldedRootEmb σ β₂ := by
  obtain ⟨k₁, rfl⟩ := P.foldedIndex_surjective σ β₁
  obtain ⟨k₂, rfl⟩ := P.foldedIndex_surjective σ β₂
  have hne₁ : P.foldedRootEmb σ (P.foldedIndex σ k₁) ≠ 0 := fun h ↦ by
    have hv := congrArg (fun x : LinearMap.fixedSubmodule σ.weightMap ↦ (x : M)) h
    rw [coe_foldedRootEmb, coe_foldedIndex, Submodule.coe_zero] at hv
    exact orbitSum_ne_zero hσ k₁ hv
  rw [LinearIndependent.pair_iff' hne₁, not_forall] at hdep
  obtain ⟨r, hr⟩ := hdep
  have hval : P.orbitSum σ k₂ = r • P.orbitSum σ k₁ := by
    have hv := congrArg (fun x : LinearMap.fixedSubmodule σ.weightMap ↦ (x : M))
      (not_ne_iff.mp hr).symm
    simpa [coe_foldedRootEmb, coe_foldedIndex] using hv
  obtain ⟨w, hw, i₀, hi₀, hwk₁⟩ := exists_weylGroup_eq_and_mem_support hσ horth k₁
  let k₂' := P.weylGroupToPerm w k₂
  have hval' : P.orbitSum σ k₂' = r • P.orbitSum σ i₀ := by
    rw [← hwk₁, ← smul_orbitSum_of_weylGroupEquiv_eq hw,
      ← smul_orbitSum_of_weylGroupEquiv_eq hw, hval, smul_comm]
  have hpm : P.orbitSum σ k₂' = P.orbitSum σ i₀ ∨ P.orbitSum σ k₂' = -P.orbitSum σ i₀ := by
    by_cases hpos : b.IsPos k₂'
    · exact .inl (orbitSum_eq_of_mem
        (mem_orbitIndices_of_isPos_of_orbitSum_eq_smul hσ horth hi₀ hpos hval'))
    · right
      have hneg_pos : b.IsPos (P.reflectionPerm k₂' k₂') :=
        (isPos_reflectionPerm_self_iff_mem_negRoots P b k₂').mpr ((mem_negRoots P b k₂').mpr hpos)
      have hval_neg : P.orbitSum σ (P.reflectionPerm k₂' k₂') = (-r) • P.orbitSum σ i₀ := by
        rw [orbitSum_reflectionPerm_self, hval', neg_smul]
      have heq := orbitSum_eq_of_mem
        (mem_orbitIndices_of_isPos_of_orbitSum_eq_smul hσ horth hi₀ hneg_pos hval_neg)
      rwa [orbitSum_reflectionPerm_self, neg_eq_iff_eq_neg] at heq
  have hback : ∀ {x y : M}, w • x = w • y → x = y := fun h ↦ by
    simpa using congrArg (w⁻¹ • ·) h
  rcases hpm with h | h
  · left
    apply Subtype.ext
    rw [coe_foldedRootEmb, coe_foldedRootEmb, coe_foldedIndex, coe_foldedIndex]
    exact (hback (by rw [smul_orbitSum_of_weylGroupEquiv_eq hw,
      smul_orbitSum_of_weylGroupEquiv_eq hw, hwk₁]; exact h)).symm
  · right
    apply Subtype.ext
    rw [coe_foldedRootEmb, Submodule.coe_neg, coe_foldedRootEmb, coe_foldedIndex, coe_foldedIndex]
    have h₁ : P.orbitSum σ k₂ = -P.orbitSum σ k₁ :=
      hback (by rw [smul_neg, smul_orbitSum_of_weylGroupEquiv_eq hw,
        smul_orbitSum_of_weylGroupEquiv_eq hw, hwk₁]; exact h)
    rw [h₁, neg_neg]

omit [CharZero K] [P.IsCrystallographic] [P.IsReduced] in
private theorem linearIndepOn_foldedRootEmb (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) :
    LinearIndepOn K (P.foldedRootEmb σ) (P.foldedIndex σ '' b.support) := by
  classical
  rw [linearIndepOn_iff']
  intro t c ht hsum β hβ
  obtain ⟨i₀, hi₀, rfl⟩ := ht hβ
  have hsum_M : ∑ k ∈ b.support,
      (if P.foldedIndex σ k ∈ t then c (P.foldedIndex σ k) else 0) • P.root k = 0 := by
    have hmap : ∀ k ∈ b.support, P.foldedIndex σ k ∈ b.support.image (P.foldedIndex σ) :=
      fun k hk ↦ Finset.mem_image_of_mem _ hk
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    have hval := congrArg (fun x : LinearMap.fixedSubmodule σ.weightMap ↦ (x : M)) hsum
    rw [Submodule.coe_sum, Submodule.coe_zero] at hval
    rw [← hval]
    have hsub_t : t ⊆ b.support.image (P.foldedIndex σ) := fun γ hγ ↦ by
      obtain ⟨i, hi, rfl⟩ := ht hγ
      exact Finset.mem_image_of_mem _ hi
    rw [← Finset.sum_subset hsub_t (fun γ _ hγ ↦
      Finset.sum_eq_zero fun k hk ↦ by simp [(Finset.mem_filter.mp hk).2, hγ])]
    refine Finset.sum_congr rfl fun γ hγ ↦ ?_
    obtain ⟨i, hi, rfl⟩ := ht hγ
    have hfib : b.support.filter (fun k ↦ P.foldedIndex σ k = P.foldedIndex σ i) =
        P.orbitIndices σ i := by
      ext k
      simp only [Finset.mem_filter, Subtype.ext_iff, coe_foldedIndex]
      exact ⟨fun ⟨hk, hki⟩ ↦ (orbitSum_eq_orbitSum_iff_of_mem_support hσ hi hk).mp hki.symm,
        fun hk ↦ ⟨orbitIndices_subset_support hσ hi hk, orbitSum_eq_of_mem hk⟩⟩
    rw [hfib, Submodule.coe_smul, coe_foldedRootEmb, coe_foldedIndex, orbitSum_def, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k hk ↦ by simp only [foldedIndex_eq_of_mem hk, hγ, ↓reduceIte]
  have hi₀_zero := linearIndepOn_iff'.mp b.linearIndepOn_root b.support _ subset_rfl hsum_M i₀ hi₀
  simpa [hβ] using hi₀_zero

omit [P.IsCrystallographic] [P.IsReduced] in
private theorem mem_or_neg_mem_closure_foldedRootEmb (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) (β : P.foldedIndices σ) :
    P.foldedRootEmb σ β ∈
        AddSubmonoid.closure (P.foldedRootEmb σ '' (P.foldedIndex σ '' b.support)) ∨
      -P.foldedRootEmb σ β ∈
        AddSubmonoid.closure (P.foldedRootEmb σ '' (P.foldedIndex σ '' b.support)) := by
  classical
  have hpos_mem : ∀ k : ι, b.IsPos k →
      P.foldedRootEmb σ (P.foldedIndex σ k) ∈
        AddSubmonoid.closure (P.foldedRootEmb σ '' (P.foldedIndex σ '' b.support)) := by
    intro k hk
    obtain ⟨c, hc⟩ := (mem_posRootCone P b).mp (orbitSum_mem_posRootCone hσ hk)
    obtain ⟨d, hd⟩ := exists_sum_foldedRootEmb_eq P hσ
      (x := P.foldedRootEmb σ (P.foldedIndex σ k))
      (by rw [coe_foldedRootEmb, coe_foldedIndex]; exact hc) fun {i j} hi hj ↦ by
        have hcsum : P.orbitSum σ k = ∑ m ∈ b.support, (c m : K) • P.root m := by
          simp_rw [Nat.cast_smul_eq_nsmul]; exact hc
        exact Nat.cast_injective (eq_of_mem_orbitIndices_of_sum_smul_root_eq hσ
          (P.weightMap_orbitSum_self σ k) hcsum hi hj)
    rw [hd]
    refine sum_mem fun γ hγ ↦ nsmul_mem ?_ (d γ)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hγ
    exact AddSubmonoid.subset_closure ⟨P.foldedIndex σ i, ⟨i, hi, rfl⟩, rfl⟩
  obtain ⟨k, rfl⟩ := P.foldedIndex_surjective σ β
  by_cases hk : b.IsPos k
  · exact .inl (hpos_mem k hk)
  · right
    have hkneg : b.IsPos (P.reflectionPerm k k) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b k).mpr ((mem_negRoots P b k).mpr hk)
    have hneg_eq : -P.foldedRootEmb σ (P.foldedIndex σ k) =
        P.foldedRootEmb σ (P.foldedIndex σ (P.reflectionPerm k k)) := by
      apply Subtype.ext
      rw [Submodule.coe_neg, coe_foldedRootEmb, coe_foldedRootEmb, coe_foldedIndex,
        coe_foldedIndex, P.orbitSum_reflectionPerm_self σ k]
    exact hneg_eq ▸ hpos_mem _ hkneg

private theorem mapsTo_preReflection_foldedRootEmb {b : P.Base} {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (β : P.foldedIndices σ) :
    MapsTo
      (preReflection (P.foldedRootEmb σ β)
        ((Dual.eval K (LinearMap.fixedSubmodule σ.weightMap)).flip
          (P.foldedCorootEmb hσ horth β)))
      (range (P.foldedRootEmb σ)) (range (P.foldedRootEmb σ)) := by
  rintro _ ⟨γ, rfl⟩
  obtain ⟨k, rfl⟩ := P.foldedIndex_surjective σ β
  obtain ⟨m, rfl⟩ := P.foldedIndex_surjective σ γ
  have hO := orbitIndices_pairwise_isOrthogonal hσ horth k
  let w := P.orbitBlockReflection σ k hO
  refine ⟨P.foldedIndex σ (P.weylGroupToPerm w m), Subtype.ext ?_⟩
  rw [coe_foldedRootEmb, coe_foldedIndex, preReflection_apply, Submodule.coe_sub,
    Submodule.coe_smul, coe_foldedRootEmb, coe_foldedRootEmb, coe_foldedIndex, coe_foldedIndex]
  change P.orbitSum σ (P.weylGroupToPerm w m) =
    P.orbitSum σ m -
      P.foldedCorootFun σ (P.foldedIndex σ k) (P.foldedRootEmb σ (P.foldedIndex σ m)) •
        P.orbitSum σ k
  rw [foldedCorootFun_foldedIndex P hσ horth, coe_foldedRootEmb, coe_foldedIndex,
    ← orbitBlockReflection_smul_of_weightMap_eq hO (P.weightMap_orbitSum_self σ m),
    smul_orbitSum_of_weylGroupEquiv_eq (weylGroupEquiv_orbitBlockReflection hO)]

private theorem exists_int_eq_foldedRootEmb_foldedCorootEmb {b : P.Base} {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (β γ : P.foldedIndices σ) :
    ∃ z : ℤ, z = Dual.eval K (LinearMap.fixedSubmodule σ.weightMap)
      (P.foldedRootEmb σ β) (P.foldedCorootEmb hσ horth γ) := by
  obtain ⟨j, rfl⟩ := P.foldedIndex_surjective σ β
  obtain ⟨k, rfl⟩ := P.foldedIndex_surjective σ γ
  refine ⟨∑ l ∈ P.orbitIndices σ j, P.pairingIn ℤ l k, ?_⟩
  change algebraMap ℤ K (∑ l ∈ P.orbitIndices σ j, P.pairingIn ℤ l k) =
    P.foldedCorootFun σ (P.foldedIndex σ k) (P.foldedRootEmb σ (P.foldedIndex σ j))
  rw [foldedCorootFun_foldedIndex P hσ horth, coe_foldedRootEmb, coe_foldedIndex,
    orbitSum_def, map_sum, map_sum]
  exact Finset.sum_congr rfl fun l _ ↦ by
    rw [P.algebraMap_pairingIn ℤ, root_coroot'_eq_pairing]

variable [P.IsRootSystem]

/-- **Existence of the orthogonal orbit-sum realization.** Over a characteristic-zero field, if
`σ` permutes `b.support` and every simple `σ`-orbit is pairwise orthogonal, `(P, b, σ)` admits a
unique orbit-sum realization. -/
noncomputable def orthogonalOrbitSumRealization (b : P.Base) (σ : P.Aut)
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    P.OrbitSumRealization b σ := by
  have : Module.Finite K M :=
    Module.finite_def.mpr
      ⟨(Set.toFinite (range P.root)).toFinset,
        by rw [Set.Finite.coe_toFinset, IsRootSystem.span_root_eq_top]⟩
  let p := Dual.eval K (LinearMap.fixedSubmodule σ.weightMap)
  have hp_two : ∀ β : P.foldedIndices σ,
      p (P.foldedRootEmb σ β) (P.foldedCorootEmb hσ horth β) = 2 := fun β ↦ by
    obtain ⟨k, rfl⟩ := P.foldedIndex_surjective σ β
    change P.foldedCorootFun σ (P.foldedIndex σ k) (P.foldedRootEmb σ (P.foldedIndex σ k)) = 2
    rw [foldedCorootFun_foldedIndex P hσ horth, coe_foldedRootEmb, coe_foldedIndex]
    exact coroot'_orbitSum_self hσ horth k
  let Q := RootPairing.mk'' p (P.foldedRootEmb σ) (P.foldedCorootEmb hσ horth)
    hp_two (mapsTo_preReflection_foldedRootEmb P hσ horth) (span_foldedRootEmb_eq_top P b σ hσ)
  have hQ_rs : Q.IsRootSystem :=
    RootPairing.isRootSystem_mk'' (exists_int_eq_foldedRootEmb_foldedCorootEmb P hσ horth)
  have hQ_crys : Q.IsCrystallographic := ⟨exists_int_eq_foldedRootEmb_foldedCorootEmb P hσ horth⟩
  have hQ_red : Q.IsReduced := ⟨foldedRootEmb_isReduced P b σ hσ horth⟩
  exact
    { pairing := Q
      base := Base.mk' Q (P.foldedIndex σ '' b.support)
        (linearIndepOn_foldedRootEmb P b σ hσ)
        (mem_or_neg_mem_closure_foldedRootEmb P b σ hσ)
      rootSystem := hQ_rs
      reduced := hQ_red
      crystallographic := hQ_crys
      evaluation := fun _ _ ↦ rfl
      root_eq := fun _ ↦ rfl
      base_eq := fun β ↦ by
        simp only [Base.mk', Set.Finite.mem_toFinset, Set.mem_image, Finset.mem_coe,
          Subtype.ext_iff, coe_foldedIndex] }

end Existence

end RootPairing
