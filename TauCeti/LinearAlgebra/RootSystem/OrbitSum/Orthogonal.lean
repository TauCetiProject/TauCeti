/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.SimplyLaced
public import TauCeti.LinearAlgebra.RootSystem.OrbitSum.Realization
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Orthogonal
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

1. `RootPairing.pairwise_isOrthogonal_orbitIndices_of_pairing_eq_zero`,
   `RootPairing.orthogonalProd_orbitIndices_comm_aut`,
   `RootPairing.orthogonalProd_orbitIndices_smul_of_mem_fixedSubmodule`, and
   `RootPairing.simpleOrbitWeyl`: single-orbit pairwise orthogonality and commuting block
   reflections acting on `LinearMap.fixedSubmodule σ.weightMap` as reflection in the orbit sum.
2. `OrbitSumRealization.coroot_orbitSum_of_pairwise`,
   `OrbitSumRealization.coe_reflection_orbitSum_of_pairwise`,
   `OrbitSumRealization.pairing_orbitSum_of_pairwise`,
   `OrbitSumRealization.pairingIn_orbitSum_of_pairwise`, and
   `OrbitSumRealization.pairing_orbitSum_eq_div_of_pairwise`: per-orbit coroot, reflection, and
   oriented Cartan formulas on any orbit-sum realization for a single pairwise-orthogonal orbit.
3. `RootPairing.exists_weylGroup_comm_and_mem_support_of_isPos`: height descent showing every
   `b`-positive root lies in the orbit of `b.support` under the centralizer of `σ` in `P.weylGroup`.
4. `RootPairing.pairwise_isOrthogonal_orbitIndices` (Stembridge's Claim 4): every `σ`-orbit of roots
   is pairwise orthogonal, giving `RootPairing.simplyLacedForm_apply_orbitSum_self` (`2 * |O|`), the
   general commuting block reflection `RootPairing.orbitWeyl`, and global coroot, reflection, and
   oriented Cartan formulas (`OrbitSumRealization.coroot_orbitSum`,
   `OrbitSumRealization.coe_reflection_orbitSum`, `OrbitSumRealization.pairingIn_orbitSum`, and
   `OrbitSumRealization.pairing_orbitSum_eq_div`).

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, Claims 1 and 4, pp. 1–3.
-/

public section

namespace RootPairing

open Finset Function Set TauCeti

/-! ### Single-orbit orthogonality and block reflections -/

section SingleOrbit

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι]

/-- If `i` has zero Cartan pairing with every other root in its `σ`-orbit, then the entire orbit
`P.orbitIndices σ i` is pairwise orthogonal. -/
theorem pairwise_isOrthogonal_orbitIndices_of_pairing_eq_zero (σ : P.Aut) {i : ι}
    (horth : ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal := by
  have hp {u v : ι} (hu : u ∈ P.orbitIndices σ i) (hv : v ∈ P.orbitIndices σ i)
      (huv : u ≠ v) : P.pairing u v = 0 := by
    obtain ⟨m, rfl⟩ := (mem_orbitIndices_iff_exists_pow (P := P)).mp hu
    let g : P.Aut := σ ^ m
    have hg_idx : g.indexEquiv = σ.indexEquiv ^ m := by
      rw [← Equiv.indexHom_apply, map_pow, Equiv.indexHom_apply]
    have hg_symm : g.indexEquiv.symm = σ.indexEquiv ^ (-(m : ℤ)) := by
      rw [← Equiv.Perm.inv_def, hg_idx, ← zpow_natCast, ← zpow_neg]
    have hv' : g.indexEquiv.symm v ∈ P.orbitIndices σ i := by
      rw [mem_orbitIndices, hg_symm, Equiv.Perm.sameCycle_zpow_right]
      exact mem_orbitIndices.mp hv
    have hne : i ≠ g.indexEquiv.symm v := fun h ↦
      huv (by rw [← hg_idx, h, _root_.Equiv.apply_symm_apply])
    have hpair := g.toHom.pairing (i := i) (j := g.indexEquiv.symm v)
    rwa [_root_.Equiv.apply_symm_apply, horth _ hv' hne, hg_idx] at hpair
  exact fun _ hj _ hk hjk ↦ ⟨hp hj hk hjk, hp hk hj hjk.symm⟩

/-- For a pairwise-orthogonal `σ`-orbit `P.orbitIndices σ r`, evaluating `P.coroot' r` on
`P.orbitSum σ r` yields `2`. -/
theorem coroot'_orbitSum_self_of_pairwise (σ : P.Aut) {r : ι}
    (hr : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal) :
    P.coroot' r (P.orbitSum σ r) = 2 := by
  classical
  rw [orbitSum_def, map_sum, Finset.sum_eq_single r]
  · rw [root_coroot'_eq_pairing, pairing_same]
  · exact fun j hj hjr ↦ by
      rw [root_coroot'_eq_pairing, (hr hj (self_mem_orbitIndices P σ r) hjr).1]
  · exact fun hnot ↦ absurd (self_mem_orbitIndices P σ r) hnot

/-- The product of reflections over a pairwise-orthogonal `σ`-orbit commutes with `σ`. -/
theorem orthogonalProd_orbitIndices_comm_aut (σ : P.Aut) {r : ι}
    (hr : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal) :
    (P.orthogonalProd (P.orbitIndices σ r) hr : P.Aut) * σ =
      σ * (P.orthogonalProd (P.orbitIndices σ r) hr : P.Aut) :=
  P.orthogonalProd_comm_aut _ _ σ fun _ hj ↦ indexEquiv_mem_orbitIndices_iff.mpr hj

/-- On a `σ`-fixed weight `x`, the product of reflections over a pairwise-orthogonal `σ`-orbit acts
by `x - P.coroot' r x • P.orbitSum σ r` (reflection in the orbit sum). -/
theorem orthogonalProd_orbitIndices_smul_of_mem_fixedSubmodule (σ : P.Aut) {r : ι}
    (hr : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal)
    {x : M} (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    P.orthogonalProd (P.orbitIndices σ r) hr • x = x - P.coroot' r x • P.orbitSum σ r := by
  rw [orthogonalProd_smul, orbitSum_def, Finset.smul_sum]
  exact congrArg (x - ·) (Finset.sum_congr rfl fun j hj ↦ by
    rw [coroot'_eq_of_mem_orbitIndices hj hx])

section SimpleOrbit

variable (b : P.Base) (σ : P.Aut)

/-- Pairwise orthogonality of simple orbits at the orbit representative `i ∈ b.support` extends to
every pair of distinct elements of `P.orbitIndices σ i`. -/
theorem pairwise_isOrthogonal_orbitIndices_of_mem_support
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal :=
  P.pairwise_isOrthogonal_orbitIndices_of_pairing_eq_zero σ (horth i hi)

/-- **The commuting block reflection of a simple orbit.** For `i ∈ b.support`, the reflections in
the roots of `P.orbitIndices σ i` commute, and their product in `P.weylGroup` commutes with `σ`. -/
noncomputable def simpleOrbitWeyl
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) : P.weylGroup :=
  P.orthogonalProd (P.orbitIndices σ i)
    (P.pairwise_isOrthogonal_orbitIndices_of_mem_support b σ horth hi)

theorem simpleOrbitWeyl_def
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    P.simpleOrbitWeyl b σ horth hi =
      P.orthogonalProd (P.orbitIndices σ i)
        (P.pairwise_isOrthogonal_orbitIndices_of_mem_support b σ horth hi) := by
  rfl

theorem simpleOrbitWeyl_eq_of_mem
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i j : ι} (hi : i ∈ b.support) (hj : j ∈ b.support) (hmem : j ∈ P.orbitIndices σ i) :
    P.simpleOrbitWeyl b σ horth hj = P.simpleOrbitWeyl b σ horth hi := by
  rw [simpleOrbitWeyl_def, simpleOrbitWeyl_def, orthogonalProd_def, orthogonalProd_def]
  exact Finset.noncommProd_congr (orbitIndices_eq_of_mem hmem) (fun _ _ ↦ rfl) _

theorem simpleOrbitWeyl_smul
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) (x : M) :
    P.simpleOrbitWeyl b σ horth hi • x =
      x - ∑ j ∈ P.orbitIndices σ i, P.coroot' j x • P.root j :=
  P.orthogonalProd_smul _ _ x

@[simp]
theorem simpleOrbitWeyl_mul_self
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    P.simpleOrbitWeyl b σ horth hi * P.simpleOrbitWeyl b σ horth hi = 1 :=
  P.orthogonalProd_mul_self _ _

@[simp]
theorem simpleOrbitWeyl_inv
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    (P.simpleOrbitWeyl b σ horth hi)⁻¹ = P.simpleOrbitWeyl b σ horth hi :=
  P.orthogonalProd_inv _ _

theorem simpleOrbitWeyl_comm_aut
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    (P.simpleOrbitWeyl b σ horth hi : P.Aut) * σ =
      σ * (P.simpleOrbitWeyl b σ horth hi : P.Aut) :=
  P.orthogonalProd_orbitIndices_comm_aut σ _

/-- On any `σ`-fixed weight `x`, `simpleOrbitWeyl` acts as `x - P.coroot' i x • P.orbitSum σ i`
(reflection in the simple-orbit sum). -/
theorem simpleOrbitWeyl_smul_of_mem_fixedSubmodule
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) {x : M} (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    P.simpleOrbitWeyl b σ horth hi • x = x - P.coroot' i x • P.orbitSum σ i :=
  P.orthogonalProd_orbitIndices_smul_of_mem_fixedSubmodule σ _ hx

end SimpleOrbit

end SingleOrbit

/-! ### Per-orbit coroot, reflection, and Cartan formulas on any realization -/

namespace OrbitSumRealization

section Pairwise

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}

/-- In any orbit-sum realization over a characteristic-zero domain, for any single
pairwise-orthogonal orbit `P.orbitIndices σ r`, the folded coroot functional of `P.orbitSum σ r` is
the restriction of `P.coroot' r` to `LinearMap.fixedSubmodule σ.weightMap`. -/
theorem coroot_orbitSum_of_pairwise (F : P.OrbitSumRealization b σ) {r : ι}
    (hr : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal) :
    F.pairing.coroot ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ =
      (P.coroot' r).comp (LinearMap.fixedSubmodule σ.weightMap).subtype := by
  have : Module.IsReflexive R (LinearMap.fixedSubmodule σ.weightMap) :=
    .of_isPerfPair F.pairing.toLinearMap
  set u : P.foldedIndices σ := ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
  let g : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap) :=
    (P.coroot' r).comp (LinearMap.fixedSubmodule σ.weightMap).subtype
  have hf₁ : F.pairing.coroot u (F.pairing.root u) = 2 := by
    rw [← F.toLinearMap_apply]
    exact F.pairing.coroot_root_two u
  have hf₂ : MapsTo (Module.preReflection (F.pairing.root u) (F.pairing.coroot u))
      (range F.pairing.root) (range F.pairing.root) := by
    have heq_fn : ⇑(Module.preReflection (F.pairing.root u) (F.pairing.coroot u)) =
        ⇑(F.pairing.reflection u) := by
      ext x
      rw [Module.preReflection_apply, reflection_apply, F.coroot'_apply]
    rw [heq_fn]
    exact F.pairing.mapsTo_reflection_root u
  have hg₁ : g (F.pairing.root u) = 2 := by
    rw [LinearMap.comp_apply, Submodule.coe_subtype, F.coe_root]
    exact P.coroot'_orbitSum_self_of_pairwise σ hr
  have hg₂ : MapsTo (Module.preReflection (F.pairing.root u) g)
      (range F.pairing.root) (range F.pairing.root) := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨t, ht⟩ := mem_foldedIndices.mp v.2
    let w_r := P.orthogonalProd (P.orbitIndices σ r) hr
    have hcomm (z : ι) : (w_r : P.Aut).indexEquiv (σ.indexEquiv z) =
        σ.indexEquiv ((w_r : P.Aut).indexEquiv z) :=
      congrArg (fun q : P.Aut ↦ q.indexEquiv z) (P.orthogonalProd_orbitIndices_comm_aut σ hr)
    refine ⟨⟨P.orbitSum σ (P.weylGroupToPerm w_r t), P.orbitSum_mem_foldedIndices σ _⟩,
      Subtype.ext ?_⟩
    rw [F.coe_root, Module.preReflection_apply, Submodule.coe_sub, Submodule.coe_smul, F.coe_root,
      F.coe_root, LinearMap.comp_apply, Submodule.coe_subtype, F.coe_root, ← ht,
      ← P.orthogonalProd_orbitIndices_smul_of_mem_fixedSubmodule σ hr
        (P.orbitSum_mem_fixedSubmodule σ t)]
    exact (weightMap_orbitSum (w_r : P.Aut) hcomm t).symm
  exact Module.Dual.eq_of_preReflection_mapsTo (finite_range F.pairing.root)
    IsRootSystem.span_root_eq_top hf₁ hf₂ hg₁ hg₂

/-- In any orbit-sum realization over a characteristic-zero domain, for any single
pairwise-orthogonal orbit `P.orbitIndices σ r`, evaluating the folded coroot of `P.orbitSum σ r` on
a fixed weight `x` gives `P.coroot' r x`. -/
theorem coroot_orbitSum_apply_of_pairwise (F : P.OrbitSumRealization b σ) {r : ι}
    (hr : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ x =
      P.coroot' r (x : M) := by
  rw [F.coroot_orbitSum_of_pairwise hr, LinearMap.comp_apply, Submodule.coe_subtype]

/-- In any orbit-sum realization over a characteristic-zero domain, for any single
pairwise-orthogonal orbit `P.orbitIndices σ r`, `F.pairing.coroot'` at `P.orbitSum σ r` acts on
fixed weights as `P.coroot' r`. -/
theorem coroot'_orbitSum_of_pairwise (F : P.OrbitSumRealization b σ) {r : ι}
    (hr : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot' ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ x =
      P.coroot' r (x : M) := by
  rw [F.coroot'_apply, F.coroot_orbitSum_apply_of_pairwise hr]

/-- In any orbit-sum realization over a characteristic-zero domain, for any single
pairwise-orthogonal orbit `P.orbitIndices σ r`, the folded reflection in `P.orbitSum σ r` acts on
`LinearMap.fixedSubmodule σ.weightMap` as `P.orthogonalProd (P.orbitIndices σ r) hr`. -/
theorem coe_reflection_orbitSum_of_pairwise (F : P.OrbitSumRealization b σ) {r : ι}
    (hr : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (F.pairing.reflection ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ x : M) =
      P.orthogonalProd (P.orbitIndices σ r) hr • (x : M) := by
  rw [reflection_apply, Submodule.coe_sub, Submodule.coe_smul, F.coe_root,
    F.coroot'_orbitSum_of_pairwise hr x,
    P.orthogonalProd_orbitIndices_smul_of_mem_fixedSubmodule σ hr x.2]

/-- In any orbit-sum realization over a characteristic-zero domain, when the coroot orbit
`P.orbitIndices σ s` is pairwise orthogonal, pairing `P.orbitSum σ r` with the folded coroot of
`P.orbitSum σ s` equals `∑ k ∈ P.orbitIndices σ r, P.pairing k s`. -/
theorem pairing_orbitSum_of_pairwise (F : P.OrbitSumRealization b σ) (r : ι) {s : ι}
    (hs : (P.orbitIndices σ s : Set ι).Pairwise P.IsOrthogonal) :
    F.pairing.pairing ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
      ⟨P.orbitSum σ s, P.orbitSum_mem_foldedIndices σ s⟩ =
      ∑ k ∈ P.orbitIndices σ r, P.pairing k s := by
  rw [← root_coroot'_eq_pairing, F.coroot'_orbitSum_of_pairwise hs, F.root_orbitSum]
  simp only [orbitSum_def, map_sum, root_coroot'_eq_pairing]

/-- In any orbit-sum realization of a crystallographic root pairing over a characteristic-zero
domain, when the coroot orbit `P.orbitIndices σ s` is pairwise orthogonal, the folded integer Cartan
pairing of `P.orbitSum σ r` with `P.orbitSum σ s` equals
`∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k s`. -/
theorem pairingIn_orbitSum_of_pairwise [P.IsCrystallographic] (F : P.OrbitSumRealization b σ)
    (r : ι) {s : ι} (hs : (P.orbitIndices σ s : Set ι).Pairwise P.IsOrthogonal) :
    F.pairing.pairingIn ℤ ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
      ⟨P.orbitSum σ s, P.orbitSum_mem_foldedIndices σ s⟩ =
      ∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k s := by
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [algebraMap_pairingIn, F.pairing_orbitSum_of_pairwise r hs, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ (P.algebraMap_pairingIn ℤ k s).symm

end Pairwise

/-- In any orbit-sum realization over a characteristic-zero field `K`, when the coroot orbit
`P.orbitIndices σ s` is pairwise orthogonal, pairing `P.orbitSum σ r` with the folded coroot of
`P.orbitSum σ s` equals the double sum of `P.pairing k l` over both orbits divided by
`#(P.orbitIndices σ s)`. -/
theorem pairing_orbitSum_eq_div_of_pairwise {ι K M N : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    {P : RootPairing ι K M N} [Finite ι] {b : P.Base} {σ : P.Aut}
    (F : P.OrbitSumRealization b σ) (r : ι) {s : ι}
    (hs : (P.orbitIndices σ s : Set ι).Pairwise P.IsOrthogonal) :
    F.pairing.pairing ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
      ⟨P.orbitSum σ s, P.orbitSum_mem_foldedIndices σ s⟩ =
      (∑ k ∈ P.orbitIndices σ r, ∑ l ∈ P.orbitIndices σ s, P.pairing k l) /
        (#(P.orbitIndices σ s) : K) := by
  have hcard : (#(P.orbitIndices σ s) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (card_orbitIndices_pos P σ s).ne'
  rw [F.pairing_orbitSum_of_pairwise r hs, eq_div_iff hcard, Finset.sum_comm]
  have hconst (l : ι) (hl : l ∈ P.orbitIndices σ s) :
      ∑ k ∈ P.orbitIndices σ r, P.pairing k l = ∑ k ∈ P.orbitIndices σ r, P.pairing k s := by
    simp only [← root_coroot'_eq_pairing, ← map_sum, ← orbitSum_def]
    exact coroot'_eq_of_mem_orbitIndices hl (P.orbitSum_mem_fixedSubmodule σ r)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]

end OrbitSumRealization

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

private theorem simplyLacedForm_apply_orbitSum_self_of_pairwise
    (hsl : b.cartanMatrix.IsSimplyLaced)
    {r : ι} (hpair : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal) :
    (b.simplyLacedForm hsl).form (P.orbitSum σ r) (P.orbitSum σ r) =
      2 * (#(P.orbitIndices σ r) : R) := by
  rw [P.simplyLacedForm_apply_orbitSum_of_mem_fixedSubmodule b σ hsl
    (P.orbitSum_mem_fixedSubmodule σ r) r, P.coroot'_orbitSum_self_of_pairwise σ hpair, mul_comm]

end SimplyLacedOrbitForm

/-! ### Height descent and Stembridge's Claim 4 -/

section Ordered

private theorem aut_indexEquiv_comm {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} {g σ : P.Aut} (h : g * σ = σ * g) (z : ι) :
    g.indexEquiv (σ.indexEquiv z) = σ.indexEquiv (g.indexEquiv z) :=
  congrArg (fun q : P.Aut ↦ q.indexEquiv z) h

private theorem aut_inv_indexEquiv_comm {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} {g σ : P.Aut} (h : g * σ = σ * g) (z : ι) :
    (g⁻¹).indexEquiv (σ.indexEquiv z) = σ.indexEquiv ((g⁻¹).indexEquiv z) := by
  have hc : Commute g σ := h
  exact aut_indexEquiv_comm hc.inv_left.eq z

variable {ι K M N : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.IsRootSystem]
  (b : P.Base) (σ : P.Aut)

private theorem height_weylGroupToPerm_simpleOrbitWeyl
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) (r : ι) :
    (b.height (P.weylGroupToPerm (P.simpleOrbitWeyl b σ horth hi) r) : K) =
      (b.height r : K) - (b.simplyLacedForm hsl).form (P.root r) (P.orbitSum σ i) := by
  calc (b.height (P.weylGroupToPerm (P.simpleOrbitWeyl b σ horth hi) r) : K)
      = heightLinearMap P b
          (P.root r - ∑ j ∈ P.orbitIndices σ i, P.coroot' j (P.root r) • P.root j) := by
        rw [← heightLinearMap_root P b, ← P.weylGroup_apply_root, simpleOrbitWeyl_smul]
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

/-- **Height descent to a simple orbit.** When `P` is a simply laced root system over a linearly
ordered field and `σ` permutes `b.support` with pairwise-orthogonal simple orbits, every
`b`-positive root `r` is the image of some simple root `i ∈ b.support` under an element
`w : P.weylGroup` commuting with `σ`. -/
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
    · let w_i := P.simpleOrbitWeyl b σ horth hi
      set r' := P.weylGroupToPerm w_i r
      have hr'_pos : b.IsPos r' := P.isPos_weylGroupToPerm_orthogonalProd
        (P.pairwise_isOrthogonal_orbitIndices_of_mem_support b σ horth hi)
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
              rw [P.simpleOrbitWeyl_comm_aut b σ horth hi, Subgroup.coe_mul, mul_assoc]
      · rw [map_mul, Equiv.Perm.mul_apply, hw'i₀, ← Equiv.Perm.mul_apply, ← map_mul,
          P.simpleOrbitWeyl_mul_self b σ horth hi, map_one, Equiv.Perm.one_apply]

/-- **Stembridge's Claim 4.** When `P` is a simply laced root system over a linearly ordered field
and `σ` permutes `b.support` with pairwise-orthogonal simple orbits, **every** `σ`-orbit
`P.orbitIndices σ r` is pairwise orthogonal. -/
theorem pairwise_isOrthogonal_orbitIndices
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) :
    (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal := by
  have hpos_case {s : ι} (hs : b.IsPos s) :
      (P.orbitIndices σ s : Set ι).Pairwise P.IsOrthogonal := by
    obtain ⟨w, hw_comm, i, hi, hwi⟩ :=
      P.exists_weylGroup_comm_and_mem_support_of_isPos b σ hsl hσ horth hs
    have hwinv_comm (z : ι) : ((w⁻¹ : P.weylGroup) : P.Aut).indexEquiv (σ.indexEquiv z) =
        σ.indexEquiv (((w⁻¹ : P.weylGroup) : P.Aut).indexEquiv z) :=
      P.weylGroup.coe_inv w ▸ aut_inv_indexEquiv_comm hw_comm z
    have hws : ((w⁻¹ : P.weylGroup) : P.Aut).indexEquiv s = i := by
      rw [← weylGroupToPerm_apply, ← hwi, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Equiv.Perm.one_apply]
    have himg {k : ι} (hk : k ∈ P.orbitIndices σ s) :
        ((w⁻¹ : P.weylGroup) : P.Aut).indexEquiv k ∈ P.orbitIndices σ i := by
      rw [← hws, ← map_orbitIndices ((w⁻¹ : P.weylGroup) : P.Aut) hwinv_comm s]
      exact Finset.mem_map_of_mem _ hk
    intro j hj k hk hjk
    have horth_i := P.pairwise_isOrthogonal_orbitIndices_of_mem_support b σ horth hi
      (himg hj) (himg hk) (((w⁻¹ : P.weylGroup) : P.Aut).indexEquiv.injective.ne hjk)
    refine ⟨?_, ?_⟩
    · exact (((w⁻¹ : P.weylGroup) : P.Aut).toHom.pairing (i := j) (j := k)).symm.trans horth_i.1
    · exact (((w⁻¹ : P.weylGroup) : P.Aut).toHom.pairing (i := k) (j := j)).symm.trans horth_i.2
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
      rw [P.pairing_reflectionPerm_self_left, P.pairing_reflectionPerm_self_right, neg_neg]
    exact ⟨(hpair_neg j k).symm.trans horth_neg.1, (hpair_neg k j).symm.trans horth_neg.2⟩

/-- When `P` is a simply laced root system over a linearly ordered field and `σ` permutes
`b.support` with pairwise-orthogonal simple orbits, distinct roots in any `σ`-orbit have zero Cartan
pairing. -/
theorem pairing_eq_zero_of_mem_orbitIndices
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r j k : ι} (hj : j ∈ P.orbitIndices σ r) (hk : k ∈ P.orbitIndices σ r) (hjk : j ≠ k) :
    P.pairing j k = 0 :=
  (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth r hj hk hjk).1

/-- When `P` is a simply laced root system over a linearly ordered field and `σ` permutes
`b.support` with pairwise-orthogonal simple orbits, distinct roots in any `σ`-orbit have zero
integer Cartan pairing. -/
theorem pairingIn_eq_zero_of_mem_orbitIndices
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r j k : ι} (hj : j ∈ P.orbitIndices σ r) (hk : k ∈ P.orbitIndices σ r) (hjk : j ≠ k) :
    P.pairingIn ℤ j k = 0 := by
  apply FaithfulSMul.algebraMap_injective ℤ K
  rw [algebraMap_pairingIn, map_zero]
  exact P.pairing_eq_zero_of_mem_orbitIndices b σ hsl hσ horth hj hk hjk

/-- **Squared length of every orbit sum.** When `P` is a simply laced root system over a linearly
ordered field and `σ` permutes `b.support` with pairwise-orthogonal simple orbits, the squared
length of `P.orbitSum σ r` under `b.simplyLacedForm` is `2 * #(P.orbitIndices σ r)` for every root
`r`. -/
theorem simplyLacedForm_apply_orbitSum_self
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) :
    (b.simplyLacedForm hsl).form (P.orbitSum σ r) (P.orbitSum σ r) =
      2 * (#(P.orbitIndices σ r) : K) :=
  P.simplyLacedForm_apply_orbitSum_self_of_pairwise b σ hsl
    (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth r)

/-- **The commuting block reflection of an arbitrary root orbit**, when `P` is a simply laced root
system over a linearly ordered field and `σ` permutes `b.support` with pairwise-orthogonal simple
orbits. -/
noncomputable def orbitWeyl
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) : P.weylGroup :=
  P.orthogonalProd (P.orbitIndices σ r) (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth r)

theorem orbitWeyl_def
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) :
    P.orbitWeyl b σ hsl hσ horth r =
      P.orthogonalProd (P.orbitIndices σ r)
        (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth r) := by
  rfl

theorem orbitWeyl_eq_of_mem
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r j : ι} (hj : j ∈ P.orbitIndices σ r) :
    P.orbitWeyl b σ hsl hσ horth j = P.orbitWeyl b σ hsl hσ horth r := by
  rw [orbitWeyl_def, orbitWeyl_def, orthogonalProd_def, orthogonalProd_def]
  exact Finset.noncommProd_congr (orbitIndices_eq_of_mem hj) (fun _ _ ↦ rfl) _

@[simp]
theorem orbitWeyl_indexEquiv
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) :
    P.orbitWeyl b σ hsl hσ horth (σ.indexEquiv r) = P.orbitWeyl b σ hsl hσ horth r :=
  P.orbitWeyl_eq_of_mem b σ hsl hσ horth
    (indexEquiv_mem_orbitIndices_iff.mpr (self_mem_orbitIndices P σ r))

theorem orbitWeyl_eq_simpleOrbitWeyl
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {i : ι} (hi : i ∈ b.support) :
    P.orbitWeyl b σ hsl hσ horth i = P.simpleOrbitWeyl b σ horth hi := by
  rfl

theorem orbitWeyl_smul
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : M) :
    P.orbitWeyl b σ hsl hσ horth r • x =
      x - ∑ j ∈ P.orbitIndices σ r, P.coroot' j x • P.root j :=
  P.orthogonalProd_smul _ _ x

@[simp]
theorem orbitWeyl_mul_self
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) :
    P.orbitWeyl b σ hsl hσ horth r * P.orbitWeyl b σ hsl hσ horth r = 1 :=
  P.orthogonalProd_mul_self _ _

@[simp]
theorem orbitWeyl_inv
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) :
    (P.orbitWeyl b σ hsl hσ horth r)⁻¹ = P.orbitWeyl b σ hsl hσ horth r :=
  P.orthogonalProd_inv _ _

theorem orbitWeyl_comm_aut
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι) :
    (P.orbitWeyl b σ hsl hσ horth r : P.Aut) * σ =
      σ * (P.orbitWeyl b σ hsl hσ horth r : P.Aut) :=
  P.orthogonalProd_orbitIndices_comm_aut σ _

/-- On any `σ`-fixed weight `x`, `orbitWeyl` acts as `x - P.coroot' r x • P.orbitSum σ r`
(reflection in the orbit sum). -/
theorem orbitWeyl_smul_of_mem_fixedSubmodule
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι)
    {x : M} (hx : x ∈ LinearMap.fixedSubmodule σ.weightMap) :
    P.orbitWeyl b σ hsl hσ horth r • x = x - P.coroot' r x • P.orbitSum σ r :=
  P.orthogonalProd_orbitIndices_smul_of_mem_fixedSubmodule σ _ hx

/-! ### Reducedness of the orbit-sum system -/

private theorem root_mem_orbitIndices_of_sum_orthogonal
    (hsl : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s i : ι} (hi : i ∈ b.support) {a : ι → ℕ}
    (ha_supp : P.root s = ∑ m ∈ P.orbitIndices σ i, a m • P.root m) :
    s ∈ P.orbitIndices σ i := by
  classical
  have horth_i := P.pairwise_isOrthogonal_orbitIndices_of_mem_support b σ horth hi
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
  have hsq_cast : (∑ m ∈ P.orbitIndices σ i, (a m * a m : ℕ) : K) = 1 := by linarith
  have hsq : ∑ m ∈ P.orbitIndices σ i, a m * a m = 1 := by exact_mod_cast hsq_cast
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
    orbitSum_eq_of_mem (P.root_mem_orbitIndices_of_sum_orthogonal b σ hsl horth hi ha_supp)
  have hzero : (1 - c) • P.orbitSum σ i = 0 := by rw [sub_smul, one_smul, ← heq, horb_eq, sub_self]
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right (orbitSum_ne_zero hσ i))).symm

/-- **Proportional orbit sums differ by a sign.** When `P` is a simply laced root system over a
linearly ordered field and `σ` permutes `b.support` with pairwise-orthogonal simple orbits, if one
root-orbit sum is a `K`-scalar multiple of another, the scalar is `1` or `-1`. -/
theorem eq_one_or_neg_one_of_orbitSum_eq_smul
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r₁ r₂ : ι} {c : K} (heq : P.orbitSum σ r₂ = c • P.orbitSum σ r₁) :
    c = 1 ∨ c = -1 := by
  have hpos₁ {t₁ : ι} (ht₁ : b.IsPos t₁) (t₂ : ι) {c' : K}
      (hc' : P.orbitSum σ t₂ = c' • P.orbitSum σ t₁) : c' = 1 ∨ c' = -1 := by
    obtain ⟨w, hw_comm, i, hi, hwi⟩ :=
      P.exists_weylGroup_comm_and_mem_support_of_isPos b σ hsl hσ horth ht₁
    have hwinv_comm (z : ι) : ((w⁻¹ : P.weylGroup) : P.Aut).indexEquiv (σ.indexEquiv z) =
        σ.indexEquiv (((w⁻¹ : P.weylGroup) : P.Aut).indexEquiv z) :=
      P.weylGroup.coe_inv w ▸ aut_inv_indexEquiv_comm hw_comm z
    have htrans := congrArg ((w⁻¹ : P.weylGroup) : P.Aut).weightMap hc'
    rw [weightMap_orbitSum _ hwinv_comm, map_smul, weightMap_orbitSum _ hwinv_comm] at htrans
    have hwi' : ((w⁻¹ : P.weylGroup) : P.Aut).indexEquiv t₁ = i := by
      rw [← weylGroupToPerm_apply, ← hwi, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Equiv.Perm.one_apply]
    rw [hwi'] at htrans
    set s := ((w⁻¹ : P.weylGroup) : P.Aut).indexEquiv t₂
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

@[simp]
private theorem foldedCorootFun_apply (hsl : b.cartanMatrix.IsSimplyLaced)
    (u : P.foldedIndices σ) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.foldedCorootFun b σ hsl u x =
      (2 / (b.simplyLacedForm hsl).form (u : M) (u : M)) *
        (b.simplyLacedForm hsl).form (x : M) (u : M) :=
  rfl

private theorem foldedCorootFun_orbitSum_apply
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.foldedCorootFun b σ hsl ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ x =
      P.coroot' r (x : M) := by
  have hcard : (#(P.orbitIndices σ r) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (card_orbitIndices_pos P σ r).ne'
  rw [foldedCorootFun_apply, P.simplyLacedForm_apply_orbitSum_self b σ hsl hσ horth r,
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
    have hd_coe : (d : M) = c₁ • (u₁ : M) - c₂ • (u₂ : M) := by simp [d]
    have hd_eval : P.foldedCorootFun b σ hsl u₁ d - P.foldedCorootFun b σ hsl u₂ d = 0 := by
      rw [heq, sub_self]
    have hd_quad : B.form (d : M) (d : M) = 0 := by
      rw [foldedCorootFun_apply, foldedCorootFun_apply] at hd_eval
      calc B.form (d : M) (d : M)
          = B.form (c₁ • (u₁ : M) - c₂ • (u₂ : M)) (d : M) := by rw [← hd_coe]
        _ = c₁ * B.form (d : M) (u₁ : M) - c₂ * B.form (d : M) (u₂ : M) := by
            have hsymm (x y : M) : B.form x y = B.form y x := B.symm.eq x y
            rw [map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
              LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, hsymm (u₁ : M) (d : M),
              hsymm (u₂ : M) (d : M)]
        _ = 0 := hd_eval
    have hd_zero : (d : M) = 0 :=
      by_contra fun hne ↦ (b.posDef_simplyLacedForm hsl (d : M) hne).ne' hd_quad
    have hprop : (u₂ : M) = (c₁ / c₂) • (u₁ : M) := by
      have hsub : c₁ • (u₁ : M) = c₂ • (u₂ : M) := sub_eq_zero.mp (hd_coe ▸ hd_zero)
      rw [div_eq_inv_mul, mul_smul, hsub, inv_smul_smul₀ hc₂.ne']
    obtain ⟨r₁, hr₁⟩ := mem_foldedIndices.mp u₁.2
    obtain ⟨r₂, hr₂⟩ := mem_foldedIndices.mp u₂.2
    rw [← hr₁, ← hr₂] at hprop
    rcases P.eq_one_or_neg_one_of_orbitSum_eq_smul b σ hsl hσ horth hprop with hc_eq | hc_eq
    · rw [hc_eq, one_smul] at hprop
      exact Subtype.ext (hr₁.symm.trans (hprop.symm.trans hr₂))
    · exfalso; have := div_pos hc₁ hc₂; linarith

@[simp]
private theorem coe_foldedCorootEmb_apply
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (u : P.foldedIndices σ) :
    P.foldedCorootEmb b σ hsl hσ horth u = P.foldedCorootFun b σ hsl u :=
  rfl

private theorem foldedPair_self
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (u : P.foldedIndices σ) :
    Module.Dual.eval K (LinearMap.fixedSubmodule σ.weightMap)
      (P.foldedRootEmb σ u) (P.foldedCorootEmb b σ hsl hσ horth u) = 2 := by
  obtain ⟨r, hr⟩ := mem_foldedIndices.mp u.2
  have hu : u = ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ := Subtype.ext hr.symm
  subst hu
  rw [Module.Dual.eval_apply, coe_foldedCorootEmb_apply,
    P.foldedCorootFun_orbitSum_apply b σ hsl hσ horth r, coe_foldedRootEmb_apply]
  exact P.coroot'_orbitSum_self_of_pairwise σ
    (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth r)

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
  have hcomm := aut_indexEquiv_comm (P.orbitWeyl_comm_aut b σ hsl hσ horth r)
  refine ⟨⟨P.orbitSum σ (P.weylGroupToPerm w_r t), P.orbitSum_mem_foldedIndices σ _⟩,
    Subtype.ext ?_⟩
  rw [coe_foldedRootEmb_apply, Module.preReflection_apply, Submodule.coe_sub, Submodule.coe_smul,
    coe_foldedRootEmb_apply, coe_foldedRootEmb_apply, LinearMap.flip_apply, Module.Dual.eval_apply,
    coe_foldedCorootEmb_apply, P.foldedCorootFun_orbitSum_apply b σ hsl hσ horth r,
    coe_foldedRootEmb_apply, ← ht, ← P.orbitWeyl_smul_of_mem_fixedSubmodule b σ hsl hσ horth r
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
  rw [Module.Dual.eval_apply, coe_foldedCorootEmb_apply,
    P.foldedCorootFun_orbitSum_apply b σ hsl hσ horth t, coe_foldedRootEmb_apply, ← hr,
    orbitSum_def, map_sum, Int.cast_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by
    rw [root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ, algebraMap_int_eq, eq_intCast]

private noncomputable def foldedPairing
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    RootPairing (P.foldedIndices σ) K (LinearMap.fixedSubmodule σ.weightMap)
      (Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :=
  have : Module.Finite K (LinearMap.fixedSubmodule σ.weightMap) :=
    .of_basis (b.fixedSubmoduleBasis hσ)
  RootPairing.mk'' (Module.Dual.eval K (LinearMap.fixedSubmodule σ.weightMap))
    (P.foldedRootEmb σ) (P.foldedCorootEmb b σ hsl hσ horth)
    (P.foldedPair_self b σ hsl hσ horth) (P.foldedPreReflection_mapsTo b σ hsl hσ horth)
    (b.span_foldedRootEmb_eq_top hσ)

@[simp]
private theorem foldedPairing_root
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    (P.foldedPairing b σ hsl hσ horth).root = P.foldedRootEmb σ :=
  rfl

private instance isRootSystem_foldedPairing
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    (P.foldedPairing b σ hsl hσ horth).IsRootSystem := by
  have : Module.Finite K (LinearMap.fixedSubmodule σ.weightMap) :=
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
    rw [foldedPairing_root] at hdep ⊢
    have hu_ne : P.foldedRootEmb σ u ≠ 0 := fun h0 ↦
      have hu0 : (u : M) = 0 :=
        (P.coe_foldedRootEmb_apply σ u).symm.trans
          ((congrArg Subtype.val h0).trans Submodule.coe_zero)
      zero_notMem_foldedIndices hσ (hu0 ▸ u.2)
    rw [LinearIndependent.pair_iff' hu_ne, not_forall_not] at hdep
    obtain ⟨a, ha⟩ := hdep
    have hv_smul : (v : M) = a • (u : M) := by
      have hval := (congrArg Subtype.val ha).symm
      rwa [coe_foldedRootEmb_apply, Submodule.coe_smul, coe_foldedRootEmb_apply] at hval
    obtain ⟨r₁, hr₁⟩ := mem_foldedIndices.mp u.2
    obtain ⟨r₂, hr₂⟩ := mem_foldedIndices.mp v.2
    rw [← hr₁, ← hr₂] at hv_smul
    rcases P.eq_one_or_neg_one_of_orbitSum_eq_smul b σ hsl hσ horth hv_smul with rfl | rfl
    · exact Or.inl (by simpa using ha)
    · exact Or.inr (neg_eq_iff_eq_neg.mp ((neg_one_smul K _).symm.trans ha))

private noncomputable def foldedBase
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    (P.foldedPairing b σ hsl hσ horth).Base :=
  Base.mk' (P.foldedPairing b σ hsl hσ horth)
    {u : P.foldedIndices σ | ∃ j ∈ b.support, P.orbitSum σ j = (u : M)}
    (b.linearIndepOn_foldedRootEmb hσ) fun u ↦ by
      obtain ⟨r, hr⟩ := mem_foldedIndices.mp u.2
      have hu : u = ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ := Subtype.ext hr.symm
      subst hu
      rw [foldedPairing_root]
      by_cases hr_pos : b.IsPos r
      · exact Or.inl (b.foldedRootEmb_orbitSum_mem_closure_of_isPos hσ hr_pos)
      · right
        have hr_neg : b.IsPos (P.reflectionPerm r r) :=
          (isPos_reflectionPerm_self_iff_mem_negRoots P b r).mpr ((mem_negRoots P b r).mpr hr_pos)
        have hneg_eq : -(P.foldedRootEmb σ ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩) =
            P.foldedRootEmb σ
              ⟨P.orbitSum σ (P.reflectionPerm r r), P.orbitSum_mem_foldedIndices σ _⟩ := by
          apply Subtype.ext
          rw [Submodule.coe_neg, coe_foldedRootEmb_apply, coe_foldedRootEmb_apply, Subtype.coe_mk,
            Subtype.coe_mk, orbitSum_reflectionPerm_self]
        rw [hneg_eq]
        exact b.foldedRootEmb_orbitSum_mem_closure_of_isPos hσ hr_neg

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
  root_eq u := P.coe_foldedRootEmb_apply σ u
  base_eq u := by simp [foldedBase, Base.mk']

/-! ### Global coroot, reflection, and Cartan formulas on an orthogonal simply laced fold -/

namespace OrbitSumRealization

variable {P b σ}

/-- In any orbit-sum realization of an orthogonal simply laced fold over a linearly ordered field,
the folded coroot functional of `P.orbitSum σ r` is the restriction of `P.coroot' r` to
`LinearMap.fixedSubmodule σ.weightMap`. -/
theorem coroot_orbitSum (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι) :
    F.pairing.coroot ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ =
      (P.coroot' r).comp (LinearMap.fixedSubmodule σ.weightMap).subtype :=
  F.coroot_orbitSum_of_pairwise (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth r)

/-- In any orbit-sum realization of an orthogonal simply laced fold over a linearly ordered field,
evaluating the folded coroot of `P.orbitSum σ r` on a fixed weight `x` gives `P.coroot' r x`. -/
theorem coroot_orbitSum_apply (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ x =
      P.coroot' r (x : M) :=
  F.coroot_orbitSum_apply_of_pairwise (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth r) x

/-- In any orbit-sum realization of an orthogonal simply laced fold over a linearly ordered field,
`F.pairing.coroot'` at `P.orbitSum σ r` acts on fixed weights as `P.coroot' r`. -/
theorem coroot'_orbitSum (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot' ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ x =
      P.coroot' r (x : M) :=
  F.coroot'_orbitSum_of_pairwise (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth r) x

/-- In any orbit-sum realization of an orthogonal simply laced fold over a linearly ordered field,
the folded reflection in `P.orbitSum σ r` acts on `LinearMap.fixedSubmodule σ.weightMap` as the
commuting block reflection `P.orbitWeyl b σ hsl hσ horth r`. -/
theorem coe_reflection_orbitSum (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    (F.pairing.reflection ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩ x : M) =
      P.orbitWeyl b σ hsl hσ horth r • (x : M) := by
  rw [F.coe_reflection_orbitSum_of_pairwise
    (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth r) x, orbitWeyl_def]

/-- **Folded Cartan pairing formula.** In any orbit-sum realization of an orthogonal simply laced
fold over a linearly ordered field, pairing `P.orbitSum σ r` with the folded coroot of
`P.orbitSum σ s` sums `P.pairing k s` over `k ∈ P.orbitIndices σ r`. -/
theorem pairing_orbitSum (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r s : ι) :
    F.pairing.pairing ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
      ⟨P.orbitSum σ s, P.orbitSum_mem_foldedIndices σ s⟩ =
      ∑ k ∈ P.orbitIndices σ r, P.pairing k s :=
  F.pairing_orbitSum_of_pairwise r (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth s)

/-- **Folded integer Cartan pairing formula.** In any orbit-sum realization of an orthogonal simply
laced fold over a linearly ordered field, the folded integer Cartan pairing of `P.orbitSum σ r` with
`P.orbitSum σ s` equals `∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k s`. -/
theorem pairingIn_orbitSum (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r s : ι) :
    F.pairing.pairingIn ℤ ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
      ⟨P.orbitSum σ s, P.orbitSum_mem_foldedIndices σ s⟩ =
      ∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k s :=
  F.pairingIn_orbitSum_of_pairwise r (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth s)

/-- **Stembridge's oriented Cartan formula (equation (3)).** In any orbit-sum realization of an
orthogonal simply laced fold over a linearly ordered field, the folded pairing of `P.orbitSum σ r`
with the folded coroot of `P.orbitSum σ s` equals the double sum of `P.pairing k l` over both orbits
divided by `#(P.orbitIndices σ s)` (the size of the coroot orbit `s`). -/
theorem pairing_orbitSum_eq_div (F : P.OrbitSumRealization b σ)
    (hsl : b.cartanMatrix.IsSimplyLaced) (hσ : ∀ k ∈ b.support, σ.indexEquiv k ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r s : ι) :
    F.pairing.pairing ⟨P.orbitSum σ r, P.orbitSum_mem_foldedIndices σ r⟩
      ⟨P.orbitSum σ s, P.orbitSum_mem_foldedIndices σ s⟩ =
      (∑ k ∈ P.orbitIndices σ r, ∑ l ∈ P.orbitIndices σ s, P.pairing k l) /
        (#(P.orbitIndices σ s) : K) :=
  F.pairing_orbitSum_eq_div_of_pairwise r (P.pairwise_isOrthogonal_orbitIndices b σ hsl hσ horth s)

end OrbitSumRealization

end Ordered

end RootPairing
