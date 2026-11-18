/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Folding.Realization
public import TauCeti.LinearAlgebra.RootSystem.InvariantForm.SimplyLaced
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.Data.Finset.NoncommProd
import TauCeti.Data.Int.SumSquares
import TauCeti.GroupTheory.Perm.Basic
import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport

/-!
# The orthogonal orbit-sum fold of a simply-laced root system

Let `P` be a finite reduced crystallographic root pairing, `b` a base of `P` whose Cartan matrix is
simply laced, and `σ` an automorphism of `P` permuting the simple roots of `b` such that distinct
simple roots in each `σ`-orbit are pairwise orthogonal. Following Stembridge (*Folding by
automorphisms*, 2008), this file propagates pairwise orthogonality from the simple `σ`-orbits to all
root `σ`-orbits over any characteristic-zero domain, constructs the folded root system
`RootPairing.orthogonalFold` as an `OrbitSumRealization` over any characteristic-zero field, and
establishes the coroot, Cartan, and reflection formulas for pairwise-orthogonal orbits on any
`OrbitSumRealization`:

* **Commuting block reflections** (`RootPairing.orbitReflection`): when the reflections of a
  `σ`-orbit pairwise commute in `P.weylGroup`, their commuting product in `P.weylGroup` is an
  involution commuting with `σ`; when the orbit is pairwise orthogonal, it acts on `σ`-fixed weights
  `x` as `x - P.coroot' i x • P.orbitSum σ i`.
* **Height descent and Stembridge's Claim 4** (`RootPairing.pairing_eq_zero_of_mem_orbitIndices`,
  `RootPairing.pairwise_isOrthogonal_orbitIndices`): over any characteristic-zero domain, positive
  height descent under the simple block reflections moves every root into `b.support`, transporting
  pairwise orthogonality from the simple `σ`-orbits to *every* root `σ`-orbit. Over a
  characteristic-zero field, each orbit sum `P.orbitSum σ r` has squared norm
  `2 * #(P.orbitIndices σ r)` under `P.simplyLacedForm`
  (`RootPairing.simplyLacedForm_orbitSum_self`), and two indices have the same orbit sum if and only
  if they lie in the same `σ`-orbit (`RootPairing.foldedIndex_eq_iff_mem_orbitIndices`).
* **The orthogonal fold** (`RootPairing.orthogonalFold`): over any characteristic-zero field `K`,
  the unique `P.OrbitSumRealization b σ`, together with the formulas valid on *any*
  `F : P.OrbitSumRealization b σ` for pairwise-orthogonal orbits:
  - `F.coroot'_foldedIndex_apply`: `F.pairing.coroot' (P.foldedIndex σ r) x = P.coroot' r x`;
  - `F.pairingIn_foldedIndex`: the folded Cartan pairing is `∑ k ∈ P.orbitIndices σ r, ⟨αₖ, αₜ^∨⟩`;
  - `F.card_orbitIndices_mul_pairingIn_foldedIndex` and `F.pairing_foldedIndex_eq_neg_card_div`:
    for distinct simple orbits `O, T`, `⟨βₒ, βₜ^∨⟩ = -N_{O, T} / |T|` where `N_{O, T}` counts
    non-orthogonal pairs between `O` and `T` (with `|T|`, not `|O|`, in the denominator);
  - `F.coe_reflection_foldedIndex`: reflection in `P.foldedIndex σ r` restricts
    `P.orbitReflection σ r` to the fixed submodule.

## Main definitions

* `RootPairing.orbitReflection`: the commuting product of reflections over a `σ`-orbit in
  `P.weylGroup`.
* `RootPairing.orthogonalFold`: the `OrbitSumRealization` of an orthogonal diagram fold over a
  characteristic-zero field.

## Main results

* `RootPairing.commute_coe_orbitReflection` and `RootPairing.orbitReflection_smul_of_fixed`: block
  reflections commute with `σ` and act as rank-one reflections along orbit sums on fixed weights.
* `RootPairing.pairing_eq_zero_of_mem_orbitIndices` and
  `RootPairing.pairwise_isOrthogonal_orbitIndices`: every root `σ`-orbit is pairwise orthogonal
  (Stembridge, Claim 4).
* `RootPairing.simplyLacedForm_orbitSum_self`: `(βₒ, βₒ) = 2 * |O|`.
* `RootPairing.OrbitSumRealization.coroot'_foldedIndex_apply`,
  `RootPairing.OrbitSumRealization.pairing_foldedIndex_eq_neg_card_div`, and
  `RootPairing.OrbitSumRealization.coe_reflection_foldedIndex`: coroot, oriented Cartan, and
  reflection comparisons for pairwise-orthogonal orbits on any `OrbitSumRealization`.

## References

* J. R. Stembridge, *Folding by automorphisms*, note of 20 August 2008, equations (1)--(3) and
  Claims 1 and 4, pages 1--3.
-/

public section

namespace RootPairing

open Finset Function Set Submodule TauCeti

/-! ### Commuting block reflections -/

section OrbitReflection

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι]

/-- The **orbit reflection** attached to `i : ι` under `σ`: when the reflections of
`P.orbitIndices σ i` pairwise commute in `P.weylGroup`, this is their commuting product in
`P.weylGroup` (and `1` otherwise). -/
noncomputable def orbitReflection (σ : P.Aut) (i : ι) : P.weylGroup := by
  classical
  exact if h : (P.orbitIndices σ i : Set ι).Pairwise (Commute on weylGroup.ofIdx P) then
    (P.orbitIndices σ i).noncommProd (weylGroup.ofIdx P) h
  else 1

variable {P} in
theorem orbitReflection_eq_of_mem {σ : P.Aut} {i j : ι} (h : j ∈ P.orbitIndices σ i) :
    P.orbitReflection σ j = P.orbitReflection σ i := by
  simp only [orbitReflection]
  rw [P.orbitIndices_eq_of_mem h]

@[simp]
theorem orbitReflection_indexEquiv (σ : P.Aut) (i : ι) :
    P.orbitReflection σ (σ.indexEquiv i) = P.orbitReflection σ i :=
  P.orbitReflection_eq_of_mem (P.indexEquiv_mem_orbitIndices_iff.mpr (P.self_mem_orbitIndices σ i))

@[simp]
theorem orbitReflection_one (i : ι) : P.orbitReflection 1 i = weylGroup.ofIdx P i := by
  have hcomm : (({i} : Finset ι) : Set ι).Pairwise (Commute on weylGroup.ofIdx P) := by
    norm_cast
    exact Set.pairwise_singleton _ _
  simp only [orbitReflection, P.orbitIndices_one, hcomm, ↓reduceDIte, Finset.noncommProd_singleton]

variable {P} in
/-- When the reflections of `P.orbitIndices σ i` pairwise commute in `P.weylGroup`,
`P.orbitReflection σ i` is their commuting product. -/
theorem orbitReflection_eq_noncommProd {σ : P.Aut} {i : ι}
    (hcomm : (P.orbitIndices σ i : Set ι).Pairwise (Commute on weylGroup.ofIdx P)) :
    P.orbitReflection σ i = (P.orbitIndices σ i).noncommProd (weylGroup.ofIdx P) hcomm := by
  classical
  simp only [orbitReflection, hcomm, ↓reduceDIte]

variable {P} in
/-- When the reflections of `P.orbitIndices σ i` do not pairwise commute in `P.weylGroup`,
`P.orbitReflection σ i` defaults to `1`. -/
theorem orbitReflection_eq_one_of_not_pairwise_commute {σ : P.Aut} {i : ι}
    (hcomm : ¬ (P.orbitIndices σ i : Set ι).Pairwise (Commute on weylGroup.ofIdx P)) :
    P.orbitReflection σ i = 1 := by
  classical
  simp only [orbitReflection, hcomm, ↓reduceDIte]

/-- Every orbit reflection has order dividing `2` in `P.weylGroup`. -/
@[simp]
theorem orbitReflection_mul_self (σ : P.Aut) (i : ι) :
    P.orbitReflection σ i * P.orbitReflection σ i = 1 := by
  by_cases hcomm : (P.orbitIndices σ i : Set ι).Pairwise (Commute on weylGroup.ofIdx P)
  · rw [P.orbitReflection_eq_noncommProd hcomm]
    exact weylGroup.noncommProd_ofIdx_mul_self P hcomm
  · rw [P.orbitReflection_eq_one_of_not_pairwise_commute hcomm, mul_one]

@[simp]
theorem orbitReflection_inv (σ : P.Aut) (i : ι) :
    (P.orbitReflection σ i)⁻¹ = P.orbitReflection σ i :=
  inv_eq_iff_mul_eq_one.mpr (P.orbitReflection_mul_self σ i)

/-- **Block reflections commute with `σ`.** Conjugating `P.orbitReflection σ i` by `σ` permutes its
commuting reflection factors along `σ.indexEquiv`, leaving the product unchanged. -/
theorem commute_coe_orbitReflection (σ : P.Aut) (i : ι) :
    Commute (P.orbitReflection σ i : P.Aut) σ := by
  by_cases hcomm : (P.orbitIndices σ i : Set ι).Pairwise (Commute on weylGroup.ofIdx P)
  · have hfix : σ.weylGroupEquiv (P.orbitReflection σ i) = P.orbitReflection σ i := by
      rw [P.orbitReflection_eq_noncommProd hcomm, Finset.map_noncommProd]
      have hmap : (P.orbitIndices σ i).map σ.indexEquiv.toEmbedding = P.orbitIndices σ i :=
        (P.map_orbitIndices σ (fun _ ↦ rfl) i).trans (P.orbitIndices_indexEquiv σ i)
      have hcomm' :
          (((P.orbitIndices σ i).map σ.indexEquiv.toEmbedding : Finset ι) : Set ι).Pairwise
            (Commute on weylGroup.ofIdx P) := by
        rw [hmap]
        exact hcomm
      refine (Finset.noncommProd_congr rfl
        (fun j _ ↦ σ.weylGroupEquiv_ofIdx j) _).trans ?_
      exact (Finset.noncommProd_map (P.orbitIndices σ i) σ.indexEquiv.toEmbedding
        (weylGroup.ofIdx P) hcomm').symm.trans (Finset.noncommProd_congr hmap (fun _ _ ↦ rfl) _)
    have haut : σ * (P.orbitReflection σ i : P.Aut) * σ⁻¹ = (P.orbitReflection σ i : P.Aut) := by
      have hcoe := congrArg (Subtype.val : P.weylGroup → P.Aut) hfix
      rw [Equiv.coe_weylGroupEquiv, Equiv.autCongr_apply] at hcoe
      exact mul_assoc σ (P.orbitReflection σ i : P.Aut) σ⁻¹ ▸ hcoe
    exact Commute.symm (mul_inv_eq_iff_eq_mul.mp haut)
  · rw [P.orbitReflection_eq_one_of_not_pairwise_commute hcomm, Subgroup.coe_one]
    exact Commute.one_left σ

section OrthogonalOrbit

variable {P} {σ : P.Aut} {i : ι}

/-- Action of `P.orbitReflection σ i` on any ambient weight `x : M`. -/
theorem orbitReflection_smul (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal)
    (x : M) :
    P.orbitReflection σ i • x = x - ∑ j ∈ P.orbitIndices σ i, P.coroot' j x • P.root j := by
  rw [P.orbitReflection_eq_noncommProd (weylGroup.pairwise_commute_ofIdx_of_isOrthogonal P horth),
    weylGroup.noncommProd_ofIdx_smul P horth]

/-- **Action of `P.orbitReflection σ i` on `σ`-fixed weights.** On `E^σ`, the commuting block
reflection acts as the rank-one reflection subtracting `P.coroot' i x • P.orbitSum σ i`. -/
theorem orbitReflection_smul_of_fixed (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal)
    {x : M} (hx : σ.weightMap x = x) :
    P.orbitReflection σ i • x = x - P.coroot' i x • P.orbitSum σ i := by
  rw [P.orbitReflection_smul horth, P.orbitSum_def, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j hj ↦ by rw [P.coroot'_eq_of_mem_orbitIndices_of_fixed hx hj]

/-- `P.orbitReflection σ i` negates every root in `P.orbitIndices σ i`. -/
theorem weylGroupToPerm_orbitReflection_of_mem
    (horth : (P.orbitIndices σ i : Set ι).Pairwise P.IsOrthogonal)
    {j : ι} (hj : j ∈ P.orbitIndices σ i) :
    P.weylGroupToPerm (P.orbitReflection σ i) j = P.reflectionPerm j j := by
  classical
  apply P.root.injective
  rw [← P.weylGroup_apply_root, P.orbitReflection_smul horth, Finset.sum_eq_single j,
    root_coroot'_eq_pairing, pairing_same, root_reflectionPerm, reflection_apply_self]
  · abel_nf
    rw [two_smul]
    abel
  · intro k hk hne
    rw [root_coroot'_eq_pairing, (horth hj hk hne.symm).1, zero_smul]
  · exact fun h ↦ (h hj).elim

/-- Any element `w : P.weylGroup` commuting with `σ` permutes `σ`-orbits via
`P.weylGroupToPerm w`. -/
theorem map_orbitIndices_of_commute {w : P.weylGroup} (hw : Commute (w : P.Aut) σ) (r : ι) :
    (P.orbitIndices σ r).map (P.weylGroupToPerm w).toEmbedding =
      P.orbitIndices σ (P.weylGroupToPerm w r) := by
  have hperm : P.weylGroupToPerm w = (w : P.Aut).indexEquiv :=
    _root_.Equiv.Perm.ext (P.weylGroupToPerm_apply w)
  rw [hperm]
  exact P.map_orbitIndices (w : P.Aut) (Equiv.indexEquiv_commute hw) r

/-- Any element `w : P.weylGroup` commuting with `σ` carries `P.orbitSum σ r` to
`P.orbitSum σ (P.weylGroupToPerm w r)`. -/
theorem smul_orbitSum_of_commute {w : P.weylGroup} (hw : Commute (w : P.Aut) σ) (r : ι) :
    w • P.orbitSum σ r = P.orbitSum σ (P.weylGroupToPerm w r) := by
  rw [Subgroup.smul_def, Equiv.smul_weight_eq_weightMap, P.weylGroupToPerm_apply]
  exact P.weightMap_orbitSum (w : P.Aut) (Equiv.indexEquiv_commute hw) r

end OrthogonalOrbit

end OrbitReflection

/-! ### Height descent and Stembridge's Claim 4 -/

section SimpleOrbitOrthogonal

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}

/-- Under the simple-orbit orthogonality hypothesis, the `σ`-orbit of any simple root is pairwise
`P.IsOrthogonal`. -/
theorem pairwise_isOrthogonal_orbitIndices_of_mem_support
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s : ι} (hs : s ∈ b.support) :
    (P.orbitIndices σ s : Set ι).Pairwise P.IsOrthogonal := by
  intro j hj k hk hne
  have hj' : j ∈ b.support := P.mem_support_of_mem_orbitIndices hσ hs hj
  have hk' : k ∈ P.orbitIndices σ j := (P.orbitIndices_eq_of_mem hj).symm ▸ hk
  have hp : P.pairing j k = 0 := horth j hj' k hk' hne
  exact ⟨hp, P.pairing_eq_zero_iff'.mp hp⟩

end SimpleOrbitOrthogonal

section Descent

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [P.IsReduced] [P.IsCrystallographic]
  {b : P.Base} {σ : P.Aut}

omit [CharZero R] [IsDomain R] [P.IsReduced] [P.IsCrystallographic] in
/-- Every element of `Subgroup.closure (P.orbitReflection σ '' b.support)` commutes with `σ`. -/
private theorem commute_of_mem_closure_orbitReflection
    {w : P.weylGroup} (hw : w ∈ Subgroup.closure (P.orbitReflection σ '' (b.support : Set ι))) :
    Commute (w : P.Aut) σ := by
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, -, rfl⟩ := hg
    exact P.commute_coe_orbitReflection σ s
  | one => simp
  | mul _ _ _ _ ih₁ ih₂ => exact ih₁.mul_left ih₂
  | inv _ _ ih => exact ih.inv_left

omit [P.IsReduced] in
/-- Every positive orbit sum pairs positively in `ℤ` with at least one simple coroot. -/
private theorem exists_mem_support_sum_pairingIn_pos
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support) {q : ι} (hq : b.IsPos q) :
    ∃ s ∈ b.support, 0 < ∑ j ∈ P.orbitIndices σ q, P.pairingIn ℤ j s := by
  let _ := Fintype.ofFinite ι
  let B := P.posRootForm ℤ
  obtain ⟨f, hf⟩ := (mem_posRootCone P b).mp (P.orbitSum_mem_posRootCone hσ hq)
  set c : b.support → ℤ := fun k ↦ f k
  have hc : ¬ c ≤ 0 := fun hle ↦ P.orbitSum_ne_zero hσ q <| by
    rw [hf]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hk0 : (f k : ℤ) ≤ 0 := hle ⟨k, hk⟩
    have hfk : f k = 0 := by omega
    rw [hfk, zero_smul]
  obtain ⟨s, -, hsp⟩ := B.posForm.exists_pos_and_pos_apply_sum_smul
    (v := fun k : b.support ↦ P.rootSpanMem ℤ k)
    (fun _ ↦ P.posRootForm_posForm_pos_of_ne_zero ℤ)
    (.of_comp (P.rootSpan ℤ).subtype (b.linearIndepOn_root.restrict_scalars' ℤ))
    (fun k l hkl ↦ (B.posForm_apply_root_root_le_zero_iff k l).mpr <|
      b.pairingIn_le_zero_of_ne (Subtype.coe_ne_coe.mpr hkl) k.2 l.2)
    hc
  have hspan_eq : ∑ l : b.support, c l • P.rootSpanMem ℤ l =
      ∑ j ∈ P.orbitIndices σ q, P.rootSpanMem ℤ j := by
    apply Subtype.ext
    push_cast
    rw [Finset.sum_coe_sort b.support (fun k ↦ (f k : ℤ) • P.root k)]
    simpa only [c, P.orbitSum_def, natCast_zsmul] using hf.symm
  rw [hspan_eq, map_sum, LinearMap.sum_apply] at hsp
  have h2pos : 0 < 2 * ∑ j ∈ P.orbitIndices σ q,
      B.posForm (P.rootSpanMem ℤ j) (P.rootSpanMem ℤ s) := by omega
  have hform (j : ι) : 2 * B.posForm (P.rootSpanMem ℤ j) (P.rootSpanMem ℤ s) =
      P.pairingIn ℤ j s * B.rootLength s := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    simp only [map_mul, map_ofNat, RootPositiveForm.algebraMap_posForm, algebraMap_pairingIn,
      RootPositiveForm.algebraMap_rootLength]
    exact B.two_mul_apply_root_root j s
  rw [Finset.mul_sum, Finset.sum_congr rfl fun j _ ↦ hform j, ← Finset.sum_mul] at h2pos
  refine ⟨s, s.2, ?_⟩
  exact pos_of_mul_pos_left h2pos (B.rootLength_pos s).le

/-- If a root `r` is a natural combination of the roots in an orthogonal simple orbit
`P.orbitIndices σ s`, then `r` belongs to `P.orbitIndices σ s`. -/
private theorem mem_orbitIndices_of_root_eq_sum
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s r : ι} (hs : s ∈ b.support) {f : ι → ℕ}
    (hsub : P.root r = ∑ k ∈ P.orbitIndices σ s, f k • P.root k) :
    r ∈ P.orbitIndices σ s := by
  classical
  let _ := Fintype.ofFinite ι
  let B := (P.posRootForm ℤ).toInvariantForm
  have horth_s := P.pairwise_isOrthogonal_orbitIndices_of_mem_support hσ horth hs
  have hsubZ : P.root r = ∑ k ∈ P.orbitIndices σ s, (f k : ℤ) • P.root k := by
    simpa only [natCast_zsmul] using hsub
  have hpair (k : ι) (hk : k ∈ P.orbitIndices σ s) :
      P.pairingIn ℤ r k = 2 * (f k : ℤ) := by
    rw [P.pairingIn_eq_sum_of_root_eq_sum hsubZ k, Finset.sum_eq_single k]
    · rw [pairingIn_same, mul_comm]
    · intro l hl hlk
      have hl0 : P.pairingIn ℤ l k = 0 := by
        apply FaithfulSMul.algebraMap_injective ℤ R
        rw [P.algebraMap_pairingIn ℤ, (horth_s hl hk hlk).1, map_zero]
      rw [hl0, mul_zero]
    · exact fun h ↦ (h hk).elim
  have hcomp (k : ι) (hk : k ∈ P.orbitIndices σ s) (hfk : f k ≠ 0) :
      P.componentOf k = P.componentOf r := by
    by_cases hrk : k = r
    · rw [hrk]
    · refine SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable ?_)
      rw [P.nonorthogonalGraph_adj]
      refine ⟨hrk, fun ho ↦ ?_⟩
      have hp0 : P.pairingIn ℤ r k = 0 := by
        apply FaithfulSMul.algebraMap_injective ℤ R
        rw [P.algebraMap_pairingIn ℤ, ho.2, map_zero]
      have := hpair k hk
      omega
  have hlen (k : ι) (hk : k ∈ P.orbitIndices σ s) :
      (f k ^ 2 : ℕ) • B.form (P.root k) (P.root k) =
        (f k ^ 2 : ℕ) • B.form (P.root r) (P.root r) := by
    by_cases hfk : f k = 0
    · simp [hfk]
    · rw [B.apply_root_root_eq_of_componentOf_eq b hsimply (hcomp k hk hfk)]
  have hnorm : B.form (P.root r) (P.root r) =
      (∑ k ∈ P.orbitIndices σ s, f k ^ 2) • B.form (P.root r) (P.root r) := by
    calc B.form (P.root r) (P.root r)
        = B.form (∑ k ∈ P.orbitIndices σ s, f k • P.root k)
            (∑ l ∈ P.orbitIndices σ s, f l • P.root l) := by rw [← hsub]
      _ = ∑ k ∈ P.orbitIndices σ s, (f k ^ 2 : ℕ) • B.form (P.root k) (P.root k) := by
          simp only [map_sum, map_nsmul, LinearMap.sum_apply, LinearMap.smul_apply]
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          rw [Finset.sum_eq_single k]
          · rw [smul_smul, sq]
          · intro l hl hlk
            rw [(B.apply_root_root_zero_iff l k).mpr (horth_s hl hk hlk).1, smul_zero]
          · exact fun h ↦ (h hk).elim
      _ = ∑ k ∈ P.orbitIndices σ s, (f k ^ 2 : ℕ) • B.form (P.root r) (P.root r) :=
          Finset.sum_congr rfl hlen
      _ = (∑ k ∈ P.orbitIndices σ s, f k ^ 2) • B.form (P.root r) (P.root r) := by
          rw [← Finset.sum_smul]
  have hsqZ : ∑ k : P.orbitIndices σ s, (f k : ℤ) ^ 2 = 1 := by
    have hcast : (((∑ k ∈ P.orbitIndices σ s, f k ^ 2 : ℕ) : R) - 1) *
        B.form (P.root r) (P.root r) = 0 := by
      rw [sub_mul, one_mul, ← nsmul_eq_mul, ← hnorm, sub_self]
    have h1 : ((∑ k ∈ P.orbitIndices σ s, f k ^ 2 : ℕ) : R) = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hcast).resolve_right (B.ne_zero r))
    have hnat : ∑ k ∈ P.orbitIndices σ s, f k ^ 2 = 1 := by exact_mod_cast h1
    rw [Finset.sum_coe_sort (P.orbitIndices σ s) (fun k ↦ (f k : ℤ) ^ 2)]
    exact_mod_cast hnat
  obtain ⟨k₀, hk₀⟩ := sum_sq_eq_one_iff.mp hsqZ
  have hk₀_one : f k₀ = 1 ∧ ∀ k : P.orbitIndices σ s, k ≠ k₀ → f k = 0 := by
    rcases hk₀ with hk₀ | hk₀
    · refine ⟨?_, fun k hne ↦ ?_⟩
      · have := congrFun hk₀ k₀; simp at this; omega
      · have := congrFun hk₀ k; simp [hne] at this; omega
    · exfalso
      have := congrFun hk₀ k₀
      simp at this
  have hroot : P.root r = P.root k₀ := by
    rw [hsub, ← Finset.sum_coe_sort (P.orbitIndices σ s), Finset.sum_eq_single k₀,
      hk₀_one.1, one_smul]
    · exact fun k _ hne ↦ by rw [hk₀_one.2 k hne, zero_smul]
    · exact fun h ↦ (h (Finset.mem_univ k₀)).elim
  exact P.root.injective hroot ▸ k₀.2

/-- **Height descent step.** Applying a simple block reflection `P.orbitReflection σ s` with
`0 < ∑ j ∈ P.orbitIndices σ r, P.pairingIn ℤ j s` to a positive root `r` either witnesses
`r ∈ P.orbitIndices σ s` or produces a positive root of strictly smaller height. -/
private theorem mem_orbitIndices_or_height_lt
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {s r : ι} (hs : s ∈ b.support) (hr : b.IsPos r)
    (hpos : 0 < ∑ j ∈ P.orbitIndices σ r, P.pairingIn ℤ j s) :
    r ∈ P.orbitIndices σ s ∨
      (b.IsPos (P.weylGroupToPerm (P.orbitReflection σ s) r) ∧
        b.height (P.weylGroupToPerm (P.orbitReflection σ s) r) < b.height r) := by
  classical
  have horth_s := P.pairwise_isOrthogonal_orbitIndices_of_mem_support hσ horth hs
  have hcomm_s := P.commute_coe_orbitReflection σ s
  set r' := P.weylGroupToPerm (P.orbitReflection σ s) r
  set z : ℤ := ∑ j ∈ P.orbitIndices σ r, P.pairingIn ℤ j s
  by_cases hr' : b.IsPos r'
  · right
    refine ⟨hr', ?_⟩
    have hz : (z : R) = P.coroot' s (P.orbitSum σ r) := by
      rw [P.orbitSum_def, map_sum, Int.cast_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by
        simpa [root_coroot'_eq_pairing] using P.algebraMap_pairingIn ℤ j s
    have horb : P.orbitSum σ r = P.orbitSum σ r' + z • P.orbitSum σ s := by
      have hsub : P.orbitSum σ r' = P.orbitSum σ r - z • P.orbitSum σ s := by
        rw [← P.smul_orbitSum_of_commute hcomm_s r,
          P.orbitReflection_smul_of_fixed horth_s (P.weightMap_orbitSum_self σ r), ← hz,
          Int.cast_smul_eq_zsmul]
      rw [hsub, sub_add_cancel]
    let U := P.orbitIndices σ r' ∪ P.orbitIndices σ s
    have hrel : ∑ j ∈ P.orbitIndices σ r, (1 : ℤ) • P.root j =
        ∑ j ∈ U, ((if j ∈ P.orbitIndices σ r' then (1 : ℤ) else 0) +
          (if j ∈ P.orbitIndices σ s then z else 0)) • P.root j := by
      simp_rw [add_smul, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
        Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, ← Finset.smul_sum,
        ← P.orbitSum_def, ← P.orbitSum_def, ← P.orbitSum_def, horb]
    have hht := sum_mul_height_eq_of_sum_zsmul_root_eq P b hrel
    simp_rw [add_mul, ite_mul, one_mul, zero_mul] at hht
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right,
      Finset.sum_congr rfl fun j hj ↦ P.height_eq_of_mem_orbitIndices hσ hj,
      Finset.sum_congr rfl fun j hj ↦ P.height_eq_of_mem_orbitIndices hσ hj,
      Finset.sum_congr rfl fun j hj ↦
        congrArg (z * ·) ((P.height_eq_of_mem_orbitIndices hσ hj).trans
          (b.height_eq_one_iff.mpr hs)),
      mul_one, Finset.sum_const, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul] at hht
    have hcard : #(P.orbitIndices σ r') = #(P.orbitIndices σ r) := by
      rw [← P.map_orbitIndices_of_commute hcomm_s r, Finset.card_map]
    rw [hcard] at hht
    have : 0 < (#(P.orbitIndices σ r) : ℤ) :=
      Int.natCast_pos.mpr (P.card_orbitIndices_pos σ r)
    have : 0 < (#(P.orbitIndices σ s) : ℤ) :=
      Int.natCast_pos.mpr (P.card_orbitIndices_pos σ s)
    nlinarith
  · left
    obtain ⟨f, -, hf⟩ := exists_root_eq_sum_nat_of_mem_posRoots P b ((mem_posRoots P b r).mpr hr)
    obtain ⟨g, -, hg⟩ := exists_root_eq_sum_nat_of_mem_posRoots P b ((mem_posRoots P b _).mpr
      ((isPos_reflectionPerm_self_iff_mem_negRoots P b r').mpr ((mem_negRoots P b r').mpr hr')))
    have hroot' : P.root r' =
        P.root r - ∑ k ∈ P.orbitIndices σ s, P.pairingIn ℤ r k • P.root k := by
      rw [← P.weylGroup_apply_root, P.orbitReflection_smul horth_s]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [root_coroot'_eq_pairing, ← P.algebraMap_pairingIn ℤ r k, algebraMap_int_eq,
        Int.coe_castRingHom, Int.cast_smul_eq_zsmul]
    have hli : LinearIndepOn ℤ P.root (b.support : Set ι) :=
      b.linearIndepOn_root.restrict_scalars' ℤ
    have hcomb : ∑ k ∈ b.support,
        ((f k : ℤ) + (g k : ℤ) -
          if k ∈ P.orbitIndices σ s then P.pairingIn ℤ r k else 0) • P.root k = 0 := by
      have hite : ∑ k ∈ b.support,
          (if k ∈ P.orbitIndices σ s then P.pairingIn ℤ r k else 0) • P.root k =
          ∑ k ∈ P.orbitIndices σ s, P.pairingIn ℤ r k • P.root k := by
        simp_rw [ite_smul, zero_smul]
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr
          (fun k hk ↦ P.mem_support_of_mem_orbitIndices hσ hs hk)]
      simp_rw [sub_smul, add_smul, natCast_zsmul]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← hf, ← hg,
        root_reflectionPerm, reflection_apply_self, hite]
      rw [hroot']
      abel
    have hcoeff := linearIndepOn_iff'.mp hli b.support _ subset_rfl hcomb
    have hsub : P.root r = ∑ k ∈ P.orbitIndices σ s, f k • P.root k := by
      rw [hf]
      refine (Finset.sum_subset (fun k hk ↦ P.mem_support_of_mem_orbitIndices hσ hs hk) ?_).symm
      intro k hk hnot
      have hk0 := hcoeff k hk
      simp only [hnot, ↓reduceIte, sub_zero] at hk0
      have hfk : f k = 0 := by omega
      rw [hfk, zero_smul]
    exact P.mem_orbitIndices_of_root_eq_sum hσ hsimply horth hs hsub

/-- **Simple-orbit generation of root orbits.** The subgroup of `P.weylGroup` generated by the
simple block reflections `P.orbitReflection σ s` (`s ∈ b.support`) moves every root index into
`b.support`. -/
theorem exists_mem_closure_orbitReflection_mem_support
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι) :
    ∃ w ∈ Subgroup.closure (P.orbitReflection σ '' (b.support : Set ι)),
      P.weylGroupToPerm w r ∈ b.support := by
  have hpos_case : ∀ n : ℕ, ∀ q : ι, b.IsPos q → (b.height q).toNat ≤ n →
      ∃ w ∈ Subgroup.closure (P.orbitReflection σ '' (b.support : Set ι)),
        P.weylGroupToPerm w q ∈ b.support := by
    intro n
    induction n with
    | zero =>
      intro q hq hle
      have := one_le_height_of_mem_posRoots P b ((mem_posRoots P b q).mpr hq)
      omega
    | succ n ih =>
      intro q hq hle
      obtain ⟨s, hs, hsp⟩ := P.exists_mem_support_sum_pairingIn_pos hσ hq
      rcases P.mem_orbitIndices_or_height_lt hσ hsimply horth hs hq hsp with hmem | ⟨hq', hlt⟩
      · exact ⟨1, Subgroup.one_mem _, P.mem_support_of_mem_orbitIndices hσ hs hmem⟩
      · have hpos' := one_le_height_of_mem_posRoots P b ((mem_posRoots P b _).mpr hq')
        obtain ⟨w', hw', hsupp⟩ := ih _ hq' (by omega)
        refine ⟨w' * P.orbitReflection σ s,
          Subgroup.mul_mem _ hw' (Subgroup.subset_closure ⟨s, hs, rfl⟩), ?_⟩
        simpa [map_mul] using hsupp
  by_cases hr : b.IsPos r
  · exact hpos_case (b.height r).toNat r hr le_rfl
  · have hr₀ : b.IsPos (P.reflectionPerm r r) :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b r).mpr ((mem_negRoots P b r).mpr hr)
    obtain ⟨w₀, hw₀, hs₀⟩ := hpos_case _ _ hr₀ le_rfl
    set s₀ := P.weylGroupToPerm w₀ (P.reflectionPerm r r) with hs₀_def
    have hneg : P.weylGroupToPerm w₀ r = P.reflectionPerm s₀ s₀ := by
      rw [P.weylGroupToPerm_apply, hs₀_def, P.weylGroupToPerm_apply,
        ← (w₀ : P.Aut).toHom.indexEquiv_reflectionPerm, P.reflectionPerm_reflectionPerm_self]
    have hs₀_fix : P.weylGroupToPerm (P.orbitReflection σ s₀) (P.reflectionPerm s₀ s₀) = s₀ := by
      have horth_s₀ := P.pairwise_isOrthogonal_orbitIndices_of_mem_support hσ horth hs₀
      rw [← P.weylGroupToPerm_orbitReflection_of_mem horth_s₀ (P.self_mem_orbitIndices σ s₀),
        ← _root_.Equiv.Perm.mul_apply, ← map_mul, P.orbitReflection_mul_self, map_one,
        _root_.Equiv.Perm.coe_one, id_eq]
    refine ⟨P.orbitReflection σ s₀ * w₀,
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨s₀, hs₀, rfl⟩) hw₀, ?_⟩
    rw [map_mul, _root_.Equiv.Perm.mul_apply, hneg, hs₀_fix]
    exact hs₀

/-- **Stembridge's Claim 4.** In a finite simply-laced root pairing, if `σ` permutes `b.support`
with pairwise orthogonal simple orbits, then *every* root `σ`-orbit is pairwise orthogonal. -/
theorem pairing_eq_zero_of_mem_orbitIndices
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r j : ι} (hj : j ∈ P.orbitIndices σ r) (hne : r ≠ j) :
    P.pairing r j = 0 := by
  obtain ⟨w, hw, hs⟩ := P.exists_mem_closure_orbitReflection_mem_support hσ hsimply horth r
  have hcomm := P.commute_of_mem_closure_orbitReflection (b := b) hw
  have hj' : P.weylGroupToPerm w j ∈ P.orbitIndices σ (P.weylGroupToPerm w r) := by
    rw [← P.map_orbitIndices_of_commute hcomm r]
    exact mem_map_of_mem _ hj
  have hne' : P.weylGroupToPerm w r ≠ P.weylGroupToPerm w j :=
    (P.weylGroupToPerm w).injective.ne hne
  have hpair : P.pairing (P.weylGroupToPerm w r) (P.weylGroupToPerm w j) = P.pairing r j := by
    rw [P.weylGroupToPerm_apply, P.weylGroupToPerm_apply]
    exact (w : P.Aut).toHom.pairing
  exact hpair.symm.trans (horth _ hs _ hj' hne')

/-- Pairwise `P.IsOrthogonal` formulation of Stembridge's Claim 4 for every root orbit. -/
theorem pairwise_isOrthogonal_orbitIndices
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι) :
    (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal := by
  intro j hj k hk hne
  have hk' : k ∈ P.orbitIndices σ j := (P.orbitIndices_eq_of_mem hj).symm ▸ hk
  have hp : P.pairing j k = 0 :=
    P.pairing_eq_zero_of_mem_orbitIndices hσ hsimply horth hk' hne
  exact ⟨hp, P.pairing_eq_zero_iff'.mp hp⟩

/-- If a positive root's orbit sum is a scalar multiple of a simple root's orbit sum, the scalar is
`1` and the root lies in that simple orbit. -/
private theorem eq_one_and_mem_of_isPos_of_orbitSum_eq_smul
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r s : ι} {c : R} (hr : b.IsPos r) (hs : s ∈ b.support)
    (heq : P.orbitSum σ r = c • P.orbitSum σ s) :
    c = 1 ∧ r ∈ P.orbitIndices σ s := by
  classical
  have hpos_mem (j : ι) : j ∈ P.orbitIndices σ r → b.IsPos j :=
    fun hj ↦ (P.isPos_iff_of_mem_orbitIndices hσ hj).mpr hr
  choose g hg using fun j : P.orbitIndices σ r ↦
    exists_root_eq_sum_nat_of_mem_posRoots P b ((mem_posRoots P b j.1).mpr (hpos_mem j.1 j.2))
  have hlhs : P.orbitSum σ r =
      ∑ k ∈ b.support, ((∑ j : P.orbitIndices σ r, g j k : ℕ) : R) • P.root k := by
    rw [P.orbitSum_def, ← Finset.sum_coe_sort (P.orbitIndices σ r)]
    calc ∑ j : P.orbitIndices σ r, P.root j
        = ∑ j : P.orbitIndices σ r, ∑ k ∈ b.support, (g j k : R) • P.root k :=
            Finset.sum_congr rfl fun j _ ↦ by
              simpa only [Nat.cast_smul_eq_nsmul] using (hg j).2
      _ = ∑ k ∈ b.support, ((∑ j : P.orbitIndices σ r, g j k : ℕ) : R) • P.root k := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ ↦ by rw [Nat.cast_sum, Finset.sum_smul]
  have hrhs : c • P.orbitSum σ s =
      ∑ k ∈ b.support, (if k ∈ P.orbitIndices σ s then c else 0) • P.root k := by
    simp_rw [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr
      (fun k hk ↦ P.mem_support_of_mem_orbitIndices hσ hs hk), ← Finset.smul_sum, ← P.orbitSum_def]
  have hdiff : ∑ k ∈ b.support,
      (((∑ j : P.orbitIndices σ r, g j k : ℕ) : R) -
        if k ∈ P.orbitIndices σ s then c else 0) • P.root k = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, ← hlhs, ← hrhs, heq, sub_self]
  have hcoeff := linearIndepOn_iff'.mp b.linearIndepOn_root b.support _ subset_rfl hdiff
  let r₀ : P.orbitIndices σ r := ⟨r, P.self_mem_orbitIndices σ r⟩
  have hsub : P.root r = ∑ k ∈ P.orbitIndices σ s, g r₀ k • P.root k := by
    rw [(hg r₀).2]
    refine (Finset.sum_subset (fun k hk ↦ P.mem_support_of_mem_orbitIndices hσ hs hk) ?_).symm
    intro k hk hnot
    have hk0 := hcoeff k hk
    simp only [hnot, ↓reduceIte, sub_zero] at hk0
    have hsum0 : ∑ j : P.orbitIndices σ r, g j k = 0 := by exact_mod_cast hk0
    have hgk : g r₀ k = 0 := (Finset.sum_eq_zero_iff.mp hsum0) r₀ (Finset.mem_univ r₀)
    rw [hgk, zero_smul]
  have hmem : r ∈ P.orbitIndices σ s :=
    P.mem_orbitIndices_of_root_eq_sum hσ hsimply horth hs hsub
  have horth_s := P.pairwise_isOrthogonal_orbitIndices_of_mem_support hσ horth hs
  have h2 : (c - 1) * 2 = 0 := by
    have h0 : (c - 1) • P.orbitSum σ s = 0 := by
      rw [sub_smul, one_smul, ← heq, P.orbitSum_eq_of_mem hmem, sub_self]
    simpa [map_smul, smul_eq_mul, P.coroot'_orbitSum_self horth_s] using
      congrArg (P.coroot' s) h0
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right two_ne_zero), hmem⟩

/-- **Proportionality of orbit sums.** Under the orthogonal-fold hypotheses, `P.orbitSum σ r₁ =
c • P.orbitSum σ r₂` implies `(c = 1 ∧ r₁ ∈ P.orbitIndices σ r₂)` or
`(c = -1 ∧ r₁ ∈ P.orbitIndices σ (P.reflectionPerm r₂ r₂))`. -/
theorem eq_one_or_neg_one_of_orbitSum_eq_smul
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    {r₁ r₂ : ι} {c : R} (heq : P.orbitSum σ r₁ = c • P.orbitSum σ r₂) :
    (c = 1 ∧ r₁ ∈ P.orbitIndices σ r₂) ∨
      (c = -1 ∧ r₁ ∈ P.orbitIndices σ (P.reflectionPerm r₂ r₂)) := by
  obtain ⟨w, hw, hs⟩ := P.exists_mem_closure_orbitReflection_mem_support hσ hsimply horth r₂
  have hcomm := P.commute_of_mem_closure_orbitReflection (b := b) hw
  set r₁' := P.weylGroupToPerm w r₁
  set s := P.weylGroupToPerm w r₂ with hs_def
  have heq' : P.orbitSum σ r₁' = c • P.orbitSum σ s := by
    rw [← P.smul_orbitSum_of_commute hcomm r₁, ← P.smul_orbitSum_of_commute hcomm r₂, heq,
      smul_comm]
  have hpull {a b₀ : ι} (hm : P.weylGroupToPerm w a ∈ P.orbitIndices σ (P.weylGroupToPerm w b₀)) :
      a ∈ P.orbitIndices σ b₀ := by
    rw [← P.map_orbitIndices_of_commute hcomm b₀] at hm
    simpa using hm
  by_cases hpos : b.IsPos r₁'
  · obtain ⟨rfl, hm⟩ := P.eq_one_and_mem_of_isPos_of_orbitSum_eq_smul hσ hsimply horth hpos hs heq'
    exact .inl ⟨rfl, hpull hm⟩
  · have hpos_neg : b.IsPos (P.reflectionPerm r₁' r₁') :=
      (isPos_reflectionPerm_self_iff_mem_negRoots P b r₁').mpr ((mem_negRoots P b r₁').mpr hpos)
    have heq_neg : P.orbitSum σ (P.reflectionPerm r₁' r₁') = (-c) • P.orbitSum σ s := by
      rw [P.orbitSum_reflectionPerm_self, heq', neg_smul]
    obtain ⟨hc, hm⟩ :=
      P.eq_one_and_mem_of_isPos_of_orbitSum_eq_smul hσ hsimply horth hpos_neg hs heq_neg
    have hneg_pull : r₁' ∈ P.orbitIndices σ (P.reflectionPerm s s) :=
      P.mem_orbitIndices.mpr <| by
        simpa [P.reflectionPerm_reflectionPerm_self] using
          (P.mem_orbitIndices.mp hm).map (g := fun z ↦ P.reflectionPerm z z) fun z ↦
            (σ.toHom.indexEquiv_reflectionPerm z z).symm
    have hs_neg : P.reflectionPerm s s = P.weylGroupToPerm w (P.reflectionPerm r₂ r₂) := by
      rw [hs_def, P.weylGroupToPerm_apply, P.weylGroupToPerm_apply]
      exact ((w : P.Aut).toHom.indexEquiv_reflectionPerm r₂ r₂).symm
    exact .inr ⟨by linear_combination -hc, hpull (hs_neg ▸ hneg_pull)⟩

/-- **Injectivity of orbit sums on `σ`-orbits.** Under the orthogonal-fold hypotheses, two root
indices define the same folded root index if and only if they belong to the same `σ`-orbit. -/
theorem foldedIndex_eq_iff_mem_orbitIndices
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r₁ r₂ : ι) :
    P.foldedIndex σ r₁ = P.foldedIndex σ r₂ ↔ r₁ ∈ P.orbitIndices σ r₂ := by
  refine ⟨fun h ↦ ?_, P.foldedIndex_eq_of_mem⟩
  have heq : P.orbitSum σ r₁ = (1 : R) • P.orbitSum σ r₂ := by
    simpa [coe_foldedIndex] using congrArg Subtype.val h
  rcases P.eq_one_or_neg_one_of_orbitSum_eq_smul hσ hsimply horth heq with ⟨-, hm⟩ | ⟨hc, -⟩
  · exact hm
  · exfalso
    have h2 : (2 : R) = 0 := by linear_combination hc
    exact two_ne_zero h2

end Descent

/-! ### Orbit-sum norms and construction of the orthogonal fold -/

section OrthogonalFold

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]

section Norms

variable {P}

/-- Under `P.simplyLacedForm`, pairing a `σ`-fixed weight `x` against `P.orbitSum σ r` multiplies
`P.coroot' r x` by `#(P.orbitIndices σ r)`. -/
theorem simplyLacedForm_apply_orbitSum_of_fixed (b : P.Base)
    (hsimply : b.cartanMatrix.IsSimplyLaced) {σ : P.Aut} {x : M} (hx : σ.weightMap x = x) (r : ι) :
    P.simplyLacedForm.form x (P.orbitSum σ r) = #(P.orbitIndices σ r) * P.coroot' r x := by
  rw [P.orbitSum_def, map_sum]
  have hterm (j : ι) (hj : j ∈ P.orbitIndices σ r) :
      P.simplyLacedForm.form x (P.root j) = P.coroot' r x := by
    rw [P.simplyLacedForm_apply_root b hsimply, P.coroot'_eq_of_mem_orbitIndices_of_fixed hx hj]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

/-- **Squared norm of an orbit sum** (Stembridge, equation (2)): under `P.simplyLacedForm`, each
orbit sum `P.orbitSum σ r` has squared norm `2 * #(P.orbitIndices σ r)`. -/
theorem simplyLacedForm_orbitSum_self {b : P.Base} {σ : P.Aut}
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) (r : ι) :
    P.simplyLacedForm.form (P.orbitSum σ r) (P.orbitSum σ r) =
      2 * #(P.orbitIndices σ r) := by
  rw [P.simplyLacedForm_apply_orbitSum_of_fixed b hsimply (P.weightMap_orbitSum_self σ r) r,
    P.coroot'_orbitSum_self (P.pairwise_isOrthogonal_orbitIndices hσ hsimply horth r), mul_comm]

end Norms

section Construction

variable (b : P.Base) (σ : P.Aut)

omit [CharZero K] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] in
/-- Root embedding of `P.foldedIndices σ` into `LinearMap.fixedSubmodule σ.weightMap`. -/
private def foldedRootEmb :
    P.foldedIndices σ ↪ LinearMap.fixedSubmodule σ.weightMap :=
  ⟨fun u ↦ ⟨(u : M), P.coe_foldedIndices_mem_fixedSubmodule σ u⟩,
    fun _ _ h ↦ Subtype.ext (congrArg (Subtype.val : LinearMap.fixedSubmodule σ.weightMap → M) h)⟩

omit [CharZero K] [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic] in
@[simp]
private theorem coe_foldedRootEmb (u : P.foldedIndices σ) :
    (P.foldedRootEmb σ u : M) = (u : M) :=
  rfl

omit [P.IsReduced] in
/-- Candidate coroot functional attached to `u : P.foldedIndices σ`, defined directly on `E^σ` from
`P.simplyLacedForm` without choosing an orbit representative. -/
private noncomputable def foldedCorootFun
    (u : P.foldedIndices σ) : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) :=
  (2 / P.simplyLacedForm.form (u : M) (u : M)) •
    (P.simplyLacedForm.form.flip (u : M)).comp (LinearMap.fixedSubmodule σ.weightMap).subtype

private theorem foldedCorootFun_foldedIndex_apply
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r : ι) (x : LinearMap.fixedSubmodule σ.weightMap) :
    P.foldedCorootFun σ (P.foldedIndex σ r) x = P.coroot' r (x : M) := by
  have hx : σ.weightMap (x : M) = (x : M) := LinearMap.mem_fixedSubmodule_iff.mp x.2
  have hd : (#(P.orbitIndices σ r) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (P.card_orbitIndices_pos σ r).ne'
  rw [foldedCorootFun, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_subtype,
    P.simplyLacedForm.form.flip_apply, smul_eq_mul, P.coe_foldedIndex,
    P.simplyLacedForm_orbitSum_self hσ hsimply horth r,
    P.simplyLacedForm_apply_orbitSum_of_fixed b hsimply hx r]
  field_simp

private theorem foldedCorootFun_injective
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    Injective (P.foldedCorootFun σ) := by
  let _ := Fintype.ofFinite ι
  let B := P.posRootForm ℤ
  intro u₁ u₂ h
  obtain ⟨r₁, rfl⟩ := P.foldedIndex_surjective σ u₁
  obtain ⟨r₂, rfl⟩ := P.foldedIndex_surjective σ u₂
  have hcor (x : LinearMap.fixedSubmodule σ.weightMap) :
      P.coroot' r₁ (x : M) = P.coroot' r₂ (x : M) := by
    simpa [P.foldedCorootFun_foldedIndex_apply b σ hσ hsimply horth] using LinearMap.congr_fun h x
  have hB_orb (r : ι) {x : M} (hx : σ.weightMap x = x) :
      2 * P.RootForm x (P.orbitSum σ r) =
        (((#(P.orbitIndices σ r) : ℤ) * B.rootLength r : ℤ) : K) * P.coroot' r x := by
    rw [P.orbitSum_def, map_sum, Finset.mul_sum]
    have hterm (j : ι) (hj : j ∈ P.orbitIndices σ r) :
        2 * P.RootForm x (P.root j) = (B.rootLength r : K) * P.coroot' r x := by
      obtain ⟨m, hm⟩ := P.mem_orbitIndices_iff_exists_pow.mp hj
      have hlen : P.RootForm (P.root j) (P.root j) = (B.rootLength r : K) := by
        rw [← hm, ← Equiv.weightMap_pow_root σ m r, (σ ^ m : P.Aut).toHom.rootForm_weightMap]
        exact (B.algebraMap_rootLength r).symm
      have h2 := B.toInvariantForm.two_mul_apply_root x j
      simp only [B, posRootForm, RootPositiveForm.toInvariantForm_form] at h2
      rw [hlen, P.coroot'_eq_of_mem_orbitIndices_of_fixed hx hj] at h2
      linear_combination h2
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  set m₁ : ℤ := (#(P.orbitIndices σ r₁) : ℤ) * B.rootLength r₁
  set m₂ : ℤ := (#(P.orbitIndices σ r₂) : ℤ) * B.rootLength r₂
  have hm₁ : 0 < m₁ :=
    mul_pos (Int.natCast_pos.mpr (P.card_orbitIndices_pos σ r₁)) (B.rootLength_pos r₁)
  have hm₂ : 0 < m₂ :=
    mul_pos (Int.natCast_pos.mpr (P.card_orbitIndices_pos σ r₂)) (B.rootLength_pos r₂)
  set v₁ : P.rootSpan ℤ := ∑ j ∈ P.orbitIndices σ r₁, P.rootSpanMem ℤ j
  set v₂ : P.rootSpan ℤ := ∑ j ∈ P.orbitIndices σ r₂, P.rootSpanMem ℤ j
  set z : P.rootSpan ℤ := m₂ • v₁ - m₁ • v₂
  have hz_coe : (z : M) = (m₂ : K) • P.orbitSum σ r₁ - (m₁ : K) • P.orbitSum σ r₂ := by
    simp [z, v₁, v₂, P.orbitSum_def, Int.cast_smul_eq_zsmul]
  have hz_fix : σ.weightMap (z : M) = (z : M) := by
    rw [hz_coe, map_sub, map_smul, map_smul, P.weightMap_orbitSum_self, P.weightMap_orbitSum_self]
  have hz_cor : P.coroot' r₁ (z : M) = P.coroot' r₂ (z : M) :=
    hcor ⟨(z : M), LinearMap.mem_fixedSubmodule_iff.mpr hz_fix⟩
  have hz_form : P.RootForm (z : M) (z : M) = 0 := by
    have h2 : 2 * P.RootForm (z : M) (z : M) = 0 := by
      calc 2 * P.RootForm (z : M) (z : M)
          = (m₂ : K) * (2 * P.RootForm (z : M) (P.orbitSum σ r₁)) -
              (m₁ : K) * (2 * P.RootForm (z : M) (P.orbitSum σ r₂)) := by
              conv_lhs => arg 2; arg 2; rw [hz_coe]
              rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
              ring
        _ = (m₂ : K) * ((m₁ : K) * P.coroot' r₁ (z : M)) -
              (m₁ : K) * ((m₂ : K) * P.coroot' r₂ (z : M)) := by
              rw [hB_orb r₁ hz_fix, hB_orb r₂ hz_fix]
        _ = 0 := by rw [hz_cor]; ring
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have hz0 : z = 0 := by
    by_contra hne
    have hpos := P.posRootForm_posForm_pos_of_ne_zero ℤ hne
    have hcast : ((B.posForm z z : ℤ) : K) = 0 :=
      (P.algebraMap_posRootForm_posForm ℤ z z).trans hz_form
    exact hpos.ne' (Int.cast_eq_zero.mp hcast)
  have hm₂K : (m₂ : K) ≠ 0 := Int.cast_ne_zero.mpr hm₂.ne'
  have hsmul : P.orbitSum σ r₁ = ((m₂ : K)⁻¹ * (m₁ : K)) • P.orbitSum σ r₂ := by
    have hsub : (m₂ : K) • P.orbitSum σ r₁ = (m₁ : K) • P.orbitSum σ r₂ :=
      sub_eq_zero.mp (hz_coe ▸ congrArg Subtype.val hz0)
    rw [← inv_smul_smul₀ hm₂K (P.orbitSum σ r₁), hsub, smul_smul]
  rcases P.eq_one_or_neg_one_of_orbitSum_eq_smul hσ hsimply horth hsmul with ⟨_, hm⟩ | ⟨hc, -⟩
  · exact P.foldedIndex_eq_of_mem hm
  · exfalso
    have hsumK : ((m₁ + m₂ : ℤ) : K) = 0 := by
      push_cast
      have hmul := congrArg ((m₂ : K) * ·) hc
      rw [← mul_assoc, mul_inv_cancel₀ hm₂K, one_mul, mul_neg_one] at hmul
      linear_combination hmul
    have hsumZ : m₁ + m₂ = 0 := Int.cast_eq_zero.mp hsumK
    omega

/-- Shared pre-reflection calculation on `P.foldedRootEmb σ`. -/
private theorem preReflection_foldedCorootFun_foldedRootEmb
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)
    (r t : ι) :
    Module.preReflection (P.foldedRootEmb σ (P.foldedIndex σ r))
      (P.foldedCorootFun σ (P.foldedIndex σ r))
      (P.foldedRootEmb σ (P.foldedIndex σ t)) =
      P.foldedRootEmb σ (P.foldedIndex σ (P.weylGroupToPerm (P.orbitReflection σ r) t)) := by
  have horth_r := P.pairwise_isOrthogonal_orbitIndices hσ hsimply horth r
  apply Subtype.ext
  rw [Module.preReflection_apply, Submodule.coe_sub, Submodule.coe_smul_of_tower,
    P.foldedCorootFun_foldedIndex_apply b σ hσ hsimply horth r,
    coe_foldedRootEmb, coe_foldedRootEmb, coe_foldedRootEmb,
    P.coe_foldedIndex, P.coe_foldedIndex, P.coe_foldedIndex,
    ← P.orbitReflection_smul_of_fixed horth_r (P.weightMap_orbitSum_self σ t),
    P.smul_orbitSum_of_commute (P.commute_coe_orbitReflection σ r) t]

/-- Auxiliary construction of the folded `RootPairing` via `RootPairing.mk''`. -/
private noncomputable def orthogonalFoldPairing
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    RootPairing (P.foldedIndices σ) K (LinearMap.fixedSubmodule σ.weightMap)
      (Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :=
  have : Module.Finite K M := Module.Finite.of_basis b.toWeightBasis
  let corootEmb : P.foldedIndices σ ↪ Module.Dual K (LinearMap.fixedSubmodule σ.weightMap) :=
    ⟨P.foldedCorootFun σ, P.foldedCorootFun_injective b σ hσ hsimply horth⟩
  RootPairing.mk'' (Module.Dual.eval K (LinearMap.fixedSubmodule σ.weightMap))
    (P.foldedRootEmb σ) corootEmb
    (fun u ↦ by
      obtain ⟨r, rfl⟩ := P.foldedIndex_surjective σ u
      rw [Module.Dual.eval_apply]
      exact (P.foldedCorootFun_foldedIndex_apply b σ hσ hsimply horth r _).trans
        (by rw [coe_foldedRootEmb, P.coe_foldedIndex]; exact
          P.coroot'_orbitSum_self (P.pairwise_isOrthogonal_orbitIndices hσ hsimply horth r)))
    (by
      intro u x hx
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨r, rfl⟩ := P.foldedIndex_surjective σ u
      obtain ⟨t, rfl⟩ := P.foldedIndex_surjective σ v
      exact ⟨P.foldedIndex σ (P.weylGroupToPerm (P.orbitReflection σ r) t),
        (P.preReflection_foldedCorootFun_foldedRootEmb b σ hσ hsimply horth r t).symm⟩)
    (top_unique <| (P.span_fixedSubmodule_orbitSum_support_eq_top b σ).symm.trans_le <|
      Submodule.span_mono <| by
        rintro _ ⟨s, -, rfl⟩
        exact ⟨P.foldedIndex σ s, Subtype.ext (P.coe_foldedIndex σ s)⟩)

section PrivateProperties

variable (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
  (hsimply : b.cartanMatrix.IsSimplyLaced)
  (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0)

@[simp]
private theorem orthogonalFoldPairing_root (u : P.foldedIndices σ) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).root u = P.foldedRootEmb σ u :=
  rfl

@[simp]
private theorem orthogonalFoldPairing_coroot (u : P.foldedIndices σ) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).coroot u = P.foldedCorootFun σ u :=
  rfl

@[simp]
private theorem orthogonalFoldPairing_toLinearMap (x : LinearMap.fixedSubmodule σ.weightMap)
    (f : Module.Dual K (LinearMap.fixedSubmodule σ.weightMap)) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).toLinearMap x f = f x :=
  rfl

@[simp]
private theorem orthogonalFoldPairing_coroot' (u : P.foldedIndices σ)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).coroot' u x = P.foldedCorootFun σ u x :=
  rfl

/-- Shared sum expansion for the pairing of two folded indices in `orthogonalFoldPairing`. -/
private theorem orthogonalFoldPairing_toLinearMap_root_coroot (r t : ι) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).toLinearMap
      ((P.orthogonalFoldPairing b σ hσ hsimply horth).root (P.foldedIndex σ r))
      ((P.orthogonalFoldPairing b σ hσ hsimply horth).coroot (P.foldedIndex σ t)) =
      ((∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k t : ℤ) : K) := by
  rw [orthogonalFoldPairing_toLinearMap, orthogonalFoldPairing_coroot, orthogonalFoldPairing_root,
    P.foldedCorootFun_foldedIndex_apply b σ hσ hsimply horth t, coe_foldedRootEmb,
    P.coe_foldedIndex, P.orbitSum_def, map_sum, Int.cast_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by
    simpa [root_coroot'_eq_pairing] using (P.algebraMap_pairingIn ℤ k t).symm

private theorem orthogonalFoldPairing_int (u v : P.foldedIndices σ) :
    ∃ z : ℤ, (z : K) = (P.orthogonalFoldPairing b σ hσ hsimply horth).toLinearMap
      ((P.orthogonalFoldPairing b σ hσ hsimply horth).root u)
      ((P.orthogonalFoldPairing b σ hσ hsimply horth).coroot v) := by
  obtain ⟨r, rfl⟩ := P.foldedIndex_surjective σ u
  obtain ⟨t, rfl⟩ := P.foldedIndex_surjective σ v
  exact ⟨∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k t,
    (P.orthogonalFoldPairing_toLinearMap_root_coroot b σ hσ hsimply horth r t).symm⟩

private theorem orthogonalFoldPairing_isRootSystem :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).IsRootSystem := by
  have : Module.Finite K M := Module.Finite.of_basis b.toWeightBasis
  rw [orthogonalFoldPairing]
  exact RootPairing.isRootSystem_mk'' (P.orthogonalFoldPairing_int b σ hσ hsimply horth)

private theorem orthogonalFoldPairing_isCrystallographic :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).IsCrystallographic :=
  ⟨P.orthogonalFoldPairing_int b σ hσ hsimply horth⟩

private theorem orthogonalFoldPairing_isReduced :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).IsReduced where
  eq_or_eq_neg u v hdep := by
    obtain ⟨r₁, rfl⟩ := P.foldedIndex_surjective σ u
    obtain ⟨r₂, rfl⟩ := P.foldedIndex_surjective σ v
    let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
    have hne : Ψ.root (P.foldedIndex σ r₂) ≠ 0 := fun h0 ↦
      P.orbitSum_ne_zero hσ r₂ (by
        simpa [Ψ] using congrArg (Subtype.val : LinearMap.fixedSubmodule σ.weightMap → M) h0)
    rw [LinearIndependent.pair_symm_iff, LinearIndependent.pair_iff' hne] at hdep
    push Not at hdep
    obtain ⟨c, hc⟩ := hdep
    have hsmul : P.orbitSum σ r₁ = c • P.orbitSum σ r₂ := by
      simpa [Ψ] using congrArg (Subtype.val : LinearMap.fixedSubmodule σ.weightMap → M) hc.symm
    rcases P.eq_one_or_neg_one_of_orbitSum_eq_smul hσ hsimply horth hsmul with ⟨_, hm⟩ | ⟨rfl, _⟩
    · exact .inl (congrArg Ψ.root (P.foldedIndex_eq_of_mem hm))
    · exact .inr (by simpa [Ψ] using hc.symm)

private theorem orthogonalFoldPairing_reflectionPerm (r t : ι) :
    (P.orthogonalFoldPairing b σ hσ hsimply horth).reflectionPerm
        (P.foldedIndex σ r) (P.foldedIndex σ t) =
      P.foldedIndex σ (P.weylGroupToPerm (P.orbitReflection σ r) t) := by
  let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
  apply Ψ.root.injective
  rw [Ψ.root_reflectionPerm, Ψ.reflection_apply]
  exact P.preReflection_foldedCorootFun_foldedRootEmb b σ hσ hsimply horth r t

/-- One step of `ℤ`-span descent along a simple block reflection `P.orbitReflection σ s₀`. -/
private theorem orthogonalFoldPairing_inSpan_of_orbitReflection
    [DecidableEq (P.foldedIndices σ)] {s₀ q : ι} (hs₀ : s₀ ∈ b.support)
    (hq :
      let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
      let supp := b.support.image (P.foldedIndex σ)
      let q' := P.weylGroupToPerm (P.orbitReflection σ s₀) q
      Ψ.coroot (P.foldedIndex σ q') ∈ span ℤ (Ψ.coroot '' (supp : Set (P.foldedIndices σ))) ∧
        Ψ.root (P.foldedIndex σ q') ∈ span ℤ (Ψ.root '' (supp : Set (P.foldedIndices σ)))) :
    let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
    let supp := b.support.image (P.foldedIndex σ)
    Ψ.coroot (P.foldedIndex σ q) ∈ span ℤ (Ψ.coroot '' (supp : Set (P.foldedIndices σ))) ∧
      Ψ.root (P.foldedIndex σ q) ∈ span ℤ (Ψ.root '' (supp : Set (P.foldedIndices σ))) := by
  let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
  have := P.orthogonalFoldPairing_isCrystallographic b σ hσ hsimply horth
  let supp := b.support.image (P.foldedIndex σ)
  have hinvol : P.weylGroupToPerm (P.orbitReflection σ s₀)
      (P.weylGroupToPerm (P.orbitReflection σ s₀) q) = q := by
    rw [← _root_.Equiv.Perm.mul_apply, ← map_mul, P.orbitReflection_mul_self, map_one,
      _root_.Equiv.Perm.coe_one, id_eq]
  have hrefl := P.orthogonalFoldPairing_reflectionPerm b σ hσ hsimply horth s₀
    (P.weylGroupToPerm (P.orbitReflection σ s₀) q)
  rw [hinvol] at hrefl
  have hs₀_mem : P.foldedIndex σ s₀ ∈ (supp : Set (P.foldedIndices σ)) :=
    Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hs₀)
  set u' := P.foldedIndex σ (P.weylGroupToPerm (P.orbitReflection σ s₀) q)
  set u₀ := P.foldedIndex σ s₀
  dsimp only
  rw [← hrefl, Ψ.coroot_reflectionPerm, Ψ.root_reflectionPerm, Ψ.coreflection_apply_coroot,
    Ψ.reflection_apply_root, ← Ψ.algebraMap_pairingIn ℤ u₀ u', ← Ψ.algebraMap_pairingIn ℤ u' u₀,
    algebraMap_int_eq, Int.coe_castRingHom, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact ⟨sub_mem hq.1 (zsmul_mem (subset_span (Set.mem_image_of_mem Ψ.coroot hs₀_mem)) _),
    sub_mem hq.2 (zsmul_mem (subset_span (Set.mem_image_of_mem Ψ.root hs₀_mem)) _)⟩

/-- Both folded roots and folded coroots lie in the `ℤ`-spans of the simple folded roots and
coroots, by induction along `Subgroup.closure (P.orbitReflection σ '' b.support)`. -/
private theorem orthogonalFoldPairing_mem_span_int
    [DecidableEq (P.foldedIndices σ)] (u : P.foldedIndices σ) :
    let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
    let supp := b.support.image (P.foldedIndex σ)
    Ψ.coroot u ∈ span ℤ (Ψ.coroot '' (supp : Set (P.foldedIndices σ))) ∧
      Ψ.root u ∈ span ℤ (Ψ.root '' (supp : Set (P.foldedIndices σ))) := by
  let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
  let supp := b.support.image (P.foldedIndex σ)
  let inSpan (q : ι) : Prop :=
    Ψ.coroot (P.foldedIndex σ q) ∈ span ℤ (Ψ.coroot '' (supp : Set (P.foldedIndices σ))) ∧
      Ψ.root (P.foldedIndex σ q) ∈ span ℤ (Ψ.root '' (supp : Set (P.foldedIndices σ)))
  have hclosure {w : P.weylGroup}
      (hw : w ∈ Subgroup.closure (P.orbitReflection σ '' (b.support : Set ι))) :
      ∀ q : ι, inSpan (P.weylGroupToPerm w q) → inSpan q := by
    induction hw using Subgroup.closure_induction'' with
    | one => intro q hq; simpa using hq
    | mem g hg =>
      obtain ⟨s₀, hs₀, rfl⟩ := hg
      exact fun _ hq ↦ P.orthogonalFoldPairing_inSpan_of_orbitReflection b σ hσ hsimply horth hs₀ hq
    | inv_mem g hg =>
      obtain ⟨s₀, hs₀, rfl⟩ := hg
      intro q hq
      rw [P.orbitReflection_inv] at hq
      exact P.orthogonalFoldPairing_inSpan_of_orbitReflection b σ hσ hsimply horth hs₀ hq
    | mul w₁ w₂ _ _ ih₁ ih₂ =>
      exact fun q hq ↦ ih₂ q (ih₁ (P.weylGroupToPerm w₂ q) (by simpa [map_mul] using hq))
  obtain ⟨r, rfl⟩ := P.foldedIndex_surjective σ u
  obtain ⟨w, hw, hsupp⟩ := P.exists_mem_closure_orbitReflection_mem_support hσ hsimply horth r
  have hmem : P.foldedIndex σ (P.weylGroupToPerm w r) ∈ (supp : Set (P.foldedIndices σ)) :=
    Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hsupp)
  exact hclosure hw r (And.intro
    (subset_span (Set.mem_image_of_mem Ψ.coroot hmem))
    (subset_span (Set.mem_image_of_mem Ψ.root hmem)))

end PrivateProperties

/-- **The orthogonal orbit-sum fold** (Stembridge, Claim 1). For a finite simply-laced root system
`P` over a characteristic-zero field `K`, a base `b`, and an automorphism `σ` permuting `b.support`
with pairwise orthogonal simple orbits, the distinct orbit sums form a reduced crystallographic root
system on `LinearMap.fixedSubmodule σ.weightMap` and its linear dual with base given by the
simple-orbit sums. -/
noncomputable def orthogonalFold
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    P.OrbitSumRealization b σ := by
  classical
  let Ψ := P.orthogonalFoldPairing b σ hσ hsimply horth
  have := P.orthogonalFoldPairing_isRootSystem b σ hσ hsimply horth
  have := P.orthogonalFoldPairing_isReduced b σ hσ hsimply horth
  have := P.orthogonalFoldPairing_isCrystallographic b σ hσ hsimply horth
  let supp := b.support.image (P.foldedIndex σ)
  have h₀ : LinearIndepOn K Ψ.root (supp : Set (P.foldedIndices σ)) := by
    have hcoe : (supp : Set (P.foldedIndices σ)) = P.foldedIndex σ '' (b.support : Set ι) := by
      simp [supp]
    rw [hcoe]
    have hli := P.linearIndepOn_coe_foldedIndex_image_support hσ
    exact LinearIndepOn.of_comp (LinearMap.fixedSubmodule σ.weightMap).subtype hli
  have h₁ : Set.Pairwise (supp : Set (P.foldedIndices σ)) fun u v ↦ Ψ.pairingIn ℤ u v ≤ 0 := by
    intro u hu v hv huv
    obtain ⟨s₁, hs₁, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
    obtain ⟨s₂, hs₂, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    have hsum : Ψ.pairingIn ℤ (P.foldedIndex σ s₁) (P.foldedIndex σ s₂) =
        ∑ k ∈ P.orbitIndices σ s₁, P.pairingIn ℤ k s₂ := by
      apply FaithfulSMul.algebraMap_injective ℤ K
      rw [Ψ.algebraMap_pairingIn ℤ, algebraMap_int_eq, Int.coe_castRingHom]
      exact P.orthogonalFoldPairing_toLinearMap_root_coroot b σ hσ hsimply horth s₁ s₂
    rw [hsum]
    refine Finset.sum_nonpos fun k hk ↦ ?_
    have hks₂ : k ≠ s₂ := fun h ↦ huv (h ▸ (P.foldedIndex_eq_of_mem hk).symm)
    exact b.pairingIn_le_zero_of_ne hks₂ (P.mem_support_of_mem_orbitIndices hσ hs₁ hk) hs₂
  have hspan := P.orthogonalFoldPairing_mem_span_int b σ hσ hsimply horth
  exact
    { pairing := Ψ
      base := Base.mkOfPairwiseLEZero Ψ h₀ h₁ (fun u ↦ (hspan u).1) (fun u ↦ (hspan u).2)
      rootSystem := inferInstance
      reduced := inferInstance
      crystallographic := inferInstance
      evaluation := P.orthogonalFoldPairing_toLinearMap b σ hσ hsimply horth
      root_eq := fun _ ↦ by simp [Ψ]
      mem_support_base_iff := fun u ↦ by
        rw [Base.mkOfPairwiseLEZero_support]
        simp only [supp, Finset.mem_image]
        exact ⟨fun ⟨j, hj, hju⟩ ↦
            ⟨j, hj, (P.coe_foldedIndex σ j).symm.trans (congrArg Subtype.val hju)⟩,
          fun ⟨j, hj, hju⟩ ↦ ⟨j, hj, Subtype.ext ((P.coe_foldedIndex σ j).trans hju)⟩⟩ }

/-- Existence form of `P.orthogonalFold`. -/
theorem nonempty_orbitSumRealization_of_isSimplyLaced
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    (horth : ∀ i ∈ b.support, ∀ j ∈ P.orbitIndices σ i, i ≠ j → P.pairing i j = 0) :
    Nonempty (P.OrbitSumRealization b σ) :=
  ⟨P.orthogonalFold b σ hσ hsimply horth⟩

end Construction

end OrthogonalFold

/-! ### Characteristic formulas on any `OrbitSumRealization` -/

namespace OrbitSumRealization

section CommRing

variable {ι R M N : Type*} [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] {b : P.Base} {σ : P.Aut}
  (F : P.OrbitSumRealization b σ)

/-- **Folded coroot evaluation.** On any `F : P.OrbitSumRealization b σ`, for any pairwise
orthogonal `σ`-orbit `P.orbitIndices σ r`, evaluating `F.pairing.coroot (P.foldedIndex σ r)` on a
fixed weight `x` equals `P.coroot' r x`. -/
theorem coroot_foldedIndex_apply {r : ι}
    (horth_r : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot (P.foldedIndex σ r) x = P.coroot' r (x : M) := by
  let f : Module.Dual R (LinearMap.fixedSubmodule σ.weightMap) :=
    (P.coroot' r).comp (LinearMap.fixedSubmodule σ.weightMap).subtype
  have hcor : F.pairing.coroot (P.foldedIndex σ r) = f := by
    refine F.coroot_eq_of_preReflection_mapsTo (P.foldedIndex σ r) ?_ ?_
    · rw [LinearMap.comp_apply, Submodule.coe_subtype, F.coe_root_foldedIndex]
      exact P.coroot'_orbitSum_self horth_r
    · rintro _ ⟨v, rfl⟩
      obtain ⟨t, rfl⟩ := P.foldedIndex_surjective σ v
      refine ⟨P.foldedIndex σ (P.weylGroupToPerm (P.orbitReflection σ r) t), Subtype.ext ?_⟩
      rw [F.coe_root_foldedIndex, Module.preReflection_apply, Submodule.coe_sub,
        Submodule.coe_smul_of_tower, LinearMap.comp_apply, Submodule.coe_subtype,
        F.coe_root_foldedIndex, F.coe_root_foldedIndex,
        ← P.orbitReflection_smul_of_fixed horth_r (P.weightMap_orbitSum_self σ t),
        P.smul_orbitSum_of_commute (P.commute_coe_orbitReflection σ r) t]
  exact LinearMap.congr_fun hcor x

/-- `coroot'` form of `coroot_foldedIndex_apply`. -/
theorem coroot'_foldedIndex_apply {r : ι}
    (horth_r : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    F.pairing.coroot' (P.foldedIndex σ r) x = P.coroot' r (x : M) := by
  rw [F.coroot'_eq_coroot, F.coroot_foldedIndex_apply horth_r]

/-- **Folded root-coroot pairing.** When `P.orbitIndices σ t` is pairwise orthogonal, pairing
`P.foldedIndex σ r` with the coroot of `P.foldedIndex σ t` sums `P.pairing k t` over
`k ∈ P.orbitIndices σ r`. -/
theorem pairing_foldedIndex (r : ι) {t : ι}
    (horth_t : (P.orbitIndices σ t : Set ι).Pairwise P.IsOrthogonal) :
    F.pairing.pairing (P.foldedIndex σ r) (P.foldedIndex σ t) =
      ∑ k ∈ P.orbitIndices σ r, P.pairing k t := by
  rw [← F.pairing.root_coroot'_eq_pairing, F.coroot'_foldedIndex_apply horth_t,
    F.coe_root_foldedIndex, P.orbitSum_def, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ P.root_coroot'_eq_pairing t k

/-- **Reflection comparison.** On any `F : P.OrbitSumRealization b σ`, for any pairwise orthogonal
`σ`-orbit `P.orbitIndices σ r`, the folded reflection in `P.foldedIndex σ r` restricts the
commuting block reflection `P.orbitReflection σ r` to `LinearMap.fixedSubmodule σ.weightMap`. -/
theorem coe_reflection_foldedIndex {r : ι}
    (horth_r : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal)
    (x : LinearMap.fixedSubmodule σ.weightMap) :
    ((F.pairing.reflection (P.foldedIndex σ r) x :
      LinearMap.fixedSubmodule σ.weightMap) : M) =
      P.orbitReflection σ r • (x : M) := by
  rw [F.pairing.reflection_apply, Submodule.coe_sub, Submodule.coe_smul_of_tower,
    F.coroot'_foldedIndex_apply horth_r, F.coe_root_foldedIndex,
    P.orbitReflection_smul_of_fixed horth_r (LinearMap.mem_fixedSubmodule_iff.mp x.2)]

/-- Folded `reflectionPerm` agrees with the index permutation action of `P.orbitReflection σ r`
whenever `P.orbitIndices σ r` is pairwise orthogonal. -/
theorem reflectionPerm_foldedIndex {r : ι}
    (horth_r : (P.orbitIndices σ r : Set ι).Pairwise P.IsOrthogonal) (t : ι) :
    F.pairing.reflectionPerm (P.foldedIndex σ r) (P.foldedIndex σ t) =
      P.foldedIndex σ (P.weylGroupToPerm (P.orbitReflection σ r) t) := by
  apply F.pairing.root.injective
  apply Subtype.ext
  rw [F.pairing.root_reflectionPerm, F.coe_reflection_foldedIndex horth_r, F.coe_root_foldedIndex,
    F.coe_root_foldedIndex, P.smul_orbitSum_of_commute (P.commute_coe_orbitReflection σ r) t]

/-- Integer-valued form of `pairing_foldedIndex`. -/
theorem pairingIn_foldedIndex [P.IsCrystallographic] (r : ι) {t : ι}
    (horth_t : (P.orbitIndices σ t : Set ι).Pairwise P.IsOrthogonal) :
    F.pairing.pairingIn ℤ (P.foldedIndex σ r) (P.foldedIndex σ t) =
      ∑ k ∈ P.orbitIndices σ r, P.pairingIn ℤ k t := by
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [F.pairing.algebraMap_pairingIn ℤ, F.pairing_foldedIndex r horth_t, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ (P.algebraMap_pairingIn ℤ k t).symm

/-- **Oriented Cartan edge-count identity in `ℤ`** (Stembridge, equation (3)): for simple roots
`s₁, s₂ ∈ b.support` in distinct `σ`-orbits with `P.orbitIndices σ s₂` pairwise orthogonal,
`#(P.orbitIndices σ s₂)` times the folded Cartan integer `⟨β_{s₁}, β_{s₂}^∨⟩` equals minus the
number of non-orthogonal pairs between `P.orbitIndices σ s₁` and `P.orbitIndices σ s₂`. -/
theorem card_orbitIndices_mul_pairingIn_foldedIndex [DecidableEq R] [P.IsCrystallographic]
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    {s₁ s₂ : ι} (horth_s₂ : (P.orbitIndices σ s₂ : Set ι).Pairwise P.IsOrthogonal)
    (hs₁ : s₁ ∈ b.support) (hs₂ : s₂ ∈ b.support)
    (hne : P.foldedIndex σ s₁ ≠ P.foldedIndex σ s₂) :
    (#(P.orbitIndices σ s₂) : ℤ) *
        F.pairing.pairingIn ℤ (P.foldedIndex σ s₁) (P.foldedIndex σ s₂) =
      -(#((P.orbitIndices σ s₁ ×ˢ P.orbitIndices σ s₂).filter
          fun p ↦ P.pairing p.1 p.2 ≠ 0) : ℤ) := by
  have hprod : (#(P.orbitIndices σ s₂) : ℤ) *
        F.pairing.pairingIn ℤ (P.foldedIndex σ s₁) (P.foldedIndex σ s₂) =
      ∑ p ∈ P.orbitIndices σ s₁ ×ˢ P.orbitIndices σ s₂, P.pairingIn ℤ p.1 p.2 := by
    rw [Finset.sum_product_right]
    have hrow (t' : ι) (ht' : t' ∈ P.orbitIndices σ s₂) :
        ∑ k ∈ P.orbitIndices σ s₁, P.pairingIn ℤ k t' =
          F.pairing.pairingIn ℤ (P.foldedIndex σ s₁) (P.foldedIndex σ s₂) := by
      have horth_t' : (P.orbitIndices σ t' : Set ι).Pairwise P.IsOrthogonal := by
        rw [P.orbitIndices_eq_of_mem ht']
        exact horth_s₂
      rw [← F.pairingIn_foldedIndex s₁ horth_t', P.foldedIndex_eq_of_mem ht']
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul]
  rw [hprod]
  have hterm (p : ι × ι) (hp : p ∈ P.orbitIndices σ s₁ ×ˢ P.orbitIndices σ s₂) :
      P.pairingIn ℤ p.1 p.2 = if P.pairing p.1 p.2 ≠ 0 then -1 else 0 := by
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    have hb₁ : p.1 ∈ b.support := P.mem_support_of_mem_orbitIndices hσ hs₁ hp₁
    have hb₂ : p.2 ∈ b.support := P.mem_support_of_mem_orbitIndices hσ hs₂ hp₂
    have hpne : (⟨p.1, hb₁⟩ : b.support) ≠ ⟨p.2, hb₂⟩ := by
      intro h
      have heq : p.1 = p.2 := congrArg Subtype.val h
      exact hne ((P.foldedIndex_eq_of_mem hp₁).symm.trans (heq ▸ P.foldedIndex_eq_of_mem hp₂))
    have hzero_iff : P.pairingIn ℤ p.1 p.2 = 0 ↔ P.pairing p.1 p.2 = 0 := by
      rw [← P.algebraMap_pairingIn ℤ p.1 p.2, algebraMap_int_eq, Int.coe_castRingHom,
        Int.cast_eq_zero]
    rcases hsimply hpne with h0 | h1
    · have hp0 : P.pairingIn ℤ p.1 p.2 = 0 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using h0
      simp [hp0, hzero_iff.mp hp0]
    · have hp1 : P.pairingIn ℤ p.1 p.2 = -1 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using h1
      have hnz : P.pairing p.1 p.2 ≠ 0 := fun hz ↦ by
        have := hzero_iff.mpr hz
        omega
      simp [hp1, hnz]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_neg_one]

end CommRing

section Field

variable {ι K M N : Type*} [Field K] [CharZero K] [DecidableEq K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [Finite ι] [P.IsCrystallographic] {b : P.Base} {σ : P.Aut}
  (F : P.OrbitSumRealization b σ)

/-- **Oriented Cartan entry as edge count divided by target-orbit size** (Stembridge, equation (3)):
for simple roots `s₁, s₂ ∈ b.support` in distinct `σ`-orbits with `P.orbitIndices σ s₂` pairwise
orthogonal, `⟨β_{s₁}, β_{s₂}^∨⟩ = -N_{O₁, O₂} / |O₂|`. -/
theorem pairing_foldedIndex_eq_neg_card_div
    (hσ : ∀ i ∈ b.support, σ.indexEquiv i ∈ b.support)
    (hsimply : b.cartanMatrix.IsSimplyLaced)
    {s₁ s₂ : ι} (horth_s₂ : (P.orbitIndices σ s₂ : Set ι).Pairwise P.IsOrthogonal)
    (hs₁ : s₁ ∈ b.support) (hs₂ : s₂ ∈ b.support)
    (hne : P.foldedIndex σ s₁ ≠ P.foldedIndex σ s₂) :
    F.pairing.pairing (P.foldedIndex σ s₁) (P.foldedIndex σ s₂) =
      -(#((P.orbitIndices σ s₁ ×ˢ P.orbitIndices σ s₂).filter
          fun p ↦ P.pairing p.1 p.2 ≠ 0) : K) / (#(P.orbitIndices σ s₂) : K) := by
  have hd : (#(P.orbitIndices σ s₂) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (P.card_orbitIndices_pos σ s₂).ne'
  have hint := congrArg (Int.cast (R := K))
    (F.card_orbitIndices_mul_pairingIn_foldedIndex hσ hsimply horth_s₂ hs₁ hs₂ hne)
  push_cast at hint
  rw [eq_div_iff hd, mul_comm, ← F.pairing.algebraMap_pairingIn ℤ, algebraMap_int_eq,
    Int.coe_castRingHom]
  exact hint

end Field

end OrbitSumRealization

end RootPairing
