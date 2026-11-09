/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Length

/-!
# Root strings in the pinned `G₂` root datum

This file records root-string calculations for the short-root span in characteristic three
and for the long–short Chevalley straightening relation. For the pinned datum
`TauCeti.DynkinType.g2SimplyConnectedRootDatum` they say:

* a long root pairs by a multiple of three with every short coroot;
* whenever a long root plus a short root is a root, the resulting root is short;
* whenever two short roots add to a long root, their root string has bottom coefficient two;
* whenever two short roots add to a short root, their root string has bottom coefficient one;
* when a root sum is long, adding either summand again does not give a root;
* a short root and a long root whose sum is a root have descending string coefficient zero
  and ascending coefficient three.

The long-sum statement means that the corresponding Chevalley bracket coefficient is
`±(2 + 1) = ±3`, the sign depending on the choice of Chevalley basis. Thus the first three results
are the integral root-datum input for proving that the span of the short root spaces, together with
the short coroot directions, is an ideal after base change to characteristic three.
The short-sum statement gives coefficient `±2`, the first coefficient of the three-factor
short-pair Chevalley commutator relation.
The absence of higher roots also gives the class-two Chevalley commutator relation at a long
root sum.
The four-term long–short string gives the exact factors two and three that occur in the
successive divided brackets used by straightening.

## Main results

* `TauCeti.DynkinType.three_dvd_g2_pairing_of_long_short`: a long root pairs with a short coroot by
  a multiple of three.
* `TauCeti.DynkinType.g2Length_eq_one_of_long_add_short_eq_root`: a root obtained by adding a long
  and a short root is short.
* `TauCeti.DynkinType.g2_chainBotCoeff_eq_two_of_short_add_short_eq_long`: two short roots whose sum
  is long have bottom root-string coefficient two.
* `TauCeti.DynkinType.g2_chainBotCoeff_eq_one_of_short_add_short_eq_short`: two short roots whose
  sum is short have bottom root-string coefficient one.
* `TauCeti.DynkinType.g2_root_add_notMem_range_of_add_eq_long`: a long root sum has no
  higher roots.
* `TauCeti.DynkinType.g2_chainBotCoeff_eq_zero_and_chainTopCoeff_eq_three_of_short_long`:
  the four-term string starting at a long root in a short-root direction.

## References

The coordinates and numbering follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate IX.  The coefficient-three phenomenon is the type `G₂` entry in the Chevalley commutator
relations; see R. W. Carter, *Simple Groups of Lie Type*, Chapter 5.
-/

public section

namespace TauCeti.DynkinType

open Function Set

/-- A long root of the pinned `G₂` datum pairs by a multiple of three with every short coroot.

This is the toral coefficient that vanishes after base change to characteristic three. -/
theorem three_dvd_g2_pairing_of_long_short (i j : Fin 12) (hi : g2Length i = 3)
    (hj : g2Length j = 1) : (3 : ℤ) ∣ g2SimplyConnectedRootDatum.pairing i j := by
  rw [g2SimplyConnectedRootDatum_pairing, g2Root_apply, g2Coroot_apply]
  rw [g2Length_apply] at hi hj
  revert i j
  decide +kernel

/-- Adding a long root and a short root in the pinned `G₂` datum can only produce a short root.

This is the root-space closure statement needed for the characteristic-three short-root ideal. -/
theorem g2Length_eq_one_of_long_add_short_eq_root (i j k : Fin 12)
    (hi : g2Length i = 3) (hj : g2Length j = 1)
    (hadd : g2SimplyConnectedRootDatum.root k =
      g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root j) :
      g2Length k = 1 := by
  simp only [g2SimplyConnectedRootDatum_root, g2Root_apply] at hadd
  rw [g2Length_apply] at hi hj ⊢
  revert i j k
  decide +kernel

private theorem g2Pairing_eq_one_of_short_add_short_eq_long (i j k : Fin 12)
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 3)
    (hadd : g2SimplyConnectedRootDatum.root k =
      g2SimplyConnectedRootDatum.root j + g2SimplyConnectedRootDatum.root i) :
      g2SimplyConnectedRootDatum.pairing j i = 1 := by
  simp only [g2SimplyConnectedRootDatum_root, g2SimplyConnectedRootDatum_pairing,
    g2Root_apply, g2Coroot_apply] at hadd ⊢
  rw [g2Length_apply] at hi hj hk
  revert i j k
  decide +kernel

private theorem g2Root_add_two_smul_ne_root_of_short_add_short_eq_long (i j k l : Fin 12)
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 3)
    (hadd : g2SimplyConnectedRootDatum.root k =
      g2SimplyConnectedRootDatum.root j + g2SimplyConnectedRootDatum.root i) :
      g2SimplyConnectedRootDatum.root l ≠
        g2SimplyConnectedRootDatum.root j + 2 • g2SimplyConnectedRootDatum.root i := by
  simp only [g2SimplyConnectedRootDatum_root, g2Root_apply] at hadd ⊢
  rw [g2Length_apply] at hi hj hk
  revert i j k l
  decide +kernel

/-- If two short roots of the pinned `G₂` datum add to a long root, the bottom coefficient of
their root string is two.  Consequently the associated Chevalley bracket coefficient is `±3`
(the sign depending on the choice of Chevalley basis), and vanishes in characteristic three. -/
theorem g2_chainBotCoeff_eq_two_of_short_add_short_eq_long (i j k : Fin 12)
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 3)
    (hadd : g2SimplyConnectedRootDatum.root k =
      g2SimplyConnectedRootDatum.root j + g2SimplyConnectedRootDatum.root i) :
      g2SimplyConnectedRootDatum.chainBotCoeff i j = 2 := by
  let P := g2SimplyConnectedRootDatum
  have hadd_mem : P.root i + P.root j ∈ range P.root := by
    refine ⟨k, ?_⟩
    rw [hadd, add_comm]
  have hli : LinearIndependent ℤ ![P.root i, P.root j] :=
    P.linearIndependent_of_add_mem_range_root' hadd_mem
  have htop_ge : 1 ≤ P.chainTopCoeff i j := P.one_le_chainTopCoeff_of_root_add_mem hadd_mem
  have htop_le : P.chainTopCoeff i j ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ P.chainTopCoeff i j := by omega
    obtain ⟨l, hl⟩ := (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli).2 htwo
    exact g2Root_add_two_smul_ne_root_of_short_add_short_eq_long i j k l hi hj hk hadd hl
  have hpair : P.pairing j i = 1 :=
    g2Pairing_eq_one_of_short_add_short_eq_long i j k hi hj hk hadd
  have hpairIn : P.pairingIn ℤ j i = 1 := by
    simpa using (P.algebraMap_pairingIn ℤ j i).trans hpair
  have hstring := P.chainBotCoeff_sub_chainTopCoeff hli
  rw [hpairIn] at hstring
  omega

/-- Two short roots whose sum is short have bottom root-string coefficient one. Thus their
Chevalley bracket has coefficient `±2`. -/
theorem g2_chainBotCoeff_eq_one_of_short_add_short_eq_short (i j k : Fin 12)
    (hi : g2Length i = 1) (hj : g2Length j = 1) (hk : g2Length k = 1)
    (hadd : g2SimplyConnectedRootDatum.root k =
      g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root j) :
    g2SimplyConnectedRootDatum.chainBotCoeff i j = 1 := by
  have hli := g2SimplyConnectedRootDatum.linearIndependent_of_add_mem_range_root' ⟨k, hadd⟩
  obtain ⟨hsub, htwo⟩ :
      g2SimplyConnectedRootDatum.root j - g2SimplyConnectedRootDatum.root i ∈
        Set.range g2SimplyConnectedRootDatum.root ∧
      g2SimplyConnectedRootDatum.root j - 2 • g2SimplyConnectedRootDatum.root i ∉
        Set.range g2SimplyConnectedRootDatum.root := by
    clear hli
    simp only [Set.mem_range, g2SimplyConnectedRootDatum_root, g2Root_apply] at hadd ⊢
    simp only [g2Length_apply] at hi hj hk
    revert i j k
    decide +kernel
  have hone := (g2SimplyConnectedRootDatum.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hli
    (n := 1)).1 (by simpa using hsub)
  have hnot := mt (g2SimplyConnectedRootDatum.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hli
    (n := 2)).2 htwo
  omega

/-- If the sum of two `G₂` roots is long, adding either summand to that sum does not give a
root. This is the absence of higher roots in the corresponding class-two root string. -/
theorem g2_root_add_notMem_range_of_add_eq_long (i j k : Fin 12)
    (hk : g2Length k = 3)
    (hadd : g2SimplyConnectedRootDatum.root k =
      g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root j) :
    g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root k ∉
      range g2SimplyConnectedRootDatum.root := by
  rintro ⟨l, hl⟩
  simp only [g2SimplyConnectedRootDatum_root, g2Root_apply] at hadd hl
  rw [g2Length_apply] at hk
  revert i j k l
  decide +kernel

/-- A short root and a long root whose sum is a root start a four-term root string:
its descending coefficient is zero and its ascending coefficient is three. -/
theorem g2_chainBotCoeff_eq_zero_and_chainTopCoeff_eq_three_of_short_long
    (i j : Fin 12) (hi : g2Length i = 1) (hj : g2Length j = 3)
    (hadd : g2SimplyConnectedRootDatum.root i + g2SimplyConnectedRootDatum.root j ∈
      range g2SimplyConnectedRootDatum.root) :
    g2SimplyConnectedRootDatum.chainBotCoeff i j = 0 ∧
      g2SimplyConnectedRootDatum.chainTopCoeff i j = 3 := by
  have hp : g2SimplyConnectedRootDatum.pairing j i = -3 := by
    simp only [mem_range, g2SimplyConnectedRootDatum_root, g2SimplyConnectedRootDatum_pairing,
      g2Root_apply, g2Coroot_apply] at hadd ⊢
    rw [g2Length_apply] at hi hj
    revert i j
    decide +kernel
  have hli := g2SimplyConnectedRootDatum.linearIndependent_of_add_mem_range_root' hadd
  have hs := g2SimplyConnectedRootDatum.chainBotCoeff_sub_chainTopCoeff hli
  have hb := g2SimplyConnectedRootDatum.chainBotCoeff_add_chainTopCoeff_le_three (i := i) (j := j)
  have hp' : g2SimplyConnectedRootDatum.pairingIn ℤ j i = -3 := by
    simpa using (g2SimplyConnectedRootDatum.algebraMap_pairingIn ℤ j i).trans hp
  rw [hp'] at hs
  omega

end TauCeti.DynkinType
