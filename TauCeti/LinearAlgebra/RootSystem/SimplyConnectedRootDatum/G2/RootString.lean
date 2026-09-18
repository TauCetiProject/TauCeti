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

This file records the root-string calculations that distinguish the short-root span in
characteristic three.  For the pinned datum `TauCeti.DynkinType.g2SimplyConnectedRootDatum` they
say:

* a long root pairs by a multiple of three with every short coroot;
* whenever a long root plus a short root is a root, the resulting root is short;
* whenever two short roots add to a long root, their root string has bottom coefficient two.

The last statement means that the corresponding Chevalley bracket coefficient is
`±(2 + 1) = ±3`, the sign depending on the choice of Chevalley basis.  Thus all three results are
the integral root-datum input for proving that the span of the short root spaces, together with
the short coroot directions, is an ideal after base change to characteristic three.
Constructing that Lie ideal and identifying the induced exceptional isogeny are later steps.

## Main results

* `TauCeti.DynkinType.three_dvd_g2_pairing_of_long_short`: a long root pairs with a short coroot by
  a multiple of three.
* `TauCeti.DynkinType.g2Length_eq_one_of_long_add_short_eq_root`: a root obtained by adding a long
  and a short root is short.
* `TauCeti.DynkinType.g2_chainBotCoeff_eq_two_of_short_add_short_eq_long`: two short roots whose sum
  is long have bottom root-string coefficient two.

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

end TauCeti.DynkinType
