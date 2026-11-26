/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.TitsSystem.Basic
public import TauCeti.LinearAlgebra.RootSystem.Inversions.Basic
import TauCeti.LinearAlgebra.RootSystem.Coxeter.Length

/-!
# Tits word length and root inversions for a Chevalley datum

Over any field `K`, the isomorphism `D.titsWeylGroupMulEquiv K : (D.titsSystem K).WeylGroup ≃* W`
identifies the Tits simple reflections `D.titsSimpleReflection K i` with the simple reflections of
the root datum's Weyl group. Transporting the Coxeter structure of `D.titsSystem K` along this
isomorphism shows that Tits word length agrees with the root-inversion count, yielding a direct
proof of the root-positivity criterion for simple-reflection length increase.

## Main results

* `ChevalleyDatum.wordLength_eq_ncard_inversions`: the Tits word length of
  `q : (D.titsSystem K).WeylGroup` equals the inversion count of `D.titsWeylGroupMulEquiv K q`.
* `ChevalleyDatum.wordLength_titsWeylGroupMulEquiv_symm`: transporting `w : W` to
  `(D.titsSystem K).WeylGroup` turns its inversion count into its Tits word length.
* `ChevalleyDatum.wordLength_titsSimpleReflection_mul_gt_iff_mem_posRoots`: left multiplication by
  the `i`-th simple reflection increases Tits word length precisely when
  `(D.titsWeylGroupMulEquiv K q)⁻¹(αᵢ)` is a positive root.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type v) [Field K]

/-- The Tits word length of `q : (D.titsSystem K).WeylGroup` equals the inversion count of
`D.titsWeylGroupMulEquiv K q`. -/
theorem wordLength_eq_ncard_inversions (q : (D.titsSystem K).WeylGroup) :
    (D.titsSystem K).simpleGenerators.wordLength q =
      (inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
        (D.titsWeylGroupMulEquiv K q)).ncard := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  let T := D.titsSystem K
  let P := t.simplyConnectedRootDatum ht
  let b := t.simplyConnectedBase ht
  let e : T.simple ≃ b.support :=
    (Set.equivOfEq (D.titsSystem_simple K)).trans
      ((Equiv.ofInjective (D.titsSimpleReflection K)
        (D.titsSimpleReflection_injective K)).symm.trans
        (t.simpleSupportEquivSimplyConnectedBase ht))
  have he_symm (k : b.support) :
      (e.symm k : T.WeylGroup) =
        D.titsSimpleReflection K ((t.simpleSupportEquivSimplyConnectedBase ht).symm k) := by
    simp only [e, Equiv.symm_trans_apply, Equiv.symm_symm, Set.equivOfEq_symm_apply,
      Equiv.ofInjective_apply]
  let cs := (T.coxeterSystem.map (D.titsWeylGroupMulEquiv K)).reindex e
  have hcs : ∀ k : b.support, cs.simple k = RootPairing.weylGroup.ofIdx P (k : Fin t.numRoots) := by
    intro k
    rw [CoxeterSystem.reindex_simple, CoxeterSystem.map_simple,
      TitsSystem.coxeterSystem_simple, he_symm, D.titsWeylGroupMulEquiv_titsSimpleReflection,
      t.simpleIndex_simpleSupportEquivSimplyConnectedBase_symm]
  simpa only [cs, CoxeterSystem.length_reindex, CoxeterSystem.length_map,
    TitsSystem.coxeterSystem_length] using
    RootPairing.length_eq_ncard_inversions_of_simple_eq P b cs hcs
      (D.titsWeylGroupMulEquiv K q)

/-- Transporting a root-datum Weyl element to `(D.titsSystem K).WeylGroup` turns its inversion
count into its Tits word length. -/
@[simp]
theorem wordLength_titsWeylGroupMulEquiv_symm
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    (D.titsSystem K).simpleGenerators.wordLength
        ((D.titsWeylGroupMulEquiv K).symm w) =
      (inversions (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) w).ncard := by
  rw [D.wordLength_eq_ncard_inversions K, MulEquiv.apply_symm_apply]

/-- Left multiplication by the `i`-th simple reflection increases the Tits word length of `q`
precisely when `(titsWeylGroupMulEquiv q)⁻¹(αᵢ)` is a positive root. -/
theorem wordLength_titsSimpleReflection_mul_gt_iff_mem_posRoots
    (i : Fin t.rank) (q : (D.titsSystem K).WeylGroup) :
    (D.titsSystem K).simpleGenerators.wordLength q <
        (D.titsSystem K).simpleGenerators.wordLength (D.titsSimpleReflection K i * q) ↔
      (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.titsWeylGroupMulEquiv K q)⁻¹
        (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  have hpos : (t.simplyConnectedBase ht).IsPos (t.simpleIndex ht i) :=
    (t.simplyConnectedBase ht).isPos_of_mem_support
      ((t.mem_support_simplyConnectedBase ht).mpr (by simp))
  simp only [D.wordLength_eq_ncard_inversions K, map_mul,
    D.titsWeylGroupMulEquiv_titsSimpleReflection K i,
    lt_ncard_inversions_ofIdx_mul_iff _ _ _ hpos, mem_inversions, and_iff_right hpos, not_not,
    t.posRoots_rationalRootSystem ht, mem_posRoots]

end TauCeti.DynkinType.ChevalleyDatum
