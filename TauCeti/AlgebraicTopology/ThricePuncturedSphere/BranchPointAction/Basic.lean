/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Classification
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.LoopAtInfinity
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pullback
public import TauCeti.Combinatorics.PermutationTriple.BranchPoints

/-!
# Pulling covers of the thrice-punctured sphere back along the anharmonic generators

The six anharmonic self-homeomorphisms of `ℂ ∖ {0, 1}` permute the three punctures, and pulling a
cover back along one of them permutes the roles of `0`, `1` and `∞` in its monodromy triple. This
file proves this for the two generators: the involution `mob01 : z ↦ 1 − z`, which exchanges the
punctures `0` and `1`, and the involution `mob1Inf : z ↦ z / (z − 1)`, which exchanges `1` and `∞`.
The other four anharmonic maps are composites of these two.

For `mob01` the computation is transport-free because `mob01` fixes the basepoint `1/2`. Its induced
automorphism of `π₁(ℂ ∖ {0, 1}, 1/2)` exchanges `periph0` and `periph1` and carries `periphInf` to
`periph1⁻¹ * periphInf * periph1`
(`TauCeti.ThricePuncturedSphere.homeomorphMulEquivOfEq_mob01_periph0` and its companions), which
are exactly the three components of `swap01`. So the pullback of a numbered cover along `mob01` has
monodromy triple `swap01` of the original triple, on the nose, and hence the same holds on
isomorphism classes of bare covers.

The map `mob1Inf` moves the basepoint `1/2` to `−1`, so the pullback of a cover at `1/2` is a cover
at `−1`. Moving its basepoint back to `1/2` along the path `α₋₁` through the upper half-plane
(`TauCeti.ConnectedFiberNumberedCover.basepointChange`) precomposes its numbered monodromy with the
inverse of the automorphism `mob1InfMulAut` of `π₁(ℂ ∖ {0, 1}, 1/2)`, which fixes `periph0` and
carries `periph1` to `periphInf` (`TauCeti.ThricePuncturedSphere.mob1InfMulAut_periph1`). The
resulting triple is `swap1Inf` of the original one, on the nose for this choice of path. Another
path changes it by a simultaneous conjugation, so the statement that does not depend on the path
is the one on isomorphism classes: there, moving the basepoint of a bare cover involves no choice.

On isomorphism classes both statements read: the pullback is the action of
`MulOpposite.op (Equiv.swap i j)` on `TauCeti.ConnectedIsoClass`, the right action of
`Perm (Fin 3)` by reindexing the branch points. This identifies the topological branch-point
operations with the combinatorial ones at the two generators of `Perm (Fin 3)`.

## Main declarations

* `TauCeti.ThricePuncturedSphere.permutationTriple_comp_mob01`: precomposing a representation of
  `π₁(ℂ ∖ {0, 1}, 1/2)` with the automorphism induced by `mob01` applies `swap01` to its triple.
* `TauCeti.ConnectedFiberNumberedCover.connectedTriple_pullback_mob01`: **the triple of the
  pullback of a numbered cover along `mob01` is `swap01` of its triple.**
* `TauCeti.ConnectedFiberNumberedCoverClass.triple_pullback_mob01`: the same on classes of numbered
  covers.
* `TauCeti.ConnectedCoverClass.isoClass_pullback_mob01`: **pulling a bare cover back along `mob01`
  acts on the isomorphism class of its triple by the branch-point exchange of `0` and `1`.**
* `TauCeti.ThricePuncturedSphere.permutationTriple_comp_mob1InfMulAut_symm`: precomposing with the
  inverse of `mob1InfMulAut` applies `swap1Inf`.
* `TauCeti.ConnectedFiberNumberedCover.connectedTriple_basepointChange_pullback_mob1Inf`: **the
  triple of the pullback of a numbered cover along `mob1Inf`, with its basepoint moved back along
  `α₋₁`, is `swap1Inf` of its triple.**
* `TauCeti.ConnectedCoverClass.isoClass_basepointChange_pullback_mob1Inf`: **pulling a bare cover
  back along `mob1Inf` acts on the isomorphism class of its triple by the branch-point exchange of
  `1` and `∞`.**

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §2.7 (the monodromy of a cover) and Theorem 2.61 (covers with the same branch values are
  isomorphic exactly when their monodromies are conjugate).
* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5 (permuting the branch points of a constellation).
-/

public section

open CategoryTheory Equiv

namespace TauCeti

open ThricePuncturedSphere

variable {n : ℕ}

namespace ThricePuncturedSphere

/-- Precomposing a representation of `π₁(ℂ ∖ {0, 1}, 1/2)` with the automorphism induced by
`z ↦ 1 − z` exchanges the roles of `0` and `1` in its permutation triple. -/
theorem permutationTriple_comp_mob01
    (ρ : FundamentalGroup ThricePuncturedSphere basePt →* Perm (Fin n)) :
    permutationTriple
        (ρ.comp (FundamentalGroup.homeomorphMulEquivOfEq mob01 mob01_basePt).toMonoidHom) =
      (permutationTriple ρ).swap01 :=
  PermutationTriple.ext_of_two
    (by rw [PermutationTriple.swap01_σ0, permutationTriple_σ0, permutationTriple_σ1,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, homeomorphMulEquivOfEq_mob01_periph0])
    (by rw [PermutationTriple.swap01_σ1, permutationTriple_σ1, permutationTriple_σ0,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, homeomorphMulEquivOfEq_mob01_periph1])

/-- Precomposing a representation of `π₁(ℂ ∖ {0, 1}, 1/2)` with the inverse of the automorphism
induced by `z ↦ z / (z − 1)` exchanges the roles of `1` and `∞` in its permutation triple. -/
theorem permutationTriple_comp_mob1InfMulAut_symm
    (ρ : FundamentalGroup ThricePuncturedSphere basePt →* Perm (Fin n)) :
    permutationTriple (ρ.comp mob1InfMulAut.symm.toMonoidHom) = (permutationTriple ρ).swap1Inf :=
  PermutationTriple.ext_of_two (by simp [mob1InfMulAut_symm_periph0])
    (by simp only [PermutationTriple.swap1Inf_σ1, permutationTriple_σ1, permutationTriple_σinf,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mob1InfMulAut_symm_periph1, map_mul, map_inv])

/-- Pulling back along `z ↦ z / (z − 1)` from `1/2` to `−1` and changing the basepoint back along
`α₋₁` induces the inverse of `mob1InfMulAut` on `π₁(ℂ ∖ {0, 1}, 1/2)`. -/
private theorem homeomorphMulEquivOfEq_mob1Inf_comp_fundamentalGroupMulEquivOfPath_symm :
    (FundamentalGroup.homeomorphMulEquivOfEq mob1Inf (mob1Inf_mob1Inf basePt)).toMonoidHom.comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath αMob1Inf).symm.toMonoidHom =
      mob1InfMulAut.symm.toMonoidHom := by
  refine MonoidHom.ext fun g => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mob1InfMulAut_def,
    MulEquiv.symm_trans_apply, FundamentalGroup.homeomorphMulEquivOfEq_apply,
    FundamentalGroup.homeomorphMulEquiv_symm_apply]
  -- `mob1Inf` is an involution, so it is its own inverse as a continuous map
  exact FundamentalGroup.mapOfEq_congr (by ext; simp) _ _ _

end ThricePuncturedSphere

/-- **The monodromy triple of the pullback of a numbered cover along `z ↦ 1 − z` exchanges the
branch points `0` and `1`.** This is the branch-point operation `swap01` of
`TauCeti.PermutationTriple`, realized on the nose because `z ↦ 1 − z` fixes the basepoint. -/
@[simp]
theorem ConnectedFiberNumberedCover.connectedTriple_pullback_mob01
    (c : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (c.pullback mob01 mob01_basePt).connectedTriple =
      c.connectedTriple.reindexBranchPoints (Equiv.swap 0 1) := by
  apply Subtype.ext
  rw [ConnectedTriple.coe_reindexBranchPoints, PermutationTriple.reindexBranchPoints_swap_zero_one,
    coe_connectedTriple, coe_connectedTriple, IsCoveringMap.monodromyTriple_def,
    IsCoveringMap.monodromyTriple_def, permCongrHom_comp_monodromyPerm_pullback]
  exact permutationTriple_comp_mob01 _

/-- The triple of the pullback of a class of numbered covers along `z ↦ 1 − z` is the triple of
the class with the branch points `0` and `1` exchanged. -/
@[simp]
theorem ConnectedFiberNumberedCoverClass.triple_pullback_mob01
    (C : ConnectedFiberNumberedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (C.pullback mob01 mob01_basePt).triple = C.triple.reindexBranchPoints (Equiv.swap 0 1) :=
  ind (fun c => by
    rw [pullback_mk, triple_mk, triple_mk]
    exact c.connectedTriple_pullback_mob01) C

/-- **Pulling a cover of `ℂ ∖ {0, 1}` back along `z ↦ 1 − z` acts on the isomorphism class of its
triple by exchanging the branch points `0` and `1`.** The topological branch-point operation on
covers is the combinatorial one on `TauCeti.ConnectedIsoClass`, at the generator
`Equiv.swap 0 1` of the right action of `Perm (Fin 3)`. -/
@[simp]
theorem ConnectedCoverClass.isoClass_pullback_mob01
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (C.pullback mob01 mob01_basePt).isoClass =
      MulOpposite.op (Equiv.swap (0 : Fin 3) 1) • C.isoClass := by
  obtain ⟨N, rfl⟩ := ConnectedFiberNumberedCoverClass.forgetNumbering_surjective C
  rw [← ConnectedFiberNumberedCoverClass.forgetNumbering_pullback,
    ConnectedFiberNumberedCoverClass.isoClass_forgetNumbering,
    ConnectedFiberNumberedCoverClass.isoClass_forgetNumbering,
    ConnectedFiberNumberedCoverClass.triple_pullback_mob01, ConnectedIsoClass.op_smul_mk]

/-- **The monodromy triple of the pullback of a numbered cover along `z ↦ z / (z − 1)` exchanges
the branch points `1` and `∞`.** The map moves the basepoint `1/2` to `−1`, so the pulled-back cover
is numbered over `−1`; moving its basepoint back to `1/2` along the path `α₋₁` through the upper
half-plane gives a numbered cover whose triple is the branch-point operation `swap1Inf` of the
original triple, on the nose. Another connecting path changes the result by a simultaneous
conjugation. -/
@[simp]
theorem ConnectedFiberNumberedCover.connectedTriple_basepointChange_pullback_mob1Inf
    (c : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n) :
    ((c.pullback mob1Inf (mob1Inf_mob1Inf basePt)).basepointChange αMob1Inf).connectedTriple =
      c.connectedTriple.reindexBranchPoints (Equiv.swap 1 2) := by
  apply Subtype.ext
  simp only [ConnectedTriple.coe_reindexBranchPoints,
    PermutationTriple.reindexBranchPoints_swap_one_two, coe_connectedTriple,
    IsCoveringMap.monodromyTriple_def]
  rw [permCongrHom_comp_monodromyPerm_basepointChange, permCongrHom_comp_monodromyPerm_pullback,
    MonoidHom.comp_assoc, homeomorphMulEquivOfEq_mob1Inf_comp_fundamentalGroupMulEquivOfPath_symm,
    permutationTriple_comp_mob1InfMulAut_symm]

/-- **Pulling a cover of `ℂ ∖ {0, 1}` back along `z ↦ z / (z − 1)` acts on the isomorphism class
of its triple by exchanging the branch points `1` and `∞`.** The pulled-back cover is a cover at
`−1`, the image of the basepoint, and it is compared with covers at `1/2` by moving its basepoint,
which a bare cover allows without choices. The topological branch-point operation is the
combinatorial one on `TauCeti.ConnectedIsoClass`, at the generator `Equiv.swap 1 2` of the right
action of `Perm (Fin 3)`. -/
@[simp]
theorem ConnectedCoverClass.isoClass_basepointChange_pullback_mob1Inf
    (C : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n)
    (h : basePt ∈ connectedComponent (mob1Inf basePt)) :
    ((C.pullback mob1Inf (mob1Inf_mob1Inf basePt)).basepointChange h).isoClass =
      MulOpposite.op (Equiv.swap (1 : Fin 3) 2) • C.isoClass := by
  obtain ⟨N, rfl⟩ := ConnectedFiberNumberedCoverClass.forgetNumbering_surjective C
  induction N using ConnectedFiberNumberedCoverClass.ind with | h c => ?_
  -- the moved pulled-back bare cover is the image of the moved pulled-back numbered cover
  rw [ConnectedFiberNumberedCoverClass.forgetNumbering_mk, ConnectedCoverClass.pullback_mk,
    ConnectedCoverClass.basepointChange_mk, ← ConnectedFiberNumberedCover.forgetNumbering_pullback,
    ← ConnectedFiberNumberedCover.forgetNumbering_basepointChange _ αMob1Inf]
  simp [← ConnectedFiberNumberedCoverClass.forgetNumbering_mk, ConnectedIsoClass.op_smul_mk]

end TauCeti
